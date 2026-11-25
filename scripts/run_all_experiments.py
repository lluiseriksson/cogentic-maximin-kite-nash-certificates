"""Generate all 16 canonical KITE-NASH-CERT-1.0 certificates and 4 exact-Q studies
for Paper 56 (Google Research Cogentic, Nov. 25, 2026, MaximinKiteNE).

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import json
import sys
import time
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, List, Sequence

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from src.kite_certifier import (
    SCHEMA_VERSION,
    STAGE4_TARGET,
    VOLTERRA_FLOOR,
    _lcm_int,
    verify_certificate,
)
from src.kite_exact import (
    bimatrix_regrets,
    eval_H_full,
    eval_Q53_rat,
    format_exact_rat,
    l1_distance,
    simplex_round_floor,
    vec_mat,
)

CERT_DIR = ROOT / "certificates"
RES_DIR = ROOT / "results"


def _f(x: int | Fraction, d: int = 1) -> Fraction:
    return x if isinstance(x, Fraction) else Fraction(x, d)


def _fmt_vec(v: Sequence[Fraction]) -> List[str]:
    return [format_exact_rat(q) for q in v]


def _fmt_mat(M: Sequence[Sequence[Fraction]]) -> List[List[str]]:
    return [_fmt_vec(row) for row in M]


def _round_largest_remainder(p: Sequence[Fraction], D: int) -> List[int]:
    qs, rems, r = simplex_round_floor(p, D)
    order = sorted(range(len(p)), key=lambda k: (-rems[k], k))
    counts = list(qs)
    for k in order[:r]:
        counts[k] += 1
    return counts


def _make_mode1_in_kite(
    cid: str,
    s: Fraction,
    R: List[List[Fraction]],
    C: List[List[Fraction]],
    x: List[Fraction],
    y: List[Fraction],
) -> Dict[str, Any]:
    reg = bimatrix_regrets(R, C, x, y)
    r1, r2 = reg["r1"], reg["r2"]
    m, n = len(R), len(R[0])
    if r1 > s:
        theta = (r1 - s) / r1
        br_idx = reg["i_star"]
        x_out = [(Fraction(1, 1) - theta) * x[i] + (theta if i == br_idx else Fraction(0, 1)) for i in range(m)]
        y_out = list(y)
    elif r2 > s:
        theta = (r2 - s) / r2
        br_idx = reg["j_star"]
        x_out = list(x)
        y_out = [(Fraction(1, 1) - theta) * y[j] + (theta if j == br_idx else Fraction(0, 1)) for j in range(n)]
    else:
        br_idx = 0
        x_out, y_out = list(x), list(y)
    out_reg = bimatrix_regrets(R, C, x_out, y_out)
    return {
        "schema": SCHEMA_VERSION,
        "mode": "kite_best_response_and_welfare_cert",
        "cert_id": cid,
        "branch": "in_kite",
        "s_kite": format_exact_rat(s),
        "R": _fmt_mat(R),
        "C": _fmt_mat(C),
        "x": _fmt_vec(x),
        "y": _fmt_vec(y),
        "x_out": _fmt_vec(x_out),
        "y_out": _fmt_vec(y_out),
        "best_response_idx": br_idx,
        "claimed_uR": format_exact_rat(reg["uR"]),
        "claimed_uC": format_exact_rat(reg["uC"]),
        "claimed_r1": format_exact_rat(r1),
        "claimed_r2": format_exact_rat(r2),
        "claimed_welfare": format_exact_rat(reg["uR"] + reg["uC"]),
        "claimed_output_regret": format_exact_rat(out_reg["max_regret"]),
    }


def _make_mode1_escape(
    cid: str,
    s: Fraction,
    R: List[List[Fraction]],
    C: List[List[Fraction]],
    x: List[Fraction],
    y: List[Fraction],
    t1: Fraction,
    t2: Fraction,
) -> Dict[str, Any]:
    reg = bimatrix_regrets(R, C, x, y)
    welfare = reg["uR"] + reg["uC"]
    wcap = Fraction(2, 1) - s / (Fraction(1, 1) - s)
    lam = s * t1 + (Fraction(1, 1) - s) * t2
    ratio = lam / (Fraction(1, 1) - lam)
    return {
        "schema": SCHEMA_VERSION,
        "mode": "kite_best_response_and_welfare_cert",
        "cert_id": cid,
        "branch": "escaped_welfare_cap",
        "s_kite": format_exact_rat(s),
        "R": _fmt_mat(R),
        "C": _fmt_mat(C),
        "x": _fmt_vec(x),
        "y": _fmt_vec(y),
        "dual_theta1": format_exact_rat(t1),
        "dual_theta2": format_exact_rat(t2),
        "claimed_uR": format_exact_rat(reg["uR"]),
        "claimed_uC": format_exact_rat(reg["uC"]),
        "claimed_r1": format_exact_rat(reg["r1"]),
        "claimed_r2": format_exact_rat(reg["r2"]),
        "claimed_welfare": format_exact_rat(welfare),
        "claimed_welfare_cap": format_exact_rat(wcap),
        "claimed_dual_lambda": format_exact_rat(lam),
        "claimed_dual_ratio": format_exact_rat(ratio),
    }


def _make_mode2(
    cid: str,
    s: Fraction,
    R: List[List[Fraction]],
    C: List[List[Fraction]],
    x_mm: List[Fraction],
    y_mm: List[Fraction],
    vR: Fraction,
    x_col_guard: List[Fraction],
    y_col_mm: List[Fraction],
    vC: Fraction,
    round_p: List[Fraction],
    D: int,
    outcome: str,
    halt_x: List[Fraction] | None = None,
    halt_y: List[Fraction] | None = None,
    x_bar: List[Fraction] | None = None,
) -> Dict[str, Any]:
    counts = _round_largest_remainder(round_p, D)
    _, _, rem_r = simplex_round_floor(round_p, D)
    p_hat = [Fraction(c, D) for c in counts]
    l1_err = l1_distance(p_hat, round_p)
    cert: Dict[str, Any] = {
        "schema": SCHEMA_VERSION,
        "mode": "minimax_screen_and_rounding_cert",
        "cert_id": cid,
        "s_kite": format_exact_rat(s),
        "R": _fmt_mat(R),
        "C": _fmt_mat(C),
        "x_mm": _fmt_vec(x_mm),
        "y_mm": _fmt_vec(y_mm),
        "claimed_vR": format_exact_rat(vR),
        "x_col_guard": _fmt_vec(x_col_guard),
        "y_col_mm": _fmt_vec(y_col_mm),
        "claimed_vC": format_exact_rat(vC),
        "round_target_p": _fmt_vec(round_p),
        "denom_D": D,
        "rounded_counts": counts,
        "claimed_remainder_r": rem_r,
        "claimed_l1_error": format_exact_rat(l1_err),
        "claimed_screen_outcome": outcome,
    }
    if outcome == "early_halt":
        assert halt_x is not None and halt_y is not None
        h_reg = bimatrix_regrets(R, C, halt_x, halt_y)
        cert["halt_x"] = _fmt_vec(halt_x)
        cert["halt_y"] = _fmt_vec(halt_y)
        cert["claimed_halt_regret"] = format_exact_rat(h_reg["max_regret"])
    else:
        assert x_bar is not None
        x_tilde = [Fraction(1, 4) * x_mm[i] + Fraction(3, 4) * x_bar[i] for i in range(len(x_mm))]
        anchor_floor = min(vec_mat(x_tilde, R))
        cert["x_bar"] = _fmt_vec(x_bar)
        cert["x_tilde"] = _fmt_vec(x_tilde)
        cert["claimed_anchor_floor"] = format_exact_rat(anchor_floor)
    return cert


def _make_mode3(
    cid: str,
    regime: str,
    probes: List[List[Fraction]],
) -> Dict[str, Any]:
    H_vals = [eval_H_full(z, c1, c2)["H"] for z, c1, c2 in probes]
    max_H = max(H_vals)
    min_H = min(H_vals)
    worst_idx = H_vals.index(max_H)
    return {
        "schema": SCHEMA_VERSION,
        "mode": "stage4_H_algebraic_cert",
        "cert_id": cid,
        "regime": regime,
        "probes": [_fmt_vec(p) for p in probes],
        "claimed_probe_count": len(probes),
        "claimed_worst_probe_idx": worst_idx,
        "claimed_max_H": format_exact_rat(max_H),
        "claimed_min_H": format_exact_rat(min_H),
        "claimed_margin_to_minus_1_3000": format_exact_rat(STAGE4_TARGET - max_H),
        "claimed_gap_to_volterra_floor": format_exact_rat(VOLTERRA_FLOOR - max_H),
    }


def _make_mode4(
    cid: str,
    eps: Fraction,
    stage: str,
    R: List[List[Fraction]],
    C: List[List[Fraction]],
    x: List[Fraction],
    y: List[Fraction],
) -> Dict[str, Any]:
    reg = bimatrix_regrets(R, C, x, y)
    supp_x = sum(1 for v in x if v > 0)
    supp_y = sum(1 for v in y if v > 0)
    lcm_den = 1
    for v in list(x) + list(y):
        lcm_den = _lcm_int(lcm_den, v.denominator)
    return {
        "schema": SCHEMA_VERSION,
        "mode": "bimatrix_one_fifth_ne_cert",
        "cert_id": cid,
        "eps_target": format_exact_rat(eps),
        "construction_stage": stage,
        "R": _fmt_mat(R),
        "C": _fmt_mat(C),
        "x": _fmt_vec(x),
        "y": _fmt_vec(y),
        "claimed_uR": format_exact_rat(reg["uR"]),
        "claimed_uC": format_exact_rat(reg["uC"]),
        "claimed_r1": format_exact_rat(reg["r1"]),
        "claimed_r2": format_exact_rat(reg["r2"]),
        "claimed_max_regret": format_exact_rat(reg["max_regret"]),
        "claimed_supp_x": supp_x,
        "claimed_supp_y": supp_y,
        "claimed_lcm_denom": lcm_den,
    }


def build_all_16_certificates() -> List[Dict[str, Any]]:
    certs: List[Dict[str, Any]] = []

    # --- MODE 1 (4 certs) ---
    # 1. Zero-slack tight 1/5-kite row mixing: r1 = 1/4, r2 = 0 => (4/5)(1/4) + 0 = 1/5 exact!
    # At x=(1,0), y=(1,0): uR = 3/4, M1 = 1 => r1 = 1/4; uC = 1, M2 = 1 => r2 = 0.
    # Mixing theta = 1/5 => x' = (4/5, 1/5). Let C[1][1]=1, C[1][0]=0 => Col payoff at y=(1,0) is 4/5, best is 1 => r2' = 1/5!
    R1 = [[_f(3, 4), _f(0)], [_f(1), _f(1, 2)]]
    C1 = [[_f(1), _f(1)], [_f(0), _f(1)]]
    certs.append(_make_mode1_in_kite(
        "kite_row_mix_tight_1_5",
        _f(1, 5), R1, C1, [_f(1), _f(0)], [_f(1), _f(0)],
    ))

    # 2. Asymmetric 3x3 column mixing strictly inside 1/5-kite: r1 = 1/10, r2 = 11/50
    # At x=(1,0,0), y=(1,0,0): R[0][0]=9/10, R[1][0]=1 => r1=1/10; C[0][0]=39/50, C[0][1]=1 => r2=11/50.
    # (1/5)(1/10) + (4/5)(11/50) = 1/50 + 44/250 = 49/250 < 1/5!
    R2 = [
        [_f(9, 10), _f(4, 5), _f(1, 2)],
        [_f(1), _f(9, 10), _f(3, 5)],
        [_f(1, 2), _f(1, 2), _f(1, 2)],
    ]
    C2 = [
        [_f(39, 50), _f(1), _f(1, 2)],
        [_f(1, 2), _f(3, 4), _f(1, 4)],
        [_f(1, 3), _f(1, 3), _f(1, 3)],
    ]
    certs.append(_make_mode1_in_kite(
        "kite_col_mix_asymmetric_3x3",
        _f(1, 5), R2, C2, [_f(1), _f(0), _f(0)], [_f(1), _f(0), _f(0)],
    ))

    # 3. Escaped 1/5-kite certifying strict welfare cap uR + uC < 7/4 and dual ratio a = 3/2 in [1/4, 4]
    # At x=(1,0), y=(1,0): R[0][0]=7/10, R[1][0]=1 => r1=3/10; C[0][0]=4/5, C[0][1]=1 => r2=1/5.
    # lhs_row = (4/5)(3/10) + (1/5)(1/5) = 6/25 + 1/25 = 7/25 > 1/5; lhs_col = (1/5)(3/10)+(4/5)(1/5) = 11/50 > 1/5.
    # uR + uC = 7/10 + 4/5 = 3/2 < 7/4!
    R3 = [[_f(7, 10), _f(1, 5)], [_f(1), _f(1, 2)]]
    C3 = [[_f(4, 5), _f(1)], [_f(1, 4), _f(1, 2)]]
    certs.append(_make_mode1_escape(
        "kite_escape_welfare_7_4_cap",
        _f(1, 5), R3, C3, [_f(1), _f(0)], [_f(1), _f(0)], _f(1, 3), _f(2, 3),
    ))

    # 4. General s=1/4 kite escape: welfare cap 2 - (1/4)/(3/4) = 5/3, dual ratio in [1/3, 3]
    # At x=(1,0), y=(1,0): uR = 3/5, M1 = 1 => r1 = 2/5; uC = 3/5, M2 = 1 => r2 = 2/5.
    # lhs_row = lhs_col = 2/5 > 1/4; uR + uC = 6/5 < 5/3!
    R4 = [[_f(3, 5), _f(0)], [_f(1), _f(2, 5)]]
    C4 = [[_f(3, 5), _f(1)], [_f(0), _f(2, 5)]]
    certs.append(_make_mode1_escape(
        "kite_escape_general_s1_4",
        _f(1, 4), R4, C4, [_f(1), _f(0)], [_f(1), _f(0)], _f(1, 4), _f(3, 4),
    ))

    # --- MODE 2 (4 certs) ---
    # 5. Early halt: max(vR, vC) <= 1/5 in 3x3 diagonal game: vR = 1/6, vC = 1/5!
    # R5 = diag(1/2, 1/2, 1/2) => uniform saddle vR = 1/6; C5 = diag(3/5, 3/5, 3/5) => uniform saddle vC = 1/5.
    # Lem. 2.2 minimax profile (x_col_guard, y_mm) = (u3, u3) gives exact regret 0 <= 1/5!
    u3 = [_f(1, 3), _f(1, 3), _f(1, 3)]
    R5 = [[_f(1, 2), _f(0), _f(0)], [_f(0), _f(1, 2), _f(0)], [_f(0), _f(0), _f(1, 2)]]
    C5 = [[_f(3, 5), _f(0), _f(0)], [_f(0), _f(3, 5), _f(0)], [_f(0), _f(0), _f(3, 5)]]
    certs.append(_make_mode2(
        "minimax_early_halt_diag_1_6",
        _f(1, 5), R5, C5,
        u3, u3, _f(1, 6),
        u3, u3, _f(1, 5),
        [_f(1, 7), _f(2, 7), _f(4, 7)], 24,
        "early_halt",
        halt_x=u3, halt_y=u3,
    ))

    # 6. Early halt exact boundary vR = vC = 1/5 <= 1/5 in 2x2 anti-diagonal / diagonal matching game
    R6 = [[_f(2, 5), _f(0)], [_f(0), _f(2, 5)]]
    C6 = [[_f(0), _f(2, 5)], [_f(2, 5), _f(0)]]
    u2 = [_f(1, 2), _f(1, 2)]
    certs.append(_make_mode2(
        "minimax_early_halt_boundary_1_5",
        _f(1, 5), R6, C6,
        u2, u2, _f(1, 5),
        u2, u2, _f(1, 5),
        [_f(3, 11), _f(8, 11)], 30,
        "early_halt",
        halt_x=u2, halt_y=u2,
    ))

    # 7. Anchored continue: 3x3 scaled RPS with vR = 1/2 > 1/5, vC = 1/2 (vR >= vC)
    R7 = [[_f(1, 2), _f(0), _f(1)], [_f(1), _f(1, 2), _f(0)], [_f(0), _f(1), _f(1, 2)]]
    C7 = [[_f(1, 2), _f(1), _f(0)], [_f(0), _f(1, 2), _f(1)], [_f(1), _f(0), _f(1, 2)]]
    certs.append(_make_mode2(
        "minimax_anchored_continue_rps",
        _f(1, 5), R7, C7,
        u3, u3, _f(1, 2),
        u3, u3, _f(1, 2),
        [_f(1, 6), _f(1, 3), _f(1, 2)], 60,
        "anchored_continue",
        x_bar=[_f(1, 2), _f(1, 4), _f(1, 4)],
    ))

    # 8. Anchored continue: 4x4 asymmetric (Row-oriented after Step 2: vR = 2/5 > 1/5, vR >= vC = 3/10)
    R8 = [
        [_f(2, 5), _f(1, 2), _f(3, 5), _f(7, 10)],
        [_f(3, 10), _f(4, 5), _f(1, 4), _f(3, 5)],
        [_f(1, 5), _f(1, 5), _f(9, 10), _f(1, 2)],
        [_f(1, 10), _f(2, 5), _f(3, 5), _f(4, 5)],
    ]
    C8 = [
        [_f(3, 10), _f(1, 5), _f(1, 10), _f(0)],
        [_f(2, 5), _f(4, 5), _f(3, 10), _f(1, 5)],
        [_f(1, 2), _f(1, 5), _f(9, 10), _f(2, 5)],
        [_f(3, 5), _f(7, 10), _f(1, 5), _f(1)],
    ]
    certs.append(_make_mode2(
        "minimax_anchored_4x4_tight",
        _f(1, 5), R8, C8,
        [_f(1), _f(0), _f(0), _f(0)], [_f(1), _f(0), _f(0), _f(0)], _f(2, 5),
        [_f(1), _f(0), _f(0), _f(0)], [_f(1), _f(0), _f(0), _f(0)], _f(3, 10),
        [_f(1, 13), _f(3, 13), _f(4, 13), _f(5, 13)], 100,
        "anchored_continue",
        x_bar=[_f(0), _f(1, 2), _f(1, 4), _f(1, 4)],
    ))

    # --- MODE 3 (4 certs) ---
    # 9. Low-gate z <= 1 probes (Lemma 5.2)
    low_probes = [
        [_f(1, 4), _f(1, 4), _f(1, 4)],
        [_f(1, 4), _f(1, 2), _f(1, 2)],
        [_f(1, 2), _f(1, 2), _f(1, 2)],
        [_f(1, 2), _f(1), _f(1, 2)],
        [_f(3, 4), _f(3, 4), _f(3, 4)],
        [_f(3, 4), _f(1), _f(1)],
        [_f(3, 4), _f(2), _f(3, 2)],
        [_f(7, 8), _f(7, 8), _f(7, 8)],
        [_f(7, 8), _f(1), _f(1)],
        [_f(15, 16), _f(1), _f(1)],
        [_f(1), _f(1), _f(1)],
        [_f(1), _f(5, 4), _f(3, 2)],
    ]
    certs.append(_make_mode3("stage4_low_gate_grid_z_le_1", "low_gate_z_le_1", low_probes))

    # 10. High-gate mid z in (1, 2] probes (Lemma 5.4 curved gate)
    mid_probes = [
        [_f(9, 8), _f(9, 8), _f(9, 8)],
        [_f(5, 4), _f(5, 4), _f(5, 4)],
        [_f(5, 4), _f(1), _f(3, 2)],
        [_f(4, 3), _f(4, 3), _f(4, 3)],
        [_f(3, 2), _f(3, 2), _f(3, 2)],
        [_f(3, 2), _f(5, 4), _f(7, 4)],
        [_f(3, 2), _f(2), _f(2)],
        [_f(7, 4), _f(7, 4), _f(7, 4)],
        [_f(11, 6), _f(11, 6), _f(11, 6)],
        [_f(11, 6), _f(3, 2), _f(2)],
        [_f(2), _f(2), _f(2)],
        [_f(2), _f(3, 2), _f(5, 2)],
    ]
    certs.append(_make_mode3("stage4_high_gate_mid_1_to_2", "high_gate_mid_1_to_2", mid_probes))

    # 11. High-gate top z in (2, 4] probes (Lemma 5.4 saturated gate f0=9/5)
    top_probes = [
        [_f(9, 4), _f(9, 4), _f(9, 4)],
        [_f(5, 2), _f(5, 2), _f(5, 2)],
        [_f(5, 2), _f(2), _f(3)],
        [_f(3), _f(3), _f(3)],
        [_f(3), _f(2), _f(7, 2)],
        [_f(3), _f(4), _f(4)],
        [_f(7, 2), _f(7, 2), _f(7, 2)],
        [_f(4), _f(1, 4), _f(4)],
        [_f(4), _f(2), _f(4)],
        [_f(4), _f(4), _f(4)],
    ]
    certs.append(_make_mode3("stage4_high_gate_top_2_to_4", "high_gate_top_2_to_4", top_probes))

    # 12. Adversarial corners, kinks, and near-supremum probes across full [1/4, 4]^3
    adv_probes = [
        [_f(1, 4), _f(4), _f(1, 4)],
        [_f(1, 4), _f(1, 4), _f(4)],
        [_f(3, 4), _f(1, 4), _f(7, 4)],
        [_f(7, 8), _f(1, 2), _f(1)],
        [_f(7, 8), _f(3, 2), _f(3, 2)],
        [_f(1), _f(1, 4), _f(1)],
        [_f(1), _f(4), _f(4)],
        [_f(9, 8), _f(1), _f(5, 4)],
        [_f(5, 4), _f(3, 2), _f(7, 4)],
        [_f(3, 2), _f(1), _f(2)],
        [_f(11, 6), _f(1), _f(3)],
        [_f(2), _f(1, 4), _f(4)],
        [_f(3), _f(1, 4), _f(1, 4)],
        [_f(4), _f(1, 4), _f(1, 4)],
    ]
    certs.append(_make_mode3("stage4_corners_and_kinks_full", "mixed_cube", adv_probes))

    # --- MODE 4 (4 certs) ---
    # 13. 3x3 asymmetric BoS-style game certified at rho = 1/5 via stage2_kite
    certs.append(_make_mode4(
        "ne_one_fifth_kite_mix_3x3",
        _f(1, 5), "stage2_kite",
        R2, C2,
        [_f(1), _f(0), _f(0)],
        [_f(10, 11), _f(1, 11), _f(0)],
    ))

    # 14. 4x4 hard game with exact zero-slack rho = 1/5 and support (2, 2)
    R14 = [
        [_f(3, 4), _f(0), _f(1, 2), _f(1, 4)],
        [_f(1), _f(1, 2), _f(1, 4), _f(1, 2)],
        [_f(1, 2), _f(1, 4), _f(3, 5), _f(1, 5)],
        [_f(1, 4), _f(1, 2), _f(1, 5), _f(3, 5)],
    ]
    C14 = [
        [_f(1), _f(1), _f(1, 2), _f(1, 4)],
        [_f(0), _f(1), _f(1, 4), _f(1, 2)],
        [_f(1, 4), _f(1, 2), _f(1, 2), _f(1, 4)],
        [_f(1, 2), _f(1, 4), _f(1, 4), _f(1, 2)],
    ]
    # With x=(4/5, 1/5, 0, 0), y=(1, 0, 0, 0): uR = (4/5)(3/4)+(1/5)(1)=4/5, M1=1 => r1=1/5;
    # xC = (4/5, 1, 9/20, 3/10) => uC=4/5, M2=1 => r2=1/5! Let's make y have support 2 too:
    # Let y=(1,0,0,0) -> supp_y=1, or y=(9/10, 1/10, 0, 0)? Check:
    # Ry = (27/40, 19/20, 19/40, 11/40); uR = (4/5)(27/40)+(1/5)(19/20) = 27/50 + 19/100 = 73/100 -> r1 = 22/100 > 1/5.
    # Keep exact zero-slack x=(4/5, 1/5, 0, 0), y=(1, 0, 0, 0): r1 = 1/5, r2 = 1/5 (BOTH EXACTLY 1/5!).
    certs.append(_make_mode4(
        "ne_one_fifth_4x4_zero_slack",
        _f(1, 5), "stage2_kite",
        R14, C14,
        [_f(4, 5), _f(1, 5), _f(0), _f(0)],
        [_f(1), _f(0), _f(0), _f(0)],
    ))

    # 15. 5x5 structured bimatrix certified via stage3_anchored_lp (max regret <= 1/5)
    # 5x5 cyclic perturbed game with uniform mixture (1/5, ..., 1/5)
    R15 = [
        [_f(3, 5), _f(4, 5), _f(2, 5), _f(3, 5), _f(3, 5)],
        [_f(3, 5), _f(3, 5), _f(4, 5), _f(2, 5), _f(3, 5)],
        [_f(3, 5), _f(3, 5), _f(3, 5), _f(4, 5), _f(2, 5)],
        [_f(2, 5), _f(3, 5), _f(3, 5), _f(3, 5), _f(4, 5)],
        [_f(4, 5), _f(2, 5), _f(3, 5), _f(3, 5), _f(3, 5)],
    ]
    C15 = [
        [_f(4, 5), _f(3, 5), _f(2, 5), _f(3, 5), _f(1, 2)],
        [_f(1, 2), _f(4, 5), _f(3, 5), _f(2, 5), _f(3, 5)],
        [_f(3, 5), _f(1, 2), _f(4, 5), _f(3, 5), _f(2, 5)],
        [_f(2, 5), _f(3, 5), _f(1, 2), _f(4, 5), _f(3, 5)],
        [_f(3, 5), _f(2, 5), _f(3, 5), _f(1, 2), _f(4, 5)],
    ]
    # Perturb x=(1/4, 1/4, 1/6, 1/6, 1/6), y=(1/5, 1/5, 1/5, 1/5, 1/5) => Ry = (3/5,...), r1=0; xC max - uC <= 1/20 <= 1/5!
    certs.append(_make_mode4(
        "ne_one_fifth_5x5_anchored_lp",
        _f(1, 5), "stage3_anchored_lp",
        R15, C15,
        [_f(1, 4), _f(1, 4), _f(1, 6), _f(1, 6), _f(1, 6)],
        [_f(1, 5), _f(1, 5), _f(1, 5), _f(1, 5), _f(1, 5)],
    ))

    # 16. 3x3 exact Nash equilibrium (rho = 0) benchmark
    certs.append(_make_mode4(
        "ne_exact_equilibrium_3x3_rps",
        _f(1, 5), "exact_ne",
        R7, C7,
        u3, u3,
    ))

    assert len(certs) == 16
    return certs


def main() -> None:
    CERT_DIR.mkdir(parents=True, exist_ok=True)
    RES_DIR.mkdir(parents=True, exist_ok=True)

    # 1. Generate and time all 16 canonical certificates
    certs = build_all_16_certificates()
    atlas_rows: List[Dict[str, Any]] = []
    for cert in certs:
        out_path = CERT_DIR / f"{cert['cert_id']}.cert.json"
        out_path.write_text(json.dumps(cert, indent=2) + "\n", encoding="utf-8")
        # Warm-up + 7 timed runs
        summary = verify_certificate(cert)
        t0 = time.perf_counter()
        reps = 7
        for _ in range(reps):
            verify_certificate(cert)
        mean_ms = round(((time.perf_counter() - t0) * 1000.0) / reps, 3)
        atlas_rows.append({
            "cert_id": cert["cert_id"],
            "mode": cert["mode"],
            "mean_ms": mean_ms,
            "summary": summary,
        })
    (RES_DIR / "exp1_certificate_atlas.json").write_text(
        json.dumps({"count": len(atlas_rows), "certificates": atlas_rows}, indent=2) + "\n",
        encoding="utf-8",
    )

    # 2. Experiment 2: Exact rational 3D grid sweep of H(z, c1, c2) on [1/4, 4]^3 (13^3 = 2197 points)
    grid_pts = [
        _f(1, 4), _f(1, 2), _f(3, 4), _f(7, 8), _f(1), _f(9, 8), _f(5, 4),
        _f(3, 2), _f(11, 6), _f(2), _f(5, 2), _f(3), _f(4),
    ]
    slice_rows: List[Dict[str, Any]] = []
    global_max_H = Fraction(-1000, 1)
    global_argmax: List[str] = []
    for z in grid_pts:
        slice_max_H = Fraction(-1000, 1)
        slice_max_Hup = Fraction(-1000, 1)
        slice_argmax = ["", ""]
        for c1 in grid_pts:
            for c2 in grid_pts:
                ev = eval_H_full(z, c1, c2)
                if ev["H"] > slice_max_H:
                    slice_max_H = ev["H"]
                    slice_argmax = [format_exact_rat(c1), format_exact_rat(c2)]
                if ev["H_up"] > slice_max_Hup:
                    slice_max_Hup = ev["H_up"]
                if ev["H"] > global_max_H:
                    global_max_H = ev["H"]
                    global_argmax = [format_exact_rat(z), format_exact_rat(c1), format_exact_rat(c2)]
        assert slice_max_H <= STAGE4_TARGET, f"H exceeded -1/3000 at z={z}: {slice_max_H}"
        slice_rows.append({
            "z_rat": format_exact_rat(z),
            "z_val": round(z.numerator / z.denominator, 6),
            "f0_rat": format_exact_rat(eval_H_full(z, z, z)["f0"]),
            "max_H_rat": format_exact_rat(slice_max_H),
            "max_H_val": round(slice_max_H.numerator / slice_max_H.denominator, 7),
            "max_H_up_val": round(slice_max_Hup.numerator / slice_max_Hup.denominator, 7),
            "argmax_c1_c2": slice_argmax,
        })
    (RES_DIR / "exp2_stage4_H_landscape.json").write_text(
        json.dumps({
            "grid_size_per_axis": len(grid_pts),
            "total_exact_points": len(grid_pts) ** 3,
            "stage4_target_rat": "-1/3000",
            "volterra_floor_rat": "-1/16384",
            "global_max_H_rat": format_exact_rat(global_max_H),
            "global_max_H_val": round(global_max_H.numerator / global_max_H.denominator, 7),
            "global_argmax_z_c1_c2": global_argmax,
            "all_le_minus_1_3000": global_max_H <= STAGE4_TARGET,
            "slices": slice_rows,
        }, indent=2) + "\n",
        encoding="utf-8",
    )

    # 3. Experiment 3: Kite welfare cap 2 - s/(1-s) & Eq. (5.3) shifted cubic Q(f0)
    kite_curve = []
    for k in range(1, 20):
        s_q = Fraction(k, 40)
        cap_q = Fraction(2, 1) - s_q / (Fraction(1, 1) - s_q)
        kite_curve.append({
            "s_rat": format_exact_rat(s_q),
            "s_val": round(s_q.numerator / s_q.denominator, 4),
            "welfare_cap_rat": format_exact_rat(cap_q),
            "welfare_cap_val": round(cap_q.numerator / cap_q.denominator, 6),
        })
    eq53_curve = []
    for k in range(0, 21):
        f0 = Fraction(1, 1) + Fraction(k, 30)  # [1, 5/3]
        z = (Fraction(5, 1) * f0 - Fraction(1, 1)) / Fraction(4, 1)
        lhs_53 = -f0 / Fraction(128, 1) + (Fraction(5, 1) - Fraction(3, 1) * f0) * (f0 - Fraction(1, 1)) * z / (Fraction(40, 1) * f0)
        rhs_53 = Fraction(-7, 4000) / f0
        q_val = eval_Q53_rat(f0)
        assert lhs_53 < rhs_53 and q_val < 0
        eq53_curve.append({
            "f0_rat": format_exact_rat(f0),
            "f0_val": round(f0.numerator / f0.denominator, 5),
            "lhs_53_val": round(lhs_53.numerator / lhs_53.denominator, 7),
            "rhs_53_val": round(rhs_53.numerator / rhs_53.denominator, 7),
            "Q_f0_val": round(q_val.numerator / q_val.denominator, 6),
        })
    (RES_DIR / "exp3_kite_and_eq53_sweep.json").write_text(
        json.dumps({"kite_curve": kite_curve, "eq53_curve": eq53_curve}, indent=2) + "\n",
        encoding="utf-8",
    )

    # 4. Experiment 4: Historical polynomial-time eps-NE frontier & simplex rounding scaling
    frontier = [
        {"year": 2006, "authors": "DMP (2006)", "eps_rat": "1/2", "eps_val": 0.5000},
        {"year": 2007, "authors": "DMP (2007)", "eps_rat": "38197/100000", "eps_val": 0.38197},
        {"year": 2007, "authors": "BBM (2007)", "eps_rat": "36392/100000", "eps_val": 0.36392},
        {"year": 2008, "authors": "TS (2008)", "eps_rat": "3393/10000", "eps_val": 0.3393},
        {"year": 2022, "authors": "DFM (2022)", "eps_rat": "1/3", "eps_val": 0.33333},
        {"year": 2026, "authors": "Cogentic (2026)", "eps_rat": "1/5", "eps_val": 0.2000},
    ]
    rounding_rows = []
    test_p = [_f(1, 13), _f(2, 13), _f(3, 13), _f(3, 13), _f(4, 13)]
    for D in (10, 25, 50, 100, 250, 500, 1000):
        cnts = _round_largest_remainder(test_p, D)
        l1_e = l1_distance([Fraction(c, D) for c in cnts], test_p)
        bound = Fraction(len(test_p), D)
        assert l1_e <= bound
        rounding_rows.append({
            "D": D,
            "d": len(test_p),
            "l1_rat": format_exact_rat(l1_e),
            "l1_val": round(l1_e.numerator / l1_e.denominator, 6),
            "bound_val": round(bound.numerator / bound.denominator, 6),
        })
    (RES_DIR / "exp4_historical_barrier_and_rounding.json").write_text(
        json.dumps({"frontier": frontier, "rounding": rounding_rows}, indent=2) + "\n",
        encoding="utf-8",
    )

    print(f"[PASS] Generated {len(atlas_rows)} canonical {SCHEMA_VERSION} certificates and 4 exact-Q studies.")
    print(f"[PASS] 3D exact grid (2197 pts): global max H = {format_exact_rat(global_max_H)} ({round(global_max_H.numerator/global_max_H.denominator, 6)}) <= -1/3000")
    for r in atlas_rows:
        print(f"  {r['cert_id']:34s} {r['mean_ms']:6.3f} ms  ({r['mode']})")


if __name__ == "__main__":
    main()
