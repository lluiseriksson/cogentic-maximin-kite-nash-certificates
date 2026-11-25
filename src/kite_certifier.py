"""Pure-stdlib, zero-floating-point exact-Q certificate auditor for Paper 56:
KITE-NASH-CERT-1.0 (Google Research Cogentic, Nov. 25, 2026, MaximinKiteNE).

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, List, Set, Tuple

from .kite_exact import (
    bimatrix_regrets,
    dot_vec,
    eval_H_full,
    eval_Q53_rat,
    format_exact_rat,
    l1_distance,
    mat_vec,
    parse_exact_rat,
    simplex_round_floor,
    vec_mat,
)

SCHEMA_VERSION = "KITE-NASH-CERT-1.0"
MAX_NESTING_DEPTH = 20
STAGE4_TARGET = Fraction(-1, 3000)
VOLTERRA_FLOOR = Fraction(-1, 16384)  # -2^{-14}


class CertificateError(ValueError):
    """Raised whenever a KITE-NASH-CERT-1.0 certificate fails exact validation."""


def _gcd_int(a: int, b: int) -> int:
    a, b = abs(a), abs(b)
    while b:
        a, b = b, a % b
    return a


def _lcm_int(a: int, b: int) -> int:
    if a == 0 or b == 0:
        return 0
    return abs(a * b) // _gcd_int(a, b)


def _guard_json_ast(obj: Any, depth: int = 0) -> None:
    if depth > MAX_NESTING_DEPTH:
        raise CertificateError(f"Nesting depth exceeded {MAX_NESTING_DEPTH}")
    if obj is None or type(obj) in (bool, int, str):
        return
    if type(obj) is list:
        for item in obj:
            _guard_json_ast(item, depth + 1)
        return
    if type(obj) is dict:
        for k, v in obj.items():
            if type(k) is not str:
                raise CertificateError("All JSON object keys must be strings")
            _guard_json_ast(v, depth + 1)
        return
    raise CertificateError(f"Unsupported or non-exact JSON type: {type(obj).__name__}")


def _strict_int(val: Any, label: str) -> int:
    if isinstance(val, bool) or not isinstance(val, int):
        raise CertificateError(f"{label}: expected strict integer")
    return val


def _parse_rat(val: Any, label: str) -> Fraction:
    try:
        return parse_exact_rat(val, label)
    except ValueError as exc:
        raise CertificateError(str(exc)) from exc


def _parse_simplex(raw: Any, expected_len: int, label: str) -> List[Fraction]:
    if not isinstance(raw, list) or len(raw) != expected_len:
        raise CertificateError(f"{label}: expected list of length {expected_len}")
    vec = [_parse_rat(v, f"{label}[{i}]") for i, v in enumerate(raw)]
    if any(v < 0 for v in vec):
        raise CertificateError(f"{label}: negative probability entry")
    if sum(vec, Fraction(0, 1)) != Fraction(1, 1):
        raise CertificateError(f"{label}: entries must sum exactly to 1")
    return vec


def _parse_payoff_matrix(raw: Any, label: str) -> Tuple[List[List[Fraction]], int, int]:
    if not isinstance(raw, list) or not raw:
        raise CertificateError(f"{label}: payoff matrix must be non-empty")
    m = len(raw)
    if not isinstance(raw[0], list) or not raw[0]:
        raise CertificateError(f"{label}[0]: matrix row must be non-empty")
    n = len(raw[0])
    mat: List[List[Fraction]] = []
    for i, row in enumerate(raw):
        if not isinstance(row, list) or len(row) != n:
            raise CertificateError(f"{label}[{i}]: ragged matrix row")
        parsed_row: List[Fraction] = []
        for j, entry in enumerate(row):
            q = _parse_rat(entry, f"{label}[{i}][{j}]")
            if q < 0 or q > 1:
                raise CertificateError(f"{label}[{i}][{j}]: payoff {q} outside [0, 1]")
            parsed_row.append(q)
        mat.append(parsed_row)
    return mat, m, n


def _check_claimed_rat(payload: Dict[str, Any], key: str, actual: Fraction) -> None:
    if key not in payload:
        raise CertificateError(f"Missing required claimed field '{key}'")
    claimed = _parse_rat(payload[key], key)
    if claimed != actual:
        raise CertificateError(
            f"Claimed {key}={format_exact_rat(claimed)} != exact {format_exact_rat(actual)}"
        )


def _verify_mode1(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 1: Exact Lem. 2.3 s-kite best-response mixing & primal-dual welfare cap."""
    s = _parse_rat(payload.get("s_kite"), "s_kite")
    if not (Fraction(0, 1) < s < Fraction(1, 2)):
        raise CertificateError(f"s_kite must lie strictly in (0, 1/2), got {s}")
    R, m, n = _parse_payoff_matrix(payload.get("R"), "R")
    C, mC, nC = _parse_payoff_matrix(payload.get("C"), "C")
    if (m, n) != (mC, nC):
        raise CertificateError("Payoff matrices R and C must have identical dimensions")
    x = _parse_simplex(payload.get("x"), m, "x")
    y = _parse_simplex(payload.get("y"), n, "y")

    reg = bimatrix_regrets(R, C, x, y)
    uR, uC, r1, r2 = reg["uR"], reg["uC"], reg["r1"], reg["r2"]
    welfare = uR + uC
    lhs_row = (Fraction(1, 1) - s) * r1 + s * r2
    lhs_col = s * r1 + (Fraction(1, 1) - s) * r2

    _check_claimed_rat(payload, "claimed_uR", uR)
    _check_claimed_rat(payload, "claimed_uC", uC)
    _check_claimed_rat(payload, "claimed_r1", r1)
    _check_claimed_rat(payload, "claimed_r2", r2)
    _check_claimed_rat(payload, "claimed_welfare", welfare)

    branch = payload.get("branch")
    if branch == "in_kite":
        if lhs_row > s or lhs_col > s:
            raise CertificateError("in_kite branch requires (1-s)r1 + s*r2 <= s and s*r1 + (1-s)r2 <= s")
        x_out = _parse_simplex(payload.get("x_out"), m, "x_out")
        y_out = _parse_simplex(payload.get("y_out"), n, "y_out")
        # Verify canonical Lem. 2.3(a) mixing construction
        if r1 > s:
            theta = (r1 - s) / r1
            i_star = _strict_int(payload.get("best_response_idx"), "best_response_idx")
            if not (0 <= i_star < m):
                raise CertificateError("best_response_idx out of range for Row")
            Ry = mat_vec(R, y)
            if Ry[i_star] != reg["M1"]:
                raise CertificateError("best_response_idx is not an exact pure best response for Row")
            expected_x = [
                (Fraction(1, 1) - theta) * x[i] + (theta if i == i_star else Fraction(0, 1))
                for i in range(m)
            ]
            if x_out != expected_x or y_out != y:
                raise CertificateError("x_out/y_out do not match exact Lem. 2.3(a) row mixing formula")
        elif r2 > s:
            theta = (r2 - s) / r2
            j_star = _strict_int(payload.get("best_response_idx"), "best_response_idx")
            if not (0 <= j_star < n):
                raise CertificateError("best_response_idx out of range for Column")
            xC = vec_mat(x, C)
            if xC[j_star] != reg["M2"]:
                raise CertificateError("best_response_idx is not an exact pure best response for Column")
            expected_y = [
                (Fraction(1, 1) - theta) * y[j] + (theta if j == j_star else Fraction(0, 1))
                for j in range(n)
            ]
            if y_out != expected_y or x_out != x:
                raise CertificateError("x_out/y_out do not match exact Lem. 2.3(a) column mixing formula")
        else:
            if x_out != x or y_out != y:
                raise CertificateError("When max(r1,r2) <= s, output pair must equal (x, y)")
        out_reg = bimatrix_regrets(R, C, x_out, y_out)
        if out_reg["max_regret"] > s:
            raise CertificateError(f"Output strategy max regret {out_reg['max_regret']} exceeds s={s}")
        _check_claimed_rat(payload, "claimed_output_regret", out_reg["max_regret"])
        return {
            "verified": True,
            "mode": payload["mode"],
            "cert_id": payload["cert_id"],
            "branch": branch,
            "s_kite": format_exact_rat(s),
            "r1": format_exact_rat(r1),
            "r2": format_exact_rat(r2),
            "welfare": format_exact_rat(welfare),
            "output_regret": format_exact_rat(out_reg["max_regret"]),
        }

    if branch == "escaped_welfare_cap":
        if not (lhs_row > s or lhs_col > s):
            raise CertificateError("escaped_welfare_cap branch requires escaping at least one s-kite inequality")
        welfare_cap = Fraction(2, 1) - s / (Fraction(1, 1) - s)
        if not (welfare < welfare_cap):
            raise CertificateError(f"Welfare {welfare} failed strict cap < {welfare_cap}")
        t1 = _parse_rat(payload.get("dual_theta1"), "dual_theta1")
        t2 = _parse_rat(payload.get("dual_theta2"), "dual_theta2")
        if t1 < 0 or t2 < 0 or (t1 + t2) != Fraction(1, 1):
            raise CertificateError("dual_theta1, dual_theta2 must be nonnegative and sum to 1")
        lam_star = s * t1 + (Fraction(1, 1) - s) * t2
        if not (s <= lam_star <= Fraction(1, 1) - s):
            raise CertificateError("Dual multiplier lambda* out of [s, 1-s]")
        dual_ratio = lam_star / (Fraction(1, 1) - lam_star)
        lo_ratio = s / (Fraction(1, 1) - s)
        hi_ratio = (Fraction(1, 1) - s) / s
        if not (lo_ratio <= dual_ratio <= hi_ratio):
            raise CertificateError("Dual weight ratio a = lambda*/(1-lambda*) out of [s/(1-s), (1-s)/s]")
        # Cogentic Lem. 2.3(b) dual LP (D): theta1 weights Row face (1-s)r1 + s*r2,
        # theta2 weights Column face s*r1 + (1-s)r2, so lambda* = s*theta1 + (1-s)*theta2 gives
        # theta1 * lhs_row + theta2 * lhs_col = (1 - lambda*) * r1 + lambda* * r2 > s.
        dual_sep = t1 * lhs_row + t2 * lhs_col
        if not (dual_sep > s):
            raise CertificateError(f"Dual multipliers (theta1, theta2) fail strict separation: {dual_sep} <= {s}")
        _check_claimed_rat(payload, "claimed_welfare_cap", welfare_cap)
        _check_claimed_rat(payload, "claimed_dual_lambda", lam_star)
        _check_claimed_rat(payload, "claimed_dual_ratio", dual_ratio)
        return {
            "verified": True,
            "mode": payload["mode"],
            "cert_id": payload["cert_id"],
            "branch": branch,
            "s_kite": format_exact_rat(s),
            "welfare": format_exact_rat(welfare),
            "welfare_cap": format_exact_rat(welfare_cap),
            "dual_lambda": format_exact_rat(lam_star),
            "dual_ratio": format_exact_rat(dual_ratio),
        }

    raise CertificateError(f"Unknown Mode 1 branch: {branch!r}")


def _verify_mode2(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 2: Exact Lem. 2.2 zero-sum minimax screen & Lem. 2.1(b) denominator-D simplex rounding."""
    s = _parse_rat(payload.get("s_kite"), "s_kite")
    if not (Fraction(0, 1) < s < Fraction(1, 2)):
        raise CertificateError(f"s_kite must lie in (0, 1/2), got {s}")
    R, m, n = _parse_payoff_matrix(payload.get("R"), "R")
    C, mC, nC = _parse_payoff_matrix(payload.get("C"), "C")
    if (m, n) != (mC, nC):
        raise CertificateError("Payoff matrices R and C must have identical dimensions")

    x_mm = _parse_simplex(payload.get("x_mm"), m, "x_mm")
    y_mm = _parse_simplex(payload.get("y_mm"), n, "y_mm")
    vR = _parse_rat(payload.get("claimed_vR"), "claimed_vR")
    # Exact saddle-point optimality for zero-sum game R:
    # min_j (x_mm^T R)_j >= vR >= max_i (R y_mm)_i
    xR = vec_mat(x_mm, R)
    Ry = mat_vec(R, y_mm)
    if min(xR) < vR or max(Ry) > vR:
        raise CertificateError(
            f"Zero-sum R saddle-point failed: min(x_mm^T R)={min(xR)}, max(R y_mm)={max(Ry)}, vR={vR}"
        )

    x_col_br = _parse_simplex(payload.get("x_col_guard"), m, "x_col_guard")
    y_col_mm = _parse_simplex(payload.get("y_col_mm"), n, "y_col_mm")
    vC = _parse_rat(payload.get("claimed_vC"), "claimed_vC")
    # Exact saddle-point optimality for zero-sum game C (Column maximizes, Row minimizes):
    # min_i (C y_col_mm)_i >= vC >= max_j (x_col_guard^T C)_j
    Cy = mat_vec(C, y_col_mm)
    xC = vec_mat(x_col_br, C)
    if min(Cy) < vC or max(xC) > vC:
        raise CertificateError(
            f"Zero-sum C saddle-point failed: min(C y_col_mm)={min(Cy)}, max(x_col_guard^T C)={max(xC)}, vC={vC}"
        )

    # Denominator-D simplex rounding audit (Lem. 2.1(b))
    p_raw = payload.get("round_target_p")
    if not isinstance(p_raw, list) or not p_raw:
        raise CertificateError("round_target_p must be a non-empty simplex vector")
    d_round = len(p_raw)
    p_vec = _parse_simplex(p_raw, d_round, "round_target_p")
    D = _strict_int(payload.get("denom_D"), "denom_D")
    if D <= 0:
        raise CertificateError("denom_D must be a positive integer")
    counts_raw = payload.get("rounded_counts")
    if not isinstance(counts_raw, list) or len(counts_raw) != d_round:
        raise CertificateError("rounded_counts must match length of round_target_p")
    counts = [_strict_int(c, f"rounded_counts[{k}]") for k, c in enumerate(counts_raw)]
    if any(c < 0 for c in counts) or sum(counts) != D:
        raise CertificateError("rounded_counts must be nonnegative integers summing to denom_D")
    qs, _rems, rem_r = simplex_round_floor(p_vec, D)
    if not (0 <= rem_r < d_round):
        raise CertificateError("Internal remainder range violation")
    for k in range(d_round):
        if counts[k] not in (qs[k], qs[k] + 1):
            raise CertificateError(f"rounded_counts[{k}]={counts[k]} not in {{floor, floor+1}}={{{qs[k]}, {qs[k]+1}}}")
    p_hat = [Fraction(c, D) for c in counts]
    l1_err = l1_distance(p_hat, p_vec)
    if l1_err > Fraction(d_round, D):
        raise CertificateError(f"Rounding L1 error {l1_err} exceeds d/D={Fraction(d_round, D)}")
    if _strict_int(payload.get("claimed_remainder_r"), "claimed_remainder_r") != rem_r:
        raise CertificateError("claimed_remainder_r mismatch")
    _check_claimed_rat(payload, "claimed_l1_error", l1_err)

    outcome = payload.get("claimed_screen_outcome")
    if outcome == "early_halt":
        if not (vR <= s and vC <= s):
            raise CertificateError("early_halt requires max(vR, vC) <= s (both vR <= s and vC <= s)")
        # Check exact Lem. 2.2 minimax early-halt pair (halt_x, halt_y) == (x_col_guard, y_mm)
        x_h = _parse_simplex(payload.get("halt_x"), m, "halt_x")
        y_h = _parse_simplex(payload.get("halt_y"), n, "halt_y")
        if x_h != x_col_br or y_h != y_mm:
            raise CertificateError("early_halt pair (halt_x, halt_y) must equal minimax profile (x_col_guard, y_mm)")
        h_reg = bimatrix_regrets(R, C, x_h, y_h)
        if h_reg["max_regret"] > s:
            raise CertificateError(f"Early-halt pair max regret {h_reg['max_regret']} exceeds s={s}")
        _check_claimed_rat(payload, "claimed_halt_regret", h_reg["max_regret"])
        return {
            "verified": True,
            "mode": payload["mode"],
            "cert_id": payload["cert_id"],
            "screen_outcome": outcome,
            "vR": format_exact_rat(vR),
            "vC": format_exact_rat(vC),
            "l1_error": format_exact_rat(l1_err),
            "remainder_r": rem_r,
            "halt_regret": format_exact_rat(h_reg["max_regret"]),
        }

    if outcome == "anchored_continue":
        if not (vR > s and vR >= vC):
            raise CertificateError("anchored_continue (Row-oriented after Step 2) requires vR > s and vR >= vC")
        x_bar = _parse_simplex(payload.get("x_bar"), m, "x_bar")
        x_tilde = _parse_simplex(payload.get("x_tilde"), m, "x_tilde")
        expected_tilde = [Fraction(1, 4) * x_mm[i] + Fraction(3, 4) * x_bar[i] for i in range(m)]
        if x_tilde != expected_tilde:
            raise CertificateError("x_tilde does not equal (1/4) x_mm + (3/4) x_bar")
        floor_actual = min(vec_mat(x_tilde, R))
        guaranteed_lb = vR / Fraction(4, 1)
        if floor_actual < guaranteed_lb or guaranteed_lb <= s / Fraction(4, 1):
            raise CertificateError("Anchored query payoff floor failed vR/4 > s/4")
        _check_claimed_rat(payload, "claimed_anchor_floor", floor_actual)
        return {
            "verified": True,
            "mode": payload["mode"],
            "cert_id": payload["cert_id"],
            "screen_outcome": outcome,
            "vR": format_exact_rat(vR),
            "vC": format_exact_rat(vC),
            "l1_error": format_exact_rat(l1_err),
            "remainder_r": rem_r,
            "anchor_floor": format_exact_rat(floor_actual),
        }

    raise CertificateError(f"Unknown claimed_screen_outcome: {outcome!r}")


def _verify_mode3(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 3: Exact Section 4-5 Stage 4 H(z, c1, c2) <= -1/3000 < -2^{-14} certification."""
    regime = payload.get("regime")
    if regime not in ("low_gate_z_le_1", "high_gate_mid_1_to_2", "high_gate_top_2_to_4", "mixed_cube"):
        raise CertificateError(f"Unknown Mode 3 regime: {regime!r}")

    probes_raw = payload.get("probes")
    if not isinstance(probes_raw, list) or not probes_raw:
        raise CertificateError("probes must be a non-empty list of [z, c1, c2] triples")

    seen: Set[Tuple[Fraction, Fraction, Fraction]] = set()
    H_vals: List[Fraction] = []
    H_up_vals: List[Fraction] = []
    for idx, triple in enumerate(probes_raw):
        if not isinstance(triple, list) or len(triple) != 3:
            raise CertificateError(f"probes[{idx}]: must be [z, c1, c2]")
        z = _parse_rat(triple[0], f"probes[{idx}].z")
        c1 = _parse_rat(triple[1], f"probes[{idx}].c1")
        c2 = _parse_rat(triple[2], f"probes[{idx}].c2")
        for nm, q in (("z", z), ("c1", c1), ("c2", c2)):
            if not (Fraction(1, 4) <= q <= Fraction(4, 1)):
                raise CertificateError(f"probes[{idx}].{nm}={q} outside [1/4, 4]")
        if regime == "low_gate_z_le_1" and z > Fraction(1, 1):
            raise CertificateError(f"probes[{idx}].z={z} violates low_gate_z_le_1")
        if regime == "high_gate_mid_1_to_2" and not (Fraction(1, 1) < z <= Fraction(2, 1)):
            raise CertificateError(f"probes[{idx}].z={z} violates high_gate_mid_1_to_2")
        if regime == "high_gate_top_2_to_4" and not (Fraction(2, 1) < z <= Fraction(4, 1)):
            raise CertificateError(f"probes[{idx}].z={z} violates high_gate_top_2_to_4")
        key = (z, c1, c2)
        if key in seen:
            raise CertificateError(f"Duplicate probe triple at index {idx}")
        seen.add(key)

        ev = eval_H_full(z, c1, c2)
        # Verify Prop. 4.1(1) J <= J_mid and equality when A*B >= 0
        if ev["J"] > ev["J_mid"]:
            raise CertificateError(f"Probe {idx}: J > J_mid violated")
        if ev["A"] * ev["B"] >= 0 and ev["J"] != ev["J_mid"]:
            raise CertificateError(f"Probe {idx}: J != J_mid when AB >= 0")
        # Verify Lem. 5.1(2) Eq. (5.1) H <= H_up = G_mid + h_comb + E_var
        if ev["H_up"] != ev["G_mid"] + ev["h_comb"] + ev["E_var"]:
            raise CertificateError(f"Probe {idx}: H_up decomposition mismatch")
        if ev["H"] > ev["H_up"]:
            raise CertificateError(f"Probe {idx}: H > H_up violated")
        # Verify strict Stage 4 bound H <= -1/3000 < -2^{-14}
        if ev["H"] > STAGE4_TARGET:
            raise CertificateError(f"Probe {idx}: H={ev['H']} exceeds -1/3000")
        if not (ev["H"] < VOLTERRA_FLOOR):
            raise CertificateError(f"Probe {idx}: H={ev['H']} not strictly below -2^{-14}")
        # Regime-specific Lean-matched structural invariants
        f0 = ev["f0"]
        if z <= Fraction(1, 1):
            lhs_57 = Fraction(21, 1) * (Fraction(17, 1) * (z - c2) ** 2 + Fraction(4, 1) * c2 ** 2)
            rhs_57 = (Fraction(21, 1) * c2 - Fraction(17, 1) * z) ** 2 + Fraction(68, 1) * z ** 2
            if lhs_57 != rhs_57:
                raise CertificateError(f"Probe {idx}: Eq. (5.7) square completion identity failed")
        if Fraction(1, 1) <= z <= Fraction(2, 1):
            if not (f0 * (Fraction(2, 1) - z) <= f0 <= z <= f0 * z):
                raise CertificateError(f"Probe {idx}: High-gate breakpoint order failed")
            if f0 <= Fraction(5, 3):
                # Eq. (5.3) check: -f0/128 + (5-3f0)(f0-1)z / (40 f0) < -7/(4000 f0)
                lhs_53 = -f0 / Fraction(128, 1) + (Fraction(5, 1) - Fraction(3, 1) * f0) * (f0 - Fraction(1, 1)) * z / (Fraction(40, 1) * f0)
                if not (lhs_53 < Fraction(-7, 4000) / f0):
                    raise CertificateError(f"Probe {idx}: Eq. (5.3) negative drift bound failed")
                if not (eval_Q53_rat(f0) < Fraction(0, 1)):
                    raise CertificateError(f"Probe {idx}: Q(f0) >= 0 on [1, 5/3]")
        H_vals.append(ev["H"])
        H_up_vals.append(ev["H_up"])

    max_H = max(H_vals)
    min_H = min(H_vals)
    worst_idx = H_vals.index(max_H)
    margin_3000 = STAGE4_TARGET - max_H
    gap_volterra = VOLTERRA_FLOOR - max_H

    if _strict_int(payload.get("claimed_probe_count"), "claimed_probe_count") != len(H_vals):
        raise CertificateError("claimed_probe_count mismatch")
    if _strict_int(payload.get("claimed_worst_probe_idx"), "claimed_worst_probe_idx") != worst_idx:
        raise CertificateError("claimed_worst_probe_idx mismatch")
    _check_claimed_rat(payload, "claimed_max_H", max_H)
    _check_claimed_rat(payload, "claimed_min_H", min_H)
    _check_claimed_rat(payload, "claimed_margin_to_minus_1_3000", margin_3000)
    _check_claimed_rat(payload, "claimed_gap_to_volterra_floor", gap_volterra)

    return {
        "verified": True,
        "mode": payload["mode"],
        "cert_id": payload["cert_id"],
        "regime": regime,
        "probe_count": len(H_vals),
        "max_H": format_exact_rat(max_H),
        "min_H": format_exact_rat(min_H),
        "margin_to_minus_1_3000": format_exact_rat(margin_3000),
        "gap_to_volterra_floor": format_exact_rat(gap_volterra),
    }


def _verify_mode4(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 4: End-to-end exact rational 1/5-approximate Nash equilibrium certificate."""
    R, m, n = _parse_payoff_matrix(payload.get("R"), "R")
    C, mC, nC = _parse_payoff_matrix(payload.get("C"), "C")
    if (m, n) != (mC, nC):
        raise CertificateError("Payoff matrices R and C must have identical dimensions")
    eps = _parse_rat(payload.get("eps_target"), "eps_target")
    if not (Fraction(0, 1) < eps <= Fraction(1, 5)):
        raise CertificateError(f"eps_target must satisfy 0 < eps <= 1/5, got {eps}")
    stage = payload.get("construction_stage")
    if stage not in ("stage1_minimax", "stage2_kite", "stage3_anchored_lp", "exact_ne"):
        raise CertificateError(f"Unknown construction_stage: {stage!r}")
    x = _parse_simplex(payload.get("x"), m, "x")
    y = _parse_simplex(payload.get("y"), n, "y")

    reg = bimatrix_regrets(R, C, x, y)
    uR, uC, r1, r2, rho = reg["uR"], reg["uC"], reg["r1"], reg["r2"], reg["max_regret"]
    if rho > eps:
        raise CertificateError(f"Max regret {rho} exceeds target eps={eps}")
    if stage == "exact_ne" and rho != Fraction(0, 1):
        raise CertificateError(f"exact_ne stage requires max regret == 0, got {rho}")

    supp_x = sum(1 for v in x if v > 0)
    supp_y = sum(1 for v in y if v > 0)
    lcm_den = 1
    for v in list(x) + list(y):
        lcm_den = _lcm_int(lcm_den, v.denominator)

    _check_claimed_rat(payload, "claimed_uR", uR)
    _check_claimed_rat(payload, "claimed_uC", uC)
    _check_claimed_rat(payload, "claimed_r1", r1)
    _check_claimed_rat(payload, "claimed_r2", r2)
    _check_claimed_rat(payload, "claimed_max_regret", rho)
    if _strict_int(payload.get("claimed_supp_x"), "claimed_supp_x") != supp_x:
        raise CertificateError("claimed_supp_x mismatch")
    if _strict_int(payload.get("claimed_supp_y"), "claimed_supp_y") != supp_y:
        raise CertificateError("claimed_supp_y mismatch")
    if _strict_int(payload.get("claimed_lcm_denom"), "claimed_lcm_denom") != lcm_den:
        raise CertificateError("claimed_lcm_denom mismatch")

    return {
        "verified": True,
        "mode": payload["mode"],
        "cert_id": payload["cert_id"],
        "dims": f"{m}x{n}",
        "stage": stage,
        "eps_target": format_exact_rat(eps),
        "max_regret": format_exact_rat(rho),
        "r1": format_exact_rat(r1),
        "r2": format_exact_rat(r2),
        "supp_x": supp_x,
        "supp_y": supp_y,
        "lcm_denom": lcm_den,
    }


def verify_certificate(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Verify a parsed KITE-NASH-CERT-1.0 certificate using exact rational arithmetic."""
    _guard_json_ast(payload)
    if type(payload) is not dict:
        raise CertificateError("Certificate payload must be a JSON object")
    if payload.get("schema") != SCHEMA_VERSION:
        raise CertificateError(f"Invalid schema: expected {SCHEMA_VERSION}")
    cert_id = payload.get("cert_id")
    if type(cert_id) is not str or not cert_id.strip():
        raise CertificateError("cert_id must be a non-empty string")
    mode = payload.get("mode")
    if mode == "kite_best_response_and_welfare_cert":
        return _verify_mode1(payload)
    if mode == "minimax_screen_and_rounding_cert":
        return _verify_mode2(payload)
    if mode == "stage4_H_algebraic_cert":
        return _verify_mode3(payload)
    if mode == "bimatrix_one_fifth_ne_cert":
        return _verify_mode4(payload)
    raise CertificateError(f"Unknown verification mode: {mode!r}")


def _reject_raw_decimal(token: str) -> Any:
    raise CertificateError(f"IEEE-754 decimal token forbidden: {token}")


def _reject_raw_constant(token: str) -> Any:
    raise CertificateError(f"Non-finite JSON constant forbidden: {token}")


def _reject_dup_keys(pairs: List[Tuple[str, Any]]) -> Dict[str, Any]:
    out: Dict[str, Any] = {}
    for k, v in pairs:
        if k in out:
            raise CertificateError(f"Duplicate JSON object key forbidden: {k!r}")
        out[k] = v
    return out


def verify_certificate_json_text(text: str) -> Dict[str, Any]:
    """Parse raw JSON rejecting all IEEE-754 tokens, NaN/Infinity, and duplicate keys, then verify."""
    try:
        payload = json.loads(
            text,
            parse_float=_reject_raw_decimal,
            parse_constant=_reject_raw_constant,
            object_pairs_hook=_reject_dup_keys,
        )
    except CertificateError:
        raise
    except Exception as exc:
        raise CertificateError(f"Malformed JSON: {exc}") from exc
    return verify_certificate(payload)


def verify_certificate_file(path: Path) -> Dict[str, Any]:
    """Read and verify a certificate JSON file from disk."""
    return verify_certificate_json_text(path.read_text(encoding="utf-8"))
