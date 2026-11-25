"""63-check pytest suite (16 canonical certs + 60 live adversarial forgery attacks + 2 raw JSON checks)
for Paper 56 (KITE-NASH-CERT-1.0).

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import copy
import json
from pathlib import Path
from typing import Any, Callable, Dict, List, Tuple

import pytest

from src.kite_certifier import (
    CertificateError,
    verify_certificate,
    verify_certificate_file,
    verify_certificate_json_text,
)

ROOT = Path(__file__).resolve().parent.parent
CERT_DIR = ROOT / "certificates"


def _load(stem: str) -> Dict[str, Any]:
    return json.loads((CERT_DIR / f"{stem}.cert.json").read_text(encoding="utf-8"))


def test_all_16_canonical_certificates_pass() -> None:
    paths = sorted(CERT_DIR.glob("*.cert.json"))
    assert len(paths) == 16
    for p in paths:
        res = verify_certificate_file(p)
        assert res["verified"] is True


def test_raw_json_rejects_ieee754_float_token() -> None:
    raw = json.dumps(_load("kite_row_mix_tight_1_5")).replace('"1/5"', "0.2", 1)
    with pytest.raises(CertificateError):
        verify_certificate_json_text(raw)


def test_raw_json_rejects_nan_infinity() -> None:
    raw = '{"schema": "KITE-NASH-CERT-1.0", "mode": "stage4_H_algebraic_cert", "cert_id": "x", "claimed_probe_count": NaN}'
    with pytest.raises(CertificateError):
        verify_certificate_json_text(raw)


def test_raw_json_rejects_duplicate_keys() -> None:
    raw = '{"schema": "KITE-NASH-CERT-1.0", "schema": "KITE-NASH-CERT-1.0", "mode": "stage4_H_algebraic_cert", "cert_id": "x"}'
    with pytest.raises(CertificateError):
        verify_certificate_json_text(raw)


def _build_60_attacks() -> List[Tuple[str, Callable[[], Dict[str, Any]]]]:
    m1_in = _load("kite_row_mix_tight_1_5")
    m1_esc = _load("kite_escape_welfare_7_4_cap")
    m2_h = _load("minimax_early_halt_diag_1_6")
    m2_c = _load("minimax_anchored_continue_rps")
    m3_lo = _load("stage4_low_gate_grid_z_le_1")
    m3_mid = _load("stage4_high_gate_mid_1_to_2")
    m4 = _load("ne_one_fifth_4x4_zero_slack")

    def mod(base: Dict[str, Any], fn: Callable[[Dict[str, Any]], None]) -> Callable[[], Dict[str, Any]]:
        def _run() -> Dict[str, Any]:
            c = copy.deepcopy(base)
            fn(c)
            return c
        return _run

    attacks: List[Tuple[str, Callable[[], Dict[str, Any]]]] = [
        # --- 10 Schema / Parser / AST Attacks ---
        ("S01_wrong_schema", mod(m1_in, lambda c: c.__setitem__("schema", "KITE-NASH-CERT-0.9"))),
        ("S02_unknown_mode", mod(m1_in, lambda c: c.__setitem__("mode", "bogus_mode"))),
        ("S03_empty_cert_id", mod(m1_in, lambda c: c.__setitem__("cert_id", "   "))),
        ("S04_non_reduced_rat", mod(m1_in, lambda c: c.__setitem__("s_kite", "2/10"))),
        ("S05_leading_zero_rat", mod(m1_in, lambda c: c.__setitem__("s_kite", "01/5"))),
        ("S06_negative_zero_rat", mod(m1_in, lambda c: c.__setitem__("claimed_r2", "-0"))),
        ("S07_plus_sign_rat", mod(m1_in, lambda c: c.__setitem__("s_kite", "+1/5"))),
        ("S08_unicode_digit_rat", mod(m1_in, lambda c: c.__setitem__("s_kite", "١/5"))),
        ("S09_int_in_rat_field", mod(m1_in, lambda c: c.__setitem__("claimed_r2", 0))),
        ("S10_bool_in_int_field", mod(m1_in, lambda c: c.__setitem__("best_response_idx", True))),

        # --- 14 Mode 1 (s-Kite Mixing & Welfare Cap) Forgeries ---
        ("M1_01_s_ge_half", mod(m1_in, lambda c: c.__setitem__("s_kite", "1/2"))),
        ("M1_02_payoff_gt_1", mod(m1_in, lambda c: c["R"][0].__setitem__(0, "6/5"))),
        ("M1_03_payoff_neg", mod(m1_in, lambda c: c["C"][0].__setitem__(0, "-1/10"))),
        ("M1_04_x_not_simplex", mod(m1_in, lambda c: c.__setitem__("x", ["1/2", "1/3"]))),
        ("M1_05_x_neg_prob", mod(m1_in, lambda c: c.__setitem__("x", ["2", "-1"]))),
        ("M1_06_forged_uR", mod(m1_in, lambda c: c.__setitem__("claimed_uR", "4/5"))),
        ("M1_07_forged_r1", mod(m1_in, lambda c: c.__setitem__("claimed_r1", "1/5"))),
        ("M1_08_wrong_br_idx", mod(m1_in, lambda c: c.__setitem__("best_response_idx", 0))),
        ("M1_09_wrong_x_out", mod(m1_in, lambda c: c.__setitem__("x_out", ["1/2", "1/2"]))),
        ("M1_10_forged_out_regret", mod(m1_in, lambda c: c.__setitem__("claimed_output_regret", "0"))),
        ("M1_11_escape_claimed_in_kite", mod(m1_esc, lambda c: c.__setitem__("branch", "in_kite"))),
        ("M1_12_in_kite_claimed_escape", mod(m1_in, lambda c: c.__setitem__("branch", "escaped_welfare_cap"))),
        ("M1_13_bad_dual_sum", mod(m1_esc, lambda c: c.__setitem__("dual_theta1", "1/2"))),
        ("M1_14_dual_sep_fails_single_face", mod(m1_esc, lambda c: (
            c["R"][0].__setitem__(0, "7/10"),
            c["C"][0].__setitem__(0, "9/10"),
            c.__setitem__("claimed_uC", "9/10"),
            c.__setitem__("claimed_r2", "1/10"),
            c.__setitem__("claimed_welfare", "8/5"),
            c.__setitem__("dual_theta1", "0"),
            c.__setitem__("dual_theta2", "1"),
            c.__setitem__("claimed_dual_lambda", "4/5"),
            c.__setitem__("claimed_dual_ratio", "4"),
        ))),

        # --- 14 Mode 2 (Minimax Screen & Simplex Rounding) Forgeries ---
        ("M2_01_forged_vR_high", mod(m2_h, lambda c: c.__setitem__("claimed_vR", "1/5"))),
        ("M2_02_forged_vR_low", mod(m2_h, lambda c: c.__setitem__("claimed_vR", "1/10"))),
        ("M2_03_forged_vC", mod(m2_h, lambda c: c.__setitem__("claimed_vC", "3/4"))),
        ("M2_04_bad_denom_zero", mod(m2_h, lambda c: c.__setitem__("denom_D", 0))),
        ("M2_05_counts_wrong_sum", mod(m2_h, lambda c: c["rounded_counts"].__setitem__(0, 0))),
        ("M2_06_counts_not_floor_ceil", mod(m2_h, lambda c: c.__setitem__("rounded_counts", [0, 0, 24]))),
        ("M2_07_forged_rem_r", mod(m2_h, lambda c: c.__setitem__("claimed_remainder_r", 0))),
        ("M2_08_forged_l1_err", mod(m2_h, lambda c: c.__setitem__("claimed_l1_error", "0"))),
        ("M2_09_early_halt_high_regret", mod(m2_h, lambda c: (c.__setitem__("halt_x", ["0", "1", "0"]), c.__setitem__("halt_y", ["1", "0", "0"])))),
        ("M2_10_early_halt_on_high_v", mod(m2_c, lambda c: c.__setitem__("claimed_screen_outcome", "early_halt"))),
        ("M2_11_continue_on_low_v", mod(m2_h, lambda c: c.__setitem__("claimed_screen_outcome", "anchored_continue"))),
        ("M2_12_bad_x_tilde", mod(m2_c, lambda c: c.__setitem__("x_tilde", ["1", "0", "0"]))),
        ("M2_13_forged_anchor_floor", mod(m2_c, lambda c: c.__setitem__("claimed_anchor_floor", "1/2"))),
        ("M2_14_unknown_outcome", mod(m2_c, lambda c: c.__setitem__("claimed_screen_outcome", "abort"))),

        # --- 12 Mode 3 (Stage 4 H(z, c1, c2) <= -1/3000) Forgeries ---
        ("M3_01_unknown_regime", mod(m3_lo, lambda c: c.__setitem__("regime", "invalid_regime"))),
        ("M3_02_empty_probes", mod(m3_lo, lambda c: c.__setitem__("probes", []))),
        ("M3_03_z_below_1_4", mod(m3_lo, lambda c: c["probes"].__setitem__(0, ["1/5", "1", "1"]))),
        ("M3_04_c1_above_4", mod(m3_lo, lambda c: c["probes"].__setitem__(0, ["1/2", "9/2", "1"]))),
        ("M3_05_regime_z_violation_lo", mod(m3_lo, lambda c: c["probes"].__setitem__(0, ["3/2", "1", "1"]))),
        ("M3_06_regime_z_violation_mid", mod(m3_mid, lambda c: c["probes"].__setitem__(0, ["1", "1", "1"]))),
        ("M3_07_duplicate_probe", mod(m3_lo, lambda c: c["probes"].__setitem__(1, c["probes"][0]))),
        ("M3_08_forged_probe_count", mod(m3_lo, lambda c: c.__setitem__("claimed_probe_count", 11))),
        ("M3_09_forged_worst_idx", mod(m3_lo, lambda c: c.__setitem__("claimed_worst_probe_idx", 0 if m3_lo["claimed_worst_probe_idx"] != 0 else 1))),
        ("M3_10_forged_max_H", mod(m3_lo, lambda c: c.__setitem__("claimed_max_H", "-1/3000"))),
        ("M3_11_forged_margin_3000", mod(m3_lo, lambda c: c.__setitem__("claimed_margin_to_minus_1_3000", "0"))),
        ("M3_12_forged_gap_volterra", mod(m3_lo, lambda c: c.__setitem__("claimed_gap_to_volterra_floor", "1/1000"))),

        # --- 10 Mode 4 (End-to-End 1/5-NE Bimatrix) Forgeries ---
        ("M4_01_eps_above_1_5", mod(m4, lambda c: c.__setitem__("eps_target", "1/3"))),
        ("M4_02_eps_zero", mod(m4, lambda c: c.__setitem__("eps_target", "0"))),
        ("M4_03_unknown_stage", mod(m4, lambda c: c.__setitem__("construction_stage", "heuristic"))),
        ("M4_04_regret_exceeds_eps", mod(m4, lambda c: c.__setitem__("x", ["1", "0", "0", "0"]))),
        ("M4_05_exact_ne_with_pos_regret", mod(m4, lambda c: c.__setitem__("construction_stage", "exact_ne"))),
        ("M4_06_ragged_matrix", mod(m4, lambda c: c["R"][0].pop())),
        ("M4_07_forged_max_regret", mod(m4, lambda c: c.__setitem__("claimed_max_regret", "1/10"))),
        ("M4_08_forged_supp_x", mod(m4, lambda c: c.__setitem__("claimed_supp_x", 1))),
        ("M4_09_forged_supp_y", mod(m4, lambda c: c.__setitem__("claimed_supp_y", 2))),
        ("M4_10_forged_lcm_denom", mod(m4, lambda c: c.__setitem__("claimed_lcm_denom", 1))),
    ]
    assert len(attacks) == 60
    return attacks


@pytest.mark.parametrize("name,builder", _build_60_attacks(), ids=[a[0] for a in _build_60_attacks()])
def test_live_adversarial_forgery_rejected(name: str, builder: Callable[[], Dict[str, Any]]) -> None:
    forged = builder()
    with pytest.raises(CertificateError):
        verify_certificate(forged)
