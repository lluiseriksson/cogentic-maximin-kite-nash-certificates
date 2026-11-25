"""Pure-stdlib exact rational bimatrix, s-kite, minimax, simplex-rounding, and
Stage 4 H(z, c1, c2) certification engine for Paper 56 (Google Research Cogentic,
Nov. 25, 2026, MaximinKiteNE): KITE-NASH-CERT-1.0.

Zero floating-point arithmetic: uses Python int and fractions.Fraction exclusively.

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

from fractions import Fraction
from typing import Any, Dict, List, Sequence, Tuple

MAX_RAT_LEN = 2000


def parse_exact_rat(val: object, label: str = "rational") -> Fraction:
    """Parse a canonical ASCII integer or reduced 'p/q' rational string (zero floats)."""
    if isinstance(val, bool) or isinstance(val, int) or not isinstance(val, str):
        raise ValueError(f"{label}: expected canonical rational string, got {type(val).__name__}")
    s = val
    if not s or len(s) > MAX_RAT_LEN or s != s.strip():
        raise ValueError(f"{label}: invalid rational length or whitespace")
    if s in ("-0", "+0") or s.startswith("+"):
        raise ValueError(f"{label}: non-canonical sign in '{s}'")
    neg = s.startswith("-")
    body = s[1:] if neg else s
    if "/" in body:
        parts = body.split("/")
        if len(parts) != 2:
            raise ValueError(f"{label}: multiple '/' in '{s}'")
        num_s, den_s = parts
        if not (num_s and num_s.isascii() and num_s.isdigit()):
            raise ValueError(f"{label}: non-ASCII/non-digit numerator in '{s}'")
        if not (den_s and den_s.isascii() and den_s.isdigit()):
            raise ValueError(f"{label}: non-ASCII/non-digit denominator in '{s}'")
        if (len(num_s) > 1 and num_s.startswith("0")) or den_s.startswith("0"):
            raise ValueError(f"{label}: leading zero in '{s}'")
        num = int(num_s)
        den = int(den_s)
        if den <= 1:
            raise ValueError(f"{label}: denominator must be >= 2 in fraction '{s}'")
        if num == 0:
            raise ValueError(f"{label}: zero must be formatted as '0', got '{s}'")
        frac = Fraction(-num if neg else num, den)
        if frac.denominator != den:
            raise ValueError(f"{label}: fraction '{s}' is not in lowest terms")
        return frac
    if not (body and body.isascii() and body.isdigit()):
        raise ValueError(f"{label}: non-ASCII/non-digit integer in '{s}'")
    if len(body) > 1 and body.startswith("0"):
        raise ValueError(f"{label}: leading zero in '{s}'")
    num = int(body)
    if num == 0 and neg:
        raise ValueError(f"{label}: negative zero forbidden")
    return Fraction(-num if neg else num, 1)


def format_exact_rat(q: Fraction) -> str:
    """Format a Fraction as a canonical integer or lowest-terms 'p/q' string."""
    if q.denominator == 1:
        return str(q.numerator)
    return f"{q.numerator}/{q.denominator}"


def pos_part(x: Fraction) -> Fraction:
    """Return max(x, 0) exactly."""
    return x if x > 0 else Fraction(0, 1)


def mat_vec(mat: Sequence[Sequence[Fraction]], v: Sequence[Fraction]) -> List[Fraction]:
    """Exact matrix-vector product M v."""
    return [sum((row[j] * v[j] for j in range(len(v))), Fraction(0, 1)) for row in mat]


def vec_mat(u: Sequence[Fraction], mat: Sequence[Sequence[Fraction]]) -> List[Fraction]:
    """Exact row-vector-matrix product u^T M."""
    n = len(mat[0])
    return [sum((u[i] * mat[i][j] for i in range(len(u))), Fraction(0, 1)) for j in range(n)]


def dot_vec(u: Sequence[Fraction], v: Sequence[Fraction]) -> Fraction:
    """Exact inner product u^T v."""
    return sum((a * b for a, b in zip(u, v)), Fraction(0, 1))


def bimatrix_regrets(
    R: Sequence[Sequence[Fraction]],
    C: Sequence[Sequence[Fraction]],
    x: Sequence[Fraction],
    y: Sequence[Fraction],
) -> Dict[str, Any]:
    """Compute exact payoffs, pure best responses, indices, and regrets of (x, y)."""
    Ry = mat_vec(R, y)
    xC = vec_mat(x, C)
    uR = dot_vec(x, Ry)
    uC = dot_vec(xC, y)
    M1 = max(Ry)
    M2 = max(xC)
    i_star = Ry.index(M1)
    j_star = xC.index(M2)
    r1 = M1 - uR
    r2 = M2 - uC
    return {
        "uR": uR,
        "uC": uC,
        "M1": M1,
        "M2": M2,
        "i_star": i_star,
        "j_star": j_star,
        "r1": r1,
        "r2": r2,
        "max_regret": max(r1, r2),
    }


def simplex_round_floor(p: Sequence[Fraction], D: int) -> Tuple[List[int], List[Fraction], int]:
    """Compute exact floor quotients q_k = floor(D * p_k), fractional remainders f_k, and r = D - sum q_k."""
    qs: List[int] = []
    rems: List[Fraction] = []
    for pk in p:
        scaled = pk * D
        q = scaled.numerator // scaled.denominator
        qs.append(q)
        rems.append(scaled - Fraction(q, 1))
    rem_count = D - sum(qs)
    return qs, rems, rem_count


def l1_distance(u: Sequence[Fraction], v: Sequence[Fraction]) -> Fraction:
    """Exact L1 distance sum_k |u_k - v_k|."""
    return sum((abs(a - b) for a, b in zip(u, v)), Fraction(0, 1))


# --- Exact Stage 4 Functional H(z, c1, c2) (Equations 4.1-4.8 & Lemma 5.1) ---


def gate_f(z: Fraction) -> Fraction:
    """Gate function f(z) from Eq. (4.1) on [1/4, 4]."""
    if z <= Fraction(1, 1):
        return Fraction(1, 1)
    if z <= Fraction(2, 1):
        return (Fraction(4, 1) * z + Fraction(1, 1)) / Fraction(5, 1)
    return Fraction(9, 5)


def lambda_K(z: Fraction, y: Fraction) -> Fraction:
    """Kink slope multiplier lambda_K(z, y) from Eq. (4.2)."""
    f0 = gate_f(z)
    t1 = min(Fraction(1, 1), Fraction(8, 1) * pos_part(z - Fraction(7, 8)))
    t2 = Fraction(1, 1) + min(Fraction(1, 1), Fraction(4, 1) * pos_part(y - z))
    return (f0 / Fraction(128, 1)) * t1 * t2


def big_Lambda(z: Fraction, y: Fraction) -> Fraction:
    """Slope functional Lambda(z, y) from Eq. (4.3)."""
    f0 = gate_f(z)
    fz = f0 * z
    term1 = f0 / Fraction(8, 1)
    term2 = (
        Fraction(3, 1) * (y + fz)
        + pos_part(y + fz - Fraction(2, 1) * f0)
        + Fraction(4, 1) * pos_part(y - fz)
    ) / Fraction(32, 1)
    term3 = -pos_part(y - z) / Fraction(8, 1)
    term4 = -(f0 * z) / Fraction(5, 1)
    return term1 + term2 + term3 + term4 + lambda_K(z, y)


def eval_J_exact(f0: Fraction, c1: Fraction, c2: Fraction) -> Tuple[Fraction, Fraction, Fraction]:
    """Closed-form exact rational value of J(f0; c1, c2) from Lemma 5.1(1), plus (A, B)."""
    A = (c2 + f0 * c1 - Fraction(2, 1) * f0) / Fraction(2, 1)
    B = (c2 - f0 * c1) / Fraction(2, 1)
    if A <= 0 and B <= 0:
        return Fraction(0, 1), A, B
    if A >= 0 and B >= 0:
        return (c2 - f0) / Fraction(16, 1), A, B
    if A > 0 and B < 0:
        # Forces c1 > 1 since A - B = f0 * (c1 - 1) > 0
        num = (c2 + f0 * c1 - Fraction(2, 1) * f0) ** 2
        den = Fraction(64, 1) * f0 * (c1 - Fraction(1, 1))
        return num / den, A, B
    # A < 0 < B forces c1 < 1 since B - A = f0 * (1 - c1) > 0
    num = (c2 - f0 * c1) ** 2
    den = Fraction(64, 1) * f0 * (Fraction(1, 1) - c1)
    return num / den, A, B


def eval_J_mid(f0: Fraction, c1: Fraction, c2: Fraction) -> Fraction:
    """Piecewise-linear upper bound J_mid(f0; c1, c2) from Eq. (4.5)."""
    return (
        pos_part(c2 + f0 * c1 - Fraction(2, 1) * f0)
        + Fraction(2, 1) * pos_part(c2 - f0)
        + pos_part(c2 - f0 * c1)
    ) / Fraction(64, 1)


def eval_F_exact(f0: Fraction, c1: Fraction, c2: Fraction) -> Tuple[Fraction, Fraction, Fraction, Fraction, Fraction]:
    """Exact rational F(f0; c1, c2) from Eq. (4.6); returns (F, J, J_mid, A, B)."""
    J_val, A, B = eval_J_exact(f0, c1, c2)
    J_mid = eval_J_mid(f0, c1, c2)
    quad_num = (
        Fraction(3, 1) * (c2 + f0 * c1) ** 2
        + pos_part(c2 + f0 * c1 - Fraction(2, 1) * f0) ** 2
        - Fraction(4, 1) * pos_part(c2 - f0 * c1) ** 2
    )
    F_val = (
        (f0 * c1) / Fraction(8, 1)
        - c2 / Fraction(8, 1)
        + quad_num / (Fraction(64, 1) * f0)
        + J_val
        + pos_part(c2 - c1) ** 2 / Fraction(16, 1)
        - (f0 * c1 * c1) / Fraction(10, 1)
        - (c2 * c2) / Fraction(10, 1)
    )
    return F_val, J_val, J_mid, A, B


def eval_E_var(z: Fraction, c1: Fraction, c2: Fraction) -> Fraction:
    """Exact rational head-variance term E_var(z; c1, c2) from Eq. (4.7)."""
    if z <= Fraction(3, 4) and (c1 + c2) <= Fraction(2, 1):
        cube = pos_part((c1 + c2) / Fraction(2, 1) - Fraction(1, 4)) ** 3
        return min(Fraction(5, 1536), Fraction(5, 162) * cube)
    if z <= Fraction(7, 8):
        return Fraction(5, 1536)
    return (Fraction(5, 1) * gate_f(z)) / Fraction(6144, 1)


def eval_H_full(z: Fraction, c1: Fraction, c2: Fraction) -> Dict[str, Fraction]:
    """Evaluate H(z, c1, c2) (Eq. 4.8) and its Lemma 5.1(2) decomposition H_up exactly in Q."""
    f0 = gate_f(z)
    lam_K = lambda_K(z, c2)
    Lam = big_Lambda(z, c2)
    F_val, J_val, J_mid, A, B = eval_F_exact(f0, c1, c2)
    E_var = eval_E_var(z, c1, c2)
    H_val = (
        F_val
        - Lam * (c1 - z)
        - (Fraction(1, 8) - c2 / Fraction(80, 1)) * (z - c2)
        + E_var
    )
    # Lemma 5.1(2) diagonal-plus-fiber upper bound: F_up replaces J with J_mid
    F_up_c1 = F_val - J_val + J_mid
    H_up = (
        F_up_c1
        - Lam * (c1 - z)
        - (Fraction(1, 8) - c2 / Fraction(80, 1)) * (z - c2)
        + E_var
    )
    # Diagonal slice G_mid(z, c2) = H_up(z, z, c2) - E_var
    F_diag, J_diag, J_mid_diag, _, _ = eval_F_exact(f0, z, c2)
    G_mid = (F_diag - J_diag + J_mid_diag) - (Fraction(1, 8) - c2 / Fraction(80, 1)) * (z - c2)
    h_comb = (F_up_c1 - (F_diag - J_diag + J_mid_diag)) - Lam * (c1 - z)
    return {
        "f0": f0,
        "lambda_K": lam_K,
        "Lambda": Lam,
        "A": A,
        "B": B,
        "J": J_val,
        "J_mid": J_mid,
        "F": F_val,
        "E_var": E_var,
        "H": H_val,
        "G_mid": G_mid,
        "h_comb": h_comb,
        "H_up": H_up,
    }


def eval_Q53_rat(f0: Fraction) -> Fraction:
    """Evaluate shifted-cubic polynomial Q(f0) = -60 f0^3 + 167 f0^2 - 132 f0 + 20 from Eq. (5.3)."""
    return (
        Fraction(-60, 1) * f0 ** 3
        + Fraction(167, 1) * f0 ** 2
        - Fraction(132, 1) * f0
        + Fraction(20, 1)
    )
