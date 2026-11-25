# Constructive Lean 4 Formalization and Exact-Rational Certificates for Polynomial-Time 1/5-Approximate Nash Equilibria

Independent, zero-dependency, zero-floating-point formalization and certificate verification stack for Google Research Cogentic's November 25, 2026 preprint *"An Exact Polynomial-Time Algorithm for 1/5-Approximate Nash Equilibria in Bimatrix Games"* (`MaximinKiteNE`).

- **Author:** Lluis Eriksson
- **Code, Lean 4 proofs & certificates license:** MIT
- **Manuscript & figures license:** CC-BY-4.0
- **Repository:** https://github.com/lluiseriksson/cogentic-maximin-kite-nash-certificates

## Highlights

- **Constructive Lean 4.35.0 Kernel (`lean/MaximinKiteNash.lean`):** 18 standalone theorems, 0 `sorry`, 0 `axiom`, 0 `Classical.choice` (all 18 theorems audit strictly to `[propext, Quot.sound]`).
- **Exact-$\mathbb{Q}$ Auditor (`KITE-NASH-CERT-1.0`):** Pure-stdlib Python `int` + `fractions.Fraction` across 4 modes (`kite_best_response_and_welfare_cert`, `minimax_screen_and_rounding_cert`, `stage4_H_algebraic_cert`, `bimatrix_one_fifth_ne_cert`), zero floats, strict canonical rational parsing, AST whitelist, duplicate rejection.
- **Independent Exact Stage 4 Audit:** Verified $H(z, c_1, c_2) \le -1/1280 \le -1/3000 < -2^{-14}$ across $13^3 = 2{,}197$ exact rational grid points on $[1/4, 4]^3$.
- **Canonical Atlas & Red-Team Suite:** 16 canonical certificates ($0.104$–$2.564\,\mathrm{ms}$), 64/64 pytest checks (16 canonical certs + 60 live adversarial forgeries + 3 raw JSON IEEE-754/`NaN`/duplicate-key checks), and 40-file SHA-256 manifest enforcement.

## One-Command Verification

```bash
python scripts/verify_all.py
```
