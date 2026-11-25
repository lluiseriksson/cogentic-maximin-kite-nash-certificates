"""Generate 3 publication-quality 300-DPI figures for Paper 56 (KITE-NASH-CERT-1.0).

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parent.parent
RES_DIR = ROOT / "results"
FIG_DIR = ROOT / "paper" / "figures"

plt.rcParams.update({
    "font.family": "serif",
    "font.size": 8.5,
    "axes.titlesize": 9.0,
    "axes.labelsize": 8.5,
    "xtick.labelsize": 7.8,
    "ytick.labelsize": 7.8,
    "legend.fontsize": 7.4,
    "axes.spines.top": False,
    "axes.spines.right": False,
})


def make_fig1() -> None:
    d2 = json.loads((RES_DIR / "exp2_stage4_H_landscape.json").read_text(encoding="utf-8"))
    d3 = json.loads((RES_DIR / "exp3_kite_and_eq53_sweep.json").read_text(encoding="utf-8"))

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.0, 2.75), dpi=300)

    # Panel (a): Stage 4 exact rational negativity margin -max H(z, c1, c2) on log scale
    zs = [r["z_val"] for r in d2["slices"]]
    neg_h = [-r["max_H_val"] for r in d2["slices"]]
    neg_hup = [-r["max_H_up_val"] for r in d2["slices"]]
    ax1.semilogy(zs, neg_h, "o-", color="#1b4f72", lw=1.7, ms=4.2, label=r"Exact $-\max_{c_1,c_2} H(z,c_1,c_2)$")
    ax1.semilogy(zs, neg_hup, "s--", color="#2e86c1", lw=1.2, ms=3.2, alpha=0.85, label=r"Lem. 5.1(2) $-\max H_{\mathrm{up}}$")
    ax1.axhline(1.0 / 3000.0, color="#c0392b", lw=1.35, ls="-.", label=r"Stage 4 threshold $1/3000$")
    ax1.axhline(1.0 / 16384.0, color="#7d3c98", lw=1.25, ls=":", label=r"Volterra floor $2^{-14}$")
    ax1.axvline(1.0, color="#7f8c8d", lw=0.8, ls="--")
    ax1.axvline(2.0, color="#7f8c8d", lw=0.8, ls="--")
    ax1.fill_between([0.2, 4.1], 1.0 / 16384.0, 1.0 / 3000.0, color="#f5b7b1", alpha=0.28)
    ax1.set_xlim(0.2, 4.1)
    ax1.set_ylim(3.0e-5, 0.95)
    ax1.set_xlabel(r"Scale variable $z \in [1/4, 4]$")
    ax1.set_ylabel(r"Strict negativity margin $-H$ (log)")
    ax1.set_title(r"(a) Stage 4 Negativity Margin (2,197 $\mathbb{Q}^3$ pts)")
    ax1.grid(True, which="both", alpha=0.22)
    ax1.legend(loc="upper left", frameon=True, framealpha=0.94, fontsize=6.8)

    # Panel (b): Eq. (5.3) shifted cubic drift bound on f0 in [1, 5/3]
    f0s = [r["f0_val"] for r in d3["eq53_curve"]]
    lhs = [r["lhs_53_val"] * 1000.0 for r in d3["eq53_curve"]]
    rhs = [r["rhs_53_val"] * 1000.0 for r in d3["eq53_curve"]]
    ax2.plot(f0s, lhs, "o-", color="#117864", lw=1.7, ms=3.4, label=r"LHS of Eq. (5.3)")
    ax2.plot(f0s, rhs, "--", color="#c0392b", lw=1.4, label=r"$-7/(4000 f_0)$ bound")
    ax2.fill_between(f0s, lhs, rhs, color="#a3e4d7", alpha=0.35, label="Strict negativity gap")
    ax2.set_xlabel(r"Gate value $f_0 \in [1, 5/3]$")
    ax2.set_ylabel(r"Drift value ($\times 10^{-3}$)")
    ax2.set_title("(b) Exact Shifted-Cubic Eq. (5.3) Negativity")
    ax2.grid(True, alpha=0.25)
    ax2.legend(loc="lower left", frameon=True, framealpha=0.92)

    fig.tight_layout(pad=0.9)
    fig.savefig(FIG_DIR / "fig1_stage4_landscape_and_eq53.png", dpi=300)
    plt.close(fig)


def make_fig2() -> None:
    d3 = json.loads((RES_DIR / "exp3_kite_and_eq53_sweep.json").read_text(encoding="utf-8"))
    d4 = json.loads((RES_DIR / "exp4_historical_barrier_and_rounding.json").read_text(encoding="utf-8"))

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.0, 2.75), dpi=300)

    # Panel (a): Historical polynomial-time eps-NE frontier
    fr = d4["frontier"]
    labels = [r["authors"] for r in fr]
    vals = [r["eps_val"] for r in fr]
    colors = ["#7f8c8d", "#5d6d7e", "#2e86c1", "#2874a6", "#1f618d", "#c0392b"]
    y_pos = np.arange(len(labels))
    bars = ax1.barh(y_pos, vals, color=colors, height=0.62, edgecolor="#1c2833", lw=0.6)
    ax1.set_yticks(y_pos)
    ax1.set_yticklabels(labels)
    ax1.invert_yaxis()
    ax1.set_xlim(0.0, 0.59)
    ax1.set_xlabel(r"Additive approximation guarantee $\varepsilon$")
    ax1.set_title(r"(a) Poly-Time $\varepsilon$-NE Frontier (2006–2026)")
    for b, v in zip(bars, vals):
        ax1.text(v + 0.01, b.get_y() + b.get_height() / 2, f"{v:.4f}", va="center", fontsize=7.4)
    ax1.grid(True, axis="x", alpha=0.25)

    # Panel (b): s-kite welfare cap 2 - s/(1-s) and dual ratio window
    ss = [r["s_val"] for r in d3["kite_curve"]]
    caps = [r["welfare_cap_val"] for r in d3["kite_curve"]]
    ax2.plot(ss, caps, "-", color="#1b4f72", lw=1.8, label=r"Welfare cap $2 - \frac{s}{1-s}$")
    ax2.scatter([0.2], [1.75], color="#c0392b", s=48, zorder=5, label=r"$s=1/5 \Rightarrow X+Y < 7/4$")
    ax2.annotate(r"$(1/5,\,7/4)$", xy=(0.2, 1.75), xytext=(0.25, 1.82),
                 arrowprops=dict(arrowstyle="->", color="#c0392b", lw=1.0), fontsize=7.8, color="#c0392b")
    ax2.scatter([0.25], [5.0 / 3.0], color="#117864", s=34, zorder=5, label=r"$s=1/4 \Rightarrow X+Y < 5/3$")
    ax2.set_xlabel(r"Kite threshold $s \in (0, 1/2)$")
    ax2.set_ylabel(r"Strict welfare cap $X+Y$")
    ax2.set_title(r"(b) Lem. 2.3(b) Escaped $s$-Kite Welfare Cap")
    ax2.grid(True, alpha=0.25)
    ax2.legend(loc="lower left", frameon=True, framealpha=0.92)

    fig.tight_layout(pad=0.9)
    fig.savefig(FIG_DIR / "fig2_frontier_and_kite_cap.png", dpi=300)
    plt.close(fig)


def make_fig3() -> None:
    d1 = json.loads((RES_DIR / "exp1_certificate_atlas.json").read_text(encoding="utf-8"))
    d4 = json.loads((RES_DIR / "exp4_historical_barrier_and_rounding.json").read_text(encoding="utf-8"))

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.2, 2.75), dpi=300)

    # Panel (a): Verification latency across all 16 canonical certificates by mode
    rows = d1["certificates"]
    mode_map = {
        "kite_best_response_and_welfare_cert": ("M1: Kite/Cap", "#1b4f72"),
        "minimax_screen_and_rounding_cert": ("M2: Minimax/Rnd", "#117864"),
        "stage4_H_algebraic_cert": ("M3: Stage 4 H", "#b9770e"),
        "bimatrix_one_fifth_ne_cert": ("M4: 1/5-NE", "#7d3c98"),
    }
    xs = np.arange(len(rows))
    ms = [r["mean_ms"] for r in rows]
    cols = [mode_map[r["mode"]][1] for r in rows]
    ax1.bar(xs, ms, color=cols, edgecolor="#1c2833", lw=0.5, width=0.68)
    ax1.set_xticks(xs)
    ax1.set_xticklabels([f"{i+1}" for i in range(len(rows))], fontsize=7.0)
    ax1.set_ylim(0.0, 3.35)
    ax1.set_ylabel("Mean verify time (ms)")
    ax1.set_xlabel("Canonical certificate index (1–16)")
    ax1.set_title(r"(a) Exact-$\mathbb{Q}$ Auditor Runtime (16 Certs)")
    from matplotlib.patches import Patch
    handles = [Patch(facecolor=c, edgecolor="#1c2833", label=lbl) for lbl, c in mode_map.values()]
    ax1.legend(handles=handles, loc="upper left", ncol=2, frameon=True, framealpha=0.94, fontsize=6.6)
    ax1.grid(True, axis="y", alpha=0.25)

    # Panel (b): Lem. 2.1(b) denominator-D simplex rounding L1 error vs d/D bound
    rrows = d4["rounding"]
    Ds = [r["D"] for r in rrows]
    l1s = [r["l1_val"] for r in rrows]
    bnds = [r["bound_val"] for r in rrows]
    ax2.loglog(Ds, bnds, "s--", color="#c0392b", lw=1.4, ms=4.0, label=r"Lean Thm. 9 bound $d/D$ ($d=5$)")
    ax2.loglog(Ds, l1s, "o-", color="#1b4f72", lw=1.7, ms=4.4, label=r"Exact $\|\hat{p}-p\|_1$ (largest-rem)")
    ax2.set_xlabel(r"Simplex denominator $D$")
    ax2.set_ylabel(r"$L_1$ rounding error")
    ax2.set_title(r"(b) Lem. 2.1(b) Exact Simplex Rounding ($d=5$)")
    ax2.grid(True, which="both", alpha=0.25)
    ax2.legend(loc="upper right", frameon=True, framealpha=0.92)

    fig.tight_layout(pad=0.9)
    fig.savefig(FIG_DIR / "fig3_atlas_and_rounding.png", dpi=300)
    plt.close(fig)


def main() -> None:
    FIG_DIR.mkdir(parents=True, exist_ok=True)
    make_fig1()
    make_fig2()
    make_fig3()
    print("[PASS] Generated 3 publication-quality 300-DPI figures in paper/figures/.")


if __name__ == "__main__":
    main()
