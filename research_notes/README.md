# Beyond-paper research notes

The two public notes have detailed PDF versions, LaTeX sources, and shorter
Markdown summaries.

## Far-left front stability

- [Detailed PDF](FARLEFT_CHI4_RESOLUTION.pdf)
- [LaTeX source](FARLEFT_CHI4_RESOLUTION.tex)
- [Markdown summary](FARLEFT_CHI4_RESOLUTION.md)

The sharp threshold is `χ=4`, simultaneously from the dispersion relation and
the nonlinear entropy coefficient. The optimal theorem gives
basin-conditional convergence for `0≤χ<4`; a genuine convective-escape PDE
orbit shows why an unconditional result in an arbitrary frame is false.

## General-m minimal stability

- [Detailed PDF](GENERAL_M_STABILITY_RESOLUTION.pdf)
- [LaTeX source](GENERAL_M_STABILITY_RESOLUTION.tex)
- [Markdown summary](GENERAL_M_STABILITY_RESOLUTION.md)
- [Bifurcation probe](m_supercritical_bifurcation_probe.py)

Formalized stability holds under the full formula conditions for `1≤m<2`, at
the critical endpoint `m=2` under its explicit admissibility, and for every
`m>1` under an explicit small-sensitivity condition. An exact Wiener-algebra
branch proves that global attraction already fails for a fixed `m=3` tuple at
some sensitivity below the linear threshold. The weakly nonlinear
direction-change curve lies near `m≈2.9` in the normalized family.

All cited Lean headline theorems are `sorry`-free and use only
`[propext, Classical.choice, Quot.sound]`.
