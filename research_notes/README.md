# Shen chemotaxis trilogy — beyond-paper research notes

Results that go beyond the three papers. The Lean theorems use exactly the standard classical
axioms `[propext, Classical.choice, Quot.sound]`. The papers cover m=1 and χ near χ*≈1;
these notes push both frontiers to their sharp limits and record the counterexamples that
delimit them.

- **`FARLEFT_CHI4_RESOLUTION.md`** — the traveling-front far-left stability. Sharp threshold
  χ=4 (dispersion + entropy); whole-line weighted sharp-entropy engine; basin-conditional χ<4
  convergence (optimal); UNCONDITIONAL χ<4 proved FALSE via a formalized convective-escape
  counterexample; catalogue of why L¹/bare-L²/KPP-refill/front-anchor/Harnack routes fail.

- **`GENERAL_M_STABILITY_RESOLUTION.md`** — Paper 3 Theorem 2.5 for general m. Complete sharp
  picture: stable for 1≤m≤2 (all in-range χ₀) and all m>1 (small χ₀); FALSE for m≳2.9 large χ₀
  (subcritical steady pattern). The sharp divider m_c(U)≈2.9 is a bifurcation threshold, cross-
  validated analytic + numerical. Bifurcation probe script alongside.

Each note lists the exact Lean theorem names and source files. The `m=3` steady
counterexample is mechanized as
`minimal_equilibrium_global_stability_false_m3`.
