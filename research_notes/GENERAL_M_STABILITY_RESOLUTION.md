# General-m minimal stability — complete resolution (2026-07-26)

Paper 3 Theorem 2.5 (minimal-equilibrium eventual global stability), general-m u^m flux,
1D Neumann, physical-mass hyperplane. The full m-dependence is now resolved:

| range | verdict | how |
|-------|---------|-----|
| 1 ≤ m ≤ 2, in-range χ₀ | **TRUE** (proved, on main) | mass/Agmon energy method (subcritical + critical m=2) |
| all m > 1, small χ₀ | **TRUE** (proved, on main) | small-sensitivity good-slice route (∫u^{−2m}u_x² ≤ χ₀²μσ_β²) |
| m ≳ 2.9, large χ₀ (< χ_lin) | **FALSE** | subcritical steady bifurcation ⇒ mass-preserving nonconstant steady state below the Turing threshold; starting there never converges to the constant |
| χ₀ > χ_lin | FALSE (known) | linear instability |

**The sharp divider for global stability is a PATTERN-BIFURCATION threshold m_c(U), NOT the
m=2 energy-method divider.** m=2 is where the mass-seeded L^P energy method stops; the
constant equilibrium remains globally stable past it (small χ₀ always; up to χ_lin for m < m_c).

**Critical m_c (supercritical→subcritical transition), cross-validated analytic (Lyapunov–
Schmidt χ₂) + numerical (pseudo-arclength continuation, residual ~1e-11):**
- U=0.5: m_c ≈ 2.867
- U=1:   m_c ≈ 2.937
- U=2:   m_c ≈ 3.006

Explicit counterexample (analytic, Q1181): m=3, β=γ=μ=ν=u_*=1, χ_lin=2(1+π²)≈21.739, branch
BACKWARD. Numerical confirms: (U=1,m=4) Δχ=−1.7e-3, (U=0.5,m=3) Δχ=−9.6e-4 (both backward).
χ₂'s leading m-dependence is a negative quadratic ⇒ backward for all large m.

Formalizing this in Lean requires bifurcation theory (Crandall–Rabinowitz / Lyapunov–Schmidt
for the nonconstant steady state existence) — a separate project; the mathematical resolution
is complete. Script: research_notes/m_supercritical_bifurcation_probe.py.
