import ShenWork.Paper1.WholeLineMaximalBUCImport
import ShenWork.Paper1.WholeLineChiLargeBoxObstruction

/-!
# Proposition 1.1, the residual large-`χ` critical window (`1 ≤ χ`)

The canonical box-ceiling construction covers the positive-sensitivity regimes
`m + γ - 1 < α` and `χ < 1 ∧ α = m + γ - 1`
(`Proposition_1_1_positive_branches_of_regime`).  At the CRITICAL exponent the
box architecture provably stops working once `1 ≤ χ`
(`not_wholeLineBoxMargin_of_one_le_chi_critical`): no admissible height exists
at all.  The paper reaches this window through the different architecture it
imports by citation — a maximal `BUC` solution plus a blow-up alternative,
continued by an a-priori `L^∞` bound.

This file assembles that architecture into the Proposition-1.1 conclusion,
consuming exactly two inputs:

* `WholeLineMaximalBUCImport p` — the imported local/maximal theory (same
  citation-as-hypothesis status as Theorem 1.2's Henry input), and
* `WholeLineLargeChiAPrioriBound p` — the single analytic estimate, the
  uniform `BUC` bound along any maximal orbit (the physical-space content of
  the Stage-3 gradient / `L^{P/m} → L^∞` estimate).

The reduction is honest: the residual window is closed **iff** that one
a-priori estimate holds, and nothing about the box obstruction is swept under
the rug.  The blow-up alternative does the continuation; the a-priori bound
feeds it; the maximal orbit supplies the finite-subhorizon interfaces.
-/

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-- Residual large-`χ` critical branch of Proposition 1.1.  Given the imported
maximal-`BUC` local theory and the single uniform a-priori bound, every
paper-admissible nonnegative datum has a global nonnegative classical solution
that is uniformly eventually bounded — for the whole window `1 ≤ χ` at the
critical exponent, which the box construction cannot reach. -/
theorem Proposition_1_1_large_chi_critical_branch
    (p : CMParams) (_hχ : 1 ≤ p.χ) (_hcritical : p.α = p.m + p.γ - 1)
    (himport : WholeLineMaximalBUCImport p)
    (hapriori : WholeLineLargeChiAPrioriBound p)
    (u₀ : ℝ → ℝ) (hu₀ : PaperNonnegativeInitialDatum u₀) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalNonnegativeCauchySolutionFrom p u₀ u v ∧
      UniformEventuallyBounded u := by
  obtain ⟨Tmax, U, horbit⟩ := himport u₀ hu₀
  obtain ⟨C, hC⟩ := hapriori u₀ hu₀ Tmax U horbit
  obtain ⟨_hpos, hdatum, htrace, _hcont, hclass, _hmild, hnonneg, hblowup⟩ := horbit
  have htop : Tmax = ⊤ := hblowup ⟨C, hC⟩
  subst htop
  refine ⟨fun t x => (U t).1 x, fun t => frozenElliptic p (fun x => (U t).1 x),
    ⟨?_, hdatum, htrace, ?_⟩, ?_⟩
  · intro T hT
    exact hclass T hT (WithTop.coe_lt_top T)
  · intro t x ht
    exact hnonneg t x ht (WithTop.coe_lt_top t)
  · refine ⟨C, ?_⟩
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht x
    exact (WholeLineBUC.abs_apply_le_norm (U t) x).trans (hC t ht (WithTop.coe_lt_top t))

section AxiomAudit

#print axioms Proposition_1_1_large_chi_critical_branch

end AxiomAudit

end ShenWork.Paper1
