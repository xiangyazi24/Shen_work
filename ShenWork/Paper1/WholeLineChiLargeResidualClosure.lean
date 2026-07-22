import ShenWork.Paper1.WholeLineChiLargeCommittedExponent
import ShenWork.Paper1.WholeLineChiLargeStage3
import ShenWork.Paper1.WholeLineLocalMomentBound
import ShenWork.Paper1.Proposition11LargeChiCritical
import ShenWork.Paper1.Proposition11PositiveConjunctChiLtOne

/-!
# Exact continuation/bootstrap closure for the large-critical window

The committed threshold chooses `P > max (2m) γ`; the local-moment
absorption lemma then chooses a translated weight `0 < κ < 1/2`.  The new
whole-line weighted `L² → L∞` estimate turns a time-uniform translated
`L^P` moment bound into the uniform BUC bound required by the blow-up
alternative.

Consequently the only analytic Stage-1 input left below is the production of
that translated local-moment estimate on an arbitrary maximal BUC orbit.
The local/maximal-orbit construction itself is kept as the separate imported
continuation input already used by `Proposition_1_1_large_chi_critical_branch`.
-/

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-- Exact Stage-1 producer needed after the exponent and translated weight
have been selected.  All scalar coefficient inequalities needed by the
critical energy calculation are included as premises; the conclusion is the
time- and translation-uniform local `L^P` moment bound on maximal orbits. -/
def WholeLineLargeChiCriticalStage1Producer (p : CMParams) : Prop :=
  ∀ P κ : ℝ,
    max (2 * p.m) p.γ < P →
    P < p.m + p.γ →
    p.χ * (P - 1) < P + p.m - 1 →
    0 < κ → κ < 1 / 2 →
    0 < wholeLineLocalMomentAbsorption p P κ →
    WholeLineLargeChiMaximalLocalMomentBound p P κ

/-- There is no parameter obstruction in the committed `1 ≤ χ` critical
window: it supplies both an exponent above `2m` and an absorptive translated
weight below `1/2`. -/
theorem wholeLineLargeChiCritical_exists_stage1_parameters
    (p : CMParams)
    (hwindow :
      p.χ < min ((p.m + p.γ - 1) / (2 * p.m - 1))
        ((p.m + p.γ - 1) / (p.γ - 1)))
    (hχ : 1 ≤ p.χ)
    (hcritical : p.α = p.m + p.γ - 1) :
    ∃ P κ : ℝ,
      max (2 * p.m) p.γ < P ∧
      P < p.m + p.γ ∧
      p.χ * (P - 1) < P + p.m - 1 ∧
      0 < κ ∧ κ < 1 / 2 ∧
      0 < wholeLineLocalMomentAbsorption p P κ := by
  obtain ⟨P, hP, hPupper, hadmissible⟩ :=
    paper1_committed_large_chi_exists_admissible_exponent_gt_two_m
      p hwindow hχ
  have hPone : 1 < P := by
    have hm2 : 1 ≤ 2 * p.m := by linarith [p.hm]
    exact lt_of_le_of_lt
      (hm2.trans (le_max_left (2 * p.m) p.γ)) hP
  obtain ⟨κ, hκ, hκhalf, habsorption⟩ :=
    exists_small_localMomentWeight p hPone
      (zero_le_one.trans hχ) hadmissible hcritical
  exact ⟨P, κ, hP, hPupper, hadmissible,
    hκ, hκhalf, habsorption⟩

/-- Stage 1 plus the estimates in `WholeLineChiLargeStage3` give the exact
uniform BUC a-priori bound consumed by maximal continuation. -/
theorem wholeLineLargeChiAPrioriBound_of_critical_stage1
    (p : CMParams)
    (hwindow :
      p.χ < min ((p.m + p.γ - 1) / (2 * p.m - 1))
        ((p.m + p.γ - 1) / (p.γ - 1)))
    (hχ : 1 ≤ p.χ)
    (hcritical : p.α = p.m + p.γ - 1)
    (hstage1 : WholeLineLargeChiCriticalStage1Producer p) :
    WholeLineLargeChiAPrioriBound p := by
  obtain ⟨P, κ, hP, hPupper, hadmissible,
      hκ, hκhalf, habsorption⟩ :=
    wholeLineLargeChiCritical_exists_stage1_parameters
      p hwindow hχ hcritical
  have hmoment : WholeLineLargeChiMaximalLocalMomentBound p P κ :=
    hstage1 P κ hP hPupper hadmissible hκ hκhalf habsorption
  have hP2m : 2 * p.m ≤ P :=
    (le_max_left (2 * p.m) p.γ).trans hP.le
  have hPγ : p.γ ≤ P :=
    (le_max_right (2 * p.m) p.γ).trans hP.le
  have hκone : κ < 1 := by linarith
  exact wholeLineLargeChiAPrioriBound_of_maximalLocalMoment
    p (zero_le_one.trans hχ) hPγ hP2m hκ hκone hmoment

/-- The large-critical branch, now reduced to the two genuinely upstream
continuation inputs: maximal BUC orbits and the Stage-1 local moment estimate.
No ceiling/overshoot regime is used. -/
theorem Proposition_1_1_large_chi_critical_branch_of_stage1
    (p : CMParams)
    (hwindow :
      p.χ < min ((p.m + p.γ - 1) / (2 * p.m - 1))
        ((p.m + p.γ - 1) / (p.γ - 1)))
    (hχ : 1 ≤ p.χ)
    (hcritical : p.α = p.m + p.γ - 1)
    (himport : WholeLineMaximalBUCImport p)
    (hstage1 : WholeLineLargeChiCriticalStage1Producer p)
    (u₀ : ℝ → ℝ) (hu₀ : PaperNonnegativeInitialDatum u₀) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalNonnegativeCauchySolutionFrom p u₀ u v ∧
      UniformEventuallyBounded u := by
  exact Proposition_1_1_large_chi_critical_branch p hχ hcritical himport
    (wholeLineLargeChiAPrioriBound_of_critical_stage1
      p hwindow hχ hcritical hstage1) u₀ hu₀

/-- The exact whole-line continuation/bootstrap residual, uniformly over the
committed large-critical parameter window. -/
def WholeLineLargeChiCriticalContinuationBootstrap : Prop :=
  ∀ p : CMParams,
    p.χ < min ((p.m + p.γ - 1) / (2 * p.m - 1))
      ((p.m + p.γ - 1) / (p.γ - 1)) →
    1 ≤ p.χ →
    p.α = p.m + p.γ - 1 →
    WholeLineMaximalBUCImport p ∧
      WholeLineLargeChiCriticalStage1Producer p

/-- Conditional full closure of Proposition 1.1.  This theorem shows that
the limsup clause introduces no further obligation in the `1 ≤ χ` branch:
maximal continuation and the local-moment Stage 1 discharge the last residual
directly. -/
theorem paper1_Proposition_1_1_of_largeChi_continuationBootstrap
    (H : WholeLineLargeChiCriticalContinuationBootstrap) :
    Proposition_1_1 := by
  apply paper1_Proposition_1_1_of_large_chi_critical_residual
  intro p _hχpos hwindow hχ hcritical u₀ hu₀
  obtain ⟨himport, hstage1⟩ := H p hwindow hχ hcritical
  exact Proposition_1_1_large_chi_critical_branch_of_stage1
    p hwindow hχ hcritical himport hstage1 u₀ hu₀

section AxiomAudit

#print axioms wholeLineLargeChiCritical_exists_stage1_parameters
#print axioms wholeLineLargeChiAPrioriBound_of_critical_stage1
#print axioms Proposition_1_1_large_chi_critical_branch_of_stage1
#print axioms paper1_Proposition_1_1_of_largeChi_continuationBootstrap

end AxiomAudit

end ShenWork.Paper1
