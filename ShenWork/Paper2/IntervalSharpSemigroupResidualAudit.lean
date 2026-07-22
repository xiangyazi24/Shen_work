import ShenWork.Paper2.IntervalSharpSemigroupFrontier
import ShenWork.Paper2.IntervalDomainTheorem13MinimalResidual
import ShenWork.Paper1.Proposition11LargeChiCritical

/-!
# Residual audit after the sharp interval semigroup construction

The new `q = 2` Neumann spectral estimates are available through
`intervalDomainSharpSemigroupEstimateData`, but the two residuals considered
here are not missing instances of those estimates.

For Paper 2, alternative (iv) still needs the exponent-domain inequality used
by Proposition 2.2.  The first concrete parameter package below satisfies the
printed alternative while violating that inequality.  A second package shows
that an arbitrary statement-layer constant `K` cannot be identified with the
positive spectral/energy constant by a semigroup estimate.

For Paper 1, the remaining analytic premise is literally quantified over
initial data on `ℝ` and maximal orbits in `WholeLineBUC`.  The interval data
has state space `intervalDomain.Point → ℝ`; no interval-to-whole-line maximal
orbit or a-priori-bound transport is present in this interface.
-/

open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.IntervalSharpSemigroupResidualAudit

open ShenWork.Paper2.IntervalDomainTheorem13CriticalConstants
open ShenWork.Paper2.IntervalDomainTheorem13MinimalResidual

/-! ## Paper 2, Theorem 1.3 alternative (iv) -/

/-- An interval parameter package satisfying the printed fourth alternative
through its zero-dimensional-factor branch, but lying outside the exponent
domain required by Proposition 2.2. -/
def caseIVGuardCounterParams : CM2Params where
  N := 1
  hN := by norm_num
  α := 1 / 2
  γ := 2
  m := 1 / 4
  μ := 1
  ν := 1
  χ₀ := 1
  a := 1
  b := 1
  β := 1 / 2
  hα := by norm_num
  hγ := by norm_num
  hm := by norm_num
  hμ := by norm_num
  hν := by norm_num
  ha := by norm_num
  hb := by norm_num
  hβ := by norm_num

def caseIVGuardCounterConstants :
    Paper2Constants caseIVGuardCounterParams where
  K := 0
  K_nonneg := le_rfl

theorem caseIVGuardCounter_printed :
    PrintedStrongLogisticCaseIV
      caseIVGuardCounterParams caseIVGuardCounterConstants := by
  refine ⟨?_, ?_, Or.inl ?_⟩
  · norm_num [caseIVGuardCounterParams]
  · norm_num [caseIVGuardCounterParams]
  · norm_num [caseIVGuardCounterParams, positivePart]

theorem caseIVGuardCounter_not_exponent_guard :
    ¬ (2 - 2 * caseIVGuardCounterParams.m <
      theorem13CriticalQStar caseIVGuardCounterParams) := by
  norm_num [caseIVGuardCounterParams, theorem13CriticalQStar]

theorem caseIVGuardCounter_not_minimalHonestResidual :
    ¬ IntervalDomainTheorem13MinimalHonestResidual
      caseIVGuardCounterParams caseIVGuardCounterConstants := by
  intro hres
  exact caseIVGuardCounter_not_exponent_guard
    (hres.2 caseIVGuardCounter_printed)

/-- In the global branch of the printed theorem, where `1 ≤ m` is assumed,
the exponent guard is automatic.  The obstruction is real only for the local
boundedness branch, which permits `m < 1`. -/
theorem theorem13_caseIV_exponent_guard_of_one_le_m
    (p : CM2Params) (hm : 1 ≤ p.m) :
    2 - 2 * p.m < theorem13CriticalQStar p := by
  have hq := theorem13CriticalQStar_pos p
  linarith

theorem theorem13_caseIV_scale_gt_one_of_one_le_m
    (p : CM2Params) (hm : 1 ≤ p.m)
    (hcrit : p.α = 2 * p.m + p.γ - 2) :
    1 < (theorem13CriticalQStar p + p.α) / p.γ := by
  rw [one_lt_div p.hγ, hcrit]
  have hq := theorem13CriticalQStar_pos p
  linarith

/-- With the literal paper constant and the global-branch hypothesis
`1 ≤ m`, both components of the minimal residual are algebraic.  No
semigroup estimate is used in this proof. -/
theorem theorem13PaperConstants_minimalHonestResidual_of_one_le_m
    (p : CM2Params) (hm : 1 ≤ p.m)
    (hs : 1 < (theorem13CriticalQStar p + p.α) / p.γ) :
    IntervalDomainTheorem13MinimalHonestResidual p
      (theorem13PaperConstants p hs) := by
  refine ⟨theorem13PaperConstants_K p hs, ?_⟩
  intro _hIV
  exact theorem13_caseIV_exponent_guard_of_one_le_m p hm

/-- Consequently the existing exact interval theorem closes with the literal
paper constant throughout the global regime.  This isolates the point: the
fresh semigroup bounds did not supply a missing energy step; that step was
already present, and only constant fidelity plus an exponent guard remained. -/
theorem Theorem_1_3_intervalDomainM_with_paperConstants_of_one_le_m
    (p : CM2Params) (hN : p.N = 1) (hχ : 0 < p.χ₀)
    (hm : 1 ≤ p.m)
    (hs : 1 < (theorem13CriticalQStar p + p.α) / p.γ) :
    Theorem_1_3 intervalDomainM p (theorem13PaperConstants p hs) := by
  exact Theorem_1_3_intervalDomainM_from_minimal_honest_residual
    p (theorem13PaperConstants p hs) hN hχ
      (theorem13PaperConstants_minimalHonestResidual_of_one_le_m p hm hs)

/-- Case-(iv) specialization: its critical equality and `1 ≤ m` themselves
supply the scale-domain premise needed to construct the literal paper
constant, so no extra analytic hypothesis remains in the global regime. -/
theorem Theorem_1_3_intervalDomainM_caseIV_with_paperConstants
    (p : CM2Params) (hN : p.N = 1) (hχ : 0 < p.χ₀)
    (hm : 1 ≤ p.m) (hcrit : p.α = 2 * p.m + p.γ - 2) :
    Theorem_1_3 intervalDomainM p
      (theorem13PaperConstants p
        (theorem13_caseIV_scale_gt_one_of_one_le_m p hm hcrit)) := by
  exact Theorem_1_3_intervalDomainM_with_paperConstants_of_one_le_m
    p hN hχ hm (theorem13_caseIV_scale_gt_one_of_one_le_m p hm hcrit)

/-- A second interval package for which the concrete critical constant is
strictly positive. -/
def criticalKCounterParams : CM2Params where
  N := 1
  hN := by norm_num
  α := 2
  γ := 2
  m := 1
  μ := 1
  ν := 1
  χ₀ := 1
  a := 1
  b := 1
  β := 1 / 2
  hα := by norm_num
  hγ := by norm_num
  hm := by norm_num
  hμ := by norm_num
  hν := by norm_num
  ha := by norm_num
  hb := by norm_num
  hβ := by norm_num

def criticalKCounterConstants : Paper2Constants criticalKCounterParams where
  K := 0
  K_nonneg := le_rfl

theorem criticalKCounter_concrete_K_pos :
    0 < theorem13CriticalK criticalKCounterParams := by
  apply theorem13CriticalK_pos
  norm_num [criticalKCounterParams, theorem13CriticalQStar]

theorem criticalKCounter_statement_K_ne_concrete :
    criticalKCounterConstants.K ≠ theorem13CriticalK criticalKCounterParams := by
  simpa [criticalKCounterConstants] using
    (ne_of_lt criticalKCounter_concrete_K_pos)

theorem criticalKCounter_not_minimalHonestResidual :
    ¬ IntervalDomainTheorem13MinimalHonestResidual
      criticalKCounterParams criticalKCounterConstants := by
  intro hres
  exact criticalKCounter_statement_K_ne_concrete hres.1

/-! ## Paper 1, Proposition 1.1 at `1 ≤ χ` -/

/-- The exact remaining Paper-1 premise: local/maximal theory and the critical
a-priori bound are both whole-line statements. -/
def Paper1LargeChiWholeLineResidual (p : CMParams) : Prop :=
  ShenWork.Paper1.WholeLineMaximalBUCImport p ∧
    ShenWork.Paper1.WholeLineLargeChiAPrioriBound p

/-- Re-exposes the existing closure with the whole-line residual bundled.  In
particular, no `SemigroupEstimateData intervalDomain` argument occurs here. -/
theorem paper1_large_chi_critical_from_wholeLine_residual
    (p : CMParams)
    (hχ : 1 ≤ p.χ) (hcritical : p.α = p.m + p.γ - 1)
    (hres : Paper1LargeChiWholeLineResidual p)
    (u₀ : ℝ → ℝ) (hu₀ : ShenWork.Paper1.PaperNonnegativeInitialDatum u₀) :
    ∃ u v : ℝ → ℝ → ℝ,
      ShenWork.Paper1.IsGlobalNonnegativeCauchySolutionFrom p u₀ u v ∧
      ShenWork.Paper1.UniformEventuallyBounded u := by
  exact ShenWork.Paper1.Proposition_1_1_large_chi_critical_branch
    p hχ hcritical hres.1 hres.2 u₀ hu₀

section AxiomAudit

#print axioms caseIVGuardCounter_printed
#print axioms caseIVGuardCounter_not_exponent_guard
#print axioms caseIVGuardCounter_not_minimalHonestResidual
#print axioms theorem13_caseIV_exponent_guard_of_one_le_m
#print axioms theorem13_caseIV_scale_gt_one_of_one_le_m
#print axioms theorem13PaperConstants_minimalHonestResidual_of_one_le_m
#print axioms Theorem_1_3_intervalDomainM_with_paperConstants_of_one_le_m
#print axioms Theorem_1_3_intervalDomainM_caseIV_with_paperConstants
#print axioms criticalKCounter_concrete_K_pos
#print axioms criticalKCounter_statement_K_ne_concrete
#print axioms criticalKCounter_not_minimalHonestResidual
#print axioms paper1_large_chi_critical_from_wholeLine_residual

end AxiomAudit

end ShenWork.Paper2.IntervalSharpSemigroupResidualAudit
