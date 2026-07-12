/-
  Full diagonal linearized semigroup for the positive Paper3 equilibrium.

  Unlike the pure Neumann heat semigroup on `(I-P0)`, this multiplier keeps
  the zero mode.  Its zeroth decay rate is the logistic damping `a*alpha`, and
  every nonzero mode uses the complete eliminated chemotaxis growth `sigma_k`.
-/
import ShenWork.Paper3.IntervalDomainLinearizedSmoothing

namespace ShenWork.Paper3

open ShenWork.PDE.SectorialOperator

noncomputable section

/-- The coefficient multiplying `lambda/(mu+lambda)` after eliminating the
elliptic variable. -/
def paper3LinearChemMultiplier
    (p : CM2Params) (uStar vStar : ℝ) : ℝ :=
  p.χ₀ * p.ν * p.γ * uStar ^ (p.m + p.γ - 1) /
    (1 + vStar) ^ p.β

/-- Positive decay multiplier `d(lambda)=-sigma(lambda)`. -/
def paper3FullModeDecay
    (p : CM2Params) (uStar vStar lambdaN : ℝ) : ℝ :=
  -sigma p uStar vStar lambdaN

/-- Exact eliminated form of the full modal decay multiplier. -/
theorem paper3FullModeDecay_eq
    (p : CM2Params) {uStar vStar lambdaN : ℝ}
    (hvStar : 0 ≤ vStar) (hlambda : 0 ≤ lambdaN) :
    paper3FullModeDecay p uStar vStar lambdaN =
      p.a * p.α + lambdaN -
        paper3LinearChemMultiplier p uStar vStar *
          (lambdaN / (p.μ + lambdaN)) := by
  have hvpow : 0 < (1 + vStar) ^ p.β :=
    Real.rpow_pos_of_pos (by linarith) _
  have hden : 0 < p.μ + lambdaN := by linarith [p.hμ]
  unfold paper3FullModeDecay paper3LinearChemMultiplier sigma
  field_simp [ne_of_gt hvpow, ne_of_gt hden]
  ring

/-- The full zeroth mode is damped exactly at the logistic rate. -/
@[simp] theorem paper3FullModeDecay_zero
    (p : CM2Params) (uStar vStar : ℝ) :
    paper3FullModeDecay p uStar vStar 0 = p.a * p.α := by
  simp [paper3FullModeDecay, sigma]

/-- Full diagonal semigroup on the unit-interval cosine coefficients.  No
zeroth-mode projection occurs in this definition. -/
def unitIntervalFullLinearizedSemigroupCoeff
    (p : CM2Params) (uStar vStar t : ℝ)
    (a : ℕ → ℂ) : ℕ → ℂ :=
  diagonalSemigroupCoeff
    (unitIntervalLinearizedGrowth p uStar vStar) t a

theorem unitIntervalFullLinearizedSemigroupCoeff_apply
    (p : CM2Params) (uStar vStar t : ℝ)
    (a : ℕ → ℂ) (n : ℕ) :
    unitIntervalFullLinearizedSemigroupCoeff p uStar vStar t a n =
      (Real.exp
        (-paper3FullModeDecay p uStar vStar
          (unitIntervalNeumannSpectrum.eigenvalue n) * t) : ℂ) * a n := by
  simp only [unitIntervalFullLinearizedSemigroupCoeff,
    diagonalSemigroupCoeff, unitIntervalLinearizedGrowth,
    paper3FullModeDecay]
  congr 2
  ring_nf

/-- A full spectral gap controls the complete diagonal semigroup in coefficient
`ell^2`, including its zeroth mode. -/
theorem unitIntervalFullLinearizedSemigroupCoeff_l2_norm_le
    (p : CM2Params) {uStar vStar rate t : ℝ}
    (hgap : UnitIntervalLinearSpectralGap p uStar vStar rate)
    (ht : 0 ≤ t) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    coeffL2Norm
        (unitIntervalFullLinearizedSemigroupCoeff p uStar vStar t a) ≤
      Real.exp (-rate * t) * coeffL2Norm a := by
  simpa [unitIntervalFullLinearizedSemigroupCoeff,
    mul_comm, mul_left_comm, mul_assoc] using
    (diagonalSemigroupCoeff_l2_norm_le_of_growth_le
      (growth := unitIntervalLinearizedGrowth p uStar vStar)
      (omega := -rate) ht hgap.2 ha)

/-- The continuous-spectrum gap suggested by minimizing the exact multiplier.
For `kappa <= mu` the minimum is the zeroth rate; otherwise it is the completed
square value `A-(sqrt(kappa)-sqrt(mu))^2`. -/
def paper3ExplicitContinuousLinearGap
    (p : CM2Params) (uStar vStar : ℝ) : ℝ :=
  let A := p.a * p.α
  let kappa := paper3LinearChemMultiplier p uStar vStar
  if kappa ≤ p.μ then A
  else A - (Real.sqrt kappa - Real.sqrt p.μ) ^ 2

/-- In the monotone branch `kappa <= mu`, every nonnegative spectral value has
decay at least the zeroth damping `A`. -/
theorem paper3FullModeDecay_ge_logistic_of_multiplier_le_mu
    (p : CM2Params) {uStar vStar lambdaN : ℝ}
    (hvStar : 0 ≤ vStar) (hlambda : 0 ≤ lambdaN)
    (hkappa : paper3LinearChemMultiplier p uStar vStar ≤ p.μ) :
    p.a * p.α ≤ paper3FullModeDecay p uStar vStar lambdaN := by
  rw [paper3FullModeDecay_eq p hvStar hlambda]
  have hden : 0 < p.μ + lambdaN := by linarith [p.hμ]
  have hfactor : 0 ≤
      1 - paper3LinearChemMultiplier p uStar vStar /
        (p.μ + lambdaN) := by
    rw [sub_nonneg, div_le_one hden]
    linarith
  have hprod : 0 ≤ lambdaN *
      (1 - paper3LinearChemMultiplier p uStar vStar /
        (p.μ + lambdaN)) := mul_nonneg hlambda hfactor
  have hid :
      lambdaN - paper3LinearChemMultiplier p uStar vStar *
          (lambdaN / (p.μ + lambdaN)) =
        lambdaN *
          (1 - paper3LinearChemMultiplier p uStar vStar /
            (p.μ + lambdaN)) := by
    field_simp [ne_of_gt hden]
  linarith [hid, hprod]

/-- Completed-square lower bound in the interior-minimum branch. -/
theorem paper3FullModeDecay_ge_completedSquareGap
    (p : CM2Params) {uStar vStar lambdaN : ℝ}
    (hvStar : 0 ≤ vStar) (hlambda : 0 ≤ lambdaN)
    (hmu_kappa : p.μ < paper3LinearChemMultiplier p uStar vStar) :
    p.a * p.α -
        (Real.sqrt (paper3LinearChemMultiplier p uStar vStar) -
          Real.sqrt p.μ) ^ 2 ≤
      paper3FullModeDecay p uStar vStar lambdaN := by
  let kappa := paper3LinearChemMultiplier p uStar vStar
  have hkappa : 0 ≤ kappa := by dsimp [kappa]; linarith [p.hμ]
  have hmu : 0 ≤ p.μ := p.hμ.le
  have hsqrtK : (Real.sqrt kappa) ^ 2 = kappa := Real.sq_sqrt hkappa
  have hsqrtMu : (Real.sqrt p.μ) ^ 2 = p.μ := Real.sq_sqrt hmu
  have hden : 0 < p.μ + lambdaN := by linarith [p.hμ]
  have hsquare : 0 ≤
      (lambdaN + p.μ - Real.sqrt kappa * Real.sqrt p.μ) ^ 2 :=
    sq_nonneg _
  have hid :
      lambdaN - kappa * (lambdaN / (p.μ + lambdaN)) +
          (Real.sqrt kappa - Real.sqrt p.μ) ^ 2 =
        (lambdaN + p.μ - Real.sqrt kappa * Real.sqrt p.μ) ^ 2 /
          (p.μ + lambdaN) := by
    field_simp [ne_of_gt hden]
    nlinarith
  rw [paper3FullModeDecay_eq p hvStar hlambda]
  change p.a * p.α - (Real.sqrt kappa - Real.sqrt p.μ) ^ 2 ≤
    p.a * p.α + lambdaN - kappa * (lambdaN / (p.μ + lambdaN))
  have hquot : 0 ≤
      (lambdaN + p.μ - Real.sqrt kappa * Real.sqrt p.μ) ^ 2 /
        (p.μ + lambdaN) := div_nonneg hsquare hden.le
  linarith [hid]

/-- Positivity of the explicit continuous-spectrum gap under the usual
eliminated multiplier threshold. -/
theorem paper3ExplicitContinuousLinearGap_pos
    (p : CM2Params) {uStar vStar : ℝ}
    (ha : 0 < p.a)
    (hthreshold : paper3LinearChemMultiplier p uStar vStar <
      (Real.sqrt p.μ + Real.sqrt (p.a * p.α)) ^ 2) :
    0 < paper3ExplicitContinuousLinearGap p uStar vStar := by
  let A : ℝ := p.a * p.α
  let kappa : ℝ := paper3LinearChemMultiplier p uStar vStar
  have hA : 0 < A := mul_pos ha p.hα
  have hmu : 0 ≤ p.μ := p.hμ.le
  have hA0 : 0 ≤ A := hA.le
  unfold paper3ExplicitContinuousLinearGap
  dsimp only
  split_ifs with hkappa_mu
  · exact hA
  · have hmu_kappa : p.μ < kappa := lt_of_not_ge hkappa_mu
    have hkappa : 0 ≤ kappa := by linarith [p.hμ]
    have hsqrtK : (Real.sqrt kappa) ^ 2 = kappa := Real.sq_sqrt hkappa
    have hsqrtMu : (Real.sqrt p.μ) ^ 2 = p.μ := Real.sq_sqrt hmu
    have hsqrtA : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA0
    have hsqrtK0 : 0 ≤ Real.sqrt kappa := Real.sqrt_nonneg _
    have hsqrtMu0 : 0 ≤ Real.sqrt p.μ := Real.sqrt_nonneg _
    have hsqrtApos : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
    have hsqrtMu_lt_K : Real.sqrt p.μ < Real.sqrt kappa := by
      nlinarith [sq_nonneg (Real.sqrt kappa - Real.sqrt p.μ)]
    have hsqrtK_lt_sum :
        Real.sqrt kappa < Real.sqrt p.μ + Real.sqrt A := by
      change kappa < (Real.sqrt p.μ + Real.sqrt A) ^ 2 at hthreshold
      by_contra hnot
      have hle : Real.sqrt p.μ + Real.sqrt A ≤ Real.sqrt kappa :=
        le_of_not_gt hnot
      nlinarith [sq_nonneg
        (Real.sqrt kappa - (Real.sqrt p.μ + Real.sqrt A))]
    have hdiff_pos :
        0 < Real.sqrt kappa - Real.sqrt p.μ := sub_pos.mpr hsqrtMu_lt_K
    have hdiff_lt :
        Real.sqrt kappa - Real.sqrt p.μ < Real.sqrt A := by linarith
    have hprod :
        0 < (Real.sqrt A -
              (Real.sqrt kappa - Real.sqrt p.μ)) *
            (Real.sqrt A +
              (Real.sqrt kappa - Real.sqrt p.μ)) :=
      mul_pos (sub_pos.mpr hdiff_lt)
        (add_pos_of_pos_of_nonneg hsqrtApos hdiff_pos.le)
    nlinarith

/-- The explicit continuous gap yields a full unit-interval spectral gap.  It
is a convenient sufficient condition; the discrete `LinearlyStable` extraction
in `IntervalDomainUniformSpectralGap` remains more general. -/
theorem unitIntervalLinearSpectralGap_of_explicitContinuousThreshold
    (p : CM2Params) {uStar vStar : ℝ}
    (hvStar : 0 ≤ vStar) (ha : 0 < p.a)
    (hthreshold : paper3LinearChemMultiplier p uStar vStar <
      (Real.sqrt p.μ + Real.sqrt (p.a * p.α)) ^ 2) :
    UnitIntervalLinearSpectralGap p uStar vStar
      (paper3ExplicitContinuousLinearGap p uStar vStar) := by
  let gap := paper3ExplicitContinuousLinearGap p uStar vStar
  have hgap : 0 < gap :=
    paper3ExplicitContinuousLinearGap_pos p ha hthreshold
  refine ⟨hgap, ?_⟩
  intro n
  let lambdaN := unitIntervalNeumannSpectrum.eigenvalue n
  have hlambda : 0 ≤ lambdaN :=
    unitIntervalNeumannSpectrum_hasNeumannSpectrum.eigenvalue_nonneg n
  have hdecay : gap ≤ paper3FullModeDecay p uStar vStar lambdaN := by
    unfold gap paper3ExplicitContinuousLinearGap
    dsimp only
    split_ifs with hkappa_mu
    · exact paper3FullModeDecay_ge_logistic_of_multiplier_le_mu
        p hvStar hlambda hkappa_mu
    · exact paper3FullModeDecay_ge_completedSquareGap
        p hvStar hlambda (lt_of_not_ge hkappa_mu)
  change sigma p uStar vStar lambdaN ≤ -gap
  change gap ≤ -sigma p uStar vStar lambdaN at hdecay
  simpa using (neg_le_neg hdecay)

#print axioms paper3FullModeDecay_eq
#print axioms unitIntervalFullLinearizedSemigroupCoeff_l2_norm_le
#print axioms paper3FullModeDecay_ge_logistic_of_multiplier_le_mu
#print axioms paper3FullModeDecay_ge_completedSquareGap
#print axioms paper3ExplicitContinuousLinearGap_pos
#print axioms unitIntervalLinearSpectralGap_of_explicitContinuousThreshold

end

end ShenWork.Paper3
