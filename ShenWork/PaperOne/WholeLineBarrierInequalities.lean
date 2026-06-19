import ShenWork.PaperOne.WholeLineExponentialBarrierTrapping
import Mathlib.Tactic

noncomputable section

namespace ShenWork.PaperOne

/-!
Pointwise algebra for the whole-line exponential barriers.

This file isolates the algebraic part of the barrier inequalities from
`WholeLineExponentialBarrierTrapping`: the explicit
`κ ^ 2 - c * κ + 1 = 0` cancellation, the elementary sign facts for the
negative-sensitivity chemotaxis terms, and the lower-branch exponent bookkeeping.

The final constructor keeps the remaining branch domination hypotheses explicit.
This is intentional: with the residual signs currently encoded in
`WholeLineExponentialBarrierInequalities`, the requested unconditional upper
`≥ 0` and lower `≤ 0` statements are not consequences of the κ cancellation
alone.
-/

/-- The nonlinear remainder of the pure upper exponential branch after the
`κ ^ 2 - c * κ + 1` term has been removed. -/
def upperExponentialBranchRemainder
    (p : CMParams) (κ : ℝ) (V Vx : ℝ → ℝ) (x : ℝ) : ℝ :=
  - (expBarrierTail κ x) ^ (p.α + 1)
    - p.χ * p.m * (expBarrierTail κ x) ^ (p.m - 1)
        * upperExpBranchDx κ x * Vx x
    - p.χ * (expBarrierTail κ x) ^ p.m * V x
    + p.χ * (expBarrierTail κ x) ^ (p.m + p.γ)

/-- The nonlinear/lower-order remainder of the positive lower branch after the
leading `κ` exponential has been cancelled. -/
def lowerPositiveBranchRemainder
    (p : CMParams) (κ κt D : ℝ) (V Vx : ℝ → ℝ) (x : ℝ) : ℝ :=
  - (lowerBarrierCore κ κt D x) ^ (p.α + 1)
    - p.χ * p.m * (lowerBarrierCore κ κt D x) ^ (p.m - 1)
        * lowerPositiveBranchDx κ κt D x * Vx x
    - p.χ * (lowerBarrierCore κ κt D x) ^ p.m * V x
    + p.χ * (lowerBarrierCore κ κt D x) ^ (p.m + p.γ)

/-- The exact remaining upper-branch domination needed by the current
`WholeLineExponentialBarrierInequalities` sign convention. -/
def UpperExponentialBranchDomination
    (p : CMParams) (κ : ℝ) (V Vx : ℝ → ℝ) : Prop :=
  ∀ x, 0 ≤ x → 0 ≤ upperExponentialBranchRemainder p κ V Vx x

/-- The exact remaining lower-positive-branch domination needed by the current
`WholeLineExponentialBarrierInequalities` sign convention. -/
def LowerPositiveBranchDomination
    (p : CMParams) (c κ κt D : ℝ) (V Vx : ℝ → ℝ) : Prop :=
  ∀ x, 0 < lowerBarrierCore κ κt D x →
    lowerPositiveBranchRemainder p κ κt D V Vx x ≤
      D * (κt ^ 2 - c * κt + 1) * expBarrierTail κt x

theorem upperExponentialBranchResidual_cancel
    (p : CMParams) (c κ : ℝ) (V Vx : ℝ → ℝ) (x : ℝ)
    (hκ : κ ^ 2 - c * κ + 1 = 0) :
    upperExponentialBranchResidual p c κ V Vx x =
      upperExponentialBranchRemainder p κ V Vx x := by
  unfold upperExponentialBranchResidual upperExponentialBranchRemainder
  rw [hκ]
  ring

/-- The explicit `waveExponent` cancellation on the upper exponential branch. -/
theorem upperExponentialBranchResidual_waveExponent_cancel
    (p : CMParams) {c : ℝ} (hc : 2 ≤ c)
    (V Vx : ℝ → ℝ) (x : ℝ) :
    upperExponentialBranchResidual p c (waveExponent c) V Vx x =
      upperExponentialBranchRemainder p (waveExponent c) V Vx x := by
  exact upperExponentialBranchResidual_cancel p c (waveExponent c) V Vx x
    (waveExponent_quadratic hc)

/-- Upper exponential branch, closed modulo the named nonlinear domination.
The displayed cancellation is exactly `κ ^ 2 - c * κ + 1 = 0`. -/
theorem upperBarrier_supersolution
    (p : CMParams) {c κ : ℝ} {V Vx : ℝ → ℝ}
    (hκ : κ ^ 2 - c * κ + 1 = 0)
    (hupper : UpperExponentialBranchDomination p κ V Vx) :
    ∀ x, 0 ≤ x → 0 ≤ upperExponentialBranchResidual p c κ V Vx x := by
  intro x hx
  rw [upperExponentialBranchResidual_cancel p c κ V Vx x hκ]
  exact hupper x hx

/-- The upper constant branch residual is exactly `χ * (1 - V)`. -/
theorem upperConstantBranchResidual_eq
    (p : CMParams) (c : ℝ) (V Vx : ℝ → ℝ) (x : ℝ) :
    auxiliaryStationaryResidual p c
        (fun _ : ℝ => 1) (fun _ : ℝ => 0) (fun _ : ℝ => 0) V Vx x =
      p.χ * (1 - V x) := by
  simp [auxiliaryStationaryResidual, auxiliaryFrozenNonlinearity,
    wholeLineReaction]
  ring

/-- The zero lower branch has zero residual. -/
theorem lowerZeroBranchResidual_eq_zero
    (p : CMParams) (c : ℝ) (V Vx : ℝ → ℝ) (x : ℝ) :
    auxiliaryStationaryResidual p c
        (fun _ : ℝ => 0) (fun _ : ℝ => 0) (fun _ : ℝ => 0) V Vx x = 0 := by
  have hm_pos : 0 < p.m := lt_of_lt_of_le zero_lt_one p.hm
  have hmγ_pos : 0 < p.m + p.γ := by linarith [p.hm, p.hγ]
  simp [auxiliaryStationaryResidual, auxiliaryFrozenNonlinearity,
    wholeLineReaction, Real.zero_rpow (ne_of_gt hm_pos),
    Real.zero_rpow (ne_of_gt hmγ_pos)]

theorem lowerPositiveBranchResidual_cancel
    (p : CMParams) (c κ κt D : ℝ) (V Vx : ℝ → ℝ) (x : ℝ)
    (hκ : κ ^ 2 - c * κ + 1 = 0) :
    lowerPositiveBranchResidual p c κ κt D V Vx x =
      -D * (κt ^ 2 - c * κt + 1) * expBarrierTail κt x
        + lowerPositiveBranchRemainder p κ κt D V Vx x := by
  unfold lowerPositiveBranchResidual lowerPositiveBranchRemainder
  rw [hκ]
  ring

/-- The explicit `waveExponent` cancellation on the lower positive branch. -/
theorem lowerPositiveBranchResidual_waveExponent_cancel
    (p : CMParams) {c κt D : ℝ} (hc : 2 ≤ c)
    (V Vx : ℝ → ℝ) (x : ℝ) :
    lowerPositiveBranchResidual p c (waveExponent c) κt D V Vx x =
      -D * (κt ^ 2 - c * κt + 1) * expBarrierTail κt x
        + lowerPositiveBranchRemainder p (waveExponent c) κt D V Vx x := by
  exact lowerPositiveBranchResidual_cancel p c (waveExponent c) κt D V Vx x
    (waveExponent_quadratic hc)

/-- Lower positive branch, closed modulo the named domination of the remaining
terms by the `κt` correction. -/
theorem lowerBarrier_subsolution
    (p : CMParams) {c κ κt D : ℝ} {V Vx : ℝ → ℝ}
    (hκ : κ ^ 2 - c * κ + 1 = 0)
    (hlower : LowerPositiveBranchDomination p c κ κt D V Vx) :
    ∀ x, 0 < lowerBarrierCore κ κt D x →
      lowerPositiveBranchResidual p c κ κt D V Vx x ≤ 0 := by
  intro x hx
  rw [lowerPositiveBranchResidual_cancel p c κ κt D V Vx x hκ]
  have hdom := hlower x hx
  linarith

theorem expBarrierTail_pos (κ x : ℝ) : 0 < expBarrierTail κ x := by
  unfold expBarrierTail
  exact Real.exp_pos _

theorem expBarrierTail_nonneg (κ x : ℝ) : 0 ≤ expBarrierTail κ x :=
  (expBarrierTail_pos κ x).le

theorem upperExpBranchDx_nonpos {κ x : ℝ} (hκ : 0 ≤ κ) :
    upperExpBranchDx κ x ≤ 0 := by
  unfold upperExpBranchDx
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hκ)
    (expBarrierTail_nonneg κ x)

theorem upperExpBranchDx_eq_neg_mul (κ x : ℝ) :
    upperExpBranchDx κ x = -κ * expBarrierTail κ x := rfl

/-- With `χ ≤ 0`, `Vx ≤ 0`, and `κ ≥ 0`, the derivative chemotaxis term on the
upper exponential branch has the nonnegative sign. -/
theorem upper_exp_derivative_chi_term_nonneg
    (p : CMParams) {κ x : ℝ} {Vx : ℝ → ℝ}
    (hχ : p.χ ≤ 0) (hκ : 0 ≤ κ) (hVx : Vx x ≤ 0) :
    0 ≤
      -p.χ * p.m * (expBarrierTail κ x) ^ (p.m - 1)
        * upperExpBranchDx κ x * Vx x := by
  have hm_nonneg : 0 ≤ p.m := le_trans zero_le_one p.hm
  have hm1_nonneg : 0 ≤ p.m - 1 := by linarith [p.hm]
  have htail_nonneg : 0 ≤ (expBarrierTail κ x) ^ (p.m - 1) :=
    Real.rpow_nonneg (expBarrierTail_nonneg κ x) _
  have hcoef :
      0 ≤ -p.χ * p.m * (expBarrierTail κ x) ^ (p.m - 1) := by
    exact mul_nonneg (mul_nonneg (neg_nonneg.mpr hχ) hm_nonneg)
      htail_nonneg
  have hdx : upperExpBranchDx κ x ≤ 0 := upperExpBranchDx_nonpos hκ
  have hcoef_dx :
      -p.χ * p.m * (expBarrierTail κ x) ^ (p.m - 1)
          * upperExpBranchDx κ x ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hcoef hdx
  exact mul_nonneg_of_nonpos_of_nonpos hcoef_dx hVx

/-- With `χ ≤ 0` and `V ≥ 0`, the `-χ U^m V` term has the nonnegative sign. -/
theorem upper_exp_absorption_chi_term_nonneg
    (p : CMParams) {κ x : ℝ} {V : ℝ → ℝ}
    (hχ : p.χ ≤ 0) (hV : 0 ≤ V x) :
    0 ≤ -p.χ * (expBarrierTail κ x) ^ p.m * V x := by
  have htail_nonneg : 0 ≤ (expBarrierTail κ x) ^ p.m :=
    Real.rpow_nonneg (expBarrierTail_nonneg κ x) _
  exact mul_nonneg (mul_nonneg (neg_nonneg.mpr hχ) htail_nonneg) hV

/-- With `χ ≤ 0`, the `χ U^(m+γ)` contribution is nonpositive. -/
theorem upper_exp_gamma_chi_term_nonpos
    (p : CMParams) {κ x : ℝ} (hχ : p.χ ≤ 0) :
    p.χ * (expBarrierTail κ x) ^ (p.m + p.γ) ≤ 0 := by
  have htail_nonneg : 0 ≤ (expBarrierTail κ x) ^ (p.m + p.γ) :=
    Real.rpow_nonneg (expBarrierTail_nonneg κ x) _
  exact mul_nonpos_of_nonpos_of_nonneg hχ htail_nonneg

/-- The logistic loss on the upper exponential branch is nonpositive. -/
theorem upper_exp_logistic_term_nonpos
    (p : CMParams) {κ x : ℝ} :
    - (expBarrierTail κ x) ^ (p.α + 1) ≤ 0 := by
  have htail_nonneg : 0 ≤ (expBarrierTail κ x) ^ (p.α + 1) :=
    Real.rpow_nonneg (expBarrierTail_nonneg κ x) _
  linarith

/-- If `κt ≤ a κ`, then the `a`-power of the `κ` tail decays no slower than the
`κt` tail on the right half-line. -/
theorem expBarrierTail_rpow_le_of_kappat_le
    {κ κt a x : ℝ} (hx : 0 ≤ x) (hκt : κt ≤ a * κ) :
    (expBarrierTail κ x) ^ a ≤ expBarrierTail κt x := by
  unfold expBarrierTail
  rw [← Real.exp_mul]
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_right hκt hx
  nlinarith

theorem upper_logistic_decay_le_kappat
    (p : CMParams) {κ κt x : ℝ}
    (hx : 0 ≤ x) (hκt : κt ≤ (1 + p.α) * κ) :
    (expBarrierTail κ x) ^ (p.α + 1) ≤ expBarrierTail κt x := by
  have hκt' : κt ≤ (p.α + 1) * κ := by
    convert hκt using 1
    ring
  exact expBarrierTail_rpow_le_of_kappat_le (κ := κ) (κt := κt)
    (a := p.α + 1) (x := x) hx hκt'

theorem upper_m_gamma_decay_le_kappat
    (p : CMParams) {κ κt x : ℝ}
    (hx : 0 ≤ x) (hκt : κt ≤ (p.m + p.γ) * κ) :
    (expBarrierTail κ x) ^ (p.m + p.γ) ≤ expBarrierTail κt x :=
  expBarrierTail_rpow_le_of_kappat_le (κ := κ) (κt := κt)
    (a := p.m + p.γ) (x := x) hx hκt

theorem upper_m_half_decay_le_kappat
    (p : CMParams) {κ κt x : ℝ}
    (hx : 0 ≤ x) (hκt : κt ≤ p.m * κ + 1 / 2) :
    (expBarrierTail κ x) ^ p.m * Real.exp (-(1 / 2) * x) ≤
      expBarrierTail κt x := by
  unfold expBarrierTail
  rw [← Real.exp_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_right hκt hx
  nlinarith

theorem lowerBarrierCore_le_tail {κ κt D x : ℝ} (hD : 0 ≤ D) :
    lowerBarrierCore κ κt D x ≤ expBarrierTail κ x := by
  unfold lowerBarrierCore
  have hnonneg : 0 ≤ D * expBarrierTail κt x :=
    mul_nonneg hD (expBarrierTail_nonneg κt x)
  linarith

theorem lowerBarrierCore_rpow_le_tail_rpow
    {κ κt D x a : ℝ} (hD : 0 ≤ D)
    (hcore : 0 ≤ lowerBarrierCore κ κt D x) (ha : 0 ≤ a) :
    (lowerBarrierCore κ κt D x) ^ a ≤ (expBarrierTail κ x) ^ a :=
  Real.rpow_le_rpow hcore (lowerBarrierCore_le_tail hD) ha

/-- The quadratic at `κt` factors when the speed is written as
`c = κ + κ⁻¹`. -/
theorem kappat_quadratic_eq_prod_of_speed
    {c κ κt : ℝ} (hκ0 : κ ≠ 0) (hc : c = κ + κ⁻¹) :
    κt ^ 2 - c * κt + 1 = (κt - κ) * (κt - κ⁻¹) := by
  rw [hc]
  field_simp [hκ0]
  ring

/-- The same factorization with `κ = waveExponent c`. -/
theorem kappat_quadratic_eq_prod_waveExponent
    {c κt : ℝ} (hc : 2 ≤ c) :
    κt ^ 2 - c * κt + 1 =
      (κt - waveExponent c) * (κt - (waveExponent c)⁻¹) := by
  exact kappat_quadratic_eq_prod_of_speed
    (ne_of_gt (waveExponent_pos hc)) (waveSpeed_eq hc)

theorem kappat_quadratic_nonpos_of_between
    {c κ κt : ℝ}
    (hκpos : 0 < κ) (hκlt1 : κ < 1)
    (hc : c = κ + κ⁻¹) (hleft : κ ≤ κt) (hright : κt ≤ 1) :
    κt ^ 2 - c * κt + 1 ≤ 0 := by
  rw [kappat_quadratic_eq_prod_of_speed (ne_of_gt hκpos) hc]
  have hinv_gt_one : 1 < κ⁻¹ := by
    rw [one_lt_inv₀ hκpos]
    exact hκlt1
  have hnonneg : 0 ≤ κt - κ := by linarith
  have hnonpos : κt - κ⁻¹ ≤ 0 := by linarith
  exact mul_nonpos_of_nonneg_of_nonpos hnonneg hnonpos

theorem kappat_quadratic_nonpos_waveExponent
    {c κt : ℝ} (hc : 2 < c)
    (hleft : waveExponent c ≤ κt) (hright : κt ≤ 1) :
    κt ^ 2 - c * κt + 1 ≤ 0 := by
  exact kappat_quadratic_nonpos_of_between
    (waveExponent_pos (le_of_lt hc)) (waveExponent_lt_one hc)
    (waveSpeed_eq (le_of_lt hc)) hleft hright

/-- Under the usual lower-barrier interval, the `κt` linear correction in the
currently encoded lower residual is nonnegative.  This sign is useful for
auditing the direction of the lower inequality. -/
theorem lower_linear_correction_nonneg_waveExponent
    {c κt D x : ℝ} (hc : 2 < c)
    (hleft : waveExponent c ≤ κt) (hright : κt ≤ 1) (hD : 0 ≤ D) :
    0 ≤ -D * (κt ^ 2 - c * κt + 1) * expBarrierTail κt x := by
  have hquad : κt ^ 2 - c * κt + 1 ≤ 0 :=
    kappat_quadratic_nonpos_waveExponent hc hleft hright
  have hfirst : 0 ≤ -D * (κt ^ 2 - c * κt + 1) := by
    nlinarith
  exact mul_nonneg hfirst (expBarrierTail_nonneg κt x)

/-- Assemble the current barrier-inequality structure from the closed κ
cancellation plus explicit named domination hypotheses. -/
theorem wholeLineExponentialBarrierInequalities_of_waveExponent
    {p : CMParams} {c κt D : ℝ} {V Vx : ℝ → ℝ}
    (hc : 2 ≤ c)
    (hκt : waveExponent c < κt)
    (hD : 1 ≤ D)
    (hκtα : κt ≤ (1 + p.α) * waveExponent c)
    (hκtm : κt ≤ p.m * waveExponent c + 1 / 2)
    (hκt1 : κt ≤ 1)
    (hconst :
      ∀ x, x ≤ 0 → 0 ≤ p.χ * (1 - V x))
    (hupper :
      UpperExponentialBranchDomination p (waveExponent c) V Vx)
    (hlower :
      LowerPositiveBranchDomination p c (waveExponent c) κt D V Vx) :
    WholeLineExponentialBarrierInequalities p c (waveExponent c) κt D V Vx where
  params := exponentialBarrierParameterData_of_waveExponent
    hc hκt hD hκtα hκtm hκt1
  upper_constant_branch := by
    intro x hx
    rw [upperConstantBranchResidual_eq p c V Vx x]
    exact hconst x hx
  upper_exp_branch := by
    exact upperBarrier_supersolution p (waveExponent_quadratic hc) hupper
  lower_zero_branch := by
    intro x _hx
    rw [lowerZeroBranchResidual_eq_zero p c V Vx x]
  lower_positive_branch := by
    exact lowerBarrier_subsolution p (waveExponent_quadratic hc) hlower

#print axioms upperExponentialBranchResidual_cancel
#print axioms upperExponentialBranchResidual_waveExponent_cancel
#print axioms upperBarrier_supersolution
#print axioms upperConstantBranchResidual_eq
#print axioms lowerZeroBranchResidual_eq_zero
#print axioms lowerPositiveBranchResidual_cancel
#print axioms lowerPositiveBranchResidual_waveExponent_cancel
#print axioms lowerBarrier_subsolution
#print axioms expBarrierTail_rpow_le_of_kappat_le
#print axioms kappat_quadratic_eq_prod_waveExponent
#print axioms lower_linear_correction_nonneg_waveExponent
#print axioms wholeLineExponentialBarrierInequalities_of_waveExponent

end ShenWork.PaperOne
