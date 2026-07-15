import ShenWork.Paper1.Theorem12WeightedResolverEta

open Filter MeasureTheory Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Finite-horizon weighted finiteness

This file starts the linear singular-Volterra closure of the moving-frame
weighted error.  The heat operators below act after conjugation by
`exp (eta * x)`.
-/

/-! ## A signed version of the Markov-kernel `L²` estimate -/

theorem markovKernel_signed_l2_contraction
    (K : ℝ → ℝ → ℝ) (q : ℝ → ℝ)
    (hK_meas : Measurable (Function.uncurry K))
    (hK_nn : ∀ x y, 0 ≤ K x y)
    (hrow_int : ∀ x, Integrable (K x))
    (hrow_mass : ∀ x, ∫ y : ℝ, K x y = 1)
    (hcol_int : ∀ y, Integrable (fun x => K x y))
    (hcol_mass : ∀ y, ∫ x : ℝ, K x y = 1)
    (hq_meas : Measurable q)
    (hq_sq : Integrable (fun y => q y ^ 2)) :
    Integrable (fun x => (∫ y : ℝ, K x y * q y) ^ 2) ∧
      (∫ x : ℝ, (∫ y : ℝ, K x y * q y) ^ 2) ≤
        ∫ y : ℝ, q y ^ 2 := by
  let T : ℝ → ℝ := fun x => ∫ y : ℝ, K x y * |q y|
  let R : ℝ → ℝ := fun x => ∫ y : ℝ, K x y * q y
  have hT := markovKernel_l2_contraction K q hK_meas hK_nn
    hrow_int hrow_mass hcol_int hcol_mass hq_meas hq_sq
  have hR_strong : StronglyMeasurable R := by
    apply StronglyMeasurable.integral_prod_right
    exact (hK_meas.mul (hq_meas.comp measurable_snd)).stronglyMeasurable
  have hpoint : ∀ x, R x ^ 2 ≤ T x ^ 2 := by
    intro x
    have habs : |R x| ≤ T x := by
      dsimp only [R, T]
      calc
        |∫ y : ℝ, K x y * q y| ≤
            ∫ y : ℝ, ‖K x y * q y‖ := by
          simpa [Real.norm_eq_abs] using
            (norm_integral_le_integral_norm (fun y => K x y * q y))
        _ = ∫ y : ℝ, K x y * |q y| := by
          apply integral_congr_ae
          filter_upwards with y
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hK_nn x y)]
    have hT0 : 0 ≤ T x := by
      dsimp only [T]
      exact integral_nonneg fun y => mul_nonneg (hK_nn x y) (abs_nonneg _)
    have hsquare := (sq_le_sq₀ (abs_nonneg (R x)) hT0).2 habs
    simpa [sq_abs] using hsquare
  have hR_int : Integrable (fun x => R x ^ 2) := by
    refine Integrable.mono' hT.1 (hR_strong.pow 2).aestronglyMeasurable ?_
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpoint x
  refine ⟨by simpa [R] using hR_int, ?_⟩
  calc
    (∫ x : ℝ, (∫ y : ℝ, K x y * q y) ^ 2) =
        ∫ x : ℝ, R x ^ 2 := by rfl
    _ ≤ ∫ x : ℝ, T x ^ 2 := integral_mono hR_int hT.1 hpoint
    _ ≤ ∫ y : ℝ, q y ^ 2 := hT.2

/-! ## The conjugated moving heat semigroup -/

/-- Growth factor of the heat flow after the exponential conjugation and
translation to the frame moving at speed `c`. -/
def weightedMovingHeatGrowth (eta c t : ℝ) : ℝ :=
  Real.exp ((eta ^ 2 - c * eta) * t)

/-- The translated Gaussian Markov kernel left after exponential
conjugation. -/
def weightedMovingHeatMarkovKernel
    (eta c t x y : ℝ) : ℝ :=
  heatKernel t (x + (c - 2 * eta) * t - y)

/-- The conjugated heat semigroup `M_eta S_c(t) M_eta⁻¹`. -/
def weightedMovingHeatEta
    (eta c t : ℝ) (q : ℝ → ℝ) (x : ℝ) : ℝ :=
  weightedMovingHeatGrowth eta c t *
    ∫ y : ℝ, weightedMovingHeatMarkovKernel eta c t x y * q y

theorem weightedMovingHeatMarkovKernel_measurable
    (eta c t : ℝ) :
    Measurable
      (Function.uncurry (weightedMovingHeatMarkovKernel eta c t)) := by
  unfold weightedMovingHeatMarkovKernel Function.uncurry heatKernel
  fun_prop

theorem weightedMovingHeatMarkovKernel_nonneg
    {t : ℝ} (ht : 0 < t) (eta c x y : ℝ) :
    0 ≤ weightedMovingHeatMarkovKernel eta c t x y := by
  exact heatKernel_nonneg ht _

theorem weightedMovingHeatMarkovKernel_row_integrable
    {t : ℝ} (ht : 0 < t) (eta c x : ℝ) :
    Integrable (weightedMovingHeatMarkovKernel eta c t x) := by
  simpa [weightedMovingHeatMarkovKernel] using
    heatKernel_translated_integrable ht (x + (c - 2 * eta) * t)

theorem weightedMovingHeatMarkovKernel_row_mass
    {t : ℝ} (ht : 0 < t) (eta c x : ℝ) :
    ∫ y : ℝ, weightedMovingHeatMarkovKernel eta c t x y = 1 := by
  simpa [weightedMovingHeatMarkovKernel] using
    heatKernel_integral_translated ht (x + (c - 2 * eta) * t)

theorem weightedMovingHeatMarkovKernel_col_integrable
    {t : ℝ} (ht : 0 < t) (eta c y : ℝ) :
    Integrable (fun x => weightedMovingHeatMarkovKernel eta c t x y) := by
  let a : ℝ := y - (c - 2 * eta) * t
  have h := heatKernel_translated_integrable ht a
  refine h.congr (Eventually.of_forall fun x => ?_)
  change heatKernel t (a - x) =
    weightedMovingHeatMarkovKernel eta c t x y
  unfold weightedMovingHeatMarkovKernel
  rw [heatKernel_sub_comm]
  congr 1
  dsimp [a]
  ring

theorem weightedMovingHeatMarkovKernel_col_mass
    {t : ℝ} (ht : 0 < t) (eta c y : ℝ) :
    ∫ x : ℝ, weightedMovingHeatMarkovKernel eta c t x y = 1 := by
  have h := heatKernel_integral_translated ht
    (y - (c - 2 * eta) * t)
  rw [← h]
  apply integral_congr_ae
  filter_upwards with x
  unfold weightedMovingHeatMarkovKernel
  rw [heatKernel_sub_comm]
  congr 1
  ring

theorem weightedMovingHeat_conjugation_kernel_identity
    {t : ℝ} (ht : 0 < t) (eta c x y : ℝ) :
    Real.exp (eta * x) * heatKernel t (x + c * t - y) =
      weightedMovingHeatGrowth eta c t *
        (weightedMovingHeatMarkovKernel eta c t x y *
          Real.exp (eta * y)) := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hexponent :
      eta * x + -(x + c * t - y) ^ 2 / (4 * t) =
        (eta ^ 2 - c * eta) * t +
          (-(x + (c - 2 * eta) * t - y) ^ 2 / (4 * t) + eta * y) := by
    field_simp [ht0]
    ring
  unfold weightedMovingHeatGrowth weightedMovingHeatMarkovKernel heatKernel
  calc
    Real.exp (eta * x) *
        (1 / Real.sqrt (4 * Real.pi * t) *
          Real.exp (-(x + c * t - y) ^ 2 / (4 * t))) =
        (1 / Real.sqrt (4 * Real.pi * t)) *
          Real.exp
            (eta * x + -(x + c * t - y) ^ 2 / (4 * t)) := by
      rw [Real.exp_add]
      ring
    _ = (1 / Real.sqrt (4 * Real.pi * t)) *
        Real.exp ((eta ^ 2 - c * eta) * t +
          (-(x + (c - 2 * eta) * t - y) ^ 2 / (4 * t) +
            eta * y)) := by rw [hexponent]
    _ = Real.exp ((eta ^ 2 - c * eta) * t) *
        (1 / Real.sqrt (4 * Real.pi * t) *
          Real.exp (-(x + (c - 2 * eta) * t - y) ^ 2 / (4 * t)) *
            Real.exp (eta * y)) := by
      rw [Real.exp_add, Real.exp_add]
      ring

/-- Operator bound 1.  The conjugated moving heat semigroup has norm at most
`exp ((eta²-c*eta)t)` on `L²`. -/
theorem weighted_moving_heat_L2eta_bounded
    {eta c t : ℝ} (ht : 0 < t)
    {q : ℝ → ℝ} (hq_meas : Measurable q)
    (hq_sq : Integrable (fun y => q y ^ 2)) :
    Integrable (fun x => weightedMovingHeatEta eta c t q x ^ 2) ∧
      (∫ x : ℝ, weightedMovingHeatEta eta c t q x ^ 2) ≤
        weightedMovingHeatGrowth eta c t ^ 2 *
          ∫ y : ℝ, q y ^ 2 := by
  have hcontract := markovKernel_signed_l2_contraction
    (weightedMovingHeatMarkovKernel eta c t) q
    (weightedMovingHeatMarkovKernel_measurable eta c t)
    (weightedMovingHeatMarkovKernel_nonneg ht eta c)
    (weightedMovingHeatMarkovKernel_row_integrable ht eta c)
    (weightedMovingHeatMarkovKernel_row_mass ht eta c)
    (weightedMovingHeatMarkovKernel_col_integrable ht eta c)
    (weightedMovingHeatMarkovKernel_col_mass ht eta c)
    hq_meas hq_sq
  let R : ℝ → ℝ := fun x =>
    ∫ y : ℝ, weightedMovingHeatMarkovKernel eta c t x y * q y
  have hout : Integrable
      (fun x => weightedMovingHeatGrowth eta c t ^ 2 * R x ^ 2) :=
    hcontract.1.const_mul _
  refine ⟨?_, ?_⟩
  · simpa [weightedMovingHeatEta, R, mul_pow] using hout
  · calc
      (∫ x : ℝ, weightedMovingHeatEta eta c t q x ^ 2) =
          weightedMovingHeatGrowth eta c t ^ 2 *
            ∫ x : ℝ, R x ^ 2 := by
        simp only [weightedMovingHeatEta, R, mul_pow]
        rw [integral_const_mul]
      _ ≤ weightedMovingHeatGrowth eta c t ^ 2 *
          ∫ y : ℝ, q y ^ 2 :=
        mul_le_mul_of_nonneg_left hcontract.2 (sq_nonneg _)

/-! ## The spatial derivative of the conjugated heat semigroup -/

def weightedMovingHeatGradientMarkovKernel
    (eta c t x y : ℝ) : ℝ :=
  Real.sqrt (Real.pi * t) *
    |deriv (fun z : ℝ => heatKernel t z)
      (x + (c - 2 * eta) * t - y)|

/-- The spatial derivative `∂x S_eta(t)`, in kernel form. -/
def weightedMovingHeatGradientEta
    (eta c t : ℝ) (q : ℝ → ℝ) (x : ℝ) : ℝ :=
  weightedMovingHeatGrowth eta c t *
    ∫ y : ℝ,
      deriv (fun z : ℝ => heatKernel t z)
        (x + (c - 2 * eta) * t - y) * q y

private theorem sqrt_pi_mul_two_div_sqrt_four_pi_mul
    {t : ℝ} (ht : 0 < t) :
    Real.sqrt (Real.pi * t) *
        (2 / Real.sqrt (4 * Real.pi * t)) = 1 := by
  have hpit : 0 < Real.pi * t := by positivity
  have hs : 0 < Real.sqrt (Real.pi * t) := Real.sqrt_pos.mpr hpit
  have hs4 : Real.sqrt (4 * Real.pi * t) =
      2 * Real.sqrt (Real.pi * t) := by
    rw [show 4 * Real.pi * t = 4 * (Real.pi * t) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  rw [hs4]
  field_simp [ne_of_gt hs]

theorem weightedMovingHeatGradientMarkovKernel_measurable
    {t : ℝ} (ht : 0 < t) (eta c : ℝ) :
    Measurable
      (Function.uncurry
        (weightedMovingHeatGradientMarkovKernel eta c t)) := by
  unfold weightedMovingHeatGradientMarkovKernel Function.uncurry
  simp_rw [deriv_heatKernel ht]
  unfold heatKernel
  fun_prop

theorem weightedMovingHeatGradientMarkovKernel_nonneg
    (eta c t x y : ℝ) :
    0 ≤ weightedMovingHeatGradientMarkovKernel eta c t x y := by
  unfold weightedMovingHeatGradientMarkovKernel
  positivity

theorem weightedMovingHeatGradientMarkovKernel_row_integrable
    {t : ℝ} (ht : 0 < t) (eta c x : ℝ) :
    Integrable (weightedMovingHeatGradientMarkovKernel eta c t x) := by
  let a : ℝ := x + (c - 2 * eta) * t
  have h := heatKernel_deriv_abs_translated_integrable ht a
  refine (h.const_mul (Real.sqrt (Real.pi * t))).congr ?_
  exact Eventually.of_forall fun y => by
    unfold weightedMovingHeatGradientMarkovKernel
    change Real.sqrt (Real.pi * t) *
        |deriv (fun z : ℝ => heatKernel t (z - y)) a| =
      Real.sqrt (Real.pi * t) *
        |deriv (fun z : ℝ => heatKernel t z)
          (x + (c - 2 * eta) * t - y)|
    rw [deriv_heatKernel_translated_left ht a y]
    rw [deriv_heatKernel ht]

theorem weightedMovingHeatGradientMarkovKernel_row_mass
    {t : ℝ} (ht : 0 < t) (eta c x : ℝ) :
    ∫ y : ℝ, weightedMovingHeatGradientMarkovKernel eta c t x y = 1 := by
  unfold weightedMovingHeatGradientMarkovKernel
  rw [integral_const_mul]
  have h := heatKernel_deriv_abs_integral_translated ht
    (x + (c - 2 * eta) * t)
  have heq :
      (fun y : ℝ =>
        |deriv (fun z : ℝ => heatKernel t z)
          (x + (c - 2 * eta) * t - y)|) =
      fun y : ℝ =>
        |deriv (fun z : ℝ => heatKernel t (z - y))
          (x + (c - 2 * eta) * t)| := by
    funext y
    rw [deriv_heatKernel_translated_left ht,
      deriv_heatKernel ht]
  rw [heq, h]
  exact sqrt_pi_mul_two_div_sqrt_four_pi_mul ht

theorem weightedMovingHeatGradientMarkovKernel_col_integrable
    {t : ℝ} (ht : 0 < t) (eta c y : ℝ) :
    Integrable
      (fun x => weightedMovingHeatGradientMarkovKernel eta c t x y) := by
  let a : ℝ := y - (c - 2 * eta) * t
  have h := (heatKernel_deriv_abs_integrable ht).comp_add_right (-a)
  refine (h.const_mul (Real.sqrt (Real.pi * t))).congr ?_
  exact Eventually.of_forall fun x => by
    unfold weightedMovingHeatGradientMarkovKernel
    dsimp [a]
    ring

theorem weightedMovingHeatGradientMarkovKernel_col_mass
    {t : ℝ} (ht : 0 < t) (eta c y : ℝ) :
    ∫ x : ℝ, weightedMovingHeatGradientMarkovKernel eta c t x y = 1 := by
  let a : ℝ := y - (c - 2 * eta) * t
  have htranslate := integral_add_right_eq_self
    (μ := (volume : Measure ℝ))
    (fun x : ℝ => |deriv (fun z : ℝ => heatKernel t z) x|) (-a)
  have hbase := heatKernel_deriv_abs_integral ht
  unfold weightedMovingHeatGradientMarkovKernel
  rw [integral_const_mul]
  have heq :
      (fun x : ℝ =>
        |deriv (fun z : ℝ => heatKernel t z)
          (x + (c - 2 * eta) * t - y)|) =
      fun x : ℝ =>
        |deriv (fun z : ℝ => heatKernel t z) (x + -a)| := by
    funext x
    congr 2
    dsimp [a]
    ring
  rw [heq, htranslate, hbase]
  exact sqrt_pi_mul_two_div_sqrt_four_pi_mul ht

/-- Operator bound 2.  The derivative of the conjugated semigroup has the
integrable singular bound `exp ((eta²-c*eta)t) / sqrt (pi*t)`. -/
theorem weighted_moving_heat_gradient_L2eta_bounded
    {eta c t : ℝ} (ht : 0 < t)
    {q : ℝ → ℝ} (hq_meas : Measurable q)
    (hq_sq : Integrable (fun y => q y ^ 2)) :
    Integrable
      (fun x => weightedMovingHeatGradientEta eta c t q x ^ 2) ∧
      (∫ x : ℝ, weightedMovingHeatGradientEta eta c t q x ^ 2) ≤
        (weightedMovingHeatGrowth eta c t /
          Real.sqrt (Real.pi * t)) ^ 2 *
            ∫ y : ℝ, q y ^ 2 := by
  let K := weightedMovingHeatGradientMarkovKernel eta c t
  have henvelope := markovKernel_l2_contraction K q
    (weightedMovingHeatGradientMarkovKernel_measurable ht eta c)
    (weightedMovingHeatGradientMarkovKernel_nonneg eta c t)
    (weightedMovingHeatGradientMarkovKernel_row_integrable ht eta c)
    (weightedMovingHeatGradientMarkovKernel_row_mass ht eta c)
    (weightedMovingHeatGradientMarkovKernel_col_integrable ht eta c)
    (weightedMovingHeatGradientMarkovKernel_col_mass ht eta c)
    hq_meas hq_sq
  have hs : 0 < Real.sqrt (Real.pi * t) := by positivity
  let T : ℝ → ℝ := fun x => ∫ y : ℝ, K x y * |q y|
  have hderiv_meas : Measurable (Function.uncurry (fun x y =>
      deriv (fun z : ℝ => heatKernel t z)
        (x + (c - 2 * eta) * t - y))) := by
    unfold Function.uncurry
    simp_rw [deriv_heatKernel ht]
    unfold heatKernel
    fun_prop
  have hout_strong : StronglyMeasurable
      (weightedMovingHeatGradientEta eta c t q) := by
    unfold weightedMovingHeatGradientEta
    apply stronglyMeasurable_const.mul
    apply StronglyMeasurable.integral_prod_right
    exact (hderiv_meas.mul
      (hq_meas.comp measurable_snd)).stronglyMeasurable
  have hrawFormula : ∀ x,
      (∫ y : ℝ,
        |deriv (fun z : ℝ => heatKernel t z)
          (x + (c - 2 * eta) * t - y) * q y|) =
        T x / Real.sqrt (Real.pi * t) := by
    intro x
    have hT : T x = Real.sqrt (Real.pi * t) *
        ∫ y : ℝ,
          |deriv (fun z : ℝ => heatKernel t z)
            (x + (c - 2 * eta) * t - y) * q y| := by
      dsimp [T, K, weightedMovingHeatGradientMarkovKernel]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      rw [abs_mul]
      ring
    rw [hT]
    field_simp [ne_of_gt hs]
  have hpointAbs : ∀ x,
      |weightedMovingHeatGradientEta eta c t q x| ≤
        (weightedMovingHeatGrowth eta c t /
          Real.sqrt (Real.pi * t)) * T x := by
    intro x
    have hgrowth : 0 ≤ weightedMovingHeatGrowth eta c t :=
      (Real.exp_pos _).le
    unfold weightedMovingHeatGradientEta
    rw [abs_mul, abs_of_nonneg hgrowth]
    calc
      weightedMovingHeatGrowth eta c t *
          |∫ y : ℝ,
            deriv (fun z : ℝ => heatKernel t z)
              (x + (c - 2 * eta) * t - y) * q y| ≤
          weightedMovingHeatGrowth eta c t *
            ∫ y : ℝ,
              ‖deriv (fun z : ℝ => heatKernel t z)
                (x + (c - 2 * eta) * t - y) * q y‖ :=
        mul_le_mul_of_nonneg_left
          (by simpa [Real.norm_eq_abs] using
            norm_integral_le_integral_norm (fun y : ℝ =>
              deriv (fun z : ℝ => heatKernel t z)
                (x + (c - 2 * eta) * t - y) * q y)) hgrowth
      _ = weightedMovingHeatGrowth eta c t *
          (T x / Real.sqrt (Real.pi * t)) := by
        have hnorm :
            (∫ y : ℝ,
              ‖deriv (fun z : ℝ => heatKernel t z)
                (x + (c - 2 * eta) * t - y) * q y‖) =
              T x / Real.sqrt (Real.pi * t) := by
          simpa [Real.norm_eq_abs] using hrawFormula x
        rw [hnorm]
      _ = (weightedMovingHeatGrowth eta c t /
          Real.sqrt (Real.pi * t)) * T x := by ring
  have hcoef0 : 0 ≤ weightedMovingHeatGrowth eta c t /
      Real.sqrt (Real.pi * t) := div_nonneg (Real.exp_nonneg _) hs.le
  have hpointSq : ∀ x,
      weightedMovingHeatGradientEta eta c t q x ^ 2 ≤
        (weightedMovingHeatGrowth eta c t /
          Real.sqrt (Real.pi * t)) ^ 2 * T x ^ 2 := by
    intro x
    have hT0 : 0 ≤ T x := by
      dsimp [T]
      exact integral_nonneg fun y => mul_nonneg
        (weightedMovingHeatGradientMarkovKernel_nonneg eta c t x y)
        (abs_nonneg _)
    have hsquare := (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg hcoef0 hT0)).2 (hpointAbs x)
    simpa [sq_abs, mul_pow] using hsquare
  have hdom : Integrable (fun x =>
      (weightedMovingHeatGrowth eta c t /
        Real.sqrt (Real.pi * t)) ^ 2 * T x ^ 2) :=
    henvelope.1.const_mul _
  have hout : Integrable
      (fun x => weightedMovingHeatGradientEta eta c t q x ^ 2) := by
    refine Integrable.mono' hdom
      (hout_strong.pow 2).aestronglyMeasurable ?_
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpointSq x
  refine ⟨?_, ?_⟩
  · exact hout
  · calc
      (∫ x : ℝ, weightedMovingHeatGradientEta eta c t q x ^ 2) =
          ∫ x : ℝ, weightedMovingHeatGradientEta eta c t q x ^ 2 := rfl
      _ ≤ ∫ x : ℝ,
          (weightedMovingHeatGrowth eta c t /
            Real.sqrt (Real.pi * t)) ^ 2 * T x ^ 2 :=
        integral_mono hout hdom hpointSq
      _ = (weightedMovingHeatGrowth eta c t /
              Real.sqrt (Real.pi * t)) ^ 2 *
            ∫ x : ℝ, T x ^ 2 := by
        rw [integral_const_mul]
      _ ≤ (weightedMovingHeatGrowth eta c t /
              Real.sqrt (Real.pi * t)) ^ 2 *
            ∫ y : ℝ, q y ^ 2 :=
        mul_le_mul_of_nonneg_left henvelope.2 (sq_nonneg _)

/-! ## The weighted chemotaxis and reaction operators -/

def weightedFluxDifference
    (p : CMParams) (eta : ℝ) (u₂ u₁ : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (eta * x) *
    (u₂ x ^ p.m * deriv (frozenElliptic p u₂) x -
      u₁ x ^ p.m * deriv (frozenElliptic p u₁) x)

def weightedFluxSquareConstant (p : CMParams) (M eta : ℝ) : ℝ :=
  2 * (M ^ p.m * (weightedResolverEtaConstant eta *
      (p.γ * M ^ (p.γ - 1)))) ^ 2 +
    2 * ((p.m * M ^ (p.m - 1)) * M ^ p.γ) ^ 2

def weightedChemotaxisOperatorDifference
    (p : CMParams) (eta : ℝ) (u₂ u₁ : ℝ → ℝ) (x : ℝ) : ℝ :=
  (-p.χ) * weightedFluxDifference p eta u₂ u₁ x

def weightedChemotaxisOperatorSquareConstant
    (p : CMParams) (M eta : ℝ) : ℝ :=
  p.χ ^ 2 * weightedFluxSquareConstant p M eta

def weightedReactionDifference
    (p : CMParams) (eta : ℝ) (u₂ u₁ : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (eta * x) *
    (reactionFun p.α (u₂ x) - reactionFun p.α (u₁ x))

private theorem weighted_raw_difference_sq_integrable
    {eta : ℝ} {u₂ u₁ : ℝ → ℝ}
    (hclose : Integrable (fun x =>
      Real.exp (2 * eta * x) * |u₂ x - u₁ x| ^ 2)) :
    Integrable (fun x =>
      (Real.exp (eta * x) * (u₂ x - u₁ x)) ^ 2) := by
  refine hclose.congr (Eventually.of_forall fun x => ?_)
  change Real.exp (2 * eta * x) * |u₂ x - u₁ x| ^ 2 =
    (Real.exp (eta * x) * (u₂ x - u₁ x)) ^ 2
  symm
  rw [mul_pow, sq_abs, show Real.exp (eta * x) ^ 2 =
      Real.exp (2 * eta * x) by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring]

private theorem weighted_raw_difference_sq_integral_eq
    {eta : ℝ} {u₂ u₁ : ℝ → ℝ} :
    (∫ x : ℝ, (Real.exp (eta * x) * (u₂ x - u₁ x)) ^ 2) =
      ∫ x : ℝ, Real.exp (2 * eta * x) * |u₂ x - u₁ x| ^ 2 := by
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change (Real.exp (eta * x) * (u₂ x - u₁ x)) ^ 2 =
      Real.exp (2 * eta * x) * |u₂ x - u₁ x| ^ 2
    rw [mul_pow, sq_abs, show Real.exp (eta * x) ^ 2 =
        Real.exp (2 * eta * x) by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring]

/-- Operator bound 5.  The nonlinear flux difference, with its coefficients
frozen at the two trapped profiles, is bounded linearly by their weighted
population difference. -/
theorem weighted_flux_difference_L2eta_bounded
    (p : CMParams) {M eta : ℝ}
    (hM : 0 ≤ M) (heta_nonneg : 0 ≤ eta) (heta_one : eta < 1)
    {u₂ u₁ : ℝ → ℝ}
    (hu₂ : IsCUnifBdd u₂) (hu₁ : IsCUnifBdd u₁)
    (hu₂_mem : ∀ x, u₂ x ∈ Set.Icc (0 : ℝ) M)
    (hu₁_mem : ∀ x, u₁ x ∈ Set.Icc (0 : ℝ) M)
    (hclose : Integrable (fun x =>
      Real.exp (2 * eta * x) * |u₂ x - u₁ x| ^ 2)) :
    Integrable (fun x => (weightedFluxDifference p eta u₂ u₁ x) ^ 2) ∧
      (∫ x : ℝ, (weightedFluxDifference p eta u₂ u₁ x) ^ 2) ≤
        weightedFluxSquareConstant p M eta *
          ∫ x : ℝ,
            Real.exp (2 * eta * x) * |u₂ x - u₁ x| ^ 2 := by
  let A : ℝ := M ^ p.m
  let B : ℝ := (p.m * M ^ (p.m - 1)) * M ^ p.γ
  let K : ℝ := weightedResolverEtaConstant eta *
    (p.γ * M ^ (p.γ - 1))
  let dV : ℝ → ℝ := fun x =>
    Real.exp (eta * x) *
      (deriv (frozenElliptic p u₂) x -
        deriv (frozenElliptic p u₁) x)
  let q : ℝ → ℝ := fun x =>
    Real.exp (eta * x) * (u₂ x - u₁ x)
  have hgrad := weighted_frozenElliptic_gradient_difference_L2eta_bounded
    p hM heta_nonneg heta_one hu₁ hu₂ hu₁_mem hu₂_mem hclose
  have hq : Integrable (fun x => q x ^ 2) := by
    simpa [q] using weighted_raw_difference_sq_integrable hclose
  have hA0 : 0 ≤ A := Real.rpow_nonneg hM _
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg
      (mul_nonneg (le_trans zero_le_one p.hm)
        (Real.rpow_nonneg hM _))
      (Real.rpow_nonneg hM _)
  have hpoint : ∀ x,
      |weightedFluxDifference p eta u₂ u₁ x| ≤
        A * |dV x| + B * |q x| := by
    intro x
    have hu₂m : u₂ x ^ p.m ≤ M ^ p.m :=
      Real.rpow_le_rpow (hu₂_mem x).1 (hu₂_mem x).2
        (le_trans zero_le_one p.hm)
    have hpow := abs_rpow_sub_rpow_le_of_mem_Icc
      p.hm hM (hu₂_mem x) (hu₁_mem x)
    have hV := frozenElliptic_deriv_abs_le_rpow_of_Icc
      p hM hu₁ hu₁_mem x
    have hexp0 : 0 ≤ Real.exp (eta * x) := Real.exp_nonneg _
    have hsplit :
        u₂ x ^ p.m * deriv (frozenElliptic p u₂) x -
            u₁ x ^ p.m * deriv (frozenElliptic p u₁) x =
          u₂ x ^ p.m *
              (deriv (frozenElliptic p u₂) x -
                deriv (frozenElliptic p u₁) x) +
            (u₂ x ^ p.m - u₁ x ^ p.m) *
              deriv (frozenElliptic p u₁) x := by ring
    rw [weightedFluxDifference, hsplit, abs_mul,
      abs_of_nonneg hexp0]
    calc
      Real.exp (eta * x) *
          |u₂ x ^ p.m *
              (deriv (frozenElliptic p u₂) x -
                deriv (frozenElliptic p u₁) x) +
            (u₂ x ^ p.m - u₁ x ^ p.m) *
              deriv (frozenElliptic p u₁) x| ≤
          Real.exp (eta * x) *
            (|u₂ x ^ p.m| *
                |deriv (frozenElliptic p u₂) x -
                  deriv (frozenElliptic p u₁) x| +
              |u₂ x ^ p.m - u₁ x ^ p.m| *
                |deriv (frozenElliptic p u₁) x|) := by
        gcongr
        simpa only [abs_mul] using abs_add_le
          (u₂ x ^ p.m *
            (deriv (frozenElliptic p u₂) x -
              deriv (frozenElliptic p u₁) x))
          ((u₂ x ^ p.m - u₁ x ^ p.m) *
            deriv (frozenElliptic p u₁) x)
      _ ≤ A * |dV x| + B * |q x| := by
        rw [abs_of_nonneg (Real.rpow_nonneg (hu₂_mem x).1 _)]
        dsimp [A, B, dV, q]
        rw [abs_mul, abs_mul, abs_of_nonneg hexp0]
        calc
          Real.exp (eta * x) *
              (u₂ x ^ p.m *
                  |deriv (frozenElliptic p u₂) x -
                    deriv (frozenElliptic p u₁) x| +
                |u₂ x ^ p.m - u₁ x ^ p.m| *
                  |deriv (frozenElliptic p u₁) x|) ≤
          Real.exp (eta * x) *
                (M ^ p.m *
                    |deriv (frozenElliptic p u₂) x -
                      deriv (frozenElliptic p u₁) x| +
                  (p.m * M ^ (p.m - 1) * |u₂ x - u₁ x|) *
                    M ^ p.γ) := by
            apply mul_le_mul_of_nonneg_left _ hexp0
            apply add_le_add
            · exact mul_le_mul_of_nonneg_right hu₂m (abs_nonneg _)
            · exact mul_le_mul hpow hV (abs_nonneg _)
                (mul_nonneg
                  (mul_nonneg (le_trans zero_le_one p.hm)
                    (Real.rpow_nonneg hM _))
                  (abs_nonneg _))
          _ = M ^ p.m *
                (Real.exp (eta * x) *
                  |deriv (frozenElliptic p u₂) x -
                    deriv (frozenElliptic p u₁) x|) +
              p.m * M ^ (p.m - 1) * M ^ p.γ *
                (Real.exp (eta * x) * |u₂ x - u₁ x|) := by ring
  have hpoint_sq : ∀ x,
      weightedFluxDifference p eta u₂ u₁ x ^ 2 ≤
        2 * A ^ 2 * dV x ^ 2 + 2 * B ^ 2 * q x ^ 2 := by
    intro x
    have hs := (sq_le_sq₀ (abs_nonneg _)
      (add_nonneg (mul_nonneg hA0 (abs_nonneg _))
        (mul_nonneg hB0 (abs_nonneg _)))).2 (hpoint x)
    rw [sq_abs] at hs
    calc
      weightedFluxDifference p eta u₂ u₁ x ^ 2 ≤
          (A * |dV x| + B * |q x|) ^ 2 := hs
      _ ≤ 2 * (A * |dV x|) ^ 2 + 2 * (B * |q x|) ^ 2 := by
        nlinarith [sq_nonneg (A * |dV x| - B * |q x|)]
      _ = 2 * A ^ 2 * dV x ^ 2 + 2 * B ^ 2 * q x ^ 2 := by
        rw [mul_pow, mul_pow, sq_abs, sq_abs]
        ring
  have hdV : Integrable (fun x => dV x ^ 2) := by
    simpa [dV] using hgrad.1
  have hdom : Integrable (fun x =>
      2 * A ^ 2 * dV x ^ 2 + 2 * B ^ 2 * q x ^ 2) :=
    (hdV.const_mul (2 * A ^ 2)).add
      (hq.const_mul (2 * B ^ 2))
  have hflux_cont : Continuous (weightedFluxDifference p eta u₂ u₁) := by
    unfold weightedFluxDifference
    have hm0 : 0 ≤ p.m := le_trans zero_le_one p.hm
    have hp₂ : Continuous (fun x => u₂ x ^ p.m) :=
      hu₂.1.rpow_const (fun _ => Or.inr hm0)
    have hp₁ : Continuous (fun x => u₁ x ^ p.m) :=
      hu₁.1.rpow_const (fun _ => Or.inr hm0)
    have hd₂ : Continuous (deriv (frozenElliptic p u₂)) :=
      (frozenElliptic_deriv_lipschitz_of_Icc
        p hM hu₂ hu₂_mem).continuous
    have hd₁ : Continuous (deriv (frozenElliptic p u₁)) :=
      (frozenElliptic_deriv_lipschitz_of_Icc
        p hM hu₁ hu₁_mem).continuous
    fun_prop
  have hout : Integrable
      (fun x => weightedFluxDifference p eta u₂ u₁ x ^ 2) := by
    refine Integrable.mono' hdom
      (hflux_cont.pow 2).aestronglyMeasurable ?_
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpoint_sq x
  refine ⟨hout, ?_⟩
  calc
    (∫ x : ℝ, weightedFluxDifference p eta u₂ u₁ x ^ 2) ≤
        ∫ x : ℝ, 2 * A ^ 2 * dV x ^ 2 + 2 * B ^ 2 * q x ^ 2 :=
      integral_mono hout hdom hpoint_sq
    _ = 2 * A ^ 2 * (∫ x : ℝ, dV x ^ 2) +
        2 * B ^ 2 * (∫ x : ℝ, q x ^ 2) := by
      rw [integral_add (hdV.const_mul _) (hq.const_mul _),
        integral_const_mul, integral_const_mul]
    _ ≤ 2 * A ^ 2 * (K ^ 2 * ∫ x : ℝ,
          Real.exp (2 * eta * x) * |u₂ x - u₁ x| ^ 2) +
        2 * B ^ 2 * ∫ x : ℝ,
          Real.exp (2 * eta * x) * |u₂ x - u₁ x| ^ 2 := by
      have hqeq := weighted_raw_difference_sq_integral_eq
        (eta := eta) (u₂ := u₂) (u₁ := u₁)
      have hgrad_le : (∫ x : ℝ, dV x ^ 2) ≤
          K ^ 2 * ∫ x : ℝ,
            Real.exp (2 * eta * x) * |u₂ x - u₁ x| ^ 2 := by
        simpa [dV, K] using hgrad.2
      have hq_eq : (∫ x : ℝ, q x ^ 2) =
          ∫ x : ℝ,
            Real.exp (2 * eta * x) * |u₂ x - u₁ x| ^ 2 := by
        simpa [q] using hqeq
      rw [hq_eq]
      exact add_le_add
        (mul_le_mul_of_nonneg_left hgrad_le (by positivity)) le_rfl
    _ = weightedFluxSquareConstant p M eta *
        ∫ x : ℝ,
          Real.exp (2 * eta * x) * |u₂ x - u₁ x| ^ 2 := by
      dsimp [A, B, K, weightedFluxSquareConstant]
      ring

/-- Operator bound 5 with the actual PDE coefficient `-chi` included. -/
theorem weighted_chemotaxis_operator_L2eta_bounded
    (p : CMParams) {M eta : ℝ}
    (hM : 0 ≤ M) (heta_nonneg : 0 ≤ eta) (heta_one : eta < 1)
    {u₂ u₁ : ℝ → ℝ}
    (hu₂ : IsCUnifBdd u₂) (hu₁ : IsCUnifBdd u₁)
    (hu₂_mem : ∀ x, u₂ x ∈ Set.Icc (0 : ℝ) M)
    (hu₁_mem : ∀ x, u₁ x ∈ Set.Icc (0 : ℝ) M)
    (hclose : Integrable (fun x =>
      Real.exp (2 * eta * x) * |u₂ x - u₁ x| ^ 2)) :
    Integrable (fun x =>
        weightedChemotaxisOperatorDifference p eta u₂ u₁ x ^ 2) ∧
      (∫ x : ℝ,
          weightedChemotaxisOperatorDifference p eta u₂ u₁ x ^ 2) ≤
        weightedChemotaxisOperatorSquareConstant p M eta *
          ∫ x : ℝ,
            Real.exp (2 * eta * x) * |u₂ x - u₁ x| ^ 2 := by
  have hflux := weighted_flux_difference_L2eta_bounded
    p hM heta_nonneg heta_one hu₂ hu₁ hu₂_mem hu₁_mem hclose
  have hout : Integrable (fun x =>
      weightedChemotaxisOperatorDifference p eta u₂ u₁ x ^ 2) := by
    have hscaled := hflux.1.const_mul (p.χ ^ 2)
    simpa [weightedChemotaxisOperatorDifference, mul_pow] using hscaled
  refine ⟨hout, ?_⟩
  calc
    (∫ x : ℝ,
        weightedChemotaxisOperatorDifference p eta u₂ u₁ x ^ 2) =
        p.χ ^ 2 *
          ∫ x : ℝ, weightedFluxDifference p eta u₂ u₁ x ^ 2 := by
      simp_rw [weightedChemotaxisOperatorDifference, mul_pow]
      rw [integral_const_mul]
      congr 1
      ring
    _ ≤ p.χ ^ 2 *
        (weightedFluxSquareConstant p M eta *
          ∫ x : ℝ,
            Real.exp (2 * eta * x) * |u₂ x - u₁ x| ^ 2) :=
      mul_le_mul_of_nonneg_left hflux.2 (sq_nonneg _)
    _ = weightedChemotaxisOperatorSquareConstant p M eta *
        ∫ x : ℝ,
          Real.exp (2 * eta * x) * |u₂ x - u₁ x| ^ 2 := by
      unfold weightedChemotaxisOperatorSquareConstant
      ring

/-- Operator bound 6.  The reaction difference is a bounded multiplication
operator on the weighted space. -/
theorem weighted_reaction_difference_L2eta_bounded
    (p : CMParams) {M eta : ℝ} (hM : 0 ≤ M)
    {u₂ u₁ : ℝ → ℝ}
    (hu₂ : IsCUnifBdd u₂) (hu₁ : IsCUnifBdd u₁)
    (hu₂_mem : ∀ x, u₂ x ∈ Set.Icc (0 : ℝ) M)
    (hu₁_mem : ∀ x, u₁ x ∈ Set.Icc (0 : ℝ) M)
    (hclose : Integrable (fun x =>
      Real.exp (2 * eta * x) * |u₂ x - u₁ x| ^ 2)) :
    Integrable
        (fun x => weightedReactionDifference p eta u₂ u₁ x ^ 2) ∧
      (∫ x : ℝ, weightedReactionDifference p eta u₂ u₁ x ^ 2) ≤
        reactionLip p.α M ^ 2 *
          ∫ x : ℝ,
            Real.exp (2 * eta * x) * |u₂ x - u₁ x| ^ 2 := by
  let q : ℝ → ℝ := fun x =>
    Real.exp (eta * x) * (u₂ x - u₁ x)
  have hq : Integrable (fun x => q x ^ 2) := by
    simpa [q] using weighted_raw_difference_sq_integrable hclose
  have hL0 := reactionLip_nonneg p.hα hM
  have hpoint : ∀ x,
      |weightedReactionDifference p eta u₂ u₁ x| ≤
        reactionLip p.α M * |q x| := by
    intro x
    have hr := reaction_increment_abs_le p.hα hM
      (hu₁_mem x) (hu₂_mem x)
    unfold weightedReactionDifference
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    dsimp [q]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (eta * x) *
          |reactionFun p.α (u₂ x) - reactionFun p.α (u₁ x)| ≤
          Real.exp (eta * x) *
            (reactionLip p.α M * |u₂ x - u₁ x|) :=
        mul_le_mul_of_nonneg_left hr (Real.exp_nonneg _)
      _ = reactionLip p.α M *
          (Real.exp (eta * x) * |u₂ x - u₁ x|) := by ring
  have hpoint_sq : ∀ x,
      weightedReactionDifference p eta u₂ u₁ x ^ 2 ≤
        reactionLip p.α M ^ 2 * q x ^ 2 := by
    intro x
    have hs := (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg hL0 (abs_nonneg _))).2 (hpoint x)
    simpa [sq_abs, mul_pow] using hs
  have hdom : Integrable (fun x =>
      reactionLip p.α M ^ 2 * q x ^ 2) :=
    hq.const_mul _
  have hout_meas : AEStronglyMeasurable
      (fun x => weightedReactionDifference p eta u₂ u₁ x ^ 2) := by
    have hr₂ : Continuous (fun x => reactionFun p.α (u₂ x)) :=
      (continuous_reactionFun
        (le_trans zero_le_one p.hα)).comp hu₂.1
    have hr₁ : Continuous (fun x => reactionFun p.α (u₁ x)) :=
      (continuous_reactionFun
        (le_trans zero_le_one p.hα)).comp hu₁.1
    have hexp : Continuous (fun x : ℝ => Real.exp (eta * x)) := by
      fun_prop
    exact ((hexp.mul (hr₂.sub hr₁)).pow 2).aestronglyMeasurable
  have hout : Integrable
      (fun x => weightedReactionDifference p eta u₂ u₁ x ^ 2) := by
    refine Integrable.mono' hdom hout_meas ?_
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpoint_sq x
  refine ⟨hout, ?_⟩
  calc
    (∫ x : ℝ, weightedReactionDifference p eta u₂ u₁ x ^ 2) ≤
        ∫ x : ℝ, reactionLip p.α M ^ 2 * q x ^ 2 :=
      integral_mono hout hdom hpoint_sq
    _ = reactionLip p.α M ^ 2 * ∫ x : ℝ, q x ^ 2 := by
      rw [integral_const_mul]
    _ = reactionLip p.α M ^ 2 *
        ∫ x : ℝ,
          Real.exp (2 * eta * x) * |u₂ x - u₁ x| ^ 2 := by
      rw [weighted_raw_difference_sq_integral_eq]

/-! ## The divergence-conjugation obstruction at Lemma 4a -/

/-- Conjugating a physical divergence by `exp (eta*x)` creates a zero-order
term.  Thus the flux contribution is `(partial_x - eta)` applied to the
weighted flux, not just `partial_x`. -/
theorem weighted_divergence_conjugation_identity
    {eta x : ℝ} {F : ℝ → ℝ} (hF : DifferentiableAt ℝ F x) :
    Real.exp (eta * x) * deriv F x =
      deriv (fun y => Real.exp (eta * y) * F y) x -
        eta * (Real.exp (eta * x) * F x) := by
  have hlin : HasDerivAt (fun y : ℝ => eta * y) eta x := by
    simpa using (hasDerivAt_const x eta).mul (hasDerivAt_id x)
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (eta * y))
      (Real.exp (eta * x) * eta) x := hlin.exp
  have hproduct := (hexp.mul hF.hasDerivAt).deriv
  change deriv (fun y : ℝ => Real.exp (eta * y) * F y) x = _ at hproduct
  rw [hproduct]
  ring

/-!
The Lemma 4a identity requested in the specification omits the second term
in `weighted_divergence_conjugation_identity`.  Moreover, the imported
canonical-global API has only segment fixed-point mild identities; it has no
whole-line classical/wave-to-mild representation from which to subtract the
traveling wave.  Lemma 4a and its finite iteration therefore cannot be
declared without either correcting the identity and proving that bridge, or
carrying the requested conclusion as a hypothesis.
-/

section AxiomAudit
#print axioms markovKernel_signed_l2_contraction
#print axioms weighted_moving_heat_L2eta_bounded
#print axioms weighted_moving_heat_gradient_L2eta_bounded
#print axioms weighted_flux_difference_L2eta_bounded
#print axioms weighted_chemotaxis_operator_L2eta_bounded
#print axioms weighted_reaction_difference_L2eta_bounded
#print axioms weighted_divergence_conjugation_identity
end AxiomAudit

end ShenWork.Paper1
