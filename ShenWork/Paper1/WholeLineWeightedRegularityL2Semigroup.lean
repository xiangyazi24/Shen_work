import ShenWork.Paper1.WholeLineWeightedRegularityDuhamel
import ShenWork.Paper1.Theorem12WeightedFiniteness
import ShenWork.Paper1.WholeLineWeightedRegularityCap
import ShenWork.Paper1.WholeLineCauchySemigroupRestart
import ShenWork.Paper1.WholeLineCauchyBUCHeatContinuity
import ShenWork.PaperOne.WholeLineConvolutionDifferentiation
import ShenWork.PDE.HeatKernelLpEstimates
import Mathlib.Analysis.Normed.Lp.SmoothApprox

open Filter MeasureTheory Set Topology
open scoped RealInnerProductSpace
open scoped Nat NNReal ContDiff

noncomputable section

namespace ShenWork.Paper1

/-!
# The conjugated moving heat flow on whole-line `L²`

This file realizes the positive-time conjugated moving heat kernel as a
bounded operator on `WholeLineRealL2`.  The construction uses the concrete
Schur estimate already available for the kernel, rather than adding an
abstract semigroup assumption.
-/

/-- The conjugated moving heat kernel sends the canonical representative of
an `L²` class to another square-integrable measurable function. -/
theorem weightedMovingHeatEta_l2_data
    {eta c t : ℝ} (ht : 0 < t) (Z : WholeLineRealL2) :
    AEStronglyMeasurable
        (weightedMovingHeatEta eta c t (Z : ℝ → ℝ)) volume ∧
      Integrable
        (fun x => weightedMovingHeatEta eta c t (Z : ℝ → ℝ) x ^ 2) ∧
      (∫ x : ℝ, weightedMovingHeatEta eta c t (Z : ℝ → ℝ) x ^ 2) ≤
        weightedMovingHeatGrowth eta c t ^ 2 *
          ∫ x : ℝ, (Z x) ^ 2 := by
  have hZmeas : Measurable (Z : ℝ → ℝ) :=
    (Lp.stronglyMeasurable Z).measurable
  have hZsq : Integrable (fun x : ℝ => (Z x) ^ 2) :=
    (memLp_two_iff_integrable_sq (Lp.memLp Z).1).1 (Lp.memLp Z)
  have hout := weighted_moving_heat_L2eta_bounded
    (eta := eta) (c := c) ht hZmeas hZsq
  have hstrong : StronglyMeasurable
      (weightedMovingHeatEta eta c t (Z : ℝ → ℝ)) := by
    unfold weightedMovingHeatEta
    apply StronglyMeasurable.const_mul
    apply StronglyMeasurable.integral_prod_right
    exact ((weightedMovingHeatMarkovKernel_measurable eta c t).mul
      (hZmeas.comp measurable_snd)).stronglyMeasurable
  exact ⟨hstrong.aestronglyMeasurable, hout.1, hout.2⟩

/-- Positive-time conjugated moving heat flow on `L²`, before packaging
linearity and continuity. -/
def weightedMovingHeatL2Fun
    (eta c t : ℝ) (ht : 0 < t) (Z : WholeLineRealL2) : WholeLineRealL2 :=
  wholeLineRealL2OfSqIntegrable
    (weightedMovingHeatEta eta c t (Z : ℝ → ℝ))
    (weightedMovingHeatEta_l2_data ht Z).1
    (weightedMovingHeatEta_l2_data ht Z).2.1

/-- The positive-time `L²` lift has the expected concrete kernel
representative. -/
theorem weightedMovingHeatL2Fun_coe_ae
    {eta c t : ℝ} (ht : 0 < t) (Z : WholeLineRealL2) :
    ((weightedMovingHeatL2Fun eta c t ht Z : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      weightedMovingHeatEta eta c t (Z : ℝ → ℝ) := by
  exact wholeLineRealL2OfSqIntegrable_coe_ae _ _ _

/-- A positive-time translated Gaussian row is in `L²`. -/
theorem weightedMovingHeatMarkovKernel_memLp_two
    {eta c t : ℝ} (ht : 0 < t) (x : ℝ) :
    MemLp (weightedMovingHeatMarkovKernel eta c t x) 2 volume := by
  simpa [weightedMovingHeatMarkovKernel] using
    (heatKernel_translated_memLp (p := 2) ht (by norm_num)
      (x + (c - 2 * eta) * t))

/-- A translated Gaussian row times an `L²` representative is integrable.
This justifies the ordinary Bochner-integral linearity used below. -/
theorem weightedMovingHeatMarkovKernel_mul_integrable
    {eta c t : ℝ} (ht : 0 < t) (x : ℝ) (Z : WholeLineRealL2) :
    Integrable
      (fun y => weightedMovingHeatMarkovKernel eta c t x y * Z y) volume := by
  have hmul := (weightedMovingHeatMarkovKernel_memLp_two
    (eta := eta) (c := c) ht x).integrable_mul (Lp.memLp Z)
  simpa [Pi.mul_apply] using hmul

/-- The concrete positive-time heat lift is additive on `L²`. -/
theorem weightedMovingHeatL2Fun_add
    {eta c t : ℝ} (ht : 0 < t) (Z W : WholeLineRealL2) :
    weightedMovingHeatL2Fun eta c t ht (Z + W) =
      weightedMovingHeatL2Fun eta c t ht Z +
        weightedMovingHeatL2Fun eta c t ht W := by
  rw [Lp.ext_iff]
  have hZW : ((Z + W : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      fun y => Z y + W y := Lp.coeFn_add Z W
  have hleft := weightedMovingHeatL2Fun_coe_ae
    (eta := eta) (c := c) ht (Z + W)
  have hrightZ := weightedMovingHeatL2Fun_coe_ae
    (eta := eta) (c := c) ht Z
  have hrightW := weightedMovingHeatL2Fun_coe_ae
    (eta := eta) (c := c) ht W
  have hright := Lp.coeFn_add
    (weightedMovingHeatL2Fun eta c t ht Z)
    (weightedMovingHeatL2Fun eta c t ht W)
  filter_upwards [hleft, hrightZ, hrightW, hright] with x hx hxZ hxW hxR
  rw [hx, hxR]
  change weightedMovingHeatEta eta c t ((Z + W : WholeLineRealL2) : ℝ → ℝ) x =
    ((weightedMovingHeatL2Fun eta c t ht Z : WholeLineRealL2) : ℝ → ℝ) x +
      ((weightedMovingHeatL2Fun eta c t ht W : WholeLineRealL2) : ℝ → ℝ) x
  rw [hxZ, hxW]
  unfold weightedMovingHeatEta
  rw [show (∫ y : ℝ,
        weightedMovingHeatMarkovKernel eta c t x y * (Z + W) y) =
      ∫ y : ℝ,
        weightedMovingHeatMarkovKernel eta c t x y * (Z y + W y) by
    apply integral_congr_ae
    filter_upwards [hZW] with y hy
    rw [hy]]
  rw [show (fun y : ℝ =>
      weightedMovingHeatMarkovKernel eta c t x y * (Z y + W y)) =
      (fun y => weightedMovingHeatMarkovKernel eta c t x y * Z y) +
        (fun y => weightedMovingHeatMarkovKernel eta c t x y * W y) by
    funext y
    simp only [Pi.add_apply]
    ring]
  have hadd :
      integral volume
        ((fun y : ℝ => weightedMovingHeatMarkovKernel eta c t x y * Z y) +
          (fun y : ℝ => weightedMovingHeatMarkovKernel eta c t x y * W y)) =
        (∫ y : ℝ, weightedMovingHeatMarkovKernel eta c t x y * Z y) +
          ∫ y : ℝ, weightedMovingHeatMarkovKernel eta c t x y * W y :=
    integral_add
      (weightedMovingHeatMarkovKernel_mul_integrable
        (eta := eta) (c := c) ht x Z)
      (weightedMovingHeatMarkovKernel_mul_integrable
        (eta := eta) (c := c) ht x W)
  rw [hadd]
  ring

/-- The concrete positive-time heat lift respects real scalar
multiplication. -/
theorem weightedMovingHeatL2Fun_smul
    {eta c t : ℝ} (ht : 0 < t) (a : ℝ) (Z : WholeLineRealL2) :
    weightedMovingHeatL2Fun eta c t ht (a • Z) =
      a • weightedMovingHeatL2Fun eta c t ht Z := by
  rw [Lp.ext_iff]
  have haZ : ((a • Z : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      fun y => a * Z y := by
    simpa only [Pi.smul_apply, smul_eq_mul] using Lp.coeFn_smul a Z
  have hleft := weightedMovingHeatL2Fun_coe_ae
    (eta := eta) (c := c) ht (a • Z)
  have hrightZ := weightedMovingHeatL2Fun_coe_ae
    (eta := eta) (c := c) ht Z
  have hright := Lp.coeFn_smul a (weightedMovingHeatL2Fun eta c t ht Z)
  filter_upwards [hleft, hrightZ, hright] with x hx hxZ hxR
  rw [hx, hxR]
  change weightedMovingHeatEta eta c t ((a • Z : WholeLineRealL2) : ℝ → ℝ) x =
    a * ((weightedMovingHeatL2Fun eta c t ht Z : WholeLineRealL2) : ℝ → ℝ) x
  rw [hxZ]
  unfold weightedMovingHeatEta
  have hreplace :
      (∫ y : ℝ, weightedMovingHeatMarkovKernel eta c t x y * (a • Z) y) =
        ∫ y : ℝ, a *
          (weightedMovingHeatMarkovKernel eta c t x y * Z y) := by
    apply integral_congr_ae
    filter_upwards [haZ] with y hy
    rw [hy]
    ring
  rw [hreplace, integral_const_mul]
  ring

/-- Concrete integral formula for the square of the whole-line `L²` norm. -/
theorem wholeLineRealL2_norm_sq_eq_integral (Z : WholeLineRealL2) :
    ‖Z‖ ^ 2 = ∫ x : ℝ, Z x ^ 2 := by
  have hinner := wholeLineIntegral_mul_eq_inner_of_aeEq
    Z Z (EventuallyEq.rfl) (EventuallyEq.rfl)
  rw [real_inner_self_eq_norm_sq] at hinner
  simpa only [pow_two] using hinner.symm

/-- Sharp positive-time operator bound inherited from the concrete Schur
estimate. -/
theorem weightedMovingHeatL2Fun_norm_le
    {eta c t : ℝ} (ht : 0 < t) (Z : WholeLineRealL2) :
    ‖weightedMovingHeatL2Fun eta c t ht Z‖ ≤
      weightedMovingHeatGrowth eta c t * ‖Z‖ := by
  have houtSq :
      ‖weightedMovingHeatL2Fun eta c t ht Z‖ ^ 2 =
        ∫ x : ℝ, weightedMovingHeatEta eta c t (Z : ℝ → ℝ) x ^ 2 := by
    simpa only [weightedMovingHeatL2Fun] using
      wholeLineRealL2OfSqIntegrable_norm_sq
        (weightedMovingHeatEta eta c t (Z : ℝ → ℝ))
        (weightedMovingHeatEta_l2_data ht Z).1
        (weightedMovingHeatEta_l2_data ht Z).2.1
  have hraw := (weightedMovingHeatEta_l2_data
    (eta := eta) (c := c) ht Z).2.2
  rw [← wholeLineRealL2_norm_sq_eq_integral Z, ← houtSq] at hraw
  have hgrowth : 0 ≤ weightedMovingHeatGrowth eta c t :=
    Real.exp_nonneg _
  have hright : 0 ≤ weightedMovingHeatGrowth eta c t * ‖Z‖ :=
    mul_nonneg hgrowth (norm_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) hright).mp
  nlinarith

/-- The positive-time kernel operator as a real linear map. -/
def weightedMovingHeatL2LinearMap
    (eta c t : ℝ) (ht : 0 < t) :
    WholeLineRealL2 →ₗ[ℝ] WholeLineRealL2 where
  toFun := weightedMovingHeatL2Fun eta c t ht
  map_add' := weightedMovingHeatL2Fun_add ht
  map_smul' := weightedMovingHeatL2Fun_smul ht

/-- The positive-time conjugated moving heat operator on whole-line `L²`. -/
def weightedMovingHeatL2CLM
    (eta c t : ℝ) (ht : 0 < t) :
    WholeLineRealL2 →L[ℝ] WholeLineRealL2 :=
  (weightedMovingHeatL2LinearMap eta c t ht).mkContinuous
    (weightedMovingHeatGrowth eta c t)
    (weightedMovingHeatL2Fun_norm_le ht)

@[simp]
theorem weightedMovingHeatL2CLM_apply
    {eta c t : ℝ} (ht : 0 < t) (Z : WholeLineRealL2) :
    weightedMovingHeatL2CLM eta c t ht Z =
      weightedMovingHeatL2Fun eta c t ht Z := rfl

/-- Operator-norm bound for the concrete positive-time realization. -/
theorem weightedMovingHeatL2CLM_norm_le
    {eta c t : ℝ} (ht : 0 < t) :
    ‖weightedMovingHeatL2CLM eta c t ht‖ ≤
      weightedMovingHeatGrowth eta c t := by
  exact LinearMap.mkContinuous_norm_le _ (Real.exp_nonneg _)
    (weightedMovingHeatL2Fun_norm_le ht)

/-- Totalized semigroup family: identity at time zero, the concrete heat
operator at positive time, and zero at negative time.  Only its restriction
to nonnegative time is used by the cancellation argument. -/
def weightedMovingHeatL2Semigroup (eta c t : ℝ) :
    WholeLineRealL2 →L[ℝ] WholeLineRealL2 :=
  if ht : 0 < t then weightedMovingHeatL2CLM eta c t ht
  else if t = 0 then 1 else 0

theorem weightedMovingHeatL2Semigroup_of_pos
    {eta c t : ℝ} (ht : 0 < t) :
    weightedMovingHeatL2Semigroup eta c t =
      weightedMovingHeatL2CLM eta c t ht := by
  simp only [weightedMovingHeatL2Semigroup, dif_pos ht]

@[simp]
theorem weightedMovingHeatL2Semigroup_zero (eta c : ℝ) :
    weightedMovingHeatL2Semigroup eta c 0 = 1 := by
  simp [weightedMovingHeatL2Semigroup]

theorem weightedMovingHeatL2Semigroup_norm_le_of_pos
    {eta c t : ℝ} (ht : 0 < t) :
    ‖weightedMovingHeatL2Semigroup eta c t‖ ≤
      weightedMovingHeatGrowth eta c t := by
  rw [weightedMovingHeatL2Semigroup_of_pos ht]
  exact weightedMovingHeatL2CLM_norm_le ht

/-! ## Concrete semigroup law on `L²` -/

/-- The translated Markov kernels compose with addition of the two positive
times.  The drift translation is additive, so this is exactly the ordinary
Gaussian convolution identity. -/
theorem weightedMovingHeatMarkovKernel_convolution_add
    {eta c r q x z : ℝ} (hr : 0 < r) (hq : 0 < q) :
    (∫ y : ℝ,
        weightedMovingHeatMarkovKernel eta c r x y *
          weightedMovingHeatMarkovKernel eta c q y z) =
      weightedMovingHeatMarkovKernel eta c (r + q) x z := by
  unfold weightedMovingHeatMarkovKernel
  rw [show (fun y : ℝ =>
      heatKernel r (x + (c - 2 * eta) * r - y) *
        heatKernel q (y + (c - 2 * eta) * q - z)) =
      fun y : ℝ =>
        heatKernel r ((x + (c - 2 * eta) * r) - y) *
          heatKernel q (y - (z - (c - 2 * eta) * q)) by
    funext y
    congr 2 <;> ring]
  rw [heatKernel_convolution_add hr hq]
  congr 1
  ring

/-- The double kernel occurring in the positive-time composition is
absolutely integrable for every `L²` datum.  This is the Fubini input that
lets the concrete kernel identity descend to `WholeLineRealL2`. -/
theorem weightedMovingHeatMarkovKernel_comp_integrable
    {eta c r q x : ℝ} (hr : 0 < r) (hq : 0 < q)
    (Z : WholeLineRealL2) :
    Integrable
      (fun p : ℝ × ℝ =>
        weightedMovingHeatMarkovKernel eta c r x p.1 *
          weightedMovingHeatMarkovKernel eta c q p.1 p.2 * Z p.2)
      (volume.prod volume) := by
  let J : ℝ × ℝ → ℝ := fun p =>
    weightedMovingHeatMarkovKernel eta c r x p.1 *
      weightedMovingHeatMarkovKernel eta c q p.1 p.2 * Z p.2
  have hJmeas : AEStronglyMeasurable J (volume.prod volume) := by
    apply Measurable.aestronglyMeasurable
    dsimp [J]
    exact (((weightedMovingHeatMarkovKernel_measurable eta c r).comp
        (measurable_const.prodMk measurable_fst)).mul
      ((weightedMovingHeatMarkovKernel_measurable eta c q).comp
        (measurable_fst.prodMk measurable_snd))).mul
      ((Lp.stronglyMeasurable Z).measurable.comp measurable_snd)
  have hsum : 0 < r + q := add_pos hr hq
  have hsections : ∀ z : ℝ, Integrable (fun y : ℝ => J (y, z)) := by
    intro z
    have hbound : ∀ y : ℝ,
        |weightedMovingHeatMarkovKernel eta c q y z * Z z| ≤
          (1 / Real.sqrt (4 * Real.pi * q)) * |Z z| := by
      intro y
      rw [abs_mul, abs_of_nonneg
        (weightedMovingHeatMarkovKernel_nonneg hq eta c y z)]
      exact mul_le_mul_of_nonneg_right
        (by
          unfold weightedMovingHeatMarkovKernel
          exact heatKernel_pointwise_bound hq _)
        (abs_nonneg _)
    have hmeas : AEStronglyMeasurable
        (fun y : ℝ =>
          weightedMovingHeatMarkovKernel eta c q y z * Z z) volume := by
      apply Measurable.aestronglyMeasurable
      exact ((weightedMovingHeatMarkovKernel_measurable eta c q).comp
        (measurable_id.prodMk measurable_const)).mul measurable_const
    simpa [J, mul_assoc] using
      (weightedMovingHeatMarkovKernel_row_integrable hr eta c x).mul_bdd
        hmeas (by
          simpa [Real.norm_eq_abs] using
            (Filter.Eventually.of_forall hbound))
  have hnorm_sections :
      (fun z : ℝ => ∫ y : ℝ, ‖J (y, z)‖) =
        fun z : ℝ =>
          ‖weightedMovingHeatMarkovKernel eta c (r + q) x z * Z z‖ := by
    funext z
    calc
      (∫ y : ℝ, ‖J (y, z)‖) =
          |Z z| *
            (∫ y : ℝ,
              weightedMovingHeatMarkovKernel eta c r x y *
                weightedMovingHeatMarkovKernel eta c q y z) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with y
        rw [Real.norm_eq_abs]
        dsimp [J]
        rw [abs_mul, abs_mul,
          abs_of_nonneg
            (weightedMovingHeatMarkovKernel_nonneg hr eta c x y),
          abs_of_nonneg
            (weightedMovingHeatMarkovKernel_nonneg hq eta c y z)]
        ring
      _ = |Z z| *
          weightedMovingHeatMarkovKernel eta c (r + q) x z := by
        rw [weightedMovingHeatMarkovKernel_convolution_add hr hq]
      _ = ‖weightedMovingHeatMarkovKernel eta c (r + q) x z * Z z‖ := by
        rw [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg
            (weightedMovingHeatMarkovKernel_nonneg hsum eta c x z)]
        ring
  refine (integrable_prod_iff' hJmeas).2
    ⟨Filter.Eventually.of_forall hsections, ?_⟩
  rw [hnorm_sections]
  exact (weightedMovingHeatMarkovKernel_mul_integrable hsum x Z).norm

/-- Positive-time semigroup law for the concrete `L²` heat operators. -/
theorem weightedMovingHeatL2CLM_comp_add
    {eta c r q : ℝ} (hr : 0 < r) (hq : 0 < q) :
    (weightedMovingHeatL2CLM eta c r hr).comp
        (weightedMovingHeatL2CLM eta c q hq) =
      weightedMovingHeatL2CLM eta c (r + q) (add_pos hr hq) := by
  ext Z
  simp only [ContinuousLinearMap.comp_apply, weightedMovingHeatL2CLM_apply]
  have houter := weightedMovingHeatL2Fun_coe_ae
    (eta := eta) (c := c) hr
    (weightedMovingHeatL2Fun eta c q hq Z)
  have hinner := weightedMovingHeatL2Fun_coe_ae
    (eta := eta) (c := c) hq Z
  have hright := weightedMovingHeatL2Fun_coe_ae
    (eta := eta) (c := c) (add_pos hr hq) Z
  filter_upwards [houter, hright] with x hxOuter hxRight
  rw [hxOuter, hxRight]
  unfold weightedMovingHeatEta
  have hreplace :
      (∫ y : ℝ,
          weightedMovingHeatMarkovKernel eta c r x y *
            ((weightedMovingHeatL2Fun eta c q hq Z : WholeLineRealL2) :
              ℝ → ℝ) y) =
        ∫ y : ℝ,
          weightedMovingHeatMarkovKernel eta c r x y *
            weightedMovingHeatEta eta c q (Z : ℝ → ℝ) y := by
    apply integral_congr_ae
    filter_upwards [hinner] with y hy
    rw [hy]
  rw [hreplace]
  unfold weightedMovingHeatEta
  let J : ℝ × ℝ → ℝ := fun p =>
    weightedMovingHeatMarkovKernel eta c r x p.1 *
      weightedMovingHeatMarkovKernel eta c q p.1 p.2 * Z p.2
  have hswap := MeasureTheory.integral_integral_swap
    (f := fun y z : ℝ => J (y, z))
    (weightedMovingHeatMarkovKernel_comp_integrable
      (eta := eta) (c := c) (x := x) hr hq Z)
  rw [show
      (∫ y : ℝ,
          weightedMovingHeatMarkovKernel eta c r x y *
            (weightedMovingHeatGrowth eta c q *
              ∫ z : ℝ,
                weightedMovingHeatMarkovKernel eta c q y z * Z z)) =
        weightedMovingHeatGrowth eta c q *
          ∫ y : ℝ, ∫ z : ℝ, J (y, z) by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    rw [show
        (∫ z : ℝ, J (y, z)) =
          weightedMovingHeatMarkovKernel eta c r x y *
            ∫ z : ℝ,
              weightedMovingHeatMarkovKernel eta c q y z * Z z by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with z
      dsimp [J]
      ring]
    ring]
  rw [hswap]
  rw [show
      (∫ z : ℝ, ∫ y : ℝ, J (y, z)) =
        ∫ z : ℝ,
          weightedMovingHeatMarkovKernel eta c (r + q) x z * Z z by
    apply integral_congr_ae
    filter_upwards with z
    dsimp [J]
    rw [integral_mul_const,
      weightedMovingHeatMarkovKernel_convolution_add hr hq]]
  rw [show weightedMovingHeatGrowth eta c r *
      (weightedMovingHeatGrowth eta c q *
        ∫ z : ℝ,
          weightedMovingHeatMarkovKernel eta c (r + q) x z * Z z) =
      weightedMovingHeatGrowth eta c (r + q) *
        ∫ z : ℝ,
          weightedMovingHeatMarkovKernel eta c (r + q) x z * Z z by
    unfold weightedMovingHeatGrowth
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring]

/-- Semigroup law in the totalized nonnegative-time interface. -/
theorem weightedMovingHeatL2Semigroup_add
    {eta c r q : ℝ} (hr : 0 ≤ r) (hq : 0 ≤ q) :
    (weightedMovingHeatL2Semigroup eta c r).comp
        (weightedMovingHeatL2Semigroup eta c q) =
      weightedMovingHeatL2Semigroup eta c (r + q) := by
  rcases hr.eq_or_lt with rfl | hr
  · simp only [weightedMovingHeatL2Semigroup_zero, zero_add]
    rfl
  rcases hq.eq_or_lt with rfl | hq
  · simp only [weightedMovingHeatL2Semigroup_zero, add_zero]
    rfl
  rw [weightedMovingHeatL2Semigroup_of_pos hr,
    weightedMovingHeatL2Semigroup_of_pos hq,
    weightedMovingHeatL2Semigroup_of_pos (add_pos hr hq)]
  exact weightedMovingHeatL2CLM_comp_add hr hq

/-! ## Strong continuity at time zero -/

/-- A scalar majorant for the uniform error on a Lipschitz BUC datum. -/
def weightedMovingHeatBUCErrorBound
    (eta c : ℝ) (C : NNReal) (g : WholeLineBUC) (t : ℝ) : ℝ :=
  weightedMovingHeatGrowth eta c t *
      (dist (wholeLineHeatBUCTotal t g) g +
        (C : ℝ) * |(c - 2 * eta) * t|) +
    |weightedMovingHeatGrowth eta c t - 1| * ‖g‖

/-- At positive time the weighted moving flow is the ordinary BUC heat flow,
evaluated at the drifted point and multiplied by the conjugation growth. -/
theorem weightedMovingHeatEta_eq_growth_heatBUCTotal_shift
    {eta c t : ℝ} (ht : 0 < t) (g : WholeLineBUC) (x : ℝ) :
    weightedMovingHeatEta eta c t (g.1 : ℝ → ℝ) x =
      weightedMovingHeatGrowth eta c t *
        (wholeLineHeatBUCTotal t g).1
          (x + (c - 2 * eta) * t) := by
  simp only [wholeLineHeatBUCTotal, dif_pos ht, wholeLineHeatBUC_apply]
  unfold weightedMovingHeatEta weightedMovingHeatMarkovKernel heatSemigroup
  rfl

/-- Uniform pointwise control of the weighted moving heat error on a
Lipschitz BUC datum. -/
theorem weightedMovingHeatEta_sub_le_bucErrorBound
    {eta c t : ℝ} (ht : 0 < t) {C : NNReal} {g : WholeLineBUC}
    (hg : LipschitzWith C (g.1 : ℝ → ℝ)) (x : ℝ) :
    |weightedMovingHeatEta eta c t (g.1 : ℝ → ℝ) x - g.1 x| ≤
      weightedMovingHeatBUCErrorBound eta c C g t := by
  let d : ℝ := c - 2 * eta
  let H : WholeLineBUC := wholeLineHeatBUCTotal t g
  let a : ℝ := weightedMovingHeatGrowth eta c t
  have ha : 0 ≤ a := by
    dsimp [a, weightedMovingHeatGrowth]
    positivity
  have hheat : |H.1 (x + d * t) - g.1 (x + d * t)| ≤ dist H g := by
    calc
      |H.1 (x + d * t) - g.1 (x + d * t)| =
          |(H - g).1 (x + d * t)| := rfl
      _ ≤ ‖H - g‖ := WholeLineBUC.abs_apply_le_norm (H - g) _
      _ = dist H g := (WholeLineBUC.dist_eq_norm_sub H g).symm
  have hshift : |g.1 (x + d * t) - g.1 x| ≤ (C : ℝ) * |d * t| := by
    simpa [Real.dist_eq] using hg.dist_le_mul (x + d * t) x
  have hgx : |g.1 x| ≤ ‖g‖ := WholeLineBUC.abs_apply_le_norm g x
  rw [weightedMovingHeatEta_eq_growth_heatBUCTotal_shift ht]
  change |a * H.1 (x + d * t) - g.1 x| ≤ _
  have hdecomp :
      a * H.1 (x + d * t) - g.1 x =
        a * (H.1 (x + d * t) - g.1 (x + d * t)) +
          a * (g.1 (x + d * t) - g.1 x) +
            (a - 1) * g.1 x := by ring
  rw [hdecomp]
  calc
    |a * (H.1 (x + d * t) - g.1 (x + d * t)) +
          a * (g.1 (x + d * t) - g.1 x) + (a - 1) * g.1 x| ≤
        |a * (H.1 (x + d * t) - g.1 (x + d * t))| +
          |a * (g.1 (x + d * t) - g.1 x)| +
            |(a - 1) * g.1 x| := by
      calc
        _ ≤ |a * (H.1 (x + d * t) - g.1 (x + d * t)) +
              a * (g.1 (x + d * t) - g.1 x)| +
              |(a - 1) * g.1 x| := abs_add_le _ _
        _ ≤ _ := add_le_add (abs_add_le _ _) le_rfl
    _ = a * |H.1 (x + d * t) - g.1 (x + d * t)| +
          a * |g.1 (x + d * t) - g.1 x| + |a - 1| * |g.1 x| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg ha]
    _ ≤ a * dist H g + a * ((C : ℝ) * |d * t|) +
          |a - 1| * ‖g‖ := by
      gcongr
    _ = weightedMovingHeatBUCErrorBound eta c C g t := by
      dsimp [weightedMovingHeatBUCErrorBound, a, H, d]
      ring

/-- The preceding uniform error majorant tends to zero at time zero. -/
theorem weightedMovingHeatBUCErrorBound_tendsto_zero
    (eta c : ℝ) (C : NNReal) (g : WholeLineBUC) :
    Tendsto (weightedMovingHeatBUCErrorBound eta c C g) (𝓝 0) (𝓝 0) := by
  have hgrowth : ContinuousAt (weightedMovingHeatGrowth eta c) 0 := by
    unfold weightedMovingHeatGrowth
    fun_prop
  have hheat : ContinuousAt
      (fun t : ℝ => dist (wholeLineHeatBUCTotal t g) g) 0 :=
    (wholeLineHeatBUCTotal_continuousAt_zero g).dist continuousAt_const
  have hshift : ContinuousAt
      (fun t : ℝ => (C : ℝ) * |(c - 2 * eta) * t|) 0 := by
    fun_prop
  have habsGrowth : ContinuousAt
      (fun t : ℝ => |weightedMovingHeatGrowth eta c t - 1|) 0 := by
    fun_prop
  have hcont : ContinuousAt
      (weightedMovingHeatBUCErrorBound eta c C g) 0 :=
    (hgrowth.mul (hheat.add hshift)).add
      (habsGrowth.mul continuousAt_const)
  convert hcont.tendsto using 1
  simp [weightedMovingHeatBUCErrorBound, weightedMovingHeatGrowth]

/-- The concrete weighted heat integral only depends on the a.e. class of
its datum. -/
theorem weightedMovingHeatEta_congr_ae
    {eta c t : ℝ} {f g : ℝ → ℝ} (hfg : f =ᵐ[volume] g) (x : ℝ) :
    weightedMovingHeatEta eta c t f x =
      weightedMovingHeatEta eta c t g x := by
  unfold weightedMovingHeatEta
  congr 1
  apply integral_congr_ae
  filter_upwards [hfg] with y hy
  rw [hy]

/-- Pairing control for an `L²` class represented by an integrable Lipschitz
BUC function.  This is the compact-core estimate used in the density
argument for strong continuity. -/
theorem weightedMovingHeatL2Semigroup_inner_error_le_of_bucRep
    {eta c t : ℝ} (ht : 0 < t) {C : NNReal}
    (Z : WholeLineRealL2) (g : WholeLineBUC)
    (hrep : (Z : ℝ → ℝ) =ᵐ[volume] (g.1 : ℝ → ℝ))
    (hg : LipschitzWith C (g.1 : ℝ → ℝ))
    (hg_int : Integrable (g.1 : ℝ → ℝ)) :
    |⟪weightedMovingHeatL2Semigroup eta c t Z, Z⟫ - ‖Z‖ ^ 2| ≤
      weightedMovingHeatBUCErrorBound eta c C g t *
        ∫ x : ℝ, |g.1 x| := by
  let S : WholeLineRealL2 := weightedMovingHeatL2Semigroup eta c t Z
  let E : ℝ := weightedMovingHeatBUCErrorBound eta c C g t
  have hSrep : (S : ℝ → ℝ) =ᵐ[volume]
      weightedMovingHeatEta eta c t (Z : ℝ → ℝ) := by
    dsimp [S]
    rw [weightedMovingHeatL2Semigroup_of_pos ht]
    exact weightedMovingHeatL2Fun_coe_ae ht Z
  have hprod : Integrable (fun x : ℝ =>
      g.1 x * weightedMovingHeatEta eta c t (Z : ℝ → ℝ) x) := by
    have hmul := (Lp.memLp Z).integrable_mul (Lp.memLp S)
    exact hmul.congr (hrep.mul hSrep)
  have hself : Integrable (fun x : ℝ => g.1 x * g.1 x) := by
    have hmul := (Lp.memLp Z).integrable_mul (Lp.memLp Z)
    exact hmul.congr (hrep.mul hrep)
  have hZS := wholeLineIntegral_mul_eq_inner_of_aeEq Z S hrep hSrep
  have hZZ := wholeLineIntegral_mul_eq_inner_of_aeEq Z Z hrep hrep
  have heq :
      ⟪S, Z⟫ - ‖Z‖ ^ 2 =
        ∫ x : ℝ, g.1 x *
          (weightedMovingHeatEta eta c t (g.1 : ℝ → ℝ) x - g.1 x) := by
    rw [real_inner_comm, ← hZS, ← real_inner_self_eq_norm_sq, ← hZZ,
      ← integral_sub hprod hself]
    apply integral_congr_ae
    filter_upwards with x
    rw [weightedMovingHeatEta_congr_ae hrep x]
    ring
  rw [show weightedMovingHeatL2Semigroup eta c t Z = S from rfl, heq]
  calc
    |∫ x : ℝ, g.1 x *
          (weightedMovingHeatEta eta c t (g.1 : ℝ → ℝ) x - g.1 x)| ≤
        ∫ x : ℝ, E * |g.1 x| := by
      change ‖∫ x : ℝ, g.1 x *
          (weightedMovingHeatEta eta c t (g.1 : ℝ → ℝ) x - g.1 x)‖ ≤ _
      apply norm_integral_le_of_norm_le (hg_int.abs.const_mul E)
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul]
      simpa [E, mul_comm] using mul_le_mul_of_nonneg_left
        (weightedMovingHeatEta_sub_le_bucErrorBound ht hg x)
        (abs_nonneg (g.1 x))
    _ = E * ∫ x : ℝ, |g.1 x| := by rw [integral_const_mul]
    _ = weightedMovingHeatBUCErrorBound eta c C g t *
        ∫ x : ℝ, |g.1 x| := rfl

/-- Squared `L²` error bound on the Lipschitz BUC core. -/
theorem weightedMovingHeatL2Semigroup_norm_sub_sq_le_of_bucRep
    {eta c t : ℝ} (ht : 0 < t) {C : NNReal}
    (Z : WholeLineRealL2) (g : WholeLineBUC)
    (hrep : (Z : ℝ → ℝ) =ᵐ[volume] (g.1 : ℝ → ℝ))
    (hg : LipschitzWith C (g.1 : ℝ → ℝ))
    (hg_int : Integrable (g.1 : ℝ → ℝ)) :
    ‖weightedMovingHeatL2Semigroup eta c t Z - Z‖ ^ 2 ≤
      (weightedMovingHeatGrowth eta c t ^ 2 - 1) * ‖Z‖ ^ 2 +
        2 * weightedMovingHeatBUCErrorBound eta c C g t *
          ∫ x : ℝ, |g.1 x| := by
  let S : WholeLineRealL2 := weightedMovingHeatL2Semigroup eta c t Z
  let a : ℝ := weightedMovingHeatGrowth eta c t
  let E : ℝ := weightedMovingHeatBUCErrorBound eta c C g t
  let I : ℝ := ∫ x : ℝ, |g.1 x|
  have ha : 0 ≤ a := by
    dsimp [a, weightedMovingHeatGrowth]
    positivity
  have hSnorm : ‖S‖ ≤ a * ‖Z‖ := by
    calc
      ‖S‖ ≤ ‖weightedMovingHeatL2Semigroup eta c t‖ * ‖Z‖ :=
        (weightedMovingHeatL2Semigroup eta c t).le_opNorm Z
      _ ≤ a * ‖Z‖ := mul_le_mul_of_nonneg_right
        (weightedMovingHeatL2Semigroup_norm_le_of_pos ht) (norm_nonneg _)
  have hSsq : ‖S‖ ^ 2 ≤ (a * ‖Z‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ha (norm_nonneg _))).2 hSnorm
  have hpairAbs : |⟪S, Z⟫ - ‖Z‖ ^ 2| ≤ E * I := by
    simpa [S, E, I] using
      weightedMovingHeatL2Semigroup_inner_error_le_of_bucRep
        ht Z g hrep hg hg_int
  have hpair : ‖Z‖ ^ 2 - E * I ≤ ⟪S, Z⟫ := by
    have := neg_le_of_abs_le hpairAbs
    linarith
  change ‖S - Z‖ ^ 2 ≤ (a ^ 2 - 1) * ‖Z‖ ^ 2 + 2 * E * I
  rw [norm_sub_sq_real]
  nlinarith

/-- Strong continuity at zero on the integrable Lipschitz BUC core. -/
theorem weightedMovingHeatL2Semigroup_tendsto_zero_of_bucRep
    {eta c : ℝ} {C : NNReal}
    (Z : WholeLineRealL2) (g : WholeLineBUC)
    (hrep : (Z : ℝ → ℝ) =ᵐ[volume] (g.1 : ℝ → ℝ))
    (hg : LipschitzWith C (g.1 : ℝ → ℝ))
    (hg_int : Integrable (g.1 : ℝ → ℝ)) :
    Tendsto (fun t : ℝ => weightedMovingHeatL2Semigroup eta c t Z)
      (nhdsWithin 0 (Ioi 0)) (nhds Z) := by
  let I : ℝ := ∫ x : ℝ, |g.1 x|
  let R : ℝ → ℝ := fun t =>
    (weightedMovingHeatGrowth eta c t ^ 2 - 1) * ‖Z‖ ^ 2 +
      2 * weightedMovingHeatBUCErrorBound eta c C g t * I
  have hgrowth : Tendsto (weightedMovingHeatGrowth eta c)
      (nhds 0) (nhds 1) := by
    have hcont : ContinuousAt (weightedMovingHeatGrowth eta c) 0 := by
      unfold weightedMovingHeatGrowth
      fun_prop
    simpa [weightedMovingHeatGrowth] using hcont.tendsto
  have hE := weightedMovingHeatBUCErrorBound_tendsto_zero eta c C g
  have hRfull : Tendsto R (nhds 0) (nhds 0) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) (nhds 0) (nhds 1) :=
      tendsto_const_nhds
    have hfirst := ((hgrowth.pow 2).sub hone).mul_const (‖Z‖ ^ 2)
    have hsecond := (hE.const_mul 2).mul_const I
    simpa [R] using hfirst.add hsecond
  have hR : Tendsto R (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    hRfull.mono_left inf_le_left
  have hsq : Tendsto
      (fun t : ℝ =>
        ‖weightedMovingHeatL2Semigroup eta c t Z - Z‖ ^ 2)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun _ => sq_nonneg _
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact weightedMovingHeatL2Semigroup_norm_sub_sq_le_of_bucRep
        ht Z g hrep hg hg_int
    · exact hR
  have hnorm : Tendsto
      (fun t : ℝ => ‖weightedMovingHeatL2Semigroup eta c t Z - Z‖)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hsqrt := hsq.sqrt
    simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg] using hsqrt
  apply tendsto_iff_dist_tendsto_zero.2
  simpa [dist_eq_norm] using hnorm

/-- Strong continuity at zero for an `L²` class with a smooth
compactly-supported representative. -/
theorem weightedMovingHeatL2Semigroup_tendsto_zero_of_smoothCompactRep
    {eta c : ℝ} (Z : WholeLineRealL2) {g : ℝ → ℝ}
    (hrep : (Z : ℝ → ℝ) =ᵐ[volume] g)
    (hcompact : HasCompactSupport g) (hsmooth : ContDiff ℝ ∞ g) :
    Tendsto (fun t : ℝ => weightedMovingHeatL2Semigroup eta c t Z)
      (nhdsWithin 0 (Ioi 0)) (nhds Z) := by
  obtain ⟨C, hC⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hcompact hsmooth (by simp)
  obtain ⟨M, hM⟩ :=
    hsmooth.continuous.bounded_above_of_compact_support hcompact
  let gBUC : WholeLineBUC := wholeLineBUCOfUniformBound g
    hC.uniformContinuous M (fun x => by
      simpa [Real.norm_eq_abs] using hM x)
  have hrepBUC : (Z : ℝ → ℝ) =ᵐ[volume] (gBUC.1 : ℝ → ℝ) := by
    simpa [gBUC] using hrep
  have hgBUC : LipschitzWith C (gBUC.1 : ℝ → ℝ) := by
    simpa [gBUC] using hC
  have hgInt : Integrable (gBUC.1 : ℝ → ℝ) := by
    simpa [gBUC] using
      hsmooth.continuous.integrable_of_hasCompactSupport hcompact
  exact weightedMovingHeatL2Semigroup_tendsto_zero_of_bucRep
    Z gBUC hrepBUC hgBUC hgInt

/-- Strong continuity at time zero on all of whole-line `L²`.  The proof
extends the smooth compact-support core result using the locally uniform
operator bound. -/
theorem weightedMovingHeatL2Semigroup_tendsto_zero
    (eta c : ℝ) (Z : WholeLineRealL2) :
    Tendsto (fun t : ℝ => weightedMovingHeatL2Semigroup eta c t Z)
      (nhdsWithin 0 (Ioi 0)) (nhds Z) := by
  let M : ℝ := Real.exp |eta ^ 2 - c * eta|
  have hM : 0 < M := by
    dsimp [M]
    positivity
  have hgrowth_le : ∀ {t : ℝ}, 0 < t → t < 1 →
      weightedMovingHeatGrowth eta c t ≤ M := by
    intro t ht ht1
    unfold weightedMovingHeatGrowth
    dsimp [M]
    apply Real.exp_le_exp.mpr
    calc
      (eta ^ 2 - c * eta) * t ≤ |(eta ^ 2 - c * eta) * t| :=
        le_abs_self _
      _ = |eta ^ 2 - c * eta| * t := by rw [abs_mul, abs_of_pos ht]
      _ ≤ |eta ^ 2 - c * eta| * 1 :=
        mul_le_mul_of_nonneg_left ht1.le (abs_nonneg _)
      _ = |eta ^ 2 - c * eta| := mul_one _
  rw [Metric.tendsto_nhds]
  intro eps heps
  let delta : ℝ := eps / (4 * (M + 1))
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hdense := MeasureTheory.Lp.dense_hasCompactSupport_contDiff
    (F := ℝ) (E := ℝ) (μ := (volume : Measure ℝ)) (p := 2)
    (by norm_num)
  obtain ⟨G, hGmem, hZG⟩ := hdense.exists_dist_lt Z hdelta
  rcases hGmem with ⟨g, hGrep, hgCompact, hgSmooth⟩
  have hGtend :=
    weightedMovingHeatL2Semigroup_tendsto_zero_of_smoothCompactRep
      (eta := eta) (c := c) G hGrep hgCompact hgSmooth
  have hGevent : ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      dist (weightedMovingHeatL2Semigroup eta c t G) G < eps / 2 :=
    (Metric.tendsto_nhds.1 hGtend) (eps / 2) (half_pos heps)
  have htlt : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), t < (1 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [self_mem_nhdsWithin, htlt, hGevent] with t ht ht1 hcore
  have hop : ‖weightedMovingHeatL2Semigroup eta c t‖ ≤ M :=
    (weightedMovingHeatL2Semigroup_norm_le_of_pos ht).trans
      (hgrowth_le ht ht1)
  have hmap : dist
      (weightedMovingHeatL2Semigroup eta c t Z)
      (weightedMovingHeatL2Semigroup eta c t G) ≤ M * dist Z G := by
    exact ((weightedMovingHeatL2Semigroup eta c t).dist_le_opNorm Z G).trans
      (mul_le_mul_of_nonneg_right hop dist_nonneg)
  have hdeltaEq : (M + 1) * delta = eps / 4 := by
    dsimp [delta]
    field_simp
  have htail : M * dist Z G + dist G Z < eps / 4 := by
    rw [dist_comm G Z]
    calc
      M * dist Z G + dist Z G = (M + 1) * dist Z G := by ring
      _ < (M + 1) * delta :=
        mul_lt_mul_of_pos_left hZG (add_pos_of_pos_of_nonneg hM zero_le_one)
      _ = eps / 4 := hdeltaEq
  calc
    dist (weightedMovingHeatL2Semigroup eta c t Z) Z ≤
        dist (weightedMovingHeatL2Semigroup eta c t Z)
            (weightedMovingHeatL2Semigroup eta c t G) +
          dist (weightedMovingHeatL2Semigroup eta c t G) G + dist G Z := by
      calc
        _ ≤ dist (weightedMovingHeatL2Semigroup eta c t Z)
              (weightedMovingHeatL2Semigroup eta c t G) +
            dist (weightedMovingHeatL2Semigroup eta c t G) Z :=
          dist_triangle _ _ _
        _ ≤ dist (weightedMovingHeatL2Semigroup eta c t Z)
              (weightedMovingHeatL2Semigroup eta c t G) +
            (dist (weightedMovingHeatL2Semigroup eta c t G) G +
              dist G Z) := add_le_add le_rfl (dist_triangle _ _ _)
        _ = _ := by ring
    _ ≤ M * dist Z G +
        dist (weightedMovingHeatL2Semigroup eta c t G) G + dist G Z := by
      gcongr
    _ < eps := by linarith

/-! ## A reusable signed-kernel `L²` operator -/

/-- Concrete data for a signed integral kernel with equal absolute row and
column masses.  The final field is deliberately explicit: it is precisely
what licenses pointwise integral linearity on chosen `L²` representatives.
For the Gaussian derivative kernels it follows from their own `L²` row
bounds. -/
structure WholeLineL2SchurKernelData (L : ℝ → ℝ → ℝ) (C : ℝ) : Prop where
  mass_nonneg : 0 ≤ C
  kernel_measurable : Measurable (Function.uncurry L)
  absKernel_measurable : Measurable (Function.uncurry (fun x y => |L x y|))
  abs_row_integrable : ∀ x, Integrable (fun y => |L x y|) volume
  abs_row_mass : ∀ x, ∫ y : ℝ, |L x y| = C
  abs_col_integrable : ∀ y, Integrable (fun x => |L x y|) volume
  abs_col_mass : ∀ y, ∫ x : ℝ, |L x y| = C
  row_mul_l2_integrable : ∀ x (Z : WholeLineRealL2),
    Integrable (fun y => L x y * Z y) volume

theorem WholeLineL2SchurKernelData.output_l2_data
    {L : ℝ → ℝ → ℝ} {C : ℝ}
    (hK : WholeLineL2SchurKernelData L C) (Z : WholeLineRealL2) :
    AEStronglyMeasurable (fun x => ∫ y : ℝ, L x y * Z y) volume ∧
      Integrable (fun x => (∫ y : ℝ, L x y * Z y) ^ 2) volume ∧
      (∫ x : ℝ, (∫ y : ℝ, L x y * Z y) ^ 2) ≤
        C ^ 2 * ∫ y : ℝ, Z y ^ 2 := by
  have hZmeas : Measurable (Z : ℝ → ℝ) :=
    (Lp.stronglyMeasurable Z).measurable
  have hZsq : Integrable (fun y : ℝ => Z y ^ 2) :=
    (memLp_two_iff_integrable_sq (Lp.memLp Z).1).1 (Lp.memLp Z)
  have hbound := absKernel_l2_contraction_of_dominated_envelope
    L (fun x y => |L x y|) (fun x y => |L x y|) (Z : ℝ → ℝ) C
    hK.mass_nonneg hK.kernel_measurable hK.absKernel_measurable
    (fun _ _ => abs_nonneg _) (fun _ _ => rfl) (fun _ _ => le_rfl)
    hK.absKernel_measurable (fun _ _ => abs_nonneg _)
    hK.abs_row_integrable hK.abs_row_mass
    hK.abs_col_integrable hK.abs_col_mass hZmeas hZsq
  have hstrong : StronglyMeasurable (fun x => ∫ y : ℝ, L x y * Z y) := by
    apply StronglyMeasurable.integral_prod_right
    exact (hK.kernel_measurable.mul
      (hZmeas.comp measurable_snd)).stronglyMeasurable
  exact ⟨hstrong.aestronglyMeasurable, hbound.1, hbound.2⟩

/-- The `L²` lift of a signed Schur kernel. -/
def WholeLineL2SchurKernelData.toL2Fun
    {L : ℝ → ℝ → ℝ} {C : ℝ}
    (hK : WholeLineL2SchurKernelData L C) (Z : WholeLineRealL2) :
    WholeLineRealL2 :=
  wholeLineRealL2OfSqIntegrable
    (fun x => ∫ y : ℝ, L x y * Z y)
    (hK.output_l2_data Z).1 (hK.output_l2_data Z).2.1

theorem WholeLineL2SchurKernelData.toL2Fun_coe_ae
    {L : ℝ → ℝ → ℝ} {C : ℝ}
    (hK : WholeLineL2SchurKernelData L C) (Z : WholeLineRealL2) :
    ((hK.toL2Fun Z : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      fun x => ∫ y : ℝ, L x y * Z y := by
  exact wholeLineRealL2OfSqIntegrable_coe_ae _ _ _

theorem WholeLineL2SchurKernelData.toL2Fun_add
    {L : ℝ → ℝ → ℝ} {C : ℝ}
    (hK : WholeLineL2SchurKernelData L C) (Z W : WholeLineRealL2) :
    hK.toL2Fun (Z + W) = hK.toL2Fun Z + hK.toL2Fun W := by
  rw [Lp.ext_iff]
  have hZW : ((Z + W : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      fun y => Z y + W y := Lp.coeFn_add Z W
  have hleft := hK.toL2Fun_coe_ae (Z + W)
  have hrightZ := hK.toL2Fun_coe_ae Z
  have hrightW := hK.toL2Fun_coe_ae W
  have hright := Lp.coeFn_add (hK.toL2Fun Z) (hK.toL2Fun W)
  filter_upwards [hleft, hrightZ, hrightW, hright] with x hx hxZ hxW hxR
  rw [hx, hxR]
  change (∫ y : ℝ, L x y * (Z + W) y) =
    ((hK.toL2Fun Z : WholeLineRealL2) : ℝ → ℝ) x +
      ((hK.toL2Fun W : WholeLineRealL2) : ℝ → ℝ) x
  rw [hxZ, hxW]
  rw [show (∫ y : ℝ, L x y * (Z + W) y) =
      ∫ y : ℝ, L x y * (Z y + W y) by
    apply integral_congr_ae
    filter_upwards [hZW] with y hy
    rw [hy]]
  have hadd := integral_add (hK.row_mul_l2_integrable x Z)
    (hK.row_mul_l2_integrable x W)
  rw [show (fun y : ℝ => L x y * (Z y + W y)) =
      (fun y => L x y * Z y) + (fun y => L x y * W y) by
    funext y
    simp only [Pi.add_apply]
    ring]
  exact hadd

theorem WholeLineL2SchurKernelData.toL2Fun_smul
    {L : ℝ → ℝ → ℝ} {C : ℝ}
    (hK : WholeLineL2SchurKernelData L C) (a : ℝ) (Z : WholeLineRealL2) :
    hK.toL2Fun (a • Z) = a • hK.toL2Fun Z := by
  rw [Lp.ext_iff]
  have haZ : ((a • Z : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      fun y => a * Z y := by
    simpa only [Pi.smul_apply, smul_eq_mul] using Lp.coeFn_smul a Z
  have hleft := hK.toL2Fun_coe_ae (a • Z)
  have hrightZ := hK.toL2Fun_coe_ae Z
  have hright := Lp.coeFn_smul a (hK.toL2Fun Z)
  filter_upwards [hleft, hrightZ, hright] with x hx hxZ hxR
  rw [hx, hxR]
  change (∫ y : ℝ, L x y * (a • Z) y) =
    a * ((hK.toL2Fun Z : WholeLineRealL2) : ℝ → ℝ) x
  rw [hxZ]
  rw [show (∫ y : ℝ, L x y * (a • Z) y) =
      ∫ y : ℝ, a * (L x y * Z y) by
    apply integral_congr_ae
    filter_upwards [haZ] with y hy
    rw [hy]
    ring]
  rw [integral_const_mul]

theorem WholeLineL2SchurKernelData.toL2Fun_norm_le
    {L : ℝ → ℝ → ℝ} {C : ℝ}
    (hK : WholeLineL2SchurKernelData L C) (Z : WholeLineRealL2) :
    ‖hK.toL2Fun Z‖ ≤ C * ‖Z‖ := by
  have houtSq : ‖hK.toL2Fun Z‖ ^ 2 =
      ∫ x : ℝ, (∫ y : ℝ, L x y * Z y) ^ 2 := by
    simpa only [WholeLineL2SchurKernelData.toL2Fun] using
      wholeLineRealL2OfSqIntegrable_norm_sq
        (fun x => ∫ y : ℝ, L x y * Z y)
        (hK.output_l2_data Z).1 (hK.output_l2_data Z).2.1
  have hraw := (hK.output_l2_data Z).2.2
  rw [← wholeLineRealL2_norm_sq_eq_integral Z, ← houtSq] at hraw
  have hright : 0 ≤ C * ‖Z‖ :=
    mul_nonneg hK.mass_nonneg (norm_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) hright).mp
  nlinarith

/-- The continuous `L²` operator associated with signed Schur-kernel
data. -/
def WholeLineL2SchurKernelData.toCLM
    {L : ℝ → ℝ → ℝ} {C : ℝ}
    (hK : WholeLineL2SchurKernelData L C) :
    WholeLineRealL2 →L[ℝ] WholeLineRealL2 :=
  ({ toFun := hK.toL2Fun
     map_add' := hK.toL2Fun_add
     map_smul' := hK.toL2Fun_smul } :
      WholeLineRealL2 →ₗ[ℝ] WholeLineRealL2).mkContinuous C hK.toL2Fun_norm_le

@[simp]
theorem WholeLineL2SchurKernelData.toCLM_apply
    {L : ℝ → ℝ → ℝ} {C : ℝ}
    (hK : WholeLineL2SchurKernelData L C) (Z : WholeLineRealL2) :
    hK.toCLM Z = hK.toL2Fun Z := rfl

theorem WholeLineL2SchurKernelData.toCLM_norm_le
    {L : ℝ → ℝ → ℝ} {C : ℝ}
    (hK : WholeLineL2SchurKernelData L C) : ‖hK.toCLM‖ ≤ C := by
  exact LinearMap.mkContinuous_norm_le _ hK.mass_nonneg hK.toL2Fun_norm_le

/-! ## Gaussian generator rows -/

/-- An absolutely integrable continuous function with a uniform pointwise
bound belongs to `L²`. -/
theorem memLp_two_of_continuous_of_abs_integrable_of_bound
    {f : ℝ → ℝ} {M : ℝ} (_hM : 0 ≤ M)
    (hfcont : Continuous f) (hfabs : Integrable (fun x => |f x|) volume)
    (hbound : ∀ x, |f x| ≤ M) : MemLp f 2 volume := by
  have hdom : Integrable (fun x => M * |f x|) volume := hfabs.const_mul M
  have hsq : Integrable (fun x => f x ^ 2) volume := by
    refine hdom.mono' (hfcont.pow 2).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc
      f x ^ 2 = |f x| * |f x| := by rw [← sq_abs, pow_two]
      _ ≤ M * |f x| :=
        mul_le_mul_of_nonneg_right (hbound x) (abs_nonneg _)
  exact (memLp_two_iff_integrable_sq hfcont.aestronglyMeasurable).2 hsq

/-- Positive-time heat-gradient rows belong to `L²`. -/
theorem heatKernel_deriv_memLp_two {t : ℝ} (ht : 0 < t) :
    MemLp (fun x : ℝ => deriv (fun z : ℝ => heatKernel t z) x) 2 volume := by
  let M : ℝ :=
    ((1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t))) *
      (Real.sqrt (1 / (4 * t)))⁻¹
  have hM : 0 ≤ M := by dsimp [M]; positivity
  exact memLp_two_of_continuous_of_abs_integrable_of_bound hM
    (ShenWork.IntervalNeumannFullKernel.continuous_deriv_heatKernel ht)
    (heatKernel_deriv_abs_integrable ht)
    (heatKernel_deriv_pointwise_bound ht)

/-- Positive-time heat-Hessian rows belong to `L²`. -/
theorem heatKernel_secondDeriv_memLp_two {t : ℝ} (ht : 0 < t) :
    MemLp
      (fun x : ℝ => deriv (fun u : ℝ =>
        deriv (fun z : ℝ => heatKernel t z) u) x) 2 volume := by
  let M := ShenWork.IntervalNeumannFullKernel.heatHessPointwiseBound t
  have hM : 0 ≤ M :=
    ShenWork.IntervalNeumannFullKernel.heatHessPointwiseBound_nonneg ht
  apply memLp_two_of_continuous_of_abs_integrable_of_bound hM
    (ShenWork.IntervalNeumannFullKernel.continuous_secondDeriv_heatKernel ht)
    (ShenWork.IntervalNeumannFullKernel.secondDeriv_heatKernel_abs_integrable ht)
  intro x
  have hraw := ShenWork.IntervalNeumannFullKernel.abs_secondDeriv_heatKernel_le ht x
  refine hraw.trans ?_
  have hexp : Real.exp (-x ^ 2 / (4 * (2 * t))) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have hden : 0 ≤ 4 * (2 * t) := by positivity
    have hq : 0 ≤ x ^ 2 / (4 * (2 * t)) := div_nonneg (sq_nonneg _) hden
    calc
      -x ^ 2 / (4 * (2 * t)) = -(x ^ 2 / (4 * (2 * t))) := by ring
      _ ≤ 0 := neg_nonpos.mpr hq
  exact mul_le_of_le_one_right hM hexp

/-- The scalar kernel of the time derivative of the conjugated moving heat
flow. -/
def weightedMovingHeatGeneratorBase (eta c t z : ℝ) : ℝ :=
  weightedMovingHeatGrowth eta c t *
    (deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) z +
      (c - 2 * eta) * deriv (fun w : ℝ => heatKernel t w) z +
      (eta ^ 2 - c * eta) * heatKernel t z)

/-- Integral-kernel form of the positive-time conjugated heat generator. -/
def weightedMovingHeatGeneratorKernel (eta c t x y : ℝ) : ℝ :=
  weightedMovingHeatGeneratorBase eta c t
    (x + (c - 2 * eta) * t - y)

/-- Absolute row/column mass of the generator kernel. -/
def weightedMovingHeatGeneratorMass (eta c t : ℝ) : ℝ :=
  ∫ z : ℝ, |weightedMovingHeatGeneratorBase eta c t z|

/-- Explicit `L¹` mass majorant for the generator kernel. -/
def weightedMovingHeatGeneratorMassBound (eta c t : ℝ) : ℝ :=
  weightedMovingHeatGrowth eta c t *
    ((5 * Real.sqrt 2 / 2) * t ^ (-(1 : ℝ)) +
      |c - 2 * eta| * (2 / Real.sqrt (4 * Real.pi * t)) +
      |eta ^ 2 - c * eta|)

theorem weightedMovingHeatGeneratorBase_continuous
    {eta c t : ℝ} (ht : 0 < t) :
    Continuous (weightedMovingHeatGeneratorBase eta c t) := by
  have h2 :=
    ShenWork.IntervalNeumannFullKernel.continuous_secondDeriv_heatKernel ht
  have h1 := ShenWork.IntervalNeumannFullKernel.continuous_deriv_heatKernel ht
  have h0 : Continuous (heatKernel t) := by
    unfold heatKernel
    fun_prop
  unfold weightedMovingHeatGeneratorBase
  exact continuous_const.mul
    ((h2.add (continuous_const.mul h1)).add (continuous_const.mul h0))

theorem weightedMovingHeatGeneratorBase_integrable
    {eta c t : ℝ} (ht : 0 < t) :
    Integrable (weightedMovingHeatGeneratorBase eta c t) volume := by
  have h2 : Integrable
      (fun z : ℝ => deriv (fun u : ℝ =>
        deriv (fun w : ℝ => heatKernel t w) u) z) volume := by
    have hmeas : AEStronglyMeasurable
        (fun z : ℝ => deriv (fun u : ℝ =>
          deriv (fun w : ℝ => heatKernel t w) u) z) volume :=
      (ShenWork.IntervalNeumannFullKernel.continuous_secondDeriv_heatKernel ht).aestronglyMeasurable
    apply (integrable_norm_iff hmeas).mp
    simpa only [Real.norm_eq_abs] using
      (ShenWork.IntervalNeumannFullKernel.secondDeriv_heatKernel_abs_integrable ht)
  have h1 : Integrable
      (fun z : ℝ => deriv (fun w : ℝ => heatKernel t w) z) volume :=
    heatKernel_deriv_integrable ht
  have h0 : Integrable (heatKernel t) volume := heatKernel_integrable ht
  simpa only [weightedMovingHeatGeneratorBase] using
    ((h2.add (h1.const_mul (c - 2 * eta))).add
      (h0.const_mul (eta ^ 2 - c * eta))).const_mul
        (weightedMovingHeatGrowth eta c t)

theorem weightedMovingHeatGeneratorBase_abs_integrable
    {eta c t : ℝ} (ht : 0 < t) :
    Integrable (fun z => |weightedMovingHeatGeneratorBase eta c t z|) volume := by
  simpa only [Real.norm_eq_abs] using
    (weightedMovingHeatGeneratorBase_integrable (eta := eta) (c := c) ht).norm

theorem weightedMovingHeatGeneratorBase_memLp_two
    {eta c t : ℝ} (ht : 0 < t) :
    MemLp (weightedMovingHeatGeneratorBase eta c t) 2 volume := by
  have h2 := heatKernel_secondDeriv_memLp_two ht
  have h1 := heatKernel_deriv_memLp_two ht
  have h0 : MemLp (heatKernel t) 2 volume := by
    simpa using heatKernel_memLp (p := 2) ht (by norm_num)
  simpa only [weightedMovingHeatGeneratorBase] using
    ((h2.add (h1.const_mul (c - 2 * eta))).add
      (h0.const_mul (eta ^ 2 - c * eta))).const_mul
        (weightedMovingHeatGrowth eta c t)

theorem weightedMovingHeatGeneratorKernel_measurable
    {eta c t : ℝ} (ht : 0 < t) :
    Measurable (Function.uncurry
      (weightedMovingHeatGeneratorKernel eta c t)) := by
  have hb := (weightedMovingHeatGeneratorBase_continuous
    (eta := eta) (c := c) ht).measurable
  unfold weightedMovingHeatGeneratorKernel Function.uncurry
  exact hb.comp (by fun_prop)

theorem weightedMovingHeatGeneratorKernel_abs_measurable
    {eta c t : ℝ} (ht : 0 < t) :
    Measurable (Function.uncurry
      (fun x y => |weightedMovingHeatGeneratorKernel eta c t x y|)) := by
  exact (weightedMovingHeatGeneratorKernel_measurable
    (eta := eta) (c := c) ht).abs

theorem weightedMovingHeatGeneratorKernel_abs_row_integrable
    {eta c t : ℝ} (ht : 0 < t) (x : ℝ) :
    Integrable
      (fun y => |weightedMovingHeatGeneratorKernel eta c t x y|) volume := by
  let a := x + (c - 2 * eta) * t
  have hbase := weightedMovingHeatGeneratorBase_abs_integrable
    (eta := eta) (c := c) ht
  have htrans := hbase.comp_neg.comp_add_right (-a)
  convert htrans using 1
  ext y
  unfold weightedMovingHeatGeneratorKernel
  dsimp [a]
  congr 2
  ring

theorem weightedMovingHeatGeneratorKernel_abs_row_mass
    {eta c t : ℝ} (_ht : 0 < t) (x : ℝ) :
    (∫ y : ℝ, |weightedMovingHeatGeneratorKernel eta c t x y|) =
      weightedMovingHeatGeneratorMass eta c t := by
  let a := x + (c - 2 * eta) * t
  let G : ℝ → ℝ := fun z => |weightedMovingHeatGeneratorBase eta c t z|
  calc
    (∫ y : ℝ, |weightedMovingHeatGeneratorKernel eta c t x y|) =
        ∫ y : ℝ, G (-(y - a)) := by
      apply integral_congr_ae
      filter_upwards with y
      unfold weightedMovingHeatGeneratorKernel
      dsimp [G, a]
      congr 2
      ring
    _ = ∫ q : ℝ, G (-q) :=
      integral_sub_right_eq_self (fun q => G (-q)) a
    _ = ∫ z : ℝ, G z := integral_neg_eq_self G volume
    _ = weightedMovingHeatGeneratorMass eta c t := rfl

theorem weightedMovingHeatGeneratorKernel_abs_col_integrable
    {eta c t : ℝ} (ht : 0 < t) (y : ℝ) :
    Integrable
      (fun x => |weightedMovingHeatGeneratorKernel eta c t x y|) volume := by
  have hbase := weightedMovingHeatGeneratorBase_abs_integrable
    (eta := eta) (c := c) ht
  have htrans := hbase.comp_add_right ((c - 2 * eta) * t - y)
  convert htrans using 1
  ext x
  unfold weightedMovingHeatGeneratorKernel
  congr 2
  ring

theorem weightedMovingHeatGeneratorKernel_abs_col_mass
    {eta c t : ℝ} (_ht : 0 < t) (y : ℝ) :
    (∫ x : ℝ, |weightedMovingHeatGeneratorKernel eta c t x y|) =
      weightedMovingHeatGeneratorMass eta c t := by
  let G : ℝ → ℝ := fun z => |weightedMovingHeatGeneratorBase eta c t z|
  calc
    (∫ x : ℝ, |weightedMovingHeatGeneratorKernel eta c t x y|) =
        ∫ x : ℝ, G (x + ((c - 2 * eta) * t - y)) := by
      apply integral_congr_ae
      filter_upwards with x
      unfold weightedMovingHeatGeneratorKernel
      dsimp [G]
      congr 2
      ring
    _ = ∫ z : ℝ, G z := integral_add_right_eq_self _ _
    _ = weightedMovingHeatGeneratorMass eta c t := rfl

theorem weightedMovingHeatGeneratorKernel_row_memLp_two
    {eta c t : ℝ} (ht : 0 < t) (x : ℝ) :
    MemLp (weightedMovingHeatGeneratorKernel eta c t x) 2 volume := by
  let a := x + (c - 2 * eta) * t
  have hmpNeg : MeasurePreserving (fun y : ℝ => -y) volume volume :=
    Measure.measurePreserving_neg volume
  have hmpAdd : MeasurePreserving (fun y : ℝ => a + y) volume volume :=
    measurePreserving_add_left volume a
  have hcomp := (weightedMovingHeatGeneratorBase_memLp_two
    (eta := eta) (c := c) ht).comp_measurePreserving (hmpAdd.comp hmpNeg)
  convert hcomp using 1

theorem weightedMovingHeatGeneratorKernel_row_mul_l2_integrable
    {eta c t : ℝ} (ht : 0 < t) (x : ℝ) (Z : WholeLineRealL2) :
    Integrable
      (fun y => weightedMovingHeatGeneratorKernel eta c t x y * Z y) volume := by
  have hmul := (weightedMovingHeatGeneratorKernel_row_memLp_two
    (eta := eta) (c := c) ht x).integrable_mul (Lp.memLp Z)
  simpa only [Pi.mul_apply] using hmul

theorem weightedMovingHeatGeneratorMass_nonneg (eta c t : ℝ) :
    0 ≤ weightedMovingHeatGeneratorMass eta c t := by
  exact integral_nonneg fun _ => abs_nonneg _

theorem weightedMovingHeatGeneratorMass_le_bound
    {eta c t : ℝ} (ht : 0 < t) :
    weightedMovingHeatGeneratorMass eta c t ≤
      weightedMovingHeatGeneratorMassBound eta c t := by
  let H2 : ℝ → ℝ := fun z =>
    |deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) z|
  let H1 : ℝ → ℝ := fun z =>
    |deriv (fun w : ℝ => heatKernel t w) z|
  let H0 : ℝ → ℝ := fun z => heatKernel t z
  let G : ℝ → ℝ := fun z =>
    weightedMovingHeatGrowth eta c t *
      (H2 z + |c - 2 * eta| * H1 z +
        |eta ^ 2 - c * eta| * H0 z)
  have hGint : Integrable G volume := by
    have h2 :=
      ShenWork.IntervalNeumannFullKernel.secondDeriv_heatKernel_abs_integrable ht
    have h1 := heatKernel_deriv_abs_integrable ht
    have h0 := heatKernel_integrable ht
    dsimp only [G, H2, H1, H0]
    exact ((h2.add (h1.const_mul |c - 2 * eta|)).add
      (h0.const_mul |eta ^ 2 - c * eta|)).const_mul
        (weightedMovingHeatGrowth eta c t)
  have hbaseInt := weightedMovingHeatGeneratorBase_abs_integrable
    (eta := eta) (c := c) ht
  have hpoint : ∀ z,
      |weightedMovingHeatGeneratorBase eta c t z| ≤ G z := by
    intro z
    have hg : 0 ≤ weightedMovingHeatGrowth eta c t := Real.exp_nonneg _
    have hk : 0 ≤ heatKernel t z := heatKernel_nonneg ht z
    unfold weightedMovingHeatGeneratorBase
    rw [abs_mul, abs_of_nonneg hg]
    dsimp only [G, H2, H1, H0]
    apply mul_le_mul_of_nonneg_left _ hg
    calc
      |deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) z +
          (c - 2 * eta) * deriv (fun w : ℝ => heatKernel t w) z +
          (eta ^ 2 - c * eta) * heatKernel t z| ≤
          |deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) z| +
            |(c - 2 * eta) * deriv (fun w : ℝ => heatKernel t w) z| +
            |(eta ^ 2 - c * eta) * heatKernel t z| := by
        exact (abs_add_le _ _).trans
          (add_le_add (abs_add_le _ _) le_rfl)
      _ = |deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) z| +
            |c - 2 * eta| * |deriv (fun w : ℝ => heatKernel t w) z| +
            |eta ^ 2 - c * eta| * heatKernel t z := by
        rw [abs_mul, abs_mul, abs_of_nonneg hk]
  have hmono : weightedMovingHeatGeneratorMass eta c t ≤ ∫ z : ℝ, G z := by
    unfold weightedMovingHeatGeneratorMass
    exact integral_mono hbaseInt hGint hpoint
  have h2int : Integrable H2 volume :=
    ShenWork.IntervalNeumannFullKernel.secondDeriv_heatKernel_abs_integrable ht
  have h1int : Integrable H1 volume := heatKernel_deriv_abs_integrable ht
  have h0int : Integrable H0 volume := heatKernel_integrable ht
  have hG_eval :
      (∫ z : ℝ, G z) = weightedMovingHeatGrowth eta c t *
        ((∫ z : ℝ, H2 z) +
          |c - 2 * eta| * (2 / Real.sqrt (4 * Real.pi * t)) +
          |eta ^ 2 - c * eta|) := by
    have hadd12 :
        (∫ z : ℝ, H2 z + |c - 2 * eta| * H1 z) =
          (∫ z : ℝ, H2 z) +
            ∫ z : ℝ, |c - 2 * eta| * H1 z :=
      integral_add h2int (h1int.const_mul |c - 2 * eta|)
    have hadd120 :
        (∫ z : ℝ,
            (H2 z + |c - 2 * eta| * H1 z) +
              |eta ^ 2 - c * eta| * H0 z) =
          (∫ z : ℝ, H2 z + |c - 2 * eta| * H1 z) +
            ∫ z : ℝ, |eta ^ 2 - c * eta| * H0 z :=
      integral_add (h2int.add (h1int.const_mul |c - 2 * eta|))
        (h0int.const_mul |eta ^ 2 - c * eta|)
    dsimp only [G]
    rw [integral_const_mul]
    rw [hadd120, hadd12]
    rw [integral_const_mul, integral_const_mul,
      heatKernel_deriv_abs_integral ht,
      heatKernel_integral_eq_one ht, mul_one]
  rw [hG_eval] at hmono
  unfold weightedMovingHeatGeneratorMassBound
  refine hmono.trans ?_
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  have h2bound :=
    ShenWork.IntervalNeumannFullKernel.secondDeriv_heatKernel_abs_integral_le ht
  linarith

/-- Concrete Schur data for the positive-time generator kernel. -/
def weightedMovingHeatGeneratorSchurData
    (eta c t : ℝ) (ht : 0 < t) :
    WholeLineL2SchurKernelData
      (weightedMovingHeatGeneratorKernel eta c t)
      (weightedMovingHeatGeneratorMass eta c t) where
  mass_nonneg := weightedMovingHeatGeneratorMass_nonneg eta c t
  kernel_measurable := weightedMovingHeatGeneratorKernel_measurable ht
  absKernel_measurable := weightedMovingHeatGeneratorKernel_abs_measurable ht
  abs_row_integrable := weightedMovingHeatGeneratorKernel_abs_row_integrable ht
  abs_row_mass := weightedMovingHeatGeneratorKernel_abs_row_mass ht
  abs_col_integrable := weightedMovingHeatGeneratorKernel_abs_col_integrable ht
  abs_col_mass := weightedMovingHeatGeneratorKernel_abs_col_mass ht
  row_mul_l2_integrable := weightedMovingHeatGeneratorKernel_row_mul_l2_integrable ht

/-- Positive-time generator-smoothed heat operator on whole-line `L²`. -/
def weightedMovingHeatGeneratorL2CLM
    (eta c t : ℝ) (ht : 0 < t) :
    WholeLineRealL2 →L[ℝ] WholeLineRealL2 :=
  (weightedMovingHeatGeneratorSchurData eta c t ht).toCLM

theorem weightedMovingHeatGeneratorL2CLM_norm_le
    {eta c t : ℝ} (ht : 0 < t) :
    ‖weightedMovingHeatGeneratorL2CLM eta c t ht‖ ≤
      weightedMovingHeatGeneratorMass eta c t :=
  (weightedMovingHeatGeneratorSchurData eta c t ht).toCLM_norm_le

/-! ## Uniform generator bounds on a finite positive-time window -/

/-- On `(0,h]`, the inverse square-root singularity is dominated by the
inverse-time singularity with coefficient `sqrt h`. -/
theorem rpow_neg_half_le_sqrt_mul_rpow_neg_one
    {r h : ℝ} (hr : 0 < r) (hrh : r ≤ h) :
    r ^ (-(1 / 2 : ℝ)) ≤ Real.sqrt h * r ^ (-(1 : ℝ)) := by
  have hr0 : 0 ≤ r := hr.le
  have hh0 : 0 ≤ h := hr.le.trans hrh
  have hsqrt : Real.sqrt r ≤ Real.sqrt h := Real.sqrt_le_sqrt hrh
  have hinv0 : 0 ≤ r ^ (-(1 : ℝ)) := Real.rpow_nonneg hr0 _
  have hfactor :
      r ^ (-(1 / 2 : ℝ)) =
        Real.sqrt r * r ^ (-(1 : ℝ)) := by
    calc
      r ^ (-(1 / 2 : ℝ)) =
          r ^ ((1 / 2 : ℝ) + (-(1 : ℝ))) := by congr 1; ring
      _ = r ^ (1 / 2 : ℝ) * r ^ (-(1 : ℝ)) := by
        rw [Real.rpow_add hr]
      _ = Real.sqrt r * r ^ (-(1 : ℝ)) := by
        rw [Real.sqrt_eq_rpow]
  rw [hfactor]
  exact mul_le_mul_of_nonneg_right hsqrt hinv0

/-- On `(0,h]`, a constant is dominated by `h / r`. -/
theorem one_le_mul_rpow_neg_one
    {r h : ℝ} (hr : 0 < r) (hrh : r ≤ h) :
    1 ≤ h * r ^ (-(1 : ℝ)) := by
  rw [Real.rpow_neg_one]
  exact (le_div_iff₀ hr).2 (by simpa using hrh)

/-- An explicit horizon-dependent coefficient for the positive-time
generator bound.  Its three summands respectively control the Gaussian
Hessian, drift-gradient, and zeroth-order conjugation terms. -/
def weightedMovingHeatGeneratorHorizonConst (eta c h : ℝ) : ℝ :=
  Real.exp (|eta ^ 2 - c * eta| * h) *
    ((5 * Real.sqrt 2 / 2) +
      |c - 2 * eta| * (2 / Real.sqrt (4 * Real.pi)) * Real.sqrt h +
      |eta ^ 2 - c * eta| * h)

theorem weightedMovingHeatGeneratorHorizonConst_nonneg
    {eta c h : ℝ} (hh : 0 ≤ h) :
    0 ≤ weightedMovingHeatGeneratorHorizonConst eta c h := by
  unfold weightedMovingHeatGeneratorHorizonConst
  positivity

/-- The explicit generator mass majorant has the native analytic-semigroup
`r⁻¹` bound on every finite window `(0,h]`. -/
theorem weightedMovingHeatGeneratorMassBound_le_horizon
    {eta c r h : ℝ} (hr : 0 < r) (hrh : r ≤ h) :
    weightedMovingHeatGeneratorMassBound eta c r ≤
      weightedMovingHeatGeneratorHorizonConst eta c h *
        r ^ (-(1 : ℝ)) := by
  have hr0 : 0 ≤ r := hr.le
  have hh0 : 0 ≤ h := hr.le.trans hrh
  have hlambda :
      (eta ^ 2 - c * eta) * r ≤ |eta ^ 2 - c * eta| * h := by
    calc
      (eta ^ 2 - c * eta) * r ≤ |eta ^ 2 - c * eta| * r :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hr0
      _ ≤ |eta ^ 2 - c * eta| * h :=
        mul_le_mul_of_nonneg_left hrh (abs_nonneg _)
  have hgrowth :
      weightedMovingHeatGrowth eta c r ≤
        Real.exp (|eta ^ 2 - c * eta| * h) := by
    unfold weightedMovingHeatGrowth
    exact Real.exp_le_exp.mpr hlambda
  have hhalf := rpow_neg_half_le_sqrt_mul_rpow_neg_one hr hrh
  have hone := one_le_mul_rpow_neg_one hr hrh
  have hgradCoeff :
      0 ≤ |c - 2 * eta| * (2 / Real.sqrt (4 * Real.pi)) := by
    positivity
  have hzeroCoeff : 0 ≤ |eta ^ 2 - c * eta| := abs_nonneg _
  have hgrad := mul_le_mul_of_nonneg_left hhalf hgradCoeff
  have hgrad' :
      |c - 2 * eta| *
          ((2 / Real.sqrt (4 * Real.pi)) * r ^ (-(1 / 2 : ℝ))) ≤
        (|c - 2 * eta| * (2 / Real.sqrt (4 * Real.pi))) *
          (Real.sqrt h * r ^ (-(1 : ℝ))) := by
    simpa only [mul_assoc] using hgrad
  have hzero := mul_le_mul_of_nonneg_left hone hzeroCoeff
  have hzero' :
      |eta ^ 2 - c * eta| ≤
        |eta ^ 2 - c * eta| * (h * r ^ (-(1 : ℝ))) := by
    simpa only [mul_one] using hzero
  have hbracket :
      (5 * Real.sqrt 2 / 2) * r ^ (-(1 : ℝ)) +
          |c - 2 * eta| *
            ((2 / Real.sqrt (4 * Real.pi)) * r ^ (-(1 / 2 : ℝ))) +
          |eta ^ 2 - c * eta| ≤
        ((5 * Real.sqrt 2 / 2) +
            |c - 2 * eta| * (2 / Real.sqrt (4 * Real.pi)) * Real.sqrt h +
            |eta ^ 2 - c * eta| * h) * r ^ (-(1 : ℝ)) := by
    calc
      (5 * Real.sqrt 2 / 2) * r ^ (-(1 : ℝ)) +
            |c - 2 * eta| *
              ((2 / Real.sqrt (4 * Real.pi)) * r ^ (-(1 / 2 : ℝ))) +
            |eta ^ 2 - c * eta| ≤
          (5 * Real.sqrt 2 / 2) * r ^ (-(1 : ℝ)) +
            (|c - 2 * eta| * (2 / Real.sqrt (4 * Real.pi))) *
              (Real.sqrt h * r ^ (-(1 : ℝ))) +
            |eta ^ 2 - c * eta| *
              (h * r ^ (-(1 : ℝ))) := by
        exact add_le_add (add_le_add le_rfl hgrad') hzero'
      _ = ((5 * Real.sqrt 2 / 2) +
            |c - 2 * eta| * (2 / Real.sqrt (4 * Real.pi)) * Real.sqrt h +
            |eta ^ 2 - c * eta| * h) * r ^ (-(1 : ℝ)) := by ring
  have hraw0 :
      0 ≤ (5 * Real.sqrt 2 / 2) * r ^ (-(1 : ℝ)) +
          |c - 2 * eta| *
            ((2 / Real.sqrt (4 * Real.pi)) * r ^ (-(1 / 2 : ℝ))) +
          |eta ^ 2 - c * eta| := by
    positivity
  unfold weightedMovingHeatGeneratorMassBound
  rw [two_div_sqrt_four_pi_mul_eq_rpow_cauchy hr]
  calc
    weightedMovingHeatGrowth eta c r *
          ((5 * Real.sqrt 2 / 2) * r ^ (-(1 : ℝ)) +
            |c - 2 * eta| *
              ((2 / Real.sqrt (4 * Real.pi)) * r ^ (-(1 / 2 : ℝ))) +
            |eta ^ 2 - c * eta|) ≤
        Real.exp (|eta ^ 2 - c * eta| * h) *
          ((5 * Real.sqrt 2 / 2) * r ^ (-(1 : ℝ)) +
            |c - 2 * eta| *
              ((2 / Real.sqrt (4 * Real.pi)) * r ^ (-(1 / 2 : ℝ))) +
            |eta ^ 2 - c * eta|) :=
      mul_le_mul_of_nonneg_right hgrowth hraw0
    _ ≤ Real.exp (|eta ^ 2 - c * eta| * h) *
          (((5 * Real.sqrt 2 / 2) +
              |c - 2 * eta| * (2 / Real.sqrt (4 * Real.pi)) * Real.sqrt h +
              |eta ^ 2 - c * eta| * h) * r ^ (-(1 : ℝ))) :=
      mul_le_mul_of_nonneg_left hbracket (Real.exp_nonneg _)
    _ = weightedMovingHeatGeneratorHorizonConst eta c h *
          r ^ (-(1 : ℝ)) := by
      unfold weightedMovingHeatGeneratorHorizonConst
      ring

/-- Native `r⁻¹` operator-norm input for the abstract generator-cancellation
lemma, now discharged by the concrete conjugated Gaussian kernel. -/
theorem weightedMovingHeatGeneratorL2CLM_norm_le_horizon
    {eta c r h : ℝ} (hr : 0 < r) (hrh : r ≤ h) :
    ‖weightedMovingHeatGeneratorL2CLM eta c r hr‖ ≤
      weightedMovingHeatGeneratorHorizonConst eta c h *
        r ^ (-(1 : ℝ)) := by
  exact (weightedMovingHeatGeneratorL2CLM_norm_le hr).trans
    ((weightedMovingHeatGeneratorMass_le_bound hr).trans
      (weightedMovingHeatGeneratorMassBound_le_horizon hr hrh))

/-- The concrete representative of the generator-smoothed `L²` class is the
signed Gaussian generator convolution. -/
theorem weightedMovingHeatGeneratorL2CLM_coe_ae
    {eta c r : ℝ} (hr : 0 < r) (Z : WholeLineRealL2) :
    (((weightedMovingHeatGeneratorL2CLM eta c r hr) Z :
        WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      fun x => ∫ y : ℝ,
        weightedMovingHeatGeneratorKernel eta c r x y * Z y := by
  exact (weightedMovingHeatGeneratorSchurData eta c r hr).toL2Fun_coe_ae Z

/-- Totalized generator family.  The singular cancellation argument only
uses positive times, but this packaging gives it a proof-independent map
`ℝ → (L² →L L²)`. -/
def weightedMovingHeatL2Generator (eta c r : ℝ) :
    WholeLineRealL2 →L[ℝ] WholeLineRealL2 :=
  if hr : 0 < r then weightedMovingHeatGeneratorL2CLM eta c r hr else 0

theorem weightedMovingHeatL2Generator_of_pos
    {eta c r : ℝ} (hr : 0 < r) :
    weightedMovingHeatL2Generator eta c r =
      weightedMovingHeatGeneratorL2CLM eta c r hr := by
  simp only [weightedMovingHeatL2Generator, dif_pos hr]

@[simp]
theorem weightedMovingHeatL2Generator_zero (eta c : ℝ) :
    weightedMovingHeatL2Generator eta c 0 = 0 := by
  simp [weightedMovingHeatL2Generator]

/-- Directly packaged `hA` input for
`generator_holder_remainder_pointwise` and its integral corollaries. -/
theorem weightedMovingHeatL2Generator_norm_le_horizon
    (eta c h : ℝ) :
    ∀ r ∈ Ioc (0 : ℝ) h,
      ‖weightedMovingHeatL2Generator eta c r‖ ≤
        weightedMovingHeatGeneratorHorizonConst eta c h *
          r ^ (-(1 : ℝ)) := by
  intro r hr
  rw [weightedMovingHeatL2Generator_of_pos hr.1]
  exact weightedMovingHeatGeneratorL2CLM_norm_le_horizon hr.1 hr.2

/-! ## Generator compatibility with the heat semigroup -/

/-- First spatial Gaussian derivatives respect heat-kernel convolution. -/
theorem deriv_heatKernel_convolution_add
    {r q X A : ℝ} (hr : 0 < r) (hq : 0 < q) :
    (∫ y : ℝ,
        deriv (fun z : ℝ => heatKernel r z) (X - y) *
          heatKernel q (y - A)) =
      deriv (fun z : ℝ => heatKernel (r + q) z) (X - A) := by
  let f : ℝ → ℝ := fun y => heatKernel q (y - A)
  let M : ℝ := 1 / Real.sqrt (4 * Real.pi * q)
  have hfmeas : AEStronglyMeasurable f volume := by
    dsimp [f]
    exact (heatKernel_continuous hq).comp
      (continuous_id.sub continuous_const) |>.aestronglyMeasurable
  have hfbound : ∀ y, |f y| ≤ M := by
    intro y
    dsimp [f, M]
    rw [abs_of_nonneg (heatKernel_nonneg hq _)]
    exact heatKernel_pointwise_bound hq _
  have hdiff := ShenWork.PaperOne.ConvLeibniz.heatConvolution_space_deriv
    (f := f) (t := r) (x := X) (M := M) hr hfmeas hfbound
  have hfun : (fun z : ℝ => heatSemigroup r f z) =
      fun z : ℝ => heatKernel (r + q) (z - A) := by
    funext z
    unfold heatSemigroup
    dsimp [f]
    exact heatKernel_convolution_add
      (t := r) (s := q) (x := z) (z := A) hr hq
  calc
    (∫ y : ℝ,
        deriv (fun z : ℝ => heatKernel r z) (X - y) *
          heatKernel q (y - A)) =
        deriv (fun z : ℝ => heatSemigroup r f z) X := by
      rw [hdiff.deriv]
      apply integral_congr_ae
      filter_upwards with y
      dsimp [f]
      rw [deriv_heatKernel_translated_left hr X y,
        deriv_heatKernel hr (X - y)]
    _ = deriv (fun z : ℝ => heatKernel (r + q) (z - A)) X := by
      rw [hfun]
    _ = deriv (fun z : ℝ => heatKernel (r + q) z) (X - A) := by
      rw [deriv_heatKernel_translated_left (add_pos hr hq) X A,
        deriv_heatKernel (add_pos hr hq) (X - A)]

/-- Second spatial Gaussian derivatives respect heat-kernel convolution. -/
theorem secondDeriv_heatKernel_convolution_add
    {r q X A : ℝ} (hr : 0 < r) (hq : 0 < q) :
    (∫ y : ℝ,
        deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel r z) u)
            (X - y) * heatKernel q (y - A)) =
      deriv (fun u : ℝ =>
        deriv (fun z : ℝ => heatKernel (r + q) z) u) (X - A) := by
  let f : ℝ → ℝ := fun y => heatKernel q (y - A)
  let M : ℝ := 1 / Real.sqrt (4 * Real.pi * q)
  have hfmeas : AEStronglyMeasurable f volume := by
    dsimp [f]
    exact (heatKernel_continuous hq).comp
      (continuous_id.sub continuous_const) |>.aestronglyMeasurable
  have hfbound : ∀ y, |f y| ≤ M := by
    intro y
    dsimp [f, M]
    rw [abs_of_nonneg (heatKernel_nonneg hq _)]
    exact heatKernel_pointwise_bound hq _
  have hdiff := ShenWork.PaperOne.ConvLeibniz.heatConvolution_space_second_deriv
    (f := f) (t := r) (x := X) (M := M) hr hfmeas hfbound
  have hfun : (fun z : ℝ => heatSemigroup r f z) =
      fun z : ℝ => heatKernel (r + q) (z - A) := by
    funext z
    unfold heatSemigroup
    dsimp [f]
    exact heatKernel_convolution_add
      (t := r) (s := q) (x := z) (z := A) hr hq
  have htrans :
      deriv (fun z : ℝ =>
          deriv (fun w : ℝ => heatKernel (r + q) (w - A)) z) X =
        deriv (fun u : ℝ =>
          deriv (fun z : ℝ => heatKernel (r + q) z) u) (X - A) := by
    have hfirst : (fun z : ℝ =>
        deriv (fun w : ℝ => heatKernel (r + q) (w - A)) z) =
        fun z : ℝ => deriv (fun w : ℝ => heatKernel (r + q) w) (z - A) := by
      funext z
      rw [deriv_heatKernel_translated_left (add_pos hr hq) z A,
        deriv_heatKernel (add_pos hr hq) (z - A)]
    rw [hfirst]
    have hinner : HasDerivAt (fun z : ℝ => z - A) 1 X := by
      simpa [sub_eq_add_neg] using (hasDerivAt_id X).add_const (-A)
    have hmain :=
      ((ShenWork.IntervalNeumannFullKernel.heatKernel_secondDeriv_hasDerivAt
        (add_pos hr hq) (X - A)).comp X hinner).deriv
    convert hmain using 1
    rw [ShenWork.IntervalNeumannFullKernel.deriv_deriv_heatKernel
      (add_pos hr hq) (X - A)]
    ring
  calc
    (∫ y : ℝ,
        deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel r z) u)
            (X - y) * heatKernel q (y - A)) =
        deriv (fun z : ℝ => deriv (fun w : ℝ => heatSemigroup r f w) z) X := by
      rw [hdiff.deriv]
    _ = deriv (fun z : ℝ =>
        deriv (fun w : ℝ => heatKernel (r + q) (w - A)) z) X := by
      rw [hfun]
    _ = _ := htrans

/-- The positive-time generator kernel composes with the heat kernel by
addition of times.  The scalar heat growth of the inner semigroup is kept
explicit because it is outside its Markov kernel. -/
theorem weightedMovingHeatGeneratorKernel_convolution_add
    {eta c r q x z : ℝ} (hr : 0 < r) (hq : 0 < q) :
    weightedMovingHeatGrowth eta c q *
        (∫ y : ℝ,
          weightedMovingHeatGeneratorKernel eta c r x y *
            weightedMovingHeatMarkovKernel eta c q y z) =
      weightedMovingHeatGeneratorKernel eta c (r + q) x z := by
  let d : ℝ := c - 2 * eta
  let k : ℝ := eta ^ 2 - c * eta
  let X : ℝ := x + d * r
  let A : ℝ := z - d * q
  let Q : ℝ → ℝ := fun y => heatKernel q (y - A)
  let H0 : ℝ → ℝ := fun y => heatKernel r (X - y)
  let H1 : ℝ → ℝ := fun y =>
    deriv (fun w : ℝ => heatKernel r w) (X - y)
  let H2 : ℝ → ℝ := fun y =>
    deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel r w) u) (X - y)
  let M : ℝ := 1 / Real.sqrt (4 * Real.pi * q)
  have hQmeas : AEStronglyMeasurable Q volume := by
    dsimp [Q]
    exact (heatKernel_continuous hq).comp
      (continuous_id.sub continuous_const) |>.aestronglyMeasurable
  have hQbound : ∀ y, |Q y| ≤ M := by
    intro y
    dsimp [Q, M]
    rw [abs_of_nonneg (heatKernel_nonneg hq _)]
    exact heatKernel_pointwise_bound hq _
  have h0int : Integrable (fun y => H0 y * Q y) := by
    simpa [H0] using
      heatKernel_mul_bounded_integrable hr X hQbound hQmeas
  have h1int : Integrable (fun y => H1 y * Q y) := by
    have hraw := heatKernel_deriv_mul_bounded_integrable hr X hQbound hQmeas
    refine hraw.congr ?_
    filter_upwards with y
    dsimp [H1]
    rw [deriv_heatKernel_translated_left hr X y,
      deriv_heatKernel hr (X - y)]
  have h2int : Integrable (fun y => H2 y * Q y) := by
    simpa [H2] using
      ShenWork.PaperOne.ConvLeibniz.secondDeriv_heatKernel_mul_bounded_integrable
        hr X hQbound hQmeas
  have hsplit :
      (∫ y : ℝ, (H2 y + d * H1 y + k * H0 y) * Q y) =
        (∫ y : ℝ, H2 y * Q y) +
          d * (∫ y : ℝ, H1 y * Q y) +
            k * (∫ y : ℝ, H0 y * Q y) := by
    rw [show (fun y : ℝ => (H2 y + d * H1 y + k * H0 y) * Q y) =
        (fun y => H2 y * Q y) +
          (fun y => d * (H1 y * Q y)) +
            (fun y => k * (H0 y * Q y)) by
      funext y
      simp only [Pi.add_apply]
      ring]
    calc
      ∫ y : ℝ, ((fun y => H2 y * Q y) +
            (fun y => d * (H1 y * Q y))) y + k * (H0 y * Q y) =
          (∫ y : ℝ, H2 y * Q y + d * (H1 y * Q y)) +
            ∫ y : ℝ, k * (H0 y * Q y) :=
        integral_add (h2int.add (h1int.const_mul d)) (h0int.const_mul k)
      _ = ((∫ y : ℝ, H2 y * Q y) +
            ∫ y : ℝ, d * (H1 y * Q y)) +
            ∫ y : ℝ, k * (H0 y * Q y) := by
        rw [integral_add h2int (h1int.const_mul d)]
      _ = _ := by rw [integral_const_mul, integral_const_mul]
  unfold weightedMovingHeatGeneratorKernel weightedMovingHeatGeneratorBase
  unfold weightedMovingHeatMarkovKernel
  rw [show (fun y : ℝ =>
      weightedMovingHeatGrowth eta c r *
        (deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel r w) u)
              (x + (c - 2 * eta) * r - y) +
          (c - 2 * eta) * deriv (fun w : ℝ => heatKernel r w)
              (x + (c - 2 * eta) * r - y) +
          (eta ^ 2 - c * eta) * heatKernel r
              (x + (c - 2 * eta) * r - y)) *
        heatKernel q (y + (c - 2 * eta) * q - z)) =
      fun y => weightedMovingHeatGrowth eta c r *
        (H2 y + d * H1 y + k * H0 y) * Q y by
    funext y
    dsimp [H2, H1, H0, Q, X, A, d, k]
    ring_nf]
  rw [show (∫ y : ℝ,
      weightedMovingHeatGrowth eta c r *
        (H2 y + d * H1 y + k * H0 y) * Q y) =
      weightedMovingHeatGrowth eta c r *
        ∫ y : ℝ, (H2 y + d * H1 y + k * H0 y) * Q y by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    ring]
  rw [hsplit]
  rw [show (∫ y : ℝ, H2 y * Q y) =
      deriv (fun u : ℝ =>
        deriv (fun w : ℝ => heatKernel (r + q) w) u) (X - A) by
    simpa [H2, Q] using
      secondDeriv_heatKernel_convolution_add (r := r) (q := q)
        (X := X) (A := A) hr hq]
  rw [show (∫ y : ℝ, H1 y * Q y) =
      deriv (fun w : ℝ => heatKernel (r + q) w) (X - A) by
    simpa [H1, Q] using
      deriv_heatKernel_convolution_add (r := r) (q := q)
        (X := X) (A := A) hr hq]
  rw [show (∫ y : ℝ, H0 y * Q y) =
      heatKernel (r + q) (X - A) by
    simpa [H0, Q] using
      heatKernel_convolution_add (t := r) (s := q) (x := X) (z := A) hr hq]
  have hgrowth : weightedMovingHeatGrowth eta c q *
      weightedMovingHeatGrowth eta c r =
      weightedMovingHeatGrowth eta c (r + q) := by
    unfold weightedMovingHeatGrowth
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← mul_assoc, hgrowth]
  congr 1
  dsimp [X, A, d, k]
  ring_nf

/-- Absolute integrability of the generator/heat double kernel against an
arbitrary `L²` datum. -/
theorem weightedMovingHeatGeneratorKernel_comp_integrable
    {eta c r q x : ℝ} (hr : 0 < r) (hq : 0 < q)
    (Z : WholeLineRealL2) :
    Integrable
      (fun p : ℝ × ℝ =>
        weightedMovingHeatGeneratorKernel eta c r x p.1 *
          weightedMovingHeatMarkovKernel eta c q p.1 p.2 * Z p.2)
      (volume.prod volume) := by
  let J : ℝ × ℝ → ℝ := fun p =>
    weightedMovingHeatGeneratorKernel eta c r x p.1 *
      weightedMovingHeatMarkovKernel eta c q p.1 p.2 * Z p.2
  let K : ℝ :=
    (∫ z : ℝ,
        weightedMovingHeatMarkovKernel eta c q (0 : ℝ) z ^ (2 : ℝ)) ^
          (1 / (2 : ℝ)) *
      (∫ z : ℝ, Z z ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
  have hJmeas : AEStronglyMeasurable J (volume.prod volume) := by
    apply Measurable.aestronglyMeasurable
    dsimp [J]
    exact (((weightedMovingHeatGeneratorKernel_measurable
      (eta := eta) (c := c) hr).comp
        (measurable_const.prodMk measurable_fst)).mul
      ((weightedMovingHeatMarkovKernel_measurable eta c q).comp
        (measurable_fst.prodMk measurable_snd))).mul
      ((Lp.stronglyMeasurable Z).measurable.comp measurable_snd)
  have hsections : ∀ y : ℝ, Integrable (fun z : ℝ => J (y, z)) := by
    intro y
    have hraw := (weightedMovingHeatMarkovKernel_mul_integrable
      (eta := eta) (c := c) hq y Z).const_mul
        (weightedMovingHeatGeneratorKernel eta c r x y)
    simpa [J, mul_assoc] using hraw
  have hrowSq : ∀ y : ℝ,
      (∫ z : ℝ,
          weightedMovingHeatMarkovKernel eta c q y z ^ (2 : ℝ)) =
        ∫ z : ℝ,
          weightedMovingHeatMarkovKernel eta c q (0 : ℝ) z ^ (2 : ℝ) := by
    intro y
    unfold weightedMovingHeatMarkovKernel
    have hshift (a : ℝ) :
        (∫ z : ℝ, heatKernel q (a - z) ^ (2 : ℝ)) =
          ∫ z : ℝ, heatKernel q z ^ (2 : ℝ) := by
      calc
        (∫ z : ℝ, heatKernel q (a - z) ^ (2 : ℝ)) =
            ∫ z : ℝ, (fun w : ℝ => heatKernel q w ^ (2 : ℝ))
              (z + (-a)) := by
                apply integral_congr_ae
                filter_upwards with z
                rw [← heatKernel_neg]
                congr 3
                ring
        _ = ∫ z : ℝ, heatKernel q z ^ (2 : ℝ) :=
          MeasureTheory.integral_add_right_eq_self
            (μ := (volume : Measure ℝ))
            (fun w : ℝ => heatKernel q w ^ (2 : ℝ)) (-a)
    rw [hshift (y + (c - 2 * eta) * q)]
    simpa only [zero_add] using (hshift ((c - 2 * eta) * q)).symm
  have hholder : ∀ y : ℝ,
      ∫ z : ℝ, ‖weightedMovingHeatMarkovKernel eta c q y z‖ * ‖Z z‖ ≤ K := by
    intro y
    have hheat : MemLp (weightedMovingHeatMarkovKernel eta c q y)
        (ENNReal.ofReal (2 : ℝ)) volume := by
      simpa using weightedMovingHeatMarkovKernel_memLp_two
        (eta := eta) (c := c) hq y
    have hZ : MemLp (Z : ℝ → ℝ) (ENNReal.ofReal (2 : ℝ)) volume := by
      simpa using Lp.memLp Z
    have hraw := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
      (p := (2 : ℝ)) (q := (2 : ℝ)) (μ := volume)
      (f := weightedMovingHeatMarkovKernel eta c q y) (g := (Z : ℝ → ℝ))
      Real.HolderConjugate.two_two hheat hZ
    calc
      ∫ z : ℝ, ‖weightedMovingHeatMarkovKernel eta c q y z‖ * ‖Z z‖ ≤
          (∫ z : ℝ,
              weightedMovingHeatMarkovKernel eta c q y z ^ (2 : ℝ)) ^
                (1 / (2 : ℝ)) *
            (∫ z : ℝ, Z z ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
        simpa only [Real.norm_eq_abs, Real.rpow_two, sq_abs] using hraw
      _ = K := by rw [hrowSq y]
  have hsecMeas : AEStronglyMeasurable
      (fun y : ℝ => ∫ z : ℝ, ‖J (y, z)‖) volume :=
    hJmeas.norm.integral_prod_right'
  have hmajorInt : Integrable
      (fun y : ℝ => K *
        |weightedMovingHeatGeneratorKernel eta c r x y|) volume :=
    (weightedMovingHeatGeneratorKernel_abs_row_integrable
      (eta := eta) (c := c) hr x).const_mul K
  have hsecBound : ∀ y : ℝ,
      (∫ z : ℝ, ‖J (y, z)‖) ≤
        K * |weightedMovingHeatGeneratorKernel eta c r x y| := by
    intro y
    rw [show (∫ z : ℝ, ‖J (y, z)‖) =
        |weightedMovingHeatGeneratorKernel eta c r x y| *
          ∫ z : ℝ,
            ‖weightedMovingHeatMarkovKernel eta c q y z‖ * ‖Z z‖ by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with z
      dsimp [J]
      simp only [abs_mul]
      ring]
    rw [mul_comm K]
    exact mul_le_mul_of_nonneg_left (hholder y) (abs_nonneg _)
  exact (integrable_prod_iff hJmeas).2
    ⟨Eventually.of_forall hsections,
      hmajorInt.mono' hsecMeas (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
        exact hsecBound y)⟩

section AxiomAudit

#print axioms weightedMovingHeatL2Semigroup_norm_le_of_pos
#print axioms weightedMovingHeatL2Semigroup_add
#print axioms weightedMovingHeatGeneratorMass_le_bound
#print axioms weightedMovingHeatGeneratorL2CLM_norm_le_horizon
#print axioms weightedMovingHeatGeneratorL2CLM_coe_ae
#print axioms weightedMovingHeatL2Generator_norm_le_horizon
#print axioms weightedMovingHeatGeneratorKernel_comp_integrable

end AxiomAudit

end ShenWork.Paper1
