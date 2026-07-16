import ShenWork.Paper1.WholeLineWeightedRegularityL2Semigroup

open Filter MeasureTheory Set Topology
open scoped RealInnerProductSpace

noncomputable section

namespace ShenWork.Paper1

/-!
# The spatial heat gradient on weighted whole-line `L²`

This file packages the scalar Schur estimate for
`weightedMovingHeatGradientEta` as a continuous linear operator on
`WholeLineRealL2`.  The construction uses only the value-level `L²` datum;
in particular, it assumes no spatial derivative of that datum.
-/

/-- The signed convolution kernel of the first spatial derivative of the
conjugated moving heat flow. -/
def weightedMovingHeatGradientKernel
    (eta c t x y : ℝ) : ℝ :=
  weightedMovingHeatGrowth eta c t *
    deriv (fun z : ℝ => heatKernel t z)
      (x + (c - 2 * eta) * t - y)

/-- The sharp `L²` Schur mass of the conjugated heat-gradient kernel. -/
def weightedMovingHeatGradientMass (eta c t : ℝ) : ℝ :=
  weightedMovingHeatGrowth eta c t /
    Real.sqrt (Real.pi * t)

theorem weightedMovingHeatGradientKernel_measurable
    {eta c t : ℝ} (ht : 0 < t) :
    Measurable (Function.uncurry
      (weightedMovingHeatGradientKernel eta c t)) := by
  unfold weightedMovingHeatGradientKernel Function.uncurry
  simp_rw [deriv_heatKernel ht]
  unfold heatKernel
  fun_prop

theorem weightedMovingHeatGradientKernel_abs_measurable
    {eta c t : ℝ} (ht : 0 < t) :
    Measurable (Function.uncurry
      (fun x y => |weightedMovingHeatGradientKernel eta c t x y|)) :=
  (weightedMovingHeatGradientKernel_measurable
    (eta := eta) (c := c) ht).abs

private theorem weightedMovingHeatGradient_sqrt_identity
    {t : ℝ} (ht : 0 < t) :
    2 / Real.sqrt (4 * Real.pi * t) =
      1 / Real.sqrt (Real.pi * t) := by
  have hpit : 0 < Real.pi * t := by positivity
  have hs : 0 < Real.sqrt (Real.pi * t) := Real.sqrt_pos.mpr hpit
  have hs4 : Real.sqrt (4 * Real.pi * t) =
      2 * Real.sqrt (Real.pi * t) := by
    rw [show 4 * Real.pi * t = 4 * (Real.pi * t) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  rw [hs4]
  field_simp [ne_of_gt hs]

theorem weightedMovingHeatGradientKernel_abs_row_integrable
    {eta c t : ℝ} (ht : 0 < t) (x : ℝ) :
    Integrable
      (fun y => |weightedMovingHeatGradientKernel eta c t x y|) volume := by
  have hbase := (heatKernel_deriv_abs_integrable ht).comp_neg.comp_add_right
    (-(x + (c - 2 * eta) * t))
  have hg : 0 ≤ weightedMovingHeatGrowth eta c t := Real.exp_nonneg _
  have hscaled := hbase.const_mul (weightedMovingHeatGrowth eta c t)
  refine hscaled.congr (Eventually.of_forall fun y => ?_)
  simp only [weightedMovingHeatGradientKernel, abs_mul, abs_of_nonneg hg]
  congr 2
  ring

theorem weightedMovingHeatGradientKernel_abs_row_mass
    {eta c t : ℝ} (ht : 0 < t) (x : ℝ) :
    (∫ y : ℝ, |weightedMovingHeatGradientKernel eta c t x y|) =
      weightedMovingHeatGradientMass eta c t := by
  have hg : 0 ≤ weightedMovingHeatGrowth eta c t := Real.exp_nonneg _
  unfold weightedMovingHeatGradientKernel weightedMovingHeatGradientMass
  rw [show (fun y : ℝ =>
      |weightedMovingHeatGrowth eta c t *
        deriv (fun z : ℝ => heatKernel t z)
          (x + (c - 2 * eta) * t - y)|) =
      fun y => weightedMovingHeatGrowth eta c t *
        |deriv (fun z : ℝ => heatKernel t z)
          (x + (c - 2 * eta) * t - y)| by
    funext y
    rw [abs_mul, abs_of_nonneg hg]]
  rw [integral_const_mul]
  let a := x + (c - 2 * eta) * t
  let F : ℝ → ℝ := fun z =>
    |deriv (fun w : ℝ => heatKernel t w) z|
  have hshift : (∫ y : ℝ,
      |deriv (fun z : ℝ => heatKernel t z)
        (x + (c - 2 * eta) * t - y)|) =
      ∫ z : ℝ, F z := by
    calc
      (∫ y : ℝ,
          |deriv (fun z : ℝ => heatKernel t z)
            (x + (c - 2 * eta) * t - y)|) =
          ∫ y : ℝ, F (-(y - a)) := by
            apply integral_congr_ae
            filter_upwards with y
            dsimp [F, a]
            congr 2
            ring
      _ = ∫ q : ℝ, F (-q) :=
        integral_sub_right_eq_self (fun q => F (-q)) a
      _ = ∫ z : ℝ, F z := integral_neg_eq_self F volume
  rw [hshift]
  change weightedMovingHeatGrowth eta c t *
      (∫ z : ℝ, |deriv (fun w : ℝ => heatKernel t w) z|) = _
  rw [heatKernel_deriv_abs_integral ht,
    weightedMovingHeatGradient_sqrt_identity ht]
  ring

theorem weightedMovingHeatGradientKernel_abs_col_integrable
    {eta c t : ℝ} (ht : 0 < t) (y : ℝ) :
    Integrable
      (fun x => |weightedMovingHeatGradientKernel eta c t x y|) volume := by
  have hbase := (heatKernel_deriv_abs_integrable ht).comp_add_right
    ((c - 2 * eta) * t - y)
  have hg : 0 ≤ weightedMovingHeatGrowth eta c t := Real.exp_nonneg _
  have hscaled := hbase.const_mul (weightedMovingHeatGrowth eta c t)
  refine hscaled.congr (Eventually.of_forall fun x => ?_)
  simp only [weightedMovingHeatGradientKernel, abs_mul, abs_of_nonneg hg]
  congr 2
  ring

theorem weightedMovingHeatGradientKernel_abs_col_mass
    {eta c t : ℝ} (ht : 0 < t) (y : ℝ) :
    (∫ x : ℝ, |weightedMovingHeatGradientKernel eta c t x y|) =
      weightedMovingHeatGradientMass eta c t := by
  have hg : 0 ≤ weightedMovingHeatGrowth eta c t := Real.exp_nonneg _
  unfold weightedMovingHeatGradientKernel weightedMovingHeatGradientMass
  rw [show (fun x : ℝ =>
      |weightedMovingHeatGrowth eta c t *
        deriv (fun z : ℝ => heatKernel t z)
          (x + (c - 2 * eta) * t - y)|) =
      fun x => weightedMovingHeatGrowth eta c t *
        |deriv (fun z : ℝ => heatKernel t z)
          (x + (c - 2 * eta) * t - y)| by
    funext x
    rw [abs_mul, abs_of_nonneg hg]]
  rw [integral_const_mul]
  have htranslate :
      (∫ x : ℝ, |deriv (fun z : ℝ => heatKernel t z)
        (x + (c - 2 * eta) * t - y)|) =
      ∫ z : ℝ, |deriv (fun w : ℝ => heatKernel t w) z| := by
    let F : ℝ → ℝ := fun z =>
      |deriv (fun w : ℝ => heatKernel t w) z|
    calc
      (∫ x : ℝ, |deriv (fun z : ℝ => heatKernel t z)
          (x + (c - 2 * eta) * t - y)|) =
          ∫ x : ℝ, F (x + ((c - 2 * eta) * t - y)) := by
            apply integral_congr_ae
            filter_upwards with x
            dsimp [F]
            congr 2
            ring
      _ = ∫ z : ℝ, F z := integral_add_right_eq_self _ _
  rw [htranslate, heatKernel_deriv_abs_integral ht,
    weightedMovingHeatGradient_sqrt_identity ht]
  ring

theorem weightedMovingHeatGradientKernel_row_memLp_two
    {eta c t : ℝ} (ht : 0 < t) (x : ℝ) :
    MemLp (weightedMovingHeatGradientKernel eta c t x) 2 volume := by
  let a := x + (c - 2 * eta) * t
  have hmpNeg : MeasurePreserving (fun y : ℝ => -y) volume volume :=
    Measure.measurePreserving_neg volume
  have hmpAdd : MeasurePreserving (fun y : ℝ => a + y) volume volume :=
    measurePreserving_add_left volume a
  have hcomp := (heatKernel_deriv_memLp_two ht).comp_measurePreserving
    (hmpAdd.comp hmpNeg)
  have hscaled := hcomp.const_mul (weightedMovingHeatGrowth eta c t)
  convert hscaled using 1

theorem weightedMovingHeatGradientKernel_row_mul_l2_integrable
    {eta c t : ℝ} (ht : 0 < t) (x : ℝ) (Z : WholeLineRealL2) :
    Integrable
      (fun y => weightedMovingHeatGradientKernel eta c t x y * Z y)
      volume := by
  have hmul := (weightedMovingHeatGradientKernel_row_memLp_two
    (eta := eta) (c := c) ht x).integrable_mul (Lp.memLp Z)
  simpa only [Pi.mul_apply] using hmul

theorem weightedMovingHeatGradientMass_nonneg
    {eta c t : ℝ} (_ht : 0 < t) :
    0 ≤ weightedMovingHeatGradientMass eta c t := by
  unfold weightedMovingHeatGradientMass
  exact div_nonneg (Real.exp_nonneg _) (Real.sqrt_nonneg _)

/-- Concrete signed-Schur data for the first spatial heat derivative. -/
def weightedMovingHeatGradientSchurData
    (eta c t : ℝ) (ht : 0 < t) :
    WholeLineL2SchurKernelData
      (weightedMovingHeatGradientKernel eta c t)
      (weightedMovingHeatGradientMass eta c t) where
  mass_nonneg := weightedMovingHeatGradientMass_nonneg ht
  kernel_measurable := weightedMovingHeatGradientKernel_measurable ht
  absKernel_measurable := weightedMovingHeatGradientKernel_abs_measurable ht
  abs_row_integrable := weightedMovingHeatGradientKernel_abs_row_integrable ht
  abs_row_mass := weightedMovingHeatGradientKernel_abs_row_mass ht
  abs_col_integrable := weightedMovingHeatGradientKernel_abs_col_integrable ht
  abs_col_mass := weightedMovingHeatGradientKernel_abs_col_mass ht
  row_mul_l2_integrable := weightedMovingHeatGradientKernel_row_mul_l2_integrable ht

/-- The positive-time first spatial derivative of the conjugated moving heat
flow as a continuous linear map on `L²(ℝ)`. -/
def weightedMovingHeatGradientL2CLM
    (eta c t : ℝ) (ht : 0 < t) :
    WholeLineRealL2 →L[ℝ] WholeLineRealL2 :=
  (weightedMovingHeatGradientSchurData eta c t ht).toCLM

/-- Kernel representative of the `L²` heat-gradient lift. -/
theorem weightedMovingHeatGradientL2CLM_kernel_coe_ae
    {eta c t : ℝ} (ht : 0 < t) (Z : WholeLineRealL2) :
    (((weightedMovingHeatGradientL2CLM eta c t ht) Z : WholeLineRealL2) :
        ℝ → ℝ) =ᵐ[volume]
      fun x => ∫ y : ℝ,
        weightedMovingHeatGradientKernel eta c t x y * Z y := by
  exact (weightedMovingHeatGradientSchurData eta c t ht).toL2Fun_coe_ae Z

/-- The `L²` lift has exactly the scalar heat-gradient representative. -/
theorem weightedMovingHeatGradientL2CLM_coe_ae
    {eta c t : ℝ} (ht : 0 < t) (Z : WholeLineRealL2) :
    (((weightedMovingHeatGradientL2CLM eta c t ht) Z : WholeLineRealL2) :
        ℝ → ℝ) =ᵐ[volume]
      weightedMovingHeatGradientEta eta c t (Z : ℝ → ℝ) := by
  have hrep := weightedMovingHeatGradientL2CLM_kernel_coe_ae
    (eta := eta) (c := c) ht Z
  filter_upwards [hrep] with x hx
  rw [hx]
  unfold weightedMovingHeatGradientKernel weightedMovingHeatGradientEta
  rw [show (fun y : ℝ => weightedMovingHeatGrowth eta c t *
      deriv (fun z : ℝ => heatKernel t z)
        (x + (c - 2 * eta) * t - y) * Z y) =
      fun y => weightedMovingHeatGrowth eta c t *
        (deriv (fun z : ℝ => heatKernel t z)
          (x + (c - 2 * eta) * t - y) * Z y) by
    funext y
    ring]
  rw [integral_const_mul]

/-- Sharp operator-norm estimate for the first spatial heat derivative. -/
theorem weightedMovingHeatGradientL2CLM_norm_le
    {eta c t : ℝ} (ht : 0 < t) :
    ‖weightedMovingHeatGradientL2CLM eta c t ht‖ ≤
      weightedMovingHeatGrowth eta c t /
        Real.sqrt (Real.pi * t) := by
  exact (weightedMovingHeatGradientSchurData eta c t ht).toCLM_norm_le

/-- Pointwise sharp `L²` smoothing estimate. -/
theorem weightedMovingHeatGradientL2CLM_apply_norm_le
    {eta c t : ℝ} (ht : 0 < t) (Z : WholeLineRealL2) :
    ‖(weightedMovingHeatGradientL2CLM eta c t ht) Z‖ ≤
      (weightedMovingHeatGrowth eta c t /
        Real.sqrt (Real.pi * t)) * ‖Z‖ := by
  exact (weightedMovingHeatGradientSchurData eta c t ht).toL2Fun_norm_le Z

/-! ## Compatibility with the weighted heat semigroup -/

/-- The signed first-derivative kernel composes with a later heat step by
addition of the two positive times. -/
theorem weightedMovingHeatGradientKernel_convolution_add
    {eta c r q x z : ℝ} (hr : 0 < r) (hq : 0 < q) :
    weightedMovingHeatGrowth eta c q *
        (∫ y : ℝ,
          weightedMovingHeatGradientKernel eta c r x y *
            weightedMovingHeatMarkovKernel eta c q y z) =
      weightedMovingHeatGradientKernel eta c (r + q) x z := by
  let d : ℝ := c - 2 * eta
  let X : ℝ := x + d * r
  let A : ℝ := z - d * q
  unfold weightedMovingHeatGradientKernel weightedMovingHeatMarkovKernel
  rw [show (fun y : ℝ =>
      weightedMovingHeatGrowth eta c r *
          deriv (fun w : ℝ => heatKernel r w)
            (x + (c - 2 * eta) * r - y) *
        heatKernel q (y + (c - 2 * eta) * q - z)) =
      fun y => weightedMovingHeatGrowth eta c r *
        (deriv (fun w : ℝ => heatKernel r w) (X - y) *
          heatKernel q (y - A)) by
    funext y
    dsimp [X, A, d]
    ring_nf]
  rw [integral_const_mul,
    deriv_heatKernel_convolution_add (r := r) (q := q)
      (X := X) (A := A) hr hq]
  have hgrowth : weightedMovingHeatGrowth eta c q *
      weightedMovingHeatGrowth eta c r =
      weightedMovingHeatGrowth eta c (r + q) := by
    unfold weightedMovingHeatGrowth
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← mul_assoc, hgrowth]
  congr 1
  dsimp [X, A, d]
  ring_nf

/-- Absolute integrability of the heat-gradient/heat double kernel against
an arbitrary `L²` datum.  This is the Fubini input for semigroup
composition. -/
theorem weightedMovingHeatGradientKernel_comp_integrable
    {eta c r q x : ℝ} (hr : 0 < r) (hq : 0 < q)
    (Z : WholeLineRealL2) :
    Integrable
      (fun p : ℝ × ℝ =>
        weightedMovingHeatGradientKernel eta c r x p.1 *
          weightedMovingHeatMarkovKernel eta c q p.1 p.2 * Z p.2)
      (volume.prod volume) := by
  let J : ℝ × ℝ → ℝ := fun p =>
    weightedMovingHeatGradientKernel eta c r x p.1 *
      weightedMovingHeatMarkovKernel eta c q p.1 p.2 * Z p.2
  let K : ℝ :=
    (∫ z : ℝ,
        weightedMovingHeatMarkovKernel eta c q (0 : ℝ) z ^ (2 : ℝ)) ^
          (1 / (2 : ℝ)) *
      (∫ z : ℝ, Z z ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
  have hJmeas : AEStronglyMeasurable J (volume.prod volume) := by
    apply Measurable.aestronglyMeasurable
    dsimp [J]
    exact (((weightedMovingHeatGradientKernel_measurable
      (eta := eta) (c := c) hr).comp
        (measurable_const.prodMk measurable_fst)).mul
      ((weightedMovingHeatMarkovKernel_measurable eta c q).comp
        (measurable_fst.prodMk measurable_snd))).mul
      ((Lp.stronglyMeasurable Z).measurable.comp measurable_snd)
  have hsections : ∀ y : ℝ, Integrable (fun z : ℝ => J (y, z)) := by
    intro y
    have hraw := (weightedMovingHeatMarkovKernel_mul_integrable
      (eta := eta) (c := c) hq y Z).const_mul
        (weightedMovingHeatGradientKernel eta c r x y)
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
          integral_add_right_eq_self
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
    have hraw := integral_mul_norm_le_Lp_mul_Lq
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
        |weightedMovingHeatGradientKernel eta c r x y|) volume :=
    (weightedMovingHeatGradientKernel_abs_row_integrable
      (eta := eta) (c := c) hr x).const_mul K
  have hsecBound : ∀ y : ℝ,
      (∫ z : ℝ, ‖J (y, z)‖) ≤
        K * |weightedMovingHeatGradientKernel eta c r x y| := by
    intro y
    rw [show (∫ z : ℝ, ‖J (y, z)‖) =
        |weightedMovingHeatGradientKernel eta c r x y| *
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
        rw [Real.norm_eq_abs,
          abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
        exact hsecBound y)⟩

/-- Positive-time `L²` composition law
`(∂ₓS(r)) S(q) = ∂ₓS(r+q)`. -/
theorem weightedMovingHeatGradientL2CLM_comp_heat
    {eta c r q : ℝ} (hr : 0 < r) (hq : 0 < q) :
    (weightedMovingHeatGradientL2CLM eta c r hr).comp
        (weightedMovingHeatL2CLM eta c q hq) =
      weightedMovingHeatGradientL2CLM eta c (r + q) (add_pos hr hq) := by
  ext Z
  simp only [ContinuousLinearMap.comp_apply, weightedMovingHeatL2CLM_apply]
  have houter := weightedMovingHeatGradientL2CLM_kernel_coe_ae
    (eta := eta) (c := c) hr (weightedMovingHeatL2Fun eta c q hq Z)
  have hinner := weightedMovingHeatL2Fun_coe_ae
    (eta := eta) (c := c) hq Z
  have hright := weightedMovingHeatGradientL2CLM_kernel_coe_ae
    (eta := eta) (c := c) (add_pos hr hq) Z
  filter_upwards [houter, hright] with x hxOuter hxRight
  rw [hxOuter, hxRight]
  have hreplace :
      (∫ y : ℝ,
          weightedMovingHeatGradientKernel eta c r x y *
            (((weightedMovingHeatL2Fun eta c q hq Z : WholeLineRealL2) :
              ℝ → ℝ) y)) =
        ∫ y : ℝ,
          weightedMovingHeatGradientKernel eta c r x y *
            weightedMovingHeatEta eta c q (Z : ℝ → ℝ) y := by
    apply integral_congr_ae
    filter_upwards [hinner] with y hy
    rw [hy]
  rw [hreplace]
  unfold weightedMovingHeatEta
  let J : ℝ × ℝ → ℝ := fun p =>
    weightedMovingHeatGradientKernel eta c r x p.1 *
      weightedMovingHeatMarkovKernel eta c q p.1 p.2 * Z p.2
  have hswap := integral_integral_swap
    (f := fun y z : ℝ => J (y, z))
    (weightedMovingHeatGradientKernel_comp_integrable
      (eta := eta) (c := c) (x := x) hr hq Z)
  rw [show
      (∫ y : ℝ,
          weightedMovingHeatGradientKernel eta c r x y *
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
          weightedMovingHeatGradientKernel eta c r x y *
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
      weightedMovingHeatGrowth eta c q *
          (∫ z : ℝ, ∫ y : ℝ, J (y, z)) =
        ∫ z : ℝ,
          weightedMovingHeatGradientKernel eta c (r + q) x z * Z z by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with z
    dsimp [J]
    rw [integral_mul_const, ← mul_assoc,
      weightedMovingHeatGradientKernel_convolution_add hr hq]]

/-- Totalized first spatial heat-gradient family: its value at nonpositive
time is zero. -/
def weightedMovingHeatL2Gradient (eta c r : ℝ) :
    WholeLineRealL2 →L[ℝ] WholeLineRealL2 :=
  if hr : 0 < r then weightedMovingHeatGradientL2CLM eta c r hr else 0

theorem weightedMovingHeatL2Gradient_of_pos
    {eta c r : ℝ} (hr : 0 < r) :
    weightedMovingHeatL2Gradient eta c r =
      weightedMovingHeatGradientL2CLM eta c r hr := by
  simp only [weightedMovingHeatL2Gradient, dif_pos hr]

@[simp]
theorem weightedMovingHeatL2Gradient_zero (eta c : ℝ) :
    weightedMovingHeatL2Gradient eta c 0 = 0 := by
  simp [weightedMovingHeatL2Gradient]

/-- Totalized composition law at a nonnegative later heat time. -/
theorem weightedMovingHeatL2Gradient_comp_semigroup_add
    {eta c r q : ℝ} (hr : 0 < r) (hq : 0 ≤ q) :
    (weightedMovingHeatL2Gradient eta c r).comp
        (weightedMovingHeatL2Semigroup eta c q) =
      weightedMovingHeatL2Gradient eta c (r + q) := by
  rcases hq.eq_or_lt with hq0 | hq
  · subst q
    rw [weightedMovingHeatL2Semigroup_zero, add_zero]
    ext Z
    rfl
  · rw [weightedMovingHeatL2Gradient_of_pos hr,
      weightedMovingHeatL2Semigroup_of_pos hq,
      weightedMovingHeatL2Gradient_of_pos (add_pos hr hq)]
    exact weightedMovingHeatGradientL2CLM_comp_heat hr hq

section AxiomAudit

#print axioms weightedMovingHeatGradientL2CLM_kernel_coe_ae
#print axioms weightedMovingHeatGradientL2CLM_coe_ae
#print axioms weightedMovingHeatGradientL2CLM_norm_le
#print axioms weightedMovingHeatGradientL2CLM_apply_norm_le
#print axioms weightedMovingHeatGradientKernel_convolution_add
#print axioms weightedMovingHeatGradientKernel_comp_integrable
#print axioms weightedMovingHeatGradientL2CLM_comp_heat
#print axioms weightedMovingHeatL2Gradient_zero
#print axioms weightedMovingHeatL2Gradient_comp_semigroup_add

end AxiomAudit

end ShenWork.Paper1
