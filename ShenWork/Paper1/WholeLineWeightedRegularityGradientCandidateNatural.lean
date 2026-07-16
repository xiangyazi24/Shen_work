import ShenWork.Paper1.WholeLineWeightedRegularityGradientCandidate
import ShenWork.Paper1.WholeLineWeightedRegularityForcingWindowNatural
import ShenWork.Paper1.WholeLineWeightedRegularityBoundedDriftRestart
import ShenWork.Paper1.WholeLineWeightedRegularityForcingTrajectory
import ShenWork.Paper1.WholeLineWeightedRegularityGlobalH0
import ShenWork.Paper1.WholeLineWeightedRegularityCompactHolderClosure
import ShenWork.PDE.IntervalFullKernelSDependentMeasurable

open Filter MeasureTheory Set Topology
open scoped RealInnerProductSpace Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Natural data for the full weighted gradient candidate

The full weighted spatial-gradient candidate uses only the exact-weight
generator forcing.  This file supplies the measurable positive-lag heat
history and the remaining measure-theoretic restart data without assuming a
spatial derivative of that forcing.
-/

/-- Operator-norm form of the already established apply-level positive-lag
gradient modulus. -/
theorem weightedMovingHeatL2Gradient_sub_norm_le_rpow_neg_three_half
    {eta c H r h : ℝ}
    (hr : 0 < r) (hh : 0 ≤ h) (hrhH : r + h ≤ H) :
    ‖weightedMovingHeatL2Gradient eta c (r + h) -
        weightedMovingHeatL2Gradient eta c r‖ ≤
      weightedMovingHeatGradientTimeHorizonConst eta c H * h *
        r ^ (-(3 / 2 : ℝ)) := by
  have hH : 0 ≤ H := by linarith
  have hC : 0 ≤ weightedMovingHeatGradientTimeHorizonConst eta c H * h *
      r ^ (-(3 / 2 : ℝ)) :=
    mul_nonneg
      (mul_nonneg
        (weightedMovingHeatGradientTimeHorizonConst_nonneg hH) hh)
      (Real.rpow_nonneg hr.le _)
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro Z
  rw [ContinuousLinearMap.sub_apply]
  exact weightedMovingHeatL2Gradient_sub_apply_norm_le_rpow_neg_three_half
    hr hh hrhH Z

/-- The totalized weighted heat-gradient operator is norm-continuous at every
strictly positive lag. -/
theorem weightedMovingHeatL2Gradient_continuousAt_of_pos
    {eta c r : ℝ} (hr : 0 < r) :
    ContinuousAt (weightedMovingHeatL2Gradient eta c) r := by
  rw [Metric.continuousAt_iff]
  intro eps heps
  let H : ℝ := 2 * r
  let C : ℝ := weightedMovingHeatGradientTimeHorizonConst eta c H *
    (r / 2) ^ (-(3 / 2 : ℝ))
  have hH : 0 ≤ H := by dsimp [H]; linarith
  have hTC : 0 ≤ weightedMovingHeatGradientTimeHorizonConst eta c H :=
    weightedMovingHeatGradientTimeHorizonConst_nonneg hH
  have hrhalf : 0 < r / 2 := by linarith
  have hrpow : 0 ≤ (r / 2) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_nonneg hrhalf.le _
  have hC : 0 ≤ C := mul_nonneg hTC hrpow
  let delta : ℝ := min (r / 2) (eps / (C + 1))
  have hC1 : 0 < C + 1 := by linarith
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact lt_min hrhalf (div_pos heps hC1)
  refine ⟨delta, hdelta, ?_⟩
  intro y hy
  rw [Real.dist_eq] at hy
  have hyr : |y - r| < r / 2 :=
    hy.trans_le (min_le_left _ _)
  have hyhalf : r / 2 < y := by
    have hneg : -(r / 2) < y - r := neg_lt_of_abs_lt hyr
    linarith
  have hypos : 0 < y := hrhalf.trans hyhalf
  have hyH : y ≤ H := by
    have hupper : y - r < r / 2 := lt_of_abs_lt hyr
    dsimp only [H]
    linarith
  have hdistSmall : |y - r| < eps / (C + 1) :=
    hy.trans_le (min_le_right _ _)
  have hCdist : C * |y - r| < eps := by
    have hmul : (C + 1) * |y - r| < eps := by
      have habs0 : 0 ≤ |y - r| := abs_nonneg _
      have := mul_lt_mul_of_pos_left hdistSmall hC1
      have hcancel : (C + 1) * (eps / (C + 1)) = eps := by
        field_simp [hC1.ne']
      rw [hcancel] at this
      exact this
    nlinarith [abs_nonneg (y - r)]
  rw [dist_eq_norm]
  rcases le_total r y with hry | hyrle
  · have hstep : 0 ≤ y - r := sub_nonneg.mpr hry
    have hsum : r + (y - r) ≤ H := by simpa using hyH
    have hmod :=
      weightedMovingHeatL2Gradient_sub_norm_le_rpow_neg_three_half
        (eta := eta) (c := c) hr hstep hsum
    have habs : |y - r| = y - r := abs_of_nonneg hstep
    calc
      ‖weightedMovingHeatL2Gradient eta c y -
          weightedMovingHeatL2Gradient eta c r‖ =
          ‖weightedMovingHeatL2Gradient eta c (r + (y - r)) -
            weightedMovingHeatL2Gradient eta c r‖ := by ring_nf
      _ ≤ (weightedMovingHeatGradientTimeHorizonConst eta c H *
            r ^ (-(3 / 2 : ℝ)) * (y - r)) := by
          simpa only [mul_assoc, mul_left_comm, mul_comm] using hmod
      _ ≤ C * |y - r| := by
        rw [habs]
        apply mul_le_mul_of_nonneg_right _ hstep
        dsimp only [C]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hrhalf
            (by linarith : r / 2 ≤ r)
            (by norm_num : -(3 / 2 : ℝ) ≤ 0)) hTC
      _ < eps := hCdist
  · have hstep : 0 ≤ r - y := sub_nonneg.mpr hyrle
    have hsum : y + (r - y) ≤ H := by
      dsimp only [H]
      linarith
    have hmod :=
      weightedMovingHeatL2Gradient_sub_norm_le_rpow_neg_three_half
        (eta := eta) (c := c) hypos hstep hsum
    have habs : |y - r| = r - y := by
      rw [abs_of_nonpos (sub_nonpos.mpr hyrle)]
      ring
    calc
      ‖weightedMovingHeatL2Gradient eta c y -
          weightedMovingHeatL2Gradient eta c r‖ =
          ‖weightedMovingHeatL2Gradient eta c (y + (r - y)) -
            weightedMovingHeatL2Gradient eta c y‖ := by
          rw [show y + (r - y) = r by ring, norm_sub_rev]
      _ ≤ (weightedMovingHeatGradientTimeHorizonConst eta c H *
            y ^ (-(3 / 2 : ℝ)) * (r - y)) := by
          simpa only [mul_assoc, mul_left_comm, mul_comm] using hmod
      _ ≤ C * |y - r| := by
        rw [habs]
        apply mul_le_mul_of_nonneg_right _ hstep
        dsimp only [C]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hrhalf hyhalf.le
            (by norm_num : -(3 / 2 : ℝ) ≤ 0)) hTC
      _ < eps := hCdist

/-- Positive-lag continuity after reversing time about a fixed terminal
time. -/
theorem weightedMovingHeatL2Gradient_terminal_continuousOn_Iio
    (eta c r : ℝ) :
    ContinuousOn (fun q => weightedMovingHeatL2Gradient eta c (r - q))
      (Set.Iio r) := by
  intro q hq
  exact (weightedMovingHeatL2Gradient_continuousAt_of_pos
    (sub_pos.mpr hq)).comp_continuousWithinAt
      (continuousAt_const.sub continuousAt_id).continuousWithinAt

/-- The totalized terminal heat-gradient operator is strongly measurable in
the history variable.  Its only discontinuity is the null terminal slice;
outside the positive-lag half-line it is exactly zero. -/
theorem weightedMovingHeatL2Gradient_terminal_aestronglyMeasurable
    (eta c r : ℝ) :
    AEStronglyMeasurable
      (fun q => weightedMovingHeatL2Gradient eta c (r - q)) volume := by
  let G : ℝ → WholeLineRealL2 →L[ℝ] WholeLineRealL2 :=
    fun q => weightedMovingHeatL2Gradient eta c (r - q)
  have hGlt : AEStronglyMeasurable G (volume.restrict (Set.Iio r)) :=
    (weightedMovingHeatL2Gradient_terminal_continuousOn_Iio eta c r).aestronglyMeasurable
      measurableSet_Iio
  have hind : AEStronglyMeasurable ((Set.Iio r).indicator G) volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Iio).2 hGlt
  refine hind.congr (Eventually.of_forall fun q => ?_)
  by_cases hq : q < r
  · simp [Set.indicator, hq, G]
  · have hlag : r - q ≤ 0 := sub_nonpos.mpr (le_of_not_gt hq)
    simp [Set.indicator, hq, G, weightedMovingHeatL2Gradient,
      not_lt.mpr hlag]

/-- Strong measurability of an exact-weight forcing trajectory passes through
the variable positive-lag heat-gradient operator. -/
theorem weightedMovingHeatL2Gradient_history_aestronglyMeasurable
    {eta c r : ℝ} {F : ℝ → WholeLineRealL2}
    (hF : AEStronglyMeasurable F volume) :
    AEStronglyMeasurable
      (fun q => weightedMovingHeatL2Gradient eta c (r - q) (F q))
      volume := by
  exact isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂
    (weightedMovingHeatL2Gradient_terminal_aestronglyMeasurable eta c r) hF

/-- Joint measurability of a scalar source passes through the moving
weighted heat-gradient kernel.  The global closed form of the Gaussian
derivative handles the totalized nonpositive-lag branch, so no exceptional
time slice has to be removed by hand. -/
theorem weightedMovingHeatGradientEta_history_stronglyMeasurable_of_joint_measurable
    {eta c tau : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) :
    StronglyMeasurable
      (fun z : ℝ × ℝ =>
        weightedMovingHeatGradientEta eta c (tau - z.1) (f z.1) z.2) := by
  let raw : (ℝ × ℝ) × ℝ → ℝ := fun z =>
    deriv (fun w : ℝ => heatKernel (tau - z.1.1) w)
        (z.1.2 + (c - 2 * eta) * (tau - z.1.1) - z.2) *
      f z.1.1 z.2
  have hraw : StronglyMeasurable raw := by
    apply Measurable.stronglyMeasurable
    have hfraw : Measurable (fun z : (ℝ × ℝ) × ℝ =>
        f z.1.1 z.2) :=
      hf.comp (measurable_fst.fst.prodMk measurable_snd)
    dsimp only [raw]
    simp_rw [ShenWork.IntervalNeumannFullKernel.deriv_heatKernel_global]
    unfold heatKernel
    fun_prop
  have hint : StronglyMeasurable
      (fun z : ℝ × ℝ => ∫ y : ℝ, raw (z, y)) :=
    hraw.integral_prod_right'
  have hgrowth : Continuous (fun z : ℝ × ℝ =>
      weightedMovingHeatGrowth eta c (tau - z.1)) := by
    dsimp only [weightedMovingHeatGrowth]
    fun_prop
  have hprod := hgrowth.stronglyMeasurable.mul hint
  simpa only [raw, weightedMovingHeatGradientEta] using hprod

/-- On every finite-measure spatial window, the scalar heat-gradient
history is product-integrable as soon as its exact `L²` history is Bochner
integrable.  The spatial `L¹` estimate is Cauchy--Schwarz against the
window indicator, so the endpoint singularity is used only to the first
power in time. -/
theorem weightedMovingHeatGradientEta_history_local_prod_integrable
    {eta c a r : ℝ} (har : a ≤ r)
    {f : ℝ → ℝ → ℝ} {F : ℝ → WholeLineRealL2}
    (hFrep : ∀ q ∈ Set.Ioc a r,
      (((F q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] f q))
    (hDint : IntervalIntegrable
      (fun q => weightedMovingHeatL2Gradient eta c (r - q) (F q))
      volume a r)
    (hjoint : Measurable (Function.uncurry f)) :
    ∀ A : Set ℝ, MeasurableSet A →
      (volume : Measure ℝ) A < ⊤ →
      Integrable
        (fun z : ℝ × ℝ => A.indicator
          (weightedMovingHeatGradientEta eta c (r - z.1) (f z.1)) z.2)
        ((volume.restrict (Set.Ioc a r)).prod volume) := by
  intro A hA hAfin
  let mu : Measure ℝ := volume.restrict (Set.Ioc a r)
  let D : ℝ → WholeLineRealL2 := fun q =>
    weightedMovingHeatL2Gradient eta c (r - q) (F q)
  let g : ℝ × ℝ → ℝ := fun z => A.indicator
    (weightedMovingHeatGradientEta eta c (r - z.1) (f z.1)) z.2
  have hscalar : AEStronglyMeasurable
      (fun z : ℝ × ℝ =>
        weightedMovingHeatGradientEta eta c (r - z.1) (f z.1) z.2)
      (mu.prod volume) :=
    (weightedMovingHeatGradientEta_history_stronglyMeasurable_of_joint_measurable
      (eta := eta) (c := c) (tau := r) hjoint).aestronglyMeasurable
  have hgmeas : AEStronglyMeasurable g (mu.prod volume) := by
    have hpre : MeasurableSet {z : ℝ × ℝ | z.2 ∈ A} :=
      hA.preimage measurable_snd
    exact (hscalar.indicator hpre).congr (Eventually.of_forall fun z => by
      by_cases hz : z.2 ∈ A <;> simp [g, hz])
  have hDrep : ∀ᵐ q ∂mu,
      (((D q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        weightedMovingHeatGradientEta eta c (r - q) (f q)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (Measure.ae_ne volume r).filter_mono ae_restrict_le] with q hq hqr
    have hlag : 0 < r - q := sub_pos.mpr (lt_of_le_of_ne hq.2 hqr)
    dsimp only [D]
    rw [weightedMovingHeatL2Gradient_of_pos hlag]
    exact (weightedMovingHeatGradientL2CLM_coe_ae hlag (F q)).trans
      (Eventually.of_forall fun x =>
        weightedMovingHeatGradientEta_congr_ae (hFrep q hq) x)
  have hsections : ∀ᵐ q ∂mu, Integrable (fun x => g (q, x)) volume := by
    filter_upwards [hDrep] with q hrep
    have hDon : IntegrableOn ((D q : WholeLineRealL2) : ℝ → ℝ) A
        volume :=
      integrableOn_Lp_of_measure_ne_top (D q)
        fact_one_le_two_ennreal.elim hAfin.ne
    have hDind : Integrable
        (A.indicator ((D q : WholeLineRealL2) : ℝ → ℝ)) volume :=
      (integrable_indicator_iff hA).2 hDon
    refine hDind.congr ?_
    filter_upwards [hrep] with x hx
    by_cases hxA : x ∈ A
    · simp [g, hxA, hx]
    · simp [g, hxA]
  let I : WholeLineRealL2 :=
    indicatorConstLp 2 hA hAfin.ne (1 : ℝ)
  have hDmu : Integrable D mu := by
    simpa only [mu, D] using
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le har).mp hDint)
  have hmajor : Integrable (fun q => ‖I‖ * ‖D q‖) mu :=
    hDmu.norm.const_mul ‖I‖
  have hinnerMeas : AEStronglyMeasurable
      (fun q => ∫ x, ‖g (q, x)‖ ∂volume) mu :=
    hgmeas.norm.integral_prod_right'
  have hinnerBound : ∀ᵐ q ∂mu,
      (∫ x, ‖g (q, x)‖ ∂volume) ≤ ‖I‖ * ‖D q‖ := by
    filter_upwards [hDrep] with q hrep
    have hImem : MemLp (I : ℝ → ℝ) (ENNReal.ofReal (2 : ℝ)) volume := by
      simpa using Lp.memLp I
    have hDmem : MemLp (D q : ℝ → ℝ) (ENNReal.ofReal (2 : ℝ)) volume := by
      simpa using Lp.memLp (D q)
    have hholder := integral_mul_norm_le_Lp_mul_Lq
      (p := (2 : ℝ)) (q := (2 : ℝ)) (μ := volume)
      (f := (I : ℝ → ℝ))
      (g := ((D q : WholeLineRealL2) : ℝ → ℝ))
      Real.HolderConjugate.two_two hImem hDmem
    have hleft : (∫ x, ‖g (q, x)‖ ∂volume) =
        ∫ x, ‖(I : ℝ → ℝ) x‖ * ‖(D q : ℝ → ℝ) x‖ ∂volume := by
      apply integral_congr_ae
      filter_upwards [indicatorConstLp_coeFn
          (p := 2) (hs := hA) (hμs := hAfin.ne) (c := (1 : ℝ)), hrep]
        with x hIx hDx
      by_cases hxA : x ∈ A
      · have hIx' : (I : ℝ → ℝ) x = 1 := by
          simpa only [Set.indicator_of_mem hxA] using hIx
        rw [hDx, hIx']
        simp [g, hxA]
      · have hIx' : (I : ℝ → ℝ) x = 0 := by
          simpa only [I, Set.indicator_of_notMem hxA] using hIx
        rw [hIx']
        simp [g, hxA]
    rw [hleft]
    calc
      (∫ x, ‖(I : ℝ → ℝ) x‖ * ‖(D q : ℝ → ℝ) x‖ ∂volume) ≤
          (∫ x, ‖(I : ℝ → ℝ) x‖ ^ (2 : ℝ) ∂volume) ^
              (1 / (2 : ℝ)) *
            (∫ x, ‖(D q : ℝ → ℝ) x‖ ^ (2 : ℝ) ∂volume) ^
              (1 / (2 : ℝ)) := hholder
      _ = ‖I‖ * ‖D q‖ := by
        rw [show (∫ x, ‖(I : ℝ → ℝ) x‖ ^ (2 : ℝ) ∂volume) =
            ‖I‖ ^ 2 by
          simpa only [Real.norm_eq_abs, Real.rpow_two, sq_abs] using
            (wholeLineRealL2_norm_sq_eq_integral I).symm,
          show (∫ x, ‖(D q : ℝ → ℝ) x‖ ^ (2 : ℝ) ∂volume) =
            ‖D q‖ ^ 2 by
          simpa only [Real.norm_eq_abs, Real.rpow_two, sq_abs] using
            (wholeLineRealL2_norm_sq_eq_integral (D q)).symm,
          ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
          Real.sqrt_sq (norm_nonneg I), Real.sqrt_sq (norm_nonneg (D q))]
  simpa only [mu, g] using (integrable_prod_iff hgmeas).2
    ⟨hsections, hmajor.mono' hinnerMeas (by
      filter_upwards [hinnerBound] with q hq
      rw [Real.norm_eq_abs,
        abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact hq)⟩

/-! ## Classical spatial differentiation for an `L²` datum -/

/-- Pointwise semigroup composition for the concrete representatives of an
`L²` datum.  The existing operator semigroup law only gives equality almost
everywhere; this pointwise form is what classical spatial differentiation
needs. -/
theorem weightedMovingHeatEta_comp_l2_data
    {eta c r q : ℝ} (hr : 0 < r) (hq : 0 < q)
    (Z : WholeLineRealL2) (x : ℝ) :
    weightedMovingHeatEta eta c r
        (weightedMovingHeatEta eta c q (Z : ℝ → ℝ)) x =
      weightedMovingHeatEta eta c (r + q) (Z : ℝ → ℝ) x := by
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
  have hkernelComp :
      (∫ z : ℝ, ∫ y : ℝ, J (y, z)) =
        ∫ z : ℝ,
          weightedMovingHeatMarkovKernel eta c (r + q) x z * Z z := by
    apply integral_congr_ae
    filter_upwards with z
    dsimp [J]
    rw [integral_mul_const]
    rw [weightedMovingHeatMarkovKernel_convolution_add hr hq]
  rw [hkernelComp]
  have hgrowthComp : weightedMovingHeatGrowth eta c r *
      (weightedMovingHeatGrowth eta c q *
        ∫ z : ℝ,
          weightedMovingHeatMarkovKernel eta c (r + q) x z * Z z) =
      weightedMovingHeatGrowth eta c (r + q) *
        ∫ z : ℝ,
          weightedMovingHeatMarkovKernel eta c (r + q) x z * Z z := by
    unfold weightedMovingHeatGrowth
    rw [← mul_assoc, ← Real.exp_add]
    congr 1
    ring_nf
  exact hgrowthComp

/-- The concrete scalar gradient is the integral operator associated with
the weighted gradient kernel. -/
theorem weightedMovingHeatGradientEta_eq_kernel_integral
    (eta c t : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    weightedMovingHeatGradientEta eta c t f x =
      ∫ y : ℝ, weightedMovingHeatGradientKernel eta c t x y * f y := by
  unfold weightedMovingHeatGradientKernel weightedMovingHeatGradientEta
  rw [show (fun y : ℝ => weightedMovingHeatGrowth eta c t *
      deriv (fun z : ℝ => heatKernel t z)
        (x + (c - 2 * eta) * t - y) * f y) =
      fun y => weightedMovingHeatGrowth eta c t *
        (deriv (fun z : ℝ => heatKernel t z)
          (x + (c - 2 * eta) * t - y) * f y) by
    funext y
    ring]
  rw [integral_const_mul]

/-- Pointwise gradient/semigroup composition for an `L²` datum. -/
theorem weightedMovingHeatGradientEta_comp_l2_data
    {eta c r q : ℝ} (hr : 0 < r) (hq : 0 < q)
    (Z : WholeLineRealL2) (x : ℝ) :
    weightedMovingHeatGradientEta eta c r
        (weightedMovingHeatEta eta c q (Z : ℝ → ℝ)) x =
      weightedMovingHeatGradientEta eta c (r + q)
        (Z : ℝ → ℝ) x := by
  rw [weightedMovingHeatGradientEta_eq_kernel_integral,
    weightedMovingHeatGradientEta_eq_kernel_integral]
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
  have hkernelComp :
      weightedMovingHeatGrowth eta c q *
          (∫ z : ℝ, ∫ y : ℝ, J (y, z)) =
        ∫ z : ℝ,
          weightedMovingHeatGradientKernel eta c (r + q) x z * Z z := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with z
    dsimp [J]
    rw [integral_mul_const, ← mul_assoc]
    rw [weightedMovingHeatGradientKernel_convolution_add hr hq]
  exact hkernelComp

/-- Positive weighted heat time maps `L²` data to bounded scalar
representatives. -/
theorem weightedMovingHeatEta_l2_data_bounded
    {eta c t : ℝ} (ht : 0 < t) (Z : WholeLineRealL2) :
    ∃ C : ℝ, ∀ x,
      |weightedMovingHeatEta eta c t (Z : ℝ → ℝ) x| ≤ C := by
  let C : ℝ := weightedMovingHeatGrowth eta c t *
    heatKernelLpNormClosedForm t 2 *
      (∫ y : ℝ, ‖(Z : ℝ → ℝ) y‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
  refine ⟨C, fun x => ?_⟩
  have hZmem : MemLp (Z : ℝ → ℝ) (ENNReal.ofReal 2) volume := by
    simpa using (Lp.memLp Z)
  have hheat := heatSemigroup_Lp_Linfty_smoothing_abs
    (f := (Z : ℝ → ℝ)) ht Real.HolderConjugate.two_two
      (x + (c - 2 * eta) * t) hZmem
  unfold weightedMovingHeatEta weightedMovingHeatMarkovKernel
  rw [abs_mul, abs_of_pos
    (show 0 < weightedMovingHeatGrowth eta c t by
      exact Real.exp_pos _)]
  change weightedMovingHeatGrowth eta c t *
      |heatSemigroup t (Z : ℝ → ℝ)
        (x + (c - 2 * eta) * t)| ≤ C
  simpa only [C, mul_assoc] using
    (mul_le_mul_of_nonneg_left hheat
      (show 0 ≤ weightedMovingHeatGrowth eta c t by
        exact Real.exp_nonneg _))

/-- Every positive weighted heat slice of an `L²` datum is classically
spatially differentiable, with derivative given by the concrete gradient
kernel.  The proof regularizes for half the heat time, so it assumes no
pointwise bound on the original datum. -/
theorem weightedMovingHeatEta_spatial_hasDerivAt_l2_data
    {eta c t x : ℝ} (ht : 0 < t) (Z : WholeLineRealL2) :
    HasDerivAt (weightedMovingHeatEta eta c t (Z : ℝ → ℝ))
      (weightedMovingHeatGradientEta eta c t (Z : ℝ → ℝ) x) x := by
  let q : ℝ := t / 2
  have hq : 0 < q := half_pos ht
  obtain ⟨C, hC⟩ := weightedMovingHeatEta_l2_data_bounded
    (eta := eta) (c := c) hq Z
  have hmeas := (weightedMovingHeatEta_l2_data
    (eta := eta) (c := c) hq Z).1
  have houter := weightedMovingHeatEta_spatial_hasDerivAt_of_bounded
    (eta := eta) (c := c) (t := q) (x := x) hq hmeas hC
  convert houter using 1
  · funext y
    rw [weightedMovingHeatEta_comp_l2_data hq hq Z y]
    congr 3
    dsimp [q]
    ring
  · rw [weightedMovingHeatGradientEta_comp_l2_data hq hq Z x]
    congr 3
    dsimp [q]
    ring

/-! ## Local scalar domination from the unweighted forcing -/

/-- Value-level companion to the gradient conjugation estimate. -/
theorem weightedMovingHeatEta_abs_le_of_exp_raw_bound
    {eta c t K : ℝ} (ht : 0 < t) (hK : 0 ≤ K)
    {raw : ℝ → ℝ}
    (hraw_meas : AEStronglyMeasurable raw volume)
    (hraw_bound : ∀ y, |raw y| ≤ K) (x : ℝ) :
    |weightedMovingHeatEta eta c t
        (fun y => Real.exp (eta * y) * raw y) x| ≤
      Real.exp t * Real.exp (eta * x) * K := by
  have hconj := exp_mul_movingFrameHeatOp_eq_weightedMovingHeatEta
    (eta := eta) (c := c) ht raw x
  have hV := wholeLineCauchyHeatOp_abs_bound_of_nonneg_time
    hraw_bound hK hraw_meas ht.le (x + c * t)
  let S : ℝ := weightedMovingHeatEta eta c t
    (fun y => Real.exp (eta * y) * raw y) x
  let V : ℝ := paper5MovingFrameHeatOp c t raw x
  have hexp_cancel : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]
    simp
  have hS : S = Real.exp t * (Real.exp (eta * x) * V) := by
    calc
      S = 1 * S := by ring
      _ = Real.exp t * (Real.exp (-t) * S) := by
        rw [← mul_assoc, hexp_cancel]
      _ = Real.exp t * (Real.exp (eta * x) * V) := by
        rw [hconj]
  rw [show weightedMovingHeatEta eta c t
      (fun y => Real.exp (eta * y) * raw y) x = S from rfl, hS,
    abs_mul, abs_mul, abs_of_pos (Real.exp_pos t),
    abs_of_pos (Real.exp_pos (eta * x))]
  have hV' : |V| ≤ K := by
    simpa only [V, paper5MovingFrameHeatOp] using hV
  calc
    Real.exp t * (Real.exp (eta * x) * |V|) ≤
        Real.exp t * (Real.exp (eta * x) * K) := by gcongr
    _ = Real.exp t * Real.exp (eta * x) * K := by ring

/-- The exact-weight heat gradient can be estimated from a uniform bound on
the *unweighted* forcing.  The exponential conjugation keeps the target
weight exact, while the unweighted Gaussian derivative contributes only the
integrable half-order endpoint singularity. -/
theorem weightedMovingHeatGradientEta_abs_le_of_exp_raw_bound_l2
    {eta c t K : ℝ} (ht : 0 < t) (hK : 0 ≤ K)
    {raw : ℝ → ℝ}
    (hraw_meas : AEStronglyMeasurable raw volume)
    (hraw_bound : ∀ y, |raw y| ≤ K)
    (F : WholeLineRealL2)
    (hFrep : ((F : ℝ → ℝ) =ᵐ[volume]
      fun y => Real.exp (eta * y) * raw y))
    (x : ℝ) :
    |weightedMovingHeatGradientEta eta c t
        (fun y => Real.exp (eta * y) * raw y) x| ≤
      Real.exp t * Real.exp (eta * x) *
        (((2 / Real.sqrt (4 * Real.pi)) * K) *
            t ^ (-(1 / 2 : ℝ)) + |eta| * K) := by
  have hgrowth_ne : weightedMovingHeatGrowth eta c t ≠ 0 := by
    unfold weightedMovingHeatGrowth
    exact Real.exp_ne_zero _
  have hgrad_kernel :=
    weightedMovingHeatGradientKernel_row_mul_l2_integrable
      (eta := eta) (c := c) ht x F
  have hgrad_int : Integrable (fun y : ℝ =>
      deriv (fun z : ℝ => heatKernel t z)
          (x + (c - 2 * eta) * t - y) *
        (Real.exp (eta * y) * raw y)) volume := by
    have hscaled := hgrad_kernel.const_mul
      (weightedMovingHeatGrowth eta c t)⁻¹
    refine hscaled.congr ?_
    filter_upwards [hFrep] with y hy
    rw [hy]
    unfold weightedMovingHeatGradientKernel
    field_simp [hgrowth_ne]
  have hheat_int : Integrable (fun y : ℝ =>
      weightedMovingHeatMarkovKernel eta c t x y *
        (Real.exp (eta * y) * raw y)) volume := by
    refine (weightedMovingHeatMarkovKernel_mul_integrable
      (eta := eta) (c := c) ht x F).congr ?_
    filter_upwards [hFrep] with y hy
    rw [hy]
  have hgrad_conj :=
    exp_mul_movingFrameHeatGradOp_eq_weightedMovingHeatGradientEta_sub
      (eta := eta) (c := c) ht raw x hgrad_int hheat_int
  have hheat_conj :=
    exp_mul_movingFrameHeatOp_eq_weightedMovingHeatEta
      (eta := eta) (c := c) ht raw x
  let G : ℝ := weightedMovingHeatGradientEta eta c t
    (fun y => Real.exp (eta * y) * raw y) x
  let S : ℝ := weightedMovingHeatEta eta c t
    (fun y => Real.exp (eta * y) * raw y) x
  let D : ℝ := paper5MovingFrameHeatGradOp c t raw x
  let V : ℝ := paper5MovingFrameHeatOp c t raw x
  have hexp_cancel : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]
    simp
  have hGsub : G - eta * S =
      Real.exp t * (Real.exp (eta * x) * D) := by
    calc
      G - eta * S = 1 * (G - eta * S) := by ring
      _ = Real.exp t * (Real.exp (-t) * (G - eta * S)) := by
        rw [← mul_assoc, hexp_cancel]
      _ = Real.exp t * (Real.exp (eta * x) * D) := by
        rw [hgrad_conj]
  have hS : S = Real.exp t * (Real.exp (eta * x) * V) := by
    calc
      S = 1 * S := by ring
      _ = Real.exp t * (Real.exp (-t) * S) := by
        rw [← mul_assoc, hexp_cancel]
      _ = Real.exp t * (Real.exp (eta * x) * V) := by
        rw [hheat_conj]
  have hG : G = Real.exp t * Real.exp (eta * x) * (D + eta * V) := by
    rw [show G = (G - eta * S) + eta * S by ring, hGsub, hS]
    ring
  have hD : |D| ≤ ((2 / Real.sqrt (4 * Real.pi)) * K) *
      t ^ (-(1 / 2 : ℝ)) := by
    simpa only [D, paper5MovingFrameHeatGradOp, Real.norm_eq_abs] using
      wholeLineCauchyHeatGradOp_norm_le_rpow ht hK hraw_bound
        (x + c * t)
  have hV : |V| ≤ K := by
    simpa only [V, paper5MovingFrameHeatOp] using
      wholeLineCauchyHeatOp_abs_bound_of_nonneg_time hraw_bound hK
        hraw_meas ht.le (x + c * t)
  rw [show weightedMovingHeatGradientEta eta c t
      (fun y => Real.exp (eta * y) * raw y) x = G from rfl, hG,
    abs_mul, abs_mul, abs_of_pos (Real.exp_pos t),
    abs_of_pos (Real.exp_pos (eta * x))]
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
  calc
    |D + eta * V| ≤ |D| + |eta * V| := abs_add_le _ _
    _ = |D| + |eta| * |V| := by rw [abs_mul]
    _ ≤ ((2 / Real.sqrt (4 * Real.pi)) * K) *
          t ^ (-(1 / 2 : ℝ)) + |eta| * K := by
      gcongr

/-- Joint measurability of the scalar weighted heat-value history.  This
local copy is kept in the gradient construction so that neither scalar
history measurability nor a choice of `Lp` representatives is exposed to the
eventual capstone. -/
theorem weightedMovingHeatEta_history_stronglyMeasurable_gradientNatural
    {eta c tau : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) :
    StronglyMeasurable
      (fun z : ℝ × ℝ =>
        weightedMovingHeatEta eta c (tau - z.1) (f z.1) z.2) := by
  let raw : (ℝ × ℝ) × ℝ → ℝ := fun z =>
    weightedMovingHeatMarkovKernel eta c (tau - z.1.1) z.1.2 z.2 *
      f z.1.1 z.2
  have hraw : StronglyMeasurable raw := by
    apply Measurable.stronglyMeasurable
    have hfraw : Measurable (fun z : (ℝ × ℝ) × ℝ =>
        f z.1.1 z.2) :=
      hf.comp (measurable_fst.fst.prodMk measurable_snd)
    dsimp only [raw, weightedMovingHeatMarkovKernel, heatKernel]
    fun_prop
  have hint : StronglyMeasurable
      (fun z : ℝ × ℝ => ∫ y : ℝ, raw (z, y)) :=
    hraw.integral_prod_right'
  have hgrowth : Continuous (fun z : ℝ × ℝ =>
      weightedMovingHeatGrowth eta c (tau - z.1)) := by
    dsimp only [weightedMovingHeatGrowth]
    fun_prop
  have hprod := hgrowth.stronglyMeasurable.mul hint
  simpa only [raw, weightedMovingHeatEta] using hprod

/-- Differentiate a scalar weighted heat history whose forcing slices are
represented in exact-weight `L²`.  The spatial derivative is supplied by the
positive-time `L²` heat smoothing theorem, rather than by a pointwise bound
or a spatial derivative of the forcing. -/
theorem weightedMovingHeatValueHistory_hasDerivAt_of_dominated_l2
    {eta c a r x rho : ℝ} {f : ℝ → ℝ → ℝ}
    {F : ℝ → WholeLineRealL2} {bound : ℝ → ℝ}
    (har : a < r) (hrho : 0 < rho)
    (hFrep : ∀ q ∈ Set.Ioc a r,
      (((F q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] f q))
    (hvalue_meas : ∀ z ∈ Metric.ball x rho,
      AEStronglyMeasurable
        (fun q : ℝ => weightedMovingHeatEta eta c (r - q) (f q) z)
        (volume.restrict (Set.uIoc a r)))
    (hvalue_int : IntervalIntegrable
      (fun q : ℝ => weightedMovingHeatEta eta c (r - q) (f q) x)
      volume a r)
    (hgrad_meas : AEStronglyMeasurable
      (fun q : ℝ => weightedMovingHeatGradientEta eta c (r - q) (f q) x)
      (volume.restrict (Set.uIoc a r)))
    (hbound_int : IntervalIntegrable bound volume a r)
    (hbound : ∀ᵐ q : ℝ ∂volume, q ∈ Set.uIoc a r →
      ∀ z ∈ Metric.ball x rho,
        ‖weightedMovingHeatGradientEta eta c (r - q) (f q) z‖ ≤
          bound q) :
    HasDerivAt (weightedMovingHeatValueHistory eta c a r f)
      (weightedMovingHeatGradientHistory eta c a r f x) x := by
  have hne : ∀ᵐ q : ℝ ∂volume, q ≠ r := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  unfold weightedMovingHeatValueHistory weightedMovingHeatGradientHistory
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := a) (b := r)
    (F := fun z q => weightedMovingHeatEta eta c (r - q) (f q) z)
    (F' := fun z q => weightedMovingHeatGradientEta eta c (r - q) (f q) z)
    (x₀ := x) (s := Metric.ball x rho) (bound := bound)
    (Metric.ball_mem_nhds x hrho)
    ?hF_meas hvalue_int hgrad_meas hbound hbound_int ?h_diff).2
  · filter_upwards [Metric.ball_mem_nhds x hrho] with z hz
    exact hvalue_meas z hz
  · filter_upwards [hne] with q hqr hqI z _hz
    rw [Set.uIoc_of_le har.le, Set.mem_Ioc] at hqI
    have hq_lt : q < r := lt_of_le_of_ne hqI.2 hqr
    have hbase := weightedMovingHeatEta_spatial_hasDerivAt_l2_data
      (eta := eta) (c := c) (x := z) (sub_pos.mpr hq_lt) (F q)
    convert hbase using 1
    · funext y
      exact (weightedMovingHeatEta_congr_ae (hFrep q hqI) y).symm
    · exact
        (weightedMovingHeatGradientEta_congr_ae (hFrep q hqI) z).symm

/-- On a positive restart window, an exact-weight `L²` realization and a
uniform bound for the corresponding unweighted forcing automatically supply
the dominated spatial derivative of the scalar Duhamel history. -/
theorem weightedMovingHeatValueHistory_hasDerivAt_of_exp_raw_window_l2
    {eta c a r x K : ℝ} (har : a < r) (hK : 0 ≤ K)
    {f raw : ℝ → ℝ → ℝ} {F : ℝ → WholeLineRealL2}
    (hFrep : ∀ q ∈ Set.Ioc a r,
      (((F q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] f q))
    (hjoint : Measurable (Function.uncurry f))
    (hraw_meas : ∀ q ∈ Set.Ioc a r,
      AEStronglyMeasurable (raw q) volume)
    (hraw_bound : ∀ q ∈ Set.Ioc a r, ∀ y, |raw q y| ≤ K)
    (hfactor : ∀ q ∈ Set.Ioc a r, ∀ y,
      f q y = Real.exp (eta * y) * raw q y) :
    HasDerivAt (weightedMovingHeatValueHistory eta c a r f)
      (weightedMovingHeatGradientHistory eta c a r f x) x := by
  let H : ℝ := r - a
  let E : ℝ := Real.exp H * Real.exp (|eta| * (|x| + 1))
  let A : ℝ := E * ((2 / Real.sqrt (4 * Real.pi)) * K)
  let B : ℝ := E * (|eta| * K)
  let bound : ℝ → ℝ := fun q =>
    A * (r - q) ^ (-(1 / 2 : ℝ)) + B
  have hvalueJoint :=
    weightedMovingHeatEta_history_stronglyMeasurable_gradientNatural
      (eta := eta) (c := c) (tau := r) hjoint
  have hgradJoint :=
    weightedMovingHeatGradientEta_history_stronglyMeasurable_of_joint_measurable
      (eta := eta) (c := c) (tau := r) hjoint
  have hvalue_meas_global : ∀ z : ℝ, AEStronglyMeasurable
      (fun q : ℝ => weightedMovingHeatEta eta c (r - q) (f q) z)
      volume := by
    intro z
    exact (hvalueJoint.comp_measurable
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hgrad_meas_global : ∀ z : ℝ, AEStronglyMeasurable
      (fun q : ℝ =>
        weightedMovingHeatGradientEta eta c (r - q) (f q) z)
      volume := by
    intro z
    exact (hgradJoint.comp_measurable
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hvalue_int : IntervalIntegrable
      (fun q : ℝ => weightedMovingHeatEta eta c (r - q) (f q) x)
      volume a r := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le har.le]
    let C : ℝ := Real.exp H * Real.exp (eta * x) * K
    have hC : 0 ≤ C := by dsimp [C]; positivity
    apply IntegrableOn.of_bound measure_Icc_lt_top
      ((hvalue_meas_global x).mono_measure Measure.restrict_le_self) C
    have hnea : ∀ᵐ q : ℝ ∂volume.restrict (Set.Icc a r), q ≠ a :=
      (Measure.ae_ne volume a).filter_mono ae_restrict_le
    have hner : ∀ᵐ q : ℝ ∂volume.restrict (Set.Icc a r), q ≠ r :=
      (Measure.ae_ne volume r).filter_mono ae_restrict_le
    filter_upwards [ae_restrict_mem measurableSet_Icc, hnea, hner]
      with q hq hqa hqr
    have hqoc : q ∈ Set.Ioc a r :=
      ⟨lt_of_le_of_ne hq.1 (Ne.symm hqa), hq.2⟩
    have hlag : 0 < r - q := sub_pos.mpr (lt_of_le_of_ne hq.2 hqr)
    have hlagH : r - q ≤ H := by dsimp only [H]; linarith [hq.1]
    have heq : weightedMovingHeatEta eta c (r - q) (f q) x =
        weightedMovingHeatEta eta c (r - q)
          (fun y => Real.exp (eta * y) * raw q y) x :=
      weightedMovingHeatEta_congr_ae
        (Eventually.of_forall (hfactor q hqoc)) x
    rw [Real.norm_eq_abs, heq]
    calc
      |weightedMovingHeatEta eta c (r - q)
          (fun y => Real.exp (eta * y) * raw q y) x| ≤
          Real.exp (r - q) * Real.exp (eta * x) * K :=
        weightedMovingHeatEta_abs_le_of_exp_raw_bound hlag hK
          (hraw_meas q hqoc) (hraw_bound q hqoc) x
      _ ≤ Real.exp H * Real.exp (eta * x) * K := by
        gcongr
      _ = C := rfl
  have hbound_int : IntervalIntegrable bound volume a r := by
    have hs : IntervalIntegrable
        (fun q : ℝ => A * (r - q) ^ (-(1 / 2 : ℝ)))
        volume a r :=
      (intervalIntegrable_sub_rpow_neg_half_between a r).const_mul A
    have hc : IntervalIntegrable (fun _q : ℝ => B) volume a r :=
      intervalIntegrable_const
    simpa only [bound] using hs.add hc
  have hbound : ∀ᵐ q : ℝ ∂volume, q ∈ Set.uIoc a r →
      ∀ z ∈ Metric.ball x (1 : ℝ),
        ‖weightedMovingHeatGradientEta eta c (r - q) (f q) z‖ ≤
          bound q := by
    filter_upwards [Measure.ae_ne volume r] with q hqr hqI z hz
    rw [Set.uIoc_of_le har.le, Set.mem_Ioc] at hqI
    have hq_lt : q < r := lt_of_le_of_ne hqI.2 hqr
    have hlag : 0 < r - q := sub_pos.mpr hq_lt
    have hlagH : r - q ≤ H := by dsimp only [H]; linarith [hqI.1]
    have hFexp : (((F q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        fun y => Real.exp (eta * y) * raw q y) :=
      (hFrep q hqI).trans (Eventually.of_forall (hfactor q hqI))
    have hpoint :=
      weightedMovingHeatGradientEta_abs_le_of_exp_raw_bound_l2
        (eta := eta) (c := c) hlag hK (hraw_meas q hqI)
          (hraw_bound q hqI) (F q) hFexp z
    have hzx : |z - x| < 1 := by
      simpa only [Metric.mem_ball, Real.dist_eq] using hz
    have hzabs : |z| ≤ |x| + 1 := by
      calc
        |z| = |(z - x) + x| := by ring_nf
        _ ≤ |z - x| + |x| := abs_add_le _ _
        _ ≤ |x| + 1 := by linarith
    have hetaz : eta * z ≤ |eta| * (|x| + 1) := by
      calc
        eta * z ≤ |eta * z| := le_abs_self _
        _ = |eta| * |z| := abs_mul _ _
        _ ≤ |eta| * (|x| + 1) := by gcongr
    have hexpt : Real.exp (r - q) ≤ Real.exp H :=
      Real.exp_le_exp.mpr hlagH
    have hexpz : Real.exp (eta * z) ≤
        Real.exp (|eta| * (|x| + 1)) := Real.exp_le_exp.mpr hetaz
    have hinner : 0 ≤ ((2 / Real.sqrt (4 * Real.pi)) * K) *
          (r - q) ^ (-(1 / 2 : ℝ)) + |eta| * K := by
      positivity
    rw [Real.norm_eq_abs]
    calc
      |weightedMovingHeatGradientEta eta c (r - q) (f q) z| =
          |weightedMovingHeatGradientEta eta c (r - q)
            (fun y => Real.exp (eta * y) * raw q y) z| := by
        rw [weightedMovingHeatGradientEta_congr_ae
          (Eventually.of_forall (hfactor q hqI)) z]
      _ ≤ Real.exp (r - q) * Real.exp (eta * z) *
          (((2 / Real.sqrt (4 * Real.pi)) * K) *
            (r - q) ^ (-(1 / 2 : ℝ)) + |eta| * K) := hpoint
      _ ≤ Real.exp H * Real.exp (|eta| * (|x| + 1)) *
          (((2 / Real.sqrt (4 * Real.pi)) * K) *
            (r - q) ^ (-(1 / 2 : ℝ)) + |eta| * K) := by
        gcongr
      _ = bound q := by
        dsimp only [bound, A, B, E]
        ring
  apply weightedMovingHeatValueHistory_hasDerivAt_of_dominated_l2
    (eta := eta) (c := c) (F := F) har (by norm_num : (0 : ℝ) < 1)
      hFrep
  · intro z hz
    exact (hvalue_meas_global z).mono_measure Measure.restrict_le_self
  · exact hvalue_int
  · exact (hgrad_meas_global x).mono_measure Measure.restrict_le_self
  · exact hbound_int
  · exact hbound

/-! ## Exact `L²` restart identification -/

/-- Differentiate an actual scalar restart when its initial weighted slice
is represented only in `L²`.  Positive heat time supplies the classical
derivative of the homogeneous leg. -/
theorem weightedMovingHeat_fullGenerator_spatial_identity_l2_data
    {eta c a r x : ℝ} {Wr Wa Wrx : ℝ → ℝ}
    {f : ℝ → ℝ → ℝ} (X₀ : WholeLineRealL2)
    (har : a < r)
    (hX₀rep : ((X₀ : ℝ → ℝ) =ᵐ[volume] Wa))
    (hrestart : ∀ z,
      Wr z = weightedMovingHeatEta eta c (r - a) Wa z +
        weightedMovingHeatValueHistory eta c a r f z)
    (hWr_deriv : HasDerivAt Wr (Wrx x) x)
    (hhistory : HasDerivAt (weightedMovingHeatValueHistory eta c a r f)
      (weightedMovingHeatGradientHistory eta c a r f x) x) :
    Wrx x = weightedMovingHeatGradientEta eta c (r - a) Wa x +
      weightedMovingHeatGradientHistory eta c a r f x := by
  have hhom₀ := weightedMovingHeatEta_spatial_hasDerivAt_l2_data
    (eta := eta) (c := c) (x := x) (sub_pos.mpr har) X₀
  have hhom : HasDerivAt (weightedMovingHeatEta eta c (r - a) Wa)
      (weightedMovingHeatGradientEta eta c (r - a) Wa x) x := by
    convert hhom₀ using 1
    · funext z
      exact (weightedMovingHeatEta_congr_ae hX₀rep z).symm
    · exact (weightedMovingHeatGradientEta_congr_ae hX₀rep x).symm
  have hright := hhom.add hhistory
  have hfun : Wr = fun z =>
      weightedMovingHeatEta eta c (r - a) Wa z +
        weightedMovingHeatValueHistory eta c a r f z := by
    funext z
    exact hrestart z
  have hrightW : HasDerivAt Wr
      (weightedMovingHeatGradientEta eta c (r - a) Wa x +
        weightedMovingHeatGradientHistory eta c a r f x) x := by
    rw [hfun]
    exact hright
  exact hWr_deriv.unique hrightW

/-- A pointwise differentiated restart identifies the concrete scalar
derivative with the full Hilbert heat-gradient candidate. -/
theorem weightedMovingHeatFullGradientCandidate_coe_ae_of_pointwise
    {eta c a r : ℝ} (har : a < r)
    {x₀ xr : ℝ → ℝ} {f : ℝ → ℝ → ℝ}
    {X₀ : WholeLineRealL2} {F : ℝ → WholeLineRealL2}
    (hX₀ : (((X₀ : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] x₀))
    (hFrep : ∀ q ∈ Set.Ioc a r,
      (((F q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] f q))
    (hDint : IntervalIntegrable
      (fun q => weightedMovingHeatL2Gradient eta c (r - q) (F q))
      volume a r)
    (hlocal : ∀ A : Set ℝ, MeasurableSet A →
      (volume : Measure ℝ) A < ⊤ →
      Integrable
        (fun z : ℝ × ℝ => A.indicator
          (weightedMovingHeatGradientEta eta c (r - z.1) (f z.1)) z.2)
        ((volume.restrict (Set.Ioc a r)).prod volume))
    (hpoint : ∀ᵐ x ∂volume,
      xr x = weightedMovingHeatGradientEta eta c (r - a) x₀ x +
        ∫ q in a..r,
          weightedMovingHeatGradientEta eta c (r - q) (f q) x) :
    (((weightedMovingHeatFullGradientCandidate eta c a X₀ F r :
        WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] xr) := by
  have hlag : 0 < r - a := sub_pos.mpr har
  have hhom :
      (((weightedMovingHeatL2Gradient eta c (r - a) X₀ :
          WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        weightedMovingHeatGradientEta eta c (r - a) x₀) := by
    rw [weightedMovingHeatL2Gradient_of_pos hlag]
    exact (weightedMovingHeatGradientL2CLM_coe_ae hlag X₀).trans
      (Eventually.of_forall fun x =>
        weightedMovingHeatGradientEta_congr_ae hX₀ x)
  have hduh := weightedMovingHeatL2Gradient_intervalIntegral_coe_ae
    har.le hFrep hDint hlocal
  unfold weightedMovingHeatFullGradientCandidate
  filter_upwards [Lp.coeFn_add
      (weightedMovingHeatL2Gradient eta c (r - a) X₀)
      (∫ q in a..r,
        weightedMovingHeatL2Gradient eta c (r - q) (F q)),
    hhom, hduh, hpoint] with x hadd hhomx hduhx hpointx
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hhomx, hduhx, ← hpointx]

/-! ## Measurable exact-weight `L²` trajectories from local time moduli -/

private def naturalL2SpatialCutoff
    (n : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (Set.Icc (-(n : ℝ)) (n : ℝ)).indicator f x

private theorem naturalL2SpatialCutoff_aestronglyMeasurable
    (n : ℕ) {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (naturalL2SpatialCutoff n f) volume := by
  exact hf.indicator measurableSet_Icc

private theorem naturalL2SpatialCutoff_sq_integrable
    (n : ℕ) {f : ℝ → ℝ}
    (hf2 : Integrable (fun x : ℝ => f x ^ 2) volume) :
    Integrable (fun x : ℝ => naturalL2SpatialCutoff n f x ^ 2) volume := by
  have hi := hf2.indicator (measurableSet_Icc :
    MeasurableSet (Set.Icc (-(n : ℝ)) (n : ℝ)))
  refine hi.congr (Eventually.of_forall fun x => ?_)
  simp only [naturalL2SpatialCutoff, Set.indicator_apply]
  split_ifs <;> simp

private theorem naturalL2SpatialCutoff_sub_sq_integral_le
    (n : ℕ) {f g : ℝ → ℝ} {B : ℝ}
    (hB : 0 ≤ B)
    (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume)
    (hpoint : ∀ x ∈ Set.Icc (-(n : ℝ)) (n : ℝ),
      |f x - g x| ≤ B) :
    (∫ x : ℝ, (naturalL2SpatialCutoff n f x -
        naturalL2SpatialCutoff n g x) ^ 2) ≤
      (2 * n : ℝ) * B ^ 2 := by
  have heq :
      (∫ x : ℝ, (naturalL2SpatialCutoff n f x -
          naturalL2SpatialCutoff n g x) ^ 2) =
        ∫ x in Set.Icc (-(n : ℝ)) (n : ℝ),
          (f x - g x) ^ 2 := by
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simp only [naturalL2SpatialCutoff, Set.indicator_apply]
      split_ifs <;> simp
  rw [heq]
  have hfgMeas : AEStronglyMeasurable
      (fun x : ℝ => (f x - g x) ^ 2) volume :=
    (hf.sub hg).pow 2
  have hfun : IntegrableOn (fun x : ℝ => (f x - g x) ^ 2)
      (Set.Icc (-(n : ℝ)) (n : ℝ)) volume := by
    refine Measure.integrableOn_of_bounded
      (s := Set.Icc (-(n : ℝ)) (n : ℝ)) (f := fun x : ℝ =>
        (f x - g x) ^ 2) (M := B ^ 2) ?_ hfgMeas ?_
    · simp [Real.volume_Icc]
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      rw [Real.norm_eq_abs, abs_sq, ← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) hB).2 (hpoint x hx)
  have hconst : IntegrableOn (fun _x : ℝ => B ^ 2)
      (Set.Icc (-(n : ℝ)) (n : ℝ)) volume :=
    integrableOn_const (by simp [Real.volume_Icc])
  calc
    (∫ x in Set.Icc (-(n : ℝ)) (n : ℝ), (f x - g x) ^ 2) ≤
        ∫ _x in Set.Icc (-(n : ℝ)) (n : ℝ), B ^ 2 := by
      apply setIntegral_mono_on hfun hconst measurableSet_Icc
      intro x hx
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) hB).2 (hpoint x hx)
    _ = (2 * n : ℝ) * B ^ 2 := by
      rw [setIntegral_const, Measure.real_def, Real.volume_Icc]
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [ENNReal.toReal_ofReal (by linarith :
        (0 : ℝ) ≤ (n : ℝ) - -(n : ℝ))]
      simp only [smul_eq_mul]
      ring

private theorem wholeLineRealL2OfSqIntegrable_norm_sub_sq_natural
    (f g : ℝ → ℝ)
    (hf_meas : AEStronglyMeasurable f volume)
    (hg_meas : AEStronglyMeasurable g volume)
    (hf2 : Integrable (fun x : ℝ => f x ^ 2) volume)
    (hg2 : Integrable (fun x : ℝ => g x ^ 2) volume) :
    ‖wholeLineRealL2OfSqIntegrable f hf_meas hf2 -
        wholeLineRealL2OfSqIntegrable g hg_meas hg2‖ ^ 2 =
      ∫ x : ℝ, (f x - g x) ^ 2 := by
  let Zf := wholeLineRealL2OfSqIntegrable f hf_meas hf2
  let Zg := wholeLineRealL2OfSqIntegrable g hg_meas hg2
  have hrep : (((Zf - Zg : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      fun x => f x - g x) := by
    filter_upwards [Lp.coeFn_sub Zf Zg,
      wholeLineRealL2OfSqIntegrable_coe_ae f hf_meas hf2,
      wholeLineRealL2OfSqIntegrable_coe_ae g hg_meas hg2]
      with x hsub hf hg
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hf, hg]
  have hinner := wholeLineIntegral_mul_eq_inner_of_aeEq
    (Zf - Zg) (Zf - Zg) hrep hrep
  rw [real_inner_self_eq_norm_sq] at hinner
  simpa only [Zf, Zg, pow_two] using hinner.symm

/-- A family with square-integrable slices and a uniform positive time
modulus on every compact spatial window has a strongly measurable canonical
`L²` realization.  This is a pointwise-cutoff construction; it assumes no
stronger exponential weight and no time continuity in the full `L²` norm. -/
theorem wholeLineRealL2Section_aestronglyMeasurable_of_local_holder
    {g : ℝ → ℝ → ℝ} {alpha : ℝ}
    (halpha : 0 < alpha)
    (hg_meas : ∀ s, AEStronglyMeasurable (g s) volume)
    (hg2 : ∀ s, Integrable (fun x : ℝ => g s x ^ 2) volume)
    (hlocal : ∀ n : ℕ, ∃ H : ℝ, 0 ≤ H ∧
      ∀ s t : ℝ, |s - t| ≤ 1 →
        ∀ x ∈ Set.Icc (-(n : ℝ)) (n : ℝ),
          |g s x - g t x| ≤ H * |s - t| ^ alpha) :
    AEStronglyMeasurable
      (wholeLineRealL2Section g hg_meas hg2) volume := by
  let gc : ℕ → ℝ → ℝ → ℝ := fun n s =>
    naturalL2SpatialCutoff n (g s)
  have hgc_meas : ∀ n s, AEStronglyMeasurable (gc n s) volume :=
    fun n s => naturalL2SpatialCutoff_aestronglyMeasurable n (hg_meas s)
  have hgc2 : ∀ n s, Integrable (fun x : ℝ => gc n s x ^ 2) volume :=
    fun n s => naturalL2SpatialCutoff_sq_integrable n (hg2 s)
  have hcont : ∀ n, Continuous
      (wholeLineRealL2Section (gc n) (hgc_meas n) (hgc2 n)) := by
    intro n
    obtain ⟨H, hH, hmod⟩ := hlocal n
    apply wholeLineRealL2Section_continuous_of_integral_sub_sq_tendsto_zero
    intro t
    apply squeeze_zero'
    · exact Eventually.of_forall fun s => integral_nonneg fun _ => sq_nonneg _
    · filter_upwards [Metric.ball_mem_nhds t (by norm_num : (0 : ℝ) < 1)]
        with s hs
      have hst : |s - t| ≤ 1 := by
        rw [Metric.mem_ball, Real.dist_eq] at hs
        exact hs.le
      exact naturalL2SpatialCutoff_sub_sq_integral_le
        (B := H * |s - t| ^ alpha) n
        (mul_nonneg hH (Real.rpow_nonneg (abs_nonneg _) _))
        (hg_meas s) (hg_meas t) (fun x hx => hmod s t hst x hx)
    · have hbase : Tendsto (fun s : ℝ => |s - t| ^ alpha)
          (nhds t) (nhds 0) := by
        have hc : ContinuousAt (fun s : ℝ => |s - t| ^ alpha) t :=
          (continuousAt_id.sub continuousAt_const).abs.rpow_const
            (Or.inr halpha.le)
        simpa only [sub_self, abs_zero, Real.zero_rpow halpha.ne'] using hc.tendsto
      have hupper : Tendsto
          (fun s : ℝ => (2 * n : ℝ) *
            (H * |s - t| ^ alpha) ^ 2) (nhds t) (nhds 0) := by
        simpa only [mul_zero, zero_pow (by norm_num : 2 ≠ 0)] using
          (tendsto_const_nhds.mul
            ((tendsto_const_nhds.mul hbase).pow 2))
      exact hupper
  have hcut_tendsto : ∀ s, Tendsto
      (fun n => wholeLineRealL2Section (gc n) (hgc_meas n) (hgc2 n) s)
      atTop (nhds (wholeLineRealL2Section g hg_meas hg2 s)) := by
    intro s
    apply tendsto_iff_norm_sub_tendsto_zero.2
    have hint : Tendsto (fun n => ∫ x : ℝ,
        (gc n s x - g s x) ^ 2) atTop (nhds 0) := by
      have hdom := tendsto_integral_of_dominated_convergence
        (F := fun n x => (gc n s x - g s x) ^ 2)
        (f := fun _x : ℝ => 0)
        (fun x : ℝ => g s x ^ 2)
        (fun n => ((hgc_meas n s).sub (hg_meas s)).pow 2)
        (hg2 s)
        (fun n => Eventually.of_forall fun x => by
          change |(gc n s x - g s x) ^ 2| ≤ g s x ^ 2
          rw [abs_sq]
          by_cases hx : x ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
          · simp [gc, naturalL2SpatialCutoff, hx, sq_nonneg]
          · simp [gc, naturalL2SpatialCutoff, hx])
        (Eventually.of_forall fun x => by
          rcases exists_nat_ge |x| with ⟨N, hN⟩
          apply tendsto_const_nhds.congr'
          filter_upwards [eventually_ge_atTop N] with n hn
          have hxabs : |x| ≤ (n : ℝ) := hN.trans (Nat.cast_le.mpr hn)
          have hx : x ∈ Set.Icc (-(n : ℝ)) (n : ℝ) :=
            ⟨by linarith [neg_abs_le x], (le_abs_self x).trans hxabs⟩
          simp [gc, naturalL2SpatialCutoff, hx])
      simpa only [integral_zero] using hdom
    have hsq : Tendsto (fun n =>
        ‖wholeLineRealL2Section (gc n) (hgc_meas n) (hgc2 n) s -
          wholeLineRealL2Section g hg_meas hg2 s‖ ^ 2)
        atTop (nhds 0) := by
      exact hint.congr' (Eventually.of_forall fun n =>
        (wholeLineRealL2OfSqIntegrable_norm_sub_sq_natural
          (gc n s) (g s) (hgc_meas n s) (hg_meas s)
          (hgc2 n s) (hg2 s)).symm)
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
    have hsqrt' : Tendsto (fun n => Real.sqrt
        (‖wholeLineRealL2Section (gc n) (hgc_meas n) (hgc2 n) s -
          wholeLineRealL2Section g hg_meas hg2 s‖ ^ 2))
        atTop (nhds 0) := by
      simpa only [Function.comp_apply, Real.sqrt_zero] using hsqrt
    exact hsqrt'.congr' (Eventually.of_forall fun n => by
      rw [Real.sqrt_sq (norm_nonneg _)])
  exact (stronglyMeasurable_of_tendsto atTop
    (fun n => (hcont n).stronglyMeasurable)
    (tendsto_pi_nhds.2 hcut_tendsto)).aestronglyMeasurable

/-- Clamp a locally Hölder family to a closed time window and realize all
of its exact `L²` slices by one strongly measurable Hilbert trajectory. -/
theorem exists_wholeLineRealL2_clamped_trajectory_of_local_holder
    {a b alpha C : ℝ} (hab : a ≤ b) (halpha : 0 < alpha)
    {f : ℝ → ℝ → ℝ}
    (hf_meas : ∀ q ∈ Set.Icc a b, AEStronglyMeasurable (f q) volume)
    (hf2 : ∀ q ∈ Set.Icc a b,
      Integrable (fun x : ℝ => f q x ^ 2) volume)
    (hf_le : ∀ q ∈ Set.Icc a b, (∫ x : ℝ, f q x ^ 2) ≤ C)
    (hlocal : ∀ n : ℕ, ∃ H : ℝ, 0 ≤ H ∧
      ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
        |s - t| ≤ 1 → ∀ x ∈ Set.Icc (-(n : ℝ)) (n : ℝ),
          |f s x - f t x| ≤ H * |s - t| ^ alpha) :
    ∃ F : ℝ → WholeLineRealL2,
      AEStronglyMeasurable F volume ∧
      ∀ q ∈ Set.Icc a b,
        (((F q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] f q) ∧
        ‖F q‖ ^ 2 ≤ C := by
  let proj : ℝ → ℝ := fun s => (Set.projIcc a b hab s).1
  let g : ℝ → ℝ → ℝ := fun s => f (proj s)
  have hproj_mem : ∀ s, proj s ∈ Set.Icc a b :=
    fun s => (Set.projIcc a b hab s).2
  have hg_meas : ∀ s, AEStronglyMeasurable (g s) volume :=
    fun s => hf_meas (proj s) (hproj_mem s)
  have hg2 : ∀ s, Integrable (fun x : ℝ => g s x ^ 2) volume :=
    fun s => hf2 (proj s) (hproj_mem s)
  have hg_local : ∀ n : ℕ, ∃ H : ℝ, 0 ≤ H ∧
      ∀ s t : ℝ, |s - t| ≤ 1 →
        ∀ x ∈ Set.Icc (-(n : ℝ)) (n : ℝ),
          |g s x - g t x| ≤ H * |s - t| ^ alpha := by
    intro n
    obtain ⟨H, hH, hmod⟩ := hlocal n
    refine ⟨H, hH, ?_⟩
    intro s t hst x hx
    have hprojDist : |proj s - proj t| ≤ |s - t| := by
      have hL := (LipschitzWith.projIcc hab).dist_le_mul s t
      simpa only [NNReal.coe_one, one_mul, Real.dist_eq, proj] using hL
    have hprojOne : |proj s - proj t| ≤ 1 := hprojDist.trans hst
    have hraw := hmod (proj s) (hproj_mem s) (proj t) (hproj_mem t)
      hprojOne x hx
    calc
      |g s x - g t x| ≤ H * |proj s - proj t| ^ alpha := by
        simpa only [g] using hraw
      _ ≤ H * |s - t| ^ alpha := by
        gcongr
  let F : ℝ → WholeLineRealL2 := wholeLineRealL2Section g hg_meas hg2
  refine ⟨F,
    wholeLineRealL2Section_aestronglyMeasurable_of_local_holder
      halpha hg_meas hg2 hg_local, ?_⟩
  intro q hq
  have hproj : proj q = q := by
    simpa only [proj] using congrArg Subtype.val (Set.projIcc_of_mem hab hq)
  have hrep := wholeLineRealL2Section_coe_ae g hg_meas hg2 q
  have hnorm := wholeLineRealL2Section_norm_sq g hg_meas hg2 q
  constructor
  · simpa only [F, g, hproj] using hrep
  · rw [show F q = wholeLineRealL2Section g hg_meas hg2 q from rfl,
      hnorm]
    simpa only [g, hproj] using hf_le q hq

/-! ## Closed positive-window capstone -/

/-- A square-root modulus on a set implies continuity there. -/
theorem continuousOn_of_uniform_sqrt_modulus
    {E : Type*} [NormedAddCommGroup E]
    {s : Set ℝ} {X : ℝ → E} {H : ℝ} (hH : 0 ≤ H)
    (hmod : ∀ q ∈ s, ∀ r ∈ s,
      ‖X q - X r‖ ≤ H * Real.sqrt |q - r|) :
    ContinuousOn X s := by
  intro q hq
  rw [Metric.continuousWithinAt_iff]
  intro eps heps
  have hH1 : 0 < H + 1 := by linarith
  let delta : ℝ := (eps / (H + 1)) ^ 2
  have hdelta : 0 < delta := sq_pos_of_pos (div_pos heps hH1)
  refine ⟨delta, hdelta, ?_⟩
  intro r hr hdist
  have hsqrt : Real.sqrt (dist r q) < eps / (H + 1) := by
    rw [Real.sqrt_lt' (div_pos heps hH1)]
    exact hdist
  have hbig : (H + 1) * Real.sqrt (dist r q) < eps := by
    have hmul := mul_lt_mul_of_pos_left hsqrt hH1
    have hcancel : (H + 1) * (eps / (H + 1)) = eps := by
      field_simp [hH1.ne']
    simpa only [hcancel] using hmul
  have hsmall : H * Real.sqrt (dist r q) ≤
      (H + 1) * Real.sqrt (dist r q) := by
    exact mul_le_mul_of_nonneg_right (by linarith)
      (Real.sqrt_nonneg _)
  have hm := hmod r hr q hq
  have habs : |r - q| = dist r q := by rw [Real.dist_eq]
  rw [habs] at hm
  rw [dist_eq_norm]
  exact hm.trans_lt (hsmall.trans_lt hbig)

/-- Natural closed-window realization of the full weighted spatial
gradient.  The forcing trajectory is constructed internally from its exact
square budget and compact-space time modulus.  The conclusion exports the
Hilbert representative, its continuity and quantitative modulus, and the
concrete square-integrability of every physical gradient slice. -/
theorem exists_weightedMovingHeatFullGradientCandidate_natural_closed_window
    (p : CMParams)
    {eta c a L R alpha C Kraw : ℝ}
    (haL : a < L) (hLR : L ≤ R) (hdiam : R - L ≤ 1)
    (halpha : 0 < alpha) (hC : 0 ≤ C) (hKraw : 0 ≤ Kraw)
    {W Wx f raw : ℝ → ℝ → ℝ}
    (hWa_meas : AEStronglyMeasurable (W a) volume)
    (hWa_sq : Integrable (fun x : ℝ => W a x ^ 2) volume)
    (hrestart : ∀ r ∈ Set.Icc L R, ∀ z,
      W r z = weightedMovingHeatEta eta c (r - a) (W a) z +
        weightedMovingHeatValueHistory eta c a r f z)
    (hWr_deriv : ∀ r ∈ Set.Icc L R, ∀ x,
      HasDerivAt (W r) (Wx r x) x)
    (hf_meas : ∀ q ∈ Set.Icc a R,
      AEStronglyMeasurable (f q) volume)
    (hf_sq : ∀ q ∈ Set.Icc a R,
      Integrable (fun x : ℝ => f q x ^ 2) volume)
    (hf_le : ∀ q ∈ Set.Icc a R, (∫ x : ℝ, f q x ^ 2) ≤ C)
    (hf_local : ∀ n : ℕ, ∃ H : ℝ, 0 ≤ H ∧
      ∀ s ∈ Set.Icc a R, ∀ t ∈ Set.Icc a R,
        |s - t| ≤ 1 → ∀ x ∈ Set.Icc (-(n : ℝ)) (n : ℝ),
          |f s x - f t x| ≤ H * |s - t| ^ alpha)
    (hjoint : Measurable (Function.uncurry f))
    (hraw_meas : ∀ q ∈ Set.Ioc a R,
      AEStronglyMeasurable (raw q) volume)
    (hraw_bound : ∀ q ∈ Set.Ioc a R, ∀ y, |raw q y| ≤ Kraw)
    (hfactor : ∀ q ∈ Set.Ioc a R, ∀ y,
      f q y = Real.exp (eta * y) * raw q y) :
    ∃ X : ℝ → WholeLineRealL2, ∃ BX HX : ℝ,
      0 ≤ BX ∧ 0 ≤ HX ∧
      ContinuousOn X (Set.Icc L R) ∧
      (∀ r ∈ Set.Icc L R,
        (((X r : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] Wx r)) ∧
      (∀ r ∈ Set.Icc L R,
        Integrable (fun x : ℝ => Wx r x ^ 2) volume) ∧
      (∀ r ∈ Set.Icc L R, ‖X r‖ ≤ BX) ∧
      (∀ s ∈ Set.Icc L R, ∀ t ∈ Set.Icc L R,
        ‖X s - X t‖ ≤ HX * Real.sqrt |s - t|) ∧
      (∀ s ∈ Set.Icc L R, ∀ t ∈ Set.Icc L R,
        ‖X s - X t‖ ≤ HX * |s - t| ^ paper5ForcingTimeExponent p) ∧
      ∀ s ∈ Set.Icc L R, ∀ t ∈ Set.Icc L R,
        (∫ x : ℝ, (Wx s x - Wx t x) ^ 2) ≤
          (HX * |s - t| ^ paper5ForcingTimeExponent p) ^ 2 := by
  have haR : a < R := haL.trans_le hLR
  obtain ⟨F, hFmeas, hFdata⟩ :=
    exists_wholeLineRealL2_clamped_trajectory_of_local_holder
      haR.le halpha hf_meas hf_sq hf_le hf_local
  let K : ℝ := Real.sqrt C
  have hK : 0 ≤ K := Real.sqrt_nonneg C
  have hKsq : K ^ 2 = C := by
    dsimp only [K]
    exact Real.sq_sqrt hC
  have hFrep : ∀ q ∈ Set.Icc a R,
      (((F q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] f q) :=
    fun q hq => (hFdata q hq).1
  have hFnorm : ∀ q ∈ Set.Icc a R, ‖F q‖ ≤ K := by
    intro q hq
    have hsq := (hFdata q hq).2
    nlinarith [norm_nonneg (F q)]
  let X₀ : WholeLineRealL2 :=
    wholeLineRealL2Total (W a)
  have hX₀rep : ((X₀ : ℝ → ℝ) =ᵐ[volume] W a) :=
    wholeLineRealL2Total_coe_ae _ hWa_meas hWa_sq
  let X : ℝ → WholeLineRealL2 := fun r =>
    weightedMovingHeatFullGradientCandidate eta c a X₀ F r
  have hhist_meas : ∀ r ∈ Set.Icc a R,
      AEStronglyMeasurable
        (fun q => weightedMovingHeatL2Gradient eta c (r - q) (F q))
        (volume.restrict (Set.Icc a r)) := by
    intro r hr
    exact (weightedMovingHeatL2Gradient_history_aestronglyMeasurable
      (eta := eta) (c := c) (r := r) hFmeas).mono_measure
        Measure.restrict_le_self
  have hDint : ∀ r ∈ Set.Icc a R, IntervalIntegrable
      (fun q => weightedMovingHeatL2Gradient eta c (r - q) (F q))
      volume a r := by
    intro r hr
    exact weightedMovingHeatL2Gradient_intervalIntegrable_of_uniform_norm_bound
      (eta := eta) (c := c) hr.1 hK
        (fun q hq => hFnorm q ⟨hq.1, hq.2.trans hr.2⟩)
        (hhist_meas r hr)
  have hlocalProd : ∀ r ∈ Set.Icc a R,
      ∀ A : Set ℝ, MeasurableSet A →
        (volume : Measure ℝ) A < ⊤ →
        Integrable
          (fun z : ℝ × ℝ => A.indicator
            (weightedMovingHeatGradientEta eta c (r - z.1) (f z.1)) z.2)
          ((volume.restrict (Set.Ioc a r)).prod volume) := by
    intro r hr
    exact weightedMovingHeatGradientEta_history_local_prod_integrable
      hr.1 (fun q hq => hFrep q ⟨hq.1.le, hq.2.trans hr.2⟩)
        (hDint r hr) hjoint
  have hXrep : ∀ r ∈ Set.Icc L R,
      (((X r : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] Wx r) := by
    intro r hr
    have har : a < r := haL.trans_le hr.1
    have hrAR : r ∈ Set.Icc a R := ⟨har.le, hr.2⟩
    have hhistory : ∀ x, HasDerivAt
        (weightedMovingHeatValueHistory eta c a r f)
        (weightedMovingHeatGradientHistory eta c a r f x) x := by
      intro x
      exact weightedMovingHeatValueHistory_hasDerivAt_of_exp_raw_window_l2
        (eta := eta) (c := c) (K := Kraw) har hKraw
        (fun q hq => hFrep q ⟨hq.1.le, hq.2.trans hr.2⟩)
        hjoint
        (fun q hq => hraw_meas q ⟨hq.1, hq.2.trans hr.2⟩)
        (fun q hq => hraw_bound q ⟨hq.1, hq.2.trans hr.2⟩)
        (fun q hq => hfactor q ⟨hq.1, hq.2.trans hr.2⟩)
    apply weightedMovingHeatFullGradientCandidate_coe_ae_of_pointwise
      (eta := eta) (c := c) har hX₀rep
      (fun q hq => hFrep q ⟨hq.1.le, hq.2.trans hr.2⟩)
      (hDint r hrAR) (hlocalProd r hrAR)
    exact Eventually.of_forall fun x => by
      have hx := weightedMovingHeat_fullGenerator_spatial_identity_l2_data
        (eta := eta) (c := c) (x := x) X₀ har hX₀rep
          (hrestart r hr) (hWr_deriv r hr x) (hhistory x)
      simpa only [weightedMovingHeatGradientHistory] using hx
  have hWx2 : ∀ r ∈ Set.Icc L R,
      Integrable (fun x : ℝ => Wx r x ^ 2) volume := by
    intro r hr
    exact integrable_sq_of_wholeLineRealL2_ae_eq (X r) (hXrep r hr)
  let delta : ℝ := L - a
  have hdelta : 0 < delta := sub_pos.mpr haL
  let G : ℝ := weightedMovingHeatGradientHorizonConst eta c (R - a)
  have hG : 0 ≤ G :=
    weightedMovingHeatGradientHorizonConst_nonneg eta c (R - a)
  let BX : ℝ := G * delta ^ (-(1 / 2 : ℝ)) * ‖X₀‖ +
    2 * (G * K) * Real.sqrt (R - a)
  have hBX : 0 ≤ BX := by
    dsimp only [BX]
    positivity
  have hXbound : ∀ r ∈ Set.Icc L R, ‖X r‖ ≤ BX := by
    intro r hr
    have har : a ≤ r := (haL.trans_le hr.1).le
    have hlagH : r - a ≤ R - a := by linarith [hr.2]
    have hpow : (r - a) ^ (-(1 / 2 : ℝ)) ≤
        delta ^ (-(1 / 2 : ℝ)) := by
      exact Real.rpow_le_rpow_of_nonpos hdelta
        (by dsimp only [delta]; linarith [hr.1]) (by norm_num)
    have hhom : ‖weightedMovingHeatL2Gradient eta c (r - a) X₀‖ ≤
        G * delta ^ (-(1 / 2 : ℝ)) * ‖X₀‖ := by
      calc
        ‖weightedMovingHeatL2Gradient eta c (r - a) X₀‖ ≤
            G * (r - a) ^ (-(1 / 2 : ℝ)) * ‖X₀‖ := by
          exact weightedMovingHeatL2Gradient_apply_norm_le_rpow_neg_half
            (sub_nonneg.mpr har) hlagH X₀
        _ ≤ G * delta ^ (-(1 / 2 : ℝ)) * ‖X₀‖ := by
          gcongr
    have hrAR : r ∈ Set.Icc a R := ⟨har, hr.2⟩
    have hduh : ‖∫ q in a..r,
        weightedMovingHeatL2Gradient eta c (r - q) (F q)‖ ≤
        2 * (G * K) * Real.sqrt (r - a) := by
      apply wholeLineRealL2_intervalIntegral_norm_le_sub_rpow_neg_half
        har (hDint r hrAR)
      intro q hq
      have hqAR : q ∈ Set.Icc a R := ⟨hq.1, hq.2.trans hr.2⟩
      calc
        ‖weightedMovingHeatL2Gradient eta c (r - q) (F q)‖ ≤
            G * (r - q) ^ (-(1 / 2 : ℝ)) * ‖F q‖ := by
          exact weightedMovingHeatL2Gradient_apply_norm_le_rpow_neg_half
            (sub_nonneg.mpr hq.2) (by linarith [hq.1, hr.2]) (F q)
        _ ≤ G * (r - q) ^ (-(1 / 2 : ℝ)) * K := by
          exact mul_le_mul_of_nonneg_left (hFnorm q hqAR)
            (mul_nonneg hG (Real.rpow_nonneg (sub_nonneg.mpr hq.2) _))
        _ = (G * K) * (r - q) ^ (-(1 / 2 : ℝ)) := by ring
    have hsqrt : Real.sqrt (r - a) ≤ Real.sqrt (R - a) :=
      Real.sqrt_le_sqrt hlagH
    unfold X weightedMovingHeatFullGradientCandidate
    calc
      ‖weightedMovingHeatL2Gradient eta c (r - a) X₀ +
          ∫ q in a..r,
            weightedMovingHeatL2Gradient eta c (r - q) (F q)‖ ≤
          ‖weightedMovingHeatL2Gradient eta c (r - a) X₀‖ +
            ‖∫ q in a..r,
              weightedMovingHeatL2Gradient eta c (r - q) (F q)‖ :=
        norm_add_le _ _
      _ ≤ G * delta ^ (-(1 / 2 : ℝ)) * ‖X₀‖ +
          2 * (G * K) * Real.sqrt (r - a) := add_le_add hhom hduh
      _ ≤ G * delta ^ (-(1 / 2 : ℝ)) * ‖X₀‖ +
          2 * (G * K) * Real.sqrt (R - a) := by gcongr
      _ = BX := rfl
  let rho : ℝ := min (delta / 2) 1
  have hrho : 0 < rho := by
    dsimp only [rho]
    exact lt_min (half_pos hdelta) zero_lt_one
  let HX₀ : ℝ :=
    weightedMovingHeatGradientTimeHorizonConst eta c (R - a) *
          delta ^ (-(3 / 2 : ℝ)) * ‖X₀‖ +
      5 * weightedMovingHeatGradientHorizonConst eta c (R - a) * K +
      2 * weightedMovingHeatGradientTimeHorizonConst eta c (R - a) * K
  have hRa : 0 ≤ R - a := sub_nonneg.mpr haR.le
  have hGT : 0 ≤
      weightedMovingHeatGradientTimeHorizonConst eta c (R - a) :=
    weightedMovingHeatGradientTimeHorizonConst_nonneg hRa
  have hHX₀ : 0 ≤ HX₀ := by
    dsimp only [HX₀]
    have hterm₁ : 0 ≤
        weightedMovingHeatGradientTimeHorizonConst eta c (R - a) *
            delta ^ (-(3 / 2 : ℝ)) * ‖X₀‖ :=
      mul_nonneg (mul_nonneg hGT (Real.rpow_nonneg hdelta.le _)) (norm_nonneg X₀)
    have hterm₂ : 0 ≤
        5 * weightedMovingHeatGradientHorizonConst eta c (R - a) * K :=
      mul_nonneg (mul_nonneg (by positivity) hG) hK
    have hterm₃ : 0 ≤
        2 * weightedMovingHeatGradientTimeHorizonConst eta c (R - a) * K :=
      mul_nonneg (mul_nonneg (by positivity) hGT) hK
    exact add_nonneg (add_nonneg hterm₁ hterm₂) hterm₃
  have hlocalX : ∀ s ∈ Set.Icc L R, ∀ t ∈ Set.Icc L R,
      s < t → t - s ≤ rho →
      ‖X t - X s‖ ≤ HX₀ * Real.sqrt (t - s) := by
    intro s hs t ht hst hstep
    have hsInterior : a + delta ≤ s := by
      dsimp only [delta]
      linarith [hs.1]
    have hraw :=
      weightedMovingHeatFullGradientCandidate_sub_norm_le_sqrt_of_history_measurable
        (eta := eta) (c := c) (a := a) (R := R)
        (s := s) (t := t) (delta := delta) (K := K)
        hdelta hK haR hsInterior hst.le ht.2 (sub_pos.mpr hst)
        (by simpa only [rho] using hstep) X₀ hFnorm hhist_meas
    have hpow3 : (s - a) ^ (-(3 / 2 : ℝ)) ≤
        delta ^ (-(3 / 2 : ℝ)) := by
      exact Real.rpow_le_rpow_of_nonpos hdelta
        (by dsimp only [delta]; linarith [hs.1]) (by norm_num)
    have hfirst :
        weightedMovingHeatGradientTimeHorizonConst eta c (R - a) *
            (s - a) ^ (-(3 / 2 : ℝ)) * ‖X₀‖ ≤
          weightedMovingHeatGradientTimeHorizonConst eta c (R - a) *
            delta ^ (-(3 / 2 : ℝ)) * ‖X₀‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow3 hGT) (norm_nonneg X₀)
    have hcoef :
        (weightedMovingHeatGradientTimeHorizonConst eta c (R - a) *
            (s - a) ^ (-(3 / 2 : ℝ)) * ‖X₀‖ +
          5 * weightedMovingHeatGradientHorizonConst eta c (R - a) * K +
          2 * weightedMovingHeatGradientTimeHorizonConst eta c (R - a) * K)
          ≤ HX₀ := by
      dsimp only [HX₀]
      linarith
    exact hraw.trans (mul_le_mul_of_nonneg_right hcoef
      (Real.sqrt_nonneg _))
  obtain ⟨HX, hHX, hXsqrt⟩ :=
    exists_uniform_sqrt_holder_of_local_and_bound
      hrho hHX₀ hBX hXbound hlocalX
  have hXcont : ContinuousOn X (Set.Icc L R) :=
    continuousOn_of_uniform_sqrt_modulus hHX hXsqrt
  have hXpower : ∀ s ∈ Set.Icc L R, ∀ t ∈ Set.Icc L R,
      ‖X s - X t‖ ≤ HX * |s - t| ^ paper5ForcingTimeExponent p :=
    uniform_forcingExponent_holder_of_sqrt_holder p hdiam hHX hXsqrt
  have hWx_diff_bound : ∀ s ∈ Set.Icc L R, ∀ t ∈ Set.Icc L R,
      (∫ x : ℝ, (Wx s x - Wx t x) ^ 2) ≤
        (HX * |s - t| ^ paper5ForcingTimeExponent p) ^ 2 := by
    intro s hs t ht
    exact wholeLineIntegral_sub_sq_le_of_norm_sub_le
      (X s) (X t) (hXrep s hs) (hXrep t ht)
      (mul_nonneg hHX (Real.rpow_nonneg (abs_nonneg (s - t)) _))
      (hXpower s hs t ht)
  exact ⟨X, BX, HX, hBX, hHX, hXcont, hXrep, hWx2, hXbound,
    hXsqrt, hXpower, hWx_diff_bound⟩
section AxiomAudit

#print axioms weightedMovingHeatL2Gradient_continuousAt_of_pos
#print axioms weightedMovingHeatL2Gradient_terminal_continuousOn_Iio
#print axioms
  weightedMovingHeatL2Gradient_terminal_aestronglyMeasurable
#print axioms
  weightedMovingHeatL2Gradient_history_aestronglyMeasurable
#print axioms weightedMovingHeatEta_comp_l2_data
#print axioms weightedMovingHeatGradientEta_comp_l2_data
#print axioms weightedMovingHeatEta_l2_data_bounded
#print axioms weightedMovingHeatEta_spatial_hasDerivAt_l2_data
#print axioms weightedMovingHeatEta_abs_le_of_exp_raw_bound
#print axioms weightedMovingHeatGradientEta_abs_le_of_exp_raw_bound_l2
#print axioms weightedMovingHeatEta_history_stronglyMeasurable_gradientNatural
#print axioms weightedMovingHeatValueHistory_hasDerivAt_of_dominated_l2
#print axioms weightedMovingHeatValueHistory_hasDerivAt_of_exp_raw_window_l2
#print axioms weightedMovingHeat_fullGenerator_spatial_identity_l2_data
#print axioms weightedMovingHeatFullGradientCandidate_coe_ae_of_pointwise
#print axioms wholeLineRealL2Section_aestronglyMeasurable_of_local_holder
#print axioms exists_wholeLineRealL2_clamped_trajectory_of_local_holder
#print axioms continuousOn_of_uniform_sqrt_modulus
#print axioms exists_weightedMovingHeatFullGradientCandidate_natural_closed_window

end AxiomAudit

end ShenWork.Paper1
