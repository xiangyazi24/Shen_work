import ShenWork.Paper1.WholeLineWeightedRegularityGeneratorForcingNatural
import ShenWork.Paper1.WholeLineWeightedRegularityGeneratorMild
import ShenWork.Paper1.WholeLineWeightedRegularityDuhamelContinuity

open Filter MeasureTheory Set Topology
open scoped RealInnerProductSpace

noncomputable section

namespace ShenWork.Paper1

/-!
# Natural restart data for the exact-weight generator history

This file supplies the measure-theoretic part of the full-generator restart.
The nonlinear forcing is used only at the target exponential weight.  In
particular, no stronger weight, weighted second derivative, or realization of
the spatial generator is assumed.
-/

/-- The norm of the canonical total `L²` realization is the concrete square
integral whenever the scalar representative is measurable and square
integrable. -/
theorem wholeLineRealL2Total_norm_sq_eq_integral
    {f : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f volume)
    (hf_sq : Integrable (fun x : ℝ => f x ^ 2) volume) :
    ‖wholeLineRealL2Total f‖ ^ 2 = ∫ x : ℝ, f x ^ 2 := by
  have hrep := wholeLineRealL2Total_coe_ae f hf_meas hf_sq
  rw [wholeLineRealL2_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [hrep] with x hx
  rw [hx]

/-- A uniform square budget for scalar representatives gives a uniform norm
budget for their canonical `L²` realizations. -/
theorem wholeLineRealL2Total_norm_le_sqrt_of_integral_sq_le
    {f : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf_sq : Integrable (fun x : ℝ => f x ^ 2) volume)
    (hf_le : (∫ x : ℝ, f x ^ 2) ≤ C) :
    ‖wholeLineRealL2Total f‖ ≤ Real.sqrt C := by
  have hnorm := wholeLineRealL2Total_norm_sq_eq_integral hf_meas hf_sq
  have hsqrt0 : 0 ≤ Real.sqrt C := Real.sqrt_nonneg C
  have hsqrt_sq : (Real.sqrt C) ^ 2 = C := Real.sq_sqrt hC
  nlinarith [sq_nonneg (‖wholeLineRealL2Total f‖ - Real.sqrt C),
    norm_nonneg (wholeLineRealL2Total f)]

/-- On a finite nonnegative lag window, the concrete weighted heat growth is
bounded by one explicit exponential constant. -/
theorem weightedMovingHeatGrowth_le_exp_abs_mul_of_mem_Icc
    {eta c H lag : ℝ}
    (hlag : lag ∈ Set.Icc (0 : ℝ) H) :
    weightedMovingHeatGrowth eta c lag ≤
      Real.exp (|eta ^ 2 - c * eta| * H) := by
  unfold weightedMovingHeatGrowth
  apply Real.exp_le_exp.mpr
  calc
    (eta ^ 2 - c * eta) * lag ≤
        |eta ^ 2 - c * eta| * lag := by
      exact mul_le_mul_of_nonneg_right (le_abs_self _) hlag.1
    _ ≤ |eta ^ 2 - c * eta| * H := by
      exact mul_le_mul_of_nonneg_left hlag.2 (abs_nonneg _)

/-- Static exact-weight forcing square bounds and measurability of the heat
history imply its Bochner interval-integrability.  The time-measurability
premise is deliberately stated for the composed heat history: it is the
separate history-section issue, while all norm and integrability estimates
are discharged here from the scalar square budget. -/
theorem weightedMovingHeatL2Semigroup_intervalIntegrable_of_uniform_square_bound
    {eta c a r C : ℝ} (har : a ≤ r) (hC : 0 ≤ C)
    {f : ℝ → ℝ → ℝ}
    (hf_meas : ∀ q ∈ Set.Icc a r,
      AEStronglyMeasurable (f q) volume)
    (hf_sq : ∀ q ∈ Set.Icc a r,
      Integrable (fun x : ℝ => f q x ^ 2) volume)
    (hf_le : ∀ q ∈ Set.Icc a r,
      (∫ x : ℝ, f q x ^ 2) ≤ C)
    (hhist_meas : AEStronglyMeasurable
      (fun q => weightedMovingHeatL2Semigroup eta c (r - q)
        (wholeLineRealL2Total (f q)))
      (volume.restrict (Set.Icc a r))) :
    IntervalIntegrable
      (fun q => weightedMovingHeatL2Semigroup eta c (r - q)
        (wholeLineRealL2Total (f q))) volume a r := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le har]
  apply IntegrableOn.of_bound measure_Icc_lt_top hhist_meas
    (Real.exp (|eta ^ 2 - c * eta| * (r - a)) * Real.sqrt C)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with q hq
  have hlag : r - q ∈ Set.Icc (0 : ℝ) (r - a) := by
    constructor <;> linarith [hq.1, hq.2]
  have hsource : ‖wholeLineRealL2Total (f q)‖ ≤ Real.sqrt C :=
    wholeLineRealL2Total_norm_le_sqrt_of_integral_sq_le hC
      (hf_meas q hq) (hf_sq q hq) (hf_le q hq)
  rcases hlag.1.eq_or_lt with hzero | hpos
  · have hzero' : r - q = 0 := hzero.symm
    rw [hzero', weightedMovingHeatL2Semigroup_zero,
      ContinuousLinearMap.one_apply]
    exact hsource.trans (by
      simpa using mul_le_mul_of_nonneg_right
        (show (1 : ℝ) ≤
            Real.exp (|eta ^ 2 - c * eta| * (r - a)) by
          rw [← Real.exp_zero]
          apply Real.exp_le_exp.mpr
          exact mul_nonneg (abs_nonneg _) (sub_nonneg.mpr har))
        (Real.sqrt_nonneg C))
  · calc
      ‖weightedMovingHeatL2Semigroup eta c (r - q)
          (wholeLineRealL2Total (f q))‖ ≤
          weightedMovingHeatGrowth eta c (r - q) *
            ‖wholeLineRealL2Total (f q)‖ :=
        by
          rw [weightedMovingHeatL2Semigroup_of_pos hpos]
          exact weightedMovingHeatL2Fun_norm_le hpos _
      _ ≤ Real.exp (|eta ^ 2 - c * eta| * (r - a)) *
          Real.sqrt C := by
        gcongr
        exact weightedMovingHeatGrowth_le_exp_abs_mul_of_mem_Icc
          hlag

/-- A jointly measurable scalar heat history with a uniform exact-weight
forcing square budget is locally product-integrable on every finite-measure
spatial set.  This is the concrete Fubini premise used by
`weightedMovingHeatL2Semigroup_mild_restart_eq_of_pointwise_total`.

The terminal zero-lag slice is discarded as a null time.  Every remaining
slice is controlled by the concrete `L²` heat estimate, so no global spatial
`L¹` assumption is introduced. -/
theorem weightedMovingHeatEta_history_local_prod_integrable_of_uniform_square_bound
    {eta c a r C : ℝ} (har : a ≤ r) (hC : 0 ≤ C)
    {f : ℝ → ℝ → ℝ}
    (hf_meas : ∀ q ∈ Set.Icc a r,
      AEStronglyMeasurable (f q) volume)
    (hf_sq : ∀ q ∈ Set.Icc a r,
      Integrable (fun x : ℝ => f q x ^ 2) volume)
    (hf_le : ∀ q ∈ Set.Icc a r,
      (∫ x : ℝ, f q x ^ 2) ≤ C)
    (hjoint : AEStronglyMeasurable
      (fun z : ℝ × ℝ =>
        weightedMovingHeatEta eta c (r - z.1) (f z.1) z.2)
      ((volume.restrict (Set.Ioc a r)).prod volume))
    (A : Set ℝ) (hA : MeasurableSet A)
    (hAfin : (volume : Measure ℝ) A < ⊤) :
    Integrable
      (fun z : ℝ × ℝ => A.indicator
        (weightedMovingHeatEta eta c (r - z.1) (f z.1)) z.2)
      ((volume.restrict (Set.Ioc a r)).prod volume) := by
  let mu : Measure ℝ := volume.restrict (Set.Ioc a r)
  let raw : ℝ × ℝ → ℝ := fun z =>
    weightedMovingHeatEta eta c (r - z.1) (f z.1) z.2
  let B : ℝ :=
    Real.exp (|eta ^ 2 - c * eta| * (r - a)) ^ 2 * C
  have hB : 0 ≤ B := mul_nonneg (sq_nonneg _) hC
  have hmu_fin : mu Set.univ < ⊤ := by
    dsimp only [mu]
    rw [Measure.restrict_apply_univ]
    exact measure_Ioc_lt_top
  letI : IsFiniteMeasure mu := ⟨hmu_fin⟩
  have hslice : ∀ᵐ q ∂mu,
      Integrable (fun x : ℝ => raw (q, x) ^ 2) volume ∧
        (∫ x : ℝ, raw (q, x) ^ 2) ≤ B := by
    have hne : ∀ᵐ q : ℝ ∂mu, q ≠ r := by
      simpa only [mu] using
        (Measure.ae_ne volume r).filter_mono ae_restrict_le
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hne]
      with q hq hqr
    have hqcc : q ∈ Set.Icc a r := ⟨hq.1.le, hq.2⟩
    have hlag : 0 < r - q := sub_pos.mpr (lt_of_le_of_ne hq.2 hqr)
    let Z : WholeLineRealL2 := wholeLineRealL2Total (f q)
    have hrep : ((Z : ℝ → ℝ) =ᵐ[volume] f q) := by
      exact wholeLineRealL2Total_coe_ae _
        (hf_meas q hqcc) (hf_sq q hqcc)
    have heq : weightedMovingHeatEta eta c (r - q) (Z : ℝ → ℝ) =
        weightedMovingHeatEta eta c (r - q) (f q) := by
      funext x
      exact weightedMovingHeatEta_congr_ae hrep x
    have hdata := weightedMovingHeatEta_l2_data
      (eta := eta) (c := c) hlag Z
    have hnormZ : ‖Z‖ ^ 2 ≤ C := by
      dsimp only [Z]
      rw [wholeLineRealL2Total_norm_sq_eq_integral
        (hf_meas q hqcc) (hf_sq q hqcc)]
      exact hf_le q hqcc
    have hgrowth : weightedMovingHeatGrowth eta c (r - q) ≤
        Real.exp (|eta ^ 2 - c * eta| * (r - a)) := by
      apply weightedMovingHeatGrowth_le_exp_abs_mul_of_mem_Icc
      constructor <;> linarith [hq.1, hq.2]
    have hgrowth0 : 0 ≤ weightedMovingHeatGrowth eta c (r - q) :=
      Real.exp_nonneg _
    have hexp0 : 0 ≤
        Real.exp (|eta ^ 2 - c * eta| * (r - a)) := Real.exp_nonneg _
    constructor
    · simpa only [raw, heq] using hdata.2.1
    · have hZint : (∫ x : ℝ, (Z x) ^ 2) = ‖Z‖ ^ 2 :=
        (wholeLineRealL2_norm_sq_eq_integral Z).symm
      calc
        (∫ x : ℝ, raw (q, x) ^ 2) =
            ∫ x : ℝ,
              weightedMovingHeatEta eta c (r - q) (Z : ℝ → ℝ) x ^ 2 := by
          simp only [raw, heq]
        _ ≤ weightedMovingHeatGrowth eta c (r - q) ^ 2 *
              ∫ x : ℝ, (Z x) ^ 2 := hdata.2.2
        _ = weightedMovingHeatGrowth eta c (r - q) ^ 2 * ‖Z‖ ^ 2 := by
          rw [hZint]
        _ ≤ Real.exp (|eta ^ 2 - c * eta| * (r - a)) ^ 2 * C := by
          gcongr
  have hraw_sq_meas : AEStronglyMeasurable (fun z => raw z ^ 2)
      (mu.prod volume) := by
    simpa only [mu, raw] using hjoint.pow 2
  have htime_meas : AEStronglyMeasurable
      (fun q => ∫ x : ℝ, ‖raw (q, x) ^ 2‖ ∂volume) mu :=
    hraw_sq_meas.norm.integral_prod_right'
  have htime_int : Integrable
      (fun q => ∫ x : ℝ, ‖raw (q, x) ^ 2‖ ∂volume) mu := by
    apply Integrable.of_bound htime_meas B
    filter_upwards [hslice] with q hq
    have hnon : 0 ≤ ∫ x : ℝ, ‖raw (q, x) ^ 2‖ ∂volume :=
      integral_nonneg fun _ => norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnon]
    simpa only [Real.norm_eq_abs, abs_sq] using hq.2
  have hraw_sq_int : Integrable (fun z => raw z ^ 2) (mu.prod volume) := by
    rw [integrable_prod_iff hraw_sq_meas]
    exact ⟨hslice.mono (fun q hq => hq.1), htime_int⟩
  have hraw_mem : MemLp raw 2 (mu.prod volume) :=
    (memLp_two_iff_integrable_sq hjoint).2 (by
      simpa only [mu, raw] using hraw_sq_int)
  let Zprod : Lp ℝ 2 (mu.prod volume) := hraw_mem.toLp raw
  let S : Set (ℝ × ℝ) := Set.univ ×ˢ A
  have hS : MeasurableSet S := MeasurableSet.univ.prod hA
  have hSfin : (mu.prod volume) S ≠ ⊤ := by
    dsimp only [S]
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top hmu_fin.ne hAfin.ne
  have hZon : IntegrableOn (Zprod : ℝ × ℝ → ℝ) S
      (mu.prod volume) :=
    integrableOn_Lp_of_measure_ne_top Zprod
      fact_one_le_two_ennreal.elim hSfin
  have hrep : ((Zprod : ℝ × ℝ → ℝ) =ᵐ[mu.prod volume] raw) :=
    MemLp.coeFn_toLp hraw_mem
  have hraw_on : IntegrableOn raw S (mu.prod volume) :=
    hZon.congr_fun_ae (hrep.filter_mono ae_restrict_le)
  have hind : Integrable (S.indicator raw) (mu.prod volume) :=
    (integrable_indicator_iff hS).2 hraw_on
  refine hind.congr ?_
  exact Eventually.of_forall fun z => by
    by_cases hz : z.2 ∈ A
    · simp [S, raw, hz]
    · simp [S, raw, hz]

/-- The two measure-theoretic hypotheses required by the pointwise-to-`L²`
restart lift follow together from one uniform exact-weight square budget.
Only time measurability of the `L²` history and joint measurability of its
scalar representative remain explicit. -/
theorem weightedMovingHeat_generatorRestart_data_of_uniform_square_bound
    {eta c a r C : ℝ} (har : a ≤ r) (hC : 0 ≤ C)
    {f : ℝ → ℝ → ℝ}
    (hf_meas : ∀ q ∈ Set.Icc a r,
      AEStronglyMeasurable (f q) volume)
    (hf_sq : ∀ q ∈ Set.Icc a r,
      Integrable (fun x : ℝ => f q x ^ 2) volume)
    (hf_le : ∀ q ∈ Set.Icc a r,
      (∫ x : ℝ, f q x ^ 2) ≤ C)
    (hhist_meas : AEStronglyMeasurable
      (fun q => weightedMovingHeatL2Semigroup eta c (r - q)
        (wholeLineRealL2Total (f q)))
      (volume.restrict (Set.Icc a r)))
    (hjoint : AEStronglyMeasurable
      (fun z : ℝ × ℝ =>
        weightedMovingHeatEta eta c (r - z.1) (f z.1) z.2)
      ((volume.restrict (Set.Ioc a r)).prod volume)) :
    IntervalIntegrable
        (fun q => weightedMovingHeatL2Semigroup eta c (r - q)
          (wholeLineRealL2Total (f q))) volume a r ∧
      ∀ A : Set ℝ, MeasurableSet A →
        (volume : Measure ℝ) A < ⊤ →
        Integrable
          (fun z : ℝ × ℝ => A.indicator
            (weightedMovingHeatEta eta c (r - z.1) (f z.1)) z.2)
          ((volume.restrict (Set.Ioc a r)).prod volume) := by
  refine ⟨weightedMovingHeatL2Semigroup_intervalIntegrable_of_uniform_square_bound
      har hC hf_meas hf_sq hf_le hhist_meas, ?_⟩
  intro A hA hAfin
  exact weightedMovingHeatEta_history_local_prod_integrable_of_uniform_square_bound
    har hC hf_meas hf_sq hf_le hjoint A hA hAfin

/-- Fully assembled pointwise-to-`L²` restart lift under a uniform
exact-weight forcing square budget.  This theorem removes both Bochner
integrability and local Fubini from downstream generator-restart proofs. -/
theorem weightedMovingHeatL2Semigroup_mild_restart_eq_of_pointwise_total_of_uniform_square_bound
    {eta c a r C : ℝ} (har : a < r) (hC : 0 ≤ C)
    {z f : ℝ → ℝ → ℝ}
    (hz_meas : ∀ q ∈ Set.Icc a r,
      AEStronglyMeasurable (z q) volume)
    (hz_sq : ∀ q ∈ Set.Icc a r,
      Integrable (fun x : ℝ => z q x ^ 2) volume)
    (hf_meas : ∀ q ∈ Set.Icc a r,
      AEStronglyMeasurable (f q) volume)
    (hf_sq : ∀ q ∈ Set.Icc a r,
      Integrable (fun x : ℝ => f q x ^ 2) volume)
    (hf_le : ∀ q ∈ Set.Icc a r,
      (∫ x : ℝ, f q x ^ 2) ≤ C)
    (hhist_meas : AEStronglyMeasurable
      (fun q => weightedMovingHeatL2Semigroup eta c (r - q)
        (wholeLineRealL2Total (f q)))
      (volume.restrict (Set.Icc a r)))
    (hjoint : AEStronglyMeasurable
      (fun w : ℝ × ℝ =>
        weightedMovingHeatEta eta c (r - w.1) (f w.1) w.2)
      ((volume.restrict (Set.Ioc a r)).prod volume))
    (hpoint : ∀ᵐ x ∂volume,
      z r x = weightedMovingHeatEta eta c (r - a) (z a) x +
        ∫ q in a..r,
          weightedMovingHeatEta eta c (r - q) (f q) x) :
    wholeLineRealL2Total (z r) =
      weightedMovingHeatL2Semigroup eta c (r - a)
          (wholeLineRealL2Total (z a)) +
        ∫ q in a..r,
          weightedMovingHeatL2Semigroup eta c (r - q)
            (wholeLineRealL2Total (f q)) := by
  have hdata :=
    weightedMovingHeat_generatorRestart_data_of_uniform_square_bound
      har.le hC hf_meas hf_sq hf_le hhist_meas hjoint
  exact weightedMovingHeatL2Semigroup_mild_restart_eq_of_pointwise_total
    har hz_meas hz_sq
      (fun q hq => hf_meas q ⟨hq.1.le, hq.2⟩)
      (fun q hq => hf_sq q ⟨hq.1.le, hq.2⟩)
      hdata.1 hdata.2 hpoint

/-! ## The zero-order Volterra seam

The canonical Cauchy restart is written for the damped generator and has the
solution itself in the shifted source.  Removing that zero-order damping is
therefore a Volterra uniqueness problem.  The following lemma closes its
uniqueness half on a short window without a generator-domain assumption.
-/

/-- Uniform operator bound for the totalized weighted heat semigroup on a
compact nonnegative lag window. -/
theorem weightedMovingHeatL2Semigroup_norm_apply_le_on_lag_window
    {eta c H lag : ℝ} (hlag : lag ∈ Set.Icc (0 : ℝ) H)
    (Z : WholeLineRealL2) :
    ‖weightedMovingHeatL2Semigroup eta c lag Z‖ ≤
      Real.exp (|eta ^ 2 - c * eta| * H) * ‖Z‖ := by
  rcases hlag.1.eq_or_lt with hzero | hpos
  · have hzero' : lag = 0 := hzero.symm
    rw [hzero', weightedMovingHeatL2Semigroup_zero,
      ContinuousLinearMap.one_apply]
    have hK : (1 : ℝ) ≤ Real.exp (|eta ^ 2 - c * eta| * H) := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      exact mul_nonneg (abs_nonneg _) (hlag.1.trans hlag.2)
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hK (norm_nonneg Z)
  · calc
      ‖weightedMovingHeatL2Semigroup eta c lag Z‖ ≤
          weightedMovingHeatGrowth eta c lag * ‖Z‖ := by
        rw [weightedMovingHeatL2Semigroup_of_pos hpos]
        exact weightedMovingHeatL2Fun_norm_le hpos Z
      _ ≤ Real.exp (|eta ^ 2 - c * eta| * H) * ‖Z‖ := by
        exact mul_le_mul_of_nonneg_right
          (weightedMovingHeatGrowth_le_exp_abs_mul_of_mem_Icc hlag)
          (norm_nonneg Z)

/-- A strongly measurable `L²` forcing history with one uniform norm
budget has an interval-integrable heat history on every finite restart
window.  This is the Hilbert-valued counterpart of the scalar square-budget
producer above. -/
theorem weightedMovingHeatL2Semigroup_intervalIntegrable_of_uniform_norm_bound
    {eta c a r K : ℝ} (har : a ≤ r) (hK : 0 ≤ K)
    {F : ℝ → WholeLineRealL2}
    (hF : ∀ q ∈ Set.Icc a r, ‖F q‖ ≤ K)
    (hhist_meas : AEStronglyMeasurable
      (fun q => weightedMovingHeatL2Semigroup eta c (r - q) (F q))
      (volume.restrict (Set.Icc a r))) :
    IntervalIntegrable
      (fun q => weightedMovingHeatL2Semigroup eta c (r - q) (F q))
      volume a r := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le har]
  apply IntegrableOn.of_bound measure_Icc_lt_top hhist_meas
    (Real.exp (|eta ^ 2 - c * eta| * (r - a)) * K)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with q hq
  have hlag : r - q ∈ Set.Icc (0 : ℝ) (r - a) := by
    constructor <;> linarith [hq.1, hq.2]
  exact (weightedMovingHeatL2Semigroup_norm_apply_le_on_lag_window
    (eta := eta) (c := c) hlag (F q)).trans
      (mul_le_mul_of_nonneg_left (hF q hq) (Real.exp_nonneg _))

/-- The damped direct history and its complementary resolvent history are
both interval-integrable under the same exact-weight forcing norm budget.
The scalar damping multipliers have absolute value at most one on a
nonnegative lag. -/
theorem weightedMovingHeat_damped_histories_intervalIntegrable_of_uniform_norm_bound
    {eta c a t K : ℝ} (hat : a ≤ t) (hK : 0 ≤ K)
    {F : ℝ → WholeLineRealL2}
    (hF : ∀ q ∈ Set.Icc a t, ‖F q‖ ≤ K)
    (hhist_meas : AEStronglyMeasurable
      (fun q => weightedMovingHeatL2Semigroup eta c (t - q) (F q))
      (volume.restrict (Set.Icc a t))) :
    IntervalIntegrable
        (fun q => Real.exp (-(t - q)) •
          weightedMovingHeatL2Semigroup eta c (t - q) (F q))
        volume a t ∧
      IntervalIntegrable
        (fun q => (1 - Real.exp (-(t - q))) •
          weightedMovingHeatL2Semigroup eta c (t - q) (F q))
        volume a t := by
  let A : ℝ := Real.exp (|eta ^ 2 - c * eta| * (t - a))
  have hscalarD : AEStronglyMeasurable
      (fun q : ℝ => Real.exp (-(t - q)))
      (volume.restrict (Set.Icc a t)) :=
    (by fun_prop : Continuous
      (fun q : ℝ => Real.exp (-(t - q)))).aestronglyMeasurable.mono_measure
        Measure.restrict_le_self
  have hscalarC : AEStronglyMeasurable
      (fun q : ℝ => 1 - Real.exp (-(t - q)))
      (volume.restrict (Set.Icc a t)) :=
    (by fun_prop : Continuous
      (fun q : ℝ => 1 - Real.exp (-(t - q)))).aestronglyMeasurable.mono_measure
        Measure.restrict_le_self
  have hDmeas : AEStronglyMeasurable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q) (F q))
      (volume.restrict (Set.Icc a t)) := hscalarD.smul hhist_meas
  have hCmeas : AEStronglyMeasurable
      (fun q => (1 - Real.exp (-(t - q))) •
        weightedMovingHeatL2Semigroup eta c (t - q) (F q))
      (volume.restrict (Set.Icc a t)) := hscalarC.smul hhist_meas
  have hboundD : ∀ᵐ q ∂(volume.restrict (Set.Icc a t)),
      ‖Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q) (F q)‖ ≤ A * K := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with q hq
    have hlag : t - q ∈ Set.Icc (0 : ℝ) (t - a) := by
      constructor <;> linarith [hq.1, hq.2]
    have hheat := weightedMovingHeatL2Semigroup_norm_apply_le_on_lag_window
      (eta := eta) (c := c) hlag (F q)
    have hexp : Real.exp (-(t - q)) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (neg_nonpos.mpr hlag.1)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-(t - q)) *
          ‖weightedMovingHeatL2Semigroup eta c (t - q) (F q)‖ ≤
          1 * (A * ‖F q‖) := mul_le_mul hexp hheat
            (norm_nonneg _) (by positivity)
      _ ≤ 1 * (A * K) := by
        gcongr
        exact hF q hq
      _ = A * K := one_mul _
  have hboundC : ∀ᵐ q ∂(volume.restrict (Set.Icc a t)),
      ‖(1 - Real.exp (-(t - q))) •
        weightedMovingHeatL2Semigroup eta c (t - q) (F q)‖ ≤ A * K := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with q hq
    have hlag : t - q ∈ Set.Icc (0 : ℝ) (t - a) := by
      constructor <;> linarith [hq.1, hq.2]
    have hheat := weightedMovingHeatL2Semigroup_norm_apply_le_on_lag_window
      (eta := eta) (c := c) hlag (F q)
    have hexp0 : Real.exp (-(t - q)) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (neg_nonpos.mpr hlag.1)
    have hcoef : |1 - Real.exp (-(t - q))| ≤ 1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr hexp0)]
      linarith [Real.exp_pos (-(t - q))]
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |1 - Real.exp (-(t - q))| *
          ‖weightedMovingHeatL2Semigroup eta c (t - q) (F q)‖ ≤
          1 * (A * ‖F q‖) := mul_le_mul hcoef hheat
            (norm_nonneg _) (by positivity)
      _ ≤ 1 * (A * K) := by
        gcongr
        exact hF q hq
      _ = A * K := one_mul _
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hat,
    intervalIntegrable_iff_integrableOn_Icc_of_le hat]
  exact ⟨IntegrableOn.of_bound measure_Icc_lt_top hDmeas (A * K) hboundD,
    IntegrableOn.of_bound measure_Icc_lt_top hCmeas (A * K) hboundC⟩

/-- The exponentially damped weighted heat orbit obeys the same compact-lag
bound, since the extra scalar factor is at most one. -/
theorem exp_neg_smul_weightedMovingHeatL2Semigroup_norm_le_on_lag_window
    {eta c H lag : ℝ} (hlag : lag ∈ Set.Icc (0 : ℝ) H)
    (Z : WholeLineRealL2) :
    ‖Real.exp (-lag) • weightedMovingHeatL2Semigroup eta c lag Z‖ ≤
      Real.exp (|eta ^ 2 - c * eta| * H) * ‖Z‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  calc
    Real.exp (-lag) *
        ‖weightedMovingHeatL2Semigroup eta c lag Z‖ ≤
      Real.exp (-lag) *
        (Real.exp (|eta ^ 2 - c * eta| * H) * ‖Z‖) := by
      exact mul_le_mul_of_nonneg_left
        (weightedMovingHeatL2Semigroup_norm_apply_le_on_lag_window hlag Z)
        (Real.exp_nonneg _)
    _ ≤ 1 * (Real.exp (|eta ^ 2 - c * eta| * H) * ‖Z‖) := by
      gcongr
      simpa only [Real.exp_zero] using
        Real.exp_le_exp.mpr (neg_nonpos.mpr hlag.1)
    _ = _ := one_mul _

/-- Short-window uniqueness for the homogeneous damped Volterra equation in
the exact weighted `L²` space.  This uses only trajectory continuity and the
semigroup norm bound; in particular it assumes neither `Wxx` nor membership
in the generator domain. -/
theorem weightedMovingHeat_dampedVolterra_eq_zero_of_short
    {eta c a r : ℝ} {D : ℝ → WholeLineRealL2}
    (har : a ≤ r)
    (hDcont : ContinuousOn D (Set.Icc a r))
    (hvolterra : ∀ t ∈ Set.Icc a r,
      D t = ∫ q in a..t,
        Real.exp (-(t - q)) •
          weightedMovingHeatL2Semigroup eta c (t - q) (D q))
    (hshort :
      Real.exp (|eta ^ 2 - c * eta| * (r - a)) * (r - a) < 1) :
    ∀ t ∈ Set.Icc a r, D t = 0 := by
  have hIcc : (Set.Icc a r).Nonempty := ⟨a, le_rfl, har⟩
  have hnorm_cont : ContinuousOn (fun t => ‖D t‖) (Set.Icc a r) :=
    continuous_norm.comp_continuousOn hDcont
  obtain ⟨t₀, ht₀, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn hIcc hnorm_cont
  let K : ℝ := Real.exp (|eta ^ 2 - c * eta| * (r - a))
  let M : ℝ := ‖D t₀‖
  have hK0 : 0 ≤ K := Real.exp_nonneg _
  have hM0 : 0 ≤ M := norm_nonneg _
  have hpoint : ∀ q ∈ Set.uIoc a t₀,
      ‖Real.exp (-(t₀ - q)) •
          weightedMovingHeatL2Semigroup eta c (t₀ - q) (D q)‖ ≤
        K * M := by
    intro q hq
    rw [Set.uIoc_of_le ht₀.1] at hq
    have hq_ar : q ∈ Set.Icc a r :=
      ⟨hq.1.le, hq.2.trans ht₀.2⟩
    have hlag : t₀ - q ∈ Set.Icc (0 : ℝ) (r - a) := by
      constructor <;> linarith [hq.1, hq.2, ht₀.1, ht₀.2]
    calc
      ‖Real.exp (-(t₀ - q)) •
          weightedMovingHeatL2Semigroup eta c (t₀ - q) (D q)‖ ≤
          K * ‖D q‖ := by
        simpa only [K] using
          exp_neg_smul_weightedMovingHeatL2Semigroup_norm_le_on_lag_window
            hlag (D q)
      _ ≤ K * M := mul_le_mul_of_nonneg_left (hmax hq_ar) hK0
  have hnorm_int := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := t₀) hpoint
  have hM_le : M ≤ K * M * (t₀ - a) := by
    rw [← hvolterra t₀ ht₀] at hnorm_int
    simpa only [M, abs_of_nonneg (sub_nonneg.mpr ht₀.1)] using hnorm_int
  have hM_le' : M ≤ K * M * (r - a) := by
    calc
      M ≤ K * M * (t₀ - a) := hM_le
      _ ≤ K * M * (r - a) := by
        exact mul_le_mul_of_nonneg_left
          (sub_le_sub_right ht₀.2 a) (mul_nonneg hK0 hM0)
  have hM : M = 0 := by
    dsimp only [K] at hshort hM_le'
    nlinarith
  intro t ht
  apply norm_eq_zero.mp
  exact le_antisymm ((hmax ht).trans_eq hM) (norm_nonneg _)

/-- Two continuous trajectories with the same initial datum and forcing in
the damped shifted-source equation agree on a short window.  This is the
reducer used for damping removal: the intended second trajectory is the
full-generator Duhamel candidate. -/
theorem weightedMovingHeat_dampedRestart_unique_of_short
    {eta c a r : ℝ}
    {Z Y F : ℝ → WholeLineRealL2} {Z₀ : WholeLineRealL2}
    (har : a ≤ r)
    (hZcont : ContinuousOn Z (Set.Icc a r))
    (hYcont : ContinuousOn Y (Set.Icc a r))
    (hZint : ∀ t ∈ Set.Icc a r, IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q) (Z q + F q))
      volume a t)
    (hYint : ∀ t ∈ Set.Icc a r, IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q) (Y q + F q))
      volume a t)
    (hZdamped : ∀ t ∈ Set.Icc a r,
      Z t = Real.exp (-(t - a)) •
          weightedMovingHeatL2Semigroup eta c (t - a) Z₀ +
        ∫ q in a..t, Real.exp (-(t - q)) •
          weightedMovingHeatL2Semigroup eta c (t - q) (Z q + F q))
    (hYdamped : ∀ t ∈ Set.Icc a r,
      Y t = Real.exp (-(t - a)) •
          weightedMovingHeatL2Semigroup eta c (t - a) Z₀ +
        ∫ q in a..t, Real.exp (-(t - q)) •
          weightedMovingHeatL2Semigroup eta c (t - q) (Y q + F q))
    (hshort :
      Real.exp (|eta ^ 2 - c * eta| * (r - a)) * (r - a) < 1) :
    ∀ t ∈ Set.Icc a r, Z t = Y t := by
  let D : ℝ → WholeLineRealL2 := fun t => Z t - Y t
  have hDcont : ContinuousOn D (Set.Icc a r) := hZcont.sub hYcont
  have hDvolterra : ∀ t ∈ Set.Icc a r,
      D t = ∫ q in a..t,
        Real.exp (-(t - q)) •
          weightedMovingHeatL2Semigroup eta c (t - q) (D q) := by
    intro t ht
    have hZi := hZint t ht
    have hYi := hYint t ht
    change Z t - Y t = ∫ q in a..t,
      Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q) (Z q - Y q)
    rw [hZdamped t ht, hYdamped t ht]
    rw [add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub hZi hYi]
    apply intervalIntegral.integral_congr
    intro q _hq
    simp only [← smul_sub, ← map_sub]
    congr 2
    abel
  have hDzero := weightedMovingHeat_dampedVolterra_eq_zero_of_short
    har hDcont hDvolterra hshort
  intro t ht
  exact sub_eq_zero.mp (hDzero t ht)

/-- The undamped full-generator Duhamel candidate based at `a`. -/
def weightedMovingHeatFullGeneratorCandidate
    (eta c a : ℝ) (Z₀ : WholeLineRealL2)
    (F : ℝ → WholeLineRealL2) (t : ℝ) : WholeLineRealL2 :=
  weightedMovingHeatL2Semigroup eta c (t - a) Z₀ +
    ∫ q in a..t,
      weightedMovingHeatL2Semigroup eta c (t - q) (F q)

/-- Bochner Fubini on the time triangle `a < s < q ≤ t`.  Encoding the
triangle by a zero extension makes the only analytic hypothesis the
integrability of that kernel on the finite product measure. -/
theorem intervalIntegral_integral_triangle_swap_of_integrable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a t : ℝ} (hat : a ≤ t)
    {G : ℝ → ℝ → E}
    (hG : Integrable
      (fun z : ℝ × ℝ => if z.2 < z.1 then G z.1 z.2 else 0)
      ((volume.restrict (Set.Ioc a t)).prod
        (volume.restrict (Set.Ioc a t)))) :
    (∫ q in a..t, ∫ s in a..q, G q s) =
      ∫ s in a..t, ∫ q in s..t, G q s := by
  let mu : Measure ℝ := volume.restrict (Set.Ioc a t)
  let J : ℝ → ℝ → E := fun q s =>
    if s < q then G q s else 0
  have hJ : Integrable (Function.uncurry J) (mu.prod mu) := by
    simpa only [mu, J, Function.uncurry] using hG
  have hswap := MeasureTheory.integral_integral_swap (f := J) hJ
  have hleft : (∫ q in a..t, ∫ s in a..q, G q s) =
      ∫ q, ∫ s, J q s ∂mu ∂mu := by
    rw [intervalIntegral.integral_of_le hat]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro q hq
    change (∫ s in a..q, G q s) = ∫ s, J q s ∂mu
    rw [intervalIntegral.integral_of_le hq.1.le]
    rw [show (∫ s, J q s ∂mu) = ∫ s in Set.Ioc a t, J q s by rfl]
    rw [← MeasureTheory.integral_indicator measurableSet_Ioc,
      ← MeasureTheory.integral_indicator measurableSet_Ioc]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [Measure.ae_ne volume q] with s hsq
    by_cases hs : s ∈ Set.Ioc a q
    · have hsat : s ∈ Set.Ioc a t := ⟨hs.1, hs.2.trans hq.2⟩
      simp only [Set.indicator_of_mem hs, Set.indicator_of_mem hsat, J]
      rw [if_pos (lt_of_le_of_ne hs.2 hsq)]
    · by_cases hsat : s ∈ Set.Ioc a t
      · have hnotlt : ¬ s < q := by
          intro hlt
          exact hs ⟨hsat.1, hlt.le⟩
        simp only [Set.indicator_of_notMem hs, Set.indicator_of_mem hsat, J,
          if_neg hnotlt]
      · simp only [Set.indicator_of_notMem hs,
          Set.indicator_of_notMem hsat]
  have hright : (∫ s in a..t, ∫ q in s..t, G q s) =
      ∫ s, ∫ q, J q s ∂mu ∂mu := by
    rw [intervalIntegral.integral_of_le hat]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    change (∫ q in s..t, G q s) = ∫ q, J q s ∂mu
    rw [intervalIntegral.integral_of_le hs.2]
    rw [show (∫ q, J q s ∂mu) = ∫ q in Set.Ioc a t, J q s by rfl]
    rw [← MeasureTheory.integral_indicator measurableSet_Ioc,
      ← MeasureTheory.integral_indicator measurableSet_Ioc]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [Measure.ae_ne volume s] with q _hqs
    by_cases hq : q ∈ Set.Ioc a t
    · by_cases hqst : q ∈ Set.Ioc s t
      · simp only [Set.indicator_of_mem hqst, Set.indicator_of_mem hq, J,
          if_pos hqst.1]
      · have hnlt : ¬ s < q := by
          intro hlt
          exact hqst ⟨hlt, hq.2⟩
        simp only [Set.indicator_of_notMem hqst, Set.indicator_of_mem hq, J,
          if_neg hnlt]
    · have hnotst : q ∉ Set.Ioc s t := by
        intro hmem
        exact hq ⟨hs.1.trans hmem.1, hmem.2⟩
      simp only [Set.indicator_of_notMem hnotst,
        Set.indicator_of_notMem hq]
  rw [hleft, hright, hswap]

/-- Elementary scalar resolvent mass of the zero-order damping kernel. -/
theorem intervalIntegral_exp_neg_sub
    {a t : ℝ} :
    (∫ q in a..t, Real.exp (-(t - q))) =
      1 - Real.exp (-(t - a)) := by
  have hderiv : deriv (fun q : ℝ => Real.exp (q - t)) =
      fun q : ℝ => Real.exp (q - t) := by
    funext q
    simpa using (((hasDerivAt_id q).sub_const t).exp).deriv
  have hdiff : ∀ q ∈ Set.uIcc a t,
      DifferentiableAt ℝ (fun q : ℝ => Real.exp (q - t)) q := by
    intro q _
    exact (((hasDerivAt_id q).sub_const t).exp).differentiableAt
  have hcont : ContinuousOn (fun q : ℝ => Real.exp (q - t))
      (Set.uIcc a t) :=
    (Real.continuous_exp.comp
      (continuous_id.sub continuous_const)).continuousOn
  have hi := intervalIntegral.integral_deriv_eq_sub'
    (fun q : ℝ => Real.exp (q - t)) hderiv hdiff hcont
  simpa [show ∀ q : ℝ, -(t - q) = q - t by intro q; ring] using hi

/-- The damping-removal triangle identity follows from Bochner Fubini and
the weighted heat semigroup law.  The two explicit hypotheses are exactly
the inner Duhamel integrability needed to commute a continuous linear map
with the inner integral, and integrability of the zero-extended triangular
kernel needed for Fubini. -/
theorem weightedMovingHeat_triangleFubini_of_integrable
    {eta c a t : ℝ} (hat : a ≤ t)
    {F : ℝ → WholeLineRealL2}
    (hinner : ∀ q ∈ Set.Icc a t, IntervalIntegrable
      (fun s => weightedMovingHeatL2Semigroup eta c (q - s) (F s))
      volume a q)
    (hproduct : Integrable
      (fun z : ℝ × ℝ => if z.2 < z.1 then
        Real.exp (-(t - z.1)) •
          weightedMovingHeatL2Semigroup eta c (t - z.1)
            (weightedMovingHeatL2Semigroup eta c (z.1 - z.2) (F z.2))
        else 0)
      ((volume.restrict (Set.Ioc a t)).prod
        (volume.restrict (Set.Ioc a t)))) :
    (∫ q in a..t, Real.exp (-(t - q)) •
      weightedMovingHeatL2Semigroup eta c (t - q)
        (∫ s in a..q,
          weightedMovingHeatL2Semigroup eta c (q - s) (F s))) =
    ∫ s in a..t, (1 - Real.exp (-(t - s))) •
      weightedMovingHeatL2Semigroup eta c (t - s) (F s) := by
  let G : ℝ → ℝ → WholeLineRealL2 := fun q s =>
    Real.exp (-(t - q)) •
      weightedMovingHeatL2Semigroup eta c (t - q)
        (weightedMovingHeatL2Semigroup eta c (q - s) (F s))
  have hcommute : ∀ q ∈ Set.Icc a t,
      Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q)
          (∫ s in a..q,
            weightedMovingHeatL2Semigroup eta c (q - s) (F s)) =
        ∫ s in a..q, G q s := by
    intro q hq
    let L : WholeLineRealL2 →L[ℝ] WholeLineRealL2 :=
      Real.exp (-(t - q)) • weightedMovingHeatL2Semigroup eta c (t - q)
    have hmap := L.intervalIntegral_comp_comm (hinner q hq)
    simpa only [L, G, ContinuousLinearMap.smul_apply] using hmap.symm
  calc
    (∫ q in a..t, Real.exp (-(t - q)) •
      weightedMovingHeatL2Semigroup eta c (t - q)
        (∫ s in a..q,
          weightedMovingHeatL2Semigroup eta c (q - s) (F s))) =
        ∫ q in a..t, ∫ s in a..q, G q s := by
      apply intervalIntegral.integral_congr
      intro q hq
      rw [Set.uIcc_of_le hat] at hq
      exact hcommute q hq
    _ = ∫ s in a..t, ∫ q in s..t, G q s := by
      apply intervalIntegral_integral_triangle_swap_of_integrable hat
      simpa only [G] using hproduct
    _ = ∫ s in a..t, (1 - Real.exp (-(t - s))) •
        weightedMovingHeatL2Semigroup eta c (t - s) (F s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le hat] at hs
      have hcollapse : ∀ q ∈ Set.uIcc s t,
          weightedMovingHeatL2Semigroup eta c (t - q)
            (weightedMovingHeatL2Semigroup eta c (q - s) (F s)) =
          weightedMovingHeatL2Semigroup eta c (t - s) (F s) := by
        intro q hq
        rw [Set.uIcc_of_le hs.2] at hq
        have hadd := weightedMovingHeatL2Semigroup_add
          (eta := eta) (c := c) (sub_nonneg.mpr hq.2)
          (sub_nonneg.mpr hq.1)
        have happ := congrArg
          (fun L : WholeLineRealL2 →L[ℝ] WholeLineRealL2 => L (F s)) hadd
        simpa only [ContinuousLinearMap.comp_apply,
          show t - q + (q - s) = t - s by ring] using happ
      calc
        (∫ q in s..t, G q s) = ∫ q in s..t,
            Real.exp (-(t - q)) •
              weightedMovingHeatL2Semigroup eta c (t - s) (F s) := by
          apply intervalIntegral.integral_congr
          intro q hq
          dsimp only [G]
          rw [hcollapse q hq]
        _ = (∫ q in s..t, Real.exp (-(t - q))) •
            weightedMovingHeatL2Semigroup eta c (t - s) (F s) := by
          exact intervalIntegral.integral_smul_const _ _
        _ = _ := by
          rw [intervalIntegral_exp_neg_sub]

/-- A measurable triangular weighted-heat kernel is Bochner integrable as
soon as the forcing has one uniform `L²` norm bound on the finite window.
Both heat factors are estimated at the same exact exponential weight; no
stronger weight or spatial generator enters. -/
theorem weightedMovingHeat_triangleKernel_integrable_of_uniform_norm_bound
    {eta c a t K : ℝ} (hat : a ≤ t) (hK : 0 ≤ K)
    {F : ℝ → WholeLineRealL2}
    (hF : ∀ s ∈ Set.Ioc a t, ‖F s‖ ≤ K)
    (hmeas : AEStronglyMeasurable
      (fun z : ℝ × ℝ => if z.2 < z.1 then
        Real.exp (-(t - z.1)) •
          weightedMovingHeatL2Semigroup eta c (t - z.1)
            (weightedMovingHeatL2Semigroup eta c (z.1 - z.2) (F z.2))
        else 0)
      ((volume.restrict (Set.Ioc a t)).prod
        (volume.restrict (Set.Ioc a t)))) :
    Integrable
      (fun z : ℝ × ℝ => if z.2 < z.1 then
        Real.exp (-(t - z.1)) •
          weightedMovingHeatL2Semigroup eta c (t - z.1)
            (weightedMovingHeatL2Semigroup eta c (z.1 - z.2) (F z.2))
        else 0)
      ((volume.restrict (Set.Ioc a t)).prod
        (volume.restrict (Set.Ioc a t))) := by
  let I : Set ℝ := Set.Ioc a t
  let R : Set (ℝ × ℝ) := I ×ˢ I
  let mu : Measure (ℝ × ℝ) :=
    (volume.prod volume).restrict R
  let A : ℝ := Real.exp (|eta ^ 2 - c * eta| * (t - a))
  have hI_fin : (volume : Measure ℝ) I < ⊤ := by
    dsimp only [I]
    exact measure_Ioc_lt_top
  have hR_fin : (volume.prod volume) R < ⊤ := by
    dsimp only [R]
    rw [Measure.prod_prod]
    exact lt_top_iff_ne_top.mpr
      (ENNReal.mul_ne_top hI_fin.ne hI_fin.ne)
  have hmu_fin : mu Set.univ < ⊤ := by
    dsimp only [mu]
    rw [Measure.restrict_apply_univ]
    exact hR_fin
  letI : IsFiniteMeasure mu := ⟨hmu_fin⟩
  have hmeas' : AEStronglyMeasurable
      (fun z : ℝ × ℝ => if z.2 < z.1 then
        Real.exp (-(t - z.1)) •
          weightedMovingHeatL2Semigroup eta c (t - z.1)
            (weightedMovingHeatL2Semigroup eta c (z.1 - z.2) (F z.2))
        else 0) mu := by
    simpa only [mu, R, I, ← Measure.prod_restrict] using hmeas
  have hbound : ∀ᵐ z ∂mu,
      ‖(if z.2 < z.1 then
          Real.exp (-(t - z.1)) •
            weightedMovingHeatL2Semigroup eta c (t - z.1)
              (weightedMovingHeatL2Semigroup eta c (z.1 - z.2) (F z.2))
        else 0)‖ ≤ A * (A * K) := by
    have hRmem : ∀ᵐ z : ℝ × ℝ ∂mu, z ∈ R := by
      exact ae_restrict_mem (by
        dsimp only [R, I]
        exact measurableSet_Ioc.prod measurableSet_Ioc)
    filter_upwards [hRmem] with z hz
    by_cases hsq : z.2 < z.1
    · rw [if_pos hsq, norm_smul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      have houterLag : t - z.1 ∈ Set.Icc (0 : ℝ) (t - a) := by
        constructor <;> linarith [hz.1.1, hz.1.2]
      have hinnerLag : z.1 - z.2 ∈ Set.Icc (0 : ℝ) (t - a) := by
        constructor <;> linarith [hz.1.2, hz.2.1]
      have hinner :=
        weightedMovingHeatL2Semigroup_norm_apply_le_on_lag_window
          (eta := eta) (c := c) hinnerLag (F z.2)
      have houter :=
        weightedMovingHeatL2Semigroup_norm_apply_le_on_lag_window
          (eta := eta) (c := c) houterLag
            (weightedMovingHeatL2Semigroup eta c (z.1 - z.2) (F z.2))
      have hFz : ‖F z.2‖ ≤ K := hF z.2 hz.2
      have hinner' :
          ‖weightedMovingHeatL2Semigroup eta c (z.1 - z.2) (F z.2)‖ ≤
            A * K := hinner.trans (mul_le_mul_of_nonneg_left hFz
              (Real.exp_nonneg _))
      have houter' :
          ‖weightedMovingHeatL2Semigroup eta c (t - z.1)
              (weightedMovingHeatL2Semigroup eta c (z.1 - z.2) (F z.2))‖ ≤
            A * (A * K) := houter.trans
              (mul_le_mul_of_nonneg_left hinner' (Real.exp_nonneg _))
      have hexp : Real.exp (-(t - z.1)) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (neg_nonpos.mpr houterLag.1)
      calc
        Real.exp (-(t - z.1)) *
            ‖weightedMovingHeatL2Semigroup eta c (t - z.1)
              (weightedMovingHeatL2Semigroup eta c (z.1 - z.2) (F z.2))‖ ≤
            1 * (A * (A * K)) := mul_le_mul hexp houter'
              (norm_nonneg _) (by positivity)
        _ = A * (A * K) := one_mul _
    · simp only [if_neg hsq, norm_zero]
      exact mul_nonneg (Real.exp_nonneg _)
        (mul_nonneg (Real.exp_nonneg _) hK)
  have hint : Integrable
      (fun z : ℝ × ℝ => if z.2 < z.1 then
        Real.exp (-(t - z.1)) •
          weightedMovingHeatL2Semigroup eta c (t - z.1)
            (weightedMovingHeatL2Semigroup eta c (z.1 - z.2) (F z.2))
        else 0) mu :=
    Integrable.of_bound hmeas' (A * (A * K)) hbound
  simpa only [mu, R, I, ← Measure.prod_restrict] using hint

/-- Product integrability of the triangular kernel also supplies
interval-integrability of the nested damped Duhamel history.  This is the
integrability half of Fubini, separated from the equality half above. -/
theorem weightedMovingHeat_nested_damped_history_intervalIntegrable_of_triangleKernel
    {eta c a t : ℝ} (hat : a ≤ t)
    {F : ℝ → WholeLineRealL2}
    (hinner : ∀ q ∈ Set.Icc a t, IntervalIntegrable
      (fun s => weightedMovingHeatL2Semigroup eta c (q - s) (F s))
      volume a q)
    (hproduct : Integrable
      (fun z : ℝ × ℝ => if z.2 < z.1 then
        Real.exp (-(t - z.1)) •
          weightedMovingHeatL2Semigroup eta c (t - z.1)
            (weightedMovingHeatL2Semigroup eta c (z.1 - z.2) (F z.2))
        else 0)
      ((volume.restrict (Set.Ioc a t)).prod
        (volume.restrict (Set.Ioc a t)))) :
    IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q)
          (∫ s in a..q,
            weightedMovingHeatL2Semigroup eta c (q - s) (F s)))
      volume a t := by
  let mu : Measure ℝ := volume.restrict (Set.Ioc a t)
  let G : ℝ → ℝ → WholeLineRealL2 := fun q s =>
    Real.exp (-(t - q)) •
      weightedMovingHeatL2Semigroup eta c (t - q)
        (weightedMovingHeatL2Semigroup eta c (q - s) (F s))
  let J : ℝ → ℝ → WholeLineRealL2 := fun q s =>
    if s < q then G q s else 0
  have hJ : Integrable (Function.uncurry J) (mu.prod mu) := by
    simpa only [mu, J, G, Function.uncurry] using hproduct
  have houter : Integrable (fun q => ∫ s, J q s ∂mu) mu :=
    hJ.integral_prod_left
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hat, IntegrableOn,
    ← MeasureTheory.restrict_Ioc_eq_restrict_Icc]
  apply houter.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
  have hqcc : q ∈ Set.Icc a t := ⟨hq.1.le, hq.2⟩
  let L : WholeLineRealL2 →L[ℝ] WholeLineRealL2 :=
    Real.exp (-(t - q)) • weightedMovingHeatL2Semigroup eta c (t - q)
  have hmap := L.intervalIntegral_comp_comm (hinner q hqcc)
  have hcommute :
      Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q)
          (∫ s in a..q,
            weightedMovingHeatL2Semigroup eta c (q - s) (F s)) =
        ∫ s in a..q, G q s := by
    simpa only [L, G, ContinuousLinearMap.smul_apply] using hmap.symm
  rw [hcommute, intervalIntegral.integral_of_le hq.1.le]
  symm
  change (∫ s in Set.Ioc a q, G q s) = ∫ s, J q s ∂mu
  rw [show (∫ s, J q s ∂mu) =
      ∫ s in Set.Ioc a t, J q s by rfl]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioc,
    ← MeasureTheory.integral_indicator measurableSet_Ioc]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [Measure.ae_ne volume q] with s hsq
  by_cases hs : s ∈ Set.Ioc a q
  · have hsat : s ∈ Set.Ioc a t := ⟨hs.1, hs.2.trans hq.2⟩
    simp only [Set.indicator_of_mem hs, Set.indicator_of_mem hsat, J]
    rw [if_pos (lt_of_le_of_ne hs.2 hsq)]
  · by_cases hsat : s ∈ Set.Ioc a t
    · have hnotlt : ¬ s < q := by
        intro hlt
        exact hs ⟨hsat.1, hlt.le⟩
      simp only [Set.indicator_of_notMem hs, Set.indicator_of_mem hsat, J,
        if_neg hnotlt]
    · simp only [Set.indicator_of_notMem hs,
        Set.indicator_of_notMem hsat]

/-- Measurability of the triangular two-time kernel is already contained in
measurability of the single terminal heat history.  On the triangle the
semigroup law collapses the two heat factors to `S(t-s)`, leaving only a
continuous scalar depending on the outer time. -/
theorem weightedMovingHeat_triangleKernel_aestronglyMeasurable_of_terminal_history
    {eta c a t : ℝ} {F : ℝ → WholeLineRealL2}
    (hterminal : AEStronglyMeasurable
      (fun s => weightedMovingHeatL2Semigroup eta c (t - s) (F s))
      (volume.restrict (Set.Ioc a t))) :
    AEStronglyMeasurable
      (fun z : ℝ × ℝ => if z.2 < z.1 then
        Real.exp (-(t - z.1)) •
          weightedMovingHeatL2Semigroup eta c (t - z.1)
            (weightedMovingHeatL2Semigroup eta c (z.1 - z.2) (F z.2))
        else 0)
      ((volume.restrict (Set.Ioc a t)).prod
        (volume.restrict (Set.Ioc a t))) := by
  let mu : Measure ℝ := volume.restrict (Set.Ioc a t)
  let tri : Set (ℝ × ℝ) := {z | z.2 < z.1}
  let simple : ℝ × ℝ → WholeLineRealL2 := fun z =>
    if z ∈ tri then
      Real.exp (-(t - z.1)) •
        weightedMovingHeatL2Semigroup eta c (t - z.2) (F z.2)
    else 0
  have hscalar : AEStronglyMeasurable
      (fun q : ℝ => Real.exp (-(t - q))) mu := by
    exact (by fun_prop : Continuous
      (fun q : ℝ => Real.exp (-(t - q)))).aestronglyMeasurable.mono_measure
        Measure.restrict_le_self
  have htri : MeasurableSet tri := by
    dsimp only [tri]
    exact measurableSet_lt measurable_snd measurable_fst
  have hsimple : AEStronglyMeasurable simple (mu.prod mu) := by
    have hterminal' : AEStronglyMeasurable
        (fun s => weightedMovingHeatL2Semigroup eta c (t - s) (F s))
        mu := by
      simpa only [mu] using hterminal
    have hbase := hscalar.comp_fst.smul
      hterminal'.comp_snd
    simpa only [simple, tri, Set.mem_setOf_eq, Set.indicator] using
      hbase.indicator htri
  apply hsimple.congr
  have heq : (
      fun z : ℝ × ℝ => if z.2 < z.1 then
        Real.exp (-(t - z.1)) •
          weightedMovingHeatL2Semigroup eta c (t - z.1)
            (weightedMovingHeatL2Semigroup eta c (z.1 - z.2) (F z.2))
        else 0) =ᵐ[mu.prod mu] simple := by
    rw [show mu.prod mu =
        (volume.prod volume).restrict
          (Set.Ioc a t ×ˢ Set.Ioc a t) by
      simpa only [mu] using
        (Measure.prod_restrict
          (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
          (Set.Ioc a t) (Set.Ioc a t))]
    filter_upwards [ae_restrict_mem
      (measurableSet_Ioc.prod measurableSet_Ioc)] with z hz
    by_cases hsq : z.2 < z.1
    · simp only [simple, tri, Set.mem_setOf_eq, if_pos hsq]
      have hadd := weightedMovingHeatL2Semigroup_add
        (eta := eta) (c := c) (sub_nonneg.mpr hz.1.2)
        (sub_nonneg.mpr hsq.le)
      have happ := congrArg
        (fun L : WholeLineRealL2 →L[ℝ] WholeLineRealL2 => L (F z.2)) hadd
      have hsem : weightedMovingHeatL2Semigroup eta c (t - z.1)
          (weightedMovingHeatL2Semigroup eta c (z.1 - z.2) (F z.2)) =
          weightedMovingHeatL2Semigroup eta c (t - z.2) (F z.2) := by
        simpa only [ContinuousLinearMap.comp_apply,
          show t - z.1 + (z.1 - z.2) = t - z.2 by ring] using happ
      rw [hsem]
    · simp only [simple, tri, Set.mem_setOf_eq, if_neg hsq]
  exact heq.symm

/-- Uniform exact-weight forcing control closes every integrability premise
of the triangular damping-removal identity.  The only remaining inputs are
strong measurability of the one-terminal heat histories and of the explicit
two-time kernel; no weighted spatial derivative is used. -/
theorem weightedMovingHeat_triangleFubini_of_uniform_norm_bound
    {eta c a t K : ℝ} (hat : a ≤ t) (hK : 0 ≤ K)
    {F : ℝ → WholeLineRealL2}
    (hF : ∀ s ∈ Set.Icc a t, ‖F s‖ ≤ K)
    (hhist_meas : ∀ q ∈ Set.Icc a t,
      AEStronglyMeasurable
        (fun s => weightedMovingHeatL2Semigroup eta c (q - s) (F s))
        (volume.restrict (Set.Icc a q)))
    (htriangle_meas : AEStronglyMeasurable
      (fun z : ℝ × ℝ => if z.2 < z.1 then
        Real.exp (-(t - z.1)) •
          weightedMovingHeatL2Semigroup eta c (t - z.1)
            (weightedMovingHeatL2Semigroup eta c (z.1 - z.2) (F z.2))
        else 0)
      ((volume.restrict (Set.Ioc a t)).prod
        (volume.restrict (Set.Ioc a t)))) :
    (∫ q in a..t, Real.exp (-(t - q)) •
      weightedMovingHeatL2Semigroup eta c (t - q)
        (∫ s in a..q,
          weightedMovingHeatL2Semigroup eta c (q - s) (F s))) =
    ∫ s in a..t, (1 - Real.exp (-(t - s))) •
      weightedMovingHeatL2Semigroup eta c (t - s) (F s) := by
  apply weightedMovingHeat_triangleFubini_of_integrable hat
  · intro q hq
    exact weightedMovingHeatL2Semigroup_intervalIntegrable_of_uniform_norm_bound
      hq.1 hK
        (fun s hs => hF s ⟨hs.1, hs.2.trans hq.2⟩)
        (hhist_meas q hq)
  · exact weightedMovingHeat_triangleKernel_integrable_of_uniform_norm_bound
      hat hK (fun s hs => hF s ⟨hs.1.le, hs.2⟩) htriangle_meas

/-- The homogeneous full heat orbit satisfies the damped shifted-source
resolvent equation.  This is the non-Fubini half of damping removal. -/
theorem weightedMovingHeat_homogeneous_damped_resolvent_identity
    {eta c a t : ℝ} (hat : a ≤ t) (Z₀ : WholeLineRealL2) :
    weightedMovingHeatL2Semigroup eta c (t - a) Z₀ =
      Real.exp (-(t - a)) •
          weightedMovingHeatL2Semigroup eta c (t - a) Z₀ +
        ∫ q in a..t, Real.exp (-(t - q)) •
          weightedMovingHeatL2Semigroup eta c (t - q)
            (weightedMovingHeatL2Semigroup eta c (q - a) Z₀) := by
  let Zt := weightedMovingHeatL2Semigroup eta c (t - a) Z₀
  have hsem : ∀ q ∈ Set.uIcc a t,
      weightedMovingHeatL2Semigroup eta c (t - q)
          (weightedMovingHeatL2Semigroup eta c (q - a) Z₀) = Zt := by
    intro q hq
    rw [Set.uIcc_of_le hat] at hq
    have hadd := weightedMovingHeatL2Semigroup_add
      (eta := eta) (c := c) (sub_nonneg.mpr hq.2)
      (sub_nonneg.mpr hq.1)
    have happ := congrArg
      (fun L : WholeLineRealL2 →L[ℝ] WholeLineRealL2 => L Z₀) hadd
    simpa only [ContinuousLinearMap.comp_apply,
      show t - q + (q - a) = t - a by ring, Zt] using happ
  have hhist :
      (∫ q in a..t, Real.exp (-(t - q)) •
          weightedMovingHeatL2Semigroup eta c (t - q)
            (weightedMovingHeatL2Semigroup eta c (q - a) Z₀)) =
        (1 - Real.exp (-(t - a))) • Zt := by
    calc
      _ = ∫ q in a..t, Real.exp (-(t - q)) • Zt := by
        apply intervalIntegral.integral_congr
        intro q hq
        change Real.exp (-(t - q)) •
            weightedMovingHeatL2Semigroup eta c (t - q)
              (weightedMovingHeatL2Semigroup eta c (q - a) Z₀) =
          Real.exp (-(t - q)) • Zt
        rw [hsem q hq]
      _ = (∫ q in a..t, Real.exp (-(t - q))) • Zt := by
        exact intervalIntegral.integral_smul_const _ _
      _ = _ := by rw [intervalIntegral_exp_neg_sub]
  rw [hhist]
  dsimp only [Zt]
  module

/-- The homogeneous damped history is interval-integrable.  Semigroup
composition makes it a scalar exponential times one fixed `L²` vector. -/
theorem weightedMovingHeat_homogeneous_damped_history_intervalIntegrable
    {eta c a t : ℝ} (hat : a ≤ t) (Z₀ : WholeLineRealL2) :
    IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q)
          (weightedMovingHeatL2Semigroup eta c (q - a) Z₀))
      volume a t := by
  let Zt := weightedMovingHeatL2Semigroup eta c (t - a) Z₀
  have href : IntervalIntegrable
      (fun q => Real.exp (-(t - q)) • Zt) volume a t := by
    apply Continuous.intervalIntegrable
    fun_prop
  apply href.congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with q hq
  rw [Set.uIoc_of_le hat] at hq
  have hadd := weightedMovingHeatL2Semigroup_add
    (eta := eta) (c := c) (sub_nonneg.mpr hq.2)
    (sub_nonneg.mpr hq.1.le)
  have happ := congrArg
    (fun L : WholeLineRealL2 →L[ℝ] WholeLineRealL2 => L Z₀) hadd
  have hsem : weightedMovingHeatL2Semigroup eta c (t - q)
      (weightedMovingHeatL2Semigroup eta c (q - a) Z₀) = Zt := by
    simpa only [ContinuousLinearMap.comp_apply,
      show t - q + (q - a) = t - a by ring, Zt] using happ
  rw [hsem]

/-- The source Duhamel orbit satisfies the damped shifted-source resolvent
identity once the one triangular Bochner-Fubini interchange has been
supplied.  All other steps are semigroup-free linear algebra plus the scalar
resolvent mass `intervalIntegral_exp_neg_sub`.

This theorem isolates the remaining Fubini atom without hiding it in a
generic continuation package. -/
theorem weightedMovingHeat_duhamel_damped_resolvent_identity_of_triangleFubini
    {eta c a t : ℝ} {F : ℝ → WholeLineRealL2}
    (hnested_int : IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q)
          (∫ s in a..q,
            weightedMovingHeatL2Semigroup eta c (q - s) (F s)))
      volume a t)
    (hdirect_int : IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q) (F q))
      volume a t)
    (hcomplement_int : IntervalIntegrable
      (fun s => (1 - Real.exp (-(t - s))) •
        weightedMovingHeatL2Semigroup eta c (t - s) (F s))
      volume a t)
    (htriangle :
      (∫ q in a..t, Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q)
          (∫ s in a..q,
            weightedMovingHeatL2Semigroup eta c (q - s) (F s))) =
      ∫ s in a..t, (1 - Real.exp (-(t - s))) •
        weightedMovingHeatL2Semigroup eta c (t - s) (F s)) :
    (∫ s in a..t,
        weightedMovingHeatL2Semigroup eta c (t - s) (F s)) =
      ∫ q in a..t, Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q)
          ((∫ s in a..q,
              weightedMovingHeatL2Semigroup eta c (q - s) (F s)) + F q) := by
  let N : ℝ → WholeLineRealL2 := fun q =>
    Real.exp (-(t - q)) •
      weightedMovingHeatL2Semigroup eta c (t - q)
        (∫ s in a..q,
          weightedMovingHeatL2Semigroup eta c (q - s) (F s))
  let R : ℝ → WholeLineRealL2 := fun q =>
    Real.exp (-(t - q)) •
      weightedMovingHeatL2Semigroup eta c (t - q) (F q)
  let C : ℝ → WholeLineRealL2 := fun s =>
    (1 - Real.exp (-(t - s))) •
      weightedMovingHeatL2Semigroup eta c (t - s) (F s)
  have hsplit :
      (∫ q in a..t, Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q)
          ((∫ s in a..q,
              weightedMovingHeatL2Semigroup eta c (q - s) (F s)) + F q)) =
        (∫ q in a..t, N q) + ∫ q in a..t, R q := by
    calc
      _ = ∫ q in a..t, N q + R q := by
        apply intervalIntegral.integral_congr
        intro q _hq
        dsimp only [N, R]
        rw [map_add, smul_add]
      _ = _ := intervalIntegral.integral_add hnested_int hdirect_int
  rw [hsplit, htriangle]
  change (∫ s in a..t,
      weightedMovingHeatL2Semigroup eta c (t - s) (F s)) =
    (∫ s in a..t, C s) + ∫ s in a..t, R s
  rw [← intervalIntegral.integral_add hcomplement_int hdirect_int]
  apply intervalIntegral.integral_congr
  intro s _hs
  dsimp only [C, R]
  module

/-- Full candidate consistency with the damped shifted-source equation,
reduced to the single triangular Fubini identity.  This combines the closed
homogeneous resolvent atom with the preceding source atom. -/
theorem weightedMovingHeatFullGeneratorCandidate_damped_resolvent_identity_of_triangleFubini
    {eta c a t : ℝ} (hat : a ≤ t)
    (Z₀ : WholeLineRealL2) {F : ℝ → WholeLineRealL2}
    (hnested_int : IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q)
          (∫ s in a..q,
            weightedMovingHeatL2Semigroup eta c (q - s) (F s)))
      volume a t)
    (hdirect_int : IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q) (F q))
      volume a t)
    (hcomplement_int : IntervalIntegrable
      (fun s => (1 - Real.exp (-(t - s))) •
        weightedMovingHeatL2Semigroup eta c (t - s) (F s))
      volume a t)
    (htriangle :
      (∫ q in a..t, Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q)
          (∫ s in a..q,
            weightedMovingHeatL2Semigroup eta c (q - s) (F s))) =
      ∫ s in a..t, (1 - Real.exp (-(t - s))) •
        weightedMovingHeatL2Semigroup eta c (t - s) (F s)) :
    weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F t =
      Real.exp (-(t - a)) •
          weightedMovingHeatL2Semigroup eta c (t - a) Z₀ +
        ∫ q in a..t, Real.exp (-(t - q)) •
          weightedMovingHeatL2Semigroup eta c (t - q)
            (weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F q + F q) := by
  let P : ℝ → WholeLineRealL2 := fun q =>
    weightedMovingHeatL2Semigroup eta c (q - a) Z₀
  let H : ℝ → WholeLineRealL2 := fun q =>
    ∫ s in a..q, weightedMovingHeatL2Semigroup eta c (q - s) (F s)
  let IH : ℝ → WholeLineRealL2 := fun q =>
    Real.exp (-(t - q)) •
      weightedMovingHeatL2Semigroup eta c (t - q) (P q)
  let IS : ℝ → WholeLineRealL2 := fun q =>
    Real.exp (-(t - q)) •
      weightedMovingHeatL2Semigroup eta c (t - q) (H q + F q)
  let IT : ℝ → WholeLineRealL2 := fun q =>
    Real.exp (-(t - q)) •
      weightedMovingHeatL2Semigroup eta c (t - q)
        (weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F q + F q)
  have hhom : P t =
      Real.exp (-(t - a)) •
          weightedMovingHeatL2Semigroup eta c (t - a) Z₀ +
        ∫ q in a..t, IH q := by
    simpa only [P, IH] using
      weightedMovingHeat_homogeneous_damped_resolvent_identity hat Z₀
  have hsrc : H t = ∫ q in a..t, IS q := by
    simpa only [H, IS] using
      weightedMovingHeat_duhamel_damped_resolvent_identity_of_triangleFubini
        hnested_int hdirect_int hcomplement_int htriangle
  have hIH_int : IntervalIntegrable IH volume a t := by
    simpa only [P, IH] using
      weightedMovingHeat_homogeneous_damped_history_intervalIntegrable hat Z₀
  have hIS_int : IntervalIntegrable IS volume a t := by
    apply (hnested_int.add hdirect_int).congr_ae
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with q _hq
    dsimp only [IS, H]
    rw [map_add, smul_add]
  have hsplit : (∫ q in a..t, IT q) =
      (∫ q in a..t, IH q) + ∫ q in a..t, IS q := by
    calc
      _ = ∫ q in a..t, IH q + IS q := by
        apply intervalIntegral.integral_congr
        intro q _hq
        dsimp only [IT, IH, IS, P, H,
          weightedMovingHeatFullGeneratorCandidate]
        rw [add_assoc, map_add, smul_add]
      _ = _ := intervalIntegral.integral_add hIH_int hIS_int
  change P t + H t =
    Real.exp (-(t - a)) •
        weightedMovingHeatL2Semigroup eta c (t - a) Z₀ +
      ∫ q in a..t, IT q
  rw [hhom, hsrc, hsplit]
  abel

/-- Integrability of the full candidate's damped shifted-source history from
the homogeneous atom and the two source histories. -/
theorem weightedMovingHeatFullGeneratorCandidate_damped_history_intervalIntegrable
    {eta c a t : ℝ} (hat : a ≤ t)
    (Z₀ : WholeLineRealL2) {F : ℝ → WholeLineRealL2}
    (hnested_int : IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q)
          (∫ s in a..q,
            weightedMovingHeatL2Semigroup eta c (q - s) (F s)))
      volume a t)
    (hdirect_int : IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q) (F q))
      volume a t) :
    IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q)
          (weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F q + F q))
      volume a t := by
  let P : ℝ → WholeLineRealL2 := fun q =>
    weightedMovingHeatL2Semigroup eta c (q - a) Z₀
  let H : ℝ → WholeLineRealL2 := fun q =>
    ∫ s in a..q, weightedMovingHeatL2Semigroup eta c (q - s) (F s)
  let IH : ℝ → WholeLineRealL2 := fun q =>
    Real.exp (-(t - q)) •
      weightedMovingHeatL2Semigroup eta c (t - q) (P q)
  let IS : ℝ → WholeLineRealL2 := fun q =>
    Real.exp (-(t - q)) •
      weightedMovingHeatL2Semigroup eta c (t - q) (H q + F q)
  have hIH_int : IntervalIntegrable IH volume a t := by
    simpa only [P, IH] using
      weightedMovingHeat_homogeneous_damped_history_intervalIntegrable hat Z₀
  have hIS_int : IntervalIntegrable IS volume a t := by
    apply (hnested_int.add hdirect_int).congr_ae
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with q _hq
    dsimp only [IS, H]
    rw [map_add, smul_add]
  apply (hIH_int.add hIS_int).congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with q _hq
  dsimp only [IH, IS, P, H,
    weightedMovingHeatFullGeneratorCandidate]
  simp only [map_add, smul_add]
  abel

/-- Exact reducer for the remaining damping-removal identity.  Once the
full-generator candidate is shown, by semigroup composition and triangular
Fubini, to satisfy the damped shifted-source equation, short-window
Volterra uniqueness identifies it with the canonical trajectory.

The hypothesis `hcandidate_damped` is thus the precise remaining analytic
atom; it contains no generator-domain or second-derivative statement. -/
theorem weightedMovingHeat_fullGenerator_restart_of_damped_resolvent_of_short
    {eta c a r : ℝ}
    {Z F : ℝ → WholeLineRealL2} {Z₀ : WholeLineRealL2}
    (har : a ≤ r)
    (hZcont : ContinuousOn Z (Set.Icc a r))
    (hcandidate_cont : ContinuousOn
      (weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F)
      (Set.Icc a r))
    (hZint : ∀ t ∈ Set.Icc a r, IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q) (Z q + F q))
      volume a t)
    (hcandidate_int : ∀ t ∈ Set.Icc a r, IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q)
          (weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F q + F q))
      volume a t)
    (hZdamped : ∀ t ∈ Set.Icc a r,
      Z t = Real.exp (-(t - a)) •
          weightedMovingHeatL2Semigroup eta c (t - a) Z₀ +
        ∫ q in a..t, Real.exp (-(t - q)) •
          weightedMovingHeatL2Semigroup eta c (t - q) (Z q + F q))
    (hcandidate_damped : ∀ t ∈ Set.Icc a r,
      weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F t =
        Real.exp (-(t - a)) •
            weightedMovingHeatL2Semigroup eta c (t - a) Z₀ +
          ∫ q in a..t, Real.exp (-(t - q)) •
            weightedMovingHeatL2Semigroup eta c (t - q)
              (weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F q + F q))
    (hshort :
      Real.exp (|eta ^ 2 - c * eta| * (r - a)) * (r - a) < 1) :
    ∀ t ∈ Set.Icc a r,
      Z t = weightedMovingHeatL2Semigroup eta c (t - a) Z₀ +
        ∫ q in a..t,
          weightedMovingHeatL2Semigroup eta c (t - q) (F q) := by
  have heq := weightedMovingHeat_dampedRestart_unique_of_short
    har hZcont hcandidate_cont hZint hcandidate_int
      hZdamped hcandidate_damped hshort
  intro t ht
  simpa only [weightedMovingHeatFullGeneratorCandidate] using heq t ht

/-- Full damping removal with the triangular Fubini identity exposed as the
only resolvent premise.  Candidate consistency and its history
integrability are assembled internally. -/
theorem weightedMovingHeat_fullGenerator_restart_of_damped_triangleFubini_of_short
    {eta c a r : ℝ}
    {Z F : ℝ → WholeLineRealL2} {Z₀ : WholeLineRealL2}
    (har : a ≤ r)
    (hZcont : ContinuousOn Z (Set.Icc a r))
    (hcandidate_cont : ContinuousOn
      (weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F)
      (Set.Icc a r))
    (hZint : ∀ t ∈ Set.Icc a r, IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q) (Z q + F q))
      volume a t)
    (hZdamped : ∀ t ∈ Set.Icc a r,
      Z t = Real.exp (-(t - a)) •
          weightedMovingHeatL2Semigroup eta c (t - a) Z₀ +
        ∫ q in a..t, Real.exp (-(t - q)) •
          weightedMovingHeatL2Semigroup eta c (t - q) (Z q + F q))
    (hnested_int : ∀ t ∈ Set.Icc a r, IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q)
          (∫ s in a..q,
            weightedMovingHeatL2Semigroup eta c (q - s) (F s)))
      volume a t)
    (hdirect_int : ∀ t ∈ Set.Icc a r, IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q) (F q))
      volume a t)
    (hcomplement_int : ∀ t ∈ Set.Icc a r, IntervalIntegrable
      (fun s => (1 - Real.exp (-(t - s))) •
        weightedMovingHeatL2Semigroup eta c (t - s) (F s))
      volume a t)
    (htriangle : ∀ t ∈ Set.Icc a r,
      (∫ q in a..t, Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q)
          (∫ s in a..q,
            weightedMovingHeatL2Semigroup eta c (q - s) (F s))) =
      ∫ s in a..t, (1 - Real.exp (-(t - s))) •
        weightedMovingHeatL2Semigroup eta c (t - s) (F s))
    (hshort :
      Real.exp (|eta ^ 2 - c * eta| * (r - a)) * (r - a) < 1) :
    ∀ t ∈ Set.Icc a r,
      Z t = weightedMovingHeatL2Semigroup eta c (t - a) Z₀ +
        ∫ q in a..t,
          weightedMovingHeatL2Semigroup eta c (t - q) (F q) := by
  apply weightedMovingHeat_fullGenerator_restart_of_damped_resolvent_of_short
    har hZcont hcandidate_cont hZint
  · intro t ht
    exact weightedMovingHeatFullGeneratorCandidate_damped_history_intervalIntegrable
      ht.1 Z₀ (hnested_int t ht) (hdirect_int t ht)
  · exact hZdamped
  · intro t ht
    exact weightedMovingHeatFullGeneratorCandidate_damped_resolvent_identity_of_triangleFubini
      ht.1 Z₀ (hnested_int t ht) (hdirect_int t ht)
        (hcomplement_int t ht) (htriangle t ht)
  · exact hshort

/-- Damping removal with the triangular Fubini premise discharged from a
uniform exact-weight forcing norm budget and the corresponding one-terminal
heat-history measurability.  This is the natural full-generator restart
interface: it carries no two-time kernel hypothesis. -/
theorem weightedMovingHeat_fullGenerator_restart_of_damped_uniform_forcing_of_short
    {eta c a r K : ℝ}
    {Z F : ℝ → WholeLineRealL2} {Z₀ : WholeLineRealL2}
    (har : a ≤ r) (hK : 0 ≤ K)
    (hF : ∀ s ∈ Set.Icc a r, ‖F s‖ ≤ K)
    (hhist_meas : ∀ t ∈ Set.Icc a r,
      AEStronglyMeasurable
        (fun s => weightedMovingHeatL2Semigroup eta c (t - s) (F s))
        (volume.restrict (Set.Icc a t)))
    (hZcont : ContinuousOn Z (Set.Icc a r))
    (hcandidate_cont : ContinuousOn
      (weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F)
      (Set.Icc a r))
    (hZint : ∀ t ∈ Set.Icc a r, IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q) (Z q + F q))
      volume a t)
    (hZdamped : ∀ t ∈ Set.Icc a r,
      Z t = Real.exp (-(t - a)) •
          weightedMovingHeatL2Semigroup eta c (t - a) Z₀ +
        ∫ q in a..t, Real.exp (-(t - q)) •
          weightedMovingHeatL2Semigroup eta c (t - q) (Z q + F q))
    (hnested_int : ∀ t ∈ Set.Icc a r, IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q)
          (∫ s in a..q,
            weightedMovingHeatL2Semigroup eta c (q - s) (F s)))
      volume a t)
    (hdirect_int : ∀ t ∈ Set.Icc a r, IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q) (F q))
      volume a t)
    (hcomplement_int : ∀ t ∈ Set.Icc a r, IntervalIntegrable
      (fun s => (1 - Real.exp (-(t - s))) •
        weightedMovingHeatL2Semigroup eta c (t - s) (F s))
      volume a t)
    (hshort :
      Real.exp (|eta ^ 2 - c * eta| * (r - a)) * (r - a) < 1) :
    ∀ t ∈ Set.Icc a r,
      Z t = weightedMovingHeatL2Semigroup eta c (t - a) Z₀ +
        ∫ q in a..t,
          weightedMovingHeatL2Semigroup eta c (t - q) (F q) := by
  apply weightedMovingHeat_fullGenerator_restart_of_damped_triangleFubini_of_short
    har hZcont hcandidate_cont hZint hZdamped
      hnested_int hdirect_int hcomplement_int
  · intro t ht
    have hterminal : AEStronglyMeasurable
        (fun s => weightedMovingHeatL2Semigroup eta c (t - s) (F s))
        (volume.restrict (Set.Ioc a t)) :=
      (hhist_meas t ht).mono_measure
        (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)
    exact weightedMovingHeat_triangleFubini_of_uniform_norm_bound
      ht.1 hK (fun s hs => hF s ⟨hs.1, hs.2.trans ht.2⟩)
        (fun q hq => hhist_meas q ⟨hq.1, hq.2.trans ht.2⟩)
        (weightedMovingHeat_triangleKernel_aestronglyMeasurable_of_terminal_history
          hterminal)
  · exact hshort

/-- The preceding restart theorem with both scalar resolvent histories
constructed internally from the same forcing norm and terminal-history
data.  Only the genuinely nested history remains explicit. -/
theorem weightedMovingHeat_fullGenerator_restart_of_damped_uniform_forcing_histories_of_short
    {eta c a r K : ℝ}
    {Z F : ℝ → WholeLineRealL2} {Z₀ : WholeLineRealL2}
    (har : a ≤ r) (hK : 0 ≤ K)
    (hF : ∀ s ∈ Set.Icc a r, ‖F s‖ ≤ K)
    (hhist_meas : ∀ t ∈ Set.Icc a r,
      AEStronglyMeasurable
        (fun s => weightedMovingHeatL2Semigroup eta c (t - s) (F s))
        (volume.restrict (Set.Icc a t)))
    (hZcont : ContinuousOn Z (Set.Icc a r))
    (hcandidate_cont : ContinuousOn
      (weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F)
      (Set.Icc a r))
    (hZint : ∀ t ∈ Set.Icc a r, IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q) (Z q + F q))
      volume a t)
    (hZdamped : ∀ t ∈ Set.Icc a r,
      Z t = Real.exp (-(t - a)) •
          weightedMovingHeatL2Semigroup eta c (t - a) Z₀ +
        ∫ q in a..t, Real.exp (-(t - q)) •
          weightedMovingHeatL2Semigroup eta c (t - q) (Z q + F q))
    (hnested_int : ∀ t ∈ Set.Icc a r, IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q)
          (∫ s in a..q,
            weightedMovingHeatL2Semigroup eta c (q - s) (F s)))
      volume a t)
    (hshort :
      Real.exp (|eta ^ 2 - c * eta| * (r - a)) * (r - a) < 1) :
    ∀ t ∈ Set.Icc a r,
      Z t = weightedMovingHeatL2Semigroup eta c (t - a) Z₀ +
        ∫ q in a..t,
          weightedMovingHeatL2Semigroup eta c (t - q) (F q) := by
  have hscalarHistories : ∀ t ∈ Set.Icc a r,
      IntervalIntegrable
          (fun q => Real.exp (-(t - q)) •
            weightedMovingHeatL2Semigroup eta c (t - q) (F q))
          volume a t ∧
        IntervalIntegrable
          (fun q => (1 - Real.exp (-(t - q))) •
            weightedMovingHeatL2Semigroup eta c (t - q) (F q))
          volume a t := by
    intro t ht
    exact weightedMovingHeat_damped_histories_intervalIntegrable_of_uniform_norm_bound
      ht.1 hK (fun q hq => hF q ⟨hq.1, hq.2.trans ht.2⟩)
        (hhist_meas t ht)
  exact weightedMovingHeat_fullGenerator_restart_of_damped_uniform_forcing_of_short
    har hK hF hhist_meas hZcont hcandidate_cont hZint hZdamped hnested_int
      (fun t ht => (hscalarHistories t ht).1)
      (fun t ht => (hscalarHistories t ht).2) hshort

/-- All source-side histories, including the nested Duhamel history, are
constructed from the uniform forcing norm and terminal heat-history
measurability.  The remaining premises concern only the canonical damped
trajectory, continuity of the undamped candidate, and short-window
Volterra uniqueness. -/
theorem weightedMovingHeat_fullGenerator_restart_of_damped_uniform_forcing_all_histories_of_short
    {eta c a r K : ℝ}
    {Z F : ℝ → WholeLineRealL2} {Z₀ : WholeLineRealL2}
    (har : a ≤ r) (hK : 0 ≤ K)
    (hF : ∀ s ∈ Set.Icc a r, ‖F s‖ ≤ K)
    (hhist_meas : ∀ t ∈ Set.Icc a r,
      AEStronglyMeasurable
        (fun s => weightedMovingHeatL2Semigroup eta c (t - s) (F s))
        (volume.restrict (Set.Icc a t)))
    (hZcont : ContinuousOn Z (Set.Icc a r))
    (hcandidate_cont : ContinuousOn
      (weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F)
      (Set.Icc a r))
    (hZint : ∀ t ∈ Set.Icc a r, IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q) (Z q + F q))
      volume a t)
    (hZdamped : ∀ t ∈ Set.Icc a r,
      Z t = Real.exp (-(t - a)) •
          weightedMovingHeatL2Semigroup eta c (t - a) Z₀ +
        ∫ q in a..t, Real.exp (-(t - q)) •
          weightedMovingHeatL2Semigroup eta c (t - q) (Z q + F q))
    (hshort :
      Real.exp (|eta ^ 2 - c * eta| * (r - a)) * (r - a) < 1) :
    ∀ t ∈ Set.Icc a r,
      Z t = weightedMovingHeatL2Semigroup eta c (t - a) Z₀ +
        ∫ q in a..t,
          weightedMovingHeatL2Semigroup eta c (t - q) (F q) := by
  have hnested : ∀ t ∈ Set.Icc a r, IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q)
          (∫ s in a..q,
            weightedMovingHeatL2Semigroup eta c (q - s) (F s)))
      volume a t := by
    intro t ht
    have hinner : ∀ q ∈ Set.Icc a t, IntervalIntegrable
        (fun s => weightedMovingHeatL2Semigroup eta c (q - s) (F s))
        volume a q := by
      intro q hq
      exact weightedMovingHeatL2Semigroup_intervalIntegrable_of_uniform_norm_bound
        hq.1 hK (fun s hs => hF s ⟨hs.1, hs.2.trans (hq.2.trans ht.2)⟩)
          (hhist_meas q ⟨hq.1, hq.2.trans ht.2⟩)
    have hterminal : AEStronglyMeasurable
        (fun s => weightedMovingHeatL2Semigroup eta c (t - s) (F s))
        (volume.restrict (Set.Ioc a t)) :=
      (hhist_meas t ht).mono_measure
        (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)
    have htriMeas :=
      weightedMovingHeat_triangleKernel_aestronglyMeasurable_of_terminal_history
        hterminal
    have hproduct :=
      weightedMovingHeat_triangleKernel_integrable_of_uniform_norm_bound
        ht.1 hK (fun s hs => hF s ⟨hs.1.le, hs.2.trans ht.2⟩) htriMeas
    exact weightedMovingHeat_nested_damped_history_intervalIntegrable_of_triangleKernel
      ht.1 hinner hproduct
  exact weightedMovingHeat_fullGenerator_restart_of_damped_uniform_forcing_histories_of_short
    har hK hF hhist_meas hZcont hcandidate_cont hZint hZdamped hnested hshort

/-- The homogeneous weighted-heat orbit is continuous on every closed
forward time window, including its zero-lag endpoint.  At the endpoint this
is precisely strong continuity of the semigroup on `L²`; away from it the
already constructed positive-lag derivative gives ordinary continuity. -/
theorem weightedMovingHeatL2Semigroup_homogeneous_continuousOn
    {eta c a r : ℝ} (har : a ≤ r) (Z₀ : WholeLineRealL2) :
    ContinuousOn
      (fun t : ℝ => weightedMovingHeatL2Semigroup eta c (t - a) Z₀)
      (Set.Icc a r) := by
  intro t ht
  by_cases hta : t = a
  · subst t
    rw [Metric.continuousWithinAt_iff]
    intro eps heps
    have hzero := weightedMovingHeatL2Semigroup_tendsto_zero eta c Z₀
    have hevent := (Metric.tendsto_nhds.1 hzero) eps heps
    change {s : ℝ |
      dist (weightedMovingHeatL2Semigroup eta c s Z₀) Z₀ < eps} ∈
        𝓝[Set.Ioi (0 : ℝ)] 0 at hevent
    obtain ⟨delta, hdelta, hball⟩ :=
      Metric.mem_nhdsWithin_iff.mp hevent
    refine ⟨delta, hdelta, ?_⟩
    intro y hy hydist
    by_cases hya : y = a
    · simpa only [hya, sub_self, dist_self] using heps
    · have hay : a < y := lt_of_le_of_ne hy.1 (Ne.symm hya)
      have hlag_mem : y - a ∈ Metric.ball (0 : ℝ) delta ∩ Set.Ioi 0 := by
        constructor
        · rw [Metric.mem_ball, Real.dist_eq, sub_zero]
          exact hydist
        · exact sub_pos.mpr hay
      have hclose := hball hlag_mem
      simpa only [sub_self, weightedMovingHeatL2Semigroup_zero,
        ContinuousLinearMap.one_apply] using hclose
  · have hlag : t - a ≠ 0 := sub_ne_zero.mpr hta
    exact (ContinuousAt.comp
      (f := fun q : ℝ => q - a)
      (weightedMovingHeatL2Semigroup_orbit_continuousAt_of_ne_zero Z₀ hlag)
      (continuousAt_id.sub continuousAt_const)).continuousWithinAt

/-- Uniformly bounded measurable forcing gives continuity of the complete
undamped full-generator candidate on every compact window strictly inside
the ambient forcing window.  Thus continuity is not an independent analytic
input to damping removal. -/
theorem weightedMovingHeatFullGeneratorCandidate_continuousOn_of_uniform_norm_bound
    {eta c L R a r K : ℝ}
    (hLa : L < a) (har : a ≤ r) (hrR : r < R)
    {F : ℝ → WholeLineRealL2} (Z₀ : WholeLineRealL2)
    (hK : 0 ≤ K)
    (hF : ∀ q ∈ Set.Icc L R, ‖F q‖ ≤ K)
    (hhist_meas : ∀ t : ℝ, AEStronglyMeasurable
      (fun q => weightedMovingHeatL2Semigroup eta c (t - q) (F q))
      (volume.restrict (Set.uIoc L R))) :
    ContinuousOn
      (weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F)
      (Set.Icc a r) := by
  have hLR : L < R := hLa.trans_le (har.trans hrR.le)
  have hhom := weightedMovingHeatL2Semigroup_homogeneous_continuousOn
    (eta := eta) (c := c) har Z₀
  intro t ht
  have htLR : t ∈ Set.Ioo L R := by
    constructor <;> linarith [ht.1, ht.2]
  have hduhamel :=
    weightedMovingHeatL2Semigroup_duhamel_continuousAt_of_uniform_norm_bound
      (eta := eta) (c := c) hLR (show a ∈ Set.Ioo L R by
        constructor <;> linarith) htLR hK hF hhist_meas
  exact (hhom t ht).add hduhamel.continuousWithinAt

/-- Damping removal with no candidate-continuity premise.  A larger ambient
forcing window supplies both Duhamel continuity and all restricted terminal
histories on the restart window. -/
theorem weightedMovingHeat_fullGenerator_restart_of_damped_uniform_forcing_ambient_of_short
    {eta c L R a r K : ℝ}
    {Z F : ℝ → WholeLineRealL2} {Z₀ : WholeLineRealL2}
    (hLa : L < a) (har : a ≤ r) (hrR : r < R)
    (hK : 0 ≤ K)
    (hF : ∀ q ∈ Set.Icc L R, ‖F q‖ ≤ K)
    (hhist_meas : ∀ t : ℝ, AEStronglyMeasurable
      (fun q => weightedMovingHeatL2Semigroup eta c (t - q) (F q))
      (volume.restrict (Set.uIoc L R)))
    (hZcont : ContinuousOn Z (Set.Icc a r))
    (hZint : ∀ t ∈ Set.Icc a r, IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q) (Z q + F q))
      volume a t)
    (hZdamped : ∀ t ∈ Set.Icc a r,
      Z t = Real.exp (-(t - a)) •
          weightedMovingHeatL2Semigroup eta c (t - a) Z₀ +
        ∫ q in a..t, Real.exp (-(t - q)) •
          weightedMovingHeatL2Semigroup eta c (t - q) (Z q + F q))
    (hshort :
      Real.exp (|eta ^ 2 - c * eta| * (r - a)) * (r - a) < 1) :
    ∀ t ∈ Set.Icc a r,
      Z t = weightedMovingHeatL2Semigroup eta c (t - a) Z₀ +
        ∫ q in a..t,
          weightedMovingHeatL2Semigroup eta c (t - q) (F q) := by
  have hFsmall : ∀ q ∈ Set.Icc a r, ‖F q‖ ≤ K := by
    intro q hq
    exact hF q ⟨hLa.le.trans hq.1, hq.2.trans hrR.le⟩
  have hhist_small : ∀ t ∈ Set.Icc a r,
      AEStronglyMeasurable
        (fun q => weightedMovingHeatL2Semigroup eta c (t - q) (F q))
        (volume.restrict (Set.Icc a t)) := by
    intro t ht
    apply (hhist_meas t).mono_measure
    apply Measure.restrict_mono
    · intro q hq
      rw [Set.uIoc_of_le (hLa.trans_le (har.trans hrR.le)).le]
      exact ⟨hLa.trans_le hq.1, hq.2.trans (ht.2.trans hrR.le)⟩
    · exact le_rfl
  have hcandidate_cont :=
    weightedMovingHeatFullGeneratorCandidate_continuousOn_of_uniform_norm_bound
      (eta := eta) (c := c) hLa har hrR Z₀ hK hF hhist_meas
  exact
    weightedMovingHeat_fullGenerator_restart_of_damped_uniform_forcing_all_histories_of_short
      har hK hFsmall hhist_small hZcont hcandidate_cont hZint hZdamped hshort

section AxiomAudit

#print axioms wholeLineRealL2Total_norm_sq_eq_integral
#print axioms wholeLineRealL2Total_norm_le_sqrt_of_integral_sq_le
#print axioms weightedMovingHeatGrowth_le_exp_abs_mul_of_mem_Icc
#print axioms
  weightedMovingHeatL2Semigroup_intervalIntegrable_of_uniform_square_bound
#print axioms
  weightedMovingHeatEta_history_local_prod_integrable_of_uniform_square_bound
#print axioms
  weightedMovingHeat_generatorRestart_data_of_uniform_square_bound
#print axioms
  weightedMovingHeatL2Semigroup_mild_restart_eq_of_pointwise_total_of_uniform_square_bound
#print axioms
  weightedMovingHeatL2Semigroup_norm_apply_le_on_lag_window
#print axioms
  weightedMovingHeatL2Semigroup_intervalIntegrable_of_uniform_norm_bound
#print axioms
  weightedMovingHeat_damped_histories_intervalIntegrable_of_uniform_norm_bound
#print axioms
  exp_neg_smul_weightedMovingHeatL2Semigroup_norm_le_on_lag_window
#print axioms weightedMovingHeat_dampedVolterra_eq_zero_of_short
#print axioms weightedMovingHeat_dampedRestart_unique_of_short
#print axioms intervalIntegral_integral_triangle_swap_of_integrable
#print axioms intervalIntegral_exp_neg_sub
#print axioms weightedMovingHeat_triangleFubini_of_integrable
#print axioms
  weightedMovingHeat_triangleKernel_integrable_of_uniform_norm_bound
#print axioms
  weightedMovingHeat_nested_damped_history_intervalIntegrable_of_triangleKernel
#print axioms
  weightedMovingHeat_triangleKernel_aestronglyMeasurable_of_terminal_history
#print axioms weightedMovingHeat_triangleFubini_of_uniform_norm_bound
#print axioms weightedMovingHeat_homogeneous_damped_resolvent_identity
#print axioms
  weightedMovingHeat_homogeneous_damped_history_intervalIntegrable
#print axioms
  weightedMovingHeat_duhamel_damped_resolvent_identity_of_triangleFubini
#print axioms
  weightedMovingHeatFullGeneratorCandidate_damped_resolvent_identity_of_triangleFubini
#print axioms
  weightedMovingHeatFullGeneratorCandidate_damped_history_intervalIntegrable
#print axioms
  weightedMovingHeat_fullGenerator_restart_of_damped_resolvent_of_short
#print axioms
  weightedMovingHeat_fullGenerator_restart_of_damped_triangleFubini_of_short
#print axioms
  weightedMovingHeat_fullGenerator_restart_of_damped_uniform_forcing_of_short
#print axioms
  weightedMovingHeat_fullGenerator_restart_of_damped_uniform_forcing_histories_of_short
#print axioms
  weightedMovingHeat_fullGenerator_restart_of_damped_uniform_forcing_all_histories_of_short
#print axioms weightedMovingHeatL2Semigroup_homogeneous_continuousOn
#print axioms
  weightedMovingHeatFullGeneratorCandidate_continuousOn_of_uniform_norm_bound
#print axioms
  weightedMovingHeat_fullGenerator_restart_of_damped_uniform_forcing_ambient_of_short

end AxiomAudit

end ShenWork.Paper1
