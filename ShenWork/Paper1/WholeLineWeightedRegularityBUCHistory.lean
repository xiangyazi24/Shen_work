import ShenWork.Paper1.WholeLineWeightedRegularityL2History
import ShenWork.Paper1.WholeLineWeightedRegularityDQSources
import Mathlib.Topology.Hom.ContinuousEval

open Filter Topology MeasureTheory Set
open scoped BoundedContinuousFunction Interval

noncomputable section

namespace ShenWork.Paper1

private def wholeLineBUCSpatialCutoff
    (n : ℕ) (F : WholeLineBUC) (x : ℝ) : ℝ :=
  (Set.Icc (-(n : ℝ)) (n : ℝ)).indicator F.1 x

private theorem wholeLineBUCSpatialCutoff_aestronglyMeasurable
    (n : ℕ) (F : WholeLineBUC) :
    AEStronglyMeasurable (wholeLineBUCSpatialCutoff n F) volume := by
  exact F.1.continuous.aestronglyMeasurable.indicator measurableSet_Icc

private theorem wholeLineBUCSpatialCutoff_sq_integrable
    (n : ℕ) (F : WholeLineBUC) :
    Integrable (fun x : ℝ => wholeLineBUCSpatialCutoff n F x ^ 2) volume := by
  let A : Set ℝ := Set.Icc (-(n : ℝ)) (n : ℝ)
  have hbase : IntegrableOn (fun x : ℝ => F.1 x ^ 2) A volume := by
    refine Measure.integrableOn_of_bounded
      (s := A) (μ := volume) (f := fun x : ℝ => F.1 x ^ 2)
      (M := ‖F‖ ^ 2) ?_ ?_ ?_
    · simp [A, Real.volume_Icc]
    · exact F.1.continuous.pow 2 |>.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      rw [Real.norm_eq_abs, abs_sq]
      exact sq_le_sq.mpr (by
        simpa only [abs_of_nonneg (norm_nonneg F)] using
          WholeLineBUC.abs_apply_le_norm F x)
  have hi := hbase.integrable_indicator measurableSet_Icc
  refine hi.congr (Eventually.of_forall fun x => ?_)
  simp only [wholeLineBUCSpatialCutoff, Set.indicator_apply]
  split_ifs <;> simp

private theorem wholeLineBUCSpatialCutoff_sub_sq_integral_eq
    (n : ℕ) (F G : WholeLineBUC) :
    (∫ x : ℝ, (wholeLineBUCSpatialCutoff n F x -
        wholeLineBUCSpatialCutoff n G x) ^ 2) =
      ∫ x in Set.Icc (-(n : ℝ)) (n : ℝ), (F.1 x - G.1 x) ^ 2 := by
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [wholeLineBUCSpatialCutoff, Set.indicator_apply]
    split_ifs <;> simp

private theorem wholeLineBUCSpatialCutoff_sub_sq_integral_le
    (n : ℕ) (F G : WholeLineBUC) :
    (∫ x : ℝ, (wholeLineBUCSpatialCutoff n F x -
        wholeLineBUCSpatialCutoff n G x) ^ 2) ≤
      (2 * n : ℝ) * ‖F - G‖ ^ 2 := by
  rw [wholeLineBUCSpatialCutoff_sub_sq_integral_eq]
  have hcont : AEStronglyMeasurable (fun x : ℝ => (F.1 x - G.1 x) ^ 2) volume :=
    (F.1.continuous.sub G.1.continuous).pow 2 |>.aestronglyMeasurable
  have hfun : IntegrableOn (fun x : ℝ => (F.1 x - G.1 x) ^ 2)
      (Set.Icc (-(n : ℝ)) (n : ℝ)) volume := by
    refine Measure.integrableOn_of_bounded
      (s := Set.Icc (-(n : ℝ)) (n : ℝ)) (μ := volume)
      (f := fun x : ℝ => (F.1 x - G.1 x) ^ 2)
      (M := ‖F - G‖ ^ 2) ?_ hcont ?_
    · simp [Real.volume_Icc]
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      rw [Real.norm_eq_abs, abs_sq, ← sq_abs]
      have hpoint : |F.1 x - G.1 x| ≤ ‖F - G‖ := by
        simpa only [Pi.sub_apply] using WholeLineBUC.abs_apply_le_norm (F - G) x
      exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 hpoint
  have hconst : IntegrableOn (fun _x : ℝ => ‖F - G‖ ^ 2)
      (Set.Icc (-(n : ℝ)) (n : ℝ)) volume :=
    integrableOn_const (by simp [Real.volume_Icc])
  calc
    (∫ x in Set.Icc (-(n : ℝ)) (n : ℝ), (F.1 x - G.1 x) ^ 2) ≤
        ∫ _x in Set.Icc (-(n : ℝ)) (n : ℝ), ‖F - G‖ ^ 2 := by
      apply setIntegral_mono_on hfun hconst
      · exact measurableSet_Icc
      · intro x hx
        have hpoint : |F.1 x - G.1 x| ≤ ‖F - G‖ := by
          simpa only [Pi.sub_apply] using WholeLineBUC.abs_apply_le_norm (F - G) x
        rw [← sq_abs]
        exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 hpoint
    _ = (2 * n : ℝ) * ‖F - G‖ ^ 2 := by
      rw [setIntegral_const, Measure.real_def, Real.volume_Icc]
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [ENNReal.toReal_ofReal (by linarith :
        (0 : ℝ) ≤ (n : ℝ) - -(n : ℝ))]
      simp only [smul_eq_mul]
      ring

private theorem wholeLineBUC_norm_sub_eq_dist (F G : WholeLineBUC) :
    ‖F - G‖ = dist F G := by
  change ‖(F - G).1‖ = dist F.1 G.1
  change ‖F.1 - G.1‖ = dist F.1 G.1
  exact (dist_eq_norm F.1 G.1).symm

private theorem wholeLineRealL2Section_cutoff_continuous
    (n : ℕ) {F : ℝ → WholeLineBUC} (hF : Continuous F) :
    Continuous (wholeLineRealL2Section
      (fun s x => wholeLineBUCSpatialCutoff n (F s) x)
      (fun s => wholeLineBUCSpatialCutoff_aestronglyMeasurable n (F s))
      (fun s => wholeLineBUCSpatialCutoff_sq_integrable n (F s))) := by
  apply wholeLineRealL2Section_continuous_of_integral_sub_sq_tendsto_zero
  intro t
  apply squeeze_zero
  · intro s
    exact integral_nonneg fun _x => sq_nonneg _
  · intro s
    exact wholeLineBUCSpatialCutoff_sub_sq_integral_le n (F s) (F t)
  · have hnorm : Tendsto (fun s => ‖F s - F t‖)
        (nhds t) (nhds 0) := by
      simpa only [wholeLineBUC_norm_sub_eq_dist, dist_self] using
        (hF.continuousAt.dist
          (continuousAt_const : ContinuousAt (fun _s : ℝ => F t) t))
    have hsq : Tendsto (fun s => ‖F s - F t‖ ^ 2)
        (nhds t) (nhds 0) := by
      simpa only [zero_pow (by norm_num : 2 ≠ 0)] using hnorm.pow 2
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hsq : Tendsto
        (fun s => (2 * n : ℝ) * ‖F s - F t‖ ^ 2)
        (nhds t) (nhds ((2 * n : ℝ) * 0)))

private theorem wholeLineBUCSpatialCutoff_eventually_eq
    (F : WholeLineBUC) (x : ℝ) :
    ∀ᶠ n : ℕ in atTop, wholeLineBUCSpatialCutoff n F x = F.1 x := by
  rcases exists_nat_ge |x| with ⟨N, hN⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  have hxabs : |x| ≤ (n : ℝ) := hN.trans (Nat.cast_le.mpr hn)
  have hx : x ∈ Set.Icc (-(n : ℝ)) (n : ℝ) := by
    exact ⟨by linarith [neg_abs_le x], (le_abs_self x).trans hxabs⟩
  exact Set.indicator_of_mem hx _

private theorem wholeLineRealL2OfSqIntegrable_norm_sub_sq
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

private theorem wholeLineRealL2Section_cutoff_tendsto
    {F : ℝ → WholeLineBUC}
    (hF2 : ∀ s, Integrable (fun x : ℝ => F s |>.1 x ^ 2) volume)
    (s : ℝ) :
    Tendsto
      (fun n => wholeLineRealL2Section
        (fun _s x => wholeLineBUCSpatialCutoff n (F s) x)
        (fun _s => wholeLineBUCSpatialCutoff_aestronglyMeasurable n (F s))
        (fun _s => wholeLineBUCSpatialCutoff_sq_integrable n (F s)) s)
      atTop
      (nhds (wholeLineRealL2Section
        (fun s x => F s |>.1 x)
        (fun s => (F s).1.continuous.aestronglyMeasurable)
        hF2 s)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hint : Tendsto
      (fun n => ∫ x : ℝ,
        (wholeLineBUCSpatialCutoff n (F s) x - (F s).1 x) ^ 2)
      atTop (nhds 0) := by
    have hdom := tendsto_integral_of_dominated_convergence
      (F := fun n x =>
        (wholeLineBUCSpatialCutoff n (F s) x - (F s).1 x) ^ 2)
      (f := fun _x : ℝ => 0)
      (fun x : ℝ => (F s).1 x ^ 2)
      (fun n => by
        exact (((wholeLineBUCSpatialCutoff_aestronglyMeasurable n (F s)).sub
          (F s).1.continuous.aestronglyMeasurable).pow 2))
      (hF2 s)
      (fun n => Eventually.of_forall fun x => by
        change |(wholeLineBUCSpatialCutoff n (F s) x - (F s).1 x) ^ 2| ≤
          (F s).1 x ^ 2
        rw [abs_sq]
        by_cases hx : x ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
        · rw [wholeLineBUCSpatialCutoff, Set.indicator_of_mem hx]
          simpa using sq_nonneg ((F s).1 x)
        · rw [wholeLineBUCSpatialCutoff, Set.indicator_of_notMem hx]
          simp)
      (Eventually.of_forall fun x => by
        apply tendsto_const_nhds.congr'
        filter_upwards [wholeLineBUCSpatialCutoff_eventually_eq (F s) x]
          with n hn
        rw [hn, sub_self, zero_pow (by norm_num : 2 ≠ 0)])
    simpa only [integral_zero] using hdom
  have hsq : Tendsto
      (fun n => ‖wholeLineRealL2Section
          (fun _s x => wholeLineBUCSpatialCutoff n (F s) x)
          (fun _s => wholeLineBUCSpatialCutoff_aestronglyMeasurable n (F s))
          (fun _s => wholeLineBUCSpatialCutoff_sq_integrable n (F s)) s -
        wholeLineRealL2Section
          (fun s x => (F s).1 x)
          (fun s => (F s).1.continuous.aestronglyMeasurable)
          hF2 s‖ ^ 2) atTop (nhds 0) := by
    have heq : ∀ n,
        ‖wholeLineRealL2Section
            (fun _s x => wholeLineBUCSpatialCutoff n (F s) x)
            (fun _s => wholeLineBUCSpatialCutoff_aestronglyMeasurable n (F s))
            (fun _s => wholeLineBUCSpatialCutoff_sq_integrable n (F s)) s -
          wholeLineRealL2Section
            (fun s x => (F s).1 x)
            (fun s => (F s).1.continuous.aestronglyMeasurable)
            hF2 s‖ ^ 2 =
          ∫ x : ℝ,
            (wholeLineBUCSpatialCutoff n (F s) x - (F s).1 x) ^ 2 := by
      intro n
      exact wholeLineRealL2OfSqIntegrable_norm_sub_sq
        _ _ _ _ _ _
    exact hint.congr' (Eventually.of_forall fun n => (heq n).symm)
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  have hsqrt' : Tendsto
      (fun n => Real.sqrt (‖wholeLineRealL2Section
          (fun _s x => wholeLineBUCSpatialCutoff n (F s) x)
          (fun _s => wholeLineBUCSpatialCutoff_aestronglyMeasurable n (F s))
          (fun _s => wholeLineBUCSpatialCutoff_sq_integrable n (F s)) s -
        wholeLineRealL2Section
          (fun s x => (F s).1 x)
          (fun s => (F s).1.continuous.aestronglyMeasurable)
          hF2 s‖ ^ 2)) atTop (nhds 0) := by
    simpa only [Real.sqrt_zero] using hsqrt
  exact hsqrt'.congr' (Eventually.of_forall fun n => by
    rw [Real.sqrt_sq (norm_nonneg _)])

/-- A continuous BUC-valued history with square-integrable slices has a
canonical strongly measurable `L²(ℝ)` history.  No `L²` continuity in time is
assumed: compact spatial cutoffs provide measurable approximants. -/
theorem wholeLineRealL2Section_aestronglyMeasurable_of_continuous_buc
    {F : ℝ → WholeLineBUC} (hF : Continuous F)
    (hF2 : ∀ s, Integrable (fun x : ℝ => (F s).1 x ^ 2) volume) :
    AEStronglyMeasurable
      (wholeLineRealL2Section
        (fun s x => (F s).1 x)
        (fun s => (F s).1.continuous.aestronglyMeasurable)
        hF2) volume := by
  have hmeas : ∀ n, StronglyMeasurable
      (wholeLineRealL2Section
        (fun s x => wholeLineBUCSpatialCutoff n (F s) x)
        (fun s => wholeLineBUCSpatialCutoff_aestronglyMeasurable n (F s))
        (fun s => wholeLineBUCSpatialCutoff_sq_integrable n (F s))) := fun n =>
    (wholeLineRealL2Section_cutoff_continuous n hF).stronglyMeasurable
  exact (stronglyMeasurable_of_tendsto atTop hmeas
    (tendsto_pi_nhds.2 fun s => wholeLineRealL2Section_cutoff_tendsto hF2 s)).aestronglyMeasurable

private theorem wholeLineRealL2Section_cutoff_continuousOn_Iio
    (n : ℕ) {F : ℝ → WholeLineBUC} {T : ℝ}
    (hF : ContinuousOn F (Set.Iio T)) :
    ContinuousOn (wholeLineRealL2Section
      (fun s x => wholeLineBUCSpatialCutoff n (F s) x)
      (fun s => wholeLineBUCSpatialCutoff_aestronglyMeasurable n (F s))
      (fun s => wholeLineBUCSpatialCutoff_sq_integrable n (F s)))
      (Set.Iio T) := by
  intro t ht
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hint : Tendsto
      (fun s => ∫ x : ℝ,
        (wholeLineBUCSpatialCutoff n (F s) x -
          wholeLineBUCSpatialCutoff n (F t) x) ^ 2)
      (nhdsWithin t (Set.Iio T)) (nhds 0) := by
    apply squeeze_zero
    · intro s
      exact integral_nonneg fun _x => sq_nonneg _
    · intro s
      exact wholeLineBUCSpatialCutoff_sub_sq_integral_le n (F s) (F t)
    · have hdist : Tendsto (fun s => dist (F s) (F t))
          (nhdsWithin t (Set.Iio T)) (nhds 0) := by
        simpa only [dist_self] using
          ((hF t ht).dist (continuousWithinAt_const :
            ContinuousWithinAt (fun _s : ℝ => F t) (Set.Iio T) t))
      have hnorm : Tendsto (fun s => ‖F s - F t‖)
          (nhdsWithin t (Set.Iio T)) (nhds 0) := by
        simpa only [wholeLineBUC_norm_sub_eq_dist] using hdist
      have hsq : Tendsto (fun s => ‖F s - F t‖ ^ 2)
          (nhdsWithin t (Set.Iio T)) (nhds 0) := by
        simpa only [zero_pow (by norm_num : 2 ≠ 0)] using hnorm.pow 2
      simpa only [mul_zero] using
        (tendsto_const_nhds.mul hsq : Tendsto
          (fun s => (2 * n : ℝ) * ‖F s - F t‖ ^ 2)
          (nhdsWithin t (Set.Iio T)) (nhds ((2 * n : ℝ) * 0)))
  have hsq : Tendsto
      (fun s => ‖wholeLineRealL2Section
        (fun s x => wholeLineBUCSpatialCutoff n (F s) x)
        (fun s => wholeLineBUCSpatialCutoff_aestronglyMeasurable n (F s))
        (fun s => wholeLineBUCSpatialCutoff_sq_integrable n (F s)) s -
        wholeLineRealL2Section
          (fun s x => wholeLineBUCSpatialCutoff n (F s) x)
          (fun s => wholeLineBUCSpatialCutoff_aestronglyMeasurable n (F s))
          (fun s => wholeLineBUCSpatialCutoff_sq_integrable n (F s)) t‖ ^ 2)
      (nhdsWithin t (Set.Iio T)) (nhds 0) := by
    simpa only [wholeLineRealL2Section_norm_sub_sq] using hint
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  have hsqrt' : Tendsto
      (fun s => Real.sqrt (‖wholeLineRealL2Section
        (fun s x => wholeLineBUCSpatialCutoff n (F s) x)
        (fun s => wholeLineBUCSpatialCutoff_aestronglyMeasurable n (F s))
        (fun s => wholeLineBUCSpatialCutoff_sq_integrable n (F s)) s -
        wholeLineRealL2Section
          (fun s x => wholeLineBUCSpatialCutoff n (F s) x)
          (fun s => wholeLineBUCSpatialCutoff_aestronglyMeasurable n (F s))
          (fun s => wholeLineBUCSpatialCutoff_sq_integrable n (F s)) t‖ ^ 2))
      (nhdsWithin t (Set.Iio T)) (nhds 0) := by
    simpa only [Real.sqrt_zero] using hsqrt
  exact hsqrt'.congr' (Eventually.of_forall fun s => by
    rw [Real.sqrt_sq (norm_nonneg _)])

/-- Local version for positive-lag Duhamel histories.  Continuity is needed
only before the terminal time; the terminal singular slice is not included
in the restricted measure. -/
theorem wholeLineRealL2Section_aestronglyMeasurableOn_Iio_of_continuousOn_buc
    {t : ℝ} {F : ℝ → WholeLineBUC} (hF : ContinuousOn F (Set.Iio t))
    (hF2 : ∀ s, Integrable (fun x : ℝ => (F s).1 x ^ 2) volume) :
    AEStronglyMeasurable
      (wholeLineRealL2Section
        (fun s x => (F s).1 x)
        (fun s => (F s).1.continuous.aestronglyMeasurable)
        hF2) (volume.restrict (Set.Iio t)) := by
  let Z : ℝ → WholeLineRealL2 := wholeLineRealL2Section
    (fun s x => (F s).1 x)
    (fun s => (F s).1.continuous.aestronglyMeasurable) hF2
  let Zn : ℕ → ℝ → WholeLineRealL2 := fun n => wholeLineRealL2Section
    (fun s x => wholeLineBUCSpatialCutoff n (F s) x)
    (fun s => wholeLineBUCSpatialCutoff_aestronglyMeasurable n (F s))
    (fun s => wholeLineBUCSpatialCutoff_sq_integrable n (F s))
  have hmeas : ∀ n, AEStronglyMeasurable (Zn n)
      (volume.restrict (Set.Iio t)) := fun n =>
    (wholeLineRealL2Section_cutoff_continuousOn_Iio n hF).aestronglyMeasurable
      measurableSet_Iio
  have hlim : ∀ s, Tendsto (fun n => Zn n s) atTop (nhds (Z s)) := by
    intro s
    exact wholeLineRealL2Section_cutoff_tendsto hF2 s
  exact aestronglyMeasurable_of_tendsto_ae atTop hmeas
    (Eventually.of_forall hlim)

/-- Totalize a positive-lag `L²` history by zero at and after its terminal
time.  The result is globally strongly measurable, hence usable directly in
an interval integral. -/
theorem wholeLineRealL2Section_Iio_totalized_aestronglyMeasurable
    {t : ℝ} {F : ℝ → WholeLineBUC} (hF : ContinuousOn F (Set.Iio t))
    (hF2 : ∀ s, Integrable (fun x : ℝ => (F s).1 x ^ 2) volume) :
    AEStronglyMeasurable
      (fun s => if s < t then
        wholeLineRealL2Section
          (fun q x => (F q).1 x)
          (fun q => (F q).1.continuous.aestronglyMeasurable)
          hF2 s
        else 0) volume := by
  let Z : ℝ → WholeLineRealL2 := wholeLineRealL2Section
    (fun s x => (F s).1 x)
    (fun s => (F s).1.continuous.aestronglyMeasurable) hF2
  have hZIio : AEStronglyMeasurable Z (volume.restrict (Set.Iio t)) :=
    wholeLineRealL2Section_aestronglyMeasurableOn_Iio_of_continuousOn_buc hF hF2
  have hind : AEStronglyMeasurable ((Set.Iio t).indicator Z) volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Iio).2 hZIio
  exact hind.congr (Eventually.of_forall fun s => by
    simp only [Set.indicator_apply, Set.mem_Iio]
    split_ifs <;> rfl)

/-- Interval-integrability of the totalized history from an explicit scalar
majorant. -/
theorem wholeLineRealL2Section_Iio_totalized_intervalIntegrable_of_majorant
    {t : ℝ} (ht : 0 ≤ t)
    {F : ℝ → WholeLineBUC} (hF : ContinuousOn F (Set.Iio t))
    (hF2 : ∀ s, Integrable (fun x : ℝ => (F s).1 x ^ 2) volume)
    {q : ℝ → ℝ} (hq_int : IntervalIntegrable q volume 0 t)
    (hq_nonneg : ∀ s ∈ Set.Icc (0 : ℝ) t, 0 ≤ q s)
    (hmajor : ∀ s ∈ Set.Icc (0 : ℝ) t, s < t →
      ‖wholeLineRealL2Section
        (fun q x => (F q).1 x)
        (fun q => (F q).1.continuous.aestronglyMeasurable)
        hF2 s‖ ≤ q s) :
    IntervalIntegrable
      (fun s => if s < t then
        wholeLineRealL2Section
          (fun q x => (F q).1 x)
          (fun q => (F q).1.continuous.aestronglyMeasurable)
          hF2 s
        else 0) volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht] at hq_int ⊢
  apply Integrable.mono' hq_int
  · exact (wholeLineRealL2Section_Iio_totalized_aestronglyMeasurable
      hF hF2).restrict
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    split_ifs with hst
    · exact hmajor s hs hst
    · simpa using hq_nonneg s hs

/-- A Bochner-integrable BUC history is jointly locally integrable after
spatial restriction to any finite-measure set.  This is the concrete
product-integrability input needed by the canonical `L²` Fubini bridge. -/
theorem wholeLineBUCHistory_local_prod_integrable
    {μ : Measure ℝ} [SFinite μ]
    {F : ℝ → WholeLineBUC}
    (hFmeas : AEStronglyMeasurable F μ)
    (hFnorm : Integrable (fun s => ‖F s‖) μ)
    (A : Set ℝ) (hA : MeasurableSet A)
    (hAfin : (volume : Measure ℝ) A < ⊤) :
    Integrable
      (fun z : ℝ × ℝ => A.indicator (F z.1).1 z.2)
      (μ.prod volume) := by
  let S : Set (ℝ × ℝ) := Prod.snd ⁻¹' A
  let raw : ℝ × ℝ → ℝ := fun z => (F z.1).1 z.2
  have hraw : AEStronglyMeasurable raw (μ.prod volume) := by
    have hamb : AEStronglyMeasurable
        (fun z : ℝ × ℝ => (F z.1).1) (μ.prod volume) :=
      wholeLineBUCSubmodule.subtypeL.continuous.comp_aestronglyMeasurable
        hFmeas.comp_fst
    exact continuous_eval.comp_aestronglyMeasurable
      (hamb.prodMk measurable_snd.aestronglyMeasurable)
  have hS : MeasurableSet S := hA.preimage measurable_snd
  have htarget : AEStronglyMeasurable
      (fun z : ℝ × ℝ => A.indicator (F z.1).1 z.2)
      (μ.prod volume) := by
    have hi := hraw.indicator hS
    refine hi.congr (Eventually.of_forall fun z => ?_)
    by_cases hz : z.2 ∈ A
    · simp [S, raw, hz]
    · simp [S, raw, hz]
  let oneA : ℝ → ℝ := A.indicator (fun _ => (1 : ℝ))
  have honeA : Integrable oneA volume := by
    exact (integrableOn_const hAfin.ne).integrable_indicator hA
  have hmajor : Integrable
      (fun z : ℝ × ℝ => ‖F z.1‖ * oneA z.2)
      (μ.prod volume) := hFnorm.mul_prod honeA
  refine Integrable.mono' hmajor htarget ?_
  exact Eventually.of_forall fun z => by
    by_cases hz : z.2 ∈ A
    · simp only [Set.indicator_of_mem hz, oneA, Real.norm_eq_abs, mul_one]
      exact WholeLineBUC.abs_apply_le_norm (F z.1) z.2
    · simp [oneA, hz]

/-- The Bochner integral of a canonical square-integrable BUC history has
the expected pointwise representative.  Only BUC-history integrability and
slice `L²` membership are used; no global spatial `L¹` assumption appears. -/
theorem wholeLineRealL2_intervalIntegral_coe_ae_of_buc_history
    {a b : ℝ} (hab : a ≤ b)
    {F : ℝ → WholeLineBUC}
    (hFmeas : AEStronglyMeasurable F
      (volume.restrict (Set.Ioc a b)))
    (hFnorm : Integrable (fun s => ‖F s‖)
      (volume.restrict (Set.Ioc a b)))
    (hF2 : ∀ s, Integrable (fun x : ℝ => (F s).1 x ^ 2) volume)
    (hZint : IntervalIntegrable
      (wholeLineRealL2Section
        (fun s x => (F s).1 x)
        (fun s => (F s).1.continuous.aestronglyMeasurable)
        hF2) volume a b) :
    ((((∫ s in a..b, wholeLineRealL2Section
        (fun s x => (F s).1 x)
        (fun s => (F s).1.continuous.aestronglyMeasurable)
        hF2 s) : WholeLineRealL2) : ℝ → ℝ)
      =ᵐ[volume] fun x => ∫ s in a..b, (F s).1 x) := by
  apply wholeLineRealL2_intervalIntegral_coe_ae_of_local_prod_integrable
    hab hZint
  · exact Eventually.of_forall fun s =>
      wholeLineRealL2Section_coe_ae
        (fun s x => (F s).1 x)
        (fun s => (F s).1.continuous.aestronglyMeasurable)
        hF2 s
  · intro A hA hAfin
    exact wholeLineBUCHistory_local_prod_integrable
      hFmeas hFnorm A hA hAfin


#print axioms ShenWork.Paper1.wholeLineBUCHistory_local_prod_integrable
#print axioms
  ShenWork.Paper1.wholeLineRealL2_intervalIntegral_coe_ae_of_buc_history

#print axioms
  wholeLineRealL2Section_aestronglyMeasurableOn_Iio_of_continuousOn_buc
#print axioms wholeLineRealL2Section_Iio_totalized_aestronglyMeasurable
#print axioms
  wholeLineRealL2Section_Iio_totalized_intervalIntegrable_of_majorant

#print axioms wholeLineRealL2Section_aestronglyMeasurable_of_continuous_buc

end ShenWork.Paper1
