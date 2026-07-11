/-
  Positive-lag target-time differentiation for the interval conjugate operator.

  A conjugate slice is factored at half of the target lag as an ordinary
  Neumann heat step applied to a fixed, already-smoothed conjugate slice.  The
  existing heat generator identity then gives the time derivative.  The same
  factorisation supplies a lower-lag-uniform bound, and dominated convergence
  differentiates a fixed old-history integral ending strictly before the
  target time.
-/
import ShenWork.Paper2.IntervalConjugateSemigroupSecondDeriv
import ShenWork.Paper2.IntervalFullSemigroupTimeDerivative
import ShenWork.Paper2.IntervalConjugateChemFluxIntegrable

open MeasureTheory Filter Set Topology
open scoped Topology

noncomputable section

namespace ShenWork.Paper2

open ShenWork.IntervalDomain (intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator)
open ShenWork.IntervalConjugateChemFluxIntegrable
  (conjugateDuhamel_intervalIntegrable_of_measurable_bound)

/-- At every positive lag, the target-time derivative of the conjugate
operator is its literal second spatial derivative, including at the two
Neumann endpoints. -/
theorem intervalConjugateKernelOperator_hasDerivAt_time_secondDeriv_Icc
    {r : ℝ} (hr : 0 < r) {Q : ℝ → ℝ} (hQcont : Continuous Q)
    (hQint : Integrable Q (intervalMeasure 1)) {CQ : ℝ}
    (hQbound : ∀ y, |Q y| ≤ CQ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt
      (fun q : ℝ => intervalConjugateKernelOperator q Q x)
      (deriv (fun y : ℝ => deriv
        (fun z : ℝ => intervalConjugateKernelOperator r Q z) y) x)
      r := by
  have hr2 : 0 < r / 2 := by positivity
  let B : ℝ → ℝ := fun z => intervalConjugateKernelOperator (r / 2) Q z
  have hBdiff : Differentiable ℝ B := fun z =>
    (ShenWork.IntervalConjugateDuhamelMap.intervalConjugateKernelOperator_hasDerivAt
      hr2 hQint hQbound z).differentiableAt
  have hBcont : Continuous B := hBdiff.continuous
  obtain ⟨M, hM⟩ :=
    intervalConjugateKernelOperator_cosineCoeff_bounded hr2 hQcont
  have hheat := intervalFullSemigroupOperator_hasDerivAt_time_secondDeriv_Icc
    (t := r / 2) (x := x) hr2 hBcont hM hx
  have hheat' :
      HasDerivAt
        (fun q : ℝ => intervalFullSemigroupOperator q B x)
        (deriv (fun y : ℝ => deriv
          (fun z : ℝ => intervalFullSemigroupOperator (r / 2) B z) y) x)
        (r - r / 2) := by
    simpa only [show r - r / 2 = r / 2 by ring] using hheat
  have hshift : HasDerivAt (fun q : ℝ => q - r / 2) 1 r :=
    (hasDerivAt_id r).sub_const (r / 2)
  have hfactored :
      HasDerivAt
        (fun q : ℝ => intervalFullSemigroupOperator (q - r / 2) B x)
        (deriv (fun y : ℝ => deriv
          (fun z : ℝ => intervalFullSemigroupOperator (r / 2) B z) y) x)
        r := by
    simpa using hheat'.comp r hshift
  have htimeEq :
      (fun q : ℝ => intervalFullSemigroupOperator (q - r / 2) B x) =ᶠ[nhds r]
        (fun q : ℝ => intervalConjugateKernelOperator q Q x) := by
    filter_upwards [Ioi_mem_nhds (by linarith : r / 2 < r)] with q hq
    have hlag : 0 < q - r / 2 := sub_pos.mpr hq
    simpa [B, show q - r / 2 + r / 2 = q by ring] using
      intervalFullSemigroupOperator_comp_conjugateKernel
        hlag hr2 hQcont hQint hQbound hx
  have hspaceEq :
      (fun z : ℝ => intervalFullSemigroupOperator (r / 2) B z) =ᶠ[nhds x]
        (fun z : ℝ => intervalConjugateKernelOperator r Q z) := by
    simpa [B] using
      intervalFullSemigroup_comp_conjugate_eventuallyEq_Icc
        hr hQcont hQint hQbound hx
  have hsecondEq :
      deriv (fun y : ℝ => deriv
        (fun z : ℝ => intervalFullSemigroupOperator (r / 2) B z) y) x =
        deriv (fun y : ℝ => deriv
          (fun z : ℝ => intervalConjugateKernelOperator r Q z) y) x :=
    hspaceEq.deriv.deriv_eq
  rw [← hsecondEq]
  exact hfactored.congr_of_eventuallyEq htimeEq.symm

/-- A positive lower lag gives one constant dominating the actual target-time
derivative of every later conjugate slice. -/
theorem intervalConjugateKernelOperator_timeDeriv_abs_le_of_lower
    {d r : ℝ} (hd : 0 < d) (hdr : d ≤ r)
    {Q : ℝ → ℝ} (hQcont : Continuous Q)
    (hQint : Integrable Q (intervalMeasure 1)) {CQ : ℝ}
    (hQbound : ∀ y, |Q y| ≤ CQ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |deriv (fun q : ℝ => intervalConjugateKernelOperator q Q x) r| ≤
      (5 * Real.sqrt 2 / 2) * (d / 2) ^ (-(1 : ℝ)) *
        (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
          (d / 2) ^ (-(1 / 2) : ℝ) * CQ) := by
  have hr : 0 < r := hd.trans_le hdr
  have hd2 : 0 < d / 2 := by positivity
  have hhalf : d / 2 ≤ r / 2 := by linarith
  have hp1 : (r / 2) ^ (-(1 : ℝ)) ≤ (d / 2) ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hd2 hhalf (by norm_num)
  have hp2 : (r / 2) ^ (-(1 / 2) : ℝ) ≤ (d / 2) ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hd2 hhalf (by norm_num)
  have hCQ : 0 ≤ CQ := (abs_nonneg (Q 0)).trans (hQbound 0)
  rw [(intervalConjugateKernelOperator_hasDerivAt_time_secondDeriv_Icc
    hr hQcont hQint hQbound hx).deriv]
  refine (intervalConjugateKernelOperator_secondDeriv_abs_le_of_split_Icc
    hr hQcont hQint hQbound hx).trans ?_
  have hCmix : 0 ≤ 5 * Real.sqrt 2 / 2 := by positivity
  have hCg : 0 ≤
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left hp1 hCmix)
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp2 hCg) hCQ)
    (mul_nonneg (mul_nonneg hCg (Real.rpow_nonneg (by positivity) _)) hCQ)
    (mul_nonneg hCmix (Real.rpow_nonneg (by positivity) _))

/-- For a fixed bounded continuous flux, the actual target-time derivative of
the conjugate operator is continuous throughout the positive-lag half-line. -/
theorem intervalConjugateKernelOperator_timeDeriv_continuousOn_Ioi
    {Q : ℝ → ℝ} (hQcont : Continuous Q)
    (hQint : Integrable Q (intervalMeasure 1)) {CQ : ℝ}
    (hQbound : ∀ y, |Q y| ≤ CQ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousOn
      (fun r : ℝ => deriv
        (fun q : ℝ => intervalConjugateKernelOperator q Q x) r)
      (Set.Ioi (0 : ℝ)) := by
  intro r hr
  have hrpos : 0 < r := hr
  let b : ℝ := r / 2
  have hb : 0 < b := by dsimp [b]; positivity
  have hbr : b < r := by dsimp [b]; linarith
  let B : ℝ → ℝ := fun z => intervalConjugateKernelOperator b Q z
  have hBdiff : Differentiable ℝ B := fun z =>
    (ShenWork.IntervalConjugateDuhamelMap.intervalConjugateKernelOperator_hasDerivAt
      hb hQint hQbound z).differentiableAt
  have hBcont : Continuous B := hBdiff.continuous
  obtain ⟨M, hM⟩ :=
    intervalConjugateKernelOperator_cosineCoeff_bounded hb hQcont
  have hfactor : Set.EqOn
      (fun q : ℝ => intervalConjugateKernelOperator q Q x)
      (fun q : ℝ => intervalFullSemigroupOperator (q - b) B x)
      (Set.Ioi b) := by
    intro q hq
    have hlag : 0 < q - b := sub_pos.mpr hq
    symm
    simpa [B, show q - b + b = q by ring] using
      intervalFullSemigroupOperator_comp_conjugateKernel
        hlag hb hQcont hQint hQbound hx
  have hderivEq : Set.EqOn
      (fun q : ℝ => deriv
        (fun w : ℝ => intervalConjugateKernelOperator w Q x) q)
      (fun q : ℝ =>
        ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondValue
          (q - b) (cosineCoeffs B) x)
      (Set.Ioi b) := by
    intro q hq
    have hlag : 0 < q - b := sub_pos.mpr hq
    have hev :
        (fun w : ℝ => intervalConjugateKernelOperator w Q x) =ᶠ[nhds q]
          (fun w : ℝ => intervalFullSemigroupOperator (w - b) B x) := by
      filter_upwards [Ioi_mem_nhds hq] with w hw
      exact hfactor hw
    have hbase := intervalFullSemigroupOperator_hasDerivAt_time_secondDeriv_Icc
      (t := q - b) (x := x) hlag hBcont hM hx
    have hshift : HasDerivAt (fun w : ℝ => w - b) 1 q :=
      (hasDerivAt_id q).sub_const b
    have hshifted := hbase.comp q hshift
    calc
      deriv (fun w : ℝ => intervalConjugateKernelOperator w Q x) q =
          deriv (fun w : ℝ => intervalFullSemigroupOperator (w - b) B x) q :=
        hev.deriv_eq
      _ = deriv (fun y : ℝ => deriv
          (fun z : ℝ => intervalFullSemigroupOperator (q - b) B z) y) x :=
        by simpa [Function.comp_apply] using hshifted.deriv
      _ = ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondValue
          (q - b) (cosineCoeffs B) x :=
        ShenWork.Paper2.intervalFullSemigroupOperator_secondDeriv_eq_secondValue_Icc
          hlag hBcont hM hx
  have hsecondCont : ContinuousOn
      (fun q : ℝ =>
        ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondValue
          (q - b) (cosineCoeffs B) x)
      (Set.Ioi b) := by
    have hprod :=
      ShenWork.IntervalSemigroupNeumann.unitIntervalCosineHeatSecondValue_continuousOn_Ioi_prod
        hM
    exact hprod.comp
      (by fun_prop : Continuous (fun q : ℝ => (q - b, x))).continuousOn
      (by
        intro q hq
        exact ⟨by simpa using (sub_pos.mpr (Set.mem_Ioi.mp hq)), Set.mem_univ _⟩)
  have hlocal : ContinuousOn
      (fun q : ℝ => deriv
        (fun w : ℝ => intervalConjugateKernelOperator w Q x) q)
      (Set.Ioi b) :=
    hsecondCont.congr fun q hq => hderivEq hq
  exact (hlocal.continuousAt (Ioi_mem_nhds hbr)).continuousWithinAt

private def conjugateOldValueIntegrand
    (Q : ℝ → ℝ → ℝ) (r s x : ℝ) : ℝ :=
  intervalConjugateKernelOperator (r - s) (Q s) x

private def conjugateOldHessIntegrand
    (Q : ℝ → ℝ → ℝ) (r s x : ℝ) : ℝ :=
  deriv (fun y : ℝ => deriv
    (fun z : ℝ => intervalConjugateKernelOperator (r - s) (Q s) z) y) x

private theorem conjugateOldValueIntegrand_hasDerivAt_time
    {Q : ℝ → ℝ → ℝ} (hQcont : ∀ s, Continuous (Q s))
    (hQint : ∀ s, Integrable (Q s) (intervalMeasure 1))
    {CQ : ℝ} (hQbound : ∀ s y, |Q s y| ≤ CQ)
    {r s x : ℝ} (hsr : s < r) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (fun q : ℝ => conjugateOldValueIntegrand Q q s x)
      (conjugateOldHessIntegrand Q r s x) r := by
  have hbase := intervalConjugateKernelOperator_hasDerivAt_time_secondDeriv_Icc
    (r := r - s) (x := x) (sub_pos.mpr hsr) (hQcont s)
      (hQint s) (hQbound s) hx
  have hshift : HasDerivAt (fun q : ℝ => q - s) 1 r :=
    (hasDerivAt_id r).sub_const s
  simpa [conjugateOldValueIntegrand, conjugateOldHessIntegrand] using
    hbase.comp r hshift

/- The fixed old-history piece has no zero-lag singularity.  Its difference
quotients are dominated by the lower-lag estimate above. -/
private theorem conjugateFixedOldHistory_hasDerivAt
    {a t CQ : ℝ} (ha0 : 0 ≤ a) (hat : a < t) (hCQ : 0 ≤ CQ)
    {Q : ℝ → ℝ → ℝ}
    (hQmeas : Measurable (Function.uncurry Q))
    (hQcont : ∀ s, Continuous (Q s))
    (hQint : ∀ s, Integrable (Q s) (intervalMeasure 1))
    (hQbound : ∀ s y, |Q s y| ≤ CQ)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt
      (fun r : ℝ => ∫ s in (0 : ℝ)..a,
        conjugateOldValueIntegrand Q r s x)
      (∫ s in (0 : ℝ)..a, conjugateOldHessIntegrand Q t s x)
      t := by
  let d : ℝ := (t - a) / 2
  have hd : 0 < d := by dsimp [d]; linarith
  let B : ℝ :=
    (5 * Real.sqrt 2 / 2) * (d / 2) ^ (-(1 : ℝ)) *
      (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
        (d / 2) ^ (-(1 / 2) : ℝ) * CQ)
  have hval_t : IntervalIntegrable
      (fun s : ℝ => conjugateOldValueIntegrand Q t s x) volume 0 a := by
    have ht0 : 0 < t := lt_of_le_of_lt ha0 hat
    have hfull :=
      conjugateDuhamel_intervalIntegrable_of_measurable_bound
        (x := x) ht0 hCQ hQmeas hQint hQbound
    exact hfull.mono_set (by
      rw [Set.uIcc_of_le ha0, Set.uIcc_of_le ht0.le]
      exact Set.Icc_subset_Icc le_rfl hat.le)
  have hslope_tendsto : Tendsto
      (fun r : ℝ => ∫ s in (0 : ℝ)..a,
        slope (fun q : ℝ => conjugateOldValueIntegrand Q q s x) t r)
      (𝓝[≠] t)
      (𝓝 (∫ s in (0 : ℝ)..a, conjugateOldHessIntegrand Q t s x)) := by
    have hball_ne : ∀ᶠ r in 𝓝[≠] t, r ∈ Metric.ball t d :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Metric.ball_mem_nhds t hd)
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (l := 𝓝[≠] t) (bound := fun _ : ℝ => B) ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [hball_ne, self_mem_nhdsWithin] with r hr hrne
      have hra : a < r := by
        rw [Metric.mem_ball, Real.dist_eq] at hr
        dsimp [d] at hr
        have habs := abs_lt.mp hr
        linarith
      have hr0 : 0 < r := lt_of_le_of_lt ha0 hra
      have hval_r_full :=
        conjugateDuhamel_intervalIntegrable_of_measurable_bound
          (x := x) hr0 hCQ hQmeas hQint hQbound
      have hval_r : IntervalIntegrable
          (fun s : ℝ => conjugateOldValueIntegrand Q r s x) volume 0 a :=
        hval_r_full.mono_set (by
          rw [Set.uIcc_of_le ha0, Set.uIcc_of_le hr0.le]
          exact Set.Icc_subset_Icc le_rfl hra.le)
      have hsl : IntervalIntegrable
          (fun s : ℝ => slope
            (fun q : ℝ => conjugateOldValueIntegrand Q q s x) t r)
          volume 0 a := by
        rw [show (fun s : ℝ => slope
              (fun q : ℝ => conjugateOldValueIntegrand Q q s x) t r) =
            fun s : ℝ =>
              (conjugateOldValueIntegrand Q r s x -
                conjugateOldValueIntegrand Q t s x) / (r - t) by
          funext s
          rw [slope_def_field]]
        exact (hval_r.sub hval_t).div_const (r - t)
      simpa [Set.uIoc_of_le ha0] using hsl.aestronglyMeasurable
    · filter_upwards [hball_ne, self_mem_nhdsWithin] with r hr hrne
      filter_upwards with s hsa
      rw [Set.uIoc_of_le ha0] at hsa
      have hsa_le : s ≤ a := hsa.2
      have htball : t ∈ Metric.ball t d := Metric.mem_ball_self hd
      have hdiff : ∀ q ∈ Metric.ball t d,
          DifferentiableAt ℝ
            (fun w : ℝ => conjugateOldValueIntegrand Q w s x) q := by
        intro q hq
        rw [Metric.mem_ball, Real.dist_eq] at hq
        have habs := abs_lt.mp hq
        have hsq : s < q := by
          dsimp [d] at habs
          linarith [hat, hsa_le]
        exact (conjugateOldValueIntegrand_hasDerivAt_time
          hQcont hQint hQbound hsq hx).differentiableAt
      have hderiv : ∀ q ∈ Metric.ball t d,
          ‖deriv (fun w : ℝ => conjugateOldValueIntegrand Q w s x) q‖ ≤ B := by
        intro q hq
        rw [Metric.mem_ball, Real.dist_eq] at hq
        have habs := abs_lt.mp hq
        have hlag : 0 < q - s := by
          dsimp [d] at habs
          linarith [hat, hsa_le]
        have hdlag : d ≤ q - s := by
          dsimp [d] at habs ⊢
          linarith [hat, hsa_le]
        have hlower := intervalConjugateKernelOperator_timeDeriv_abs_le_of_lower
          hd hdlag (hQcont s) (hQint s) (hQbound s) hx
        rw [(intervalConjugateKernelOperator_hasDerivAt_time_secondDeriv_Icc
          hlag (hQcont s) (hQint s) (hQbound s) hx).deriv] at hlower
        rw [(conjugateOldValueIntegrand_hasDerivAt_time
          hQcont hQint hQbound (sub_pos.mp hlag) hx).deriv, Real.norm_eq_abs]
        simpa [B] using hlower
      have hmv := (convex_ball t d).norm_image_sub_le_of_norm_deriv_le
        hdiff hderiv htball hr
      have hden : 0 < ‖r - t‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hrne)
      rw [slope_def_field, norm_div]
      exact (div_le_iff₀ hden).2 hmv
    · filter_upwards with s hsa
      rw [Set.uIoc_of_le ha0] at hsa
      exact (conjugateOldValueIntegrand_hasDerivAt_time
        hQcont hQint hQbound (hsa.2.trans_lt hat) hx).tendsto_slope
  apply hasDerivAt_iff_tendsto_slope.mpr
  refine hslope_tendsto.congr' ?_
  have hball_ne : ∀ᶠ r in 𝓝[≠] t, r ∈ Metric.ball t d :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Metric.ball_mem_nhds t hd)
  filter_upwards [hball_ne, self_mem_nhdsWithin] with r hr hrne
  have hra : a < r := by
    rw [Metric.mem_ball, Real.dist_eq] at hr
    dsimp [d] at hr
    have habs := abs_lt.mp hr
    linarith
  have hr0 : 0 < r := lt_of_le_of_lt ha0 hra
  have hval_r_full :=
    conjugateDuhamel_intervalIntegrable_of_measurable_bound
      (x := x) hr0 hCQ hQmeas hQint hQbound
  have hval_r : IntervalIntegrable
      (fun s : ℝ => conjugateOldValueIntegrand Q r s x) volume 0 a :=
    hval_r_full.mono_set (by
      rw [Set.uIcc_of_le ha0, Set.uIcc_of_le hr0.le]
      exact Set.Icc_subset_Icc le_rfl hra.le)
  rw [show (fun s : ℝ => slope
        (fun q : ℝ => conjugateOldValueIntegrand Q q s x) t r) =
      fun s : ℝ =>
        (conjugateOldValueIntegrand Q r s x -
          conjugateOldValueIntegrand Q t s x) / (r - t) by
    funext s
    rw [slope_def_field], intervalIntegral.integral_div,
    intervalIntegral.integral_sub hval_r hval_t]
  rw [slope_def_field]

/-- A fixed conjugate Duhamel history ending strictly before the target time
can be differentiated without any spatial derivative or positive-time bound
on the source.  Only the original flux itself is required to be jointly
measurable, slice-continuous/integrable, and uniformly bounded. -/
theorem intervalConjugateDuhamel_fixedHistory_hasDerivAt_time
    {a t CQ : ℝ} (ha0 : 0 ≤ a) (hat : a < t) (hCQ : 0 ≤ CQ)
    {Q : ℝ → ℝ → ℝ}
    (hQmeas : Measurable (Function.uncurry Q))
    (hQcont : ∀ s, Continuous (Q s))
    (hQint : ∀ s, Integrable (Q s) (intervalMeasure 1))
    (hQbound : ∀ s y, |Q s y| ≤ CQ)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt
      (fun r : ℝ => ∫ s in (0 : ℝ)..a,
        intervalConjugateKernelOperator (r - s) (Q s) x)
      (∫ s in (0 : ℝ)..a, deriv (fun y : ℝ => deriv
        (fun z : ℝ => intervalConjugateKernelOperator (t - s) (Q s) z) y) x)
      t := by
  simpa [conjugateOldValueIntegrand, conjugateOldHessIntegrand] using
    conjugateFixedOldHistory_hasDerivAt
      ha0 hat hCQ hQmeas hQcont hQint hQbound hx

section AxiomAudit

-- All four public interfaces are checked independently here.
#print axioms intervalConjugateKernelOperator_hasDerivAt_time_secondDeriv_Icc
#print axioms intervalConjugateKernelOperator_timeDeriv_abs_le_of_lower
#print axioms intervalConjugateKernelOperator_timeDeriv_continuousOn_Ioi
#print axioms intervalConjugateDuhamel_fixedHistory_hasDerivAt_time

end AxiomAudit

end ShenWork.Paper2
