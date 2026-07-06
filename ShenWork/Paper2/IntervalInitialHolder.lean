/-
  ShenWork/Paper2/IntervalInitialHolder.lean

  Small geometry package for the zero-time initial-leg Holder route.

  The eventual faithful producer should show that the Neumann heat semigroup
  preserves the initial Holder modulus.  This file only records the datum-level
  Holder predicate and period-2 circle distance facts needed by the reflected
  coupling route; it does not assert semigroup preservation.
-/
import ShenWork.Paper2.ChemMildHolderBootstrap
import Mathlib.Analysis.Normed.Group.AddCircle

open Metric
open MeasureTheory
open scoped Real

namespace ShenWork.Paper2

noncomputable section

open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)

/-- Initial-data spatial Holder modulus on the genuine interval domain. -/
def InitialDatumHolder
    (u₀ : intervalDomainPoint → ℝ) (θ H₀ : ℝ) : Prop :=
  ∀ x y : intervalDomainPoint,
    |u₀ x - u₀ y| ≤ H₀ * |x.1 - y.1| ^ θ

/-- Contractive coupling interface for the Neumann heat leg started from two
points.  This is deliberately a consumer-facing interface: the actual
probabilistic construction of such a coupling is a separate analytic task. -/
structure NeumannHeatContractiveCouplingFor
    (t : ℝ) (x y : intervalDomainPoint) (f : ℝ → ℝ) where
  μ : Measure (ℝ × ℝ)
  prob : IsProbabilityMeasure μ
  support : ∀ᵐ z ∂μ, z.1 ∈ Set.Icc (0 : ℝ) 1 ∧ z.2 ∈ Set.Icc (0 : ℝ) 1
  dist_le : ∀ᵐ z ∂μ, |z.1 - z.2| ≤ |x.1 - y.1|
  diff_integrable : Integrable (fun z : ℝ × ℝ => f z.1 - f z.2) μ
  semigroup_diff_eq :
    intervalFullSemigroupOperator t f x.1 -
        intervalFullSemigroupOperator t f y.1 =
      ∫ z : ℝ × ℝ, f z.1 - f z.2 ∂μ

/-- If the Neumann heat leg admits interval-supported couplings whose coordinate
distance is contractive, then initial-data Holder regularity propagates to the
zero-time initial-leg Holder frontier. -/
theorem InitialLegUniformHolderAtZero_of_contracting_couplings
    {u₀ : intervalDomainPoint → ℝ} {T θ H₀ : ℝ}
    (_hθ0 : 0 < θ) (_hH₀ : 0 ≤ H₀)
    (hholder : InitialDatumHolder u₀ θ H₀)
    (hplan : ∀ t, 0 < t → t ≤ T → ∀ x y : intervalDomainPoint,
      NeumannHeatContractiveCouplingFor t x y (intervalDomainLift u₀)) :
    InitialLegUniformHolderAtZero u₀ T θ H₀ := by
  intro t htpos htT x y
  rcases hplan t htpos htT x y with ⟨μ, hprob, hsupp, hdist, hint, hdiff⟩
  haveI : IsProbabilityMeasure μ := hprob
  rw [hdiff]
  have hpoint :
      (fun z : ℝ × ℝ => |intervalDomainLift u₀ z.1 - intervalDomainLift u₀ z.2|)
        ≤ᵐ[μ]
      fun _z : ℝ × ℝ => H₀ * |x.1 - y.1| ^ θ := by
    filter_upwards [hsupp, hdist] with z hz hdist_z
    have hholder_z :
        |intervalDomainLift u₀ z.1 - intervalDomainLift u₀ z.2|
          ≤ H₀ * |z.1 - z.2| ^ θ := by
      simpa [intervalDomainLift, hz.1, hz.2] using
        hholder ⟨z.1, hz.1⟩ ⟨z.2, hz.2⟩
    exact hholder_z.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) hdist_z _hθ0.le) _hH₀)
  calc
    |∫ z : ℝ × ℝ,
        intervalDomainLift u₀ z.1 - intervalDomainLift u₀ z.2 ∂μ|
        = ‖∫ z : ℝ × ℝ,
            intervalDomainLift u₀ z.1 - intervalDomainLift u₀ z.2 ∂μ‖ := by
          rw [Real.norm_eq_abs]
    _ ≤ ∫ z : ℝ × ℝ,
          ‖intervalDomainLift u₀ z.1 - intervalDomainLift u₀ z.2‖ ∂μ :=
        norm_integral_le_integral_norm _
    _ = ∫ z : ℝ × ℝ,
          |intervalDomainLift u₀ z.1 - intervalDomainLift u₀ z.2| ∂μ := by
        simp [Real.norm_eq_abs]
    _ ≤ ∫ _z : ℝ × ℝ, H₀ * |x.1 - y.1| ^ θ ∂μ :=
        integral_mono_ae hint.abs (integrable_const _) hpoint
    _ = H₀ * |x.1 - y.1| ^ θ := by
        simp

/-- Small-time mild Holder wrapper using initial-data Holder regularity and a
contractive-coupling producer for the homogeneous Neumann heat leg.  The
coupling construction remains an explicit input; this theorem only connects it
to the existing small-time mild Holder bootstrap. -/
theorem mild_orderBox_smallTime_holder_of_initialDatumHolder_contracting_couplings
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) {θ H₀ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hH₀ : 0 ≤ H₀)
    (hholder : InitialDatumHolder u₀ θ H₀)
    (hplan : ∀ t, 0 < t → t ≤ D.T → ∀ x y : intervalDomainPoint,
      NeumannHeatContractiveCouplingFor t x y (intervalDomainLift u₀)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t, 0 < t → t ≤ D.T → ∀ x y : intervalDomainPoint,
      |D.u t x - D.u t y| ≤ K * |x.1 - y.1| ^ θ := by
  exact mild_orderBox_smallTime_holder_of_initialLeg_holder D hθ0 hθ1 hH₀
    (InitialLegUniformHolderAtZero_of_contracting_couplings hθ0 hH₀ hholder hplan)

/-- On the period-2 additive circle, real representatives whose ordinary
distance is at most half the period have the same circle distance. -/
theorem addCircle_two_dist_coe_eq_abs_of_abs_le_one {x y : ℝ}
    (hxy : |x - y| ≤ 1) :
    dist ((x : AddCircle (2 : ℝ))) (y : AddCircle (2 : ℝ)) = |x - y| := by
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
  have hp : (2 : ℝ) ≠ 0 := by norm_num
  have hhalf : |x - y| ≤ |(2 : ℝ)| / 2 := by
    norm_num at hxy ⊢
    exact hxy
  simpa using
    (AddCircle.norm_coe_eq_abs_iff (p := (2 : ℝ)) (x := x - y) hp).2 hhalf

/-- Points in the interval `[0,1]` embed isometrically into the period-2 circle. -/
theorem addCircle_two_dist_coe_eq_abs_Icc {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    dist ((x : AddCircle (2 : ℝ))) (y : AddCircle (2 : ℝ)) = |x - y| := by
  apply addCircle_two_dist_coe_eq_abs_of_abs_le_one
  rw [abs_sub_le_iff]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- Common translation on the period-2 circle preserves distance.  This is the
pure metric part of the reflected Brownian coupling argument. -/
theorem addCircle_two_dist_translate (x y z : ℝ) :
    dist (((x + z : ℝ) : AddCircle (2 : ℝ)))
        ((y + z : ℝ) : AddCircle (2 : ℝ)) =
      dist ((x : AddCircle (2 : ℝ))) (y : AddCircle (2 : ℝ)) := by
  rw [dist_eq_norm, dist_eq_norm, ← QuotientAddGroup.mk_sub,
    ← QuotientAddGroup.mk_sub]
  congr 1
  ring_nf

/-- Every point on the period-2 additive circle is within distance `1` of zero. -/
theorem addCircle_two_dist_zero_le_one (z : AddCircle (2 : ℝ)) :
    dist z 0 ≤ 1 := by
  rw [dist_eq_norm, sub_zero]
  have hp : (2 : ℝ) ≠ 0 := by norm_num
  have h := AddCircle.norm_le_half_period (p := (2 : ℝ)) (x := z) hp
  norm_num at h ⊢
  exact h

/-- Fold a point of the period-2 circle back to `[0,1]` by its distance to zero. -/
noncomputable def addCircleTwoFoldPoint
    (z : AddCircle (2 : ℝ)) : intervalDomainPoint :=
  ⟨dist z 0, dist_nonneg, addCircle_two_dist_zero_le_one z⟩

/-- Folding after a common real translation is contractive for interval starting
points.  This is the deterministic metric core of the common-noise reflected
Brownian coupling route. -/
theorem addCircle_two_foldPoint_translate_contract_real
    (x y : intervalDomainPoint) (z : ℝ) :
    |(addCircleTwoFoldPoint (((x.1 + z : ℝ) : AddCircle (2 : ℝ)))).1 -
      (addCircleTwoFoldPoint (((y.1 + z : ℝ) : AddCircle (2 : ℝ)))).1| ≤
      |x.1 - y.1| := by
  have hrev :=
    abs_dist_sub_le (((x.1 + z : ℝ) : AddCircle (2 : ℝ)))
      (((y.1 + z : ℝ) : AddCircle (2 : ℝ))) (0 : AddCircle (2 : ℝ))
  have htrans := addCircle_two_dist_translate x.1 y.1 z
  have hxy := addCircle_two_dist_coe_eq_abs_Icc x.2 y.2
  simpa [addCircleTwoFoldPoint, htrans, hxy] using hrev

/-- Fold the common period-2 translate of an interval point back to `[0,1]`. -/
noncomputable def addCircleTwoFoldTranslatePoint
    (x : intervalDomainPoint) (z : ℝ) : intervalDomainPoint :=
  addCircleTwoFoldPoint (((x.1 + z : ℝ) : AddCircle (2 : ℝ)))

/-- Coupling map induced by folding the same period-2 noise from two starting
points. -/
noncomputable def addCircleTwoFoldCouplingMap
    (x y : intervalDomainPoint) (z : ℝ) : ℝ × ℝ :=
  ((addCircleTwoFoldTranslatePoint x z).1, (addCircleTwoFoldTranslatePoint y z).1)

/-- The folded common-noise coupling map is Borel-measurable. -/
theorem addCircleTwoFoldCouplingMap_measurable
    (x y : intervalDomainPoint) : Measurable (addCircleTwoFoldCouplingMap x y) := by
  unfold addCircleTwoFoldCouplingMap addCircleTwoFoldTranslatePoint
  exact (Continuous.prodMk
    (Continuous.dist
      ((AddCircle.continuous_mk' (2 : ℝ)).comp (continuous_const.add continuous_id))
      continuous_const)
    (Continuous.dist
      ((AddCircle.continuous_mk' (2 : ℝ)).comp (continuous_const.add continuous_id))
      continuous_const)).measurable

/-- Common folded-noise interface for the reflected Neumann heat leg.  A
producer should supply one noise law `ν` such that folding the same translated
period-2 noise from `x` and `y` gives the two semigroup values.  This file only
uses the interface; the analytic kernel-law representation is a separate task. -/
structure NeumannHeatCommonFoldNoiseFor
    (t : ℝ) (x y : intervalDomainPoint) (f : ℝ → ℝ) where
  ν : Measure ℝ
  prob : IsProbabilityMeasure ν
  fx_integrable : Integrable (fun z : ℝ =>
    f (addCircleTwoFoldPoint (((x.1 + z : ℝ) : AddCircle (2 : ℝ)))).1) ν
  fy_integrable : Integrable (fun z : ℝ =>
    f (addCircleTwoFoldPoint (((y.1 + z : ℝ) : AddCircle (2 : ℝ)))).1) ν
  sx_eq :
    intervalFullSemigroupOperator t f x.1 =
      ∫ z : ℝ,
        f (addCircleTwoFoldPoint (((x.1 + z : ℝ) : AddCircle (2 : ℝ)))).1 ∂ν
  sy_eq :
    intervalFullSemigroupOperator t f y.1 =
      ∫ z : ℝ,
        f (addCircleTwoFoldPoint (((y.1 + z : ℝ) : AddCircle (2 : ℝ)))).1 ∂ν

/-- Push a common folded-noise witness forward to the existing contractive
coupling interface.  The extra measurability assumption is deliberately
explicit: the common-noise witness controls the two pulled-back integrands, but
for arbitrary `f` it does not by itself make the pushforward difference function
strongly measurable off the range of the coupling map. -/
noncomputable def NeumannHeatContractiveCouplingFor_of_common_fold_noise
    {t : ℝ} {x y : intervalDomainPoint} {f : ℝ → ℝ}
    (H : NeumannHeatCommonFoldNoiseFor t x y f)
    (hdiff_sm : AEStronglyMeasurable
      (fun z : ℝ × ℝ => f z.1 - f z.2)
      (Measure.map (addCircleTwoFoldCouplingMap x y) H.ν)) :
    NeumannHeatContractiveCouplingFor t x y f := by
  let pair : ℝ → ℝ × ℝ := addCircleTwoFoldCouplingMap x y
  have hpair_meas : Measurable pair := addCircleTwoFoldCouplingMap_measurable x y
  have hpair_aem : AEMeasurable pair H.ν := hpair_meas.aemeasurable
  haveI : IsProbabilityMeasure H.ν := H.prob
  have hcomp_int : Integrable
      ((fun z : ℝ × ℝ => f z.1 - f z.2) ∘ pair) H.ν := by
    change Integrable (fun z : ℝ =>
      f (addCircleTwoFoldPoint (((x.1 + z : ℝ) : AddCircle (2 : ℝ)))).1 -
      f (addCircleTwoFoldPoint (((y.1 + z : ℝ) : AddCircle (2 : ℝ)))).1) H.ν
    exact H.fx_integrable.sub H.fy_integrable
  have hmap_int : Integrable (fun z : ℝ × ℝ => f z.1 - f z.2)
      (Measure.map pair H.ν) :=
    (integrable_map_measure hdiff_sm hpair_aem).2 hcomp_int
  refine
    { μ := Measure.map pair H.ν
      prob := ?_
      support := ?_
      dist_le := ?_
      diff_integrable := hmap_int
      semigroup_diff_eq := ?_ }
  · exact Measure.isProbabilityMeasure_map hpair_aem
  · rw [ae_map_iff hpair_aem (by measurability)]
    filter_upwards with z
    simp [pair, addCircleTwoFoldCouplingMap]
  · rw [ae_map_iff hpair_aem (by measurability)]
    filter_upwards with z
    simpa [pair, addCircleTwoFoldCouplingMap, addCircleTwoFoldTranslatePoint] using
      addCircle_two_foldPoint_translate_contract_real x y z
  · rw [H.sx_eq, H.sy_eq, ← integral_sub H.fx_integrable H.fy_integrable]
    rw [integral_map hpair_aem hdiff_sm]
    simp [pair, addCircleTwoFoldCouplingMap, addCircleTwoFoldTranslatePoint]

/-- A common folded-noise representation preserves the initial Holder modulus
for the homogeneous Neumann heat leg.  The proof uses only the deterministic
fold contraction plus integral Minkowski; the construction of the noise law is
kept explicit in `hplan`. -/
theorem InitialLegUniformHolderAtZero_of_common_fold_noise
    {u₀ : intervalDomainPoint → ℝ} {T θ H₀ : ℝ}
    (hθ0 : 0 < θ) (hH₀ : 0 ≤ H₀)
    (hholder : InitialDatumHolder u₀ θ H₀)
    (hplan : ∀ t, 0 < t → t ≤ T → ∀ x y : intervalDomainPoint,
      NeumannHeatCommonFoldNoiseFor t x y (intervalDomainLift u₀)) :
    InitialLegUniformHolderAtZero u₀ T θ H₀ := by
  intro t htpos htT x y
  rcases hplan t htpos htT x y with ⟨ν, hprob, hxint, hyint, hxeq, hyeq⟩
  haveI : IsProbabilityMeasure ν := hprob
  rw [hxeq, hyeq, ← integral_sub hxint hyint]
  have hdiff_int : Integrable (fun z : ℝ =>
      intervalDomainLift u₀
          (addCircleTwoFoldPoint (((x.1 + z : ℝ) : AddCircle (2 : ℝ)))).1 -
        intervalDomainLift u₀
          (addCircleTwoFoldPoint (((y.1 + z : ℝ) : AddCircle (2 : ℝ)))).1) ν :=
    hxint.sub hyint
  have hpoint :
      (fun z : ℝ =>
          |intervalDomainLift u₀
              (addCircleTwoFoldPoint (((x.1 + z : ℝ) : AddCircle (2 : ℝ)))).1 -
            intervalDomainLift u₀
              (addCircleTwoFoldPoint (((y.1 + z : ℝ) : AddCircle (2 : ℝ)))).1|)
        ≤ᵐ[ν]
      fun _z : ℝ => H₀ * |x.1 - y.1| ^ θ := by
    filter_upwards with z
    set X : intervalDomainPoint :=
      addCircleTwoFoldPoint (((x.1 + z : ℝ) : AddCircle (2 : ℝ))) with hX
    set Y : intervalDomainPoint :=
      addCircleTwoFoldPoint (((y.1 + z : ℝ) : AddCircle (2 : ℝ))) with hY
    have hholder_z :
        |intervalDomainLift u₀ X.1 - intervalDomainLift u₀ Y.1|
          ≤ H₀ * |X.1 - Y.1| ^ θ := by
      simpa [InitialDatumHolder, intervalDomainLift, X, Y] using hholder X Y
    have hdist_z : |X.1 - Y.1| ≤ |x.1 - y.1| := by
      simpa [X, Y] using addCircle_two_foldPoint_translate_contract_real x y z
    exact hholder_z.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) hdist_z hθ0.le) hH₀)
  calc
    |∫ z : ℝ,
        intervalDomainLift u₀
            (addCircleTwoFoldPoint (((x.1 + z : ℝ) : AddCircle (2 : ℝ)))).1 -
          intervalDomainLift u₀
            (addCircleTwoFoldPoint (((y.1 + z : ℝ) : AddCircle (2 : ℝ)))).1 ∂ν|
        = ‖∫ z : ℝ,
            intervalDomainLift u₀
                (addCircleTwoFoldPoint (((x.1 + z : ℝ) : AddCircle (2 : ℝ)))).1 -
              intervalDomainLift u₀
                (addCircleTwoFoldPoint (((y.1 + z : ℝ) : AddCircle (2 : ℝ)))).1 ∂ν‖ := by
          rw [Real.norm_eq_abs]
    _ ≤ ∫ z : ℝ,
          ‖intervalDomainLift u₀
              (addCircleTwoFoldPoint (((x.1 + z : ℝ) : AddCircle (2 : ℝ)))).1 -
            intervalDomainLift u₀
              (addCircleTwoFoldPoint (((y.1 + z : ℝ) : AddCircle (2 : ℝ)))).1‖ ∂ν :=
        norm_integral_le_integral_norm _
    _ = ∫ z : ℝ,
          |intervalDomainLift u₀
              (addCircleTwoFoldPoint (((x.1 + z : ℝ) : AddCircle (2 : ℝ)))).1 -
            intervalDomainLift u₀
              (addCircleTwoFoldPoint (((y.1 + z : ℝ) : AddCircle (2 : ℝ)))).1| ∂ν := by
        simp [Real.norm_eq_abs]
    _ ≤ ∫ _z : ℝ, H₀ * |x.1 - y.1| ^ θ ∂ν :=
        integral_mono_ae hdiff_int.abs (integrable_const _) hpoint
    _ = H₀ * |x.1 - y.1| ^ θ := by
        simp

/-- Small-time mild Holder wrapper using initial-data Holder regularity and a
common folded-noise producer for the homogeneous Neumann heat leg. -/
theorem mild_orderBox_smallTime_holder_of_initialDatumHolder_common_fold_noise
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) {θ H₀ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hH₀ : 0 ≤ H₀)
    (hholder : InitialDatumHolder u₀ θ H₀)
    (hplan : ∀ t, 0 < t → t ≤ D.T → ∀ x y : intervalDomainPoint,
      NeumannHeatCommonFoldNoiseFor t x y (intervalDomainLift u₀)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t, 0 < t → t ≤ D.T → ∀ x y : intervalDomainPoint,
      |D.u t x - D.u t y| ≤ K * |x.1 - y.1| ^ θ := by
  exact mild_orderBox_smallTime_holder_of_initialLeg_holder D hθ0 hθ1 hH₀
    (InitialLegUniformHolderAtZero_of_common_fold_noise hθ0 hH₀ hholder hplan)

end

end ShenWork.Paper2
