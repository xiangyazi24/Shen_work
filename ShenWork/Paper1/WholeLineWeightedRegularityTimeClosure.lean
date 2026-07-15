/-
  ShenWork/Paper1/WholeLineWeightedRegularityTimeClosure.lean

  Canonical whole-line L² interfaces for differentiating the weighted
  quadratic energy.  The total lift below removes arbitrary choices of L²
  representatives from the positive-time regularity frontier.
-/
import ShenWork.Paper1.WholeLineWeightedRegularityDuhamel
import ShenWork.Paper1.WholeLineWeightedRegularityForcingTrajectory
import ShenWork.Paper1.WholeLineWeightedRegularitySecondDeriv

open Filter MeasureTheory Topology
open scoped RealInnerProductSpace Topology

noncomputable section

namespace ShenWork.Paper1

/-- The canonical whole-line `L²` lift when a real field is square integrable,
and zero otherwise.  This totalization lets a local-in-time regularity theorem
refer to one fixed Hilbert-valued trajectory. -/
def wholeLineRealL2Total (f : ℝ → ℝ) : WholeLineRealL2 := by
  classical
  exact if h : AEStronglyMeasurable f volume ∧
      Integrable (fun x : ℝ => f x ^ 2) volume then
    wholeLineRealL2OfSqIntegrable f h.1 h.2
  else 0

/-- On every square-integrable measurable field, the total lift is the
canonical lift and hence realizes the field almost everywhere. -/
theorem wholeLineRealL2Total_coe_ae
    (f : ℝ → ℝ)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf_sq : Integrable (fun x : ℝ => f x ^ 2) volume) :
    ((wholeLineRealL2Total f : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] f := by
  rw [wholeLineRealL2Total, dif_pos ⟨hf_meas, hf_sq⟩]
  exact wholeLineRealL2OfSqIntegrable_coe_ae f hf_meas hf_sq

/-- Hilbert differentiability of an `L²` realization is the exact analytic
input needed for the derivative of its concrete quadratic energy. -/
theorem wholeLineHalfEnergy_hasDerivAt_of_L2_hasDerivAt
    {phi phi_t : ℝ → ℝ → ℝ}
    {Z : ℝ → WholeLineRealL2} {Zt : WholeLineRealL2} {t : ℝ}
    (hZ : HasDerivAt Z Zt t)
    (hrep : ∀ᶠ s in nhds t,
      ((Z s : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] phi s)
    (htrep : ((Zt : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] phi_t t) :
    HasDerivAt (ShenWork.PaperOne.wholeLineHalfEnergy phi)
      (∫ x : ℝ, phi t x * phi_t t x) t := by
  apply wholeLineHalfEnergy_hasDerivAt_of_L2_differenceQuotient
  · exact hasDerivAt_iff_tendsto_slope_zero.mp hZ
  · exact hrep
  · exact htrep

/-- A local square-integrability hypothesis identifies the total canonical
trajectory with the concrete pointwise field near the differentiation time.
Thus no arbitrary `L²` representative or representative-equality hypothesis
appears in this interface. -/
theorem wholeLineHalfEnergy_hasDerivAt_of_canonicalL2_hasDerivAt
    {phi phi_t : ℝ → ℝ → ℝ} {t : ℝ}
    (hphi_meas : ∀ᶠ s in nhds t,
      AEStronglyMeasurable (phi s) volume)
    (hphi_sq : ∀ᶠ s in nhds t,
      Integrable (fun x : ℝ => phi s x ^ 2) volume)
    (hphit_meas : AEStronglyMeasurable (phi_t t) volume)
    (hphit_sq : Integrable (fun x : ℝ => phi_t t x ^ 2) volume)
    (hZ : HasDerivAt
      (fun s => wholeLineRealL2Total (phi s))
      (wholeLineRealL2Total (phi_t t)) t) :
    HasDerivAt (ShenWork.PaperOne.wholeLineHalfEnergy phi)
      (∫ x : ℝ, phi t x * phi_t t x) t := by
  apply wholeLineHalfEnergy_hasDerivAt_of_L2_hasDerivAt hZ
  · filter_upwards [hphi_meas, hphi_sq] with s hsmeas hsint
    exact wholeLineRealL2Total_coe_ae (phi s) hsmeas hsint
  · exact wholeLineRealL2Total_coe_ae (phi_t t) hphit_meas hphit_sq

/-- Difference-quotient form of the canonical `L²` closure.  This is the
direct endpoint for a positive-time restart argument stated in slopes. -/
theorem wholeLineHalfEnergy_hasDerivAt_of_canonicalL2_differenceQuotient
    {phi phi_t : ℝ → ℝ → ℝ} {t : ℝ}
    (hphi_meas : ∀ᶠ s in nhds t,
      AEStronglyMeasurable (phi s) volume)
    (hphi_sq : ∀ᶠ s in nhds t,
      Integrable (fun x : ℝ => phi s x ^ 2) volume)
    (hphit_meas : AEStronglyMeasurable (phi_t t) volume)
    (hphit_sq : Integrable (fun x : ℝ => phi_t t x ^ 2) volume)
    (hquot : Tendsto
      (fun h : ℝ => h⁻¹ •
        (wholeLineRealL2Total (phi (t + h)) -
          wholeLineRealL2Total (phi t)))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds (wholeLineRealL2Total (phi_t t)))) :
    HasDerivAt (ShenWork.PaperOne.wholeLineHalfEnergy phi)
      (∫ x : ℝ, phi t x * phi_t t x) t := by
  apply wholeLineHalfEnergy_hasDerivAt_of_canonicalL2_hasDerivAt
    hphi_meas hphi_sq hphit_meas hphit_sq
  exact hasDerivAt_iff_tendsto_slope_zero.mpr hquot

/-- The norm of an `L²` class is the square integral of any real pointwise
representative. -/
theorem wholeLineRealL2_norm_sq_eq_integral_sq_of_aeEq
    (Z : WholeLineRealL2) {f : ℝ → ℝ}
    (hrep : ((Z : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] f) :
    ‖Z‖ ^ 2 = ∫ x : ℝ, f x ^ 2 := by
  have hinner := wholeLineIntegral_mul_eq_inner_of_aeEq Z Z hrep hrep
  rw [real_inner_self_eq_norm_sq] at hinner
  simpa only [pow_two] using hinner.symm

/-- Concrete scalar `L²` convergence of pointwise time difference quotients
implies differentiability of the fixed total canonical Hilbert trajectory.
This is the direct bridge for raw-difference-quotient and Fatou arguments. -/
theorem canonicalL2_hasDerivAt_of_integral_differenceQuotient_sq_tendsto_zero
    {phi phi_t : ℝ → ℝ → ℝ} {t : ℝ}
    (hphi_meas : ∀ᶠ s in nhds t,
      AEStronglyMeasurable (phi s) volume)
    (hphi_sq : ∀ᶠ s in nhds t,
      Integrable (fun x : ℝ => phi s x ^ 2) volume)
    (hphit_meas : AEStronglyMeasurable (phi_t t) volume)
    (hphit_sq : Integrable (fun x : ℝ => phi_t t x ^ 2) volume)
    (hlim : Tendsto (fun h : ℝ => ∫ x : ℝ,
      (h⁻¹ * (phi (t + h) x - phi t x) - phi_t t x) ^ 2)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0)) :
    HasDerivAt
      (fun s => wholeLineRealL2Total (phi s))
      (wholeLineRealL2Total (phi_t t)) t := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hadd0 : Tendsto (fun h : ℝ => t + h) (nhds 0) (nhds t) := by
    have hconst : ContinuousAt (fun _ : ℝ => t) 0 := continuousAt_const
    have hid : ContinuousAt (fun h : ℝ => h) 0 := continuousAt_id
    have hadd' := hconst.add hid
    change Tendsto (fun h : ℝ => t + h) (nhds 0) (nhds (t + 0)) at hadd'
    simpa only [add_zero] using hadd'
  have hadd : Tendsto (fun h : ℝ => t + h)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds t) :=
    hadd0.mono_left inf_le_left
  have hphi_meas_add : ∀ᶠ h in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      AEStronglyMeasurable (phi (t + h)) volume :=
    hadd.eventually hphi_meas
  have hphi_sq_add : ∀ᶠ h in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      Integrable (fun x : ℝ => phi (t + h) x ^ 2) volume :=
    hadd.eventually hphi_sq
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hlim
  have hsqrt0 : Tendsto (fun h : ℝ => Real.sqrt (∫ x : ℝ,
      (h⁻¹ * (phi (t + h) x - phi t x) - phi_t t x) ^ 2))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    simpa only [Function.comp_apply, Real.sqrt_zero] using hsqrt
  refine hsqrt0.congr' ?_
  filter_upwards [hphi_meas_add, hphi_sq_add] with h hhmeas hh_sq
  let Zh : WholeLineRealL2 := wholeLineRealL2Total (phi (t + h))
  let Z0 : WholeLineRealL2 := wholeLineRealL2Total (phi t)
  let Zt : WholeLineRealL2 := wholeLineRealL2Total (phi_t t)
  let E : WholeLineRealL2 := h⁻¹ • (Zh - Z0) - Zt
  have h0meas : AEStronglyMeasurable (phi t) volume :=
    hphi_meas.self_of_nhds
  have h0_sq : Integrable (fun x : ℝ => phi t x ^ 2) volume :=
    hphi_sq.self_of_nhds
  have hZh : ((Zh : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      phi (t + h) := wholeLineRealL2Total_coe_ae _ hhmeas hh_sq
  have hZ0 : ((Z0 : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      phi t := wholeLineRealL2Total_coe_ae _ h0meas h0_sq
  have hZt : ((Zt : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      phi_t t := wholeLineRealL2Total_coe_ae _ hphit_meas hphit_sq
  have hsub : (((Zh - Z0 : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      fun x => phi (t + h) x - phi t x) := by
    filter_upwards [Lp.coeFn_sub Zh Z0, hZh, hZ0] with x hx hxh hx0
    rw [hx]
    simp only [Pi.sub_apply]
    rw [hxh, hx0]
  have hscale : (((h⁻¹ • (Zh - Z0) : WholeLineRealL2) : ℝ → ℝ)
      =ᵐ[volume] fun x => h⁻¹ * (phi (t + h) x - phi t x)) := by
    filter_upwards [Lp.coeFn_smul h⁻¹ (Zh - Z0), hsub] with x hx hs
    rw [hx]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hs]
  have hE : ((E : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      fun x => h⁻¹ * (phi (t + h) x - phi t x) - phi_t t x := by
    filter_upwards [Lp.coeFn_sub (h⁻¹ • (Zh - Z0)) Zt,
      hscale, hZt] with x hx hs ht
    rw [hx]
    simp only [Pi.sub_apply]
    rw [hs, ht]
  have hnormsq := wholeLineRealL2_norm_sq_eq_integral_sq_of_aeEq E hE
  change Real.sqrt (∫ x : ℝ,
      (h⁻¹ * (phi (t + h) x - phi t x) - phi_t t x) ^ 2) = ‖E‖
  calc
    Real.sqrt (∫ x : ℝ,
        (h⁻¹ * (phi (t + h) x - phi t x) - phi_t t x) ^ 2) =
        Real.sqrt (‖E‖ ^ 2) := by rw [hnormsq]
    _ = ‖E‖ := Real.sqrt_sq (norm_nonneg E)

/-- Scalar difference-quotient closure for a concrete whole-line quadratic
energy. -/
theorem wholeLineHalfEnergy_hasDerivAt_of_integral_differenceQuotient_sq
    {phi phi_t : ℝ → ℝ → ℝ} {t : ℝ}
    (hphi_meas : ∀ᶠ s in nhds t,
      AEStronglyMeasurable (phi s) volume)
    (hphi_sq : ∀ᶠ s in nhds t,
      Integrable (fun x : ℝ => phi s x ^ 2) volume)
    (hphit_meas : AEStronglyMeasurable (phi_t t) volume)
    (hphit_sq : Integrable (fun x : ℝ => phi_t t x ^ 2) volume)
    (hlim : Tendsto (fun h : ℝ => ∫ x : ℝ,
      (h⁻¹ * (phi (t + h) x - phi t x) - phi_t t x) ^ 2)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0)) :
    HasDerivAt (ShenWork.PaperOne.wholeLineHalfEnergy phi)
      (∫ x : ℝ, phi t x * phi_t t x) t := by
  apply wholeLineHalfEnergy_hasDerivAt_of_canonicalL2_hasDerivAt
    hphi_meas hphi_sq hphit_meas hphit_sq
  exact canonicalL2_hasDerivAt_of_integral_differenceQuotient_sq_tendsto_zero
    hphi_meas hphi_sq hphit_meas hphit_sq hlim

/-- Scalar difference-quotient endpoint for the actual weighted population
half energy. -/
theorem paper5WeightedHalfEnergy_hasDerivAt_of_integral_differenceQuotient_sq
    {eta c t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hW_meas : ∀ᶠ s in nhds t,
      AEStronglyMeasurable
        (paper5WeightedPopulation eta (coMovingPath c u) U s) volume)
    (hW_sq : ∀ᶠ s in nhds t,
      Integrable (fun x : ℝ =>
        paper5WeightedPopulation eta (coMovingPath c u) U s x ^ 2) volume)
    (hWt_meas : AEStronglyMeasurable
      (paper5WeightedPopulationT eta
        (paper5CoMovingMaterialTime c u) t) volume)
    (hWt_sq : Integrable (fun x : ℝ =>
      paper5WeightedPopulationT eta
        (paper5CoMovingMaterialTime c u) t x ^ 2) volume)
    (hlim : Tendsto (fun h : ℝ => ∫ x : ℝ,
      (h⁻¹ *
          (paper5WeightedPopulation eta (coMovingPath c u) U (t + h) x -
            paper5WeightedPopulation eta (coMovingPath c u) U t x) -
        paper5WeightedPopulationT eta
          (paper5CoMovingMaterialTime c u) t x) ^ 2)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0)) :
    HasDerivAt (paper5WeightedHalfEnergy eta c u U)
      (∫ x : ℝ,
        paper5WeightedPopulation eta (coMovingPath c u) U t x *
          paper5WeightedPopulationT eta
            (paper5CoMovingMaterialTime c u) t x) t := by
  simpa [paper5WeightedHalfEnergy] using
    (wholeLineHalfEnergy_hasDerivAt_of_integral_differenceQuotient_sq
      (phi := paper5WeightedPopulation eta (coMovingPath c u) U)
      (phi_t := paper5WeightedPopulationT eta
        (paper5CoMovingMaterialTime c u))
      hW_meas hW_sq hWt_meas hWt_sq hlim)

/-- Canonical-Hilbert derivative producer for the actual weighted co-moving
population half energy.  The only time-regularity input is differentiability
of the fixed total canonical `L²` trajectory. -/
theorem paper5WeightedHalfEnergy_hasDerivAt_of_canonicalL2_hasDerivAt
    {eta c t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hW_meas : ∀ᶠ s in nhds t,
      AEStronglyMeasurable
        (paper5WeightedPopulation eta (coMovingPath c u) U s) volume)
    (hW_sq : ∀ᶠ s in nhds t,
      Integrable (fun x : ℝ =>
        paper5WeightedPopulation eta (coMovingPath c u) U s x ^ 2) volume)
    (hWt_meas : AEStronglyMeasurable
      (paper5WeightedPopulationT eta
        (paper5CoMovingMaterialTime c u) t) volume)
    (hWt_sq : Integrable (fun x : ℝ =>
      paper5WeightedPopulationT eta
        (paper5CoMovingMaterialTime c u) t x ^ 2) volume)
    (hZ : HasDerivAt
      (fun s => wholeLineRealL2Total
        (paper5WeightedPopulation eta (coMovingPath c u) U s))
      (wholeLineRealL2Total
        (paper5WeightedPopulationT eta
          (paper5CoMovingMaterialTime c u) t)) t) :
    HasDerivAt (paper5WeightedHalfEnergy eta c u U)
      (∫ x : ℝ,
        paper5WeightedPopulation eta (coMovingPath c u) U t x *
          paper5WeightedPopulationT eta
            (paper5CoMovingMaterialTime c u) t x) t := by
  simpa [paper5WeightedHalfEnergy] using
    (wholeLineHalfEnergy_hasDerivAt_of_canonicalL2_hasDerivAt
      (phi := paper5WeightedPopulation eta (coMovingPath c u) U)
      (phi_t := paper5WeightedPopulationT eta
        (paper5CoMovingMaterialTime c u))
      hW_meas hW_sq hWt_meas hWt_sq hZ)

/-- Difference-quotient endpoint for the actual weighted co-moving
population half energy. -/
theorem paper5WeightedHalfEnergy_hasDerivAt_of_canonicalL2_differenceQuotient
    {eta c t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hW_meas : ∀ᶠ s in nhds t,
      AEStronglyMeasurable
        (paper5WeightedPopulation eta (coMovingPath c u) U s) volume)
    (hW_sq : ∀ᶠ s in nhds t,
      Integrable (fun x : ℝ =>
        paper5WeightedPopulation eta (coMovingPath c u) U s x ^ 2) volume)
    (hWt_meas : AEStronglyMeasurable
      (paper5WeightedPopulationT eta
        (paper5CoMovingMaterialTime c u) t) volume)
    (hWt_sq : Integrable (fun x : ℝ =>
      paper5WeightedPopulationT eta
        (paper5CoMovingMaterialTime c u) t x ^ 2) volume)
    (hquot : Tendsto
      (fun h : ℝ => h⁻¹ •
        (wholeLineRealL2Total
            (paper5WeightedPopulation eta (coMovingPath c u) U (t + h)) -
          wholeLineRealL2Total
            (paper5WeightedPopulation eta (coMovingPath c u) U t)))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds (wholeLineRealL2Total
        (paper5WeightedPopulationT eta
          (paper5CoMovingMaterialTime c u) t)))) :
    HasDerivAt (paper5WeightedHalfEnergy eta c u U)
      (∫ x : ℝ,
        paper5WeightedPopulation eta (coMovingPath c u) U t x *
          paper5WeightedPopulationT eta
            (paper5CoMovingMaterialTime c u) t x) t := by
  apply paper5WeightedHalfEnergy_hasDerivAt_of_canonicalL2_hasDerivAt
    hW_meas hW_sq hWt_meas hWt_sq
  exact hasDerivAt_iff_tendsto_slope_zero.mpr hquot

/-! ## Closing the material derivative from the spatial generator -/

/-- If a measurable field is pointwise the sum of two square-integrable
fields, then it is square integrable.  This elementary closure is stated for
squares so that it can be applied directly to pointwise PDE identities. -/
theorem wholeLine_sq_integrable_of_eq_add
    {f g k : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f volume)
    (hg_sq : Integrable (fun x : ℝ => g x ^ 2) volume)
    (hk_sq : Integrable (fun x : ℝ => k x ^ 2) volume)
    (heq : ∀ x, f x = g x + k x) :
    Integrable (fun x : ℝ => f x ^ 2) volume := by
  let major : ℝ → ℝ := fun x => 2 * (g x ^ 2 + k x ^ 2)
  have hmajor : Integrable major volume := by
    simpa only [major] using (hg_sq.add hk_sq).const_mul 2
  refine hmajor.mono' (hf_meas.pow 2) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), heq x]
  dsimp only [major]
  nlinarith [sq_nonneg (g x - k x)]

/-- The classical weighted population equation in the form adapted to the
full conjugated moving-heat generator.  The lower-order forcing on the right
is exactly `paper5WeightedGeneratorForcing`; no coefficient package is
introduced. -/
theorem paper5WeightedPopulationT_eq_spatialGenerator_add_generatorForcing
    (p : CMParams) {T eta c t x : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hsol : IsClassicalSolution p T u v) (ht0 : 0 < t) (htT : t < T)
    (hTW : IsTravelingWave p c U V)
    (hu : 0 ≤ coMovingPath c u t x)
    (hu1 : ContDiff ℝ 1 (coMovingPath c u t))
    (hv2 : ContDiff ℝ 2 (coMovingPath c v t))
    (hU1 : ContDiff ℝ 1 U) (hV2 : ContDiff ℝ 2 V) :
    paper5WeightedPopulationT eta
        (paper5CoMovingMaterialTime c u) t x =
      (paper5WeightedPopulationXX eta (coMovingPath c u) U t x +
        (c - 2 * eta) *
          paper5WeightedPopulationX eta (coMovingPath c u) U t x +
        (eta ^ 2 - c * eta) *
          paper5WeightedPopulation eta (coMovingPath c u) U t x) +
        paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V t x := by
  have hsource :=
    paper5WeightedLowerOrderSource_eq_material_sub_principal_of_classical
      p (eta := eta) hsol ht0 htT hTW hu hu1 hv2 hU1 hV2
  have hforcing :=
    paper5WeightedLowerOrderSource_sub_growth_eq_generatorForcing
      p (eta := eta) hsol ht0 htT hTW hu (hTW.U_pos x).le
        hu1 hv2 hU1 hV2
  linarith

/-- Once the full spatial generator and the genuine nonlinear forcing are
in `L²`, the classical PDE puts the material time derivative in `L²`.
This is the non-circular square-integrability input required by the
canonical Hilbert differentiation interface above. -/
theorem paper5WeightedPopulationT_sq_integrable_of_generatorForcing
    (p : CMParams) {T eta c t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hsol : IsClassicalSolution p T u v) (ht0 : 0 < t) (htT : t < T)
    (hTW : IsTravelingWave p c U V)
    (hu : ∀ x, 0 ≤ coMovingPath c u t x)
    (hu1 : ContDiff ℝ 1 (coMovingPath c u t))
    (hv2 : ContDiff ℝ 2 (coMovingPath c v t))
    (hU1 : ContDiff ℝ 1 U) (hV2 : ContDiff ℝ 2 V)
    (hWt_meas : AEStronglyMeasurable
      (paper5WeightedPopulationT eta
        (paper5CoMovingMaterialTime c u) t) volume)
    (hgenerator_sq : Integrable (fun x : ℝ =>
      (paper5WeightedPopulationXX eta (coMovingPath c u) U t x +
        (c - 2 * eta) *
          paper5WeightedPopulationX eta (coMovingPath c u) U t x +
        (eta ^ 2 - c * eta) *
          paper5WeightedPopulation eta (coMovingPath c u) U t x) ^ 2)
      volume)
    (hforcing_sq : Integrable (fun x : ℝ =>
      paper5WeightedGeneratorForcing p eta
        (coMovingPath c u) (coMovingPath c v) U V t x ^ 2) volume) :
    Integrable (fun x : ℝ =>
      paper5WeightedPopulationT eta
        (paper5CoMovingMaterialTime c u) t x ^ 2) volume := by
  apply wholeLine_sq_integrable_of_eq_add hWt_meas
    hgenerator_sq hforcing_sq
  intro x
  exact paper5WeightedPopulationT_eq_spatialGenerator_add_generatorForcing
    p hsol ht0 htT hTW (hu x) hu1 hv2 hU1 hV2

/-- Thin `hhalf` producer after positive-time maximal regularity: weighted
closeness realizes the population slice in `L²`; the generator and forcing
realizations supply the material derivative in `L²`; and the sole remaining
time input is differentiability of the fixed canonical `L²` trajectory. -/
theorem paper5WeightedHalfEnergy_hasDerivAt_of_generatorForcing_and_canonicalL2
    (p : CMParams) {T eta c t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hsol : IsClassicalSolution p T u v) (ht0 : 0 < t) (htT : t < T)
    (hTW : IsTravelingWave p c U V)
    (hu : ∀ x, 0 ≤ coMovingPath c u t x)
    (hu1 : ContDiff ℝ 1 (coMovingPath c u t))
    (hv2 : ContDiff ℝ 2 (coMovingPath c v t))
    (hU1 : ContDiff ℝ 1 U) (hV2 : ContDiff ℝ 2 V)
    (hW_meas : ∀ᶠ s in nhds t,
      AEStronglyMeasurable
        (paper5WeightedPopulation eta (coMovingPath c u) U s) volume)
    (hclose : ∀ᶠ s in nhds t, Integrable (fun x : ℝ =>
      Real.exp (2 * eta * x) *
        |coMovingPath c u s x - U x| ^ 2) volume)
    (hWt_meas : AEStronglyMeasurable
      (paper5WeightedPopulationT eta
        (paper5CoMovingMaterialTime c u) t) volume)
    (hgenerator_sq : Integrable (fun x : ℝ =>
      (paper5WeightedPopulationXX eta (coMovingPath c u) U t x +
        (c - 2 * eta) *
          paper5WeightedPopulationX eta (coMovingPath c u) U t x +
        (eta ^ 2 - c * eta) *
          paper5WeightedPopulation eta (coMovingPath c u) U t x) ^ 2)
      volume)
    (hforcing_sq : Integrable (fun x : ℝ =>
      paper5WeightedGeneratorForcing p eta
        (coMovingPath c u) (coMovingPath c v) U V t x ^ 2) volume)
    (hZ : HasDerivAt
      (fun s => wholeLineRealL2Total
        (paper5WeightedPopulation eta (coMovingPath c u) U s))
      (wholeLineRealL2Total
        (paper5WeightedPopulationT eta
          (paper5CoMovingMaterialTime c u) t)) t) :
    HasDerivAt (paper5WeightedHalfEnergy eta c u U)
      (∫ x : ℝ,
        paper5WeightedPopulation eta (coMovingPath c u) U t x *
          paper5WeightedPopulationT eta
            (paper5CoMovingMaterialTime c u) t x) t := by
  have hW_sq : ∀ᶠ s in nhds t, Integrable (fun x : ℝ =>
      paper5WeightedPopulation eta (coMovingPath c u) U s x ^ 2) volume := by
    filter_upwards [hclose] with s hs
    exact paper5WeightedPopulation_sq_integrable_of_weighted_difference hs
  have hWt_sq :=
    paper5WeightedPopulationT_sq_integrable_of_generatorForcing
      p hsol ht0 htT hTW hu hu1 hv2 hU1 hV2 hWt_meas
        hgenerator_sq hforcing_sq
  exact paper5WeightedHalfEnergy_hasDerivAt_of_canonicalL2_hasDerivAt
    hW_meas hW_sq hWt_meas hWt_sq hZ

/-- Fully concrete difference-quotient version of the preceding `hhalf`
producer.  The time frontier is now a scalar squared-error integral tending
to zero, exactly the form delivered by a raw-DQ/Fatou closure. -/
theorem paper5WeightedHalfEnergy_hasDerivAt_of_generatorForcing_and_DQ
    (p : CMParams) {T eta c t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hsol : IsClassicalSolution p T u v) (ht0 : 0 < t) (htT : t < T)
    (hTW : IsTravelingWave p c U V)
    (hu : ∀ x, 0 ≤ coMovingPath c u t x)
    (hu1 : ContDiff ℝ 1 (coMovingPath c u t))
    (hv2 : ContDiff ℝ 2 (coMovingPath c v t))
    (hU1 : ContDiff ℝ 1 U) (hV2 : ContDiff ℝ 2 V)
    (hW_meas : ∀ᶠ s in nhds t,
      AEStronglyMeasurable
        (paper5WeightedPopulation eta (coMovingPath c u) U s) volume)
    (hclose : ∀ᶠ s in nhds t, Integrable (fun x : ℝ =>
      Real.exp (2 * eta * x) *
        |coMovingPath c u s x - U x| ^ 2) volume)
    (hWt_meas : AEStronglyMeasurable
      (paper5WeightedPopulationT eta
        (paper5CoMovingMaterialTime c u) t) volume)
    (hgenerator_sq : Integrable (fun x : ℝ =>
      (paper5WeightedPopulationXX eta (coMovingPath c u) U t x +
        (c - 2 * eta) *
          paper5WeightedPopulationX eta (coMovingPath c u) U t x +
        (eta ^ 2 - c * eta) *
          paper5WeightedPopulation eta (coMovingPath c u) U t x) ^ 2)
      volume)
    (hforcing_sq : Integrable (fun x : ℝ =>
      paper5WeightedGeneratorForcing p eta
        (coMovingPath c u) (coMovingPath c v) U V t x ^ 2) volume)
    (hlim : Tendsto (fun h : ℝ => ∫ x : ℝ,
      (h⁻¹ *
          (paper5WeightedPopulation eta (coMovingPath c u) U (t + h) x -
            paper5WeightedPopulation eta (coMovingPath c u) U t x) -
        paper5WeightedPopulationT eta
          (paper5CoMovingMaterialTime c u) t x) ^ 2)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0)) :
    HasDerivAt (paper5WeightedHalfEnergy eta c u U)
      (∫ x : ℝ,
        paper5WeightedPopulation eta (coMovingPath c u) U t x *
          paper5WeightedPopulationT eta
            (paper5CoMovingMaterialTime c u) t x) t := by
  have hW_sq : ∀ᶠ s in nhds t, Integrable (fun x : ℝ =>
      paper5WeightedPopulation eta (coMovingPath c u) U s x ^ 2) volume := by
    filter_upwards [hclose] with s hs
    exact paper5WeightedPopulation_sq_integrable_of_weighted_difference hs
  have hWt_sq :=
    paper5WeightedPopulationT_sq_integrable_of_generatorForcing
      p hsol ht0 htT hTW hu hu1 hv2 hU1 hV2 hWt_meas
        hgenerator_sq hforcing_sq
  exact paper5WeightedHalfEnergy_hasDerivAt_of_integral_differenceQuotient_sq
    hW_meas hW_sq hWt_meas hWt_sq hlim

section AxiomAudit

#print axioms wholeLineRealL2Total_coe_ae
#print axioms wholeLineHalfEnergy_hasDerivAt_of_L2_hasDerivAt
#print axioms wholeLineHalfEnergy_hasDerivAt_of_canonicalL2_hasDerivAt
#print axioms wholeLineHalfEnergy_hasDerivAt_of_canonicalL2_differenceQuotient
#print axioms paper5WeightedHalfEnergy_hasDerivAt_of_canonicalL2_hasDerivAt
#print axioms
  paper5WeightedHalfEnergy_hasDerivAt_of_canonicalL2_differenceQuotient
#print axioms wholeLineRealL2_norm_sq_eq_integral_sq_of_aeEq
#print axioms
  canonicalL2_hasDerivAt_of_integral_differenceQuotient_sq_tendsto_zero
#print axioms
  wholeLineHalfEnergy_hasDerivAt_of_integral_differenceQuotient_sq
#print axioms
  paper5WeightedHalfEnergy_hasDerivAt_of_integral_differenceQuotient_sq
#print axioms wholeLine_sq_integrable_of_eq_add
#print axioms
  paper5WeightedPopulationT_eq_spatialGenerator_add_generatorForcing
#print axioms
  paper5WeightedPopulationT_sq_integrable_of_generatorForcing
#print axioms
  paper5WeightedHalfEnergy_hasDerivAt_of_generatorForcing_and_canonicalL2
#print axioms
  paper5WeightedHalfEnergy_hasDerivAt_of_generatorForcing_and_DQ

end AxiomAudit

end ShenWork.Paper1
