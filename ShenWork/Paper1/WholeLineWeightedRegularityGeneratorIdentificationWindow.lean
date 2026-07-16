import ShenWork.Paper1.WholeLineWeightedRegularityGeneratorIdentification

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Window-local identification of the exact weighted generator

The original right-derivative identification used the fixed increments
`(n+1)⁻¹`, which need not remain inside a prescribed positive-time restart
window.  Here the increment sequence is explicit, and then specialized to a
scaled sequence contained in `[t,r]`.
-/

/-- A right strong derivative is identified pointwise along any positive
increment sequence tending to zero. -/
theorem wholeLineRealL2Total_hasDerivWithinAt_coe_ae_of_pointwise_along
    {phi phi_t : ℝ → ℝ → ℝ} {t : ℝ} {V : WholeLineRealL2}
    {eps : ℕ → ℝ}
    (heps_pos : ∀ n, 0 < eps n)
    (heps : Tendsto eps atTop (𝓝 0))
    (hphi_meas : ∀ n : ℕ,
      AEStronglyMeasurable (phi (t + eps n)) volume)
    (hphi_sq : ∀ n : ℕ, Integrable (fun x : ℝ =>
      phi (t + eps n) x ^ 2) volume)
    (hphi0_meas : AEStronglyMeasurable (phi t) volume)
    (hphi0_sq : Integrable (fun x : ℝ => phi t x ^ 2) volume)
    (hright : HasDerivWithinAt
      (fun s => wholeLineRealL2Total (phi s)) V (Set.Ici t) t)
    (hpoint : ∀ x, HasDerivAt (fun s => phi s x) (phi_t t x) t) :
    ((V : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] phi_t t := by
  let Q : ℕ → WholeLineRealL2 := fun n =>
    (eps n)⁻¹ •
      (wholeLineRealL2Total (phi (t + eps n)) -
        wholeLineRealL2Total (phi t))
  let q : ℕ → ℝ → ℝ := fun n x =>
    (eps n)⁻¹ * (phi (t + eps n) x - phi t x)
  have hQ : Tendsto Q atTop (𝓝 V) := by
    simpa only [Q] using
      hasDerivWithinAt_Ici_forwardSlope_sequence hright heps_pos heps
  have hrep : ∀ n, ((Q n : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] q n := by
    intro n
    have hplus := wholeLineRealL2Total_coe_ae
      (phi (t + eps n)) (hphi_meas n) (hphi_sq n)
    have hzero := wholeLineRealL2Total_coe_ae
      (phi t) hphi0_meas hphi0_sq
    filter_upwards [Lp.coeFn_sub
        (wholeLineRealL2Total (phi (t + eps n)))
        (wholeLineRealL2Total (phi t)),
      Lp.coeFn_smul (eps n)⁻¹
        (wholeLineRealL2Total (phi (t + eps n)) -
          wholeLineRealL2Total (phi t)),
      hplus, hzero] with x hsub hsmul hplusx hzerox
    dsimp only [Q, q]
    rw [hsmul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hplusx, hzerox]
  have hq : ∀ x, Tendsto (fun n => q n x) atTop (𝓝 (phi_t t x)) := by
    intro x
    have hslope := (hpoint x).tendsto_slope_zero_right
    have hepsWithin : Tendsto eps atTop (𝓝[>] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨heps, ?_⟩
      exact Eventually.of_forall fun n => heps_pos n
    have hcomp := hslope.comp hepsWithin
    simpa only [q, Function.comp_apply, smul_eq_mul] using hcomp
  exact wholeLineRealL2_limit_coe_ae_of_pointwise hQ hrep hq

/-- Window-local form: all representatives used to identify a right
derivative lie in the supplied closed right window. -/
theorem wholeLineRealL2Total_hasDerivWithinAt_coe_ae_of_pointwise_window
    {phi phi_t : ℝ → ℝ → ℝ} {t r : ℝ} {V : WholeLineRealL2}
    (htr : t < r)
    (hphi_meas : ∀ s ∈ Set.Icc t r,
      AEStronglyMeasurable (phi s) volume)
    (hphi_sq : ∀ s ∈ Set.Icc t r,
      Integrable (fun x : ℝ => phi s x ^ 2) volume)
    (hright : HasDerivWithinAt
      (fun s => wholeLineRealL2Total (phi s)) V (Set.Ici t) t)
    (hpoint : ∀ x, HasDerivAt (fun s => phi s x) (phi_t t x) t) :
    ((V : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] phi_t t := by
  let eps : ℕ → ℝ := fun n =>
    (r - t) * (((n + 1 : ℕ) : ℝ)⁻¹)
  have heps_pos : ∀ n, 0 < eps n := by
    intro n
    dsimp only [eps]
    exact mul_pos (sub_pos.mpr htr) (inv_pos.mpr (by positivity))
  have hinv : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)⁻¹))
      atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0))
  have heps : Tendsto eps atTop (𝓝 0) := by
    simpa only [eps, mul_zero] using hinv.const_mul (r - t)
  have heps_le : ∀ n, eps n ≤ r - t := by
    intro n
    have hden : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      norm_num
    have hile : (((n + 1 : ℕ) : ℝ)⁻¹) ≤ 1 :=
      inv_le_one_of_one_le₀ hden
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hile (sub_nonneg.mpr htr.le)
  apply wholeLineRealL2Total_hasDerivWithinAt_coe_ae_of_pointwise_along
    heps_pos heps
  · intro n
    exact hphi_meas _ ⟨by linarith [heps_pos n], by linarith [heps_le n]⟩
  · intro n
    exact hphi_sq _ ⟨by linarith [heps_pos n], by linarith [heps_le n]⟩
  · exact hphi_meas t ⟨le_rfl, htr.le⟩
  · exact hphi_sq t ⟨le_rfl, htr.le⟩
  · exact hright
  · exact hpoint

/-- Classical window-local specialization: the exact semigroup-generator
summand is the conjugated spatial generator. -/
theorem paper5WeightedFullGenerator_coe_ae_spatialGenerator_of_rightDerivative_window
    (p : CMParams) {T eta c t r : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    {A F : WholeLineRealL2}
    (hsol : IsClassicalSolution p T u v) (ht0 : 0 < t) (htT : t < T)
    (htr : t < r)
    (hTW : IsTravelingWave p c U V)
    (hu : ∀ x, 0 ≤ coMovingPath c u t x)
    (hu1 : ContDiff ℝ 1 (coMovingPath c u t))
    (hv2 : ContDiff ℝ 2 (coMovingPath c v t))
    (hU1 : ContDiff ℝ 1 U) (hV2 : ContDiff ℝ 2 V)
    (hW_meas : ∀ s ∈ Set.Icc t r, AEStronglyMeasurable
      (paper5WeightedPopulation eta (coMovingPath c u) U s) volume)
    (hW_sq : ∀ s ∈ Set.Icc t r, Integrable (fun x : ℝ =>
      paper5WeightedPopulation eta (coMovingPath c u) U s x ^ 2) volume)
    (hright : HasDerivWithinAt
      (fun s => wholeLineRealL2Total
        (paper5WeightedPopulation eta (coMovingPath c u) U s))
      (A + F) (Set.Ici t) t)
    (hpoint : ∀ x, HasDerivAt
      (fun s => paper5WeightedPopulation eta (coMovingPath c u) U s x)
      (paper5WeightedPopulationT eta
        (paper5CoMovingMaterialTime c u) t x) t)
    (hFrep : (((F : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      paper5WeightedGeneratorForcing p eta
        (coMovingPath c u) (coMovingPath c v) U V t)) :
    (((A : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      fun x =>
        paper5WeightedPopulationXX eta (coMovingPath c u) U t x +
          (c - 2 * eta) *
            paper5WeightedPopulationX eta (coMovingPath c u) U t x +
          (eta ^ 2 - c * eta) *
            paper5WeightedPopulation eta (coMovingPath c u) U t x) := by
  have htotal : ((((A + F : WholeLineRealL2) : ℝ → ℝ)) =ᵐ[volume]
      paper5WeightedPopulationT eta
        (paper5CoMovingMaterialTime c u) t) :=
    wholeLineRealL2Total_hasDerivWithinAt_coe_ae_of_pointwise_window
      htr hW_meas hW_sq hright hpoint
  apply wholeLineRealL2_spatialGenerator_coe_ae_of_total_and_forcing
    htotal hFrep
  intro x
  exact paper5WeightedPopulationT_eq_spatialGenerator_add_generatorForcing
    p hsol ht0 htT hTW (hu x) hu1 hv2 hU1 hV2

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.wholeLineRealL2Total_hasDerivWithinAt_coe_ae_of_pointwise_along
#print axioms
  ShenWork.Paper1.wholeLineRealL2Total_hasDerivWithinAt_coe_ae_of_pointwise_window
#print axioms
  ShenWork.Paper1.paper5WeightedFullGenerator_coe_ae_spatialGenerator_of_rightDerivative_window
