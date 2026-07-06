/-
  ShenWork/Paper2/IntervalChemFluxHolderCommonFold.lean

  Common-folded-noise entry points for the chemotaxis-flux Holder source
  package.  The actual heat-kernel law is still an upstream analytic frontier;
  this file only replaces the older contractive-coupling input by the more
  faithful common-noise representation interface.
-/
import ShenWork.Paper2.IntervalChemFluxHolderSourceDecay

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)

namespace ShenWork.Paper2

noncomputable section

/-- Mild-solution source package from initial-data Holder regularity plus a
common folded-noise representation for the homogeneous Neumann heat leg.

This is the common-noise analogue of
`ChemFluxCthetaSourceOn_of_gradientMild_initialHolder_components`: the uniform
`u`-Holder modulus is produced using the common folded-noise initial-leg
consumer, while the resolver-gradient Holder modulus remains explicit. -/
theorem ChemFluxCthetaSourceOn_of_gradientMild_initialHolder_commonFoldNoise_components
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    {θ H₀ Hg : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hH₀_nonneg : 0 ≤ H₀) (hHg_nonneg : 0 ≤ Hg)
    (hholder : InitialDatumHolder u₀ θ H₀)
    (hplan : ∀ t, 0 < t → t ≤ D.T → ∀ x y : intervalDomainPoint,
      NeumannHeatCommonFoldNoiseFor t x y (intervalDomainLift u₀))
    (hg_holder : ∀ s, 0 < s → s ≤ D.T → ∀ a b : ℝ,
      a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |resolverGradReal p (D.u s) a - resolverGradReal p (D.u s) b| ≤
          Hg * |a - b| ^ θ) :
    ∃ HQ : ℝ, 0 ≤ HQ ∧
      ChemFluxCthetaSourceOn p D.u D.T θ
        (D.M * (Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * (p.ν * D.M ^ p.γ)))) HQ := by
  rcases mild_orderBox_smallTime_holder_of_initialDatumHolder_common_fold_noise
      D hθ0 hθ1 hH₀_nonneg hholder hplan with
    ⟨Hu, hHu_nonneg, hu_holder⟩
  set G : ℝ := Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
      (2 * (p.ν * D.M ^ p.γ)) with hG
  set HQ : ℝ := Hu * G + D.M * Hg + D.M * G * p.β * G with hHQ
  have hG_nonneg : 0 ≤ G := by
    rw [hG]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _)))
  have hHQ_nonneg : 0 ≤ HQ := by
    rw [hHQ]
    exact add_nonneg
      (add_nonneg
        (mul_nonneg hHu_nonneg hG_nonneg)
        (mul_nonneg D.hM.le hHg_nonneg))
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg D.hM.le hG_nonneg)
          p.hβ)
        hG_nonneg)
  refine ⟨HQ, hHQ_nonneg, ?_⟩
  refine ChemFluxCthetaSourceOn_of_gradientMild_uniform_components
    (D := D) (θ := θ) (HQ := HQ) (Hu := Hu) (Hg := Hg)
    hθ0 hθ1 hHQ_nonneg hHu_nonneg hHg_nonneg ?_ hu_holder hg_holder
  rw [hHQ, hG]

/-- Common-folded-noise version of the weak small-exponent initial-holder source
package.  The only remaining heat-kernel input is the common-noise law; the
resolver-gradient Holder field is produced internally for `0 < θ < 1/2`. -/
theorem ChemFluxCthetaSourceOn_of_gradientMild_initialHolder_smallTheta_commonFoldNoise_components
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    {θ H₀ : ℝ}
    (hθ0 : 0 < θ) (hθlt : θ < (1 / 2 : ℝ))
    (hH₀_nonneg : 0 ≤ H₀)
    (hholder : InitialDatumHolder u₀ θ H₀)
    (hplan : ∀ t, 0 < t → t ≤ D.T → ∀ x y : intervalDomainPoint,
      NeumannHeatCommonFoldNoiseFor t x y (intervalDomainLift u₀)) :
    ∃ HQ : ℝ, 0 ≤ HQ ∧
      ChemFluxCthetaSourceOn p D.u D.T θ
        (D.M * (Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * (p.ν * D.M ^ p.γ)))) HQ := by
  set Hg : ℝ := (2 : ℝ) ^ (1 - θ) *
    Real.sqrt (∑' k : ℕ,
      (ShenWork.IntervalResolverWeakBounds.intervalNeumannResolverGradHolderWeight p θ k) ^ 2) *
      (2 * (p.ν * D.M ^ p.γ)) with hHg
  have hθ1 : θ < 1 := by nlinarith [hθlt]
  have hHg_nonneg : 0 ≤ Hg := by
    rw [hHg]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
        (Real.sqrt_nonneg _))
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _)))
  have hcont_on : ∀ s, 0 < s → s ≤ D.T →
      ContinuousOn (intervalDomainLift (D.u s)) (Set.Icc (0 : ℝ) 1) := by
    intro s hs0 hsT
    rw [continuousOn_iff_continuous_restrict]
    have : Set.restrict (Set.Icc (0 : ℝ) 1) (intervalDomainLift (D.u s)) =
        D.u s := by
      ext ⟨y, hy⟩
      simp [Set.restrict, intervalDomainLift, hy]
      rfl
    rw [this]
    exact D.hcont s hs0 hsT
  have hlb : ∀ s, 0 < s → s ≤ D.T → ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ intervalDomainLift (D.u s) y := by
    intro s hs0 hsT y hy
    simpa [intervalDomainLift, hy] using D.hnonneg s hs0 hsT ⟨y, hy⟩
  have hub : ∀ s, 0 < s → s ≤ D.T → ∀ y ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (D.u s) y ≤ D.M := by
    intro s hs0 hsT y hy
    have hb := D.hbound s hs0 hsT ⟨y, hy⟩
    simpa [intervalDomainLift, hy] using (abs_le.mp hb).2
  have hg_holder : ∀ s, 0 < s → s ≤ D.T → ∀ a b : ℝ,
      a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |resolverGradReal p (D.u s) a - resolverGradReal p (D.u s) b| ≤
          Hg * |a - b| ^ θ := by
    intro s hs0 hsT a b ha hb
    rw [hHg]
    exact ShenWork.IntervalResolverWeakBounds.resolverGradReal_holder_Icc_of_bounded_smallTheta
      p hθ0 hθlt (hcont_on s hs0 hsT) (hlb s hs0 hsT) (hub s hs0 hsT) ha hb
  exact ChemFluxCthetaSourceOn_of_gradientMild_initialHolder_commonFoldNoise_components
    D hθ0 hθ1 hH₀_nonneg hHg_nonneg hholder hplan hg_holder

/-- Common-folded-noise source package with the resolver-gradient Holder field
discharged from a uniform resolver-second-derivative bound. -/
theorem ChemFluxCthetaSourceOn_of_gradientMild_initialHolder_grad2_commonFoldNoise_components
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    {θ H₀ Hg : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hH₀_nonneg : 0 ≤ H₀) (hHg_nonneg : 0 ≤ Hg)
    (hholder : InitialDatumHolder u₀ θ H₀)
    (hplan : ∀ t, 0 < t → t ≤ D.T → ∀ x y : intervalDomainPoint,
      NeumannHeatCommonFoldNoiseFor t x y (intervalDomainLift u₀))
    (hdecay : ∀ s, 0 < s → s ≤ D.T → SourceCoeffQuadraticDecay p (D.u s))
    (hgrad2_bound : ∀ s, 0 < s → s ≤ D.T → ∀ z ∈ Set.Icc (0 : ℝ) 1,
      |resolverGrad2Real p (D.u s) z| ≤ Hg) :
    ∃ HQ : ℝ, 0 ≤ HQ ∧
      ChemFluxCthetaSourceOn p D.u D.T θ
        (D.M * (Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * (p.ν * D.M ^ p.γ)))) HQ := by
  have hg_holder :=
    resolverGradReal_uniform_holder_Icc_of_sourceDecay_grad2Bound
      (p := p) (u := D.u) (T := D.T) hθ0 hθ1.le hHg_nonneg hdecay hgrad2_bound
  exact ChemFluxCthetaSourceOn_of_gradientMild_initialHolder_commonFoldNoise_components
    D hθ0 hθ1 hH₀_nonneg hHg_nonneg hholder hplan hg_holder

/-- Common-folded-noise source package from a uniform source-coefficient
quadratic decay frontier. -/
theorem ChemFluxCthetaSourceOn_of_initialHolder_uniformSourceCoeff_commonFoldNoise_components
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    {θ H₀ Csrc : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hH₀_nonneg : 0 ≤ H₀)
    (hholder : InitialDatumHolder u₀ θ H₀)
    (hplan : ∀ t, 0 < t → t ≤ D.T → ∀ x y : intervalDomainPoint,
      NeumannHeatCommonFoldNoiseFor t x y (intervalDomainLift u₀))
    (Hsrc : UniformSourceCoeffQuadraticDecayOn p D.u D.T Csrc) :
    ∃ HQ : ℝ, 0 ≤ HQ ∧
      ChemFluxCthetaSourceOn p D.u D.T θ
        (D.M * (Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * (p.ν * D.M ^ p.γ)))) HQ := by
  exact ChemFluxCthetaSourceOn_of_gradientMild_initialHolder_grad2_commonFoldNoise_components
    D hθ0 hθ1 hH₀_nonneg
    (resolverGrad2UniformBound_nonneg Hsrc.Csrc_nonneg)
    hholder hplan Hsrc.sourceDecay
    (by
      intro s hs0 hsT z _hz
      exact resolverGrad2Real_uniform_bound_of_uniformSourceCoeffQuadraticDecayOn
        Hsrc s hs0 hsT z)

end

end ShenWork.Paper2
