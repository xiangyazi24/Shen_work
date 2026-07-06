/-
  ShenWork/Paper2/IntervalChemFluxHolderCommonFoldC1eta.lean

  C1/eta-facing `ChemLegData` wrappers for the non-smallTheta intrinsic
  common-fold chemotaxis-flux Holder routes.
-/

import ShenWork.Paper2.IntervalChemFluxHolderCommonFold

open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)

namespace ShenWork.Paper2

noncomputable section

/-- C1/eta-facing `ChemLegData` from the intrinsic grad2 source route. -/
theorem ChemLegData_of_gradientMild_initialHolder_grad2_intrinsic_cutoff_components
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    {t θ H₀ Hg : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hH₀_nonneg : 0 ≤ H₀) (hHg_nonneg : 0 ≤ Hg)
    (hholder : InitialDatumHolder u₀ θ H₀)
    (hdecay : ∀ s, 0 < s → s ≤ D.T → SourceCoeffQuadraticDecay p (D.u s))
    (hgrad2_bound : ∀ s, 0 < s → s ≤ D.T → ∀ z ∈ Set.Icc (0 : ℝ) 1,
      |resolverGrad2Real p (D.u s) z| ≤ Hg)
    (ht : 0 < t) (htT : t ≤ D.T) :
    ∃ HQ : ℝ, 0 ≤ HQ ∧
      ChemLegData t θ
        (D.M * (Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * (p.ν * D.M ^ p.γ)))) HQ
        (2 * (D.M * (Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * (p.ν * D.M ^ p.γ)))))
        (chemFluxCthetaCutoffSource p D.u D.T) := by
  rcases ChemFluxCthetaSourceOn_of_gradientMild_initialHolder_grad2_intrinsic_components
      D hθ0 hθ1 hH₀_nonneg hHg_nonneg hholder hdecay hgrad2_bound with
    ⟨HQ, hHQ_nonneg, Hsource⟩
  exact ⟨HQ, hHQ_nonneg,
    ChemLegData_of_gradientMild_CthetaSourceOn_cutoff D Hsource ht htT⟩

/-- C1/eta-facing `ChemLegData` from the intrinsic uniform source-coefficient
route. -/
theorem ChemLegData_of_initialHolder_uniformSourceCoeff_intrinsic_cutoff_components
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    {t θ H₀ Csrc : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hH₀_nonneg : 0 ≤ H₀)
    (hholder : InitialDatumHolder u₀ θ H₀)
    (Hsrc : UniformSourceCoeffQuadraticDecayOn p D.u D.T Csrc)
    (ht : 0 < t) (htT : t ≤ D.T) :
    ∃ HQ : ℝ, 0 ≤ HQ ∧
      ChemLegData t θ
        (D.M * (Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * (p.ν * D.M ^ p.γ)))) HQ
        (2 * (D.M * (Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * (p.ν * D.M ^ p.γ)))))
        (chemFluxCthetaCutoffSource p D.u D.T) := by
  rcases ChemFluxCthetaSourceOn_of_initialHolder_uniformSourceCoeff_intrinsic_components
      D hθ0 hθ1 hH₀_nonneg hholder Hsrc with
    ⟨HQ, hHQ_nonneg, Hsource⟩
  exact ⟨HQ, hHQ_nonneg,
    ChemLegData_of_gradientMild_CthetaSourceOn_cutoff D Hsource ht htT⟩

end

end ShenWork.Paper2
