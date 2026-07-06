/-
  ShenWork/Paper2/ChemMildC1etaCommonFoldWrappers.lean

  C1eta-facing wrappers that consume the intrinsic common-fold chem-flux data
  route, avoiding the older explicit heat-coupling input at this boundary.
-/
import ShenWork.Paper2.ChemMildC1etaUncond
import ShenWork.Paper2.IntervalChemFluxHolderCommonFold

open MeasureTheory
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

namespace ShenWork.Paper2

noncomputable section

/-- Intrinsic common-fold route from initial Holder data to the differentiated
`[0,1]` C1/eta bridge package. -/
theorem chemMild_C1eta_diffSlice_of_initialHolder_intrinsic_cutoff
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (Dsol : GradientMildSolutionData p u₀)
    {χ₀ t θ η H₀ Ainit Areact : ℝ}
    {w initLeg reactLeg : ℝ → ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hθη : η < θ)
    (hθ0 : 0 < θ) (hθlt : θ < (1 / 2 : ℝ))
    (hH₀_nonneg : 0 ≤ H₀)
    (hholder : InitialDatumHolder u₀ θ H₀)
    (ht : 0 < t) (htT : t ≤ Dsol.T)
    (init_diff : Differentiable ℝ initLeg) (react_diff : Differentiable ℝ reactLeg)
    (hAinit_nn : 0 ≤ Ainit) (hAreact_nn : 0 ≤ Areact)
    (w_split : ∀ x : ℝ,
      w x = initLeg x - χ₀ * chemLitLeg t
        (chemFluxCthetaCutoffSource p Dsol.u Dsol.T) x + reactLeg x)
    (init_holder : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      |deriv initLeg x - deriv initLeg y| ≤ Ainit * |x - y| ^ η)
    (react_holder : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      |deriv reactLeg x - deriv reactLeg y| ≤ Areact * |x - y| ^ η) :
    ∃ HQ : ℝ, 0 ≤ HQ ∧
      DifferentiatedMildSliceDiffOn χ₀ t θ η
        (Dsol.M * (Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * (p.ν * Dsol.M ^ p.γ)))) HQ
        (2 * (Dsol.M * (Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * (p.ν * Dsol.M ^ p.γ)))))
        (chemFluxCthetaCutoffSource p Dsol.u Dsol.T)
        w initLeg reactLeg Ainit (chemDuhamelConst t θ η HQ) Areact := by
  rcases ChemLegData_of_gradientMild_initialHolder_smallTheta_intrinsic_cutoff_components
      Dsol hθ0 hθlt hH₀_nonneg hholder ht htT with
    ⟨HQ, hHQ_nonneg, chemData⟩
  refine ⟨HQ, hHQ_nonneg, ?_⟩
  exact differentiatedMildSliceDiffOn_of_brick4_chem hη0 hη1 hθη chemData
    init_diff react_diff hAinit_nn hAreact_nn w_split init_holder react_holder

/-- Intrinsic common-fold route from initial Holder data to the C1/eta slice
conclusion and Wiener coefficient summability. -/
theorem chemMild_C1eta_sliceDiffOn_of_initialHolder_intrinsic_cutoff
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (Dsol : GradientMildSolutionData p u₀)
    {χ₀ t θ η H₀ Ainit Areact : ℝ}
    {w initLeg reactLeg : ℝ → ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hθη : η < θ)
    (hθ0 : 0 < θ) (hθlt : θ < (1 / 2 : ℝ))
    (hH₀_nonneg : 0 ≤ H₀)
    (hholder : InitialDatumHolder u₀ θ H₀)
    (ht : 0 < t) (htT : t ≤ Dsol.T)
    (init_diff : Differentiable ℝ initLeg) (react_diff : Differentiable ℝ reactLeg)
    (hAinit_nn : 0 ≤ Ainit) (hAreact_nn : 0 ≤ Areact)
    (w_split : ∀ x : ℝ,
      w x = initLeg x - χ₀ * chemLitLeg t
        (chemFluxCthetaCutoffSource p Dsol.u Dsol.T) x + reactLeg x)
    (init_holder : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      |deriv initLeg x - deriv initLeg y| ≤ Ainit * |x - y| ^ η)
    (react_holder : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      |deriv reactLeg x - deriv reactLeg y| ≤ Areact * |x - y| ^ η)
    (hNeumann : derivWithin w (Set.Icc (0 : ℝ) 1) 0 = 0 ∧
      derivWithin w (Set.Icc (0 : ℝ) 1) 1 = 0) :
    ∃ HQ : ℝ, 0 ≤ HQ ∧
      DifferentiableOn ℝ w (Set.Icc (0:ℝ) 1) ∧
        (∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
          |derivWithin w (Set.Icc (0:ℝ) 1) x -
              derivWithin w (Set.Icc (0:ℝ) 1) y|
            ≤ (Ainit + |χ₀| * chemDuhamelConst t θ η HQ + Areact) *
              |x - y| ^ η) ∧
        Summable (fun n : ℕ => |cosineCoeffs w n|) := by
  rcases
      chemMild_C1eta_diffSlice_of_initialHolder_intrinsic_cutoff
        Dsol hη0 hη1 hθη hθ0 hθlt hH₀_nonneg hholder ht htT
        init_diff react_diff hAinit_nn hAreact_nn w_split init_holder react_holder with
    ⟨HQ, hHQ_nonneg, Dslice⟩
  refine ⟨HQ, hHQ_nonneg, ?_⟩
  exact chemMild_C1eta_slice_diffOn hη0 hη1.le Dslice hNeumann

/-- Intrinsic common-fold route with the canonical homogeneous initial value
leg; the reaction leg remains explicit. -/
theorem chemMild_C1eta_diffSlice_of_initialValueLeg_intrinsic_cutoff
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (Dsol : GradientMildSolutionData p u₀)
    {χ₀ t θ η H₀ Cu₀ Areact : ℝ}
    {w reactLeg : ℝ → ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hθη : η < θ)
    (hθ0 : 0 < θ) (hθlt : θ < (1 / 2 : ℝ))
    (hH₀_nonneg : 0 ≤ H₀)
    (hholder : InitialDatumHolder u₀ θ H₀)
    (ht : 0 < t) (htT : t ≤ Dsol.T)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀)
      (ShenWork.IntervalDomain.intervalMeasure 1))
    (hu₀_bdd : ∀ y, |intervalDomainLift u₀ y| ≤ Cu₀)
    (hCu₀_nn : 0 ≤ Cu₀)
    (react_diff : Differentiable ℝ reactLeg)
    (hAreact_nn : 0 ≤ Areact)
    (w_split : ∀ x : ℝ,
      w x = initialValueLeg t (intervalDomainLift u₀) x - χ₀ * chemLitLeg t
        (chemFluxCthetaCutoffSource p Dsol.u Dsol.T) x + reactLeg x)
    (react_holder : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      |deriv reactLeg x - deriv reactLeg y| ≤ Areact * |x - y| ^ η) :
    ∃ HQ : ℝ, 0 ≤ HQ ∧
      DifferentiatedMildSliceDiffOn χ₀ t θ η
        (Dsol.M * (Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * (p.ν * Dsol.M ^ p.γ)))) HQ
        (2 * (Dsol.M * (Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * (p.ν * Dsol.M ^ p.γ)))))
        (chemFluxCthetaCutoffSource p Dsol.u Dsol.T)
        w (initialValueLeg t (intervalDomainLift u₀)) reactLeg
        (initialValueLegDerivHolderConst t η Cu₀) (chemDuhamelConst t θ η HQ)
        Areact := by
  have init_diff : Differentiable ℝ (initialValueLeg t (intervalDomainLift u₀)) :=
    initialValueLeg_differentiable ht hu₀_meas hu₀_bdd
  have hAinit_nn : 0 ≤ initialValueLegDerivHolderConst t η Cu₀ :=
    initialValueLegDerivHolderConst_nonneg ht hCu₀_nn
  have init_holder : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      |deriv (initialValueLeg t (intervalDomainLift u₀)) x -
          deriv (initialValueLeg t (intervalDomainLift u₀)) y|
        ≤ initialValueLegDerivHolderConst t η Cu₀ * |x - y| ^ η :=
    initialValueLeg_deriv_holder_Icc ht hη0 hη1 hu₀_meas hu₀_bdd
  exact
    chemMild_C1eta_diffSlice_of_initialHolder_intrinsic_cutoff
      Dsol hη0 hη1 hθη hθ0 hθlt hH₀_nonneg hholder ht htT
      init_diff react_diff hAinit_nn hAreact_nn w_split init_holder react_holder

/-- Intrinsic common-fold route with canonical phase-1 value legs. -/
theorem chemMild_C1eta_diffSlice_of_phase1ValueLegs_intrinsic_cutoff
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (Dsol : GradientMildSolutionData p u₀)
    {χ₀ t θ η H₀ Cu₀ CL : ℝ}
    {L : ℝ → ℝ → ℝ} {w : ℝ → ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hθη : η < θ)
    (hθ0 : 0 < θ) (hθlt : θ < (1 / 2 : ℝ))
    (hH₀_nonneg : 0 ≤ H₀)
    (hholder : InitialDatumHolder u₀ θ H₀)
    (ht : 0 < t) (htT : t ≤ Dsol.T)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀)
      (ShenWork.IntervalDomain.intervalMeasure 1))
    (hu₀_bdd : ∀ y, |intervalDomainLift u₀ y| ≤ Cu₀)
    (hCu₀_nn : 0 ≤ Cu₀)
    (hL_meas : Measurable (Function.uncurry L))
    (hCL_nn : 0 ≤ CL)
    (hL_bdd : ∀ s y, |L s y| ≤ CL)
    (w_split : ∀ x : ℝ,
      w x = initialValueLeg t (intervalDomainLift u₀) x - χ₀ * chemLitLeg t
        (chemFluxCthetaCutoffSource p Dsol.u Dsol.T) x + reactionValueLeg t L x) :
    ∃ HQ : ℝ, 0 ≤ HQ ∧
      DifferentiatedMildSliceDiffOn χ₀ t θ η
        (Dsol.M * (Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * (p.ν * Dsol.M ^ p.γ)))) HQ
        (2 * (Dsol.M * (Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * (p.ν * Dsol.M ^ p.γ)))))
        (chemFluxCthetaCutoffSource p Dsol.u Dsol.T)
        w (initialValueLeg t (intervalDomainLift u₀)) (reactionValueLeg t L)
        (initialValueLegDerivHolderConst t η Cu₀) (chemDuhamelConst t θ η HQ)
        (reactionDerivLegHolderConst t η CL) := by
  have react_diff : Differentiable ℝ (reactionValueLeg t L) := by
    intro x
    exact (reactionValueLeg_hasDerivAt ht hL_meas hCL_nn hL_bdd x).differentiableAt
  have hAreact_nn : 0 ≤ reactionDerivLegHolderConst t η CL :=
    reactionDerivLegHolderConst_nonneg ht hCL_nn
  have react_holder_deriv : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      |deriv (reactionValueLeg t L) x - deriv (reactionValueLeg t L) y|
        ≤ reactionDerivLegHolderConst t η CL * |x - y| ^ η := by
    intro x hx y hy
    rw [reactionValueLeg_deriv_eq ht hL_meas hCL_nn hL_bdd x,
      reactionValueLeg_deriv_eq ht hL_meas hCL_nn hL_bdd y]
    exact reactionDerivLeg_holder_Icc ht hη0 hη1 hL_meas hCL_nn hL_bdd x hx y hy
  exact
    chemMild_C1eta_diffSlice_of_initialValueLeg_intrinsic_cutoff
      Dsol hη0 hη1 hθη hθ0 hθlt hH₀_nonneg hholder ht htT
      hu₀_meas hu₀_bdd hCu₀_nn react_diff hAreact_nn w_split react_holder_deriv

/-- Intrinsic common-fold route with canonical phase-1 value legs to the C1/eta
slice conclusion and Wiener coefficient summability. -/
theorem chemMild_C1eta_sliceDiffOn_of_phase1ValueLegs_intrinsic_cutoff
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (Dsol : GradientMildSolutionData p u₀)
    {χ₀ t θ η H₀ Cu₀ CL : ℝ}
    {L : ℝ → ℝ → ℝ} {w : ℝ → ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hθη : η < θ)
    (hθ0 : 0 < θ) (hθlt : θ < (1 / 2 : ℝ))
    (hH₀_nonneg : 0 ≤ H₀)
    (hholder : InitialDatumHolder u₀ θ H₀)
    (ht : 0 < t) (htT : t ≤ Dsol.T)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀)
      (ShenWork.IntervalDomain.intervalMeasure 1))
    (hu₀_bdd : ∀ y, |intervalDomainLift u₀ y| ≤ Cu₀)
    (hCu₀_nn : 0 ≤ Cu₀)
    (hL_meas : Measurable (Function.uncurry L))
    (hCL_nn : 0 ≤ CL)
    (hL_bdd : ∀ s y, |L s y| ≤ CL)
    (w_split : ∀ x : ℝ,
      w x = initialValueLeg t (intervalDomainLift u₀) x - χ₀ * chemLitLeg t
        (chemFluxCthetaCutoffSource p Dsol.u Dsol.T) x + reactionValueLeg t L x)
    (hNeumann : derivWithin w (Set.Icc (0 : ℝ) 1) 0 = 0 ∧
      derivWithin w (Set.Icc (0 : ℝ) 1) 1 = 0) :
    ∃ HQ : ℝ, 0 ≤ HQ ∧
      DifferentiableOn ℝ w (Set.Icc (0:ℝ) 1) ∧
        (∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
          |derivWithin w (Set.Icc (0:ℝ) 1) x -
              derivWithin w (Set.Icc (0:ℝ) 1) y|
            ≤ (initialValueLegDerivHolderConst t η Cu₀ +
                |χ₀| * chemDuhamelConst t θ η HQ +
                  reactionDerivLegHolderConst t η CL) *
              |x - y| ^ η) ∧
        Summable (fun n : ℕ => |cosineCoeffs w n|) := by
  rcases
      chemMild_C1eta_diffSlice_of_phase1ValueLegs_intrinsic_cutoff
        Dsol hη0 hη1 hθη hθ0 hθlt hH₀_nonneg hholder ht htT
        hu₀_meas hu₀_bdd hCu₀_nn hL_meas hCL_nn hL_bdd w_split with
    ⟨HQ, hHQ_nonneg, Dslice⟩
  refine ⟨HQ, hHQ_nonneg, ?_⟩
  exact chemMild_C1eta_slice_diffOn hη0 hη1.le Dslice hNeumann

end

end ShenWork.Paper2
