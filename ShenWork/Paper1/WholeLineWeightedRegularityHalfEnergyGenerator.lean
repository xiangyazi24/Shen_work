import ShenWork.Paper1.WholeLineWeightedRegularityGeneratorIdentification
import ShenWork.Paper1.WholeLineWeightedRegularityGeneratorPairing

open Filter MeasureTheory Set Topology
open scoped RealInnerProductSpace

noncomputable section

namespace ShenWork.Paper1

/-!
# Ordinary weighted half-energy derivative from the exact mild generator

The generator trajectory itself need not be strongly continuous.  Its scalar
pairing with the state is continuous after diffusion and drift integration by
parts, because the resulting expression contains only the state, its first
spatial derivative, and the nonlinear forcing.
-/

/-- Positive-time half-energy closure from natural exact-weight state,
gradient, forcing, and mild-generator trajectories.  The spatial-generator
representative and the material-velocity representative are both constructed
internally from the right mild derivative and the classical PDE. -/
theorem paper5WeightedHalfEnergy_hasDerivAt_of_exactGeneratorTrajectories
    (p : CMParams) {T eta c t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    {X A F : ℝ → WholeLineRealL2}
    (ht0 : 0 < t) (htT : t < T)
    (hsol : IsClassicalSolution p T u v)
    (hTW : IsTravelingWave p c U V)
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V)
    (hphi_meas : ∀ q, 0 < q → AEStronglyMeasurable
      (paper5WeightedPopulation eta (coMovingPath c u) U q) volume)
    (hphi_sq : ∀ q, 0 < q → Integrable (fun x : ℝ =>
      paper5WeightedPopulation eta (coMovingPath c u) U q x ^ 2) volume)
    (hZcont : ContinuousOn (fun q => wholeLineRealL2Total
      (paper5WeightedPopulation eta (coMovingPath c u) U q))
      (Set.Ioo (0 : ℝ) T))
    (hXcont : ContinuousOn X (Set.Ioo (0 : ℝ) T))
    (hFcont : ContinuousOn F (Set.Ioo (0 : ℝ) T))
    (hu : ∀ q ∈ Set.Ioo (0 : ℝ) T, ∀ x,
      0 ≤ coMovingPath c u q x)
    (hu2 : ∀ q ∈ Set.Ioo (0 : ℝ) T,
      ContDiff ℝ 2 (coMovingPath c u q))
    (hv2 : ∀ q ∈ Set.Ioo (0 : ℝ) T,
      ContDiff ℝ 2 (coMovingPath c v q))
    (hclose : ∀ q ∈ Set.Ioo (0 : ℝ) T, Integrable (fun x =>
      Real.exp (2 * eta * x) *
        |coMovingPath c u q x - U x| ^ 2))
    (hWx2 : ∀ q ∈ Set.Ioo (0 : ℝ) T, Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U q x ^ 2))
    (hXrep : ∀ q ∈ Set.Ioo (0 : ℝ) T,
      (((X q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        paper5WeightedPopulationX eta (coMovingPath c u) U q))
    (hFrep : ∀ q ∈ Set.Ioo (0 : ℝ) T,
      (((F q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V q))
    (hZright : ∀ q ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s => wholeLineRealL2Total
        (paper5WeightedPopulation eta (coMovingPath c u) U s))
        (A q + F q) (Set.Ici q) q)
    (hpoint : ∀ q ∈ Set.Ioo (0 : ℝ) T, ∀ x,
      HasDerivAt
        (fun s => paper5WeightedPopulation eta (coMovingPath c u) U s x)
        (paper5WeightedPopulationT eta
          (paper5CoMovingMaterialTime c u) q x) q) :
    HasDerivAt (paper5WeightedHalfEnergy eta c u U)
      (∫ x : ℝ,
        paper5WeightedPopulation eta (coMovingPath c u) U t x *
          paper5WeightedPopulationT eta
            (paper5CoMovingMaterialTime c u) t x) t := by
  let Z : ℝ → WholeLineRealL2 := fun q => wholeLineRealL2Total
    (paper5WeightedPopulation eta (coMovingPath c u) U q)
  have hArep : ∀ q ∈ Set.Ioo (0 : ℝ) T,
      (((A q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        fun x =>
          paper5WeightedPopulationXX eta (coMovingPath c u) U q x +
            (c - 2 * eta) *
              paper5WeightedPopulationX eta (coMovingPath c u) U q x +
            (eta ^ 2 - c * eta) *
              paper5WeightedPopulation eta (coMovingPath c u) U q x) := by
    intro q hq
    apply
      paper5WeightedFullGenerator_coe_ae_spatialGenerator_of_rightDerivative
        p hsol hq.1 hq.2 hTW (hu q hq)
          ((hu2 q hq).of_le (by norm_num)) (hv2 q hq)
          (hU2.of_le (by norm_num)) hV2
    · intro n
      exact hphi_meas _ (add_pos hq.1 (by positivity))
    · intro n
      exact hphi_sq _ (add_pos hq.1 (by positivity))
    · exact hphi_meas q hq.1
    · exact hphi_sq q hq.1
    · exact hZright q hq
    · exact hpoint q hq
    · exact hFrep q hq
  have hVrep : ∀ q ∈ Set.Ioo (0 : ℝ) T,
      ((((A q + F q : WholeLineRealL2) : ℝ → ℝ)) =ᵐ[volume]
        paper5WeightedPopulationT eta
          (paper5CoMovingMaterialTime c u) q) := by
    intro q hq
    filter_upwards [Lp.coeFn_add (A q) (F q), hArep q hq, hFrep q hq]
      with x hadd hA hF
    rw [hadd]
    simp only [Pi.add_apply]
    rw [hA, hF]
    exact
      (paper5WeightedPopulationT_eq_spatialGenerator_add_generatorForcing
        p hsol hq.1 hq.2 hTW (hu q hq x)
          ((hu2 q hq).of_le (by norm_num)) (hv2 q hq)
          (hU2.of_le (by norm_num)) hV2).symm
  have hpair : ∀ q ∈ Set.Ioo (0 : ℝ) T, ContinuousAt
      (fun s => ⟪Z s, A s + F s⟫) q := by
    intro q hq
    apply wholeLineRealL2_inner_generator_add_forcing_continuousAt
      (hZcont.continuousAt (isOpen_Ioo.mem_nhds hq))
      (hXcont.continuousAt (isOpen_Ioo.mem_nhds hq))
      (hFcont.continuousAt (isOpen_Ioo.mem_nhds hq))
    have hopen : ∀ᶠ s in nhds q, s ∈ Set.Ioo (0 : ℝ) T :=
      isOpen_Ioo.mem_nhds hq
    filter_upwards [hopen] with s hs
    apply paper5WeightedPopulation_inner_spatialGenerator_eq
      (hu2 s hs) hU2 (hclose s hs) (hWx2 s hs)
    · exact wholeLineRealL2Total_coe_ae _
        (hphi_meas s hs.1) (hphi_sq s hs.1)
    · exact hXrep s hs
    · exact hArep s hs
  apply paper5WeightedHalfEnergy_hasDerivAt_of_continuous_right_pairing_positive
    ht0 htT
  · intro q hq
    exact hphi_meas q hq.1
  · intro q hq
    exact hphi_sq q hq.1
  · exact hZcont
  · intro q hq
    simpa only [Z] using hpair q hq
  · intro q hq
    simpa only [Z] using hZright q hq
  · exact hVrep

section AxiomAudit

#print axioms
  paper5WeightedHalfEnergy_hasDerivAt_of_exactGeneratorTrajectories

end AxiomAudit

end ShenWork.Paper1
