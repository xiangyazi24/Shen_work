import ShenWork.Paper1.WholeLineWeightedRegularityHalfEnergyGenerator

open Filter MeasureTheory Set Topology
open scoped RealInnerProductSpace

noncomputable section

namespace ShenWork.Paper1

/-!
# Weighted half-energy differentiation on a local positive-time window

The mild restart used at a fixed positive time is naturally available only
on a short window around that time.  The quadratic-energy argument is local,
so its state, gradient, and forcing trajectories need not be extended to the
whole maximal time interval.
-/

/-- Local-window form of the exact-generator half-energy closure.  Global
weighted `H0` measurability is retained only for the canonical positive
difference-quotient sequence used to identify the spatial generator. -/
theorem paper5WeightedHalfEnergy_hasDerivAt_of_exactGeneratorWindow
    (p : CMParams) {T eta c L R t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    {X A F : ℝ → WholeLineRealL2}
    (hL0 : 0 < L) (hLt : L < t) (htR : t < R) (hRT : R < T)
    (hsol : IsClassicalSolution p T u v)
    (hTW : IsTravelingWave p c U V)
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V)
    (hphi_meas : ∀ q, 0 < q → AEStronglyMeasurable
      (paper5WeightedPopulation eta (coMovingPath c u) U q) volume)
    (hphi_sq : ∀ q, 0 < q → Integrable (fun x : ℝ =>
      paper5WeightedPopulation eta (coMovingPath c u) U q x ^ 2) volume)
    (hZcont : ContinuousOn (fun q => wholeLineRealL2Total
      (paper5WeightedPopulation eta (coMovingPath c u) U q))
      (Set.Ioo L R))
    (hXcont : ContinuousOn X (Set.Ioo L R))
    (hFcont : ContinuousOn F (Set.Ioo L R))
    (hu : ∀ q ∈ Set.Ioo L R, ∀ x, 0 ≤ coMovingPath c u q x)
    (hu2 : ∀ q ∈ Set.Ioo L R,
      ContDiff ℝ 2 (coMovingPath c u q))
    (hv2 : ∀ q ∈ Set.Ioo L R,
      ContDiff ℝ 2 (coMovingPath c v q))
    (hclose : ∀ q ∈ Set.Ioo L R, Integrable (fun x =>
      Real.exp (2 * eta * x) *
        |coMovingPath c u q x - U x| ^ 2))
    (hWx2 : ∀ q ∈ Set.Ioo L R, Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U q x ^ 2))
    (hXrep : ∀ q ∈ Set.Ioo L R,
      (((X q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        paper5WeightedPopulationX eta (coMovingPath c u) U q))
    (hFrep : ∀ q ∈ Set.Ioo L R,
      (((F q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V q))
    (hZright : ∀ q ∈ Set.Ioo L R,
      HasDerivWithinAt (fun s => wholeLineRealL2Total
        (paper5WeightedPopulation eta (coMovingPath c u) U s))
        (A q + F q) (Set.Ici q) q)
    (hpoint : ∀ q ∈ Set.Ioo L R, ∀ x,
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
  have hArep : ∀ q ∈ Set.Ioo L R,
      (((A q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        fun x =>
          paper5WeightedPopulationXX eta (coMovingPath c u) U q x +
            (c - 2 * eta) *
              paper5WeightedPopulationX eta (coMovingPath c u) U q x +
            (eta ^ 2 - c * eta) *
              paper5WeightedPopulation eta (coMovingPath c u) U q x) := by
    intro q hq
    have hq0 : 0 < q := hL0.trans hq.1
    have hqT : q < T := hq.2.trans hRT
    apply
      paper5WeightedFullGenerator_coe_ae_spatialGenerator_of_rightDerivative
        p hsol hq0 hqT hTW (hu q hq)
          ((hu2 q hq).of_le (by norm_num)) (hv2 q hq)
          (hU2.of_le (by norm_num)) hV2
    · intro n
      exact hphi_meas _ (add_pos hq0 (by positivity))
    · intro n
      exact hphi_sq _ (add_pos hq0 (by positivity))
    · exact hphi_meas q hq0
    · exact hphi_sq q hq0
    · exact hZright q hq
    · exact hpoint q hq
    · exact hFrep q hq
  have hVrep : ∀ q ∈ Set.Ioo L R,
      ((((A q + F q : WholeLineRealL2) : ℝ → ℝ)) =ᵐ[volume]
        paper5WeightedPopulationT eta
          (paper5CoMovingMaterialTime c u) q) := by
    intro q hq
    have hq0 : 0 < q := hL0.trans hq.1
    have hqT : q < T := hq.2.trans hRT
    filter_upwards [Lp.coeFn_add (A q) (F q), hArep q hq, hFrep q hq]
      with x hadd hA hF
    rw [hadd]
    simp only [Pi.add_apply]
    rw [hA, hF]
    exact
      (paper5WeightedPopulationT_eq_spatialGenerator_add_generatorForcing
        p hsol hq0 hqT hTW (hu q hq x)
          ((hu2 q hq).of_le (by norm_num)) (hv2 q hq)
          (hU2.of_le (by norm_num)) hV2).symm
  have hpair : ∀ q ∈ Set.Ioo L R, ContinuousAt
      (fun s => ⟪Z s, A s + F s⟫) q := by
    intro q hq
    apply wholeLineRealL2_inner_generator_add_forcing_continuousAt
      (hZcont.continuousAt (isOpen_Ioo.mem_nhds hq))
      (hXcont.continuousAt (isOpen_Ioo.mem_nhds hq))
      (hFcont.continuousAt (isOpen_Ioo.mem_nhds hq))
    have hopen : ∀ᶠ s in nhds q, s ∈ Set.Ioo L R :=
      isOpen_Ioo.mem_nhds hq
    filter_upwards [hopen] with s hs
    apply paper5WeightedPopulation_inner_spatialGenerator_eq
      (hu2 s hs) hU2 (hclose s hs) (hWx2 s hs)
    · exact wholeLineRealL2Total_coe_ae _
        (hphi_meas s (hL0.trans hs.1))
        (hphi_sq s (hL0.trans hs.1))
    · exact hXrep s hs
    · exact hArep s hs
  let a : ℝ := (L + t) / 2
  let b : ℝ := (t + R) / 2
  have hat : a < t := by dsimp only [a]; linarith
  have htb : t < b := by dsimp only [b]; linarith
  have hsub : Set.Icc a b ⊆ Set.Ioo L R := by
    rintro q ⟨hq1, hq2⟩
    dsimp only [a, b] at hq1 hq2
    constructor <;> linarith
  simpa only [paper5WeightedHalfEnergy] using
    (wholeLineHalfEnergy_hasDerivAt_of_continuous_right_pairing_canonicalL2
      (phi := paper5WeightedPopulation eta (coMovingPath c u) U)
      (phi_t := paper5WeightedPopulationT eta
        (paper5CoMovingMaterialTime c u))
      (V := fun q => A q + F q) hat htb isOpen_Ioo hsub
      (fun q hq => hphi_meas q (hL0.trans hq.1))
      (fun q hq => hphi_sq q (hL0.trans hq.1))
      hZcont
      (fun q hq => by simpa only [Z] using hpair q hq)
      (fun q hq => hZright q (hsub ⟨hq.1, hq.2.le⟩))
      hVrep)

section AxiomAudit

#print axioms paper5WeightedHalfEnergy_hasDerivAt_of_exactGeneratorWindow

end AxiomAudit

end ShenWork.Paper1
