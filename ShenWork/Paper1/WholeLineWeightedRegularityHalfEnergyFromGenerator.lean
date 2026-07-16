import ShenWork.Paper1.WholeLineWeightedRegularityGeneratorIdentificationWindow
import ShenWork.Paper1.WholeLineWeightedRegularityHalfEnergyWindow

open Filter MeasureTheory Set Topology
open scoped RealInnerProductSpace

noncomputable section

namespace ShenWork.Paper1

/-!
# Weighted half energy from an explicit generator representative

On a positive-time window, spatial `C²` regularity and exact weighted
closeness already supply the measurable square-integrable representatives of
the weighted population.  Thus the ordinary half-energy derivative can be
obtained from a local generator representative without carrying global
measurability or square-integrability hypotheses.
-/

/-- A window-local representative of the conjugated spatial generator,
together with the actual right derivative and pointwise material derivative,
supplies the ordinary derivative of the weighted half energy. -/
theorem paper5WeightedHalfEnergy_hasDerivAt_of_generatorRepresentationWindow
    {eta c L R t : ℝ}
    {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {X A F : ℝ → WholeLineRealL2}
    (hLt : L < t) (htR : t < R)
    (hU2 : ContDiff ℝ 2 U)
    (hZcont : ContinuousOn (fun q => wholeLineRealL2Total
      (paper5WeightedPopulation eta (coMovingPath c u) U q))
      (Set.Ioo L R))
    (hXcont : ContinuousOn X (Set.Ioo L R))
    (hFcont : ContinuousOn F (Set.Ioo L R))
    (hu2 : ∀ q ∈ Set.Ioo L R,
      ContDiff ℝ 2 (coMovingPath c u q))
    (hclose : ∀ q ∈ Set.Ioo L R, Integrable (fun x =>
      Real.exp (2 * eta * x) *
        |coMovingPath c u q x - U x| ^ 2))
    (hWx2 : ∀ q ∈ Set.Ioo L R, Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U q x ^ 2))
    (hXrep : ∀ q ∈ Set.Ioo L R,
      (((X q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        paper5WeightedPopulationX eta (coMovingPath c u) U q))
    (hArep : ∀ q ∈ Set.Ioo L R,
      (((A q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        fun x =>
          paper5WeightedPopulationXX eta (coMovingPath c u) U q x +
            (c - 2 * eta) *
              paper5WeightedPopulationX eta (coMovingPath c u) U q x +
            (eta ^ 2 - c * eta) *
              paper5WeightedPopulation eta (coMovingPath c u) U q x))
    (hZright : ∀ q ∈ Set.Ioo L R,
      HasDerivWithinAt (fun s => wholeLineRealL2Total
        (paper5WeightedPopulation eta (coMovingPath c u) U s))
        (A q + F q) (Set.Ici q) q)
    (hpoint : ∀ q ∈ Set.Ioo L R, ∀ x,
      HasDerivAt (fun s =>
        paper5WeightedPopulation eta (coMovingPath c u) U s x)
        (paper5WeightedPopulationT eta
          (paper5CoMovingMaterialTime c u) q x) q) :
    HasDerivAt (paper5WeightedHalfEnergy eta c u U)
      (∫ x : ℝ,
        paper5WeightedPopulation eta (coMovingPath c u) U t x *
          paper5WeightedPopulationT eta
            (paper5CoMovingMaterialTime c u) t x) t := by
  have hphi_meas : ∀ q ∈ Set.Ioo L R, AEStronglyMeasurable
      (paper5WeightedPopulation eta (coMovingPath c u) U q) volume := by
    intro q hq
    exact ((Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).mul
        ((hu2 q hq).continuous.sub hU2.continuous)).aestronglyMeasurable
  have hphi_sq : ∀ q ∈ Set.Ioo L R, Integrable (fun x : ℝ =>
      paper5WeightedPopulation eta (coMovingPath c u) U q x ^ 2) volume := by
    intro q hq
    exact paper5WeightedPopulation_sq_integrable_of_weighted_difference
      (hclose q hq)
  have hVrep : ∀ q ∈ Set.Ioo L R,
      ((((A q + F q : WholeLineRealL2) : ℝ → ℝ)) =ᵐ[volume]
        paper5WeightedPopulationT eta
          (paper5CoMovingMaterialTime c u) q) := by
    intro q hq
    let r : ℝ := (q + R) / 2
    have hqR : q < R := hq.2
    have hqr : q < r := by dsimp only [r]; linarith
    have hrR : r < R := by dsimp only [r]; linarith
    apply wholeLineRealL2Total_hasDerivWithinAt_coe_ae_of_pointwise_window
      hqr
    · intro s hs
      exact hphi_meas s ⟨hq.1.trans_le hs.1, hs.2.trans_lt hrR⟩
    · intro s hs
      exact hphi_sq s ⟨hq.1.trans_le hs.1, hs.2.trans_lt hrR⟩
    · exact hZright q hq
    · exact hpoint q hq
  have hpair : ∀ q ∈ Set.Ioo L R, ContinuousAt
      (fun s => ⟪wholeLineRealL2Total
        (paper5WeightedPopulation eta (coMovingPath c u) U s),
          A s + F s⟫) q := by
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
        (hphi_meas s hs) (hphi_sq s hs)
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
  exact
    wholeLineHalfEnergy_hasDerivAt_of_continuous_right_pairing_canonicalL2
      (phi := paper5WeightedPopulation eta (coMovingPath c u) U)
      (phi_t := paper5WeightedPopulationT eta
        (paper5CoMovingMaterialTime c u))
      (V := fun q => A q + F q) hat htb isOpen_Ioo hsub
      hphi_meas hphi_sq hZcont hpair
      (fun q hq => hZright q (hsub ⟨hq.1, hq.2.le⟩)) hVrep

/-- Classical co-moving specialization.  The local generator representative
is constructed from the right derivative, pointwise PDE identity, and forcing
representative; no global weighted-state measurability premise is required. -/
theorem paper5WeightedHalfEnergy_hasDerivAt_of_exactGeneratorWindow_local
    (p : CMParams) {T eta c L R t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    {X A F : ℝ → WholeLineRealL2}
    (hL0 : 0 < L) (hLt : L < t) (htR : t < R) (hRT : R < T)
    (hsol : IsClassicalSolution p T u v)
    (hTW : IsTravelingWave p c U V)
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V)
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
  have hphi_meas : ∀ q ∈ Set.Ioo L R, AEStronglyMeasurable
      (paper5WeightedPopulation eta (coMovingPath c u) U q) volume := by
    intro q hq
    exact ((Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).mul
        ((hu2 q hq).continuous.sub hU2.continuous)).aestronglyMeasurable
  have hphi_sq : ∀ q ∈ Set.Ioo L R, Integrable (fun x : ℝ =>
      paper5WeightedPopulation eta (coMovingPath c u) U q x ^ 2) volume := by
    intro q hq
    exact paper5WeightedPopulation_sq_integrable_of_weighted_difference
      (hclose q hq)
  have hArep : ∀ q ∈ Set.Ioo L R,
      (((A q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        fun x =>
          paper5WeightedPopulationXX eta (coMovingPath c u) U q x +
            (c - 2 * eta) *
              paper5WeightedPopulationX eta (coMovingPath c u) U q x +
            (eta ^ 2 - c * eta) *
              paper5WeightedPopulation eta (coMovingPath c u) U q x) := by
    intro q hq
    let r : ℝ := (q + R) / 2
    have hqR : q < R := hq.2
    have hqr : q < r := by dsimp only [r]; linarith
    have hrR : r < R := by dsimp only [r]; linarith
    have hq0 : 0 < q := hL0.trans hq.1
    have hqT : q < T := hq.2.trans hRT
    apply
      paper5WeightedFullGenerator_coe_ae_spatialGenerator_of_rightDerivative_window
        p hsol hq0 hqT hqr hTW (hu q hq)
          ((hu2 q hq).of_le (by norm_num)) (hv2 q hq)
          (hU2.of_le (by norm_num)) hV2
    · intro s hs
      exact hphi_meas s ⟨hq.1.trans_le hs.1, hs.2.trans_lt hrR⟩
    · intro s hs
      exact hphi_sq s ⟨hq.1.trans_le hs.1, hs.2.trans_lt hrR⟩
    · exact hZright q hq
    · exact hpoint q hq
    · exact hFrep q hq
  simpa only [paper5WeightedHalfEnergy] using
    (paper5WeightedHalfEnergy_hasDerivAt_of_generatorRepresentationWindow
      hLt htR hU2 hZcont hXcont hFcont hu2 hclose hWx2 hXrep hArep
      hZright hpoint)

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.paper5WeightedHalfEnergy_hasDerivAt_of_generatorRepresentationWindow
#print axioms
  ShenWork.Paper1.paper5WeightedHalfEnergy_hasDerivAt_of_exactGeneratorWindow_local
