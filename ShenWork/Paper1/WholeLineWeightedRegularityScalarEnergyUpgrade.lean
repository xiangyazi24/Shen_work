import ShenWork.Paper1.WholeLineWeightedRegularityEnergyUpgrade

open Filter MeasureTheory Set Topology
open scoped RealInnerProductSpace

noncomputable section

namespace ShenWork.Paper1

/-!
# Ordinary energy derivatives from a continuous scalar pairing

For the weighted mild solution the generator trajectory itself need not be
proved continuous.  It is enough that its scalar pairing with the state is
continuous; after spatial integration by parts that pairing is expressed by
the strongly continuous `H¹` fields.  This file isolates that strictly
weaker upgrade.
-/

/-- A continuous `L²` state with right derivatives has an ordinary
quadratic-energy derivative when the scalar state--velocity pairing is
continuous. -/
theorem wholeLineHalfEnergy_hasDerivAt_of_continuous_right_pairing_L2
    {phi phi_t : ℝ → ℝ → ℝ}
    {Z V : ℝ → WholeLineRealL2} {a b t : ℝ} {o : Set ℝ}
    (hat : a < t) (htb : t < b)
    (ho : IsOpen o) (hsub : Set.Icc a b ⊆ o)
    (hZcont : ContinuousOn Z o)
    (hpair : ∀ q ∈ o,
      ContinuousAt (fun s => ⟪Z s, V s⟫) q)
    (hZright : ∀ q ∈ Set.Ico a b,
      HasDerivWithinAt Z (V q) (Set.Ici q) q)
    (hrep : ∀ q ∈ o,
      ((Z q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] phi q)
    (hVrep : ∀ q ∈ o,
      ((V q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] phi_t q) :
    HasDerivAt (ShenWork.PaperOne.wholeLineHalfEnergy phi)
      (∫ x : ℝ, phi t x * phi_t t x) t := by
  let D : ℝ → ℝ := fun q => ⟪Z q, V q⟫
  have hfcont : ContinuousOn
      (ShenWork.PaperOne.wholeLineHalfEnergy phi) (Set.Icc a b) := by
    have hquad : ContinuousOn
        (fun q => (1 / 2 : ℝ) * ‖Z q‖ ^ 2) (Set.Icc a b) :=
      continuousOn_const.mul (((hZcont.mono hsub).norm).pow 2)
    apply hquad.congr
    intro q hq
    exact wholeLineHalfEnergy_eq_halfNormSq_of_aeEq
      (Z q) (hrep q (hsub hq))
  have hDcont : ∀ q ∈ o, ContinuousAt D q := by
    intro q hq
    exact hpair q hq
  have hright : ∀ q ∈ Set.Ico a b,
      HasDerivWithinAt (ShenWork.PaperOne.wholeLineHalfEnergy phi)
        (D q) (Set.Ici q) q := by
    intro q hq
    have hqIcc : q ∈ Set.Icc a b := ⟨hq.1, hq.2.le⟩
    have hqo : q ∈ o := hsub hqIcc
    have hopen : ∀ᶠ s in nhds q, s ∈ o := ho.mem_nhds hqo
    have hopenWithin : ∀ᶠ s in nhdsWithin q (Set.Ici q), s ∈ o :=
      hopen.filter_mono inf_le_left
    have hrightIntegral := wholeLineHalfEnergy_hasDerivWithinAt_Ici_of_L2
      (hZright q hq)
      (by
        filter_upwards [hopenWithin] with s hs
        exact hrep s hs)
      (hVrep q hqo)
    have hinter : (∫ x : ℝ, phi q x * phi_t q x) = D q :=
      wholeLineIntegral_mul_eq_inner_of_aeEq (Z q) (V q)
        (hrep q hqo) (hVrep q hqo)
    rwa [hinter] at hrightIntegral
  have hscalar : HasDerivAt
      (ShenWork.PaperOne.wholeLineHalfEnergy phi) (D t) t :=
    hasDerivAt_of_continuous_right_derivative_on_Icc
      hat htb hfcont ho hsub hDcont hright
  have htIcc : t ∈ Set.Icc a b := ⟨hat.le, htb.le⟩
  have hto : t ∈ o := hsub htIcc
  have hinter : (∫ x : ℝ, phi t x * phi_t t x) = D t :=
    wholeLineIntegral_mul_eq_inner_of_aeEq (Z t) (V t)
      (hrep t hto) (hVrep t hto)
  rwa [hinter]

/-- Canonical-total specialization of the scalar-pairing upgrade. -/
theorem wholeLineHalfEnergy_hasDerivAt_of_continuous_right_pairing_canonicalL2
    {phi phi_t : ℝ → ℝ → ℝ}
    {V : ℝ → WholeLineRealL2} {a b t : ℝ} {o : Set ℝ}
    (hat : a < t) (htb : t < b)
    (ho : IsOpen o) (hsub : Set.Icc a b ⊆ o)
    (hphi_meas : ∀ q ∈ o, AEStronglyMeasurable (phi q) volume)
    (hphi_sq : ∀ q ∈ o, Integrable (fun x : ℝ => phi q x ^ 2) volume)
    (hZcont : ContinuousOn (fun q => wholeLineRealL2Total (phi q)) o)
    (hpair : ∀ q ∈ o, ContinuousAt
      (fun s => ⟪wholeLineRealL2Total (phi s), V s⟫) q)
    (hZright : ∀ q ∈ Set.Ico a b,
      HasDerivWithinAt (fun s => wholeLineRealL2Total (phi s))
        (V q) (Set.Ici q) q)
    (hVrep : ∀ q ∈ o,
      ((V q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] phi_t q) :
    HasDerivAt (ShenWork.PaperOne.wholeLineHalfEnergy phi)
      (∫ x : ℝ, phi t x * phi_t t x) t := by
  apply wholeLineHalfEnergy_hasDerivAt_of_continuous_right_pairing_L2
    hat htb ho hsub hZcont hpair hZright
  · intro q hq
    exact wholeLineRealL2Total_coe_ae (phi q)
      (hphi_meas q hq) (hphi_sq q hq)
  · exact hVrep

/-- Positive-time weighted specialization.  The only continuity premise on
the velocity is continuity of its scalar pairing with the state. -/
theorem paper5WeightedHalfEnergy_hasDerivAt_of_continuous_right_pairing_positive
    {eta c T t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {V : ℝ → WholeLineRealL2}
    (ht : 0 < t) (htT : t < T)
    (hphi_meas : ∀ q ∈ Set.Ioo (0 : ℝ) T, AEStronglyMeasurable
      (paper5WeightedPopulation eta (coMovingPath c u) U q) volume)
    (hphi_sq : ∀ q ∈ Set.Ioo (0 : ℝ) T, Integrable (fun x : ℝ =>
      paper5WeightedPopulation eta (coMovingPath c u) U q x ^ 2) volume)
    (hZcont : ContinuousOn (fun q => wholeLineRealL2Total
      (paper5WeightedPopulation eta (coMovingPath c u) U q))
      (Set.Ioo (0 : ℝ) T))
    (hpair : ∀ q ∈ Set.Ioo (0 : ℝ) T, ContinuousAt
      (fun s => ⟪wholeLineRealL2Total
        (paper5WeightedPopulation eta (coMovingPath c u) U s), V s⟫) q)
    (hZright : ∀ q ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s => wholeLineRealL2Total
        (paper5WeightedPopulation eta (coMovingPath c u) U s))
        (V q) (Set.Ici q) q)
    (hVrep : ∀ q ∈ Set.Ioo (0 : ℝ) T,
      ((V q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        paper5WeightedPopulationT eta (paper5CoMovingMaterialTime c u) q) :
    HasDerivAt (paper5WeightedHalfEnergy eta c u U)
      (∫ x : ℝ,
        paper5WeightedPopulation eta (coMovingPath c u) U t x *
          paper5WeightedPopulationT eta
            (paper5CoMovingMaterialTime c u) t x) t := by
  let a : ℝ := t / 2
  let b : ℝ := (t + T) / 2
  have ha : 0 < a := by dsimp only [a]; positivity
  have hat : a < t := by dsimp only [a]; linarith
  have htb : t < b := by dsimp only [b]; linarith
  have hbT : b < T := by dsimp only [b]; linarith
  have hsub : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T := by
    intro q hq
    exact ⟨ha.trans_le hq.1, hq.2.trans_lt hbT⟩
  simpa only [paper5WeightedHalfEnergy] using
    (wholeLineHalfEnergy_hasDerivAt_of_continuous_right_pairing_canonicalL2
      (phi := paper5WeightedPopulation eta (coMovingPath c u) U)
      (phi_t := paper5WeightedPopulationT eta
        (paper5CoMovingMaterialTime c u))
      hat htb isOpen_Ioo hsub hphi_meas hphi_sq hZcont hpair
      (fun q hq => hZright q ⟨ha.trans_le hq.1, hq.2.trans hbT⟩)
      hVrep)

section AxiomAudit

#print axioms wholeLineHalfEnergy_hasDerivAt_of_continuous_right_pairing_L2
#print axioms
  wholeLineHalfEnergy_hasDerivAt_of_continuous_right_pairing_canonicalL2
#print axioms
  paper5WeightedHalfEnergy_hasDerivAt_of_continuous_right_pairing_positive

end AxiomAudit

end ShenWork.Paper1
