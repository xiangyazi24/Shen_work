import ShenWork.Paper1.WholeLineWeightedRegularityL2History
import ShenWork.Paper1.WholeLineWeightedRegularityTimeClosure

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Canonical `L²` increments from pointwise time integration

This file separates the two honest ingredients in the weighted time
derivative: a Bochner-integrable canonical `L²` velocity and the scalar
fundamental theorem of calculus for its representatives.  The spatial
Fubini hypothesis is local on finite-measure windows, so no false global
space-time `L¹` premise is introduced.
-/

/-- The local Bochner/Fubini representative theorem for an oriented interval.
The earlier theorem was stated for ordered endpoints; this wrapper records
the same result on the unordered interval and handles the sign internally. -/
theorem wholeLineRealL2_intervalIntegral_coe_ae_of_local_prod_integrable_any
    {a b : ℝ} {Z : ℝ → WholeLineRealL2} {g : ℝ → ℝ → ℝ}
    (hZint : IntervalIntegrable Z volume a b)
    (hrep : ∀ᵐ q ∂(volume.restrict (Set.uIoc a b)),
      (((Z q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] g q))
    (hlocal : ∀ A : Set ℝ, MeasurableSet A →
      (volume : Measure ℝ) A < ⊤ →
      Integrable
        (fun z : ℝ × ℝ => A.indicator (g z.1) z.2)
        ((volume.restrict (Set.uIoc a b)).prod volume)) :
    ((((∫ q in a..b, Z q) : WholeLineRealL2) : ℝ → ℝ)
      =ᵐ[volume] fun x => ∫ q in a..b, g q x) := by
  rcases le_total a b with hab | hba
  · apply wholeLineRealL2_intervalIntegral_coe_ae_of_local_prod_integrable
      hab hZint
    · simpa only [Set.uIoc_of_le hab] using hrep
    · intro A hA hAfin
      simpa only [Set.uIoc_of_le hab] using hlocal A hA hAfin
  · have hrep' : ∀ᵐ q ∂(volume.restrict (Set.Ioc b a)),
        (((Z q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] g q) := by
      simpa only [Set.uIoc_of_ge hba] using hrep
    have hlocal' : ∀ A : Set ℝ, MeasurableSet A →
        (volume : Measure ℝ) A < ⊤ →
        Integrable
          (fun z : ℝ × ℝ => A.indicator (g z.1) z.2)
          ((volume.restrict (Set.Ioc b a)).prod volume) := by
      intro A hA hAfin
      simpa only [Set.uIoc_of_ge hba] using hlocal A hA hAfin
    have hforward :=
      wholeLineRealL2_intervalIntegral_coe_ae_of_local_prod_integrable
        hba hZint.symm hrep' hlocal'
    have hvec : (∫ q in a..b, Z q) = -(∫ q in b..a, Z q) :=
      intervalIntegral.integral_symm b a
    rw [hvec]
    filter_upwards [Lp.coeFn_neg (∫ q in b..a, Z q), hforward]
      with x hxneg hxforward
    rw [hxneg]
    simp only [Pi.neg_apply]
    rw [hxforward]
    exact (intervalIntegral.integral_symm b a).symm

/-- Equality of canonical `L²` increments follows from an a.e. scalar
increment identity and the concrete Bochner representative theorem. -/
theorem wholeLineRealL2Total_increment_eq_of_pointwise_intervalIntegral
    {phi g : ℝ → ℝ → ℝ} {G : ℝ → WholeLineRealL2}
    {t s : ℝ}
    (hphi_meas : ∀ q, AEStronglyMeasurable (phi q) volume)
    (hphi_sq : ∀ q, Integrable (fun x : ℝ => phi q x ^ 2) volume)
    (hGint : IntervalIntegrable G volume t s)
    (hGrep : ∀ᵐ q ∂(volume.restrict (Set.uIoc t s)),
      (((G q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] g q))
    (hlocal : ∀ A : Set ℝ, MeasurableSet A →
      (volume : Measure ℝ) A < ⊤ →
      Integrable
        (fun z : ℝ × ℝ => A.indicator (g z.1) z.2)
        ((volume.restrict (Set.uIoc t s)).prod volume))
    (hscalar : ∀ᵐ x ∂volume,
      ∫ q in t..s, g q x = phi s x - phi t x) :
    wholeLineRealL2Total (phi s) =
      wholeLineRealL2Total (phi t) + ∫ q in t..s, G q := by
  have hIntRep :=
    wholeLineRealL2_intervalIntegral_coe_ae_of_local_prod_integrable_any
      hGint hGrep hlocal
  apply Lp.ext
  filter_upwards [wholeLineRealL2Total_coe_ae (phi s)
      (hphi_meas s) (hphi_sq s),
    wholeLineRealL2Total_coe_ae (phi t) (hphi_meas t) (hphi_sq t),
    Lp.coeFn_add (wholeLineRealL2Total (phi t)) (∫ q in t..s, G q),
    hIntRep, hscalar] with x hs ht hadd hint hftc
  rw [hs, hadd]
  simp only [Pi.add_apply]
  rw [ht, hint, hftc]
  ring

/-- A continuous canonical `L²` velocity and scalar pointwise increments
produce the exact Hilbert-space increment identity at every endpoint. -/
theorem wholeLineRealL2Total_increment_eq_of_continuous_velocity
    {phi g : ℝ → ℝ → ℝ} {G : ℝ → WholeLineRealL2}
    {t : ℝ}
    (hphi_meas : ∀ q, AEStronglyMeasurable (phi q) volume)
    (hphi_sq : ∀ q, Integrable (fun x : ℝ => phi q x ^ 2) volume)
    (hG : Continuous G)
    (hGrep : ∀ q,
      (((G q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] g q))
    (hlocal : ∀ s, ∀ A : Set ℝ, MeasurableSet A →
      (volume : Measure ℝ) A < ⊤ →
      Integrable
        (fun z : ℝ × ℝ => A.indicator (g z.1) z.2)
        ((volume.restrict (Set.uIoc t s)).prod volume))
    (hscalar : ∀ s, ∀ᵐ x ∂volume,
      ∫ q in t..s, g q x = phi s x - phi t x) :
    ∀ s, wholeLineRealL2Total (phi s) =
      wholeLineRealL2Total (phi t) + ∫ q in t..s, G q := by
  intro s
  apply wholeLineRealL2Total_increment_eq_of_pointwise_intervalIntegral
    hphi_meas hphi_sq (hG.intervalIntegrable t s)
  · exact Eventually.of_forall fun q => hGrep q
  · exact hlocal s
  · exact hscalar s

section AxiomAudit

#print axioms
  wholeLineRealL2_intervalIntegral_coe_ae_of_local_prod_integrable_any
#print axioms
  wholeLineRealL2Total_increment_eq_of_pointwise_intervalIntegral
#print axioms
  wholeLineRealL2Total_increment_eq_of_continuous_velocity

end AxiomAudit

end ShenWork.Paper1
