import ShenWork.Paper1.WholeLineWeightedRegularityL2Semigroup
import ShenWork.Paper1.WholeLineWeightedRegularityL2History
import ShenWork.Paper1.WholeLineWeightedRegularityTimeClosure

open Filter MeasureTheory Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Exact-weight `L²` generator mild identities

The canonical perturbation restart is first obtained pointwise in space.
This file isolates the measure-theoretic step which lifts that identity to
`WholeLineRealL2`.  The forcing is assumed only at the target exponential
weight: no stronger exponential weight and no spatial generator or second
derivative is used.
-/

/-- The Bochner history of the weighted moving heat semigroup has the
expected scalar kernel representative.  The endpoint `q = r` is harmless:
inside `Ioc a r` it is removed as a null singleton, so the heat lag is
strictly positive almost everywhere and the interval integral is unchanged.

The local product-integrability premise is precisely the Fubini input on
finite-measure spatial windows; it does not impose a global space-time
`L¹` hypothesis. -/
theorem weightedMovingHeatL2Semigroup_intervalIntegral_coe_ae
    {eta c a r : ℝ} (har : a ≤ r)
    {f : ℝ → ℝ → ℝ} {F : ℝ → WholeLineRealL2}
    (hFrep : ∀ q ∈ Set.Ioc a r,
      (((F q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] f q))
    (hDint : IntervalIntegrable
      (fun q => weightedMovingHeatL2Semigroup eta c (r - q) (F q))
      volume a r)
    (hlocal : ∀ A : Set ℝ, MeasurableSet A →
      (volume : Measure ℝ) A < ⊤ →
      Integrable
        (fun z : ℝ × ℝ => A.indicator
          (weightedMovingHeatEta eta c (r - z.1) (f z.1)) z.2)
        ((volume.restrict (Set.Ioc a r)).prod volume)) :
    ((((∫ q in a..r,
          weightedMovingHeatL2Semigroup eta c (r - q) (F q)) :
        WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      fun x => ∫ q in a..r,
        weightedMovingHeatEta eta c (r - q) (f q) x) := by
  have hDrep : ∀ᵐ q ∂(volume.restrict (Set.Ioc a r)),
      (((weightedMovingHeatL2Semigroup eta c (r - q) (F q) :
          WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        weightedMovingHeatEta eta c (r - q) (f q)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (Measure.ae_ne volume r).filter_mono ae_restrict_le] with q hq hqr
    have hlag : 0 < r - q := sub_pos.mpr (lt_of_le_of_ne hq.2 hqr)
    rw [weightedMovingHeatL2Semigroup_of_pos hlag]
    exact (weightedMovingHeatL2Fun_coe_ae hlag (F q)).trans
      (Eventually.of_forall fun x =>
        weightedMovingHeatEta_congr_ae (hFrep q hq) x)
  exact wholeLineRealL2_intervalIntegral_coe_ae_of_local_prod_integrable
    har hDint hDrep hlocal

/-- An a.e. pointwise mild restart identity lifts to an equality in
`WholeLineRealL2`.  All representatives and Fubini data are explicit, so
this theorem can be instantiated by the canonical co-moving perturbation
and its exact-weight generator forcing without assuming the generator or a
weighted second derivative. -/
theorem weightedMovingHeatL2Semigroup_mild_restart_eq_of_pointwise
    {eta c a r : ℝ} (har : a < r)
    {z f : ℝ → ℝ → ℝ}
    {Z F : ℝ → WholeLineRealL2}
    (hZa : (((Z a : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] z a))
    (hZr : (((Z r : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] z r))
    (hFrep : ∀ q ∈ Set.Ioc a r,
      (((F q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] f q))
    (hDint : IntervalIntegrable
      (fun q => weightedMovingHeatL2Semigroup eta c (r - q) (F q))
      volume a r)
    (hlocal : ∀ A : Set ℝ, MeasurableSet A →
      (volume : Measure ℝ) A < ⊤ →
      Integrable
        (fun w : ℝ × ℝ => A.indicator
          (weightedMovingHeatEta eta c (r - w.1) (f w.1)) w.2)
        ((volume.restrict (Set.Ioc a r)).prod volume))
    (hpoint : ∀ᵐ x ∂volume,
      z r x = weightedMovingHeatEta eta c (r - a) (z a) x +
        ∫ q in a..r,
          weightedMovingHeatEta eta c (r - q) (f q) x) :
    Z r = weightedMovingHeatL2Semigroup eta c (r - a) (Z a) +
      ∫ q in a..r,
        weightedMovingHeatL2Semigroup eta c (r - q) (F q) := by
  have hlag : 0 < r - a := sub_pos.mpr har
  have hhom :
      (((weightedMovingHeatL2Semigroup eta c (r - a) (Z a) :
          WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        weightedMovingHeatEta eta c (r - a) (z a)) := by
    rw [weightedMovingHeatL2Semigroup_of_pos hlag]
    exact (weightedMovingHeatL2Fun_coe_ae hlag (Z a)).trans
      (Eventually.of_forall fun x =>
        weightedMovingHeatEta_congr_ae hZa x)
  have hduhamel :=
    weightedMovingHeatL2Semigroup_intervalIntegral_coe_ae
      har.le hFrep hDint hlocal
  apply Lp.ext
  filter_upwards [hZr,
    Lp.coeFn_add
      (weightedMovingHeatL2Semigroup eta c (r - a) (Z a))
      (∫ q in a..r,
        weightedMovingHeatL2Semigroup eta c (r - q) (F q)),
    hhom, hduhamel, hpoint] with x hzr hadd hhomx hduhamelx hpointx
  rw [hzr, hadd]
  simp only [Pi.add_apply]
  rw [hhomx, hduhamelx, hpointx]

/-- Canonical-total specialization of the preceding lift.  Exact-weight
square-integrability supplies the endpoint and forcing representatives
internally.  Thus the only evolution premises left visible are the
pointwise mild restart, Bochner integrability of its heat history, and the
local Fubini condition. -/
theorem weightedMovingHeatL2Semigroup_mild_restart_eq_of_pointwise_total
    {eta c a r : ℝ} (har : a < r)
    {z f : ℝ → ℝ → ℝ}
    (hz_meas : ∀ q ∈ Set.Icc a r,
      AEStronglyMeasurable (z q) volume)
    (hz_sq : ∀ q ∈ Set.Icc a r,
      Integrable (fun x : ℝ => z q x ^ 2) volume)
    (hf_meas : ∀ q ∈ Set.Ioc a r,
      AEStronglyMeasurable (f q) volume)
    (hf_sq : ∀ q ∈ Set.Ioc a r,
      Integrable (fun x : ℝ => f q x ^ 2) volume)
    (hDint : IntervalIntegrable
      (fun q => weightedMovingHeatL2Semigroup eta c (r - q)
        (wholeLineRealL2Total (f q))) volume a r)
    (hlocal : ∀ A : Set ℝ, MeasurableSet A →
      (volume : Measure ℝ) A < ⊤ →
      Integrable
        (fun w : ℝ × ℝ => A.indicator
          (weightedMovingHeatEta eta c (r - w.1) (f w.1)) w.2)
        ((volume.restrict (Set.Ioc a r)).prod volume))
    (hpoint : ∀ᵐ x ∂volume,
      z r x = weightedMovingHeatEta eta c (r - a) (z a) x +
        ∫ q in a..r,
          weightedMovingHeatEta eta c (r - q) (f q) x) :
    wholeLineRealL2Total (z r) =
      weightedMovingHeatL2Semigroup eta c (r - a)
          (wholeLineRealL2Total (z a)) +
        ∫ q in a..r,
          weightedMovingHeatL2Semigroup eta c (r - q)
            (wholeLineRealL2Total (f q)) := by
  apply weightedMovingHeatL2Semigroup_mild_restart_eq_of_pointwise
    har
  · exact wholeLineRealL2Total_coe_ae _
      (hz_meas a ⟨le_rfl, har.le⟩)
      (hz_sq a ⟨le_rfl, har.le⟩)
  · exact wholeLineRealL2Total_coe_ae _
      (hz_meas r ⟨har.le, le_rfl⟩)
      (hz_sq r ⟨har.le, le_rfl⟩)
  · intro q hq
    exact wholeLineRealL2Total_coe_ae _ (hf_meas q hq) (hf_sq q hq)
  · exact hDint
  · exact hlocal
  · exact hpoint

section AxiomAudit

#print axioms weightedMovingHeatL2Semigroup_intervalIntegral_coe_ae
#print axioms weightedMovingHeatL2Semigroup_mild_restart_eq_of_pointwise
#print axioms
  weightedMovingHeatL2Semigroup_mild_restart_eq_of_pointwise_total

end AxiomAudit

end ShenWork.Paper1
