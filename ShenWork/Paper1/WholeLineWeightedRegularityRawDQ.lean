import ShenWork.Paper1.WholeLineWeightedRegularityDQSources
import ShenWork.Paper1.WholeLineWeightedRegularityL2History

open Filter MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace ShenWork.Paper1

/-- An exact cap-weighted value bound and quotient bound assemble into an
honest `L²` representative of the conjugated raw quotient. -/
theorem exists_capWeighted_rawSpatialDifferenceQuotientL2
    {eta R h B0 B1 : ℝ}
    (heta : 0 ≤ eta) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1)
    {w : ℝ → ℝ} (hw : Continuous w)
    (hvalue : Integrable (fun x : ℝ =>
      capWeight eta R x * |w x| ^ 2))
    (hvalue_bound : (∫ x : ℝ,
      capWeight eta R x * |w x| ^ 2) ≤ B0 ^ 2)
    (hquot : Integrable (fun x : ℝ => capWeight eta R x *
      |spatialDifferenceQuotient h w x| ^ 2))
    (hquot_bound : (∫ x : ℝ, capWeight eta R x *
      |spatialDifferenceQuotient h w x| ^ 2) ≤ B1 ^ 2) :
    ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x => capWeightSqrt eta R x *
        (eta * w x + spatialDifferenceQuotient h w x)) ∧
      ‖Z‖ ≤ eta * B0 + B1 := by
  let g0 : ℝ → ℝ := fun x => capWeightSqrt eta R x * w x
  let g1 : ℝ → ℝ := fun x => capWeightSqrt eta R x *
    spatialDifferenceQuotient h w x
  have hg0_cont : Continuous g0 := by
    exact (capWeightSqrt_continuous eta R).mul hw
  have hq_cont : Continuous (spatialDifferenceQuotient h w) := by
    unfold spatialDifferenceQuotient
    exact ((hw.comp (continuous_id.add continuous_const)).sub hw).div_const h
  have hg1_cont : Continuous g1 :=
    (capWeightSqrt_continuous eta R).mul hq_cont
  have hg0_sq : Integrable (fun x : ℝ => g0 x ^ 2) := by
    refine hvalue.congr (Eventually.of_forall fun x => ?_)
    exact (capWeightSqrt_mul_sq_eq eta R x (w x)).symm
  have hg1_sq : Integrable (fun x : ℝ => g1 x ^ 2) := by
    refine hquot.congr (Eventually.of_forall fun x => ?_)
    exact (capWeightSqrt_mul_sq_eq eta R x
      (spatialDifferenceQuotient h w x)).symm
  let Z0 : WholeLineRealL2 := wholeLineRealL2OfSqIntegrable
    g0 hg0_cont.aestronglyMeasurable hg0_sq
  let Z1 : WholeLineRealL2 := wholeLineRealL2OfSqIntegrable
    g1 hg1_cont.aestronglyMeasurable hg1_sq
  have hZ0_rep : ((Z0 : ℝ → ℝ) =ᵐ[volume] g0) :=
    wholeLineRealL2OfSqIntegrable_coe_ae
      g0 hg0_cont.aestronglyMeasurable hg0_sq
  have hZ1_rep : ((Z1 : ℝ → ℝ) =ᵐ[volume] g1) :=
    wholeLineRealL2OfSqIntegrable_coe_ae
      g1 hg1_cont.aestronglyMeasurable hg1_sq
  have hZ0_norm_sq : ‖Z0‖ ^ 2 = ∫ x : ℝ, g0 x ^ 2 :=
    wholeLineRealL2OfSqIntegrable_norm_sq
      g0 hg0_cont.aestronglyMeasurable hg0_sq
  have hZ1_norm_sq : ‖Z1‖ ^ 2 = ∫ x : ℝ, g1 x ^ 2 :=
    wholeLineRealL2OfSqIntegrable_norm_sq
      g1 hg1_cont.aestronglyMeasurable hg1_sq
  have hZ0_norm : ‖Z0‖ ≤ B0 := by
    apply (sq_le_sq₀ (norm_nonneg Z0) hB0).mp
    rw [hZ0_norm_sq]
    calc
      (∫ x : ℝ, g0 x ^ 2) =
          ∫ x : ℝ, capWeight eta R x * |w x| ^ 2 := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x =>
          capWeightSqrt_mul_sq_eq eta R x (w x)
      _ ≤ B0 ^ 2 := hvalue_bound
  have hZ1_norm : ‖Z1‖ ≤ B1 := by
    apply (sq_le_sq₀ (norm_nonneg Z1) hB1).mp
    rw [hZ1_norm_sq]
    calc
      (∫ x : ℝ, g1 x ^ 2) =
          ∫ x : ℝ, capWeight eta R x *
            |spatialDifferenceQuotient h w x| ^ 2 := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x =>
          capWeightSqrt_mul_sq_eq eta R x
            (spatialDifferenceQuotient h w x)
      _ ≤ B1 ^ 2 := hquot_bound
  let Z : WholeLineRealL2 := eta • Z0 + Z1
  refine ⟨Z, ?_, ?_⟩
  · have hsmul : (((eta • Z0 : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        fun x => eta * Z0 x) := by
      simpa only [smul_eq_mul] using Lp.coeFn_smul eta Z0
    have hadd : ((Z : ℝ → ℝ) =ᵐ[volume]
        fun x => (eta • Z0) x + Z1 x) := by
      simpa only [Z] using Lp.coeFn_add (eta • Z0) Z1
    filter_upwards [hsmul, hadd, hZ0_rep, hZ1_rep]
      with x hsmulx haddx h0 h1
    rw [haddx, hsmulx, h0, h1]
    dsimp only [g0, g1]
    ring
  · calc
      ‖Z‖ ≤ ‖eta • Z0‖ + ‖Z1‖ := by
        simpa only [Z] using norm_add_le (eta • Z0) Z1
      _ = eta * ‖Z0‖ + ‖Z1‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg heta]
      _ ≤ eta * B0 + B1 :=
        add_le_add (mul_le_mul_of_nonneg_left hZ0_norm heta) hZ1_norm

#print axioms exists_capWeighted_rawSpatialDifferenceQuotientL2

end ShenWork.Paper1
