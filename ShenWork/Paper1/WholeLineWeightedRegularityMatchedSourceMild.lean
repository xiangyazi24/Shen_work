import ShenWork.Paper1.WholeLineWeightedRegularityMatchedSourceDQ
import ShenWork.Paper1.WholeLineWeightedRegularityMild

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Pointwise mild slices of the matched raw sources

The matched source estimates produce cap-weighted square bounds for the
conjugated raw spatial quotients.  The two theorems below turn those bounds
into honest `WholeLineRealL2` representatives after one positive heat lag.
All constants are independent of the cap radius.
-/

/-- A positive-lag moving heat-gradient slice of the genuine matched flux
raw source has an honest `WholeLineRealL2` representative. -/
theorem exists_capWeightedMovingHeatGradient_genuineFluxRawDQL2_le_kernel
    (p : CMParams) {M Brel DU eta R h c tau T X F : ℝ}
    (hM : 0 ≤ M) (hBrel : 0 ≤ Brel) (hDU : 0 ≤ DU)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (hh : h ≠ 0)
    (htau : 0 < tau) (htauT : tau ≤ T) (hX : 0 ≤ X) (hF : 0 ≤ F)
    {u U : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hU : IsCUnifBdd U)
    (hu_mem : ∀ x, u x ∈ Set.Icc (0 : ℝ) M)
    (hU_mem : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (hUpos : ∀ x, 0 < U x)
    (hbase : ∀ x, |(U (x + h) - U x) / h| ≤ DU)
    (hrelative : ∀ x, ∀ theta ∈ Set.Icc (0 : ℝ) 1,
      |(U (x + h) - U x) / h| ≤
        Brel * (theta * U (x + h) + (1 - theta) * U x))
    (hW : Integrable (fun x => capWeight eta R x * |u x - U x| ^ 2))
    (hraw : Integrable (fun x => capWeight eta R x *
      |eta * (u x - U x) +
        spatialDifferenceQuotient h (fun y => u y - U y) x| ^ 2))
    (hraw_energy :
      (∫ x : ℝ, capWeight eta R x *
        |eta * (u x - U x) +
          spatialDifferenceQuotient h (fun y => u y - U y) x| ^ 2) ≤ X ^ 2)
    (hW_energy :
      (∫ x : ℝ, capWeight eta R x * |u x - U x| ^ 2) ≤ F ^ 2) :
    let G := fun y => wholeLineChemotaxisFlux p u y -
      wholeLineChemotaxisFlux p U y
    let Fq := fun y => eta * G y + spatialDifferenceQuotient h G y
    ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x => capWeightSqrt eta R x *
        paper5MovingFrameHeatGradOp c tau Fq x) ∧
      ‖Z‖ ≤
        (2 * capMildGrowthBound eta c T * eta +
          (2 * capMildGrowthBound eta c T *
            (2 / Real.sqrt (4 * Real.pi))) *
              tau ^ (-(1 / 2 : ℝ))) *
          (Real.sqrt (matchedFluxRawQSquareConstant p M eta) * X +
            Real.sqrt
              (matchedFluxRawWSquareConstant p M Brel DU eta h) * F) := by
  dsimp only
  let G : ℝ → ℝ := fun y => wholeLineChemotaxisFlux p u y -
    wholeLineChemotaxisFlux p U y
  let Fq : ℝ → ℝ := fun y => eta * G y + spatialDifferenceQuotient h G y
  let CQ : ℝ := matchedFluxRawQSquareConstant p M eta
  let CW : ℝ := matchedFluxRawWSquareConstant p M Brel DU eta h
  let B : ℝ := Real.sqrt CQ * X + Real.sqrt CW * F
  have hCQ : 0 ≤ CQ := by
    dsimp only [CQ, matchedFluxRawQSquareConstant]
    exact mul_nonneg (by norm_num)
      (matchedFluxQuotientQSquareConstant_nonneg p M eta)
  have hCW : 0 ≤ CW := by
    dsimp only [CW, matchedFluxRawWSquareConstant]
    have hQ0 := matchedFluxQuotientQSquareConstant_nonneg p M eta
    have hW0 := matchedFluxQuotientWSquareConstant_nonneg
      p M Brel DU eta h
    have hC0 := capWeightedFluxSquareConstant_nonneg p M eta
    positivity
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact add_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) hX)
      (mul_nonneg (Real.sqrt_nonneg _) hF)
  have hsource := capWeight_genuineFluxDifference_rawSpatialDQ_l2_bounded
    p hM hBrel hDU heta0 heta1 hh hu hU hu_mem hU_mem hUpos
      hbase hrelative hW hraw
  dsimp only at hsource
  have hsource_energy :
      (∫ x : ℝ, capWeight eta R x * |Fq x| ^ 2) ≤ B ^ 2 := by
    have hlinear :
        (∫ x : ℝ, capWeight eta R x * |Fq x| ^ 2) ≤
          CQ * X ^ 2 + CW * F ^ 2 := by
      calc
        (∫ x : ℝ, capWeight eta R x * |Fq x| ^ 2) ≤
            CQ *
                (∫ x : ℝ, capWeight eta R x *
                  |eta * (u x - U x) +
                    spatialDifferenceQuotient h (fun y => u y - U y) x| ^ 2) +
              CW * ∫ x : ℝ, capWeight eta R x * |u x - U x| ^ 2 := by
          simpa only [Fq, G, CQ, CW] using hsource.2
        _ ≤ CQ * X ^ 2 + CW * F ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_left hraw_energy hCQ)
            (mul_le_mul_of_nonneg_left hW_energy hCW)
    calc
      (∫ x : ℝ, capWeight eta R x * |Fq x| ^ 2) ≤
          CQ * X ^ 2 + CW * F ^ 2 := hlinear
      _ = (Real.sqrt CQ * X) ^ 2 + (Real.sqrt CW * F) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hCQ, Real.sq_sqrt hCW]
      _ ≤ (Real.sqrt CQ * X + Real.sqrt CW * F) ^ 2 := by
        nlinarith [mul_nonneg
          (mul_nonneg (Real.sqrt_nonneg CQ) hX)
          (mul_nonneg (Real.sqrt_nonneg CW) hF)]
      _ = B ^ 2 := by rfl
  have hG_cont : Continuous G :=
    (wholeLineChemotaxisFlux_continuous_of_Icc p hM hu hu_mem).sub
      (wholeLineChemotaxisFlux_continuous_of_Icc p hM hU hU_mem)
  have hFq_cont : Continuous Fq := by
    dsimp only [Fq, spatialDifferenceQuotient]
    exact (hG_cont.const_mul eta).add
      (((hG_cont.comp (continuous_id.add continuous_const)).sub
        hG_cont).div_const h)
  rcases exists_capWeightedMovingHeatGradientL2
      heta0 htau hB R c hFq_cont.measurable
      (by simpa only [Fq, G] using hsource.1) hsource_energy with
    ⟨Z, hrep, hZ⟩
  refine ⟨Z, hrep, hZ.trans ?_⟩
  have hmass := capHeatGradientSchurMass_le_capMildKernel
    (c := c) heta0 htau htauT
  have hexp : Real.exp (-tau) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr htau.le)
  have hfactor :
      Real.exp (-tau) * capHeatGradientSchurMass eta c tau ≤
        2 * capMildGrowthBound eta c T * eta +
          (2 * capMildGrowthBound eta c T *
            (2 / Real.sqrt (4 * Real.pi))) *
              tau ^ (-(1 / 2 : ℝ)) :=
    (mul_le_mul_of_nonneg_right hexp
      (capHeatGradientSchurMass_pos htau heta0 c).le).trans
        (by simpa using hmass)
  calc
    Real.exp (-tau) * capHeatGradientSchurMass eta c tau * B ≤
        (2 * capMildGrowthBound eta c T * eta +
          (2 * capMildGrowthBound eta c T *
            (2 / Real.sqrt (4 * Real.pi))) *
              tau ^ (-(1 / 2 : ℝ))) * B :=
      mul_le_mul_of_nonneg_right hfactor hB
    _ = _ := by rfl

/-- A positive-lag moving heat slice of the genuine matched shifted-reaction
raw source has an honest `WholeLineRealL2` representative. -/
theorem exists_capWeightedMovingHeat_genuineShiftedReactionRawDQL2_le_kernel
    (p : CMParams) {M eta R h DU c tau T X F : ℝ}
    (hM : 0 ≤ M) (heta0 : 0 ≤ eta) (hDU : 0 ≤ DU) (hh : h ≠ 0)
    (htau : 0 < tau) (htauT : tau ≤ T) (hX : 0 ≤ X) (hF : 0 ≤ F)
    {u U : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hU : IsCUnifBdd U)
    (hu_mem : ∀ x, u x ∈ Set.Icc (0 : ℝ) M)
    (hU_mem : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (hU_quot : ∀ x, |spatialDifferenceQuotient h U x| ≤ DU)
    (hW : Integrable (fun x => capWeight eta R x * |u x - U x| ^ 2))
    (hraw : Integrable (fun x => capWeight eta R x *
      |eta * (u x - U x) +
        spatialDifferenceQuotient h (fun y => u y - U y) x| ^ 2))
    (hraw_energy :
      (∫ x : ℝ, capWeight eta R x *
        |eta * (u x - U x) +
          spatialDifferenceQuotient h (fun y => u y - U y) x| ^ 2) ≤ X ^ 2)
    (hW_energy :
      (∫ x : ℝ, capWeight eta R x * |u x - U x| ^ 2) ≤ F ^ 2) :
    let G := fun y => wholeLineCauchyShiftedReaction p u y -
      wholeLineCauchyShiftedReaction p U y
    let Fq := fun y => eta * G y + spatialDifferenceQuotient h G y
    ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x => capWeightSqrt eta R x *
        paper5MovingFrameHeatOp c tau Fq x) ∧
      ‖Z‖ ≤ 2 * capMildGrowthBound eta c T *
        (Real.sqrt (matchedShiftedReactionRawQSquareConstant p M) * X +
          Real.sqrt
            (matchedShiftedReactionRawWSquareConstant p M eta DU) * F) := by
  dsimp only
  let G : ℝ → ℝ := fun y => wholeLineCauchyShiftedReaction p u y -
    wholeLineCauchyShiftedReaction p U y
  let Fq : ℝ → ℝ := fun y => eta * G y + spatialDifferenceQuotient h G y
  let CQ : ℝ := matchedShiftedReactionRawQSquareConstant p M
  let CW : ℝ := matchedShiftedReactionRawWSquareConstant p M eta DU
  let B : ℝ := Real.sqrt CQ * X + Real.sqrt CW * F
  have hCQ : 0 ≤ CQ := by
    dsimp only [CQ, matchedShiftedReactionRawQSquareConstant]
    positivity
  have hCW : 0 ≤ CW := by
    dsimp only [CW, matchedShiftedReactionRawWSquareConstant]
    positivity
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact add_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) hX)
      (mul_nonneg (Real.sqrt_nonneg _) hF)
  have hsource :=
    capWeight_genuineShiftedReactionDifference_rawSpatialDQ_l2_bounded
      p hM heta0 hDU hh hu hU hu_mem hU_mem hU_quot hW hraw
  dsimp only at hsource
  have hsource_energy :
      (∫ x : ℝ, capWeight eta R x * |Fq x| ^ 2) ≤ B ^ 2 := by
    have hlinear :
        (∫ x : ℝ, capWeight eta R x * |Fq x| ^ 2) ≤
          CQ * X ^ 2 + CW * F ^ 2 := by
      calc
        (∫ x : ℝ, capWeight eta R x * |Fq x| ^ 2) ≤
            CQ *
                (∫ x : ℝ, capWeight eta R x *
                  |eta * (u x - U x) +
                    spatialDifferenceQuotient h (fun y => u y - U y) x| ^ 2) +
              CW * ∫ x : ℝ, capWeight eta R x * |u x - U x| ^ 2 := by
          simpa only [Fq, G, CQ, CW] using hsource.2
        _ ≤ CQ * X ^ 2 + CW * F ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_left hraw_energy hCQ)
            (mul_le_mul_of_nonneg_left hW_energy hCW)
    calc
      (∫ x : ℝ, capWeight eta R x * |Fq x| ^ 2) ≤
          CQ * X ^ 2 + CW * F ^ 2 := hlinear
      _ = (Real.sqrt CQ * X) ^ 2 + (Real.sqrt CW * F) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hCQ, Real.sq_sqrt hCW]
      _ ≤ (Real.sqrt CQ * X + Real.sqrt CW * F) ^ 2 := by
        nlinarith [mul_nonneg
          (mul_nonneg (Real.sqrt_nonneg CQ) hX)
          (mul_nonneg (Real.sqrt_nonneg CW) hF)]
      _ = B ^ 2 := by rfl
  have hG_cont : Continuous G :=
    (wholeLineCauchyShiftedReaction_continuous p hu.1).sub
      (wholeLineCauchyShiftedReaction_continuous p hU.1)
  have hFq_cont : Continuous Fq := by
    dsimp only [Fq, spatialDifferenceQuotient]
    exact (hG_cont.const_mul eta).add
      (((hG_cont.comp (continuous_id.add continuous_const)).sub
        hG_cont).div_const h)
  rcases exists_capWeightedMovingHeatL2
      heta0 htau hB R c hFq_cont.measurable
      (by simpa only [Fq, G] using hsource.1) hsource_energy with
    ⟨Z, hrep, hZ⟩
  refine ⟨Z, hrep, hZ.trans ?_⟩
  have hmass := capHeatSchurMass_le_capMildGrowthBound
    (c := c) heta0 htau.le htauT
  have hexp : Real.exp (-tau) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr htau.le)
  have hfactor : Real.exp (-tau) * capHeatSchurMass eta c tau ≤
      2 * capMildGrowthBound eta c T :=
    (mul_le_mul_of_nonneg_right hexp
      (capHeatSchurMass_pos eta c tau).le).trans (by simpa using hmass)
  calc
    Real.exp (-tau) * capHeatSchurMass eta c tau * B ≤
        (2 * capMildGrowthBound eta c T) * B :=
      mul_le_mul_of_nonneg_right hfactor hB
    _ = _ := by ring

#print axioms
  exists_capWeightedMovingHeatGradient_genuineFluxRawDQL2_le_kernel
#print axioms
  exists_capWeightedMovingHeat_genuineShiftedReactionRawDQL2_le_kernel

end ShenWork.Paper1
