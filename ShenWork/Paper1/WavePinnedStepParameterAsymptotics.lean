import ShenWork.Paper1.WaveGreenParameterAsymptotics
import ShenWork.Paper1.WavePinnedStepComparison

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-- The record-independent weighted derivative coefficient is exactly the
weighted derivative-kernel mass times the source weight. -/
theorem paperStepWeightedDerivCoeff_eq_mass_mul
    (c lam κ B : ℝ) :
    PaperLocalFixedStepData.paperStepWeightedDerivCoeff c lam κ B =
      greenWeightedMass1 c lam κ * B := by
  unfold PaperLocalFixedStepData.paperStepWeightedDerivCoeff
    greenWeightedMass1
  ring

/-- For the affine source radius used by the canonical construction, the
lower-pinned successor comparison coefficient is little-o of the implicit
resolvent parameter. -/
theorem paperPinnedStepCmono_large_source_tendsto_zero
    (p : CMParams) (c M κ κtilde D C : ℝ) :
    Tendsto
      (fun lam : ℝ =>
        (1 / lam) * paperPinnedStepCmono p c lam M κ κtilde D
          (2 * (C + lam)))
      atTop (nhds 0) := by
  let A : ℝ :=
    reactionLip p.α M +
      (-p.χ) * M ^ p.γ * rpowLip p.m M
  let Q : ℝ :=
    (-p.χ) * p.m * M ^ p.γ * (p.m - 1) * M ^ (p.m - 1)
  let R : ℝ := lowerPinnedBarrierRatio κ κtilde D M
  have hCdiv : Tendsto (fun lam : ℝ => C / lam) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hBdiv : Tendsto
      (fun lam : ℝ => (2 * (C + lam)) / lam) atTop (nhds 2) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have h := (hCdiv.add hone).const_mul 2
    have h' : Tendsto (fun lam : ℝ => 2 * (C / lam + 1))
        atTop (nhds 2) := by simpa using h
    refine h'.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with lam hlam
    field_simp [ne_of_gt hlam]
  have hmassB : Tendsto
      (fun lam : ℝ =>
        greenWeightedMass1 c lam κ * ((2 * (C + lam)) / lam))
      atTop (nhds 0) := by
    simpa using (greenWeightedMass1_tendsto_zero c κ).mul hBdiv
  have hKdiv : Tendsto
      (fun lam : ℝ =>
        (1 / lam) *
          paperLowerPinnedStepLogSlopeCoeff c lam κ κtilde D M
            (2 * (C + lam)))
      atTop (nhds 0) := by
    have h := hmassB.const_mul R
    have h' : Tendsto
        (fun lam : ℝ =>
          R * (greenWeightedMass1 c lam κ * ((2 * (C + lam)) / lam)))
        atTop (nhds 0) := by simpa using h
    refine h'.congr' (Filter.Eventually.of_forall ?_)
    intro lam
    dsimp [R]
    rw [paperLowerPinnedStepLogSlopeCoeff,
      paperStepWeightedDerivCoeff_eq_mass_mul]
    ring
  have hAdiv : Tendsto (fun lam : ℝ => A / lam) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have htotal := hAdiv.add (hKdiv.const_mul Q)
  have htotal' : Tendsto
      (fun lam : ℝ => A / lam +
        Q * ((1 / lam) *
          paperLowerPinnedStepLogSlopeCoeff c lam κ κtilde D M
            (2 * (C + lam))))
      atTop (nhds 0) := by simpa using htotal
  refine htotal'.congr' (Filter.Eventually.of_forall ?_)
  intro lam
  dsimp [A, Q]
  unfold paperPinnedStepCmono
  ring

section AxiomAudit

#print axioms paperStepWeightedDerivCoeff_eq_mass_mul
#print axioms paperPinnedStepCmono_large_source_tendsto_zero

end AxiomAudit

end ShenWork.Paper1
