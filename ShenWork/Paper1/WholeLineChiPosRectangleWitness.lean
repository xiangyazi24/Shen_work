import ShenWork.Paper1.WholeLineChiPosRectangleTargets

/-!
# Non-vacuity witnesses for the positive-sensitivity rectangle squeeze

The critical χ>0 convergence theorem runs on rectangles carrying two strict
scalar margins (`chiPosFloorGap` and `chiPosCeilingGap` both positive).  An
axiom-clean conditional statement proves nothing if those margins can never be
positive simultaneously, so this file exhibits an explicit inhabited instance
and records the exact algebraic reason the paper's threshold `χ < 1/2` is the
right one in the model case.

Model parameters: `m = α = γ = 1`, `χ = 1/4`; rectangle `[1/10, 3/2]`.
-/

open Real

noncomputable section

namespace ShenWork.Paper1

/-- The model parameter point `m = α = γ = 1`, `χ = 1/4`, which satisfies the
paper's positive-branch threshold `χ < 1/2`. -/
def chiPosWitnessParams : CMParams :=
  { m := 1, α := 1, γ := 1, χ := 1/4
    hm := le_refl 1, hα := le_refl 1, hγ := le_refl 1 }

theorem chiPosWitnessParams_chi_pos : 0 < chiPosWitnessParams.χ := by
  norm_num [chiPosWitnessParams]

theorem chiPosWitnessParams_chi_half : chiPosWitnessParams.χ < 1 / 2 := by
  norm_num [chiPosWitnessParams]

theorem chiPosWitnessParams_critical :
    chiPosWitnessParams.α =
      chiPosWitnessParams.m + chiPosWitnessParams.γ - 1 := by
  norm_num [chiPosWitnessParams]

/-- Both rectangle margins are strictly positive at the witness rectangle, so
the hypotheses of `ChiPosWholeLineRectangle` are simultaneously satisfiable:
the squeeze theorem is not vacuous. -/
theorem chiPosWitness_floorGap_pos :
    0 < chiPosFloorGap chiPosWitnessParams (3/2) (1/10) := by
  unfold chiPosFloorGap chiPosWitnessParams
  norm_num [Real.rpow_one, Real.rpow_zero]

theorem chiPosWitness_ceilingGap_pos :
    0 < chiPosCeilingGap chiPosWitnessParams (1/10) (3/2) := by
  unfold chiPosCeilingGap chiPosWitnessParams
  norm_num [Real.rpow_one, Real.rpow_zero]

/-- The floor margin at the equilibrium ceiling `MChi` is what forces
`χ < 1/2` in the model case: with `m = α = γ = 1` the floor equilibrium is
`ell = (1 - χ M) / (1 - χ)`, which is positive exactly when `χ M < 1`, and the
relevant ceiling is `M = MChi = 1 / (1 - χ)`.  Hence the threshold condition is
`χ / (1 - χ) < 1`, i.e. `χ < 1/2`. -/
theorem chiPos_model_threshold_iff {χ : ℝ} (hχ0 : 0 ≤ χ) (hχ1 : χ < 1) :
    χ * (1 / (1 - χ)) < 1 ↔ χ < 1 / 2 := by
  have h1χ : 0 < 1 - χ := by linarith
  rw [mul_one_div, div_lt_one h1χ]
  constructor <;> intro h <;> linarith

section AxiomAudit

#print axioms chiPosWitness_floorGap_pos
#print axioms chiPosWitness_ceilingGap_pos
#print axioms chiPos_model_threshold_iff

end AxiomAudit

end ShenWork.Paper1
