/-
  ShenWork/Paper2/IntervalCarrySeamConjDischarge.lean

  χ₀<0 STEP 2 — specialize `u := conjugatePicardLimit p u₀ T` and DISCHARGE the
  CarrySeam atom `hvnn` from the LANDED conjugate-Picard cone data
  `ConjugateMildSolutionData` (IntervalConjugatePicard.lean:545), via the landed
  per-slice producer `carrySeam_hvnn` (IntervalChiNegMemHSigmaOne.lean:241).

  ## Two-way audit of the discharge
  `carrySeam_hvnn hμ hu_cont hu_nonneg` PRODUCES
    `∀ τ ∈ Icc 0 t, ∀ x, 0 ≤ resolverValue μ (cosineCoeffs (lift (u τ))) x`
  and CONSUMES, on `Icc 0 t`:
    * `hu_cont : ∀ τ ∈ Icc 0 t, Continuous (u τ)` — for τ>0 from `S.hcont`
      (`HasContinuousSlices`, i.e. `∀ τ, 0<τ → τ≤T → Continuous (u τ)`, with `t ≤ T`);
      for τ=0, `conjugatePicardLimit … 0 = fun _ => 0` (the guard `0 < 0` is false), so
      the slice is literally `fun _ => 0`, continuous.
    * `hu_nonneg : ∀ τ ∈ Icc 0 t, ∀ z, 0 ≤ u τ z` — for τ>0 from `S.hnonneg`; for τ=0
      the slice is `fun _ => 0`.
  Both inputs are SUPPLIED from `S : ConjugateMildSolutionData` (the landed conjugate
  mild-solution bundle whose `hcont`/`hnonneg` are built from the Picard contraction
  data).  No re-statement; the producer's hypotheses are genuinely met.

  ## Irreducible carried set (the χ₀<0 H¹ frontier), each atom audited in the report.
  No `sorry`/`admit`/`native_decide`/custom axiom.  New file only.
-/
import ShenWork.Paper2.IntervalChiNegMemHSigmaOne
import ShenWork.Paper2.IntervalConjugatePicard

noncomputable section

namespace ShenWork.Paper2.IntervalCarrySeamConjDischarge

open scoped Real
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2.IntervalDenomEnvelopeResolver (resolverValue)
open ShenWork.Paper2.IntervalChiNegMemHSigmaOne (carrySeam_hvnn)
open ShenWork.IntervalConjugatePicard (conjugatePicardLimit ConjugateMildSolutionData)

variable {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {μ : ℝ}

/-- The τ=0 slice of `conjugatePicardLimit` is the zero function (guard `0 < 0`
is false). -/
theorem conjugatePicardLimit_zero_slice (T : ℝ) :
    conjugatePicardLimit p u₀ T 0 = fun _ => (0 : ℝ) := by
  funext x
  simp [conjugatePicardLimit]

/-- **`hvnn` for `conjugatePicardLimit`, on `Icc 0 t` — DISCHARGED from
`ConjugateMildSolutionData`.**  Consumes `carrySeam_hvnn`, supplying its two slice
hypotheses (`Continuous`, `≥0`) from the landed cone bundle `S.hcont`/`S.hnonneg`
for τ>0 and the zero-slice fact for τ=0.  This removes `hvnn` from the carried set
of the χ₀<0 `CarrySeam` once `u` is the conjugate Picard fixed point. -/
theorem carrySeam_hvnn_conjugate (hμ : 0 < μ)
    (S : ConjugateMildSolutionData p u₀) {t : ℝ} (htT : t ≤ S.T)
    (hu : S.u = conjugatePicardLimit p u₀ S.T) :
    ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ x,
      0 ≤ resolverValue μ (cosineCoeffs (intervalDomainLift (S.u τ))) x := by
  refine carrySeam_hvnn hμ ?_ ?_
  · -- slice continuity on Icc 0 t
    intro τ hτ
    rcases eq_or_lt_of_le hτ.1 with h0 | h0
    · -- τ = 0 : slice is the zero function
      have hz : S.u τ = fun _ => (0 : ℝ) := by
        rw [hu, ← h0]; exact conjugatePicardLimit_zero_slice _
      rw [hz]; exact continuous_const
    · exact S.hcont τ h0 (le_trans hτ.2 htT)
  · -- slice nonnegativity on Icc 0 t
    intro τ hτ z
    rcases eq_or_lt_of_le hτ.1 with h0 | h0
    · have hz : S.u τ = fun _ => (0 : ℝ) := by
        rw [hu, ← h0]; exact conjugatePicardLimit_zero_slice _
      rw [hz]
    · exact S.hnonneg τ h0 (le_trans hτ.2 htT) z

end ShenWork.Paper2.IntervalCarrySeamConjDischarge

namespace ShenWork.Paper2.IntervalCarrySeamConjDischarge
section AxiomAudit
#print axioms conjugatePicardLimit_zero_slice
#print axioms carrySeam_hvnn_conjugate
end AxiomAudit
end ShenWork.Paper2.IntervalCarrySeamConjDischarge
