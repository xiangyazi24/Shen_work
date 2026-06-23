/-
  ShenWork/Paper2/IntervalChiNegDatumBound.lean

  **χ₀<0 hmean0 closer — the datum sup-bound `|u₀ x| ≤ M` from the existence Core.**

  The χ₀<0 capstones carry `hmean0 : |cosineCoeffs (lift u₀) 0| ≤ D.M`.  The landed
  cosine→mean bridge `conjugate_hmean0_of_datumBound` reduces it to `Continuous u₀`
  plus the datum sup-bound `∀ x, |u₀ x| ≤ M`.  Here that bound is DERIVED:

  * `ConjugateMildExistenceCore.hbase_ball` bounds the 0-th Picard iterate, which by
    definition is the heat semigroup `S(t)(lift u₀)`, by `M` on `(0,T]`.
  * `semigroup_initialApproach` (landed strong-continuity block) gives
    `|S(t)(lift u₀)(x) − u₀(x)| < ε` for small `t > 0`.
  * Hence `|u₀ x| ≤ |u₀ x − S(t)u₀ x| + |S(t)u₀ x| < ε + M` for every `ε > 0`, so
    `|u₀ x| ≤ M` (`le_of_forall_pos_le_add`).

  The M threading is exact: `conjugateMildData` is
  `conjugateMildSolutionData_of_data (Core).toData`, and both `of_data` and `toData`
  set the carried `M` to the Core `M` field — so the bound is for the SAME `D.M`.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalConjugatePicardCoreDischarge
import ShenWork.Paper2.IntervalConjugatePicardCoreInhabit
import ShenWork.Paper2.IntervalChiNegValueOpCont
import ShenWork.Paper2.IntervalChiNegCapstone
import ShenWork.Paper2.IntervalPicardIterateInitialApproach

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter ConjugateMildExistenceCore)
open ShenWork.IntervalPicardIterateInitialApproach (semigroup_initialApproach)
open ShenWork.Paper2.IntervalChiNegValueOpCont (conjugate_hmean0_of_datumBound)
open ShenWork.Paper2.IntervalChiNegCapstone (conjugateMildData)
open ShenWork.IntervalConjugatePicard (conjugateMildExistenceCore_exists)
open ShenWork.Paper2 (PaperPositiveInitialDatum)

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegDatumBound

/-- **The datum sup-bound from the existence Core.**  The 0-th Picard iterate is the
heat semigroup `S(t)(lift u₀)`, bounded by `C.M` on `(0,T]` (`hbase_ball`); letting
`t → 0⁺` via `semigroup_initialApproach` transfers the bound to `u₀`. -/
theorem core_datum_bound {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hu₀_cont : Continuous u₀) (C : ConjugateMildExistenceCore p u₀) :
    ∀ x : intervalDomainPoint, |u₀ x| ≤ C.M := by
  intro x
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  -- strong-continuity horizon `δ` for this `ε`.
  obtain ⟨δ, hδ, hδclose⟩ := semigroup_initialApproach p hu₀_cont ε hε
  -- a sample time `t₀ ∈ (0, T]` with `t₀ < δ`.
  set t₀ : ℝ := min (δ / 2) C.T with ht₀def
  have ht₀_pos : 0 < t₀ := lt_min (by linarith) C.hT
  have ht₀_le_T : t₀ ≤ C.T := min_le_right _ _
  have ht₀_lt_δ : t₀ < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  -- the heat-semigroup value at `t₀`.
  have hball := C.hbase_ball t₀ ht₀_pos ht₀_le_T x
  -- `conjugatePicardIter p u₀ 0 t₀ x = S(t₀)(lift u₀)(x.1)` definitionally.
  have hiter : conjugatePicardIter p u₀ 0 t₀ x
      = intervalFullSemigroupOperator t₀ (intervalDomainLift u₀) x.1 := rfl
  rw [hiter] at hball
  -- strong continuity at `t₀`.
  have hclose := hδclose t₀ ht₀_pos ht₀_lt_δ x
  -- `|u₀ x| ≤ |u₀ x − S| + |S| < ε + M`.
  have htri : |u₀ x|
      ≤ |u₀ x - intervalFullSemigroupOperator t₀ (intervalDomainLift u₀) x.1|
        + |intervalFullSemigroupOperator t₀ (intervalDomainLift u₀) x.1| := by
    have := abs_add_le (u₀ x - intervalFullSemigroupOperator t₀
      (intervalDomainLift u₀) x.1)
      (intervalFullSemigroupOperator t₀ (intervalDomainLift u₀) x.1)
    simpa using this
  have hclose' : |u₀ x - intervalFullSemigroupOperator t₀
      (intervalDomainLift u₀) x.1| < ε := by
    rw [abs_sub_comm]; exact hclose
  calc |u₀ x|
      ≤ |u₀ x - intervalFullSemigroupOperator t₀ (intervalDomainLift u₀) x.1|
        + |intervalFullSemigroupOperator t₀ (intervalDomainLift u₀) x.1| := htri
    _ ≤ ε + C.M := by
        apply add_le_add
        · exact le_of_lt hclose'
        · exact hball
    _ = C.M + ε := by ring

/-- **`hmean0` for the conjugate mild data.**  From the four faithful hypotheses,
extract the existence Core, derive the datum bound for the Core `M`, and close the
cosine-mean coefficient bound through `conjugate_hmean0_of_datumBound`.  The carried
`M` is exactly `(conjugateMildData …).M` (= the Core `M`), the value the capstone
exposes as `D.M`. -/
theorem conjugateMildData_hmean0 (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum ShenWork.IntervalDomain.intervalDomain u₀) :
    |cosineCoeffs (intervalDomainLift u₀) 0| ≤ (conjugateMildData p hα hγ hu₀).M := by
  have hu₀_cont : Continuous u₀ := (PaperPositiveInitialDatum.admissible hu₀).2
  -- the existence Core for these faithful hypotheses.
  set C : ConjugateMildExistenceCore p u₀ :=
    Classical.choice (conjugateMildExistenceCore_exists p hα hγ hu₀).choose_spec.1 with hCdef
  -- `(conjugateMildData …).M` is definitionally the Core `M`.
  have hM_eq : (conjugateMildData p hα hγ hu₀).M = C.M := rfl
  rw [hM_eq]
  -- datum bound for the Core `M`, then the cosine-mean bridge.
  exact conjugate_hmean0_of_datumBound hu₀_cont C.hM.le (core_datum_bound hu₀_cont C)

/-! ## AxiomAudit -/

section AxiomAudit
#print axioms core_datum_bound
#print axioms conjugateMildData_hmean0
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegDatumBound
