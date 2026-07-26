/-
  Paper 2, Theorem 1.3: closure of the m < 1 audited boundary.

  The audit (`IntervalSharpSemigroupResidualAudit`) shows that for m < 1 the
  case-(iv) exponent guard `2 - 2m < q*` can FAIL while the printed fourth
  alternative holds (`caseIVGuardCounterParams`), so the minimal honest
  residual interface is not inhabitable there.  This file shows the guard
  failure obstructs only that interface, not the theorem: the printed
  Theorem 1.3 gates its global/boundedness conjunct on `1 ≤ m`, so for
  `m < 1` the theorem's entire content is its first conjunct — local
  existence of a bounded classical branch — and that is carried
  unconditionally by the faithful general-`m` positive-strip Picard fixed
  point, whose trajectory is bounded by its own ball radius.  No energy
  estimate, no exponent guard, and no constant fidelity are consumed.

  Consequently `Theorem_1_3 intervalDomainM p C` holds for EVERY constant
  record `C` whenever `m < 1`, in particular for the audit's guard
  counterexample package, and combined with the `1 ≤ m` paper-constant
  closure the case-(iv) critical family closes for every `m > 0`.
-/
import ShenWork.Paper2.IntervalDomainMLocalExistenceAllExponents
import ShenWork.Paper2.IntervalSharpSemigroupResidualAudit

open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainTheorem13MLtOneClosure

open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit
  (ConjugateMildSolutionDataM conjugateMildSolutionDataM_exists_paperPositive)

/-- A pointwise uniform bound on interior slices gives the statement-level
`IsPaper2BoundedBefore` on the faithful general-`m` domain, whose
`supNorm` field is `intervalDomainSupNorm`. -/
theorem intervalDomainM_boundedBefore_of_pointwise_uniform_bound
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hpoint : ∀ t, 0 < t → t < T →
      ∀ x : intervalDomainPoint, |u t x| ≤ M) :
    IsPaper2BoundedBefore intervalDomainM T u := by
  refine ⟨M, ?_⟩
  intro t ht0 htT
  change intervalDomainSupNorm (u t) ≤ M
  unfold intervalDomainSupNorm
  exact Real.sSup_le
    (fun _ hy => by obtain ⟨x, rfl⟩ := hy; exact hpoint t ht0 htT x)
    hM

/-- Faithful general-`m` local existence WITH the a-priori bound of the
constructed branch, for arbitrary paper-positive data and all positive
exponents.  The bound is the Picard ball radius of the positive-strip
fixed point; no strong-logistic hypothesis is used. -/
theorem intervalDomainM_localExistence_bounded_allExponents
    (p : CM2Params) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PaperPositiveInitialDatum intervalDomainM u₀ →
        ∃ T > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
          IsPaper2ClassicalSolution intervalDomainM p T u v ∧
          InitialTrace intervalDomainM u₀ u ∧
          IsPaper2BoundedBefore intervalDomainM T u := by
  intro u₀ hu₀
  let D := (conjugateMildSolutionDataM_exists_paperPositive p hu₀).some
  have H := intervalDomainM_classicalSolution_of_mildData p hu₀.admissible.2 D
  refine ⟨D.T, D.hT, D.u,
    ShenWork.IntervalCoupledRegularityBootstrap.coupledChemicalConcentration
      p D.u, H.1, H.2, ?_⟩
  exact intervalDomainM_boundedBefore_of_pointwise_uniform_bound D.hM.le
    (fun t ht0 htT x => D.hbound t ht0 htT.le x)

/-- **Theorem 1.3 on the faithful general-`m` interval model, `m < 1`, for
every constant record.**  The printed statement gates its global conjunct on
`1 ≤ m`, so in the `m < 1` regime its content is exactly the bounded local
branch, which is unconditional.  In particular neither the case-(iv)
exponent guard nor the critical-constant identification is needed here —
the audited `m < 1` boundary of the residual interface is a boundary of
that interface only. -/
theorem Theorem_1_3_intervalDomainM_of_m_lt_one
    (p : CM2Params) (C : Paper2Constants p) (hm : p.m < 1) :
    Theorem_1_3 intervalDomainM p C := by
  intro _ha _hb _hm_pos _hstrong
  refine ⟨?_, ?_⟩
  · intro u₀ hu₀
    exact intervalDomainM_localExistence_bounded_allExponents p u₀ hu₀
  · intro hm_ge
    exact absurd hm_ge (not_le.mpr hm)

open ShenWork.Paper2.IntervalSharpSemigroupResidualAudit in
/-- The audit's guard counterexample package (`m = 1/4`, printed case (iv)
satisfied, exponent guard violated, residual interface refuted) nevertheless
satisfies the full printed Theorem 1.3 — with its own arbitrary constant
record.  The guard failure was an artifact of routing everything through the
`1 ≤ m` energy chain. -/
theorem Theorem_1_3_intervalDomainM_caseIVGuardCounter :
    Theorem_1_3 intervalDomainM
      caseIVGuardCounterParams caseIVGuardCounterConstants :=
  Theorem_1_3_intervalDomainM_of_m_lt_one
    caseIVGuardCounterParams caseIVGuardCounterConstants
    (by norm_num [caseIVGuardCounterParams])

open ShenWork.Paper2.IntervalSharpSemigroupResidualAudit in
/-- Case-(iv) capstone for EVERY `m > 0`: on the one-dimensional faithful
model with positive sensitivity and the case-(iv) critical equality, the
printed Theorem 1.3 closes with a concrete constant record — the literal
paper constant when `1 ≤ m` (global regime), and any record when `m < 1`
(where no critical constant is consumed). -/
theorem Theorem_1_3_intervalDomainM_caseIV_all_m
    (p : CM2Params) (hN : p.N = 1) (hχ : 0 < p.χ₀)
    (hcrit : p.α = 2 * p.m + p.γ - 2) :
    ∃ C : Paper2Constants p, Theorem_1_3 intervalDomainM p C := by
  by_cases hm : 1 ≤ p.m
  · exact ⟨_,
      Theorem_1_3_intervalDomainM_caseIV_with_paperConstants
        p hN hχ hm hcrit⟩
  · exact ⟨⟨0, le_rfl⟩,
      Theorem_1_3_intervalDomainM_of_m_lt_one p ⟨0, le_rfl⟩ (not_le.mp hm)⟩

section AxiomAudit

#print axioms intervalDomainM_boundedBefore_of_pointwise_uniform_bound
#print axioms intervalDomainM_localExistence_bounded_allExponents
#print axioms Theorem_1_3_intervalDomainM_of_m_lt_one
#print axioms Theorem_1_3_intervalDomainM_caseIVGuardCounter
#print axioms Theorem_1_3_intervalDomainM_caseIV_all_m

end AxiomAudit

end ShenWork.Paper2.IntervalDomainTheorem13MLtOneClosure

end
