import ShenWork.Paper2.IntervalUniformTruncatedMapCertificateProducer

/-!
# The `mapCertificate` datum — `UniformTruncatedConjugateMapCertificateData` producer

The 4th χ₀<0 assembly input.  This file assembles the `∀M,u₀,C` family datum from
the committed per-`C` producer `uniformTruncatedConjugateMapCertificate_of_realizedBudgets`.

## Route decision (a vs b) — resolved by reading the component theorems

The certificate has four fields; they split as follows against the core
`UniformConjugateMildExistenceCore` (whose `CQ/CLsup/CQsup` are FREE scalar fields
constrained only by nonnegativity):

* `hmeas_preserved` — **route (a)**: provable for ANY `C` directly from the core's
  own carried field `C.hmeas_preserved` (no budget needed).
* `hmapsTo`, `hcont_preserved` — **NOT route (a)**: the component theorems
  `truncatedConjugateDuhamelMap_mapsTo_of_realized_budget` and
  `…_hasContinuousSlices_of_realized_budget` both **consume** `HS`
  (`UniformTruncatedSourceSupBudgetRealization`) and rewrite `H.hCQsup_eq` — i.e. they
  need `C.CQsup` to **equal** the concrete source-sup formula `R·(‖grad‖₂·2ν R^γ)`.
  For an arbitrary `C` this is false (`CQsup` is free), and **no core field pins it**:
  route (b)'s "core-validity field" does not exist in the current struct.  The HS
  docstring says as much — "the scalar structure does not currently retain them."
* `hcontr` — needs `HD` (`UniformTruncatedDuhamelDifferenceCertificate`: the truncated
  flux/logistic Lipschitz differences).  **No in-repo producer of `HD` exists.**

Hence neither pure route closes the unconditional `∀C` datum.  What IS sound is the
reduction below: given per-core suppliers of `HS` and `HD`, the datum follows.  The two
suppliers are the exact remaining obligations, named precisely (see the residual note).
-/

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

open ShenWork.Paper2
open ShenWork.IntervalConjugatePicard
open ShenWork.IntervalDomain

/-- **`mapCertificate` datum, reduced to its two genuine per-core inputs.**

Given, for every core `C`, the source-sup budget realization `HS` (the
`CQsup/CLsup/CQ = formula` equalities the scalar core does not retain) and the
Duhamel difference certificate `HD` (the truncated flux/logistic Lipschitz
differences), the full `∀M,u₀,C` map-certificate datum follows.  `hmeas_preserved`
needs neither — it comes straight from `C.hmeas_preserved`. -/
theorem uniformTruncatedConjugateMapCertificateData_of_realizations
    {p : CM2Params} (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (HS : ∀ {u₀ : intervalDomainPoint → ℝ}
        (C : UniformConjugateMildExistenceCore p u₀),
        UniformTruncatedSourceSupBudgetRealization p C)
    (HD : ∀ {u₀ : intervalDomainPoint → ℝ}
        (C : UniformConjugateMildExistenceCore p u₀),
        UniformTruncatedDuhamelDifferenceCertificate p C) :
    UniformTruncatedConjugateMapCertificateData p := by
  intro M hM u₀ hu₀ hbound C
  exact uniformTruncatedConjugateMapCertificate_of_realizedBudgets hα hγ C (HS C) (HD C)

end ShenWork.Paper2.BFormPositiveDatumNegPart
