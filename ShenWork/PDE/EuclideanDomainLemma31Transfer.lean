/-
  ShenWork/PDE/EuclideanDomainLemma31Transfer.lean

  General-N transfer, machine-checked.

  The General-N Phase-1 audit found exactly ONE substantive named
  Paper2/Paper3 headline that closes for every `BoundedDomainData` without a
  branch-data package that already contains the desired analytic conclusion:
  `Paper3.Lemma_3_1_proved`.  This file records that the transfer to the
  concrete finite-dimensional Euclidean instance is real — it typechecks and
  is clean-3 — rather than merely asserted in prose.

  Everything else in Paper2/Paper3 requires the smooth-domain trace/Green layer
  and the domain-linked Neumann elliptic/semigroup theory catalogued in
  `HANDOFF/generalN-phase1-report.md`; those are NOT provided here.
-/
import ShenWork.PDE.EuclideanDomainBasic
import ShenWork.Paper3.Statements

noncomputable section

namespace ShenWork.EuclideanDomain
namespace EuclideanDomainData

open ShenWork.Paper3

variable {N : ℕ} (D : EuclideanDomainData N)

/-- General-N transfer of Lemma 3.1: on the concrete Euclidean bounded-domain
instance, in every dimension `N` and for every bounded open `Ω`, Lemma 3.1
holds.  It specializes `Paper3.Lemma_3_1_proved`, which only unpacks the
regularity already bundled inside a positive global bounded solution. -/
theorem euclideanDomain_Lemma_3_1 (p : CM2Params) :
    Lemma_3_1 D.euclideanDomain p :=
  Lemma_3_1_proved D.euclideanDomain p

section AxiomAudit

#print axioms euclideanDomain_Lemma_3_1

end AxiomAudit

end EuclideanDomainData
end ShenWork.EuclideanDomain

end
