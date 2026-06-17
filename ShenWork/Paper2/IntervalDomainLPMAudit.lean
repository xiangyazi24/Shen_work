/-
  Paper 2 interval Lp-Moser audit.

  The existing interval ladder proves Lemma 2.6 from the named frontier package
  in `IntervalDomainTheorem11Composite`.  The full `BranchData` record is still
  blocked by the remaining estimate fields, and the generic record cannot be
  manufactured from the current abstract API alone.
-/
import ShenWork.Paper2.IntervalDomainTheorem11

namespace ShenWork.Paper2.IntervalDomainLPMAudit

noncomputable section

open ShenWork.Paper2.IntervalDomainTheorem11Composite

abbrev lemma26IntervalDomainFromFrontiers :=
  Lemma_2_6_intervalDomain_of_mass_gradient_frontier_inside_nonneg

abbrev corollary21IntervalDomainFromFrontiers :=
  Corollary_2_1_intervalDomain_of_mass_gradient_frontier_from_solution_positivity

theorem not_forall_branchData_from_lemma26 :
    ¬ (∀ D : BoundedDomainData, ∀ p : CM2Params,
        Paper2BootstrapEstimateBranchData D p) := by
  intro h
  exact not_forall_Lemma_2_6
    (fun D => (h D proposition21CounterParams).lemma26)

theorem not_forall_branchData_from_lemma27 :
    ¬ (∀ D : BoundedDomainData, ∀ p : CM2Params,
        Paper2BootstrapEstimateBranchData D p) := by
  intro h
  exact not_forall_Lemma_2_7
    (fun D => (h D proposition21CounterParams).lemma27)

theorem not_forall_branchData_from_prop22 :
    ¬ (∀ D : BoundedDomainData, ∀ p : CM2Params,
        Paper2BootstrapEstimateBranchData D p) := by
  intro h
  exact not_forall_Proposition_2_2 (fun D p => (h D p).prop22)

theorem not_forall_branchData_from_prop23 :
    ¬ (∀ D : BoundedDomainData, ∀ p : CM2Params,
        Paper2BootstrapEstimateBranchData D p) := by
  intro h
  exact not_forall_Proposition_2_3 (fun D p => (h D p).prop23)

theorem not_forall_branchData_from_prop24 :
    ¬ (∀ D : BoundedDomainData, ∀ p : CM2Params,
        Paper2BootstrapEstimateBranchData D p) := by
  intro h
  exact not_forall_Proposition_2_4
    (fun D p => Proposition_2_4.of_branchData (h D p))

theorem not_forall_branchData_from_prop25 :
    ¬ (∀ D : BoundedDomainData, ∀ p : CM2Params,
        Paper2BootstrapEstimateBranchData D p) := by
  intro h
  exact not_forall_Proposition_2_5 (fun D p => (h D p).prop25)

end

end ShenWork.Paper2.IntervalDomainLPMAudit
