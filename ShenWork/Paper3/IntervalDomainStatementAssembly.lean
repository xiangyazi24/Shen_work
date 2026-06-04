/-
  Paper3 interval-domain statement-target assembly.

  This file only packages proved bridges from the interval-domain StabilityChain
  and Sectorial files.  It adds no new analytic frontier: the remaining
  hypotheses are the canonical core existence package and the concrete
  initial-continuity frontier already exposed downstream.
-/
import ShenWork.Paper3.IntervalDomainStabilityChain

open ShenWork.IntervalDomain
open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

/-- Concrete interval-domain Paper3 targets currently closed by the existing
StabilityChain/Sectorial infrastructure once the canonical core existence and
initial-continuity frontiers are supplied. -/
def IntervalDomainPaper3CoreStatementTargets
    (p : CM2Params) (M0 uBar vLower : ℝ) : Prop :=
  Lemma_3_1 intervalDomain p ∧
    Lemma_3_3 intervalDomain p intervalDomainStabilityNorms ∧
    UpperEnvelopeMonotonicityRaw intervalDomain p intervalDomain.supNorm ∧
    IntervalDomainStabilityChainTheorem21Target p M0 uBar vLower ∧
    IntervalDomainSectorialTheorem21And22UnconditionalTarget
      p M0 uBar vLower

/-- Core Paper3 interval-domain statement-target assembly.

The result records all concrete statement targets that are already connected by
existing branch theorems:
* `Lemma_3_1` is closed by the global classical-solution regularity field;
* concrete `Lemma_3_3` comes from `IntervalDomainInitialContinuityRaw`;
* upper-envelope monotonicity is the interval sup-norm max-principle bridge;
* the StabilityChain `Theorem_2_1` target uses the persistence part of the
  sectorial core existence package;
* the Sectorial `Theorem_2_1/2.2` target uses the full core existence package.
-/
theorem intervalDomain_paper3_coreStatementTargets_of_coreExistence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hcont : IntervalDomainInitialContinuityRaw p)
    (hcore : IntervalDomainSectorialMainlineCoreExistence p uBar) :
    IntervalDomainPaper3CoreStatementTargets p M0 uBar vLower := by
  have hchain :
      IntervalDomainStabilityChainConcreteMainlineTarget
        p M0 uBar vLower :=
    intervalDomain_stabilityChainConcreteMainlineTarget_of_sectorialMainlineExistence
      p M0 uBar vLower hcont hcore.to_mainlineExistence
  exact ⟨Lemma_3_1_proved intervalDomain p,
    hchain.1,
    hchain.2.1,
    hchain.2.2,
    intervalDomain_sectorialMainline_unconditionalTarget_of_coreExistence
      p M0 uBar vLower hcore⟩

/-- Instance-facing version of the core Paper3 interval-domain statement-target
assembly. -/
theorem intervalDomain_paper3_coreStatementTargets_of_coreExistenceFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    [hcont : Fact (IntervalDomainInitialContinuityRaw p)]
    [hcore : Fact (IntervalDomainSectorialMainlineCoreExistence p uBar)] :
    IntervalDomainPaper3CoreStatementTargets p M0 uBar vLower :=
  intervalDomain_paper3_coreStatementTargets_of_coreExistence
    p M0 uBar vLower hcont.out hcore.out

end

end ShenWork.Paper3
