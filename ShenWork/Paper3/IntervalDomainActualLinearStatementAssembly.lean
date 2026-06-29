import ShenWork.Paper3.IntervalDomainStatementAssembly
import ShenWork.Paper3.IntervalDomainPersistenceActualLinearSectorial

open ShenWork.IntervalDomain

namespace ShenWork.Paper3

noncomputable section

/-!
Actual-linear small-sensitivity entry points for the interval-domain Paper3
Theorem 2.1 persistence statement.

The analytic producer
`intervalDomain_sectorialTheorem21Persistence_actualLinearSmall` already
constructs the concrete persistence package in the `m = 1`, `β ≥ 1`,
small-positive-sensitivity regime.  This file wires that producer through the
statement-level `of_persistence` wrappers, so these endpoints no longer carry
an explicit `IntervalDomainSectorialTheorem21Persistence` input.
-/

/-- Concrete interval-domain Paper3 Theorem 2.1 in the actual-linear
small-sensitivity regime, with the persistence package produced internally. -/
theorem intervalDomain_paper3_Theorem_2_1_of_actualLinearSmall
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1))) :
    Theorem_2_1 intervalDomain p
      (intervalDomainPaper3Constants p M0 uBar vLower) :=
  intervalDomain_paper3_Theorem_2_1_of_persistence
    p M0 uBar vLower
    (intervalDomain_sectorialTheorem21Persistence_actualLinearSmall
      (uBar := uBar) ha hb hχ0 hm hβ hχ)

/-- Concrete interval-domain Paper3 Theorem 2.1 and its four named parts in the
actual-linear small-sensitivity regime. -/
theorem intervalDomain_paper3_Theorem_2_1_partTargets_of_actualLinearSmall
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1))) :
    IntervalDomainPaper3Theorem21PartTargets p M0 uBar vLower :=
  intervalDomain_paper3_Theorem_2_1_partTargets_of_persistence
    p M0 uBar vLower
    (intervalDomain_sectorialTheorem21Persistence_actualLinearSmall
      (uBar := uBar) ha hb hχ0 hm hβ hχ)

/-- Sectorial-constant interval-domain Paper3 Theorem 2.1 in the actual-linear
small-sensitivity regime. -/
theorem intervalDomain_paper3_Theorem_2_1_sectorial_of_actualLinearSmall
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1))) :
    Theorem_2_1 intervalDomain p
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower) :=
  intervalDomain_paper3_Theorem_2_1_sectorial_of_persistence
    p M0 uBar vLower
    (intervalDomain_sectorialTheorem21Persistence_actualLinearSmall
      (uBar := uBar) ha hb hχ0 hm hβ hχ)

end

end ShenWork.Paper3

#print axioms
  ShenWork.Paper3.intervalDomain_paper3_Theorem_2_1_of_actualLinearSmall
#print axioms
  ShenWork.Paper3.intervalDomain_paper3_Theorem_2_1_partTargets_of_actualLinearSmall
#print axioms
  ShenWork.Paper3.intervalDomain_paper3_Theorem_2_1_sectorial_of_actualLinearSmall
