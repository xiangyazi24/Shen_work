/-
  Paper2 unit-point statement-target assembly.

  This file packages the already-proved unit-point logistic bridges.  It adds
  no ODE analysis beyond the imported `UnitPointLogisticBridge`.
-/
import ShenWork.Paper2.UnitPointLogisticBridge

namespace ShenWork.Paper2

noncomputable section

/-! ## Unit-point main statement targets -/

/-- Unit-point Paper2 targets closed unconditionally by the logistic bridge:
the logistic package, Theorem 1.1, and Theorem 1.3. -/
def UnitPointPaper2MainStatementTargets
    (p : CM2Params) (C : Paper2Constants p) : Prop :=
  UnitPointLogisticNonminimalPackage p ∧
    Theorem_1_1 unitPointDomain p ∧
    Theorem_1_3 unitPointDomain p C

/-- Assemble the unit-point Paper2 main targets from the logistic bridge. -/
theorem unitPointPaper2_mainStatementTargets
    (p : CM2Params) (C : Paper2Constants p) :
    UnitPointPaper2MainStatementTargets p C :=
  ⟨unitPointDomain.UnitPointLogisticNonminimalPackage_holds p,
    Theorem_1_1_unitPointDomain_holds p,
    unitPointDomain.Theorem_1_3_holds p C⟩

/-- Single-target wrapper for the unit-point logistic nonminimal package. -/
theorem unitPointPaper2_logisticNonminimalPackage
    (p : CM2Params) :
    UnitPointLogisticNonminimalPackage p :=
  unitPointDomain.UnitPointLogisticNonminimalPackage_holds p

/-- Single-target wrapper for unit-point Paper2 Theorem 1.1. -/
theorem unitPointPaper2_Theorem_1_1
    (p : CM2Params) :
    Theorem_1_1 unitPointDomain p :=
  Theorem_1_1_unitPointDomain_holds p

/-- Single-target wrapper for unit-point Paper2 Theorem 1.3. -/
theorem unitPointPaper2_Theorem_1_3
    (p : CM2Params) (C : Paper2Constants p) :
    Theorem_1_3 unitPointDomain p C :=
  unitPointDomain.Theorem_1_3_holds p C

/-! ## Unit-point Theorem 1.2 target -/

/-- Unit-point Theorem 1.2 target under the genuine exclusion of the
unbounded ODE slice `0 < a ∧ b = 0`. -/
theorem unitPointPaper2_Theorem_1_2_when_not_a_pos_b_zero
    (p : CM2Params)
    (hnot : ¬ (0 < p.a ∧ p.b = 0)) :
    Theorem_1_2 unitPointDomain p :=
  unitPointDomain.Theorem_1_2_when_not_a_pos_b_zero p hnot

/-- Unit-point Paper2 targets combining the unconditional main targets with
Theorem 1.2 under its unit-point exclusion hypothesis. -/
def UnitPointPaper2MainWithTheorem12Targets
    (p : CM2Params) (C : Paper2Constants p) : Prop :=
  UnitPointPaper2MainStatementTargets p C ∧ Theorem_1_2 unitPointDomain p

/-- Assemble the unit-point main targets and conditional Theorem 1.2 target. -/
theorem unitPointPaper2_mainWithTheorem12Targets
    (p : CM2Params) (C : Paper2Constants p)
    (hnot : ¬ (0 < p.a ∧ p.b = 0)) :
    UnitPointPaper2MainWithTheorem12Targets p C :=
  ⟨unitPointPaper2_mainStatementTargets p C,
    unitPointPaper2_Theorem_1_2_when_not_a_pos_b_zero p hnot⟩

end

end ShenWork.Paper2
