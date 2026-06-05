/-
  Paper3 unit-point statement-target assembly.

  This file packages the unit-point bridges proved in
  `UnitPointLogisticBridge`.  It adds no ODE analysis.
-/
import ShenWork.Paper3.UnitPointLogisticBridge

open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

/-! ## Unit-point Proposition 1.x targets -/

/-- Unit-point Paper3 Proposition 1.3 and Proposition 1.4 targets. -/
def UnitPointPaper3Proposition13And14Targets
    (p : CM2Params) (C : Paper2Constants p) : Prop :=
  Proposition_1_3 unitPointDomain p C ∧ Proposition_1_4 unitPointDomain p

/-- Assemble the unit-point Paper3 Proposition 1.3 and Proposition 1.4
targets from the existing logistic/decay bridge. -/
theorem unitPointPaper3_proposition13And14Targets
    (p : CM2Params) (C : Paper2Constants p) :
    UnitPointPaper3Proposition13And14Targets p C :=
  ⟨unitPointDomain.Proposition_1_3_holds p C,
    unitPointDomain.Proposition_1_4_holds p⟩

/-- Single-target wrapper for unit-point Paper3 Proposition 1.3. -/
theorem unitPointPaper3_Proposition_1_3
    (p : CM2Params) (C : Paper2Constants p) :
    Proposition_1_3 unitPointDomain p C :=
  unitPointDomain.Proposition_1_3_holds p C

/-- Single-target wrapper for unit-point Paper3 Proposition 1.4. -/
theorem unitPointPaper3_Proposition_1_4
    (p : CM2Params) :
    Proposition_1_4 unitPointDomain p :=
  unitPointDomain.Proposition_1_4_holds p

/-- Single-target wrapper for unit-point Paper3 Proposition 1.2 under the
genuine exclusion of the unbounded ODE slice `0 < a ∧ b = 0`. -/
theorem unitPointPaper3_Proposition_1_2_when_not_a_pos_b_zero
    (p : CM2Params)
    (hnot : ¬ (0 < p.a ∧ p.b = 0)) :
    Proposition_1_2 unitPointDomain p :=
  unitPointDomain.Proposition_1_2_when_not_a_pos_b_zero p hnot

/-- Unit-point Proposition 1.x targets including Proposition 1.2 under its
unit-point exclusion hypothesis. -/
def UnitPointPaper3Proposition1Targets
    (p : CM2Params) (C : Paper2Constants p) : Prop :=
  Proposition_1_2 unitPointDomain p ∧
    UnitPointPaper3Proposition13And14Targets p C

/-- Assemble unit-point Paper3 Proposition 1.2, 1.3, and 1.4 targets. -/
theorem unitPointPaper3_proposition1Targets
    (p : CM2Params) (C : Paper2Constants p)
    (hnot : ¬ (0 < p.a ∧ p.b = 0)) :
    UnitPointPaper3Proposition1Targets p C :=
  ⟨unitPointPaper3_Proposition_1_2_when_not_a_pos_b_zero p hnot,
    unitPointPaper3_proposition13And14Targets p C⟩

/-! ## Unit-point Theorem 2.1 branch targets -/

/-- Unit-point Paper3 Theorem 2.1 in the positive-logistic, nonpositive
sensitivity branch. -/
theorem unitPointPaper3_Theorem_2_1_when_a_pos_chi_nonpos
    (p : CM2Params) (C : Paper3Constants unitPointDomain p)
    (ha : 0 < p.a) (hχ : p.χ₀ ≤ 0) :
    Theorem_2_1 unitPointDomain p C :=
  unitPointDomain.Theorem_2_1_when_a_pos_chi_nonpos p ha hχ C

/-- Unit-point Paper3 Theorem 2.1 in the positive-logistic, `β < 1` branch. -/
theorem unitPointPaper3_Theorem_2_1_when_a_pos_beta_lt_one
    (p : CM2Params) (C : Paper3Constants unitPointDomain p)
    (ha : 0 < p.a) (hβ : p.β < 1) :
    Theorem_2_1 unitPointDomain p C :=
  unitPointDomain.Theorem_2_1_when_a_pos_beta_lt_one p ha hβ C

end

end ShenWork.Paper3
