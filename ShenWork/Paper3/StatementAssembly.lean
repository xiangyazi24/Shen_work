/-
  Paper3 generic statement-target assembly.

  This file packages statement-layer branch-data bridges from `Statements`.
  It adds no analytic estimates.
-/
import ShenWork.Paper3.Statements

namespace ShenWork.Paper3

noncomputable section

/-! ## Theorem 2.1 persistence targets -/

/-- Paper3 Theorem 2.1 together with its four part statements from the same
raw persistence package. -/
def Paper3UniformPersistenceTargets
    (D : BoundedDomainData) (p : CM2Params)
    (C : Paper3Constants D p) : Prop :=
  Theorem_2_1 D p C ∧
    Theorem_2_1_part1 D p ∧
    Theorem_2_1_part2 D p ∧
    Theorem_2_1_part3 D p ∧
    Theorem_2_1_part4 D p C

/-- Assemble Paper3 Theorem 2.1 and all four part statements from the
statement-layer raw persistence data. -/
theorem paper3_uniformPersistenceTargets_of_rawData
    {D : BoundedDomainData} {p : CM2Params}
    {C : Paper3Constants D p}
    (hData : Paper3UniformPersistenceRawData D p C) :
    Paper3UniformPersistenceTargets D p C := by
  have h21 : Theorem_2_1 D p C :=
    Theorem_2_1.of_uniformPersistenceRawData hData
  exact ⟨h21, h21.1, h21.2.1, h21.2.2.1, h21.2.2.2⟩

/-- Instance-facing wrapper for Paper3 Theorem 2.1 persistence targets. -/
theorem paper3_uniformPersistenceTargets_of_rawDataFact
    (D : BoundedDomainData) (p : CM2Params)
    (C : Paper3Constants D p)
    [hData : Fact (Paper3UniformPersistenceRawData D p C)] :
    Paper3UniformPersistenceTargets D p C :=
  paper3_uniformPersistenceTargets_of_rawData hData.out

/-! ## Theorem 2.3--2.5 stability targets -/

/-- Paper3 Theorems 2.3--2.5 from the same stability branch-data package. -/
def Paper3Stability23To25Targets
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (C : Paper3Constants D p) : Prop :=
  Theorem_2_3 D p N ∧ Theorem_2_4 D p N C ∧ Theorem_2_5 D p N C

/-- Assemble Paper3 Theorems 2.3--2.5 from the statement-layer stability
branch-data package. -/
theorem paper3_stability23To25Targets_of_branchData
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {C : Paper3Constants D p}
    (hData : Paper3Stability23To25BranchData D p N C) :
    Paper3Stability23To25Targets D p N C :=
  Theorem_2_3_to_2_5.of_stabilityBranchData hData

/-- Instance-facing wrapper for Paper3 Theorems 2.3--2.5. -/
theorem paper3_stability23To25Targets_of_branchDataFact
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (C : Paper3Constants D p)
    [hData : Fact (Paper3Stability23To25BranchData D p N C)] :
    Paper3Stability23To25Targets D p N C :=
  paper3_stability23To25Targets_of_branchData hData.out

end

end ShenWork.Paper3
