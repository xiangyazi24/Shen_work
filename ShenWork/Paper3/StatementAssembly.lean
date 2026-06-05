/-
  Paper3 generic statement-target assembly.

  This file packages statement-layer branch-data bridges from `Statements`.
  It adds no analytic estimates.
-/
import ShenWork.Paper3.Statements

open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

/-! ## Proposition 1.x targets -/

/-- Paper3 Proposition 1.2, Proposition 1.3, and Proposition 1.4 targets. -/
def Paper3Proposition1Targets
    (D : BoundedDomainData) (p : CM2Params)
    (C : Paper2Constants p) : Prop :=
  Proposition_1_2 D p ∧ Proposition_1_3 D p C ∧ Proposition_1_4 D p

/-- Frontier data for Paper3 Proposition 1.2--1.4. -/
structure Paper3Proposition1FrontierData
    (D : BoundedDomainData) (p : CM2Params)
    (C : Paper2Constants p) : Prop where
  negativeBound : NegativeSensitivityGlobalEventualBound D p
  proposition13 :
    0 < p.a → 0 < p.b → 1 ≤ p.m → StrongLogisticCondition p C →
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2GlobalClassicalSolution D p u v ∧
          InitialTrace D u₀ u ∧
          IsPaper2Bounded D u
  proposition14 :
    p.m = 1 → 1 ≤ p.β →
      ((p.a = 0 ∧ p.b = 0) ∨ (0 ≤ p.a ∧ 0 < p.b)) →
        p.χ₀ < chiBeta p →
          ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
            ∃ u v : ℝ → D.Point → ℝ,
              IsPaper2GlobalClassicalSolution D p u v ∧
              InitialTrace D u₀ u ∧
              IsPaper2Bounded D u

/-- Assemble Paper3 Propositions 1.2--1.4 from their statement-layer frontier
data. -/
theorem paper3_proposition1Targets_of_frontierData
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (hData : Paper3Proposition1FrontierData D p C) :
    Paper3Proposition1Targets D p C :=
  ⟨Proposition_1_2_of_negativeSensitivityGlobalEventualBound
      D p hData.negativeBound,
    Proposition_1_3.of_assumed_existence_branch hData.proposition13,
    Proposition_1_4.of_assumed_existence_branch hData.proposition14⟩

/-- Instance-facing wrapper for Paper3 Propositions 1.2--1.4. -/
theorem paper3_proposition1Targets_of_frontierDataFact
    (D : BoundedDomainData) (p : CM2Params) (C : Paper2Constants p)
    [hData : Fact (Paper3Proposition1FrontierData D p C)] :
    Paper3Proposition1Targets D p C :=
  paper3_proposition1Targets_of_frontierData hData.out

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

/-! ## Theorem 2.2 stability-threshold target -/

/-- Paper3 Theorem 2.2 from its branch-data package. -/
def Paper3Theorem22Target
    (D : BoundedDomainData) (p : CM2Params) (S : SpectralData)
    (N : StabilityNorms D) (C : Paper3Constants D p) : Prop :=
  Theorem_2_2 D p S N C

/-- Assemble Paper3 Theorem 2.2 from the statement-layer branch-data
package. -/
theorem paper3_Theorem_2_2_of_branchData
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (hData : Paper3Theorem22BranchData D p S N C) :
    Paper3Theorem22Target D p S N C :=
  Theorem_2_2.of_branchData hData

/-- Instance-facing wrapper for Paper3 Theorem 2.2. -/
theorem paper3_Theorem_2_2_of_branchDataFact
    (D : BoundedDomainData) (p : CM2Params) (S : SpectralData)
    (N : StabilityNorms D) (C : Paper3Constants D p)
    [hData : Fact (Paper3Theorem22BranchData D p S N C)] :
    Paper3Theorem22Target D p S N C :=
  paper3_Theorem_2_2_of_branchData hData.out

/-! ## Compactness and regularization targets -/

/-- Paper3 compactness/regularization support targets carried by the raw-data
package. -/
def Paper3CompactnessRegularizationTargets
    (D : BoundedDomainData) (p : CM2Params)
    (K : CompactnessData D) (N : StabilityNorms D)
    (C : Paper3Constants D p) : Prop :=
  Lemma_3_1 D p ∧
    Lemma_3_2 D p K ∧
      Lemma_3_3 D p N ∧
        Lemma_3_4 D p K ∧
          Lemma_3_5 D p C ∧
            Lemma_7_1 D K

/-- Assemble Paper3 compactness/regularization targets from the statement-layer
raw-data package. -/
theorem paper3_compactnessRegularizationTargets_of_rawData
    {D : BoundedDomainData} {p : CM2Params}
    {K : CompactnessData D} {N : StabilityNorms D}
    {C : Paper3Constants D p}
    (hData : Paper3CompactnessRegularizationRawData D p K N C) :
    Paper3CompactnessRegularizationTargets D p K N C :=
  compactness_regularization_support_of_rawData hData

/-- Instance-facing wrapper for Paper3 compactness/regularization targets. -/
theorem paper3_compactnessRegularizationTargets_of_rawDataFact
    (D : BoundedDomainData) (p : CM2Params)
    (K : CompactnessData D) (N : StabilityNorms D)
    (C : Paper3Constants D p)
    [hData : Fact (Paper3CompactnessRegularizationRawData D p K N C)] :
    Paper3CompactnessRegularizationTargets D p K N C :=
  paper3_compactnessRegularizationTargets_of_rawData hData.out

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

/-! ## Mainline umbrella targets -/

/-- Generic Paper3 mainline targets assembled from the existing proposition,
persistence, threshold-stability, compactness/regularization, and stability
branch-data packages. -/
def Paper3MainlineTargets
    (D : BoundedDomainData) (p : CM2Params) (S : SpectralData)
    (K : CompactnessData D) (N : StabilityNorms D)
    (C1 : Paper2Constants p) (C3 : Paper3Constants D p) : Prop :=
  Paper3Proposition1Targets D p C1 ∧
    Paper3UniformPersistenceTargets D p C3 ∧
      Paper3Theorem22Target D p S N C3 ∧
        Paper3CompactnessRegularizationTargets D p K N C3 ∧
          Paper3Stability23To25Targets D p N C3

/-- Bundled generic Paper3 mainline frontier data. -/
structure Paper3MainlineData
    (D : BoundedDomainData) (p : CM2Params) (S : SpectralData)
    (K : CompactnessData D) (N : StabilityNorms D)
    (C1 : Paper2Constants p) (C3 : Paper3Constants D p) : Prop where
  propositions : Paper3Proposition1FrontierData D p C1
  persistence : Paper3UniformPersistenceRawData D p C3
  theorem22 : Paper3Theorem22BranchData D p S N C3
  compactness : Paper3CompactnessRegularizationRawData D p K N C3
  stability : Paper3Stability23To25BranchData D p N C3

/-- Assemble the generic Paper3 mainline umbrella from the existing
statement-layer data records. -/
theorem paper3_mainlineTargets_of_data
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {K : CompactnessData D} {N : StabilityNorms D}
    {C1 : Paper2Constants p} {C3 : Paper3Constants D p}
    (hData : Paper3MainlineData D p S K N C1 C3) :
    Paper3MainlineTargets D p S K N C1 C3 :=
  ⟨paper3_proposition1Targets_of_frontierData hData.propositions,
    paper3_uniformPersistenceTargets_of_rawData hData.persistence,
    paper3_Theorem_2_2_of_branchData hData.theorem22,
    paper3_compactnessRegularizationTargets_of_rawData hData.compactness,
    paper3_stability23To25Targets_of_branchData hData.stability⟩

/-- Instance-facing wrapper for the generic Paper3 mainline umbrella. -/
theorem paper3_mainlineTargets_of_dataFact
    (D : BoundedDomainData) (p : CM2Params) (S : SpectralData)
    (K : CompactnessData D) (N : StabilityNorms D)
    (C1 : Paper2Constants p) (C3 : Paper3Constants D p)
    [hData : Fact (Paper3MainlineData D p S K N C1 C3)] :
    Paper3MainlineTargets D p S K N C1 C3 :=
  paper3_mainlineTargets_of_data hData.out

end

end ShenWork.Paper3
