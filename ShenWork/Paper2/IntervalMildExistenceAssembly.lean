import ShenWork.Paper2.IntervalMildPicardThreshold
import ShenWork.Paper2.IntervalMildToLocalExistence
import ShenWork.Paper2.IntervalDomainPIDBound

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildPicardThreshold
open ShenWork.IntervalMildToLocalExistence
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.IntervalMildExistenceAssembly

/-- Picard input data from a positive datum with the extra closed-domain floor
needed by the banked small-time positivity argument. -/
theorem intervalDomain_mildExistenceData_of_positiveDatum
    (p : CM2Params) (hα_ge : 1 ≤ p.α) (hγ_ge : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {M c : ℝ} (hM : 0 < M) (hc : 0 < c)
    (hbound : ∀ x : intervalDomainPoint, |u₀ x| ≤ M)
    (hfloor : ∀ x : intervalDomainPoint, c ≤ u₀ x) :
    ∃ D : MildExistenceData p u₀, 0 < D.T := by
  obtain ⟨δ, hδ, hδdata⟩ :=
    thresholdMildExistenceData_exists p hM hc hα_ge hγ_ge
  obtain ⟨D, hDT⟩ := hδdata u₀ hu₀.admissible.2 hbound hfloor
  exact ⟨D, by simpa [hDT] using hδ⟩

/-- Paper-faithful positive data supply the closed-domain floor required by
`intervalDomain_mildExistenceData_of_positiveDatum`. -/
theorem intervalDomain_mildExistenceData_of_paperPositiveDatum
    (p : CM2Params) (hα_ge : 1 ≤ p.α) (hγ_ge : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    ∃ D : MildExistenceData p u₀, 0 < D.T := by
  obtain ⟨M, hM, hbound⟩ :=
    ShenWork.MinPersistenceAtoms.pid_exists_bound hu₀.toPositive
  obtain ⟨c, hc, hfloor⟩ := hu₀.floor
  exact intervalDomain_mildExistenceData_of_positiveDatum
    p hα_ge hγ_ge hu₀.toPositive hM hc hbound hfloor

/-- Convert assembled Picard input data into packaged gradient mild-solution
data. -/
theorem intervalDomain_gradientMildSolutionData_of_positiveDatum
    (p : CM2Params) (hα_ge : 1 ≤ p.α) (hγ_ge : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {M c : ℝ} (hM : 0 < M) (hc : 0 < c)
    (hbound : ∀ x : intervalDomainPoint, |u₀ x| ≤ M)
    (hfloor : ∀ x : intervalDomainPoint, c ≤ u₀ x) :
    ∃ D : GradientMildSolutionData p u₀, 0 < D.T := by
  obtain ⟨E, hE⟩ :=
    intervalDomain_mildExistenceData_of_positiveDatum
      p hα_ge hγ_ge hu₀ hM hc hbound hfloor
  exact ⟨gradientMildSolutionData_of_data E,
    by simpa [gradientMildSolutionData_of_data_T] using hE⟩

/-- The fixed-point plus regularity bundle gives `IsMildSolutionData`.  This is
the explicit `GradientMildSolutionData → IsMildSolutionData` wiring step. -/
theorem intervalDomain_isMildSolutionData_of_gradientMildSolutionData
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (hfp : ∀ t x, 0 ≤ t → t ≤ D.T →
      D.u t x = intervalDuhamelOperator p u₀ D.u t x)
    (hreg : RegularityBootstrap p D.T u₀ D.u) :
    ∃ v : ℝ → intervalDomainPoint → ℝ,
      IsMildSolutionData p D.T u₀ D.u v :=
  isMildSolutionData_of_fp_and_regularity p u₀ hfp hreg

/-- Final formal bridge through `localExistence_of_isMildSolutionData`.  The
non-Picard inputs are exactly the old-Duhamel fixed point and regularity
bootstrap data. -/
theorem intervalDomain_localExistence_of_gradientMildSolutionData
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (D : GradientMildSolutionData p u₀)
    (hfp : ∀ t x, 0 ≤ t → t ≤ D.T →
      D.u t x = intervalDuhamelOperator p u₀ D.u t x)
    (hreg : RegularityBootstrap p D.T u₀ D.u) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u₀ u := by
  obtain ⟨v, hdata⟩ :=
    intervalDomain_isMildSolutionData_of_gradientMildSolutionData p D hfp hreg
  exact localExistence_of_isMildSolutionData p u₀ hu₀ D.hT hdata

#print axioms intervalDomain_mildExistenceData_of_positiveDatum
#print axioms intervalDomain_mildExistenceData_of_paperPositiveDatum
#print axioms intervalDomain_gradientMildSolutionData_of_positiveDatum
#print axioms intervalDomain_isMildSolutionData_of_gradientMildSolutionData
#print axioms intervalDomain_localExistence_of_gradientMildSolutionData

end ShenWork.Paper2.IntervalMildExistenceAssembly

