import ShenWork.Paper2.IntervalMildExistenceAssembly

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildPicardThreshold
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.IntervalMildExistenceAssembly

/-- A continuous strictly positive function on the compact interval subtype has a
uniform positive floor. -/
theorem intervalDomain_uniformFloor_of_continuous_pos
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀_cont : Continuous u₀) (hu₀_pos : ∀ x, 0 < u₀ x) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : intervalDomainPoint, c ≤ u₀ x := by
  haveI : CompactSpace intervalDomainPoint :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  haveI : Nonempty intervalDomainPoint :=
    ⟨⟨0, by constructor <;> norm_num⟩⟩
  obtain ⟨x₀, _hx₀, hx₀_min⟩ :=
    isCompact_univ.exists_isMinOn (Set.univ_nonempty : (Set.univ :
      Set intervalDomainPoint).Nonempty) hu₀_cont.continuousOn
  refine ⟨u₀ x₀, hu₀_pos x₀, ?_⟩
  intro x
  exact isMinOn_iff.mp hx₀_min x (Set.mem_univ x)

/-- Continuous strict positivity upgrades admissible data to the paper-faithful
closed-domain positive datum. -/
theorem intervalDomain_paperPositiveInitialDatum_of_continuous_pos
    {u₀ : intervalDomainPoint → ℝ}
    (hadm : intervalDomain.initialAdmissible u₀)
    (hu₀_cont : Continuous u₀) (hu₀_pos : ∀ x, 0 < u₀ x) :
    PaperPositiveInitialDatum intervalDomain u₀ := by
  exact ⟨hadm, intervalDomain_uniformFloor_of_continuous_pos hu₀_cont hu₀_pos⟩

/-- Assembly bridge with the closed-domain threshold discharged from compactness:
continuous strictly positive admissible data supply the floor required by the
banked Picard threshold. -/
theorem intervalDomain_mildExistenceData_of_continuous_positiveDatum
    (p : CM2Params) (hα_ge : 1 ≤ p.α) (hγ_ge : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hu₀_cont : Continuous u₀) (hu₀_pos : ∀ x, 0 < u₀ x) :
    ∃ D : MildExistenceData p u₀, 0 < D.T := by
  have hpaper : PaperPositiveInitialDatum intervalDomain u₀ :=
    intervalDomain_paperPositiveInitialDatum_of_continuous_pos
      hu₀.admissible hu₀_cont hu₀_pos
  exact intervalDomain_mildExistenceData_of_paperPositiveDatum
    p hα_ge hγ_ge hpaper

/-- Gradient mild-solution data with the u₀ threshold discharged from continuity
and strict positivity on the compact interval subtype. -/
theorem intervalDomain_gradientMildSolutionData_of_continuous_positiveDatum
    (p : CM2Params) (hα_ge : 1 ≤ p.α) (hγ_ge : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hu₀_cont : Continuous u₀) (hu₀_pos : ∀ x, 0 < u₀ x) :
    ∃ D : GradientMildSolutionData p u₀, 0 < D.T := by
  obtain ⟨E, hE⟩ :=
    intervalDomain_mildExistenceData_of_continuous_positiveDatum
      p hα_ge hγ_ge hu₀ hu₀_cont hu₀_pos
  exact ⟨gradientMildSolutionData_of_data E,
    by simpa [gradientMildSolutionData_of_data_T] using hE⟩

#print axioms intervalDomain_uniformFloor_of_continuous_pos
#print axioms intervalDomain_paperPositiveInitialDatum_of_continuous_pos
#print axioms intervalDomain_mildExistenceData_of_continuous_positiveDatum
#print axioms intervalDomain_gradientMildSolutionData_of_continuous_positiveDatum

end ShenWork.Paper2.IntervalMildExistenceAssembly
