import ShenWork.Paper2.IntervalDomainMChiNonposHeadline
import ShenWork.Paper2.IntervalChiNegHeadline
import ShenWork.Paper2.IntervalDomainTheorem13MinimalResidual
import ShenWork.Paper2.IntervalDomainTheorem13CorrectedHeadline
import ShenWork.Paper3.IntervalDomainMTheorem23Eventual
import ShenWork.Paper3.IntervalDomainMTheorem24Eventual

/-!
# All-data non-vacuity for the faithful interval stability theorems

The eventual Paper 3 stability predicates quantify over an already existing
`PositiveGlobalBoundedSolution`.  This file supplies that carrier for every
admissible datum which is strictly positive on the closed unit interval.  No
smallness or closeness-to-equilibrium hypothesis is imposed.

For `χ₀ ≤ 0`, the carrier comes from the faithful general-`m` maximum-principle
bound and maximal continuation.  For `χ₀ > 0`, the same conclusion is recorded
on the intersection with Paper 2's corrected strong-logistic alternatives.
-/

namespace ShenWork.Paper3

open ShenWork.IntervalDomain
open ShenWork.Paper2
open Set
open ShenWork.Paper2.IntervalDomainMChiNonpos
open ShenWork.Paper2.IntervalDomainTheorem13CorrectedBoundedness
open ShenWork.Paper2.IntervalDomainTheorem13CorrectedContinuation
open ShenWork.Paper2.IntervalDomainTheorem13CorrectedHeadline
open ShenWork.Paper2.IntervalDomainTheorem13MinimalResidual

noncomputable section

/-- Global bounded existence for every admissible datum that is strictly
positive on the whole concrete interval.  On `intervalDomainM`, admissibility
includes continuity and boundedness. -/
def AllPositiveContinuousDataGlobalBoundedExistence
    (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ u₀ : D.Point → ℝ,
    PositiveInitialDatum D u₀ →
    (∀ x, 0 < u₀ x) →
      ∃ u v : ℝ → D.Point → ℝ,
        PositiveGlobalBoundedSolution D p u v ∧
        InitialTrace D u₀ u

/-- Closed-interval strict positivity plus the concrete admissibility
condition gives the uniform positive floor required by Paper 2 continuation. -/
theorem intervalDomainM_paperPositiveInitialDatum_of_positive_continuous
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hu₀_pos : ∀ x, 0 < u₀ x) :
    PaperPositiveInitialDatum intervalDomainM u₀ := by
  refine ⟨hu₀.admissible, ?_⟩
  haveI : CompactSpace intervalDomainPoint :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  haveI : Nonempty intervalDomainPoint :=
    ⟨⟨0, by constructor <;> norm_num⟩⟩
  obtain ⟨x₀, _hx₀, hx₀_min⟩ :=
    isCompact_univ.exists_isMinOn
      (Set.univ_nonempty : (Set.univ : Set intervalDomainPoint).Nonempty)
      hu₀.admissible.2.continuousOn
  exact ⟨u₀ x₀, hu₀_pos x₀,
    fun x => isMinOn_iff.mp hx₀_min x (Set.mem_univ x)⟩

/-- For nonpositive sensitivity and `m ≥ 1`, every strictly positive
continuous interval datum generates a positive global bounded faithful orbit.
This is the exact orbit hypothesis consumed by eventual Theorems 2.1, 2.3,
2.4, and 2.5. -/
theorem
intervalDomainM_allPositiveContinuousData_globalBoundedExistence_chiNonpos
    (p : CM2Params)
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hchi : p.χ₀ ≤ 0) (hm : 1 ≤ p.m) :
    AllPositiveContinuousDataGlobalBoundedExistence intervalDomainM p := by
  intro u₀ hu₀ hu₀_pos
  have hu₀_paper : PaperPositiveInitialDatum intervalDomainM u₀ :=
    intervalDomainM_paperPositiveInitialDatum_of_positive_continuous
      hu₀ hu₀_pos
  obtain ⟨u, v, hglobal, htrace, hbounded⟩ :=
    globalSolution_chiNonpos_m_ge_one
      p hguard hchi hm u₀ hu₀_paper
  exact ⟨u, v,
    PositiveGlobalBoundedSolution.of_global_bounded hglobal hbounded,
    htrace⟩

/-- The legacy linear-flux headline `paper2_chiNonpos` also produces the
global carrier required by Paper 3.  At `m = 1`, its global solution is
transported to the faithful presentation only to invoke the explicit global
maximum bound; the boundedness predicate itself has the same supremum norm on
the two interval records. -/
theorem
intervalDomain_allPositiveContinuousData_globalBoundedExistence_chiNonpos_from_paper2
    (p : CM2Params) (hm : p.m = 1)
    (hchi : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (halpha : 1 ≤ p.α) (hgamma : 1 ≤ p.γ) :
    AllPositiveContinuousDataGlobalBoundedExistence intervalDomain p := by
  intro u₀ hu₀ hu₀_pos
  have hu₀M : PositiveInitialDatum intervalDomainM u₀ := by
    simpa [intervalDomainM, intervalDomain] using hu₀
  have hu₀_paperM : PaperPositiveInitialDatum intervalDomainM u₀ :=
    intervalDomainM_paperPositiveInitialDatum_of_positive_continuous
      hu₀M hu₀_pos
  have hu₀_paper : PaperPositiveInitialDatum intervalDomain u₀ := by
    simpa [intervalDomainM, intervalDomain] using hu₀_paperM
  have hm_ge : 1 ≤ p.m := by rw [hm]
  obtain ⟨_T, _hT, u, v, _hsol, htrace, _hbound, hglobal_of_m⟩ :=
    (ShenWork.Paper2.IntervalChiNegAssembly.paper2_chiNonpos
      p hchi ha hb halpha hgamma hchi).1 ha hb u₀ hu₀_paper
  have hglobal : IsPaper2GlobalClassicalSolution intervalDomain p u v :=
    hglobal_of_m hm_ge
  have hglobalM :
      IsPaper2GlobalClassicalSolution intervalDomainM p u v := by
    intro T hT
    exact ShenWork.Paper2.IntervalDomainM.classicalSolution_intervalDomainM_of_m_eq_one
      hm (hglobal.classical hT)
  have htraceM : InitialTrace intervalDomainM u₀ u := by
    simpa [intervalDomainM, intervalDomain] using htrace
  have hboundedM : IsPaper2Bounded intervalDomainM u :=
    critical_bounded_global_nonpos_m_ge_one
      (Or.inr hb) hchi hm_ge hu₀M hglobalM htraceM
  have hbounded : IsPaper2Bounded intervalDomain u := by
    simpa [intervalDomainM, intervalDomain] using hboundedM
  exact ⟨u, v,
    PositiveGlobalBoundedSolution.of_global_bounded hglobal hbounded,
    htrace⟩

/-- Positive-logistic branch of faithful eventual Theorem 2.3, realized from
an arbitrary strictly positive continuous datum rather than merely a small
perturbation of equilibrium. -/
theorem intervalDomainM_Theorem_2_3_positiveEventual_allData
    (p : CM2Params) (hchi : p.χ₀ ≤ 0) (hm : 1 ≤ p.m) :
    ∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      ∀ u₀ : intervalDomainPoint → ℝ,
        PositiveInitialDatum intervalDomainM u₀ →
        (∀ x, 0 < u₀ x) →
          ∃ u v : ℝ → intervalDomainPoint → ℝ,
            InitialTrace intervalDomainM u₀ u ∧
            PositiveGlobalBoundedSolution intervalDomainM p u v ∧
            UniformConvergesInSup intervalDomainM u eq.1 ∧
            ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
              EventualExponentialC1ConvergenceWith
                intervalDomainM intervalDomainMSectorialStabilityNorms
                  u v eq.1 eq.2 C rate t₀ := by
  intro ha hb
  dsimp
  intro u₀ hu₀ hu₀_pos
  obtain ⟨u, v, huv, htrace⟩ :=
    intervalDomainM_allPositiveContinuousData_globalBoundedExistence_chiNonpos
      p (Or.inr hb) hchi hm u₀ hu₀ hu₀_pos
  have hstability :=
    intervalDomainM_Theorem_2_3_positiveEventual p hchi ha hb
  exact ⟨u, v, htrace, huv,
    hstability.1 u v huv,
    hstability.2 u v huv⟩

/-- Minimal branch of faithful eventual Theorem 2.3, realized from every
strictly positive continuous datum on the physical mass hyperplane. -/
theorem intervalDomainM_Theorem_2_3_minimalEventual_allData
    (p : CM2Params) (hchi : p.χ₀ ≤ 0) (hm : 1 ≤ p.m) :
    ∀ (_ha0 : p.a = 0) (_hb0 : p.b = 0),
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        ∀ u₀ : intervalDomainPoint → ℝ,
          PositiveInitialDatum intervalDomainM u₀ →
          (∀ x, 0 < u₀ x) →
          intervalDomainM.integral u₀ = intervalDomainM.volume * uStar →
            ∃ u v : ℝ → intervalDomainPoint → ℝ,
              InitialTrace intervalDomainM u₀ u ∧
              PositiveGlobalBoundedSolution intervalDomainM p u v ∧
              HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar ∧
              UniformConvergesInSup intervalDomainM u eq.1 ∧
              ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
                EventualExponentialC1ConvergenceWith
                  intervalDomainM intervalDomainMSectorialStabilityNorms
                    u v eq.1 eq.2 C rate t₀ := by
  intro ha0 hb0 uStar huStar
  dsimp
  intro u₀ hu₀ hu₀_pos hmass₀
  obtain ⟨u, v, huv, htrace⟩ :=
    intervalDomainM_allPositiveContinuousData_globalBoundedExistence_chiNonpos
      p (Or.inl ha0) hchi hm u₀ hu₀ hu₀_pos
  have hmass :
      HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar :=
    intervalDomainM_minimal_hasEquilibriumMassOnPositiveTimes_of_trace
      p ha0 hb0 hu₀ huv.1 htrace hmass₀
  have hstability :=
    intervalDomainM_Theorem_2_3_minimalEventual
      p hchi ha0 hb0 uStar huStar
  exact ⟨u, v, htrace, huv, hmass,
    hstability.1 u v huv hmass,
    hstability.2 u v huv hmass⟩

/-- All-data, non-vacuous faithful Theorem 2.3.  The first conjunct is the
positive-logistic branch; the second is the minimal physical-mass branch. -/
theorem intervalDomainM_Theorem_2_3_EventualGlobalStability_allData
    (p : CM2Params) (hchi : p.χ₀ ≤ 0) (hm : 1 ≤ p.m) :
    (∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      ∀ u₀ : intervalDomainPoint → ℝ,
        PositiveInitialDatum intervalDomainM u₀ →
        (∀ x, 0 < u₀ x) →
          ∃ u v : ℝ → intervalDomainPoint → ℝ,
            InitialTrace intervalDomainM u₀ u ∧
            PositiveGlobalBoundedSolution intervalDomainM p u v ∧
            UniformConvergesInSup intervalDomainM u eq.1 ∧
            ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
              EventualExponentialC1ConvergenceWith
                intervalDomainM intervalDomainMSectorialStabilityNorms
                  u v eq.1 eq.2 C rate t₀) ∧
    (∀ (_ha0 : p.a = 0) (_hb0 : p.b = 0),
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        ∀ u₀ : intervalDomainPoint → ℝ,
          PositiveInitialDatum intervalDomainM u₀ →
          (∀ x, 0 < u₀ x) →
          intervalDomainM.integral u₀ = intervalDomainM.volume * uStar →
            ∃ u v : ℝ → intervalDomainPoint → ℝ,
              InitialTrace intervalDomainM u₀ u ∧
              PositiveGlobalBoundedSolution intervalDomainM p u v ∧
              HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar ∧
              UniformConvergesInSup intervalDomainM u eq.1 ∧
              ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
                EventualExponentialC1ConvergenceWith
                  intervalDomainM intervalDomainMSectorialStabilityNorms
                    u v eq.1 eq.2 C rate t₀) := by
  exact ⟨
    intervalDomainM_Theorem_2_3_positiveEventual_allData p hchi hm,
    intervalDomainM_Theorem_2_3_minimalEventual_allData p hchi hm⟩

/-- On the positive-sensitivity branch, Paper 2's corrected strong-logistic
condition likewise gives an all-data positive global bounded carrier. -/
theorem
intervalDomainM_allPositiveContinuousData_globalBoundedExistence_of_correctedStrongLogistic
    (p : CM2Params) (hN : p.N = 1)
    (hb : 0 < p.b) (hm : 1 ≤ p.m) (hchi : 0 < p.χ₀)
    (hstrong : CorrectedStrongLogisticCondition p) :
    AllPositiveContinuousDataGlobalBoundedExistence intervalDomainM p := by
  intro u₀ hu₀ hu₀_pos
  have hu₀_paper : PaperPositiveInitialDatum intervalDomainM u₀ :=
    intervalDomainM_paperPositiveInitialDatum_of_positive_continuous
      hu₀ hu₀_pos
  obtain ⟨u, v, hglobal, htrace⟩ :=
    globalSolution_of_correctedStrongLogistic_positive_chi
      hN hb hm hchi hstrong u₀ hu₀_paper
  have hbounded : IsPaper2Bounded intervalDomainM u :=
    boundedGlobal_of_correctedStrongLogistic_positive_chi
      hN hb hu₀ hglobal htrace hchi hstrong
  exact ⟨u, v,
    PositiveGlobalBoundedSolution.of_global_bounded hglobal hbounded,
    htrace⟩

/-- The exact Paper 2 minimal-honest-residual package mentioned in the
all-data closure likewise discharges the faithful all-data orbit hypothesis.
Its conclusion already contains both the global solution and the global
boundedness proof. -/
theorem
intervalDomainM_allPositiveContinuousData_globalBoundedExistence_from_minimalHonestResidual
    (p : CM2Params) (C : Paper2Constants p)
    (hN : p.N = 1) (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m) (hchi : 0 < p.χ₀)
    (hres : IntervalDomainTheorem13MinimalHonestResidual p C)
    (hstrong : StrongLogisticCondition p C) :
    AllPositiveContinuousDataGlobalBoundedExistence intervalDomainM p := by
  intro u₀ hu₀ hu₀_pos
  have hu₀_paper : PaperPositiveInitialDatum intervalDomainM u₀ :=
    intervalDomainM_paperPositiveInitialDatum_of_positive_continuous
      hu₀ hu₀_pos
  have hheadline : Theorem_1_3 intervalDomainM p C :=
    Theorem_1_3_intervalDomainM_from_minimal_honest_residual
      p C hN hchi hres
  obtain ⟨u, v, hglobal, htrace, hbounded⟩ :=
    (hheadline ha hb p.hm hstrong).2 hm u₀ hu₀_paper
  exact ⟨u, v,
    PositiveGlobalBoundedSolution.of_global_bounded hglobal hbounded,
    htrace⟩

/-- All-data realization of eventual Theorem 2.4 on the parameter
intersection where Paper 2 proves global existence.  The additional
`CorrectedStrongLogisticCondition` is an existence condition, not a stability
condition: the four Paper 3 threshold branches do not in general imply it. -/
theorem
intervalDomainM_Theorem_2_4_EventualGlobalStability_allData_of_correctedStrongLogistic
    (p : CM2Params) (hN : p.N = 1)
    (ha : 0 < p.a) (hb : 0 < p.b) (hm : 1 ≤ p.m)
    (hchi : 0 < p.χ₀)
    (hstrong : CorrectedStrongLogisticCondition p)
    (hcondition :
      NonminimalGlobalStabilityFormulaCondition p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2
        (unitIntervalNormalizedResolverGradientConstant p)) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomainM u₀ →
      (∀ x, 0 < u₀ x) →
        ∃ u v : ℝ → intervalDomainPoint → ℝ,
          InitialTrace intervalDomainM u₀ u ∧
          PositiveGlobalBoundedSolution intervalDomainM p u v ∧
          UniformConvergesInSup intervalDomainM u
            (positiveEquilibrium p ⟨ha, hb⟩).1 ∧
          ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
            EventualExponentialC1ConvergenceWith
              intervalDomainM intervalDomainMSectorialStabilityNorms u v
                (positiveEquilibrium p ⟨ha, hb⟩).1
                (positiveEquilibrium p ⟨ha, hb⟩).2 C rate t₀ := by
  intro u₀ hu₀ hu₀_pos
  obtain ⟨u, v, huv, htrace⟩ :=
    intervalDomainM_allPositiveContinuousData_globalBoundedExistence_of_correctedStrongLogistic
      p hN hb hm hchi hstrong u₀ hu₀ hu₀_pos
  have hstability :
      EventuallyGloballyExponentiallyStableNonminimal intervalDomainM p
        intervalDomainMSectorialStabilityNorms
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2 :=
    intervalDomainM_Theorem_2_4_EventualGlobalStabilityFormula p
      ha hb p.hβ p.hα p.hγ ha hb hcondition
  exact ⟨u, v, htrace, huv,
    hstability.1 u v huv,
    hstability.2 u v huv⟩

#print axioms
  intervalDomainM_paperPositiveInitialDatum_of_positive_continuous
#print axioms
  intervalDomainM_allPositiveContinuousData_globalBoundedExistence_chiNonpos
#print axioms
  intervalDomain_allPositiveContinuousData_globalBoundedExistence_chiNonpos_from_paper2
#print axioms intervalDomainM_Theorem_2_3_positiveEventual_allData
#print axioms intervalDomainM_Theorem_2_3_minimalEventual_allData
#print axioms
  intervalDomainM_Theorem_2_3_EventualGlobalStability_allData
#print axioms
  intervalDomainM_allPositiveContinuousData_globalBoundedExistence_of_correctedStrongLogistic
#print axioms
  intervalDomainM_allPositiveContinuousData_globalBoundedExistence_from_minimalHonestResidual
#print axioms
  intervalDomainM_Theorem_2_4_EventualGlobalStability_allData_of_correctedStrongLogistic

end

end ShenWork.Paper3
