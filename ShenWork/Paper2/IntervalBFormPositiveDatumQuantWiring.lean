import ShenWork.Paper2.IntervalBFormPositiveDatumLocalExistence
import ShenWork.Paper2.IntervalBFormPositiveDatumLocalExistenceSq
import ShenWork.Paper2.IntervalDomainFinalWiring

open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumLocal

/-- Uniform local existence from the quantitative local factory in the
`χ₀ ≤ 0`, `γ ≥ 1` regime.

This is the same restart-and-glue construction used in `FinalWiring`, exposed
as a reusable input for the B-form route. -/
theorem uniformLocalExistence_of_quantitative_regime
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hQuant : ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u) :
    IntervalDomainUniformLocalExistence p := by
  intro M hM
  set M' := SupNormBridge.regimeBound p M
  have hM' : 0 < M' := SupNormBridge.regimeBound_pos p hM
  obtain ⟨δ, hδ, hex⟩ := hQuant M' hM'
  have hRestart : RestartExtension.RestartAndGlueWorks p :=
    GlueExtension.restartAndGlueWorks_of_hypotheses p
      TimeShift.regularityTimeShiftWorks
      (GlueExtension.overlapUniqueForPID_of_l2EnergyMethod
        (intervalDomainClassicalUniquenessL2EnergyMethod_of_boundedDatumUniform p
          (intervalDomainL2UBoundedDatumUniform_of_bounded
            (boundednessHypothesis_of_uniformSupBoundZeroM hγ_ge_one
              (uniformLiftBoundZeroM_of_regime p hχ ha hb)))))
      GlueExtension.timeShiftInitialTraceWorks
      (PiecewiseClassical.piecewiseClassicalWorks p)
  refine ⟨δ / 2, by linarith, ?_⟩
  intro u₀ hu₀ hbound T₀ hT₀ u v hsol htrace
  have hSupBound : ∀ t, 0 < t → t < T₀ → ∀ x : intervalDomainPoint,
      |u t x| ≤ M' :=
    SupNormBridge.interiorSupNorm_le_regimeBound
      p hχ ha hb hu₀ hM hbound hT₀ hsol htrace
  have hbound' : ∀ x, |u₀ x| ≤ M' := fun x =>
    le_trans (hbound x) (SupNormBridge.regimeBound_ge_M p M)
  have hfactory : ∀ {w : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain w → (∀ x, |w x| ≤ M') →
        ∃ uw vw, IsPaper2ClassicalSolution intervalDomain p δ uw vw ∧
          InitialTrace intervalDomain w uw := fun hw hbw => hex hw hbw
  exact hRestart hM' hδ hfactory hu₀ hbound' hT₀ hsol htrace hSupBound

/-- General-χ B-form headline with the uniform-local-existence input replaced
by the quantitative local factory used by the restart/glue continuation route. -/
theorem paper2_theorem_1_1_general_chi_bform_from_quant
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hBForm : PositiveDatumBFormLocalHyp p)
    (hQuant : ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bform p hχ ha hb hγ_ge_one hBForm
    (uniformLocalExistence_of_quantitative_regime
      p hχ ha hb hγ_ge_one hQuant)

section AxiomAudit

#print axioms uniformLocalExistence_of_quantitative_regime
#print axioms paper2_theorem_1_1_general_chi_bform_from_quant

end AxiomAudit

end ShenWork.Paper2.BFormPositiveDatumLocal

namespace ShenWork.Paper2.BFormPositiveDatumLocalSq

/-- Squared-barrier B-form headline with the uniform-local-existence input
replaced by the quantitative local factory used by the restart/glue route. -/
theorem paper2_theorem_1_1_general_chi_bformSq_from_quant
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hBForm : PositiveDatumBFormLocalHypSq p)
    (hQuant : ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bformSq p hχ ha hb hγ_ge_one hBForm
    (ShenWork.Paper2.BFormPositiveDatumLocal.uniformLocalExistence_of_quantitative_regime
      p hχ ha hb hγ_ge_one hQuant)

section AxiomAudit

#print axioms paper2_theorem_1_1_general_chi_bformSq_from_quant

end AxiomAudit

end ShenWork.Paper2.BFormPositiveDatumLocalSq
