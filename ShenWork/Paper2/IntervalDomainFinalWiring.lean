/-
  Final wiring: Paper 2 Theorem 1.1 from regime + 3 hypotheses.
  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainTheorem11Umbrella
import ShenWork.Paper2.IntervalDomainPiecewiseGlue
import ShenWork.Paper2.IntervalDomainGlueExtension
import ShenWork.Paper2.IntervalDomainTimeShift
import ShenWork.Paper2.IntervalDomainSupNormBridge
import ShenWork.Paper2.IntervalDomainRestartExtension

open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.FinalWiring

/-- **Paper 2 Theorem 1.1 from regime + 3 hypotheses.** -/
theorem paper2_theorem_1_1_from_three
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hQuant : ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u)
    (hPCW : PiecewiseGlue.PiecewiseClassicalWorks p)
    (hMildLocal :
      IntervalDomainGradientMildHalfStepLogisticSourceFrontierCoreLocalData p) :
    Theorem_1_1 intervalDomain p := by
  apply Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hextend_mge
    p hχ ha hb hγ_ge_one
  · exact localExistence_of_gradientMildHalfStepLogisticSourceFrontierCoreLocalData
      p hMildLocal
  · -- IntervalDomainUniformLocalExistence
    intro M hM
    -- Use M' = regimeBound p M for the quantitative estimate + sup-norm bound
    set M' := SupNormBridge.regimeBound p M
    have hM' := SupNormBridge.regimeBound_pos p hM
    obtain ⟨δ, hδ, hex⟩ := hQuant M' hM'
    -- Build RestartAndGlueWorks
    have hRestart : RestartExtension.RestartAndGlueWorks p :=
      GlueExtension.restartAndGlueWorks_of_hypotheses p
        TimeShift.regularityTimeShiftWorks
        (GlueExtension.overlapUniqueForPID_of_l2EnergyMethod
          (intervalDomainClassicalUniquenessL2EnergyMethod_of_boundedDatumUniform p
            (intervalDomainL2UBoundedDatumUniform_of_bounded
              (boundednessHypothesis_of_uniformSupBoundZeroM hγ_ge_one
                (uniformLiftBoundZeroM_of_regime p hχ ha hb)))))
        GlueExtension.timeShiftInitialTraceWorks
        hPCW
    refine ⟨δ / 2, by linarith, ?_⟩
    intro u₀ hu₀ hbound T₀ hT₀ u v hsol htrace
    -- Sup-norm bound by M' at interior times
    have hSupBound : ∀ t, 0 < t → t < T₀ → ∀ x : intervalDomainPoint, |u t x| ≤ M' :=
      SupNormBridge.interiorSupNorm_le_regimeBound p hχ ha hb hu₀ hM hbound hT₀ hsol htrace
    -- u₀ bounded by M'
    have hbound' : ∀ x, |u₀ x| ≤ M' := fun x =>
      le_trans (hbound x) (SupNormBridge.regimeBound_ge_M p M)
    -- Factory at M'
    have hfactory : ∀ {w : intervalDomainPoint → ℝ},
        PositiveInitialDatum intervalDomain w → (∀ x, |w x| ≤ M') →
        ∃ uw vw, IsPaper2ClassicalSolution intervalDomain p δ uw vw ∧
          InitialTrace intervalDomain w uw := fun hw hbw => hex hw hbw
    -- Apply RestartAndGlueWorks
    exact hRestart hM' hδ hfactory hu₀ hbound' hT₀ hsol htrace hSupBound

end ShenWork.Paper2.FinalWiring
