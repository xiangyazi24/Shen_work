import ShenWork.Paper2.IntervalDomainChiZeroUnconditionalLocalExistence
import ShenWork.Paper2.IntervalDomainThm11Assembly

open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2

/-- χ₀ = 0 supplies the uniform restart-before-end local existence hypothesis. -/
theorem intervalDomain_uniformLocalExistence_chiZero_unconditional
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ) :
    IntervalDomainUniformLocalExistence p := by
  intro M hM
  set M' := SupNormBridge.regimeBound p M
  have hM' : 0 < M' := SupNormBridge.regimeBound_pos p hM
  obtain ⟨δ, hδ, hex⟩ :=
    Thm11ChiZeroCoreProvider.quantitativeLocalExistence_chiZero_datum
      p hχ0 ha hb hα
      (chiZeroDatumProviderSupply p hχ0 ha hb hα) M' hM'
  have hRestart : RestartExtension.RestartAndGlueWorks p :=
    GlueExtension.restartAndGlueWorks_of_hypotheses p
      TimeShift.regularityTimeShiftWorks
      (GlueExtension.overlapUniqueForPID_of_l2EnergyMethod
        (intervalDomainClassicalUniquenessL2EnergyMethod_of_boundedDatumUniform p
          (intervalDomainL2UBoundedDatumUniform_of_bounded
            (boundednessHypothesis_of_uniformSupBoundZeroM hγ
              (uniformLiftBoundZeroM_of_regime p (le_of_eq hχ0) ha hb)))))
      GlueExtension.timeShiftInitialTraceWorks
      (PiecewiseClassical.piecewiseClassicalWorks p)
  refine ⟨δ / 2, by linarith, ?_⟩
  intro u₀ hu₀ hbound T₀ hT₀ u v hsol htrace
  have hSupBound : ∀ t, 0 < t → t < T₀ → ∀ x : intervalDomainPoint,
      |u t x| ≤ M' :=
    SupNormBridge.interiorSupNorm_le_regimeBound
      p (le_of_eq hχ0) ha hb hu₀ hM hbound hT₀ hsol htrace
  have hbound' : ∀ x, |u₀ x| ≤ M' := fun x =>
    le_trans (hbound x) (SupNormBridge.regimeBound_ge_M p M)
  have hfactory : ∀ {w : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain w → (∀ x, |w x| ≤ M') →
        ∃ uw vw, IsPaper2ClassicalSolution intervalDomain p δ uw vw ∧
          InitialTrace intervalDomain w uw := fun hw hbw => hex hw hbw
  exact hRestart hM' hδ hfactory hu₀ hbound' hT₀ hsol htrace hSupBound

/-- Paper 2 Theorem 1.1 on the interval domain, unconditionally for χ₀ = 0. -/
theorem intervalDomain_theorem_1_1_chiZero_unconditional
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ) :
    Theorem_1_1 intervalDomain p :=
  Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hextend_mge
    p (le_of_eq hχ0) ha hb hγ
    (RestartLocalWiring.localExistence_of_gradientMildHalfStepRestartFrontierCoreLocalData
      p
      (Thm11ChiZeroCoreProvider.hMildLocal_chi0_zero_of_datum
        p hχ0 ha hb hα (chiZeroDatumProviderSupply p hχ0 ha hb hα)))
    (intervalDomain_uniformLocalExistence_chiZero_unconditional
      p hχ0 ha hb hα hγ)

#print axioms intervalDomain_theorem_1_1_chiZero_unconditional

end ShenWork.Paper2
