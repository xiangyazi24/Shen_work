import ShenWork.Paper2.IntervalBFormPositiveDatumLocalExistence
import ShenWork.Paper2.IntervalBFormPositiveDatumNegPartFrontier
import ShenWork.Paper2.IntervalBFormPositiveDatumLocalExistenceSq
import ShenWork.Paper2.IntervalBFormPositiveDatumLocalExistenceSqBanked
import ShenWork.Paper2.IntervalBFormPositiveDatumLocalExistenceSqBankedConcrete
import ShenWork.Paper2.IntervalBFormPositiveDatumLocalExistenceSqRegular
import ShenWork.Paper2.IntervalBFormPositiveDatumLocalExistenceSqDeepest
import ShenWork.Paper2.IntervalDomainConeQuantBridge
import ShenWork.Paper2.IntervalDomainFinalWiring
import ShenWork.Paper2.IntervalDomainMinPersistFinal
import ShenWork.Paper2.IntervalDomainThresholdQuantBridge

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

/-- Uniform local existence from the proved threshold/Picard-restart
production of the quantitative local factory. -/
theorem uniformLocalExistence_of_picardFrontier_persistence
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hPersist : QuantFromThreshold.ClassicalMinPersistence p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    IntervalDomainUniformLocalExistence p :=
  uniformLocalExistence_of_quantitative_regime p hχ ha hb hγ_ge_one
    (ThresholdQuantBridge.quantitativeLocalExistence_of_picardFrontier_persistence
      p hχ ha hb hα_ge hγ_ge_one hPF hPersist hlocal)

/-- Uniform local existence from the Picard-restart route, with the per-datum
`hlocal` seed supplied by the positive-datum B-form package. -/
theorem uniformLocalExistence_of_picardFrontier_persistence_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hPersist : QuantFromThreshold.ClassicalMinPersistence p)
    (hBForm : PositiveDatumBFormLocalHyp p) :
    IntervalDomainUniformLocalExistence p :=
  uniformLocalExistence_of_picardFrontier_persistence
    p hχ ha hb hα_ge hγ_ge_one hPF hPersist
    (positiveDatum_localExistence_of_BForm hBForm)

/-- Uniform local existence from the unified Picard-limit restart frontier,
with the per-datum `hlocal` seed supplied by the positive-datum B-form package. -/
theorem uniformLocalExistence_of_picardLimitFrontier_persistence_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hPersist : QuantFromThreshold.ClassicalMinPersistence p)
    (hBForm : PositiveDatumBFormLocalHyp p) :
    IntervalDomainUniformLocalExistence p :=
  uniformLocalExistence_of_picardFrontier_persistence_of_BForm
    p hχ ha hb hα_ge hγ_ge_one
    (ConeQuantBridge.picardRestartFrontier_of_picardLimitFrontier hPLF)
    hPersist hBForm

/-- Boundary min-point derivative residual used to produce
`ClassicalMinPersistence` in the general-`χ₀ ≤ 0` regime. -/
def BoundaryMinPersistenceBound (p : CM2Params) : Prop :=
  ∀ {u₀ : intervalDomainPoint → ℝ},
    PositiveInitialDatum intervalDomain u₀ →
    ∀ {M : ℝ}, 0 < M → (∀ x, |u₀ x| ≤ M) →
    ∀ {t₁ T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
      ∀ s ∈ Set.Ico (t₁ / 2) T, ∀ ys ∈ Set.Icc (0 : ℝ) 1, ys = 0 ∨ ys = 1 →
        intervalDomainLift (u s) ys =
          sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) →
        -(|p.χ₀| * ShenWork.MinPersistenceAtoms.fluxCoeffConst p.β
              (p.ν * (SupNormBridge.regimeBound p M) ^ p.γ)
            + p.b * (SupNormBridge.regimeBound p M) ^ p.α)
            * sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) ≤
          deriv (fun r => intervalDomainLift (u r) ys) s

/-- Windowed boundary min-point derivative residual.  This is the same
boundary input as `BoundaryMinPersistenceBound`, but with the positivity of
the lower threshold time exposed at the call site. -/
def BoundaryMinPersistenceWindowBound (p : CM2Params) : Prop :=
  ∀ {u₀ : intervalDomainPoint → ℝ},
    PositiveInitialDatum intervalDomain u₀ →
    ∀ {M : ℝ}, 0 < M → (∀ x, |u₀ x| ≤ M) →
    ∀ {t₁ T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}, 0 < t₁ →
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
      ∀ s ∈ Set.Ico (t₁ / 2) T, ∀ ys ∈ Set.Icc (0 : ℝ) 1, ys = 0 ∨ ys = 1 →
        intervalDomainLift (u s) ys =
          sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) →
        -(|p.χ₀| * ShenWork.MinPersistenceAtoms.fluxCoeffConst p.β
              (p.ν * (SupNormBridge.regimeBound p M) ^ p.γ)
            + p.b * (SupNormBridge.regimeBound p M) ^ p.α)
            * sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) ≤
          deriv (fun r => intervalDomainLift (u r) ys) s

/-- The legacy boundary residual implies the windowed boundary residual. -/
theorem boundaryMinPersistenceWindowBound_of_boundary
    {p : CM2Params} (hbdry : BoundaryMinPersistenceBound p) :
    BoundaryMinPersistenceWindowBound p := by
  intro u₀ hu₀ M hM hbnd t₁ T u v _ht₁ hsol htr s hs ys hys hys01 harg
  exact hbdry hu₀ hM hbnd hsol htr s hs ys hys hys01 harg

/-- Classical minimum persistence from the boundary min-point bound, with the
regime overlap uniqueness supplied by the existing L² energy method. -/
theorem classicalMinPersistence_of_boundary_regime
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hbdry : BoundaryMinPersistenceBound p) :
    QuantFromThreshold.ClassicalMinPersistence p := by
  have hOverlap : GlueExtension.OverlapUniqueForPID p :=
    GlueExtension.overlapUniqueForPID_of_l2EnergyMethod
      (intervalDomainClassicalUniquenessL2EnergyMethod_of_boundedDatumUniform p
        (intervalDomainL2UBoundedDatumUniform_of_bounded
          (boundednessHypothesis_of_uniformSupBoundZeroM hγ_ge_one
            (uniformLiftBoundZeroM_of_regime p hχ ha hb))))
  exact ShenWork.MinPersistenceAtoms.classicalMinPersistence_of_boundary
    p hχ ha hb hOverlap hbdry

/-- Classical minimum persistence from the windowed boundary min-point bound.
This keeps the `0 < t₁` fact visible to endpoint boundary arguments. -/
theorem classicalMinPersistence_of_boundary_window_regime
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hbdry : BoundaryMinPersistenceWindowBound p) :
    QuantFromThreshold.ClassicalMinPersistence p := by
  have hOverlap : GlueExtension.OverlapUniqueForPID p :=
    GlueExtension.overlapUniqueForPID_of_l2EnergyMethod
      (intervalDomainClassicalUniquenessL2EnergyMethod_of_boundedDatumUniform p
        (intervalDomainL2UBoundedDatumUniform_of_bounded
          (boundednessHypothesis_of_uniformSupBoundZeroM hγ_ge_one
            (uniformLiftBoundZeroM_of_regime p hχ ha hb))))
  intro u₀ hu₀ δ t₁ ht₁ ht₁δ
  obtain ⟨M, hM, hbnd⟩ := ShenWork.MinPersistenceAtoms.pid_exists_bound hu₀
  refine ShenWork.MinPersistenceAtoms.minPersist_existsC_uniform hχ hu₀ ht₁ ht₁δ
    (SupNormBridge.regimeBound_pos p hM).le hOverlap
    (fun hsol htr =>
      ShenWork.MinPersistenceAtoms.hSupNorm_of_regime
        p hχ ha hb hu₀ hM hbnd ht₁ hsol.T_pos hsol htr)
    ?_
  intro T u v hsol htr s hs ys hys hys01 harg
  exact hbdry hu₀ hM hbnd ht₁ hsol htr s hs ys hys hys01 harg

/-- Quantitative local existence from the Picard-restart route and boundary
min-point persistence, retaining the per-datum local seed as a source input. -/
theorem quantitativeLocalExistence_of_picardFrontier_boundary
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hbdry : BoundaryMinPersistenceBound p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u :=
  ThresholdQuantBridge.quantitativeLocalExistence_of_picardFrontier_persistence
    p hχ ha hb hα_ge hγ_ge_one hPF
    (classicalMinPersistence_of_boundary_regime p hχ ha hb hγ_ge_one hbdry)
    hlocal

/-- Quantitative local existence from the unified Picard-limit restart frontier
and boundary min-point persistence, retaining the per-datum local seed as a
source input. -/
theorem quantitativeLocalExistence_of_picardLimitFrontier_boundary
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hbdry : BoundaryMinPersistenceBound p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u :=
  quantitativeLocalExistence_of_picardFrontier_boundary
    p hχ ha hb hα_ge hγ_ge_one
    (ConeQuantBridge.picardRestartFrontier_of_picardLimitFrontier hPLF)
    hbdry hlocal

/-- Quantitative local existence from the Picard-restart route and the
windowed boundary min-point persistence input. -/
theorem quantitativeLocalExistence_of_picardFrontier_boundary_window
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hbdry : BoundaryMinPersistenceWindowBound p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u :=
  ThresholdQuantBridge.quantitativeLocalExistence_of_picardFrontier_persistence
    p hχ ha hb hα_ge hγ_ge_one hPF
    (classicalMinPersistence_of_boundary_window_regime
      p hχ ha hb hγ_ge_one hbdry)
    hlocal

/-- Quantitative local existence from the unified Picard-limit restart
frontier and the windowed boundary min-point persistence input. -/
theorem quantitativeLocalExistence_of_picardLimitFrontier_boundary_window
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hbdry : BoundaryMinPersistenceWindowBound p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u :=
  quantitativeLocalExistence_of_picardFrontier_boundary_window
    p hχ ha hb hα_ge hγ_ge_one
    (ConeQuantBridge.picardRestartFrontier_of_picardLimitFrontier hPLF)
    hbdry hlocal

/-- Uniform local existence from the Picard-restart route and the boundary
min-point form of the persistence input. -/
theorem uniformLocalExistence_of_picardFrontier_boundary
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hbdry : BoundaryMinPersistenceBound p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    IntervalDomainUniformLocalExistence p :=
  uniformLocalExistence_of_picardFrontier_persistence
    p hχ ha hb hα_ge hγ_ge_one hPF
    (classicalMinPersistence_of_boundary_regime p hχ ha hb hγ_ge_one hbdry)
    hlocal

/-- Uniform local existence from the Picard-restart route and boundary
min-point persistence, with `hlocal` supplied by the positive-datum B-form
package. -/
theorem uniformLocalExistence_of_picardFrontier_boundary_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hbdry : BoundaryMinPersistenceBound p)
    (hBForm : PositiveDatumBFormLocalHyp p) :
    IntervalDomainUniformLocalExistence p :=
  uniformLocalExistence_of_picardFrontier_boundary
    p hχ ha hb hα_ge hγ_ge_one hPF hbdry
    (positiveDatum_localExistence_of_BForm hBForm)

/-- Uniform local existence from the unified Picard-limit restart frontier and
boundary min-point persistence, with `hlocal` supplied by the positive-datum
B-form package. -/
theorem uniformLocalExistence_of_picardLimitFrontier_boundary_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hbdry : BoundaryMinPersistenceBound p)
    (hBForm : PositiveDatumBFormLocalHyp p) :
    IntervalDomainUniformLocalExistence p :=
  uniformLocalExistence_of_picardFrontier_boundary_of_BForm
    p hχ ha hb hα_ge hγ_ge_one
    (ConeQuantBridge.picardRestartFrontier_of_picardLimitFrontier hPLF)
    hbdry hBForm

/-- Quantitative local existence from the Picard-restart route, with the
per-datum local seed supplied by the positive-datum B-form package. -/
theorem quantitativeLocalExistence_of_picardFrontier_persistence_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hPersist : QuantFromThreshold.ClassicalMinPersistence p)
    (hBForm : PositiveDatumBFormLocalHyp p) :
    ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u :=
  ThresholdQuantBridge.quantitativeLocalExistence_of_picardFrontier_persistence
    p hχ ha hb hα_ge hγ_ge_one hPF hPersist
    (positiveDatum_localExistence_of_BForm hBForm)

/-- Quantitative local existence from the unified Picard-limit restart frontier,
with the per-datum local seed supplied by the positive-datum B-form package. -/
theorem quantitativeLocalExistence_of_picardLimitFrontier_persistence_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hPersist : QuantFromThreshold.ClassicalMinPersistence p)
    (hBForm : PositiveDatumBFormLocalHyp p) :
    ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u :=
  quantitativeLocalExistence_of_picardFrontier_persistence_of_BForm
    p hχ ha hb hα_ge hγ_ge_one
    (ConeQuantBridge.picardRestartFrontier_of_picardLimitFrontier hPLF)
    hPersist hBForm

/-- Quantitative local existence from the Picard-restart route and the boundary
min-point persistence residual, with the per-datum local seed supplied by the
positive-datum B-form package. -/
theorem quantitativeLocalExistence_of_picardFrontier_boundary_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hbdry : BoundaryMinPersistenceBound p)
    (hBForm : PositiveDatumBFormLocalHyp p) :
    ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u :=
  quantitativeLocalExistence_of_picardFrontier_boundary
    p hχ ha hb hα_ge hγ_ge_one hPF hbdry
    (positiveDatum_localExistence_of_BForm hBForm)

/-- Quantitative local existence from the unified Picard-limit restart frontier
and the boundary min-point persistence residual, with the per-datum local seed
supplied by the positive-datum B-form package. -/
theorem quantitativeLocalExistence_of_picardLimitFrontier_boundary_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hbdry : BoundaryMinPersistenceBound p)
    (hBForm : PositiveDatumBFormLocalHyp p) :
    ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u :=
  quantitativeLocalExistence_of_picardLimitFrontier_boundary
    p hχ ha hb hα_ge hγ_ge_one hPLF hbdry
    (positiveDatum_localExistence_of_BForm hBForm)

/-- Quantitative local existence from the Picard-restart route and the windowed
boundary min-point persistence input, with the per-datum local seed supplied by
the positive-datum B-form package. -/
theorem quantitativeLocalExistence_of_picardFrontier_boundary_window_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hbdry : BoundaryMinPersistenceWindowBound p)
    (hBForm : PositiveDatumBFormLocalHyp p) :
    ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u :=
  quantitativeLocalExistence_of_picardFrontier_boundary_window
    p hχ ha hb hα_ge hγ_ge_one hPF hbdry
    (positiveDatum_localExistence_of_BForm hBForm)

/-- Quantitative local existence from the unified Picard-limit restart frontier
and the windowed boundary min-point persistence input, with the per-datum local
seed supplied by the positive-datum B-form package. -/
theorem quantitativeLocalExistence_of_picardLimitFrontier_boundary_window_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hbdry : BoundaryMinPersistenceWindowBound p)
    (hBForm : PositiveDatumBFormLocalHyp p) :
    ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u :=
  quantitativeLocalExistence_of_picardLimitFrontier_boundary_window
    p hχ ha hb hα_ge hγ_ge_one hPLF hbdry
    (positiveDatum_localExistence_of_BForm hBForm)

/-- General-χ headline from the source-side hQuant package:
B-form local seed, Picard-limit restart frontier, and boundary persistence. -/
theorem paper2_theorem_1_1_general_chi_from_picardLimitFrontier_boundary_of_BForm_hQuant
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hbdry : BoundaryMinPersistenceBound p)
    (hBForm : PositiveDatumBFormLocalHyp p) :
    Theorem_1_1 intervalDomain p :=
  FinalWiring.paper2_theorem_1_1_from_quant p hχ ha hb hγ_ge_one
    (quantitativeLocalExistence_of_picardLimitFrontier_boundary_of_BForm
      p hχ ha hb hα_ge hγ_ge_one hPLF hbdry hBForm)

/-- General-χ B-form headline with the uniform-local-existence input replaced
by the quantitative local factory used by the restart/glue continuation route. -/
theorem paper2_theorem_1_1_general_chi_bform_from_quant
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (_hBForm : PositiveDatumBFormLocalHyp p)
    (hQuant : ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  FinalWiring.paper2_theorem_1_1_from_quant
    p hχ ha hb hγ_ge_one hQuant

/-- General-χ B-form headline with the uniform-local-existence input replaced
by the Picard-restart/min-persistence local-existence route. -/
theorem paper2_theorem_1_1_general_chi_bform_from_picardFrontier_persistence
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hBForm : PositiveDatumBFormLocalHyp p)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hPersist : QuantFromThreshold.ClassicalMinPersistence p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bform p hχ ha hb hγ_ge_one hBForm
    (uniformLocalExistence_of_picardFrontier_persistence
      p hχ ha hb hα_ge hγ_ge_one hPF hPersist hlocal)

/-- General-χ B-form headline with the uniform-local-existence input replaced
by the Picard-restart/min-persistence route, and with `hlocal` supplied by the
B-form package itself. -/
theorem paper2_theorem_1_1_general_chi_bform_from_picardFrontier_persistence_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hBForm : PositiveDatumBFormLocalHyp p)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hPersist : QuantFromThreshold.ClassicalMinPersistence p) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bform p hχ ha hb hγ_ge_one hBForm
    (uniformLocalExistence_of_picardFrontier_persistence_of_BForm
      p hχ ha hb hα_ge hγ_ge_one hPF hPersist hBForm)

/-- General-χ B-form headline with `hlocal` supplied by the B-form package and
the restart frontier reduced to the unified Picard-limit residual. -/
theorem paper2_theorem_1_1_general_chi_bform_from_picardLimitFrontier_persistence_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hBForm : PositiveDatumBFormLocalHyp p)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hPersist : QuantFromThreshold.ClassicalMinPersistence p) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bform p hχ ha hb hγ_ge_one hBForm
    (uniformLocalExistence_of_picardLimitFrontier_persistence_of_BForm
      p hχ ha hb hα_ge hγ_ge_one hPLF hPersist hBForm)

/-- General-χ B-form headline with the uniform-local-existence input replaced
by the Picard-restart route plus the boundary min-point persistence input. -/
theorem paper2_theorem_1_1_general_chi_bform_from_picardFrontier_boundary
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hBForm : PositiveDatumBFormLocalHyp p)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hbdry : BoundaryMinPersistenceBound p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bform p hχ ha hb hγ_ge_one hBForm
    (uniformLocalExistence_of_picardFrontier_boundary
      p hχ ha hb hα_ge hγ_ge_one hPF hbdry hlocal)

/-- General-χ B-form headline with the uniform-local-existence input replaced
by the Picard-restart/boundary-persistence route, and with `hlocal` supplied by
the B-form package itself. -/
theorem paper2_theorem_1_1_general_chi_bform_from_picardFrontier_boundary_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hBForm : PositiveDatumBFormLocalHyp p)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hbdry : BoundaryMinPersistenceBound p) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bform p hχ ha hb hγ_ge_one hBForm
    (uniformLocalExistence_of_picardFrontier_boundary_of_BForm
      p hχ ha hb hα_ge hγ_ge_one hPF hbdry hBForm)

/-- General-χ B-form headline with `hlocal` supplied by the B-form package,
`ClassicalMinPersistence` reduced to the boundary residual, and the restart
frontier reduced to the unified Picard-limit residual. -/
theorem paper2_theorem_1_1_general_chi_bform_from_picardLimitFrontier_boundary_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hBForm : PositiveDatumBFormLocalHyp p)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hbdry : BoundaryMinPersistenceBound p) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bform p hχ ha hb hγ_ge_one hBForm
    (uniformLocalExistence_of_picardLimitFrontier_boundary_of_BForm
      p hχ ha hb hα_ge hγ_ge_one hPLF hbdry hBForm)

section AxiomAudit

#print axioms uniformLocalExistence_of_quantitative_regime
#print axioms uniformLocalExistence_of_picardFrontier_persistence
#print axioms uniformLocalExistence_of_picardFrontier_persistence_of_BForm
#print axioms uniformLocalExistence_of_picardLimitFrontier_persistence_of_BForm
#print axioms classicalMinPersistence_of_boundary_regime
#print axioms boundaryMinPersistenceWindowBound_of_boundary
#print axioms classicalMinPersistence_of_boundary_window_regime
#print axioms uniformLocalExistence_of_picardFrontier_boundary
#print axioms uniformLocalExistence_of_picardFrontier_boundary_of_BForm
#print axioms uniformLocalExistence_of_picardLimitFrontier_boundary_of_BForm
#print axioms quantitativeLocalExistence_of_picardFrontier_boundary
#print axioms quantitativeLocalExistence_of_picardLimitFrontier_boundary
#print axioms quantitativeLocalExistence_of_picardFrontier_boundary_window
#print axioms quantitativeLocalExistence_of_picardLimitFrontier_boundary_window
#print axioms quantitativeLocalExistence_of_picardFrontier_persistence_of_BForm
#print axioms quantitativeLocalExistence_of_picardLimitFrontier_persistence_of_BForm
#print axioms quantitativeLocalExistence_of_picardFrontier_boundary_of_BForm
#print axioms quantitativeLocalExistence_of_picardLimitFrontier_boundary_of_BForm
#print axioms quantitativeLocalExistence_of_picardFrontier_boundary_window_of_BForm
#print axioms quantitativeLocalExistence_of_picardLimitFrontier_boundary_window_of_BForm
#print axioms
  paper2_theorem_1_1_general_chi_from_picardLimitFrontier_boundary_of_BForm_hQuant
#print axioms paper2_theorem_1_1_general_chi_bform_from_quant
#print axioms paper2_theorem_1_1_general_chi_bform_from_picardFrontier_persistence
#print axioms
  paper2_theorem_1_1_general_chi_bform_from_picardFrontier_persistence_of_BForm
#print axioms
  paper2_theorem_1_1_general_chi_bform_from_picardLimitFrontier_persistence_of_BForm
#print axioms paper2_theorem_1_1_general_chi_bform_from_picardFrontier_boundary
#print axioms
  paper2_theorem_1_1_general_chi_bform_from_picardFrontier_boundary_of_BForm
#print axioms
  paper2_theorem_1_1_general_chi_bform_from_picardLimitFrontier_boundary_of_BForm

end AxiomAudit

end ShenWork.Paper2.BFormPositiveDatumLocal

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-- Uniform local existence from the Picard-restart route, with the per-datum
`hlocal` seed supplied by the negative-part B-form frontier. -/
theorem uniformLocalExistence_of_picardFrontier_persistence_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hPersist : QuantFromThreshold.ClassicalMinPersistence p)
    (hPerDatum : BFormPositiveLocalFrontier p) :
    IntervalDomainUniformLocalExistence p :=
  ShenWork.Paper2.BFormPositiveDatumLocal.uniformLocalExistence_of_picardFrontier_persistence
    p hχ ha hb hα_ge hγ_ge_one hPF hPersist
    (positiveDatum_localExistence_of_BForm hPerDatum)

/-- Uniform local existence from the unified Picard-limit restart frontier,
with the per-datum `hlocal` seed supplied by the negative-part B-form frontier. -/
theorem uniformLocalExistence_of_picardLimitFrontier_persistence_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hPersist : QuantFromThreshold.ClassicalMinPersistence p)
    (hPerDatum : BFormPositiveLocalFrontier p) :
    IntervalDomainUniformLocalExistence p :=
  uniformLocalExistence_of_picardFrontier_persistence_of_BForm
    p hχ ha hb hα_ge hγ_ge_one
    (ConeQuantBridge.picardRestartFrontier_of_picardLimitFrontier hPLF)
    hPersist hPerDatum

/-- Uniform local existence from the Picard-restart route and boundary
min-point persistence, with `hlocal` supplied by the negative-part B-form
frontier. -/
theorem uniformLocalExistence_of_picardFrontier_boundary_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hbdry : ShenWork.Paper2.BFormPositiveDatumLocal.BoundaryMinPersistenceBound p)
    (hPerDatum : BFormPositiveLocalFrontier p) :
    IntervalDomainUniformLocalExistence p :=
  ShenWork.Paper2.BFormPositiveDatumLocal.uniformLocalExistence_of_picardFrontier_boundary
    p hχ ha hb hα_ge hγ_ge_one hPF hbdry
    (positiveDatum_localExistence_of_BForm hPerDatum)

/-- Uniform local existence from the unified Picard-limit restart frontier and
boundary min-point persistence, with `hlocal` supplied by the negative-part
B-form frontier. -/
theorem uniformLocalExistence_of_picardLimitFrontier_boundary_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hbdry : ShenWork.Paper2.BFormPositiveDatumLocal.BoundaryMinPersistenceBound p)
    (hPerDatum : BFormPositiveLocalFrontier p) :
    IntervalDomainUniformLocalExistence p :=
  uniformLocalExistence_of_picardFrontier_boundary_of_BForm
    p hχ ha hb hα_ge hγ_ge_one
    (ConeQuantBridge.picardRestartFrontier_of_picardLimitFrontier hPLF)
    hbdry hPerDatum

/-- Quantitative local existence from the Picard-restart route, with the
per-datum local seed supplied by the negative-part B-form frontier. -/
theorem quantitativeLocalExistence_of_picardFrontier_persistence_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hPersist : QuantFromThreshold.ClassicalMinPersistence p)
    (hPerDatum : BFormPositiveLocalFrontier p) :
    ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u :=
  ThresholdQuantBridge.quantitativeLocalExistence_of_picardFrontier_persistence
    p hχ ha hb hα_ge hγ_ge_one hPF hPersist
    (positiveDatum_localExistence_of_BForm hPerDatum)

/-- Quantitative local existence from the unified Picard-limit restart frontier,
with the per-datum local seed supplied by the negative-part B-form frontier. -/
theorem quantitativeLocalExistence_of_picardLimitFrontier_persistence_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hPersist : QuantFromThreshold.ClassicalMinPersistence p)
    (hPerDatum : BFormPositiveLocalFrontier p) :
    ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u :=
  quantitativeLocalExistence_of_picardFrontier_persistence_of_BForm
    p hχ ha hb hα_ge hγ_ge_one
    (ConeQuantBridge.picardRestartFrontier_of_picardLimitFrontier hPLF)
    hPersist hPerDatum

/-- Quantitative local existence from the Picard-restart route and boundary
min-point persistence, with the per-datum local seed supplied by the
negative-part B-form frontier. -/
theorem quantitativeLocalExistence_of_picardFrontier_boundary_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hbdry : ShenWork.Paper2.BFormPositiveDatumLocal.BoundaryMinPersistenceBound p)
    (hPerDatum : BFormPositiveLocalFrontier p) :
    ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u :=
  ShenWork.Paper2.BFormPositiveDatumLocal.quantitativeLocalExistence_of_picardFrontier_boundary
    p hχ ha hb hα_ge hγ_ge_one hPF hbdry
    (positiveDatum_localExistence_of_BForm hPerDatum)

/-- Quantitative local existence from the unified Picard-limit restart frontier
and boundary min-point persistence, with the per-datum local seed supplied by
the negative-part B-form frontier. -/
theorem quantitativeLocalExistence_of_picardLimitFrontier_boundary_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hbdry : ShenWork.Paper2.BFormPositiveDatumLocal.BoundaryMinPersistenceBound p)
    (hPerDatum : BFormPositiveLocalFrontier p) :
    ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u :=
  ShenWork.Paper2.BFormPositiveDatumLocal.quantitativeLocalExistence_of_picardLimitFrontier_boundary
    p hχ ha hb hα_ge hγ_ge_one hPLF hbdry
    (positiveDatum_localExistence_of_BForm hPerDatum)

/-- Quantitative local existence from the Picard-restart route and windowed
boundary persistence, with the per-datum local seed supplied by the
negative-part B-form frontier. -/
theorem quantitativeLocalExistence_of_picardFrontier_boundary_window_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hbdry :
      ShenWork.Paper2.BFormPositiveDatumLocal.BoundaryMinPersistenceWindowBound p)
    (hPerDatum : BFormPositiveLocalFrontier p) :
    ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u :=
  by
    exact
      BFormPositiveDatumLocal.quantitativeLocalExistence_of_picardFrontier_boundary_window
        p hχ ha hb hα_ge hγ_ge_one hPF hbdry
        (positiveDatum_localExistence_of_BForm hPerDatum)

/-- Quantitative local existence from the unified Picard-limit restart frontier
and windowed boundary persistence, with the per-datum local seed supplied by
the negative-part B-form frontier. -/
theorem quantitativeLocalExistence_of_picardLimitFrontier_boundary_window_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hbdry :
      ShenWork.Paper2.BFormPositiveDatumLocal.BoundaryMinPersistenceWindowBound p)
    (hPerDatum : BFormPositiveLocalFrontier p) :
    ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u :=
  by
    exact
      BFormPositiveDatumLocal.quantitativeLocalExistence_of_picardLimitFrontier_boundary_window
        p hχ ha hb hα_ge hγ_ge_one hPLF hbdry
        (positiveDatum_localExistence_of_BForm hPerDatum)

/-- General-χ headline from the negative-part source-side hQuant package:
negative-part frontier, Picard-limit restart frontier, and boundary persistence. -/
theorem paper2_theorem_1_1_general_chi_negpart_from_picardLimitFrontier_boundary_hQuant
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hbdry : ShenWork.Paper2.BFormPositiveDatumLocal.BoundaryMinPersistenceBound p)
    (hPerDatum : BFormPositiveLocalFrontier p) :
    Theorem_1_1 intervalDomain p :=
  FinalWiring.paper2_theorem_1_1_from_quant p hχ ha hb hγ_ge_one
    (quantitativeLocalExistence_of_picardLimitFrontier_boundary_of_BForm
      p hχ ha hb hα_ge hγ_ge_one hPLF hbdry hPerDatum)

/-- Negative-part B-form headline with the uniform-local-existence input
replaced by the quantitative local factory. -/
theorem paper2_theorem_1_1_general_chi_bform_negpart_from_quant
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (_hPerDatum : BFormPositiveLocalFrontier p)
    (hQuant : ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  FinalWiring.paper2_theorem_1_1_from_quant
    p hχ ha hb hγ_ge_one hQuant

/-- Negative-part B-form headline with the uniform-local-existence input
replaced by the Picard-restart/min-persistence local-existence route. -/
theorem paper2_theorem_1_1_general_chi_bform_negpart_from_picardFrontier_persistence
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPerDatum : BFormPositiveLocalFrontier p)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hPersist : QuantFromThreshold.ClassicalMinPersistence p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bform_negpart
    p hχ ha hb hγ_ge_one hPerDatum
    (ShenWork.Paper2.BFormPositiveDatumLocal.uniformLocalExistence_of_picardFrontier_persistence
        p hχ ha hb hα_ge hγ_ge_one hPF hPersist hlocal)

/-- Negative-part B-form headline with the uniform-local-existence input
replaced by the Picard-restart/min-persistence route, and with `hlocal`
supplied by the negative-part B-form frontier itself. -/
theorem
    paper2_theorem_1_1_general_chi_bform_negpart_from_picardFrontier_persistence_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPerDatum : BFormPositiveLocalFrontier p)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hPersist : QuantFromThreshold.ClassicalMinPersistence p) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bform_negpart
    p hχ ha hb hγ_ge_one hPerDatum
    (uniformLocalExistence_of_picardFrontier_persistence_of_BForm
      p hχ ha hb hα_ge hγ_ge_one hPF hPersist hPerDatum)

/-- Negative-part B-form headline with `hlocal` supplied by the B-form frontier
and the restart frontier reduced to the unified Picard-limit residual. -/
theorem
    paper2_theorem_1_1_general_chi_bform_negpart_from_picardLimitFrontier_persistence_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPerDatum : BFormPositiveLocalFrontier p)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hPersist : QuantFromThreshold.ClassicalMinPersistence p) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bform_negpart
    p hχ ha hb hγ_ge_one hPerDatum
    (uniformLocalExistence_of_picardLimitFrontier_persistence_of_BForm
      p hχ ha hb hα_ge hγ_ge_one hPLF hPersist hPerDatum)

/-- Negative-part B-form headline with the uniform-local-existence input
replaced by the Picard-restart route plus the boundary min-point persistence
input. -/
theorem paper2_theorem_1_1_general_chi_bform_negpart_from_picardFrontier_boundary
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPerDatum : BFormPositiveLocalFrontier p)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hbdry : ShenWork.Paper2.BFormPositiveDatumLocal.BoundaryMinPersistenceBound p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bform_negpart
    p hχ ha hb hγ_ge_one hPerDatum
    (ShenWork.Paper2.BFormPositiveDatumLocal.uniformLocalExistence_of_picardFrontier_boundary
        p hχ ha hb hα_ge hγ_ge_one hPF hbdry hlocal)

/-- Negative-part B-form headline with the uniform-local-existence input
replaced by the Picard-restart/boundary-persistence route, and with `hlocal`
supplied by the negative-part B-form frontier itself. -/
theorem
    paper2_theorem_1_1_general_chi_bform_negpart_from_picardFrontier_boundary_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPerDatum : BFormPositiveLocalFrontier p)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hbdry : ShenWork.Paper2.BFormPositiveDatumLocal.BoundaryMinPersistenceBound p) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bform_negpart
    p hχ ha hb hγ_ge_one hPerDatum
    (uniformLocalExistence_of_picardFrontier_boundary_of_BForm
      p hχ ha hb hα_ge hγ_ge_one hPF hbdry hPerDatum)

/-- Negative-part B-form headline with `hlocal` supplied by the B-form
frontier, `ClassicalMinPersistence` reduced to the boundary residual, and the
restart frontier reduced to the unified Picard-limit residual. -/
theorem
    paper2_theorem_1_1_general_chi_bform_negpart_from_picardLimitFrontier_boundary_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPerDatum : BFormPositiveLocalFrontier p)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hbdry : ShenWork.Paper2.BFormPositiveDatumLocal.BoundaryMinPersistenceBound p) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bform_negpart
    p hχ ha hb hγ_ge_one hPerDatum
    (uniformLocalExistence_of_picardLimitFrontier_boundary_of_BForm
      p hχ ha hb hα_ge hγ_ge_one hPLF hbdry hPerDatum)

section AxiomAudit

#print axioms uniformLocalExistence_of_picardFrontier_persistence_of_BForm
#print axioms uniformLocalExistence_of_picardLimitFrontier_persistence_of_BForm
#print axioms uniformLocalExistence_of_picardFrontier_boundary_of_BForm
#print axioms uniformLocalExistence_of_picardLimitFrontier_boundary_of_BForm
#print axioms quantitativeLocalExistence_of_picardFrontier_persistence_of_BForm
#print axioms quantitativeLocalExistence_of_picardLimitFrontier_persistence_of_BForm
#print axioms quantitativeLocalExistence_of_picardFrontier_boundary_of_BForm
#print axioms quantitativeLocalExistence_of_picardLimitFrontier_boundary_of_BForm
#print axioms quantitativeLocalExistence_of_picardFrontier_boundary_window_of_BForm
#print axioms quantitativeLocalExistence_of_picardLimitFrontier_boundary_window_of_BForm
#print axioms
  paper2_theorem_1_1_general_chi_negpart_from_picardLimitFrontier_boundary_hQuant
#print axioms paper2_theorem_1_1_general_chi_bform_negpart_from_quant
#print axioms paper2_theorem_1_1_general_chi_bform_negpart_from_picardFrontier_persistence
#print axioms
  paper2_theorem_1_1_general_chi_bform_negpart_from_picardFrontier_persistence_of_BForm
#print axioms
  paper2_theorem_1_1_general_chi_bform_negpart_from_picardLimitFrontier_persistence_of_BForm
#print axioms
  paper2_theorem_1_1_general_chi_bform_negpart_from_picardFrontier_boundary
#print axioms
  paper2_theorem_1_1_general_chi_bform_negpart_from_picardFrontier_boundary_of_BForm
#print axioms
  paper2_theorem_1_1_general_chi_bform_negpart_from_picardLimitFrontier_boundary_of_BForm

end AxiomAudit

end ShenWork.Paper2.BFormPositiveDatumNegPart

namespace ShenWork.Paper2.BFormPositiveDatumLocalSq

/-- Squared-barrier B-form headline with the uniform-local-existence input
replaced by the quantitative local factory used by the restart/glue route. -/
theorem paper2_theorem_1_1_general_chi_bformSq_from_quant
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (_hBForm : PositiveDatumBFormLocalHypSq p)
    (hQuant : ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  FinalWiring.paper2_theorem_1_1_from_quant
    p hχ ha hb hγ_ge_one hQuant

/-- Squared-barrier B-form headline with the uniform-local-existence input
replaced by the Picard-restart/min-persistence local-existence route. -/
theorem paper2_theorem_1_1_general_chi_bformSq_from_picardFrontier_persistence
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hBForm : PositiveDatumBFormLocalHypSq p)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hPersist : QuantFromThreshold.ClassicalMinPersistence p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bformSq p hχ ha hb hγ_ge_one hBForm
    (ShenWork.Paper2.BFormPositiveDatumLocal.uniformLocalExistence_of_picardFrontier_persistence
        p hχ ha hb hα_ge hγ_ge_one hPF hPersist hlocal)

/-- Squared-barrier B-form headline with the restart frontier reduced to the
unified Picard-limit residual. -/
theorem paper2_theorem_1_1_general_chi_bformSq_from_picardLimitFrontier_persistence
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hBForm : PositiveDatumBFormLocalHypSq p)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hPersist : QuantFromThreshold.ClassicalMinPersistence p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bformSq_from_picardFrontier_persistence
    p hχ ha hb hα_ge hγ_ge_one hBForm
    (ConeQuantBridge.picardRestartFrontier_of_picardLimitFrontier hPLF)
    hPersist hlocal

/-- Squared-barrier B-form headline with the uniform-local-existence input
replaced by the Picard-restart route plus the boundary min-point persistence
input. -/
theorem paper2_theorem_1_1_general_chi_bformSq_from_picardFrontier_boundary
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hBForm : PositiveDatumBFormLocalHypSq p)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hbdry : ShenWork.Paper2.BFormPositiveDatumLocal.BoundaryMinPersistenceBound p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bformSq p hχ ha hb hγ_ge_one hBForm
    (ShenWork.Paper2.BFormPositiveDatumLocal.uniformLocalExistence_of_picardFrontier_boundary
        p hχ ha hb hα_ge hγ_ge_one hPF hbdry hlocal)

/-- Squared-barrier B-form headline with boundary min-point persistence and
the restart frontier reduced to the unified Picard-limit residual. -/
theorem paper2_theorem_1_1_general_chi_bformSq_from_picardLimitFrontier_boundary
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hBForm : PositiveDatumBFormLocalHypSq p)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hbdry : ShenWork.Paper2.BFormPositiveDatumLocal.BoundaryMinPersistenceBound p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bformSq_from_picardFrontier_boundary
    p hχ ha hb hα_ge hγ_ge_one hBForm
    (ConeQuantBridge.picardRestartFrontier_of_picardLimitFrontier hPLF)
    hbdry hlocal

/-- Banked squared-barrier B-form headline with the uniform-local-existence
input replaced by the quantitative local factory. -/
theorem paper2_theorem_1_1_general_chi_bformSq_of_banked_from_quant
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (_hbanked :
      ∀ u₀ : intervalDomainPoint → ℝ,
        PaperPositiveInitialDatum intervalDomain u₀ →
          ∃ DB : ShenWork.IntervalConjugatePicard.ConjugateMildExistenceData p u₀,
            Nonempty (PositiveDatumBFormSqBankedPlumbing p DB))
    (hQuant : ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  FinalWiring.paper2_theorem_1_1_from_quant
    p hχ ha hb hγ_ge_one hQuant

/-- Banked squared-barrier B-form headline with the uniform-local-existence
input replaced by the Picard-restart/min-persistence local-existence route. -/
theorem paper2_theorem_1_1_general_chi_bformSq_of_banked_from_picardFrontier_persistence
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hbanked :
      ∀ u₀ : intervalDomainPoint → ℝ,
        PaperPositiveInitialDatum intervalDomain u₀ →
          ∃ DB : ShenWork.IntervalConjugatePicard.ConjugateMildExistenceData p u₀,
            Nonempty (PositiveDatumBFormSqBankedPlumbing p DB))
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hPersist : QuantFromThreshold.ClassicalMinPersistence p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bformSq_of_banked
    p hχ ha hb hγ_ge_one hbanked
    (ShenWork.Paper2.BFormPositiveDatumLocal.uniformLocalExistence_of_picardFrontier_persistence
        p hχ ha hb hα_ge hγ_ge_one hPF hPersist hlocal)

/-- Banked squared-barrier B-form headline with the restart frontier reduced to
the unified Picard-limit residual. -/
theorem
    paper2_theorem_1_1_general_chi_bformSq_of_banked_from_picardLimitFrontier_persistence
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hbanked :
      ∀ u₀ : intervalDomainPoint → ℝ,
        PaperPositiveInitialDatum intervalDomain u₀ →
          ∃ DB : ShenWork.IntervalConjugatePicard.ConjugateMildExistenceData p u₀,
            Nonempty (PositiveDatumBFormSqBankedPlumbing p DB))
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hPersist : QuantFromThreshold.ClassicalMinPersistence p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bformSq_of_banked_from_picardFrontier_persistence
    p hχ ha hb hα_ge hγ_ge_one hbanked
    (ConeQuantBridge.picardRestartFrontier_of_picardLimitFrontier hPLF)
    hPersist hlocal

/-- Banked squared-barrier B-form headline with the uniform-local-existence
input replaced by the Picard-restart route plus the boundary min-point
persistence input. -/
theorem paper2_theorem_1_1_general_chi_bformSq_of_banked_from_picardFrontier_boundary
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hbanked :
      ∀ u₀ : intervalDomainPoint → ℝ,
        PaperPositiveInitialDatum intervalDomain u₀ →
          ∃ DB : ShenWork.IntervalConjugatePicard.ConjugateMildExistenceData p u₀,
            Nonempty (PositiveDatumBFormSqBankedPlumbing p DB))
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hbdry : ShenWork.Paper2.BFormPositiveDatumLocal.BoundaryMinPersistenceBound p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bformSq_of_banked
    p hχ ha hb hγ_ge_one hbanked
    (ShenWork.Paper2.BFormPositiveDatumLocal.uniformLocalExistence_of_picardFrontier_boundary
        p hχ ha hb hα_ge hγ_ge_one hPF hbdry hlocal)

/-- Banked squared-barrier B-form headline with boundary min-point persistence
and the restart frontier reduced to the unified Picard-limit residual. -/
theorem
    paper2_theorem_1_1_general_chi_bformSq_of_banked_from_picardLimitFrontier_boundary
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hbanked :
      ∀ u₀ : intervalDomainPoint → ℝ,
        PaperPositiveInitialDatum intervalDomain u₀ →
          ∃ DB : ShenWork.IntervalConjugatePicard.ConjugateMildExistenceData p u₀,
            Nonempty (PositiveDatumBFormSqBankedPlumbing p DB))
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hbdry : ShenWork.Paper2.BFormPositiveDatumLocal.BoundaryMinPersistenceBound p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bformSq_of_banked_from_picardFrontier_boundary
    p hχ ha hb hα_ge hγ_ge_one hbanked
    (ConeQuantBridge.picardRestartFrontier_of_picardLimitFrontier hPLF)
    hbdry hlocal

/-- Concrete-banked squared-barrier B-form headline with the
uniform-local-existence input replaced by the quantitative local factory. -/
theorem paper2_theorem_1_1_general_chi_bformSq_of_concrete_banked_from_quant
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (_hdeep :
      ∀ u₀ : intervalDomainPoint → ℝ,
        PaperPositiveInitialDatum intervalDomain u₀ →
          ∃ DB : ShenWork.IntervalConjugatePicard.ConjugateMildExistenceData p u₀,
            Nonempty (PositiveDatumBFormSqBankedConcreteHypotheses p DB))
    (hQuant : ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  FinalWiring.paper2_theorem_1_1_from_quant
    p hχ ha hb hγ_ge_one hQuant

/-- Concrete-banked squared-barrier B-form headline with the
uniform-local-existence input replaced by the Picard-restart/min-persistence
local-existence route. -/
theorem paper2_theorem_1_1_general_chi_bformSq_of_concrete_banked_from_picardFrontier_persistence
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hdeep :
      ∀ u₀ : intervalDomainPoint → ℝ,
        PaperPositiveInitialDatum intervalDomain u₀ →
          ∃ DB : ShenWork.IntervalConjugatePicard.ConjugateMildExistenceData p u₀,
            Nonempty (PositiveDatumBFormSqBankedConcreteHypotheses p DB))
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hPersist : QuantFromThreshold.ClassicalMinPersistence p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bformSq_of_concrete_banked
    p hχ ha hb hγ_ge_one hdeep
    (ShenWork.Paper2.BFormPositiveDatumLocal.uniformLocalExistence_of_picardFrontier_persistence
        p hχ ha hb hα_ge hγ_ge_one hPF hPersist hlocal)

/-- Concrete-banked squared-barrier B-form headline with the restart frontier
reduced to the unified Picard-limit residual. -/
theorem
    paper2_theorem_1_1_general_chi_bformSq_of_concrete_banked_from_picardLimitFrontier_persistence
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hdeep :
      ∀ u₀ : intervalDomainPoint → ℝ,
        PaperPositiveInitialDatum intervalDomain u₀ →
          ∃ DB : ShenWork.IntervalConjugatePicard.ConjugateMildExistenceData p u₀,
            Nonempty (PositiveDatumBFormSqBankedConcreteHypotheses p DB))
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hPersist : QuantFromThreshold.ClassicalMinPersistence p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bformSq_of_concrete_banked_from_picardFrontier_persistence
    p hχ ha hb hα_ge hγ_ge_one hdeep
    (ConeQuantBridge.picardRestartFrontier_of_picardLimitFrontier hPLF)
    hPersist hlocal

/-- Concrete-banked squared-barrier B-form headline with the
uniform-local-existence input replaced by the Picard-restart route plus the
boundary min-point persistence input. -/
theorem paper2_theorem_1_1_general_chi_bformSq_of_concrete_banked_from_picardFrontier_boundary
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hdeep :
      ∀ u₀ : intervalDomainPoint → ℝ,
        PaperPositiveInitialDatum intervalDomain u₀ →
          ∃ DB : ShenWork.IntervalConjugatePicard.ConjugateMildExistenceData p u₀,
            Nonempty (PositiveDatumBFormSqBankedConcreteHypotheses p DB))
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hbdry : ShenWork.Paper2.BFormPositiveDatumLocal.BoundaryMinPersistenceBound p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bformSq_of_concrete_banked
    p hχ ha hb hγ_ge_one hdeep
    (ShenWork.Paper2.BFormPositiveDatumLocal.uniformLocalExistence_of_picardFrontier_boundary
        p hχ ha hb hα_ge hγ_ge_one hPF hbdry hlocal)

/-- Concrete-banked squared-barrier B-form headline with boundary min-point
persistence and the restart frontier reduced to the unified Picard-limit
residual. -/
theorem
    paper2_theorem_1_1_general_chi_bformSq_of_concrete_banked_from_picardLimitFrontier_boundary
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hdeep :
      ∀ u₀ : intervalDomainPoint → ℝ,
        PaperPositiveInitialDatum intervalDomain u₀ →
          ∃ DB : ShenWork.IntervalConjugatePicard.ConjugateMildExistenceData p u₀,
            Nonempty (PositiveDatumBFormSqBankedConcreteHypotheses p DB))
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hbdry : ShenWork.Paper2.BFormPositiveDatumLocal.BoundaryMinPersistenceBound p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bformSq_of_concrete_banked_from_picardFrontier_boundary
    p hχ ha hb hα_ge hγ_ge_one hdeep
    (ConeQuantBridge.picardRestartFrontier_of_picardLimitFrontier hPLF)
    hbdry hlocal

/-- Regular squared-barrier B-form headline with the uniform-local-existence
input replaced by the quantitative local factory. -/
theorem paper2_theorem_1_1_general_chi_bformSq_regular_from_quant
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (_hBForm : PositiveDatumBFormLocalHypSqRegular p)
    (hQuant : ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  FinalWiring.paper2_theorem_1_1_from_quant
    p hχ ha hb hγ_ge_one hQuant

/-- Regular squared-barrier B-form headline with the uniform-local-existence
input replaced by the Picard-restart/min-persistence local-existence route. -/
theorem paper2_theorem_1_1_general_chi_bformSq_regular_from_picardFrontier_persistence
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hBForm : PositiveDatumBFormLocalHypSqRegular p)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hPersist : QuantFromThreshold.ClassicalMinPersistence p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bformSq_regular
    p hχ ha hb hγ_ge_one hBForm
    (ShenWork.Paper2.BFormPositiveDatumLocal.uniformLocalExistence_of_picardFrontier_persistence
        p hχ ha hb hα_ge hγ_ge_one hPF hPersist hlocal)

/-- Regular squared-barrier B-form headline with the restart frontier reduced
to the unified Picard-limit residual. -/
theorem paper2_theorem_1_1_general_chi_bformSq_regular_from_picardLimitFrontier_persistence
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hBForm : PositiveDatumBFormLocalHypSqRegular p)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hPersist : QuantFromThreshold.ClassicalMinPersistence p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bformSq_regular_from_picardFrontier_persistence
    p hχ ha hb hα_ge hγ_ge_one hBForm
    (ConeQuantBridge.picardRestartFrontier_of_picardLimitFrontier hPLF)
    hPersist hlocal

/-- Regular squared-barrier B-form headline with the uniform-local-existence
input replaced by the Picard-restart route plus the boundary min-point
persistence input. -/
theorem paper2_theorem_1_1_general_chi_bformSq_regular_from_picardFrontier_boundary
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hBForm : PositiveDatumBFormLocalHypSqRegular p)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hbdry : ShenWork.Paper2.BFormPositiveDatumLocal.BoundaryMinPersistenceBound p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bformSq_regular
    p hχ ha hb hγ_ge_one hBForm
    (ShenWork.Paper2.BFormPositiveDatumLocal.uniformLocalExistence_of_picardFrontier_boundary
        p hχ ha hb hα_ge hγ_ge_one hPF hbdry hlocal)

/-- Regular squared-barrier B-form headline with boundary min-point persistence
and the restart frontier reduced to the unified Picard-limit residual. -/
theorem paper2_theorem_1_1_general_chi_bformSq_regular_from_picardLimitFrontier_boundary
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hBForm : PositiveDatumBFormLocalHypSqRegular p)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hbdry : ShenWork.Paper2.BFormPositiveDatumLocal.BoundaryMinPersistenceBound p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bformSq_regular_from_picardFrontier_boundary
    p hχ ha hb hα_ge hγ_ge_one hBForm
    (ConeQuantBridge.picardRestartFrontier_of_picardLimitFrontier hPLF)
    hbdry hlocal

/-- Deepest squared-barrier B-form headline with the uniform-local-existence
input replaced by the quantitative local factory. -/
theorem paper2_theorem_1_1_general_chi_bformSq_of_deepest_from_quant
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (_hdeepest : PositiveDatumBFormLocalHypSqDeepest p)
    (hQuant : ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  FinalWiring.paper2_theorem_1_1_from_quant
    p hχ ha hb hγ_ge_one hQuant

/-- Deepest squared-barrier B-form headline with the uniform-local-existence
input replaced by the Picard-restart/min-persistence local-existence route. -/
theorem paper2_theorem_1_1_general_chi_bformSq_of_deepest_from_picardFrontier_persistence
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hdeepest : PositiveDatumBFormLocalHypSqDeepest p)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hPersist : QuantFromThreshold.ClassicalMinPersistence p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bformSq_of_deepest
    p hχ ha hb hγ_ge_one hdeepest
    (ShenWork.Paper2.BFormPositiveDatumLocal.uniformLocalExistence_of_picardFrontier_persistence
        p hχ ha hb hα_ge hγ_ge_one hPF hPersist hlocal)

/-- Deepest squared-barrier B-form headline with the restart frontier reduced
to the unified Picard-limit residual. -/
theorem paper2_theorem_1_1_general_chi_bformSq_of_deepest_from_picardLimitFrontier_persistence
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hdeepest : PositiveDatumBFormLocalHypSqDeepest p)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hPersist : QuantFromThreshold.ClassicalMinPersistence p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bformSq_of_deepest_from_picardFrontier_persistence
    p hχ ha hb hα_ge hγ_ge_one hdeepest
    (ConeQuantBridge.picardRestartFrontier_of_picardLimitFrontier hPLF)
    hPersist hlocal

/-- Deepest squared-barrier B-form headline with the uniform-local-existence
input replaced by the Picard-restart route plus the boundary min-point
persistence input. -/
theorem paper2_theorem_1_1_general_chi_bformSq_of_deepest_from_picardFrontier_boundary
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hdeepest : PositiveDatumBFormLocalHypSqDeepest p)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hbdry : ShenWork.Paper2.BFormPositiveDatumLocal.BoundaryMinPersistenceBound p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bformSq_of_deepest
    p hχ ha hb hγ_ge_one hdeepest
    (ShenWork.Paper2.BFormPositiveDatumLocal.uniformLocalExistence_of_picardFrontier_boundary
        p hχ ha hb hα_ge hγ_ge_one hPF hbdry hlocal)

/-- Deepest squared-barrier B-form headline with boundary min-point persistence
and the restart frontier reduced to the unified Picard-limit residual. -/
theorem paper2_theorem_1_1_general_chi_bformSq_of_deepest_from_picardLimitFrontier_boundary
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hdeepest : PositiveDatumBFormLocalHypSqDeepest p)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hbdry : ShenWork.Paper2.BFormPositiveDatumLocal.BoundaryMinPersistenceBound p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bformSq_of_deepest_from_picardFrontier_boundary
    p hχ ha hb hα_ge hγ_ge_one hdeepest
    (ConeQuantBridge.picardRestartFrontier_of_picardLimitFrontier hPLF)
    hbdry hlocal

section AxiomAudit

#print axioms paper2_theorem_1_1_general_chi_bformSq_from_quant
#print axioms paper2_theorem_1_1_general_chi_bformSq_of_banked_from_quant
#print axioms paper2_theorem_1_1_general_chi_bformSq_of_concrete_banked_from_quant
#print axioms paper2_theorem_1_1_general_chi_bformSq_regular_from_quant
#print axioms paper2_theorem_1_1_general_chi_bformSq_of_deepest_from_quant
#print axioms paper2_theorem_1_1_general_chi_bformSq_from_picardFrontier_persistence
#print axioms paper2_theorem_1_1_general_chi_bformSq_from_picardLimitFrontier_persistence
#print axioms paper2_theorem_1_1_general_chi_bformSq_of_banked_from_picardFrontier_persistence
#print axioms
  paper2_theorem_1_1_general_chi_bformSq_of_banked_from_picardLimitFrontier_persistence
#print axioms
  paper2_theorem_1_1_general_chi_bformSq_of_concrete_banked_from_picardFrontier_persistence
#print axioms
  paper2_theorem_1_1_general_chi_bformSq_of_concrete_banked_from_picardLimitFrontier_persistence
#print axioms paper2_theorem_1_1_general_chi_bformSq_regular_from_picardFrontier_persistence
#print axioms
  paper2_theorem_1_1_general_chi_bformSq_regular_from_picardLimitFrontier_persistence
#print axioms paper2_theorem_1_1_general_chi_bformSq_of_deepest_from_picardFrontier_persistence
#print axioms
  paper2_theorem_1_1_general_chi_bformSq_of_deepest_from_picardLimitFrontier_persistence
#print axioms paper2_theorem_1_1_general_chi_bformSq_from_picardFrontier_boundary
#print axioms paper2_theorem_1_1_general_chi_bformSq_from_picardLimitFrontier_boundary
#print axioms
  paper2_theorem_1_1_general_chi_bformSq_of_banked_from_picardFrontier_boundary
#print axioms
  paper2_theorem_1_1_general_chi_bformSq_of_banked_from_picardLimitFrontier_boundary
#print axioms
  paper2_theorem_1_1_general_chi_bformSq_of_concrete_banked_from_picardFrontier_boundary
#print axioms
  paper2_theorem_1_1_general_chi_bformSq_of_concrete_banked_from_picardLimitFrontier_boundary
#print axioms paper2_theorem_1_1_general_chi_bformSq_regular_from_picardFrontier_boundary
#print axioms
  paper2_theorem_1_1_general_chi_bformSq_regular_from_picardLimitFrontier_boundary
#print axioms
  paper2_theorem_1_1_general_chi_bformSq_of_deepest_from_picardFrontier_boundary
#print axioms
  paper2_theorem_1_1_general_chi_bformSq_of_deepest_from_picardLimitFrontier_boundary

end AxiomAudit

end ShenWork.Paper2.BFormPositiveDatumLocalSq
