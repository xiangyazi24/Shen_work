/-
  Final wiring: Paper 2 Theorem 1.1 from regime + 3 hypotheses.
  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainTheorem11Umbrella
import ShenWork.Paper2.IntervalDomainPiecewiseGlue
import ShenWork.Paper2.IntervalDomainPiecewiseClassical
import ShenWork.Paper2.IntervalDomainGlueExtension
import ShenWork.Paper2.IntervalDomainTimeShift
import ShenWork.Paper2.IntervalDomainSupNormBridge
import ShenWork.Paper2.IntervalDomainRestartExtension

open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.FinalWiring

/-- A `PositiveInitialDatum` has a positive uniform absolute-value bound. -/
private lemma exists_supBound_of_positiveInitialDatum
    {u₀ : intervalDomain.Point → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : intervalDomain.Point, |u₀ x| ≤ M := by
  obtain ⟨M₀, hM₀⟩ := hu₀.admissible.1
  refine ⟨max M₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x
  have hx_mem : |u₀ x| ∈ Set.range (fun y : intervalDomain.Point => |u₀ y|) :=
    ⟨x, rfl⟩
  exact (hM₀ hx_mem).trans (le_max_left _ _)

/-- A quantitative local factory immediately gives ordinary local existence:
extract a positive sup-bound from the initial datum and apply the factory at
that bound. -/
theorem localExistence_of_quantitativeLocalExistence
    (p : CM2Params)
    (hQuant : ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u) :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro u₀ hu₀
  obtain ⟨M, hM_pos, hM_bound⟩ := exists_supBound_of_positiveInitialDatum hu₀
  obtain ⟨δ, hδ_pos, hδ⟩ := hQuant M hM_pos
  obtain ⟨u, v, hsol, htrace⟩ := hδ hu₀ hM_bound
  exact ⟨δ, hδ_pos, u, v, hsol, htrace⟩

/-- Uniform continuation from the quantitative local factory plus the
piecewise-classical restart/glue package. -/
theorem uniformLocalExistence_of_quantitative_and_piecewise
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hQuant : ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u)
    (hPCW : PiecewiseGlue.PiecewiseClassicalWorks p) :
    IntervalDomainUniformLocalExistence p := by
  intro M hM
  set M' := SupNormBridge.regimeBound p M
  have hM' := SupNormBridge.regimeBound_pos p hM
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
      hPCW
  refine ⟨δ / 2, by linarith, ?_⟩
  intro u₀ hu₀ hbound T₀ hT₀ u v hsol htrace
  have hSupBound : ∀ t, 0 < t → t < T₀ → ∀ x : intervalDomainPoint, |u t x| ≤ M' :=
    SupNormBridge.interiorSupNorm_le_regimeBound p hχ ha hb hu₀ hM hbound hT₀ hsol htrace
  have hbound' : ∀ x, |u₀ x| ≤ M' := fun x =>
    le_trans (hbound x) (SupNormBridge.regimeBound_ge_M p M)
  have hfactory : ∀ {w : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain w → (∀ x, |w x| ≤ M') →
      ∃ uw vw, IsPaper2ClassicalSolution intervalDomain p δ uw vw ∧
        InitialTrace intervalDomain w uw := fun hw hbw => hex hw hbw
  exact hRestart hM' hδ hfactory hu₀ hbound' hT₀ hsol htrace hSupBound

/-- **Paper 2 Theorem 1.1 from regime + 3 hypotheses.**

Compatibility wrapper.  The quantitative local factory already supplies the
ordinary local-existence input, so the mild-local argument is retained only for
older callers. -/
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
    (_hMildLocal :
      IntervalDomainGradientMildHalfStepLogisticSourceFrontierCoreLocalData p) :
    Theorem_1_1 intervalDomain p := by
  exact
    Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hextend_mge
      p hχ ha hb hγ_ge_one
      (localExistence_of_quantitativeLocalExistence p hQuant)
      (uniformLocalExistence_of_quantitative_and_piecewise
        p hχ ha hb hγ_ge_one hQuant hPCW)

/-- **Paper 2 Theorem 1.1 from regime + 2 hypotheses.**

Compatibility wrapper.  `hPCW` is discharged unconditionally, and the
quantitative local factory already supplies ordinary local existence, so the
mild-local argument is retained only for older callers. -/
theorem paper2_theorem_1_1_from_two
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hQuant : ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u)
    (_hMildLocal :
      IntervalDomainGradientMildHalfStepLogisticSourceFrontierCoreLocalData p) :
    Theorem_1_1 intervalDomain p :=
  Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hextend_mge
    p hχ ha hb hγ_ge_one
    (localExistence_of_quantitativeLocalExistence p hQuant)
    (uniformLocalExistence_of_quantitative_and_piecewise
      p hχ ha hb hγ_ge_one hQuant
      (PiecewiseClassical.piecewiseClassicalWorks p))

/-- **Paper 2 Theorem 1.1 from the quantitative local factory and a
piecewise-classical restart/glue package.**

Compared with `paper2_theorem_1_1_from_three`, the quantitative factory now
also supplies the ordinary local-existence input, so no separate mild-local
frontier is needed. -/
theorem paper2_theorem_1_1_from_quant_and_piecewise
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hQuant : ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u)
    (hPCW : PiecewiseGlue.PiecewiseClassicalWorks p) :
    Theorem_1_1 intervalDomain p :=
  Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hextend_mge
    p hχ ha hb hγ_ge_one
    (localExistence_of_quantitativeLocalExistence p hQuant)
    (uniformLocalExistence_of_quantitative_and_piecewise
      p hχ ha hb hγ_ge_one hQuant hPCW)

/-- **Paper 2 Theorem 1.1 from one quantitative local factory.**

The piecewise-classical restart/glue package is discharged by
`PiecewiseClassical.piecewiseClassicalWorks`, and the same quantitative local
factory supplies both local existence and uniform continuation. -/
theorem paper2_theorem_1_1_from_quant
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hQuant : ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_from_quant_and_piecewise
    p hχ ha hb hγ_ge_one hQuant
    (PiecewiseClassical.piecewiseClassicalWorks p)

end ShenWork.Paper2.FinalWiring
