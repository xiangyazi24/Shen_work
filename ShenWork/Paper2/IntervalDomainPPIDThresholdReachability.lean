/-
  PPID-typed anti-Zeno reachability from threshold local existence.

  The current all-PPID common-floor route is uninhabitable: bounded PPID data
  have no common positive lower floor.  This file banks the honest replacement:
  a per-datum PPID seed, a threshold factory on `{|w| <= M, c <= w}`, and
  min-persistence for the original datum give a fixed positive restart step on
  each prescribed target window.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainQuantFromThreshold
import ShenWork.Paper2.IntervalDomainTheorem11StrongPath

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.QuantFromThreshold

noncomputable section

namespace ShenWork.Paper2.PPIDThresholdReachability

private lemma exists_supBound_ppid
    {u₀ : intervalDomain.Point → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : intervalDomain.Point, |u₀ x| ≤ M := by
  obtain ⟨M₀, hM₀⟩ := hu₀.admissible.1
  refine ⟨max M₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x
  have hx_mem : |u₀ x| ∈ Set.range (fun y : intervalDomain.Point => |u₀ y|) :=
    ⟨x, rfl⟩
  exact (hM₀ hx_mem).trans (le_max_left _ _)

/-- PPID seed local existence plus threshold local existence and min-persistence
gives anti-Zeno reachability for the fixed original PPID datum.

The restart lower threshold `c` may depend on the datum and the target window;
there is no all-PPID common floor. -/
theorem reachableArbitrarilyLong_ppid_of_threshold_persistence_seed
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hThreshold : ThresholdQuantitativeLocalExistence p)
    (hPersist : ClassicalMinPersistence p)
    (hlocalPPID : ∀ u₀ : intervalDomain.Point → ℝ,
      PaperPositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u)
    {u₀ : intervalDomain.Point → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    ShenWork.IntervalDomainExistence.ReachableArbitrarilyLong p u₀ := by
  intro T hT
  obtain ⟨M, hM, hbound⟩ := exists_supBound_ppid hu₀
  obtain ⟨T₁, hT₁, u, v, hsol, htrace⟩ := hlocalPPID u₀ hu₀
  by_cases hbig : T ≤ T₁
  · exact ⟨hT, u, v, hsol.restrict_horizon hT hbig, htrace⟩
  push Not at hbig
  have hOverlap : GlueExtension.OverlapUniqueForPID p :=
    GlueExtension.overlapUniqueForPID_of_l2EnergyMethod
      (intervalDomainClassicalUniquenessL2EnergyMethod_of_boundedDatumUniform p
        (intervalDomainL2UBoundedDatumUniform_of_bounded
          (boundednessHypothesis_of_uniformSupBoundZeroM hγ_ge_one
            (uniformLiftBoundZeroM_of_regime p hχ ha hb))))
  set M' : ℝ := SupNormBridge.regimeBound p M with hM'_def
  have hM' : 0 < M' := SupNormBridge.regimeBound_pos p hM
  have hSupBound : ∀ T' : ℝ, 0 < T' →
      ∀ u' v' : ℝ → intervalDomainPoint → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T' u' v' →
        InitialTrace intervalDomain u₀ u' →
        ∀ t, 0 < t → t < T' → ∀ x : intervalDomainPoint, |u' t x| ≤ M' :=
    fun T' hT' u' v' hsol' htr' =>
      SupNormBridge.interiorSupNorm_le_regimeBound p hχ ha hb
        hu₀.toPositive hM hbound hT' hsol' htr'
  obtain ⟨c, hc, hpersist⟩ :=
    hPersist u₀ hu₀.toPositive T (3 * T₁ / 8) (by linarith) (by linarith)
  obtain ⟨δc, hδc, hfactory⟩ := hThreshold M' c hM' hc
  have hseed : ∃ u' v',
      IsPaper2ClassicalSolution intervalDomain p (3 * T₁ / 4) u' v' ∧
      InitialTrace intervalDomain u₀ u' :=
    ⟨u, v, hsol.restrict_horizon (by linarith) (by linarith), htrace⟩
  have hreach := QuantFromThreshold.reaches_fixed_horizon p
    (PiecewiseClassical.piecewiseClassicalWorks p)
    TimeShift.regularityTimeShiftWorks hOverlap
    GlueExtension.timeShiftInitialTraceWorks
    hu₀.toPositive hM' hSupBound
    (δ := T) (t₁ := 3 * T₁ / 8) (T₀ := 3 * T₁ / 4)
    hT (by linarith) (by linarith) (by linarith) (by linarith)
    hc hpersist hδc (fun w hw hbw hlw => hfactory w hw hbw hlw) hseed
  obtain ⟨n, hn⟩ := exists_nat_ge ((T - 3 * T₁ / 4) / (δc / 2))
  have hδc2 : (0 : ℝ) < δc / 2 := by positivity
  have hTle : T ≤ 3 * T₁ / 4 + (n : ℝ) * (δc / 2) := by
    have := (div_le_iff₀ hδc2).mp hn
    linarith
  obtain ⟨u', v', hsol', htrace'⟩ := hreach n
  rw [min_eq_left hTle] at hsol'
  exact ⟨hT, u', v', hsol', htrace'⟩

#print axioms reachableArbitrarilyLong_ppid_of_threshold_persistence_seed

end ShenWork.Paper2.PPIDThresholdReachability
