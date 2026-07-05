import ShenWork.PDE.P3MoserDxJointContinuity
import ShenWork.PDE.P3MoserGradientIntegrability
import ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Strict-window continuity of the interval-domain Moser gradient energy

This file upgrades the closed-slab joint continuity of `u` and `u_x` on
`(0,T) × [0,1]` to strict-window continuity of the Moser gradient energy.
-/

open MeasureTheory Set Filter
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open scoped Interval Topology

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserGradientIntegrability

local instance : TopologicalSpace intervalDomain.Point :=
  inferInstanceAs (TopologicalSpace intervalDomainPoint)

/-- If an integrand is jointly continuous on `[a,b] × [0,1]`, then its integral
over `[0,1]` is continuous in the parameter on `[a,b]`. -/
lemma continuousOn_intervalIntegral_zero_one_of_continuousOn_Icc_prod
    {F : ℝ → ℝ → ℝ} {a b : ℝ}
    (hFcont :
      ContinuousOn (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (fun s => ∫ y in (0 : ℝ)..1, F s y) (Set.Icc a b) := by
  let I : Set ℝ := Set.Icc a b
  let K : Set (ℝ × ℝ) := I ×ˢ Set.Icc (0 : ℝ) 1
  have hKcompact : IsCompact K := by
    dsimp [K, I]
    exact isCompact_Icc.prod isCompact_Icc
  have hFcontI : ContinuousOn (Function.uncurry F) K := by
    simpa [K, I] using hFcont
  obtain ⟨B, hB⟩ := hKcompact.bddAbove_image hFcontI.norm
  set B' : ℝ := max B 0 with hB'def
  have hFbd : ∀ s ∈ I, ∀ y ∈ Set.Icc (0 : ℝ) 1, ‖F s y‖ ≤ B' := by
    intro s hs y hy
    have hBy : ‖Function.uncurry F (s, y)‖ ≤ B :=
      hB (Set.mem_image_of_mem _ (Set.mem_prod.mpr ⟨hs, hy⟩))
    exact le_trans hBy (le_max_left _ _)
  have hslice_cont : ∀ s ∈ I, ContinuousOn (F s) (Set.Icc (0 : ℝ) 1) := by
    intro s hs
    have hmaps : Set.MapsTo (fun y : ℝ => ((s, y) : ℝ × ℝ))
        (Set.Icc (0 : ℝ) 1) K := by
      intro y hy
      exact Set.mem_prod.mpr ⟨hs, hy⟩
    have hpair_cont : ContinuousOn (fun y : ℝ => ((s, y) : ℝ × ℝ))
        (Set.Icc (0 : ℝ) 1) :=
      continuousOn_const.prodMk continuousOn_id
    have hcomp :
        ContinuousOn
          ((Function.uncurry F) ∘ fun y : ℝ => ((s, y) : ℝ × ℝ))
          (Set.Icc (0 : ℝ) 1) :=
      hFcontI.comp hpair_cont hmaps
    simpa [Function.comp_def, Function.uncurry] using hcomp
  have hcontI :
      ContinuousOn (fun s => ∫ y in (0 : ℝ)..1, F s y) I := by
    intro s₀ hs₀
    refine intervalIntegral.continuousWithinAt_of_dominated_interval
      (bound := fun _y : ℝ => B') ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hs_cont_uIcc : ContinuousOn (F s) (Set.uIcc (0 : ℝ) 1) := by
        rw [Set.uIcc_of_le zero_le_one]
        exact hslice_cont s hs
      exact
        (hs_cont_uIcc.mono Set.uIoc_subset_uIcc).aestronglyMeasurable
          measurableSet_uIoc
    · filter_upwards [self_mem_nhdsWithin] with s hs
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      rw [Set.uIoc_of_le zero_le_one] at hy
      exact hFbd s hs y ⟨hy.1.le, hy.2⟩
    · refine Filter.Eventually.of_forall (fun y hy => ?_)
      rw [Set.uIoc_of_le zero_le_one] at hy
      have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2⟩
      have hparam_cont : ContinuousWithinAt (fun s => F s y) I s₀ := by
        have hmaps : Set.MapsTo (fun s : ℝ => ((s, y) : ℝ × ℝ))
            I K := by
          intro s hs
          exact Set.mem_prod.mpr ⟨hs, hyIcc⟩
        have hpair_cont : ContinuousOn (fun s : ℝ => ((s, y) : ℝ × ℝ)) I :=
          continuousOn_id.prodMk continuousOn_const
        have hcomp :
            ContinuousOn
              ((Function.uncurry F) ∘ fun s : ℝ => ((s, y) : ℝ × ℝ)) I :=
          hFcontI.comp hpair_cont hmaps
        simpa [Function.comp_def, Function.uncurry] using
          hcomp.continuousWithinAt hs₀
      exact hparam_cont
  simpa [I] using hcontI

/-- Strict-window continuity of the weighted gradient dissipation
`∫ u^(p-2) |u_x|^2` from joint continuity of `u` and `u_x`. -/
theorem intervalDomain_weightedGradientDissipation_continuousOn_Icc_of_classical
    {params : CM2Params} {T p a b : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ha : 0 < a) (_hab : a ≤ b) (hb : b < T) :
    ContinuousOn
      (fun t => intervalDomainLpWeightedGradientDissipation p u t)
      (Set.Icc a b) := by
  let I : Set ℝ := Set.Icc a b
  let K : Set (ℝ × ℝ) := I ×ˢ Set.Icc (0 : ℝ) 1
  have hsub : K ⊆ Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1 := by
    intro z hz
    exact ⟨⟨lt_of_lt_of_le ha hz.1.1, lt_of_le_of_lt hz.1.2 hb⟩, hz.2⟩
  have hu_cont :
      ContinuousOn
        (fun z : ℝ × ℝ => intervalDomainLift (u z.1) z.2)
        K := by
    have hreg := hsol.regularity
    change intervalDomainClassicalRegularity T u v at hreg
    exact hreg.2.2.2.2.2.2.1.mono hsub
  have hdx_cont :
      ContinuousOn
        (fun z : ℝ × ℝ => deriv (intervalDomainLift (u z.1)) z.2)
        K := by
    exact (intervalDomain_dx_u_jointlyContinuous hsol).mono hsub
  have hu_pos :
      ∀ z ∈ K, 0 < intervalDomainLift (u z.1) z.2 := by
    intro z hz
    exact intervalDomain_solution_lift_u_pos hsol
      (lt_of_lt_of_le ha hz.1.1) (lt_of_le_of_lt hz.1.2 hb) hz.2
  set F : ℝ → ℝ → ℝ :=
    fun s y =>
      (intervalDomainLift (u s) y) ^ (p - 2) *
        |deriv (intervalDomainLift (u s)) y| ^ 2 with hFdef
  have hFcont :
      ContinuousOn (Function.uncurry F) K := by
    have hpow :
        ContinuousOn
          (fun z : ℝ × ℝ => (intervalDomainLift (u z.1) z.2) ^ (p - 2))
          K :=
      hu_cont.rpow_const (fun z hz => Or.inl (ne_of_gt (hu_pos z hz)))
    have hdx_sq :
        ContinuousOn
          (fun z : ℝ × ℝ => |deriv (intervalDomainLift (u z.1)) z.2| ^ 2)
          K := by
      exact (continuous_abs.comp_continuousOn hdx_cont).pow 2
    simpa [F, Function.uncurry] using hpow.mul hdx_sq
  have hint_cont :
      ContinuousOn (fun s => ∫ y in (0 : ℝ)..1, F s y) I :=
    continuousOn_intervalIntegral_zero_one_of_continuousOn_Icc_prod
      (a := a) (b := b) hFcont
  have hprofile :
      ∀ s, intervalDomainLpWeightedGradientDissipation p u s =
        ∫ y in (0 : ℝ)..1, F s y := by
    intro s
    unfold intervalDomainLpWeightedGradientDissipation
    change intervalDomainIntegral _ = _
    unfold intervalDomainIntegral
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    rw [Set.uIcc_of_le zero_le_one] at hy
    change
      intervalDomainLift
          (fun x : intervalDomain.Point =>
            (u s x) ^ (p - 2) * (intervalDomain.gradNorm (u s) x) ^ 2) y =
        F s y
    have hy01 : 0 ≤ y ∧ y ≤ 1 := hy
    simp [F, intervalDomain, intervalDomainLift, intervalDomainGradNorm, hy01, sq_abs]
  exact hint_cont.congr (fun s _hs => hprofile s)

/-- A positive classical interval-domain solution has strict-window continuity
of every Moser gradient energy with exponent at least `p0`, provided `2 ≤ p0`.
-/
theorem intervalDomain_moserGradientStrictWindowContinuity_of_classical
    {params : CM2Params} {T : ℝ} {p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hp0 : 2 ≤ p0) :
    IntervalDomainMoserGradientStrictWindowContinuity u T p0 := by
  intro p hp a b ha hab hb
  have _hp2 : 2 ≤ p := le_trans hp0 hp
  have hweighted :
      ContinuousOn
        (fun t => intervalDomainLpWeightedGradientDissipation p u t)
        (Set.Icc a b) :=
    intervalDomain_weightedGradientDissipation_continuousOn_Icc_of_classical
      (p := p) hsol ha hab hb
  have hscaled :
      ContinuousOn
        (fun t => (p / 2) ^ 2 *
          intervalDomainLpWeightedGradientDissipation p u t)
        (Set.Icc a b) :=
    hweighted.const_mul ((p / 2) ^ 2)
  refine hscaled.congr ?_
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
  have htT : t < T := lt_of_le_of_lt ht.2 hb
  exact
    intervalDomain_moser_gradient_integral_eq_weighted_of_regularity
      (pExp := p) hsol ht0 htT

/-- Strict-window integrability follows from strict-window continuity. -/
theorem intervalDomain_moserGradientStrictWindowIntegrability_of_classical
    {params : CM2Params} {T : ℝ} {p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hp0 : 2 ≤ p0) :
    IntervalDomainMoserGradientStrictWindowIntegrability u T p0 :=
  intervalDomain_moserGradientStrictWindowIntegrable_of_continuous
    (intervalDomain_moserGradientStrictWindowContinuity_of_classical hsol hp0)

/-- The same strict-window integrability in the `integratedMoserGradientEnergy`
shape used as `hG_int` downstream. -/
theorem intervalDomain_gradientIntegrability_of_classical
    {params : CM2Params} {T : ℝ} {p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hp0 : 2 ≤ p0) :
    ∀ p, p0 ≤ p → ∀ a b, 0 < a → a ≤ b → b < T →
      IntervalIntegrable
        (fun s => integratedMoserGradientEnergy intervalDomain u p s)
        volume a b := by
  intro p hp a b ha hab hb
  have h :=
    intervalDomain_moserGradientStrictWindowIntegrability_of_classical
      hsol hp0 p hp a b ha hab hb
  simpa [intervalDomainMoserGradientEnergy, integratedMoserGradientEnergy] using h

end ShenWork.IntervalDomainExistence.P3MoserGradientIntegrability

end
