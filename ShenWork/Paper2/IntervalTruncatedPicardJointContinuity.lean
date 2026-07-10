import ShenWork.Paper2.IntervalPositiveTimeDuhamelJointContinuity
import ShenWork.Paper2.IntervalTruncatedPicardLimitJointContinuity
import ShenWork.Paper2.IntervalDuhamelIntegrability
import Mathlib.Topology.ContinuousMap.Compact

open Filter Topology Set MeasureTheory
open scoped Topology

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint)
open ShenWork.PDE
  (intervalNeumannResolverR intervalNeumannResolverSourceCoeff
   intervalNeumannResolverWeight intervalNeumannResolverGradWeight
   intervalNeumannResolverR_sup_lipschitz
   intervalNeumannResolverR_grad_sup_lipschitz)
open ShenWork.PDE.ResolventEstimate
  (coeffL2Energy coeffL2Norm)
open ShenWork.IntervalResolverWeakBounds
  (resolverSourceCoeff_re_sq_summable_of_continuousOn
   resolverSourceCoeff_diff_re_sq_summable_of_continuousOn
   sourceCoeff_diff_energy_le_integral_of_continuousOn
   resolver_cosineSeries_summable_of_sourceL2
   resolver_sineSeries_summable_of_sourceL2)
open ShenWork.Paper2 (resolverGradReal resolverGradReal_eq)
open ShenWork.Paper2.BFormPositiveDatumNegPart
  (truncatedChemFluxLifted truncatedLogisticLifted truncatedLogisticLocal)

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-- A source-uniform version of the resolver coefficient difference estimate.
Unlike the ball lemmas, this statement does not require the input profiles to
be nonnegative; it works directly with Mathlib's signed real power. -/
theorem resolverSourceCoeff_diff_norm_le_of_source_bound
    (p : CM2Params) {u₁ u₂ : intervalDomainPoint → ℝ} {D : ℝ}
    (hg₁ : ContinuousOn
      (fun x : ℝ ↦ p.ν * intervalDomainLift u₁ x ^ p.γ) (Set.Icc 0 1))
    (hg₂ : ContinuousOn
      (fun x : ℝ ↦ p.ν * intervalDomainLift u₂ x ^ p.γ) (Set.Icc 0 1))
    (hD : 0 ≤ D)
    (hsrc : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |p.ν * intervalDomainLift u₁ x ^ p.γ -
        p.ν * intervalDomainLift u₂ x ^ p.γ| ≤ D) :
    coeffL2Norm (fun k : ℕ ↦
      intervalNeumannResolverSourceCoeff p u₁ k -
        intervalNeumannResolverSourceCoeff p u₂ k) ≤ 2 * D := by
  have hcore :=
    sourceCoeff_diff_energy_le_integral_of_continuousOn p hg₁ hg₂
  have hdiff_cont : ContinuousOn
      (fun x : ℝ ↦ p.ν * intervalDomainLift u₁ x ^ p.γ -
        p.ν * intervalDomainLift u₂ x ^ p.γ) (Set.Icc 0 1) :=
    hg₁.sub hg₂
  have hpt : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (p.ν * intervalDomainLift u₁ x ^ p.γ -
        p.ν * intervalDomainLift u₂ x ^ p.γ) ^ 2 ≤ D ^ 2 := by
    intro x hx
    have hxD := hsrc x hx
    calc
      (p.ν * intervalDomainLift u₁ x ^ p.γ -
          p.ν * intervalDomainLift u₂ x ^ p.γ) ^ 2
          = |p.ν * intervalDomainLift u₁ x ^ p.γ -
              p.ν * intervalDomainLift u₂ x ^ p.γ| ^ 2 :=
            (sq_abs _).symm
      _ ≤ D ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hxD 2
  have hint :
      (∫ x in (0 : ℝ)..1,
        (p.ν * intervalDomainLift u₁ x ^ p.γ -
          p.ν * intervalDomainLift u₂ x ^ p.γ) ^ 2) ≤ D ^ 2 := by
    have hsq_cont : ContinuousOn
        (fun x : ℝ ↦ (p.ν * intervalDomainLift u₁ x ^ p.γ -
          p.ν * intervalDomainLift u₂ x ^ p.γ) ^ 2) (Set.uIcc 0 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact hdiff_cont.pow 2
    have hsq_int : IntervalIntegrable
        (fun x : ℝ ↦ (p.ν * intervalDomainLift u₁ x ^ p.γ -
          p.ν * intervalDomainLift u₂ x ^ p.γ) ^ 2) volume 0 1 :=
      hsq_cont.intervalIntegrable
    have hconst_int : IntervalIntegrable (fun _ : ℝ ↦ D ^ 2) volume 0 1 :=
      continuous_const.intervalIntegrable 0 1
    have hmono := intervalIntegral.integral_mono_on (by norm_num)
      hsq_int hconst_int hpt
    simpa using hmono
  have henergy :
      coeffL2Energy (fun k : ℕ ↦
        intervalNeumannResolverSourceCoeff p u₁ k -
          intervalNeumannResolverSourceCoeff p u₂ k) ≤ (2 * D) ^ 2 := by
    calc
      coeffL2Energy (fun k : ℕ ↦
          intervalNeumannResolverSourceCoeff p u₁ k -
            intervalNeumannResolverSourceCoeff p u₂ k)
          ≤ 4 * ∫ x in (0 : ℝ)..1,
              (p.ν * intervalDomainLift u₁ x ^ p.γ -
                p.ν * intervalDomainLift u₂ x ^ p.γ) ^ 2 := hcore
      _ ≤ 4 * D ^ 2 := mul_le_mul_of_nonneg_left hint (by norm_num)
      _ = (2 * D) ^ 2 := by ring
  rw [coeffL2Norm]
  calc
    Real.sqrt (coeffL2Energy (fun k : ℕ ↦
        intervalNeumannResolverSourceCoeff p u₁ k -
          intervalNeumannResolverSourceCoeff p u₂ k))
        ≤ Real.sqrt ((2 * D) ^ 2) := Real.sqrt_le_sqrt henergy
    _ = 2 * D := Real.sqrt_sq (mul_nonneg (by norm_num) hD)

/-- Resolver value differences are uniformly controlled by a uniform bound on
the signed elliptic source difference. -/
theorem resolverValue_diff_sup_le_of_source_bound
    (p : CM2Params) {u₁ u₂ : intervalDomainPoint → ℝ} {D : ℝ}
    (hu₁ : ContinuousOn (intervalDomainLift u₁) (Set.Icc 0 1))
    (hu₂ : ContinuousOn (intervalDomainLift u₂) (Set.Icc 0 1))
    (hD : 0 ≤ D)
    (hsrc : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |p.ν * intervalDomainLift u₁ x ^ p.γ -
        p.ν * intervalDomainLift u₂ x ^ p.γ| ≤ D)
    (x : intervalDomainPoint) :
    |intervalNeumannResolverR p u₁ x - intervalNeumannResolverR p u₂ x| ≤
      Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) *
        (2 * D) := by
  have hg₁ : ContinuousOn
      (fun y : ℝ ↦ p.ν * intervalDomainLift u₁ y ^ p.γ) (Set.Icc 0 1) :=
    continuousOn_const.mul (hu₁.rpow_const (fun _ _ ↦ Or.inr p.hγ.le))
  have hg₂ : ContinuousOn
      (fun y : ℝ ↦ p.ν * intervalDomainLift u₂ y ^ p.γ) (Set.Icc 0 1) :=
    continuousOn_const.mul (hu₂.rpow_const (fun _ _ ↦ Or.inr p.hγ.le))
  have hdiff := resolverSourceCoeff_diff_re_sq_summable_of_continuousOn p hu₁ hu₂
  have hl₁ : Summable fun k : ℕ ↦
      ((intervalNeumannResolverSourceCoeff p u₁ k).re) ^ 2 := by
    simpa [ShenWork.Paper2.intervalNeumannResolverSourceCoeff_zero, sub_zero] using
      resolverSourceCoeff_re_sq_summable_of_continuousOn p hu₁
  have hl₂ : Summable fun k : ℕ ↦
      ((intervalNeumannResolverSourceCoeff p u₂ k).re) ^ 2 := by
    simpa [ShenWork.Paper2.intervalNeumannResolverSourceCoeff_zero, sub_zero] using
      resolverSourceCoeff_re_sq_summable_of_continuousOn p hu₂
  have hbound := intervalNeumannResolverR_sup_lipschitz p u₁ u₂ hdiff x
    (resolver_cosineSeries_summable_of_sourceL2 p hl₁ x.1)
    (resolver_cosineSeries_summable_of_sourceL2 p hl₂ x.1)
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (resolverSourceCoeff_diff_norm_le_of_source_bound p hg₁ hg₂ hD hsrc)
    (Real.sqrt_nonneg _))

/-- Resolver gradient differences are uniformly controlled by a uniform bound
on the signed elliptic source difference. -/
theorem resolverGrad_diff_sup_le_of_source_bound
    (p : CM2Params) {u₁ u₂ : intervalDomainPoint → ℝ} {D : ℝ}
    (hu₁ : ContinuousOn (intervalDomainLift u₁) (Set.Icc 0 1))
    (hu₂ : ContinuousOn (intervalDomainLift u₂) (Set.Icc 0 1))
    (hD : 0 ≤ D)
    (hsrc : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |p.ν * intervalDomainLift u₁ x ^ p.γ -
        p.ν * intervalDomainLift u₂ x ^ p.γ| ≤ D)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |resolverGradReal p u₁ x - resolverGradReal p u₂ x| ≤
      Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * D) := by
  have hg₁ : ContinuousOn
      (fun y : ℝ ↦ p.ν * intervalDomainLift u₁ y ^ p.γ) (Set.Icc 0 1) :=
    continuousOn_const.mul (hu₁.rpow_const (fun _ _ ↦ Or.inr p.hγ.le))
  have hg₂ : ContinuousOn
      (fun y : ℝ ↦ p.ν * intervalDomainLift u₂ y ^ p.γ) (Set.Icc 0 1) :=
    continuousOn_const.mul (hu₂.rpow_const (fun _ _ ↦ Or.inr p.hγ.le))
  have hdiff := resolverSourceCoeff_diff_re_sq_summable_of_continuousOn p hu₁ hu₂
  have hl₁ : Summable fun k : ℕ ↦
      ((intervalNeumannResolverSourceCoeff p u₁ k).re) ^ 2 := by
    simpa [ShenWork.Paper2.intervalNeumannResolverSourceCoeff_zero, sub_zero] using
      resolverSourceCoeff_re_sq_summable_of_continuousOn p hu₁
  have hl₂ : Summable fun k : ℕ ↦
      ((intervalNeumannResolverSourceCoeff p u₂ k).re) ^ 2 := by
    simpa [ShenWork.Paper2.intervalNeumannResolverSourceCoeff_zero, sub_zero] using
      resolverSourceCoeff_re_sq_summable_of_continuousOn p hu₂
  have hbound := intervalNeumannResolverR_grad_sup_lipschitz p u₁ u₂ hdiff
    ⟨x, hx⟩
    (resolver_sineSeries_summable_of_sourceL2 p hl₁ x)
    (resolver_sineSeries_summable_of_sourceL2 p hl₂ x)
  rw [resolverGradReal_eq p u₁ ⟨x, hx⟩, resolverGradReal_eq p u₂ ⟨x, hx⟩]
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (resolverSourceCoeff_diff_norm_le_of_source_bound p hg₁ hg₂ hD hsrc)
    (Real.sqrt_nonneg _))

private theorem continuous_of_dist_le_const_mul
    {α β γ : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    [PseudoMetricSpace γ] {f : α → β} {g : α → γ} {C : ℝ}
    (hg : Continuous g) (hC : 0 ≤ C)
    (hfg : ∀ a b, dist (f a) (f b) ≤ C * dist (g a) (g b)) :
    Continuous f := by
  rw [continuous_iff_continuousAt]
  intro a
  rw [Metric.continuousAt_iff]
  intro ε hε
  by_cases hC0 : C = 0
  · refine ⟨1, by norm_num, ?_⟩
    intro b _hb
    have hab := hfg b a
    rw [hC0, zero_mul] at hab
    exact lt_of_le_of_lt hab hε
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    obtain ⟨δ, hδpos, hδ⟩ :=
      (Metric.continuousAt_iff.mp hg.continuousAt) (ε / C) (div_pos hε hCpos)
    refine ⟨δ, hδpos, ?_⟩
    intro b hb
    have hmul := (lt_div_iff₀ hCpos).1 (hδ hb)
    exact (hfg b a).trans_lt (by simpa [mul_comm] using hmul)

/-- Joint continuity of both signed resolver fields on a closed time-space
slab.  The proof curries the jointly continuous signed source into the compact
sup-norm space and uses the uniform resolver difference estimates above. -/
theorem resolverValueGrad_jointContinuousOn_Icc
    (p : CM2Params) {w : ℝ → intervalDomainPoint → ℝ} {lo hi : ℝ}
    (hw : ContinuousOn
      (fun q : ℝ × ℝ ↦ intervalDomainLift (w q.1) q.2)
      (Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn
        (fun q : ℝ × ℝ ↦
          intervalDomainLift (intervalNeumannResolverR p (w q.1)) q.2)
        (Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1) ∧
      ContinuousOn
        (fun q : ℝ × ℝ ↦ resolverGradReal p (w q.1) q.2)
        (Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1) := by
  let A := ↑(Set.Icc lo hi)
  let X := ↑(Set.Icc (0 : ℝ) 1)
  have hw_slice (t : A) :
      ContinuousOn (intervalDomainLift (w t.1)) (Set.Icc (0 : ℝ) 1) := by
    exact hw.comp (continuousOn_const.prodMk continuousOn_id) (fun x hx ↦ ⟨t.2, hx⟩)
  have hsrc_joint : ContinuousOn
      (fun q : ℝ × ℝ ↦ p.ν * intervalDomainLift (w q.1) q.2 ^ p.γ)
      (Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.mul (hw.rpow_const (fun _ _ ↦ Or.inr p.hγ.le))
  let G : A → C(X, ℝ) := fun t ↦
    ⟨fun x ↦ p.ν * intervalDomainLift (w t.1) x.1 ^ p.γ,
      (continuousOn_const.mul
        ((hw_slice t).rpow_const (fun _ _ ↦ Or.inr p.hγ.le))).comp_continuous
          continuous_subtype_val (fun x ↦ x.2)⟩
  have hG_uncurry : Continuous (Function.uncurry fun t x ↦ G t x) := by
    have hcomp := hsrc_joint.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
      (fun q : A × X ↦ ⟨q.1.2, q.2.2⟩)
    simpa [G, Function.uncurry] using hcomp
  have hG : Continuous G :=
    ContinuousMap.continuous_of_continuous_uncurry G hG_uncurry
  let V : A → C(X, ℝ) := fun t ↦
    ⟨fun x ↦ intervalNeumannResolverR p (w t.1) ⟨x.1, x.2⟩,
      by
        have h :=
          ShenWork.IntervalDuhamelIntegrability.resolverValueReal_continuous_of_continuousOn
            p (hw_slice t)
        simpa [intervalNeumannResolverR] using h.comp continuous_subtype_val⟩
  let W : A → C(X, ℝ) := fun t ↦
    ⟨fun x ↦ resolverGradReal p (w t.1) x.1,
      (resolverGradReal_continuous_of_continuousOn p (hw_slice t)).comp
        continuous_subtype_val⟩
  set Cᵥ : ℝ :=
    2 * Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2)
  set Cₓ : ℝ :=
    2 * Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2)
  have hCᵥ : 0 ≤ Cᵥ := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hCₓ : 0 ≤ Cₓ := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hVdist : ∀ a b, dist (V a) (V b) ≤ Cᵥ * dist (G a) (G b) := by
    intro a b
    rw [dist_eq_norm, dist_eq_norm]
    apply (ContinuousMap.norm_le _ (mul_nonneg hCᵥ (norm_nonneg _))).2
    intro x
    rw [Real.norm_eq_abs]
    have hsrc : ∀ y ∈ Set.Icc (0 : ℝ) 1,
        |p.ν * intervalDomainLift (w a.1) y ^ p.γ -
          p.ν * intervalDomainLift (w b.1) y ^ p.γ| ≤ ‖G a - G b‖ := by
      intro y hy
      have hnorm := ContinuousMap.norm_coe_le_norm (G a - G b) ⟨y, hy⟩
      simpa [G, Real.norm_eq_abs] using hnorm
    have h := resolverValue_diff_sup_le_of_source_bound p
      (hw_slice a) (hw_slice b) (norm_nonneg (G a - G b)) hsrc ⟨x.1, x.2⟩
    change |intervalNeumannResolverR p (w a.1) ⟨x.1, x.2⟩ -
      intervalNeumannResolverR p (w b.1) ⟨x.1, x.2⟩| ≤ Cᵥ * ‖G a - G b‖
    calc
      |intervalNeumannResolverR p (w a.1) ⟨x.1, x.2⟩ -
          intervalNeumannResolverR p (w b.1) ⟨x.1, x.2⟩|
          ≤ Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) *
              (2 * ‖G a - G b‖) := h
      _ = Cᵥ * ‖G a - G b‖ := by rw [show Cᵥ = _ from rfl]; ring
  have hWdist : ∀ a b, dist (W a) (W b) ≤ Cₓ * dist (G a) (G b) := by
    intro a b
    rw [dist_eq_norm, dist_eq_norm]
    apply (ContinuousMap.norm_le _ (mul_nonneg hCₓ (norm_nonneg _))).2
    intro x
    rw [Real.norm_eq_abs]
    have hsrc : ∀ y ∈ Set.Icc (0 : ℝ) 1,
        |p.ν * intervalDomainLift (w a.1) y ^ p.γ -
          p.ν * intervalDomainLift (w b.1) y ^ p.γ| ≤ ‖G a - G b‖ := by
      intro y hy
      have hnorm := ContinuousMap.norm_coe_le_norm (G a - G b) ⟨y, hy⟩
      simpa [G, Real.norm_eq_abs] using hnorm
    have h := resolverGrad_diff_sup_le_of_source_bound p
      (hw_slice a) (hw_slice b) (norm_nonneg (G a - G b)) hsrc x.2
    change |resolverGradReal p (w a.1) x.1 - resolverGradReal p (w b.1) x.1| ≤
      Cₓ * ‖G a - G b‖
    calc
      |resolverGradReal p (w a.1) x.1 - resolverGradReal p (w b.1) x.1|
          ≤ Real.sqrt
              (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
                (2 * ‖G a - G b‖) := h
      _ = Cₓ * ‖G a - G b‖ := by rw [show Cₓ = _ from rfl]; ring
  have hV : Continuous V := continuous_of_dist_le_const_mul hG hCᵥ hVdist
  have hW : Continuous W := continuous_of_dist_le_const_mul hG hCₓ hWdist
  let toSub : ↑(Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1) → A × X := fun q ↦
    (⟨q.1.1, q.2.1⟩, ⟨q.1.2, q.2.2⟩)
  have htoSub : Continuous toSub := by
    apply Continuous.prodMk
    · exact Continuous.subtype_mk continuous_subtype_val.fst _
    · exact Continuous.subtype_mk continuous_subtype_val.snd _
  constructor
  · rw [continuousOn_iff_continuous_restrict]
    have huncurry := ContinuousMap.continuous_uncurry_of_continuous ⟨V, hV⟩
    have hcomp := huncurry.comp htoSub
    rw [show
      Set.restrict (Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1)
          (fun q : ℝ × ℝ ↦
            intervalDomainLift (intervalNeumannResolverR p (w q.1)) q.2) =
        (Function.uncurry fun t x ↦ V t x) ∘ toSub by
      funext q
      simp [Set.restrict, toSub, V, intervalDomainLift, q.2.2]
      congr]
    exact hcomp
  · rw [continuousOn_iff_continuous_restrict]
    have huncurry := ContinuousMap.continuous_uncurry_of_continuous ⟨W, hW⟩
    have hcomp := huncurry.comp htoSub
    simpa [Set.restrict, toSub, W] using hcomp

/-- Positive-time version of `resolverValueGrad_jointContinuousOn_Icc`,
obtained by closing a smaller time window around each positive base point. -/
theorem resolverValueGrad_jointContinuousOn_Ioc
    (p : CM2Params) {w : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hw : ContinuousOn
      (fun q : ℝ × ℝ ↦ intervalDomainLift (w q.1) q.2)
      (Set.Ioc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn
        (fun q : ℝ × ℝ ↦
          intervalDomainLift (intervalNeumannResolverR p (w q.1)) q.2)
        (Set.Ioc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) ∧
      ContinuousOn
        (fun q : ℝ × ℝ ↦ resolverGradReal p (w q.1) q.2)
        (Set.Ioc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
  let S : Set (ℝ × ℝ) :=
    Set.Ioc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1
  have hlocal (q : ℝ × ℝ) (hq : q ∈ S) :
      ∃ a : ℝ, 0 < a ∧ q.1 ∈ Set.Icc a T ∧
        Set.Icc a T ×ˢ Set.Icc (0 : ℝ) 1 ∈ nhdsWithin q S := by
    set a : ℝ := q.1 / 2
    have ha : 0 < a := by
      dsimp [a]
      linarith [hq.1.1]
    have hqa : q.1 ∈ Set.Icc a T :=
      ⟨by dsimp [a]; linarith [hq.1.1], hq.1.2⟩
    have ha_lt_q : a < q.1 := by
      dsimp [a]
      linarith [hq.1.1]
    have hopen : Set.Ioi a ×ˢ (Set.univ : Set ℝ) ∈ nhds q :=
      (isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ha_lt_q, trivial⟩
    have hinter : S ∩ (Set.Ioi a ×ˢ (Set.univ : Set ℝ)) ∈ nhdsWithin q S :=
      inter_mem_nhdsWithin _ hopen
    refine ⟨a, ha, hqa, mem_of_superset hinter ?_⟩
    intro z hz
    exact ⟨⟨le_of_lt hz.2.1, hz.1.1.2⟩, hz.1.2⟩
  constructor
  · intro q hq
    have hqS : q ∈ S := by simpa [S] using hq
    obtain ⟨a, ha, hqa, hnh⟩ := hlocal q hqS
    have hsub : Set.Icc a T ×ˢ Set.Icc (0 : ℝ) 1 ⊆ S := by
      intro z hz
      exact ⟨⟨lt_of_lt_of_le ha hz.1.1, hz.1.2⟩, hz.2⟩
    have hclosed := (resolverValueGrad_jointContinuousOn_Icc p
      (hw.mono (by simpa [S] using hsub))).1
    exact (hclosed q ⟨hqa, hq.2⟩).mono_of_mem_nhdsWithin (by simpa [S] using hnh)
  · intro q hq
    have hqS : q ∈ S := by simpa [S] using hq
    obtain ⟨a, ha, hqa, hnh⟩ := hlocal q hqS
    have hsub : Set.Icc a T ×ˢ Set.Icc (0 : ℝ) 1 ⊆ S := by
      intro z hz
      exact ⟨⟨lt_of_lt_of_le ha hz.1.1, hz.1.2⟩, hz.2⟩
    have hclosed := (resolverValueGrad_jointContinuousOn_Icc p
      (hw.mono (by simpa [S] using hsub))).2
    exact (hclosed q ⟨hqa, hq.2⟩).mono_of_mem_nhdsWithin (by simpa [S] using hnh)

/-- The faithful truncated logistic source preserves joint continuity. -/
theorem truncatedLogisticLifted_jointContinuousOn
    (p : CM2Params) {w : ℝ → intervalDomainPoint → ℝ} {S : Set (ℝ × ℝ)}
    (hw : ContinuousOn
      (fun q : ℝ × ℝ ↦ intervalDomainLift (w q.1) q.2) S) :
    ContinuousOn (fun q : ℝ × ℝ ↦
      truncatedLogisticLifted p (w q.1) q.2) S := by
  have hpos : ContinuousOn
      (fun q : ℝ × ℝ ↦ positivePart (intervalDomainLift (w q.1) q.2)) S := by
    simpa [positivePart] using ContinuousOn.sup hw continuousOn_const
  have hpow : ContinuousOn
      (fun q : ℝ × ℝ ↦
        positivePart (intervalDomainLift (w q.1) q.2) ^ p.α) S :=
    hpos.rpow_const (fun _ _ ↦ Or.inr p.hα.le)
  simpa [truncatedLogisticLifted, truncatedLogisticLocal] using
    hw.mul (continuousOn_const.sub (continuousOn_const.mul hpow))

/-- Conditional joint continuity of the faithful truncated chemotaxis flux.
The strict denominator condition is stated explicitly because the truncated
definition keeps the signed resolver source; it is not a consequence of slice
continuity alone. -/
theorem truncatedChemFluxLifted_jointContinuousOn_Ioc
    (p : CM2Params) {w : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hw : ContinuousOn
      (fun q : ℝ × ℝ ↦ intervalDomainLift (w q.1) q.2)
      (Set.Ioc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1))
    (hden : ∀ q ∈ Set.Ioc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1,
      0 < 1 + intervalDomainLift (intervalNeumannResolverR p (w q.1)) q.2) :
    ContinuousOn (fun q : ℝ × ℝ ↦
      truncatedChemFluxLifted p (w q.1) q.2)
      (Set.Ioc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hR := resolverValueGrad_jointContinuousOn_Ioc p hw
  have hpos : ContinuousOn
      (fun q : ℝ × ℝ ↦ positivePart (intervalDomainLift (w q.1) q.2))
      (Set.Ioc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
    simpa [positivePart] using ContinuousOn.sup hw continuousOn_const
  have hbase : ContinuousOn
      (fun q : ℝ × ℝ ↦
        1 + intervalDomainLift (intervalNeumannResolverR p (w q.1)) q.2)
      (Set.Ioc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.add hR.1
  have hpow : ContinuousOn
      (fun q : ℝ × ℝ ↦
        (1 + intervalDomainLift (intervalNeumannResolverR p (w q.1)) q.2) ^ p.β)
      (Set.Ioc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    hbase.rpow_const (fun _ _ ↦ Or.inr p.hβ)
  have hne : ∀ q ∈ Set.Ioc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1,
      (1 + intervalDomainLift (intervalNeumannResolverR p (w q.1)) q.2) ^ p.β ≠ 0 :=
    fun q hq ↦ ne_of_gt (Real.rpow_pos_of_pos (hden q hq) p.β)
  simpa [truncatedChemFluxLifted] using (hpos.mul hR.2).div hpow hne

end ShenWork.Paper2.BFormPositiveDatumNegPart
