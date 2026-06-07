/-
  Time-shift autonomy for IsPaper2ClassicalSolution.

  The PDE is autonomous, so time-shifting preserves classical solutions.
  The regularity time-shift is taken as a hypothesis (it's a tedious but
  straightforward field-by-field verification).

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainUniformContinuation

open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.TimeShift

/-- Helper: shifting `t ↦ t + τ` preserves `IntervalDomainSupNormDerivativeNonposOn`
when we shrink the domain from `I_orig` to the pre-shifted set. -/
private lemma supNormDerivNonposOn_timeShift
    {u : ℝ → intervalDomainPoint → ℝ} {I : Set ℝ} {τ : ℝ}
    (h : IntervalDomainSupNormDerivativeNonposOn u I)
    {J : Set ℝ} (hJI : Set.MapsTo (· + τ) J I)
    (hJI_int : Set.MapsTo (· + τ) (interior J) (interior I)) :
    IntervalDomainSupNormDerivativeNonposOn (fun t x => u (t + τ) x) J := by
  -- The sup-norm of (fun t x => u (t+τ) x) at time t is intervalDomainSupNorm (u (t+τ))
  -- (definitional equality by beta/eta).
  -- We use h.continuousOn, h.differentiableOn, h.deriv_nonpos composed with (· + τ).
  refine ⟨?_, ?_, ?_⟩
  · -- ContinuousOn: (fun t => supNorm (u (t+τ))) = (fun t => supNorm (u t)) ∘ (·+τ)
    exact h.continuousOn.comp (continuous_add_const τ).continuousOn hJI
  · -- DifferentiableOn: same composition
    exact h.differentiableOn.comp
      (differentiableOn_id.add_const τ) hJI_int
  · -- deriv ≤ 0: chain rule gives deriv(supNorm∘u∘(·+τ)) t = deriv(supNorm∘u) (t+τ)
    intro t ht
    have heq : deriv (fun s => intervalDomainSupNorm (u (s + τ))) t =
               deriv (fun s => intervalDomainSupNorm (u s)) (t + τ) :=
      deriv_comp_add_const (f := fun s => intervalDomainSupNorm (u s)) (a := τ) t
    exact heq ▸ h.deriv_nonpos (t + τ) (hJI_int ht)

/-- The regularity time-shift hypothesis: shifting `t ↦ t + τ` preserves
the 9 regularity conjuncts. Each conjunct is either spatial-only
(trivial) or involves time derivatives (chain rule). -/
def RegularityTimeShiftWorks : Prop :=
  ∀ {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ},
    intervalDomainClassicalRegularity T u v →
  ∀ {τ : ℝ}, 0 < τ → τ < T →
    intervalDomainClassicalRegularity (T - τ)
      (fun t x => u (t + τ) x) (fun t x => v (t + τ) x)

/-- **Proof that `RegularityTimeShiftWorks`**: the time-shift `t ↦ t + τ`
preserves all 7 conjuncts of `intervalDomainClassicalRegularity`. -/
theorem regularityTimeShiftWorks : RegularityTimeShiftWorks := by
  intro T u v hreg τ hτ_pos hτ_lt
  obtain ⟨h3, h4, h5, h6, h7, h8, h9⟩ := hreg
  -- Membership translation: t ∈ Ioo 0 (T-τ) → t+τ ∈ Ioo 0 T
  have mem_shift : ∀ t, t ∈ Set.Ioo (0 : ℝ) (T - τ) → t + τ ∈ Set.Ioo (0 : ℝ) T := by
    intro t ht; exact ⟨by linarith [ht.1, hτ_pos], by linarith [ht.2]⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (3) Spatial C² on Ioo 0 1
    intro t ht
    exact h3 (t + τ) (mem_shift t ht)
  · -- (4) Closed-domain time C¹
    intro x t ht
    obtain ⟨⟨hdiffU, hdiffV⟩, hcontU, hcontV⟩ := h4 x (t + τ) (mem_shift t ht)
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · -- DifferentiableAt u-shift: goal has (fun s => u(s+τ) x) by beta
      exact differentiableAt_comp_add_const.mpr hdiffU
    · exact differentiableAt_comp_add_const.mpr hdiffV
    · -- ContinuousOn deriv of u-shift
      -- goal: ContinuousOn (fun s => deriv (fun r => u(r+τ) x) s) (Ioo 0 (T-τ))
      -- by beta reduction from (fun r => (fun t' x' => u(t'+τ) x') r x)
      show ContinuousOn (fun s => deriv (fun r => u (r + τ) x) s) (Set.Ioo 0 (T - τ))
      rw [funext (fun s => deriv_comp_add_const (f := fun r => u r x) (a := τ) s)]
      exact hcontU.comp (continuous_add_const τ).continuousOn
        (fun t' ht' => mem_shift t' ht')
    · show ContinuousOn (fun s => deriv (fun r => v (r + τ) x) s) (Set.Ioo 0 (T - τ))
      rw [funext (fun s => deriv_comp_add_const (f := fun r => v r x) (a := τ) s)]
      exact hcontV.comp (continuous_add_const τ).continuousOn
        (fun t' ht' => mem_shift t' ht')
  · -- (5) Joint ∂ₜ continuity on Ioo 0 (T-τ) ×ˢ Ioo 0 1
    obtain ⟨hjU, hjV⟩ := h5
    refine ⟨?_, ?_⟩
    · -- u: goal is ContinuousOn (uncurry (fun t x => deriv(fun s => lift(u(s+τ)) x) t)) S
      show ContinuousOn
        (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
          deriv (fun s : ℝ => intervalDomainLift (u (s + τ)) x) t))
        (Set.Ioo 0 (T - τ) ×ˢ Set.Ioo 0 1)
      have heq : (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
              deriv (fun s : ℝ => intervalDomainLift (u (s + τ)) x) t)) =
            (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
              deriv (fun s : ℝ => intervalDomainLift (u s) x) t)) ∘ Prod.map (· + τ) id := by
        ext ⟨t, x⟩
        simp only [Function.uncurry, Prod.map, id]
        exact deriv_comp_add_const (f := fun s => intervalDomainLift (u s) x) (a := τ) t
      rw [heq]
      exact hjU.comp (Continuous.continuousOn (by fun_prop))
        (fun ⟨t, x⟩ ⟨ht, hx⟩ => ⟨mem_shift t ht, hx⟩)
    · show ContinuousOn
        (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
          deriv (fun s : ℝ => intervalDomainLift (v (s + τ)) x) t))
        (Set.Ioo 0 (T - τ) ×ˢ Set.Ioo 0 1)
      have heq : (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
              deriv (fun s : ℝ => intervalDomainLift (v (s + τ)) x) t)) =
            (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
              deriv (fun s : ℝ => intervalDomainLift (v s) x) t)) ∘ Prod.map (· + τ) id := by
        ext ⟨t, x⟩
        simp only [Function.uncurry, Prod.map, id]
        exact deriv_comp_add_const (f := fun s => intervalDomainLift (v s) x) (a := τ) t
      rw [heq]
      exact hjV.comp (Continuous.continuousOn (by fun_prop))
        (fun ⟨t, x⟩ ⟨ht, hx⟩ => ⟨mem_shift t ht, hx⟩)
  · -- (6) Interior Neumann
    intro t ht; exact h6 (t + τ) (mem_shift t ht)
  · -- (7) Closed spatial C² + endpoint Neumann
    intro t ht; exact h7 (t + τ) (mem_shift t ht)
  · -- (8) Closed-slab ∂ₜ continuity on Ioo 0 (T-τ) ×ˢ Icc 0 1
    obtain ⟨hjU, hjV⟩ := h8
    refine ⟨?_, ?_⟩
    · show ContinuousOn
        (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
          deriv (fun s : ℝ => intervalDomainLift (u (s + τ)) x) t))
        (Set.Ioo 0 (T - τ) ×ˢ Set.Icc 0 1)
      have heq : (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
              deriv (fun s : ℝ => intervalDomainLift (u (s + τ)) x) t)) =
            (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
              deriv (fun s : ℝ => intervalDomainLift (u s) x) t)) ∘ Prod.map (· + τ) id := by
        ext ⟨t, x⟩
        simp only [Function.uncurry, Prod.map, id]
        exact deriv_comp_add_const (f := fun s => intervalDomainLift (u s) x) (a := τ) t
      rw [heq]
      exact hjU.comp (Continuous.continuousOn (by fun_prop))
        (fun ⟨t, x⟩ ⟨ht, hx⟩ => ⟨mem_shift t ht, hx⟩)
    · show ContinuousOn
        (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
          deriv (fun s : ℝ => intervalDomainLift (v (s + τ)) x) t))
        (Set.Ioo 0 (T - τ) ×ˢ Set.Icc 0 1)
      have heq : (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
              deriv (fun s : ℝ => intervalDomainLift (v (s + τ)) x) t)) =
            (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
              deriv (fun s : ℝ => intervalDomainLift (v s) x) t)) ∘ Prod.map (· + τ) id := by
        ext ⟨t, x⟩
        simp only [Function.uncurry, Prod.map, id]
        exact deriv_comp_add_const (f := fun s => intervalDomainLift (v s) x) (a := τ) t
      rw [heq]
      exact hjV.comp (Continuous.continuousOn (by fun_prop))
        (fun ⟨t, x⟩ ⟨ht, hx⟩ => ⟨mem_shift t ht, hx⟩)
  · -- (9) Closed-slab solution continuity on Ioo 0 (T-τ) ×ˢ Icc 0 1
    obtain ⟨hjU, hjV⟩ := h9
    refine ⟨?_, ?_⟩
    · show ContinuousOn
        (Function.uncurry (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u (t + τ)) x))
        (Set.Ioo 0 (T - τ) ×ˢ Set.Icc 0 1)
      have heq : (Function.uncurry (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u (t + τ)) x)) =
            (Function.uncurry (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x)) ∘
            Prod.map (· + τ) id := by
        ext ⟨t, x⟩; simp [Function.uncurry, Prod.map]
      rw [heq]
      exact hjU.comp (Continuous.continuousOn (by fun_prop))
        (fun ⟨t, x⟩ ⟨ht, hx⟩ => ⟨mem_shift t ht, hx⟩)
    · show ContinuousOn
        (Function.uncurry (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v (t + τ)) x))
        (Set.Ioo 0 (T - τ) ×ˢ Set.Icc 0 1)
      have heq : (Function.uncurry (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v (t + τ)) x)) =
            (Function.uncurry (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x)) ∘
            Prod.map (· + τ) id := by
        ext ⟨t, x⟩; simp [Function.uncurry, Prod.map]
      rw [heq]
      exact hjV.comp (Continuous.continuousOn (by fun_prop))
        (fun ⟨t, x⟩ ⟨ht, hx⟩ => ⟨mem_shift t ht, hx⟩)


/-- **Time-shift of a classical solution**, given regularity time-shift.

If `(u, v)` is a classical solution on `[0, T]` and `0 < τ < T`, then
`(u(· + τ), v(· + τ))` is a classical solution on `[0, T − τ]`.
PDE autonomy: positivity, PDE, Neumann all hold at shifted times. -/
theorem classicalSolution_timeShift
    (hRegShift : RegularityTimeShiftWorks)
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ_pos : 0 < τ) (hτ_lt : τ < T) :
    IsPaper2ClassicalSolution intervalDomain p (T - τ)
      (fun t x => u (t + τ) x) (fun t x => v (t + τ) x) := by
  obtain ⟨hT_pos, hreg, hpos_u, hpos_v, hpde_u, hpde_v, hneumann⟩ := hsol
  refine ⟨by linarith, hRegShift hreg hτ_pos hτ_lt, ?_, ?_, ?_, ?_, ?_⟩
  · intro t x ht htTτ; exact hpos_u (t + τ) x (by linarith) (by linarith)
  · intro t x ht htTτ; exact hpos_v (t + τ) x (by linarith) (by linarith)
  · intro t x ht htTτ hx
    have hpde := hpde_u (t + τ) x (by linarith) (by linarith) hx
    simp only [intervalDomain] at hpde ⊢
    show deriv (fun s => u (s + τ) x) t = _
    have : deriv (fun s => u (s + τ) x) t = deriv (fun s => u s x) (t + τ) :=
      deriv_comp_add_const (f := fun s => u s x) (a := τ) t
    rw [this]; exact hpde
  · intro t x ht htTτ hx
    exact hpde_v (t + τ) x (by linarith) (by linarith) hx
  · intro t x ht htTτ hx
    exact hneumann (t + τ) x (by linarith) (by linarith) hx

/-! The initial trace of the time-shifted solution `u(τ)` is provable from
joint time-continuity of `u` at `τ` (from the G4 joint continuity infrastructure).
It requires: `‖u(t+τ) − u(τ)‖∞ → 0` as `t → 0⁺`, which follows from
`ContinuousOn` of `(t,x) ↦ u(t)(x)` on the closed slab and compactness
of `[0,1]`.  We leave this as a separate lemma to avoid coupling the
time-shift theorem to the joint-continuity infrastructure. -/

end ShenWork.Paper2.TimeShift
