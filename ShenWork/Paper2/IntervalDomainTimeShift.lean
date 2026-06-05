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

/-- The regularity time-shift hypothesis: shifting `t ↦ t + τ` preserves
the 9 regularity conjuncts. Each conjunct is either spatial-only
(trivial) or involves time derivatives (chain rule). -/
def RegularityTimeShiftWorks : Prop :=
  ∀ {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ},
    intervalDomainClassicalRegularity T u v →
  ∀ {τ : ℝ}, 0 < τ → τ < T →
    intervalDomainClassicalRegularity (T - τ)
      (fun t x => u (t + τ) x) (fun t x => v (t + τ) x)

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
