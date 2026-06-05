/-
  F1: Interior slice PID + uniform continuation infrastructure.

  Key lemma: a classical solution interior slice `u(τ)` satisfies PID.
  This is the entry point for the restart-before-end argument that
  constructs `IntervalDomainUniformLocalExistence` from `hlocal`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainTheorem11Umbrella
import ShenWork.Paper2.IntervalDomainL2StaticVDifference

open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.UniformContinuation

/-- **Interior slice of a classical solution satisfies PID.**
At any interior time `τ ∈ (0, T)`, the slice `u τ` is positive on the
interior, bounded, and continuous — hence `PositiveInitialDatum`. -/
theorem classicalSolution_slice_positiveInitialDatum
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    PositiveInitialDatum intervalDomain (u τ) := by
  have hC2 := (hsol.regularity.2.2.2.2.2.2.1 τ hτ).1
  have hcontOn : ContinuousOn (intervalDomainLift (u τ)) (Set.Icc (0:ℝ) 1) :=
    hC2.1.continuousOn
  have hcont : Continuous (u τ) := by
    have hcomp := hcontOn.comp_continuous continuous_subtype_val (fun x => x.2)
    exact hcomp.congr (fun x => by
      simp only [Function.comp, intervalDomainLift, x.2, dif_pos, Subtype.coe_eta])
  have hbdd := classicalSolution_u_range_bddAbove hsol hτ
  exact ⟨⟨hbdd, hcont⟩, fun x _hx => hsol.u_pos' hτ.1 hτ.2⟩

/-- **Pointwise bound on a classical solution slice from sup-norm bound.**
If `u` is a classical solution with sup-norm ≤ M (from Lemma 3.1), then
`|u τ x| ≤ M` for all `x` at interior times. -/
theorem classicalSolution_slice_abs_le_of_supNorm_le
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    {M : ℝ}
    (hM : ∀ t, 0 < t → t < T →
      ∀ x : intervalDomainPoint, |u t x| ≤ M) :
    ∀ x : intervalDomainPoint, |u τ x| ≤ M :=
  fun x => hM τ hτ.1 hτ.2 x

end ShenWork.Paper2.UniformContinuation
