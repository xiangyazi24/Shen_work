/-
  HsupNorm refactor, pure-heat (a = b = 0) case.

  ## What the task asked, and what is actually true

  Goal: discharge `IntervalDomainSupNormDerivativeNonposOn u (Ioo 0 D.T)`
  in the `a = b = 0` regime, where the logistic source vanishes and
  `u(t) = S(t)u₀` is the pure Neumann heat semigroup.

  The suggested route — the constant majorant `g(t) := ‖u₀‖_∞` through
  `HsupNormProof.nonposOn_of_eq` — requires `‖u(t)‖_∞ = g(t)` EXACTLY
  (the constructor reads the derivative off `g`, so it needs equality,
  not domination).  But Neumann heat **strictly decreases** the sup-norm
  of non-constant data (diffusion flattens the profile: the maximum is
  non-increasing, the minimum non-decreasing, both strict unless the
  datum is constant).  So `‖S(t)u₀‖_∞ < ‖u₀‖_∞` for `t > 0` whenever `u₀`
  is non-constant, and the constant majorant is NOT equal to the
  sup-norm.  The constant-`g` route therefore works ONLY for
  constant-in-time `u` (`nonposOn_of_const_in_time` below).

  ## The genuine content (two true facts, both proved here)

  1. `heat_supNorm_le_initial` — the sub-Markov bound
     `‖S(t)u₀‖_∞ ≤ B` whenever `‖lift u₀‖ ≤ B` on `ℝ`.  TRUE, leak-free
     (the kernel has unit mass and is non-negative).

  2. `nonposOn_of_const_in_time` — the one case where the constant
     majorant is valid: time-constant `u`.

  ## Why the differentiable STRUCTURE is still the wrong predicate

  Even the genuine pure-heat statement is *monotone* non-increasing, not
  *differentiable*: `t ↦ ‖S(t)u₀‖_∞` is a max over `x ∈ [0,1]` of a
  family that is real-analytic in `t`, hence differentiable wherever the
  argmax is unique, but it can have a corner at times where two maxima
  tie (e.g. symmetric data).  `IntervalDomainSupNormDerivativeNonposOn`
  demands differentiability at EVERY interior time, which the heat
  sup-norm does not have in general.  The faithful refactor target is the
  weaker, true predicate `Paper2.SupNormNonincreasingOn` (monotone, no
  differentiability) — see `IntervalHsupNormProof.lean` for the full
  finding on the unconditional field.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalHsupNormProof
import ShenWork.PDE.IntervalFullKernelSupBound

open Filter Topology
open ShenWork.IntervalDomain
  (intervalDomainPoint intervalDomainLift intervalDomainSupNorm
   IntervalDomainSupNormDerivativeNonposOn)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)

noncomputable section

namespace ShenWork.Paper2.HsupNormHeat

/-- The pure-heat trajectory `t ↦ S(t)u₀` as a function of the subtype. -/
def heatTrajectory (u₀ : intervalDomainPoint → ℝ) :
    ℝ → intervalDomainPoint → ℝ :=
  fun t x => intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1

/-- **Sub-Markov bound (TRUE).**  If `|lift u₀| ≤ B` on all of `ℝ`, then
the heat trajectory stays bounded by `B`: `‖S(t)u₀‖_∞ ≤ B`. -/
theorem heat_supNorm_le_initial
    {u₀ : intervalDomainPoint → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ y, |intervalDomainLift u₀ y| ≤ B)
    {t : ℝ} (ht : 0 < t) :
    intervalDomainSupNorm (heatTrajectory u₀ t) ≤ B := by
  unfold intervalDomainSupNorm heatTrajectory
  apply Real.sSup_le
  · rintro r ⟨x, rfl⟩
    exact ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
      ht hB hbound x.1
  · exact hB

/-- **Constant-in-time case (the valid constant-`g`).**  If `u` is
constant in time on the open interval `I` (`u t = w` for all `t ∈ I`),
then the differentiable sup-norm structure holds with derivative `0`. -/
theorem nonposOn_of_const_in_time
    {u : ℝ → intervalDomainPoint → ℝ} {I : Set ℝ} {w : intervalDomainPoint → ℝ}
    (hU : IsOpen I) (hconst : ∀ t ∈ I, u t = w) :
    IntervalDomainSupNormDerivativeNonposOn u I := by
  refine HsupNormProof.nonposOn_of_eq (g := fun _ => intervalDomainSupNorm w)
    hU ?_ ?_ ?_ ?_
  · -- the sup-norm trajectory equals a constant function on `I`
    have heq : Set.EqOn (fun t => intervalDomainSupNorm (u t))
        (fun _ => intervalDomainSupNorm w) I := by
      intro s hs; simp only; rw [hconst s hs]
    exact continuousOn_const.congr heq
  · intro t ht; rw [hconst t ht]
  · intro _ _; exact differentiableAt_const _
  · intro _ _; rw [deriv_const']

end ShenWork.Paper2.HsupNormHeat
