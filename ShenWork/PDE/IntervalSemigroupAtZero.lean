import ShenWork.PDE.IntervalDuhamelRepresentation

/-!
# The `S 0 = id` obligation: a NEGATIVE / DEGENERACY result

This file analyses the named obligation
`IntervalSemigroupIdentityAtZero f : intervalFullSemigroupOperator 0 f x = f x`
(for `x ∈ (0,1)`) from `IntervalDuhamelRepresentation`.

## The key finding (NOT what the docstring claims)

The docstring of `IntervalSemigroupIdentityAtZero` describes `S 0 = id` as an
"approximate identity / Gaussian-to-delta limit": `S t f → f` as `t → 0⁺`.  That
*limit* statement is true.  But the predicate is stated as the **value at `t = 0`
itself**, `intervalFullSemigroupOperator 0 f x = f x`, and *that* is FALSE in
general for the concrete definitions in this development.

The reason is purely definitional, and has nothing to do with the spectral
machinery.  In Lean,
`heatKernel 0 x = 1 / Real.sqrt (4·π·0) · exp(…) = 1/0 · … = 0`
(`heatKernel_zero`).  Hence the period-`2` image kernel is identically zero at
`t = 0`:
`intervalNeumannFullKernel 0 x y = ∑' k, (heatKernel 0 _ + heatKernel 0 _) = 0`,
and so the propagator value is the integral of the zero function:
`intervalFullSemigroupOperator 0 f x = ∫ y, 0 · f y ∂μ = 0`.

Therefore `intervalFullSemigroupOperator 0 f x = 0` for **every** `f` and `x`,
and the predicate `S 0 f x = f x` holds **iff `f x = 0`**.

The intended spectral route (`S t f x = ∑ₙ e^{−tλₙ} f̂ₙ cos(nπx)`, evaluate at
`t=0` to get the cosine reconstruction `= f x`) does **not** apply: the spectral
identity `intervalFullSemigroupOperator_eq_cosineHeatValue_unconditional` carries
the hypothesis `0 < t` and is simply false at `t = 0` for the concrete
zero-at-zero kernel (its RHS at `t=0` would be `∑ₙ f̂ₙ cos(nπx) = f x`, while the
LHS is `0`).

## Consequence for the representation theorem

`intervalDuhamelRepresentation_of` consumes `hid` as
`∀ t ∈ (0,T), IntervalSemigroupIdentityAtZero (intervalDomainLift (u t))`.
By the result below this hypothesis forces `u t x = 0` for all interior `x`,
i.e. it is only satisfiable for the trivial solution.  The obligation is
therefore **mis-stated**: to be dischargeable it must be reformulated as the
`t → 0⁺` *limit*
`Filter.Tendsto (fun t => intervalFullSemigroupOperator t f x)
   (𝓝[>] 0) (𝓝 (f x))`,
which is the genuine approximate-identity statement.  No purely value-at-`0`
theorem can close it.
-/

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalDuhamelRepresentation

namespace ShenWork.IntervalSemigroupAtZero

noncomputable section

/-- The period-`2` image Neumann kernel is **identically zero** at time `0`,
because each Gaussian image `heatKernel 0 _` vanishes (`heatKernel_zero`). -/
theorem intervalNeumannFullKernel_zero (x y : ℝ) :
    intervalNeumannFullKernel 0 x y = 0 := by
  unfold intervalNeumannFullKernel
  simp [heatKernel_zero]

/-- **The actual value of the propagator at time `0`.**
`intervalFullSemigroupOperator 0 f x = 0` for every `f`, `x` — the kernel is
identically zero, so the defining integral is the integral of the zero
integrand. -/
theorem intervalFullSemigroupOperator_zero (f : ℝ → ℝ) (x : ℝ) :
    intervalFullSemigroupOperator 0 f x = 0 := by
  unfold intervalFullSemigroupOperator
  simp [intervalNeumannFullKernel_zero]

/-- **`S 0 = id` holds at an interior point iff `f` vanishes there.**

Since `intervalFullSemigroupOperator 0 f x = 0`, the predicate value
`intervalFullSemigroupOperator 0 f x = f x` is equivalent to `f x = 0`.  This is
the precise sense in which the named obligation `IntervalSemigroupIdentityAtZero`
is *false* as a value-at-`0` statement (it is only the trivial-data case). -/
theorem intervalSemigroupAtZero_iff (f : ℝ → ℝ) (x : ℝ) :
    intervalFullSemigroupOperator 0 f x = f x ↔ f x = 0 := by
  rw [intervalFullSemigroupOperator_zero]
  exact eq_comm

/-- **The named predicate forces the data to vanish.**
`IntervalSemigroupIdentityAtZero f` (i.e. `S 0 f = f` on all interior points) is
equivalent to `f` vanishing on `(0,1)`.  In particular it is NOT satisfied by a
generic continuous `f`, so it cannot be discharged as stated. -/
theorem intervalSemigroupIdentityAtZero_iff_zero (f : ℝ → ℝ) :
    IntervalSemigroupIdentityAtZero f ↔ ∀ x ∈ Set.Ioo (0 : ℝ) 1, f x = 0 := by
  unfold IntervalSemigroupIdentityAtZero
  refine forall_congr' (fun x => ?_)
  refine imp_congr_right (fun _ => ?_)
  exact intervalSemigroupAtZero_iff f x

end

end ShenWork.IntervalSemigroupAtZero
