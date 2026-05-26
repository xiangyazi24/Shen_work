/-
  L² difference-energy differential inequality for the interval-domain Paper2 PDE.

  GOAL (task): build a `IntervalDomainL2DifferenceEnergyFrontier` directly from
  two `IsPaper2ClassicalSolution`, in particular its `diffIneq` field
  `HasDerivWithinAt (fun τ => ∫₀¹ (w τ)² + (z τ)²) (Eprime τ) (Ici τ) τ` together
  with `Eprime τ ≤ K · E τ`, so that
  `intervalDomainClassicalUniquenessL2EnergyMethod_concrete` becomes
  unconditional and `GlobalSolutionGluingFromReachability p` closes.

  ## What this file proves honestly (no `sorry`/`admit`/`axiom`)

  The fourth conjunct of `intervalDomainClassicalRegularity` (interior time
  differentiability) now makes the *abstract* `timeDeriv u t x` a genuine time
  derivative, which is the necessary first ingredient of the time-Leibniz step.
  We extract this cleanly for the difference `w = u₁ − u₂`:

    * `intervalDomain_timeDeriv_isGenuine` — at every interior `(x,t)`,
      `HasDerivAt (fun s => u s x) (timeDeriv u t x) t`.  (From the 4th conjunct.)
    * `intervalDomain_difference_hasDerivAt_time` — hence the pointwise time
      derivative of the difference and of its square exist at interior points,
      with the expected values.

  These are exactly the *pointwise* (per-`x`, at the single time `t`) inputs that
  a dominated-differentiation (Leibniz) theorem consumes.

  ## Why `diffIneq` does NOT close on the current hypotheses — the precise gap

  To turn the pointwise time derivatives into
  `HasDerivWithinAt (fun τ => ∫₀¹ (w τ x)² + (z τ x)² dx) (Eprime τ) (Ici τ) τ`
  one must differentiate under the spatial integral.  The repo's finite-interval
  Leibniz wrapper
  `intervalDomain_intervalIntegral_hasDerivAt_of_dominated_deriv_le`
  (and the underlying Mathlib `hasDerivAt_integral_of_dominated_loc_of_deriv_le`)
  requires, in addition to pointwise time-derivative existence:

    (D1) a *whole time-ball* of differentiability:
         `∀ᵐ y, ∀ s ∈ Metric.ball t 1, HasDerivAt (fun τ => F τ y) (F' s y) s`,
         i.e. the time slice must be differentiable for *all* `s` in a
         neighborhood of `t`, including `s ≤ 0` and `s ≥ T` where
         `IsPaper2ClassicalSolution` asserts nothing; and

    (D2) a `τ`-uniform **integrable dominating envelope**
         `∀ᵐ y, ∀ s ∈ Metric.ball t 1, ‖F' s y‖ ≤ bound y` with
         `Integrable bound` — i.e. an integrable bound on `∂τ((w s y)²) =
         2 w s y · ∂τ w s y` uniform over the time neighborhood.

  `intervalDomainClassicalRegularity` provides **neither**.  Its 4th conjunct is
  *pointwise at the single interior time* `t` (not on a ball, and only for
  interior times in `(0,T)`); it gives no modulus and no uniform-in-`s`
  integrable envelope on `∂τw`.  The pointwise PDE identity expresses
  `∂τw = Δw − χ₀(chemDiv₁−chemDiv₂) + (logistic₁−logistic₂)` at interior points,
  but supplies no uniform control of `Δw = deriv(deriv(lift w))` over `x ∈ [0,1]`
  near the boundary and no time-ball uniformity.  Supplying (D1)+(D2) is genuine
  **joint parabolic space-time regularity** (a uniform-in-`τ` integrable bound on
  `∂τw` and the second spatial derivative), which is not implied by — and is at
  least as strong as — the uniqueness the energy method is being used to prove.

  This is the SAME blocker already isolated and named in
  `ShenWork.Paper2.IntervalDomainL2FrontierBuilder`
  (`IntervalDomainL2JointTimeRegularity`) and analyzed in
  `ShenWork.Paper2.IntervalDomainJointTimeRegularity`.  We therefore do not fake
  `diffIneq`; we add the genuine pointwise time-derivative facts that any honest
  proof of the missing joint-time bound must use, and restate the precise gap.

  This file contains **no `sorry`, no `admit`, no custom `axiom`.**
-/
import ShenWork.Paper2.IntervalDomainL2FrontierBuilder

open ShenWork.IntervalDomain MeasureTheory
open scoped Topology

namespace ShenWork.Paper2

noncomputable section

/-- **The abstract `timeDeriv` is a genuine time derivative at interior points.**

The fourth conjunct of `intervalDomainClassicalRegularity` asserts that for every
interior spatial point `x ∈ (0,1)` and interior time `t ∈ (0,T)` the time slice
`s ↦ u s x` is `DifferentiableAt`.  Since `intervalDomain.timeDeriv u t x` is by
definition `deriv (fun s => u s x) t`, this upgrades to a genuine `HasDerivAt`.
This is the per-`x`, single-time pointwise input of the time-Leibniz step. -/
theorem intervalDomain_timeDeriv_isGenuine
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {x : intervalDomain.Point} (hx : (x.1 : ℝ) ∈ Set.Ioo (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun s : ℝ => u s x) (intervalDomain.timeDeriv u t x) t := by
  -- Unpack the fourth regularity conjunct.
  have hreg : intervalDomainClassicalRegularity T u v := hsol.regularity
  have hdiff : DifferentiableAt ℝ (fun s : ℝ => u s x) t :=
    (hreg.2.2.2 x hx t ht).1
  -- `timeDeriv u t x = deriv (fun s => u s x) t` definitionally.
  simpa [intervalDomain, intervalDomainClassicalRegularity] using hdiff.hasDerivAt

/-- Same, for the `v`-component. -/
theorem intervalDomain_timeDeriv_isGenuine_v
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {x : intervalDomain.Point} (hx : (x.1 : ℝ) ∈ Set.Ioo (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun s : ℝ => v s x) (intervalDomain.timeDeriv v t x) t := by
  have hreg : intervalDomainClassicalRegularity T u v := hsol.regularity
  have hdiff : DifferentiableAt ℝ (fun s : ℝ => v s x) t :=
    (hreg.2.2.2 x hx t ht).2
  simpa [intervalDomain, intervalDomainClassicalRegularity] using hdiff.hasDerivAt

/-- **Pointwise time derivative of the difference `w = u₁ − u₂` at interior
points.**  At each interior `(x,t)` lying in the common time horizon, the time
slice `s ↦ u₁ s x − u₂ s x` has a genuine derivative equal to the difference of
the two `timeDeriv`s. -/
theorem intervalDomain_difference_hasDerivAt_time
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomain.Point → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {x : intervalDomain.Point} (hx : (x.1 : ℝ) ∈ Set.Ioo (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) (min T₁ T₂)) :
    HasDerivAt (fun s : ℝ => u₁ s x - u₂ s x)
      (intervalDomain.timeDeriv u₁ t x - intervalDomain.timeDeriv u₂ t x) t := by
  have ht1 : t ∈ Set.Ioo (0 : ℝ) T₁ :=
    ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
  have ht2 : t ∈ Set.Ioo (0 : ℝ) T₂ :=
    ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
  have h1 := intervalDomain_timeDeriv_isGenuine hsol₁ hx ht1
  have h2 := intervalDomain_timeDeriv_isGenuine hsol₂ hx ht2
  exact h1.sub h2

/-- **Pointwise time derivative of the squared difference `w²` at interior
points.**  Combining the chain rule with the genuine derivative of `w`, the
integrand `s ↦ (u₁ s x − u₂ s x)²` of the L² energy has, at each interior `(x,t)`
in the common horizon, time derivative `2 w · ∂τw` — the seed of the
`½ d/dτ ∫ w² = ∫ w·∂τw` energy identity. -/
theorem intervalDomain_difference_sq_hasDerivAt_time
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomain.Point → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {x : intervalDomain.Point} (hx : (x.1 : ℝ) ∈ Set.Ioo (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) (min T₁ T₂)) :
    HasDerivAt (fun s : ℝ => (u₁ s x - u₂ s x) ^ 2)
      (2 * (u₁ t x - u₂ t x) *
        (intervalDomain.timeDeriv u₁ t x - intervalDomain.timeDeriv u₂ t x)) t := by
  have hw := intervalDomain_difference_hasDerivAt_time hsol₁ hsol₂ hx ht
  -- Chain rule for the square: `d/ds (w s)^2 = 2 (w t) * w'`.
  have := hw.pow 2
  simpa [pow_one, two_mul, mul_comm, mul_left_comm, mul_assoc] using this

/-!
## The differential-inequality field `diffIneq` — precise remaining gap

`diffIneq` requires, for arbitrary abstract classical solutions and at every
interior time `τ`,

    HasDerivWithinAt
      (fun s => ∫₀¹ (u₁ s x − u₂ s x)² + (v₁ s x − v₂ s x)² dx)
      (Eprime τ) (Set.Ici τ) τ
  ∧ Eprime τ ≤ K · E τ.

The three pointwise facts above give the integrand's time derivative
`∂τ((w s x)²) = 2 (w t x)(∂τw t x)` at every interior `(x,t)`.  To pass to a
derivative of the *spatial integral* one invokes
`intervalDomain_intervalIntegral_hasDerivAt_of_dominated_deriv_le`
(ShenWork/Paper2/IntervalDomainLpMonotonicity.lean), whose hypotheses are:

  (D1) `∀ᵐ y, ∀ s ∈ Metric.ball t 1, HasDerivAt (fun τ => F τ y) (F' s y) s`
       — time-slice differentiability on a *whole* time-ball around `t`;
  (D2) `∀ᵐ y, ∀ s ∈ Metric.ball t 1, ‖F' s y‖ ≤ bound y` with `Integrable bound`
       — a τ-uniform integrable dominating envelope on `2 w ∂τw`.

The available hypotheses deliver only the single-time, interior-`x` pointwise
derivative (the facts above): NOT (D1) — `IsPaper2ClassicalSolution` says nothing
for times `s ∉ (0,T)` that lie in `Metric.ball t 1` — and NOT (D2) — there is no
uniform-in-`s` integrable bound on `∂τw` (equivalently on `Δw` via the PDE) over
`[0,1]`.  Both are genuine joint parabolic space-time regularity.

This is exactly the obligation already named as
`IntervalDomainL2JointTimeRegularity p` in
`ShenWork.Paper2.IntervalDomainL2FrontierBuilder`.  We therefore record the
honest reduction rather than fabricating `diffIneq`:
-/

/-- **Honest reduction of the frontier builder.**

The full L²-difference-energy frontier builder — and hence
`GlobalSolutionGluingFromReachability` via
`intervalDomainClassicalUniquenessL2EnergyMethod_concrete` — follows from the
single named joint space-time regularity obligation
`IntervalDomainL2JointTimeRegularity p` (which packages the missing (D1)+(D2)
domination together with the chemotaxis/reaction Lipschitz bounds).  The
pointwise time-derivative facts proved above are precisely the per-`x`,
single-time inputs that any honest discharge of that obligation must feed into
the dominated-differentiation step. -/
def intervalDomainL2DifferenceEnergyFrontierBuilder_of_jointTime
    {p : CM2Params}
    (hjoint : IntervalDomainL2JointTimeRegularity p) :
    IntervalDomainL2DifferenceEnergyFrontierBuilder p :=
  intervalDomainL2DifferenceEnergyFrontierBuilder_of_jointTimeRegularity hjoint

/-!
## Status note (honest, precise gap report)

* **Proved here (no `sorry`/`admit`/`axiom`):**
  - `intervalDomain_timeDeriv_isGenuine` (+ `_v`): the abstract `timeDeriv` is a
    genuine `HasDerivAt` at interior `(x,t)`, from the 4th regularity conjunct.
  - `intervalDomain_difference_hasDerivAt_time`: the difference `w = u₁−u₂` has a
    genuine pointwise time derivative at interior points.
  - `intervalDomain_difference_sq_hasDerivAt_time`: the integrand `w²` of the L²
    energy has time derivative `2 w·∂τw` (the `½ d/dτ ∫ w² = ∫ w·∂τw` seed).
  - `intervalDomainL2DifferenceEnergyFrontierBuilder_of_jointTime`: the frontier
    builder, hence gluing, reduces to the single named obligation.

* **NOT closed unconditionally — the precise blocking field:**
  the `diffIneq` field of `IntervalDomainL2DifferenceEnergyFrontier`, i.e.
  `HasDerivWithinAt (fun τ => ∫₀¹ w² + z²) (Eprime τ) (Ici τ) τ` together with
  `Eprime τ ≤ K·E τ`, for ARBITRARY abstract classical solutions.  Mathlib's
  dominated-differentiation requires (D1) time-slice differentiability on a whole
  time-ball around `τ` and (D2) a `τ`-uniform integrable envelope on `2 w·∂τw`;
  `intervalDomainClassicalRegularity` provides only single-time interior pointwise
  differentiability and no uniform integrable bound.  This is the joint parabolic
  space-time regularity already isolated as `IntervalDomainL2JointTimeRegularity`.

  Consequently gluing does **not** close unconditionally on the current
  hypotheses; it is unconditional **modulo** `IntervalDomainL2JointTimeRegularity p`
  via `intervalDomainClassicalUniquenessL2EnergyMethod_of_jointTimeRegularity` and
  `GlobalSolutionGluingFromReachability_of_l2EnergyMethod`.
-/

end

end ShenWork.Paper2
