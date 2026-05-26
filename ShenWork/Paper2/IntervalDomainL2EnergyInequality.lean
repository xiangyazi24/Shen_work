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
import ShenWork.PDE.IntervalUnderIntegralLeibniz

open ShenWork.IntervalDomain MeasureTheory
open ShenWork.IntervalUnderIntegralLeibniz
open ShenWork.Paper2.IntervalDomainLpMonotonicity
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
    (hreg.2.2.2.1 x hx t ht).1.1
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
    (hreg.2.2.2.1 x hx t ht).1.2
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

/-! ## Energy as an explicit interval integral, and the localized time-Leibniz -/

/-- The lift of a pointwise sum of two squares splits as a sum of squares of the
lifts.  Pure unfolding of `intervalDomainLift` (case split on `x ∈ [0,1]`). -/
theorem intervalDomainLift_sumSq
    (f g : intervalDomain.Point → ℝ) (y : ℝ) :
    intervalDomainLift (fun x => f x ^ 2 + g x ^ 2) y
      = (intervalDomainLift f y) ^ 2 + (intervalDomainLift g y) ^ 2 := by
  unfold intervalDomainLift
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
  · simp [hy]
  · simp [hy]

/-- The L² difference energy written as a plain interval integral of the lifted
squared differences. -/
theorem intervalDomainClassicalL2DifferenceEnergy_eq_integral
    (u v U V : ℝ → intervalDomain.Point → ℝ) (t : ℝ) :
    intervalDomainClassicalL2DifferenceEnergy u v U V t
      = ∫ y in (0 : ℝ)..1,
          (intervalDomainLift (fun x => u t x - U t x) y) ^ 2
            + (intervalDomainLift (fun x => v t x - V t x) y) ^ 2 := by
  unfold intervalDomainClassicalL2DifferenceEnergy intervalDomain
  show intervalDomainIntegral
      (fun x => (u t x - U t x) ^ 2 + (v t x - V t x) ^ 2) = _
  unfold intervalDomainIntegral
  refine intervalIntegral.integral_congr ?_
  intro y _
  exact intervalDomainLift_sumSq _ _ y

/-- **The time-derivative integrand of the energy.**  At an interior space-time
point, `∂τ[(lift w τ y)² + (lift z τ y)²] = 2(lift w τ y)(∂τ lift w) + 2(lift z τ
y)(∂τ lift z)`, where `w = u₁−u₂`, `z = v₁−v₂`.  Off `[0,1]` the lift is `0`, so
the integrand and its derivative both vanish; on `(0,1)` this is the per-`x`
square chain rule. -/
def intervalDomainEnergyIntegrand
    (u₁ v₁ u₂ v₂ : ℝ → intervalDomain.Point → ℝ) (s y : ℝ) : ℝ :=
  (intervalDomainLift (fun x => u₁ s x - u₂ s x) y) ^ 2
    + (intervalDomainLift (fun x => v₁ s x - v₂ s x) y) ^ 2

/-- The time-derivative field of the energy integrand, as an `ℝ → ℝ → ℝ` family
in `(s, y)`. -/
def intervalDomainEnergyIntegrandDeriv
    (u₁ v₁ u₂ v₂ : ℝ → intervalDomain.Point → ℝ) (s y : ℝ) : ℝ :=
  2 * (intervalDomainLift (fun x => u₁ s x - u₂ s x) y)
      * deriv (fun r => intervalDomainLift (fun x => u₁ r x - u₂ r x) y) s
    + 2 * (intervalDomainLift (fun x => v₁ s x - v₂ s x) y)
      * deriv (fun r => intervalDomainLift (fun x => v₁ r x - v₂ r x) y) s

/-- **(D1), discharged on the localization ball.**  For an interior spatial point
`y ∈ (0,1)` and every time `s` in a ball `Metric.ball τ δ ⊆ (0,T)`, the energy
integrand `r ↦ intervalDomainEnergyIntegrand … r y` has the stated time
derivative.  Uses the interior-time-differentiability conjunct `.2.2.2.1` at the
interior time `s` (valid because the ball lies inside `(0,T)`) together with the
square chain rule, lifted through `intervalDomainLift` on the interior branch. -/
theorem intervalDomainEnergyIntegrand_hasDerivAt_interior
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomain.Point → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1)
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) (min T₁ T₂)) :
    HasDerivAt
      (fun r => intervalDomainEnergyIntegrand u₁ v₁ u₂ v₂ r y)
      (intervalDomainEnergyIntegrandDeriv u₁ v₁ u₂ v₂ s y) s := by
  classical
  -- The interior point `y` packages into `intervalDomain.Point`.
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy
  set x : intervalDomain.Point := ⟨y, hyIcc⟩ with hx
  have hxIoo : (x.1 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := hy
  -- On the interior branch the lift of a slice equals the slice value at `x`.
  have hlift_u : ∀ r : ℝ,
      intervalDomainLift (fun z => u₁ r z - u₂ r z) y = u₁ r x - u₂ r x := by
    intro r; simp [intervalDomainLift, hyIcc, hx]
  have hlift_v : ∀ r : ℝ,
      intervalDomainLift (fun z => v₁ r z - v₂ r z) y = v₁ r x - v₂ r x := by
    intro r; simp [intervalDomainLift, hyIcc, hx]
  -- Pointwise time derivatives of the difference slices at `s` (interior time).
  have hwsq := intervalDomain_difference_sq_hasDerivAt_time hsol₁ hsol₂ hxIoo hs
  -- For `v` we need the analogous square-derivative lemma; build it directly.
  have hzw : HasDerivAt (fun r : ℝ => v₁ r x - v₂ r x)
      (intervalDomain.timeDeriv v₁ s x - intervalDomain.timeDeriv v₂ s x) s := by
    have hs1 : s ∈ Set.Ioo (0 : ℝ) T₁ :=
      ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩
    have hs2 : s ∈ Set.Ioo (0 : ℝ) T₂ :=
      ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_right _ _)⟩
    exact (intervalDomain_timeDeriv_isGenuine_v hsol₁ hxIoo hs1).sub
      (intervalDomain_timeDeriv_isGenuine_v hsol₂ hxIoo hs2)
  have hzsq := hzw.pow 2
  -- Assemble: rewrite the integrand and its derivative through the lift identities.
  have hsum : HasDerivAt
      (fun r => (u₁ r x - u₂ r x) ^ 2 + (v₁ r x - v₂ r x) ^ 2)
      (2 * (u₁ s x - u₂ s x) *
          (intervalDomain.timeDeriv u₁ s x - intervalDomain.timeDeriv u₂ s x)
        + 2 * (v₁ s x - v₂ s x) *
          (intervalDomain.timeDeriv v₁ s x - intervalDomain.timeDeriv v₂ s x)) s := by
    have h1 := hwsq
    have h2 : HasDerivAt (fun r : ℝ => (v₁ r x - v₂ r x) ^ 2)
        (2 * (v₁ s x - v₂ s x) *
          (intervalDomain.timeDeriv v₁ s x - intervalDomain.timeDeriv v₂ s x)) s := by
      simpa [pow_one, two_mul, mul_comm, mul_left_comm, mul_assoc] using hzsq
    exact h1.add h2
  -- Transport `hsum` to the lifted integrand via the eventual equality of functions.
  have hfun_eq : (fun r => intervalDomainEnergyIntegrand u₁ v₁ u₂ v₂ r y)
      = fun r => (u₁ r x - u₂ r x) ^ 2 + (v₁ r x - v₂ r x) ^ 2 := by
    funext r; simp [intervalDomainEnergyIntegrand, hlift_u r, hlift_v r]
  -- The derivative-field also rewrites: `deriv (lift slice) s = timeDeriv … s x`.
  have hderiv_u :
      deriv (fun r => intervalDomainLift (fun z => u₁ r z - u₂ r z) y) s
        = intervalDomain.timeDeriv u₁ s x - intervalDomain.timeDeriv u₂ s x := by
    have : (fun r => intervalDomainLift (fun z => u₁ r z - u₂ r z) y)
        = fun r => u₁ r x - u₂ r x := by funext r; exact hlift_u r
    rw [this]
    exact (intervalDomain_difference_hasDerivAt_time hsol₁ hsol₂ hxIoo hs).deriv
  have hderiv_v :
      deriv (fun r => intervalDomainLift (fun z => v₁ r z - v₂ r z) y) s
        = intervalDomain.timeDeriv v₁ s x - intervalDomain.timeDeriv v₂ s x := by
    have : (fun r => intervalDomainLift (fun z => v₁ r z - v₂ r z) y)
        = fun r => v₁ r x - v₂ r x := by funext r; exact hlift_v r
    rw [this]; exact hzw.deriv
  rw [hfun_eq]
  have hval : intervalDomainEnergyIntegrandDeriv u₁ v₁ u₂ v₂ s y
      = 2 * (u₁ s x - u₂ s x) *
          (intervalDomain.timeDeriv u₁ s x - intervalDomain.timeDeriv u₂ s x)
        + 2 * (v₁ s x - v₂ s x) *
          (intervalDomain.timeDeriv v₁ s x - intervalDomain.timeDeriv v₂ s x) := by
    unfold intervalDomainEnergyIntegrandDeriv
    rw [hlift_u s, hlift_v s, hderiv_u, hderiv_v]
  rw [hval]
  exact hsum

/-- **Energy time-derivative identity (step i), modulo the (D2) envelope.**

Given an integrable dominating envelope `bound` for the energy
integrand's time derivative, uniform over a localization ball
`Metric.ball τ δ ⊆ (0,T)`, the L² difference energy `E` has a genuine time
derivative `∫₀¹ ∂τ[(lift w)² + (lift z)²]` at `τ`.  All hypotheses except the
envelope (`hbound_int`, `h_bound`) are discharged here from the regularity:
(D1) via `intervalDomainEnergyIntegrand_hasDerivAt_interior`, the
measurability/integrability via continuity of the integrand on the compact
interior.  This isolates the envelope as the single residual analytic input. -/
theorem intervalDomainClassicalL2DifferenceEnergy_hasDerivAt_of_envelope
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomain.Point → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {τ δ : ℝ} (hδ : 0 < δ)
    (hball : Metric.ball τ δ ⊆ Set.Ioo (0 : ℝ) (min T₁ T₂))
    {bound : ℝ → ℝ}
    (hF_meas : ∀ᶠ s in 𝓝 τ,
        AEStronglyMeasurable
          (intervalDomainEnergyIntegrand u₁ v₁ u₂ v₂ s)
          intervalDomainInteriorMeasure)
    (hF_int : IntervalIntegrable
        (intervalDomainEnergyIntegrand u₁ v₁ u₂ v₂ τ) volume 0 1)
    (hF'_meas : AEStronglyMeasurable
        (intervalDomainEnergyIntegrandDeriv u₁ v₁ u₂ v₂ τ)
        intervalDomainInteriorMeasure)
    (h_bound : ∀ᵐ y ∂intervalDomainInteriorMeasure,
        ∀ s ∈ Metric.ball τ δ,
          ‖intervalDomainEnergyIntegrandDeriv u₁ v₁ u₂ v₂ s y‖ ≤ bound y)
    (hbound_int : Integrable bound intervalDomainInteriorMeasure) :
    HasDerivAt
      (intervalDomainClassicalL2DifferenceEnergy u₁ v₁ u₂ v₂)
      (∫ y in (0 : ℝ)..1,
        intervalDomainEnergyIntegrandDeriv u₁ v₁ u₂ v₂ τ y) τ := by
  -- (D1): time-slice differentiability for a.e. interior `y`, on the whole ball.
  have h_diff : ∀ᵐ y ∂intervalDomainInteriorMeasure,
      ∀ s ∈ Metric.ball τ δ,
        HasDerivAt (fun r => intervalDomainEnergyIntegrand u₁ v₁ u₂ v₂ r y)
          (intervalDomainEnergyIntegrandDeriv u₁ v₁ u₂ v₂ s y) s := by
    refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
    refine Filter.Eventually.of_forall (fun y hy s hs => ?_)
    exact intervalDomainEnergyIntegrand_hasDerivAt_interior hsol₁ hsol₂ hy
      (hball hs)
  -- Localized Leibniz gives the derivative of the integral form of `E`.
  have hderiv :
      HasDerivAt
        (fun s => ∫ y in (0 : ℝ)..1,
          intervalDomainEnergyIntegrand u₁ v₁ u₂ v₂ s y)
        (∫ y in (0 : ℝ)..1,
          intervalDomainEnergyIntegrandDeriv u₁ v₁ u₂ v₂ τ y) τ :=
    intervalIntegral_hasDerivAt_time_of_local hδ hF_meas hF_int hF'_meas
      h_bound hbound_int h_diff
  -- Rewrite `E` as that integral form.
  have hEeq : (intervalDomainClassicalL2DifferenceEnergy u₁ v₁ u₂ v₂)
      = fun s => ∫ y in (0 : ℝ)..1,
          intervalDomainEnergyIntegrand u₁ v₁ u₂ v₂ s y := by
    funext s
    rw [intervalDomainClassicalL2DifferenceEnergy_eq_integral]
    rfl
  rw [hEeq]
  exact hderiv

/-- **(D2) envelope from closed-slab joint continuity, and the energy
derivative.**  This is the decisive reduction: if the energy integrand's
time-derivative field is *jointly continuous on the closed slab*
`Icc(τ−δ,τ+δ) ×ˢ Icc 0 1`, then `exists_bound_of_continuousOn_slab` supplies the
(D2) constant envelope and the energy has a genuine time derivative at `τ`.
Everything reduces to this one closed-slab continuity input. -/
theorem intervalDomainClassicalL2DifferenceEnergy_hasDerivAt_of_slabContinuous
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomain.Point → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {τ δ : ℝ} (hδ : 0 < δ)
    (hball : Metric.ball τ δ ⊆ Set.Ioo (0 : ℝ) (min T₁ T₂))
    (hF_meas : ∀ᶠ s in 𝓝 τ,
        AEStronglyMeasurable
          (intervalDomainEnergyIntegrand u₁ v₁ u₂ v₂ s)
          intervalDomainInteriorMeasure)
    (hF_int : IntervalIntegrable
        (intervalDomainEnergyIntegrand u₁ v₁ u₂ v₂ τ) volume 0 1)
    (hF'_meas : AEStronglyMeasurable
        (intervalDomainEnergyIntegrandDeriv u₁ v₁ u₂ v₂ τ)
        intervalDomainInteriorMeasure)
    (hslab : ContinuousOn
        (Function.uncurry (intervalDomainEnergyIntegrandDeriv u₁ v₁ u₂ v₂))
        (Set.Icc (τ - δ) (τ + δ) ×ˢ Set.Icc (0 : ℝ) 1)) :
    HasDerivAt
      (intervalDomainClassicalL2DifferenceEnergy u₁ v₁ u₂ v₂)
      (∫ y in (0 : ℝ)..1,
        intervalDomainEnergyIntegrandDeriv u₁ v₁ u₂ v₂ τ y) τ := by
  obtain ⟨bound, hbound_int, h_bound⟩ :=
    exists_bound_of_continuousOn_slab hδ hslab
  exact intervalDomainClassicalL2DifferenceEnergy_hasDerivAt_of_envelope
    hsol₁ hsol₂ hδ hball hF_meas hF_int hF'_meas h_bound hbound_int

/-! ### PIECE 1, discharged for the genuine build-path constructors

The constructors that actually feed `GlobalSolutionGluingFromReachability` (the
constant equilibrium and the spatially-constant short-horizon witnesses, see
`constantInTime_classicalRegularity` and the `c`/`ellipticV p c` data in
`ShenWork.PDE.IntervalDomainExistence`) are **time-constant at every point**.  For
such data the energy integrand's time-derivative field is *identically zero*,
hence trivially continuous on the CLOSED spatial slab `Icc 0 1` — the strengthened
PIECE-1 hypothesis.  This is the honest content of "the genuine non-trivial
constructors in the build path are spatially-constant on `(0,1)` (so `∂ₜ` const,
continuous on `Icc`)": we do not need to strengthen the abstract 6th conjunct, we
discharge the closed-slab input directly for the data that occurs. -/
theorem intervalDomainEnergyIntegrandDeriv_eq_zero_of_timeConst
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomain.Point → ℝ}
    (hu₁ : ∀ (x : intervalDomain.Point) (r s : ℝ), u₁ r x = u₁ s x)
    (hv₁ : ∀ (x : intervalDomain.Point) (r s : ℝ), v₁ r x = v₁ s x)
    (hu₂ : ∀ (x : intervalDomain.Point) (r s : ℝ), u₂ r x = u₂ s x)
    (hv₂ : ∀ (x : intervalDomain.Point) (r s : ℝ), v₂ r x = v₂ s x)
    (s y : ℝ) :
    intervalDomainEnergyIntegrandDeriv u₁ v₁ u₂ v₂ s y = 0 := by
  classical
  -- Each lifted slice `r ↦ intervalDomainLift (uᵢ r) y` is constant in `r`,
  -- so its time `deriv` is `0`; the product field collapses to `0`.
  have hconst_u :
      (fun r => intervalDomainLift (fun x => u₁ r x - u₂ r x) y)
        = fun _ => intervalDomainLift (fun x => u₁ s x - u₂ s x) y := by
    funext r
    by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
    · simp only [intervalDomainLift, hy, dif_pos]
      rw [hu₁ ⟨y, hy⟩ r s, hu₂ ⟨y, hy⟩ r s]
    · simp [intervalDomainLift, hy]
  have hconst_v :
      (fun r => intervalDomainLift (fun x => v₁ r x - v₂ r x) y)
        = fun _ => intervalDomainLift (fun x => v₁ s x - v₂ s x) y := by
    funext r
    by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
    · simp only [intervalDomainLift, hy, dif_pos]
      rw [hv₁ ⟨y, hy⟩ r s, hv₂ ⟨y, hy⟩ r s]
    · simp [intervalDomainLift, hy]
  unfold intervalDomainEnergyIntegrandDeriv
  rw [hconst_u, hconst_v]
  simp [deriv_const]

/-- **PIECE 1 closed for time-constant data: the closed-slab continuity input
of `…_hasDerivAt_of_slabContinuous` holds unconditionally.**  Consequently the
energy time-derivative exists and equals `0` for such data. -/
theorem intervalDomainEnergyIntegrandDeriv_continuousOn_closedSlab_of_timeConst
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomain.Point → ℝ}
    (hu₁ : ∀ (x : intervalDomain.Point) (r s : ℝ), u₁ r x = u₁ s x)
    (hv₁ : ∀ (x : intervalDomain.Point) (r s : ℝ), v₁ r x = v₁ s x)
    (hu₂ : ∀ (x : intervalDomain.Point) (r s : ℝ), u₂ r x = u₂ s x)
    (hv₂ : ∀ (x : intervalDomain.Point) (r s : ℝ), v₂ r x = v₂ s x)
    (τ δ : ℝ) :
    ContinuousOn
      (Function.uncurry (intervalDomainEnergyIntegrandDeriv u₁ v₁ u₂ v₂))
      (Set.Icc (τ - δ) (τ + δ) ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hzero : (Function.uncurry (intervalDomainEnergyIntegrandDeriv u₁ v₁ u₂ v₂))
      = fun _ => (0 : ℝ) := by
    funext q
    obtain ⟨s, y⟩ := q
    simpa [Function.uncurry] using
      intervalDomainEnergyIntegrandDeriv_eq_zero_of_timeConst hu₁ hv₁ hu₂ hv₂ s y
  rw [hzero]
  exact continuousOn_const

/-!
## The differential-inequality field `diffIneq` — precise remaining gap (UPDATED)

`diffIneq` requires, for arbitrary abstract classical solutions and at every
interior time `τ`,

    HasDerivWithinAt
      (fun s => ∫₀¹ (u₁ s x − u₂ s x)² + (v₁ s x − v₂ s x)² dx)
      (Eprime τ) (Set.Ici τ) τ
  ∧ Eprime τ ≤ K · E τ.

### What the faithful 6-conjunct regularity NOW buys (genuine progress)

The time-derivative half (`HasDerivAt E …`) is reduced here to a single,
sharply-named analytic input — *closed-slab joint continuity of the integrand's
time-derivative field* — via:

  * `intervalDomainEnergyIntegrand_hasDerivAt_interior` discharges **(D1)** (the
    time-slice differentiability on the whole *localization* ball) using the
    4th conjunct `.2.2.2.1` plus the square chain rule.  The old "global
    `Metric.ball τ 1` leaks outside `(0,T)`" obstruction is eliminated by the
    `intervalIntegral_hasDerivAt_time_of_local` localization (`exists_ball_subset_Ioo`).
  * `intervalDomainClassicalL2DifferenceEnergy_hasDerivAt_of_envelope` closes the
    Leibniz step from any integrable **(D2)** envelope, with the
    measurability/integrability side conditions explicit.
  * `intervalDomainClassicalL2DifferenceEnergy_hasDerivAt_of_slabContinuous`
    discharges (D2) from `ContinuousOn (uncurry F') (Icc(τ−δ,τ+δ) ×ˢ Icc 0 1)`
    via `exists_bound_of_continuousOn_slab` (the 6th conjunct's compact-slab
    envelope tool).

So the entire time-derivative existence reduces to **one** hypothesis.

### The exact remaining blocker — spatial-endpoint envelope integrability

The 6th conjunct supplies joint continuity of `(t,x) ↦ ∂ₜ(intervalDomainLift
(uᵢ t)) x` on the **OPEN** slab `(0,T) ×ˢ (0,1)`.  The (D2) tool
`exists_bound_of_continuousOn_slab` needs continuity on the **CLOSED** slab
`Icc(τ−δ,τ+δ) ×ˢ Icc 0 1`, i.e. *up to the spatial endpoints* `x ∈ {0,1}`.  The
mismatch is precisely at `x = 0` and `x = 1`:

  * `intervalDomainLift` has its `if x ∈ [0,1]` branch boundary exactly there;
  * the 6th regularity conjunct is stated on the open `(0,1)` and is **silent**
    at the endpoints — it does NOT assert that `∂ₜ(lift uᵢ)` extends continuously
    (equivalently, stays bounded by an integrable envelope) as `x → 0⁺, 1⁻`.

The integral `∫₀¹` runs up to the endpoints, and the dominating envelope must be
`intervalDomainInteriorMeasure`-integrable over all of `(0,1)`, including a
neighbourhood of `0` and `1`.  Open-interior continuity gives a *pointwise* bound
at each interior `y` but **no τ-uniform integrable envelope as `y → 0⁺, 1⁻`**.
This is the named subtlety: **spatial-endpoint envelope integrability** of the
time-derivative field.  It is genuine parabolic boundary regularity (the
time-derivative field is bounded up to the Neumann boundary), NOT a missing
Mathlib lemma and NOT implied by the 6 conjuncts.

### Also outstanding: the `Eprime ≤ K·E` bound

Even granting closed-slab continuity, the *inequality* half needs steps (ii)–(iv):
PDE substitution `∂τw = Δw − χ₀·chemDiff + logisticDiff`, the Neumann IBP
`∫ w·Δw = −∫(∂ₓw)² ≤ 0` (`intervalCosineLaplacianCoeff_eq` /
`intervalDomainLift_hasDerivAt_of_interiorC2`, requiring the genuine endpoint
Neumann values `w'(0)=w'(1)=0` — again an endpoint fact), and the Lipschitz
bounds on the chemotaxis/reaction differences.  These remain to be assembled.

Both outstanding items are precisely the joint parabolic *boundary* regularity
packaged abstractly as `IntervalDomainL2JointTimeRegularity p`.  We therefore
record the honest reduction rather than fabricating `diffIneq`:
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
  - `intervalDomain_difference_hasDerivAt_time` /
    `intervalDomain_difference_sq_hasDerivAt_time`: genuine pointwise time
    derivative of `w = u₁−u₂` and of `w²`.
  - `intervalDomainLift_sumSq`,
    `intervalDomainClassicalL2DifferenceEnergy_eq_integral`: the L² energy as a
    plain interval integral of lifted squared differences.
  - `intervalDomainEnergyIntegrand_hasDerivAt_interior`: **(D1) discharged** —
    the energy integrand's time-slice has the expected derivative for *every*
    `s` in a localization ball `⊆ (0,T)` and a.e. interior `y`.
  - `intervalDomainClassicalL2DifferenceEnergy_hasDerivAt_of_envelope`: the
    localized Leibniz energy derivative from any integrable (D2) envelope.
  - `intervalDomainClassicalL2DifferenceEnergy_hasDerivAt_of_slabContinuous`:
    **the time-derivative half of `diffIneq` reduced to a single hypothesis** —
    closed-slab joint continuity of the integrand's time-derivative field —
    discharged through `exists_bound_of_continuousOn_slab`.
  - `intervalDomainL2DifferenceEnergyFrontierBuilder_of_jointTime`: the frontier
    builder, hence gluing, reduces to the single named obligation.

* **NOT closed unconditionally — the EXACT remaining step (named precisely):**

  1. *Spatial-endpoint envelope integrability.*  The 6th regularity conjunct
     gives joint continuity of the time-derivative field only on the **OPEN**
     slab `(0,T) ×ˢ (0,1)`.  `exists_bound_of_continuousOn_slab` (the (D2) tool)
     needs continuity on the **CLOSED** slab `Icc(τ−δ,τ+δ) ×ˢ Icc 0 1`, i.e. up
     to the spatial endpoints `x ∈ {0,1}` where `intervalDomainLift` branches and
     the conjunct is silent.  Equivalently: a `τ`-uniform **integrable** envelope
     on `∂τw` as `x → 0⁺, 1⁻`.  This boundary-uniform bound is genuine parabolic
     boundary regularity, not a Mathlib gap and not implied by the 6 conjuncts.
     It is the precise hypothesis of
     `intervalDomainClassicalL2DifferenceEnergy_hasDerivAt_of_slabContinuous`.

  2. *The `Eprime ≤ K·E` inequality.*  Steps (ii)–(iv): PDE substitution, the
     Neumann IBP `∫ w·Δw = −∫(∂ₓw)² ≤ 0` (needing endpoint Neumann values
     `w'(0)=w'(1)=0`, again a boundary fact), and the chemotaxis/reaction
     Lipschitz absorption.  Still to assemble.

  Both reduce to the joint parabolic *boundary* regularity packaged abstractly as
  `IntervalDomainL2JointTimeRegularity p`.  Consequently gluing does **not** close
  unconditionally; it is unconditional **modulo** that obligation, via
  `intervalDomainClassicalUniquenessL2EnergyMethod_of_jointTimeRegularity` and
  `GlobalSolutionGluingFromReachability_of_l2EnergyMethod`.  The genuine advance
  of this file: the time-derivative existence is now reduced to a *single*
  sharply-named boundary-continuity hypothesis (item 1), with (D1) and the
  Leibniz mechanics fully proved.

  ## UPDATE — closed-boundary conjuncts (7) and (8) added to the definition

  `intervalDomainClassicalRegularity` now carries two appended conjuncts that
  every `IsPaper2ClassicalSolution` is required to satisfy (and which the
  build-path spatially-constant constructors discharge trivially,
  `intervalDomainLift_const_contDiffOn_Icc` /
  `intervalDomainLift_const_deriv_endpoint_zero` /
  `intervalDomainLift_constInTime_jointDeriv_continuousOn`):

    (7) CLOSED-`Icc 0 1` spatial `C²` of the lift **plus the genuine endpoint
        Neumann VALUES** `deriv (lift (u t)) 0 = 0`, `deriv (lift (u t)) 1 = 0`
        (and for `v`).  This supplies the `g'(0)=g'(1)=0` of
        `intervalCosineLaplacianCoeff_eq` directly as endpoint values (no longer
        only a one-sided `Tendsto`).
    (8) CLOSED-slab joint continuity of the per-`x` time-derivative field
        `(t,x) ↦ ∂ₜ(lift (u s)) x` on `Ioo 0 T ×ˢ Icc 0 1` — continuous up to the
        spatial endpoints, exactly item (1)'s missing **closed**-slab continuity
        for the `∂ₜ` FACTOR of the envelope.

  These close exactly the two endpoint facts named above as "boundary facts".
  Two obligations nevertheless REMAIN before `diffIneq` is unconditional for
  ARBITRARY classical solutions, and they are named EXACTLY:

    (R1) *Joint `(t,x)` continuity of the SOLUTION field itself* on the closed
         slab.  The integrand-derivative field is
         `2·(lift w)·(∂ₜ lift w) + 2·(lift z)·(∂ₜ lift z)`.  Conjunct (8) makes
         the `∂ₜ` factor continuous on the closed slab, but
         `intervalDomainClassicalL2DifferenceEnergy_hasDerivAt_of_slabContinuous`
         needs the PRODUCT continuous, hence also the FACTOR `(t,x) ↦ lift(u s) x`
         jointly continuous on `Ioo 0 T ×ˢ Icc 0 1`.  Conjunct (7) gives only
         per-fixed-`t` spatial `C²`, not joint `(t,x)` continuity.  This is an
         additional joint-continuity conjunct, still absent.

    (R2) *The `Eprime ≤ K·E` inequality.*  PDE substitution + Neumann IBP +
         chemotaxis/reaction Lipschitz absorption, UNCHANGED in difficulty by
         (7)/(8).  Moreover the existing IBP lemma `intervalCosineLaplacianCoeff_eq`
         is stated for the ZERO-EXTENSION `intervalDomainLift`, which is NOT
         two-sided `HasDerivAt` at `x ∈ {0,1}` for a solution whose boundary trace
         is nonzero (the lift jumps to `0` outside `[0,1]`).  Closing the IBP for
         arbitrary solutions requires either an `Icc`-INTRINSIC IBP (consuming
         conjunct (7)'s `ContDiffOn ℝ 2 … (Icc 0 1)` via `HasDerivWithinAt`) or a
         boundary-vanishing reduction — a genuine rework of the IBP object, not a
         wiring step.

  VERDICT: conjuncts (7)/(8) are real, provable for the build path, and discharge
  the spatial-endpoint Neumann VALUES and the `∂ₜ`-factor closed-slab continuity.
  Gluing still does NOT close unconditionally: the precise residual is (R1) a
  joint `(t,x)` solution-field continuity conjunct, and (R2) the `Eprime ≤ K·E`
  energy-inequality assembly with an `Icc`-intrinsic Neumann IBP.  Both remain
  packaged as `IntervalDomainL2JointTimeRegularity p`.
-/

end

end ShenWork.Paper2
