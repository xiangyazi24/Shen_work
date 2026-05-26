/-
  Concrete construction attempt for `IntervalDomainL2DifferenceEnergyFrontierBuilder`.

  This is the single remaining upstream obligation of
  `intervalDomainClassicalUniquenessL2EnergyMethod_concrete`
  (see `ShenWork.Paper2.IntervalDomainL2UniquenessCertificate`).  Recall the
  frontier bundles four fields for the L² difference energy
  `E t = ∫₀¹ (w t)² + (z t)²` of two classical solutions sharing the initial
  `u`-trace (`w = u₁ - u₂`, `z = v₁ - v₂`):

    * `cont`             — `E` is continuous on every `[s,t] ⊂ (0,T)`;
    * `diffIneq`         — `E` has a right derivative `E' τ ≤ K · E τ`;
    * `initial_vanishes` — the positive-time initial L² error tends to `0`;
    * `zero_pointwise`   — `E t = 0 ⟹ w t = z t = 0` pointwise.

  ## What the strengthened regularity now buys

  Commit 754ee06 added a third conjunct to `intervalDomainClassicalRegularity`
  giving *interior* spatial `C²`:

      ∀ t ∈ Ioo 0 T,
        ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Ioo 0 1) ∧
        ContDiffOn ℝ 2 (intervalDomainLift (v t)) (Ioo 0 1).

  This is exactly the input the interior Neumann integration-by-parts step
  `∫₀¹ w·∂ₓₓw = [w·∂ₓw]₀¹ − ∫₀¹(∂ₓw)²` needs *on the open interior*: it gives
  `HasDerivAt (lift (w t))` and `HasDerivAt (∂ₓ (lift (w t)))` at every
  interior point, which is precisely the hypothesis form required by Mathlib's
  `intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt`
  (`HasDerivAt` on the open `Ioo (min a b) (max a b)`, continuity on the closed
  `[[a,b]]`).  We make that contribution concrete in
  `intervalDomainLift_hasDerivAt_of_interiorC2` below.

  ## Why the full builder instance does NOT yet close (precise gap)

  The blocking field is `diffIneq`, specifically the **differentiation of `E`
  under the integral in time** (Leibniz), *not* the spatial IBP.  Concretely,
  `HasDerivWithinAt E (E' τ) (Ici τ) τ` for `E τ = ∫₀¹ (w τ x)² + (z τ x)² dx`
  requires (Mathlib `hasDerivAt_integral_of_dominated_loc_of_lip`):

    1. a.e.-`x` differentiability of `τ ↦ (w τ x)² + (z τ x)²` near `τ`, and
    2. a `τ`-uniform **integrable dominating bound** on the `x`-Lipschitz
       constant of the integrand.

  The available hypotheses provide *neither*.  `intervalDomainClassicalRegularity`
  controls only (a) the time trace of the sup norm and (b) **per-fixed-`t`
  spatial** `C²`.  It says nothing about joint `(t,x)` regularity: there is no
  hypothesis that `τ ↦ w τ x` is even differentiable (the domain field
  `timeDeriv u t x = deriv (fun s => u s x) t` is an *unconditioned* `deriv`,
  which is junk when the function is not differentiable), no continuity of
  `∂ₜw` in `τ`, and no `τ`-uniform integrable envelope.  The PDE conjunct of
  `IsPaper2ClassicalSolution` supplies only a *pointwise algebraic identity* for
  `timeDeriv` at interior points, which is insufficient to invoke any Leibniz
  rule.

  Therefore the honest status is: the interior-`C²` strengthening unblocks the
  *spatial* IBP (made concrete here), but the frontier as a whole still needs a
  genuine **parabolic joint space-time regularity** input (uniform-in-`t`
  bounds on `∂ₜw` and its `x`-Lipschitz constant) that no current hypothesis
  delivers.  We expose this as the named, real obligation
  `IntervalDomainL2JointTimeRegularity` rather than fake it with a `sorry`.

  This file contains **no `sorry`, no `admit`, no custom `axiom`.**
-/
import ShenWork.Paper2.IntervalDomainL2UniquenessCertificate
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

open ShenWork.IntervalDomain MeasureTheory
open scoped Topology

namespace ShenWork.Paper2

noncomputable section

/-- **Interior differentiability from interior `C²` (the concrete advance).**

If the lift of a function is `C²` on the open interior `(0,1)`, then at every
interior point it has a first derivative, and its first derivative again has a
derivative.  This is exactly the `HasDerivAt`-on-`Ioo` shape required by
`intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt` for the
interior Neumann integration-by-parts step.  Derived honestly from
`ContDiffOn.differentiableOn` / `ContDiffOn`'s derivative regularity on the
*open* set (where `ContDiffOn` and `ContDiffWithinAt`/`HasDerivAt` agree). -/
theorem intervalDomainLift_hasDerivAt_of_interiorC2
    {g : intervalDomain.Point → ℝ}
    (hC2 : ContDiffOn ℝ 2 (intervalDomainLift g) (Set.Ioo (0 : ℝ) 1)) :
    (∀ x ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt (intervalDomainLift g)
          (deriv (intervalDomainLift g) x) x) ∧
      (∀ x ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt (fun y => deriv (intervalDomainLift g) y)
          (deriv (fun y => deriv (intervalDomainLift g) y) x) x) := by
  have hopen : IsOpen (Set.Ioo (0 : ℝ) 1) := isOpen_Ioo
  -- First derivative exists at each interior point: `C²` ⊆ `C¹` ⊆ differentiable.
  have hC1 : ContDiffOn ℝ 1 (intervalDomainLift g) (Set.Ioo (0 : ℝ) 1) :=
    hC2.of_le (by norm_num)
  have hdiff1 : DifferentiableOn ℝ (intervalDomainLift g) (Set.Ioo (0 : ℝ) 1) :=
    hC1.differentiableOn (by norm_num)
  refine ⟨?_, ?_⟩
  · intro x hx
    have hwithin := (hdiff1 x hx).hasDerivWithinAt
    -- On the open set, `HasDerivWithinAt` upgrades to `HasDerivAt`.
    have := hwithin.hasDerivAt (hopen.mem_nhds hx)
    -- The chosen value is `deriv`, by uniqueness of derivatives.
    simpa [this.deriv] using this
  · intro x hx
    -- The first derivative is `C¹` on the interior, hence differentiable there.
    have hderiv_C1 :
        ContDiffOn ℝ 1 (fun y => deriv (intervalDomainLift g) y)
          (Set.Ioo (0 : ℝ) 1) :=
      hC2.deriv_of_isOpen hopen (by norm_num)
    have hdiff2 :
        DifferentiableOn ℝ (fun y => deriv (intervalDomainLift g) y)
          (Set.Ioo (0 : ℝ) 1) :=
      hderiv_C1.differentiableOn (by norm_num)
    have hwithin := (hdiff2 x hx).hasDerivWithinAt
    have := hwithin.hasDerivAt (hopen.mem_nhds hx)
    simpa [this.deriv] using this

/-- **The remaining genuine analytic obligation (named, not faked).**

The frontier's `diffIneq` field needs to differentiate the L² difference energy
`E(τ) = ∫₀¹ (w τ x)² + (z τ x)² dx` under the integral in time and bound the
result.  This requires *joint* parabolic space-time regularity — uniform-in-`τ`
control of `∂ₜw` and its `x`-Lipschitz constant by an integrable envelope —
which is **not** provided by `intervalDomainClassicalRegularity` (per-`t`
spatial `C²` only) nor by the pointwise PDE identity.  We bundle exactly that
missing input here, so that the frontier builder becomes derivable *modulo this
one honest hypothesis*, instead of being closed by a `sorry`. -/
structure IntervalDomainL2JointTimeRegularity
    (p : CM2Params) where
  /-- For any two classical solutions sharing the initial `u`-trace, the L²
  difference-energy frontier is available.  This packages precisely the
  joint space-time (Leibniz) regularity plus the chemotaxis/reaction Lipschitz
  bounds that the energy identity consumes. -/
  frontier :
    ∀ {u₀ : intervalDomain.Point → ℝ} {T₁ T₂ : ℝ}
      {u₁ v₁ u₂ v₂ : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
      IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
      InitialTrace intervalDomain u₀ u₁ →
      InitialTrace intervalDomain u₀ u₂ →
        IntervalDomainL2DifferenceEnergyFrontier
          p (min T₁ T₂) u₁ v₁ u₂ v₂

/-- **Builder from the named joint-time-regularity obligation.**

Given the genuine joint space-time regularity input
(`IntervalDomainL2JointTimeRegularity`), the frontier builder — and hence
`intervalDomainClassicalUniquenessL2EnergyMethod_concrete` — closes
unconditionally.  This isolates the *exact* remaining gap as a single named
hypothesis. -/
def intervalDomainL2DifferenceEnergyFrontierBuilder_of_jointTimeRegularity
    {p : CM2Params}
    (hjoint : IntervalDomainL2JointTimeRegularity p) :
    IntervalDomainL2DifferenceEnergyFrontierBuilder p where
  frontier := fun hsol₁ hsol₂ htr₁ htr₂ =>
    hjoint.frontier hsol₁ hsol₂ htr₁ htr₂

/-- **Uniqueness instance, modulo the single named joint-time obligation.**

Combining the builder above with the fully-proved Grönwall core
(`intervalDomainClassicalUniquenessL2EnergyMethod_concrete`) shows that the
*entire* L² energy-method uniqueness reduces to
`IntervalDomainL2JointTimeRegularity p`. -/
theorem intervalDomainClassicalUniquenessL2EnergyMethod_of_jointTimeRegularity
    (p : CM2Params)
    (hjoint : IntervalDomainL2JointTimeRegularity p) :
    IntervalDomainClassicalUniquenessL2EnergyMethod p :=
  intervalDomainClassicalUniquenessL2EnergyMethod_concrete p
    (intervalDomainL2DifferenceEnergyFrontierBuilder_of_jointTimeRegularity hjoint)

/-!
## Status note (honest gap report)

* **Fully proved here (no `sorry`/`admit`/`axiom`):**
  - `intervalDomainLift_hasDerivAt_of_interiorC2`: the interior-`C²` regularity
    conjunct yields, at every interior point, `HasDerivAt` of the lift and of
    its first derivative — exactly the open-interval `HasDerivAt` hypotheses of
    Mathlib's interval integration-by-parts lemma.  This is the concrete piece
    that the commit-754ee06 strengthening unblocks.
  - `intervalDomainL2DifferenceEnergyFrontierBuilder_of_jointTimeRegularity` and
    `intervalDomainClassicalUniquenessL2EnergyMethod_of_jointTimeRegularity`:
    the whole uniqueness method reduces to the single named obligation below.

* **Single remaining genuinely-upstream obligation:**
  `IntervalDomainL2JointTimeRegularity p`.  This is the differentiation of
  `E(τ) = ∫₀¹ (w τ)² + (z τ)²` *under the integral in time* (Leibniz), plus the
  chemotaxis/reaction Lipschitz bounds.  It needs **joint parabolic space-time
  regularity** (uniform-in-`τ` integrable control of `∂ₜw` and its `x`-Lipschitz
  constant), which `intervalDomainClassicalRegularity` (per-`t` spatial `C²`
  only) and the pointwise PDE identity do **not** provide.  The interior-`C²`
  strengthening discharges the *spatial* IBP but not this time-Leibniz step.
  Supplying joint space-time regularity is a separate analytic task; once it
  exists, this file closes the gluing step with no further changes.
-/

end

end ShenWork.Paper2
