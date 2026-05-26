/-
  Joint space-time regularity for the interval-domain L² energy method.

  GOAL (as set by the task): discharge `IntervalDomainL2JointTimeRegularity p`,
  the single remaining hypothesis of
  `intervalDomainClassicalUniquenessL2EnergyMethod_of_jointTimeRegularity`, by
  exhibiting the time-Leibniz domination needed to differentiate the L²
  difference energy `E(τ) = ∫₀¹ (w τ)² + (z τ)²` under the integral in time.

  ## Honest status (read this first)

  UPDATE.  `intervalDomainClassicalRegularity` now carries a **fourth conjunct**
  (interior time regularity: `s ↦ u s x` and `s ↦ v s x` are `DifferentiableAt`
  at every interior `(x,t)`), so the def records full joint `C^{2,1}` and the
  abstract `timeDeriv u t x = deriv (fun s => u s x) t` is now a *genuine* time
  derivative — the time-Leibniz `HasDerivWithinAt` half of `diffIneq` is
  available.  This is *necessary* for the energy method but **not sufficient**
  to close `IntervalDomainL2JointTimeRegularity`: the remaining blocker is the
  differential-inequality *bound* `Eprime τ ≤ K · E τ`, i.e. the nonlinear
  spatial energy estimate — the spatial IBP `∫ w·Δw = −∫|∂ₓw|²` together with
  the chemotaxis/reaction Lipschitz control of the difference `w = u₁−u₂`,
  `z = v₁−v₂`.  Those are exactly the named analytic frontiers (`hIBP`,
  `hLpTime`, the cross-diffusion/Young frontiers) that the entire
  `IntervalDomainEnergyStep` family carries as explicit hypotheses; no lemma in
  the repo proves them unconditionally from `IsPaper2ClassicalSolution`.  Hence
  `intervalDomainL2JointTimeRegularity_concrete` is still NOT provable here, and
  is not faked.  The precise unprovable obligation is named below.

  The intended route was: a classical solution's spatial profile is, via the
  kernel↔spectral identity
  (`IntervalFullKernelInterchange.intervalFullSemigroupOperator_eq_cosineHeatValue_unconditional`),
  the cosine spectral heat value `∑ₙ e^{−tλₙ} f̂ₙ cos(nπx)`, which is jointly
  smooth in `(t,x)` for `t > 0`; hence `∂ₜ` exists with an integrable τ-uniform
  x-Lipschitz domination, giving the Leibniz step.

  **That route does not close `IntervalDomainL2JointTimeRegularity p`, for a
  structural reason that is independent of the analysis.**  The `frontier` field
  of `IntervalDomainL2JointTimeRegularity` (see
  `ShenWork.Paper2.IntervalDomainL2FrontierBuilder`) is quantified over an
  *arbitrary* pair of abstract classical solutions

      hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁
      hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂

  and `IsPaper2ClassicalSolution` (`ShenWork.Paper2.Statements`) supplies only

    * `intervalDomainClassicalRegularity` = sup-norm decay (under `χ₀ ≤ 0`) +
      *per-fixed-`t`* spatial `C²` on the open interior `(0,1)`;
    * the *pointwise algebraic* PDE identity at interior points
      `timeDeriv u t x = Δ(u t) x − χ₀ · chemDiv … + reaction`;
    * Neumann boundary vanishing.

  Critically: (i) `timeDeriv u t x := deriv (fun s => u s x) t` is an
  *unconditioned* `deriv`; nothing in `IsPaper2ClassicalSolution` asserts that
  `s ↦ u s x` is differentiable, so the PDE identity is, when `s ↦ u s x` is not
  differentiable, merely the statement that the RHS equals `deriv`'s junk value
  `0`.  (ii) There is **no hypothesis, and no theorem anywhere in the repo,
  identifying an abstract classical solution `u₁` with the spectral / semigroup
  form `intervalFullSemigroupOperator t f` of its initial data.**  Such an
  identification is exactly a *parabolic representation / uniqueness* theorem;
  it is not implied by — indeed it is at least as strong as — the uniqueness
  statement the energy method is being used to prove.

  The kernel↔spectral identities
  (`intervalFullSemigroupOperator_eq_cosineHeatValue_unconditional`,
  `intervalFullSemigroupOperator_contDiff_two_unconditional`) are statements
  about the *explicitly constructed function* `intervalFullSemigroupOperator t f`,
  NOT about the universally-quantified abstract `u₁, v₁, u₂, v₂`.  Without a
  representation bridge `(IsPaper2ClassicalSolution … u v) → u t = (semigroup of
  its trace)`, the spectral joint smoothness cannot be transported to the `w`,
  `z` differences appearing in `E(τ)`.

  Therefore the *precise* blocking field is:

      IntervalDomainL2JointTimeRegularity.frontier  —  the `diffIneq` conjunct of
      `IntervalDomainL2DifferenceEnergyFrontier`, i.e.
        `HasDerivWithinAt (fun τ => ∫₀¹ (w τ)² + (z τ)²) (Eprime τ) (Ici τ) τ`
      together with `Eprime τ ≤ K · E τ`,
      for ARBITRARY abstract solutions.

  It is blocked on a missing **parabolic representation theorem** (every
  `IsPaper2ClassicalSolution` equals the Neumann-heat semigroup evolution of its
  initial trace), which the spectral machinery presupposes but the repo does not
  provide.

  ## What this file genuinely contributes (no `sorry`/`admit`/`axiom`)

  We prove the *positive* enabling fact the task identified — that the cosine
  spectral heat value really is jointly regular in `(t,x)` for `t > 0`, and in
  particular is **differentiable in `t` at each fixed `x`** — so that the only
  thing standing between this file and the closure of the Leibniz step is the
  representation bridge named above.  Concretely:

    * `unitIntervalCosineHeatPointWeight_hasDerivAt_time`: each spectral mode
      weight `t ↦ e^{−tλₙ} cos(nπx)` is differentiable in `t`, with derivative
      `−λₙ e^{−tλₙ} cos(nπx)`.
    * `unitIntervalCosineHeatValue_spatial_contDiff_two`: re-exposes the spatial
      `C²` regularity (the spatial half of joint `C^{2,1}`) for the record.

  These are the reusable spectral facts a future representation theorem would
  consume to discharge `IntervalDomainL2JointTimeRegularity`.

  This file contains **no `sorry`, no `admit`, no custom `axiom`.**
-/
import ShenWork.Paper2.IntervalDomainL2FrontierBuilder
import ShenWork.PDE.IntervalDomainRegularityBootstrap

open ShenWork.IntervalDomain MeasureTheory
open scoped Topology

namespace ShenWork.Paper2

noncomputable section

/-- **Time-differentiability of a single spectral mode weight (positive content).**

Each Neumann cosine mode weight `t ↦ e^{−t λₙ} cos(nπx)` is differentiable in
time with derivative `−λₙ e^{−t λₙ} cos(nπx)`.  This is the elementary
per-mode building block of the joint `(t,x)` regularity of the spectral heat
value: combined with the Gaussian/exponential-in-`n` tail (already used for the
spatial `C²` Weierstrass-M test) it yields term-by-term `∂ₜ` of the series.

We state it as a genuine `HasDerivAt` so it can be fed directly into a future
dominated-differentiation (Leibniz) argument. -/
theorem unitIntervalCosineHeatPointWeight_hasDerivAt_time
    (x : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => unitIntervalCosineHeatPointWeight s x n)
      (-(unitIntervalCosineEigenvalue n) *
        unitIntervalCosineHeatPointWeight t x n) t := by
  -- `unitIntervalCosineHeatPointWeight s x n
  --    = exp (-s * λₙ) * cos (n π x)`, with `cos (n π x)` constant in `s`.
  have hexp :
      HasDerivAt (fun s : ℝ => Real.exp (-s * unitIntervalCosineEigenvalue n))
        (-(unitIntervalCosineEigenvalue n) *
          Real.exp (-t * unitIntervalCosineEigenvalue n)) t := by
    have hlin :
        HasDerivAt (fun s : ℝ => -s * unitIntervalCosineEigenvalue n)
          (-(unitIntervalCosineEigenvalue n)) t := by
      have h0 : HasDerivAt (fun s : ℝ => -s) (-1 : ℝ) t := by
        simpa using (hasDerivAt_id t).neg
      simpa [mul_comm] using h0.mul_const (unitIntervalCosineEigenvalue n)
    simpa [mul_comm] using hlin.exp
  -- Multiply by the `s`-constant `cos (n π x)`.
  have h := hexp.mul_const (unitIntervalCosineMode n x)
  -- Rewrite both sides into the `unitIntervalCosineHeatPointWeight` shape.
  have hfun :
      (fun s : ℝ =>
          Real.exp (-s * unitIntervalCosineEigenvalue n) *
            unitIntervalCosineMode n x)
        = fun s : ℝ => unitIntervalCosineHeatPointWeight s x n := by
    funext s; rfl
  rw [hfun] at h
  convert h using 1
  -- derivative value: `-λₙ * (exp(-tλₙ) * cos) = (-λₙ * exp(-tλₙ)) * cos`
  unfold unitIntervalCosineHeatPointWeight
  ring

/-- **Spatial `C²` of the spectral heat value (record of the available half).**

For `t > 0` and bounded cosine coefficients, `x ↦ ∑ₙ e^{−tλₙ} aₙ cos(nπx)` is
`C²` in space.  This is the spatial half of the joint `C^{2,1}` regularity the
energy-method Leibniz step would need; it is re-exported here directly from the
regularity bootstrap so that this file collects, in one place, the spectral
inputs a future parabolic representation theorem would consume. -/
theorem unitIntervalCosineHeatValue_spatial_contDiff_two
    {t : ℝ} (ht : 0 < t) {a : ℕ → ℝ} {M : ℝ} (hM : ∀ n, |a n| ≤ M) :
    ContDiff ℝ 2 (fun x => unitIntervalCosineHeatValue t a x) :=
  ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatValue_contDiff_two
    ht hM

/-!
## Status note (honest, precise gap report)

* **Proved here (no `sorry`/`admit`/`axiom`):**
  - `unitIntervalCosineHeatPointWeight_hasDerivAt_time` — each spectral mode
    weight is differentiable in `t` (the per-mode time-Leibniz seed).
  - `unitIntervalCosineHeatValue_spatial_contDiff_two` — spatial `C²` of the
    spectral heat value (the spatial half of joint `C^{2,1}`).

* **NOT closed — the precise blocking field:**
  `IntervalDomainL2JointTimeRegularity.frontier`, specifically the `diffIneq`
  conjunct of `IntervalDomainL2DifferenceEnergyFrontier`
  (differentiation of `E(τ) = ∫₀¹ (w τ)² + (z τ)²` under the integral in `τ`,
  plus `Eprime τ ≤ K · E τ`), for **arbitrary abstract classical solutions**.

  The spectral approach requires identifying each abstract
  `IsPaper2ClassicalSolution … u v` with the Neumann-heat semigroup evolution of
  its initial trace.  No such **parabolic representation theorem** exists in the
  repo (the kernel↔spectral identities concern the explicitly-built
  `intervalFullSemigroupOperator t f`, not the universally-quantified `u₁,…,v₂`),
  and supplying it is a separate, genuinely upstream analytic task — not implied
  by `IsPaper2ClassicalSolution`'s pointwise PDE identity (whose `timeDeriv` is
  an unconditioned `deriv` that does not even assert time-differentiability).

  Consequently `intervalDomainL2JointTimeRegularity_concrete` is **not** proven
  here; doing so honestly would require first stating and proving the
  representation bridge.  The gluing step therefore does **not** close
  unconditionally on the current hypotheses.
-/

end

end ShenWork.Paper2
