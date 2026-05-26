import ShenWork.PDE.IntervalDuhamelRepresentation
import ShenWork.PDE.CosineSpectrum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The Fourier-coefficient `s`-derivative bridge: the eigenfunction IBP core

This file works toward discharging `IntervalSolutionFourierCoeffDeriv`, the
function-argument (chain-rule) half of the variation-of-constants derivative for
the parabolic Duhamel representation (`IntervalDuhamelRepresentation.lean`).

The predicate asks: for an abstract `IsPaper2ClassicalSolution`, the map
`s ↦ S(t−s)(u s) x` has derivative `S(t−s)(F(u s)) x`.  In spectral form

  `S(t−s)(u s) x = ∑ₙ e^{−(t−s)λₙ} ⟨u s, eₙ⟩ cos(nπx)`,    `λₙ = (nπ)²`,

and differentiating in `s` the `e`-factor contributes `+λₙ` (the spectral
generator, already handled by `intervalSemigroup_timeArg_hasDerivAt`), while the
coefficient contributes `⟨∂ₛ(u s), eₙ⟩`.  The PDE gives `∂ₛu = Δu + F̃`, and the
eigenfunction integration-by-parts identity

  `⟨Δg, eₙ⟩ = −λₙ ⟨g, eₙ⟩`                                       (★)

makes the `Δu` piece cancel the `+λₙ` from the `e`-factor, leaving exactly
`∑ₙ e^{−(t−s)λₙ} ⟨F̃, eₙ⟩ cos = S(t−s)F(u s) x`.

## What is proved clean here (no `sorry`/`admit`/`axiom`)

The genuine parabolic-spectral content `(★)` — the **eigenfunction
integration-by-parts identity**, sub-step (a) of the task — is proved
unconditionally for any `C²`-on-`[0,1]` function `g` satisfying the genuine
Neumann condition `g'(0) = g'(1) = 0`:

  `intervalCosineLaplacianCoeff_eq` :
    `∫₀¹ cos(nπx) · g''(x) dx = −(nπ)² · ∫₀¹ cos(nπx) · g(x) dx`.

This is the IBP-twice fact at the heart of the cancellation, and it is the
deepest individual analytic lemma the bridge consumes.  The raw cosine
coefficient `unitIntervalCosineRawCoeff (↑g)` (and hence `cosineCoeffs g`, which
is built from it) of the spatial Laplacian of `g` therefore equals `−λₙ` times
the raw coefficient of `g`.

## The precise remaining gaps (named, not faked)

The full predicate does **not** close from `(★)` alone.  The residual inputs are
all of the *joint space-time / under-the-integral differentiation* class — the
same class already isolated as the unproven `IntervalDomainL2JointTimeRegularity`
obligation in `IntervalDomainL2FrontierBuilder.lean`:

  * `CoeffTimeDerivUnderIntegral` — `d/ds ⟨u s, eₙ⟩ = ⟨∂ₛ(u s), eₙ⟩`, i.e.
    differentiating `s ↦ ∫₀¹ cos(nπx) u(s,x) dx` under the integral sign.
    `intervalDomainClassicalRegularity` supplies only *pointwise* time
    differentiability of each slice `s ↦ u s x` (conjunct `.2.2.2`), not the
    uniform-in-`x` integrable envelope Leibniz/`hasDerivAt_integral_of_dominated`
    requires.  Genuine Mathlib gap given the present hypotheses.
  * `SpectralSeriesTermwiseDeriv` — differentiating the cosine series
    `∑ₙ e^{−(t−s)λₙ} ⟨u s, eₙ⟩ cos(nπx)` term-by-term in `s` (an
    `hasDerivAt_tsum`-style statement needing a summable dominating bound on the
    `s`-derivatives, uniform on a time-neighbourhood).  The needed decay of
    `s ↦ ⟨∂ₛ u s, eₙ⟩` in `n` is not available from the per-`t` `C²` regularity.
  * the **genuine** Neumann boundary derivative `g'(0) = g'(1) = 0`: in
    `intervalDomain`, `normalDeriv` is *defined* to be `0` at endpoints
    (`intervalDomainNormalDeriv`), so the Neumann conjunct of
    `IsPaper2ClassicalSolution` is vacuous at the boundary and does **not** yield
    the genuine one-sided derivative needed to kill the IBP boundary terms.  The
    eigenfunction identity below therefore takes `g'(0)=g'(1)=0` as an explicit
    hypothesis; supplying it for a classical solution is a further regularity
    fact about the abstract `u`.

The eigenfunction IBP identity below is the maximal reachable, fully honest
fragment; the three named items above are exactly what a future development must
add to assemble `IntervalSolutionFourierCoeffDeriv`.
-/

open MeasureTheory intervalIntegral
open ShenWork.IntervalDomain
open ShenWork.CosineSpectrum
open ShenWork.RegularityBootstrap
open scoped Topology

namespace ShenWork.IntervalSolutionCoeffDeriv

noncomputable section

/-! ## The eigenfunction integration-by-parts identity (★), sub-step (a) -/

/-- **Eigenfunction integration-by-parts identity on `[0,1]`** (the IBP-twice core).

For a function `g : ℝ → ℝ` that is `C²` on `[0,1]` — concretely: `g` has
derivative `g'` and `g'` has derivative `g''` at every point of `[0,1]`, with
`g'` and `g''` interval-integrable — and that satisfies the **genuine** Neumann
boundary condition `g'(0) = g'(1) = 0`, the raw cosine coefficient of the
spatial Laplacian `g''` equals `−(nπ)²` times the raw cosine coefficient of `g`:

  `∫₀¹ cos(nπx) · g''(x) dx = −(nπ)² · ∫₀¹ cos(nπx) · g(x) dx`.

This is the cancellation engine of the Fourier-coefficient bridge: the `−(nπ)²`
here annihilates the `+λₙ = +(nπ)²` produced by differentiating the heat factor
`e^{−(t−s)λₙ}` in `s`.  Proved by Mathlib interval integration by parts applied
twice, with both boundary terms vanishing — the first from the Neumann condition
`g'(0)=g'(1)=0`, the second from the cosine Neumann condition
`(cos)'(0)=(cos)'(1)=0` (`cosineMode_neumann_left/right`). -/
theorem intervalCosineLaplacianCoeff_eq
    (n : ℕ) {g g' g'' : ℝ → ℝ}
    (hg : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt g' (g'' x) x)
    (hg'int : IntervalIntegrable g' MeasureTheory.volume 0 1)
    (hg''int : IntervalIntegrable g'' MeasureTheory.volume 0 1)
    (hbc0 : g' 0 = 0) (hbc1 : g' 1 = 0) :
    (∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * g'' x) =
      -((n : ℝ) * Real.pi) ^ 2 *
        ∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * g x := by
  classical
  -- abbreviations: the cosine eigenfunction, its first and second derivative.
  set a : ℝ := (n : ℝ) * Real.pi with ha
  -- `cosineMode n x = cos (a x)`; record the basic derivative facts.
  have hcos_eq : ∀ x : ℝ, cosineMode n x = Real.cos (a * x) := by
    intro x; simp [cosineMode, ha]
  -- first derivative of cosineMode: `c' x = -a * sin (a x)`.
  set c : ℝ → ℝ := fun x => Real.cos (a * x) with hc
  set c' : ℝ → ℝ := fun x => -a * Real.sin (a * x) with hc'
  set c'' : ℝ → ℝ := fun x => -(a ^ 2 * Real.cos (a * x)) with hc''
  have hc_deriv : ∀ x : ℝ, HasDerivAt c (c' x) x := by
    intro x
    have h := cosineMode_hasDerivAt n x
    -- `cosineMode_hasDerivAt`: deriv is `-(a) * sin (a x)`.
    have hfun : c = cosineMode n := by funext y; rw [hc, hcos_eq y]
    rw [hfun]
    simpa [hc', ha, mul_comm, mul_left_comm, mul_assoc] using h
  have hc'_deriv : ∀ x : ℝ, HasDerivAt c' (c'' x) x := by
    intro x
    -- `c' x = -a * sin (a x)`; derivative `-a * (a * cos (a x)) = -(a² cos (a x))`.
    have hlin : HasDerivAt (fun y : ℝ => a * y) a x := by
      simpa using (hasDerivAt_id x).const_mul a
    have hsin : HasDerivAt (fun y : ℝ => Real.sin (a * y)) (a * Real.cos (a * x)) x := by
      have h := (Real.hasDerivAt_sin (a * x)).comp x hlin
      convert h using 1; ring
    have h := hsin.const_mul (-a)
    simpa [hc', hc'', pow_two, mul_comm, mul_left_comm, mul_assoc] using h
  -- continuity (for ContinuousOn hypotheses of IBP): c, c' are globally continuous.
  have hc_contg : Continuous c := continuous_iff_continuousAt.mpr (fun x => (hc_deriv x).continuousAt)
  have hc'_contg : Continuous c' := continuous_iff_continuousAt.mpr (fun x => (hc'_deriv x).continuousAt)
  have hc_cont : ContinuousOn c (Set.uIcc (0:ℝ) 1) := hc_contg.continuousOn
  have hc'_cont : ContinuousOn c' (Set.uIcc (0:ℝ) 1) := hc'_contg.continuousOn
  have hg_cont : ContinuousOn g (Set.uIcc (0:ℝ) 1) :=
    fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hg'_cont : ContinuousOn g' (Set.uIcc (0:ℝ) 1) :=
    fun x hx => (hg' x hx).continuousAt.continuousWithinAt
  -- interval integrability of the derivative factors c', c''.
  have hc'int : IntervalIntegrable c' MeasureTheory.volume 0 1 :=
    hc'_cont.intervalIntegrable
  have hc''contg : Continuous c'' := by
    rw [hc'']; fun_prop
  have hc''int : IntervalIntegrable c'' MeasureTheory.volume 0 1 :=
    hc''contg.continuousOn.intervalIntegrable
  -- Boundary facts for the cosine (Neumann): c' 0 = 0 and c' 1 = 0.
  have hc'0 : c' 0 = 0 := by simp [hc']
  have hc'1 : c' 1 = 0 := by
    have h := cosineMode_neumann_right n
    -- deriv (cosineMode n) 1 = 0, and that deriv equals c' 1.
    have : c' 1 = deriv (cosineMode n) 1 := by
      rw [← (hc_deriv 1).deriv]
      have hfun : c = cosineMode n := by funext y; rw [hc, hcos_eq y]
      rw [hfun]
    rw [this, h]
  -- HasDerivAt forms restricted to the `min/max` open interval needed by IBP.
  have hg_io : ∀ x ∈ Set.Ioo (min (0:ℝ) 1) (max 0 1), HasDerivAt g (g' x) x := by
    intro x hx; exact hg x (by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      rw [min_eq_left (by norm_num : (0:ℝ) ≤ 1), max_eq_right (by norm_num : (0:ℝ) ≤ 1)] at hx
      exact Set.mem_Icc_of_Ioo hx)
  have hg'_io : ∀ x ∈ Set.Ioo (min (0:ℝ) 1) (max 0 1), HasDerivAt g' (g'' x) x := by
    intro x hx; exact hg' x (by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      rw [min_eq_left (by norm_num : (0:ℝ) ≤ 1), max_eq_right (by norm_num : (0:ℝ) ≤ 1)] at hx
      exact Set.mem_Icc_of_Ioo hx)
  have hc_io : ∀ x ∈ Set.Ioo (min (0:ℝ) 1) (max 0 1), HasDerivAt c (c' x) x :=
    fun x _ => hc_deriv x
  have hc'_io : ∀ x ∈ Set.Ioo (min (0:ℝ) 1) (max 0 1), HasDerivAt c' (c'' x) x :=
    fun x _ => hc'_deriv x
  -- First IBP:  ∫ c · g'' = c·g'|₀¹ − ∫ c' · g'  (boundary 0 by Neumann on g').
  have hIBP1 :
      (∫ x in (0:ℝ)..1, c x * g'' x) =
        c 1 * g' 1 - c 0 * g' 0 - ∫ x in (0:ℝ)..1, c' x * g' x :=
    integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hc_cont hg'_cont hc_io hg'_io hc'int hg''int
  -- Now we want ∫ c · g'' in terms of ∫ c'' · g and relate ∫ c' · g'.
  -- From hIBP1 (boundary terms vanish via hbc0, hbc1):
  have hstep1 : (∫ x in (0:ℝ)..1, c x * g'' x) = - ∫ x in (0:ℝ)..1, c' x * g' x := by
    rw [hIBP1, hbc0, hbc1]; ring
  -- We need ∫ c' · g' .  Apply IBP again with roles (c', g) ↦ relate to ∫ c'' g.
  -- ∫ c' · g' : take u = c', v' = g', v = g  →  but that needs ∫ c' · g'  directly.
  -- Instead integrate by parts ∫ c' · g' with u = c', v = g:
  --   ∫ c' · g' = c'·g|₀¹ − ∫ c'' · g.
  have hIBP1b :
      (∫ x in (0:ℝ)..1, c' x * g' x) =
        c' 1 * g 1 - c' 0 * g 0 - ∫ x in (0:ℝ)..1, c'' x * g x :=
    integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hc'_cont hg_cont hc'_io hg_io hc''int hg'int
  have hstep2 : (∫ x in (0:ℝ)..1, c' x * g' x) = - ∫ x in (0:ℝ)..1, c'' x * g x := by
    rw [hIBP1b, hc'0, hc'1]; ring
  -- combine.
  have hcombine :
      (∫ x in (0:ℝ)..1, c x * g'' x) = ∫ x in (0:ℝ)..1, c'' x * g x := by
    rw [hstep1, hstep2]; ring
  -- finally rewrite c, c'' in cos form and pull out the constant -(a²).
  -- LHS integrand: c x * g'' x = cos (a x) * g'' x.
  -- RHS integrand: c'' x * g x = -(a² cos (a x)) * g x = -a² * (cos(a x) * g x).
  rw [show (∫ x in (0:ℝ)..1, Real.cos (a * x) * g'' x)
        = ∫ x in (0:ℝ)..1, c x * g'' x from by simp [hc]]
  rw [hcombine]
  rw [show (∫ x in (0:ℝ)..1, c'' x * g x)
        = ∫ x in (0:ℝ)..1, (-a ^ 2) * (Real.cos (a * x) * g x) from by
          apply integral_congr; intro x _; simp [hc'']; ring]
  rw [intervalIntegral.integral_const_mul]

/-! ## The named remaining obligations (the joint-time / under-integral inputs) -/

/-- **Under-the-integral time derivative of the spatial Fourier coefficient.**

`d/ds ⟨u s, eₙ⟩ = ⟨∂ₛ(u s), eₙ⟩`, i.e. differentiating
`s ↦ ∫₀¹ cos(nπx) · (intervalDomainLift (u s) x) dx` under the integral in `s`.
This is a Leibniz / `hasDerivAt_integral_of_dominated`-type statement requiring a
uniform-in-`x` integrable envelope for `∂ₛ u`, which the per-`t` `C²`
`intervalDomainClassicalRegularity` does **not** supply (it gives only pointwise
slice differentiability).  Named so the bridge can consume it. -/
def CoeffTimeDerivUnderIntegral
    (u : ℝ → intervalDomainPoint → ℝ) (ut : ℝ → intervalDomainPoint → ℝ) : Prop :=
  ∀ n : ℕ, ∀ s : ℝ,
    HasDerivAt
      (fun σ : ℝ => ∫ x in (0:ℝ)..1,
        Real.cos ((n : ℝ) * Real.pi * x) * intervalDomainLift (u σ) x)
      (∫ x in (0:ℝ)..1,
        Real.cos ((n : ℝ) * Real.pi * x) * intervalDomainLift (ut s) x) s

/-- **Term-by-term `s`-differentiation of the cosine heat series.**

The spectral value `unitIntervalCosineHeatValue (t−s) (cosineCoeffs (u s)) x` is a
`tsum` over modes; differentiating it in `s` term-by-term requires a summable
dominating bound on the `s`-derivatives of the terms, uniform on a neighbourhood
of `s` (an `hasDerivAt_tsum`-style hypothesis).  The required `n`-decay of the
coefficient time-derivatives is not available from the per-`t` `C²` regularity.
Named so the bridge can consume it. -/
def SpectralSeriesTermwiseDeriv
    (t x : ℝ) (b : ℝ → ℕ → ℝ) (b' : ℝ → ℕ → ℝ) : Prop :=
  ∀ s : ℝ, s < t →
    HasDerivAt
      (fun σ : ℝ => unitIntervalCosineHeatValue (t - σ) (b σ) x)
      ((-unitIntervalCosineHeatLaplacianValue (t - s) (b s) x)
        + unitIntervalCosineHeatValue (t - s) (b' s) x) s

end

end ShenWork.IntervalSolutionCoeffDeriv
