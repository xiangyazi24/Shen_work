# Q3220 (cron1) — uniform H¹ bound route

Repository: `xiangyazi24/Shen_work`  
Branch: `chatgpt-scratch`  
Target file: `scratch/_CHATGPT_DROP_cron1.md`

## Executive answer

The mathematically simplest route is **Route C**, but in a very specific form:

```text
prove the H¹ energy derivative by a finite-difference-in-time + spatial-IBP lemma,
not by differentiating u_x in time and not by spectral Parseval.
```

This avoids the missing `u_xt`. The key identity is the finite-difference formula

```text
H1energy(u,s) - H1energy(u,t)
  = -1/2 ∫₀¹ (u_xx(s,x) + u_xx(t,x)) * (u(s,x) - u(t,x)) dx,
```

using Neumann boundary data at both slices. After division by `s-t`, the limit uses only

```text
u_xx(s,·) -> u_xx(t,·) uniformly on [0,1],
(u(s,·)-u(t,·))/(s-t) -> u_t(t,·) uniformly on [0,1].
```

The second convergence follows from pointwise `HasDerivAt` in time plus joint continuity of `u_t`, via the interval FTC / uniform continuity on compact boxes. No mixed derivative `u_xt` is needed.

So the recommended route is:

```text
1. Prove a single-solution L² energy identity and sliding-window ∫H1energy bound.
2. Prove H1EnergyIdentity by the finite-difference spatial-IBP route.
3. Feed the already-landed algebraic H¹ DI and uniform averaging / Gronwall assembly.
```

Route A is sound but overbuilds spectral infrastructure. Route B is useful for a near-zero/local gradient bound, but it is not the cleanest global H¹ route because the source contains `u_x` and leads to a Volterra/fractional-Gronwall bootstrap that still needs uniform lower-order bounds and mild representation machinery.

## Current repo alignment

The current H¹ files already point to the correct endpoint. `IntervalDomainH1GradientBound.lean` documents the intended sequence:

```text
Y₂ bounded, ∫₀ᵀ G₂ bounded
H¹ DI without ||u||∞
Uniform Gronwall / averaging
pointwise gradient bound at p=2
```

It also shows that the algebraic part is already separated:

```text
h1_diffIneq_of_agmon_bounds
produce_pointwiseGradientBound_full
produce_pointwiseGradientBound_general_pExp
```

`IntervalChiNegH1Energy.lean` is even more explicit: it carries exactly two obligations:

```text
H1EnergyIdentity
hWindow : sliding-window ∫ H1energy ≤ C
```

Those are the two targets. Do not reopen the algebraic DI unless its hypotheses need renaming.

## Route comparison

### Route A — spectral derivative of `Σ λ_k |c_k|²`

Sound, but not the least infrastructure.

It needs:

```text
Parseval bridge for gradient energy,
per-mode time derivative of cosine coefficients,
termwise differentiation of Σ λ_k c_k(t)^2,
weighted summability of the derivative majorant,
cosine reconstruction / coefficient identity for u_t,
O(1/k²) or stronger coefficient decay for C² Neumann slices.
```

For a fully spectral local-existence chain this can be natural. But for an arbitrary classical solution record that already gives spatial C², Neumann boundary conditions, time derivative, PDE, and joint continuity, the spectral route is longer than necessary.

Use Route A only if the spectral H¹ derivative file is already almost complete and importing it creates no new hrealizes-style obligations. Otherwise, it is not the fastest path.

### Route B — direct semigroup/Duhamel gradient estimate

This can work for local gradient bounds, but it is not the cleanest uniform H¹ proof.

A typical estimate would be

```text
||u_x(t)||₂ or ||u_x(t)||∞
  ≤ C δ^(-1/2) ||u(t-δ)|| + C ∫_{t-δ}^t (t-s)^(-1/2) ||g(s)|| ds.
```

The problem is that

```text
g = -χ₀ chemotaxis + logistic
```

contains the taxis term with `u_x`, e.g.

```text
u_x * v_x + u * v_xx
```

or the divergence-form equivalent. Thus the estimate becomes a Volterra inequality for the gradient norm:

```text
M(t) ≤ C δ^(-1/2) lower_order + C ∫ (t-s)^(-1/2) (a M(s) + b) ds.
```

This is not impossible. On a short window one can absorb using

```text
∫₀^δ r^(-1/2) dr = 2 sqrt δ,
```

or use fractional Gronwall. But formalizing this requires:

```text
mild/Duhamel representation for the classical solution,
heat gradient estimate in the exact norm,
uniform resolver bounds for v_x and v_xx,
control of u and u^γ without already using the desired H¹ -> L∞ consequence,
fractional/Volterra or small-window absorption formalization.
```

If uniform L∞ is already available independently, Route B becomes quite viable. In the present dependency chain, however, H¹ is supposed to produce L∞, so Route B risks a circular dependency unless all coefficients in the Volterra inequality are controlled from lower-order estimates only.

Best use of Route B here:

```text
near-zero/local H¹ bound hlocal
```

for the uniform-Gronwall assembly, or a fallback if Route C’s energy identity stalls.

### Route C — energy identity via finite differences and IBP

This is the best route.

The classical calculation

```text
y(t) = 1/2 ∫ u_x(t)^2
```

usually writes

```text
y' = ∫ u_x u_xt.
```

But you do not need `u_xt`. Use finite differences:

```text
y(s)-y(t)
  = 1/2 ∫ (u_x(s)^2 - u_x(t)^2)
  = 1/2 ∫ (u_x(s)+u_x(t)) * ∂x(u(s)-u(t))
  = -1/2 ∫ (u_xx(s)+u_xx(t)) * (u(s)-u(t)).
```

The boundary term is

```text
[(u_x(s)+u_x(t)) * (u(s)-u(t))]₀¹ = 0
```

because both time slices satisfy Neumann boundary conditions.

Divide by `s-t` and let `s -> t`:

```text
y'(t) = -∫ u_xx(t,x) * u_t(t,x) dx.
```

Then substitute the PDE:

```text
u_t = u_xx - χ₀ * (u_x v_x + u v_xx) + u(a - b u^α).
```

So

```text
y' = -∫ u_xx²
     + χ₀ ∫ u_xx (u_x v_x + u v_xx)
     - ∫ u_xx * u(a - b u^α).
```

The reaction term can be integrated by parts as usual:

```text
-∫ u_xx f(u) = ∫ f'(u) u_x²,
```

provided the endpoint boundary term vanishes. Since `u_x=0` at endpoints, it does.

This produces the exact `H1EnergyIdentity` already expected by `IntervalChiNegH1Energy.lean`.

## The key Lean lemma for Route C

Create a new file, e.g.

```text
ShenWork/Paper2/IntervalChiNegH1EnergyIdentity.lean
```

with two stages.

```lean
import ShenWork.Paper2.IntervalChiNegH1Energy
import ShenWork.Paper2.IntervalDomainL2UEnergyUniform
import ShenWork.Paper2.IntervalDomainEnergyStep
import ShenWork.PDE.IntervalDomain
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1EnergyIdentity

open Set Filter Topology MeasureTheory
open ShenWork.IntervalDomain
  (intervalDomain intervalDomainPoint intervalDomainLift)
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
  (H1energy lapL2sq H1EnergyIdentity)

/-!
Target 1: finite-difference identity.

This lemma uses only spatial C² and Neumann data at the two time slices.
No time derivative is involved.
-/

-- theorem H1energy_sub_eq_spatialIBP
--     {u : ℝ → intervalDomainPoint → ℝ} {s t : ℝ}
--     (hC2s : ContDiffOn ℝ 2 (intervalDomainLift (u s)) (Set.Icc (0 : ℝ) 1))
--     (hC2t : ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1))
--     (hNs0 : derivWithin (intervalDomainLift (u s)) (Set.Icc (0 : ℝ) 1) 0 = 0)
--     (hNs1 : derivWithin (intervalDomainLift (u s)) (Set.Icc (0 : ℝ) 1) 1 = 0)
--     (hNt0 : derivWithin (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) 0 = 0)
--     (hNt1 : derivWithin (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) 1 = 0) :
--     H1energy u s - H1energy u t
--       = -(1/2) * ∫ x in (0 : ℝ)..1,
--           (deriv (fun y => deriv (intervalDomainLift (u s)) y) x
--             + deriv (fun y => deriv (intervalDomainLift (u t)) y) x)
--           * (intervalDomainLift (u s) x - intervalDomainLift (u t) x)

/-!
Target 2: derivative of H1energy without u_xt.

Use Target 1, divide by `s-t`, and pass to the limit using:
  * joint continuity of u_xx,
  * uniform convergence of time difference quotients to u_t from time-FTC/joint continuity.
-/

-- theorem H1energy_hasDerivAt_spatialIBP
--     {p : CM2Params} {T τ : ℝ}
--     {u v : ℝ → intervalDomainPoint → ℝ}
--     (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
--     (hτ0 : 0 < τ) (hτT : τ < T) :
--     HasDerivAt (H1energy u)
--       (-(∫ x in (0 : ℝ)..1,
--           deriv (fun y => deriv (intervalDomainLift (u τ)) y) x
--             * intervalDomain.timeDeriv u τ ⟨x, by sorry⟩)) τ

/-!
Target 3: substitute PDE and integrate by parts in space to produce the packaged
H1EnergyIdentity shape consumed downstream.
-/

-- theorem H1EnergyIdentity_of_classicalSolution
--     {p : CM2Params} {T τ : ℝ}
--     {u v : ℝ → intervalDomainPoint → ℝ}
--     (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
--     (hτ0 : 0 < τ) (hτT : τ < T) :
--     ∃ taxisX uvxx reactX,
--       H1EnergyIdentity p u τ taxisX uvxx reactX ∧
--       -- plus the term definitions / bounds needed by the DI producer
--       True

end ShenWork.Paper2.IntervalChiNegH1EnergyIdentity
```

The exact endpoint derivative API should use the repo’s existing lemmas:

```text
intervalDomain_solution_derivWithin_u_left_zero
intervalDomain_solution_derivWithin_u_right_zero
intervalDomain_spatial_integrationByParts_identity
```

Do not state the lemma with `u_xt` or `deriv (fun t => deriv (u t))`.

## How to prove uniform convergence of the time difference quotient

The required analytic lemma is small and reusable:

```text
If ∀x, HasDerivAt (fun s => F s x) (Ft t x) t
and Ft is jointly continuous on a compact time-space box,
then (F(t+h,x)-F(t,x))/h -> Ft(t,x) uniformly in x.
```

In Lean, the easiest path is not a raw epsilon proof for difference quotients. Use the interval FTC in time:

```text
F(t+h,x) - F(t,x) = ∫ r in t..t+h, Ft(r,x)
```

then

```text
(F(t+h,x)-F(t,x))/h - Ft(t,x)
  = average_{r ∈ [t,t+h]} (Ft(r,x)-Ft(t,x)).
```

Joint continuity of `Ft` gives uniform continuity on a compact neighborhood of `(t,[0,1])`, so the averaged difference tends uniformly to zero.

This avoids any mixed derivative and is often simpler than trying to use pointwise `HasDerivAt` directly under the spatial integral.

## Route B: can it work despite `g` depending on `u_x`?

Yes, but it is not the least-infrastructure path.

A local window estimate would look like:

```text
M(t) := sup_{r ∈ [t₀,t₀+δ]} ||u_x(r)||

M(t) ≤ C δ^{-1/2} ||u(t₀)||∞
       + C sqrt(δ) * M(t)
       + C δ * lower_order.
```

For small `δ`, absorb `C sqrt(δ) * M(t)` to the left. This gives a local bound. Then iterate windows.

But this requires:

```text
Duhamel representation for the classical solution on every restart window,
heat gradient bounds in the right norm,
uniform resolver bounds for v_x and v_xx,
control of u and u^γ without already using the desired H¹ -> L∞ consequence,
fractional/Volterra or small-window absorption formalization.
```

If uniform L∞ is already available independently, Route B becomes quite viable. In the current chain, however, H¹ is supposed to produce L∞, so Route B risks a circular dependency unless all coefficients in the Volterra inequality are controlled from lower-order estimates only.

Best use of Route B here:

```text
near-zero/local H¹ bound hlocal
```

for the uniform-Gronwall assembly, or a fallback if Route C’s energy identity stalls.

## Can we avoid `HasDerivAt (H1energy u)` entirely?

Yes in principle, but not cheaply in the current architecture.

A pure semigroup proof could bound `||u_x(t)||` directly and never define `H1energy'`. But that is Route B and requires the Volterra/Duhamel infrastructure above.

A weak-energy proof could integrate the PDE over time and prove an integral inequality for `H1energy` without a pointwise derivative. But uniform Gronwall in the repo is already wired around a differential inequality / averaged DI. Replacing it would require a new integral-form uniform-Gronwall theorem plus an integral H¹ estimate. That is possible, but it is not smaller than proving the finite-difference `HasDerivAt` identity.

Therefore, for this repo, do not avoid `HasDerivAt` entirely. Prove it by Route C, not by `u_xt`.

## Sliding-window dissipation bound

The sliding-window bound

```text
∫_{τ-1}^{τ} H1energy u s ds ≤ C
```

should be derived from a **single-solution L² energy identity**, not from the L² difference energy.

Testing the PDE with `u` gives, schematically,

```text
1/2 d/dt ∫ u² + ∫ u_x²
  = taxis terms + ∫ u²(a - b u^α).
```

The taxis terms can be bounded using resolver/flux bounds and Young:

```text
|∫ u u_x v_x| ≤ ε ∫ u_x² + C ∫ u²,
|∫ u² v_xx| ≤ C ∫ u²       (or handled in divergence form).
```

The logistic term satisfies

```text
∫ u²(a - b u^α) ≤ a ∫ u².
```

Thus, for a bounded solution / lower-order estimate,

```text
d/dt ∫u² + c ∫u_x² ≤ C(1 + ∫u²).
```

Integrating over a window gives

```text
∫_{τ-1}^{τ} ∫u_x² ≤ C.
```

Since

```text
H1energy = 1/2 ∫u_x²,
```

this is exactly the needed `hWindow`.

This single-solution L² energy identity is much easier than the H¹ identity because it only differentiates

```text
∫ u(t,x)^2 dx,
```

which needs `u_t` but not any spatial derivative of `u_t`. The classical solution record already gives pointwise time differentiability and joint continuity of `u_t`.

### Target file for the window producer

```lean
import ShenWork.Paper2.IntervalChiNegH1Energy
import ShenWork.Paper2.IntervalDomainL2UEnergyUniform
import ShenWork.Paper2.IntervalDomainEnergyStep
import ShenWork.PDE.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalSingleSolutionL2Window

open Set Filter Topology MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy (H1energy)

/-!
Target theorem: single-solution L² energy identity and window dissipation.
-/

-- def L2energy (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) : ℝ :=
--   (1/2 : ℝ) * ∫ x in (0 : ℝ)..1, (intervalDomainLift (u t) x)^2

-- theorem L2energy_hasDerivAt_of_classicalSolution
--     {p : CM2Params} {T t : ℝ}
--     {u v : ℝ → intervalDomainPoint → ℝ}
--     (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
--     (ht0 : 0 < t) (htT : t < T) :
--     HasDerivAt (L2energy u)
--       (∫ x in (0 : ℝ)..1,
--          intervalDomainLift (u t) x * intervalDomain.timeDeriv u t ⟨x, by sorry⟩) t

-- theorem singleSolution_H1_window_bound
--     {p : CM2Params} {T : ℝ}
--     {u v : ℝ → intervalDomainPoint → ℝ}
--     (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
--     (lowerOrderBounds : True) :
--     ∃ C, ∀ τ, 1 ≤ τ → τ < T →
--       ∫ s in (τ - 1)..τ, H1energy u s ≤ C

end ShenWork.Paper2.IntervalSingleSolutionL2Window
```

The proof can reuse the repo’s existing L² difference-energy IBP infrastructure, but it should be a new single-solution theorem rather than trying to force the difference lemma with a zero solution.

## Recommended dispatch order

1. **Single-solution L² window producer**
   * easier `HasDerivAt ∫u²`;
   * gives `hWindow` for the existing H¹ uniform bound.

2. **Finite-difference H¹ energy identity**
   * prove `H1EnergyIdentity` without `u_xt`.

3. **Term bounds feeding existing algebra**
   * taxis-gradient term;
   * `u v_xx` term via elliptic relation / Agmon as already planned;
   * reaction derivative term.

4. **Existing assembly**
   * `h1_diffIneq_of_agmon_bounds`;
   * `chiNeg_H1_norm_bound` / `produce_pointwiseGradientBound_full`;
   * `produce_pointwiseGradientBound_general_pExp` if needed.

5. **Use Route B only for local start if needed**
   * near-zero `hlocal : H1energy ≤ Ylocal` on `(0,1]`;
   * or fallback if direct H¹ identity stalls.

## Answers to the numbered questions

### 1. Least new Lean/Mathlib infrastructure

Route C, via finite differences, needs the least new infrastructure.

It uses:

```text
spatial IBP already in the repo,
Neumann boundary data already in the classical solution record,
time differentiability and joint continuity already in the classical solution record,
standard interval FTC / uniform continuity lemmas.
```

Route A needs more spectral infrastructure. Route B needs Duhamel representation plus Volterra/fractional-Gronwall machinery.

### 2. Can Route B work despite `g` depending on `u_x`?

Yes, but it becomes a fixed-point/Volterra inequality for the gradient. It can be closed on small windows by absorption or fractional Gronwall if lower-order coefficients are uniformly bounded. In the current chain, it is better as a local bound tool than as the global H¹ route.

### 3. Can we avoid proving `HasDerivAt (H1energy u)`?

Yes via a full semigroup gradient estimate route, but that is not the shortest route in this repo. The existing uniform-Gronwall/H¹ machinery wants a differential inequality. Prove `HasDerivAt` by finite differences and spatial IBP instead.

### 4. Is the single-solution sliding-window dissipation bound derivable?

Yes. It should come from testing the single PDE with `u`, proving a single-solution L² energy identity, and integrating the resulting dissipation inequality over windows. The existing L² difference energy is adjacent infrastructure, but the clean missing theorem is a single-solution L² energy/window producer.

## Bottom line

The fastest faithful path is:

```text
single-solution L² window bound
+ finite-difference H¹ energy identity without u_xt
+ existing H¹ algebra / uniform averaging
```

Do not make the spectral route the main path unless it is already nearly complete. Do not make the semigroup/Duhamel route the main path unless the direct H¹ identity stalls; it solves a harder Volterra problem and may reintroduce L∞ circularity.
