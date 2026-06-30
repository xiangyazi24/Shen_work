# Q2511 shen2: honest frontier from fixed windows to `IntegratedMoserFirstCrossingStep`

Repo target: `xiangyazi24/Shen_work`.

Source baseline: commit `9d9250e6fbc8e0efb30a61130cd0b6e471ed4321`, plus the local Q2503-style precrossing/window plumbing in:

```text
ShenWork/PDE/P3MoserIntegratedClosure.lean
```

This answer is **not** the old plumbing plan. It starts after the local file already has something like:

```lean
IntegratedMoserPrecrossingIntervalData
IntegratedMoserWindowUpperBoundData
IntegratedMoserWindowUpperBoundData.of_precrossing
```

and after the existing fixed-window lemmas:

```lean
integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds
integratedMoser_maxOneEnergy_timeIntegral_le_of_Icc_bound
relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound
```

## Executive recommendation

The minimal honest frontier is **not**:

```lean
IntegratedMoserWindowUpperBoundData ... -> LpPowerBoundedBefore D (p + rho) T u
```

That would be false: a time-integral bound on one window does not give a pointwise-in-time uniform bound on `(0,T)`.

The minimal honest frontier is instead a **high-excursion exclusion interface**:

> If a pointwise high excursion of `Y_{p+rho}(t)` above a candidate bound occurs, analytic information must produce a window on which the lower average of `Y_{p+rho}` is strictly larger than the upper bound supplied by `IntegratedMoserWindowUpperBoundData`.

Then the rest is pure contradiction plumbing.

So the source layer should expose one real analytic surface:

```lean
IntegratedMoserHighExcursionContradictionWindowFrontier
```

and prove, with no analytic content, that it implies:

```lean
IntegratedMoserFirstCrossingStep
```

## DAG

```text
Already-proved/local plumbing:
  IntegratedMoserPrecrossingIntervalData
  + IntegratedMoserWindowUpperBoundData.of_precrossing
  + fixed-window integrated Moser lemmas
      ↓
  fixed-window upper estimate:
    ∫_a^b Y_{p+rho} ≤ Upper(a,b,eps,Cp,Cgrad,Ceps)

Real analytic frontier:
  high pointwise excursion Y_{p+rho}(t0) > Cnext
      ↓
  choose a window [a,b] and eps, with window upper-bound data,
  plus a lower-average estimate
      ↓
  Lower(a,b,t0) ≤ ∫_a^b Y_{p+rho}
  and Upper(a,b,eps,...) < Lower(a,b,t0)

Pure contradiction:
  ∫_a^b Y_{p+rho} ≤ Upper < Lower ≤ ∫_a^b Y_{p+rho}
      ↓
  no excursion above Cnext
      ↓
  LpPowerBoundedBefore D (p+rho) T u
      ↓
  IntegratedMoserFirstCrossingStep
```

## What is pure vs analytic

### Pure topology/plumbing

These are safe to prove in Lean without new PDE claims:

1. Define the RHS of `IntegratedMoserWindowUpperBoundData.higherPowerIntegralBound` as a helper.
2. Package a contradiction window.
3. Prove `LpPowerBoundedBefore` from the contradiction-window frontier by `by_contra` and `linarith`.
4. Wrap the pointwise exponent theorem into `IntegratedMoserFirstCrossingStep`.

### Real analytic assumptions

These must remain in the frontier, not hidden in plumbing:

1. **High-excursion thickness:** from a large pointwise value of `Y_{p+rho}(t0)`, get a nontrivial time window where the function remains large enough on average.
2. **Lower-average estimate:** prove a quantitative lower bound `L ≤ ∫_a^b Y_{p+rho}`. This may come from continuity plus positive window length, or from absolute continuity/modulus control.
3. **Modulus / absolute continuity:** needed to choose a window with controlled length and retained height. Plain `ContinuousOn` gives a local window but no useful quantitative lower bound uniform enough to close the Moser step.
4. **Endpoint/interior placement:** the window must lie in `(0,T)` or at least inside the side conditions of the local precrossing/window data.
5. **`eps` / `Ceps` quantitative dependence:** the relative-Moser constant `Ceps` depends on `eps`. A proof must show that `eps` and the high-excursion threshold can be chosen so the fixed-window upper bound is below the lower average. This is a genuine analytic/quantitative frontier.
6. **Nonnegativity of higher-power energy/integrals on abstract domains:** do not assume abstract `D.integral` is positive unless the domain API or a specialized interval-domain lemma supplies it.

## Minimal code-shaped interface

Put this after the local `IntegratedMoserWindowUpperBoundData` definition and before the final `moser_iteration_chain_of_integrated_first_crossing_step` consumer section.

If writing in a separate scratch test file, use:

```lean
import ShenWork.PDE.P3MoserIntegratedClosure

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

Inside `P3MoserIntegratedClosure.lean` itself, do **not** add a new import for these snippets.

### 1. Pure helper: name the fixed-window upper RHS

This assumes the local Q2503 `IntegratedMoserWindowUpperBoundData` has the fields proposed in Q2501:

```lean
Cp H Cgrad Ceps higherPowerIntegralBound
```

If your local field names differ, only this helper needs renaming.

```lean
namespace IntegratedMoserWindowUpperBoundData

/-- The explicit RHS in the fixed-window bound for `∫ Y_{p+rho}`.  Naming it
prevents every later frontier from repeating the long expression. -/
def higherPowerRHS
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b eps : ℝ}
    (h : IntegratedMoserWindowUpperBoundData D u T rho p0 p a b eps) : ℝ :=
  eps * ((h.Cp + h.Cgrad * p * h.H) / 2) +
    (b - a) * (h.Ceps * h.Cp)

/-- The existing fixed-window `higherPowerIntegralBound`, rewritten using the
named RHS. -/
theorem higherPowerIntegral_le_higherPowerRHS
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b eps : ℝ}
    (h : IntegratedMoserWindowUpperBoundData D u T rho p0 p a b eps) :
    ∫ s in a..b,
        D.integral (fun x => (u s x) ^ (p + rho)) ≤
      h.higherPowerRHS := by
  simpa [higherPowerRHS] using h.higherPowerIntegralBound

end IntegratedMoserWindowUpperBoundData
```

This is pure plumbing. It proves no new estimate.

### 2. Analytic contradiction-window data

This is the smallest honest object that turns one high excursion into a contradiction with one fixed-window upper bound.

```lean
/-- Data produced by the real high-excursion argument.

A value `Y_{p+rho}(t0)` above the eventual candidate bound should produce such a
window.  The fields intentionally include both the fixed-window upper-bound data
and a separate lower-average estimate.  The lower-average and strict-gap fields
are the genuine analytic content; they should not be derived from time-integral
boundedness alone. -/
structure IntegratedMoserHighExcursionContradictionWindow
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 p : ℝ) : Prop where
  a : ℝ
  b : ℝ
  eps : ℝ
  eps_pos : 0 < eps
  window : IntegratedMoserWindowUpperBoundData D u T rho p0 p a b eps
  lowerBound : ℝ
  lowerAverage :
    lowerBound ≤
      ∫ s in a..b,
        D.integral (fun x => (u s x) ^ (p + rho))
  upper_lt_lower :
    window.higherPowerRHS < lowerBound
```

The analytic proof that constructs this data will likely combine:

```text
high excursion at t0
+ continuity / absolute continuity / modulus
+ thickness of a high-excursion window
+ lower-average estimate
+ quantitative choice of eps against Ceps
+ fixed-window upper-bound supplier
```

None of those should be faked in this file.

### 3. The actual analytic frontier

This frontier is parameterized by a fixed current exponent `p`.  It says: for this exponent, there is a candidate next-exponent bound `Cnext`, and every putative pointwise violation above `Cnext` yields a contradiction window.

```lean
/-- Honest frontier for excluding high excursions of `Y_{p+rho}`.

This is the only new analytic surface needed between the fixed-window estimates
and `LpPowerBoundedBefore D (p+rho) T u`.  It is deliberately stronger than mere
time-integral control: it requires that every high pointwise excursion generate a
window where the fixed-window upper bound is strictly incompatible with a
lower-average estimate. -/
structure IntegratedMoserHighExcursionContradictionWindowFrontier
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 p : ℝ) : Prop where
  Cnext : ℝ
  contradictionWindow :
    ∀ t, 0 < t → t < T →
      Cnext < D.integral (fun x => (u t x) ^ (p + rho)) →
        IntegratedMoserHighExcursionContradictionWindow D u T rho p0 p
```

This is the recommended minimal interface. It is not tautological: it does not assert `Y_{p+rho}(t) ≤ Cnext`; it asserts a concrete contradiction mechanism through fixed-window data.

### 4. Pure theorem: contradiction-window frontier gives the next Lp bound

```lean
/-- Pure contradiction step: a high-excursion contradiction-window frontier gives
`LpPowerBoundedBefore` at the next exponent.

No time-integral-to-pointwise principle is used here.  The only reason a
pointwise bound follows is that every pointwise violation is assumed to produce a
window whose lower and upper integral bounds contradict each other. -/
theorem LpPowerBoundedBefore_of_highExcursionContradictionWindowFrontier
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p : ℝ}
    (hfront :
      IntegratedMoserHighExcursionContradictionWindowFrontier
        D u T rho p0 p) :
    LpPowerBoundedBefore D (p + rho) T u := by
  refine ⟨hfront.Cnext, ?_⟩
  intro t ht0 htT
  by_contra hnot
  have hhigh :
      hfront.Cnext < D.integral (fun x => (u t x) ^ (p + rho)) :=
    lt_of_not_ge hnot
  let hwin := hfront.contradictionWindow t ht0 htT hhigh
  have hupper :=
    IntegratedMoserWindowUpperBoundData.higherPowerIntegral_le_higherPowerRHS
      hwin.window
  have hlower := hwin.lowerAverage
  have hgap := hwin.upper_lt_lower
  linarith
```

This theorem is the key guardrail: the proof uses a **contradiction window**, not a bare integral estimate.

### 5. Step-level frontier and consumer theorem

Now package the exponentwise frontier into the exact existing step predicate.

```lean
/-- Exponentwise high-excursion exclusion frontiers sufficient to produce the
integrated first-crossing step.

The `hLp` argument is included because the current-exponent Lp bound is needed by
the window plumbing to get the current `Cp` on each candidate window. -/
structure IntegratedMoserFirstCrossingFromWindowFrontier
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop where
  highExcursion :
    ∀ p, p0 ≤ p →
      LpPowerBoundedBefore D p T u →
        IntegratedMoserHighExcursionContradictionWindowFrontier
          D u T rho p0 p

/-- The final pure wrapper from the honest window/frontier interface to the
existing `IntegratedMoserFirstCrossingStep` atom. -/
theorem integratedMoserFirstCrossingStep_of_windowFrontier
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (hfront : IntegratedMoserFirstCrossingFromWindowFrontier D u T rho p0) :
    IntegratedMoserFirstCrossingStep D u T rho p0 := by
  intro p hp hLp
  exact LpPowerBoundedBefore_of_highExcursionContradictionWindowFrontier
    (hfront.highExcursion p hp hLp)
```

This should be the only theorem that claims the step. Its proof is purely structural; the analytic burden is entirely in `IntegratedMoserFirstCrossingFromWindowFrontier.highExcursion`.

## Optional finer-grained analytic DAG interfaces

Do not add these unless you want the frontier split into smaller future tasks. The single `IntegratedMoserHighExcursionContradictionWindowFrontier` above is the minimal source-facing interface. If you want to expose subfrontiers, split them as follows.

### A. High-excursion geometry / lower average

```lean
/-- Analytic geometry of high excursions.  This should be proved from continuity,
absolute continuity, or a quantitative modulus, not from an integral upper bound. -/
structure IntegratedMoserHighExcursionLowerAverageFrontier
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 p Cnext : ℝ) : Prop where
  chooseWindow :
    ∀ t, 0 < t → t < T →
      Cnext < D.integral (fun x => (u t x) ^ (p + rho)) →
        ∃ a b lowerBound,
          0 < a ∧ a ≤ b ∧ b < T ∧
          lowerBound ≤
            ∫ s in a..b,
              D.integral (fun x => (u s x) ^ (p + rho))
```

This owns the high-excursion thickness and lower-average estimates.

### B. Window upper-bound supplier

This is mostly plumbing once the local `of_precrossing` constructor exists, but it may still require endpoint nonnegativity and side conditions.

```lean
/-- Supplier for fixed-window upper-bound data on candidate windows.  This is the
bridge from the already-proved local fixed-window lemmas into the high-excursion
argument. -/
structure IntegratedMoserWindowUpperBoundSupplier
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 p : ℝ) : Prop where
  supply :
    ∀ a b eps, 0 < eps →
      0 < a → a ≤ b → b < T →
        IntegratedMoserWindowUpperBoundData D u T rho p0 p a b eps
```

If the actual local constructor needs more inputs, such as `hp_nonneg`, `hp_rho`, or endpoint nonnegativity, include those fields explicitly in this supplier. Do not hide them.

### C. Quantitative eps/Ceps closure

This is the delicate part: the upper bound includes the relative-interpolation constant `Ceps`, so the proof must know enough about its dependence on `eps`, `p`, `Cp`, and the window length.

```lean
/-- Quantitative closure of the fixed-window upper bound against a lower-average
window.  This is where `eps` choice and `Ceps` dependence live. -/
structure IntegratedMoserEpsCepsClosureFrontier
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 p : ℝ) : Prop where
  closeWindow :
    ∀ a b lowerBound,
      0 < a → a ≤ b → b < T →
      lowerBound ≤
        ∫ s in a..b,
          D.integral (fun x => (u s x) ^ (p + rho)) →
      ∃ eps, ∃ hwin :
        IntegratedMoserWindowUpperBoundData D u T rho p0 p a b eps,
          0 < eps ∧ hwin.higherPowerRHS < lowerBound
```

Combining A + C gives the minimal `IntegratedMoserHighExcursionContradictionWindowFrontier`. But for the next Lean plumbing, I would avoid adding A/B/C unless you are ready to start proving or specializing them.

## Why not use a bare time-integral bound?

The false route would be:

```lean
(∀ a b, ∫ s in a..b, Yq s ≤ U a b) -> LpPowerBoundedBefore D q T u
```

This is invalid. Large pointwise spikes can have small time measure. Even continuity only gives a positive-width window around a spike; it does not by itself give a width or lower average that beats the Moser upper expression uniformly in the exponent/threshold. The missing ingredient is exactly the high-excursion window/lower-average/eps-Ceps frontier above.

## What not to prove

Do **not** prove:

```lean
IntegratedMoserWindowUpperBoundData D u T rho p0 p a b eps ->
  LpPowerBoundedBefore D (p + rho) T u
```

Do **not** prove:

```lean
(∃ C, ∀ a b, ∫ s in a..b, Y_{p+rho} s ≤ C) ->
  LpPowerBoundedBefore D (p + rho) T u
```

Do **not** prove:

```lean
IntegratedMoserFirstCrossingRegularity D u T p0 ->
  IntegratedMoserFirstCrossingStep D u T rho p0
```

Regularity gives continuity/integrability, not the quantitative high-excursion exclusion.

Do **not** hide the `eps/Ceps` dependence behind a generic `∃ Ceps`; this dependence is exactly what decides whether the fixed-window upper bound can contradict the lower average.

Do **not** derive endpoint/nonnegativity facts for arbitrary `BoundedDomainData.integral` unless the domain API supplies them. For interval-domain specializations, use concrete interval-domain nonnegativity lemmas explicitly.

## Recommended next source patch

Add only the two pure structures and two pure theorem wrappers:

```lean
IntegratedMoserWindowUpperBoundData.higherPowerRHS
IntegratedMoserWindowUpperBoundData.higherPowerIntegral_le_higherPowerRHS
IntegratedMoserHighExcursionContradictionWindow
IntegratedMoserHighExcursionContradictionWindowFrontier
LpPowerBoundedBefore_of_highExcursionContradictionWindowFrontier
IntegratedMoserFirstCrossingFromWindowFrontier
integratedMoserFirstCrossingStep_of_windowFrontier
```

This gives downstream files a precise target: prove the high-excursion contradiction-window frontier, not the whole step directly and not a false integral-to-pointwise implication.
