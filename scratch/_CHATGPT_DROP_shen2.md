# Q2668 shen2: endpoint power-energy continuity at `0`

Repo target: `xiangyazi24/Shen_work`, Lean 4.

Focus files:

```text
ShenWork/PDE/P3MoserEnergyContinuity.lean
ShenWork/PDE/P3MoserRegularityProducer.lean
```

Question: can the current residual

```lean
atZero : ∀ p, p0 ≤ p →
  ContinuousWithinAt
    (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
    (Set.Icc (0 : ℝ) T) 0
```

be proved locally from

```lean
InitialTrace intervalDomain u₀ u
PositiveInitialDatum intervalDomain u₀
IsPaper2GlobalClassicalSolution intervalDomain params u v
```

plus an existing boundedness condition?

## Answer

No. With the current repository interfaces, `atZero` is **not** provable from those assumptions.

The obstruction is not a missing algebraic trick. It is that the assumptions do not constrain the stored time-zero slice `u 0`, while `atZero` is continuity of a function whose value at `0` is computed from that stored slice.

`InitialTrace` only says:

```lean
∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
  intervalDomain.supNorm (fun x => u t x - u₀ x) < ε
```

So it is a positive-time right trace to `u₀`. It says nothing about `u 0`.

Similarly, `IsPaper2GlobalClassicalSolution` unfolds to classical-solution data on every finite positive horizon, but the classical fields are all interior-time fields: they quantify over `0 < t` and `t < T`. They also do not constrain `u 0`.

The boundedness predicates I found do not fix this:

* `IsPaper2Bounded` is eventual atTop boundedness.
* `IsPaper2BoundedBefore` only quantifies over `0 < t < Tmax`.
* `LpPowerBoundedBefore` only quantifies over `0 < t < Tmax`.
* The a-priori/global packages provide positive-time or bounded-initial data, not an equality between `u 0` and `u₀`.

Thus one can keep all existing assumptions unchanged and redefine only the time-zero slice:

```text
u♯ t = u t       for t ≠ 0
u♯ 0 = w         for an arbitrary interval profile w
```

The positive-time trace, global classical-solution property, and positive-time boundedness properties are unchanged. But

```lean
intervalDomain.integral (fun x => (u♯ 0 x) ^ p)
```

can be changed arbitrarily enough to break endpoint continuity at `0`. This is the core reason no repository-local theorem can derive `atZero` from the listed assumptions.

## What `PositiveInitialDatum` does and does not give

`PositiveInitialDatum intervalDomain u₀` gives admissibility of `u₀` and positivity on the open spatial interior. For the concrete interval domain, admissibility includes boundedness and continuity of `u₀`, which is useful for future analytic trace-to-energy lemmas.

But it still does not identify `u 0` with `u₀`.

Also, for real powers, the exponent regime matters. If one wants to derive power-energy convergence from an `L∞`/sup-norm trace, then a clean theorem needs assumptions such as:

* a positive-power ladder, for example `0 < p0`, if only continuity of `r ↦ r^p` near nonnegative values is used;
* or a uniform positive floor, e.g. `PaperPositiveInitialDatum`, if negative powers or powers near zero must be handled safely;
* boundedness/non-vacuity data for the relevant sup-norm ranges, as seen in the existing L² initial-vanishing proof pattern.

Those are analytic requirements for proving the **right-limit** of the power energy. They still do not supply the missing equality at the stored endpoint value `u 0`.

## Existing nearby evidence

The closest existing pattern is in `IntervalDomainL2UFrontierAssembly.lean`: the shared `InitialTrace` is used to prove an initial-vanishing statement for the **positive-time limit** of an L² difference energy. That proof additionally carries a bounded initial datum witness and works with `0 < s`. It does not prove closed-time continuity at a stored value `s = 0`.

This is the same structural issue here: an `InitialTrace` theorem can at best prove a right-limit to the energy of `u₀`; it cannot prove that the value of the energy function at `0`, which is the energy of `u 0`, is the same number.

## Minimal honest residual

For the current `P3MoserEnergyContinuity` wrapper, the honest residual is still the existing `atZero` field. The right endpoint is already discharged by the global-classical wrapper using a longer horizon; only the left endpoint remains genuinely external.

If we want to state the residual in terms of `u₀` rather than directly as `atZero`, the minimal semantic split is:

```lean
-- Right-limit of positive-time powers to the datum energy.
∀ p, p0 ≤ p →
  Tendsto
    (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
    (𝓝[Set.Ioc (0 : ℝ) T] 0)
    (𝓝 (intervalDomain.integral (fun x => (u₀ x) ^ p)))
```

plus

```lean
-- Stored endpoint value has the datum power energy.
∀ p, p0 ≤ p →
  intervalDomain.integral (fun x => (u 0 x) ^ p) =
    intervalDomain.integral (fun x => (u₀ x) ^ p)
```

A stronger and usually more natural endpoint compatibility residual is simply:

```lean
u 0 = u₀
```

but `u 0 = u₀` by itself is not currently enough as a local one-line proof of `atZero`; one still needs the analytic theorem converting `InitialTrace` into power-energy convergence. That theorem is not present in the searched local files.

## Exact Lean wrapper code for the honest residual

This code does **not** pretend to derive `atZero` from `InitialTrace`. It just names the honest residual and feeds it into the existing global-classical endpoint wrapper. It belongs in `P3MoserEnergyContinuity.lean` or a tiny adjacent file; it does not touch high-excursion or threshold files.

```lean
import ShenWork.PDE.P3MoserEnergyContinuity
import ShenWork.Paper2.Statements

open MeasureTheory Set Filter
open ShenWork.IntervalDomain
open ShenWork.Paper2
open scoped Interval Topology

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

/-- The remaining honest left-endpoint power-energy continuity residual.

`InitialTrace intervalDomain u₀ u` only controls positive times and does not
identify the stored value `u 0` with `u₀`, so the current repository cannot derive
this from `InitialTrace` alone. -/
def IntervalDomainInitialPowerEnergyContinuityAtZero
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p →
    ContinuousWithinAt
      (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
      (Set.Icc (0 : ℝ) T) 0

/-- Build the full endpoint package from the honest left-endpoint residual and a
global classical solution. The right endpoint is produced by the existing
`T + 1` interior-time argument. -/
theorem intervalDomain_powerEnergyEndpointContinuity_of_initialPowerEnergyContinuity
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (hzero : IntervalDomainInitialPowerEnergyContinuityAtZero u T p0) :
    IntervalDomainPowerEnergyEndpointContinuity u T p0 :=
  intervalDomain_powerEnergyEndpointContinuity_of_atZero_and_global_classical
    (params := params) (T := T) (p0 := p0) (u := u) (v := v)
    hglobal hT hzero

end ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

end
```

## Suggested future theorem, if you want to reduce the residual further

A future local theorem can reduce `atZero` to a more physical initial-data statement, but it needs extra assumptions. A realistic target is:

```lean
-- Sketch only: this theorem is not currently repository-local.
theorem intervalDomain_atZero_of_initialTrace_initialValue_positivePower
    {params : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hp0 : 0 < p0)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hu_initial : u 0 = u₀)
    (hu₀ : PositiveInitialDatum intervalDomain u₀) :
    ∀ p, p0 ≤ p →
      ContinuousWithinAt
        (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
        (Set.Icc (0 : ℝ) T) 0 := by
  -- Needs a new analytic proof:
  -- 1. extract pointwise control from `intervalDomainSupNorm` using bounded ranges;
  -- 2. get a uniform compact range for `u t` near zero;
  -- 3. use uniform continuity/Lipschitz control of `r ↦ r^p` on that range;
  -- 4. integrate over `[0,1]`;
  -- 5. use `hu_initial` to replace the endpoint value `u 0` by `u₀`.
  -- For nonpositive powers replace `PositiveInitialDatum` by a uniform-floor
  -- assumption such as `PaperPositiveInitialDatum`, plus the corresponding
  -- eventual lower bound for `u t` from the sup-norm trace.
  sorry
```

The important point is that the future theorem must include an endpoint-value compatibility hypothesis such as `hu_initial : u 0 = u₀` or at least equality of all required initial power energies. Without that compatibility, the theorem is false regardless of boundedness.

## Bottom line

The current `atZero` residual is honest and minimal at the present abstraction level. Existing `InitialTrace`, positivity, global classical regularity, and boundedness assumptions control positive-time behavior but do not constrain the value used by the closed-time energy map at `t = 0`.
