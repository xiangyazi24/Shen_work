# Q2892 (shen1) — initial trace vs stored zero value for power-energy continuity

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Target file: `ShenWork/PDE/P3MoserEnergyContinuity.lean`  
Source edit requested: none; answer file only.

## Verdict

`IntervalDomainInitialPowerEnergyContinuityAtZero u T p0` is **not provable** from

```lean
InitialTrace intervalDomain u₀ u
```

plus bounded/positive initial datum assumptions alone.

It becomes provable with a **minimal extra compatibility assumption** identifying the stored `t = 0` energy with the trace datum energy, for every exponent used by the Moser ladder. Pointwise `u 0 = u₀` is sufficient but stronger than necessary. The thinnest useful compatibility residual is energy-level compatibility:

```lean
def IntervalDomainInitialPowerEnergyCompatibleAtZero
    (u₀ : intervalDomain.Point → ℝ)
    (u : ℝ → intervalDomain.Point → ℝ) (p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p →
    intervalDomain.integral (fun x => (u 0 x) ^ p) =
      intervalDomain.integral (fun x => (u₀ x) ^ p)
```

Then the intended route is:

```text
InitialTrace + paper-positive bounded datum + positive-time regularity
  ⇒ deleted-right-limit of power energy is the u₀-energy
energy compatibility at t=0
  ⇒ ContinuousWithinAt on Icc 0 T at 0
```

The existing caveat in the code comment is therefore correct: `InitialTrace` controls only positive times and does not identify the stored value `u 0` with `u₀`.

## Why no-compatibility proof is impossible

`ContinuousWithinAt f (Set.Icc 0 T) 0` is a statement about the value `f 0`, not just a deleted right limit. For

```lean
f t = intervalDomain.integral (fun x => (u t x) ^ p)
```

continuity within `[0,T]` at `0` requires the positive-time limit to equal

```lean
intervalDomain.integral (fun x => (u 0 x) ^ p)
```

But `InitialTrace intervalDomain u₀ u` only says that, for `t > 0` small,

```lean
intervalDomain.supNorm (fun x => u t x - u₀ x) < ε
```

It says nothing about `u 0`.

A concrete countermodel shape is easy: take a positive classical branch for all `t > 0` with trace datum `u₀`, but redefine the stored slice `u 0` to a different positive function. The global classical solution interface only asks for classical regularity on every strict interior time interval `(0,T)`, and `InitialTrace` only quantifies `0 < t`; neither sees the stored value at `0`. Unless the new stored slice happens to have the same `p`-energy as `u₀`, `IntervalDomainInitialPowerEnergyContinuityAtZero` fails.

For the constant-equilibrium build path, this is especially transparent: let `u t x = c` for all `t > 0`, let `u₀ x = c`, but set `u 0 x = d` with `d ≠ c`. The trace to `u₀` is exact for positive times, and positive-time classical regularity is unchanged. For any positive ladder exponent `p`, the zero-time energy is `d^p` times the interval length, while the deleted right limit is `c^p` times the interval length.

## Existing definitions/lemmas to use

Relevant existing items:

```lean
-- ShenWork/Paper2/Statements.lean
def InitialTrace
lemma InitialTrace.eventually_small

def PaperPositiveInitialDatum
lemma PaperPositiveInitialDatum.floor
lemma PaperPositiveInitialDatum.admissible

lemma IsPaper2GlobalClassicalSolution.classical
```

```lean
-- ShenWork/PDE/IntervalDomain.lean
def intervalDomainPoint
def intervalDomainLift
def intervalDomainIntegral
def intervalDomainSupNorm

def intervalDomain : BoundedDomainData := ...
-- with fields:
--   supNorm := intervalDomainSupNorm
--   integral := intervalDomainIntegral
--   initialAdmissible := fun u₀ => BddAbove (Set.range fun x => |u₀ x|) ∧ Continuous u₀
```

```lean
-- ShenWork/PDE/P3MoserEnergyContinuity.lean
theorem intervalDomain_power_jointContinuousOn
theorem intervalDomain_energyContinuousOn_Ioo
theorem intervalDomain_powerEnergyEndpointContinuity_of_atZero_and_global_classical
theorem intervalDomain_powerEnergyEndpointContinuity_of_initialPowerEnergyContinuity
```

The existing `intervalDomain_energyContinuousOn_Ioo` proves the positive-time interior continuity. It does not handle `t = 0`; the proposed route below handles exactly that left endpoint.

## Minimal residual/API

The monolithic current residual is:

```lean
def IntervalDomainInitialPowerEnergyContinuityAtZero
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p →
    ContinuousWithinAt
      (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
      (Set.Icc (0 : ℝ) T) 0
```

A thinner decomposition is:

```lean
import ShenWork.PDE.P3MoserEnergyContinuity

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2
open scoped Topology Interval

namespace ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

/-- Deleted-right trace limit of the power energy to the initial datum energy.
This intentionally does not mention the stored value `u 0`. -/
def IntervalDomainInitialTracePowerEnergyTendsto
    (u₀ : intervalDomain.Point → ℝ)
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p →
    Tendsto
      (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
      (𝓝[Set.Ioc (0 : ℝ) T] 0)
      (𝓝 (intervalDomain.integral (fun x => (u₀ x) ^ p)))

/-- Energy-level compatibility of the stored zero slice with the initial datum.
Pointwise `u 0 = u₀` implies this, but this is the exact compatibility needed
for the Moser power-energy endpoint. -/
def IntervalDomainInitialPowerEnergyCompatibleAtZero
    (u₀ : intervalDomain.Point → ℝ)
    (u : ℝ → intervalDomain.Point → ℝ) (p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p →
    intervalDomain.integral (fun x => (u 0 x) ^ p) =
      intervalDomain.integral (fun x => (u₀ x) ^ p)

/-- Deleted-right trace convergence plus zero-slice energy compatibility gives
the current endpoint-continuity residual. -/
theorem intervalDomain_initialPowerEnergyContinuityAtZero_of_traceTendsto_compat
    {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 < T)
    (hlim : IntervalDomainInitialTracePowerEnergyTendsto u₀ u T p0)
    (hcompat : IntervalDomainInitialPowerEnergyCompatibleAtZero u₀ u p0) :
    IntervalDomainInitialPowerEnergyContinuityAtZero u T p0

end ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
```

This split is strictly more informative than the monolithic residual:

* `IntervalDomainInitialTracePowerEnergyTendsto` is the analytic consequence of trace convergence and real-power continuity.
* `IntervalDomainInitialPowerEnergyCompatibleAtZero` is the exact missing stored-zero compatibility.

If you prefer an even smaller residual surface, skip the named `Tendsto` predicate and add only compatibility plus the producer theorem below.

## Producer theorem with minimal compatibility

The theorem I would add next is:

```lean
import ShenWork.PDE.P3MoserEnergyContinuity

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2
open scoped Topology Interval

namespace ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

/-- Initial trace plus a paper-positive datum gives the deleted-right power-energy
limit to the datum energy.  This theorem does not inspect or constrain `u 0`. -/
theorem intervalDomain_initialTracePowerEnergyTendsto
    {params : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 < T)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀) :
    IntervalDomainInitialTracePowerEnergyTendsto u₀ u T p0

/-- Final endpoint producer: the only compatibility required is equality of the
stored zero-slice power energies with the initial datum power energies. -/
theorem intervalDomain_initialPowerEnergyContinuityAtZero_of_initialTrace
    {params : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 < T)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hcompat : IntervalDomainInitialPowerEnergyCompatibleAtZero u₀ u p0) :
    IntervalDomainInitialPowerEnergyContinuityAtZero u T p0

end ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
```

Pointwise compatibility can be supplied by a convenience bridge:

```lean
theorem intervalDomain_initialPowerEnergyCompatibleAtZero_of_eq
    {p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (h0 : u 0 = u₀) :
    IntervalDomainInitialPowerEnergyCompatibleAtZero u₀ u p0 := by
  intro p hp
  rw [h0]
```

Energy compatibility is preferable as the main residual because it is exactly what the endpoint energy theorem consumes. Pointwise equality is cleaner for solution constructors, but unnecessarily strong for the Moser wrapper.

## Proof route for `intervalDomain_initialTracePowerEnergyTendsto`

Fix `p` with `p0 ≤ p`.

1. Use `PaperPositiveInitialDatum.floor` to get a uniform lower bound:

```lean
obtain ⟨η, hη, hfloor⟩ := PaperPositiveInitialDatum.floor hdatum
```

So `η ≤ u₀ x` for every `x`, with `0 < η`.

2. Use `PaperPositiveInitialDatum.admissible hdatum`, then unfold the concrete `intervalDomain.initialAdmissible` field if necessary, to obtain boundedness and continuity of `u₀`:

```lean
have hAdm := PaperPositiveInitialDatum.admissible hdatum
-- For intervalDomain this unfolds to:
-- BddAbove (Set.range fun x => |u₀ x|) ∧ Continuous u₀
```

Choose an upper bound `M₀` for `|u₀ x|` from the `BddAbove` field.

3. Use `InitialTrace.eventually_small` with a radius smaller than `η / 2`, and later also smaller than the uniform-continuity radius for `rpow`:

```lean
obtain ⟨δ, hδ_pos, hδ_trace⟩ :=
  InitialTrace.eventually_small htrace hε
```

For `0 < t < δ`, trace gives

```lean
intervalDomain.supNorm (fun x => u t x - u₀ x) < ε
```

Since the concrete `supNorm` is `intervalDomainSupNorm = sSup (range |...|)`, add/use a helper lemma that converts this to a pointwise estimate once the difference slice is bounded above:

```lean
theorem intervalDomain_abs_le_supNorm_of_bddAbove
    {f : intervalDomain.Point → ℝ}
    (hbdd : BddAbove (Set.range (fun x : intervalDomain.Point => |f x|))) :
    ∀ x, |f x| ≤ intervalDomain.supNorm f
```

The needed `hbdd` for `f x = u t x - u₀ x` follows from boundedness of `u₀` and positive-time spatial continuity/boundedness of `u t`, using `hglobal.classical (by linarith : 0 < t + 1)` and the closed-spatial regularity in `intervalDomainClassicalRegularity`.

4. The pointwise trace bound gives, for small positive `t`,

```lean
η / 2 ≤ u t x
```

and also an upper bound such as

```lean
|u t x| ≤ M₀ + 1
```

uniformly in `x`.

5. Real-power issue: because `p : ℝ`, do **not** use a polynomial-style estimate. Use uniform continuity of

```lean
fun r : ℝ => r ^ p
```

on a compact positive interval, for example `[η / 2, M₀ + 1]`. The positivity floor is the key. A Lean route is:

```lean
have hpow_cont : ContinuousOn (fun r : ℝ => r ^ p) (Set.Icc (η / 2) (M₀ + 1)) :=
  (continuousOn_id.rpow_const (fun r hr => Or.inl (ne_of_gt (lt_of_lt_of_le ?ηpos hr.1))))

have hpow_uc : UniformContinuousOn (fun r : ℝ => r ^ p) (Set.Icc (η / 2) (M₀ + 1)) :=
  hpow_cont.uniformContinuousOn_compact isCompact_Icc
```

The exact Mathlib names may be one of these variants depending on imports:

```lean
ContinuousOn.rpow
ContinuousOn.rpow_const
ContinuousOn.uniformContinuousOn_compact
isCompact_Icc
```

This is the same real-power positivity pattern already used in `P3MoserEnergyContinuity.lean` by `intervalDomain_power_jointContinuousOn`, which calls `ContinuousOn.rpow` with a positivity/nonzero side condition.

6. Uniform continuity converts pointwise `|u t x - u₀ x|` small into

```lean
|(u t x) ^ p - (u₀ x) ^ p| < ε
```

uniformly in `x`.

7. Integrate the pointwise difference over the unit interval. A useful helper lemma is:

```lean
theorem intervalDomain_integral_sub_abs_le_of_pointwise_abs_le
    {f g : intervalDomain.Point → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε)
    (hf_int : IntervalIntegrable (intervalDomainLift f) volume 0 1)
    (hg_int : IntervalIntegrable (intervalDomainLift g) volume 0 1)
    (hpoint : ∀ x : intervalDomain.Point, |f x - g x| ≤ ε) :
    |intervalDomain.integral f - intervalDomain.integral g| ≤ ε
```

This is just `intervalDomainIntegral`, `intervalIntegral.integral_sub`, `norm_integral_le_integral_norm`, and interval length `1`. If the exact helper does not exist yet, it is a small non-PDE lemma.

For integrability:

* `u₀` is continuous from `initialAdmissible`, and the positive floor makes `(u₀ x)^p` continuous/integrable.
* for `t > 0`, `hglobal.classical (t+1)` gives spatial regularity/continuity of `u t`, and the positive lower bound makes `(u t x)^p` continuous/integrable.

8. This proves the deleted-right convergence:

```lean
Tendsto
  (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
  (𝓝[Set.Ioc (0 : ℝ) T] 0)
  (𝓝 (intervalDomain.integral (fun x => (u₀ x) ^ p)))
```

9. Use `hcompat p hp` to replace the limit value by the stored zero energy, then prove `ContinuousWithinAt` on `Set.Icc 0 T` by splitting near `0` into the stored point `t = 0` and the deleted right interval `0 < t ≤ T`.

In metric epsilon language, after choosing a small neighborhood:

```lean
intro t htIcc htclose
by_cases ht0 : t = 0
· subst t
  -- difference is zero because the target is the actual value at 0
· have htpos : 0 < t := lt_of_le_of_ne htIcc.1 (Ne.symm ht0)
  -- use deleted-right trace convergence
```

## Real-power cautions

The `p` in this endpoint residual is a real exponent. The trace-to-energy proof should not rely on integer-power algebra.

The safe route is to require/use a uniform positive floor near `t = 0`:

```lean
PaperPositiveInitialDatum intervalDomain u₀
```

plus trace closeness small enough to keep

```lean
η / 2 ≤ u t x
```

for small `t > 0`. This makes `r ↦ r ^ p` uniformly continuous on a compact positive interval for every fixed real `p`.

Only `PositiveInitialDatum intervalDomain u₀` is weaker: it gives positivity only on `inside` and does not give a closed-domain uniform positive floor. For real `rpow`, especially for non-integer or negative exponents, that is not enough at the endpoints. The paper-faithful `PaperPositiveInitialDatum` is the right assumption.

## Recommended next step

Do not keep treating `IntervalDomainInitialPowerEnergyContinuityAtZero` as an irreducible black-box residual. Split it into:

1. a trace limit theorem, which should be provable from `InitialTrace`, `PaperPositiveInitialDatum`, and positive-time global classical regularity; and
2. an explicit stored-zero compatibility residual, preferably energy-level:

```lean
IntervalDomainInitialPowerEnergyCompatibleAtZero u₀ u p0
```

This is thinner and more honest than the current monolithic endpoint continuity residual. It also pinpoints exactly what constructors must prove about their stored `u 0` slice.
