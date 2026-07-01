# Q2893 (shen1) — analytic deleted-right power-energy trace limit

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Target area: `ShenWork/PDE/P3MoserEnergyContinuity.lean`  
Source edit requested: none; answer file only.

## Verdict

Yes: the analytic deleted-right statement

```lean
def IntervalDomainInitialTracePowerEnergyTendsto
    (u₀ : intervalDomain.Point → ℝ)
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p →
    Tendsto
      (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
      (𝓝[Set.Ioc (0 : ℝ) T] 0)
      (𝓝 (intervalDomain.integral (fun x => (u₀ x) ^ p)))
```

should be provable from current repo APIs, **provided the datum assumption is the paper-faithful positive datum**:

```lean
PaperPositiveInitialDatum intervalDomain u₀
```

together with

```lean
InitialTrace intervalDomain u₀ u
IsPaper2GlobalClassicalSolution intervalDomain params u v
0 < T
```

No zero-slice compatibility `u 0 = u₀` is needed for this deleted-right theorem. The stored slice `u 0` is not mentioned by the filter `𝓝[Set.Ioc 0 T] 0` except as a limit point, and the function being evaluated has domain variable `t`; the proof uses only `0 < t` eventually.

However, this is not currently a one-line proof from an existing named theorem. It needs several small interval-domain helper lemmas around `intervalDomainSupNorm`, boundedness of slices, and an integral Lipschitz estimate. These are analytic/domain lemmas, not new PDE residuals.

## Recommended theorem statement

Use the paper-positive datum route as the main theorem:

```lean
import ShenWork.PDE.P3MoserEnergyContinuity
import ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
open ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
open scoped Topology Interval

namespace ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

/-- Initial trace plus a paper-positive datum gives the deleted-right power-energy
limit to the datum energy.  This theorem deliberately does not inspect or
constrain the stored slice `u 0`. -/
theorem intervalDomain_initialTracePowerEnergyTendsto_of_paperPositive
    {params : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 < T)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v) :
    IntervalDomainInitialTracePowerEnergyTendsto u₀ u T p0

end ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
```

This theorem does **not** need `0 < p0`. The reason is that `PaperPositiveInitialDatum` supplies a uniform floor `η > 0`; all relevant bases lie in a compact interval `[η/2, M] ⊆ (0,∞)` for small positive time, so `r ↦ r ^ p` is uniformly continuous there for every real `p`.

If you insist on using only `PositiveInitialDatum intervalDomain u₀`, then the theorem should assume at least `0 < p0` (or directly `∀ p, p0 ≤ p → 0 < p`) plus a closed-domain nonnegativity lemma for `u₀`. Without a positive datum floor, zeros at the endpoints are possible; real `rpow` at zero is safe for positive exponents but not for negative exponents. In the Moser context `p0` is normally positive, but the `PaperPositiveInitialDatum` route is both cleaner and closer to the paper assumptions.

## Existing helpers / APIs to reuse

### `ShenWork/Paper2/Statements.lean`

Use:

```lean
def InitialTrace
lemma InitialTrace.eventually_small

def PaperPositiveInitialDatum
lemma PaperPositiveInitialDatum.floor
lemma PaperPositiveInitialDatum.admissible

lemma IsPaper2GlobalClassicalSolution.classical
lemma IsPaper2ClassicalSolution.u_pos'
```

`InitialTrace.eventually_small` gives the eventual small `intervalDomain.supNorm` distance for `0 < t`. `PaperPositiveInitialDatum.floor` gives `∃ η > 0, ∀ x, η ≤ u₀ x`. `PaperPositiveInitialDatum.admissible` unfolds through the concrete interval-domain `initialAdmissible` to boundedness of `|u₀|` and continuity of `u₀`.

### `ShenWork/PDE/IntervalDomain.lean`

Use the concrete definitions:

```lean
def intervalDomainPoint : Type := Subtype (Set.Icc (0 : ℝ) 1)
def intervalDomainLift (f : intervalDomainPoint → ℝ) : ℝ → ℝ :=
  fun x => if hx : x ∈ Set.Icc (0 : ℝ) 1 then f ⟨x, hx⟩ else 0

def intervalDomainIntegral (f : intervalDomainPoint → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, intervalDomainLift f x

def intervalDomainSupNorm (f : intervalDomainPoint → ℝ) : ℝ :=
  sSup (Set.range (fun x : intervalDomainPoint => |f x|))

def intervalDomain : BoundedDomainData where
  Point := intervalDomainPoint
  supNorm := intervalDomainSupNorm
  integral := intervalDomainIntegral
  initialAdmissible := fun u₀ =>
    BddAbove (Set.range fun x => |u₀ x|) ∧ Continuous u₀
  ...
```

The closed-spatial part of `intervalDomainClassicalRegularity` gives, for positive times, `ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc 0 1)`, which is enough to get boundedness/continuity of positive-time slices on the compact interval.

### `ShenWork/Paper2/IntervalDomainLpBootstrapEnergyInequality.lean`

Use:

```lean
theorem intervalDomain_u_rpow_intervalIntegrable_of_regularity
    {params : CM2Params} {T t q : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) :
    IntervalIntegrable
      (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ q))
      MeasureTheory.volume 0 1
```

This supplies positive-time integrability of `(u t)^p` once a finite positive horizon is chosen, e.g. `t + 1`.

### `ShenWork/PDE/P3MoserEnergyContinuity.lean`

Use as patterns:

```lean
theorem intervalDomain_power_jointContinuousOn
theorem intervalDomain_power_bounded_on_slab
theorem intervalDomain_energyContinuousOn_Ioo
```

The deleted-right proof is not the same as `intervalDomain_energyContinuousOn_Ioo`; it is a trace-to-initial-datum theorem at the left endpoint. But the existing `rpow` positivity pattern in `intervalDomain_power_jointContinuousOn` is exactly the right model: apply `ContinuousOn.rpow` / `ContinuousOn.rpow_const` only after proving the bases are nonzero or the exponent is positive.

### `ShenWork/PDE/P3MoserAgmonDirectRoute.lean`

There is a private local pattern:

```lean
private lemma intervalDomainSupNorm_nonneg_local
```

It unfolds `intervalDomainSupNorm` and uses `le_csSup_of_le` / `sSup` reasoning. Do not depend on it because it is private, but copy the same style for public helper lemmas.

## Small helper lemmas to add first

### Helper 1: pointwise bound by concrete `intervalDomain.supNorm`

This should compile essentially as written.

```lean
import ShenWork.PDE.P3MoserEnergyContinuity

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2
open scoped Topology Interval

namespace ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

/-- For a bounded slice, the concrete interval-domain sup norm dominates every
pointwise absolute value. -/
theorem intervalDomain_abs_le_supNorm_of_bddAbove
    {f : intervalDomain.Point → ℝ}
    (hbdd : BddAbove (Set.range (fun x : intervalDomain.Point => |f x|))) :
    ∀ x : intervalDomain.Point, |f x| ≤ intervalDomain.supNorm f := by
  intro x
  change |f x| ≤ intervalDomainSupNorm f
  unfold intervalDomainSupNorm
  exact le_csSup hbdd ⟨x, rfl⟩

/-- If the concrete sup norm is strictly below `ε`, then every pointwise absolute
value is strictly below `ε`. -/
theorem intervalDomain_pointwise_abs_lt_of_supNorm_lt
    {f : intervalDomain.Point → ℝ} {ε : ℝ}
    (hbdd : BddAbove (Set.range (fun x : intervalDomain.Point => |f x|)))
    (hsup : intervalDomain.supNorm f < ε) :
    ∀ x : intervalDomain.Point, |f x| < ε := by
  intro x
  exact lt_of_le_of_lt
    (intervalDomain_abs_le_supNorm_of_bddAbove hbdd x) hsup

end ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
```

### Helper 2: boundedness of a difference slice

Add this near the previous helper. This is pure order algebra; the proof route is triangle inequality plus two `BddAbove` witnesses.

```lean
/-- If two slices are bounded in absolute value, so is their difference. -/
theorem bddAbove_abs_sub_of_bddAbove_abs
    {X : Type*} {f g : X → ℝ}
    (hf : BddAbove (Set.range (fun x : X => |f x|)))
    (hg : BddAbove (Set.range (fun x : X => |g x|))) :
    BddAbove (Set.range (fun x : X => |f x - g x|)) := by
  rcases hf with ⟨Mf, hMf⟩
  rcases hg with ⟨Mg, hMg⟩
  refine ⟨Mf + Mg, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hf_le : |f x| ≤ Mf := hMf ⟨x, rfl⟩
  have hg_le : |g x| ≤ Mg := hMg ⟨x, rfl⟩
  calc
    |f x - g x| ≤ |f x| + |g x| := abs_sub_le_iff.mp ?_  -- see note below
    _ ≤ Mf + Mg := add_le_add hf_le hg_le
```

The only name risk in this skeleton is the triangle inequality lemma. In Mathlib this is usually one of:

```lean
abs_sub_le_iff
abs_sub_le_iff.mp / .mpr
abs_sub_le_iff.2
abs_sub_le_iff.1
```

or a direct triangle lemma for subtraction. If the exact name fights you, replace the first `calc` step by the standard triangle inequality after rewriting `f x - g x = f x + (-g x)`.

A more robust proof using `abs_sub_le_iff` is:

```lean
  have hf_abs := abs_le.mp hf_le
  have hg_abs := abs_le.mp hg_le
  exact (abs_sub_le_iff).2 ⟨by linarith, by linarith⟩
```

if the local imported orientation is `|a - b| ≤ c ↔ a - c ≤ b ∧ b ≤ a + c`.

### Helper 3: boundedness of positive-time slices from global classical regularity

Recommended statement:

```lean
/-- A closed-spatial continuous interval-domain slice has bounded absolute range. -/
theorem intervalDomain_bddAbove_abs_of_continuousOn_Icc
    {f : intervalDomain.Point → ℝ}
    (hf : ContinuousOn (intervalDomainLift f) (Set.Icc (0 : ℝ) 1)) :
    BddAbove (Set.range (fun x : intervalDomain.Point => |f x|))
```

Proof route:

1. `continuous_abs.comp_continuousOn hf` gives continuity of `fun y => |intervalDomainLift f y|` on `Icc 0 1`.
2. Use `isCompact_Icc.exists_isMaxOn` or `IsCompact.exists_isMaxOn` to get a maximum on `Icc 0 1`.
3. For each `x : intervalDomain.Point`, rewrite `intervalDomainLift f x.1 = f x` using `x.2`.
4. Package `BddAbove` with the maximum value.

Then add:

```lean
/-- Positive-time global classical regularity gives absolute boundedness of the
slice `u t`. -/
theorem intervalDomain_bddAbove_abs_u_slice_of_global_classical
    {params : CM2Params} {t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (ht0 : 0 < t) :
    BddAbove (Set.range (fun x : intervalDomain.Point => |u t x|))
```

Proof route:

```lean
have hT : 0 < t + 1 := by linarith
have hsol := hglobal.classical hT
have ht : t ∈ Set.Ioo (0 : ℝ) (t + 1) := ⟨ht0, by linarith⟩
have hC2 : ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
  (hsol.regularity.2.2.2.2.1 t ht).1.1
exact intervalDomain_bddAbove_abs_of_continuousOn_Icc hC2.continuousOn
```

The accessor path is the one already used in `intervalDomain_u_rpow_intervalIntegrable_of_regularity`.

### Helper 4: datum boundedness and continuity

For `PaperPositiveInitialDatum`, boundedness is immediate from admissibility after unfolding the interval-domain field:

```lean
/-- Paper-positive interval-domain data are bounded in absolute value. -/
theorem intervalDomain_bddAbove_abs_of_paperPositiveInitialDatum
    {u₀ : intervalDomain.Point → ℝ}
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀) :
    BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)) := by
  have hAdm := PaperPositiveInitialDatum.admissible hdatum
  -- `intervalDomain.initialAdmissible` unfolds to
  -- `BddAbove (Set.range fun x => |u₀ x|) ∧ Continuous u₀`.
  simpa [intervalDomain] using hAdm.1
```

If `simpa [intervalDomain]` unfolds too much or too little, use:

```lean
  change BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)) ∧
      Continuous u₀ at hAdm
  exact hAdm.1
```

### Helper 5: uniform continuity of real powers on a positive compact interval

This is the key real-`p` lemma. With a positive left endpoint it works for every real exponent.

```lean
/-- On a compact interval bounded away from zero, `r ↦ r ^ p` is uniformly
continuous for every real exponent `p`. -/
theorem real_rpow_uniformContinuousOn_Icc_of_pos_left
    {p a b : ℝ} (ha : 0 < a) :
    UniformContinuousOn (fun r : ℝ => r ^ p) (Set.Icc a b) := by
  have hcont : ContinuousOn (fun r : ℝ => r ^ p) (Set.Icc a b) := by
    exact continuousOn_id.rpow_const
      (fun r hr => Or.inl (ne_of_gt (lt_of_lt_of_le ha hr.1)))
  exact hcont.uniformContinuousOn_compact isCompact_Icc
```

Name risks: depending on imports, the last line may be spelled as one of:

```lean
hcont.uniformContinuousOn_compact isCompact_Icc
isCompact_Icc.uniformContinuousOn_of_continuousOn hcont
```

The same pattern appears in existing code via `ContinuousOn.rpow` / `ContinuousOn.rpow_const` with a nonzero side condition.

### Helper 6: integral difference bound on the unit interval

Recommended statement:

```lean
/-- On the concrete unit interval, a uniform pointwise bound controls the
absolute difference of integrals. -/
theorem intervalDomain_integral_sub_abs_le_of_pointwise_abs_le
    {f g : intervalDomain.Point → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε)
    (hf_int : IntervalIntegrable (intervalDomainLift f) volume 0 1)
    (hg_int : IntervalIntegrable (intervalDomainLift g) volume 0 1)
    (hpoint : ∀ x : intervalDomain.Point, |f x - g x| ≤ ε) :
    |intervalDomain.integral f - intervalDomain.integral g| ≤ ε
```

Proof route:

1. Rewrite `intervalDomain.integral` to `intervalDomainIntegral` and unfold.
2. Use `intervalIntegral.integral_sub hf_int hg_int`.
3. Prove `-ε ≤ ∫ (f-g)` and `∫ (f-g) ≤ ε` by `intervalIntegral.integral_mono_on zero_le_one` against the constant functions `-ε` and `ε`.
4. Use `intervalIntegral.integral_const`; on `[0,1]`, the constant integral is the constant itself.
5. Finish with `abs_le.mpr`.

This helper avoids needing a special `abs_integral_le_integral_abs` interval-integral lemma name.

## Main proof decomposition

Fix `p` with `p0 ≤ p`.

### Step 1: datum floor and datum bound

From the paper-positive datum:

```lean
obtain ⟨η, hη, hfloor⟩ := PaperPositiveInitialDatum.floor hdatum
have hdatum_bdd := intervalDomain_bddAbove_abs_of_paperPositiveInitialDatum hdatum
```

Choose an explicit upper bound `M₀` from `hdatum_bdd`, then replace it by a convenient nonnegative bound such as `M := max 1 M₀`. You need a lemma or local proof that

```lean
∀ x, |u₀ x| ≤ M
```

and therefore

```lean
∀ x, u₀ x ≤ M
```

while also retaining

```lean
∀ x, η ≤ u₀ x
```

### Step 2: trace gives pointwise convergence for small positive times

Given a small radius `δtrace`, `InitialTrace.eventually_small` gives

```lean
intervalDomain.supNorm (fun x => u t x - u₀ x) < δtrace
```

for `0 < t < δ`.

For each such `t`, get boundedness of the difference slice:

```lean
have hut_bdd : BddAbove (Set.range (fun x : intervalDomain.Point => |u t x|)) :=
  intervalDomain_bddAbove_abs_u_slice_of_global_classical hglobal ht0

have hdiff_bdd : BddAbove
    (Set.range (fun x : intervalDomain.Point => |u t x - u₀ x|)) :=
  bddAbove_abs_sub_of_bddAbove_abs hut_bdd hdatum_bdd
```

Then apply:

```lean
have hpoint_close : ∀ x, |u t x - u₀ x| < δtrace :=
  intervalDomain_pointwise_abs_lt_of_supNorm_lt hdiff_bdd hsup
```

### Step 3: small trace distance traps `u t x` in a positive compact interval

Choose `δtrace ≤ η / 2` and `δtrace ≤ 1`. Then for all `x`:

```lean
η / 2 ≤ u t x
u t x ≤ M + 1
η ≤ u₀ x
u₀ x ≤ M
```

So both `u t x` and `u₀ x` lie in the compact positive interval

```lean
Set.Icc (η / 2) (M + 1)
```

This is where `PaperPositiveInitialDatum` is strongest: the compact interval is bounded away from zero, so no sign/exponent case split is needed for real `p`.

### Step 4: uniform continuity of `rpow` converts trace closeness to power closeness

Use:

```lean
have huc : UniformContinuousOn (fun r : ℝ => r ^ p)
    (Set.Icc (η / 2) (M + 1)) :=
  real_rpow_uniformContinuousOn_Icc_of_pos_left (by linarith [hη] : 0 < η / 2)
```

Given target `ε > 0`, extract a uniform-continuity radius `δpow > 0`. Then pointwise trace closeness below `δpow` gives

```lean
∀ x, |(u t x) ^ p - (u₀ x) ^ p| < ε
```

or a non-strict `≤ ε` version after shrinking to `ε / 2`.

### Step 5: integrate the pointwise power difference

For positive `t`, use a horizon `t + 1`:

```lean
have hsolt : IsPaper2ClassicalSolution intervalDomain params (t + 1) u v :=
  hglobal.classical (by linarith : 0 < t + 1)

have hut_int : IntervalIntegrable
    (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ p)) volume 0 1 :=
  intervalDomain_u_rpow_intervalIntegrable_of_regularity
    (q := p) hsolt ht0 (by linarith)
```

For `u₀`, use its continuity plus the same positive compact interval to show

```lean
have hu0_int : IntervalIntegrable
    (intervalDomainLift (fun x : intervalDomain.Point => (u₀ x) ^ p)) volume 0 1 := ...
```

Proof route for `hu0_int`:

* from `PaperPositiveInitialDatum.admissible hdatum`, get `Continuous u₀`;
* show `ContinuousOn (fun y => intervalDomainLift u₀ y) (Icc 0 1)` by rewriting the lift on the interval;
* apply `ContinuousOn.rpow_const` using the floor `η ≤ u₀ x`;
* convert back to the lifted power function; then use `.intervalIntegrable`.

Then apply `intervalDomain_integral_sub_abs_le_of_pointwise_abs_le` to get

```lean
|intervalDomain.integral (fun x => (u t x) ^ p) -
  intervalDomain.integral (fun x => (u₀ x) ^ p)| ≤ ε
```

for all sufficiently small `t ∈ Set.Ioc 0 T`.

### Step 6: package as `Tendsto` on `𝓝[Set.Ioc 0 T] 0`

Use the metric characterization of tendsto to neighborhoods of a real number. The proof only needs eventual control for `t` in `Set.Ioc 0 T`; the set membership already supplies `0 < t` and `t ≤ T`. To get strict `t < T` when needed, shrink the neighborhood radius below `T`; alternatively use the global horizon `t + 1`, which avoids needing `t < T`.

Skeleton shape:

```lean
  intro p hp
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- choose ε/2 for integral estimate and get a trace radius from rpow UC
  -- obtain δ > 0 from `InitialTrace.eventually_small`
  refine eventually_nhdsWithin_iff.mpr ?_
  refine ⟨Set.Ioo (-δ) δ, ?open, ?mem, ?eventual⟩
  intro t ht_near htIoc
  have ht0 : 0 < t := htIoc.1
  -- use trace, pointwise supNorm helper, rpow UC, integral difference bound
```

The exact filter lemma can vary. A robust alternative is to prove the ε/δ form manually with `Metric.mem_nhdsWithin_iff` / `eventually_nhdsWithin_iff`; do not try to turn this into ordinary `ContinuousAt`, because the theorem is deleted-right and intentionally ignores `u 0`.

## PositiveInitialDatum-only route

A weaker theorem may be possible:

```lean
theorem intervalDomain_initialTracePowerEnergyTendsto_of_positiveInitialDatum
    {params : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 < T)
    (hp0 : 0 < p0)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PositiveInitialDatum intervalDomain u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v) :
    IntervalDomainInitialTracePowerEnergyTendsto u₀ u T p0
```

But this route needs additional work:

1. From `PositiveInitialDatum` plus `intervalDomain.initialAdmissible`, prove `0 ≤ u₀ x` on the **closed** interval. This is not the same as the existing `PositiveInitialDatum.pos`, which only gives positivity on `inside`. It should follow from continuity and density of the interior near the endpoints, but it is a separate endpoint lemma.
2. Since `u₀` may vanish at the boundary, use `0 < p` to prove continuity of `r ↦ r ^ p` at zero. This is why the theorem needs `0 < p0`, so `p0 ≤ p` implies `0 < p`.
3. The uniform-continuity compact interval becomes `[0, M + 1]`, not `[η/2, M + 1]`, and the `ContinuousOn.rpow` side condition must use the exponent-positive branch at zeros.

For Moser, `p0` is usually already positive, so this is mathematically plausible. But Lean-wise the paper-positive route is much cleaner and avoids all endpoint-zero `rpow` cases.

## Final recommendation

Add the paper-positive theorem first:

```lean
intervalDomain_initialTracePowerEnergyTendsto_of_paperPositive
```

with no `0 < p0` hypothesis. Treat it as an analytic helper theorem, not a residual. Then combine it with the energy-compatibility residual from Q2892 to produce the full endpoint continuity:

```text
InitialTrace + PaperPositiveInitialDatum + global classical
  ⇒ IntervalDomainInitialTracePowerEnergyTendsto
IntervalDomainInitialPowerEnergyCompatibleAtZero
  ⇒ IntervalDomainInitialPowerEnergyContinuityAtZero
```

This is the clean separation: the trace theorem proves the deleted-right limit, and the compatibility theorem handles the stored `u 0` value.
