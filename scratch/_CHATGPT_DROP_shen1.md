# Q2715 (shen1) — C2 `UnitIntervalPositiveAgmonInterpolation` audit

Repo: `xiangyazi24/Shen_work`  
Branch for this drop: `chatgpt-scratch`  
Lean target: Lean 4 / Mathlib 4.29.1  
Scope: non-Zinan files only. I did **not** inspect, edit, rely on, or propose edits to
`ShenWork/PDE/P3MoserHighExcursionProducer.lean` or
`ShenWork/PDE/P3MoserThresholdPlanProducer.lean`.

I inspected the requested files:

- `ShenWork/PDE/SobolevEmbedding.lean`
- `ShenWork/PDE/GagliardoNirenberg.lean`
- `ShenWork/Paper2/IntervalDomainLemma41.lean`
- `ShenWork/PDE/IntervalDomain.lean`
- `ShenWork/PDE/IntervalAgmonInterpolation.lean`

I also checked adjacent consumers/producers only to identify exact target names:
`ShenWork/Paper2/IntervalDomainTheorem11.lean`,
`ShenWork/Paper2/IntervalDomainMCL.lean`,
`ShenWork/Paper2/IntervalDomainGNYObstruction.lean`, and
`ShenWork/PDE/IntervalDomainAPrioriGlobal.lean`.

## Verdict

The current repo has the right **algebraic and classical Agmon ingredients**, but I do **not** see an existing direct composition that proves the current C2

```lean
def UnitIntervalPositiveAgmonInterpolation : Prop :=
  ∀ q : ℝ, 1 < q →
  ∀ eps : ℝ, 0 < eps →
    ∃ Ceps > 0,
      ∀ f : intervalDomain.Point → ℝ,
        (∀ x, 0 < f x) →
        ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1) →
          intervalDomain.integral (fun x => f x ^ q) ≤
            eps * intervalDomain.integral
              (fun x => f x ^ (q - 2) *
                (intervalDomain.gradNorm f x) ^ 2) +
            Ceps * (intervalDomain.integral f) ^ q
```

as-is.

The genuinely blocking gap is not the final `eps` absorption: `IntervalDomainLemma41.interpolation_absorption` is already in the repo and has the right shape. The blocking gap is the **Agmon/core chain-rule bridge compatible with `intervalDomainLift`**.

Concretely, the available theorem

```lean
ShenWork.GagliardoNirenberg.agmon_inequality_interval
```

requires an ordinary derivative hypothesis

```lean
∀ x ∈ Set.Icc 0 L, HasDerivAt f (f' x) x
```

on the **closed** interval. But `intervalDomainLift f` is the zero extension of a positive function on `[0,1]`; it usually jumps to `0` outside the interval. The current assumption

```lean
ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1)
```

is a closed-set/within-set smoothness assumption. It does **not** give ordinary `HasDerivAt` of the zero extension at `0` and `1` for a positive slice. This is exactly the endpoint mismatch that prevents simply applying `agmon_inequality_interval` to

```lean
fun y => (intervalDomainLift f y) ^ (q / 2)
```

and finishing by algebra.

So the smallest useful addition is a reusable **interior/within/a.e. Agmon lemma** that avoids ordinary endpoint differentiability of the zero extension. After that, the rest is mostly conversions and `rpow` bookkeeping.

## Existing theorem inventory that can be composed

### 1. Existing wiring target in `IntervalAgmonInterpolation.lean`

The file already has the correct paper-level wiring theorem:

```lean
namespace ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

/-- Produce the classical-solution positive interpolation frontier from a
uniform unit-interval Agmon/Gagliardo-Nirenberg frontier. -/
theorem intervalDomain_classicalSolutionPositiveInterpolation_of_uniform_agmon
    {params : CM2Params}
    (hagmon : UnitIntervalPositiveAgmonInterpolation) :
    IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionPositiveInterpolation
      params := by
  intro T u v hsol eps heps q hq
  rcases hagmon q hq eps heps with ⟨Ceps, hCeps_pos, hCeps⟩
  refine ⟨Ceps, hCeps_pos, ?_⟩
  intro t ht0 htT
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hf_pos : ∀ x : intervalDomain.Point, 0 < u t x :=
    fun x => hsol.u_pos' ht0 htT
  have hC2_closed :
      ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).1.1
  exact hCeps (u t) hf_pos hC2_closed
```

This is good. Do not weaken or wrap it. The right downstream frontier is already:

```lean
abbrev IntervalDomainClassicalSolutionPositiveInterpolation
    (p : CM2Params) : Prop :=
  ∀ {T : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
    IsPaper2ClassicalSolution intervalDomain p T u v →
      ∀ eps, 0 < eps → ∀ q, 1 < q → ∃ Ceps > 0,
        LpMassGradientInterpolationEstimate intervalDomain q eps Ceps T u
```

from `ShenWork/Paper2/IntervalDomainTheorem11.lean`.

### 2. Existing single-slice sanity lemma in `IntervalAgmonInterpolation.lean`

This is proved, but not enough because the constant depends on the slice:

```lean
theorem intervalDomain_agmon_interpolation_slice
    {f : intervalDomain.Point → ℝ} {q eps : ℝ}
    (hmass : 0 < intervalDomain.integral f) :
    ∃ Ceps > 0,
      intervalDomain.integral (fun x => f x ^ q) ≤
        eps * intervalDomain.integral
          (fun x => f x ^ (q - 2) * (intervalDomain.gradNorm f x) ^ 2) +
        Ceps * (intervalDomain.integral f) ^ q
```

This should not be used for `UnitIntervalPositiveAgmonInterpolation`, because the desired `Ceps` must be chosen before `f`.

### 3. Existing Sobolev/Agmon facts

From `ShenWork/PDE/SobolevEmbedding.lean`:

```lean
namespace ShenWork.Sobolev

theorem lpNorm_one_le_rpow_measure_mul_lpNorm_two
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ)
    (hf_mem : MemLp f (2 : ℝ≥0∞) μ) :
    lpNorm f (1 : ℝ≥0∞) μ ≤
      ((μ Set.univ).toReal ^ (1 / 2 : ℝ)) *
        lpNorm f (2 : ℝ≥0∞) μ

theorem interval_integral_abs_le_length_rpow_mul_lpNorm_two
    {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioc (0 : ℝ) L)))
    (hf_mem : MemLp f (2 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) L))) :
    (∫ y in (0 : ℝ)..L, |f y|) ≤
      (L ^ (1 / 2 : ℝ)) *
        lpNorm f (2 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) L))

theorem sobolev_pointwise_bound
    {L : ℝ} (hL : 0 < L)
    {f f' : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Icc 0 L))
    (hf_deriv : ∀ x ∈ Icc 0 L, HasDerivAt f (f' x) x)
    (hf'_int : IntervalIntegrable f' volume 0 L)
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    |f x| ≤ (1 / L) * (∫ y in (0 : ℝ)..L, |f y|) +
      (∫ y in (0 : ℝ)..L, |f' y|)

theorem sobolev_H1_Linfty_interval
    {L : ℝ} (hL : 0 < L)
    {f f' : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Icc 0 L))
    (hf_deriv : ∀ x ∈ Icc 0 L, HasDerivAt f (f' x) x)
    (hf_mem : MemLp f (2 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) L)))
    (hf'_mem : MemLp f' (2 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) L)))
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    |f x| ≤
      (1 / L) *
          ((L ^ (1 / 2 : ℝ)) *
            lpNorm f (2 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) L))) +
        (L ^ (1 / 2 : ℝ)) *
          lpNorm f' (2 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) L))
```

From `ShenWork/PDE/GagliardoNirenberg.lean`:

```lean
namespace ShenWork.GagliardoNirenberg

theorem agmon_inequality_interval
    {L : ℝ} (hL : 0 < L)
    {f f' : ℝ → ℝ}
    (_hf_cont : ContinuousOn f (Icc 0 L))
    (hf_deriv : ∀ x ∈ Icc 0 L, HasDerivAt f (f' x) x)
    (_hf'_int : IntervalIntegrable f' volume 0 L)
    (hf_sq_int : IntervalIntegrable (fun y => f y ^ 2) volume 0 L)
    (hf'_sq_int : IntervalIntegrable (fun y => f' y ^ 2) volume 0 L)
    (hff'_int : IntervalIntegrable (fun y => f y * f' y) volume 0 L)
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    f x ^ 2 ≤ (2 / L) * (∫ y in (0 : ℝ)..L, f y ^ 2) +
      2 * sqrt (∫ y in (0 : ℝ)..L, f y ^ 2) *
        sqrt (∫ y in (0 : ℝ)..L, f' y ^ 2)
```

This is mathematically the right engine. The endpoint derivative assumption is the mismatch.

### 4. Existing algebraic absorption in `IntervalDomainLemma41.lean`

This is directly useful and should be reused:

```lean
namespace ShenWork.Paper2.IntervalDomainLemma41

theorem quadratic_absorption {a b c : ℝ}
    (ha : 0 ≤ a) (_hb : 0 ≤ b) (_hc : 0 ≤ c)
    (h : a ≤ b * Real.sqrt a + c) :
    a ≤ b ^ 2 + 2 * c

theorem interpolation_absorption {Y G Mp δ pv C : ℝ}
    (hY : 0 ≤ Y) (hG : 0 ≤ G) (hMp : 0 ≤ Mp)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1 / 4) (hp : 0 < pv)
    (hC : 0 ≤ C)
    (hineq : Y ≤ 2 * δ * Y + δ * pv * Real.sqrt (Y * G) + C * Mp) :
    Y ≤ δ ^ 2 * pv ^ 2 / (1 - 2 * δ) ^ 2 * G +
      2 * C / (1 - 2 * δ) * Mp
```

The roadmap comments in the same file already describe the intended proof:
Agmon on `f^(p/2)`, chain rule, then Young and absorption. That roadmap is accurate, but the final analytic theorem is not exported/proved.

The similarly shaped frontier

```lean
def IntervalDomainInterpolation : Prop :=
  ∀ (eps : ℝ), 0 < eps → ∀ (pExp : ℝ), 1 < pExp → ∃ Ceps > 0,
    ∀ (f : intervalDomainPoint → ℝ),
      (∀ x, x ∈ intervalDomain.inside → 0 < f x) →
        intervalDomain.integral (fun x => (f x) ^ pExp) ≤
          eps * intervalDomain.integral
              (fun x => (f x) ^ (pExp - 2) *
                (intervalDomain.gradNorm f x) ^ 2) +
            Ceps * (intervalDomain.integral f) ^ pExp
```

is only a frontier. It is not a theorem to compose. It also has a different positivity hypothesis and no C2 hypothesis.

### 5. Interval-domain concrete definitions

The critical definitional conversions are in `ShenWork/PDE/IntervalDomain.lean`:

```lean
def intervalDomainPoint : Type := Subtype (Set.Icc (0 : ℝ) 1)

def intervalDomainLift (f : intervalDomainPoint → ℝ) : ℝ → ℝ :=
  fun x => if hx : x ∈ Set.Icc (0 : ℝ) 1 then f ⟨x, hx⟩ else 0

def intervalDomainIntegral (f : intervalDomainPoint → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, intervalDomainLift f x

def intervalDomainGradNorm (f : intervalDomainPoint → ℝ)
    (x : intervalDomainPoint) : ℝ :=
  |deriv (intervalDomainLift f) x.1|

def intervalDomain : ShenWork.Paper2.BoundedDomainData where
  Point := intervalDomainPoint
  inside := {x : intervalDomainPoint | (x.1 : ℝ) ∈ Set.Ioo 0 1}
  boundary := {x : intervalDomainPoint | x.1 = 0 ∨ x.1 = 1}
  volume := 1
  supNorm := intervalDomainSupNorm
  infValue := fun f => sInf (Set.range f)
  integral := intervalDomainIntegral
  gradNorm := intervalDomainGradNorm
  -- ...
  classicalRegularity := intervalDomainClassicalRegularity
```

This means every target integral eventually reduces to an `intervalIntegral` of an `intervalDomainLift`.

## Thin proof-producing route

The proof should not add another residual wrapper. The thin route is:

1. Add one Agmon lemma whose derivative hypotheses match closed-set/within regularity or open-interval differentiability.
2. Add an interval-domain power-chain converter for `g = (intervalDomainLift f)^(q/2)`.
3. Reuse `IntervalDomainLemma41.interpolation_absorption`.
4. Finish `UnitIntervalPositiveAgmonInterpolation` in `IntervalAgmonInterpolation.lean`.

### A. Smallest genuinely analytic missing lemma

The most reusable missing theorem is an endpoint-safe variant of `agmon_inequality_interval`. I would put it next to the existing Agmon theorem in `ShenWork/PDE/GagliardoNirenberg.lean`.

A good version is either an `Ioo` pointwise theorem or an a.e. theorem. The a.e. version is enough for the final integral inequality and avoids pointwise endpoint derivative junk.

Candidate statement:

```lean
import ShenWork.PDE.GagliardoNirenberg

open MeasureTheory Set intervalIntegral
open scoped ENNReal Interval

namespace ShenWork.GagliardoNirenberg

/-- Endpoint-safe one-dimensional Agmon inequality.

This is the same estimate as `agmon_inequality_interval`, but the derivative
hypothesis is interior-only. This matches zero-extensions such as
`intervalDomainLift f`, whose ordinary endpoint derivative need not exist even
when the function is smooth up to the boundary from inside. -/
theorem agmon_inequality_interval_Ioo
    {L : ℝ} (hL : 0 < L)
    {g g' : ℝ → ℝ}
    (hg_cont : ContinuousOn g (Set.Icc 0 L))
    (hg_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) L, HasDerivAt g (g' x) x)
    (hg'_int : IntervalIntegrable g' volume 0 L)
    (hg_sq_int : IntervalIntegrable (fun y => g y ^ 2) volume 0 L)
    (hg'_sq_int : IntervalIntegrable (fun y => g' y ^ 2) volume 0 L)
    (hgg'_int : IntervalIntegrable (fun y => g y * g' y) volume 0 L)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) L) :
    g x ^ 2 ≤ (2 / L) * (∫ y in (0 : ℝ)..L, g y ^ 2) +
      2 * Real.sqrt (∫ y in (0 : ℝ)..L, g y ^ 2) *
        Real.sqrt (∫ y in (0 : ℝ)..L, g' y ^ 2) := by
  -- Prove by adapting the existing `agmon_inequality_interval` proof.
  -- The FTC step should use an interval FTC theorem with interior derivative
  -- hypotheses, or an approximation/absolute-continuity version.
  -- No endpoint ordinary `HasDerivAt` should be required.
  -- This is the real missing analytic lemma.
  --
  -- Do not prove this by assuming endpoint differentiability of a zero-extension.
  -- That would not compose with `intervalDomainLift` for positive data.
  exact by
    -- implementation goes here
    -- deliberately left as a proposed theorem statement, not committed Lean code
    fail_if_success exact agmon_inequality_interval hL hg_cont ?_ hg'_int hg_sq_int hg'_sq_int hgg'_int hx.1.le
    -- The old theorem is shown above only to document the non-composable route.
    contradiction

end ShenWork.GagliardoNirenberg
```

The body above is not intended to be pasted verbatim; the important part is the theorem statement. The current `agmon_inequality_interval` proof can be copied and changed at the FTC points. If Mathlib has an interval FTC theorem requiring only differentiability on `Ioo`, use that. Otherwise prove this once as a small absolute-continuity/FTC lemma.

If a fully a.e. variant is more convenient for final integration, use this shape instead:

```lean
theorem agmon_inequality_interval_Ioo_ae
    {L : ℝ} (hL : 0 < L)
    {g g' : ℝ → ℝ}
    (hg_cont : ContinuousOn g (Set.Icc 0 L))
    (hg_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) L, HasDerivAt g (g' x) x)
    (hg'_int : IntervalIntegrable g' volume 0 L)
    (hg_sq_int : IntervalIntegrable (fun y => g y ^ 2) volume 0 L)
    (hg'_sq_int : IntervalIntegrable (fun y => g' y ^ 2) volume 0 L)
    (hgg'_int : IntervalIntegrable (fun y => g y * g' y) volume 0 L) :
    ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) L)),
      g x ^ 2 ≤ (2 / L) * (∫ y in (0 : ℝ)..L, g y ^ 2) +
        2 * Real.sqrt (∫ y in (0 : ℝ)..L, g y ^ 2) *
          Real.sqrt (∫ y in (0 : ℝ)..L, g' y ^ 2)
```

This avoids caring about endpoint values, which are measure-zero for the final integral estimate.

### B. Interval-domain power Agmon core

Once the endpoint-safe Agmon lemma exists, the next bridge should live in
`ShenWork/PDE/IntervalAgmonInterpolation.lean` or a small non-forbidden helper imported by it.

```lean
import ShenWork.PDE.IntervalAgmonInterpolation
import ShenWork.PDE.GagliardoNirenberg
import ShenWork.Paper2.IntervalDomainLemma41

open MeasureTheory Set intervalIntegral
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainLemma41

noncomputable section

namespace ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

/-- Agmon applied to `g = f^(q/2)`, rewritten in interval-domain notation.

This is the key bridge from the concrete interval-domain API to the analytic
Agmon estimate. -/
theorem intervalDomain_positive_C2_power_agmon_core
    {q : ℝ} (hq : 1 < q)
    {f : intervalDomain.Point → ℝ}
    (hf_pos : ∀ x, 0 < f x)
    (hfC2 : ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1)) :
    let Y : ℝ := intervalDomain.integral (fun x => f x ^ q)
    let G : ℝ := intervalDomain.integral
      (fun x => f x ^ (q - 2) * (intervalDomain.gradNorm f x) ^ 2)
    ∀ᵐ y ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      (intervalDomainLift f y) ^ q ≤ 2 * Y + q * Real.sqrt (Y * G) := by
  classical
  -- Route:
  --   g  y = (intervalDomainLift f y) ^ (q / 2)
  --   g' y = (q / 2) * (intervalDomainLift f y) ^ (q / 2 - 1)
  --            * deriv (intervalDomainLift f) y
  --
  -- 1. Use positivity of `f` on subtype points to prove
  --      0 < intervalDomainLift f y
  --    for y ∈ Icc 0 1.
  --
  -- 2. Derive interior `HasDerivAt` of `g` from the interior derivative of
  --    `intervalDomainLift f` and `HasDerivAt.rpow_const`.
  --
  -- 3. Apply the new endpoint-safe Agmon lemma with L = 1.
  --
  -- 4. Rewrite:
  --      ∫ g^2 = intervalDomain.integral (fun x => f x ^ q)
  --      ∫ (g')^2 = (q^2 / 4) * intervalDomain.integral
  --          (fun x => f x^(q-2) * gradNorm f x^2)
  --    using `Real.rpow_mul`, `Real.mul_rpow`, `sq_abs`, and
  --    `intervalIntegral.integral_congr`.
  --
  -- 5. Since q > 0, simplify
  --      2 * sqrt(Y) * sqrt((q^2/4)G) = q * sqrt(Y*G)
  --    with nonnegativity of Y and G.
  --
  -- This is the main proof-producing lemma; current repo lacks exactly these
  -- endpoint-safe Agmon and rpow/integral conversion steps.
  exact by
    -- proposed proof skeleton only
    contradiction

end ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation
```

Again: the body is intentionally a skeleton. The theorem statement is the useful new producer boundary. It is narrower than a new abstract wrapper and it exposes the exact proof obligations.

### C. Final Young/absorption producer

The final step should use the existing `interpolation_absorption`, not reprove quadratic absorption.

A useful producer lemma shape is:

```lean
namespace ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

/-- Final mass-gradient interpolation from the power Agmon core.

This is mostly algebra plus interval-domain monotonicity. -/
theorem intervalDomain_positive_C2_massGradientInterpolation
    {q eps : ℝ} (hq : 1 < q) (heps : 0 < eps) :
    ∃ Ceps > 0,
      ∀ f : intervalDomain.Point → ℝ,
        (∀ x, 0 < f x) →
        ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1) →
          intervalDomain.integral (fun x => f x ^ q) ≤
            eps * intervalDomain.integral
              (fun x => f x ^ (q - 2) *
                (intervalDomain.gradNorm f x) ^ 2) +
            Ceps * (intervalDomain.integral f) ^ q := by
  classical
  -- Suggested scalar choice:
  --   choose δ > 0 with δ < 1/4 and
  --     δ^2 * q^2 / (1 - 2δ)^2 ≤ eps.
  -- For example δ = min (1/8) (Real.sqrt eps / (4 * q)) is conservative.
  -- Then `1 - 2δ ≥ 3/4`, so the coefficient is safely small.
  --
  -- For each f:
  --   Y  := ∫ f^q
  --   G  := ∫ f^(q-2)|f'|^2
  --   M  := ∫ f
  --   Mp := M^q
  --
  -- Required facts:
  --   hY  : 0 ≤ Y
  --   hG  : 0 ≤ G
  --   hM  : 0 < M       -- positivity of integral from positive continuous slice
  --   hMp : 0 ≤ M^q     -- `Real.rpow_nonneg hM.le q`
  --
  -- Power Agmon core gives a pointwise/a.e. bound
  --   f^q ≤ B := 2Y + q*sqrt(YG).
  -- Then integrate f^q = f * f^(q-1) and use Young:
  --   Y ≤ 2*δ*Y + δ*q*sqrt(YG) + Cδ*M^q.
  -- Feed that into:
  --   IntervalDomainLemma41.interpolation_absorption
  -- and use the choice of δ to lower the G coefficient to eps.
  --
  -- Existing absorption theorem:
  --   interpolation_absorption hY hG hMp hδ_pos hδ_lt hq_pos hCδ hpre
  --
  -- Missing local sublemmas are listed below.
  exact by
    -- proposed proof skeleton only
    contradiction

/-- Once the producer above is present, the frontier closes with no extra wrapper. -/
theorem unitIntervalPositiveAgmonInterpolation_proved :
    UnitIntervalPositiveAgmonInterpolation := by
  intro q hq eps heps
  exact intervalDomain_positive_C2_massGradientInterpolation hq heps

end ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation
```

This is the intended final Lean route. The new theorem
`intervalDomain_positive_C2_massGradientInterpolation` is the thin producer; `unitIntervalPositiveAgmonInterpolation_proved` is just the definition-facing closure.

## Smallest missing lemmas, ranked

### Missing lemma 1: endpoint-safe Agmon / FTC bridge

This is the only genuinely analytic missing piece.

Current theorem requires:

```lean
∀ x ∈ Set.Icc 0 L, HasDerivAt g (g' x) x
```

Needed theorem should require one of:

```lean
∀ x ∈ Set.Ioo 0 L, HasDerivAt g (g' x) x
```

or a `HasDerivWithinAt`/`ContDiffOn` variant.

Recommended name:

```lean
ShenWork.GagliardoNirenberg.agmon_inequality_interval_Ioo
```

or

```lean
ShenWork.GagliardoNirenberg.agmon_inequality_interval_Ioo_ae
```

Why this is minimal: it fixes the mismatch created by `intervalDomainLift` being a zero extension. It also remains generally useful outside this exact interpolation theorem.

### Missing lemma 2: C2-to-chain-rule conversion for `f^(q/2)`

Recommended statement:

```lean
theorem intervalDomain_rpow_half_deriv_sq_integral
    {q : ℝ} (hq : 1 < q)
    {f : intervalDomain.Point → ℝ}
    (hf_pos : ∀ x, 0 < f x)
    (hfC2 : ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1)) :
    ∫ y in (0 : ℝ)..1,
        ((q / 2) * (intervalDomainLift f y) ^ (q / 2 - 1) *
          deriv (intervalDomainLift f) y) ^ 2 =
      (q ^ 2 / 4) * intervalDomain.integral
        (fun x => f x ^ (q - 2) * (intervalDomain.gradNorm f x) ^ 2)
```

This can be proved by `intervalIntegral.integral_congr` plus:

```lean
have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := by
  simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy
simp [intervalDomain, intervalDomainIntegral, intervalDomainLift,
  intervalDomainGradNorm, hyIcc, sq_abs]
```

The hard part is the rpow arithmetic:

```lean
2 * (q / 2 - 1) = q - 2
```

and rewriting

```lean
((intervalDomainLift f y) ^ (q / 2 - 1)) ^ (2 : ℕ)
```

or the corresponding real-power form into

```lean
(intervalDomainLift f y) ^ (q - 2)
```

using positivity of the base.

### Missing lemma 3: positive mass of a positive continuous interval-domain slice

Recommended statement:

```lean
theorem intervalDomain_integral_pos_of_pos_continuous
    {f : intervalDomain.Point → ℝ}
    (hf_pos : ∀ x, 0 < f x)
    (hf_cont : ContinuousOn (intervalDomainLift f) (Set.Icc (0 : ℝ) 1)) :
    0 < intervalDomain.integral f
```

This is needed for:

```lean
Real.rpow_pos_of_pos hM q
```

and for mass-term positivity in the final constant.

The proof should unfold `intervalDomainIntegral`, use that the lift is positive on `[0,1]`, and apply an interval-integral positivity theorem. The subtype point can be built with:

```lean
let x : intervalDomain.Point := ⟨y, hyIcc⟩
have : 0 < intervalDomainLift f y := by
  simpa [intervalDomainLift, hyIcc, x] using hf_pos x
```

### Missing lemma 4: pre-absorption Young step

Recommended statement:

```lean
theorem intervalDomain_pre_absorption_from_power_agmon
    {q δ : ℝ} (hq : 1 < q) (hδ : 0 < δ)
    {f : intervalDomain.Point → ℝ}
    (hf_pos : ∀ x, 0 < f x)
    (hfC2 : ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1)) :
    ∃ Cδ, 0 ≤ Cδ ∧
      let Y : ℝ := intervalDomain.integral (fun x => f x ^ q)
      let G : ℝ := intervalDomain.integral
        (fun x => f x ^ (q - 2) * (intervalDomain.gradNorm f x) ^ 2)
      let Mq : ℝ := (intervalDomain.integral f) ^ q
      Y ≤ 2 * δ * Y + δ * q * Real.sqrt (Y * G) + Cδ * Mq
```

This is mostly `Real.young_inequality_of_nonneg`, `Real.rpow_le_rpow`, and integral monotonicity. It is not as analytic as the Agmon/FTC bridge, but it is still a substantial Lean proof.

Then final absorption is existing:

```lean
have habs := ShenWork.Paper2.IntervalDomainLemma41.interpolation_absorption
  hY_nonneg hG_nonneg hMq_nonneg hδ_pos hδ_lt hq_pos hCδ_nonneg hpre
```

## Likely troublesome conversions

### 1. `intervalDomain.integral`

Use either `change` or unfold explicitly:

```lean
change intervalDomainIntegral (fun x : intervalDomainPoint => f x ^ q) = _
unfold intervalDomainIntegral
```

or

```lean
unfold intervalDomain intervalDomainIntegral
```

Expect target terms like:

```lean
∫ x in (0 : ℝ)..1, intervalDomainLift (fun x => f x ^ q) x
```

### 2. Turning interval variables into subtype points

Inside an interval integral congruence, the local hypothesis may be for `uIcc`, `uIoc`, or `Icc`. The common pattern is:

```lean
have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := by
  simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy
let x : intervalDomain.Point := ⟨y, hyIcc⟩
simp [intervalDomainLift, hyIcc, x]
```

If the hypothesis is from `integral_zero_ae` or `intervalIntegral.integral_mono_on`, it may come as `y ∈ Set.uIoc 0 1`; then use:

```lean
have hyIoc : y ∈ Set.Ioc (0 : ℝ) 1 := by
  simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy
have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hyIoc.1.le, hyIoc.2⟩
```

### 3. `gradNorm`

By definition:

```lean
intervalDomain.gradNorm f x = |deriv (intervalDomainLift f) x.1|
```

so squared gradient terms reduce by:

```lean
simp [intervalDomain, intervalDomainGradNorm, sq_abs]
```

When comparing to an integrand in the real variable `y`, first build the subtype `x := ⟨y, hyIcc⟩`.

### 4. `intervalDomainLift (fun x => f x ^ q)` versus `(intervalDomainLift f y)^q`

On `[0,1]`, these are equal; outside, they are not definitionally equal in a useful way. Use interval congruence under `hyIcc`:

```lean
have hpow_lift :
    intervalDomainLift (fun x : intervalDomain.Point => f x ^ q) y =
      (intervalDomainLift f y) ^ q := by
  let x : intervalDomain.Point := ⟨y, hyIcc⟩
  simp [intervalDomainLift, hyIcc, x]
```

### 5. Ordinary endpoint derivatives are the main trap

Do **not** try to obtain this from the current C2 hypothesis:

```lean
∀ x ∈ Set.Icc (0 : ℝ) 1,
  HasDerivAt (intervalDomainLift f) (deriv (intervalDomainLift f) x) x
```

For positive `f`, `intervalDomainLift f` is generally discontinuous from the outside at `0` and `1`, so ordinary differentiability at endpoints is false. The existing closed `ContDiffOn` classical-regularity conjunct is a within-domain regularity statement. This is the decisive reason the existing `agmon_inequality_interval` cannot be applied directly.

### 6. `ContDiffOn` and integrability of `deriv`

Even after an endpoint-safe Agmon theorem, integrability of

```lean
fun y => ((q / 2) * (intervalDomainLift f y) ^ (q / 2 - 1) *
  deriv (intervalDomainLift f) y) ^ 2
```

may be annoying because `deriv` is the ordinary derivative of the zero extension. Endpoint values are harmless measure-theoretically, but closed-interval continuity of `deriv` may not be directly available. The cleanest route is to make the endpoint-safe Agmon theorem accept the chosen `g'` as an explicit derivative representative and explicit integrability hypotheses, then prove those integrability hypotheses from interior continuity plus endpoint irrelevance.

### 7. `rpow` chain rule

For interior points, positivity gives:

```lean
have hbase_pos : 0 < intervalDomainLift f y := by
  let x : intervalDomain.Point := ⟨y, hyIcc⟩
  simpa [intervalDomainLift, hyIcc, x] using hf_pos x
```

Then the intended chain-rule shape is:

```lean
have hg_deriv_y :
    HasDerivAt
      (fun z : ℝ => (intervalDomainLift f z) ^ (q / 2))
      ((q / 2) * (intervalDomainLift f y) ^ (q / 2 - 1) *
        deriv (intervalDomainLift f) y)
      y := by
  -- from the derivative of `intervalDomainLift f` at interior y and rpow chain rule
```

The exact Mathlib name may be `HasDerivAt.rpow_const` or a nearby `Real` rpow derivative lemma. Keep the base positivity explicit; it greatly reduces side conditions.

### 8. Squared chain-rule integrand

The key algebraic rewrite is:

```lean
((q / 2) * a ^ (q / 2 - 1) * b) ^ 2
  = (q ^ 2 / 4) * a ^ (q - 2) * b ^ 2
```

under `0 < a`. In Lean, expect to prove the rpow exponent equality separately:

```lean
have hpow_exp : 2 * (q / 2 - 1) = q - 2 := by ring
```

and then use `Real.rpow_mul` or `Real.mul_rpow` with `a.nonneg`.

### 9. Nonnegativity of `Y` and `G`

`Y` is nonnegative by positivity of `f` and `Real.rpow_nonneg`.

`G` is nonnegative pointwise because:

```lean
0 ≤ f x ^ (q - 2)
0 ≤ (intervalDomain.gradNorm f x) ^ 2
```

The first follows from positive base even if `q - 2` is negative:

```lean
exact Real.rpow_nonneg (le_of_lt (hf_pos x)) (q - 2)
```

Then integrate with `intervalIntegral.integral_nonneg` after unfolding `intervalDomainIntegral`.

## Recommended implementation plan

1. In `ShenWork/PDE/GagliardoNirenberg.lean`, add one endpoint-safe Agmon theorem:
   `agmon_inequality_interval_Ioo` or `agmon_inequality_interval_Ioo_ae`.

2. In `ShenWork/PDE/IntervalAgmonInterpolation.lean`, add:
   - `intervalDomain_integral_pos_of_pos_continuous`, unless it is preferred in `IntervalDomain.lean`;
   - `intervalDomain_rpow_half_deriv_sq_integral`;
   - `intervalDomain_positive_C2_power_agmon_core`;
   - `intervalDomain_pre_absorption_from_power_agmon`;
   - `intervalDomain_positive_C2_massGradientInterpolation`;
   - `unitIntervalPositiveAgmonInterpolation_proved`.

3. Keep the existing wiring theorem unchanged:

```lean
intervalDomain_classicalSolutionPositiveInterpolation_of_uniform_agmon
```

That theorem is already exactly the desired consumer bridge.

## Bottom line

Existing repo facts get most of the way:

- `agmon_inequality_interval` supplies the mathematical Agmon inequality but has the wrong endpoint derivative interface for `intervalDomainLift`.
- `interpolation_absorption` supplies the final quadratic absorption.
- `intervalDomain` definitions are concrete enough for the necessary conversions.
- `UnitIntervalPowerGNYoungForMoser` shows that the repo already has a proved preliminary Agmon/sup package, but not the final uniform mass-gradient theorem.

The smallest missing analytic lemma is therefore an endpoint-safe Agmon/FTC lemma. After that, the remaining work is a finite set of interval-domain conversion lemmas and `rpow` chain-rule algebra, all suitable for non-Zinan files and without touching the forbidden producer files.
