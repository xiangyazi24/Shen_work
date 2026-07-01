# Q2894 (shen1) — Lean plan for `intervalDomain_initialTracePowerEnergyTendsto_of_paperPositive`

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Target file: `ShenWork/PDE/P3MoserEnergyContinuity.lean`  
Source edit requested: none; answer file only.

## Verdict

The theorem is mathematically true with the hypotheses as stated:

```lean
theorem intervalDomain_initialTracePowerEnergyTendsto_of_paperPositive
    {params : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 < T)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v) :
    IntervalDomainInitialTracePowerEnergyTendsto u₀ u T p0
```

No extra residual, axiom, or `u 0 = u₀` compatibility is needed, because this is a **deleted-right** tendsto at `0` along `Set.Ioc 0 T`. It only sees small `t > 0`.

The key implementation point is not PDE-heavy: it is a compact-uniform-continuity argument for `r ↦ r ^ p` on a positive interval, plus an interval-integral bound from a uniform pointwise bound. The existing repo already has the positive-time PDE regularity and the two main sup-norm/slice-boundedness helpers.

## Existing helpers checked

Use these existing declarations.

```lean
-- ShenWork/Paper2/Statements.lean
InitialTrace.eventually_small
PaperPositiveInitialDatum.floor
PaperPositiveInitialDatum.admissible
IsPaper2GlobalClassicalSolution.classical
IsPaper2ClassicalSolution.u_pos'
```

```lean
-- ShenWork/Paper2/IntervalDomainLpBootstrapEnergyInequality.lean
intervalDomain_u_rpow_intervalIntegrable_of_regularity
```

```lean
-- ShenWork/PDE/IntervalDomainAPrioriGlobal.lean
theorem intervalDomain_solution_slice_abs_bddAbove
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    BddAbove (Set.range (fun x : intervalDomain.Point => |u t x|))
```

and the related theorem:

```lean
theorem supNormControlsPointwiseBefore_of_classicalSolution
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v) :
    SupNormControlsPointwiseBefore T u
```

For the trace difference slice, the helper named in the prompt is the one to use/copy:

```lean
supNormControlsPointwiseBefore_of_bddAbove_abs
```

It is used in `IntervalDomainAPrioriGlobal.lean` to turn a family of `BddAbove (range |u t|)` hypotheses into a pointwise control package. For this theorem you need the same idea for the single family

```lean
fun t x => u t x - u₀ x
```

If the existing theorem is exactly polymorphic over any `u : ℝ → intervalDomain.Point → ℝ`, instantiate it with

```lean
w := fun t x => u t x - u₀ x
```

and supply boundedness of `w t` from boundedness of `u t` and `u₀`. If the existing theorem is only packaged for positive-time-before predicates, it may still be easier to add the one-slice helper below.

## Recommended import block

The target file already imports most of this, but for a standalone patch block use:

```lean
import ShenWork.PDE.P3MoserEnergyContinuity
import ShenWork.PDE.IntervalDomainAPrioriGlobal
import ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
open scoped Topology Interval

noncomputable section
```

If the target file already sits in

```lean
namespace ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
```

then either open `ShenWork.IntervalDomainExistence` for the APriori lemmas or fully qualify them.

## Helper lemmas to add first

### 1. A concrete pointwise sup-norm control lemma

This is the shortest useful helper. It avoids wrestling with the full `SupNormControlsPointwiseBefore` predicate inside the endpoint proof.

```lean
namespace ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

/-- For a bounded interval-domain slice, the concrete `intervalDomain.supNorm`
dominates every pointwise absolute value. -/
theorem intervalDomain_abs_le_supNorm_of_bddAbove
    {f : intervalDomain.Point → ℝ}
    (hbdd : BddAbove (Set.range (fun x : intervalDomain.Point => |f x|))) :
    ∀ x : intervalDomain.Point, |f x| ≤ intervalDomain.supNorm f := by
  intro x
  change |f x| ≤ intervalDomainSupNorm f
  unfold intervalDomainSupNorm
  exact le_csSup hbdd ⟨x, rfl⟩

/-- Strict pointwise control from strict concrete sup-norm control. -/
theorem intervalDomain_pointwise_abs_lt_of_supNorm_lt
    {f : intervalDomain.Point → ℝ} {eps : ℝ}
    (hbdd : BddAbove (Set.range (fun x : intervalDomain.Point => |f x|)))
    (hsup : intervalDomain.supNorm f < eps) :
    ∀ x : intervalDomain.Point, |f x| < eps := by
  intro x
  exact lt_of_le_of_lt
    (intervalDomain_abs_le_supNorm_of_bddAbove hbdd x) hsup

end ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
```

This should compile with the imports above. It mirrors the private `intervalDomainSupNorm_nonneg_local` style in `P3MoserAgmonDirectRoute.lean`, but gives the exact inequality needed here.

### 2. Boundedness of absolute value for the initial datum

`PaperPositiveInitialDatum.admissible` unfolds through `intervalDomain.initialAdmissible`, whose concrete field is

```lean
fun u₀ => BddAbove (Set.range fun x => |u₀ x|) ∧ Continuous u₀
```

Add a named extraction lemma:

```lean
/-- Paper-positive interval-domain data are bounded in absolute value. -/
theorem intervalDomain_initialDatum_abs_bddAbove_of_paperPositive
    {u₀ : intervalDomain.Point → ℝ}
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀) :
    BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)) := by
  have hAdm := PaperPositiveInitialDatum.admissible hdatum
  -- `simp [intervalDomain]` normally exposes the concrete `initialAdmissible` field.
  simpa [intervalDomain] using hAdm.1

/-- Paper-positive interval-domain data are continuous. -/
theorem intervalDomain_initialDatum_continuous_of_paperPositive
    {u₀ : intervalDomain.Point → ℝ}
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀) :
    Continuous u₀ := by
  have hAdm := PaperPositiveInitialDatum.admissible hdatum
  simpa [intervalDomain] using hAdm.2
```

If `simpa [intervalDomain]` is too aggressive, replace each proof by:

```lean
  change BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)) ∧
      Continuous u₀ at hAdm
  exact hAdm.1
```

and similarly for `.2`.

### 3. Boundedness of a difference slice

This is useful for applying the pointwise sup-norm control to `fun x => u t x - u₀ x`.

```lean
/-- Absolute boundedness is closed under pointwise subtraction. -/
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
    |f x - g x| ≤ |f x| + |g x| := by
      simpa [sub_eq_add_neg] using abs_add (f x) (-g x)
    _ ≤ Mf + Mg := add_le_add hf_le hg_le
```

If the `abs_add` line complains because it is equality in the reverse direction, use:

```lean
      calc
        |f x - g x| = |f x + -g x| := by ring_nf
        _ ≤ |f x| + |-g x| := abs_add _ _
        _ = |f x| + |g x| := by rw [abs_neg]
```

### 4. Positive-time boundedness for the difference slice

This uses the checked `intervalDomain_solution_slice_abs_bddAbove`.

```lean
/-- The trace-difference slice is bounded at every positive time. -/
theorem intervalDomain_traceDiff_slice_abs_bddAbove_of_global
    {params : CM2Params} {t : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (ht0 : 0 < t)
    (hu₀_bdd : BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|))) :
    BddAbove (Set.range
      (fun x : intervalDomain.Point => |u t x - u₀ x|)) := by
  have hTpos : 0 < t + 1 := by linarith
  have hsol : IsPaper2ClassicalSolution intervalDomain params (t + 1) u v :=
    hglobal.classical hTpos
  have htmem : t ∈ Set.Ioo (0 : ℝ) (t + 1) := by
    exact ⟨ht0, by linarith⟩
  have hut_bdd : BddAbove (Set.range (fun x : intervalDomain.Point => |u t x|)) :=
    intervalDomain_solution_slice_abs_bddAbove hsol htmem
  exact bddAbove_abs_sub_of_bddAbove_abs hut_bdd hu₀_bdd
```

### 5. A pointwise trace consequence

This is a convenient wrapper around `InitialTrace.eventually_small`.

```lean
/-- Initial trace gives pointwise control of `u t - u₀` at small positive times. -/
theorem intervalDomain_initialTrace_pointwise_abs_lt
    {params : CM2Params} {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (htrace : InitialTrace intervalDomain u₀ u)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hu₀_bdd : BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)))
    {eps : ℝ} (heps : 0 < eps) :
    ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x : intervalDomain.Point, |u t x - u₀ x| < eps := by
  rcases InitialTrace.eventually_small htrace heps with ⟨δ, hδ, hδsmall⟩
  refine ⟨δ, hδ, ?_⟩
  intro t ht0 htδ x
  have hdiff_bdd :=
    intervalDomain_traceDiff_slice_abs_bddAbove_of_global
      (params := params) (t := t) (u₀ := u₀) (u := u) (v := v)
      hglobal ht0 hu₀_bdd
  exact intervalDomain_pointwise_abs_lt_of_supNorm_lt hdiff_bdd
    (hδsmall t ht0 htδ) x
```

This helper is short and high leverage. It avoids using `SupNormControlsPointwiseBefore` directly.

### 6. Uniform continuity of `rpow` on a positive compact interval

This is the real-power lemma. It is safe for every real exponent because the left endpoint is positive.

```lean
/-- On a compact interval bounded away from zero, `r ↦ r ^ p` is uniformly
continuous for every real exponent. -/
theorem real_rpow_uniformContinuousOn_Icc_of_pos_left
    {p a b : ℝ} (ha : 0 < a) :
    UniformContinuousOn (fun r : ℝ => r ^ p) (Set.Icc a b) := by
  have hcont : ContinuousOn (fun r : ℝ => r ^ p) (Set.Icc a b) := by
    exact continuousOn_id.rpow_const
      (fun r hr => Or.inl (ne_of_gt (lt_of_lt_of_le ha hr.1)))
  exact hcont.uniformContinuousOn_compact isCompact_Icc
```

Name risk: in some mathlib versions the last line is spelled using the compact set as receiver, e.g.

```lean
  exact isCompact_Icc.uniformContinuousOn_of_continuousOn hcont
```

The `ContinuousOn.rpow_const` pattern is already used in the repo, for example in `intervalDomain_u_rpow_intervalIntegrable_of_regularity` and `intervalDomain_power_jointContinuousOn`.

### 7. Initial datum power integrability

Positive-time integrability is already available as `intervalDomain_u_rpow_intervalIntegrable_of_regularity`. You still need the initial datum version.

```lean
/-- Paper-positive initial data have interval-integrable real powers. -/
theorem intervalDomain_initialDatum_rpow_intervalIntegrable_of_paperPositive
    {u₀ : intervalDomain.Point → ℝ} {p : ℝ}
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀) :
    IntervalIntegrable
      (intervalDomainLift (fun x : intervalDomain.Point => (u₀ x) ^ p))
      volume 0 1 := by
  rcases PaperPositiveInitialDatum.floor hdatum with ⟨η, hη, hfloor⟩
  have hu₀_cont : Continuous u₀ :=
    intervalDomain_initialDatum_continuous_of_paperPositive hdatum
  have hlift_cont : ContinuousOn (intervalDomainLift u₀) (Set.Icc (0 : ℝ) 1) := by
    -- On the closed interval, `intervalDomainLift u₀ y = u₀ ⟨y, hy⟩`.
    -- This follows from continuity of the subtype map; if automation struggles,
    -- prove it by `ContinuousOn.congr` against `fun y => u₀ ⟨y, hy⟩` on Icc.
    sorry -- proof skeleton only
  have hpow_cont : ContinuousOn
      (fun y : ℝ => (intervalDomainLift u₀ y) ^ p)
      (Set.Icc (0 : ℝ) 1) := by
    exact hlift_cont.rpow_const
      (fun y hy => by
        have hpos : 0 < intervalDomainLift u₀ y := by
          have hx : intervalDomain.Point := ⟨y, hy⟩
          have : η ≤ u₀ hx := hfloor hx
          simpa [intervalDomainLift, hy, hx] using lt_of_lt_of_le hη this
        exact Or.inl (ne_of_gt hpos))
  have htarget_cont : ContinuousOn
      (intervalDomainLift (fun x : intervalDomain.Point => (u₀ x) ^ p))
      (Set.Icc (0 : ℝ) 1) := by
    refine hpow_cont.congr ?_
    intro y hy
    simp [intervalDomainLift, hy]
  have htarget_cont_u : ContinuousOn
      (intervalDomainLift (fun x : intervalDomain.Point => (u₀ x) ^ p))
      (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le (zero_le_one)] using htarget_cont
  exact htarget_cont_u.intervalIntegrable
```

Do not leave the `sorry`; fill the `hlift_cont` proof with one of these routes:

* Show `ContinuousOn (fun y : ℝ => u₀ ⟨y, hy⟩) (Icc 0 1)` using `hu₀_cont.continuousOn.comp` with the continuous subtype constructor on the subtype domain.
* Or add a general lemma for lift continuity on `Icc` from continuity of an interval-domain function. The repo likely already has a lemma of this shape; search for `intervalDomainLift` and `ContinuousOn` before adding a new one.

### 8. Integral difference bound

This helper is worth adding as a standalone lemma. It avoids hunting for a specific `norm_integral_le` interval lemma.

```lean
/-- On the unit interval, a uniform pointwise bound controls the absolute
difference of concrete interval-domain integrals. -/
theorem intervalDomain_integral_sub_abs_le_of_pointwise_abs_le
    {f g : intervalDomain.Point → ℝ} {eps : ℝ}
    (heps : 0 ≤ eps)
    (hf_int : IntervalIntegrable (intervalDomainLift f) volume 0 1)
    (hg_int : IntervalIntegrable (intervalDomainLift g) volume 0 1)
    (hpoint : ∀ x : intervalDomain.Point, |f x - g x| ≤ eps) :
    |intervalDomain.integral f - intervalDomain.integral g| ≤ eps := by
  change |intervalDomainIntegral f - intervalDomainIntegral g| ≤ eps
  unfold intervalDomainIntegral
  have hsub_int : IntervalIntegrable
      (fun y : ℝ => intervalDomainLift f y - intervalDomainLift g y)
      volume 0 1 := hf_int.sub hg_int
  have hconst_pos : IntervalIntegrable (fun _ : ℝ => eps) volume 0 1 :=
    intervalIntegral.intervalIntegrable_const
  have hconst_neg : IntervalIntegrable (fun _ : ℝ => -eps) volume 0 1 :=
    intervalIntegral.intervalIntegrable_const
  have hle_pos :
      ∫ y in (0 : ℝ)..1, (intervalDomainLift f y - intervalDomainLift g y) ≤
        ∫ _y in (0 : ℝ)..1, eps := by
    refine intervalIntegral.integral_mono_on (by norm_num) hsub_int hconst_pos ?_
    intro y hy
    have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (zero_le_one)] using hy
    have h := (abs_le.mp (hpoint ⟨y, hyIcc⟩)).2
    simpa [intervalDomainLift, hyIcc] using h
  have hle_neg :
      ∫ _y in (0 : ℝ)..1, (-eps) ≤
        ∫ y in (0 : ℝ)..1, (intervalDomainLift f y - intervalDomainLift g y) := by
    refine intervalIntegral.integral_mono_on (by norm_num) hconst_neg hsub_int ?_
    intro y hy
    have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (zero_le_one)] using hy
    have h := (abs_le.mp (hpoint ⟨y, hyIcc⟩)).1
    simpa [intervalDomainLift, hyIcc] using h
  have hsub_eq :
      (∫ y in (0 : ℝ)..1, (intervalDomainLift f y - intervalDomainLift g y)) =
        (∫ y in (0 : ℝ)..1, intervalDomainLift f y) -
          (∫ y in (0 : ℝ)..1, intervalDomainLift g y) := by
    rw [intervalIntegral.integral_sub hf_int hg_int]
  have hconst_pos_eval : (∫ _y in (0 : ℝ)..1, eps) = eps := by
    rw [intervalIntegral.integral_const]
    norm_num [smul_eq_mul]
  have hconst_neg_eval : (∫ _y in (0 : ℝ)..1, (-eps)) = -eps := by
    rw [intervalIntegral.integral_const]
    norm_num [smul_eq_mul]
  rw [hconst_pos_eval] at hle_pos
  rw [hconst_neg_eval] at hle_neg
  rw [hsub_eq] at hle_pos hle_neg
  exact abs_le.mpr ⟨hle_neg, hle_pos⟩
```

This is likely compilable modulo tiny simplifier differences around `Set.uIcc_of_le` and `intervalIntegral.integral_const`.

## Main theorem implementation plan

The cleanest proof is epsilon-based. For fixed exponent `p`, use a target error `eps > 0` and prove eventual membership in the metric ball around the initial energy.

### Step A: get floor and a datum bound

```lean
intro p hp
rcases PaperPositiveInitialDatum.floor hdatum with ⟨η, hη, hfloor⟩
have hη2 : 0 < η / 2 := by linarith
have hu₀_bdd := intervalDomain_initialDatum_abs_bddAbove_of_paperPositive hdatum
rcases hu₀_bdd with ⟨Mraw, hMraw⟩
let M : ℝ := max (max Mraw 1) η + 1
have hM_pos : 0 < M := by dsimp [M]; linarith [le_max_right (max Mraw 1) η]
have hu₀_abs_le_M : ∀ x : intervalDomain.Point, |u₀ x| ≤ M := by
  intro x
  have hxraw : |u₀ x| ≤ Mraw := hMraw ⟨x, rfl⟩
  dsimp [M]
  linarith [le_max_left Mraw 1, le_max_left (max Mraw 1) η]
have hu₀_le_M : ∀ x : intervalDomain.Point, u₀ x ≤ M := fun x =>
  le_trans (le_abs_self _) (hu₀_abs_le_M x)
have hη_le_M : η ≤ M := by
  dsimp [M]
  linarith [le_max_right (max Mraw 1) η]
```

You can choose a cleaner `M`; the only needs are `η ≤ M`, `1 ≤ M`, and `|u₀ x| ≤ M`.

### Step B: use uniform continuity of `rpow`

For a given `eps > 0`, first convert the energy tolerance to a pointwise power tolerance. Since interval length is `1`, using the same `eps` is fine.

```lean
rw [Metric.tendsto_nhds]
intro eps heps
have heps2 : 0 < eps / 2 := by linarith
have huc : UniformContinuousOn (fun r : ℝ => r ^ p) (Set.Icc (η / 2) (M + 1)) :=
  real_rpow_uniformContinuousOn_Icc_of_pos_left hη2
```

Extract the uniform-continuity radius. The exact shape of `UniformContinuousOn` in Mathlib is:

```lean
UniformContinuousOn f s :=
  ∀ u, u ∈ 𝓤 α → ∃ v ∈ 𝓤 β, ∀ x₁ ∈ s, ∀ x₂ ∈ s, (x₁, x₂) ∈ v → (f x₁, f x₂) ∈ u
```

For metric spaces, a convenient route is often:

```lean
rcases Metric.uniformContinuousOn_iff.mp huc (eps / 2) heps2 with
  ⟨δpow, hδpow, hpow⟩
```

Expected resulting shape:

```lean
hpow : ∀ {a b}, a ∈ Set.Icc (η / 2) (M + 1) →
                b ∈ Set.Icc (η / 2) (M + 1) →
                dist a b < δpow → dist (a ^ p) (b ^ p) < eps / 2
```

If the exact lemma name is unavailable, use `huc` directly with `Metric.mem_uniformity_dist`. The `Metric.uniformContinuousOn_iff` form is usually the fastest.

### Step C: choose trace radius

Let

```lean
let traceRad : ℝ := min (min (η / 2) 1) (δpow / 2)
```

Then use the helper from Step 5:

```lean
have htraceRad : 0 < traceRad := by
  dsimp [traceRad]
  positivity
rcases intervalDomain_initialTrace_pointwise_abs_lt
    (params := params) (u₀ := u₀) (u := u) (v := v)
    htrace hglobal hu₀_bdd htraceRad with
  ⟨δtrace, hδtrace_pos, hδtrace⟩
```

Also shrink by `T` so that points of the filter stay in the intended `Ioc 0 T`, although for using global classical you can always use horizon `t+1`:

```lean
let δ : ℝ := min δtrace T
have hδ : 0 < δ := lt_min hδtrace_pos hT
```

### Step D: prove the eventual estimate

For `t` with `t ∈ Ioc 0 T` and `|t| < δ`, we have `0 < t`, `t ≤ T`, and `t < δtrace`; apply trace pointwise control.

For every `x`:

```lean
have hclose : |u t x - u₀ x| < traceRad := hδtrace t ht0 htδtrace x
have hut_lower : η / 2 ≤ u t x := by
  have hlow : u₀ x - traceRad < u t x := by
    -- from `abs_lt.mp hclose`
  have htrace_le : traceRad ≤ η / 2 := by
    dsimp [traceRad]; exact min_le_left_of_le ...
  linarith [hfloor x]
have hut_upper : u t x ≤ M + 1 := by
  have hu₀_upper := hu₀_le_M x
  have htrace_le_one : traceRad ≤ 1 := by ...
  have hupper : u t x < u₀ x + traceRad := (abs_lt.mp hclose).2
  linarith
have hu₀_mem : u₀ x ∈ Set.Icc (η / 2) (M + 1) := by
  constructor
  · linarith [hfloor x]
  · linarith [hu₀_le_M x]
have hut_mem : u t x ∈ Set.Icc (η / 2) (M + 1) := ⟨hut_lower, by linarith⟩
have hdist : dist (u t x) (u₀ x) < δpow := by
  rw [Real.dist_eq]
  exact lt_of_lt_of_le hclose (by dsimp [traceRad]; ... : traceRad ≤ δpow)
have hpow_close : |(u t x) ^ p - (u₀ x) ^ p| ≤ eps / 2 := by
  have hpdist := hpow hut_mem hu₀_mem hdist
  rw [Real.dist_eq] at hpdist
  exact le_of_lt hpdist
```

You can avoid some `<`/`≤` annoyance by choosing `traceRad := min (min (η / 4) (1 / 2)) (δpow / 2)` and using strict inequalities throughout.

### Step E: positive-time and datum integrability

For the `u t` slice:

```lean
have hsolt : IsPaper2ClassicalSolution intervalDomain params (t + 1) u v :=
  hglobal.classical (by linarith : 0 < t + 1)
have hut_int : IntervalIntegrable
    (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ p)) volume 0 1 :=
  intervalDomain_u_rpow_intervalIntegrable_of_regularity
    (q := p) hsolt ht0 (by linarith)
```

For the initial datum:

```lean
have hu0_int : IntervalIntegrable
    (intervalDomainLift (fun x : intervalDomain.Point => (u₀ x) ^ p)) volume 0 1 :=
  intervalDomain_initialDatum_rpow_intervalIntegrable_of_paperPositive hdatum
```

Then the integral estimate is immediate:

```lean
have hIntClose :
    |intervalDomain.integral (fun x : intervalDomain.Point => (u t x) ^ p) -
      intervalDomain.integral (fun x : intervalDomain.Point => (u₀ x) ^ p)| ≤ eps / 2 :=
  intervalDomain_integral_sub_abs_le_of_pointwise_abs_le
    (by linarith : 0 ≤ eps / 2) hut_int hu0_int hpow_close
have hIntClose_eps :
    dist (intervalDomain.integral (fun x : intervalDomain.Point => (u t x) ^ p))
      (intervalDomain.integral (fun x : intervalDomain.Point => (u₀ x) ^ p)) < eps := by
  rw [Real.dist_eq]
  linarith
```

### Step F: package into `Tendsto`

Use the metric tendsto form:

```lean
rw [Metric.tendsto_nhds]
intro eps heps
-- choose δ as above
filter_upwards [self_mem_nhdsWithin] with t ht using ?_
```

The exact `nhdsWithin` proof is often easier via `eventually_nhdsWithin_iff`. A robust final wrapper is:

```lean
rw [Metric.tendsto_nhds]
intro eps heps
-- produce δ > 0 and pointwise estimate for all t ∈ Ioc 0 T with dist t 0 < δ
refine (Metric.eventually_nhdsWithin_iff).2 ?_
refine ⟨δ, hδ, ?_⟩
intro t htIoc hdistt
have ht0 : 0 < t := htIoc.1
have htδ : t < δ := by
  rw [Real.dist_eq] at hdistt
  have ht_nonneg : 0 ≤ t := le_of_lt ht0
  simpa [abs_of_nonneg ht_nonneg] using hdistt
-- apply Step D/E and return `dist ... < eps`
```

If `Metric.eventually_nhdsWithin_iff` is not found, use:

```lean
refine eventually_nhdsWithin_iff.2 ?_
refine ⟨Metric.ball (0 : ℝ) δ, Metric.ball_mem_nhds 0 hδ, ?_⟩
intro t htball htIoc
-- `htball : t ∈ Metric.ball 0 δ`, hence `dist t 0 < δ`
```

## Main theorem skeleton

This is the shape I would implement after the helpers above. The body intentionally leaves the uniform-continuity extraction in a placeholder block because Mathlib’s exact metric-uniform-continuity lemma name can vary; all other parts are straightforward with the helpers.

```lean
theorem intervalDomain_initialTracePowerEnergyTendsto_of_paperPositive
    {params : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 < T)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v) :
    IntervalDomainInitialTracePowerEnergyTendsto u₀ u T p0 := by
  intro p hp
  rcases PaperPositiveInitialDatum.floor hdatum with ⟨η, hη, hfloor⟩
  have hη2 : 0 < η / 2 := by linarith
  have hu₀_bdd : BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)) :=
    intervalDomain_initialDatum_abs_bddAbove_of_paperPositive hdatum
  rcases hu₀_bdd with ⟨Mraw, hMraw⟩
  let M : ℝ := max (max Mraw 1) η + 1
  have hM_pos : 0 < M := by
    dsimp [M]
    have hη_le : η ≤ max (max Mraw 1) η := le_max_right _ _
    linarith
  have hu₀_abs_le_M : ∀ x : intervalDomain.Point, |u₀ x| ≤ M := by
    intro x
    have hxraw : |u₀ x| ≤ Mraw := hMraw ⟨x, rfl⟩
    dsimp [M]
    have hMraw_le : Mraw ≤ max Mraw 1 := le_max_left _ _
    have hmax_le : max Mraw 1 ≤ max (max Mraw 1) η := le_max_left _ _
    linarith
  have hu₀_le_M : ∀ x : intervalDomain.Point, u₀ x ≤ M := by
    intro x
    exact le_trans (le_abs_self _) (hu₀_abs_le_M x)
  have hη_le_M : η ≤ M := by
    dsimp [M]
    have hη_le : η ≤ max (max Mraw 1) η := le_max_right _ _
    linarith
  rw [Metric.tendsto_nhds]
  intro eps heps
  have heps2 : 0 < eps / 2 := by linarith
  have huc : UniformContinuousOn (fun r : ℝ => r ^ p) (Set.Icc (η / 2) (M + 1)) :=
    real_rpow_uniformContinuousOn_Icc_of_pos_left hη2
  -- Extract a radius `δpow > 0` from `huc` for tolerance `eps/2`.
  -- Preferred if available:
  -- rcases Metric.uniformContinuousOn_iff.mp huc (eps / 2) heps2 with
  --   ⟨δpow, hδpow, hpow⟩
  rcases sorry with ⟨δpow, hδpow, hpow⟩
  let traceRad : ℝ := min (min (η / 2) 1) (δpow / 2)
  have htraceRad : 0 < traceRad := by
    dsimp [traceRad]
    positivity
  rcases intervalDomain_initialTrace_pointwise_abs_lt
      (params := params) (u₀ := u₀) (u := u) (v := v)
      htrace hglobal hu₀_bdd htraceRad with
    ⟨δtrace, hδtrace_pos, hδtrace⟩
  let δ : ℝ := min δtrace T
  have hδ : 0 < δ := lt_min hδtrace_pos hT
  refine (Metric.eventually_nhdsWithin_iff).2 ?_
  refine ⟨δ, hδ, ?_⟩
  intro t htIoc hdistt
  have ht0 : 0 < t := htIoc.1
  have htδtrace : t < δtrace := by
    have htδ : t < δ := by
      rw [Real.dist_eq] at hdistt
      simpa [abs_of_nonneg ht0.le] using hdistt
    exact lt_of_lt_of_le htδ (min_le_left _ _)
  have hpoint_close : ∀ x : intervalDomain.Point, |u t x - u₀ x| < traceRad :=
    hδtrace t ht0 htδtrace
  have hpow_point : ∀ x : intervalDomain.Point,
      |(u t x) ^ p - (u₀ x) ^ p| ≤ eps / 2 := by
    intro x
    have hclose := hpoint_close x
    have htr_eta : traceRad ≤ η / 2 := by
      dsimp [traceRad]
      exact le_trans (min_le_left _ _) (le_rfl)
    have htr_one : traceRad ≤ 1 := by
      dsimp [traceRad]
      exact le_trans (min_le_left _ _) (min_le_right _ _)
    have htr_pow : traceRad ≤ δpow := by
      dsimp [traceRad]
      have hhalf : δpow / 2 ≤ δpow := by linarith [hδpow]
      exact le_trans (min_le_right _ _) hhalf
    have hu_lower : η / 2 ≤ u t x := by
      have hleft := (abs_lt.mp hclose).1
      linarith [hfloor x, htr_eta]
    have hu_upper : u t x ≤ M + 1 := by
      have hright := (abs_lt.mp hclose).2
      linarith [hu₀_le_M x, htr_one]
    have hu0_mem : u₀ x ∈ Set.Icc (η / 2) (M + 1) := by
      constructor
      · linarith [hfloor x]
      · linarith [hu₀_le_M x]
    have hut_mem : u t x ∈ Set.Icc (η / 2) (M + 1) := ⟨hu_lower, hu_upper⟩
    have hdist : dist (u t x) (u₀ x) < δpow := by
      rw [Real.dist_eq]
      exact lt_of_lt_of_le hclose htr_pow
    -- use `hpow hut_mem hu0_mem hdist`, with exact argument order from the UC lemma
    have hpd : dist ((u t x) ^ p) ((u₀ x) ^ p) < eps / 2 :=
      hpow hut_mem hu0_mem hdist
    rw [Real.dist_eq] at hpd
    exact le_of_lt hpd
  have hsolt : IsPaper2ClassicalSolution intervalDomain params (t + 1) u v :=
    hglobal.classical (by linarith : 0 < t + 1)
  have hut_int : IntervalIntegrable
      (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ p)) volume 0 1 :=
    intervalDomain_u_rpow_intervalIntegrable_of_regularity
      (q := p) hsolt ht0 (by linarith)
  have hu0_int : IntervalIntegrable
      (intervalDomainLift (fun x : intervalDomain.Point => (u₀ x) ^ p)) volume 0 1 :=
    intervalDomain_initialDatum_rpow_intervalIntegrable_of_paperPositive hdatum
  have hIntClose :
      |intervalDomain.integral (fun x : intervalDomain.Point => (u t x) ^ p) -
        intervalDomain.integral (fun x : intervalDomain.Point => (u₀ x) ^ p)| ≤ eps / 2 :=
    intervalDomain_integral_sub_abs_le_of_pointwise_abs_le
      (by linarith : 0 ≤ eps / 2) hut_int hu0_int hpow_point
  rw [Real.dist_eq]
  linarith
```

Replace the single `sorry` block by the exact `UniformContinuousOn` metric extraction available in your mathlib. If `Metric.eventually_nhdsWithin_iff` is not available, use the equivalent `eventually_nhdsWithin_iff` with `Metric.ball 0 δ` as described above.

## Warnings and assumptions

1. The theorem as stated does **not** need `0 < p0`, because `PaperPositiveInitialDatum` supplies a uniform lower floor, so all bases stay in a compact subset of `(0,∞)` for small positive time.

2. Do **not** weaken to plain `PositiveInitialDatum` without adding more assumptions. `PositiveInitialDatum` only gives positivity on `intervalDomain.inside`; endpoints may be zero. For real `p`, especially if `p` can be negative, `rpow` continuity at zero is the problem. A `PositiveInitialDatum` route would need `0 < p0` plus closed-domain nonnegativity of `u₀`, and it is strictly more annoying in Lean.

3. The global classical solution is used only for positive-time regularity and boundedness of `u t` slices. It is not used to control `u 0`, and should not be.

4. The theorem should be kept separate from `IntervalDomainInitialPowerEnergyCompatibleAtZero`. The current theorem proves only the deleted-right trace limit; the compatibility residual is what later turns it into full `ContinuousWithinAt` at the stored zero slice.
