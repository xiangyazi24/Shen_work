# Q2885 shen2: positive-start PDE-term continuity audit

Repo target: `xiangyazi24/Shen_work`, Lean 4 / Mathlib.

Files inspected on `main` through the GitHub connector:

```text
ShenWork/PDE/P3MoserEnergyContinuity.lean
ShenWork/PDE/IntervalDomain.lean
ShenWork/Paper2/Statements.lean
ShenWork/Paper2/IntervalDomainEnergyStep.lean
ShenWork/Paper2/IntervalDomainLpEnergyFrontiers.lean
ShenWork/Paper2/IntervalDomainL2PDEIntegral.lean
```

Note: the connector-visible `main` version of `P3MoserEnergyContinuity.lean` is older than the state described in the prompt; the logistic theorem and the `IntervalDomainLpDiffusionChemotaxisPositiveStartWindowContinuity` / `IntervalDomainLpPDETermPositiveStartWindowContinuity` declarations are treated as current local compiled context.

## Verdict

The logistic positive-start continuity route is special because its integrand is built only out of the solution field `u`, powers of `u`, and constants. The current APIs already expose exactly the right ingredients for that: joint continuity of `(t,x) ↦ intervalDomainLift (u t) x`, positivity of `u`, compact slab boundedness, and `intervalIntegral.continuousWithinAt_of_dominated_interval`.

For the remaining two pieces:

* `s ↦ q * intervalDomainLpDiffusionIntegral q u s`
* `s ↦ q * (params.χ₀ * intervalDomainLpChemotaxisIntegral params q u v s)`

there is **not yet a direct proof from current APIs alone**. The obstacle is precise:

* diffusion continuity needs positive-start joint time-space continuity of the lifted Lp diffusion integrand, equivalently at least joint continuity of the lifted spatial Laplacian field `(s,y) ↦ Δ(u s)(y)` on `[a,b] × [0,1]`;
* chemotaxis continuity needs positive-start joint time-space continuity of the lifted chemotaxis-divergence field `(s,y) ↦ chemotaxisDiv params (u s) (v s)(y)` on `[a,b] × [0,1]`.

`intervalDomainClassicalRegularity` currently gives joint continuity of the solution fields and time-derivative fields, and per-fixed-time closed spatial `C²`; it does **not** give joint time-space continuity of the second spatial derivative / Laplacian or of the chemotaxis divergence. Per-time `ContDiffOn` is enough for spatial integrability at each fixed time, but not enough for continuity in time of the spatial integrals.

So the honest no-sorry route is:

1. add a generic interval-integral continuity wrapper from joint continuity of the lifted integrand;
2. prove diffusion and chemotaxis continuity from explicit joint-continuity hypotheses for their lifted integrands;
3. discharge those joint-continuity hypotheses later from stronger spatial `C^{2,1}` APIs, not from the current per-time `ContDiffOn` alone.

## Relevant existing definitions

From `IntervalDomainEnergyStep.lean`:

```lean
def intervalDomainLpDiffusionTest
    (pExp : ℝ) (u : ℝ → intervalDomain.Point → ℝ)
    (t : ℝ) (x : intervalDomain.Point) : ℝ :=
  |u t x| ^ (pExp - 2) * u t x

def intervalDomainLpDiffusionIntegral
    (pExp : ℝ) (u : ℝ → intervalDomain.Point → ℝ) (t : ℝ) : ℝ :=
  intervalDomain.integral
    (fun x =>
      intervalDomainLpDiffusionTest pExp u t x *
        intervalDomain.laplacian (u t) x)

def intervalDomainLpChemotaxisIntegral
    (params : CM2Params) (pExp : ℝ)
    (u v : ℝ → intervalDomain.Point → ℝ) (t : ℝ) : ℝ :=
  intervalDomain.integral
    (fun x =>
      intervalDomainLpDiffusionTest pExp u t x *
        intervalDomain.chemotaxisDiv params (u t) (v t) x)
```

From `IntervalDomain.lean`, the concrete operators are:

```lean
def intervalDomainGradNorm (f : intervalDomainPoint → ℝ)
    (x : intervalDomainPoint) : ℝ :=
  |deriv (intervalDomainLift f) x.1|

def intervalDomainLaplacian (f : intervalDomainPoint → ℝ)
    (x : intervalDomainPoint) : ℝ :=
  deriv (fun y : ℝ => deriv (intervalDomainLift f) y) x.1

def intervalDomainChemotaxisDiv (p : CM2Params)
    (u v : intervalDomainPoint → ℝ) (x : intervalDomainPoint) : ℝ :=
  deriv
    (fun y : ℝ =>
      intervalDomainLift u y * deriv (intervalDomainLift v) y /
        (1 + intervalDomainLift v y) ^ p.β)
    x.1
```

From `IntervalDomainLpEnergyFrontiers.lean`, the useful fixed-time integrability lemmas already exist:

```lean
intervalDomainLpDiffusionTest_lift_eq_on_Icc
intervalDomainLpDiffusionTest_contDiffOn_two_of_regularity
intervalDomainLift_laplacian_intervalIntegrable_of_contDiffOn
intervalDomainLift_lp_diffusion_intervalIntegrable_of_regularity
intervalDomainLift_lp_chemotaxis_intervalIntegrable_of_regularity
intervalDomainLift_lp_logistic_intervalIntegrable_of_regularity
```

These are fixed-time spatial integrability facts, not time-continuity facts.

## Why the logistic route works

The logistic integrand can be rewritten on the slab as a continuous expression in `intervalDomainLift (u s) y`:

```lean
(|u|^(q-2) * u) * (u * (a - b * u^alpha))
```

On a positive-start window `0 < a ≤ s ≤ b ≤ T`, use `hglobal.classical (T + 1)` so that even `s = T` is an interior time for the longer horizon. Positivity gives the nonzero side condition for `Real.rpow`; joint solution continuity gives joint continuity of all factors; compactness gives a uniform bound; then `intervalIntegral.continuousWithinAt_of_dominated_interval` gives continuity of the integral.

That pattern does not use any spatial derivative joint-continuity.

## Why diffusion is not directly provable yet

The diffusion integrand is

```lean
intervalDomainLpDiffusionTest q u s x * intervalDomain.laplacian (u s) x
```

The diffusion-test factor should be provable jointly continuous on a positive-start slab from existing data:

* `intervalDomain_solution_jointContinuousOn` gives joint continuity of `u`;
* `IsPaper2ClassicalSolution.u_pos'` gives positivity, hence the `rpow` side condition;
* `intervalDomainLpDiffusionTest_lift_eq_on_Icc` is the fixed-time lift simplifier.

But the second factor requires a joint-continuity theorem for

```lean
(s, y) ↦ intervalDomainLift (fun x => intervalDomain.laplacian (u s) x) y
```

or, equivalently, for

```lean
(s, y) ↦ deriv (fun z => deriv (intervalDomainLift (u s)) z) y
```

on `[a,b] × [0,1]` (up to the usual harmless endpoint/a.e. lift handling). Current `intervalDomainClassicalRegularity` gives per-time `ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Icc 0 1)`, but that only says `y ↦ Δu(t,y)` is continuous for fixed `t`. It does not say `t ↦ Δu(t,·)` is continuous, nor joint continuity in `(t,y)`.

Therefore diffusion positive-start continuity needs the exact missing API:

```lean
/-- Positive-start joint continuity of the lifted interval-domain Laplacian. -/
theorem intervalDomain_laplacian_jointContinuousOn_positiveStart_of_global_classical
    {params : CM2Params} {T a b : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b ≤ T) :
    ContinuousOn
      (fun sy : ℝ × ℝ =>
        intervalDomainLift
          (fun x : intervalDomain.Point => intervalDomain.laplacian (u sy.1) x)
          sy.2)
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)
```

A slightly more direct but less reusable missing API is:

```lean
/-- Positive-start joint continuity of the full lifted Lp diffusion integrand. -/
theorem intervalDomain_lpDiffusionIntegrand_jointContinuousOn_positiveStart_of_global_classical
    {params : CM2Params} {T q a b : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b ≤ T) :
    ContinuousOn
      (fun sy : ℝ × ℝ =>
        intervalDomainLift
          (fun x : intervalDomain.Point =>
            intervalDomainLpDiffusionTest q u sy.1 x *
              intervalDomain.laplacian (u sy.1) x)
          sy.2)
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)
```

The second theorem is the smallest missing API for finishing this frontier if the only consumer is the integral continuity theorem.

## Why chemotaxis is not directly provable yet

The chemotaxis integrand is

```lean
intervalDomainLpDiffusionTest q u s x *
  intervalDomain.chemotaxisDiv params (u s) (v s) x
```

Again the `intervalDomainLpDiffusionTest` factor should follow from `u` joint continuity and positivity. The missing part is joint continuity of the chemotaxis divergence:

```lean
(s, y) ↦ intervalDomainLift
  (intervalDomain.chemotaxisDiv params (u s) (v s)) y
```

The operator itself unfolds to a spatial derivative:

```lean
deriv (fun y =>
  intervalDomainLift (u s) y * deriv (intervalDomainLift (v s)) y /
    (1 + intervalDomainLift (v s) y) ^ params.β)
```

To prove its joint continuity from lower-level facts, one would need joint continuity of `u`, `v`, the spatial derivative of `v`, and enough joint spatial differentiability/continuity of that flux derivative. Current APIs do not expose this as a slab-continuity theorem.

Exact missing API:

```lean
/-- Positive-start joint continuity of the lifted interval-domain chemotaxis
    divergence. -/
theorem intervalDomain_chemotaxisDiv_jointContinuousOn_positiveStart_of_global_classical
    {params : CM2Params} {T a b : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b ≤ T) :
    ContinuousOn
      (fun sy : ℝ × ℝ =>
        intervalDomainLift
          (intervalDomain.chemotaxisDiv params (u sy.1) (v sy.1)) sy.2)
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)
```

Or direct consumer API:

```lean
/-- Positive-start joint continuity of the full lifted Lp chemotaxis integrand. -/
theorem intervalDomain_lpChemotaxisIntegrand_jointContinuousOn_positiveStart_of_global_classical
    {params : CM2Params} {T q a b : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b ≤ T) :
    ContinuousOn
      (fun sy : ℝ × ℝ =>
        intervalDomainLift
          (fun x : intervalDomain.Point =>
            intervalDomainLpDiffusionTest q u sy.1 x *
              intervalDomain.chemotaxisDiv params (u sy.1) (v sy.1) x)
          sy.2)
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)
```

This is the smallest missing API for the chemotaxis half if the only target is integral continuity.

## Reusable no-sorry wrapper once joint-integrand continuity is supplied

Add this generic lemma in `P3MoserEnergyContinuity.lean` near the logistic dominated-continuity helpers. It is PDE-independent and mirrors the existing logistic proof pattern.

```lean
/-- Positive-start time continuity of an interval-domain integral from joint
continuity of its lifted integrand on the compact time-space slab. -/
theorem intervalDomainIntegral_continuousOn_of_lift_jointContinuousOn_Icc
    {F : ℝ → intervalDomain.Point → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hF : ContinuousOn
      (fun sy : ℝ × ℝ => intervalDomainLift (F sy.1) sy.2)
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (fun s => intervalDomain.integral (F s)) (Set.Icc a b) := by
  -- Proof style:
  -- 1. `change ContinuousOn (fun s => intervalDomainIntegral (F s)) ...`.
  -- 2. `unfold intervalDomainIntegral` so the target is continuity of
  --    `fun s => ∫ y in (0:ℝ)..1, intervalDomainLift (F s) y`.
  -- 3. Use compactness of `Icc a b ×ˢ Icc 0 1` and `hF.norm` to obtain a
  --    uniform bound `M` on the lifted integrand.
  -- 4. For each `s0 ∈ Icc a b`, apply
  --    `intervalIntegral.continuousWithinAt_of_dominated_interval` with:
  --       * pointwise-in-`y` continuity in `s`, obtained from `hF` by composing
  --         the map `s ↦ (s,y)`;
  --       * domination by the constant bound `M`;
  --       * interval endpoints `0` and `1`.
  -- 5. Close `ContinuousOn` by `intro s0 hs0`.
```

This is a no-sorry route; the proof is the same compact-dominated-continuity skeleton already used for the logistic theorem.

Then the diffusion theorem becomes a one-liner wrapper after the joint integrand API:

```lean
theorem intervalDomain_lpDiffusionIntegral_continuousOn_positiveStart_of_integrand_joint
    {params : CM2Params} {T q a b : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hJ : ContinuousOn
      (fun sy : ℝ × ℝ =>
        intervalDomainLift
          (fun x : intervalDomain.Point =>
            intervalDomainLpDiffusionTest q u sy.1 x *
              intervalDomain.laplian (u sy.1) x)  -- use `laplacian`; typo here only in comment
          sy.2)
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hab : a ≤ b) :
    ContinuousOn
      (fun s => q * intervalDomainLpDiffusionIntegral q u s)
      (Set.Icc a b) := by
  have hInt := intervalDomainIntegral_continuousOn_of_lift_jointContinuousOn_Icc
    (F := fun s =>
      fun x : intervalDomain.Point =>
        intervalDomainLpDiffusionTest q u s x * intervalDomain.laplacian (u s) x)
    hab hJ
  simpa [intervalDomainLpDiffusionIntegral] using continuousOn_const.mul hInt
```

Use `intervalDomain.laplacian`, not `intervalDomain.laplian`.

The chemotaxis theorem is identical:

```lean
theorem intervalDomain_lpChemotaxisIntegral_continuousOn_positiveStart_of_integrand_joint
    {params : CM2Params} {T q a b : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hJ : ContinuousOn
      (fun sy : ℝ × ℝ =>
        intervalDomainLift
          (fun x : intervalDomain.Point =>
            intervalDomainLpDiffusionTest q u sy.1 x *
              intervalDomain.chemotaxisDiv params (u sy.1) (v sy.1) x)
          sy.2)
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hab : a ≤ b) :
    ContinuousOn
      (fun s =>
        q * (params.χ₀ * intervalDomainLpChemotaxisIntegral params q u v s))
      (Set.Icc a b) := by
  have hInt := intervalDomainIntegral_continuousOn_of_lift_jointContinuousOn_Icc
    (F := fun s =>
      fun x : intervalDomain.Point =>
        intervalDomainLpDiffusionTest q u s x *
          intervalDomain.chemotaxisDiv params (u s) (v s) x)
    hab hJ
  have hscaled : ContinuousOn
      (fun s => params.χ₀ * intervalDomainLpChemotaxisIntegral params q u v s)
      (Set.Icc a b) := by
    simpa [intervalDomainLpChemotaxisIntegral] using continuousOn_const.mul hInt
  simpa [mul_assoc] using continuousOn_const.mul hscaled
```

Finally package both:

```lean
theorem intervalDomain_lpDiffusionChemotaxisPositiveStartWindowContinuity_of_integrand_joint
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hDiffJ : ∀ q, p0 ≤ q → ∀ a b, 0 < a → a ≤ b → b ≤ T →
      ContinuousOn
        (fun sy : ℝ × ℝ =>
          intervalDomainLift
            (fun x : intervalDomain.Point =>
              intervalDomainLpDiffusionTest q u sy.1 x *
                intervalDomain.laplacian (u sy.1) x)
            sy.2)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hChemJ : ∀ q, p0 ≤ q → ∀ a b, 0 < a → a ≤ b → b ≤ T →
      ContinuousOn
        (fun sy : ℝ × ℝ =>
          intervalDomainLift
            (fun x : intervalDomain.Point =>
              intervalDomainLpDiffusionTest q u sy.1 x *
                intervalDomain.chemotaxisDiv params (u sy.1) (v sy.1) x)
            sy.2)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)) :
    IntervalDomainLpDiffusionChemotaxisPositiveStartWindowContinuity
      params u v T p0 := by
  intro q hp a b ha hab hbT
  exact ⟨
    intervalDomain_lpDiffusionIntegral_continuousOn_positiveStart_of_integrand_joint
      (q := q) (a := a) (b := b) (hDiffJ q hp a b ha hab hbT) hab,
    intervalDomain_lpChemotaxisIntegral_continuousOn_positiveStart_of_integrand_joint
      (params := params) (q := q) (a := a) (b := b)
      (hChemJ q hp a b ha hab hbT) hab⟩
```

## Can the joint-integrand hypotheses be discharged now?

### Diffusion-test factor

Likely yes, with existing APIs. The lemma should look like:

```lean
theorem intervalDomain_lpDiffusionTest_lift_jointContinuousOn_positiveStart_of_global_classical
    {params : CM2Params} {T q a b : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b ≤ T) :
    ContinuousOn
      (fun sy : ℝ × ℝ =>
        intervalDomainLift (intervalDomainLpDiffusionTest q u sy.1) sy.2)
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)
```

Proof route:

* Use `hsol := hglobal.classical (T + 1) (by linarith)` so every `s ∈ Icc a b` is strict interior for `T+1`.
* Use `intervalDomain_solution_jointContinuousOn hsol`, restricted to `Icc a b × Icc 0 1`.
* Use closed-domain positivity `hsol.u_pos'` for the nonzero side condition in `ContinuousOn.rpow`.
* Use the identity
  ```lean
  |u|^(q-2) * u = u^(q-2) * u
  ```
  from positivity, through `intervalDomainLpDiffusionTest_lift_eq_on_Icc` / direct `simp [intervalDomainLift, hy, intervalDomainLpDiffusionTest, abs_of_pos ...]`.

### Laplacian factor

Not directly from current APIs. Need:

```lean
intervalDomain_laplacian_lift_jointContinuousOn_positiveStart_of_global_classical
```

or the full diffusion integrand joint-continuity theorem. Per-time `ContDiffOn ℝ 2` does not supply time continuity of the second spatial derivative.

### Chemotaxis-divergence factor

Not directly from current APIs. Need:

```lean
intervalDomain_chemotaxisDiv_lift_jointContinuousOn_positiveStart_of_global_classical
```

or the full chemotaxis integrand joint-continuity theorem. This is stronger than existing fixed-time integrability lemmas and requires joint control of the spatial derivative of the chemotactic flux.

## Recommended next no-sorry patch

Add the generic lemma

```lean
intervalDomainIntegral_continuousOn_of_lift_jointContinuousOn_Icc
```

and the two wrappers

```lean
intervalDomain_lpDiffusionIntegral_continuousOn_positiveStart_of_integrand_joint
intervalDomain_lpChemotaxisIntegral_continuousOn_positiveStart_of_integrand_joint
```

in `P3MoserEnergyContinuity.lean`. These are pure dominated-continuity wrappers and should compile without touching producer files. Then leave exactly two named frontier inputs:

```lean
intervalDomain_lpDiffusionIntegrand_jointContinuousOn_positiveStart_of_global_classical
intervalDomain_lpChemotaxisIntegrand_jointContinuousOn_positiveStart_of_global_classical
```

Do not try to prove those from continuity of `u` alone. They require joint continuity of spatial derivative/laplacian/chemotaxis-divergence data not currently exposed by `intervalDomainClassicalRegularity`.

## Final classification

| Target | Directly provable from current APIs? | Reason |
|---|---:|---|
| Logistic positive-start continuity | Yes, already done locally | only uses joint `u` continuity, positivity, rpow, compact domination |
| Diffusion positive-start continuity | Not yet directly | needs joint time-space continuity of lifted Laplacian or full diffusion integrand |
| Chemotaxis positive-start continuity | Not yet directly | needs joint time-space continuity of lifted chemotaxis divergence or full chemotaxis integrand |
| Wrapper from joint integrand continuity to integral continuity | Yes | generic compact-slab dominated-continuity argument |
