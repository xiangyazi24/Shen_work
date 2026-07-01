# Q2829 shen2: audit of `IntervalDomain1DLinfRoute` energy/dissipation hole

Repo target: `xiangyazi24/Shen_work`, default branch `main`.

Current local target file from prompt:

```text
ShenWork/PDE/IntervalDomain1DLinfRoute.lean
```

User context: Codex has locally closed

```lean
intervalDomain_Linf_of_Lp_and_gradient
intervalDomain_all_Lp_of_Linf
intervalDomain_Proposition_2_5_1d
```

and the only remaining local hole is

```lean
intervalDomain_Lp_energy_and_dissipation_of_regularity
```

I inspected the current `main` versions of the requested files and treated the local edits conceptually. I did not modify or rely on Zinan-owned producer files:

```text
ShenWork/PDE/P3MoserHighExcursionProducer.lean
ShenWork/PDE/P3MoserThresholdPlanProducer.lean
```

## Verdict

`intervalDomain_Lp_energy_and_dissipation_of_regularity` is **not derivable as stated** from the current in-repo APIs.

The minimal obstruction is not a missing Lean trick. The statement asks for a **uniform pointwise-in-time** bound on

```lean
intervalDomain.integral (fun x =>
  (intervalDomain.gradNorm
    (fun y => (u t y) ^ (pExp / 2)) x) ^ 2)
```

for every `0 < t < T`. The current energy/Moser APIs provide:

1. pointwise differential inequalities involving `Y'`, `Y`, `G`, and `Z`, and
2. integrated-in-time Moser/dissipation control,

but they do **not** provide a pointwise-in-time upper bound for `G(t)`.

The second independent obstruction is exponent scope: `hboot : AbstractLpBootstrapHypothesis ... p0` supplies the base bootstrap data at `p0`; it does not by itself give `LpPowerBoundedBefore intervalDomain pExp T u` for every `pExp ≥ p0`. That higher-exponent fact is precisely what Moser iteration or another bootstrap step is meant to prove.

## Evidence from current APIs

### 1. `LpBootstrapEnergyInequality` is a differential inequality, not a bound theorem

In `IntervalDomainLpBootstrapEnergyInequality.lean`, the assembled theorem is:

```lean
theorem intervalDomain_LpBootstrapEnergyInequality_of_regularity
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0) :
    LpBootstrapEnergyInequality intervalDomain u T rho p0
```

Unfolding its use, for each `pExp ≥ p0` it produces constants `A`, `B`, `K`, `L` and a pointwise inequality of the form

```lean
(1 / pExp) * deriv (fun τ => ∫ u(τ)^pExp) t
  + A * G_pExp(t)
  + B * Y_pExp(t)
≤ K * Z_{pExp+rho}(t) + L
```

This is not enough to bound either `Y_pExp(t)` or `G_pExp(t)` without additional control of the higher power `Z_{pExp+rho}` and the derivative term.

Relevant exact names:

```lean
intervalDomain_LpBootstrapEnergyInequality_of_regularity
intervalDomainLpMoserGradientControl_of_regularity
intervalDomain_moser_gradient_integral_eq_weighted_of_regularity
intervalDomainLpEnergy_eq_power_of_regularity
```

`intervalDomain_moser_gradient_integral_eq_weighted_of_regularity` is useful: it identifies the Moser gradient integral with the weighted dissipation,

```lean
intervalDomain.integral
  (fun x => (intervalDomain.gradNorm
    (fun y => (u t y) ^ (pExp / 2)) x) ^ 2)
= (pExp / 2) ^ 2 * intervalDomainLpWeightedGradientDissipation pExp u t
```

but it is only an identity/comparison, not a bound.

### 2. `hboot` gives a base `LpPowerBoundedBefore`, not all higher exponents

`LpPowerBoundedBefore` is the expected pointwise-in-time Lp bound predicate:

```lean
def LpPowerBoundedBefore
    (D : BoundedDomainData) (pExp Tmax : ℝ) (u : ℝ → D.Point → ℝ) : Prop :=
  ∃ C, ∀ t, 0 < t → t < Tmax →
    D.integral (fun x => (u t x) ^ pExp) ≤ C
```

The Moser closure files treat higher exponents as a theorem output, not as a direct consequence of the base bootstrap hypothesis. For example:

```lean
all_exponents_of_moser_iteration_chain
all_exponents_of_energy_nonnegB_relative_interpolation_lpmono
```

need an iteration step / relative interpolation / dissipation data. So for arbitrary `pExp ≥ p0`, the desired `M_Lp` is not available from `hboot` alone.

### 3. The repository explicitly diagnoses pointwise dissipation as the wrong shape

`P3MoserDissipationShape.lean` says the faithful shape is integrated. It defines the old pointwise nonnegative-`B` predicate:

```lean
def MoserDissipationDropBeforeNonnegB
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → ∀ A B K L_const, 0 ≤ B →
    (∀ t, 0 < t → t < T →
      (1 / p) * deriv (fun τ => D.integral (fun x => (u τ x) ^ p)) t +
        A * D.integral (fun x =>
          (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
        B * D.integral (fun x => (u t x) ^ p) ≤
      K * D.integral (fun x => (u t x) ^ (p + rho)) + L_const) →
    ∀ t, 0 < t → t < T →
      0 ≤
        (1 / p) * deriv (fun τ => D.integral (fun x => (u τ x) ^ p)) t +
          B * D.integral (fun x => (u t x) ^ p)
```

but it also contains the diagnostic counterexample:

```lean
theorem unitLinearDrop_not_MoserDissipationDropBeforeNonnegB :
    ¬ MoserDissipationDropBeforeNonnegB
      unitLinearDropDomain unitLinearDropU 1 1 1
```

So the repository already records that the pointwise-drop/pointwise-dissipation expectation is too strong unless supplied as a genuine analytic atom.

The integrated replacement is:

```lean
def IntegratedMoserDissipationDropBefore
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T _rho p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → ∃ C, 0 ≤ C ∧
    ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
      D.integral (fun x => (u t2 x) ^ p) -
          D.integral (fun x => (u t1 x) ^ p) +
        2 * ∫ s in t1..t2,
          D.integral (fun x =>
            (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2) ≤
      C * p * ∫ s in t1..t2,
        max 1 (D.integral (fun x => (u s x) ^ p))
```

### 4. `P3MoserIntegratedClosure` only gives integrated gradient bounds

`P3MoserIntegratedClosure.lean` has the exact routine algebra for integrated dissipation:

```lean
theorem integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds
    ... :
    ∃ C, 0 ≤ C ∧
      2 * ∫ s in a..b,
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2) ≤
        M + C * p * H
```

This bounds a **time integral** of the gradient energy on `[a,b]`. It does not imply

```lean
∀ t, 0 < t → t < T → G(t) ≤ M_diss
```

without an additional pointwise regularity/maximum principle estimate. Even continuity of `G(t)` plus an integrated bound on `[0,T]` does not give a uniform pointwise bound unless there is a local modulus or differential control; continuous functions can have high narrow spikes with bounded integral.

## Why `hlogistic_dominates : rho < params.α` does not close the hole

The condition `rho < params.α` is the right analytic direction for absorbing the higher power in an integrated or differential inequality, but the current theorem does not include the actual Young/logistic absorption lemma needed to convert

```lean
K * ∫ u^(pExp + rho)
```

into a closed bound in `Y_pExp` and `G_pExp`. More importantly, even if such an absorption were added, the existing repository route formalizes the faithful output as an integrated Moser step, not a pointwise `G(t)` bound.

## What is provable now

A small bound extractor from an already-supplied `LpPowerBoundedBefore` is provable immediately:

```lean
theorem intervalDomain_Lp_bound_of_LpPowerBoundedBefore
    {T pExp : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hLp : LpPowerBoundedBefore intervalDomain pExp T u) :
    ∃ M_Lp : ℝ,
      0 ≤ M_Lp ∧
      ∀ t, 0 < t → t < T →
        intervalDomain.integral (fun x => (u t x) ^ pExp) ≤ M_Lp := by
  rcases hLp with ⟨C, hC⟩
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro t ht0 htT
  exact le_trans (hC t ht0 htT) (le_max_right _ _)
```

And a repackaging theorem is provable if the pointwise gradient bound is supplied explicitly:

```lean
def IntervalDomainPointwiseMoserGradientBoundBefore
    (u : ℝ → intervalDomain.Point → ℝ) (T pExp : ℝ) : Prop :=
  ∃ M_diss : ℝ,
    0 ≤ M_diss ∧
    ∀ t, 0 < t → t < T →
      intervalDomain.integral (fun x =>
        (intervalDomain.gradNorm
          (fun y => (u t y) ^ (pExp / 2)) x) ^ 2) ≤ M_diss

theorem intervalDomain_Lp_energy_and_dissipation_of_Lp_and_pointwiseGradient
    {T pExp : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hLp : LpPowerBoundedBefore intervalDomain pExp T u)
    (hgrad : IntervalDomainPointwiseMoserGradientBoundBefore u T pExp) :
    ∃ M_Lp M_diss : ℝ,
      0 ≤ M_Lp ∧ 0 ≤ M_diss ∧
      (∀ t, 0 < t → t < T →
        intervalDomain.integral (fun x => (u t x) ^ pExp) ≤ M_Lp) ∧
      (∀ t, 0 < t → t < T →
        intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm
            (fun y => (u t y) ^ (pExp / 2)) x) ^ 2) ≤ M_diss) := by
  rcases intervalDomain_Lp_bound_of_LpPowerBoundedBefore hLp with
    ⟨M_Lp, hMLp_nonneg, hMLp⟩
  rcases hgrad with ⟨M_diss, hMdiss_nonneg, hMdiss⟩
  exact ⟨M_Lp, M_diss, hMLp_nonneg, hMdiss_nonneg, hMLp, hMdiss⟩
```

This is Lean-friendly and directly feeds the already-closed local `intervalDomain_Linf_of_Lp_and_gradient` theorem.

## Recommended replacement signature

Replace the unprovable theorem with a statement that makes the missing pointwise gradient estimate explicit. This keeps the direct 1D `L∞` route honest:

```lean
def IntervalDomainPointwiseMoserGradientBoundBefore
    (u : ℝ → intervalDomain.Point → ℝ) (T pExp : ℝ) : Prop :=
  ∃ M_diss : ℝ,
    0 ≤ M_diss ∧
    ∀ t, 0 < t → t < T →
      intervalDomain.integral (fun x =>
        (intervalDomain.gradNorm
          (fun y => (u t y) ^ (pExp / 2)) x) ^ 2) ≤ M_diss

theorem intervalDomain_Lp_energy_and_dissipation_of_Lp_and_pointwiseGradient
    {T pExp : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hLp : LpPowerBoundedBefore intervalDomain pExp T u)
    (hgrad : IntervalDomainPointwiseMoserGradientBoundBefore u T pExp) :
    ∃ M_Lp M_diss : ℝ,
      0 ≤ M_Lp ∧ 0 ≤ M_diss ∧
      (∀ t, 0 < t → t < T →
        intervalDomain.integral (fun x => (u t x) ^ pExp) ≤ M_Lp) ∧
      (∀ t, 0 < t → t < T →
        intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm
            (fun y => (u t y) ^ (pExp / 2)) x) ^ 2) ≤ M_diss)
```

Then the direct 1D L∞ route should take:

```lean
hLp : LpPowerBoundedBefore intervalDomain pExp T u
hgrad : IntervalDomainPointwiseMoserGradientBoundBefore u T pExp
```

instead of trying to derive both from `henergy` and `hboot`.

## If the goal is to stay within existing integrated APIs

Use an integrated replacement, but note that this is **not enough** for the current pointwise Agmon step:

```lean
theorem intervalDomain_integrated_dissipation_bound_of_integratedMoser
    {T rho p0 p a b M H : ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (hinteg : IntegratedMoserDissipationDropBefore intervalDomain u T rho p0)
    (hp : p0 ≤ p)
    (hp_nonneg : 0 ≤ p)
    (haT : a ∈ Set.Icc (0 : ℝ) T)
    (hbT : b ∈ Set.Icc a T)
    (hYa : intervalDomain.integral (fun x => (u a x) ^ p) ≤ M)
    (hYb_nonneg : 0 ≤ intervalDomain.integral (fun x => (u b x) ^ p))
    (hmaxInt :
      ∫ s in a..b,
        max 1 (intervalDomain.integral (fun x => (u s x) ^ p)) ≤ H) :
    ∃ C, 0 ≤ C ∧
      2 * ∫ s in a..b,
        intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm
            (fun y => (u s y) ^ (p / 2)) x) ^ 2) ≤
        M + C * p * H :=
  integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds
    hinteg hp hp_nonneg haT hbT hYa hYb_nonneg hmaxInt
```

This is already essentially present as `integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds`. It is the right API for an integrated Moser/first-crossing route, but it cannot replace the pointwise `M_diss` required by `intervalDomain_Linf_of_Lp_and_gradient`.

## Bottom line for Codex

Do not try to prove the original theorem by clever use of `henergy`; it asks for a pointwise gradient bound that the repo intentionally does not provide. The correct non-Zinan patch is to replace it with the explicit pointwise-gradient-bound frontier above, or to reroute the 1D path through integrated Moser APIs and change the downstream Agmon step accordingly. The former is the minimal change that preserves the already-closed direct `intervalDomain_Linf_of_Lp_and_gradient` route.
