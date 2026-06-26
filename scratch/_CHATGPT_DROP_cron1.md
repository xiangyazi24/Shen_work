# Q691 / cron1: `ContDiff ℝ 4 (fun x => ν * u x ^ γ)` via `Real.rpow`

Repo target: `xiangyazi24/Shen_work`.  Scratch write target: branch `chatgpt-scratch`.

## Verdict

Yes: the Mathlib chain works for `n = 4`.

For global functions, the most direct lemma is:

```lean
ContDiff.rpow_const_of_ne
```

It preserves the **same arbitrary order** `n : WithTop ℕ∞`, so it applies directly to `n = 4`.

A minimal proof of the requested fact is:

```lean
theorem contDiff_four_const_mul_rpow_of_pos
    {ν γ : ℝ} {u : ℝ → ℝ}
    (hu : ContDiff ℝ 4 u)
    (hpos : ∀ x, 0 < u x) :
    ContDiff ℝ 4 (fun x => ν * u x ^ γ) := by
  have hpow : ContDiff ℝ 4 (fun x => u x ^ γ) :=
    hu.rpow_const_of_ne (p := γ) (fun x => ne_of_gt (hpos x))
  exact contDiff_const.mul hpow
```

For the project parameters this specializes to:

```lean
have hsrcC4 : ContDiff ℝ 4 (fun x => p.ν * u x ^ p.γ) := by
  have hpow : ContDiff ℝ 4 (fun x => u x ^ p.γ) :=
    hu.rpow_const_of_ne (p := p.γ) (fun x => ne_of_gt (hpos x))
  exact contDiff_const.mul hpow
```

The required Mathlib import is usually already present indirectly in this repo, but the direct import is:

```lean
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
```

## 1. Existing repo chain-rule examples for `rpow` composition

### C² global helper in `IntervalCkComposition.lean`

File:

```text
ShenWork/Paper2/IntervalCkComposition.lean
```

Relevant theorem:

```lean
theorem contDiff_two_rpow_of_pos {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) {c : ℝ}
    (hc : 0 < c) (hupos : ∀ x, c ≤ u x) (m : ℝ) :
    ContDiff ℝ 2 (fun x => (u x) ^ m) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hupt : u x ≠ 0 := by have := hupos x; linarith
  exact (Real.contDiffAt_rpow_const_of_ne (p := m) hupt).comp x hu.contDiffAt
```

This is the closest existing repo theorem to the desired statement, but it is only `C²`, and it assumes a uniform lower bound `c ≤ u x` instead of just pointwise positivity.

The same file also has:

```lean
theorem contDiff_two_one_add_rpow_neg {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v)
    (hvnn : ∀ x, 0 ≤ v x) (β : ℝ) :
    ContDiff ℝ 2 (fun x => (1 + v x) ^ (-β)) := by
  have hbase : ContDiff ℝ 2 (fun x => 1 + v x) := contDiff_const.add hv
  rw [contDiff_iff_contDiffAt]
  intro x
  have hbasept : (1 + v x) ≠ 0 := by have := hvnn x; positivity
  exact (Real.contDiffAt_rpow_const_of_ne (p := -β) hbasept).comp x hbase.contDiffAt
```

### C³ flux denominator in `IntervalChemDivSpatialC2.lean`

File:

```text
ShenWork/Paper2/IntervalChemDivSpatialC2.lean
```

Relevant theorem:

```lean
theorem chemFlux_contDiff_three
    {β : ℝ} {u v : ℝ → ℝ}
    (hu : ContDiff ℝ 4 u)
    (hv : ContDiff ℝ 4 v)
    (hv_pos : ∀ x, (0 : ℝ) < 1 + v x)
    (hβnn : 0 ≤ β) :
    ContDiff ℝ 3 (chemFluxFun β u v) := by
  ...
  have hdenom : ContDiff ℝ 3 (fun y => (1 + v y) ^ β) := by
    have h1v : ContDiff ℝ 3 (fun y => 1 + v y) := contDiff_const.add hv3'
    exact h1v.rpow_const_of_ne (fun x => ne_of_gt (hv_pos x))
  exact hprod.div hdenom (fun x => hdenom_pos x)
```

This uses the exact same global `ContDiff.rpow_const_of_ne` API, but at order `3`, after degrading `v : C⁴` to `C³` because the final flux target is `C³`.

### C² flux package in `IntervalChemDivFluxJointC2Producer.lean`

File:

```text
ShenWork/PDE/IntervalChemDivFluxJointC2Producer.lean
```

Relevant snippet:

```lean
have hden : ContDiffAt ℝ 2
    (fun q : ℝ × ℝ =>
      (1 + intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
        ^ p.β)
    (s, x) :=
  hbase_fun.rpow_const_of_ne (ne_of_gt hbase)
```

Again, same lemma family, here pointwise `ContDiffAt` and order `2`.

### C¹/ODE examples in `ODEUniqueness.lean`

File:

```text
ShenWork/PDE/ODEUniqueness.lean
```

Relevant snippets:

```lean
have hpow : ContDiffOn ℝ 1 (fun u : ℝ => u ^ p.α) (Icc m M) :=
  contDiffOn_fun_id.rpow_const_of_ne fun u hu =>
    ne_of_gt (lt_of_lt_of_le hm hu.1)
```

and the same pattern for `bernoulliDecayVectorField_contDiffOn_Icc`.

This is an on-set/state-interval version, not the global `C⁴` source theorem.

### Continuity-only rpow use in `SourcePerSliceClose.lean`

File on the current indexed repo:

```text
ShenWork/Wiener/EWA/SourcePerSliceClose.lean
```

Relevant snippet:

```lean
have hpow : ContinuousOn
    (Function.uncurry (fun (s : ℝ) (x : ℝ) =>
      (intervalDomainLift (realSlice u_star s) x) ^ (p.γ - 1)))
    (Icc a b ×ˢ Icc (0 : ℝ) 1) := by
  refine ContinuousOn.rpow_const hVal ?_
  ...
```

This is only `ContinuousOn`, not `ContDiff`, but it is another example of the positivity/rpow idiom.

## 2. Exact Mathlib lemma and order preservation

The repo’s `lake-manifest.json` on `chatgpt-scratch` pins Mathlib:

```text
mathlib rev: 5e932f97dd25535344f80f9dd8da3aab83df0fe6
inputRev: v4.29.1
```

At that pinned Mathlib rev, in:

```text
Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean
```

there is the scalar outer-map lemma:

```lean
theorem Real.contDiffAt_rpow_const_of_ne {x p : ℝ} {n : WithTop ℕ∞} (h : x ≠ 0) :
    ContDiffAt ℝ n (fun x => x ^ p) x :=
  (contDiffAt_rpow_of_ne (x, p) h).comp x (contDiffAt_id.prodMk contDiffAt_const)
```

and the composed-function lemmas:

```lean
theorem ContDiffAt.rpow_const_of_ne (hf : ContDiffAt ℝ n f x) (h : f x ≠ 0) :
    ContDiffAt ℝ n (fun x => f x ^ p) x :=
  hf.rpow contDiffAt_const h
```

```lean
theorem ContDiffOn.rpow_const_of_ne (hf : ContDiffOn ℝ n f s) (h : ∀ x ∈ s, f x ≠ 0) :
    ContDiffOn ℝ n (fun x => f x ^ p) s :=
  fun x hx => (hf x hx).rpow_const_of_ne (h x hx)
```

```lean
theorem ContDiff.rpow_const_of_ne (hf : ContDiff ℝ n f) (h : ∀ x, f x ≠ 0) :
    ContDiff ℝ n fun x => f x ^ p :=
  hf.rpow contDiff_const h
```

The important point is that in all these `of_ne` lemmas:

```lean
{n : WithTop ℕ∞}
```

is arbitrary and the conclusion has the same `n`. Therefore the lemma preserves any finite order, including `4`, and also works for `⊤` if the input has `ContDiff ℝ ⊤`.

There is also a different family:

```lean
ContDiff.rpow_const_of_le
```

with `{m : ℕ}` and hypothesis `↑m ≤ p`. That one is for the base possibly hitting zero. It is not needed here because the hypothesis is `u x > 0`, hence `u x ≠ 0` everywhere.

## 3. Existing theorem for `C⁴` of `ν*u^γ` from `u : C⁴` + positivity?

I did **not** find a completed theorem in the repo whose conclusion is exactly or essentially:

```lean
ContDiff ℝ 4 (fun x => ν * u x ^ γ)
```

from

```lean
hu : ContDiff ℝ 4 u
hpos : ∀ x, 0 < u x
```

The repo has lower-order/general analogues (`contDiff_two_rpow_of_pos`) and related flux lemmas (`chemFlux_contDiff_three`) but not the exact C⁴ source-power theorem.

There is, however, a comment marking this exact fact as an intended/blocking subgoal in:

```text
ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean
```

Inside the resolver-C⁴ `sorry` block it says:

```text
Source C⁴: ν*u^γ is C⁴ on [0,1] by chain rule (u C⁴ + u > 0).
```

and lists as a blocking sub-goal:

```text
(a) C⁴ chain rule for x ↦ ν*u(x)^γ from ContDiff ℝ 4 u + u > 0
```

So the exact theorem appears to be **missing**, but it should be a very small wrapper around Mathlib’s `ContDiff.rpow_const_of_ne`, as shown above.

## 4. Recommended reusable theorem to add

For a global real function:

```lean
theorem contDiff_four_const_mul_rpow_of_pos
    {ν γ : ℝ} {u : ℝ → ℝ}
    (hu : ContDiff ℝ 4 u)
    (hpos : ∀ x, 0 < u x) :
    ContDiff ℝ 4 (fun x => ν * u x ^ γ) := by
  have hpow : ContDiff ℝ 4 (fun x => u x ^ γ) :=
    hu.rpow_const_of_ne (p := γ) (fun x => ne_of_gt (hpos x))
  exact contDiff_const.mul hpow
```

For the chemotaxis source coefficient shape:

```lean
theorem contDiff_four_nu_mul_gamma_source_of_pos
    (p : CM2Params) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 4 u)
    (hpos : ∀ x, 0 < u x) :
    ContDiff ℝ 4 (fun x => p.ν * u x ^ p.γ) := by
  have hpow : ContDiff ℝ 4 (fun x => u x ^ p.γ) :=
    hu.rpow_const_of_ne (p := p.γ) (fun x => ne_of_gt (hpos x))
  exact contDiff_const.mul hpow
```

If the goal is on a set instead of globally, use the on-set version:

```lean
have hpow : ContDiffOn ℝ 4 (fun x => u x ^ γ) s :=
  hu.rpow_const_of_ne (p := γ) (fun x hx => ne_of_gt (hpos x hx))
exact contDiffOn_const.mul hpow
```

where:

```lean
hu   : ContDiffOn ℝ 4 u s
hpos : ∀ x ∈ s, 0 < u x
```

## Search terms checked

I searched for:

```text
ContDiff.rpow
rpow_const_of_ne
contDiff_rpow
Real.rpow
Real.contDiffAt_rpow_const_of_ne
ContDiff ℝ 4 rpow
p.ν * ContDiff ℝ 4
ν*u^γ ContDiff
srcSlice ContDiff ℝ 4
```

Summary of hits:

* `ContDiff.rpow`: no literal repo hit.
* `rpow_const_of_ne`: many hits; the useful Lean examples are listed above.
* `contDiff_rpow`: no repo hit.
* `Real.rpow`: many broad hits, mostly unrelated or continuity/derivative uses.
* Exact `C⁴` theorem for `ν*u^γ`: not found; only the blocking-comment in `IntervalConjugateLevel0BFormSourceOn.lean` and lower-order analogues.
