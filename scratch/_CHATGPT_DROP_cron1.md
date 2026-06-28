# Q1589 (cron1) -- replacing `PhysicalResolverJointC2Data` in the cutoff resolver majorant `BddAbove` proof

Repository: `xiangyazi24/Shen_work`  
Branch committed: `chatgpt-scratch`  
Target file: `scratch/_CHATGPT_DROP_cron1.md`

## Method / caveat

Connector-only inspection.  I did not run Lean locally and did not use Python/sandbox.

I inspected the relevant Shen_work files and Mathlib APIs through the GitHub connector.  The answer below is a concrete Lean route, but the longer analytic tail-bound lemmas are presented as implementation skeletons because they require the already-known heat/resolver decay estimates to be wired in.

## Short answer

Yes, Mathlib has exactly the compact-support boundedness lemma:

```lean
Continuous.bounded_above_of_compact_support
```

Shape:

```lean
lemma Continuous.bounded_above_of_compact_support
    (hf : Continuous f) (h : HasCompactSupport f) :
    ∃ C, ∀ x, ‖f x‖ ≤ C
```

It lives in:

```text
Mathlib/Analysis/Normed/Group/Bounded.lean
```

There is also the compact-set version:

```lean
IsCompact.exists_bound_of_continuousOn'
```

Shape:

```lean
lemma IsCompact.exists_bound_of_continuousOn'
    (hs : IsCompact s) (hf : ContinuousOn f s) :
    ∃ C, ∀ x ∈ s, ‖f x‖ ≤ C
```

The repo already uses `Continuous.bounded_above_of_compact_support` successfully in the cutoff derivative helper:

```lean
rcases hcont.bounded_above_of_compact_support hcomp with ⟨C, hC⟩
```

inside `resolverSmoothRightCutoff_iteratedFDeriv_bound_exists` in

```text
ShenWork/Paper2/IntervalHeatResolverJointC2.lean
```

So the Mathlib API is not the blocker.

## Important correction

Do **not** try to prove

```lean
HasCompactSupport (fun q : ℝ × ℝ =>
  iteratedFDeriv ℝ j
    (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q)
```

for the full resolver cutoff term.  That statement is generally false.

The term is

```lean
cutoffResolverTerm p u c k q =
  smoothRightCutoff (c / 2) c q.1 *
    (resolverTimeCoeff p u k q.1 * cosineMode k q.2)
```

The cutoff only kills the **left** tail `t < c/2`.  For `t ≥ c`, the cutoff is `1`, not `0`.  Also `q.2 : ℝ` is unrestricted, so even a compact interval in `t` gives `[c/2,T] × ℝ`, not a compact subset of `ℝ × ℝ`.

For the actual resolver, the correct target is therefore not “compact support of the full derivative”, but:

1. continuity of the iterated derivative;
2. zero / local-zero on the left side `t < c/2`;
3. boundedness on the middle slab `c/2 ≤ t ≤ T`, using product structure and cosine derivative bounds;
4. a uniform right-tail bound for `t ≥ T`.

Also: “decays to zero as `t → ∞`” is too strong in the zeroth mode.  For `k = 0`, `j = 0`, the Neumann heat flow tends to its spatial average, so the source/resolver zeroth mode can converge to a nonzero constant.  What the `BddAbove` proof needs is only a **tail bound** or finite limit, not decay to zero.

## Current hot spot

In `ShenWork/Paper2/IntervalHeatResolverJointC2.lean`, the current lemma is:

```lean
private theorem cutoffResolverMajorant_bddAbove_of_physical
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (hc : 0 < c) {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p (conjugatePicardIter p u₀ 0) Bt)
    (j k : ℕ) (hj : (j : ℕ∞) ≤ 2) :
    BddAbove (Set.range fun q : ℝ × ℝ =>
      ‖iteratedFDeriv ℝ j
        (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q‖) := by
  refine ⟨cutoffResolverExplicitMajorant Bt c hc j k, ?_⟩
  rintro _ ⟨q, rfl⟩
  exact cutoffResolverTerm_iteratedFDeriv_le_explicit H hc j k q hj
```

This uses `PhysicalResolverJointC2Data` only to get a global bound.  That is overkill for the `BddAbove` part.

## Minimal compact-support version, if you really have compact support

This is the clean Mathlib pattern.  It is useful as a local helper, but again the `hcomp` assumption is false for the full resolver term unless you change the object.

```lean
private theorem cutoffResolverMajorant_bddAbove_of_compactSupport
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (hc : 0 < c)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    (j k : ℕ) (hj : (j : ℕ∞) ≤ 2)
    (hcomp : HasCompactSupport (fun q : ℝ × ℝ =>
      iteratedFDeriv ℝ j
        (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q)) :
    BddAbove (Set.range fun q : ℝ × ℝ =>
      ‖iteratedFDeriv ℝ j
        (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q‖) := by
  have hcd : ContDiff ℝ 2
      (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) :=
    cutoffResolverTerm_contDiff_two hu₀_bound hu₀_cont hfloor hc k
  have hcont : Continuous (fun q : ℝ × ℝ =>
      iteratedFDeriv ℝ j
        (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q) :=
    hcd.continuous_iteratedFDeriv (by exact_mod_cast hj)
  rcases hcont.bounded_above_of_compact_support hcomp with ⟨C, hC⟩
  exact ⟨C, by
    rintro _ ⟨q, rfl⟩
    exact hC q⟩
```

This is the exact answer to “can `BddAbove` be proved from `ContDiff` + compact support?”: yes.

But this is not the right lemma for `cutoffResolverTerm` over all `ℝ × ℝ`.

## Correct generic helper for the actual situation

Use a left/middle/right decomposition.  This avoids `PhysicalResolverJointC2Data` and avoids pretending the full derivative has compact support.

```lean
private theorem bddAbove_range_norm_of_left_mid_tail
    {E : Type*} [SeminormedAddCommGroup E]
    {F : ℝ × ℝ → E} {a T Cmid Ctail : ℝ}
    (hleft : ∀ q : ℝ × ℝ, q.1 < a → ‖F q‖ = 0)
    (hmid : ∀ q : ℝ × ℝ, a ≤ q.1 → q.1 ≤ T → ‖F q‖ ≤ Cmid)
    (htail : ∀ q : ℝ × ℝ, T < q.1 → ‖F q‖ ≤ Ctail) :
    BddAbove (Set.range fun q : ℝ × ℝ => ‖F q‖) := by
  refine ⟨max 0 (max Cmid Ctail), ?_⟩
  rintro _ ⟨q, rfl⟩
  by_cases hqa : q.1 < a
  · rw [hleft q hqa]
    exact le_max_left 0 (max Cmid Ctail)
  · have hqa' : a ≤ q.1 := le_of_not_gt hqa
    by_cases hqT : q.1 ≤ T
    · exact (hmid q hqa' hqT).trans
        ((le_max_left Cmid Ctail).trans (le_max_right 0 (max Cmid Ctail)))
    · have hqT' : T < q.1 := lt_of_not_ge hqT
      exact (htail q hqT').trans
        ((le_max_right Cmid Ctail).trans (le_max_right 0 (max Cmid Ctail)))
```

Now instantiate it with

```lean
F := fun q : ℝ × ℝ =>
  iteratedFDeriv ℝ j
    (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q
```

and `a := c / 2`.

## Direct replacement lemma shape

The replacement for `cutoffResolverMajorant_bddAbove_of_physical` should look like this:

```lean
private theorem cutoffResolverMajorant_bddAbove_direct
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (hc : 0 < c)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    (j k : ℕ) (hj : (j : ℕ∞) ≤ 2)
    -- direct analytic boundedness data, no PhysicalResolverJointC2Data
    (T Cmid Ctail : ℝ)
    (hleft : ∀ q : ℝ × ℝ, q.1 < c / 2 →
      ‖iteratedFDeriv ℝ j
        (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q‖ = 0)
    (hmid : ∀ q : ℝ × ℝ, c / 2 ≤ q.1 → q.1 ≤ T →
      ‖iteratedFDeriv ℝ j
        (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q‖ ≤ Cmid)
    (htail : ∀ q : ℝ × ℝ, T < q.1 →
      ‖iteratedFDeriv ℝ j
        (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q‖ ≤ Ctail) :
    BddAbove (Set.range fun q : ℝ × ℝ =>
      ‖iteratedFDeriv ℝ j
        (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q‖) := by
  exact bddAbove_range_norm_of_left_mid_tail
    (F := fun q : ℝ × ℝ =>
      iteratedFDeriv ℝ j
        (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q)
    (a := c / 2) (T := T) (Cmid := Cmid) (Ctail := Ctail)
    hleft hmid htail
```

This is intentionally split so the topological/order part is completely mechanical, while the analytic facts are explicit and local.

## How to prove the three inputs

### 1. `hleft`: cutoff is locally zero for `q.1 < c/2`

This is the same pattern used in the heat file.  For strict left side, use eventual equality to zero, then transfer through `iteratedFDeriv`.

```lean
private theorem cutoffResolverTerm_iteratedFDeriv_left_zero
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {c : ℝ}
    (hc : 0 < c) (j k : ℕ) (q : ℝ × ℝ)
    (hq : q.1 < c / 2) :
    ‖iteratedFDeriv ℝ j
      (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q‖ = 0 := by
  have hc'c : c / 2 < c := by linarith
  have hev : cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k =ᶠ[𝓝 q]
      fun _ : ℝ × ℝ => (0 : ℝ) := by
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds
      (Iio_mem_nhds hq)] with q' hq'
    simp only [Set.mem_preimage, Set.mem_Iio] at hq'
    simp [cutoffResolverTerm,
      smoothRightCutoff_eq_zero_of_le hc'c (le_of_lt hq')]
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · rw [norm_iteratedFDeriv_zero, hev.eq_of_nhds, norm_zero]
  · have hev' := Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev j
    have hz := hev'.eq_of_nhds
    rw [iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.mp hjpos), Pi.zero_apply] at hz
    rw [hz, norm_zero]
```

This avoids any resolver data.

### 2. `hmid`: bounded on `c/2 ≤ t ≤ T`

Do **not** try to compactify `[c/2,T] × ℝ`.  Instead use product structure:

```lean
cutoffResolverTerm = (A ∘ Prod.fst) * (cosineMode k ∘ Prod.snd)
```

where

```lean
A t := smoothRightCutoff (c / 2) c t *
       resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t
```

Then:

* `cutoffResolverCoeff_contDiff_two` gives `ContDiff ℝ 2 A` directly, without `PhysicalResolverJointC2Data`.
* For each `i ≤ j ≤ 2`, `hA.continuous_iteratedFDeriv` gives continuity of `D^i A`.
* `IsCompact.exists_bound_of_continuousOn' isCompact_Icc ...` bounds `D^i A` on `[c/2,T]`.
* cosine derivatives are globally bounded in `x`; use the existing cosine-mode derivative bound, e.g. `unitIntervalCosineMode_iteratedFDeriv_bound` / the corresponding `cosineMode` wrapper.
* combine the finite Leibniz sum with `norm_iteratedFDeriv_mul_le`, `norm_iteratedFDeriv_comp_fst_le`, and `norm_iteratedFDeriv_comp_snd_le`.

Skeleton:

```lean
private theorem cutoffResolverTerm_iteratedFDeriv_mid_bounded
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c T : ℝ}
    (hc : 0 < c)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    (j k : ℕ) (hj : (j : ℕ∞) ≤ 2) :
    ∃ Cmid : ℝ, ∀ q : ℝ × ℝ, c / 2 ≤ q.1 → q.1 ≤ T →
      ‖iteratedFDeriv ℝ j
        (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q‖ ≤ Cmid := by
  classical
  let A : ℝ → ℝ := fun t =>
    smoothRightCutoff (c / 2) c t *
      resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t
  have hA : ContDiff ℝ 2 A :=
    cutoffResolverCoeff_contDiff_two hu₀_bound hu₀_cont hfloor hc k

  -- For every time derivative order appearing in Leibniz, get a compact bound on `[c/2,T]`.
  -- Use:
  --   (hA.continuous_iteratedFDeriv ...).continuousOn
  --   isCompact_Icc.exists_bound_of_continuousOn'
  -- Then combine with cosine derivative bounds and `norm_iteratedFDeriv_mul_le`.
  -- This is mechanical but a bit long, so keep it as a separate helper.
  sorry
```

The key point: `hmid` needs only the already sorry-free `cutoffResolverCoeff_contDiff_two` / `cutoffResolverTerm_contDiff_two`, plus compactness of the **time interval**, not `PhysicalResolverJointC2Data`.

### 3. `htail`: right-tail boundedness

Use a bounded-tail statement, not necessarily decay-to-zero:

```lean
private theorem cutoffResolverTerm_iteratedFDeriv_tail_bounded
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (hc : 0 < c)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    (j k : ℕ) (hj : (j : ℕ∞) ≤ 2) :
    ∃ T Ctail : ℝ, ∀ q : ℝ × ℝ, T < q.1 →
      ‖iteratedFDeriv ℝ j
        (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q‖ ≤ Ctail := by
  -- For q.1 > c, cutoff is locally 1 and cutoff derivatives are locally 0.
  -- So the tail is controlled by the resolver coefficient derivatives alone.
  -- For the heat base iterate, these are bounded because the heat semigroup coefficients
  -- have exponential damping for nonzero modes and a finite constant-mode limit.
  -- Combine with the global cosine derivative bound.
  sorry
```

If you already have actual `Tendsto ... (𝓝 0)` for the relevant derivative/mode, then `htail` follows by taking eventual `≤ 1`.  But for `j = 0, k = 0`, use a finite-limit/bounded-tail lemma instead.

## Replacement sites in `IntervalHeatResolverJointC2.lean`

The three visible places that currently call the physical package are:

### A. `cutoffResolverMajorant_nonneg`

Current pattern:

```lean
obtain ⟨Bt, hBt⟩ :=
  ShenWork.Paper2.HeatResolverJointRegularity.heatSemigroup_level0_resolverJointC2Data
    (p := p) hu₀_bound hu₀_cont hu₀_pos
have hbdd := cutoffResolverMajorant_bddAbove_of_physical
  (p := p) (u₀ := u₀) (M₀ := M₀) hc hBt j k _hj
exact (norm_nonneg _).trans (le_ciSup hbdd (0, 0))
```

Replace with:

```lean
have hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0 : ℝ) 1,
    0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x :=
  fun t ht x hx =>
    ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_pos_of_pos
      (p := p) hu₀_cont hu₀_pos ht hx

obtain ⟨T, Ctail, htail⟩ :=
  cutoffResolverTerm_iteratedFDeriv_tail_bounded
    (p := p) (u₀ := u₀) (M₀ := M₀) hc hu₀_bound hu₀_cont hu₀_pos j k _hj
obtain ⟨Cmid, hmid⟩ :=
  cutoffResolverTerm_iteratedFDeriv_mid_bounded
    (p := p) (u₀ := u₀) (M₀ := M₀) (T := T)
    hc hu₀_bound hu₀_cont hfloor j k _hj

have hbdd := cutoffResolverMajorant_bddAbove_direct
  (p := p) (u₀ := u₀) (M₀ := M₀) hc hu₀_bound hu₀_cont hfloor j k _hj
  T Cmid Ctail
  (fun q hq => cutoffResolverTerm_iteratedFDeriv_left_zero hc j k q hq)
  hmid htail

exact (norm_nonneg _).trans (le_ciSup hbdd (0, 0))
```

No `PhysicalResolverJointC2Data` is involved.

### B. `cutoffResolverTerm_iteratedFDeriv_bound`

Same replacement: use the direct `hbdd` above, then

```lean
exact le_ciSup hbdd q
```

### C. `cutoffResolverMajorant_summable`

This is different.  `BddAbove` alone cannot prove summability in `k`.

Current proof does two things:

1. nonnegativity of `cutoffResolverMajorant ... j k`, via `le_ciSup`; this only needs `BddAbove`;
2. domination by a summable explicit majorant, via

```lean
cutoffResolverMajorant_le_explicit
cutoffResolverExplicitMajorant_summable hBt
```

The second part still depends on `PhysicalResolverJointC2Data` because `hBt.value_summable` supplies summability of the explicit resolver majorant.

So after replacing the `BddAbove` proof, `cutoffResolverMajorant_summable` still needs a **direct summable majorant**.  The model to copy is the heat semigroup proof in `cutoffHeatSeries_contDiff_two`: it defines a concrete `v k n` with exponential/eigenvalue weights and proves `Summable (v j)` directly, without a physical data package.

For the resolver version, either:

* define a direct resolver `v j k` from heat-source coefficient estimates and elliptic weight, then prove

```lean
cutoffResolverMajorant p u₀ M₀ c hc j k ≤ v j k
Summable (v j)
```

or

* avoid the `ciSup`-defined `cutoffResolverMajorant` in the `contDiff_tsum` call and pass the direct `v` exactly as the heat semigroup file does.

The second option is cleaner: it removes both the `BddAbove` nuisance and the physical package dependency from the `contDiff_tsum` majorant lane.

## Recommended implementation order

1. Add the generic helper:

```lean
bddAbove_range_norm_of_left_mid_tail
```

2. Add the strict-left zero lemma:

```lean
cutoffResolverTerm_iteratedFDeriv_left_zero
```

3. Add the middle compact-time bound:

```lean
cutoffResolverTerm_iteratedFDeriv_mid_bounded
```

Use `cutoffResolverCoeff_contDiff_two`, `IsCompact.exists_bound_of_continuousOn'`, product Leibniz, and cosine derivative bounds.

4. Add the right-tail boundedness lemma:

```lean
cutoffResolverTerm_iteratedFDeriv_tail_bounded
```

State/prove bounded tail, not necessarily decay to zero.

5. Replace `cutoffResolverMajorant_bddAbove_of_physical` calls in `cutoffResolverMajorant_nonneg` and `cutoffResolverTerm_iteratedFDeriv_bound` with `cutoffResolverMajorant_bddAbove_direct`.

6. Separately replace `cutoffResolverMajorant_summable` with a direct summable majorant.  Do not expect `BddAbove` to imply summability.

## Bottom line

* `ContDiff` alone does **not** imply `BddAbove`; `Real.exp` is the standard counterexample.
* `ContDiff` + genuine `HasCompactSupport` **does** imply a global norm bound, and Mathlib has `Continuous.bounded_above_of_compact_support`.
* For this resolver term, genuine compact support on `ℝ × ℝ` is the wrong property.
* The correct first-principles proof is left-zero + compact-time middle bound + right-tail bound, with cosine derivatives bounded globally in `x`.
* This removes the unnecessary dependency on the sorry-bearing `PhysicalResolverJointC2Data` for the `BddAbove`/`le_ciSup` lane.
* Summability still needs a separate direct explicit majorant; copy the architecture of `cutoffHeatSeries_contDiff_two` rather than reintroducing the physical package.
