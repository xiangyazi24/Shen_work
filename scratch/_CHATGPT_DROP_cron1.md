# Q1679 (cron1) -- `tail` block in `IntervalHeatResolverJointC2.lean`

Repository: `xiangyazi24/Shen_work`  
Committed branch: `chatgpt-scratch`  
Target report file: `scratch/_CHATGPT_DROP_cron1.md`

## Scope and caveat

The prompt I received was only:

```text
Q1679 (cron1): cron1 /tmp/q_cron1_tail_lean.txt
```

The local file `/tmp/q_cron1_tail_lean.txt` is not accessible through the GitHub connector. I used the connector only and inferred the target from the current `cron1` thread and the repository state. I did **not** use Python, the sandbox, `/mnt/data`, or a sandbox download link. I did not run Lean locally.

The relevant file is:

```text
ShenWork/Paper2/IntervalHeatResolverJointC2.lean
```

The relevant proof region is the `htail` branch inside:

```lean
private theorem cutoffResolverMajorant_bddAbove_direct
```

Currently the tail branch tries to prove global boundedness of the time factor

```lean
A t = smoothRightCutoff (c / 2) c t *
  resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t
```

by hand. That branch contains the `hA_tail` sorry for `i = 0` and separate sorries for `i = 1` and `i = 2`.

## Diagnosis

The current `htail` plan is the wrong place to rebuild analytic bounds.

The proof tries to show:

```lean
have hA_global_bounds : ∀ i : ℕ, i ≤ 2 →
    ∃ B_i : ℝ, ∀ t : ℝ, ‖iteratedFDeriv ℝ i A t‖ ≤ B_i := by
  intro i hi
  interval_cases i
  · -- i = 0
    ...
    have hA_tail : ∃ B_tail : ℝ, ∀ t : ℝ, c / 2 + 2 < t →
        |A t| ≤ B_tail := by
      sorry
  · -- i = 1
    sorry
  · -- i = 2
    sorry
```

For the tail, a compactness argument cannot close the proof. Compactness only gives a bound on a finite interval such as `[c/2, c/2+2]`. The tail needs a uniform bound on all `t > c/2+2`. Reproving that directly requires reopening the whole chain:

```text
L∞ contraction of S(t)u₀
→ bounded source slice ν·(S(t)u₀)^γ
→ bounded cosine coefficients
→ elliptic resolver weight
→ resolverTimeCoeff and its first two time derivatives
```

That is exactly what the physical-data package is supposed to provide. In this file, the already-proved helper

```lean
private theorem cutoffResolverTerm_iteratedFDeriv_le_explicit
```

already gives the global derivative bound for the cutoff resolver term from

```lean
PhysicalResolverJointC2Data p (conjugatePicardIter p u₀ 0) Bt
```

and the nearby helper

```lean
private theorem cutoffResolverMajorant_bddAbove_of_physical
```

turns that global bound into the required `BddAbove` statement.

So the clean fix is: do **not** finish the manual `hA_tail`/`i=1`/`i=2` tail proof. Delegate the tail, or the whole direct `BddAbove` theorem, to the physical package.

## Smallest local patch for just `htail`

If you want to keep the left/mid/tail structure, replace the current long `htail` body by a one-shot physical bound.

Insert this before or inside the `htail` proof:

```lean
    obtain ⟨Bt, Hphys⟩ :=
      ShenWork.Paper2.HeatResolverJointRegularity.heatSemigroup_level0_resolverJointC2Data
        (p := p) (u₀ := u₀) (M₀ := M₀)
        hu₀_bound hu₀_cont hu₀_pos
```

Then replace the entire current `htail` block with:

```lean
  -- Tail bound: for t > c/2+1, use the already packaged physical global bound.
  have htail : ∃ Ctail : ℝ, ∀ q : ℝ × ℝ, c / 2 + 1 < q.1 →
      ‖iteratedFDeriv ℝ j f q‖ ≤ Ctail := by
    obtain ⟨Bt, Hphys⟩ :=
      ShenWork.Paper2.HeatResolverJointRegularity.heatSemigroup_level0_resolverJointC2Data
        (p := p) (u₀ := u₀) (M₀ := M₀)
        hu₀_bound hu₀_cont hu₀_pos
    refine ⟨cutoffResolverExplicitMajorant Bt c hc j k, ?_⟩
    intro q _hq
    have hmain := cutoffResolverTerm_iteratedFDeriv_le_explicit
      (p := p) (u := conjugatePicardIter p u₀ 0) (Bt := Bt)
      Hphys hc j k q hj
    simpa [hf_def] using hmain
```

Why this works:

* `cutoffResolverTerm_iteratedFDeriv_le_explicit` is already a global bound for all `q`, so the tail hypothesis `_hq : c / 2 + 1 < q.1` is unused.
* The bound is exactly the explicit majorant already used elsewhere in this file.
* This deletes the need for `hA_global_bounds`, `hA_tail`, and the separate `i = 1`, `i = 2` manual derivative bounds inside `htail`.

If `simpa [hf_def] using hmain` does not orient the local `set f := ... with hf_def` correctly, use the more explicit version:

```lean
    change ‖iteratedFDeriv ℝ j
        (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q‖ ≤
      cutoffResolverExplicitMajorant Bt c hc j k
    exact cutoffResolverTerm_iteratedFDeriv_le_explicit
      (p := p) (u := conjugatePicardIter p u₀ 0) (Bt := Bt)
      Hphys hc j k q hj
```

## Even cleaner patch: replace the whole “direct” theorem body

The stronger simplification is to replace the body of

```lean
private theorem cutoffResolverMajorant_bddAbove_direct
```

with a direct delegation to the physical `BddAbove` theorem:

```lean
private theorem cutoffResolverMajorant_bddAbove_direct
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (hc : 0 < c)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    (_hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    (j k : ℕ) (hj : (j : ℕ∞) ≤ 2) :
    BddAbove (Set.range fun q : ℝ × ℝ =>
      ‖iteratedFDeriv ℝ j
        (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q‖) := by
  obtain ⟨Bt, Hphys⟩ :=
    ShenWork.Paper2.HeatResolverJointRegularity.heatSemigroup_level0_resolverJointC2Data
      (p := p) (u₀ := u₀) (M₀ := M₀)
      hu₀_bound hu₀_cont hu₀_pos
  exact cutoffResolverMajorant_bddAbove_of_physical
    (p := p) (u₀ := u₀) (M₀ := M₀) hc Hphys j k hj
```

This is the safest code-maintenance move because it removes all three manual tail obligations at once. The `_hfloor` argument becomes unused, but keeping it preserves the existing theorem signature and avoids downstream edits.

## If the goal is to avoid physical data entirely

Then the tail cannot be closed by merely extending the compact interval.

You would need a new lemma of this shape:

```lean
theorem cutoffResolverCoeff_global_iteratedFDeriv_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (hc : 0 < c)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    (k i : ℕ) (hi : i ≤ 2) :
    ∃ B : ℝ, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ i
        (fun t : ℝ =>
          smoothRightCutoff (c / 2) c t *
            resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t) t‖ ≤ B := by
  -- Requires the same source-time C² bounds and elliptic resolver bounds
  -- already packaged in PhysicalResolverJointC2Data.
  sorry
```

But proving that lemma from scratch just recreates `PhysicalResolverJointC2Data.coeff_bound`, then repeats the cutoff Leibniz estimate. That is strictly more work and is more fragile.

## Recommendation

Use the **whole-theorem delegation** patch unless you specifically need to preserve the pedagogical left/mid/tail proof.

For local surgery on the current failing `tail` block, use the smaller `htail` replacement. Both fixes are conceptually the same: the tail is not a compactness problem; it is a global coefficient-bound problem, and the repository already routes that through:

```lean
PhysicalResolverJointC2Data.coeff_bound
```

via:

```lean
cutoffResolverTerm_iteratedFDeriv_le_explicit
cutoffResolverMajorant_bddAbove_of_physical
```

## Minimal import/check context

The target file already imports:

```lean
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete
```

so the fully-qualified call

```lean
ShenWork.Paper2.HeatResolverJointRegularity.heatSemigroup_level0_resolverJointC2Data
```

should not require a new import in `IntervalHeatResolverJointC2.lean`.

## Bottom line

The `tail` branch should be closed by using the physical-data majorant, not by hand-proving `hA_tail`. The direct route has already reached the abstraction boundary where the correct object is:

```lean
PhysicalResolverJointC2Data p (conjugatePicardIter p u₀ 0) Bt
```

Once that is extracted, the tail proof is one call to:

```lean
cutoffResolverTerm_iteratedFDeriv_le_explicit
```

or the whole `BddAbove` theorem is one call to:

```lean
cutoffResolverMajorant_bddAbove_of_physical
```
