# Q1651 (cron1) -- global bound gap in `cutoffResolverMajorant_bddAbove_direct`

Repository: `xiangyazi24/Shen_work`  
Committed branch: `chatgpt-scratch`  
Target report file: `scratch/_CHATGPT_DROP_cron1.md`

## Scope and caveat

The prompt was:

```text
Q1651 (cron1): cron1 /tmp/q_cron1_global.txt
```

The local file `/tmp/q_cron1_global.txt` is not accessible through the GitHub connector. I therefore inferred the target from the current cron1 boundedness thread. The relevant file is:

```text
ShenWork/Paper2/IntervalHeatResolverJointC2.lean
```

The current default-branch file has now filled the earlier `hmid` block, but the **global** remaining gap is in the `htail` block inside:

```lean
private theorem cutoffResolverMajorant_bddAbove_direct
```

specifically this local subgoal:

```lean
have hA_global_bounds : ∀ i : ℕ, i ≤ 2 →
    ∃ B_i : ℝ, ∀ t : ℝ, ‖iteratedFDeriv ℝ i A t‖ ≤ B_i := by
  ...
  sorry
```

I used the GitHub connector only. I did **not** use Python, the sandbox, `/mnt/data`, or a sandbox download link. I did not run Lean locally.

## Short answer

Do **not** try to prove `hA_global_bounds` from `hAC2`/continuity alone. That is false in general: a `C²` function on `ℝ` can be unbounded. The comments in the file say “`A(t) → L`, `A'(t) → 0`, `A''(t) → 0`”, but those are not available as local hypotheses or committed lemmas in this proof.

The cleanest way to close the global `BddAbove` obstruction is to bypass the direct left/mid/tail proof and use the already-proved physical-data route:

```lean
cutoffResolverMajorant_bddAbove_of_physical
```

That theorem already proves the required global `BddAbove` from `PhysicalResolverJointC2Data`, via the explicit uniform majorant:

```lean
cutoffResolverTerm_iteratedFDeriv_le_explicit
```

The file already imports the producer:

```lean
ShenWork.Paper2.HeatResolverJointRegularity.heatSemigroup_level0_resolverJointC2Data
```

through `IntervalHeatSemigroupHighRegularity`, so the global bound can be obtained by extracting `Bt, hBt` and applying `cutoffResolverMajorant_bddAbove_of_physical`.

## Recommended patch: replace the direct theorem body

The most robust patch is to replace the entire body of `cutoffResolverMajorant_bddAbove_direct` with a call to the physical route. This closes both `hmid` and `htail` at once and avoids inventing uncommitted tail-limit lemmas.

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
  obtain ⟨Bt, hBt⟩ :=
    ShenWork.Paper2.HeatResolverJointRegularity.heatSemigroup_level0_resolverJointC2Data
      (p := p) (u₀ := u₀) (M₀ := M₀)
      hu₀_bound hu₀_cont hu₀_pos
  exact cutoffResolverMajorant_bddAbove_of_physical
    (p := p) (u₀ := u₀) (M₀ := M₀) hc hBt j k hj
```

This is not mathematically weaker than the intended direct proof. It uses exactly the data that the global tail proof would need: uniform bounds for the resolver coefficient time derivatives. The only difference is that the bounds are supplied by the existing `PhysicalResolverJointC2Data` package instead of being reconstructed ad hoc inside the tail block.

## Why the current `hA_global_bounds` plan is not justified

The current local context has:

```lean
set A := fun t : ℝ =>
  smoothRightCutoff (c / 2) c t *
    resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t
have hAC2 := cutoffResolverCoeff_contDiff_two hu₀_bound hu₀_cont hfloor hc k
```

From this, Lean can prove:

```lean
Continuous (fun t => iteratedFDeriv ℝ i A t)
```

for `i ≤ 2`, but it cannot prove:

```lean
∃ B_i, ∀ t, ‖iteratedFDeriv ℝ i A t‖ ≤ B_i
```

because continuity on a noncompact domain is insufficient. The middle proof works because it restricts `t` to the compact interval:

```lean
Set.Icc (c / 2) (c / 2 + 1)
```

The global tail proof has no such compact interval.

The comments in the file propose using decay/finite-limit facts:

```text
A(t) → L, A'(t) → 0, A''(t) → 0 as t → ∞.
```

That route would be analytically legitimate, but only if those asymptotic lemmas are already available for `resolverTimeCoeff` and its first two time derivatives. I did not find such local hypotheses in the proof. Without them, this route is a dead end.

## If you insist on filling only `hA_global_bounds`

A more local proof can be written, but it should still use `PhysicalResolverJointC2Data`. The idea is:

1. extract `Bt, H` from `heatSemigroup_level0_resolverJointC2Data`;
2. use the one-dimensional product Leibniz bound for
   ```lean
   A = smoothRightCutoff (c / 2) c * resolverTimeCoeff ... k
   ```
3. bound cutoff derivatives by `resolverSmoothRightCutoffDerivBound_spec`;
4. bound resolver coefficient derivatives by `H.coeff_bound`.

The replacement for the `hA_global_bounds` sorry has this shape:

```lean
      obtain ⟨Bt, H⟩ :=
        ShenWork.Paper2.HeatResolverJointRegularity.heatSemigroup_level0_resolverJointC2Data
          (p := p) (u₀ := u₀) (M₀ := M₀)
          hu₀_bound hu₀_cont hu₀_pos
      intro i hi
      have hiTop : ((i : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
        exact_mod_cast hi
      have hiNat : i ≤ 2 := hi
      have hc'c : c / 2 < c := by linarith
      let Φ : ℕ → ℝ := fun r =>
        if hr : (r : ℕ∞) ≤ 2 then
          resolverSmoothRightCutoffDerivBound (c / 2) c hc'c r hr
        else 0
      refine ⟨∑ r ∈ Finset.range (i + 1),
          (i.choose r : ℝ) * Φ r * Bt (i - r) k, ?_⟩
      intro t
      have hφ : ContDiff ℝ (2 : ℕ∞) (smoothRightCutoff (c / 2) c) :=
        smoothRightCutoff_contDiff
      have hR : ContDiff ℝ (2 : ℕ∞)
          (resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k) :=
        H.coeff_contDiff k
      have hprod := norm_iteratedFDeriv_mul_le hφ hR t hiTop
      change ‖iteratedFDeriv ℝ i
          (fun t : ℝ => smoothRightCutoff (c / 2) c t *
            resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t) t‖ ≤ _
      calc
        ‖iteratedFDeriv ℝ i
            (fun t : ℝ => smoothRightCutoff (c / 2) c t *
              resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t) t‖
            ≤ ∑ r ∈ Finset.range (i + 1), (i.choose r : ℝ) *
                ‖iteratedFDeriv ℝ r (smoothRightCutoff (c / 2) c) t‖ *
                ‖iteratedFDeriv ℝ (i - r)
                  (resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k) t‖ := by
              simpa [mul_assoc] using hprod
        _ ≤ ∑ r ∈ Finset.range (i + 1),
              (i.choose r : ℝ) * Φ r * Bt (i - r) k := by
              apply Finset.sum_le_sum
              intro r hrange
              have hri : r ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hrange)
              have hrNat : r ≤ 2 := le_trans hri hiNat
              have hirNat : i - r ≤ 2 := le_trans (Nat.sub_le i r) hiNat
              have hrTop : (r : ℕ∞) ≤ (2 : ℕ∞) := by exact_mod_cast hrNat
              have hcut : ‖iteratedFDeriv ℝ r (smoothRightCutoff (c / 2) c) t‖ ≤ Φ r := by
                simp [Φ, hrTop, resolverSmoothRightCutoffDerivBound_spec hc'c hrTop t]
              have hres : ‖iteratedFDeriv ℝ (i - r)
                    (resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k) t‖ ≤
                    Bt (i - r) k :=
                H.coeff_bound (i - r) k t hirNat
              have hchoose_nn : 0 ≤ (i.choose r : ℝ) := Nat.cast_nonneg _
              have hcut_nn : 0 ≤ Φ r := by
                have hn := norm_nonneg (iteratedFDeriv ℝ r (smoothRightCutoff (c / 2) c) t)
                exact le_trans hn hcut
              exact mul_le_mul
                (mul_le_mul_of_nonneg_left hcut hchoose_nn)
                hres
                (norm_nonneg _)
                (mul_nonneg hchoose_nn hcut_nn)
```

This is the direct proof that the current comments are gesturing toward, but notice that it still depends on `PhysicalResolverJointC2Data`; it does **not** follow from continuity or asymptotic handwaving.

The first patch, replacing the whole `cutoffResolverMajorant_bddAbove_direct` body, is much less brittle and should be preferred.

## Why this is not circular

The physical route is already used later in the same file for summability:

```lean
obtain ⟨Bt, hBt⟩ :=
  ShenWork.Paper2.HeatResolverJointRegularity.heatSemigroup_level0_resolverJointC2Data
    (p := p) hu₀_bound hu₀_cont hu₀_pos
```

and then:

```lean
cutoffResolverExplicitMajorant_summable hBt hc _hj
cutoffResolverMajorant_le_explicit hc hBt j k _hj
```

So using `hBt` to prove `BddAbove` is consistent with the file’s own architecture. It is not introducing a new dependency; it is reusing the same committed coefficient-bound package already used for the summable majorant.

## Bottom line

The global gap should be closed by the existing explicit-majorant/physical-data route, not by a new tail compactness or unproved finite-limit argument.

Recommended final shape:

```text
cutoffResolverMajorant_bddAbove_direct
  := obtain PhysicalResolverJointC2Data;
     exact cutoffResolverMajorant_bddAbove_of_physical ...
```

This removes the fragile `hA_global_bounds` proof obligation entirely and gives the required global `BddAbove` immediately.
