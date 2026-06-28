# Q1649 (cron2): `htail` for `cutoffResolverMajorant_bddAbove_direct`

Static GitHub-connector response only. I did **not** run Lean locally, and I did **not** read `/tmp/q_cron2_htail.txt`, because that path is not a GitHub repository path and the delivery rules forbid using the local filesystem/sandbox. I inferred the target by repository search for `htail`.

## Target recovered from the repository

The live target is the remaining `htail` hole in:

```text
ShenWork/Paper2/IntervalHeatResolverJointC2.lean
```

inside:

```lean
private theorem cutoffResolverMajorant_bddAbove_direct
```

Current shape on `main`:

```lean
  -- Tail bound: for t > c/2+1, use explicit L∞ bounds
  have htail : ∃ Ctail : ℝ, ∀ q : ℝ × ℝ, c / 2 + 1 < q.1 →
      ‖iteratedFDeriv ℝ j f q‖ ≤ Ctail := by
    sorry
```

## Bottom line

There are two different answers, depending on what you want.

### 1. Tactical close, but it reuses the old physical route

If you only want to close the local `htail` goal, the following replacement should be the minimal proof:

```lean
  -- Tail bound: tactical close using the already-built physical resolver data.
  have htail : ∃ Ctail : ℝ, ∀ q : ℝ × ℝ, c / 2 + 1 < q.1 →
      ‖iteratedFDeriv ℝ j f q‖ ≤ Ctail := by
    obtain ⟨Bt, hBt⟩ :=
      ShenWork.Paper2.HeatResolverJointRegularity.heatSemigroup_level0_resolverJointC2Data
        (p := p) hu₀_bound hu₀_cont hu₀_pos
    refine ⟨cutoffResolverExplicitMajorant Bt c hc j k, ?_⟩
    intro q _hq
    simpa [hf_def] using
      (cutoffResolverTerm_iteratedFDeriv_le_explicit
        (p := p) (u := conjugatePicardIter p u₀ 0) (Bt := Bt)
        hBt hc j k q hj)
```

Minimal import/check context for the file is just the existing file import:

```lean
import ShenWork.Paper2.IntervalHeatResolverJointC2

open Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)

noncomputable section

namespace ShenWork.Paper2.HeatResolverJointC2Direct

#check cutoffResolverTerm_iteratedFDeriv_le_explicit
#check cutoffResolverExplicitMajorant
#check ShenWork.Paper2.HeatResolverJointRegularity.heatSemigroup_level0_resolverJointC2Data

end ShenWork.Paper2.HeatResolverJointC2Direct
```

Why this works: `cutoffResolverTerm_iteratedFDeriv_le_explicit` already bounds the full cutoff resolver term for every `q`; it does not need the tail hypothesis. So the proof ignores `_hq`.

But this is **not** a direct proof in the intended sense. It calls:

```lean
ShenWork.Paper2.HeatResolverJointRegularity.heatSemigroup_level0_resolverJointC2Data
```

which is exactly the old physical resolver-data producer. If you put this into `cutoffResolverMajorant_bddAbove_direct`, the theorem name/comment “bypasses `PhysicalResolverJointC2Data`” becomes misleading.

### 2. Honest direct close: add a tail coefficient-bound lemma

The direct proof cannot be obtained from `hAC2`/continuity alone. A continuous derivative on the noncompact half-line

```text
{t | c / 2 + 1 < t}
```

need not be bounded. The existing `hmid` works because it restricts `t` to the compact interval `[c/2, c/2+1]`; the `htail` region is noncompact, so compactness is unavailable.

For the direct route, the missing lemma should be about the time coefficient:

```lean
private theorem cutoffResolverCoeff_tail_bound_level0
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (hc : 0 < c)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    (k : ℕ) :
    ∀ i : ℕ, i ≤ 2 → ∃ C : ℝ,
      ∀ t : ℝ, c / 2 + 1 < t →
        ‖iteratedFDeriv ℝ i
          (fun t : ℝ =>
            smoothRightCutoff (c / 2) c t *
              resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t) t‖ ≤ C := by
  -- Analytic content: heat-level-0 positive-tail bounds for the resolver coefficient
  -- and its first two time derivatives, plus global boundedness of the cutoff and
  -- its derivatives.
  -- This is NOT implied by `ContDiff` alone.
  sorry
```

Then `htail` becomes the same Leibniz/projection/cosine-bound wiring already used in `hmid`:

```lean
  have htail : ∃ Ctail : ℝ, ∀ q : ℝ × ℝ, c / 2 + 1 < q.1 →
      ‖iteratedFDeriv ℝ j f q‖ ≤ Ctail := by
    have hcos : ContDiff ℝ (2 : ℕ∞) (cosineMode k) := by
      unfold cosineMode
      fun_prop
    have hjNat : j ≤ 2 := by exact_mod_cast hj
    have hAfst : ContDiff ℝ (2 : ℕ∞) (fun q : ℝ × ℝ => A q.1) :=
      hAC2.comp contDiff_fst
    have hBsnd : ContDiff ℝ (2 : ℕ∞) (fun q : ℝ × ℝ => cosineMode k q.2) :=
      hcos.comp contDiff_snd
    have hjTop : ((j : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
      exact_mod_cast hj
    have hfactor : f = fun q : ℝ × ℝ => A q.1 * cosineMode k q.2 := by
      funext q
      simp [hf_def, cutoffResolverTerm, A, mul_assoc]

    have hA_tail := cutoffResolverCoeff_tail_bound_level0
      (p := p) (u₀ := u₀) (M₀ := M₀) (c := c)
      hc hu₀_bound hu₀_cont hu₀_pos hfloor k

    choose C hC using hA_tail
    set Ctail := ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * C i (by
        have hik_or : i ≤ 2 := by
          -- only used for `i ∈ range (j+1)` below; in a polished proof avoid this
          -- dependent placeholder by defining a nondependent `Cmax` as in `hmid`.
          omega
        exact hik_or) *
        ShenWork.IntervalResolverSpectralJointC2Concrete.valueCosWeight (j - i) k

    -- Cleaner implementation advice: avoid the dependent `C i hi` in `Ctail`.
    -- Instead extract C0/C1/C2 from `hA_tail`, define `Cmax := max C0 (max C1 C2)`,
    -- and copy the existing `hmid` proof with `hC_max i hiNat q.1 ...` replaced by
    -- the tail bound `hC_max i hiNat q.1 hq_tail`.
    sorry
```

The important point is that the new analytic lemma must bound the coefficient factor on the noncompact positive tail. Once you have that, the rest is mechanical and should literally mirror the landed `hmid` proof.

## Beware: `c / 2 + 1` is not necessarily past the cutoff transition

Do **not** prove `htail` by saying “on the tail the cutoff is already 1.” That is false for arbitrary `c > 0`.

```text
c / 2 + 1 > c    iff    c < 2
```

For example, if `c = 4`, then `c / 2 + 1 = 3 < 4 = c`, so the region

```text
3 < t
```

still includes the transition zone `3 < t < 4`. Therefore a correct proof must either:

1. use global bounds for the cutoff derivatives, as `cutoffResolverTerm_iteratedFDeriv_le_explicit` already does; or
2. refactor the split so the tail begins at `R := max c (c / 2 + 1)`, with a mid interval `[c/2, R]`.

The current helper `bddAbove_range_of_left_mid_tail` is hardwired to split at `a` and `a + 1`. That is fine for a generic topological split, but it is not enough to justify “cutoff is constant on tail.”

## Existing repository facts that explain the tactical close

The old physical lane already has the exact machinery:

```lean
cutoffResolverTerm_iteratedFDeriv_le_explicit
```

It proves the bound for the full cutoff term using a global cutoff derivative bound and `boundedWeightJointMajorant`.

The underlying resolver coefficient facts are packaged as:

```lean
PhysicalSourceTimeC2.src_contDiff
PhysicalSourceTimeC2.src_bound
PhysicalSourceTimeC2.value_summable
PhysicalSourceTimeC2.grad_summable
```

and transferred to resolver coefficients by:

```lean
resolverTimeCoeff_eq_weight_smul
resolverTimeCoeff_bound
physicalResolverJointC2Data_of_floor
```

That is why the tactical close above works. It imports all tail control through `heatSemigroup_level0_resolverJointC2Data`.

## Recommendation

If the immediate goal is green build, use the tactical close above and rename/comment the theorem honestly, because it is no longer a direct bypass.

If the goal is genuinely to remove the old physical route from `cutoffResolverMajorant_nonneg` and `cutoffResolverTerm_iteratedFDeriv_bound`, do **not** fill `htail` by calling `heatSemigroup_level0_resolverJointC2Data`. Instead, add the heat-level-0 positive-tail coefficient-bound lemma, then copy the landed `hmid` Leibniz proof over the tail region.

## One-line verdict

`htail` is easy with `PhysicalResolverJointC2Data`; it is not closeable from `ContDiff`/compactness alone. The honest direct proof needs a new uniform positive-tail bound for the cutoff resolver coefficient and its first two time derivatives.
