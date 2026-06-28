# Q1646 (cron1) -- `hmid` in `cutoffResolverMajorant_bddAbove_direct`

Repository: `xiangyazi24/Shen_work`  
Committed branch: `chatgpt-scratch`  
Target report file: `scratch/_CHATGPT_DROP_cron1.md`

## Scope and caveat

The prompt was:

```text
Q1646 (cron1): cron1 /tmp/q_cron1_hmid.txt
```

The local file `/tmp/q_cron1_hmid.txt` is not accessible through the GitHub connector. I therefore inferred the target from the current repository state and the previous cron1 `BddAbove` thread.

The relevant target is the `hmid` proof inside:

```text
ShenWork/Paper2/IntervalHeatResolverJointC2.lean
```

in the private theorem:

```lean
cutoffResolverMajorant_bddAbove_direct
```

I used the GitHub connector only. I did **not** use Python, the sandbox, `/mnt/data`, or a sandbox download link.

One branch wrinkle: as in earlier cron1 drops, the source inspection is from the repository default branch. The report itself is committed on `chatgpt-scratch`, as requested.

## Local target

The relevant local skeleton is:

```lean
/-- BddAbove of the cutoff resolver term iteratedFDeriv norm, proved directly
from the product structure A(t) · B(x) without PhysicalResolverJointC2Data.
Uses: left zero (cutoff), mid compact (compactness in t × cosine bound in x),
tail explicit (L∞ contraction + eigenvalue damping). -/
private theorem cutoffResolverMajorant_bddAbove_direct
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (hc : 0 < c)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    (j k : ℕ) (hj : (j : ℕ∞) ≤ 2) :
    BddAbove (Set.range fun q : ℝ × ℝ =>
      ‖iteratedFDeriv ℝ j
        (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q‖) := by
  set f := cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k with hf_def
  have hfC2 := cutoffResolverTerm_contDiff_two hu₀_bound hu₀_cont hfloor hc k
  have hcont : Continuous (fun q : ℝ × ℝ => ‖iteratedFDeriv ℝ j f q‖) :=
    (hfC2.continuous_iteratedFDeriv (by exact_mod_cast hj)).norm
  set A := fun t : ℝ =>
    smoothRightCutoff (c / 2) c t * resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t
  have hAC2 := cutoffResolverCoeff_contDiff_two hu₀_bound hu₀_cont hfloor hc k
  ...
  have hmid : ∃ Cmid : ℝ, ∀ q : ℝ × ℝ, c / 2 ≤ q.1 → q.1 ≤ c / 2 + 1 →
      ‖iteratedFDeriv ℝ j f q‖ ≤ Cmid := by
    -- Factor f = (A ∘ fst) · (cosineMode k ∘ snd)
    have hcos : ContDiff ℝ (2 : ℕ∞) (cosineMode k) := by unfold cosineMode; fun_prop
    have hjNat : j ≤ 2 := by exact_mod_cast hj
    -- Get compact-time bound on each order of iteratedFDeriv of A
    have hA_bounds : ∀ i : ℕ, i ≤ 2 →
        ∃ C_i : ℝ, ∀ t ∈ Set.Icc (c / 2) (c / 2 + 1),
          ‖iteratedFDeriv ℝ i A t‖ ≤ C_i := by
      intro i hi
      have hcont_i : Continuous (fun t : ℝ => iteratedFDeriv ℝ i A t) :=
        hAC2.continuous_iteratedFDeriv (by exact_mod_cast hi)
      exact isCompact_Icc.exists_bound_of_continuousOn hcont_i.continuousOn
    obtain ⟨C0, hC0⟩ := hA_bounds 0 (by omega)
    obtain ⟨C1, hC1⟩ := hA_bounds 1 (by omega)
    obtain ⟨C2, hC2⟩ := hA_bounds 2 (by omega)
    -- Combine: for each q with t ∈ [c/2, c/2+1], use Leibniz product bound
    -- The explicit bound involves Σ C(j,i) · C_i · valueCosWeight(j-i, k)
    -- This is a finite sum independent of q
    sorry
```

The goal is only the **middle slab** bound. It is not the global problem; the left and tail regions are handled by `hleft` and `htail`.

## Key point

`hmid` should not compactify `x`. The quantification is over all:

```lean
q : ℝ × ℝ
```

with only a time restriction:

```lean
c / 2 ≤ q.1 ∧ q.1 ≤ c / 2 + 1
```

So the correct proof is:

1. compactness only in time, giving constants `C0`, `C1`, `C2` for the `A(t)` derivatives on `[c/2, c/2+1]`;
2. global cosine derivative bounds in the `x` variable;
3. the existing bounded-weight one-mode Leibniz lemma:

```lean
boundedWeightJointTerm_iteratedFDeriv_le
```

This lemma is already open in `IntervalHeatResolverJointC2.lean` and is exactly the right tool. It packages the product rule and the global cosine bounds through `valueCosWeight`.

## Replacement proof for the `hmid` sorry

Replace only the `sorry` at the end of the `hmid` block with the following code.

```lean
    let Bt : ℕ → ℕ → ℝ := fun i _ =>
      if i = 0 then C0 else if i = 1 then C1 else C2
    refine ⟨boundedWeightJointMajorant Bt j k, ?_⟩
    intro q hq0 hq1
    have htmem : q.1 ∈ Set.Icc (c / 2) (c / 2 + 1) := ⟨hq0, hq1⟩
    have hBt : ∀ i : ℕ, i ≤ 2 →
        ‖iteratedFDeriv ℝ i A q.1‖ ≤ Bt i k := by
      intro i hi
      have hi_cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases hi_cases with rfl | rfl | rfl
      · simpa [Bt] using hC0 q.1 htmem
      · simpa [Bt] using hC1 q.1 htmem
      · simpa [Bt] using hC2 q.1 htmem
    have hf_bw : f = boundedWeightJointTerm (fun _ : ℕ => A) k := by
      funext q
      simp [hf_def, cutoffResolverTerm, boundedWeightJointTerm, A, mul_assoc]
    rw [hf_bw]
    exact boundedWeightJointTerm_iteratedFDeriv_le
      (c := fun _ : ℕ => A) (Bt := Bt) (n := k) (k := j) (q := q)
      hAC2 hj hBt
```

## Why this is the right proof

The local function is explicitly:

```lean
f q = smoothRightCutoff (c / 2) c q.1
        * resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k q.1
        * cosineMode k q.2
```

After defining:

```lean
A t = smoothRightCutoff (c / 2) c t
        * resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t
```

this is exactly:

```lean
boundedWeightJointTerm (fun _ : ℕ => A) k
```

because `boundedWeightJointTerm c n` is:

```lean
fun q => c n q.1 * cosineMode n q.2
```

The existing lemma gives:

```lean
‖iteratedFDeriv ℝ j (boundedWeightJointTerm (fun _ => A) k) q‖
  ≤ boundedWeightJointMajorant Bt j k
```

provided we can bound each time derivative of `A` up to order 2 at `q.1`. The compact-time estimates already extracted are:

```lean
hC0 : ∀ t ∈ Set.Icc (c / 2) (c / 2 + 1), ‖iteratedFDeriv ℝ 0 A t‖ ≤ C0
hC1 : ∀ t ∈ Set.Icc (c / 2) (c / 2 + 1), ‖iteratedFDeriv ℝ 1 A t‖ ≤ C1
hC2 : ∀ t ∈ Set.Icc (c / 2) (c / 2 + 1), ‖iteratedFDeriv ℝ 2 A t‖ ≤ C2
```

So define:

```lean
Bt i _ = if i = 0 then C0 else if i = 1 then C1 else C2
```

and prove the required `hBt` by `omega` case-splitting on `i ≤ 2`.

## Imports / namespace context

Inside `ShenWork/Paper2/IntervalHeatResolverJointC2.lean`, no new import should be required. The file already has the relevant opens:

```lean
open ShenWork.IntervalResolverJointC2Physical
  (boundedWeightJointTerm boundedWeightJointMajorant
   boundedWeightJointTerm_contDiff boundedWeightJointTerm_iteratedFDeriv_le)
open ShenWork.IntervalResolverSpectralJointC2CutoffBounds
  (norm_iteratedFDeriv_comp_fst_le)
```

If testing the idea in a separate scratch Lean file, use:

```lean
import ShenWork.Paper2.IntervalHeatResolverJointC2

open Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalCoupledRegularityBootstrap (coupledChemicalConcentration)
open ShenWork.IntervalResolverJointC2Physical
  (boundedWeightJointTerm boundedWeightJointMajorant
   boundedWeightJointTerm_iteratedFDeriv_le)
open ShenWork.IntervalResolverJointC2PhysicalConcrete (resolverTimeCoeff)
open ShenWork.IntervalResolverSpectralJointC2Cutoff
  (smoothRightCutoff)
```

But the theorem itself is `private`, so the real patch belongs in `IntervalHeatResolverJointC2.lean` at the `hmid` sorry.

## Possible minor elaboration issue and fallback

If the local definition rewrite fails at:

```lean
rw [hf_bw]
```

use this slightly more explicit form:

```lean
    have hbw := boundedWeightJointTerm_iteratedFDeriv_le
      (c := fun _ : ℕ => A) (Bt := Bt) (n := k) (k := j) (q := q)
      hAC2 hj hBt
    convert hbw using 1
    · ext r
      simp [hf_def, cutoffResolverTerm, boundedWeightJointTerm, A, mul_assoc]
```

The mathematical content is the same; this is only a Lean elaboration fallback for rewriting under `iteratedFDeriv`.

## Classification

`hmid` is a **mechanical wiring** proof, not a genuine new analytic estimate. The analytic input is already encoded in:

```lean
hAC2 : ContDiff ℝ (2 : ℕ∞) A
```

and compactness of the time interval supplies finite bounds for the three derivatives of `A`. The global-in-`x` issue is handled by the existing cosine `valueCosWeight` bounds through `boundedWeightJointTerm_iteratedFDeriv_le`.

The genuinely harder remaining part in this direct proof is the later:

```lean
htail : ∃ Ctail : ℝ, ∀ q : ℝ × ℝ, c / 2 + 1 < q.1 →
  ‖iteratedFDeriv ℝ j f q‖ ≤ Ctail
```

because that requires a real tail/time-uniform resolver coefficient bound, not just compactness.

## Bottom line

Use `boundedWeightJointTerm_iteratedFDeriv_le` with a local `Bt` built from the compact-time constants `C0`, `C1`, `C2`. This avoids compactifying `x` and gives exactly the finite `Cmid` required by the left/mid/tail `BddAbove` wrapper.
