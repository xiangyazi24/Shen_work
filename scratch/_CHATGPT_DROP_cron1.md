# Q1622 (cron1) -- `BddAbove` for cutoff resolver majorants

Repository: `xiangyazi24/Shen_work`  
Committed branch: `chatgpt-scratch`  
Target report file: `scratch/_CHATGPT_DROP_cron1.md`

## Scope and caveat

The prompt was:

```text
Q1622 (cron1): cron1 /tmp/q_cron1_bddabove.txt
```

The local file `/tmp/q_cron1_bddabove.txt` is not accessible through the GitHub connector. I therefore interpreted the task from the filename and from the current repository state as the `BddAbove` question around the cutoff resolver majorant in:

```text
ShenWork/Paper2/IntervalHeatResolverJointC2.lean
```

I used the GitHub connector only. I did **not** use Python, the sandbox, `/mnt/data`, or a sandbox download link.

One branch wrinkle: fetching `ShenWork/Paper2/IntervalHeatResolverJointC2.lean` at ref `chatgpt-scratch` returned `Not Found`, so the source inspection below is for the repository default branch. The report itself is committed on `chatgpt-scratch`, as requested.

## Short answer

For the cutoff resolver majorant, the right proof of `BddAbove` is **not** compactness of the full domain and not a hypothetical theorem like `Continuous.bddAbove_range`. The right proof is an **explicit global majorant**.

The current default-branch file already implements exactly that route:

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

That is the correct pattern: exhibit a finite real bound `cutoffResolverExplicitMajorant Bt c hc j k`, then prove every value in the range is below it.

## Why compactness is the wrong global proof

The range is over all

```lean
q : ℝ × ℝ
```

so no compactness lemma applies directly to the whole range. A continuous function on `ℝ × ℝ` can be unbounded. A compact rectangle such as

```lean
Set.Icc (c / 2) c ×ˢ Set.Icc (-R) R
```

only bounds the middle strip with `|x| ≤ R`; it does not bound the whole domain.

In this resolver/heat context, the full-domain bound comes from structure:

1. derivatives of the cutoff factor in `t` are globally bounded;
2. resolver coefficient terms are controlled by `PhysicalResolverJointC2Data`;
3. cosine-mode spatial derivatives are globally bounded by the bounded-weight machinery;
4. the product derivative is bounded by a finite Leibniz sum.

So compactness is useful only for the cutoff derivative support, not for the full resolver term.

## Where compact support is legitimately used

The file uses compact support only for derivatives of the smooth cutoff itself. The local lemma is:

```lean
private theorem resolverSmoothRightCutoff_iteratedFDeriv_bound_exists
    (c' c : ℝ) (hc'c : c' < c) (k : ℕ) (hk : (k : ℕ∞) ≤ 2) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ t : ℝ, ‖iteratedFDeriv ℝ k (smoothRightCutoff c' c) t‖ ≤ B := by
  ...
```

For `k = 0`, the cutoff itself is bounded by `1`. For `k > 0`, the derivative is zero off `Set.Icc c' c`, so the proof builds a `HasCompactSupport` witness and applies:

```lean
hcont.bounded_above_of_compact_support hcomp
```

This is correct because the function being bounded is now a one-variable cutoff derivative with compact support. It would be wrong to apply this reasoning to the whole product term on `ℝ × ℝ`.

## The explicit-majorant chain in the current file

The current file has the following architecture.

### 1. Define the raw and cutoff resolver terms

```lean
import ShenWork.Paper2.IntervalHeatResolverJointC2

open Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalCoupledRegularityBootstrap (coupledChemicalConcentration)
open ShenWork.IntervalResolverJointC2PhysicalConcrete (resolverTimeCoeff)

noncomputable section

namespace ShenWork.Paper2.HeatResolverJointC2Direct

/-- Raw resolver term. -/
def resolverTerm (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (k : ℕ) : ℝ × ℝ → ℝ :=
  fun q => resolverTimeCoeff p u k q.1 * cosineMode k q.2

/-- Cutoff resolver term. -/
def cutoffResolverTerm (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (c : ℝ) (k : ℕ) : ℝ × ℝ → ℝ :=
  fun q => smoothRightCutoff (c / 2) c q.1 *
    (resolverTimeCoeff p u k q.1 * cosineMode k q.2)

end ShenWork.Paper2.HeatResolverJointC2Direct
```

### 2. Define an explicit finite-sum majorant

The key definition is:

```lean
private noncomputable def cutoffResolverExplicitMajorant
    (Bt : ℕ → ℕ → ℝ) (c : ℝ) (hc : 0 < c) (j k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
    (if hi : (i : ℕ∞) ≤ 2 then
      resolverSmoothRightCutoffDerivBound (c / 2) c (by linarith) i hi
    else 0) *
    boundedWeightJointMajorant Bt (j - i) k
```

This is exactly the finite Leibniz bound: choose `i` derivatives landing on the cutoff/time factor and `j-i` derivatives landing on the bounded-weight resolver/cosine term.

### 3. Prove the pointwise explicit bound

The pointwise theorem is:

```lean
private theorem cutoffResolverTerm_iteratedFDeriv_le_explicit
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt)
    {c : ℝ} (hc : 0 < c) (j k : ℕ) (q : ℝ × ℝ)
    (hj : (j : ℕ∞) ≤ 2) :
    ‖iteratedFDeriv ℝ j (cutoffResolverTerm p u c k) q‖ ≤
      cutoffResolverExplicitMajorant Bt c hc j k := by
  ...
```

The proof uses:

```lean
norm_iteratedFDeriv_mul_le
norm_iteratedFDeriv_comp_fst_le
boundedWeightJointTerm_iteratedFDeriv_le
```

This is the real work. Once this pointwise estimate is available, `BddAbove` is immediate.

### 4. Use that pointwise bound to prove `BddAbove`

The proof is just:

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

That is the whole `BddAbove` story.

## Public wrapper if this is needed outside the file

The current `cutoffResolverMajorant_bddAbove_of_physical` theorem is `private`, so code outside `IntervalHeatResolverJointC2.lean` cannot call it directly. The file already exposes the more useful public theorem:

```lean
theorem cutoffResolverTerm_iteratedFDeriv_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    {c : ℝ} (hc : 0 < c) (j k : ℕ) (q : ℝ × ℝ)
    (hj : (j : ℕ∞) ≤ 2) :
    ‖iteratedFDeriv ℝ j
      (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q‖ ≤
      cutoffResolverMajorant p u₀ M₀ c hc j k
```

Therefore, if another file needs the range-boundedness fact, add this public wrapper:

```lean
import ShenWork.Paper2.IntervalHeatResolverJointC2

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)

noncomputable section

namespace ShenWork.Paper2.HeatResolverJointC2Direct

/-- Public `BddAbove` wrapper for the cutoff resolver derivative range. -/
theorem cutoffResolverTerm_iteratedFDeriv_range_bddAbove
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    (hc : 0 < c) (j k : ℕ) (hj : (j : ℕ∞) ≤ 2) :
    BddAbove (Set.range fun q : ℝ × ℝ =>
      ‖iteratedFDeriv ℝ j
        (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q‖) := by
  refine ⟨cutoffResolverMajorant p u₀ M₀ c hc j k, ?_⟩
  rintro _ ⟨q, rfl⟩
  exact cutoffResolverTerm_iteratedFDeriv_bound
    (p := p) (u₀ := u₀) (M₀ := M₀)
    hu₀_bound hu₀_cont hu₀_pos hc j k q hj

end ShenWork.Paper2.HeatResolverJointC2Direct
```

This wrapper does not need to know about the private explicit majorant or `PhysicalResolverJointC2Data`; it packages the already-public bound into a `BddAbove` range statement.

## How `ciSup` should be used here

The noncomputable majorant is defined as:

```lean
noncomputable def cutoffResolverMajorant (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ) (_M₀ c : ℝ) (hc : 0 < c)
    (j k : ℕ) : ℝ :=
  ⨆ q : ℝ × ℝ, ‖iteratedFDeriv ℝ j
    (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q‖
```

For upper bounds on this `⨆`, use:

```lean
exact ciSup_le (fun q =>
  cutoffResolverTerm_iteratedFDeriv_le_explicit H hc j k q hj)
```

For pointwise bounds by the `⨆`, use:

```lean
have hbdd := cutoffResolverMajorant_bddAbove_of_physical
  (p := p) (u₀ := u₀) (M₀ := M₀) hc H j k hj
exact le_ciSup hbdd q
```

or, outside the file, avoid `le_ciSup` directly and use the public theorem:

```lean
exact cutoffResolverTerm_iteratedFDeriv_bound
  (p := p) (u₀ := u₀) (M₀ := M₀)
  hu₀_bound hu₀_cont hu₀_pos hc j k q hj
```

## Bottom line

The correct answer to the `BddAbove` problem is:

```text
Do not try to get global BddAbove from continuity or compactness of ℝ × ℝ.
Use the explicit majorant theorem.
```

In the current default branch, this is already done by:

```lean
cutoffResolverTerm_iteratedFDeriv_le_explicit
cutoffResolverMajorant_bddAbove_of_physical
cutoffResolverMajorant_le_explicit
cutoffResolverTerm_iteratedFDeriv_bound
```

If a downstream file needs a named public `BddAbove` lemma, add the small wrapper `cutoffResolverTerm_iteratedFDeriv_range_bddAbove` shown above.
