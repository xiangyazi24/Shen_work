# Q1485 (cron3): existing `boundedWeightJointGradMajorant` summability proofs

## Search scope

Searched `xiangyazi24/Shen_work` for:

```text
boundedWeightJointGradMajorant
Summable (boundedWeightJointGradMajorant
Summable (ShenWork.IntervalResolverJointC2Physical.boundedWeightJointGradMajorant
boundedWeightJointGradMajorant Summable
grad_summable boundedWeightJointGradMajorant
intervalWeakH4Neumann
quartic_decay intervalWeakH4Neumann_cosineCoeff
```

The indexed/default tree searched by the GitHub connector is commit `7db6d8e4b01d279823281613bb824200483faddd` for the relevant search results.

## Bottom line

There are **two real proof files** for `Summable (boundedWeightJointGradMajorant ...)`:

1. `ShenWork/PDE/IntervalIterateGradMajorant.lean`
2. `ShenWork/PDE/IntervalIterateGradSummableFromSourceL1.lean`

All other hits are either:

- definitions/assemblers that **consume** a gradient-summability hypothesis,
- structures carrying `grad_summable` as a field,
- pass-through wrappers, or
- comments/import noise.

For the resolver physical route with

```lean
Bt i k = intervalNeumannResolverWeight p k * Es i k
```

mere source decay

```text
Es i k = O((kπ)^-2)
```

is **not enough** for the order-2 gradient majorant.  The blocker is the `i = 0` component of `m = 2`:

```text
|kπ| * λ_k * (w_k * Es 0 k)  ~  |kπ| * Es 0 k
```

because `λ_k * w_k ≤ 1`.  Thus `Es 0 k = O(k^-2)` gives `O(k^-1)`, not summable.

You need either:

- an explicit weighted source-L1 hypothesis `Summable (fun k => |kπ| * Es 0 k)`, or
- quartic source decay `Es 0 k = O((kπ)^-4)`, which gives `O(k^-3)` after the extra `|kπ|`.

The existing code does **not** currently use `intervalWeakH4Neumann...` to prove `boundedWeightJointGradMajorant` summability.  The H4/quartic code is used for a separate resolver-C4/eigenvalue-L1 route.

## 1. `IntervalResolverJointC2Physical.lean`: definition and generic consumer, not a summability proof

File:

```text
ShenWork/PDE/IntervalResolverJointC2Physical.lean
```

This defines the gradient majorant:

```lean
def boundedWeightJointGradMajorant (Bt : ℕ → ℕ → ℝ) (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * Bt i n * gradCosWeight (k - i) n
```

and proves the generic gradient `contDiff_tsum` assembler:

```lean
theorem boundedWeightJointGradSeries_contDiff_two
    {c : ℕ → ℝ → ℝ} {Bt : ℕ → ℕ → ℝ}
    (hc : ∀ n, ContDiff ℝ (2 : ℕ∞) (c n))
    (hBt : ∀ (i n : ℕ) (t : ℝ), i ≤ 2 → ‖iteratedFDeriv ℝ i (c n) t‖ ≤ Bt i n)
    (hsumm : ∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointGradMajorant Bt k)) :
    ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => ∑' n : ℕ, boundedWeightJointGradTerm c n q) := ...
```

This file **does not prove** `Summable (boundedWeightJointGradMajorant Bt m)` from decay.  It consumes `hsumm`.

Concrete proof pattern inside the file: it proves a per-term Leibniz majorant using `norm_iteratedFDeriv_mul_le`, projection bounds, and `cosineModeDeriv_iteratedFDeriv_bound`; then `contDiff_tsum` consumes the supplied `hsumm`.

Relevant snippet:

```lean
theorem boundedWeightJointGradTerm_iteratedFDeriv_le
    {c : ℕ → ℝ → ℝ} {Bt : ℕ → ℕ → ℝ} {n k : ℕ} {q : ℝ × ℝ}
    (hc : ContDiff ℝ (2 : ℕ∞) (c n)) (hk : (k : ℕ∞) ≤ (2 : ℕ∞))
    (hBt : ∀ i, i ≤ 2 → ‖iteratedFDeriv ℝ i (c n) q.1‖ ≤ Bt i n) :
    ‖iteratedFDeriv ℝ k (boundedWeightJointGradTerm c n) q‖ ≤
      boundedWeightJointGradMajorant Bt k n := by
  ...
```

## 2. `IntervalIterateGradMajorant.lean`: real proof, but from component summability / hypothesis

File:

```text
ShenWork/PDE/IntervalIterateGradMajorant.lean
```

This file gives the clean expansion of the **order-2** gradient majorant:

```lean
theorem gradMajorant_two_eq (Bt : ℕ → ℕ → ℝ) (k : ℕ) :
    boundedWeightJointGradMajorant Bt 2 k
      = |(k : ℝ) * Real.pi| * unitIntervalCosineEigenvalue k * Bt 0 k
        + 2 * (unitIntervalCosineEigenvalue k * Bt 1 k)
        + |(k : ℝ) * Real.pi| * Bt 2 k := by
```

Then it proves:

```lean
theorem grad2_summable_of_components {Bt : ℕ → ℕ → ℝ}
    (h0 : Summable (fun k : ℕ =>
      |(k : ℝ) * Real.pi| * unitIntervalCosineEigenvalue k * Bt 0 k))
    (h1 : Summable (fun k : ℕ => unitIntervalCosineEigenvalue k * Bt 1 k))
    (h2 : Summable (fun k : ℕ => |(k : ℝ) * Real.pi| * Bt 2 k)) :
    Summable (boundedWeightJointGradMajorant Bt 2) := by
  have hsum := (h0.add (h1.mul_left 2)).add h2
  refine hsum.congr (fun k => ?_)
  rw [gradMajorant_two_eq]
```

It also has:

```lean
theorem iterate_Hg2u_of_gradSummable {Bt : ℕ → ℕ → ℝ}
    (hgrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointGradMajorant Bt m)) :
    Summable (boundedWeightJointGradMajorant Bt 2) :=
  hgrad 2 (by norm_num)
```

Decay interpretation:

For a generic `Bt`, this theorem does not assume `O(k^-2)` or `O(k^-4)` directly.  It requires exactly these three summable components:

```text
T0: |kπ| * λ_k * Bt0(k)
T1: λ_k * Bt1(k)
T2: |kπ| * Bt2(k)
```

So for polynomial decay alone:

- `Bt0(k)` must decay faster than `k^-4` in the p-series sense; `O(k^-4)` gives `k^-1`, not summable.
- `Bt0(k) = O(k^-6)` is more than enough.
- In the resolver case `Bt0 = w_k * Es0`; if `Es0 = O(k^-4)`, then `Bt0 = O(k^-6)`, so `T0 = O(k^-3)`.

This file explicitly says the gradient majorant has one extra `|kπ|` weight beyond the value majorant and cannot be obtained from finite-order `value_summable` alone.

## 3. `IntervalIterateGradSummableFromSourceL1.lean`: real proof for all `m ≤ 2`, from weighted-Btu summables

File:

```text
ShenWork/PDE/IntervalIterateGradSummableFromSourceL1.lean
```

This is the most concrete existing proof of

```lean
∀ m ≤ 2, Summable (boundedWeightJointGradMajorant Btu m)
```

It proves the order-0 and order-1 expansions:

```lean
theorem gradMajorant_zero_eq (Bt : ℕ → ℕ → ℝ) (k : ℕ) :
    boundedWeightJointGradMajorant Bt 0 k = |(k : ℝ) * Real.pi| * Bt 0 k := by
```

```lean
theorem gradMajorant_one_eq (Bt : ℕ → ℕ → ℝ) (k : ℕ) :
    boundedWeightJointGradMajorant Bt 1 k
      = unitIntervalCosineEigenvalue k * Bt 0 k + |(k : ℝ) * Real.pi| * Bt 1 k := by
```

Then the capstone is:

```lean
theorem iterate_gradSummable_of_weightedBtuSummable {Btu : ℕ → ℕ → ℝ}
    (s0 : Summable (fun k : ℕ => |(k : ℝ) * Real.pi| * Btu 0 k))
    (s1a : Summable (fun k : ℕ => unitIntervalCosineEigenvalue k * Btu 0 k))
    (s1 : Summable (fun k : ℕ => |(k : ℝ) * Real.pi| * Btu 1 k))
    (s2a : Summable (fun k : ℕ =>
      |(k : ℝ) * Real.pi| * unitIntervalCosineEigenvalue k * Btu 0 k))
    (s2b : Summable (fun k : ℕ => unitIntervalCosineEigenvalue k * Btu 1 k))
    (s2c : Summable (fun k : ℕ => |(k : ℝ) * Real.pi| * Btu 2 k)) :
    ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointGradMajorant Btu m) := by
  intro m hm
  have hm2 : m ≤ 2 := by exact_mod_cast hm
  interval_cases m
  · exact (s0.congr (fun k => (gradMajorant_zero_eq Btu k).symm))
  · exact ((s1a.add s1).congr (fun k => (gradMajorant_one_eq Btu k).symm))
  · exact grad2_summable_of_components s2a s2b s2c
```

Decay interpretation:

This proof does not bake in a single decay rate.  It asks for the exact weighted summability conditions.  For pure polynomial bounds:

- `s2a` is the strongest: `∑ |kπ| λ_k Btu0(k)`.
- If `Btu0(k) = O(k^-4)`, this is borderline `∑ k^-1`, not summable.
- If `Btu0(k) = O(k^-6)` or exponentially decaying, it is summable.

The same file has homogeneous heat-side helper proofs using exponential decay:

```lean
hom_grad_T1_summable : ∑ |kπ|·λ_k·(M₀·exp(-tλ_k))
hom_grad_T2_summable : ∑ λ_k·(M₀·λ_k·exp(-tλ_k))
hom_grad_T3_summable : ∑ |kπ|·(M₀·λ_k²·exp(-tλ_k))
```

Those use `eigenvalue_sq_mul_exp_summable` / `eigenvalue_cube_mul_exp_summable`, i.e. exponential heat decay, not bare `O(k^-2)` or quartic decay.

It also has Duhamel-side weighted summability from source-L1-at-weight:

```lean
theorem duhamelSpectral_gradWeighted_summable_of_sourceL1
    ...
    (hsum : Summable (fun k : ℕ => |(k : ℝ) * Real.pi| * Bv k)) :
    Summable (fun k : ℕ => |(k : ℝ) * Real.pi| *
      (unitIntervalCosineEigenvalue k * |duhamelSpectralCoeff a t k|)) := by
```

So this route asks for an explicit weighted source envelope, not an H4 lemma.

## 4. `IntervalPhysicalResolverDataConcrete.lean`: carries and forwards `grad_summable`, no proof from decay

File:

```text
ShenWork/PDE/IntervalPhysicalResolverDataConcrete.lean
```

The structure field is:

```lean
structure PhysicalSourceTimeC2
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (Es : ℕ → ℕ → ℝ) : Prop where
  ...
  grad_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointGradMajorant
      (fun i k => intervalNeumannResolverWeight p k * Es i k) m)
```

Then `physicalResolverJointC2Data_of_floor` simply forwards it:

```lean
  value_summable := H.value_summable
  grad_summable := H.grad_summable
```

Decay interpretation:

The file comments say `Es` has spatial `(kπ)^-2` decay and `w_k` is folded in, but the actual `grad_summable` is a **field**, not derived.  Thus this file does not prove that `O(k^-2)` suffices.  It explicitly requires the weighted gradient summability as source data.

## 5. `IntervalPhysicalSourceTimeC2Concrete.lean`: `builtEs` is only quadratic; `hgrad` is an input

File:

```text
ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean
```

`builtEs` is defined by a zeroth-mode bound and a positive-mode quadratic bound:

```lean
def builtEs
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂) (i k : ℕ) : ℝ :=
  if hi : i ≤ 2 then
    (if k = 0 then Classical.choose (H.zerothBound i hi)
     else Classical.choose (H.laplBound i hi) / ((k:ℝ) * Real.pi) ^ 2)
  else 0
```

and `physicalSourceTimeC2_of_floored` takes both value and gradient summability as inputs:

```lean
(hgrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
  Summable (boundedWeightJointGradMajorant
    (fun i k => intervalNeumannResolverWeight p k * builtEs H i k) m)) :
PhysicalSourceTimeC2 p u (builtEs H)
```

So this file does **not** prove gradient summability from `builtEs`.  In fact, the definition of `builtEs` as `(kπ)^-2` confirms why the missing proof cannot be true at order 2 unless the zeroth time-order gets extra decay/weighted summability.

## 6. `IntervalFlooredSourceTimeDataIterate.lean`: pass-through wrapper, no proof

File:

```text
ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean
```

`coupledChemDivFluxFactorJointC2Inputs_of_iterate` takes:

```lean
(hgrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
  Summable (ShenWork.IntervalResolverJointC2Physical.boundedWeightJointGradMajorant
    (fun i k => ShenWork.PDE.intervalNeumannResolverWeight p k *
      builtEs (flooredSourceTimeData_of_iterate H) i k) m))
```

and passes it through to `physicalSourceTimeC2_of_floored` / `coupledChemDivFluxFactorJointC2Inputs_of_floor`.

No decay proof here.

## 7. `IntervalChemDivWinDischarge.lean`: residual field, no proof

File:

```text
ShenWork/Paper2/IntervalChemDivWinDischarge.lean
```

The residual bundle carries:

```lean
hgrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
  Summable (ShenWork.IntervalResolverJointC2Physical.boundedWeightJointGradMajorant
    (fun i k => ShenWork.PDE.intervalNeumannResolverWeight p k *
      ShenWork.IntervalPhysicalSourceTimeC2Concrete.builtEs
        (ShenWork.IntervalFlooredSourceTimeDataIterate.flooredSourceTimeData_of_iterate
          hiter) i k) m)
```

and forwards it into `coupledChemDivFluxFactorJointC2Inputs_of_iterate`.

No decay proof here.

## 8. `IntervalResolverJointC2PhysicalConcrete.lean`: consumes `H.grad_summable`, no proof from decay

File:

```text
ShenWork/PDE/IntervalResolverJointC2PhysicalConcrete.lean
```

`coupledChemical_grad_jointContDiffAt_two` applies the generic gradient assembler using `H.grad_summable`:

```lean
have hseries : ContDiff ℝ (2 : ℕ∞)
    (fun q : ℝ × ℝ =>
      ∑' k : ℕ, boundedWeightJointGradTerm (resolverTimeCoeff p u) k q) :=
  boundedWeightJointGradSeries_contDiff_two H.coeff_contDiff
    (fun i k t hi => H.coeff_bound i k t hi) H.grad_summable
```

This is a consumer, not a summability proof.

The same theorem derives an eigenvalue-weighted value summability from `H.value_summable 2`, but that is for termwise first spatial derivative of the value series, not for proving the gradient majorant itself.

## 9. `IntervalChemDivMixedReprWitness.lean`: consumers/extractions, not `grad_summable` proof

File:

```text
ShenWork/PDE/IntervalChemDivMixedReprWitness.lean
```

This file uses `PhysicalResolverJointC2Data` and extracts some value-side eigenvalue summability.  The relevant proved lemma is:

```lean
theorem resolver_eigSummable
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt) (t : ℝ) :
    Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k * |resolverTimeCoeff p u k t|) := by
  ...
  (H.value_summable 2 le_rfl)
```

This uses `value_summable`, not `boundedWeightJointGradMajorant` summability.  It is not a grad-summable proof.

## 10. `IntervalHeatSemigroupHighRegularity.lean`: heat cutoff majorant, not `boundedWeightJointGradMajorant`

Search returns this file, but the relevant proven machinery is the heat cutoff series majorant, not `boundedWeightJointGradMajorant`.  It proves summability using exponential heat decay:

```lean
one_add_eigenvalue_pow_mul_exp_summable
cutoffHeatMajorant_summable
cutoffHeatTerm_iteratedFDeriv_bound
cutoffHeatSeries_contDiff_two
```

This is useful as a proof pattern (`norm_iteratedFDeriv_mul_le`, finite Leibniz sum, `contDiff_tsum`), but it is not an existing proof of

```lean
Summable (boundedWeightJointGradMajorant ...)
```

## `intervalWeakH4Neumann` / quartic decay usage

Search results for `intervalWeakH4Neumann` were only:

1. `ShenWork/PDE/IntervalSourceDecayQuantitative.lean`
2. `ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean`
3. `UNDERSTANDING.md`

### Defined/proved in `IntervalSourceDecayQuantitative.lean`

The file proves quartic decay:

```lean
theorem intervalWeakH4Neumann_cosineCoeff_quartic_decay_of_bound
    {f : ℝ → ℝ} (hf : IntervalWeakH2Neumann f)
    (hf'' : IntervalWeakH2Neumann hf.secondDeriv)
    {B₂ : ℝ} (hB₂ : (∫ x in (0:ℝ)..1, |hf''.secondDeriv x|) ≤ B₂) :
    ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs f k| ≤ 2 * B₂ / ((k : ℝ) * Real.pi) ^ 4 := by
```

and then uses it to prove eigenvalue-weighted L1:

```lean
theorem intervalWeakH4Neumann_eigenvalue_L1_summable
    {f : ℝ → ℝ} (hf : IntervalWeakH2Neumann f)
    (hf'' : IntervalWeakH2Neumann hf.secondDeriv) :
    Summable (fun k : ℕ => unitIntervalCosineEigenvalue k * |cosineCoeffs f k|) := by
```

The comparison is exactly:

```text
λ_k |c_k| ≤ (kπ)^2 * 2B₂/(kπ)^4 = O(k^-2)
```

so it proves `λ·coeff ∈ ℓ¹`.

### Used in `IntervalConjugateLevel0BFormSourceOn.lean`

This file has a concrete call:

```lean
have hsumm := ShenWork.IntervalSourceDecayQuantitative.intervalWeakH4Neumann_eigenvalue_L1_summable
  hf_H2 hf''_H2
```

inside the proof of `hV_C4 : ContDiff ℝ 4 V_cos`, after building `g_smooth = ν·U_cos^γ` and H2-depth-2 data.  The local block still contains nearby `sorry`s for third-derivative continuity / endpoint tendsto details, so this is a **usage route**, not a completed clean proof of a broader `grad_summable` field.

### No existing H4-to-`boundedWeightJointGradMajorant` proof found

I found no existing theorem that uses

```lean
intervalWeakH4Neumann_eigenvalue_L1_summable
```

or the quartic decay theorem to prove

```lean
Summable (boundedWeightJointGradMajorant ...)
```

So for your current target, the likely new lemma should be something like:

```lean
-- Sketch only: source coefficient quartic/L1-at-|kπ| gives resolver grad majorant.
theorem resolver_grad_summable_of_source_weightedL1
    {p : CM2Params} {Es : ℕ → ℕ → ℝ}
    (h0_weighted : Summable (fun k => |(k : ℝ) * Real.pi| * Es 0 k))
    (h1_l1 : Summable (fun k => Es 1 k))
    (h2_l1 : Summable (fun k => Es 2 k)) :
    Summable (boundedWeightJointGradMajorant
      (fun i k => intervalNeumannResolverWeight p k * Es i k) 2) := by
  -- expand `boundedWeightJointGradMajorant` at `2`
  -- bound T0 by `|kπ| * Es 0 k` using `λ_k * w_k ≤ 1`
  -- bound T1 by `2 * Es 1 k` using `λ_k * w_k ≤ 1`
  -- bound T2 by `(1 / μ) * |kπ| * Es 2 k` or a sharper `|kπ| * w_k ≤ ...`
  -- combine summable sequences
  sorry
```

If `Es 0 k` comes from H4/quartic decay, then `h0_weighted` follows by comparison to `∑ k^-3`.  If `Es 1, Es 2` remain quadratic `O(k^-2)`, their L1 conditions are already plausible by comparison to `∑ k^-2`.

## Practical answer for the current blocker

For resolver `grad_summable` with `Bt = w·builtEs`:

- `builtEs` as currently defined from `laplBound` is only quadratic for all time orders.
- This is enough for value-summability, and enough for gradient orders `m = 0,1`.
- It is **not** enough for gradient order `m = 2`, because of the `|kπ|·λ_k·Bt0` term.
- Existing proofs either assume the needed weighted summability directly (`PhysicalSourceTimeC2.grad_summable`, `hgrad`, residual fields), or prove it from explicit weighted component summabilities (`iterate_gradSummable_of_weightedBtuSummable`).
- No existing code wires H4/quartic decay into `boundedWeightJointGradMajorant` summability.  That is the missing reusable lemma to add.
