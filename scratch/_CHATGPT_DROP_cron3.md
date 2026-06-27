# Q1331 (cron3): real `cutoffResolverMajorant` for resolver cutoff series

## Short answer

Do **not** define the resolver cutoff majorant as a single coarse factor like

```lean
(1 + unitIntervalCosineEigenvalue k) ^ j * intervalNeumannResolverWeight p k * builtEs H ?i k
```

because for `j = 2` that loses the cancellation and becomes only `O(1)`.  The correct definition is a **finite Leibniz convolution**:

```text
cutoff derivative of order a
×
uncut resolver joint majorant of order j-a.
```

Concretely, use

```lean
boundedWeightJointMajorant
  (fun i k => intervalNeumannResolverWeight p k * builtEs H i k)
```

for the uncut resolver term, and convolve it with the cutoff derivative bounds.

This is exactly the physical bounded-weight mechanism already in
`IntervalResolverJointC2Physical`: the spatial growth is isolated in
`valueCosWeight`, while the time coefficient bound is
`wₖ * builtEs H i k`.

## Important signature correction

The current placeholder in `IntervalHeatResolverJointC2.lean` has signature

```lean
noncomputable def cutoffResolverMajorant (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ) (M₀ c : ℝ) (hc : 0 < c)
    (j k : ℕ) : ℝ :=
  Classical.choice inferInstance
```

That signature is too weak.  `M₀` and `hu₀_bound` alone do not expose the three source-time envelopes needed for

```lean
srcTimeCoeff p u k t
```

or for its first two time derivatives.  The definition must take either:

1. `Es : ℕ → ℕ → ℝ` plus a `PhysicalSourceTimeC2 p u Es`, or
2. the concrete floored data `H : FlooredSourceTimeData p u s₁ s₂`, then use `builtEs H`.

Since the question asked for `builtEs`, use option 2 and thread the physical summability hypothesis separately.

## Imports / opens

In `ShenWork/Paper2/IntervalHeatResolverJointC2.lean`, add the source-data import if it is not already transitively available:

```lean
import ShenWork.PDE.IntervalPhysicalSourceTimeC2Concrete
```

Then add/open these names near the current opens:

```lean
open ShenWork.IntervalPhysicalSourceTimeC2Concrete
  (FlooredSourceTimeData builtEs)
open ShenWork.IntervalResolverJointC2Physical
  (boundedWeightJointMajorant boundedWeightJointTerm
   boundedWeightJointTerm_iteratedFDeriv_le)
open ShenWork.IntervalPhysicalResolverDataConcrete
  (PhysicalSourceTimeC2 physicalResolverJointC2Data_of_floor resolverWeight_nonneg)
```

You will also need `valueCosWeight_nonneg` if you prove nonnegativity locally:

```lean
open ShenWork.IntervalResolverSpectralJointC2Concrete
  (valueCosWeight_nonneg)
```

## Cutoff derivative bound helper

The heat file already has this as a **private** helper, so it is not reusable from another file.  Either make the heat helper public, or copy this block into `IntervalHeatResolverJointC2.lean` under the resolver namespace.

```lean
private theorem rightCutoff_iteratedFDeriv_bound_exists
    (c' c : ℝ) (hc'c : c' < c) (i : ℕ) (hi : (i : ℕ∞) ≤ (2 : ℕ∞)) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ t : ℝ, ‖iteratedFDeriv ℝ i (smoothRightCutoff c' c) t‖ ≤ B := by
  rcases Nat.eq_zero_or_pos i with rfl | hi_pos
  · refine ⟨1, zero_le_one, fun t => ?_⟩
    rw [norm_iteratedFDeriv_zero]
    unfold smoothRightCutoff
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  · have hcont : Continuous
        (fun t : ℝ => iteratedFDeriv ℝ i (smoothRightCutoff c' c) t) :=
      smoothRightCutoff_contDiff.continuous_iteratedFDeriv (by exact_mod_cast hi)
    have hi_ne : i ≠ 0 := Nat.pos_iff_ne_zero.mp hi_pos
    have hzero : ∀ t, t ∉ Set.Icc c' c →
        iteratedFDeriv ℝ i (smoothRightCutoff c' c) t = 0 := by
      intro t ht
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
      rcases ht with ht_lt | ht_gt
      · have hev : smoothRightCutoff c' c =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
          filter_upwards [Iio_mem_nhds ht_lt] with s hs
          exact smoothRightCutoff_eq_zero_of_le hc'c (le_of_lt hs)
        have := (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev i).eq_of_nhds
        rwa [iteratedFDeriv_const_of_ne hi_ne, Pi.zero_apply] at this
      · have hev : smoothRightCutoff c' c =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
          filter_upwards [Ioi_mem_nhds ht_gt] with s hs
          exact smoothRightCutoff_eq_one_of_ge hc'c (le_of_lt hs)
        have := (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev i).eq_of_nhds
        rwa [iteratedFDeriv_const_of_ne hi_ne, Pi.zero_apply] at this
    have hcomp : HasCompactSupport
        (fun t : ℝ => iteratedFDeriv ℝ i (smoothRightCutoff c' c) t) :=
      HasCompactSupport.intro' isCompact_Icc isClosed_Icc hzero
    rcases hcont.bounded_above_of_compact_support hcomp with ⟨C, hC⟩
    exact ⟨max C 0, le_max_right C 0, fun t => (hC t).trans (le_max_left C 0)⟩

private noncomputable def rightCutoffDerivMajorant
    (c : ℝ) (hc : 0 < c) (i : ℕ) : ℝ :=
  if hi : (i : ℕ∞) ≤ (2 : ℕ∞) then
    Classical.choose
      (rightCutoff_iteratedFDeriv_bound_exists (c / 2) c (by linarith) i hi)
  else 0

private theorem rightCutoffDerivMajorant_nonneg
    (c : ℝ) (hc : 0 < c) (i : ℕ) :
    0 ≤ rightCutoffDerivMajorant c hc i := by
  unfold rightCutoffDerivMajorant
  split_ifs with hi
  · exact (Classical.choose_spec
      (rightCutoff_iteratedFDeriv_bound_exists (c / 2) c (by linarith) i hi)).1
  · exact le_rfl

private theorem rightCutoffDerivMajorant_spec
    (c : ℝ) (hc : 0 < c) {i : ℕ} (hi : (i : ℕ∞) ≤ (2 : ℕ∞)) (t : ℝ) :
    ‖iteratedFDeriv ℝ i (smoothRightCutoff (c / 2) c) t‖ ≤
      rightCutoffDerivMajorant c hc i := by
  unfold rightCutoffDerivMajorant
  rw [dif_pos hi]
  exact (Classical.choose_spec
    (rightCutoff_iteratedFDeriv_bound_exists (c / 2) c (by linarith) i hi)).2 t
```

## Nonnegativity helpers

`builtEs` is nonnegative by construction: zeroth-mode chooses a nonnegative bound; positive modes choose a nonnegative Laplacian envelope divided by `(kπ)^2`.

```lean
private theorem builtEs_nonneg
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂) (i k : ℕ) :
    0 ≤ builtEs H i k := by
  unfold builtEs
  by_cases hi : i ≤ 2
  · rw [dif_pos hi]
    by_cases hk : k = 0
    · rw [if_pos hk]
      exact (Classical.choose_spec (H.zerothBound i hi)).1
    · rw [if_neg hk]
      have hM : 0 ≤ Classical.choose (H.laplBound i hi) :=
        (Classical.choose_spec (H.laplBound i hi)).1
      have hkpos : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
      have hden : 0 ≤ ((k : ℝ) * Real.pi) ^ 2 := by positivity
      exact div_nonneg hM hden
  · rw [dif_neg hi]
    exact le_rfl

private theorem boundedWeightJointMajorant_nonneg_of_Bt_nonneg
    {Bt : ℕ → ℕ → ℝ} (hBt : ∀ i k, 0 ≤ Bt i k) (m k : ℕ) :
    0 ≤ boundedWeightJointMajorant Bt m k := by
  unfold boundedWeightJointMajorant
  apply Finset.sum_nonneg
  intro i _hi
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (hBt i k))
    (valueCosWeight_nonneg (m - i) k)
```

## The real majorant definition

This is the replacement for the placeholder.  Notice the majorant depends on `H`, not merely on `u₀` and `M₀`.

```lean
noncomputable def cutoffResolverMajorant
    (p : CM2Params)
    {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂)
    (c : ℝ) (hc : 0 < c) (j k : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (j + 1),
    (j.choose a : ℝ) * rightCutoffDerivMajorant c hc a *
      boundedWeightJointMajorant
        (fun i k => intervalNeumannResolverWeight p k * builtEs H i k)
        (j - a) k
```

Interpretation:

```text
D^j(φ · resolverTerm)
  ≤ Σ_{a≤j} choose(j,a) · |D^a φ| · |D^{j-a}(resolverTerm)|
  ≤ Σ_{a≤j} choose(j,a) · Φ_a · boundedWeightJointMajorant (w·builtEs) (j-a) k.
```

This preserves the cancellation:

```text
w_k              ~ 1/(kπ)^2
builtEs H i k    ~ 1/(kπ)^2      for k ≥ 1
valueCosWeight m ~ (kπ)^m        for m ≤ 2
```

so each term is `O((kπ)^{m-4})`, with `m ≤ 2`, hence at worst `O((kπ)^-2)`.

## Summability proof

Best proof: consume the existing physical bounded-weight summability field.  Do not re-prove all `(kπ)^{-2}` arithmetic inside the cutoff file.

Use this statement:

```lean
theorem cutoffResolverMajorant_summable
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂)
    {c : ℝ} (hc : 0 < c)
    (hval : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointMajorant
        (fun i k => intervalNeumannResolverWeight p k * builtEs H i k) m))
    {j : ℕ} (hj : (j : ℕ∞) ≤ (2 : ℕ∞)) :
    Summable (cutoffResolverMajorant p H c hc j) := by
  classical
  let Bt : ℕ → ℕ → ℝ := fun i k => intervalNeumannResolverWeight p k * builtEs H i k
  let term : ℕ → ℕ → ℝ := fun a k =>
    (j.choose a : ℝ) * rightCutoffDerivMajorant c hc a *
      boundedWeightJointMajorant Bt (j - a) k
  have hterm : ∀ a ∈ Finset.range (j + 1), Summable (term a) := by
    intro a ha
    have hjNat : j ≤ 2 := by exact_mod_cast hj
    have hjaNat : j - a ≤ 2 := le_trans (Nat.sub_le j a) hjNat
    have hja : ((j - a : ℕ) : ℕ∞) ≤ (2 : ℕ∞) := by exact_mod_cast hjaNat
    simpa [term, Bt] using
      (hval (j - a) hja).mul_left
        ((j.choose a : ℝ) * rightCutoffDerivMajorant c hc a)
  have hsum : ∀ s : Finset ℕ,
      (∀ a ∈ s, Summable (term a)) →
      Summable (fun k : ℕ => ∑ a in s, term a k) := by
    intro s
    refine Finset.induction_on s ?base ?step
    · intro _
      simpa using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
    · intro a s has ih hsumm
      have ha : Summable (term a) := hsumm a (by simp [has])
      have hs : Summable (fun k : ℕ => ∑ b in s, term b k) :=
        ih (fun b hb => hsumm b (by simp [hb, has]))
      simpa [Finset.sum_insert has] using ha.add hs
  simpa [cutoffResolverMajorant, term, Bt] using
    hsum (Finset.range (j + 1)) hterm
```

If your local Mathlib has the finite-sum summability theorem under a convenient name, the last `hsum` induction can be replaced by the shorter finite-sum API.  The induction above avoids depending on the exact lemma name.

## Bound theorem shape

The derivative bound should also be stated with the physical source package, not with only `hu₀_bound` and `hu₀_cont`:

```lean
theorem cutoffResolverTerm_iteratedFDeriv_bound
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂)
    (Hphys : PhysicalSourceTimeC2 p u (builtEs H))
    {c : ℝ} (hc : 0 < c) (j k : ℕ) (q : ℝ × ℝ)
    (hj : (j : ℕ∞) ≤ (2 : ℕ∞)) :
    ‖iteratedFDeriv ℝ j (cutoffResolverTerm p u c k) q‖ ≤
      cutoffResolverMajorant p H c hc j k := by
  classical
  let Bt : ℕ → ℕ → ℝ := fun i k => intervalNeumannResolverWeight p k * builtEs H i k
  have Hres := physicalResolverJointC2Data_of_floor Hphys
  let G : ℝ × ℝ → ℝ := fun q => smoothRightCutoff (c / 2) c q.1
  let R : ℝ × ℝ → ℝ := boundedWeightJointTerm (resolverTimeCoeff p u) k
  have hterm : cutoffResolverTerm p u c k = fun q => G q * R q := by
    funext q
    simp [cutoffResolverTerm, boundedWeightJointTerm, resolverTerm, G, R, mul_assoc]
  have hG : ContDiff ℝ (2 : ℕ∞) G :=
    (smoothRightCutoff_contDiff (c' := c / 2) (c := c)).comp contDiff_fst
  have hR : ContDiff ℝ (2 : ℕ∞) R :=
    boundedWeightJointTerm_contDiff k (Hres.coeff_contDiff k)
  have hjTop : ((j : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast hj
  rw [hterm]
  calc
    ‖iteratedFDeriv ℝ j (fun q => G q * R q) q‖
        ≤ ∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ) *
            ‖iteratedFDeriv ℝ a G q‖ *
            ‖iteratedFDeriv ℝ (j - a) R q‖ := by
          simpa [mul_assoc] using norm_iteratedFDeriv_mul_le hG hR q hjTop
    _ ≤ cutoffResolverMajorant p H c hc j k := by
      unfold cutoffResolverMajorant
      apply Finset.sum_le_sum
      intro a ha
      have hjNat : j ≤ 2 := by exact_mod_cast hj
      have ha_le_j : a ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      have ha2 : (a : ℕ∞) ≤ (2 : ℕ∞) := by exact_mod_cast le_trans ha_le_j hjNat
      have hjaNat : j - a ≤ 2 := le_trans (Nat.sub_le j a) hjNat
      have hja2 : ((j - a : ℕ) : ℕ∞) ≤ (2 : ℕ∞) := by exact_mod_cast hjaNat
      have hG_bound : ‖iteratedFDeriv ℝ a G q‖ ≤ rightCutoffDerivMajorant c hc a := by
        exact (norm_iteratedFDeriv_comp_fst_le smoothRightCutoff_contDiff
          (by exact_mod_cast ha2) q).trans
          (rightCutoffDerivMajorant_spec c hc ha2 q.1)
      have hR_bound : ‖iteratedFDeriv ℝ (j - a) R q‖ ≤
          boundedWeightJointMajorant Bt (j - a) k := by
        exact boundedWeightJointTerm_iteratedFDeriv_le
          (Hres.coeff_contDiff k) hja2
          (fun i hi => by
            simpa [Bt] using Hres.coeff_bound i k q.1 hi)
      have hchoose : 0 ≤ (j.choose a : ℝ) := Nat.cast_nonneg _
      have hΦ : 0 ≤ rightCutoffDerivMajorant c hc a := rightCutoffDerivMajorant_nonneg c hc a
      have hMaj : 0 ≤ boundedWeightJointMajorant Bt (j - a) k := by
        apply boundedWeightJointMajorant_nonneg_of_Bt_nonneg
        intro i k
        exact mul_nonneg (resolverWeight_nonneg p k) (builtEs_nonneg H i k)
      calc
        (j.choose a : ℝ) * ‖iteratedFDeriv ℝ a G q‖ *
            ‖iteratedFDeriv ℝ (j - a) R q‖
            ≤ (j.choose a : ℝ) * rightCutoffDerivMajorant c hc a *
                boundedWeightJointMajorant Bt (j - a) k := by
              apply mul_le_mul
              · exact mul_le_mul_of_nonneg_left hG_bound hchoose
              · exact hR_bound
              · exact norm_nonneg _
              · exact mul_nonneg hchoose hΦ
        _ = (j.choose a : ℝ) * rightCutoffDerivMajorant c hc a *
              boundedWeightJointMajorant
                (fun i k => intervalNeumannResolverWeight p k * builtEs H i k)
                (j - a) k := by
              rfl
```

The `simp [cutoffResolverTerm, boundedWeightJointTerm, resolverTerm, ...]` line may need adjustment because `cutoffResolverTerm` does not literally mention `boundedWeightJointTerm`; the intended equality is just associativity of

```lean
φ(q.1) * (resolverTimeCoeff p u k q.1 * cosineMode k q.2)
```

with

```lean
φ(q.1) * (boundedWeightJointTerm (resolverTimeCoeff p u) k q).
```

## How to plug into `contDiff_tsum`

Once the signature is changed, the `contDiff_tsum` section should use:

```lean
apply contDiff_tsum
  (𝕜 := ℝ)
  (f := cutoffResolverTerm p u c)
  (v := fun j k => cutoffResolverMajorant p H c hc j k)
```

with:

```lean
· intro k
  exact cutoffResolverTerm_contDiff_two ...

· intro j hj
  exact cutoffResolverMajorant_summable H hc Hphys.value_summable hj

· intro j k q hj
  exact cutoffResolverTerm_iteratedFDeriv_bound H Hphys hc j k q hj
```

For the level-0 heat use case, instantiate

```lean
u := conjugatePicardIter p u₀ 0
```

and pass the floored source data `H` that produces `builtEs H`.

## Bottom line

The replacement is:

```lean
Σ_{a≤j} choose(j,a) * Φ_a * boundedWeightJointMajorant (w_k * builtEs H) (j-a) k
```

not a single collapsed eigenvalue-power expression.  Summability follows immediately from the existing bounded-weight source summability `value_summable`, because the cutoff convolution is a finite sum of scalar multiples of summable sequences.
