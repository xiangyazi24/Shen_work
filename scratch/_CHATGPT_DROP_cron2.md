# Q1555 (cron2) — direct-route majorant summability from heat `C⁴` to weak-`H⁴_N` source decay

Static GitHub-connector response only. I did **not** run Lean locally, and I did **not** use Python, code-interpreter, sandbox, or `/mnt/data`.

## Bottom line

For the direct route majorant, the analytic chain should be:

```text
heatSemigroup_contDiff_four
  + heat cosine symmetry / endpoint odd-derivative vanishing
  + strict positive lower bound for the heat profile
  + C⁴ chain rule for x ↦ ν · u(x)^γ
  + weak Neumann H² certificate for g and for g''
  + uniform L¹ bound on g''''
  -> intervalWeakH4Neumann_cosineCoeff_quartic_decay_of_bound
  -> |sourceCoeff_k(t)| ≤ C / (kπ)^4 uniformly for t ≥ c/2
  -> Summable cutoff resolver majorant for j ≤ 2.
```

Important correction: for `j = 2`, **quartic decay `O(k^-4)` is already enough**. You do not need `O(k^{-4-ε})` in the one-dimensional Neumann spectrum calculation.

Indeed,

```text
w_k ~ (μ + λ_k)^-1 = O(k^-2),
(1 + λ_k)^2 = O(k^4),
|srcCoeff_k| = O(k^-4).
```

Thus the product is

```text
O(k^-2) · O(k^4) · O(k^-4) = O(k^-2),
```

and `∑ k^-2` is summable. The `k = 0` mode must be handled separately by a finite bounded-source estimate.

## Existing code anchors

The relevant existing pieces are already very close:

* `heatSemigroup_contDiff_four` in `ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean` gives fixed-positive-time spatial `ContDiff ℝ 4` for the heat cosine series.
* `IntervalWeakH2Neumann` and `intervalWeakH2Neumann_of_contDiffOn` in `ShenWork/PDE/IntervalMildSourceDecayHelper.lean` package the weak Neumann IBP identity.
* `intervalWeakH4Neumann_cosineCoeff_quartic_decay_of_bound` in `ShenWork/PDE/IntervalSourceDecayQuantitative.lean` already proves the quartic coefficient decay from a depth-2 weak-`H²_N` tower:

```lean
hf   : IntervalWeakH2Neumann f
hf'' : IntervalWeakH2Neumann hf.secondDeriv
hB₂  : (∫ x in (0:ℝ)..1, |hf''.secondDeriv x|) ≤ B₂
```

* `intervalResolverLiftR_contDiff_four` in `ShenWork/Paper2/IntervalResolverHighRegularity.lean` wants eigenvalue-weighted source coefficient summability:

```lean
Summable (fun k => unitIntervalCosineEigenvalue k *
  |(intervalNeumannResolverSourceCoeff p u k).re|)
```

* `IntervalHeatResolverDirectJointC2.lean` has the three direct-route analytic holes:

```lean
cutoffResolverTerm_contDiff_two
cutoffResolverMajorant_summable
cutoffResolverTerm_iteratedFDeriv_bound
```

The H⁴ Neumann source chain is the correct way to replace the placeholder majorant in the last two.

## The proof chain in detail

### 1. Build the heat cosine representative at time `t ≥ c/2`

For fixed `t > 0`, define

```text
U_t(x) = ∑' k,
  (Real.exp (-t * λ_k) * heatCoeff u₀ k) * cosineMode k x.
```

Then `heatSemigroup_contDiff_four hu₀_bound ht` gives

```lean
hU_C4 : ContDiff ℝ 4 U_t
```

where `ht : 0 < t`. For the direct route, use `t ≥ c/2` and `hc : 0 < c`, so `ht` follows by `linarith`.

You also need the agreement lemma already used in `IntervalConjugateLevel0BFormSourceOn.lean`:

```lean
hU_agree : ∀ x ∈ Set.Icc (0 : ℝ) 1,
  intervalDomainLift (conjugatePicardIter p u₀ 0 t) x = U_t x
```

from `ShenWork.IntervalPicardIterateRepresentation.hagree_zero`.

### 2. Add heat cosine symmetry lemmas

The cosine representative is even and symmetric about `1`:

```lean
theorem heatCosineRep_even
    (b : ℕ → ℝ) :
    (fun x => ∑' k, b k * cosineMode k (-x)) =
    (fun x => ∑' k, b k * cosineMode k x) := by
  -- `cosineMode k (-x) = cosineMode k x`, then `tsum_congr`.
  sorry

theorem heatCosineRep_reflect_one
    (b : ℕ → ℝ) :
    (fun x => ∑' k, b k * cosineMode k (2 - x)) =
    (fun x => ∑' k, b k * cosineMode k x) := by
  -- `2 - x = -x + 2`; use period 2 plus evenness of cosineMode.
  sorry
```

You do not actually need them in this exact function-equality form; pointwise versions are usually easier:

```lean
hU_even   : ∀ x, U_t (-x) = U_t x
hU_symm1  : ∀ x, U_t (2 - x) = U_t x
hU_period : Function.Periodic U_t 2
```

These are already written inline in `IntervalConjugateLevel0BFormSourceOn.lean`; factor them out.

### 3. Derive odd-derivative endpoint vanishing

From `hU_C4`, `hU_even`, and `hU_symm1`, prove reusable parity lemmas:

```lean
theorem deriv_of_even_is_odd
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (heven : ∀ x, g (-x) = g x) :
    ∀ x, deriv g (-x) = - deriv g x := by
  -- use `deriv_comp_neg`, rewrite by `heven`.
  sorry

theorem deriv_of_odd_is_even
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hodd : ∀ x, g (-x) = - g x) :
    ∀ x, deriv g (-x) = deriv g x := by
  -- use `deriv_comp_neg`, rewrite by `hodd`.
  sorry

theorem odd_zero
    {g : ℝ → ℝ} (hodd : ∀ x, g (-x) = - g x) :
    g 0 = 0 := by
  have h := hodd 0
  simp at h
  linarith
```

For the right endpoint, use the reflected version:

```lean
theorem deriv_reflect_one_antisymm
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hsymm : ∀ x, g (2 - x) = g x) :
    ∀ x, deriv g (2 - x) = - deriv g x := by
  -- use `deriv_comp_const_sub` with `a = 2`.
  sorry
```

The resulting endpoint facts for `U_t` are:

```lean
deriv U_t 0 = 0
deriv U_t 1 = 0
deriv (deriv (deriv U_t)) 0 = 0
deriv (deriv (deriv U_t)) 1 = 0
```

For the source `G_t = ν · U_t^γ`, it is better to derive symmetry of `G_t` first and then apply the same parity chain to `G_t` directly.

### 4. Positivity: fixed-slice vs uniform majorant

For a **fixed slice**, pointwise positivity on `[0,1]` plus symmetry/periodicity is enough to make the smooth cosine representative globally nonzero:

```lean
hU_pos_Icc : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < U_t x
hU_pos_all : ∀ x : ℝ, 0 < U_t x
hU_ne      : ∀ x : ℝ, U_t x ≠ 0
```

This is enough for the local chain rule

```lean
hU_C4.rpow_const_of_ne hU_ne
```

and hence enough to construct the weak-`H⁴_N` certificate for this fixed `t`.

For the **direct majorant summability with an `iSup` over `t ≥ c/2`**, fixed-slice positivity is not enough. You need a quantitative lower bound:

```lean
∃ m_c : ℝ, 0 < m_c ∧
  ∀ t, c / 2 ≤ t → ∀ x ∈ Set.Icc (0 : ℝ) 1,
    m_c ≤ intervalDomainLift (conjugatePicardIter p u₀ 0 t) x
```

or an equivalent lower bound for `U_t`. This is essential when `γ` is an arbitrary real, because fourth derivatives of `u^γ` contain powers down to `u^(γ - 4)`. Pointwise positivity gives `ContDiff`; it does **not** give a uniform constant for the `iSup` bound.

### 5. Build `C⁴` for the power source

Define

```lean
G_t : ℝ → ℝ := fun x => p.ν * U_t x ^ p.γ
```

Then:

```lean
have hG_C4 : ContDiff ℝ 4 G_t := by
  show ContDiff ℝ 4 (fun x => p.ν * U_t x ^ p.γ)
  exact contDiff_const.mul (hU_C4.rpow_const_of_ne hU_ne)
```

This answers the question “is `contDiff_four` of `u` sufficient?”:

* For **fixed-slice `C⁴` of `ν*u^γ`**, yes, provided `u` is nonzero/positive on the relevant ambient neighborhood.
* For **weak-`H⁴_N`**, not by itself: you also need the Neumann endpoint conditions for `G_t'` and `G_t'''`.
* For **uniform direct-route summability**, still not by itself: you need quantitative uniform bounds on the derivatives and a uniform positive lower bound.

### 6. Construct the depth-2 weak Neumann tower

Current `intervalWeakH4Neumann_cosineCoeff_quartic_decay_of_bound` does not require a separate `IntervalWeakH4Neumann` structure. It represents weak `H⁴_N` as a pair:

```lean
hf   : IntervalWeakH2Neumann f
hf'' : IntervalWeakH2Neumann hf.secondDeriv
```

I would still add this wrapper for clarity:

```lean
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity
import ShenWork.Paper2.IntervalResolverHighRegularity
import ShenWork.PDE.IntervalSourceDecayQuantitative
import ShenWork.Paper2.IntervalHeatResolverDirectJointC2

open MeasureTheory Set Filter
open scoped Topology BigOperators

noncomputable section

namespace ShenWork.Paper2.HeatResolverDirectJointC2

open ShenWork.PDE.IntervalMildSourceDecayHelper

/-- A depth-2 weak Neumann tower: weak `H²_N` for `f`, and weak `H²_N`
for the chosen weak second derivative. This is the practical `H⁴_N` object used
by `intervalWeakH4Neumann_cosineCoeff_quartic_decay_of_bound`. -/
structure IntervalWeakH4Neumann (f : ℝ → ℝ) where
  h2 : IntervalWeakH2Neumann f
  h2_second : IntervalWeakH2Neumann h2.secondDeriv

end ShenWork.Paper2.HeatResolverDirectJointC2
```

The robust constructor should avoid depending on the junk extension derivatives of `intervalDomainLift` outside `[0,1]`. Instead, use a smooth representative `G_t` and an agreement proof on `[0,1]`:

```lean
/-- Preferred constructor shape.

`f` is the actual source used by resolver coefficients, while `G` is the smooth
cosine representative.  They only need to agree on `[0,1]`, because all weak
IBP identities and cosine coefficients integrate over `[0,1]`. -/
noncomputable def intervalWeakH4Neumann_of_smooth_agree_on_Icc
    {f G : ℝ → ℝ}
    (hG_C4 : ContDiff ℝ 4 G)
    (hfg : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x = G x)
    (hG1_0 : deriv G 0 = 0)
    (hG1_1 : deriv G 1 = 0)
    (hG3_0 : deriv (deriv (deriv G)) 0 = 0)
    (hG3_1 : deriv (deriv (deriv G)) 1 = 0) :
    IntervalWeakH4Neumann f := by
  -- Intended implementation:
  -- 1. Build `hf : IntervalWeakH2Neumann f` with
  --      secondDeriv := deriv (deriv G)
  --    not `deriv (deriv f)`.  The weak cosine Laplacian follows from
  --    smooth IBP for `G` plus integral agreement `f = G` on `[0,1]`.
  -- 2. Build `hf'' : IntervalWeakH2Neumann hf.secondDeriv`, i.e. weak H² for
  --      deriv (deriv G),
  --    using `ContDiffOn ℝ 2 (deriv (deriv G))` from `hG_C4`, endpoint data
  --    `G'''(0)=G'''(1)=0`, and `intervalWeakH2Neumann_of_contDiffOn`.
  -- 3. Return `{ h2 := hf, h2_second := hf'' }`.
  sorry
```

This constructor is cleaner than repeatedly using `intervalWeakH2Neumann_of_contDiffOn` on the actual zero/junk extension, because the fourth-order tower should use the smooth cosine representative as the differentiable object.

### 7. Uniform fourth-derivative `L¹` bound

For the quartic coefficient theorem at a fixed `t`, you can simply extract

```lean
obtain ⟨B₂, hB₂_nonneg, hB₂⟩ := H4.h2_second.second_abs_integral_bound
```

For the direct route, this is insufficient, because the majorant needs a single constant before the final `Summable`. Add the uniform version:

```lean
theorem powerSource_fourth_abs_integral_bound_on_halfline
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c m M : ℝ}
    (hc : 0 < c)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hm : 0 < m)
    (hlo : ∀ t, c / 2 ≤ t → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      m ≤ intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    (hhi : ∀ t, c / 2 ≤ t → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 t) x ≤ M) :
    ∃ B4 : ℝ, 0 ≤ B4 ∧
      ∀ t, c / 2 ≤ t →
        -- `G_t = ν · U_t^γ`, with H4 tower built from the smooth representative
        -- chosen above.
        ∫ x in (0 : ℝ)..1,
          |deriv (deriv (deriv (deriv
             (fun x => p.ν *
               (intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) ^ p.γ)))) x| ≤ B4 := by
  -- Intended proof:
  -- * Uniform heat derivative bounds for orders 0..4 on `t ≥ c/2`:
  --     ‖∂ₓ^r U_t‖∞ ≤ C_r(c,M₀)
  --   from `exp(-tλ_k) ≤ exp(-(c/2)λ_k)` and summability of
  --     `(kπ)^r exp(-(c/2)λ_k)`.
  -- * Explicit fourth derivative formula for `ν · u^γ`:
  --     ν * [ γ u^(γ-1) u''''
  --           + 4γ(γ-1) u^(γ-2) u' u'''
  --           + 3γ(γ-1) u^(γ-2) (u'')^2
  --           + 6γ(γ-1)(γ-2) u^(γ-3) (u')^2 u''
  --           + γ(γ-1)(γ-2)(γ-3) u^(γ-4) (u')^4 ]
  -- * Bound all powers `u^(γ-r)` using `m ≤ u ≤ M`.
  -- * The interval has length 1, so an `L∞` bound gives the desired `L¹` bound.
  sorry
```

This is the main new analytic estimate needed for the `iSup` route.

### 8. Apply quartic coefficient decay uniformly

After constructing the tower `H4_t : IntervalWeakH4Neumann source_t` and the uniform `B4`, the coefficient theorem gives, for `k ≥ 1`:

```lean
have hdecay_t :
    |cosineCoeffs source_t k| ≤ 2 * B4 / ((k : ℝ) * Real.pi) ^ 4 :=
  ShenWork.IntervalSourceDecayQuantitative
    .intervalWeakH4Neumann_cosineCoeff_quartic_decay_of_bound
      H4_t.h2 H4_t.h2_second (hB4 t ht) k hk
```

Then rewrite resolver source coefficients:

```lean
have hre_eq : ∀ k,
    (ShenWork.PDE.intervalNeumannResolverSourceCoeff p w k).re =
      cosineCoeffs (fun x => p.ν * intervalDomainLift w x ^ p.γ) k := by
  intro k
  simp only [ShenWork.PDE.intervalNeumannResolverSourceCoeff,
    cosineCoeffs, Complex.ofReal_re]
```

This is the bridge from source H⁴ to the resolver majorant.

### 9. Summability of the direct majorant

The final summability lemma should have this shape:

```lean
theorem cutoffResolverMajorant_summable_from_uniform_H4_source
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c B4 : ℝ}
    (hc : 0 < c)
    (hB4_nonneg : 0 ≤ B4)
    (hsrc_decay : ∀ t, c / 2 ≤ t → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs
        (fun x => p.ν * intervalDomainLift (conjugatePicardIter p u₀ 0 t) x ^ p.γ) k|
        ≤ 2 * B4 / ((k : ℝ) * Real.pi) ^ 4)
    {j : ℕ} (hj : (j : ℕ∞) ≤ (2 : ℕ∞)) :
    Summable (fun k : ℕ =>
      (1 / (p.μ + unitIntervalCosineEigenvalue k)) *
      (1 + unitIntervalCosineEigenvalue k) ^ j *
      -- source coefficient envelope
      (if k = 0 then 1 else 2 * B4 / ((k : ℝ) * Real.pi) ^ 4)) := by
  -- For k = 0: one finite term.
  -- For k ≥ 1:
  --   1/(μ+λ_k) ≤ 1/λ_k = 1/(kπ)^2
  --   (1+λ_k)^j ≤ C_j * (kπ)^(2j), since j ≤ 2
  --   source ≤ C/(kπ)^4
  -- Product ≤ C'_j / k^(6 - 2j).
  -- For j=2, exponent is 2; summable.
  sorry
```

This is the direct answer to the `Summable(fun k => iSup_q ‖D^j(cutoffResolverTerm_k)(q)‖)` target. The `iSup_q` estimate is obtained by the separate derivative-bound lemma:

```text
‖D^j cutoffResolverTerm_k(q)‖
  ≤ C_cutoff_j(c) · (1/(μ+λ_k)) · (1+λ_k)^j · sourceEnvelope_k.
```

Then `iSup` is bounded by the same right-hand side because the right-hand side is independent of `q`.

## Minimal intermediate lemmas to add

The minimal implementation order I recommend is:

1. **Factor heat cosine symmetry helpers**
   ```lean
   cosineMode_neg
   cosineMode_add_two
   cosineMode_reflect_one
   heatCosineRep_even
   heatCosineRep_periodic
   heatCosineRep_reflect_one
   ```

2. **Factor derivative parity helpers**
   ```lean
   deriv_of_even_is_odd
   deriv_of_odd_is_even
   deriv_reflect_one_antisymm
   odd_zero
   reflected_odd_at_one_zero
   ```

3. **Smooth-agreement weak-H² constructor**
   ```lean
   intervalWeakH2Neumann_of_smooth_agree_on_Icc
   ```
   This should let the weak second derivative be `deriv (deriv G)` even when the actual source is a junk/zero extension outside `[0,1]`.

4. **Smooth-agreement weak-H⁴ constructor**
   ```lean
   intervalWeakH4Neumann_of_smooth_agree_on_Icc
   ```
   This packages `hf` and `hf''` for the existing quartic decay theorem.

5. **Power-source C⁴ and Neumann endpoint lemma**
   ```lean
   powerSource_smooth_C4_of_heat_C4_pos
   powerSource_odd_derivatives_vanish_of_heat_symmetry
   powerSource_intervalWeakH4Neumann_of_heatSemigroup
   ```

6. **Uniform halfline derivative bounds for heat**
   ```lean
   heatSemigroup_spatial_deriv_bound_on_halfline
   heatSemigroup_spatial_deriv_bounds_0_to_4_on_halfline
   ```

7. **Uniform fourth-source bound**
   ```lean
   powerSource_fourth_abs_integral_bound_on_halfline
   ```

8. **Uniform quartic source coefficient envelope**
   ```lean
   powerSource_cosineCoeff_quartic_decay_uniform_on_halfline
   ```

9. **Direct resolver majorant summability**
   ```lean
   cutoffResolverMajorant_summable_from_uniform_H4_source
   cutoffResolverTerm_iteratedFDeriv_bound_from_uniform_H4_source
   ```

## Answer to the direct question

`ContDiff ℝ 4` of the heat profile `u` is **sufficient for the fixed-slice C⁴ chain rule** for `ν*u^γ`, assuming the heat profile is positive/nonzero. It is **not sufficient by itself** for the direct-route summability claim.

You additionally need:

1. Neumann endpoint data for the source: `G_t'(0)=G_t'(1)=0` and `G_t'''(0)=G_t'''(1)=0`.
2. A weak-H² certificate for `G_t` and a weak-H² certificate for `G_t''`.
3. A uniform `L¹` bound on `G_t''''` for `t ≥ c/2`.
4. A uniform positive lower bound for `u` if `γ` is an arbitrary real, since fourth derivatives of `u^γ` involve powers as low as `u^(γ-4)`.

Once those are in place, `intervalWeakH4Neumann_cosineCoeff_quartic_decay_of_bound` gives the needed `O(k^-4)` source coefficient decay, and that is enough to make the direct resolver majorant summable for all joint derivative orders `j ≤ 2`.
