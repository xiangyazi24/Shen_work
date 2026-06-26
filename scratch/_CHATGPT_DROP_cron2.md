# Q793 (cron2) — `cosineMode_iteratedFDeriv_bound` and `valueCosWeight`

Static repo inspection only; I did not run a Lean build.

File inspected:

```text
ShenWork/PDE/IntervalResolverSpectralJointC2Concrete.lean
```

## `valueCosWeight`

Exact definition:

```lean
def valueCosWeight (m n : ℕ) : ℝ :=
  match m with
  | 0 => 1
  | 1 => |(n : ℝ) * Real.pi|
  | _ => unitIntervalCosineEigenvalue n
```

There is also the nonnegativity helper:

```lean
theorem valueCosWeight_nonneg (m n : ℕ) :
    0 ≤ valueCosWeight m n := by
  ...
```

Interpretation for the value cosine factor `cosineMode n y`:

```text
m = 0 : bound by 1
m = 1 : bound by |nπ|
m = 2 : bound by λ_n = unitIntervalCosineEigenvalue n = (nπ)^2
```

The wildcard case `_` is used as “order ≥ 2”, but every theorem here is constrained by `m ≤ 2`, so it is effectively the `m = 2` case.

## `cosineMode_iteratedFDeriv_bound`

Exact signature and bound:

```lean
theorem cosineMode_iteratedFDeriv_bound
    (n m : ℕ) (y : ℝ) (hm : m ≤ 2) :
    ‖iteratedFDeriv ℝ m (cosineMode n) y‖ ≤ valueCosWeight m n := by
  ...
```

The proof splits by `interval_cases m`:

```lean
m = 0:
  ‖cosineMode n y‖ ≤ 1

m = 1:
  ‖D cos(nπy)‖ ≤ |nπ|
  using cosineMode_deriv and Real.abs_sin_le_one

m = 2:
  ‖D² cos(nπy)‖ ≤ unitIntervalCosineEigenvalue n
  using cosineMode_second_deriv and Real.abs_cos_le_one
```

The relevant part of the proof is:

```lean
theorem cosineMode_iteratedFDeriv_bound
    (n m : ℕ) (y : ℝ) (hm : m ≤ 2) :
    ‖iteratedFDeriv ℝ m (cosineMode n) y‖ ≤ valueCosWeight m n := by
  interval_cases m
  · rw [norm_iteratedFDeriv_zero]
    unfold cosineMode valueCosWeight
    exact Real.abs_cos_le_one _
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    simp [valueCosWeight, cosineMode_deriv]
    calc (n : ℝ) * |Real.pi| * |Real.sin ((n : ℝ) * Real.pi * y)|
        ≤ (n : ℝ) * |Real.pi| * 1 := by
          exact mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _)
            (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
      _ = (n : ℝ) * |Real.pi| := by ring
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hiter : iteratedDeriv 2 (cosineMode n) y =
        deriv (fun z : ℝ => deriv (cosineMode n) z) y := by
      norm_num [iteratedDeriv_succ']
    rw [hiter, cosineMode_second_deriv]
    rw [Real.norm_eq_abs]
    have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity
    calc |-(((n : ℝ) * Real.pi) ^ 2 * cosineMode n y)|
        = unitIntervalCosineEigenvalue n * |cosineMode n y| := by
          rw [abs_neg, abs_mul,
            abs_of_nonneg (sq_nonneg ((n : ℝ) * Real.pi))]
          rfl
      _ ≤ unitIntervalCosineEigenvalue n * 1 := by
          exact mul_le_mul_of_nonneg_left
            (by unfold cosineMode; exact Real.abs_cos_le_one _) hlam
      _ = valueCosWeight 2 n := by
          simp [valueCosWeight]
```

## How `valueCosWeight` is used in the separated-product bound

For a separated mode term

```lean
boundedWeightJointTerm c n q = c n q.1 * cosineMode n q.2
```

the product-bound majorant is packaged in `IntervalResolverJointC2Physical.lean` as:

```lean
def boundedWeightJointMajorant (Bt : ℕ → ℕ → ℝ) (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * Bt i n * valueCosWeight (k - i) n
```

The theorem using it is:

```lean
theorem boundedWeightJointTerm_iteratedFDeriv_le
    {c : ℕ → ℝ → ℝ} {Bt : ℕ → ℕ → ℝ} {n k : ℕ} {q : ℝ × ℝ}
    (hc : ContDiff ℝ (2 : ℕ∞) (c n)) (hk : (k : ℕ∞) ≤ (2 : ℕ∞))
    (hBt : ∀ i, i ≤ 2 → ‖iteratedFDeriv ℝ i (c n) q.1‖ ≤ Bt i n) :
    ‖iteratedFDeriv ℝ k (boundedWeightJointTerm c n) q‖ ≤
      boundedWeightJointMajorant Bt k n := by
  ...
```

Inside the proof, after `norm_iteratedFDeriv_mul_le`, the cosine/spatial side is bounded exactly by `valueCosWeight`:

```lean
have hspace :
    ‖iteratedFDeriv ℝ (k - i)
      (fun q : ℝ × ℝ => cosineMode n q.2) q‖ ≤
      valueCosWeight (k - i) n :=
  (norm_iteratedFDeriv_comp_snd_le hcos₀ hkiTop q).trans
    (cosineMode_iteratedFDeriv_bound n (k - i) q.2 (by omega))
```

The time/coefficient side is bounded by `Bt i n`:

```lean
have htime :
    ‖iteratedFDeriv ℝ i (fun q : ℝ × ℝ => c n q.1) q‖ ≤ Bt i n :=
  (norm_iteratedFDeriv_comp_fst_le hc hiTop q).trans
    (hBt i (le_trans hik hkNat))
```

Then each Leibniz summand is bounded by:

```lean
(k.choose i : ℝ) * Bt i n * valueCosWeight (k - i) n
```

and summing over `i ∈ Finset.range (k + 1)` gives `boundedWeightJointMajorant Bt k n`.

## How this appears in `IntervalResolverSpectralJointC2Concrete.lean`

The concrete value-side cutoff proof uses the same mechanism.  In

```lean
cutoffValueTerm_restartSmoothCutoff_iteratedFDeriv_bound_of_mem_slab
```

a cosine derivative factor is first bounded by:

```lean
have hcosNorm :
    ‖iteratedFDeriv ℝ (k - i)
      (fun q : ℝ × ℝ => cosineMode n q.2) q‖ ≤
    valueCosWeight (k - i) n := by
  exact (norm_iteratedFDeriv_comp_snd_le hcos₀ hkiTop q).trans
    (cosineMode_iteratedFDeriv_bound n (k - i) q.2 (by omega))
```

Then the coefficient derivative and the cosine weight are paired:

```lean
have hcore :
    ‖iteratedFDeriv ℝ (i - j)
      (fun t : ℝ => localRestartCoeff a₀ a (t - offset) n) q.1‖ *
      valueCosWeight (k - i) n ≤
    restartCoeffCoreMajorant a₀ src
      (restartSlabMin offset s) (restartSlabMax offset s) n := by
  exact shiftedLocalRestartCoeff_valueWeight_le_core src
    hτnonneg hτmin hτmax (by omega)
```

So `valueCosWeight` is the spatial-frequency budget for the cosine factor.  The separated-product proof moves all `x`-derivative growth into this weight, then proves the coefficient side times this weight is controlled by the relevant mode majorant.

## Relevance to `heatTerm`

For the heat term

```lean
heatTerm u₀ n q =
  (Real.exp (-q.1 * unitIntervalCosineEigenvalue n) *
    cosineCoeffs (intervalDomainLift u₀) n) * cosineMode n q.2
```

the same bound pattern is:

```lean
∑ i ∈ Finset.range (k + 1),
  (k.choose i : ℝ) * Bt i n * valueCosWeight (k - i) n
```

where `Bt i n` bounds the `i`-th time derivative of

```lean
fun t => Real.exp (-t * unitIntervalCosineEigenvalue n) *
  cosineCoeffs (intervalDomainLift u₀) n
```

This is the repo-native separated-product formulation.  Collapsing the finite sum into a single `(1 + λ_n)^k` expression is an extra algebraic majorization step, not what `cosineMode_iteratedFDeriv_bound` itself provides.
