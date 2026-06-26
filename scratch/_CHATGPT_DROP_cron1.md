# Q805 / cron1: `valueCosWeight` vs `(1 + λₙ)^m`

Repo inspected: `xiangyazi24/Shen_work`
Ref inspected for source files: `chatgpt-scratch`
Branch written: `chatgpt-scratch`

## Verdict

I did **not** find an existing lemma named

```lean
valueCosWeight_le_one_add_eigenvalue_pow
```

or an obvious already-factored equivalent for

```lean
valueCosWeight m n ≤ (1 + unitIntervalCosineEigenvalue n) ^ m
```

with `m ≤ 2`.

The result is true and should be cheap to add near `valueCosWeight_nonneg` in
`ShenWork/PDE/IntervalResolverSpectralJointC2Concrete.lean`.

## What already exists nearby

In `ShenWork/PDE/IntervalResolverSpectralJointC2Concrete.lean`:

```lean
def valueCosWeight (m n : ℕ) : ℝ :=
  match m with
  | 0 => 1
  | 1 => |(n : ℝ) * Real.pi|
  | _ => unitIntervalCosineEigenvalue n

theorem valueCosWeight_nonneg (m n : ℕ) :
    0 ≤ valueCosWeight m n := by
  ...

theorem cosineMode_iteratedFDeriv_bound
    (n m : ℕ) (y : ℝ) (hm : m ≤ 2) :
    ‖iteratedFDeriv ℝ m (cosineMode n) y‖ ≤ valueCosWeight m n := by
  ...
```

So the file has the weight definition and nonnegativity, but not the desired
`≤ (1 + λₙ)^m` packaging.

## Closest existing proof pattern

`ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean` already uses the
same inequality pattern inside `heatTerm_iteratedFDeriv_global_bound`, but it is
local, not reusable as a `valueCosWeight` lemma.  In particular it proves a local
frequency bound

```lean
have hfreq_le : |(n : ℝ) * Real.pi| ≤ 1 + λ_n := by
  rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) Real.pi_pos.le)]
  unfold_let λ_n; unfold unitIntervalCosineEigenvalue
  nlinarith [sq_nonneg ((n : ℝ) * Real.pi - 1/2)]
```

and then uses

```lean
λ_n ^ i * |(n : ℝ) * Real.pi| ^ (j - i)
  ≤ (1 + λ_n) ^ i * (1 + λ_n) ^ (j - i)
  = (1 + λ_n) ^ j
```

to get the `2^j · (1 + λ_n)^j` Leibniz sum.

There is also a private summability helper in that same file:

```lean
private theorem one_add_eigenvalue_pow_mul_exp_summable
    (m : ℕ) {τ M₀ : ℝ} (hτ : 0 < τ) (hM₀ : 0 ≤ M₀) :
    Summable (fun n : ℕ =>
      (1 + unitIntervalCosineEigenvalue n) ^ m * M₀ *
        Real.exp (-τ * unitIntervalCosineEigenvalue n)) := by
  ...
```

That helps with the final summability majorant, but it does not imply the
`valueCosWeight` pointwise bound directly.

## Suggested lemma

A useful local addition near `valueCosWeight_nonneg`:

```lean
theorem valueCosWeight_le_one_add_eigenvalue_pow
    (m n : ℕ) (hm : m ≤ 2) :
    valueCosWeight m n ≤ (1 + unitIntervalCosineEigenvalue n) ^ m := by
  interval_cases m
  · simp [valueCosWeight]
  · have hfreq_le : |(n : ℝ) * Real.pi| ≤
        1 + unitIntervalCosineEigenvalue n := by
      rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) Real.pi_pos.le)]
      unfold unitIntervalCosineEigenvalue
      nlinarith [sq_nonneg ((n : ℝ) * Real.pi - 1 / 2)]
    simpa [valueCosWeight] using hfreq_le
  · simp [valueCosWeight]
    have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity
    nlinarith [sq_nonneg (unitIntervalCosineEigenvalue n)]
```

Potential tiny adjustment: if `nlinarith` wants the square expanded in the last
case, replace the final line with a short `calc` through `1 + λ ≤ (1 + λ)^2`, or
set `lam := unitIntervalCosineEigenvalue n` first and use `nlinarith` on `lam`.

## Consequence for the proposed heat-term bound

For `j ≤ 2` and `i ≤ j`, the needed factor estimate is exactly:

```lean
λ_n ^ i * valueCosWeight (j - i) n
  ≤ (1 + λ_n) ^ i * (1 + λ_n) ^ (j - i)
  = (1 + λ_n) ^ j
```

where the new lemma handles the `valueCosWeight (j - i) n` part, since
`j - i ≤ j ≤ 2`.  The remaining steps are standard nonnegativity plus
`pow_add`/`Nat.add_sub_cancel'`.

Summing over the Leibniz terms gives

```lean
∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (1 + λ_n)^j
  = 2^j * (1 + λ_n)^j
  ≤ 4 * (1 + λ_n)^j
```

for `j ≤ 2`.  If the target bound is allowed to keep `2^j` instead of absorbing
it into `4`, the proof is even cleaner.
