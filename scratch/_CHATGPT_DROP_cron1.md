# Q875 / cron1: Mathlib `HasDerivAt` rpow composition lemma

Mathlib version checked: `v4.29.1`

## Answer

For the composition theorem you want, use:

```lean
HasDerivAt.rpow_const
```

File:

```text
Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean
```

It has the shape:

```lean
theorem HasDerivAt.rpow_const
    (hf : HasDerivAt f f' x) (hx : f x ≠ 0 ∨ 1 ≤ p) :
    HasDerivAt (fun y => f y ^ p) (f' * p * f x ^ (p - 1)) x
```

For your positivity hypothesis `0 < f t`, use:

```lean
hf.rpow_const (p := γ) (Or.inl (ne_of_gt hpos))
```

where `hpos : 0 < f t`.

There is also the non-composition base theorem:

```lean
Real.hasDerivAt_rpow_const
```

in the same file:

```text
Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean
```

with shape:

```lean
theorem Real.hasDerivAt_rpow_const {x p : ℝ} (h : x ≠ 0 ∨ 1 ≤ p) :
    HasDerivAt (fun x => x ^ p) (p * x ^ (p - 1)) x
```

## Your exact form

Mathlib gives the derivative as:

```lean
f' * γ * f t ^ (γ - 1)
```

Your desired form:

```lean
γ * f t ^ (γ - 1) * a
```

is the same by commutativity/associativity of real multiplication; use `ring`/`ring_nf` if needed.