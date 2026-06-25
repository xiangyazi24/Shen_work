# Q489 (cron2): is `deriv (deriv (chemFluxFun ...)) 0 = 0` true for cosine heat/resolver profiles?

## Executive verdict

For **smooth global cosine-series representatives** `U,V : ℝ → ℝ`, the statement is TRUE:

```lean
deriv (deriv (chemFluxFun β U V)) 0 = 0
```

provided `U` and `V` are even about `0`, `V` is smooth enough, and the denominator is positive. The reason is exactly the parity argument:

```text
U even,
V even,
V' odd,
(1+V)^β even,
φ := U * V' / (1+V)^β odd,
φ' even,
φ'' odd,
φ''(0) = 0.
```

Your later worry that `φ''(0)` might be generically nonzero is correct for **general non-even Neumann data**, but not for genuine cosine-series/even-reflection data. A quick Taylor expansion confirms this:

```text
U(x) = U₀ + U₂ x²/2 + O(x⁴)
V(x) = V₀ + V₂ x²/2 + V₄ x⁴/24 + O(x⁶)
V'(x) = V₂ x + V₄ x³/6 + O(x⁵)
(1+V(x))^{-β} = Q₀ + Q₂ x²/2 + O(x⁴)
φ(x) = U(x) V'(x) (1+V(x))^{-β}
     = (U₀ V₂ Q₀) x + O(x³).
```

There is no `x²` term, so `φ''(0)=0`. `φ'(0)=U₀ V₂/(1+V₀)^β` can be nonzero; that is not a contradiction. The second derivative still vanishes because `φ` is odd.

The major Lean caution is that this is a theorem about the **global cosine representatives**, not about the zero-extension functions `intervalDomainLift u` and `intervalDomainLift v` unless those lifts literally are the global cosine representatives. For ordinary positive heat/resolver slices, `intervalDomainLift u` is zero outside `[0,1]`, hence it is not the global cosine series and is not even/smooth across `0`. The repo already distinguishes these two routes:

* `chemDivLift_neumann_bc` for `chemDivLift = intervalDomainLift (...)` is now discharged by zero-extension endpoint derivative lemmas. This proves only the two-sided Mathlib endpoint derivative/junk value.
* The real weak-H² one-sided Neumann limits for the chem-div source should be proved by comparing `chemDivLift` on the interior with a **smooth global cosine representative** `F = deriv (chemFluxFun β Ucos Vcos)`, then using parity to show `deriv F 0 = 0` and continuity to get the one-sided limit.

So the clean Lean approach is:

```text
Do NOT try to prove parity for `intervalDomainLift u`.
Define/use global cosine representatives `Ucos`, `Vcos`.
Prove `Even Ucos` and `Even Vcos` by `tsum_congr` + `cos_neg`.
Prove a reusable parity lemma for `chemFluxFun`.
Use it to show `deriv (deriv (chemFluxFun β Ucos Vcos)) 0 = 0`.
Transfer to `chemDivLift` only on `Ioo/Icc` by equality with the global representative, and use zero-extension only for the endpoint point-derivative conjuncts.
```

## What the repo currently has

`IntervalChemDivSpatialC2.lean` defines:

```lean
/-- The chemotaxis flux function whose spatial derivative is the chemDiv source.
`φ(y) = lift(u)(y) · deriv(lift(v))(y) / (1 + lift(v)(y))^β` -/
def chemFluxFun (β : ℝ) (u v : ℝ → ℝ) (y : ℝ) : ℝ :=
  u y * deriv v y / (1 + v y) ^ β
```

It also has global smoothness lemmas:

```lean
theorem chemFlux_contDiff_three
    {β : ℝ} {u v : ℝ → ℝ}
    (hu : ContDiff ℝ 4 u)
    (hv : ContDiff ℝ 4 v)
    (hv_pos : ∀ x, (0 : ℝ) < 1 + v x)
    (hβnn : 0 ≤ β) :
    ContDiff ℝ 3 (chemFluxFun β u v)

theorem chemFluxDeriv_contDiff_two
    {β : ℝ} {u v : ℝ → ℝ}
    (hu : ContDiff ℝ 4 u) (hv : ContDiff ℝ 4 v)
    (hv_pos : ∀ x, (0 : ℝ) < 1 + v x) (hβnn : 0 ≤ β) :
    ContDiff ℝ 2 (deriv (chemFluxFun β u v))
```

and an agreement lemma for the interval source:

```lean
theorem chemDivLift_contDiffOn_two_of_global
    {p : CM2Params} {u v : intervalDomainPoint → ℝ}
    (hu : ContDiff ℝ 4 (intervalDomainLift u))
    (hv : ContDiff ℝ 4 (intervalDomainLift v))
    (hv_pos : ∀ x, (0 : ℝ) < 1 + intervalDomainLift v x) :
    ContDiffOn ℝ 2 (chemDivLift p u v) (Icc (0 : ℝ) 1)
```

But note the issue: for positive heat/resolver slices, the hypotheses

```lean
ContDiff ℝ 4 (intervalDomainLift u)
ContDiff ℝ 4 (intervalDomainLift v)
```

are generally false because `intervalDomainLift` is the zero-extension and usually jumps at the endpoints. The **global C⁴ object** is the cosine-series representative, not `intervalDomainLift`.

The same file now has:

```lean
theorem chemDivLift_neumann_bc
    (p : CM2Params) (u v : intervalDomainPoint → ℝ) :
    deriv (chemDivLift p u v) 0 = 0 ∧
    deriv (chemDivLift p u v) 1 = 0 := by
  simp only [chemDivLift]
  exact ⟨ShenWork.intervalDomainLift_deriv_at_zero_eq_zero _,
    ShenWork.intervalDomainLift_deriv_at_one_eq_zero _⟩
```

That theorem is about point derivatives of zero-extensions. It is not the same as the parity theorem for `chemFluxFun` on global cosine representatives.

## Verification by Taylor expansion

Let `U,V` be smooth and even about `0`. Then all odd derivatives of `U,V` at `0` vanish, and near `0`:

```text
U(x) = U₀ + U₂ x²/2 + U₄ x⁴/24 + ...
V(x) = V₀ + V₂ x²/2 + V₄ x⁴/24 + ...
```

Then:

```text
V'(x) = V₂ x + V₄ x³/6 + ...
Q(x) := (1+V(x))^{-β} = Q₀ + Q₂ x²/2 + ...
φ(x) := U(x) V'(x) Q(x)
      = U₀ V₂ Q₀ x + (cubic terms) + ...
```

So:

```text
φ'(0)  = U₀ V₂ Q₀      -- can be nonzero
φ''(0) = 0             -- because no quadratic term
```

Concrete sanity check:

```text
U(x) = 1,
V(x) = cos(πx),
β = 0.

φ(x) = V'(x) = -π sin(πx).
φ'(0) = -π² ≠ 0.
φ''(0) = π³ sin(0) = 0.
```

So the requested value is zero for smooth cosine profiles. What can be nonzero is `deriv (chemFluxFun ...) 0`, not `deriv (deriv (chemFluxFun ...)) 0`.

## Counterexample outside the cosine/even class

The statement is false if you only assume first Neumann data and insufficient parity. For example, with `β = 0`, `U(x)=1`, and

```text
V(x) = 1 + x² + x³
```

we still have `V'(0)=0`, but

```text
φ(x) = V'(x) = 2x + 3x²,
φ''(0) = 6 ≠ 0.
```

So the vanishing is not a consequence of `V'(0)=0` alone. It needs even-reflection/odd-derivative vanishings, or equivalently enough cosine-series parity.

## Why the parity is global for cosine series

The concern “the global function may not have the same parity beyond `[-1,1]`” is not a problem if the global function is literally defined by the Neumann cosine series

```lean
fun x => ∑' k, a k * Real.cos ((k : ℝ) * Real.pi * x)
```

Each term is globally even about `0`:

```lean
Real.cos ((k : ℝ) * Real.pi * (-x)) = Real.cos (-((k : ℝ) * Real.pi * x))
                                  = Real.cos ((k : ℝ) * Real.pi * x)
```

and globally even about `1` as well:

```text
cos(kπ(1+h)) = (-1)^k cos(kπh) = cos(kπ(1-h)).
```

So if the sum is defined as a global `tsum`, the parity is global by `tsum_congr`. The function is also `2`-periodic. The only way parity fails is if you replace the global cosine representative by the interval zero-extension `intervalDomainLift`.

## Recommended Lean route

### Step 1: define local/global parity helpers

Mathlib may already have some parity API around `Even`/`Odd`; if that is inconvenient in v4.29.1, use explicit predicates:

```lean
def EvenAtZero (f : ℝ → ℝ) : Prop := ∀ x, f (-x) = f x
def OddAtZero  (f : ℝ → ℝ) : Prop := ∀ x, f (-x) = - f x
```

Useful lemmas:

```lean
theorem deriv_odd_of_evenAtZero
    {f : ℝ → ℝ}
    (hf_even : EvenAtZero f)
    (hf_diff : ∀ x, DifferentiableAt ℝ f x) :
    OddAtZero (deriv f) := by
  -- Differentiate `f (-x) = f x`.
  -- Expected result: `deriv f (-x) = - deriv f x`, equivalently oddness.
  sorry

theorem deriv_even_of_oddAtZero
    {f : ℝ → ℝ}
    (hf_odd : OddAtZero f)
    (hf_diff : ∀ x, DifferentiableAt ℝ f x) :
    EvenAtZero (deriv f) := by
  -- Differentiate `f (-x) = - f x`.
  -- Expected result: `deriv f (-x) = deriv f x`.
  sorry

theorem deriv_at_zero_eq_zero_of_evenAtZero
    {f : ℝ → ℝ}
    (hf_even : EvenAtZero f)
    (hf_diff0 : DifferentiableAt ℝ f 0) :
    deriv f 0 = 0 := by
  -- If f is even and differentiable at 0, compare the derivative from x and -x.
  sorry
```

Then:

```lean
theorem second_deriv_at_zero_eq_zero_of_oddAtZero
    {f : ℝ → ℝ}
    (hf_odd : OddAtZero f)
    (hf_C2 : ContDiff ℝ 2 f) :
    deriv (deriv f) 0 = 0 := by
  have hdf_even : EvenAtZero (deriv f) :=
    deriv_even_of_oddAtZero hf_odd (fun x => (hf_C2.differentiable (by norm_num)).differentiableAt)
  exact deriv_at_zero_eq_zero_of_evenAtZero hdf_even
    ((hf_C2.deriv (by norm_num)).differentiable (by norm_num)).differentiableAt
```

The exact `ContDiff.differentiable` calls may need minor v4.29.1 adjustment, but this is the right proof skeleton.

### Step 2: prove cosine-series evenness

For a global cosine series:

```lean
def cosineSeries (a : ℕ → ℝ) : ℝ → ℝ :=
  fun x => ∑' k, a k * Real.cos ((k : ℝ) * Real.pi * x)
```

prove:

```lean
theorem cosineSeries_evenAtZero (a : ℕ → ℝ) :
    EvenAtZero (cosineSeries a) := by
  intro x
  unfold cosineSeries
  apply tsum_congr
  intro k
  simp [mul_assoc, Real.cos_neg]
```

For the endpoint `1`, use a shifted version:

```lean
def EvenAtOne (f : ℝ → ℝ) : Prop := ∀ h, f (1 - h) = f (1 + h)
```

and prove it termwise from `cos(kπ(1±h))`.

### Step 3: prove `chemFluxFun` is odd from even inputs

Assume `U,V` are global smooth cosine representatives:

```lean
theorem chemFluxFun_oddAtZero_of_even
    {β : ℝ} {U V : ℝ → ℝ}
    (hU_even : EvenAtZero U)
    (hV_even : EvenAtZero V)
    (hV_diff : ∀ x, DifferentiableAt ℝ V x)
    (hden_pos : ∀ x, 0 < 1 + V x) :
    OddAtZero (chemFluxFun β U V) := by
  intro x
  unfold chemFluxFun
  have hVderiv_odd : deriv V (-x) = - deriv V x :=
    deriv_odd_of_evenAtZero hV_even hV_diff x
  have hden_even : (1 + V (-x)) ^ β = (1 + V x) ^ β := by
    rw [hV_even x]
  rw [hU_even x, hVderiv_odd, hden_even]
  ring
```

No direct flux expansion is needed.

### Step 4: the target theorem for global cosine representatives

```lean
theorem chemFluxFun_second_deriv_zero_at_zero_of_even
    {β : ℝ} {U V : ℝ → ℝ}
    (hU_even : EvenAtZero U)
    (hV_even : EvenAtZero V)
    (hU_C4 : ContDiff ℝ 4 U)
    (hV_C4 : ContDiff ℝ 4 V)
    (hden_pos : ∀ x, 0 < 1 + V x)
    (hβnn : 0 ≤ β) :
    deriv (deriv (chemFluxFun β U V)) 0 = 0 := by
  have hodd : OddAtZero (chemFluxFun β U V) :=
    chemFluxFun_oddAtZero_of_even hU_even hV_even
      (fun x => (hV_C4.differentiable (by norm_num)).differentiableAt) hden_pos
  exact second_deriv_at_zero_eq_zero_of_oddAtZero hodd
    ((chemFlux_contDiff_three hU_C4 hV_C4 hden_pos hβnn).of_le (by norm_num))
```

This is the lemma you want for the heat semigroup/resolver global representatives.

## How to use this for `chemDivLift` / weak-H²

Do not set `U = intervalDomainLift u` unless that lift is truly the global cosine representative. Instead, carry explicit global representatives:

```lean
Ucos : ℝ → ℝ
Vcos : ℝ → ℝ
hU_eq : Set.EqOn (intervalDomainLift u) Ucos (Set.Icc 0 1)
hV_eq : Set.EqOn (intervalDomainLift v) Vcos (Set.Icc 0 1)
hU_even : EvenAtZero Ucos
hV_even : EvenAtZero Vcos
hU_C4 : ContDiff ℝ 4 Ucos
hV_C4 : ContDiff ℝ 4 Vcos
hden_pos : ∀ x, 0 < 1 + Vcos x
```

Then prove the smooth global flux fact:

```lean
have hF0 : deriv (deriv (chemFluxFun p.β Ucos Vcos)) 0 = 0 :=
  chemFluxFun_second_deriv_zero_at_zero_of_even hU_even hV_even hU_C4 hV_C4 hden_pos p.hβ
```

and use equality on the open interior to get the genuine one-sided limit:

```lean
Tendsto (deriv (chemDivLift p u v)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
```

by eventual derivative agreement on `Ioo 0 1` plus continuity of

```lean
deriv (deriv (chemFluxFun p.β Ucos Vcos))
```

at `0` and `hF0`.

The endpoint point derivative conjuncts

```lean
deriv (chemDivLift p u v) 0 = 0
```

should continue to be handled by the zero-extension lemma, as the repo now does.

## Answer to the question “is it false?”

* For **generic smooth functions** satisfying only `v'(0)=0`, yes, the statement can be false. Example: `U=1`, `V=1+x²+x³`, `β=0`, then `φ''(0)=6`.
* For **smooth cosine-series/even-reflection functions**, no, it is not false. It is true by parity, and `φ''(0)=0` even though `φ'(0)` may be nonzero.
* For **`intervalDomainLift` zero-extensions**, the expression is not the smooth global cosine-series expression; endpoint derivatives can become Mathlib junk values. Do not use zero-extension endpoint `deriv` to prove the genuine spectral/weak-H² Neumann condition.

## Practical recommendation

Add a small parity file, perhaps:

```lean
ShenWork/Paper2/IntervalChemFluxParity.lean
```

with:

```lean
EvenAtZero, OddAtZero
cosineSeries_evenAtZero
deriv_odd_of_evenAtZero
deriv_even_of_oddAtZero
deriv_at_zero_eq_zero_of_evenAtZero
second_deriv_at_zero_eq_zero_of_oddAtZero
chemFluxFun_oddAtZero_of_even
chemFluxFun_second_deriv_zero_at_zero_of_even
```

Then use it only with the global cosine representatives, not directly with `intervalDomainLift`. This cleanly separates:

```text
global smooth parity proof   → genuine one-sided Neumann limit
zero-extension endpoint lemma → point derivative hbc0/hbc1
```

That separation matches the repo’s current direction and avoids confusing the zero-extension/junk derivative with the mathematically meaningful boundary condition.
