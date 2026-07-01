# Q2825 (cron1) — Lean 4 proof of `∫ f^(p+rho) ≤ sup(f)^rho * ∫ f^p`

Repository: `xiangyazi24/Shen_work`  
Branch: `chatgpt-scratch`  
Target file: `scratch/_CHATGPT_DROP_cron1.md`

## Short answer

Yes: the right Mathlib lemma is

```lean
intervalIntegral.integral_mono_on
```

with shape:

```lean
intervalIntegral.integral_mono_on
  (a := a) (b := b) (μ := volume)
  hab hLeftInt hRightInt hpoint
```

where

```lean
hab       : a ≤ b
hLeftInt  : IntervalIntegrable left volume a b
hRightInt : IntervalIntegrable right volume a b
hpoint    : ∀ x ∈ Set.Icc a b, left x ≤ right x
```

In this repo there is already a convenient wrapper in `ShenWork.PDE.IntervalDomain`:

```lean
ShenWork.IntervalDomain.intervalIntegral_mono
```

with argument order:

```lean
intervalIntegral_mono hL hfg hf hg
```

and internally it is exactly:

```lean
intervalIntegral.integral_mono_on hL hf hg hfg
```

For the real-power pointwise step, the useful lemmas are:

```lean
Real.rpow_add_of_nonneg
Real.rpow_le_rpow
Real.rpow_nonneg
```

For integrability from continuity, the useful names are:

```lean
ContinuousOn.rpow_const
ContinuousOn.intervalIntegrable_of_Icc
IntervalIntegrable.const_mul
```

## Clean Mathlib-only skeleton

This is the core proof if you already have a bound `F x ≤ M` on `[0,1]` and the two needed interval-integrability facts.

```lean
import Mathlib

open MeasureTheory
open scoped Interval

noncomputable section

example {F : ℝ → ℝ} {p rho M : ℝ}
    (hp : 0 ≤ p) (hrho : 0 ≤ rho)
    (hF_nonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ F x)
    (hF_le_M : ∀ x ∈ Set.Icc (0 : ℝ) 1, F x ≤ M)
    (hLeftInt :
      IntervalIntegrable (fun x : ℝ => F x ^ (p + rho)) volume 0 1)
    (hPowInt :
      IntervalIntegrable (fun x : ℝ => F x ^ p) volume 0 1) :
    (∫ x in (0 : ℝ)..1, F x ^ (p + rho)) ≤
      M ^ rho * ∫ x in (0 : ℝ)..1, F x ^ p := by
  have hRightInt :
      IntervalIntegrable (fun x : ℝ => M ^ rho * F x ^ p) volume 0 1 :=
    hPowInt.const_mul (M ^ rho)

  have hmono :
      (∫ x in (0 : ℝ)..1, F x ^ (p + rho)) ≤
        ∫ x in (0 : ℝ)..1, M ^ rho * F x ^ p := by
    refine intervalIntegral.integral_mono_on
      (a := (0 : ℝ)) (b := 1) (μ := volume)
      (f := fun x : ℝ => F x ^ (p + rho))
      (g := fun x : ℝ => M ^ rho * F x ^ p)
      zero_le_one hLeftInt hRightInt ?_
    intro x hx
    have hx0 : 0 ≤ F x := hF_nonneg x hx
    have hxM : F x ≤ M := hF_le_M x hx
    calc
      F x ^ (p + rho) = F x ^ p * F x ^ rho := by
        exact Real.rpow_add_of_nonneg hx0 hp hrho
      _ = F x ^ rho * F x ^ p := by
        rw [mul_comm]
      _ ≤ M ^ rho * F x ^ p := by
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hx0 hxM hrho)
          (Real.rpow_nonneg hx0 p)

  rw [intervalIntegral.integral_const_mul] at hmono
  exact hmono
```

The line

```lean
rw [intervalIntegral.integral_const_mul] at hmono
```

rewrites

```lean
∫ x in 0..1, M ^ rho * F x ^ p
```

to

```lean
M ^ rho * ∫ x in 0..1, F x ^ p.
```

## Same proof using the repo wrapper

If `ShenWork.PDE.IntervalDomain` is imported, you can replace the raw `intervalIntegral.integral_mono_on` block by the local wrapper.

```lean
import ShenWork.PDE.IntervalDomain

open MeasureTheory
open ShenWork.IntervalDomain
open scoped Interval

noncomputable section

example {F : ℝ → ℝ} {p rho M : ℝ}
    (hp : 0 ≤ p) (hrho : 0 ≤ rho)
    (hF_nonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ F x)
    (hF_le_M : ∀ x ∈ Set.Icc (0 : ℝ) 1, F x ≤ M)
    (hLeftInt :
      IntervalIntegrable (fun x : ℝ => F x ^ (p + rho)) volume 0 1)
    (hPowInt :
      IntervalIntegrable (fun x : ℝ => F x ^ p) volume 0 1) :
    (∫ x in (0 : ℝ)..1, F x ^ (p + rho)) ≤
      M ^ rho * ∫ x in (0 : ℝ)..1, F x ^ p := by
  have hRightInt :
      IntervalIntegrable (fun x : ℝ => M ^ rho * F x ^ p) volume 0 1 :=
    hPowInt.const_mul (M ^ rho)

  have hpoint :
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        F x ^ (p + rho) ≤ M ^ rho * F x ^ p := by
    intro x hx
    have hx0 : 0 ≤ F x := hF_nonneg x hx
    have hxM : F x ≤ M := hF_le_M x hx
    calc
      F x ^ (p + rho) = F x ^ p * F x ^ rho := by
        exact Real.rpow_add_of_nonneg hx0 hp hrho
      _ = F x ^ rho * F x ^ p := by
        rw [mul_comm]
      _ ≤ M ^ rho * F x ^ p := by
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hx0 hxM hrho)
          (Real.rpow_nonneg hx0 p)

  have hmono :
      (∫ x in (0 : ℝ)..1, F x ^ (p + rho)) ≤
        ∫ x in (0 : ℝ)..1, M ^ rho * F x ^ p :=
    intervalIntegral_mono
      (L := (1 : ℝ)) zero_le_one hpoint hLeftInt hRightInt

  rw [intervalIntegral.integral_const_mul] at hmono
  exact hmono
```

This uses the wrapper already present in the repo:

```lean
ShenWork.IntervalDomain.intervalIntegral_mono
```

## If you want integrability from continuity

If your lifted function `F` is continuous on `[0,1]`, then you can usually produce the integrability facts as follows.

```lean
import Mathlib

open MeasureTheory
open scoped Interval

noncomputable section

example {F : ℝ → ℝ} {p rho : ℝ}
    (hp : 0 ≤ p) (hrho : 0 ≤ rho)
    (hF_cont : ContinuousOn F (Set.Icc (0 : ℝ) 1)) :
    IntervalIntegrable (fun x : ℝ => F x ^ p) volume 0 1 ∧
      IntervalIntegrable (fun x : ℝ => F x ^ (p + rho)) volume 0 1 := by
  have hFp_cont : ContinuousOn (fun x : ℝ => F x ^ p) (Set.Icc (0 : ℝ) 1) :=
    hF_cont.rpow_const (fun x hx => Or.inr hp)
  have hFpr_cont : ContinuousOn (fun x : ℝ => F x ^ (p + rho)) (Set.Icc (0 : ℝ) 1) :=
    hF_cont.rpow_const (fun x hx => Or.inr (add_nonneg hp hrho))
  exact ⟨
    hFp_cont.intervalIntegrable_of_Icc zero_le_one,
    hFpr_cont.intervalIntegrable_of_Icc zero_le_one
  ⟩
```

Then feed these two facts into the previous proof.

## Deriving the `M` bound from `sSup (range |f|)`

A good tactic is to separate the supremum bookkeeping from the integral proof.  First prove a lemma of this shape:

```lean
hF_le_M : ∀ x ∈ Set.Icc (0 : ℝ) 1, F x ≤ M
```

Then the integration proof is short.

For a plain real function restricted to `[0,1]`, one clean way is:

```lean
import Mathlib

open MeasureTheory
open scoped Interval

noncomputable section

example {F : ℝ → ℝ}
    (hbdd : BddAbove
      (Set.range (fun x : {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1} => |F x.1|))) :
    let M : ℝ := sSup
      (Set.range (fun x : {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1} => |F x.1|))
    ∀ y ∈ Set.Icc (0 : ℝ) 1, F y ≤ M := by
  intro M y hy
  have h_abs : |F y| ≤ M := by
    exact le_csSup hbdd ⟨⟨y, hy⟩, rfl⟩
  exact le_trans (le_abs_self (F y)) h_abs
```

For your interval-domain setup, the analogous step should look like this, assuming `intervalDomainPoint`, `intervalDomainLift`, and `hf_bdd` are in scope:

```lean
import ShenWork.PDE.IntervalDomain

open MeasureTheory
open ShenWork.IntervalDomain
open scoped Interval

noncomputable section

-- Skeleton: adapt names/imports to the exact file where you place it.
example {f : intervalDomainPoint → ℝ}
    (hf_bdd : BddAbove (Set.range fun x : intervalDomainPoint => |f x|)) :
    let M : ℝ := sSup (Set.range fun x : intervalDomainPoint => |f x|)
    ∀ y ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift f y ≤ M := by
  intro M y hy
  have h_abs_point : |f ⟨y, hy⟩| ≤ M := by
    exact le_csSup hf_bdd ⟨⟨y, hy⟩, rfl⟩
  have h_abs_lift : |intervalDomainLift f y| ≤ M := by
    simpa [intervalDomainLift, hy] using h_abs_point
  exact le_trans (le_abs_self (intervalDomainLift f y)) h_abs_lift
```

If you also have nonnegativity on points,

```lean
hf_nonneg : ∀ x : intervalDomainPoint, 0 ≤ f x
```

then the corresponding lifted nonnegativity fact is:

```lean
have hF_nonneg : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift f y := by
  intro y hy
  simpa [intervalDomainLift, hy] using hf_nonneg ⟨y, hy⟩
```

Now use `F := intervalDomainLift f` in the generic Mathlib proof.

## Recommended proof structure in the Shen files

I would implement this in three small lemmas rather than one giant proof.

### 1. Sup-bound adapter

```lean
-- interval-domain-specific
lemma intervalDomainLift_le_sSup_abs
    {f : intervalDomainPoint → ℝ}
    (hf_bdd : BddAbove (Set.range fun x : intervalDomainPoint => |f x|)) :
    ∀ y ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift f y ≤ sSup (Set.range fun x : intervalDomainPoint => |f x|) := by
  intro y hy
  have h_abs_point :
      |f ⟨y, hy⟩| ≤ sSup (Set.range fun x : intervalDomainPoint => |f x|) := by
    exact le_csSup hf_bdd ⟨⟨y, hy⟩, rfl⟩
  have h_abs_lift :
      |intervalDomainLift f y| ≤ sSup (Set.range fun x : intervalDomainPoint => |f x|) := by
    simpa [intervalDomainLift, hy] using h_abs_point
  exact le_trans (le_abs_self (intervalDomainLift f y)) h_abs_lift
```

### 2. Pointwise `rpow` inequality

```lean
lemma rpow_add_le_sup_rpow_mul_rpow_pointwise
    {F : ℝ → ℝ} {p rho M x : ℝ}
    (hp : 0 ≤ p) (hrho : 0 ≤ rho)
    (hx0 : 0 ≤ F x) (hxM : F x ≤ M) :
    F x ^ (p + rho) ≤ M ^ rho * F x ^ p := by
  calc
    F x ^ (p + rho) = F x ^ p * F x ^ rho := by
      exact Real.rpow_add_of_nonneg hx0 hp hrho
    _ = F x ^ rho * F x ^ p := by
      rw [mul_comm]
    _ ≤ M ^ rho * F x ^ p := by
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hx0 hxM hrho)
        (Real.rpow_nonneg hx0 p)
```

### 3. Integral monotonicity lemma

```lean
lemma intervalIntegral_rpow_add_le_sup_rpow_mul_integral_rpow
    {F : ℝ → ℝ} {p rho M : ℝ}
    (hp : 0 ≤ p) (hrho : 0 ≤ rho)
    (hF_nonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ F x)
    (hF_le_M : ∀ x ∈ Set.Icc (0 : ℝ) 1, F x ≤ M)
    (hLeftInt : IntervalIntegrable (fun x : ℝ => F x ^ (p + rho)) volume 0 1)
    (hPowInt : IntervalIntegrable (fun x : ℝ => F x ^ p) volume 0 1) :
    (∫ x in (0 : ℝ)..1, F x ^ (p + rho)) ≤
      M ^ rho * ∫ x in (0 : ℝ)..1, F x ^ p := by
  have hRightInt :
      IntervalIntegrable (fun x : ℝ => M ^ rho * F x ^ p) volume 0 1 :=
    hPowInt.const_mul (M ^ rho)
  have hmono :
      (∫ x in (0 : ℝ)..1, F x ^ (p + rho)) ≤
        ∫ x in (0 : ℝ)..1, M ^ rho * F x ^ p := by
    refine intervalIntegral.integral_mono_on
      (a := (0 : ℝ)) (b := 1) (μ := volume)
      zero_le_one hLeftInt hRightInt ?_
    intro x hx
    exact rpow_add_le_sup_rpow_mul_rpow_pointwise
      hp hrho (hF_nonneg x hx) (hF_le_M x hx)
  rw [intervalIntegral.integral_const_mul] at hmono
  exact hmono
```

## Notes and pitfalls

1. Do not try to use `linarith` for the `rpow` pointwise inequality.  Use `Real.rpow_le_rpow` and then multiply by the nonnegative factor `F x ^ p`.

2. Use `Real.rpow_add_of_nonneg`, not plain rewriting, for

   ```lean
   F x ^ (p + rho) = F x ^ p * F x ^ rho
   ```

   because `Real.rpow` has special behavior at zero.  The lemma handles the zero case correctly under `0 ≤ F x`, `0 ≤ p`, `0 ≤ rho`.

3. `intervalIntegral.integral_mono_on` requires integrability of both sides.  The RHS integrability is usually just:

   ```lean
   hPowInt.const_mul (M ^ rho)
   ```

4. If your actual goal is stated with `intervalDomain.integral`, first unfold or rewrite it to the concrete interval integral of `intervalDomainLift`; then apply the lemma above.  The only interval-domain-specific work is proving the lifted nonnegativity and lifted sup bound on `Set.Icc 0 1`.

5. If the chosen sup is exactly

   ```lean
   sSup (Set.range fun x : intervalDomainPoint => |f x|)
   ```

   the bound proof should go through with `le_csSup hf_bdd ⟨x, rfl⟩`, where

   ```lean
   hf_bdd : BddAbove (Set.range fun x : intervalDomainPoint => |f x|)
   ```

   is already the kind of hypothesis used in the existing `UnitIntervalPowerGNYoungForMoser` interface.
