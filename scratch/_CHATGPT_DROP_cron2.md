# Q1291 (cron2/cron3) — exact `intervalWeakH2Neumann_of_contDiffOn` signature

Static GitHub-connector inspection only. I did **not** run Lean locally.

## Exact location

The theorem/definition is in:

```lean
ShenWork/PDE/IntervalMildSourceDecayHelper.lean
```

namespace:

```lean
ShenWork.PDE.IntervalMildSourceDecayHelper
```

The structure it builds is:

```lean
structure IntervalWeakH2Neumann (f : ℝ → ℝ) where
  secondDeriv : ℝ → ℝ
  second_intervalIntegrable : IntervalIntegrable secondDeriv volume (0 : ℝ) 1
  second_abs_integral_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∫ x in (0 : ℝ)..1, |secondDeriv x| ≤ B
  weak_cosine_laplacian : ∀ k : ℕ,
    (∫ x in (0 : ℝ)..1,
        Real.cos ((k : ℝ) * Real.pi * x) * secondDeriv x) =
      -((k : ℝ) * Real.pi) ^ 2 *
        ∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) * f x
```

## Exact signature

Yes: `intervalWeakH2Neumann_of_contDiffOn` takes `ContDiffOn ℝ 2 g (Icc 0 1)` and endpoint Neumann data.  The exact signature is:

```lean
noncomputable def intervalWeakH2Neumann_of_contDiffOn
    {g : ℝ → ℝ}
    (hgC2 : ContDiffOn ℝ 2 g (Set.Icc (0 : ℝ) 1))
    (htend0 : Filter.Tendsto (deriv g) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htend1 : Filter.Tendsto (deriv g) (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0))
    (hbc0 : deriv g 0 = 0) (hbc1 : deriv g 1 = 0) :
    IntervalWeakH2Neumann g
```

Internally it sets:

```lean
secondDeriv := deriv (deriv g)
```

and proves the weak cosine-laplacian identity using:

```lean
intervalCosineLaplacianCoeff_eq_of_contDiffOn k hgC2 htend0 htend1 hbc0 hbc1
```

## Power-source wrapper

There is also a specialized wrapper for exactly your shape `ν * u^γ`:

```lean
noncomputable def powerSource_intervalWeakH2Neumann
    {ν γ : ℝ} {u : ℝ → ℝ}
    (hgC2 : ContDiffOn ℝ 2 (fun x : ℝ => ν * u x ^ γ) (Set.Icc (0 : ℝ) 1))
    (htend0 : Filter.Tendsto (deriv (fun x : ℝ => ν * u x ^ γ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htend1 : Filter.Tendsto (deriv (fun x : ℝ => ν * u x ^ γ))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0))
    (hbc0 : deriv (fun x : ℝ => ν * u x ^ γ) 0 = 0)
    (hbc1 : deriv (fun x : ℝ => ν * u x ^ γ) 1 = 0) :
    IntervalWeakH2Neumann (fun x : ℝ => ν * u x ^ γ) :=
  intervalWeakH2Neumann_of_contDiffOn hgC2 htend0 htend1 hbc0 hbc1
```

So for `f = p.ν * U_cos^p.γ`, you can use either the generic constructor with `g := f`, or the wrapper with `u := U_cos`, `ν := p.ν`, `γ := p.γ`.

## How to build it from `U_cos : ContDiff ℝ 4`

Assume you have:

```lean
hU_C4      : ContDiff ℝ 4 U_cos
hU_pos_all : ∀ x, 0 < U_cos x
```

Then define the smooth representative:

```lean
set f : ℝ → ℝ := fun x => p.ν * U_cos x ^ p.γ with hf_def
```

Global C⁴, hence closed-interval C²:

```lean
have hU_ne : ∀ x, U_cos x ≠ 0 := fun x => ne_of_gt (hU_pos_all x)

have hf_C4 : ContDiff ℝ 4 f := by
  rw [hf_def]
  exact contDiff_const.mul (hU_C4.rpow_const_of_ne hU_ne)

have hf_C2_on : ContDiffOn ℝ 2 f (Icc (0 : ℝ) 1) :=
  (hf_C4.of_le (by norm_num : (2 : ℕ∞) ≤ 4)).contDiffOn
```

Now the constructor still needs the Neumann endpoint data for `deriv f`:

```lean
hftend0 : Filter.Tendsto (deriv f) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0)
hftend1 : Filter.Tendsto (deriv f) (nhdsWithin (1 : ℝ) (Iio 1)) (nhds 0)
hfbc0   : deriv f 0 = 0
hfbc1   : deriv f 1 = 0
```

If `f` is global C⁴, the `Tendsto` fields follow from continuity of `deriv f` once you have the endpoint equalities:

```lean
have hf'_cont : Continuous (deriv f) :=
  hf_C4.continuous_deriv (by norm_num)

have hftend0 : Filter.Tendsto (deriv f)
    (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
  conv_rhs => rw [← hfbc0]
  exact hf'_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

have hftend1 : Filter.Tendsto (deriv f)
    (nhdsWithin (1 : ℝ) (Iio 1)) (nhds 0) := by
  conv_rhs => rw [← hfbc1]
  exact hf'_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
```

Then the weak-H² certificate is:

```lean
have hf_H2 : ShenWork.PDE.IntervalMildSourceDecayHelper.IntervalWeakH2Neumann f :=
  ShenWork.PDE.IntervalMildSourceDecayHelper.intervalWeakH2Neumann_of_contDiffOn
    hf_C2_on hftend0 hftend1 hfbc0 hfbc1
```

or, without naming `f`, using the wrapper:

```lean
have hf_H2 :
    ShenWork.PDE.IntervalMildSourceDecayHelper.IntervalWeakH2Neumann
      (fun x : ℝ => p.ν * U_cos x ^ p.γ) :=
  ShenWork.PDE.IntervalMildSourceDecayHelper.powerSource_intervalWeakH2Neumann
    (ν := p.ν) (γ := p.γ) (u := U_cos)
    hf_C2_on hftend0 hftend1 hfbc0 hfbc1
```

## Endpoint equalities for `f = p.ν * U_cos^p.γ`

The constructor does **not** prove endpoint equalities for you.  You must provide:

```lean
deriv (fun x => p.ν * U_cos x ^ p.γ) 0 = 0
deriv (fun x => p.ν * U_cos x ^ p.γ) 1 = 0
```

There are two good ways.

### Route A: chain-rule from `deriv U_cos 0 = 0`, `deriv U_cos 1 = 0`

If you already have endpoint Neumann data for `U_cos`, use the derivative formula:

```text
deriv (ν * U^γ) = ν * (γ * U^(γ-1) * deriv U)
```

Then the endpoint derivative vanishes because `deriv U_cos` vanishes.

This is mathematically direct, but in Lean it may require a few `HasDerivAt` chain-rule lines with `Real.hasDerivAt_rpow_const` or the `ContDiff` derivative API.

### Route B: parity/symmetry, usually easier here

Since `U_cos` is a cosine series, it is even about `0` and symmetric about `1`:

```lean
hU_even  : ∀ x, U_cos (-x) = U_cos x
hU_symm1 : ∀ x, U_cos (2 - x) = U_cos x
```

Then `f = ν * U_cos^γ` inherits both:

```lean
have hf_even : ∀ x, f (-x) = f x := by
  intro x
  simp [hf_def, hU_even]

have hf_symm1 : ∀ x, f (2 - x) = f x := by
  intro x
  simp [hf_def, hU_symm1]
```

From evenness, `deriv f` is odd, so `deriv f 0 = 0`; from symmetry about `1`, `deriv f (2 - x) = - deriv f x`, so `deriv f 1 = 0`.  This is the same pattern already used in `IntervalConjugateLevel0BFormSourceOn.lean` for `g_smooth` and its higher derivatives.

A reusable local helper style:

```lean
have deriv_even_odd : ∀ {g : ℝ → ℝ}, ContDiff ℝ 1 g →
    (∀ x, g (-x) = g x) → ∀ x, deriv g (-x) = -(deriv g x) := by
  intro g _hg heven x
  have h1 := deriv_comp_neg (f := g) (x := x)
  rw [show (fun x => g (-x)) = g from funext heven] at h1
  linarith

have odd_zero : ∀ {g : ℝ → ℝ}, (∀ x, g (-x) = -(g x)) → g 0 = 0 := by
  intro g hodd
  have h := hodd 0
  rw [neg_zero] at h
  linarith

have hf'_odd : ∀ x, deriv f (-x) = -(deriv f x) :=
  deriv_even_odd (hf_C4.of_le (by norm_num)) hf_even

have hfbc0 : deriv f 0 = 0 :=
  odd_zero hf'_odd

have hf'_antisymm1 : ∀ x, deriv f (2 - x) = -(deriv f x) := by
  intro x
  have h1 := deriv_comp_const_sub (f := f) (a := 2) (x := x)
  rw [show (fun x => f (2 - x)) = f from funext hf_symm1] at h1
  linarith

have hfbc1 : deriv f 1 = 0 := by
  have h := hf'_antisymm1 1
  rw [show (2 : ℝ) - 1 = 1 from by norm_num] at h
  linarith
```

## Bottom line

Yes.  `intervalWeakH2Neumann_of_contDiffOn` takes:

1. `ContDiffOn ℝ 2 f (Icc 0 1)`,
2. right-endpoint/left-endpoint one-sided tendsto of `deriv f` to `0`,
3. point endpoint equalities `deriv f 0 = 0`, `deriv f 1 = 0`.

For your `f = p.ν * U_cos^p.γ`, `U_cos : ContDiff ℝ 4` plus positivity gives `f : ContDiff ℝ 4`, hence `ContDiffOn ℝ 2 f (Icc 0 1)`.  You still need to provide the Neumann endpoint data, best obtained from the cosine-series evenness and reflection-about-1 symmetry.
