# Q832 / cron1: `integral_congr_ae` for `cosineCoeffs`

Repo inspected: `xiangyazi24/Shen_work`

Source ref inspected: `main`

Branch written: `chatgpt-scratch`

## Verdict

Yes.  For this boundary obstruction, the useful Mathlib theorem is already available as

```lean
intervalIntegral.integral_congr_ae
```

and the repo already has the exact cosine-coefficient helper you want:

```lean
ShenWork.EWA.cosineCoeffs_congr_on_Ioo
```

in

```text
ShenWork/Wiener/EWA/NonCircularCoeffBridge.lean
```

The theorem is:

```lean
theorem cosineCoeffs_congr_on_Ioo {f g : ℝ → ℝ}
    (hfg : ∀ x ∈ Set.Ioo (0:ℝ) 1, f x = g x) (k : ℕ) :
    cosineCoeffs f k = cosineCoeffs g k := by
  rw [cosineCoeffs_eq_factor_mul_integral, cosineCoeffs_eq_factor_mul_integral]
  congr 1
  apply intervalIntegral.integral_congr_ae
  -- bad set is contained in `{1}` and is null
  ...
```

So for **pointwise** interior agreement, use it directly:

```lean
have hcoeff : cosineCoeffs f k = cosineCoeffs g k :=
  ShenWork.EWA.cosineCoeffs_congr_on_Ioo hfg k
```

This is exactly the endpoint-null argument: after rewriting `cosineCoeffs` as the real interval integral, the proof applies `intervalIntegral.integral_congr_ae`; since Lean interval integrals over `0..1` use `Set.uIoc 0 1 = Set.Ioc 0 1`, agreement on `Ioo 0 1` leaves only the endpoint `{1}` as a possible bad set, and that singleton has measure zero.

## Search results

### `intervalIntegral.integral_congr_ae`

Found and already used in the repo in `NonCircularCoeffBridge.lean` inside `cosineCoeffs_congr_on_Ioo`.

### `cosineCoeffs_congr`

Two relevant repo helpers exist:

```lean
ShenWork.EWA.cosineCoeffs_congr_on_Ioo
```

This is the one for the boundary obstruction.

```lean
ShenWork.EWA.cosineCoeffs_congr_on_Icc
```

This stricter `[0,1]` pointwise version is in `ShenWork/Wiener/EWA/SourceInversion.lean`; it uses `intervalIntegral.integral_congr`, not the a.e. theorem, so it does **not** solve the open-interval endpoint issue by itself.

### `cosineCoeffs_eq_factor_mul_integral`

The needed real-integral rewrite is in

```text
ShenWork/Paper2/IntervalMildPicardRegularity.lean
```

as

```lean
theorem cosineCoeffs_eq_factor_mul_integral (f : ℝ → ℝ) (n : ℕ) :
    cosineCoeffs f n =
      (if n = 0 then 1 else 2) *
        ∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * f x
```

For `k ≥ 1`, this specializes to the expected

```lean
cosineCoeffs f k = 2 * ∫ x in (0 : ℝ)..1,
  Real.cos ((k : ℝ) * Real.pi * x) * f x
```

## If the hypothesis is genuinely a.e. on `Ioo`

The committed `cosineCoeffs_congr_on_Ioo` assumes pointwise equality on `Ioo`.  If your current hypothesis is instead

```lean
hfg : f =ᵐ[volume.restrict (Set.Ioo (0:ℝ) 1)] g
```

then use the same proof pattern, but feed `integral_congr_ae` the a.e. equality directly.  The local helper should be along these lines:

```lean
theorem cosineCoeffs_congr_ae_Ioo {f g : ℝ → ℝ}
    (hfg : f =ᵐ[volume.restrict (Set.Ioo (0:ℝ) 1)] g) (k : ℕ) :
    cosineCoeffs f k = cosineCoeffs g k := by
  rw [cosineCoeffs_eq_factor_mul_integral, cosineCoeffs_eq_factor_mul_integral]
  congr 1
  apply intervalIntegral.integral_congr_ae
  -- target: weighted integrands equal a.e. on `volume.restrict (Set.uIoc 0 1)`
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  -- Mathlib has the endpoint-null rewrite used nearby in interval-integrability lemmas:
  -- `restrict_Ioo_eq_restrict_Ioc`, so `Ioc 0 1` can be replaced by `Ioo 0 1`.
  rw [← restrict_Ioo_eq_restrict_Ioc]
  exact hfg.mono (by
    intro x hx
    rw [hx])
```

I did not run Lean here, so treat the last snippet as a proof skeleton.  The already-committed pointwise `Ioo` helper is stronger evidence that the endpoint/boundary obstruction is not mathematical; the only remaining detail is matching your exact equality hypothesis (`EqOn` vs `=ᵐ[volume.restrict ...]`).

## Practical recommendation

For the cosine coefficient bound, first try importing the existing helper:

```lean
import ShenWork.Wiener.EWA.NonCircularCoeffBridge
```

and use:

```lean
ShenWork.EWA.cosineCoeffs_congr_on_Ioo
```

If that import is too heavy or creates dependency direction problems, move/duplicate only the small lemma `cosineCoeffs_congr_on_Ioo` into a lower-level coefficient utility file near `cosineCoeffs_eq_factor_mul_integral`.
