# Q381 (cron2): `realSlice`, `intervalDomainLift`, and the evalST `h_u` atom

## Executive verdict

I read the exact current definitions and the current `h_u` producers.

The answer is:

* If `h_u` is interpreted as the **real-part identity**

  ```lean
  (evalST τ (x : WA.Circ) (GWA.incl _ u_star)).re
    = intervalDomainLift (realSlice u_star τ.1) x
  ```

  then yes: on `x ∈ Set.Icc 0 1` and `τ : TimeDom T`, it is a definitional/unfolding fact. No analytic content, no Picard fixed-point equation, no Banach theorem, no source data.

* But the current code’s slab atom `h_u` is actually the **complex-valued identity**

  ```lean
  evalST τ x (GWA.incl _ u_star)
    = (intervalDomainLift (realSlice u_star τ.1) x : ℂ)
  ```

  not merely a real-part equality. For that stronger statement, the real part is definitional, but the imaginary part needs the genuine/structural reality input

  ```lean
  (evalST τ (x : WA.Circ) (GWA.incl _ u_star)).im = 0
  ```

  In the Picard fixed-point route this is discharged from `EvenRealEWA u_star`, which is itself supplied for the Picard fixed point by `picardEWA_evenReal_fixedPoint`.

So there is **no realization gap** in the real part. The only non-definitional piece in the current complex `h_u` theorem is proving that the eval is real-valued. That is not PDE/source content; it is parity/even-real algebraic content.

There is one important boundary caveat: `intervalDomainLift` is a zero-extension, so the unfolding is only valid when the theorem has `hx : x ∈ Set.Icc 0 1`. Outside `[0,1]`, the lift is `0`, while `evalST τ x …` need not vanish. The existing `h_u` slab correctly quantifies `∀ x ∈ Set.Icc 0 1`.

Also, the time does **not** need to be interior. Since `τ : TimeDom T` is already a subtype proof of `τ.1 ∈ [0,T]`, `realSlice u_star τ.1` selects the `if_pos τ.2` branch. The same definitional argument works at `τ.1 = 0` or `τ.1 = T` as well.

## Exact definitions read

### `TimeDom`

From `ShenWork/Wiener/EWA/Basic.lean`:

```lean
import ShenWork.Wiener.EWA.Basic

namespace ShenWork.EWA

/-- The compact time domain `[0, T] ⊆ ℝ`. -/
abbrev TimeDom (T : ℝ) : Type := Set.Icc (0 : ℝ) T

end ShenWork.EWA
```

So a term `τ : TimeDom T` is a subtype with `τ.1 : ℝ` and `τ.2 : τ.1 ∈ Set.Icc 0 T`.

### `evalST`

From `ShenWork/Wiener/EWA/Decisive.lean`:

```lean
import ShenWork.Wiener.EWA.Decisive

open ShenWork.GWA ShenWork.Wiener

namespace ShenWork.EWA

variable {T : ℝ}

/-- **Space-time point evaluation** `EWA T 0 →+* ℂ`: slice the time-coefficients
at time `τ` (landing in `WA 0`), then evaluate the resulting Fourier series at
the spatial point `x : WA.Circ`. -/
def evalST (τ : TimeDom T) (x : WA.Circ) : EWA T 0 →+* ℂ :=
  (WA.evalAt x).comp (sliceWA τ).toRingHom

@[simp] theorem evalST_apply (τ : TimeDom T) (x : WA.Circ) (a : EWA T 0) :
    evalST τ x a = WA.evalAt x (sliceWA τ a) := rfl

end ShenWork.EWA
```

`evalST` is not itself a physical-space lift. It is the circle/Wiener point evaluation of an EWA element after time slicing. The physical-space slice is **defined from it** by `realSlice`.

### `realSlice`

From `ShenWork/Wiener/EWA/SourceClassicalExistence.lean`:

```lean
import ShenWork.Wiener.EWA.SourceClassicalExistence

open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDomain (intervalDomainPoint)

namespace ShenWork.EWA

variable {T : ℝ}

/-- **The realized real-space slice of an `EWA T 1` element.**  At time `t` (clamped to
`[0,T]` by the membership test) and interior point `x : intervalDomainPoint`, the slice
is the real part of the Wiener point-evaluation of the grade-drop `incl u*`. -/
def realSlice (u_star : EWA T 1) : ℝ → intervalDomainPoint → ℝ :=
  fun t x =>
    if h : t ∈ Set.Icc (0 : ℝ) T then
      (evalST (⟨t, h⟩ : TimeDom T) ((x.1 : ℝ) : WA.Circ)
        (GWA.incl (by omega : (0:ℕ) ≤ 1) u_star)).re
    else 0

end ShenWork.EWA
```

Key point: for `τ : TimeDom T`, `realSlice u_star τ.1` unfolds with `dif_pos τ.2` to the real part of `evalST (⟨τ.1, τ.2⟩ : TimeDom T)`. This is definitionally the same time as `τ` after the trivial subtype equality `Subtype.ext rfl`.

### `intervalDomainLift`

From `ShenWork/PDE/IntervalDomain.lean`:

```lean
import ShenWork.PDE.IntervalDomain

namespace ShenWork.IntervalDomain

-- Unit interval domain point space used by the concrete bounded-domain API.
def intervalDomainPoint : Type := Subtype (Set.Icc (0 : ℝ) 1)

-- Extend a function on the unit interval to ℝ by zero outside
-- `[0,1]`, so that `intervalIntegral` and `deriv` can be applied directly.
def intervalDomainLift (f : intervalDomainPoint → ℝ) : ℝ → ℝ :=
  fun x => if hx : x ∈ Set.Icc (0 : ℝ) 1 then f ⟨x, hx⟩ else 0

end ShenWork.IntervalDomain
```

Key point: on `hx : x ∈ Set.Icc 0 1`, this unfolds to `f ⟨x,hx⟩`; outside `[0,1]`, it unfolds to `0`.

## The definitional real-part lemma

The following is the exact “real part only” theorem. It needs no parity and no fixed-point hypothesis:

```lean
import ShenWork.Wiener.EWA.SourceChiNegUncond

open scoped BigOperators
open Set Metric
open ShenWork.GWA ShenWork.Wiener ShenWork.CosineSpectrum
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-- Real-part version of `h_u`: purely definitional on `[0,1]`. -/
theorem realSlice_evalST_re_definally
    (u_star : EWA T 1) (τ : TimeDom T) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (evalST τ (x : WA.Circ)
      (GWA.incl (by omega : (0 : ℕ) ≤ 1) u_star)).re
      = intervalDomainLift (realSlice u_star τ.1) x := by
  have hτ : (⟨τ.1, τ.2⟩ : TimeDom T) = τ := Subtype.ext rfl
  symm
  rw [intervalDomainLift, dif_pos hx, realSlice, dif_pos τ.2, hτ]

end ShenWork.EWA
```

This is the core check. The only bookkeeping is:

1. `dif_pos hx` for `intervalDomainLift`,
2. `dif_pos τ.2` for `realSlice`,
3. `Subtype.ext rfl` to rewrite `(⟨τ.1, τ.2⟩ : TimeDom T)` back to `τ`.

No source coefficients and no `picardEWA` fixed-point equality appear.

## The current code’s actual `h_u`: complex equality

The current production theorem is in `ShenWork/Wiener/EWA/SourceChiNegUncond.lean`:

```lean
import ShenWork.Wiener.EWA.SourceChiNegUncond

open scoped BigOperators
open Set Metric
open ShenWork.GWA ShenWork.Wiener ShenWork.CosineSpectrum
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

#check realSlice_evalST_realizes
#check evalST_incl_im_zero_of_evenReal

/-- Existing theorem shape, paraphrased:

For any `u_star : EWA T 1`, any `τ : TimeDom T`, and any `x ∈ [0,1]`,
`evalST` realizes the lifted `realSlice` as a complex number, provided the eval has
zero imaginary part. -/
#check (realSlice_evalST_realizes :
  ∀ (u_star : EWA T 1) (τ : TimeDom T) (x : ℝ),
    x ∈ Set.Icc (0 : ℝ) 1 →
    (evalST τ (x : WA.Circ)
      (GWA.incl (by omega : (0 : ℕ) ≤ 1) u_star)).im = 0 →
    evalST τ (x : WA.Circ)
      (GWA.incl (by omega : (0 : ℕ) ≤ 1) u_star)
      = (intervalDomainLift (realSlice u_star τ.1) x : ℂ))

end ShenWork.EWA
```

The actual proof in the file is exactly the split above:

```lean
import ShenWork.Wiener.EWA.SourceChiNegUncond

open scoped BigOperators
open Set Metric
open ShenWork.GWA ShenWork.Wiener ShenWork.CosineSpectrum
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-- Existing proof pattern, copied structurally. -/
theorem realSlice_evalST_realizes_pattern (u_star : EWA T 1) (τ : TimeDom T) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hreal : (evalST τ (x : WA.Circ)
      (GWA.incl (by omega : (0 : ℕ) ≤ 1) u_star)).im = 0) :
    evalST τ (x : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1) u_star)
      = (intervalDomainLift (realSlice u_star τ.1) x : ℂ) := by
  have hτ : (⟨τ.1, τ.2⟩ : TimeDom T) = τ := Subtype.ext rfl
  have hlift : intervalDomainLift (realSlice u_star τ.1) x
      = (evalST τ (x : WA.Circ)
        (GWA.incl (by omega : (0 : ℕ) ≤ 1) u_star)).re := by
    rw [intervalDomainLift, dif_pos hx, realSlice, dif_pos τ.2, hτ]
  rw [hlift]
  apply Complex.ext
  · rw [Complex.ofReal_re]
  · rw [Complex.ofReal_im, hreal]

end ShenWork.EWA
```

So the complex equality is **not** just `rfl`: the imaginary component is a real-valuedness obligation.

## How the current slab discharges the imaginary part

`SourceChiNegUncond.lean` proves:

```lean
import ShenWork.Wiener.EWA.SourceChiNegUncond

open scoped BigOperators
open Set Metric
open ShenWork.GWA ShenWork.Wiener ShenWork.CosineSpectrum
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-- Full-circle reality of `evalST (incl u_star)` from `EvenRealEWA u_star`. -/
#check evalST_incl_im_zero_of_evenReal

end ShenWork.EWA
```

And `SourceChiNegUncondWire.lean` packages the slab atom:

```lean
import ShenWork.Wiener.EWA.SourceChiNegUncondWire

open scoped BigOperators
open Set Metric
open ShenWork.GWA ShenWork.Wiener ShenWork.CosineSpectrum
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

#check realSlice_h_u_slab

/-- Existing slab shape, paraphrased:

If `u_star` is even-real, then for every `τ : TimeDom T` and every `x ∈ [0,1]`,
the complex `h_u` identity holds. -/
#check (realSlice_h_u_slab :
  ∀ {u_star : EWA T 1}, EvenRealEWA u_star →
    ∀ (τ : TimeDom T), ∀ x ∈ Set.Icc (0 : ℝ) 1,
      evalST τ x (GWA.incl (by omega : (0 : ℕ) ≤ 1) u_star)
        = (intervalDomainLift (realSlice u_star τ.1) x : ℂ))

end ShenWork.EWA
```

The proof is short:

```lean
intro τ x hx
exact realSlice_evalST_realizes u_star τ x hx
  (evalST_incl_im_zero_of_evenReal hER τ (x : WA.Circ))
```

So for the Picard fixed point:

* `picardEWA_evenReal_fixedPoint` gives `EvenRealEWA u_star`,
* `evalST_incl_im_zero_of_evenReal` gives the imaginary part is zero,
* `realSlice_evalST_realizes` uses the definitional real-part unfolding plus that zero-imaginary fact.

## Boundary and scope checks

### Spatial scope

The theorem is only true in the stated form on `[0,1]`:

```lean
∀ x ∈ Set.Icc (0 : ℝ) 1, ...
```

This restriction is essential because:

```lean
intervalDomainLift f x = if hx : x ∈ Set.Icc 0 1 then f ⟨x,hx⟩ else 0
```

For `x ∉ [0,1]`, the RHS lift is `0`, while `evalST τ (x : WA.Circ) ...` is a circle/Wiener evaluation and is not definitionally zero. Therefore a global `∀ x : ℝ` version would be a genuine/false extra claim, not a definitional one.

### Time scope

For `τ : TimeDom T`, no interior-time hypothesis is needed:

```lean
τ.2 : τ.1 ∈ Set.Icc (0 : ℝ) T
```

Therefore `realSlice u_star τ.1` always unfolds through `dif_pos τ.2`. The existing h_u slab works for all `τ : TimeDom T`, not just `τ.1 ∈ Set.Ioo 0 T`.

If instead one states a lemma at an arbitrary real `t : ℝ`, then the branch depends on a proof of `t ∈ [0,T]`; outside `[0,T]`, `realSlice u_star t` is defined to be `0`.

## Answer to the direct question

The proposed reasoning is correct for the **real part**:

```text
Re(evalST τ x (incl u_star))
= realSlice u_star τ.1 ⟨x,hx⟩
= intervalDomainLift (realSlice u_star τ.1) x
```

up to the harmless subtype rewrite `⟨τ.1,τ.2⟩ = τ` and the spatial branch `hx : x ∈ [0,1]`.

But the existing current atom used by `realizes_clean` is stronger:

```lean
evalST τ x (incl u_star) = (intervalDomainLift (realSlice u_star τ.1) x : ℂ)
```

For that, definitional unfolding gives only the real part. The imaginary part is closed by `EvenRealEWA`:

```lean
(evalST τ x (incl u_star)).im = 0
```

So the final verdict is:

```text
Re-only h_u:        trivial definitional unfolding on x ∈ [0,1].
Current complex h_u: real part trivial; imaginary part needs even-real/parity.
Not a PDE/source gap: the only non-definitional content is algebraic reality of evalST.
Not valid globally in x: intervalDomainLift is a zero-extension outside [0,1].
```
