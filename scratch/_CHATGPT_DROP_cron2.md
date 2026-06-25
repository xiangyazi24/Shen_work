# Q331 (cron2): does `fullSourceCoeff_jointSolutionClosed` use source time-derivative data?

## Executive answer

`fullSourceCoeff_jointSolutionClosed` itself composes the value legs exactly as expected:

```lean
heatValueSeries_jointContinuousOn
+ duhamelSeries_jointContinuousOn hchem
+ duhamelSeries_jointContinuousOn hlog
```

It does **not** call `duhamelDerivSeries_jointContinuousOn`; that derivative-series theorem is used by the separate time-derivative field.

However, the current proof of `duhamelSeries_jointContinuousOn` is **not envelope-only**. Its summable **majorant** is envelope-only, but the proof still uses `src.hderiv` to obtain pointwise continuity of each source coefficient `s ↦ a s n`, hence continuity/integrability of the Duhamel integrand and continuity of each Duhamel coefficient.

So the precise verdict is:

```text
Majorant for value-field joint continuity: envelope-only.
Existing theorem dependencies: envelope + henv_summable + henv_bound + src.hderiv-as-continuity.
Not used in the value theorem: src.adot, src.hadotcont, src.derivBound, src.hderivBound.
```

This means the circularity can be weakened, but not all the way to “just an envelope.” A refactor target should be a smaller value-source structure carrying:

```lean
continuous coefficients: ∀ n, Continuous (fun s => a s n)
envelope : ℕ → ℝ
henv_summable : Summable envelope
henv_bound : ∀ s, 0 ≤ s → ∀ n, |a s n| ≤ envelope n
```

or a windowed analogue on `[0,T]`. It does **not** need the full time-derivative `DuhamelSourceTimeC1` package.

## What `fullSourceCoeff_jointSolutionClosed` actually calls

The theorem is:

```lean
theorem fullSourceCoeff_jointSolutionClosed (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u))
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u)) {T : ℝ} :
    ContinuousOn
      (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
        ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
  (fullSourceCoeff_jointContinuousOn p u u₀cos hu0bd hchem hlog).mono (slabClosed_subset T)
```

So it reduces to the private value theorem `fullSourceCoeff_jointContinuousOn`.

That theorem proves:

```lean
private theorem fullSourceCoeff_jointContinuousOn ... :
    ContinuousOn
      (fun q : ℝ × ℝ => ∑' n, fullSourceCoeff p u u₀cos q.1 n * cosineMode n q.2)
      (Ioi (0 : ℝ) ×ˢ univ) := by
  have hheat := heatValueSeries_jointContinuousOn u₀cos hu0bd
  have hchemJ := duhamelSeries_jointContinuousOn hchem
  have hlogJ := duhamelSeries_jointContinuousOn hlog
  have hsum := ((hheat.add (hchemJ.const_smul (-p.χ₀))).add hlogJ)
  refine hsum.congr (fun q hq => ?_)
  have := fullSourceCoeff_tsum_split p u u₀cos hu0bd hchem hlog hq
  ...
```

So yes: the value field uses `duhamelSeries_jointContinuousOn` for each Duhamel value leg.

## What the value split needs

The value split theorem is:

```lean
private theorem fullSourceCoeff_tsum_split ...
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u))
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u))
    {q : ℝ × ℝ} (hq : q ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) :
    (∑' n, fullSourceCoeff p u u₀cos q.1 n * cosineMode n q.2) = ...
```

Inside the split, the Duhamel value summability is:

```lean
have hchemS := (duhamelVal_summable' hchem hqp q.2).mul_left (-p.χ₀)
have hlogS := duhamelVal_summable' hlog hqp q.2
```

The helper `duhamelVal_summable'` uses the value envelope:

```lean
private theorem duhamelVal_summable' {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Summable (fun n => duhamelSpectralCoeff a t n * cosineMode n x) := by
  refine Summable.of_norm ((src.henv_summable.mul_left t).of_nonneg_of_le ...)
  ...
  calc |duhamelSpectralCoeff a t n| * |cosineMode n x|
      ≤ (t * src.envelope n) * 1 :=
        mul_le_mul (abs_duhamelSpectralCoeff_le src ht n) ...
```

So the split/summability side is envelope-based. But this is only the pointwise summability used for `tsum_add`; it is not the whole joint-continuity proof.

## What `duhamelSeries_jointContinuousOn` really uses

The proof of `duhamelSeries_jointContinuousOn` has three logically separate parts.

### 1. Per-mode continuity: uses `src.hderiv`

Inside `continuousOn_tsum`, for each mode `n`, it proves continuity of:

```lean
q ↦ duhamelSpectralCoeff a q.1 n * cosineMode n q.2
```

by first proving:

```lean
have hb_cont : Continuous (fun τ => duhamelSpectralCoeff a τ n) :=
  continuous_iff_continuousAt.2
    (fun τ => (duhamelSpectralCoeff_hasDerivAt src τ n).continuousAt)
```

This is a real dependency on `duhamelSpectralCoeff_hasDerivAt src`.

And `duhamelSpectralCoeff_hasDerivAt` itself proves source coefficient continuity from:

```lean
have hcont_an : Continuous (fun s => a s n) :=
  continuous_iff_continuousAt.2 (fun s => (src.hderiv s n).continuousAt)
```

Thus the value-series theorem uses `src.hderiv`, but only to get continuity of `a(·,n)` and hence continuity of the Duhamel coefficient.

### 2. Summable majorant: envelope-only

At a point `p`, the proof sets:

```lean
T := p.1 + 1
```

and on the local open box

```lean
Set.Ioo (p.1 / 2) T ×ˢ Set.univ
```

it uses the summable majorant:

```lean
fun n => T * src.envelope n
```

with summability:

```lean
have hu : Summable (fun n => T * src.envelope n) :=
  src.henv_summable.mul_left T
```

This part is envelope-only.

### 3. Bound on the coefficient: envelope + source continuity/integrability

For the norm bound, it proves:

```lean
|duhamelSpectralCoeff a q.1 n| ≤ T * src.envelope n
```

The estimate itself uses only `src.henv_bound` and `exp ≤ 1`, but to apply integral comparison it first proves integrability via continuity of the integrand:

```lean
have hintegrand_cont : ContinuousOn
    (fun s => Real.exp (-(q.1 - s) * unitIntervalCosineEigenvalue n) * a s n)
    (Set.Icc 0 q.1) :=
  ((Real.continuous_exp.comp ...).mul
    (continuous_iff_continuousAt.2
      (fun s => (src.hderiv s n).continuousAt))).continuousOn
```

Again, `src.hderiv` is used as a way to get source coefficient continuity.

## What is not used by the value theorem

In `duhamelSeries_jointContinuousOn`, I did **not** see use of:

```lean
src.adot
src.hadotcont
src.derivBound
src.hderivBound
```

Those are used in the derivative-series side:

```lean
duhamelDerivSeries_jointContinuousOn
```

whose majorant is:

```lean
src.envelope n + src.derivBound * reciprocalSquareTerm n
```

and whose proof calls:

```lean
duhamelSpectralCoeff_deriv_continuous src n
duhamelSpectralCoeff_deriv_summable_uniform_bound src ...
```

That is a separate theorem, not the value-field joint-solution theorem.

## Consequence for the circularity question

The statement:

```text
VALUE-field joint continuity only uses source envelope.
```

is **false for the current proof** if interpreted literally, because the proof uses `src.hderiv` for source-coefficient continuity.

But the statement:

```text
VALUE-field joint continuity does not need the full source time-derivative package.
```

is **true**.

A weaker interface should be enough:

```lean
structure DuhamelSourceValueRegularity (a : ℝ → ℕ → ℝ) where
  hcont : ∀ n, Continuous (fun s => a s n)
  envelope : ℕ → ℝ
  henv_summable : Summable envelope
  henv_bound : ∀ s, 0 ≤ s → ∀ n, |a s n| ≤ envelope n
```

and a windowed version:

```lean
structure DuhamelSourceValueRegularityOn (a : ℝ → ℕ → ℝ) (lo hi : ℝ) where
  hcontOn : ∀ n, ContinuousOn (fun s => a s n) (Set.Icc lo hi)
  envelope : ℕ → ℝ
  henv_summable : Summable envelope
  henv_bound : ∀ s ∈ Set.Icc lo hi, ∀ n, |a s n| ≤ envelope n
```

Then a new theorem could mirror the value proof without carrying `adot`/`derivBound`:

```lean
import ShenWork.PDE.IntervalSourceCoefficientTimeC1
import ShenWork.Wiener.EWA.SourceJointRegularity

noncomputable section

namespace ShenWork.IntervalSourceCoefficientTimeC1

/-- Proposed refactor target, not currently in the repo. -/
structure DuhamelSourceValueRegularity (a : ℝ → ℕ → ℝ) where
  hcont : ∀ n, Continuous (fun s => a s n)
  envelope : ℕ → ℝ
  henv_summable : Summable envelope
  henv_bound : ∀ s, 0 ≤ s → ∀ n, |a s n| ≤ envelope n

-- theorem duhamelSeries_jointContinuousOn_of_valueRegularity
--     {a : ℝ → ℕ → ℝ} (src : DuhamelSourceValueRegularity a) :
--     ContinuousOn
--       (Function.uncurry
--         (fun (τ : ℝ) (x : ℝ) =>
--           ∑' n, duhamelSpectralCoeff a τ n * cosineMode n x))
--       (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := ...
-- Same proof as `duhamelSeries_jointContinuousOn`, replacing:
--   src.hderiv s n .continuousAt
-- with:
--   src.hcont n
-- and keeping the same `T * src.envelope n` majorant.

end ShenWork.IntervalSourceCoefficientTimeC1
```

For your intended `DuhamelSourceTimeC1On` route, the analogous local theorem should not require the full global `DuhamelSourceTimeC1`. It should consume windowed coefficient continuity and the windowed envelope. If the source is only needed on the slab `Ioo 0 T`, this is the right direction.

## Final verdict

`fullSourceCoeff_jointSolutionClosed` calls only the value Duhamel joint-continuity theorem, not the derivative Duhamel theorem.

But the current `duhamelSeries_jointContinuousOn` proof still depends on `src.hderiv`, because it uses differentiability to prove per-mode continuity of `a(s,n)` and then of `duhamelSpectralCoeff a t n`.

So the circularity is not broken by envelope alone. It can be broken by replacing the source dependency with a **value-only source regularity** interface: coefficient continuity plus envelope/summability/bound. That is strictly weaker than `DuhamelSourceTimeC1` and avoids `adot`, `hadotcont`, `derivBound`, and `hderivBound`.
