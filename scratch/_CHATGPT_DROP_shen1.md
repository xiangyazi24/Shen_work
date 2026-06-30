# Q2461 shen1 — honest precrossing interval skeleton for integrated Moser

Repo: `xiangyazi24/Shen_work`

Target local file: `ShenWork/PDE/P3MoserIntegratedClosure.lean`

Remote note: the public `main` copy visible to me still has the earlier integrated-closure skeleton and does **not** contain the new local lemmas named in the prompt.  The patch below is therefore written against the APIs exactly as described in Q2461, and is meant to be pasted **after** the compiled local lemmas:

```lean
integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds
intervalIntegral_max_one_le_length_mul_max_one_of_Icc_bound
integratedMoser_maxOneEnergy_timeIntegral_le_of_Icc_bound
intervalIntegral_le_const_mul_integral_add_length_mul_const_of_le_on
relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_bound
relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound
```

The important design constraint is: this skeleton never concludes

```lean
LpPowerBoundedBefore D (p + rho) T u
```

from a time-integral estimate.  It concludes only a bound on

```lean
∫ s in a..b, D.integral (fun x => (u s x) ^ (p + rho))
```

or its interval average.  That is the honest next step: no pointwise extraction, no hidden first-crossing supremum theorem, and no fake `LpPowerBoundedBefore` conversion.

## Minimal patch

Paste this near the end of `P3MoserIntegratedClosure.lean`, inside the existing namespace

```lean
namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

and before the namespace-ending lines.

```lean
/-! ### Honest precrossing interval skeleton

This section is deliberately weaker than `IntegratedMoserFirstCrossingStep`.
A precrossing window `[a,b]` carries a current `p`-energy bound on that
window, and the integrated dissipation estimate gives an integrated gradient
bound on that same window.  Relative Moser then gives only a time-integral
bound for the higher power on `[a,b]`.

There is no theorem here producing `LpPowerBoundedBefore D (p + rho) T u`.
That pointwise extraction is a separate analytic/measure-theoretic frontier.
-/

section PrecrossingInterval

/-- Data available on a genuine precrossing interval.

Fields `ha_pos` and `hb_lt` are included because the relative-Moser pointwise
input is normally available only for interior times `0 < t < T`; the interval
integral ignores endpoints, but the existing helper proving the integrated
relative estimate still needs an interior window.  The closed endpoint fields
`haT` and `hbT` are kept explicitly because
`integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds` takes
exactly those endpoint-membership hypotheses.

`right_currentLp_nonneg` is also explicit.  In PDE applications it should come
from positivity/nonnegativity of `u` plus positivity of the abstract integral,
but that is not part of `BoundedDomainData`; do not fake it here.
-/
structure IntegratedMoserPrecrossingIntervalData
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 p a b M : ℝ) : Prop where
  hp : p0 ≤ p
  hp_nonneg : 0 ≤ p
  hab : a < b
  ha_pos : 0 < a
  hb_lt : b < T
  haT : a ∈ Set.Icc (0 : ℝ) T
  hbT : b ∈ Set.Icc a T
  currentLp_le_Icc :
    ∀ s ∈ Set.Icc a b,
      D.integral (fun x => (u s x) ^ p) ≤ M
  right_currentLp_nonneg :
    0 ≤ D.integral (fun x => (u b x) ^ p)
  higherPower_intervalIntegrable :
    IntervalIntegrable
      (fun s => D.integral (fun x => (u s x) ^ (p + rho)))
      MeasureTheory.volume a b
  gradient_intervalIntegrable :
    IntervalIntegrable
      (fun s =>
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2))
      MeasureTheory.volume a b

namespace IntegratedMoserPrecrossingIntervalData

/-- Left-end current-energy bound extracted from the precrossing window. -/
theorem left_currentLp_le
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M : ℝ}
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p0 p a b M) :
    D.integral (fun x => (u a x) ^ p) ≤ M :=
  hI.currentLp_le_Icc a ⟨le_rfl, hI.hab.le⟩

/-- Max-one time-integral control from the precrossing current-energy bound.

This is the honest source of the `hmaxInt` argument for the extraction lemma.
It uses the compiled local helper rather than proving a new interval-integral
fact here.
-/
theorem maxOne_timeIntegral_le
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M : ℝ}
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p0 p a b M) :
    (∫ s in a..b,
      max 1 (D.integral (fun x => (u s x) ^ p))) ≤
        (b - a) * max 1 M := by
  exact
    integratedMoser_maxOneEnergy_timeIntegral_le_of_Icc_bound
      (D := D) (u := u) (p := p) (a := a) (b := b) (M := M)
      hI.hab.le hI.currentLp_le_Icc

end IntegratedMoserPrecrossingIntervalData

/-- Integrated Moser extraction on a precrossing interval.

This is the signature-sensitive call.  It matches the Q2461 extraction API:
`hinteg, hp, hp_nonneg, haT, hbT, hYa, hYb_nonneg, hmaxInt`.
-/
theorem integratedMoser_precrossing_gradientIntegral_le
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M : ℝ}
    (hinteg : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p0 p a b M) :
    ∃ C, 2 *
      (∫ s in a..b,
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)) ≤
        M + C * p * ((b - a) * max 1 M) := by
  exact
    integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds
      (hinteg := hinteg)
      (hp := hI.hp)
      (hp_nonneg := hI.hp_nonneg)
      (haT := hI.haT)
      (hbT := hI.hbT)
      (hYa := hI.left_currentLp_le)
      (hYb_nonneg := hI.right_currentLp_nonneg)
      (hmaxInt := hI.maxOne_timeIntegral_le)

/-- A one-sided gradient integral bound, with the harmless factor `2` removed.

This is often the most convenient form to feed to the integrated relative-Moser
helper.
-/
theorem integratedMoser_precrossing_gradientIntegral_bound
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M : ℝ}
    (hinteg : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p0 p a b M) :
    ∃ Gbar,
      (∫ s in a..b,
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)) ≤ Gbar := by
  rcases integratedMoser_precrossing_gradientIntegral_le hinteg hI with
    ⟨C, hC⟩
  refine ⟨(M + C * p * ((b - a) * max 1 M)) / 2, ?_⟩
  nlinarith

/-- The honest higher-power conclusion from an integrated relative-Moser
consumer.

The argument `hhigher` is intentionally time-integrated:
from a gradient integral bound on `[a,b]`, it returns a time-integral bound for
`Y_{p+rho}` on `[a,b]`.  This is exactly what the local helper
`relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound`
should provide from `RelativeMoserInterpolationBefore`, the current `p`-energy
bound on the same Icc window, and interval integrability.

Keeping `hhigher` as an argument makes this core wrapper robust to small binder
name/order changes in the local relative-Moser helper, while the previous theorem
above still checks the extraction call with the exact Q2461 signature.
-/
theorem integratedMoser_precrossing_higherPower_timeIntegral_le_of_integrated_relative
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M : ℝ}
    (hinteg : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p0 p a b M)
    (hhigher :
      ∀ Gbar,
        (∫ s in a..b,
          D.integral (fun x =>
            (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)) ≤ Gbar →
          ∃ Zbar,
            (∫ s in a..b,
              D.integral (fun x => (u s x) ^ (p + rho))) ≤ Zbar) :
    ∃ Zbar,
      (∫ s in a..b,
        D.integral (fun x => (u s x) ^ (p + rho))) ≤ Zbar := by
  rcases integratedMoser_precrossing_gradientIntegral_bound hinteg hI with
    ⟨Gbar, hGbar⟩
  exact hhigher Gbar hGbar

/-- Average version of the previous time-integral conclusion.

This is still not a pointwise estimate.  It only bounds the interval average,
represented as `(1 / (b - a)) * ∫ ...`.
-/
theorem integratedMoser_precrossing_higherPower_average_le_of_integrated_relative
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M : ℝ}
    (hinteg : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p0 p a b M)
    (hhigher :
      ∀ Gbar,
        (∫ s in a..b,
          D.integral (fun x =>
            (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)) ≤ Gbar →
          ∃ Zbar,
            (∫ s in a..b,
              D.integral (fun x => (u s x) ^ (p + rho))) ≤ Zbar) :
    ∃ Zavg,
      (1 / (b - a)) *
        (∫ s in a..b,
          D.integral (fun x => (u s x) ^ (p + rho))) ≤ Zavg := by
  rcases
    integratedMoser_precrossing_higherPower_timeIntegral_le_of_integrated_relative
      hinteg hI hhigher with
    ⟨Zbar, hZbar⟩
  refine ⟨(1 / (b - a)) * Zbar, ?_⟩
  have hscale_nonneg : 0 ≤ 1 / (b - a) := by
    exact div_nonneg zero_le_one (sub_nonneg.mpr hI.hab.le)
  exact mul_le_mul_of_nonneg_left hZbar hscale_nonneg

end PrecrossingInterval
```

## Direct adapter to the local relative-Moser helper

If your local theorem

```lean
relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound
```

has the natural Q2451-style argument order, the `hhigher` argument above should be instantiated as follows.  This is intentionally separate from the core wrapper above, because the remote branch I can inspect does not contain the local helper signature.

```lean
have hhigher :
    ∀ Gbar,
      (∫ s in a..b,
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)) ≤ Gbar →
        ∃ Zbar,
          (∫ s in a..b,
            D.integral (fun x => (u s x) ^ (p + rho))) ≤ Zbar := by
  intro Gbar hGbar
  exact
    relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound
      (D := D) (u := u) (T := T) (rho := rho) (p0 := p0)
      (p := p) (a := a) (b := b) (Cp := M) (Gbound := Gbar)
      hrel hI.hp hI.hab.le hI.ha_pos hI.hb_lt
      hI.higherPower_intervalIntegrable
      hI.gradient_intervalIntegrable
      hI.currentLp_le_Icc
      hGbar
```

Then the final call is just:

```lean
exact
  integratedMoser_precrossing_higherPower_timeIntegral_le_of_integrated_relative
    hinteg hI hhigher
```

If the local helper uses binder names like `M` instead of `Cp`, or `Gbar` instead of `Gbound`, keep the same explicit hypotheses and change only those named arguments.  The proof obligation should remain a time-integral bound, not a pointwise `LpPowerBoundedBefore` claim.

## Why these assumptions are honest

* `0 ≤ p` is not cosmetic: your extraction lemma explicitly asks for `hp_nonneg`.  Do not try to recover it from `p0 ≤ p` unless the caller also carries `0 ≤ p0` or a stronger bootstrap threshold.
* `a < b` is needed for the average statement and gives the `a ≤ b` orientation required by the interval-integral helper.  For only the raw time-integral statement, `a ≤ b` is usually enough, but the precrossing interval should be nondegenerate anyway.
* `0 < a` and `b < T` are needed by the relative-Moser pointwise input, which is stated on `0 < t < T`.  The integrated dissipation extraction itself only needs the closed endpoint hypotheses `a ∈ Icc 0 T` and `b ∈ Icc a T`.
* `right_currentLp_nonneg` should come from PDE positivity/nonnegativity plus an integral-positivity lemma.  It is not derivable from the bare abstract `BoundedDomainData` interface.
* The `IntervalIntegrable` fields are included because the helper chain integrating relative-Moser inequalities needs time-integrability of the higher-power profile and the Moser-gradient profile on `a..b`.  If your local helper obtains these from `IntegratedMoserFirstCrossingRegularity`, replace these fields by that regularity package plus small interval-restriction lemmas.

## No-go statement

The following theorem would be dishonest at this stage and should **not** be added:

```lean
theorem bad_precrossing_to_LpPowerBoundedBefore ... :
    LpPowerBoundedBefore D (p + rho) T u := by
  ...
```

A bound on `∫_{a}^{b} Y_{p+rho}(s) ds` or on the average over one precrossing window does not provide a uniform pointwise bound for all `0 < t < T`.  The missing input would be a genuine pointwise extraction/regularization theorem, or a first-crossing argument with continuity and a window-selection lemma strong enough to convert average control into endpoint control.  That is a real next frontier, not routine Lean plumbing.
