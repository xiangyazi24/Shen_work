/-
# T6 spectral route — Duhamel-term `C²`-up-to-boundary regularity (foundations)

This file begins the **spectral-series** attack on `DuhamelTermInteriorC2` (the
conjunct-7 obligation of `localExistence`), abandoning abstract analytic-semigroup
machinery (too heavy for Mathlib) in favour of explicit cosine-series manipulation,
reusing the T1–T5 spectral-kernel infrastructure.

## The Duhamel slice, spectrally

For the full-Neumann-kernel solution the Duhamel term is, mode by mode,

  `D(t,x) = ∑'_n cₙ(t)·cos(nπx)`,   `cₙ(t) = ∫₀ᵗ e^{−(t−s)λₙ}·ĝₙ(s) ds`,

with `λₙ = (nπ)²` the Neumann eigenvalue and `ĝₙ(s)` the `n`-th cosine coefficient of
the source `g(s) = F(u(s))`.  The crude parabolic gain only gives `|cₙ(t)| ≲ 1/λₙ`
(see the `DuhamelHeatValueRepresentation` correction note in
`IntervalDuhamelRegularity.lean`: that is `H^{<3/2}`, NOT `C²`).  The **commutator
split** below is what recovers the extra derivative needed for `∂ₓₓ`:

  `cₙ(t) = ∫₀ᵗ e^{−(t−s)λₙ}·(ĝₙ(s) − ĝₙ(t)) ds   +   (1 − e^{−tλₙ})/λₙ · ĝₙ(t)`
         = (I)ₙ                                  +   (II)ₙ.

* (II)ₙ carries the bounded factor `(1−e^{−tλₙ})/λₙ ≤ 1/λₙ` times `ĝₙ(t)`; once
  multiplied by `λₙ` (for `∂ₓₓ`) it is `(1−e^{−tλₙ})·ĝₙ(t)`, uniformly bounded by
  `‖ĝ(t)‖`, with the cosine-coefficient decay of `ĝₙ(t)` supplying summability.
* (I)ₙ uses the time-modulus of continuity of `s ↦ ĝₙ(s)` near `s = t`: the factor
  `ĝₙ(s) − ĝₙ(t)` vanishes at `s = t`, cancelling the `s → t` singularity that blocks
  naïve differentiation under the integral; `λₙ·(I)ₙ` stays summable.

## Reusable T1–T5 spectral infrastructure (surveyed)

Termwise differentiation / Weierstrass-M:
* `hasDerivAt_tsum`, `hasDerivAt_tsum_of_isPreconnected` (Mathlib) — used throughout
  `IntervalDomainRegularityBootstrap`, `IntervalNeumannFullKernel`,
  `IntervalResolverGradientBridge`, `RegularityBootstrap`, `HeatKernelLpEstimates`.

Cosine heat-value engine (the `C²` core, `IntervalDomainRegularityBootstrap` /
`HeatKernelLpEstimates` / `IntervalFullKernelRegularity`):
* `unitIntervalCosineHeatValue τ a x = ∑'_n e^{−τλₙ}·cos(nπx)·aₙ`,
  `unitIntervalCosineHeatPointWeight t x n = e^{−tλₙ}·cos(nπx)`;
* `unitIntervalCosineHeatValue_hasDerivAt_of_summable_bound`,
  `unitIntervalCosineHeatValue_deriv_of_summable_bound`,
  `unitIntervalCosineHeatGradientValue_hasDerivAt{,_of_summable_bound}`,
  `unitIntervalCosineHeatValue_deriv_eq_gradientValue`;
* `unitIntervalCosineHeatValue_contDiff_two` (`ht : 0 < τ`, `|aₙ| ≤ M` ⟹ `C²`);
* endpoint Neumann: `unitIntervalCosineHeatGradientValue_eq_zero_at_{zero,one}`,
  `unitIntervalCosineHeatValue_deriv_zero_at_endpoint`.

Summability / decay:
* `unitIntervalCosineHeatTrace_single_exp_summable` (`0<t` ⟹ `∑ e^{−tλₙ}` summable),
  `unitIntervalCosineHeatTrace_summable`;
* `parabolicGain_le_one` (`IntervalDuhamelRegularity`): `λ·∫₀ᵗ e^{−(t−s)λ} ds ≤ 1`.

## What this file proves (foundations, convergence-assumption-free)

The pure per-mode **algebraic** backbone of the split, independent of any series
convergence hypothesis (those come next, once the precise summability lemmas are
fixed):
* `intervalExpKernel_time_integral` — `∫₀ᵗ e^{−(t−s)λ} ds = (1 − e^{−tλ})/λ` (λ ≠ 0);
* `duhamelSpectralCoeff_commutator_split` — the additive split `cₙ = (I) + ĝ(t)·∫K`;
* `duhamelSpectralCoeff_commutator_eq` — the closed-form split `cₙ = (I) + (II)`.

No `sorry`/`admit`/custom `axiom`.
-/

import ShenWork.PDE.IntervalDuhamelRegularity

open MeasureTheory intervalIntegral
open scoped Real

noncomputable section

namespace ShenWork.IntervalDuhamelSpectralC2

/-- **The exponential time-kernel integral.**  For `λ ≠ 0`,
`∫₀ᵗ e^{−(t−s)λ} ds = (1 − e^{−tλ})/λ`.  (The antiderivative is
`s ↦ e^{−(t−s)λ}/λ`.)  This is the closed form behind the `(II)` term of the Duhamel
commutator split, and the integral whose `λ`-multiple is the parabolic gain
`1 − e^{−tλ} ≤ 1`. -/
theorem intervalExpKernel_time_integral {t lam : ℝ} (hlam : lam ≠ 0) :
    (∫ s in (0:ℝ)..t, Real.exp (-(t - s) * lam)) = (1 - Real.exp (-t * lam)) / lam := by
  have hderiv : ∀ s : ℝ,
      HasDerivAt (fun s : ℝ => Real.exp (-(t - s) * lam) / lam)
        (Real.exp (-(t - s) * lam)) s := by
    intro s
    have harg : HasDerivAt (fun s : ℝ => -(t - s) * lam) lam s := by
      have h1 : HasDerivAt (fun s : ℝ => -(t - s)) 1 s := by
        have : HasDerivAt (fun s : ℝ => s - t) 1 s := by
          simpa using (hasDerivAt_id s).sub_const t
        refine this.congr_of_eventuallyEq ?_
        filter_upwards with y using by ring
      simpa using h1.mul_const lam
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(t - s) * lam))
        (Real.exp (-(t - s) * lam) * lam) s := harg.exp
    have hdiv := hexp.div_const lam
    simpa [mul_div_assoc, mul_div_cancel_right₀, hlam] using hdiv
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [sub_self, neg_zero, zero_mul, Real.exp_zero]
  rw [show -(t - 0) * lam = -t * lam by ring]
  ring

/-- **Duhamel commutator split (additive form).**  The Duhamel spectral coefficient
`cₙ(t) = ∫₀ᵗ e^{−(t−s)λ}·ĝ(s) ds` splits as

  `∫₀ᵗ e^{−(t−s)λ}·(ĝ(s) − ĝ(t)) ds  +  ĝ(t)·∫₀ᵗ e^{−(t−s)λ} ds`.

This is exact for any `λ` and any continuous coefficient-in-time `ĝ` — pure
integral additivity plus pulling out the constant `ĝ(t)`.  It is the algebraic
backbone of the `s → t` singularity cancellation; no convergence hypothesis. -/
theorem duhamelSpectralCoeff_commutator_split
    {t lam : ℝ} {ghat : ℝ → ℝ} (hg : Continuous ghat) :
    (∫ s in (0:ℝ)..t, Real.exp (-(t - s) * lam) * ghat s)
      = (∫ s in (0:ℝ)..t, Real.exp (-(t - s) * lam) * (ghat s - ghat t))
        + ghat t * (∫ s in (0:ℝ)..t, Real.exp (-(t - s) * lam)) := by
  have hkernel : Continuous (fun s : ℝ => Real.exp (-(t - s) * lam)) := by fun_prop
  have hI1 : IntervalIntegrable
      (fun s => Real.exp (-(t - s) * lam) * (ghat s - ghat t)) volume 0 t :=
    (hkernel.mul (hg.sub continuous_const)).intervalIntegrable 0 t
  have hI2 : IntervalIntegrable
      (fun s => Real.exp (-(t - s) * lam) * ghat t) volume 0 t :=
    (hkernel.mul continuous_const).intervalIntegrable 0 t
  have key : (∫ s in (0:ℝ)..t, Real.exp (-(t - s) * lam) * ghat s)
      = (∫ s in (0:ℝ)..t, Real.exp (-(t - s) * lam) * (ghat s - ghat t))
        + (∫ s in (0:ℝ)..t, Real.exp (-(t - s) * lam) * ghat t) := by
    rw [← intervalIntegral.integral_add hI1 hI2]
    exact intervalIntegral.integral_congr (fun s _ => by ring)
  rw [key]
  congr 1
  rw [intervalIntegral.integral_mul_const, mul_comm]

/-- **Duhamel commutator split (closed form).**  Combining the additive split with
`intervalExpKernel_time_integral`, for `λ ≠ 0`,

  `cₙ(t) = ∫₀ᵗ e^{−(t−s)λ}·(ĝ(s) − ĝ(t)) ds  +  (1 − e^{−tλ})/λ · ĝ(t)`
         = (I)                                +  (II).

This is the spectral-route algebraic foundation: (II) is the bounded
parabolic-gain term, (I) carries the time modulus of continuity that cancels the
`s → t` singularity. -/
theorem duhamelSpectralCoeff_commutator_eq
    {t lam : ℝ} {ghat : ℝ → ℝ} (hlam : lam ≠ 0) (hg : Continuous ghat) :
    (∫ s in (0:ℝ)..t, Real.exp (-(t - s) * lam) * ghat s)
      = (∫ s in (0:ℝ)..t, Real.exp (-(t - s) * lam) * (ghat s - ghat t))
        + (1 - Real.exp (-t * lam)) / lam * ghat t := by
  rw [duhamelSpectralCoeff_commutator_split hg, intervalExpKernel_time_integral hlam]
  ring

end ShenWork.IntervalDuhamelSpectralC2
