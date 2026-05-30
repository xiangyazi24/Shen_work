/-
# Interior-`C²` of the Duhamel inhomogeneous term

This file discharges the named predicate `DuhamelTermInteriorC2` introduced in
`IntervalFullKernelRegularity.lean`: the spatial interior-`C²` regularity of the
Duhamel time-integral

  `D(t,x) = ∫₀ᵗ (e^{(t-s)Δ_N} F(u(s)))(x) ds`,

i.e. the time-integral of a spatially-`C²` family of full-kernel semigroup
profiles.  With this, the localExistence interior-`C²` obligation (third conjunct
of `intervalDomainClassicalRegularity`) is fully discharged for full-kernel
solutions: the pure-propagator part is already done in
`IntervalFullKernelRegularity.lean`, this file closes the inhomogeneous part.

## The mathematical content and how the `s → t` singularity is handled

For each fixed `s < t` the inner profile `S(t−s)[F(u(s))]` is spatially `C²` on
`(0,1)` (it is a full-kernel semigroup profile of the *continuous bounded* source
`F(u(s))`, by `intervalFullSemigroupProfile_contDiffOn_two`).  Commuting `∂ₓ`,
`∂ₓₓ` with `∫₀ᵗ ds` (differentiation under the integral) naively asks for a
locally-uniform integrable-in-`s` majorant of the *second* `x`-derivative.  The
Gaussian-tail smoothing bound is

  `‖∂ₓₓ S(t−s) g‖_∞ ≤ C (t−s)^{−1} ‖g‖_∞`        (cf. `real_eigen_exp_le`)

and `(t−s)^{−1}` is **not** integrable at `s = t`.  The standard fix is the
**parabolic gain at the spectral/coefficient level**: after the Fubini swap of
`∫₀ᵗ ds` with the cosine `∑'_n`, the Duhamel term agrees on `(0,1)` with a single
cosine series

  `D(t,x) = ∑'_n b_n(t) · cos(nπ x)`,   `b_n(t) = ∫₀ᵗ e^{−(t−s) λ_n} ĝ_n(s) ds`,

whose *second-derivative coefficient* is uniformly bounded:

  `(nπ)² |b_n(t)| ≤ ‖g‖_∞ · (nπ)² ∫₀ᵗ e^{−(t−s)(nπ)²} ds`
                 `= ‖g‖_∞ · (1 − e^{−t(nπ)²}) ≤ ‖g‖_∞`.

The `(nπ)²` that would diverge pointwise in `s` is **absorbed** exactly by the
time integral — no `(t−s)^{−1}` blow-up survives, because
`(nπ)² ∫₀ᵗ e^{−(t−s)(nπ)²} ds = 1 − e^{−t(nπ)²} ≤ 1`.  This is precisely the
parabolic regularising gain.

Consequently the Duhamel slice is, on `(0,1)`, a cosine **heat value**
`unitIntervalCosineHeatValue τ b` (for an effective `τ > 0` and a bounded
coefficient sequence `b`), and the already-proven spatial-`C²` engine
`unitIntervalCosineHeatValue_contDiff_two` applies verbatim.

## What is proved clean here (no `sorry`/`admit`/axiom)

* `intervalDuhamelTerm_interiorC2_of_eqOn_heatValue` — `DuhamelTermInteriorC2 T w`
  holds whenever every Duhamel slice `w t` (`t ∈ (0,T)`) agrees on `(0,1)` with a
  bounded-coefficient cosine heat value.  This is the full reduction to the
  spatial-`C²` engine and discharges the predicate.
* `DuhamelHeatValueRepresentation` — the precise named predicate isolating the
  Fubini/parabolic-gain step that produces the heat-value representation of each
  Duhamel slice with a *bounded* coefficient sequence.
* `intervalDuhamelTerm_interiorC2` — `DuhamelTermInteriorC2 T w` from
  `DuhamelHeatValueRepresentation`, i.e. the predicate closes once the
  representation step is supplied.

## Remaining gap (named precisely)

The only step *not* reduced to already-proven Mathlib/repo lemmas is the
`DuhamelHeatValueRepresentation` hypothesis: the Fubini interchange of `∫₀ᵗ ds`
with the cosine `∑'_n`, producing the time-integrated coefficient
`b_n(t) = ∫₀ᵗ e^{−(t−s)λ_n} ĝ_n(s) ds`, **together with the parabolic-gain bound**
`(nπ)² |b_n(t)| ≤ ‖g‖_∞`.  The bound is the honest resolution of the `s → t`
singularity: it is finite and `n`-uniform precisely because the time integral
`(nπ)² ∫₀ᵗ e^{−(t−s)(nπ)²} ds = 1 − e^{−t(nπ)²}` cancels the `(nπ)²`.  This step
is elementary analysis (a one-dimensional `∫ e^{−(t−s)λ} ds = (1−e^{−tλ})/λ`
computation plus Fubini for the cosine series, dominated by the summable Gaussian
weight), but it is not yet formalised; it is named here as the single residual
obligation.
-/

import ShenWork.PDE.IntervalFullKernelRegularity

open MeasureTheory
open scoped Real

noncomputable section

namespace ShenWork.IntervalDuhamelRegularity

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainRegularityBootstrap
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalFullKernelRegularity

/-! ## The parabolic-gain coefficient bound (the `s → t` singularity, resolved)

The single elementary spectral fact behind the resolution of the `s → t`
singularity: the time integral of the heat factor times `(nπ)²` is uniformly
bounded by `1`.  This is what makes the Duhamel second-derivative coefficient
bounded even though the pointwise-in-`s` second-derivative bound `(t−s)^{−1}` is
not integrable. -/

/-- **Parabolic gain.**  For `λ ≥ 0` and `t ≥ 0`, the `λ`-weighted time integral
`λ ∫₀ᵗ e^{−(t−s)λ} ds = 1 − e^{−tλ} ≤ 1`.  The eigenvalue weight `λ = (nπ)²`
multiplying the heat factor is absorbed by the time integral, with a `1`-uniform
bound — this is the cancellation that kills the naive `(t−s)^{−1}` blow-up at
`s = t`. -/
theorem parabolicGain_le_one {lam t : ℝ} (hlam : 0 ≤ lam) (_ht : 0 ≤ t) :
    lam * (∫ s in (0:ℝ)..t, Real.exp (-(t - s) * lam)) ≤ 1 := by
  -- ∫₀ᵗ e^{−(t−s)λ} ds = (1 − e^{−tλ}) / λ  (λ > 0); the λ-multiple is 1 − e^{−tλ}.
  rcases eq_or_lt_of_le hlam with hlam0 | hlampos
  · -- λ = 0: the product is 0 ≤ 1.
    simp [← hlam0]
  · -- λ > 0.  Compute the integral via the antiderivative s ↦ e^{−(t−s)λ}/λ.
    have hint : (∫ s in (0:ℝ)..t, Real.exp (-(t - s) * lam))
        = (1 - Real.exp (-t * lam)) / lam := by
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
        have := hexp.div_const lam
        have hlam_ne : lam ≠ 0 := ne_of_gt hlampos
        simpa [mul_div_assoc, mul_div_cancel_right₀, hlam_ne] using this
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s _ => hderiv s)
        (by
          apply Continuous.intervalIntegrable
          fun_prop)]
      simp only [sub_self, neg_zero, zero_mul, Real.exp_zero]
      rw [show -(t - 0) * lam = -t * lam by ring]
      ring
    rw [hint]
    have hlam_ne : lam ≠ 0 := ne_of_gt hlampos
    rw [mul_div_assoc']
    rw [mul_comm lam (1 - Real.exp (-t * lam)), mul_div_assoc,
      div_self hlam_ne, mul_one]
    -- 1 − e^{−tλ} ≤ 1 since e^{−tλ} ≥ 0.
    have : 0 ≤ Real.exp (-t * lam) := Real.exp_nonneg _
    linarith

/-! ## Reduction of `DuhamelTermInteriorC2` to a bounded-coefficient heat value -/

/-- **Reduction of the Duhamel interior-`C²` predicate.**  If every Duhamel slice
`w t` (for `t ∈ (0,T)`) agrees on the open interior `(0,1)` with a cosine
**heat value** `unitIntervalCosineHeatValue τ b` for some `τ > 0` and some
*bounded* coefficient sequence `b`, then `DuhamelTermInteriorC2 T w` holds.

This is the full reduction to the already-proven spatial-`C²` engine
`unitIntervalCosineHeatValue_contDiff_two`.  The mathematical content delivering
such a `(τ, b)` representation — Fubini of `∫₀ᵗ ds` with the cosine `∑'_n`, and
the parabolic-gain bound `(nπ)²|b_n| ≤ ‖g‖_∞` of `parabolicGain_le_one` ensuring
`b` is bounded — is isolated as the hypothesis below. -/
theorem intervalDuhamelTerm_interiorC2_of_eqOn_heatValue
    {T : ℝ} {w : ℝ → intervalDomainPoint → ℝ}
    (hrep : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
      ∃ τ : ℝ, 0 < τ ∧ ∃ b : ℕ → ℝ, ∃ M : ℝ, (∀ n, |b n| ≤ M) ∧
        Set.EqOn (intervalDomainLift (w t))
          (fun x => unitIntervalCosineHeatValue τ b x) (Set.Ioo (0 : ℝ) 1)) :
    DuhamelTermInteriorC2 T w := by
  intro t ht
  obtain ⟨τ, hτ, b, M, hM, heq⟩ := hrep t ht
  exact intervalDomainLift_contDiffOn_two_of_eqOn_heatValue hτ hM heq

/-! ## Named representation predicate (the residual Fubini/parabolic-gain step) -/

/-- **The single residual obligation.**  The Fubini interchange producing the
heat-value representation of each Duhamel slice with a *bounded* coefficient
sequence.  Mathematically:

  `D(t,x) = ∫₀ᵗ S(t−s)[F(u(s))](x) ds = ∑'_n b_n(t) cos(nπ x)`,
  `b_n(t) = ∫₀ᵗ e^{−(t−s)λ_n} ĝ_n(s) ds`,   `(nπ)²|b_n(t)| ≤ ‖g‖_∞`,

so that on `(0,1)` the slice agrees with a bounded-coefficient cosine heat value.
The boundedness of `b` is exactly the parabolic gain `parabolicGain_le_one`
applied at each mode — this is where the `s → t` singularity is honestly
resolved.  We package the *output* of this step (existence of a bounded-coeff
heat-value representation) as a predicate; supplying it discharges
`DuhamelTermInteriorC2`. -/
def DuhamelHeatValueRepresentation (T : ℝ) (w : ℝ → intervalDomainPoint → ℝ) : Prop :=
  ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
    ∃ τ : ℝ, 0 < τ ∧ ∃ b : ℕ → ℝ, ∃ M : ℝ, (∀ n, |b n| ≤ M) ∧
      Set.EqOn (intervalDomainLift (w t))
        (fun x => unitIntervalCosineHeatValue τ b x) (Set.Ioo (0 : ℝ) 1)

/-- **`DuhamelTermInteriorC2` from the representation.**  Given the
`DuhamelHeatValueRepresentation` (the Fubini/parabolic-gain step), the Duhamel
interior-`C²` predicate is discharged. -/
theorem intervalDuhamelTerm_interiorC2
    {T : ℝ} {w : ℝ → intervalDomainPoint → ℝ}
    (hrep : DuhamelHeatValueRepresentation T w) :
    DuhamelTermInteriorC2 T w :=
  intervalDuhamelTerm_interiorC2_of_eqOn_heatValue hrep

/-! ## ⚠ CORRECTION (2026-05-30): `DuhamelHeatValueRepresentation` is OVER-STRONG —
NOT an "elementary Fubini" step (verified definition-level finding)

The header above calls `DuhamelHeatValueRepresentation` "elementary analysis (a
one-dimensional integral plus Fubini)".  **That characterisation is wrong**, and
the predicate as stated (a *bounded* coefficient sequence `b` at a *fixed* `τ > 0`)
is in general **FALSE** for the Duhamel term of a merely-bounded source.  The reason
is exactly the regularity the heat-value form encodes:

* `unitIntervalCosineHeatValue_contDiff_two` derives `C²` (indeed `C^∞`,
  real-analytic) from *only* `τ > 0` and `|b n| ≤ M`, because the factor
  `e^{−τ λ_n}` Gaussian-dominates every polynomial in `λ_n`.  So asserting
  `lift (D_t) = ∑ₙ e^{−τλ_n} bₙ cos(nπ·)` with bounded `b` is asserting `D_t` is
  `C^∞` in space.
* But `D_t(x) = ∑ₙ cₙ(t) cos(nπx)` with
  `cₙ(t) = ∫₀ᵗ e^{−(t−s)λ_n} ĝ_{s,n} ds`, and the parabolic gain
  (`parabolicGain_le_one`) gives only `λ_n |cₙ(t)| ≤ ‖g‖_∞`, i.e. `|cₙ(t)| ≲ 1/λ_n
  ~ 1/n²`.  This is `H^{s}` for `s < 3/2` — `C⁰` but **not** `C²`.  Writing
  `cₙ(t) = e^{−τλ_n} bₙ` forces `bₙ = cₙ(t) e^{τλ_n}`; the `s≈t` part of the time
  integral contributes `~ (1/λ_n) e^{τλ_n} → ∞`, so `b` is **unbounded** for any
  `τ > 0`.  (The `s` away from `t` part is fine; the singularity is at `s = t`.)

**Consequence.**  The boundedness of `b` (= the `C^∞` heat-value claim) genuinely
requires the source `g_s = F(u(s))` to have *spatial regularity* (decaying cosine
coefficients), not just an `L^∞` bound — i.e. it couples to the regularity
bootstrap of the constructed solution.  `intervalDuhamelTerm_interiorC2_of_eqOn_heatValue`
is therefore a valid reduction only when such a representation *exists*, which is
not "elementary"; for a generic bounded source it does not exist.

**Honest path to `DuhamelTermInteriorC2` (the real B1 atom).**  Prove `∂ₓₓ D_t`
directly, NOT via a heat-value form.  Differentiating the kernel twice fails (the
`∂ₓₓ K_full(t−s,·)` bound `~ (t−s)^{−3/2}` is non-integrable in `s` at `s=t`); the
correct route uses the heat-equation identity `∂ₓₓ S(r) = ∂_r S(r)` and an
integration by parts **in time** to move one derivative onto `∂_s g_s` (plus the
`S(0)=id` approximate-identity boundary term), which needs `g_s` to be `C¹` in `s`
— again a genuine coupling to the solution's joint regularity, not Fubini.  This is
the genuine deep content of `localExistence` (T6) and is not closable from the
crude parabolic gain alone. -/

end ShenWork.IntervalDuhamelRegularity
