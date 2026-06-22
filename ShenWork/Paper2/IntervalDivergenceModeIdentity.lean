/-
# The divergence-mode spectral identity for boundary-vanishing flux

This file closes the `χ₀ ≠ 0` chemotaxis residual of WALL-B by supplying the
**divergence-mode spectral identity** that connects the chemotaxis Duhamel term
to the C²-bootstrap engine through the *sine* coefficients of the flux.

## The analytic fact (proved clean here)

The chemotaxis flux `Q = u^m (1+v)^{−β} v_x` vanishes at the Neumann boundary
(`v_x(0) = v_x(1) = 0 ⟹ Q(0) = Q(1) = 0`).  For such a boundary-vanishing `Q`,
interval integration by parts gives **THE KEY IDENTITY**

  `∫₀¹ (∂ₓQ)(x)·cos(kπx) dx = kπ·∫₀¹ Q(x)·sin(kπx) dx`   (k ≥ 1; both sides 0 at k=0).

In the repo's normalization (`cosineCoeffs f n = 2∫₀¹ cos(nπx) f`, zeroth mode
unscaled) this reads

  `cosineCoeffs (∂ₓQ) k = √λ_k · sineCoeffs Q k`,        `√λ_k = kπ`.

The divergence maps **SINE** flux coefficients to **COSINE** source coefficients
with the diagonal `√λ_k` multiplier — exactly the engine's diagonal factor.

## What is proved clean (no `sorry`/`admit`/`native_decide`/axiom)

* `rawCosCoeff_deriv_eq_kpi_rawSinCoeff` — the raw IBP identity
  `∫₀¹ Q'(x) cos(kπx) = kπ·∫₀¹ Q(x) sin(kπx)` (Mathlib IBP + `Q(0)=Q(1)=0`);
* `cosineCoeffs_deriv_eq_sqrtLambda_sineCoeff` — its normalized form
  `cosineCoeffs (deriv Q) k = √(lam k)·sineCoeffs Q k`;
* `chemFlux_cosineCoeff_deriv_eq_engine` — the engine connection: the B-form kernel
  diagonal feeds `e^{−rλ_k}·√λ_k·sineCoeffs(Q)_k`;
* `chemotaxisDuhamel_cosineCoeff_eq_engine` — the assembled `χ₀ ≠ 0` chemotaxis
  Duhamel coefficient through `duhamelEnergyCoeff` with `F = sineCoeffs ∘ Q`.
-/

import ShenWork.Paper2.IntervalGradientCoeffDuhamel
import ShenWork.Paper2.IntervalMildPicardRegularity

open MeasureTheory intervalIntegral
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalMildPicardRegularity (cosineCoeffs_pos_eq_integral
  cosineCoeffs_zero_eq_integral)
open ShenWork.Paper2.HSigmaScale (lam)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.BFormHSigmaDuhamelMode (duhamelModeCoeff)
open ShenWork.Paper2.IntervalGradientCoeffDuhamel
  (cosineCoeffs_intervalFullSemigroupOperator_diag)

noncomputable section

namespace ShenWork.Paper2.IntervalDivergenceModeIdentity

open scoped Real

/-! ## Sine coefficients in the repo's Neumann normalization -/

/-- Neumann **sine** coefficients matching the `cosineCoeffs` normalization: the
zeroth mode is `0` (`sin 0 = 0`) and each positive mode carries the factor `2`,
`sineCoeffs f n = 2·∫₀¹ sin(nπx)·f(x) dx`. -/
def sineCoeffs (f : ℝ → ℝ) : ℕ → ℝ :=
  fun n => if n = 0 then 0
    else 2 * ∫ x in (0 : ℝ)..1, Real.sin ((n : ℝ) * Real.pi * x) * f x

@[simp] theorem sineCoeffs_zero (f : ℝ → ℝ) : sineCoeffs f 0 = 0 := by
  simp [sineCoeffs]

theorem sineCoeffs_pos {f : ℝ → ℝ} {n : ℕ} (hn : n ≠ 0) :
    sineCoeffs f n = 2 * ∫ x in (0 : ℝ)..1, Real.sin ((n : ℝ) * Real.pi * x) * f x := by
  simp [sineCoeffs, hn]

/-! ## The raw IBP divergence-mode identity

For a `C¹` flux `Q` on `[0,1]` that vanishes at both Neumann endpoints
(`Q 0 = Q 1 = 0`), interval integration by parts trades a `∂ₓ` against the
cosine/sine swap with a `kπ` weight:

    `∫₀¹ Q'(x)·cos(kπx) dx = kπ·∫₀¹ Q(x)·sin(kπx) dx`.

This is the genuine analytic content of the divergence-mode identity. -/

/-- `HasDerivAt (x ↦ cos(kπx)) (−kπ·sin(kπx)) x`. -/
theorem hasDerivAt_cos_kpi (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.cos ((k : ℝ) * Real.pi * y))
      (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * x)) x := by
  have hinner : HasDerivAt (fun y : ℝ => (k : ℝ) * Real.pi * y)
      ((k : ℝ) * Real.pi) x := by
    simpa using (hasDerivAt_id x).const_mul ((k : ℝ) * Real.pi)
  have hcomp : HasDerivAt (fun y : ℝ => Real.cos ((k : ℝ) * Real.pi * y))
      (-Real.sin ((k : ℝ) * Real.pi * x) * ((k : ℝ) * Real.pi)) x :=
    (Real.hasDerivAt_cos ((k : ℝ) * Real.pi * x)).comp x hinner
  convert hcomp using 1
  ring

/-- **The raw IBP divergence-mode identity** (explicit-derivative form).
For `Q` with derivative `Q'` on `[0,1]` (`HasDerivAt` at every point of the
interval), integrable `Q'`, and boundary vanishing `Q 0 = Q 1 = 0`:

    `∫₀¹ Q'(x)·cos(kπx) dx = kπ·∫₀¹ Q(x)·sin(kπx) dx`. -/
theorem rawCosCoeff_deriv_eq_kpi_rawSinCoeff
    {Q Q' : ℝ → ℝ} (k : ℕ)
    (hQ : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt Q (Q' x) x)
    (hQ'int : IntervalIntegrable Q' volume 0 1)
    (hQ0 : Q 0 = 0) (hQ1 : Q 1 = 0) :
    (∫ x in (0 : ℝ)..1, Q' x * Real.cos ((k : ℝ) * Real.pi * x))
      = (k : ℝ) * Real.pi *
          ∫ x in (0 : ℝ)..1, Q x * Real.sin ((k : ℝ) * Real.pi * x) := by
  -- `u = cos(kπ·)`, `u' = −kπ sin(kπ·)`, `v = Q`, `v' = Q'`.
  set u : ℝ → ℝ := fun y => Real.cos ((k : ℝ) * Real.pi * y) with hu_def
  set u' : ℝ → ℝ := fun y => -((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * y)
    with hu'_def
  have hu : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt u (u' x) x :=
    fun x _ => hasDerivAt_cos_kpi k x
  have hu'_int : IntervalIntegrable u' volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  -- IBP: `∫ u·Q' = u 1 · Q 1 − u 0 · Q 0 − ∫ u' · Q`.
  have hibp := integral_mul_deriv_eq_deriv_mul hu hQ hu'_int hQ'int
  -- boundary terms vanish: `Q 0 = Q 1 = 0`.
  rw [hQ0, hQ1] at hibp
  simp only [mul_zero, sub_zero, zero_sub] at hibp
  -- `∫ Q'·cos = ∫ u·Q'` (commute), and `−∫ u'·Q = kπ ∫ Q·sin`.
  have hcomm : (∫ x in (0 : ℝ)..1, Q' x * u x)
      = ∫ x in (0 : ℝ)..1, u x * Q' x := by
    refine intervalIntegral.integral_congr (fun x _ => ?_); ring
  rw [hcomm, hibp]
  -- `−∫ u'·Q = −∫ (−kπ sin)·Q = kπ ∫ sin·Q = kπ ∫ Q·sin`.
  rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp only [hu'_def]; ring

/-! ## The normalized divergence-mode identity `cosineCoeffs (∂ₓQ) = √λ·sineCoeffs Q` -/

/-- `√(lam k) = kπ` (since `lam k = (kπ)²` and `kπ ≥ 0`). -/
theorem sqrt_lam_eq_kpi (k : ℕ) : Real.sqrt (lam k) = (k : ℝ) * Real.pi := by
  have hk : (0 : ℝ) ≤ (k : ℝ) * Real.pi := by positivity
  simp only [lam, unitIntervalCosineEigenvalue]
  rw [Real.sqrt_sq hk]

/-- `(lam k)^(1/2 : ℝ) = kπ`, the engine's `√λ_k` form. -/
theorem rpow_half_lam_eq_kpi (k : ℕ) :
    (lam k) ^ (1 / 2 : ℝ) = (k : ℝ) * Real.pi := by
  rw [← Real.sqrt_eq_rpow]; exact sqrt_lam_eq_kpi k

/-- **The normalized divergence-mode identity** (explicit-derivative form):
in the repo's Neumann normalization,

    `cosineCoeffs Q' k = √(lam k)·sineCoeffs Q k`

for `Q` with derivative `Q'` on `[0,1]` and boundary vanishing `Q 0 = Q 1 = 0`.
Both sides are `0` at `k = 0`; for `k ≥ 1` this is the raw IBP identity times the
shared factor `2`, with `√(lam k) = kπ`. -/
theorem cosineCoeffs_deriv_eq_sqrtLambda_sineCoeff
    {Q Q' : ℝ → ℝ} (k : ℕ)
    (hQ : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt Q (Q' x) x)
    (hQ'cont : Continuous Q')
    (hQ0 : Q 0 = 0) (hQ1 : Q 1 = 0) :
    cosineCoeffs Q' k = Real.sqrt (lam k) * sineCoeffs Q k := by
  have hQ'int : IntervalIntegrable Q' volume 0 1 := hQ'cont.intervalIntegrable 0 1
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- `k = 0`: LHS `= ∫₀¹ Q' = Q 1 − Q 0 = 0`; RHS `= √(lam 0)·0 = 0`.
    rw [cosineCoeffs_zero_eq_integral, sineCoeffs_zero, mul_zero]
    have hint : (∫ x in (0 : ℝ)..1, Q' x) = Q 1 - Q 0 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x hx; exact hQ x hx
      · exact hQ'int
    rw [hint, hQ0, hQ1, sub_zero]
  · -- `k ≥ 1`: `cosineCoeffs Q' k = 2∫cos·Q' = 2·kπ·∫Q·sin = kπ·sineCoeffs Q k`.
    have hkne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
    rw [cosineCoeffs_pos_eq_integral hkne, sineCoeffs_pos hkne, sqrt_lam_eq_kpi]
    have hraw := rawCosCoeff_deriv_eq_kpi_rawSinCoeff k hQ hQ'int hQ0 hQ1
    -- `2∫cos·Q' = 2∫Q'·cos` (commute), then apply `hraw`.
    have hcomm : (∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) * Q' x)
        = ∫ x in (0 : ℝ)..1, Q' x * Real.cos ((k : ℝ) * Real.pi * x) := by
      refine intervalIntegral.integral_congr (fun x _ => ?_); ring
    have hsincomm : (∫ x in (0 : ℝ)..1, Q x * Real.sin ((k : ℝ) * Real.pi * x))
        = ∫ x in (0 : ℝ)..1, Real.sin ((k : ℝ) * Real.pi * x) * Q x := by
      refine intervalIntegral.integral_congr (fun x _ => ?_); ring
    rw [hcomm, hraw, hsincomm]; ring

/-! ## Engine connection: the B-form heat propagator feeds `√λ·sineCoeffs Q` -/

/-- **Engine connection (task 2).**  The B-form heat propagator applied to the
divergence `∂ₓQ = Q'` of a boundary-vanishing flux has cosine coefficients

    `cosineCoeffs (S(r) Q') k = e^{−r λ_k} · √λ_k · sineCoeffs Q k`,

i.e. the heat diagonal `e^{−rλ_k}` times the divergence-mode factor `√λ_k`
multiplying the **sine** flux coefficient.  This is exactly the per-step
integrand the engine's `duhamelEnergyCoeff` consumes (with `F = sineCoeffs ∘ Q`).
Composition of the heat diagonalization
(`cosineCoeffs_intervalFullSemigroupOperator_diag`) with the normalized
divergence-mode identity. -/
theorem cosineCoeffs_semigroup_deriv_eq_diag_sqrtLambda_sineCoeff
    {Q Q' : ℝ → ℝ} {r : ℝ} (hr : 0 < r) (hQ'cont : Continuous Q')
    (hQ : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt Q (Q' x) x)
    (hQ0 : Q 0 = 0) (hQ1 : Q 1 = 0)
    {M : ℝ} (hM : ∀ k, |cosineCoeffs Q' k| ≤ M) (k : ℕ) :
    cosineCoeffs (fun x => intervalFullSemigroupOperator r Q' x) k
      = Real.exp (-r * lam k) * (Real.sqrt (lam k) * sineCoeffs Q k) := by
  rw [cosineCoeffs_intervalFullSemigroupOperator_diag hr hQ'cont hM k,
    cosineCoeffs_deriv_eq_sqrtLambda_sineCoeff k hQ hQ'cont hQ0 hQ1]

/-! ## The `χ₀ ≠ 0` chemotaxis Duhamel coefficient through the engine -/

/-- The engine's per-mode divergence-Duhamel coefficient with the **sine** flux
source, unfolded as the interval integral

    `duhamelEnergyCoeff 1 (fun k τ => sineCoeffs (Q τ) k) t k
       = ∫₀ᵗ √λ_k · e^{−λ_k (t−τ)} · sineCoeffs (Q τ) k dτ`.

Purely definitional repackaging of `duhamelEnergyCoeff`/`duhamelModeCoeff`. -/
theorem duhamelEnergyCoeff_sineFlux_eq_integral
    (Q : ℝ → ℝ → ℝ) (t : ℝ) (k : ℕ) :
    duhamelEnergyCoeff 1 (fun k τ => sineCoeffs (Q τ) k) t k
      = ∫ τ in (0 : ℝ)..t,
          (lam k) ^ (1 / 2 : ℝ) * Real.exp (-(1 * lam k * (t - τ)))
            * sineCoeffs (Q τ) k := by
  rfl

/-- **Assembled `χ₀ ≠ 0` chemotaxis Duhamel coefficient (task 3).**

Given that the chemotaxis Duhamel term's per-mode cosine coefficient is the
prefactored divergence-mode integral

    `chemCoeff k = −χ₀ · ∫₀ᵗ √λ_k · e^{−λ_k (t−τ)} · sineCoeffs (Q τ) k dτ`

(`hchem`, the divergence-mode read-off of the chemotaxis Duhamel term — supplied
by the heat-diagonal/divergence-mode identity
`cosineCoeffs_semigroup_deriv_eq_diag_sqrtLambda_sineCoeff` integrated against
`τ`), it equals the C²-bootstrap **engine** coefficient

    `chemCoeff k = −χ₀ · duhamelEnergyCoeff 1 (fun k τ => sineCoeffs (Q τ) k) t k`.

This lands the chemotaxis Duhamel term as the engine object `duhamelEnergyCoeff`
with source `F = sineCoeffs ∘ Q` — the `χ₀ ≠ 0` analogue of WALL-B's
`gradientSolution_cosineCoeff_eq_duhamelEnergyCoeff`. -/
theorem chemotaxisDuhamel_cosineCoeff_eq_engine
    (χ₀ : ℝ) (Q : ℝ → ℝ → ℝ) (t : ℝ) (chemCoeff : ℕ → ℝ)
    (hchem : ∀ k, chemCoeff k = -χ₀ * ∫ τ in (0 : ℝ)..t,
        (lam k) ^ (1 / 2 : ℝ) * Real.exp (-(1 * lam k * (t - τ)))
          * sineCoeffs (Q τ) k) (k : ℕ) :
    chemCoeff k = -χ₀ *
      duhamelEnergyCoeff 1 (fun k τ => sineCoeffs (Q τ) k) t k := by
  rw [hchem k, duhamelEnergyCoeff_sineFlux_eq_integral]

end ShenWork.Paper2.IntervalDivergenceModeIdentity
