import ShenWork.PDE.F1ProbeFractionalMultiplier

/-!
# F1 probe: NORM-level fractional Neumann smoothing

`‖A^σ e^{-tA} a‖₂ ≤ C_σ t^{-σ} ‖a‖₂` (coefficient-`ℓ²`)

This file lifts the just-committed PER-COEFFICIENT fractional smoothing bound
`F1ProbeFractionalMultiplier.shiftedNeumannFractionalGeneratorHeatCoeff_sq_le`

`‖A^σ e^{-tA} a‖²_n ≤ ((σ/e)^σ · t^{-σ})² · ‖a_n‖²`   (mode `n`, diagonal)

to the **coefficient-`ℓ²` (Parseval energy) NORM level**

`‖A^σ e^{-tA} a‖₂ ≤ (σ/e)^σ · t^{-σ} · ‖a‖₂`,

by SUMMING the per-mode bound over modes with `tsum_le_tsum` and taking
`Real.sqrt`.  This is the **exact mirror** of the repo's `σ = 1` template
`AnalyticSemigroupGen.shiftedNeumannGeneratorHeatCoeff_l2_norm_le`
(`‖A e^{-tA} a‖₂ ≤ (1/t)·‖a‖₂`) — same `coeffL2Energy = ∑' ‖a n‖²` /
`coeffL2Norm = sqrt(energy)` objects from `ResolventEstimate`, same
`Summable.of_nonneg_of_le` / `tsum_le_tsum` / `Real.sqrt_mul`+`Real.sqrt_sq`
machinery — with the general-`σ` constant `C_σ := (σ/e)^σ · t^{-σ}` (which is
`≥ 0`, not the literal `> 0` of `1/t`) replacing `1/t`.

## Scope / honesty note

The smoothing here maps PLAIN coefficient-`ℓ²` to PLAIN coefficient-`ℓ²`: the
`λ^σ` weight is already absorbed into the coefficients of
`shiftedNeumannFractionalGeneratorHeatCoeff` (it multiplies mode `n` by
`λ_n^σ`), so both sides use `coeffL2Norm`, exactly as the `σ = 1` template
does.  This is **pure Parseval `tsum` summation**; no operator theory, no
unbounded closed operator, no domain `D(A^σ)`.

The genuinely heavier object `FractionalPowerSpace.fractionalPowerEnergyTerm`
(the weighted `X^σ` energy `(1 + λ_n)^{2σ}·‖a_n‖²`) is NOT used here and is NOT
needed for this estimate: the bound `‖A^σ e^{-tA}‖_{ℓ²→ℓ²}` is a plain-`ℓ²`
operator-norm statement.  The `X^σ_q`-norm identification (reading the smoothed
output back as an element of the weighted fractional space, i.e. the sectorial
`D(A^σ)` transport) is the separate frontier flagged in the per-coefficient
probe; it is not invoked.
-/

noncomputable section

namespace ShenWork.PDE.F1ProbeFractionalSmoothing

open ShenWork.PDE.AnalyticSemigroupGen
open ShenWork.PDE.ResolventEstimate
open ShenWork.PDE.F1ProbeFractionalMultiplier

/-- The general-`σ` smoothing constant `C_σ(t) := (σ/e)^σ · t^{-σ}` is `≥ 0`.
(For `σ = 1` this is `1/t`, the literal positive constant of the template.) -/
theorem fractionalSmoothingConst_nonneg {σ t : ℝ} (hσ : 0 ≤ σ) (ht : 0 < t) :
    0 ≤ (σ / Real.exp 1) ^ σ * t ^ (-σ) :=
  mul_nonneg
    (Real.rpow_nonneg (div_nonneg hσ (Real.exp_nonneg 1)) σ)
    (Real.rpow_nonneg ht.le (-σ))

/-- Summability transport: if `‖a n‖²` is summable then so is
`‖A^σ e^{-tA} a n‖²`, by the per-coefficient bound and comparison.

Mirror of `AnalyticSemigroupGen.shiftedNeumannGeneratorHeatCoeff_l2_summable`
with the general-`σ` squared constant `C_σ²` majorant. -/
theorem shiftedNeumannFractionalGeneratorHeatCoeff_l2_summable
    {ω σ t : ℝ} (hω : 0 ≤ ω) (hσ : 0 ≤ σ) (ht : 0 < t)
    {a : ℕ → ℂ} (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    Summable fun n : ℕ =>
      ‖shiftedNeumannFractionalGeneratorHeatCoeff ω σ t a n‖ ^ 2 := by
  apply Summable.of_nonneg_of_le
    (fun n => sq_nonneg _)
    ?_
    (ha.mul_left (((σ / Real.exp 1) ^ σ * t ^ (-σ)) ^ 2))
  intro n
  exact shiftedNeumannFractionalGeneratorHeatCoeff_sq_le hω hσ ht a n

/-- Coefficient-`ℓ²` ENERGY form of the fractional smoothing bound:
`‖A^σ e^{-tA} a‖₂² ≤ C_σ² · ‖a‖₂²`.

Mirror of `AnalyticSemigroupGen.shiftedNeumannGeneratorHeatCoeff_l2_energy_le`.
Pure Parseval: `tsum_le_tsum` of the per-coefficient bound plus
`Summable.tsum_mul_left`. -/
theorem shiftedNeumannFractionalGeneratorHeatCoeff_l2_energy_le
    {ω σ t : ℝ} (hω : 0 ≤ ω) (hσ : 0 ≤ σ) (ht : 0 < t)
    {a : ℕ → ℂ} (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    coeffL2Energy (shiftedNeumannFractionalGeneratorHeatCoeff ω σ t a) ≤
      ((σ / Real.exp 1) ^ σ * t ^ (-σ)) ^ 2 * coeffL2Energy a := by
  have hs :=
    shiftedNeumannFractionalGeneratorHeatCoeff_l2_summable hω hσ ht ha
  have hmajor :
      Summable fun n : ℕ =>
        ((σ / Real.exp 1) ^ σ * t ^ (-σ)) ^ 2 * ‖a n‖ ^ 2 :=
    ha.mul_left (((σ / Real.exp 1) ^ σ * t ^ (-σ)) ^ 2)
  have hle :
      ∀ n : ℕ,
        ‖shiftedNeumannFractionalGeneratorHeatCoeff ω σ t a n‖ ^ 2 ≤
          ((σ / Real.exp 1) ^ σ * t ^ (-σ)) ^ 2 * ‖a n‖ ^ 2 :=
    shiftedNeumannFractionalGeneratorHeatCoeff_sq_le hω hσ ht a
  have htsum := hs.tsum_le_tsum hle hmajor
  simpa [coeffL2Energy, ha.tsum_mul_left] using htsum

/-- Coefficient-`ℓ²` NORM form of the fractional smoothing bound:
`‖A^σ e^{-tA} a‖₂ ≤ (σ/e)^σ · t^{-σ} · ‖a‖₂`.

This is the general-`σ` analogue of
`AnalyticSemigroupGen.shiftedNeumannGeneratorHeatCoeff_l2_norm_le`
(the `σ = 1`, constant `1/t` case).  Proof is the same `Real.sqrt` lift of the
energy bound, using `fractionalSmoothingConst_nonneg` for the `sqrt_sq` step in
place of the literal `0 ≤ 1/t`. -/
theorem shiftedNeumannFractionalGeneratorHeatCoeff_l2_norm_le
    {ω σ t : ℝ} (hω : 0 ≤ ω) (hσ : 0 ≤ σ) (ht : 0 < t)
    {a : ℕ → ℂ} (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    coeffL2Norm (shiftedNeumannFractionalGeneratorHeatCoeff ω σ t a) ≤
      ((σ / Real.exp 1) ^ σ * t ^ (-σ)) * coeffL2Norm a := by
  have henergy :=
    shiftedNeumannFractionalGeneratorHeatCoeff_l2_energy_le hω hσ ht ha
  have hsqrt := Real.sqrt_le_sqrt henergy
  have hfactor_nonneg : 0 ≤ (σ / Real.exp 1) ^ σ * t ^ (-σ) :=
    fractionalSmoothingConst_nonneg hσ ht
  calc
    coeffL2Norm (shiftedNeumannFractionalGeneratorHeatCoeff ω σ t a)
        = Real.sqrt
          (coeffL2Energy
            (shiftedNeumannFractionalGeneratorHeatCoeff ω σ t a)) := rfl
    _ ≤ Real.sqrt
          (((σ / Real.exp 1) ^ σ * t ^ (-σ)) ^ 2 * coeffL2Energy a) := hsqrt
    _ = ((σ / Real.exp 1) ^ σ * t ^ (-σ)) * coeffL2Norm a := by
          rw [Real.sqrt_mul (sq_nonneg ((σ / Real.exp 1) ^ σ * t ^ (-σ)))]
          rw [Real.sqrt_sq hfactor_nonneg]
          rfl

end ShenWork.PDE.F1ProbeFractionalSmoothing
