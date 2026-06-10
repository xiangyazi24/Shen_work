/-
  ShenWork/Paper2/IntervalHomogeneousG2Base.lean

  **The homogeneous-heat G2 base bound — `hG2base` derived from the gate.**

  Closes the `hG2base` leg of `TowerConeAnalyticResidual`: the level-0 Picard
  iterate is the pure homogeneous heat slice `picardIter p u₀ 0 σ = S(σ)(lift u₀)`,
  whose lifted second spatial derivative obeys

      |∂ₓₓ lift(u₀-slice)(x)| ≤ G2profile A₂ σ = A₂/σ²    (x : ℝ, 0 < σ ≤ T)

  whenever the GATE condition holds.  No calibration hypothesis is needed: the
  gate at `t := σ` already dominates the homogeneous weight

      homWeightBound M σ = 2M·(4/(e·π²))/(σ/2)² = 32M/(e·π²·σ²) ≤ A₂/σ²

  (the Duhamel summand of the gate is nonnegative and is simply dropped), while
  the true spectral bound for the homogeneous slice is the EIGHT-fold smaller

      |∂ₓₓ| ≤ M·eigExpWeight σ ≤ M·(4/(e·π²))/σ² = (1/8)·homWeightBound M σ.

  Pointwise structure over `x : ℝ` (the `∀ x : ℝ` quantifier of the residual):

  * `x ∈ Ioo 0 1` — near `x` the lift agrees with the spectral heat value
    `unitIntervalCosineHeatValue σ (cosineCoeffs (lift u₀))` (the subtype spectral
    identity, the same route as `hagree_zero`); `deriv ∘ deriv` passes through the
    local agreement, `unitIntervalCosineHeatValue_spatial_second_deriv` evaluates
    it to `unitIntervalCosineHeatSecondValue`, and the series is bounded by
    `homogeneous_eigenvalue_tsum_le` + `eigExpWeight_le` + the gate.
  * `x = 0`, `x = 1` — the junk-derivative mechanism: `deriv2_lift_eq_zero_left` /
    `deriv2_lift_eq_zero_right` give `∂ₓₓ = 0` unconditionally.
  * `x < 0`, `x > 1` — `deriv (lift)` vanishes identically on the open exterior
    (`deriv_lift_eq_zero_on_Iio`/`Ioi`), so the second derivative is `0`.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalPicardIterateRepresentation
import ShenWork.Paper2.IntervalCompactSliceGradientBounds
import ShenWork.Paper2.IntervalPicardUniformWiringDischarge
import ShenWork.PDE.IntervalHomogeneousQuantBound
import ShenWork.PDE.IntervalWeightPowerBound
import ShenWork.PDE.IntervalDuhamelClosedC2

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalPicardIterateUniform
  (G2profile homWeightBound GateCondition Benv)
open ShenWork.IntervalPicardIterateTimeC1 (duhamelGainConst duhamelGainConst_nonneg)
open ShenWork.IntervalPicardUniformWiringDischarge (Benv_nonneg)
open ShenWork.IntervalHomogeneousQuantBound
  (eigExpWeight homogeneous_eigenvalue_tsum_le)
open ShenWork.IntervalWeightPowerBound (eigExpWeight_le)
open ShenWork.IntervalPicardIterateC2Bound (hom_eig_summable)
open ShenWork.IntervalDomainRegularityBootstrap
  (unitIntervalCosineHeatSecondPointWeight unitIntervalCosineHeatSecondValue)
open ShenWork.IntervalSpectralSubtypeAdapter
  (intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont)
open ShenWork.Paper2.CompactSliceGradientBounds
  (deriv2_lift_eq_zero_left deriv2_lift_eq_zero_right
    deriv_lift_eq_zero_on_Iio deriv_lift_eq_zero_on_Ioi grad2_series_abs_le)

noncomputable section

namespace ShenWork.IntervalHomogeneousG2Base

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-! ## §1 — The spectral sup bound for the homogeneous second-derivative series. -/

/-- **Sup bound for the homogeneous second-derivative series.**
`|unitIntervalCosineHeatSecondValue σ a x| ≤ M·eigExpWeight σ` for `σ > 0` and
`ℓ∞`-bounded coefficients: reshape into the generic second-derivative cosine
series and apply `grad2_series_abs_le` with the eigenvalue-weighted damped
envelope, closed by `homogeneous_eigenvalue_tsum_le`. -/
theorem secondValue_abs_le {σ M : ℝ} (hσ : 0 < σ)
    {a : ℕ → ℝ} (ha : ∀ k, |a k| ≤ M) (x : ℝ) :
    |unitIntervalCosineHeatSecondValue σ a x| ≤ M * eigExpWeight σ := by
  have hg : Summable (fun k => (λ_ k) * |Real.exp (-σ * (λ_ k)) * a k|) :=
    hom_eig_summable hσ ha
  have hreshape : unitIntervalCosineHeatSecondValue σ a x
      = ∑' k, (Real.exp (-σ * (λ_ k)) * a k) *
          (-(((k : ℝ) * Real.pi) ^ 2) * Real.cos ((k : ℝ) * Real.pi * x)) := by
    unfold unitIntervalCosineHeatSecondValue unitIntervalCosineHeatSecondPointWeight
    exact tsum_congr fun k => by unfold unitIntervalCosineEigenvalue; ring
  rw [hreshape]
  refine le_trans
    (grad2_series_abs_le
      (fun k => Real.exp (-σ * (λ_ k)) * a k)
      (fun k => (λ_ k) * |Real.exp (-σ * (λ_ k)) * a k|) x hg
      (fun k => le_refl _))
    (homogeneous_eigenvalue_tsum_le hσ ha)

/-! ## §2 — The gate dominates the homogeneous spectral weight. -/

/-- **`M·eigExpWeight σ ≤ homWeightBound M σ`** (the deliberate 8-fold slack of
the gate's homogeneous term). -/
theorem eigExpWeight_le_homWeightBound {M σ : ℝ} (hM : 0 ≤ M) (hσ : 0 < σ) :
    M * eigExpWeight σ ≤ homWeightBound M σ := by
  set c : ℝ := 4 / (Real.exp 1 * Real.pi ^ 2) with hc_def
  have hc_nn : 0 ≤ c := by rw [hc_def]; positivity
  have h1 : eigExpWeight σ ≤ c / σ ^ 2 := eigExpWeight_le hσ
  have hσ2 : (0:ℝ) < σ ^ 2 := by positivity
  have hhalf : (σ / 2) ^ 2 = σ ^ 2 / 4 := by ring
  unfold homWeightBound
  rw [← hc_def, hhalf]
  have h2 : c / (σ ^ 2 / 4) = 4 * (c / σ ^ 2) := by
    field_simp
  rw [h2]
  have h3 : M * eigExpWeight σ ≤ M * (c / σ ^ 2) :=
    mul_le_mul_of_nonneg_left h1 hM
  have h4 : (0:ℝ) ≤ c / σ ^ 2 := div_nonneg hc_nn hσ2.le
  nlinarith [mul_nonneg hM h4]

/-- **The gate kills the homogeneous weight:** under `GateCondition p M A₂ T` and
`0 < σ ≤ T`, `homWeightBound M σ ≤ A₂/σ²` (drop the nonnegative Duhamel summand). -/
theorem homWeightBound_le_of_gate {p : CM2Params} {M A₂ T σ : ℝ}
    (hM : 0 ≤ M) (hσ : 0 < σ) (hσT : σ ≤ T)
    (hgate : GateCondition p M A₂ T) :
    homWeightBound M σ ≤ A₂ / σ ^ 2 := by
  have hg := hgate σ hσ hσT
  have hduh : (0:ℝ) ≤ duhamelGainConst * (σ / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ σ := by
    have h1 : (0:ℝ) ≤ duhamelGainConst := duhamelGainConst_nonneg
    have h2 : (0:ℝ) ≤ (σ / 2) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by linarith) _
    have h3 : (0:ℝ) ≤ Benv p M A₂ σ := Benv_nonneg hM
    positivity
  linarith

/-! ## §3 — The assembled `hG2base`. -/

/-- **The homogeneous-heat G2 base bound, gate-supplied.**  For all real `x` and
`0 < σ ≤ T`, the second derivative of the lifted level-0 Picard slice is bounded
by `G2profile A₂ σ = A₂/σ²`.  Consumes only: subtype continuity + coefficient
boundedness of the datum, nonnegativity of `M`/`A₂`, and the gate. -/
theorem hG2base_of_gate
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {M A₂ T : ℝ}
    (hM : 0 ≤ M) (hA₂ : 0 ≤ A₂)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M)
    (hgate : GateCondition p M A₂ T) :
    ∀ (σ : ℝ), 0 < σ → σ ≤ T → ∀ x : ℝ,
      |deriv (deriv (intervalDomainLift (picardIter p u₀ 0 σ))) x|
        ≤ G2profile A₂ σ := by
  intro σ hσ hσT x
  have hσ2 : (0:ℝ) < σ ^ 2 := by positivity
  have hprof_nn : (0:ℝ) ≤ G2profile A₂ σ := by
    unfold G2profile; exact div_nonneg hA₂ hσ2.le
  -- the spectral coefficient family of the datum
  set a : ℕ → ℝ := fun k => cosineCoeffs (intervalDomainLift u₀) k with ha_def
  -- case split over the real line
  rcases lt_or_ge x 0 with hx0 | hx0
  · -- exterior left: `deriv lift ≡ 0` on the open `Iio 0` ⟹ second deriv `0`.
    have hmem : Set.Iio (0:ℝ) ∈ nhds x := isOpen_Iio.mem_nhds hx0
    have hEq : deriv (intervalDomainLift (picardIter p u₀ 0 σ)) =ᶠ[nhds x]
        (fun _ => (0:ℝ)) := by
      filter_upwards [hmem] with y hy
      exact deriv_lift_eq_zero_on_Iio (picardIter p u₀ 0) σ hy
    rw [hEq.deriv_eq, deriv_const]
    simpa using hprof_nn
  rcases lt_or_ge 1 x with hx1 | hx1
  · -- exterior right: symmetric.
    have hmem : Set.Ioi (1:ℝ) ∈ nhds x := isOpen_Ioi.mem_nhds hx1
    have hEq : deriv (intervalDomainLift (picardIter p u₀ 0 σ)) =ᶠ[nhds x]
        (fun _ => (0:ℝ)) := by
      filter_upwards [hmem] with y hy
      exact deriv_lift_eq_zero_on_Ioi (picardIter p u₀ 0) σ hy
    rw [hEq.deriv_eq, deriv_const]
    simpa using hprof_nn
  -- now `x ∈ Icc 0 1`
  rcases eq_or_lt_of_le hx0 with hx0e | hx0lt
  · -- `x = 0`: junk-derivative endpoint.
    rw [← hx0e, deriv2_lift_eq_zero_left (picardIter p u₀ 0) σ]
    simpa using hprof_nn
  rcases eq_or_lt_of_le hx1 with hx1e | hx1lt
  · -- `x = 1`: junk-derivative endpoint.
    rw [hx1e, deriv2_lift_eq_zero_right (picardIter p u₀ 0) σ]
    simpa using hprof_nn
  -- interior `x ∈ Ioo 0 1`: the spectral regime.
  have hxIoo : x ∈ Set.Ioo (0:ℝ) 1 := ⟨hx0lt, hx1lt⟩
  have hmem : Set.Ioo (0:ℝ) 1 ∈ nhds x := isOpen_Ioo.mem_nhds hxIoo
  -- local agreement of the lift with the heat value
  have hEq : intervalDomainLift (picardIter p u₀ 0 σ) =ᶠ[nhds x]
      (fun y => unitIntervalCosineHeatValue σ a y) := by
    filter_upwards [hmem] with y hy
    have hyIcc : y ∈ Set.Icc (0:ℝ) 1 := ⟨hy.1.le, hy.2.le⟩
    have hlift : intervalDomainLift (picardIter p u₀ 0 σ) y
        = intervalFullSemigroupOperator σ (intervalDomainLift u₀) y := by
      simp only [intervalDomainLift, picardIter, dif_pos hyIcc]
    rw [hlift]
    exact intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
      hσ hu₀_cont hu₀_bound hyIcc
  -- pass `deriv ∘ deriv` through the local agreement
  have hd2 : deriv (deriv (intervalDomainLift (picardIter p u₀ 0 σ))) x
      = deriv (deriv (fun y => unitIntervalCosineHeatValue σ a y)) x :=
    (hEq.deriv).deriv_eq
  rw [hd2]
  -- spectral evaluation of the second derivative
  have hsec : deriv (fun y : ℝ => deriv
        (fun z : ℝ => unitIntervalCosineHeatValue σ a z) y) x
      = unitIntervalCosineHeatSecondValue σ a x :=
    ShenWork.IntervalDuhamelClosedC2.unitIntervalCosineHeatValue_spatial_second_deriv
      hσ hu₀_bound
  rw [hsec]
  -- the quantitative chain: spectral sup ≤ M·E₂(σ) ≤ homWeightBound ≤ gate
  calc |unitIntervalCosineHeatSecondValue σ a x|
      ≤ M * eigExpWeight σ := secondValue_abs_le hσ hu₀_bound x
    _ ≤ homWeightBound M σ := eigExpWeight_le_homWeightBound hM hσ
    _ ≤ A₂ / σ ^ 2 := homWeightBound_le_of_gate hM hσ hσT hgate
    _ = G2profile A₂ σ := rfl

end ShenWork.IntervalHomogeneousG2Base
