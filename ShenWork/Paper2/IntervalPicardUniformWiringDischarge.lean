/-
  ShenWork/Paper2/IntervalPicardUniformWiringDischarge.lean

  Phase-0 / M-final — discharging the *endpoint residuals* of the
  `UniformWiring` field hypotheses (ShenWork/Paper2/IntervalPicardUniformWiring.lean).

  The wiring corollary `uniformWiring_of_inputs` reduces `UniformWiring` to a set
  of satisfiable inputs.  Among those, FOUR were carried as named, satisfiable
  endpoint hypotheses (`hBaseEnd0`/`hBaseEnd1`, `hStepEnd0`/`hStepEnd1`) — the
  zero-extension residual: at `x ∈ {0,1}` the lift jumps, so the *interior*
  cosine-series second-derivative bound does not apply there.

  This module DISCHARGES all four endpoint residuals GENUINELY (no longer carried
  as hypotheses).  The mechanism is the unconditional junk-derivative fact

      `CompactSliceGradientBounds.deriv2_lift_eq_zero_left/right` :
        deriv (deriv (intervalDomainLift (u σ))) 0 = 0   (resp. at 1),

  which holds for ANY `u : ℝ → intervalDomainPoint → ℝ` and ANY `σ`: the lift is
  (in general) not differentiable at the endpoint, so `deriv` returns junk `0`,
  and `deriv∘deriv` is therefore `0` there.  Since `G2profile A₂ t = A₂/t² ≥ 0`
  (from the gate) and the M2-uniform budget RHS is `≥ 0`, the endpoint bound
  `|0| = 0 ≤ profile` (resp. `≤ budget`) holds.

  Consequently `uniformWiring_of_data` produces a `UniformWiring` from the SAME
  deep analytic inputs as `uniformWiring_of_inputs` MINUS the four endpoint
  residuals, which are now proved internally.

  ## What is NOT discharged here (continuation map)

  The remaining inputs of `uniformWiring_of_data` are the genuine analytic heart,
  whose proofs require the full Picard ball-invariant regularity bootstrap and
  differentiation-under-the-integral, and are legitimately the consumer's data:

    * G1 kernel route — `Lfam` source family + its integrability/sup (`hq_int`,
      `hL`), the gradient-integrand interval-integrability (`hg_int`), and the
      χ₀=0 derivative-split identity (`hsplit`).  Route: the χ₀=0 reduction
      `intervalGradientDuhamelMap_eq_of_chi0_zero` + differentiation under the
      Duhamel integral (`IntervalGradDuhamelBound`, `IntervalFullKernelGradientLinfty`),
      with `sup|Lₙ| ≤ CL p M` from the logistic sup on the M-ball (ball invariant
      in `IntervalMildPicardCone`).
    * G2 step interior — the two `DuhamelSourceTimeC1` packages (`hsrc0`, `srcσ`),
      the half-step coefficient bound `M₁ n t ≤ 2M` (`hM₁le`, from the ball via
      `cosineCoeffs_abs_le_of_continuous_bounded`), the quadratic source decay
      (`hdecay`) and σ-continuity (`hσcont`).  Producer:
      `picardIterate_source_duhamelSourceTimeC1` (needs the per-iterate spatial
      C²/positivity/Neumann regularity — the bootstrap).

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalPicardUniformWiring
import ShenWork.Paper2.IntervalCompactSliceGradientBounds

open MeasureTheory Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalHomogeneousQuantBound (eigExpWeight)
open ShenWork.IntervalPicardIterateTimeC1 (duhamelGainConst duhamelGainConst_nonneg)
open ShenWork.IntervalPicardIterateUniform (CL G1profile G2profile Benv homWeightBound
  GateCondition UniformWiring)
open ShenWork.Paper2.CompactSliceGradientBounds (deriv2_lift_eq_zero_left
  deriv2_lift_eq_zero_right)
open ShenWork.IntervalPicardUniformWiring (uniformWiring_of_inputs)

noncomputable section

namespace ShenWork.IntervalPicardUniformWiringDischarge

/-! ## §0 — Nonnegativity of the profile and the budget from the gate. -/

/-- `0 ≤ A₂` whenever the gate holds on a nonempty horizon `0 < T`.  At `t = T`
the gate gives `0 ≤ (nonneg LHS) ≤ A₂/T²`, and `T² > 0`, so `A₂ ≥ 0`. -/
theorem A₂_nonneg_of_gate
    {p : CM2Params} {M A₂ T : ℝ} (hMnn : 0 ≤ M) (hTpos : 0 < T)
    (hgate : GateCondition p M A₂ T) :
    0 ≤ A₂ := by
  have hgt := hgate T hTpos (le_refl T)
  -- LHS of the gate at `t = T` is nonnegative.
  have hτ : 0 < T / 2 := by positivity
  have hhom_nn : 0 ≤ homWeightBound M T := by
    unfold homWeightBound
    have h1 : 0 ≤ 4 / (Real.exp 1 * Real.pi ^ 2) := by positivity
    have h2 : (0:ℝ) < (T / 2) ^ 2 := by positivity
    have h2Mnn : 0 ≤ 2 * M := by linarith
    exact mul_nonneg h2Mnn (div_nonneg h1 h2.le)
  have hBenv_nn : 0 ≤ Benv p M A₂ T := by
    unfold Benv ShenWork.IntervalPicardIterateSourceC1.iterateSourceEnvelopeConst
    refine le_trans ?_ (le_max_right _ _)
    have hpow : 0 ≤ M ^ p.α := Real.rpow_nonneg hMnn _
    have : 0 ≤ p.a + p.b * M ^ p.α := by
      have := mul_nonneg p.hb hpow; have := p.ha; linarith
    exact mul_nonneg hMnn this
  have hgain_nn : 0 ≤ duhamelGainConst * (T / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ T :=
    mul_nonneg (mul_nonneg duhamelGainConst_nonneg (Real.rpow_nonneg hτ.le _)) hBenv_nn
  have hquot_nn : 0 ≤ A₂ / T ^ 2 := le_trans (by linarith) hgt
  have hT2 : (0:ℝ) < T ^ 2 := by positivity
  by_contra hneg
  rw [not_le] at hneg
  have : A₂ / T ^ 2 < 0 := div_neg_of_neg_of_pos hneg hT2
  linarith

/-- `0 ≤ G2profile A₂ t` for `0 < t` and `0 ≤ A₂`. -/
theorem G2profile_nonneg {A₂ t : ℝ} (hA₂ : 0 ≤ A₂) (ht : 0 < t) :
    0 ≤ G2profile A₂ t := by
  unfold G2profile
  positivity

/-- `0 ≤ Benv p M A₂ t` from the `max`-with-a-nonneg-term shape of the envelope. -/
theorem Benv_nonneg {p : CM2Params} {M A₂ t : ℝ} (hMnn : 0 ≤ M) :
    0 ≤ Benv p M A₂ t := by
  unfold Benv ShenWork.IntervalPicardIterateSourceC1.iterateSourceEnvelopeConst
  refine le_trans ?_ (le_max_right _ _)
  have hpow : 0 ≤ M ^ p.α := Real.rpow_nonneg hMnn _
  have : 0 ≤ p.a + p.b * M ^ p.α := by
    have := mul_nonneg p.hb hpow; have := p.ha; linarith
  exact mul_nonneg hMnn this

/-! ## §1 — The four endpoint discharges (genuinely proved).

The second derivative of the zero-extended lift VANISHES at `0` and `1` for every
iterate level and every time, so the endpoint bound is `|0| ≤ profile`. -/

/-- **G2 base endpoint, left (`x = 0`).**  Proved: `deriv∘deriv` of the lift at
`0` is `0`, and `G2profile A₂ t ≥ 0`. -/
theorem hBaseEnd0_proved
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M A₂ T : ℝ}
    (hMnn : 0 ≤ M) (hTpos : 0 < T) (hgate : GateCondition p M A₂ T) :
    ∀ t, 0 < t → t ≤ T →
      |deriv (deriv (intervalDomainLift (picardIter p u₀ 0 t))) 0| ≤ G2profile A₂ t := by
  intro t ht _htT
  have hA₂ := A₂_nonneg_of_gate hMnn hTpos hgate
  rw [deriv2_lift_eq_zero_left (fun s => picardIter p u₀ 0 s) t, abs_zero]
  exact G2profile_nonneg hA₂ ht

/-- **G2 base endpoint, right (`x = 1`).** -/
theorem hBaseEnd1_proved
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M A₂ T : ℝ}
    (hMnn : 0 ≤ M) (hTpos : 0 < T) (hgate : GateCondition p M A₂ T) :
    ∀ t, 0 < t → t ≤ T →
      |deriv (deriv (intervalDomainLift (picardIter p u₀ 0 t))) 1| ≤ G2profile A₂ t := by
  intro t ht _htT
  have hA₂ := A₂_nonneg_of_gate hMnn hTpos hgate
  rw [deriv2_lift_eq_zero_right (fun s => picardIter p u₀ 0 s) t, abs_zero]
  exact G2profile_nonneg hA₂ ht

/-- **G2 step endpoint, left (`x = 0`).**  Proved: the budget shape `∃ M₁'≤2M ∧ …`
holds with `M₁' = 0`, since `deriv∘deriv` at `0` is `0` and the budget RHS is
`≥ 0` (gain term nonneg). -/
theorem hStepEnd0_proved
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M A₂ T : ℝ}
    (hMnn : 0 ≤ M) :
    ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∃ M₁' : ℝ, M₁' ≤ 2 * M ∧
      |deriv (deriv (intervalDomainLift (picardIter p u₀ (n + 1) t))) 0|
        ≤ M₁' * eigExpWeight (t / 2)
          + duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ t := by
  intro n t ht _htT
  refine ⟨0, by linarith, ?_⟩
  rw [deriv2_lift_eq_zero_left (fun s => picardIter p u₀ (n + 1) s) t, abs_zero]
  have hτ : 0 < t / 2 := by positivity
  have hgain_nn : 0 ≤ duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ t :=
    mul_nonneg (mul_nonneg duhamelGainConst_nonneg (Real.rpow_nonneg hτ.le _))
      (Benv_nonneg hMnn)
  simpa using hgain_nn

/-- **G2 step endpoint, right (`x = 1`).** -/
theorem hStepEnd1_proved
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M A₂ T : ℝ}
    (hMnn : 0 ≤ M) :
    ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∃ M₁' : ℝ, M₁' ≤ 2 * M ∧
      |deriv (deriv (intervalDomainLift (picardIter p u₀ (n + 1) t))) 1|
        ≤ M₁' * eigExpWeight (t / 2)
          + duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ t := by
  intro n t ht _htT
  refine ⟨0, by linarith, ?_⟩
  rw [deriv2_lift_eq_zero_right (fun s => picardIter p u₀ (n + 1) s) t, abs_zero]
  have hτ : 0 < t / 2 := by positivity
  have hgain_nn : 0 ≤ duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ t :=
    mul_nonneg (mul_nonneg duhamelGainConst_nonneg (Real.rpow_nonneg hτ.le _))
      (Benv_nonneg hMnn)
  simpa using hgain_nn

/-! ## §2 — Assembly: `UniformWiring` from data, endpoint residuals discharged.

`uniformWiring_of_data` is `uniformWiring_of_inputs` with the four endpoint
hypotheses replaced by the proved facts above.  The remaining hypotheses are the
genuine analytic inputs (G1 kernel route + G2 step interior packages); see the
module header continuation map. -/

/-- **`UniformWiring` from data (endpoint residuals discharged).**  Same deep
analytic inputs as `uniformWiring_of_inputs`, MINUS the four endpoint residuals,
which are proved internally via the unconditional junk-derivative fact.  The
single extra datum is `0 < T` (a nonempty horizon, needed for `A₂ ≥ 0`). -/
theorem uniformWiring_of_data
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (u₀ : intervalDomainPoint → ℝ) {M A₂ T : ℝ}
    (hMnn : 0 ≤ M) (hTpos : 0 < T) (hT1 : T ≤ 1) (hgate : GateCondition p M A₂ T)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hcoeff : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ 2 * M)
    -- G1 kernel inputs:
    {u₀lift : ℝ → ℝ} (hf_meas : AEStronglyMeasurable u₀lift (intervalMeasure 1))
    (hu₀L : ∀ y, |u₀lift y| ≤ M)
    (Lfam : ℕ → ℝ → ℝ → ℝ)
    (hq_int : ∀ (n : ℕ), ∀ s, Integrable (Lfam n s) (intervalMeasure 1))
    (hL : ∀ (n : ℕ), ∀ s y, |Lfam n s y| ≤ CL p M)
    (hg_int : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : ℝ,
      IntervalIntegrable
        (fun s : ℝ => deriv
          (fun z : ℝ => intervalFullSemigroupOperator (t - s) (Lfam n s) z) x) volume 0 t)
    (hsplit : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : ℝ,
      deriv (intervalDomainLift (picardIter p u₀ n t)) x
        = deriv (fun z : ℝ => intervalFullSemigroupOperator t u₀lift z) x
          + ∫ s in (0:ℝ)..t, deriv
              (fun z : ℝ => intervalFullSemigroupOperator (t - s) (Lfam n s) z) x)
    -- G2 step per-level interior inputs:
    (M₁ : ℕ → ℝ → ℝ)
    (hM₁le : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → M₁ n t ≤ 2 * M)
    (hsrc0 : ∀ (n : ℕ), DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k))
    (hL_cont : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T →
      ∀ s, 0 < s → s ≤ t → Continuous (logisticLifted p (picardIter p u₀ n s)))
    (hM₁ : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T →
      ∀ k, |cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (t / 2))) k| ≤ M₁ n t)
    (srcσ : ∀ (n : ℕ) (t : ℝ), DuhamelSourceTimeC1
      (fun σ k => cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k))
    (hdecay : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T →
      ∀ σ, 0 ≤ σ → ∀ k : ℕ, 1 ≤ k →
        |cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k|
          ≤ 2 * Benv p M A₂ t / ((k : ℝ) * Real.pi) ^ 2)
    (hσcont : ∀ (n : ℕ) (t : ℝ), ∀ k, Continuous
      (fun σ => cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k)) :
    UniformWiring p u₀ M A₂ T :=
  uniformWiring_of_inputs p hχ0 u₀ hMnn hT1 hgate hu₀_cont hu₀_bound hcoeff
    hf_meas hu₀L Lfam hq_int hL hg_int hsplit
    (hBaseEnd0_proved hMnn hTpos hgate)
    (hBaseEnd1_proved hMnn hTpos hgate)
    M₁ hM₁le hsrc0 hL_cont hM₁ srcσ hdecay hσcont
    (hStepEnd0_proved hMnn)
    (hStepEnd1_proved hMnn)

end ShenWork.IntervalPicardUniformWiringDischarge
