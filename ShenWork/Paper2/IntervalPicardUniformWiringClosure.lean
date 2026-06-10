/-
  ShenWork/Paper2/IntervalPicardUniformWiringClosure.lean

  **Deliverable D (stretch) — `uniformWiring_closure`.**

  `uniformWiring_of_data_v2` (`IntervalPicardUniformWiringDischarge`) builds a
  `UniformWiring` from the satisfiable interior (`Ioo 0 1`) χ₀ = 0 derivative split,
  the G1 kernel integrability data, and the per-level G2-step interior packages.

  This file discharges the two *infrastructure* legs of that input list directly from
  Front B (`IntervalDuhamelSpatialLeibniz` / `IntervalPicardG1Split`):

    * the **Ioo-form split** for all levels (`chi0_deriv_split_interior`) — genuinely
      proved interior split, the satisfiable shape `uniformWiring_of_data_v2` wants
      (no off-interior residual: the Ioo-form only asserts the interior, where the
      χ₀-reduction + termwise `HasDerivAt.add` give the identity exactly);
    * the **source integrability** `hq_int` via `duhamel_source_integrable`, and the
      **gradient-integrand integrability** `hg_int` via `hg_int_field`.

  With `Lfam := gLfam p u₀` and `u₀lift := lift u₀`, the remaining inputs are exactly
  the GENUINE analytic heart — the G2-step per-level `DuhamelSourceTimeC1` packages
  (deliverable B's `hsrc0`/`srcσ`), the half-step coefficient bound, the σ-shifted
  source decay / continuity, the logistic sup `hL`/`hu₀L`/`hLsup`, the joint source
  measurability, and the numeric gate.  These are taken as the named hypothesis list:
  the closure is the *data-free-modulo-(gate ∧ ball ∧ B-packages)* `UniformWiring`.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalPicardUniformWiringDischarge
import ShenWork.Paper2.IntervalDuhamelSpatialLeibniz

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalHomogeneousQuantBound (eigExpWeight)
open ShenWork.IntervalPicardIterateTimeC1 (duhamelGainConst)
open ShenWork.IntervalPicardIterateUniform (CL Benv GateCondition UniformWiring)
open ShenWork.IntervalPicardUniformWiringDischarge (uniformWiring_of_data_v2)
open ShenWork.IntervalPicardG1Split
  (gLfam hg_int_field zero_deriv_split_interior succ_deriv_split_interior)
open ShenWork.IntervalDuhamelSpatialLeibniz (duhamel_source_integrable)

noncomputable section

namespace ShenWork.IntervalPicardUniformWiringClosure

/-! ## §1 — The interior (Ioo-form) χ₀ = 0 derivative split, all levels.

The Ioo-form split for `Lfam = gLfam p u₀`, `u₀lift = lift u₀`, genuinely proved at
every level and every interior point — exactly the `hsplit` shape of
`uniformWiring_of_data_v2`. -/

/-- **`chi0_deriv_split_interior`.**  The interior derivative split at every level,
in the satisfiable `Ioo 0 1` shape consumed by `uniformWiring_of_data_v2`.  Level `0`
uses `zero_deriv_split_interior` (zero source family), level `n+1`
`succ_deriv_split_interior` (logistic source); both pieces equal `gLfam p u₀ n`. -/
theorem chi0_deriv_split_interior
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (u₀ : intervalDomainPoint → ℝ) {M T : ℝ}
    (hu₀ : ∀ y, |intervalDomainLift u₀ y| ≤ M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    (hLmeas : ∀ n : ℕ,
      Measurable (Function.uncurry (fun s => logisticLifted p (picardIter p u₀ n s))))
    {CL₀ : ℝ} (hCLnn : 0 ≤ CL₀)
    (hLsup : ∀ (n : ℕ) (s y : ℝ),
      |logisticLifted p (picardIter p u₀ n s) y| ≤ CL₀) :
    ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : ℝ, x ∈ Set.Ioo (0:ℝ) 1 →
      deriv (intervalDomainLift (picardIter p u₀ n t)) x
        = deriv (fun z : ℝ => intervalFullSemigroupOperator t (intervalDomainLift u₀) z) x
          + ∫ s in (0:ℝ)..t, deriv
              (fun z : ℝ => intervalFullSemigroupOperator (t - s) (gLfam p u₀ n s) z) x := by
  intro n t ht _htT x hx
  cases n with
  | zero =>
      -- gLfam p u₀ 0 = fun _ _ => 0
      exact zero_deriv_split_interior p u₀ ht hu₀ hu₀_meas hx
  | succ m =>
      -- gLfam p u₀ (m+1) s = logisticLifted p (picardIter p u₀ m s)
      exact succ_deriv_split_interior p hχ0 u₀ m ht hu₀ hu₀_meas
        (hLmeas m) hCLnn (fun s y => hLsup m s y) hx

/-! ## §2 — The closure: `UniformWiring` data-free-modulo-(gate ∧ ball ∧ B-packages).

`uniformWiring_closure` calls `uniformWiring_of_data_v2` with the infrastructure legs
(Ioo-split, `hq_int`, `hg_int`, `hL`) discharged from §1 + Front B, leaving the
genuine analytic inputs (gate, datum data, joint source measurability + sup, and the
G2-step `DuhamelSourceTimeC1` packages of deliverable B) as the named list. -/

/-- **Deliverable D — `uniformWiring_closure`.**

`UniformWiring p u₀ M A₂ T` from the genuine analytic inputs, with the
infrastructure legs of `uniformWiring_of_data_v2` discharged:

  * `hsplit` ← `chi0_deriv_split_interior` (Ioo-form, §1);
  * `hq_int` ← `duhamel_source_integrable` (from joint measurability + sup);
  * `hg_int` ← `hg_int_field`;
  * `hL`   ← the logistic sup bound `hLsup` (and `|0| = 0` at level `0`).

The remaining inputs are the genuine heart: the gate, the datum coefficient bounds,
the joint source measurability `hLmeas` + sup `hLsup`, and the per-level G2-step
packages (`hsrc0`/`srcσ` from deliverable B, with `hM₁le`/`hM₁`/`hdecay`/`hσcont`/
`hL_cont`). -/
theorem uniformWiring_closure
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (u₀ : intervalDomainPoint → ℝ) {M A₂ T : ℝ}
    (hMnn : 0 ≤ M) (hTpos : 0 < T) (hT1 : T ≤ 1) (hgate : GateCondition p M A₂ T)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hcoeff : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ 2 * M)
    -- datum lift sup + measurability (G1 kernel):
    (hu₀L : ∀ y, |intervalDomainLift u₀ y| ≤ M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    -- joint source measurability + sup (the cone logistic-sup datum, `n`-free):
    (hLmeas : ∀ n : ℕ,
      Measurable (Function.uncurry (fun s => logisticLifted p (picardIter p u₀ n s))))
    (hLsup : ∀ (n : ℕ) (s y : ℝ),
      |logisticLifted p (picardIter p u₀ n s) y| ≤ CL p M)
    -- G2 step per-level interior packages (deliverable B + cone):
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
    UniformWiring p u₀ M A₂ T := by
  have hCLnn : 0 ≤ CL p M := ShenWork.IntervalPicardIterateUniform.CL_nonneg hMnn
  -- `hL` for the wiring source family `gLfam`: |0| = 0 ≤ CL at level 0, sup at n+1.
  have hL : ∀ (n : ℕ), ∀ s y, |gLfam p u₀ n s y| ≤ CL p M := by
    intro n s y
    cases n with
    | zero => simp [gLfam]; exact hCLnn
    | succ m => exact hLsup m s y
  -- `hq_int` from per-level joint measurability + sup via `duhamel_source_integrable`.
  have hq_int : ∀ (n : ℕ), ∀ s, Integrable (gLfam p u₀ n s) (intervalMeasure 1) := by
    intro n
    cases n with
    | zero =>
        intro s
        simp only [gLfam]
        exact integrable_zero ℝ ℝ (intervalMeasure 1)
    | succ m =>
        exact duhamel_source_integrable (hLmeas m) (fun s y => hLsup m s y)
  exact uniformWiring_of_data_v2 p hχ0 u₀ hMnn hTpos hT1 hgate hu₀_cont hu₀_bound hcoeff
    hu₀_meas hu₀L (gLfam p u₀) hq_int hL
    (hg_int_field p u₀ hMnn hLmeas hCLnn hLsup)
    (chi0_deriv_split_interior p hχ0 u₀ hu₀L hu₀_meas hLmeas hCLnn hLsup)
    M₁ hM₁le hsrc0 hL_cont hM₁ srcσ hdecay hσcont

end ShenWork.IntervalPicardUniformWiringClosure
