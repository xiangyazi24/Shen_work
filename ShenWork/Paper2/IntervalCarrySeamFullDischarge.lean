/-
  ShenWork/Paper2/IntervalCarrySeamFullDischarge.lean

  χ₀<0 — `carrySeam_of_mild_full`: the GENUINE `CarrySeam` inhabitant with the LAST
  bridge `hmixbridge` (`MixedMulBridge (W τ) (vx τ)`) DISCHARGED internally via the
  landed `mixedMulBridge_of_summable`, so the result carries NO bridge.

  ## Accounting
  `carrySeam_of_mild` (IntervalCarrySeamDischarge.lean) builds `CarrySeam` but CARRIES
  `hmixbridge : ∀ τ ∈ Icc 0 t, MixedMulBridge (W τ) (vx τ)` as an explicit atom.  Here we
  call `carrySeam_of_mild` with `hmixbridge` produced PER SLICE from
  `mixedMulBridge_of_summable` (IntervalMixedMulBridgeDischarge.lean), whose inputs are
  {continuity, reflCircle ℓ¹} of `W τ` and `vx τ`:

  * `Continuous (W τ)` — DERIVED.  `hWdef` writes `W τ = (lift (u τ))·(denom factor)`, so
    `(hu_cont τ hτ).mul (hwfac_cont τ hτ)` gives it after rewriting by `hWdef`.
  * `Continuous (vx τ)` — passed through (`hvxcont`).
  * `Summable (fourierCoeff (reflCircle (W τ)) ·)` — CARRIED as the NAMED input `hWsum`.
    GREP-GENERAL-BEFORE-SPECIAL: the repo has `reflCircle_mul` (pointwise multiplicativity
    on `AddCircle 2`) but NO Wiener-algebra ℓ¹-of-product lemma deriving the reflCircle
    Fourier ℓ¹ of the product `(lift u)·denom` from the ℓ¹ of each factor (the convolution
    closure of ℓ¹ on the circle); Mathlib has no `fourierCoeff_mul` for this either.  It is a
    genuine gap, so `W τ`'s reflCircle ℓ¹ is taken as the explicit hypothesis `hWsum`, NOT
    faked from `hu_sum`/`hwfac_sum`.
  * `Summable (fourierCoeff (reflCircle (vx τ)) ·)` — CARRIED as the NAMED input `hvxsum`.

  Everything else is passed straight through to `carrySeam_of_mild`; nothing is weakened or
  assumed.  No `sorry`/`admit`/`native_decide`/custom axiom.  New file only.
-/
import ShenWork.Paper2.IntervalCarrySeamDischarge
import ShenWork.Paper2.IntervalMixedMulBridgeDischarge

noncomputable section

namespace ShenWork.Paper2.IntervalCarrySeamFullDischarge

open scoped Real
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalCosineInversion (reflCircle)
open ShenWork.Paper2.HSigmaScale (lam MemHSigma resolverCoeff)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.Paper2.IntervalDenomEnvelopeResolver (resolverValue)
open ShenWork.Paper2.IntervalMixedProduct (MixedMulBridge)
open ShenWork.Paper2.IntervalChiNegSeamFixedReach (CarrySeam)
open ShenWork.Paper2.IntervalCarrySeamDischarge (carrySeam_of_mild)
open ShenWork.Paper2.IntervalMixedMulBridge (mixedMulBridge_of_summable)

variable {p : CM2Params} {μ β t σ : ℝ}
variable {u : ℝ → intervalDomainPoint → ℝ} {v vx W : ℝ → ℝ → ℝ}

/-- **`carrySeam_of_mild_full` — `carrySeam_of_mild` with `hmixbridge` DISCHARGED.**
Identical hypotheses to `carrySeam_of_mild` EXCEPT the bridge `hmixbridge` is replaced by
the two mild reflCircle-ℓ¹ inputs `hWsum`/`hvxsum`; the bridge is produced per slice by
`mixedMulBridge_of_summable`.  The result is a genuine `CarrySeam` carrying NO bridge. -/
def carrySeam_of_mild_full
    (E : ShenWork.Paper2.IntervalTrajectoryEnvelope.TrajectoryHSigmaEnvelope σ t
      (fun τ => cosineCoeffs (intervalDomainLift (u τ))))
    (hμ : 0 < μ) (hμ1 : 1 ≤ μ) (hσ0 : 1 / 2 < σ) (hσ1 : σ < 3 / 2)
    (hβ : 0 ≤ β) (ht : 0 < t) (ht1 : t ≤ 1)
    (hû₀ : MemHSigma (σ + 1 / 4) (cosineCoeffs (intervalDomainLift (u 0))))
    (hvnn : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ x,
      0 ≤ resolverValue μ (cosineCoeffs (intervalDomainLift (u τ))) x)
    (hQ : ∀ τ, ShenWork.Paper2.IntervalDecompTauLift.conjQ p u τ = fun x => W τ x * vx τ x)
    (hWdef : ∀ τ, W τ = fun x => intervalDomainLift (u τ) x
      * (1 + resolverValue μ (cosineCoeffs (intervalDomainLift (u τ))) x) ^ (-β))
    (hu_cont : ∀ τ ∈ Set.Icc (0:ℝ) t, Continuous (intervalDomainLift (u τ)))
    (hwfac_cont : ∀ τ ∈ Set.Icc (0:ℝ) t, Continuous (fun x => (1 + resolverValue μ
      (cosineCoeffs (intervalDomainLift (u τ))) x) ^ (-β)))
    (hu_sum : ∀ τ ∈ Set.Icc (0:ℝ) t,
      Summable (fun n : ℤ => fourierCoeff (reflCircle (intervalDomainLift (u τ))) n))
    (hwfac_sum : ∀ τ ∈ Set.Icc (0:ℝ) t,
      Summable (fun n : ℤ => fourierCoeff (reflCircle (fun x => (1 + resolverValue μ
        (cosineCoeffs (intervalDomainLift (u τ))) x) ^ (-β))) n))
    -- CARRIED named Wiener-product-ℓ¹ inputs (genuine gap, see header): reflCircle ℓ¹ of
    -- `W τ` and `vx τ`; these DISCHARGE `hmixbridge` via `mixedMulBridge_of_summable`.
    (hWsum : ∀ τ ∈ Set.Icc (0:ℝ) t,
      Summable (fun n : ℤ => fourierCoeff (reflCircle (W τ)) n))
    (hvxsum : ∀ τ ∈ Set.Icc (0:ℝ) t,
      Summable (fun n : ℤ => fourierCoeff (reflCircle (vx τ)) n))
    (hvdef : ∀ τ, v τ = resolverValue μ (cosineCoeffs (intervalDomainLift (u τ))))
    (hvsum : ∀ τ ∈ Set.Icc (0:ℝ) t,
      Summable (fun k => |resolverCoeff μ E.env k|))
    (hvderiv : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (v τ) (vx τ x) x)
    (hvxcont : ∀ τ ∈ Set.Icc (0:ℝ) t, Continuous (vx τ))
    (hQ_cont : ∀ k, Continuous (fun τ => sineCoeffs
      (ShenWork.Paper2.IntervalDecompTauLift.conjQ p u τ) k))
    (L : ShenWork.Paper2.IntervalTrajectoryEnvelope.TrajectoryHSigmaEnvelope σ t
      (fun τ k => ShenWork.Paper2.IntervalDecompTauLift.conjFl p u k τ))
    (hFl_cont : ∀ k, Continuous (ShenWork.Paper2.IntervalDecompTauLift.conjFl p u k)) :
    CarrySeam p μ β t u v vx W σ E :=
  carrySeam_of_mild E hμ hμ1 hσ0 hσ1 hβ ht ht1 hû₀ hvnn hQ hWdef
    hu_cont hwfac_cont hu_sum hwfac_sum
    (fun τ hτ =>
      have hWcont : Continuous (W τ) := by
        rw [hWdef τ]; exact (hu_cont τ hτ).mul (hwfac_cont τ hτ)
      mixedMulBridge_of_summable hWcont (hvxcont τ hτ) (hWsum τ hτ) (hvxsum τ hτ))
    hvdef hvsum hvderiv hvxcont hQ_cont L hFl_cont

end ShenWork.Paper2.IntervalCarrySeamFullDischarge

namespace ShenWork.Paper2.IntervalCarrySeamFullDischarge
section AxiomAudit
#print axioms carrySeam_of_mild_full
end AxiomAudit
end ShenWork.Paper2.IntervalCarrySeamFullDischarge
