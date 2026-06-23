/-
  ShenWork/Paper2/IntervalCarrySeamWienerDischarge.lean

  χ₀<0 — `carrySeam_of_mild_wiener`: `carrySeam_of_mild_full` with the LAST genuine-gap
  atom `hWsum` DISCHARGED internally via the now-landed Wiener ℓ¹-convolution-closure
  lemma `reflCircle_mul_fourier_summable` (IntervalReflCircleWiener.lean:111).

  ## Accounting
  `carrySeam_of_mild_full` (IntervalCarrySeamFullDischarge.lean:56) carries
    `hWsum : ∀ τ ∈ Icc 0 t, Summable (fun n:ℤ => fourierCoeff (reflCircle (W τ)) n)`
  which its header flagged as a "genuine gap (no Wiener-algebra ℓ¹-of-product lemma)".
  That lemma is NOW landed.  Since `hWdef` writes `W τ = (lift (u τ))·(denom factor)`,
  `reflCircle (W τ)` is a reflCircle of a PRODUCT whose factor ℓ¹ are the already-carried
  `hu_sum` / `hwfac_sum` and factor continuities `hu_cont` / `hwfac_cont`.  So:
    hWsum τ hτ := by rw [hWdef τ]
                     exact reflCircle_mul_fourier_summable (hu_sum τ hτ) (hwfac_sum τ hτ)
                              (hu_cont τ hτ) (hwfac_cont τ hτ)
  This removes `hWsum` as an atom.  Hypothesis block is `carrySeam_of_mild_full` VERBATIM
  minus `hWsum`.  No `sorry`/`admit`/`native_decide`/custom axiom.  New file only.
-/
import ShenWork.Paper2.IntervalCarrySeamFullDischarge
import ShenWork.Paper2.IntervalReflCircleWiener

noncomputable section

namespace ShenWork.Paper2.IntervalCarrySeamWienerDischarge

open scoped Real
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalCosineInversion (reflCircle)
open ShenWork.Paper2.HSigmaScale (lam MemHSigma resolverCoeff)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.Paper2.IntervalDenomEnvelopeResolver (resolverValue)
open ShenWork.Paper2.IntervalMixedProduct (MixedMulBridge)
open ShenWork.Paper2.IntervalChiNegSeamFixedReach (CarrySeam)
open ShenWork.Paper2.IntervalCarrySeamFullDischarge (carrySeam_of_mild_full)
open ShenWork.Paper2.IntervalReflCircleWiener (reflCircle_mul_fourier_summable)

variable {p : CM2Params} {μ β t σ : ℝ}
variable {u : ℝ → intervalDomainPoint → ℝ} {v vx W : ℝ → ℝ → ℝ}

/-- **`carrySeam_of_mild_wiener` — `carrySeam_of_mild_full` with `hWsum` DISCHARGED.**
Identical hypotheses to `carrySeam_of_mild_full` EXCEPT the genuine-gap atom `hWsum` is
removed; it is produced per slice from `reflCircle_mul_fourier_summable` applied to the
already-present factor ℓ¹ (`hu_sum`/`hwfac_sum`) and continuities (`hu_cont`/`hwfac_cont`)
after rewriting `W τ` via `hWdef`. -/
def carrySeam_of_mild_wiener
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
  carrySeam_of_mild_full E hμ hμ1 hσ0 hσ1 hβ ht ht1 hû₀ hvnn hQ hWdef
    hu_cont hwfac_cont hu_sum hwfac_sum
    (fun τ hτ => by
      rw [hWdef τ]
      exact reflCircle_mul_fourier_summable (hu_sum τ hτ) (hwfac_sum τ hτ)
        (hu_cont τ hτ) (hwfac_cont τ hτ))
    hvxsum hvdef hvsum hvderiv hvxcont hQ_cont L hFl_cont

end ShenWork.Paper2.IntervalCarrySeamWienerDischarge

namespace ShenWork.Paper2.IntervalCarrySeamWienerDischarge
section AxiomAudit
#print axioms carrySeam_of_mild_wiener
end AxiomAudit
end ShenWork.Paper2.IntervalCarrySeamWienerDischarge
