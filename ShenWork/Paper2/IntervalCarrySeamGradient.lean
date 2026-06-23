/-
  ShenWork/Paper2/IntervalCarrySeamGradient.lean

  χ₀<0 — `carrySeam_of_mild_gradient`: a genuine `CarrySeam` inhabitant with the
  GRADIENT / CONTINUITY regularity atoms `hvderiv`, `hvxcont`, `hwfac_cont` and the
  vestigial `hvxsum` DISCHARGED from the SINGLE elliptic-gain fact
  `ContDiff ℝ 2 (v τ)` (`resolverValue_contDiff_two`), keyed off the trajectory
  `H^σ` envelope `E`.  Built on `carrySeam_of_mild` (the entry that takes the
  mixed bridge as an explicit atom), so the vestigial `vx`-reflCircle ℓ¹ is
  ELIMINATED, not threaded into the unused `mixedMulBridge_of_summable` slot.

  ## Two-way audit (each discharged atom CONSUMES a landed lemma)

  The conjugate-mild model fixes `v τ = resolverValue μ (cosineCoeffs (lift (u τ)))`
  (`hvdef`) and the gradient `vx τ = deriv (v τ)` (`hvxdef`).
  `memHSigma_lift_of_envelope E` (Frontier) + `resolverValue_contDiff_two`
  (DenomEnvelopeResolver) give `ContDiff ℝ 2 (v τ)` from `E`.  Then:

  * `hvderiv` (`HasDerivAt (v τ) (vx τ x) x`): `(ContDiff.differentiable).hasDerivAt`,
    `vx τ x = deriv (v τ) x` by `hvxdef`.  CONSUMES `resolverValue_contDiff_two`.
  * `hvxcont` (`Continuous (vx τ)`): `ContDiff.continuous_deriv` (`1 ≤ 2`) + `hvxdef`.
    CONSUMES `resolverValue_contDiff_two`.
  * `hwfac_cont` (`Continuous (1+v)^{−β}`): `contDiff_two_one_add_rpow_neg`
    (CkComposition) `.continuous`, fed `ContDiff ℝ 2 (v τ)` and `hvnn`.
  * `hbridge` (`MixedMulBridge (W τ) (vx τ)`): the landed `mixedMulBridge_of_summable`
    proof NEVER consumes the `vx`-reflCircle-ℓ¹ argument (its `_hvxsum` is an UNUSED
    binder).  `mixedMulBridge_of_Wsum` below re-exposes the bridge from `hWsum`,
    `hWcont`, `hvxcont` ALONE; `hWsum` is the product ℓ¹ `reflCircle_mul_fourier_summable`
    of the lift/denom factors (themselves from `E` via the Frontier producers).
  * `hu_sum`/`hwfac_sum`/`hvsum`: the Frontier reflCircle/resolver-coeff ℓ¹ producers
    `reflCircle_lift_summable_of_envelope` / `reflCircle_denom_summable_of_envelope` /
    `resolverCoeff_summable_of_envelope`.

  ## Carried (genuinely irreducible after this file)
  * `hu_cont` — `Continuous (intervalDomainLift (u τ))`.  `intervalDomainLift` is the
    ZERO-extension `if x ∈ [0,1] then u else 0` (`IntervalDomain:2750`), NOT the even
    `reflCircle`.  Continuity on ℝ REQUIRES `u τ` to vanish at the endpoints
    (`IntervalDomainConstantEquilibriumWitness` proves `¬ ContinuousAt` for a
    nonzero-boundary constant).  No landed `Continuous (intervalDomainLift …)`
    producer exists (only `ContinuousOn [0,1]`); a faithful boundary-trace datum.

  No `sorry`/`admit`/`native_decide`/custom axiom.  New file only.  Lines ≤ 100.
-/
import ShenWork.Paper2.IntervalCarrySeamFrontier
import ShenWork.Paper2.IntervalCarrySeamDischarge
import ShenWork.Paper2.IntervalMixedMulBridgeDischarge
import ShenWork.Paper2.IntervalReflCircleWiener
import ShenWork.Paper2.IntervalCkComposition

noncomputable section

namespace ShenWork.Paper2.IntervalCarrySeamGradient

open scoped Real
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalCosineInversion (reflCircle)
open ShenWork.Paper2.HSigmaScale (lam MemHSigma resolverCoeff)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs sineCoeffs_zero sineCoeffs_pos)
open ShenWork.Paper2.IntervalDenomEnvelopeResolver (resolverValue resolverValue_contDiff_two)
open ShenWork.Paper2.IntervalCkComposition (contDiff_two_one_add_rpow_neg)
open ShenWork.Paper2.IntervalMixedProduct (MixedMulBridge trueMixedProd)
open ShenWork.Paper2.IntervalMixedMulBridge
  (mulSinInt_eq_tsum mixedConvSum_eq_trueMixedProd rawSinCos_prod_to_sum rawSinInt_eq)
open ShenWork.IntervalCosineInversion (intervalCosineCoeff_summable_abs)
open ShenWork.Paper2.IntervalReflCircleWiener (reflCircle_mul_fourier_summable)
open ShenWork.Paper2.IntervalCarrySeamFrontier
  (reflCircle_lift_summable_of_envelope reflCircle_denom_summable_of_envelope
    resolverCoeff_summable_of_envelope)
open ShenWork.Paper2.IntervalChiNegSeamFixedReach (CarrySeam)
open ShenWork.Paper2.IntervalCarrySeamDischarge (carrySeam_of_mild)
open ShenWork.Paper2.IntervalTrajectoryEnvelope (TrajectoryHSigmaEnvelope)

variable {p : CM2Params} {μ β t σ : ℝ}
variable {u : ℝ → intervalDomainPoint → ℝ} {v vx W : ℝ → ℝ → ℝ}

/-- **`ContDiff ℝ 2 (v τ)` from the envelope `E` and the resolver model `hvdef`.** -/
theorem v_contDiff_two_of_envelope (hμ : 0 < μ) (hσ0 : 1 / 2 < σ)
    (E : TrajectoryHSigmaEnvelope σ t (fun τ => cosineCoeffs (intervalDomainLift (u τ))))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) t)
    (hvdef : v τ = resolverValue μ (cosineCoeffs (intervalDomainLift (u τ)))) :
    ContDiff ℝ 2 (v τ) := by
  rw [hvdef]
  exact resolverValue_contDiff_two hμ hσ0
    (ShenWork.Paper2.IntervalCarrySeamFrontier.memHSigma_lift_of_envelope E hτ)

/-- **`MixedMulBridge` from `W`-summability ALONE** — drops the vestigial unused
`vx`-reflCircle-ℓ¹ binder of `mixedMulBridge_of_summable`.  Same proof skeleton:
`mulSinInt_eq_tsum` (needs `hWsum`) → product-to-sum → `mixedConvSum_eq_trueMixedProd`. -/
theorem mixedMulBridge_of_Wsum {W vx : ℝ → ℝ} (hW : Continuous W) (hvx : Continuous vx)
    (hWsum : Summable (fun n : ℤ => fourierCoeff (reflCircle W) n)) :
    MixedMulBridge W vx := by
  intro k
  have hWl1 : Summable (fun m => |cosineCoeffs W m|) :=
    intervalCosineCoeff_summable_abs W hW hWsum
  rcases eq_or_ne k 0 with rfl | hk
  · rw [sineCoeffs_zero, trueMixedProd]; simp
  · rw [sineCoeffs_pos hk,
      show (∫ x in (0:ℝ)..1, Real.sin ((k:ℝ)*Real.pi*x) * (W x * vx x))
          = ∫ x in (0:ℝ)..1, Real.sin ((k:ℝ)*Real.pi*x) * (vx x * W x) from by
        refine intervalIntegral.integral_congr (fun x _ => ?_); ring,
      mulSinInt_eq_tsum W vx hW hvx hWsum k]
    rw [tsum_congr (fun m => by
      rw [rawSinCos_prod_to_sum vx hvx k m, rawSinInt_eq vx (k+m),
        rawSinInt_eq vx (Nat.dist k m)])]
    exact mixedConvSum_eq_trueMixedProd hvx hWl1 k hk

/-- **`carrySeam_of_mild_gradient` — the gradient/continuity atoms DISCHARGED.**

Hypotheses are `carrySeam_of_mild` minus `hwfac_cont`/`hvderiv`/`hvxcont`/`hmixbridge`
and the reflCircle ℓ¹ family, plus the gradient model `hvxdef : vx τ = deriv (v τ)`.
All reduce to the elliptic-gain `ContDiff ℝ 2 (v τ)`.  Carried: `hu_cont`. -/
def carrySeam_of_mild_gradient
    (E : TrajectoryHSigmaEnvelope σ t (fun τ => cosineCoeffs (intervalDomainLift (u τ))))
    (hμ : 0 < μ) (hμ1 : 1 ≤ μ) (hσ0 : 1 / 2 < σ) (hσ1 : σ < 3 / 2)
    (hβ : 0 ≤ β) (ht : 0 < t) (ht1 : t ≤ 1)
    (hû₀ : MemHSigma (σ + 1 / 4) (cosineCoeffs (intervalDomainLift (u 0))))
    (hvnn : ∀ τ ∈ Set.Icc (0 : ℝ) t, ∀ x,
      0 ≤ resolverValue μ (cosineCoeffs (intervalDomainLift (u τ))) x)
    (hQ : ∀ τ, ShenWork.Paper2.IntervalDecompTauLift.conjQ p u τ = fun x => W τ x * vx τ x)
    (hWdef : ∀ τ, W τ = fun x => intervalDomainLift (u τ) x
      * (1 + resolverValue μ (cosineCoeffs (intervalDomainLift (u τ))) x) ^ (-β))
    (hu_cont : ∀ τ ∈ Set.Icc (0 : ℝ) t, Continuous (intervalDomainLift (u τ)))
    (hvdef : ∀ τ, v τ = resolverValue μ (cosineCoeffs (intervalDomainLift (u τ))))
    (hvxdef : ∀ τ, vx τ = deriv (v τ))
    (hQ_cont : ∀ k, Continuous (fun τ => sineCoeffs
      (ShenWork.Paper2.IntervalDecompTauLift.conjQ p u τ) k))
    (L : TrajectoryHSigmaEnvelope σ t
      (fun τ k => ShenWork.Paper2.IntervalDecompTauLift.conjFl p u k τ))
    (hFl_cont : ∀ k, Continuous (ShenWork.Paper2.IntervalDecompTauLift.conjFl p u k)) :
    CarrySeam p μ β t u v vx W σ E := by
  have hv2 : ∀ τ ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ 2 (v τ) :=
    fun τ hτ => v_contDiff_two_of_envelope hμ hσ0 E hτ (hvdef τ)
  have hvxcont : ∀ τ ∈ Set.Icc (0 : ℝ) t, Continuous (vx τ) := fun τ hτ => by
    rw [hvxdef τ]; exact (hv2 τ hτ).continuous_deriv (by norm_num)
  have hvderiv : ∀ τ ∈ Set.Icc (0 : ℝ) t, ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (v τ) (vx τ x) x := fun τ hτ x _ => by
    rw [hvxdef τ]; exact ((hv2 τ hτ).differentiable (by norm_num) x).hasDerivAt
  have hwfac_cont : ∀ τ ∈ Set.Icc (0 : ℝ) t, Continuous (fun x => (1 + resolverValue μ
      (cosineCoeffs (intervalDomainLift (u τ))) x) ^ (-β)) := fun τ hτ => by
    have h := contDiff_two_one_add_rpow_neg (v := v τ) (hv2 τ hτ) (fun x => by
      rw [hvdef τ]; exact hvnn τ hτ x) β
    rw [hvdef τ] at h; exact h.continuous
  have hWcont : ∀ τ ∈ Set.Icc (0 : ℝ) t, Continuous (W τ) := fun τ hτ => by
    rw [hWdef τ]; exact (hu_cont τ hτ).mul (hwfac_cont τ hτ)
  have hWsum : ∀ τ ∈ Set.Icc (0 : ℝ) t,
      Summable (fun n : ℤ => fourierCoeff (reflCircle (W τ)) n) := fun τ hτ => by
    rw [hWdef τ]
    exact reflCircle_mul_fourier_summable
      (reflCircle_lift_summable_of_envelope hσ0 E hτ (hu_cont τ hτ))
      (reflCircle_denom_summable_of_envelope hμ hσ0 hσ1 E hτ (fun x => hvnn τ hτ x)
        (hwfac_cont τ hτ))
      (hu_cont τ hτ) (hwfac_cont τ hτ)
  have hmixbridge : ∀ τ ∈ Set.Icc (0 : ℝ) t, MixedMulBridge (W τ) (vx τ) := fun τ hτ =>
    mixedMulBridge_of_Wsum (hWcont τ hτ) (hvxcont τ hτ) (hWsum τ hτ)
  exact carrySeam_of_mild E hμ hμ1 hσ0 hσ1 hβ ht ht1 hû₀ hvnn hQ hWdef
    hu_cont hwfac_cont
    (fun τ hτ => reflCircle_lift_summable_of_envelope hσ0 E hτ (hu_cont τ hτ))
    (fun τ hτ => reflCircle_denom_summable_of_envelope hμ hσ0 hσ1 E hτ
      (fun x => hvnn τ hτ x) (hwfac_cont τ hτ))
    hmixbridge (fun τ => hvdef τ)
    (fun _ _ => resolverCoeff_summable_of_envelope hμ hσ0 E)
    hvderiv hvxcont hQ_cont L hFl_cont

end ShenWork.Paper2.IntervalCarrySeamGradient

namespace ShenWork.Paper2.IntervalCarrySeamGradient
section AxiomAudit
#print axioms v_contDiff_two_of_envelope
#print axioms mixedMulBridge_of_Wsum
#print axioms carrySeam_of_mild_gradient
end AxiomAudit
end ShenWork.Paper2.IntervalCarrySeamGradient
