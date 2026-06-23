/-
  ShenWork/Paper2/IntervalCarrySeamFrontier.lean

  χ₀<0 — `carrySeam_of_mild_frontier`: `carrySeam_of_mild_wiener` with the THREE
  reflCircle/coeff ℓ¹ summability atoms `hu_sum`, `hwfac_sum`, `hvsum` DISCHARGED
  purely from the trajectory `H^σ` envelope `E` plus landed resolver producers.

  ## Two-way audit (each discharged atom CONSUMES a landed lemma)

  * `hu_sum` (reflCircle ℓ¹ of `lift (u τ)`): `E.hdom τ hτ` gives the envelope
    domination `|cosineCoeffs (lift (u τ)) k| ≤ E.env k`; `memHSigma_of_envelope`
    (IntervalDenomSecondDerivBound) + `E.henv` give `MemHSigma σ (cosineCoeffs (lift
    (u τ)))`; `hSigma_subset_l1_of_gt_half` (IntervalWienerAlgebra) gives cosine ℓ¹;
    `fourierCoeff_reflCircle_summable_of_cosineCoeff_abs` (PdeUWiring) closes it.
    The ONLY genuine input is `hu_cont` (spatial continuity of the lift slice).

  * `hwfac_sum` (reflCircle ℓ¹ of the denom factor `(1+v)^{−β}`):
    `denom_envelope_memHSigma` (IntervalDenomEnvelopeResolver) gives `MemHSigma σ`
    of its cosine coeffs from `MemHSigma σ (cosineCoeffs (lift (u τ)))` (above) and
    resolver positivity `hvnn`; then the SAME ℓ¹ + reflCircle chain.  `hwfac_cont`
    is the genuine input.

  * `hvsum` (resolver-coeff ℓ¹ `Summable |resolverCoeff μ E.env|`):
    `resolver_memHSigmaPlus2_of_memHSigma` (HSigmaScale) lifts `E.henv` to
    `MemHSigma (σ+2) (resolverCoeff μ E.env)`; `hSigma_subset_l1_of_gt_half` (with
    `1/2 < σ+2` from `hσ0`) gives the ℓ¹.  NO genuine input.

  ## Carried (genuinely irreducible) — the precise frontier this file exposes
  The remaining `carrySeam_of_mild_wiener` inputs are the conj-mild trajectory
  REGULARITY data that NO landed producer supplies for the discontinuous
  zero-extension lift / the gradient `vx`:
    * `hu_cont`/`hwfac_cont` — spatial continuity of the lift slice / denom factor.
    * `hvxsum` — reflCircle ℓ¹ of `vx τ` (the gradient `v_x`); no `vx ∈ H^σ`
      producer exists (only the ABSTRACT carried `gvx` of `FluxFactorEnvelopes`).
    * `hvderiv`/`hvxcont` — `vx τ = ∂ₓ(v τ)` with `vx τ` continuous.
  plus the definitional/passthrough `hQ`/`hWdef`/`hvdef`/`hvnn`/`hQ_cont`/`L`/`hFl_cont`.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file only.  Lines ≤ 100.
-/
import ShenWork.Paper2.IntervalCarrySeamWienerDischarge
import ShenWork.Paper2.IntervalDenomEnvelopeResolver
import ShenWork.Paper2.IntervalDenomSecondDerivBound
import ShenWork.Paper2.IntervalDomainPdeUWiring

noncomputable section

namespace ShenWork.Paper2.IntervalCarrySeamFrontier

open scoped Real
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalCosineInversion (reflCircle)
open ShenWork.Paper2.HSigmaScale
  (lam MemHSigma resolverCoeff resolver_memHSigmaPlus2_of_memHSigma)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.Paper2.IntervalDenomEnvelopeResolver (resolverValue denom_envelope_memHSigma)
open ShenWork.Paper2.IntervalDenomSecondDerivBound (memHSigma_of_envelope)
open ShenWork.Paper2.IntervalWienerAlgebra (hSigma_subset_l1_of_gt_half)
open ShenWork.Paper2.PdeUWiring (fourierCoeff_reflCircle_summable_of_cosineCoeff_abs)
open ShenWork.Paper2.IntervalChiNegSeamFixedReach (CarrySeam)
open ShenWork.Paper2.IntervalCarrySeamWienerDischarge (carrySeam_of_mild_wiener)
open ShenWork.Paper2.IntervalTrajectoryEnvelope (TrajectoryHSigmaEnvelope)

variable {p : CM2Params} {μ β t σ : ℝ}
variable {u : ℝ → intervalDomainPoint → ℝ} {v vx W : ℝ → ℝ → ℝ}

/-- `MemHSigma σ (cosineCoeffs (lift (u τ)))` from the trajectory envelope `E`. -/
theorem memHSigma_lift_of_envelope
    (E : TrajectoryHSigmaEnvelope σ t (fun τ => cosineCoeffs (intervalDomainLift (u τ))))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) t) :
    MemHSigma σ (cosineCoeffs (intervalDomainLift (u τ))) :=
  memHSigma_of_envelope E.henv (fun k => E.hdom τ hτ k)

/-- `hu_sum` from `E` + slice continuity. -/
theorem reflCircle_lift_summable_of_envelope (hσ0 : 1 / 2 < σ)
    (E : TrajectoryHSigmaEnvelope σ t (fun τ => cosineCoeffs (intervalDomainLift (u τ))))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) t)
    (hu_cont : Continuous (intervalDomainLift (u τ))) :
    Summable (fun n : ℤ => fourierCoeff (reflCircle (intervalDomainLift (u τ))) n) :=
  fourierCoeff_reflCircle_summable_of_cosineCoeff_abs hu_cont
    (hSigma_subset_l1_of_gt_half hσ0 (memHSigma_lift_of_envelope E hτ))

/-- `hwfac_sum` from `E` + resolver positivity + denom-factor continuity. -/
theorem reflCircle_denom_summable_of_envelope (hμ : 0 < μ)
    (hσ0 : 1 / 2 < σ) (hσ1 : σ < 3 / 2)
    (E : TrajectoryHSigmaEnvelope σ t (fun τ => cosineCoeffs (intervalDomainLift (u τ))))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) t)
    (hvnn : ∀ x, 0 ≤ resolverValue μ (cosineCoeffs (intervalDomainLift (u τ))) x)
    (hwfac_cont : Continuous (fun x => (1 + resolverValue μ
      (cosineCoeffs (intervalDomainLift (u τ))) x) ^ (-β))) :
    Summable (fun n : ℤ => fourierCoeff (reflCircle (fun x => (1 + resolverValue μ
      (cosineCoeffs (intervalDomainLift (u τ))) x) ^ (-β))) n) :=
  fourierCoeff_reflCircle_summable_of_cosineCoeff_abs hwfac_cont
    (hSigma_subset_l1_of_gt_half hσ0
      (denom_envelope_memHSigma hμ hσ0 hσ1 (memHSigma_lift_of_envelope E hτ) hvnn))

/-- `hvsum` from `E` via the elliptic `H^σ → H^{σ+2}` resolver gain. -/
theorem resolverCoeff_summable_of_envelope (hμ : 0 < μ) (hσ0 : 1 / 2 < σ)
    (E : TrajectoryHSigmaEnvelope σ t (fun τ => cosineCoeffs (intervalDomainLift (u τ)))) :
    Summable (fun k => |resolverCoeff μ E.env k|) :=
  hSigma_subset_l1_of_gt_half (by linarith)
    (resolver_memHSigmaPlus2_of_memHSigma hμ E.henv).1

/-- **`carrySeam_of_mild_frontier` — `carrySeam_of_mild_wiener` with `hu_sum`,
`hwfac_sum`, `hvsum` DISCHARGED from the envelope `E` and landed resolver
producers.**  Hypotheses are `carrySeam_of_mild_wiener` VERBATIM minus those three
ℓ¹ atoms.  What remains is exactly the truly-irreducible conj-mild regularity
frontier: slice/factor continuity `hu_cont`/`hwfac_cont`, the gradient atoms
`hvxsum`/`hvderiv`/`hvxcont`, and definitional passthrough. -/
def carrySeam_of_mild_frontier
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
    (hwfac_cont : ∀ τ ∈ Set.Icc (0 : ℝ) t, Continuous (fun x => (1 + resolverValue μ
      (cosineCoeffs (intervalDomainLift (u τ))) x) ^ (-β)))
    (hvxsum : ∀ τ ∈ Set.Icc (0 : ℝ) t,
      Summable (fun n : ℤ => fourierCoeff (reflCircle (vx τ)) n))
    (hvdef : ∀ τ, v τ = resolverValue μ (cosineCoeffs (intervalDomainLift (u τ))))
    (hvderiv : ∀ τ ∈ Set.Icc (0 : ℝ) t, ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (v τ) (vx τ x) x)
    (hvxcont : ∀ τ ∈ Set.Icc (0 : ℝ) t, Continuous (vx τ))
    (hQ_cont : ∀ k, Continuous (fun τ => sineCoeffs
      (ShenWork.Paper2.IntervalDecompTauLift.conjQ p u τ) k))
    (L : TrajectoryHSigmaEnvelope σ t
      (fun τ k => ShenWork.Paper2.IntervalDecompTauLift.conjFl p u k τ))
    (hFl_cont : ∀ k, Continuous (ShenWork.Paper2.IntervalDecompTauLift.conjFl p u k)) :
    CarrySeam p μ β t u v vx W σ E :=
  carrySeam_of_mild_wiener E hμ hμ1 hσ0 hσ1 hβ ht ht1 hû₀ hvnn hQ hWdef
    hu_cont hwfac_cont
    (fun τ hτ => reflCircle_lift_summable_of_envelope hσ0 E hτ (hu_cont τ hτ))
    (fun τ hτ => reflCircle_denom_summable_of_envelope hμ hσ0 hσ1 E hτ
      (fun x => hvnn τ hτ x) (hwfac_cont τ hτ))
    hvxsum hvdef
    (fun _ _ => resolverCoeff_summable_of_envelope hμ hσ0 E)
    hvderiv hvxcont hQ_cont L hFl_cont

end ShenWork.Paper2.IntervalCarrySeamFrontier

namespace ShenWork.Paper2.IntervalCarrySeamFrontier
section AxiomAudit
#print axioms memHSigma_lift_of_envelope
#print axioms reflCircle_lift_summable_of_envelope
#print axioms reflCircle_denom_summable_of_envelope
#print axioms resolverCoeff_summable_of_envelope
#print axioms carrySeam_of_mild_frontier
end AxiomAudit
end ShenWork.Paper2.IntervalCarrySeamFrontier
