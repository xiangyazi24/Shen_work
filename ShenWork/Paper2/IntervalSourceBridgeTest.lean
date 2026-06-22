/-
  ShenWork/Paper2/IntervalSourceBridgeTest.lean

  **DECISIVE TEST (χ₀<0 spectral-representation residual): WIRING or genuine?**

  The χ₀<0 `IsPaper2ClassicalSolution` bottoms out at three residual fields
  carried by `BFormBankedInputs` / `BFormDirectFrontier`:

    (i)   `hB_global`  — `lift (D.u t) = ∑ₙ localRestartCoeff(â₀, bFormSourceCoeffs) t n · cosₙ`
    (ii)  `hsource_bridge` — the per-slice value identity the FORWARD producer
          `intervalConjugateDuhamelMap_cosineSeries` requires:
            `(−χ₀)·B_N(t−s) Q(x) + S(t−s) L(x) = unitIntervalCosineHeatValue(t−s) bForm`
    (iii) `hTimeNhd` (`HasTimeNeighborhoodSpectralAgreement`).

  This file isolates the *genuine analytic content* of the chemotaxis leg of
  (ii) and shows it is **pure wiring** from the LANDED B-kernel cosine series
  `intervalConjugateKernelOperator_cosineSeries`:

    `B_N(t) g (x) = unitIntervalCosineHeatValue t (fun n => nπ·intervalSineInner g n) x`,

  i.e. the conjugate B-kernel operator is the heat semigroup acting on the
  divergence-mode coefficient family `nπ·sineInner g = √λₙ·sineₙ = cosineCoeffs(∂ₓg)`.
  Both sides are the *same* `∑ₙ e^{−tλₙ}·cₙ·cosₙ` series — a term-by-term tsum
  congruence.  The only landed analytic input is the B-kernel cosine series
  (whose proof is the IBP/divergence-mode + heat diagonalization).  This is the
  hard half of `hsource_bridge`; the logistic half is the analogous heat-value
  identity already used in the forward producer's `hhom`, and the restart-coeff
  algebra (i) is the definitional unfolding `localRestartCoeff = e^{−τλ}â₀ + bₙ(τ)`.

  Conclusion (see report): residual (i)+(ii)+integrability = WIRING.  (iii) is
  the one genuinely separate analytic obligation (two-sided time neighborhood),
  but is itself already landed as a structure consumed downstream; it is not a
  missing lemma — it is a hypothesis fed from `IntervalMildTimeDerivContinuity`.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file, new names only.
-/
import ShenWork.Paper2.IntervalConjugateCosineSeries
import ShenWork.Paper2.IntervalBootstrapDecomp

noncomputable section

namespace ShenWork.Paper2.IntervalSourceBridgeTest

open ShenWork.IntervalConjugateDuhamelMap (intervalConjugateKernelOperator)
open ShenWork.IntervalConjugateCosineSeries
  (intervalSineInner intervalConjugateKernelOperator_cosineSeries)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.HSigmaScale (lam)
open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff)

/-- **The divergence-mode value bridge (chemotaxis leg of `hsource_bridge`).**

The conjugate B-kernel operator equals the interval heat semigroup acting on the
divergence-mode coefficient family `cₙ = nπ · intervalSineInner g n` (i.e.
`√λₙ · sineₙ(g) = cosineCoeffsₙ(∂ₓg)`):

    `B_N(t) g (x) = unitIntervalCosineHeatValue t (fun n => nπ·intervalSineInner g n) x`.

This is the value-level statement that the per-slice `hsource_bridge`'s
chemotaxis term needs.  Its proof is a single rewrite by the LANDED B-kernel
cosine series followed by a definitional `tsum` congruence against
`unitIntervalCosineHeatValue` — confirming the chemotaxis bridge is WIRING. -/
theorem conjugateKernel_eq_heatValue_divMode
    {t : ℝ} (ht : 0 < t) {g : ℝ → ℝ} (hg : Continuous g) (x : ℝ) :
    intervalConjugateKernelOperator t g x =
      unitIntervalCosineHeatValue t
        (fun n => ((n : ℝ) * Real.pi) * intervalSineInner g n) x := by
  rw [intervalConjugateKernelOperator_cosineSeries ht hg x]
  unfold unitIntervalCosineHeatValue unitIntervalCosineHeatPointWeight
  refine tsum_congr (fun n => ?_)
  -- both summands are `e^{−tλₙ}·(nπ·sineInner)·cos(nπx)` (cosineMode = unitIntervalCosineMode).
  show (Real.exp (-t * unitIntervalCosineEigenvalue n) *
        (((n : ℝ) * Real.pi) * intervalSineInner g n)) * cosineMode n x
      = Real.exp (-t * unitIntervalCosineEigenvalue n) * unitIntervalCosineMode n x *
          (((n : ℝ) * Real.pi) * intervalSineInner g n)
  rw [show unitIntervalCosineMode n x = cosineMode n x from rfl]
  ring

/-- **TASK 1 — the energy↔spectral coefficient reduction (restart-coeff algebra).**

The C²-bootstrap engine coefficient `duhamelEnergyCoeff 1 F t k` equals the
restart/Duhamel spectral coefficient `duhamelSpectralCoeff a t k` whose source
family is the divergence-mode reweighting `a s n = √λₙ · F n s`:

    `duhamelEnergyCoeff 1 F t k = duhamelSpectralCoeff (fun s n => √λₙ · F n s) t k`.

Both are `∫₀ᵗ √λ_k · e^{−λ_k(t−τ)} · F k τ dτ`; the integrands coincide after
`(lam k)^{1/2} = √(lam k)` and `−(1·λ_k·(t−τ)) = −(t−τ)·λ_k`.  This is the
algebraic core of `restartDuhamelCoeff = e^{−τλ}â₀ + bₙ(τ)` matching hdecomp's
`(−χ₀)·duhamelEnergyCoeff(sineCoeffs∘Q) + duhamelEnergyCoeff Fl`: with the
landed per-slice divergence-mode identity `√λₙ·sineCoeffsₙ(Q s) = coupledChemDiv`,
the `√λₙ·F` reweighting IS `bFormSourceCoeffs`, so the restart-coeff identity is
DEFINITIONAL once hdecomp + divergence-mode are in hand.  Pure wiring. -/
theorem duhamelEnergyCoeff_eq_duhamelSpectralCoeff_divMode
    (F : ℕ → ℝ → ℝ) (t : ℝ) (k : ℕ) :
    duhamelEnergyCoeff 1 F t k
      = duhamelSpectralCoeff (fun s n => Real.sqrt (lam n) * F n s) t k := by
  unfold duhamelEnergyCoeff duhamelSpectralCoeff
  show (∫ τ in (0:ℝ)..t,
        (lam k) ^ (1 / 2 : ℝ) * Real.exp (-(1 * lam k * (t - τ))) * F k τ)
      = ∫ s in (0:ℝ)..t,
        Real.exp (-(t - s) * unitIntervalCosineEigenvalue k)
          * (Real.sqrt (lam k) * F k s)
  refine intervalIntegral.integral_congr (fun τ _ => ?_)
  have hsqrt : (lam k) ^ (1 / 2 : ℝ) = Real.sqrt (lam k) :=
    (Real.sqrt_eq_rpow (lam k)).symm
  have hlam : lam k = unitIntervalCosineEigenvalue k := rfl
  rw [hsqrt, hlam]
  ring_nf

end ShenWork.Paper2.IntervalSourceBridgeTest

#print axioms
  ShenWork.Paper2.IntervalSourceBridgeTest.conjugateKernel_eq_heatValue_divMode
#print axioms
  ShenWork.Paper2.IntervalSourceBridgeTest.duhamelEnergyCoeff_eq_duhamelSpectralCoeff_divMode
