/-
  ShenWork/Paper2/IntervalChiNegSeamDischarge.lean

  χ₀<0 — the FINAL seam-discharge layer for `u = conjugatePicardLimit p u₀ T`.

  This file does the honest accounting of WHICH `SeamHyp`/`DecompHyp` fields of
  `IntervalChiNegMildPackage` are discharged UNCONDITIONALLY from landed lemmas for
  the conjugate mild solution, and isolates — with a PROVEN reduction — the single
  genuinely-irreducible field: the `k = 0` mean-conservation residual `hzero`.

  ## WHAT THIS FILE PROVES (all UNCONDITIONAL, axiom-clean)

  * `duhamelEnergyCoeff_zero` — for ANY source family `F`, `duhamelEnergyCoeff d F τ 0
    = 0`.  ROOT CAUSE: `lam 0 = 0`, so the `√λ₀ = 0` prefactor of `duhamelModeCoeff`
    annihilates the whole integral.  Both Duhamel legs (chemotaxis AND logistic) of
    the `k = 0` decomposition therefore vanish identically.

  * `hzero_k0_iff_meanConservation` — for the conjugate slice, the `hzero` obligation
    at `k = 0` (the RHS of `DecompHyp.hzero`) is EQUIVALENT to plain mean conservation
    `cosineCoeffs (u τ) 0 = cosineCoeffs u₀ 0`.  This is because the heat prefactor
    `exp(-(τ·lam 0)) = exp 0 = 1` and BOTH Duhamel legs vanish (`duhamelEnergyCoeff_zero`).

  * `hzero_tau0` — the `τ = 0` branch of `hzero` is exactly the initial condition
    `u 0 = u₀` (heat at `τ = 0` is the identity coefficient, both Duhamel legs vanish
    by empty integration window).  Discharged UNCONDITIONALLY from `hu0`.

  ## THE GENUINE OBSTRUCTION — `hzero` at `k = 0`, `τ > 0` (reported, NOT faked)

  By `hzero_k0_iff_meanConservation`, the `k = 0`, `τ > 0` branch of `hzero` is mean
  conservation.  The conjugate MILD equation gives, at `k = 0`,
    `cosineCoeffs (u τ) 0 = û₀ 0 + (-χ₀)·(∫₀^τ mean of B_N-flux) + (∫₀^τ mean of logistic)`.
  The chemotaxis (divergence/Neumann) leg has zero mean, but the LOGISTIC reaction
  `L(u) = u·(a − b·uᵅ)` has GENERICALLY NONZERO mean, so the mild mean EVOLVES:
    `cosineCoeffs (u τ) 0 = û₀ 0 + ∫₀^τ (∫₀¹ L(u(s,x)) dx) ds ≠ û₀ 0`.
  Hence `hzero` at `k = 0`, `τ > 0` is GENERICALLY FALSE for the conjugate mild
  solution — it is NOT a missing producer, it is a FALSE identity in the presence of a
  reactive logistic source.  (Cf. the `IntervalDecompTauLift` doctrine note: "the shape
  at `k = 0` is the mean-conservation identity … which the logistic reaction does NOT
  satisfy in general.")  It is therefore CARRIED — never discharged, never faked.

  ## OTHER SEAM FIELDS — honest status for `conjugatePicardLimit` (NOT discharged here)

  * `SeamHyp.hvnn` (resolver positivity): the elliptic STRONG MAXIMUM PRINCIPLE.  Paper2
    has NO producer (`IntervalDomainMildLocalChi0`: "`Hvpos` … genuine residual; elliptic
    strong maximum principle").  CARRIED.
  * `SeamHyp.hbr`/`hbridge`/`hvrel`/`hdiv`: the per-τ Wiener/mixed bridges + resolver
    relay.  `cosineMulBridge_of_summable` discharges each ONLY GIVEN per-τ continuity +
    Fourier `ℓ¹` of the slice — i.e. `H^σ` (σ>1/2) regularity of `u τ`, which is the very
    bootstrap target.  At a fixed σ they are landed atoms; no σ-uniform PRODUCER from the
    mild data exists.  CARRIED per (σ,E).
  * `SeamHyp.hQ_cont`/`hFl_cont`/`DecompHyp.h*_cont`: per-τ flux/source/Duhamel
    continuities — the same residuals the landed endpoint decomposition carries.  CARRIED.

  ## NET VERDICT (signature-audited)

  `MemHSigma 1` is NOT reached UNCONDITIONALLY for `conjugatePicardLimit`.  The `k = 0`
  mean-conservation seam `hzero` is GENERICALLY FALSE (logistic reaction), and the
  resolver-positivity / bridge / continuity seam has no σ-uniform mild producer.  This
  file CLOSES the `k = 0` Duhamel-vanishing + the `hzero ↔ mean-conservation` reduction
  + the `τ = 0` branch UNCONDITIONALLY, and reports the residual `hzero` (k=0, τ>0) as a
  genuinely FALSE-in-general identity, carried with an explicit signature.  It then
  re-exposes the landed `reach_H1_conjugate` to confirm the H¹ field is reached EXACTLY
  modulo the carried seam (`SF`, `D`, `F`, …) — NOT unconditionally.

  NON-CIRCULAR: uses only landed mild/decomp atoms; never `localClassicalSolution`,
  `IsPaper2ClassicalSolution`, or C²-of-`u`.  No `sorry`/`admit`/`native_decide`/custom
  `axiom`.  New file only.  `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.
-/
import ShenWork.Paper2.IntervalChiNegMildPackage

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegSeamDischarge

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalConjugatePicard (conjugatePicardLimit)
open ShenWork.Paper2.HSigmaScale (lam)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.BFormHSigmaDuhamelMode (duhamelModeCoeff)
open ShenWork.Paper2.IntervalDecompTauLift (conjQ conjFl)
open ShenWork.Paper2.IntervalChiNegMildPackage (DecompHyp SeamHyp reach_H1_conjugate)

/-! ## `lam 0 = 0` and the `k = 0` Duhamel collapse. -/

/-- `lam 0 = 0` (the zeroth Neumann–cosine eigenvalue). -/
theorem lam_zero : lam 0 = 0 := by
  show unitIntervalCosineEigenvalue 0 = 0
  unfold unitIntervalCosineEigenvalue
  simp

/-- **The `k = 0` Duhamel coefficient vanishes for ANY source family.**  The
`√λ₀ = 0` prefactor inside `duhamelModeCoeff` annihilates the integrand pointwise. -/
theorem duhamelEnergyCoeff_zero (d : ℝ) (F : ℕ → ℝ → ℝ) (τ : ℝ) :
    duhamelEnergyCoeff d F τ 0 = 0 := by
  show duhamelModeCoeff d (lam 0) (F 0) τ = 0
  unfold duhamelModeCoeff
  rw [lam_zero]
  simp

/-! ## The `hzero ↔ mean-conservation` reduction at `k = 0`. -/

/-- **The `hzero` RHS at `k = 0` collapses to plain mean conservation.**  For the
conjugate slice the heat prefactor `exp(-(τ·lam 0)) = 1` and both Duhamel legs vanish
(`duhamelEnergyCoeff_zero`), so the `DecompHyp.hzero` obligation at `k = 0` is EXACTLY
`cosineCoeffs (lift (u τ)) 0 = cosineCoeffs (lift u₀) 0`. -/
theorem hzero_k0_iff_meanConservation (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ) (τ : ℝ) :
    (cosineCoeffs (intervalDomainLift (u τ)) 0
        = Real.exp (-(τ * lam 0)) * cosineCoeffs (intervalDomainLift u₀) 0
          + (-p.χ₀) * duhamelEnergyCoeff 1
              (fun k τ => sineCoeffs (conjQ p u τ) k) τ 0
          + duhamelEnergyCoeff 1 (conjFl p u) τ 0)
      ↔ cosineCoeffs (intervalDomainLift (u τ)) 0
          = cosineCoeffs (intervalDomainLift u₀) 0 := by
  rw [duhamelEnergyCoeff_zero, duhamelEnergyCoeff_zero, lam_zero]
  simp

/-- **The `τ = 0` branch of `hzero` is exactly the initial condition.**  At `τ = 0`
the heat prefactor is `exp 0 = 1` and both Duhamel legs vanish (empty window via
`duhamelEnergyCoeff_zero` at `τ = 0`), so `hzero` at `τ = 0` for every `k` reduces to
`cosineCoeffs (lift (u 0)) k = cosineCoeffs (lift u₀) k`, discharged from `u 0 = u₀`. -/
theorem hzero_tau0 (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    (hu0 : u 0 = u₀) (k : ℕ) :
    cosineCoeffs (intervalDomainLift (u 0)) k
      = Real.exp (-((0:ℝ) * lam k)) * cosineCoeffs (intervalDomainLift u₀) k
        + (-p.χ₀) * duhamelEnergyCoeff 1
            (fun k τ => sineCoeffs (conjQ p u τ) k) 0 k
        + duhamelEnergyCoeff 1 (conjFl p u) 0 k := by
  have hchem : duhamelEnergyCoeff 1 (fun k τ => sineCoeffs (conjQ p u τ) k) 0 k = 0 := by
    show duhamelModeCoeff 1 (lam k) _ 0 = 0
    unfold duhamelModeCoeff; simp
  have hlog : duhamelEnergyCoeff 1 (conjFl p u) 0 k = 0 := by
    show duhamelModeCoeff 1 (lam k) _ 0 = 0
    unfold duhamelModeCoeff; simp
  rw [hchem, hlog, hu0]
  simp

/-! ## The H¹-field re-exposure — EXACTLY modulo the carried seam. -/

/-- **The H¹ trajectory field for the conjugate mild solution, modulo the carried
seam.**  This is the landed `reach_H1_conjugate` re-exposed verbatim: given the
genuinely-carried per-`(σ,E)` seam `SF` (resolver positivity, bridges, relays,
continuities — none with a σ-uniform mild producer), the carried `DecompHyp` `D`
(whose `k = 0` field `hzero` is the GENERICALLY-FALSE mean-conservation residual
isolated above by `hzero_k0_iff_meanConservation`), the flux-factor base `F`, and the
numeric reach data, the trajectory reaches `TrajectoryHSigmaEnvelope 1`.

This is NOT an unconditional `MemHSigma 1`: the carried seam (`SF`, `D`, `F`,
`hFcont`, `htraj_dom`, `hreach`) is exactly the irreducible per-slice mild content. -/
def reach_H1_conjugate_modulo_seam (p : CM2Params)
    {T : ℝ} (u₀ : intervalDomainPoint → ℝ)
    {μ β σ₀ t : ℝ} {u : ℝ → intervalDomainPoint → ℝ} {v vx W : ℝ → ℝ → ℝ}
    (hσ₀ : 1 / 2 < σ₀) (hσ₀hi : σ₀ < 1) (ht : 0 < t) (ht1 : t ≤ 1)
    (hmild : ShenWork.IntervalConjugateDuhamelMap.IntervalConjugateMildSolution p T u₀ u)
    (hu0 : u 0 = u₀)
    (D : DecompHyp p u₀ u hmild t)
    (SF : ∀ σ : ℝ, ∀ E : ShenWork.Paper2.IntervalTrajectoryEnvelope.TrajectoryHSigmaEnvelope
        σ t (fun τ => cosineCoeffs (intervalDomainLift (u τ))),
        SeamHyp p μ β t u v vx W σ E)
    (F : ShenWork.Paper2.IntervalTrajectoryEnvelope.FluxFactorEnvelopes σ₀ t (conjQ p u))
    (hFcont : ∀ k, Continuous (fun τ => sineCoeffs (conjQ p u τ) k))
    (htraj_dom : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k,
      |cosineCoeffs (intervalDomainLift (u τ)) k|
        ≤ |duhamelEnergyCoeff 1 (fun k τ => sineCoeffs (conjQ p u τ) k) τ k|)
    (n : ℕ) (hreach : (1 : ℝ) ≤ (0 + σ₀) + n * (1 / 4)) :
    ShenWork.Paper2.IntervalTrajectoryEnvelope.TrajectoryHSigmaEnvelope 1 t
      (fun τ => cosineCoeffs (intervalDomainLift (u τ))) :=
  reach_H1_conjugate p u₀ hσ₀ hσ₀hi ht ht1 hmild hu0 D SF F hFcont htraj_dom n hreach

end ShenWork.Paper2.IntervalChiNegSeamDischarge

namespace ShenWork.Paper2.IntervalChiNegSeamDischarge
#print axioms lam_zero
#print axioms duhamelEnergyCoeff_zero
#print axioms hzero_k0_iff_meanConservation
#print axioms hzero_tau0
#print axioms reach_H1_conjugate_modulo_seam
end ShenWork.Paper2.IntervalChiNegSeamDischarge
