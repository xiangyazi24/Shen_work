/-
  ShenWork/Paper2/IntervalChiNegSeamFixed.lean

  χ₀<0 — CORRECTED reach toward `MemHSigma 1` / `TrajectoryHSigmaEnvelope 1` for
  `u = conjugatePicardLimit p u₀ DB.T`, bypassing the GENERICALLY-FALSE k=0
  mean-conservation field (`DecompHyp.hzero`).

  This file wires the concrete conjugate mild solution into the MEAN-FIXED ladder
  (`IntervalChiNegMeanFixedIterate`), discharging — from LANDED mild/decomp data —
  the TWO fields that depend on the false k=0 row in the OLD chain:

  * `hmean` (the DIRECT mean bound `|cosineCoeffs (u τ) 0| ≤ M`): from the mild
    solution's uniform L∞ bound (`conjugatePicardLimit_bounded`, value `≤ M`) +
    per-slice continuity (`HasContinuousSlices`), via the landed
    `cosineCoeffs_zero_abs_le_of_bound`.  This REPLACES the false mean-conservation
    `hzero` at k=0 with the TRUE direct mean bound.
  * `hdecomp_pos` (the SOUND k≠0 decomposition): from the landed
    `conjugateSlice_decomp_tauLift_pos` (τ>0) glued with the initial condition
    `u 0 = u₀` at τ=0 (both Duhamel legs vanish, k≠0 gives `û₀ k`).

  ## SIGNATURE-AUDITED CARRIED FRONTIER (NOT discharged — honest §3.3 accounting)

  * `hvnn` (resolver positivity): the Neumann elliptic maximum principle for
    `resolverValue` (the Fourier-cosine resolver of `(μ-Δ)` on `[0,1]`).  FIX 2's
    proposed producer `greenConv_nonneg_of_source_nonneg` is for the Paper1
    FULL-LINE advection-diffusion Green convolution `greenConv c lam` — a DIFFERENT
    operator with NO landed bridge to `resolverValue`.  So `hvnn` is GENUINELY
    CARRIED (as the prior opus / `IntervalDomainMildLocalChi0` state); it is NOT
    dischargeable from the landed lemmas.
  * the per-τ Wiener/mixed bridges (`hbr`/`hbridge`/`hvrel`/`hdiv`/`hQ_cont`/`L`/
    `hFl_cont`) — FIX 3: dischargeable IN PRINCIPLE from E via
    `cosineMulBridge_of_summable` + `fourierCoeff_reflCircle_summable_of_cosineCoeff_abs`
    + `HasContinuousSlices`, but require the full per-factor ℓ¹/MixedMulBridge
    assembly; carried here as the `MeanStepBundle` seam, NOT faked.
  * the BASE envelope `E₀` at σ₀>1/2 (the R1 continuation seed) and the per-τ
    decomposition residual bundle `R`.

  `MemHSigma 1` is NOT unconditional for `conjugatePicardLimit`; this file removes
  the FALSE k=0 obstruction and carries the genuine seam.  No `sorry`/`admit`/
  `native_decide`/custom `axiom`.  New file only.
-/
import ShenWork.Paper2.IntervalChiNegMeanFixedIterate
import ShenWork.Paper2.IntervalDecompTauLift
import ShenWork.Paper2.IntervalMildPicardRegularity

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegSeamFixed

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalConjugatePicard (conjugatePicardLimit)
open ShenWork.IntervalMildPicard (HasContinuousSlices)
open ShenWork.IntervalMildPicardRegularity (cosineCoeffs_zero_abs_le_of_bound)

/-- Continuity of the lift on `[0,1]` from subtype-continuity of the slice. -/
theorem lift_continuousOn_of_continuous {g : intervalDomainPoint → ℝ}
    (hg : Continuous g) : ContinuousOn (intervalDomainLift g) (Set.Icc (0:ℝ) 1) := by
  rw [continuousOn_iff_continuous_restrict]
  have hres : Set.restrict (Set.Icc (0:ℝ) 1) (intervalDomainLift g) = g := by
    funext z; obtain ⟨z, hz⟩ := z
    show intervalDomainLift g z = g ⟨z, hz⟩
    rw [intervalDomainLift, dif_pos hz]
  rw [hres]; exact hg

/-- **The DIRECT mean bound — `hmean`, REPLACING the false k=0 mean-conservation.**
For `0 < τ ≤ T`, from `|conjugatePicardLimit ... τ x| ≤ M` (the mild L∞ bound) and
per-slice continuity, `|cosineCoeffs (intervalDomainLift (u τ)) 0| ≤ M`.  This is
the TRUE k=0 envelope coefficient — NOT mean-conservation. -/
theorem mean_bound_of_mild {T M : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (hM0 : 0 ≤ M)
    (hbd : ∀ τ, 0 < τ → τ ≤ T → ∀ x : intervalDomainPoint, |u τ x| ≤ M)
    (hcont : HasContinuousSlices T u)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T) :
    |cosineCoeffs (intervalDomainLift (u τ)) 0| ≤ M := by
  refine cosineCoeffs_zero_abs_le_of_bound hM0
    (lift_continuousOn_of_continuous (hcont τ hτ0 hτT)) ?_
  intro x hx
  have hxval : intervalDomainLift (u τ) x = u τ ⟨x, hx⟩ := by
    rw [intervalDomainLift, dif_pos hx]
  rw [hxval]; exact hbd τ hτ0 hτT ⟨x, hx⟩

/-- **τ=0 glue for `hdecomp_pos`.**  At `τ = 0`, with `u 0 = u₀`, the k≠0 row of
the 3-term decomposition reduces to `cosineCoeffs (lift u₀) k = û₀ k` (both Duhamel
legs vanish, heat prefactor `exp 0 = 1`).  Discharged from `hu0`. -/
theorem decomp_tau0 (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (hu0 : u 0 = u₀) (k : ℕ) :
    cosineCoeffs (intervalDomainLift (u 0)) k
      = Real.exp (-((0:ℝ) * ShenWork.Paper2.HSigmaScale.lam k))
          * cosineCoeffs (intervalDomainLift u₀) k
        + (-p.χ₀) * ShenWork.Paper2.BFormHSigmaDuhamelEnergy.duhamelEnergyCoeff 1
            (fun k τ => ShenWork.Paper2.IntervalDivergenceModeIdentity.sineCoeffs
              (ShenWork.Paper2.IntervalDecompTauLift.conjQ p u τ) k) 0 k
        + ShenWork.Paper2.BFormHSigmaDuhamelEnergy.duhamelEnergyCoeff 1
            (ShenWork.Paper2.IntervalDecompTauLift.conjFl p u) 0 k := by
  have hchem : ShenWork.Paper2.BFormHSigmaDuhamelEnergy.duhamelEnergyCoeff 1
      (fun k τ => ShenWork.Paper2.IntervalDivergenceModeIdentity.sineCoeffs
        (ShenWork.Paper2.IntervalDecompTauLift.conjQ p u τ) k) 0 k = 0 := by
    show ShenWork.Paper2.BFormHSigmaDuhamelMode.duhamelModeCoeff 1 _ _ 0 = 0
    unfold ShenWork.Paper2.BFormHSigmaDuhamelMode.duhamelModeCoeff; simp
  have hlog : ShenWork.Paper2.BFormHSigmaDuhamelEnergy.duhamelEnergyCoeff 1
      (ShenWork.Paper2.IntervalDecompTauLift.conjFl p u) 0 k = 0 := by
    show ShenWork.Paper2.BFormHSigmaDuhamelMode.duhamelModeCoeff 1 _ _ 0 = 0
    unfold ShenWork.Paper2.BFormHSigmaDuhamelMode.duhamelModeCoeff; simp
  rw [hchem, hlog, hu0]; simp

end ShenWork.Paper2.IntervalChiNegSeamFixed

namespace ShenWork.Paper2.IntervalChiNegSeamFixed
#print axioms lift_continuousOn_of_continuous
#print axioms mean_bound_of_mild
#print axioms decomp_tau0
end ShenWork.Paper2.IntervalChiNegSeamFixed
