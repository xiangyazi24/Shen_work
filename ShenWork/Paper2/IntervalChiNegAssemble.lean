/-
  ShenWork/Paper2/IntervalChiNegAssemble.lean

  χ₀<0 FINAL ASSEMBLY — the H¹ trajectory envelope for the conjugate mild slice
  `uTilde`, via the BOX-EXTEND base `E₀` (NO BCF / NO `hcontFam` / NO τ=0-broken
  joint continuity).  Threads the four `chiNeg_H1_closed`
  (IntervalChiNegClose) capstone inputs:

    hmean0 — DERIVED unconditionally via `conjugateMildData_hmean0`
             (IntervalChiNegDatumBound), from `{hu₀, 1≤α, 1≤γ}` ALONE.
    hmd    — CARRIED.  Producer `conjugateSlice_decomp_tauLift_pos`
             (IntervalDecompTauLift) EXISTS; it carries the per-slice analytic residual
             BUNDLE (hQcont/hLcont/hLM/hheat_cont/hchemI_cont/hlogI_cont/hpt_heat/
             hswap_chem/hswap_log).  Even post-398b264,
             `logisticLeg_continuous_full` / `valueOp_src_jointCont` discharge the
             logistic/value LEG continuity ONLY GIVEN the source regularity
             (hL_meas/hL_cont/hL_int/hL_bound for `logisticLifted p (u·)`); NO landed
             lemma supplies that source regularity for `conjugatePicardLimit`.
             Reduction bottoms out on SLAB JOINT-CONTINUITY of the conjugate Duhamel
             integrands ⇐ the parabolic representation theorem
             (IntervalDomainJointTimeRegularity:50-89).  Grep
               grep -rn "conjugateMild_decomp_pos" ShenWork
             finds NONE.  MISSING: `conjugateMild_decomp_pos`.  CARRIED.
    E₀     — CARRIED.  Producer `baseEnvelope_of_residualSupply_direct`
             (IntervalChiNegBaseDirectExtend, box-extend; per-mode ContinuousOn ONLY,
             NO hcontFam) EXISTS; its chem leg is the DEFLATED Duhamel output supplied
             by `chemDuhamelOutput_le_of_envBall` (IntervalChiNegHenvEnvBall, 398b264).
             But its `hsupply` first conjunct `Hrestart` is the per-restart THREE-TERM
             mild Duhamel decomposition of the ACTUAL solution — the SAME slab
             joint-continuity / parabolic-representation crux as `hmd`
             (`Hrestart_derived` supplies ONE restart FROM `hdecomp0`, but `hdecomp0`
             IS that decomposition).  Grep
               grep -rn "residualSupply_direct_of_conjugateMild" ShenWork
             finds NONE.  MISSING: `residualSupply_direct_of_conjugateMild`.  CARRIED.
    C      — CARRIED.  Producer `carrySeam_of_mild_gradient_cont`
             (IntervalCarrySeamGradientContinuousOn) EXISTS but is PER-σ (consumes
             `hσ0 : 1/2 < σ`, `hσ1 : σ < 3/2` and `CarrySeam` carries those as FIELDS).
             The slot `C : ∀ σ E, CarrySeam … σ E` quantifies over ALL σ, so it is NOT
             inhabitable by the per-σ producer (the iterate evaluates the family only
             at finitely many in-range σ, but the Lean TYPE is `∀ σ`).  Beyond the
             σ-range gap the producer still needs `hvnn` (elliptic strong maximum
             principle — no Paper2 producer) + per-τ Wiener/mixed bridges + the
             logistic envelope `L`.  Grep
               grep -rn "carrySeam_family_of_conjugateMild" ShenWork
             finds NONE.  MISSING: `carrySeam_family_of_conjugateMild`.  CARRIED.

  ## TWO-WAY AUDIT.  DERIVED: `hmean0` (the cosine-mean datum bound — the ONE field
  genuinely closable from `{hu₀, α, γ}`).  The H¹ domination is the
  `meanReach_H1_conjugate` Banach OUTPUT, never a hypothesis.  CARRIED: `hmd`, `E₀`,
  `C` — each reduces to the SAME irreducible PDE crux the campaign documents
  (parabolic representation for hmd/E₀; elliptic max principle + σ-uniformity for C),
  carried as named hypotheses, never faked, never relabeled.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file only.  Lines ≤ 100.
  Mathlib v4.29.1.  `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.
-/
import ShenWork.Paper2.IntervalChiNegClose
import ShenWork.Paper2.IntervalChiNegDatumBound

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegAssemble

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalDomain)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2 (PaperPositiveInitialDatum)
open ShenWork.Paper2.HSigmaScale (lam)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.Paper2.IntervalDecompTauLift (conjQ conjFl)
open ShenWork.Paper2.IntervalTrajectoryEnvelope (TrajectoryHSigmaEnvelope)
open ShenWork.Paper2.IntervalChiNegSeamFixedReach (CarrySeam)
open ShenWork.Paper2.IntervalChiNegClose (uTilde chiNeg_H1_closed)
open ShenWork.Paper2.IntervalChiNegCapstone (conjugateMildData)
open ShenWork.Paper2.IntervalChiNegDatumBound (conjugateMildData_hmean0)

/-- **`chiNeg_H1_final`** — the χ₀<0 uniform H¹ trajectory envelope for the patched
conjugate mild slice `uTilde`, assembled via the BOX-EXTEND route.  The `t=0` seam
`hu0` is discharged INSIDE `chiNeg_H1_closed` (`uTilde_zero`); `hmean0` is DERIVED
here unconditionally via `conjugateMildData_hmean0`.  The three analytic seams
`hmd`/`E₀`/`C` are CARRIED as named hypotheses (each reducing to the parabolic
representation / elliptic max-principle PDE crux — see header, with failed greps).
The conclusion's H¹ domination is the `meanReach_H1_conjugate` Banach OUTPUT. -/
def chiNeg_H1_final {σ₀ : ℝ} (n : ℕ) (hreach : (1 : ℝ) ≤ σ₀ + n * (1 / 4))
    (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    {μ β : ℝ} {v vx W : ℝ → ℝ → ℝ}
    (hmd : ∀ τ, 0 < τ → ∀ k, k ≠ 0 →
      cosineCoeffs (intervalDomainLift (uTilde p hα hγ hu₀ τ)) k
        = Real.exp (-(τ * lam k))
            * cosineCoeffs (intervalDomainLift u₀) k
          + (-p.χ₀) * duhamelEnergyCoeff 1
              (fun k τ => sineCoeffs (conjQ p (uTilde p hα hγ hu₀) τ) k) τ k
          + duhamelEnergyCoeff 1 (conjFl p (uTilde p hα hγ hu₀)) τ k)
    (E₀ : TrajectoryHSigmaEnvelope σ₀ (conjugateMildData p hα hγ hu₀).T
      (fun τ => cosineCoeffs (intervalDomainLift (uTilde p hα hγ hu₀ τ))))
    (C : ∀ σ E, CarrySeam p μ β (conjugateMildData p hα hγ hu₀).T
      (uTilde p hα hγ hu₀) v vx W σ E) :
    TrajectoryHSigmaEnvelope 1 (conjugateMildData p hα hγ hu₀).T
      (fun τ => cosineCoeffs (intervalDomainLift (uTilde p hα hγ hu₀ τ))) :=
  chiNeg_H1_closed n hreach p hα hγ hu₀
    (conjugateMildData_hmean0 p hα hγ hu₀) hmd E₀ C

end ShenWork.Paper2.IntervalChiNegAssemble

namespace ShenWork.Paper2.IntervalChiNegAssemble
section AxiomAudit
#print axioms chiNeg_H1_final
end AxiomAudit
end ShenWork.Paper2.IntervalChiNegAssemble
