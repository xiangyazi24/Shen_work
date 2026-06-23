/-
  ShenWork/Paper2/IntervalChiNegClose.lean

  chi0<0 CLOSE -- the patched-uTilde capstone.  The H1 trajectory envelope for the
  conjugate mild solution, with the genuine t=0-convention seam `hu0` DISCHARGED
  (not carried) by threading the patched slice
  `uTilde tau := if tau = 0 then u0 else D.u tau` through the `u`-polymorphic
  capstone `meanReach_H1_conjugate` (IntervalChiNegSeamFixedReach:116).

  ## TWO-WAY AUDIT (exhaustive grep performed for every field; producers read).

  DERIVED (consume a landed lemma whose hypotheses are supplied here):
   * `hu0 : uTilde 0 = u0`.  By `if_pos rfl` on the patch -- the ONE genuine
     subtlety.  `IntervalConjugateMildSolution` constrains ONLY t>0
     (IntervalConjugateDuhamelMap:304), so uTilde stays a mild solution and every
     t>0 field is unchanged.
   * `hM0 : 0 <= D.M`     <- `D.hM.le`           (ConjugateMildSolutionData.hM).
   * `hbd : forall tau, 0<tau -> tau<=T -> |uTilde tau x| <= D.M`
       <- `D.hbound` via `uTilde tau = D.u tau` (tau>0).
   * `hcont : HasContinuousSlices T uTilde`  <- `D.hcont` via the same (tau>0).
   The H1 domination is `meanReach_H1_conjugate`'s `meanReach_H1_of_base` Banach
   OUTPUT -- never a hypothesis.

  CARRIED -- the GENUINE un-landed analytic frontier (each grepped exhaustively;
  the producers EXIST but bottom out on the SAME irreducible PDE crux, which the
  repo's OWN files document as having no Paper2 producer):
   * `hmd` (per-tau>0, k!=0 three-term mild Duhamel decomp).  Producer
     `conjugateSlice_decomp_tauLift_pos` (IntervalDecompTauLift:110) consumes the
     per-slice `hswap_chem`/`hswap_log`; via `cosineCoeffs_integral_swap'`
     (IntervalBootstrapInputs:107) these reduce to SLAB JOINT-CONTINUITY of the
     conjugate Duhamel integrands, which IntervalDomainJointTimeRegularity:57-89
     states is blocked on a MISSING parabolic representation theorem.  `hpt_heat`
     alone IS landed (`cosineCoeffs_intervalFullSemigroupOperator_diag`,
     IntervalGradientCoeffDuhamel:94).  MISSING: `conjugateMild_decomp_pos`.
   * `E0` (sigma0-base).  Producer `baseEnvelope_of_residualSupply_direct`
     (IntervalChiNegBaseDirectExtend:170) needs `Hpersist_direct` against a SINGLE
     `Estar` over [0,T] with the uniform deflated chem envelope `chemEenv`; that is
     the uniform-in-time H^sigma flux envelope `g`/`gl` which IntervalBootstrapInputs:
     112-130 + `fluxSine_timeSupEnvelope_memHSigma` (IntervalBootstrapDecomp:189)
     only REPACKAGE -- no producer in Paper2.  MISSING: `residualSupply_direct_of_
     conjugateMild`.
   * `C` (`CarrySeam` forall sigma E).  Producer `carrySeam_of_mild_gradient_cont`
     (IntervalCarrySeamGradientContinuousOn:206) still carries `L`, `hQ_cont`,
     `hFl_cont`, `hvnn` -- the logistic H^sigma envelope + Neumann max-principle, no
     bare-mild producer (grep for a `: CarrySeam` RESULT from raw data finds NONE).
     MISSING: `carrySeam_family_of_conjugateMild`.
   * `hmean0` (`|cosineCoeffs (lift u0) 0| <= D.M`).  The existence-core `M = 2*B0`
     (IntervalConjugatePicardCoreInhabit:112) bounds it, but `D.M` is exposed only
     through `Classical.choice`-opaque layers; no landed `...0 <= D.M` lemma.

  No field is faked; no field relabeled.  No sorry/admit/native_decide/custom axiom.
  New file only.  Lines <= 100.  Mathlib v4.29.1.
-/
import ShenWork.Paper2.IntervalChiNegSeamFixedReach
import ShenWork.Paper2.IntervalChiNegCapstone

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegClose

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalDomain)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardLimit ConjugateMildSolutionData)
open ShenWork.IntervalMildPicard (HasContinuousSlices)
open ShenWork.Paper2 (PaperPositiveInitialDatum)
open ShenWork.Paper2.HSigmaScale (lam)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.Paper2.IntervalDecompTauLift (conjQ conjFl)
open ShenWork.Paper2.IntervalTrajectoryEnvelope (TrajectoryHSigmaEnvelope)
open ShenWork.Paper2.IntervalChiNegSeamFixedReach (CarrySeam meanReach_H1_conjugate)
open ShenWork.Paper2.IntervalChiNegCapstone (conjugateMildData)

/-- The t=0-patched conjugate slice: `u0` at `tau=0`, the mild solution elsewhere.
Agrees with `D.u` for every `tau != 0`, in particular on all of (0,T]. -/
def uTilde (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    ℝ → intervalDomainPoint → ℝ :=
  fun τ => if τ = 0 then u₀ else (conjugateMildData p hα hγ hu₀).u τ

theorem uTilde_zero (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    uTilde p hα hγ hu₀ 0 = u₀ := if_pos rfl

theorem uTilde_pos (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    {τ : ℝ} (hτ : 0 < τ) :
    uTilde p hα hγ hu₀ τ = (conjugateMildData p hα hγ hu₀).u τ :=
  if_neg (ne_of_gt hτ)

/-- **`chiNeg_H1_closed`** -- the chi0<0 uniform H1 trajectory envelope for the
patched conjugate mild slice `uTilde`.  The `t=0` seam `hu0` is DISCHARGED here
(`uTilde_zero`); `hbd`/`hcont`/`hM0` are DERIVED from the mild-data substrate `D`
(via `uTilde_pos` on tau>0).  The remaining FOUR analytic inputs `hmean0`/`hmd`/
`E0`/`C` are CARRIED as named hypotheses (see header: each producer bottoms out on
the missing parabolic-representation / uniform-flux-envelope crux).  The H1
domination is the `meanReach_H1_conjugate` Banach OUTPUT, never a hypothesis. -/
def chiNeg_H1_closed {σ₀ : ℝ} (n : ℕ) (hreach : (1 : ℝ) ≤ σ₀ + n * (1 / 4))
    (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    {μ β : ℝ} {v vx W : ℝ → ℝ → ℝ}
    (hmean0 : |cosineCoeffs (intervalDomainLift u₀) 0| ≤ (conjugateMildData p hα hγ hu₀).M)
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
  meanReach_H1_conjugate n hreach (uTilde_zero p hα hγ hu₀)
    (conjugateMildData p hα hγ hu₀).hM.le
    (fun τ hτ hτT x => by
      rw [uTilde_pos p hα hγ hu₀ hτ]
      exact (conjugateMildData p hα hγ hu₀).hbound τ hτ hτT x)
    (fun τ hτ hτT => by
      rw [uTilde_pos p hα hγ hu₀ hτ]
      exact (conjugateMildData p hα hγ hu₀).hcont τ hτ hτT)
    hmean0 hmd E₀ C

end ShenWork.Paper2.IntervalChiNegClose

namespace ShenWork.Paper2.IntervalChiNegClose
section AxiomAudit
#print axioms chiNeg_H1_closed
end AxiomAudit
end ShenWork.Paper2.IntervalChiNegClose
