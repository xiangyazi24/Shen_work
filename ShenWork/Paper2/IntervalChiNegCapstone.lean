/-
  ShenWork/Paper2/IntervalChiNegCapstone.lean

  CHI-NEG CAPSTONE.  Specialize the LANDED direct base producer
  `trajEnvelope_chiNeg_base_direct` to `u := conjugatePicardLimit p u0 T`, with the
  local-existence SUBSTRATE genuinely DERIVED from faithful hypotheses, then feed the
  base E0 into `meanReach_H1_conjugate` to reach the H^1 trajectory envelope.

  TWO-WAY AUDIT (per the capstone discipline).

  DERIVED (consumed a landed lemma, hyps supplied here):
   * the local-existence core `ConjugateMildExistenceCore p u0` and `T>0`, from
     `conjugateMildExistenceCore_exists` (faithful hyps `PaperPositiveInitialDatum`,
     `1 <= alpha`, `1 <= gamma`);
   * the packaged mild-solution data `ConjugateMildSolutionData p u0` with
     `u = conjugatePicardLimit p u0 T`, via `ConjugateMildExistenceCore.toData` +
     `conjugateMildSolutionData_of_data` -- yielding `hbound`, `hnonneg`, `hcont`
     (`HasContinuousSlices`), `hmild` (the pointwise Duhamel fixed point) ALL derived;
   * these discharge the `meanReach_H1_conjugate` analytic hyps `hbd`, `hcont`,
     `hM0`/`hmean0` (the sup ball `M` from the data) and supply the solution `u`.

  CARRIED -- the GENUINE un-landed frontier (no landed producer; each named precisely):
   * `hPhi` -- the producer's `ContractingWith q (trajPhi ...)`.  Landed
     `trajPhi_contractingWith` consumes a Traj-BCF sup-Lipschitz bound
     `dist (trajPhi U1) (trajPhi U2) <= q * dist U1 U2`; the landed pointwise
     `ConjugateMildExistenceCore.contraction_from_banked` /
     `conjugateDuhamel_contraction_pointwise` give only a per-`(t,x)` K-contraction in
     the SLICE model `R -> intervalDomainPoint -> R`.  MISSING lemma = the Traj-model
     bridge `trajPhi_supLipschitz_of_pointwise` (sup over the box of the pointwise
     K-bound = the BCF `dist`).  NOT landed.
   * `hUfix`/`hUu` -- the trajPhi fixed point `Uu : Traj t` identified with
     `conjugatePicardLimit`.  Requires a JOINTLY (s,x)-continuous BCF lift of the
     limit (gap G1, the singular Duhamel BCF-continuity; `HasContinuousSlices` is only
     per-slice spatial continuity) AND the fixed-point identity from the pointwise
     `IntervalConjugateMildSolution` (`conjugatePicardLimit_is_mildSolution`).  MISSING
     lemma = `conjugatePicardLimit_trajLift_isFixedPt`.  NOT landed.
   * `hcontFam`/`hseam`/`henvH`/`hx0` -- the `TrajSeamDirect` analytic fields
     (`hQcont`/`hpt_heat`/`hchemD` via `chemDuhamel_direct`, ...), `Estar in H^sigma`
     via `memHSigma_deflate`, the EnvBall seed.  Carried per `IntervalChiNegBaseDirect`.
   * the `meanReach_H1_conjugate` `CarrySeam` `C` (incl. the genuinely-carried `hvnn`
     Neumann maximum principle, the bridges, the per-tau decomp residuals `hmd`).

  The H^1 domination is the `meanReach_H1_conjugate`/Banach OUTPUT, never a hypothesis.
  No sorry/admit/native_decide/custom axiom.  New file only.  Lines <= 100.
  Mathlib v4.29.1.  `#print axioms` subset of {propext, Classical.choice, Quot.sound}.
-/
import ShenWork.Paper2.IntervalChiNegBaseDirect
import ShenWork.Paper2.IntervalChiNegSeamFixedReach
import ShenWork.Paper2.IntervalChiNegMildPackage
import ShenWork.Paper2.IntervalConjugatePicardCoreInhabit

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegCapstone

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalDomain)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard
  (conjugatePicardLimit ConjugateMildSolutionData conjugateMildSolutionData_of_data
   conjugateMildExistenceCore_exists)
open ShenWork.IntervalMildPicard (HasContinuousSlices)
open ShenWork.Paper2 (PaperPositiveInitialDatum)
open ShenWork.Paper2.HSigmaScale (lam MemHSigma)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.IntervalDecompTauLift (conjQ conjFl)
open ShenWork.Paper2.IntervalTrajectoryEnvelope (TrajectoryHSigmaEnvelope)
open ShenWork.Paper2.IntervalChiNegTrajBanach (Traj trajFun trajPhi EnvBallTraj)
open ShenWork.Paper2.IntervalChiNegBaseDirect (TrajSeamDirect trajEnvelope_chiNeg_base_direct)
open ShenWork.Paper2.IntervalChiNegSeamFixedReach
  (CarrySeam CarrySeamSupply_windowHmd meanReach_H1_conjugate
   meanReach_H1_conjugate_windowHmd meanReach_H1_conjugate_windowHmd_supply)
open ShenWork.Paper2.IntervalChiNegMildPackage (DecompHyp conjugateMild_decomp_pos)
open ShenWork.IntervalConjugateDuhamelMap (intervalConjugateDuhamelMap)
open Real
open scoped NNReal

/-! ## 1. DERIVED local-existence substrate for `conjugatePicardLimit`.

From the faithful hypotheses `PaperPositiveInitialDatum`, `1 <= alpha`, `1 <= gamma`,
the landed `conjugateMildExistenceCore_exists` gives `T>0` + a
`ConjugateMildExistenceCore`, which `.toData` + `conjugateMildSolutionData_of_data`
package into a `ConjugateMildSolutionData` whose carried solution is exactly
`conjugatePicardLimit p u0 (data).T`.  Every field below is DERIVED. -/
def conjugateMildData (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    ConjugateMildSolutionData p u₀ :=
  conjugateMildSolutionData_of_data
    (Classical.choice (conjugateMildExistenceCore_exists p hα hγ hu₀).choose_spec.1).toData

theorem conjugateMildData_u (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    (conjugateMildData p hα hγ hu₀).u
      = conjugatePicardLimit p u₀ (conjugateMildData p hα hγ hu₀).T :=
  rfl

/-! ## 2. The DIRECT base E0 for the mild solution, via the landed producer.

`trajEnvelope_chiNeg_base_direct` specialised to the BCF-lifted slice
`u s := intervalDomainLift (D.u s)` of the DERIVED mild data `D`.  The carried
frontier (`hcontFam`/`hseam`/`hPhi`/`hx0`/`hUfix`/`hUu`/`henvH`) is exactly the
producer's irreducible interface -- see header for the missing Traj-model lemmas.
The output `TrajectoryHSigmaEnvelope sigma t (fun tau => cosineCoeffs (lift (D.u tau)))`
matches the meanReach base type by `rfl`. -/
def chiNeg_base_E0_conjugate {σ : ℝ} (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    {heatE chemE logE : ℕ → ℝ}
    (henvH : MemHSigma σ (fun k => heatE k + |p.χ₀| * chemE k + logE k))
    (hcontFam : ∀ U : Traj (conjugateMildData p hα hγ hu₀).T,
      Continuous (fun z : ↥(Set.Icc (0 : ℝ) (conjugateMildData p hα hγ hu₀).T)
          × intervalDomainPoint =>
        intervalConjugateDuhamelMap p u₀ (trajFun U) z.1.1 z.2))
    (hseam : ∀ U : Traj (conjugateMildData p hα hγ hu₀).T,
      TrajSeamDirect p u₀ heatE chemE logE U (hcontFam U))
    {q : ℝ≥0}
    (hPhi : ContractingWith q
      (fun U : Traj (conjugateMildData p hα hγ hu₀).T => trajPhi p u₀ U (hcontFam U)))
    {x₀ : Traj (conjugateMildData p hα hγ hu₀).T}
    (hx₀ : x₀ ∈ EnvBallTraj (t := (conjugateMildData p hα hγ hu₀).T)
      (fun k => heatE k + |p.χ₀| * chemE k + logE k))
    {Uu : Traj (conjugateMildData p hα hγ hu₀).T}
    (hUfix : Function.IsFixedPt
      (fun U : Traj (conjugateMildData p hα hγ hu₀).T => trajPhi p u₀ U (hcontFam U)) Uu)
    (hUu : ∀ s : ↑(Set.Icc (0 : ℝ) (conjugateMildData p hα hγ hu₀).T), ∀ x : ℝ,
      intervalDomainLift (trajFun Uu s.1) x
        = intervalDomainLift ((conjugateMildData p hα hγ hu₀).u s.1) x) :
    TrajectoryHSigmaEnvelope σ (conjugateMildData p hα hγ hu₀).T
      (fun τ => cosineCoeffs (intervalDomainLift ((conjugateMildData p hα hγ hu₀).u τ))) :=
  trajEnvelope_chiNeg_base_direct p henvH u₀ hcontFam hseam hPhi hx₀ hUfix hUu

/-! ## 3. CAPSTONE -- the chi<0 H^1 trajectory envelope for `conjugatePicardLimit`.

Feeds the DERIVED base E0 (section 2) into `meanReach_H1_conjugate`.  The mild-data
analytic hyps `hbd`/`hcont`/`hM0` are DERIVED from the substrate `D`; `hmean0`,
`hu0` (the tau=0 slice convention) and the per-tau `hmd` + the `CarrySeam` `C` are
CARRIED (see header).  The output H^1 envelope's domination is the meanReach/Banach
OUTPUT, never a hypothesis. -/
def chiNeg_H1_envelope_conjugate {σ₀ : ℝ} (n : ℕ) (hreach : (1 : ℝ) ≤ σ₀ + n * (1 / 4))
    (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    {μ β : ℝ} {v vx W : ℝ → ℝ → ℝ}
    (hu0 : (conjugateMildData p hα hγ hu₀).u 0 = u₀)
    (hmean0 : |cosineCoeffs (intervalDomainLift u₀) 0| ≤ (conjugateMildData p hα hγ hu₀).M)
    (hmd : ∀ τ, 0 < τ → ∀ k, k ≠ 0 →
      cosineCoeffs (intervalDomainLift ((conjugateMildData p hα hγ hu₀).u τ)) k
        = Real.exp (-(τ * lam k))
            * cosineCoeffs (intervalDomainLift u₀) k
          + (-p.χ₀) * duhamelEnergyCoeff 1
              (fun k τ => sineCoeffs (conjQ p (conjugateMildData p hα hγ hu₀).u τ) k) τ k
          + duhamelEnergyCoeff 1 (conjFl p (conjugateMildData p hα hγ hu₀).u) τ k)
    (E₀ : TrajectoryHSigmaEnvelope σ₀ (conjugateMildData p hα hγ hu₀).T
      (fun τ => cosineCoeffs (intervalDomainLift ((conjugateMildData p hα hγ hu₀).u τ))))
    (C : ∀ σ E, CarrySeam p μ β (conjugateMildData p hα hγ hu₀).T
      (conjugateMildData p hα hγ hu₀).u v vx W σ E) :
    TrajectoryHSigmaEnvelope 1 (conjugateMildData p hα hγ hu₀).T
      (fun τ => cosineCoeffs (intervalDomainLift ((conjugateMildData p hα hγ hu₀).u τ))) :=
  meanReach_H1_conjugate n hreach hu0 (conjugateMildData p hα hγ hu₀).hM.le
    (conjugateMildData p hα hγ hu₀).hbound (conjugateMildData p hα hγ hu₀).hcont
    hmean0 hmd E₀ C

/-- Window-restricted version of `chiNeg_H1_envelope_conjugate`.  The Duhamel
decomposition seam is required only on `0 < τ ≤ T`, the actual trajectory window. -/
def chiNeg_H1_envelope_conjugate_windowHmd {σ₀ : ℝ} (n : ℕ)
    (hreach : (1 : ℝ) ≤ σ₀ + n * (1 / 4))
    (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    {μ β : ℝ} {v vx W : ℝ → ℝ → ℝ}
    (hu0 : (conjugateMildData p hα hγ hu₀).u 0 = u₀)
    (hmean0 : |cosineCoeffs (intervalDomainLift u₀) 0| ≤ (conjugateMildData p hα hγ hu₀).M)
    (hmd : ∀ τ, 0 < τ → τ ≤ (conjugateMildData p hα hγ hu₀).T → ∀ k, k ≠ 0 →
      cosineCoeffs (intervalDomainLift ((conjugateMildData p hα hγ hu₀).u τ)) k
        = Real.exp (-(τ * lam k))
            * cosineCoeffs (intervalDomainLift u₀) k
          + (-p.χ₀) * duhamelEnergyCoeff 1
              (fun k τ => sineCoeffs (conjQ p (conjugateMildData p hα hγ hu₀).u τ) k) τ k
          + duhamelEnergyCoeff 1 (conjFl p (conjugateMildData p hα hγ hu₀).u) τ k)
    (E₀ : TrajectoryHSigmaEnvelope σ₀ (conjugateMildData p hα hγ hu₀).T
      (fun τ => cosineCoeffs (intervalDomainLift ((conjugateMildData p hα hγ hu₀).u τ))))
    (C : ∀ σ E, CarrySeam p μ β (conjugateMildData p hα hγ hu₀).T
      (conjugateMildData p hα hγ hu₀).u v vx W σ E) :
    TrajectoryHSigmaEnvelope 1 (conjugateMildData p hα hγ hu₀).T
      (fun τ => cosineCoeffs (intervalDomainLift ((conjugateMildData p hα hγ hu₀).u τ))) :=
  meanReach_H1_conjugate_windowHmd n hreach hu0 (conjugateMildData p hα hγ hu₀).hM.le
    (conjugateMildData p hα hγ hu₀).hbound (conjugateMildData p hα hγ hu₀).hcont
    hmean0 hmd E₀ C

/-- Exact finite-supply version of `chiNeg_H1_envelope_conjugate_windowHmd`.
The carried seam data is supplied only along the generated σ-ladder. -/
def chiNeg_H1_envelope_conjugate_windowHmd_supply {σ₀ : ℝ} (n : ℕ)
    (hreach : (1 : ℝ) ≤ σ₀ + n * (1 / 4))
    (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    {μ β : ℝ} {v vx W : ℝ → ℝ → ℝ}
    (hu0 : (conjugateMildData p hα hγ hu₀).u 0 = u₀)
    (hmean0 : |cosineCoeffs (intervalDomainLift u₀) 0| ≤ (conjugateMildData p hα hγ hu₀).M)
    (hmd : ∀ τ, 0 < τ → τ ≤ (conjugateMildData p hα hγ hu₀).T → ∀ k, k ≠ 0 →
      cosineCoeffs (intervalDomainLift ((conjugateMildData p hα hγ hu₀).u τ)) k
        = Real.exp (-(τ * lam k))
            * cosineCoeffs (intervalDomainLift u₀) k
          + (-p.χ₀) * duhamelEnergyCoeff 1
              (fun k τ => sineCoeffs (conjQ p (conjugateMildData p hα hγ hu₀).u τ) k) τ k
          + duhamelEnergyCoeff 1 (conjFl p (conjugateMildData p hα hγ hu₀).u) τ k)
    (E₀ : TrajectoryHSigmaEnvelope σ₀ (conjugateMildData p hα hγ hu₀).T
      (fun τ => cosineCoeffs (intervalDomainLift ((conjugateMildData p hα hγ hu₀).u τ))))
    (S : CarrySeamSupply_windowHmd (p := p) (u₀ := u₀) (μ := μ) (β := β)
      (t := (conjugateMildData p hα hγ hu₀).T)
      (Mmean := (conjugateMildData p hα hγ hu₀).M)
      (u := (conjugateMildData p hα hγ hu₀).u) (v := v) (vx := vx) (W := W)
      hu0 (conjugateMildData p hα hγ hu₀).hM.le
      (conjugateMildData p hα hγ hu₀).hbound
      (conjugateMildData p hα hγ hu₀).hcont
      hmean0 hmd n σ₀ E₀) :
    TrajectoryHSigmaEnvelope 1 (conjugateMildData p hα hγ hu₀).T
      (fun τ => cosineCoeffs (intervalDomainLift ((conjugateMildData p hα hγ hu₀).u τ))) :=
  meanReach_H1_conjugate_windowHmd_supply n hreach hu0
    (conjugateMildData p hα hγ hu₀).hM.le
    (conjugateMildData p hα hγ hu₀).hbound
    (conjugateMildData p hα hγ hu₀).hcont hmean0 hmd E₀ S

/-- Capstone variant that replaces the window-restricted `hmd` seam by the
standard `DecompHyp` bundle consumed by the landed positive-time decomposition. -/
def chiNeg_H1_envelope_conjugate_decompHyp {σ₀ : ℝ} (n : ℕ)
    (hreach : (1 : ℝ) ≤ σ₀ + n * (1 / 4))
    (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    {μ β : ℝ} {v vx W : ℝ → ℝ → ℝ}
    (hu0 : (conjugateMildData p hα hγ hu₀).u 0 = u₀)
    (hmean0 : |cosineCoeffs (intervalDomainLift u₀) 0| ≤ (conjugateMildData p hα hγ hu₀).M)
    (Dhyp : DecompHyp p u₀ (conjugateMildData p hα hγ hu₀).u
      (conjugateMildData p hα hγ hu₀).hmild (conjugateMildData p hα hγ hu₀).T)
    (E₀ : TrajectoryHSigmaEnvelope σ₀ (conjugateMildData p hα hγ hu₀).T
      (fun τ => cosineCoeffs (intervalDomainLift ((conjugateMildData p hα hγ hu₀).u τ))))
    (C : ∀ σ E, CarrySeam p μ β (conjugateMildData p hα hγ hu₀).T
      (conjugateMildData p hα hγ hu₀).u v vx W σ E) :
    TrajectoryHSigmaEnvelope 1 (conjugateMildData p hα hγ hu₀).T
      (fun τ => cosineCoeffs (intervalDomainLift ((conjugateMildData p hα hγ hu₀).u τ))) :=
  chiNeg_H1_envelope_conjugate_windowHmd n hreach p hα hγ hu₀ hu0 hmean0
    (conjugateMild_decomp_pos p (conjugateMildData p hα hγ hu₀) Dhyp) E₀ C

/-- Exact finite-supply capstone variant using the standard positive-time
decomposition hypothesis bundle. -/
def chiNeg_H1_envelope_conjugate_decompHyp_supply {σ₀ : ℝ} (n : ℕ)
    (hreach : (1 : ℝ) ≤ σ₀ + n * (1 / 4))
    (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    {μ β : ℝ} {v vx W : ℝ → ℝ → ℝ}
    (hu0 : (conjugateMildData p hα hγ hu₀).u 0 = u₀)
    (hmean0 : |cosineCoeffs (intervalDomainLift u₀) 0| ≤ (conjugateMildData p hα hγ hu₀).M)
    (Dhyp : DecompHyp p u₀ (conjugateMildData p hα hγ hu₀).u
      (conjugateMildData p hα hγ hu₀).hmild (conjugateMildData p hα hγ hu₀).T)
    (E₀ : TrajectoryHSigmaEnvelope σ₀ (conjugateMildData p hα hγ hu₀).T
      (fun τ => cosineCoeffs (intervalDomainLift ((conjugateMildData p hα hγ hu₀).u τ))))
    (S : CarrySeamSupply_windowHmd (p := p) (u₀ := u₀) (μ := μ) (β := β)
      (t := (conjugateMildData p hα hγ hu₀).T)
      (Mmean := (conjugateMildData p hα hγ hu₀).M)
      (u := (conjugateMildData p hα hγ hu₀).u) (v := v) (vx := vx) (W := W)
      hu0 (conjugateMildData p hα hγ hu₀).hM.le
      (conjugateMildData p hα hγ hu₀).hbound
      (conjugateMildData p hα hγ hu₀).hcont hmean0
      (conjugateMild_decomp_pos p (conjugateMildData p hα hγ hu₀) Dhyp)
      n σ₀ E₀) :
    TrajectoryHSigmaEnvelope 1 (conjugateMildData p hα hγ hu₀).T
      (fun τ => cosineCoeffs (intervalDomainLift ((conjugateMildData p hα hγ hu₀).u τ))) :=
  chiNeg_H1_envelope_conjugate_windowHmd_supply n hreach p hα hγ hu₀ hu0 hmean0
    (conjugateMild_decomp_pos p (conjugateMildData p hα hγ hu₀) Dhyp) E₀ S

end ShenWork.Paper2.IntervalChiNegCapstone

namespace ShenWork.Paper2.IntervalChiNegCapstone
section AxiomAudit
#print axioms conjugateMildData
#print axioms conjugateMildData_u
#print axioms chiNeg_base_E0_conjugate
#print axioms chiNeg_H1_envelope_conjugate
#print axioms chiNeg_H1_envelope_conjugate_windowHmd
#print axioms chiNeg_H1_envelope_conjugate_windowHmd_supply
#print axioms chiNeg_H1_envelope_conjugate_decompHyp
#print axioms chiNeg_H1_envelope_conjugate_decompHyp_supply
end AxiomAudit
end ShenWork.Paper2.IntervalChiNegCapstone
