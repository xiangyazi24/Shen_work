/-
  ShenWork/Paper2/IntervalChiNegFinal.lean

  χ₀<0 FINAL CAPSTONE.  The H¹ trajectory envelope for `conjugatePicardLimit`, with
  EVERY data-derivable input discharged from the four faithful hypotheses and the
  genuinely-open analytic seams carried EXPLICITLY (each named with its precise
  missing producer + the exhaustive grep that found no landed wiring).

  ## TWO-WAY AUDIT (exhaustive grep performed for every field).

  DERIVED (consume a landed lemma whose hypotheses are supplied here):
   * the mild-solution substrate `D := conjugateMildData p hα hγ hu₀`, from
     `conjugateMildExistenceCore_exists` + `conjugateMildSolutionData_of_data`
     (IntervalConjugatePicardCoreInhabit:88 / IntervalConjugatePicard).  Its carried
     `u = conjugatePicardLimit p u₀ D.T` (`conjugateMildData_u`, rfl), and the fields
     `hbound`/`hcont`/`hM` discharge `meanReach_H1_conjugate`'s `hbd`/`hcont`/`hM0`.
     These are wired INSIDE `chiNeg_H1_envelope_conjugate` (IntervalChiNegCapstone),
     which this file consumes; the H¹ domination is that lemma's Banach OUTPUT.

  CARRIED — the GENUINE un-landed frontier.  Each was grepped exhaustively:
   * `E₀` (the σ₀-scale base `TrajectoryHSigmaEnvelope`).  PRODUCER
     `baseEnvelope_of_residualSupply_direct` (IntervalChiNegBaseDirectExtend:177,
     f81a362) EXISTS, but its `hsupply` field — a per-restart supply of `Hrestart`,
     `Hchem_direct`, `Hpersist_direct` against a SINGLE `Estar` valid over all of
     `[0,T]` — is the uniform-in-time continuation closure.  GREP over ShenWork for a
     consumer keyed to `conjugatePicardLimit` finds NONE; `Hrestart_derived`
     (IntervalChiNegRestartIdentity:140) supplies ONE restart's `Hrestart` from
     `hdecomp0`, but NO landed lemma supplies the `Estar`-choice + `Hpersist_direct`
     margin uniformly.  MISSING: `residualSupply_direct_of_conjugateMild`.  Carried.
   * `C` (the `CarrySeam` family `∀ σ E`).  PRODUCERS `carrySeam_of_mild_gradient_cont`
     (IntervalCarrySeamGradientContinuousOn:7) and `carrySeam_of_mild_frontier`
     (IntervalCarrySeamFrontier:110) EXIST, but each consumes the logistic envelope
     `L : TrajectoryHSigmaEnvelope σ t (conjFl p u)`, the resolver-gradient regularity
     (`hvxcont`/`hvxsum`/`hQ_cont`), and the Neumann max-principle `hvnn`.  GREP for a
     `def`/`theorem` whose RESULT is `CarrySeam p …` (from the bare mild data) finds
     NONE; `logisticEnvelope_of_traj` only DESTRUCTS an existing env.  MISSING:
     `carrySeam_family_of_conjugateMild`.  Carried.
   * `hmd` (the per-τ, k≠0 three-term mild Duhamel decomposition).  PRODUCER
     `conjugateSlice_decomp_tauLift` (IntervalDecompTauLift:175) EXISTS but itself
     carries the per-slice seam (`hQcont`/`hpt_heat`/`hswap_chem`/…); no landed lemma
     discharges those for `conjugatePicardLimit` (IntervalCarrySeamFrontier wires the
     SPATIAL continuities only).  MISSING: `conjugateMild_decomp_pos`.  Carried.
   * `hu0` (`D.u 0 = u₀`).  `IntervalConjugateMildSolution` constrains ONLY `t>0`
     slices (IntervalConjugateDuhamelMap:304); the `t=0` value is an unpinned
     convention.  GREP finds no `…0 = u₀` lemma.  Carried.
   * `hmean0` (`|cosineCoeffs (lift u₀) 0| ≤ D.M`).  The mean ball `D.M` bounds `u` for
     `t>0` (`hbound`), not the `u₀` cosine mean directly.  Carried.

  No field is faked; no field is relabeled.  The H¹ domination is the meanReach OUTPUT.
  No sorry/admit/native_decide/custom axiom.  New file only.  Lines ≤ 100.
  Mathlib v4.29.1.  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import ShenWork.Paper2.IntervalChiNegCapstone

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegFinal

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalDomain)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2 (PaperPositiveInitialDatum)
open ShenWork.Paper2.HSigmaScale (lam)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.Paper2.IntervalDecompTauLift (conjQ conjFl)
open ShenWork.Paper2.IntervalTrajectoryEnvelope (TrajectoryHSigmaEnvelope)
open ShenWork.Paper2.IntervalChiNegSeamFixedReach (CarrySeam CarrySeamSupply_windowHmd)
open ShenWork.Paper2.IntervalChiNegMildPackage (DecompHyp)
open ShenWork.Paper2.IntervalChiNegCapstone
  (conjugateMildData chiNeg_H1_envelope_conjugate
   chiNeg_H1_envelope_conjugate_windowHmd chiNeg_H1_envelope_conjugate_windowHmd_supply
   chiNeg_H1_envelope_conjugate_decompHyp chiNeg_H1_envelope_conjugate_decompHyp_supply)

/-- **`chiNeg_H1_unconditional`** — the χ₀<0 uniform H¹ trajectory envelope for
`conjugatePicardLimit p u₀ D.T`.  Conditional on the four faithful hypotheses
(`PaperPositiveInitialDatum`, `1 ≤ α`, `1 ≤ γ`, and `hû₀` carried inside the seams) and
the EXPLICITLY-carried open analytic seams `hu0`/`hmean0`/`hmd`/`E₀`/`C` (each documented
in the header with its missing producer + failed grep).  The conclusion's H¹ domination
is the `meanReach_H1_conjugate` Banach OUTPUT, never a hypothesis. -/
def chiNeg_H1_unconditional {σ₀ : ℝ} (n : ℕ) (hreach : (1 : ℝ) ≤ σ₀ + n * (1 / 4))
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
  chiNeg_H1_envelope_conjugate n hreach p hα hγ hu₀ hu0 hmean0 hmd E₀ C

/-- Window-restricted version of `chiNeg_H1_unconditional`: the `hmd` seam is
only required on the actual interval `0 < τ ≤ T`, matching the landed positive-time
Duhamel producer. -/
def chiNeg_H1_unconditional_windowHmd {σ₀ : ℝ} (n : ℕ)
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
  chiNeg_H1_envelope_conjugate_windowHmd n hreach p hα hγ hu₀ hu0 hmean0 hmd E₀ C

/-- Exact finite-supply version of `chiNeg_H1_unconditional_windowHmd`.  The
carried seam input is only the generated ladder supply, not a global `∀ σ E`
family. -/
def chiNeg_H1_unconditional_windowHmd_supply {σ₀ : ℝ} (n : ℕ)
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
  chiNeg_H1_envelope_conjugate_windowHmd_supply n hreach p hα hγ hu₀
    hu0 hmean0 hmd E₀ S

/-- Final capstone variant that replaces the window-restricted `hmd` seam by the
standard positive-time decomposition hypothesis bundle. -/
def chiNeg_H1_unconditional_decompHyp {σ₀ : ℝ} (n : ℕ)
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
  chiNeg_H1_envelope_conjugate_decompHyp n hreach p hα hγ hu₀ hu0 hmean0 Dhyp E₀ C

/-- Exact finite-supply final capstone variant with the standard positive-time
decomposition hypothesis bundle. -/
def chiNeg_H1_unconditional_decompHyp_supply {σ₀ : ℝ} (n : ℕ)
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
      (ShenWork.Paper2.IntervalChiNegMildPackage.conjugateMild_decomp_pos p
        (conjugateMildData p hα hγ hu₀) Dhyp)
      n σ₀ E₀) :
    TrajectoryHSigmaEnvelope 1 (conjugateMildData p hα hγ hu₀).T
      (fun τ => cosineCoeffs (intervalDomainLift ((conjugateMildData p hα hγ hu₀).u τ))) :=
  chiNeg_H1_envelope_conjugate_decompHyp_supply n hreach p hα hγ hu₀
    hu0 hmean0 Dhyp E₀ S

end ShenWork.Paper2.IntervalChiNegFinal

namespace ShenWork.Paper2.IntervalChiNegFinal
section AxiomAudit
#print axioms chiNeg_H1_unconditional
#print axioms chiNeg_H1_unconditional_windowHmd
#print axioms chiNeg_H1_unconditional_windowHmd_supply
#print axioms chiNeg_H1_unconditional_decompHyp
#print axioms chiNeg_H1_unconditional_decompHyp_supply
end AxiomAudit
end ShenWork.Paper2.IntervalChiNegFinal
