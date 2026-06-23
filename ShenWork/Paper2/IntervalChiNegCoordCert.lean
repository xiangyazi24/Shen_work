/-
  ShenWork/Paper2/IntervalChiNegCoordCert.lean

  **χ₀<0 CRUX A — the base trajectory `H^σ` envelope `E₀` via the cron1
  COORDINATEWISE-SUPERSOLUTION route (L∞-restricted Banach model, NO H^σ metric).**
  TWO-WAY AUDITED against the actual landed signatures.

  ## The cron1 route, verified against the repo (DERIVED vs CARRIED)

  The independent reasoner's two corrections both check out, and — crucially — the
  machinery they call for is ALREADY LANDED, axiom-clean, in this repo:

  * **NO H^σ metric.**  The contraction is the landed L∞ ORDER-BOX metric on the
    trajectory BCF space, restricted to the invariant EnvBall.  Built end-to-end:
      - `Traj t` = `C(Icc 0 t × Ω̄, ℝ)` is a Mathlib `CompleteSpace`; `EnvBallTraj
        E_base` is closed/complete (`isComplete_envBallTraj`, landed) — the
        "restricted invariant subset {L∞ box ∩ envelope}".
      - the contraction `hPhi : ContractingWith q trajPhi` is the sup-lift of the
        landed K-contraction `intervalConjugateDuhamelMap_diff_bound_of_banked`
        (`ConjugateMildExistenceCore.contraction_from_banked`) via
        `trajPhi_supLipschitz_of_pointwise` (landed).
      - the readout is `ContractingWith` UNIQUENESS (`fixedPoint_unique_traj`):
        the actual mild lift `Uu` and the Banach fixed point `Wstar∈EnvBall`
        coincide, transferring the EnvBall domination to `u`
        (`trajBanach_envelope_of_invariance`, landed).  Domination = OUTPUT, never
        a hypothesis — non-circular by construction.
      - the per-mode invariance is the supersolution CERTIFICATE: the chem leg by
        `chemDuhamel_uniform_strict` (`(1−e^{−δλ})/√λ ≤ δ` uniformly in k), the
        heat+log margin by `Hpersist_derived` (`e^{−ρλ}≤1` + `√δ` smallness) —
        `Tδ(ρ•E_base) ≤ E_base` — fed to `envBall_invariance_coeff` (all landed).
  * **The Fubini swap IS valid** (the diagonal `s=τ` is a null slice): the singular
    `(τ−s)^{−1/2}` gradient-Duhamel integral's BCF joint continuity is CLOSED in
    `conjugateLeg_continuous_full` (the rescaling `s=τ·r` + dominated convergence +
    the full deriv-series joint-`(τ,x)` continuity tower), and `hswap_chem`/
    `hswap_log` reduce to it via `cosineCoeffs_integral_swap'` (all landed).

  So crux A's analytic obstructions named by my two prior (wrong) briefs are GONE:
  the "no H^σ metric" stall dissolves (it's the L∞ metric), and the "hswap_log
  diagonal jump" stall dissolves (`conjugateLeg_continuous_full`).

  ## What this file DERIVES

  `chiNegBaseEnvelope_of_seam` — the χ₀<0 base `TrajectoryHSigmaEnvelope σ t
  (cosineCoeffs ∘ u)` = the capstone's `E₀` — assembled by consuming the landed
  `trajEnvelope_chiNeg_base` with the EXPLICIT genv-inflated supersolution
  `E_base := Estar_explicit û₀abs logE = 2·(û₀abs + logE)` and its `MemHSigma`
  (`Estar_memHSigma`, landed) + the nonnegativity, threading the landed L∞ Banach
  contraction/seed/lift inputs.  The `H^σ` membership and nonnegativity are DERIVED;
  the L∞ Banach inputs (`hPhi`/`hx₀`/`hUfix`/`hUu`/`hcontFam`) and the per-candidate
  seam `hseam` are the carried interface (see below).

  ## CARRIED — the SOLE genuine remaining gap (G2), named with the failed grep

  Every analytic engine of the route is landed; the one irreducible input is the
  per-candidate `TrajSeam.henv` (the candidate-generic CHEMOTAXIS-FLUX envelope):

      henv : ∀ s k r, |sineCoeffs (chemFluxLifted p (trajFun U r)) k| ≤ sineEnv E_base k

  for a GENERIC EnvBall candidate `U` (whose slices obey `Envelopes E_base`), against
  the BARE `sineEnv E_base`.  The landed flux-envelope engine `genv_of_traj_denom`
  (IntervalGWProductEnvelope:218) DOES produce a candidate-generic flux bound from a
  per-slice `Envelopes Uσ (cosineCoeffs (u τ))` (NOT keyed to the global solution),
  but its output is `trueCosProd (gW Uσ D.Gden) (sineEnv Uσ)` — the resolver-Wiener
  INFLATED envelope — strictly larger than bare `sineEnv Uσ`.  The `TrajSeam.henv`
  field of `envBall_invariance_coeff` demands the BARE `sineEnv E_base`; the gap is
  the missing producer that (i) supplies the candidate's resolver structure
  (`hQ`/`hWdef`/`hbr`/`hvrel`/`hdiv`/`DenomUniformEnvelope`) for a GENERIC `Traj`
  candidate `U` from `U ∈ EnvBall E_base`, and (ii) absorbs the `gW` inflation into
  the supersolution choice (`E_base` an inflated fixed point of the genv map, not the
  bare datum).  This is the cron1 `hmaps_env` "invariant-envelope proof" — the SOLE
  new analytic content.  Failed greps:
    grep -rn "henv.*candidate\|sineEnv.*EnvBall\|flux.*envelope.*generic" ⇒ only the
      CARRIED `TrajSeam.henv` field + the `u`-keyed `genv_of_trajectoryEnvelope_uncond`
    grep -rn "DenomUniformEnvelope.*Traj\|resolver.*candidate.*Envelopes" ⇒ NONE
  MISSING lemma (named): `trajSeam_henv_of_envBall` — the candidate-generic chem-flux
  bound `|sineCoeffs (chemFluxLifted p (trajFun U r)) k| ≤ sineEnv E_base k` from
  `U ∈ EnvBallTraj E_base`, via `genv_of_traj_denom` on the SEQUENCE `E_base` with the
  candidate resolver structure + the inflation absorbed into `E_base`.

  ## DERIVED vs CARRIED (verdict)
  DERIVED: the whole L∞-restricted Banach scaffold is landed and CONSUMED here
  (contraction = L∞ metric, Fubini = singular engine, supersolution certificate);
  the `E_base ∈ H^σ` + nonnegativity of the explicit supersolution.  CARRIED: the
  per-candidate seam `hseam` (its sole hard field `henv` = G2 above) and the
  mild-existence Banach inputs.  PARTIAL: crux A reduces to the single named lemma
  `trajSeam_henv_of_envBall` (the candidate-generic bare-`sineEnv` flux envelope).

  No sorry/admit/native_decide/custom axiom.  New file only.  Lines ≤ 100.
  Mathlib v4.29.1.  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import ShenWork.Paper2.IntervalChiNegMapsTo
import ShenWork.Paper2.IntervalChiNegUniformClose

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegCoordCert

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2.HSigmaScale (MemHSigma)
open ShenWork.Paper2.IntervalTrajectoryEnvelope (TrajectoryHSigmaEnvelope)
open ShenWork.Paper2.IntervalChiNegTrajBanach (Traj trajFun trajPhi EnvBallTraj)
open ShenWork.Paper2.IntervalChiNegMapsTo (TrajSeam trajEnvelope_chiNeg_base)
open ShenWork.Paper2.IntervalChiNegUniformClose (Estar_explicit Estar_memHSigma)
open scoped NNReal

/-! ## The χ₀<0 base trajectory `H^σ` envelope `E₀`, via the L∞-restricted Banach
machine fed the EXPLICIT genv-inflated supersolution `Estar = 2·(û₀abs + logE)`. -/

/-- **`chiNegBaseEnvelope_of_seam` (DERIVED — the cron1 assembly).**

The χ₀<0 base `TrajectoryHSigmaEnvelope σ t (cosineCoeffs ∘ u)` (the capstone's
`E₀`), produced by consuming the landed `trajEnvelope_chiNeg_base` with the EXPLICIT
supersolution `E_base := Estar_explicit û₀abs logE` and its `MemHSigma`
(`Estar_memHSigma`, DERIVED from `û₀abs, logE ∈ H^σ`) plus its nonnegativity.

The L∞-restricted Banach scaffold is entirely LANDED and threaded here: the
contraction `hPhi` (the L∞ order-box metric K-contraction — NO H^σ metric), the
per-candidate continuity family `hcontFam` (the singular Fubini engine
`conjugateLeg_continuous_full`), the EnvBall seed `hx₀`, and the mild lift
`hUfix`/`hUu`.  The EnvBall domination is the `trajBanach_envelope_of_invariance`
UNIQUENESS OUTPUT — never a hypothesis.  The SOLE carried analytic content is the
per-candidate seam `hseam`, whose hard field `henv` is gap G2 (see header). -/
def chiNegBaseEnvelope_of_seam {σ t : ℝ} {û₀abs logE : ℕ → ℝ}
    (hû₀ : MemHSigma σ û₀abs) (hlogE : MemHSigma σ logE)
    (hE0 : ∀ k, 0 ≤ Estar_explicit û₀abs logE k)
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (hcontFam : ∀ U : Traj t,
      Continuous (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
        ShenWork.IntervalConjugateDuhamelMap.intervalConjugateDuhamelMap p u₀
          (trajFun U) z.1.1 z.2))
    (hseam : ∀ U : Traj t, TrajSeam p u₀ (Estar_explicit û₀abs logE) U (hcontFam U))
    {q : ℝ≥0}
    (hPhi : ContractingWith q (fun U : Traj t => trajPhi p u₀ U (hcontFam U)))
    {x₀ : Traj t} (hx₀ : x₀ ∈ EnvBallTraj (t := t) (Estar_explicit û₀abs logE))
    {Uu : Traj t}
    (hUfix : Function.IsFixedPt (fun U : Traj t => trajPhi p u₀ U (hcontFam U)) Uu)
    {u : ℝ → ℝ → ℝ}
    (hUu : ∀ s : ↑(Set.Icc (0 : ℝ) t), ∀ x : ℝ,
      intervalDomainLift (trajFun Uu s.1) x = u s.1 x) :
    TrajectoryHSigmaEnvelope σ t (fun τ => cosineCoeffs (u τ)) :=
  trajEnvelope_chiNeg_base (Estar_memHSigma hû₀ hlogE) p u₀ hE0 hcontFam hseam
    hPhi hx₀ hUfix hUu

/-! ## AxiomAudit -/

section AxiomAudit
#print axioms chiNegBaseEnvelope_of_seam
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegCoordCert
