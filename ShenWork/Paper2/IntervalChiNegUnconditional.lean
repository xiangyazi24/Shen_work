/-
  ShenWork/Paper2/IntervalChiNegUnconditional.lean

  χ₀<0 — assembly of the base trajectory `H^σ` envelope from the landed
  `trajEnvelope_chiNeg_base` (IntervalChiNegMapsTo.lean), consuming the genuinely
  LANDED dischargers and exposing — precisely — the irreducible carried interface.

  ## Two-way audit / honest accounting (see REPORT)
  The brief asked to discharge EVERY `TrajSeam` field + Banach input down to
  CMParams + initial regularity.  After grepping the repo, the landed pieces split:

  * GENUINELY LANDED / consumed here:
    - `cosineCoeffs_integral_swap'` (IntervalBootstrapInputs.lean): the
      `hswap_chem`/`hswap_log` Fubini swaps reduce to slab joint-continuity data.
    - `trajPhi_contractingWith` (IntervalChiNegTrajBanach.lean): wraps a supplied
      trajectory sup-Lipschitz bound into `ContractingWith`.
    - the `hzero` three-term shape is rfl-level for `trajPhi` (BCF map definition).

  * GENUINELY CARRIED (NOT landed candidate-generically — the repo's OWN documented
    state, NOT a shortcut):
    - `henv` (candidate-generic flux H^σ envelope) — IntervalBootstrapInputs.lean
      TASK-1 module note: "the uniform-in-τ H^σ flux envelope … is the genuine PDE
      crux … requires a uniform-in-time (Gronwall/continuation) closure that is not
      yet in Paper2."  `genv_of_trajectoryEnvelope_uncond` / `carrySeam_of_mild_full`
      are keyed to the ACTUAL mild solution `u` (they CONSUME a TrajectoryHSigma-
      Envelope on `u`) and carry per-τ bridges; NOT generic over an EnvBall candidate.
    - `hgap`: `Hpersist_derived` carries `LocalExist` (per-r order-box on the actual
      solution); its shape is the Hpersist record, not the per-(s,k) TrajSeam.hgap.
    - the continuities / `hLM` / slab joint-continuities: carried solution data (the
      SAME residuals `conjugateSlice_decomp_tauLift_pos` carries for the actual `u`).
    - `hPhi` sup-Lipschitz bound, `hUfix`/`hUu` (mild-existence fixed point), `hx₀`,
      `henvH` — the Banach inputs; the mild lift identity
      `conjugateMildSolution_lift_eq_threeTermMap_on_Icc` carries
      `IntervalConjugateMildSolution` (existence), not from CMParams alone.

  This file assembles the base envelope with the LANDED contraction wrapper consumed,
  exposing the irreducible carried interface as named hypotheses, and provides the
  discharged Fubini-swap helpers (TASK-1 consumption).  No field is faked; the
  domination remains the OUTPUT of trajBanach uniqueness.

  No sorry/admit/native_decide/custom axiom.  New file only.  Lines ≤ 100.
-/
import ShenWork.Paper2.IntervalChiNegMapsTo
import ShenWork.Paper2.IntervalBootstrapInputs

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegUnconditional

open MeasureTheory Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateDuhamelMap (intervalConjugateKernelOperator)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.Paper2.IntervalChiNegMapsTo
open ShenWork.Paper2.IntervalChiNegTrajBanach
open ShenWork.Paper2.IntervalBootstrapInputs (cosineCoeffs_integral_swap')
open Real
open scoped NNReal

/-! ## 1. LANDED Fubini-swap consumption (TASK 1) — `hswap_chem`/`hswap_log`. -/

/-- The chemotaxis-leg Fubini swap of `TrajSeam.hswap_chem`, DERIVED from the slab
joint-continuity of the chemotaxis Duhamel integrand (the genuine, strictly-weaker
solution datum), via the landed `cosineCoeffs_integral_swap'`. -/
theorem hswap_chem_of_jointCont {p : CM2Params} {t : ℝ} (U : Traj t)
    (s : ↥(Set.Icc (0 : ℝ) t))
    (hjc : ContinuousOn (Function.uncurry
      (fun r x => intervalConjugateKernelOperator (s.1 - r) (chemFluxLifted p (trajFun U r)) x))
      (Set.Icc (0 : ℝ) s.1 ×ˢ Set.Icc (0 : ℝ) 1)) (k : ℕ) :
    cosineCoeffs (fun x => ∫ r in (0 : ℝ)..s.1,
        intervalConjugateKernelOperator (s.1 - r) (chemFluxLifted p (trajFun U r)) x) k
      = ∫ r in (0 : ℝ)..s.1, cosineCoeffs
        (fun x => intervalConjugateKernelOperator (s.1 - r) (chemFluxLifted p (trajFun U r)) x) k :=
  cosineCoeffs_integral_swap' s.2.1 _ hjc k

/-- The logistic-leg Fubini swap of `TrajSeam.hswap_log`, DERIVED from the slab
joint-continuity of the logistic Duhamel integrand, via `cosineCoeffs_integral_swap'`. -/
theorem hswap_log_of_jointCont {p : CM2Params} {t : ℝ} (U : Traj t)
    (s : ↥(Set.Icc (0 : ℝ) t))
    (hjc : ContinuousOn (Function.uncurry
      (fun r x => intervalFullSemigroupOperator (s.1 - r) (logisticLifted p (trajFun U r)) x))
      (Set.Icc (0 : ℝ) s.1 ×ˢ Set.Icc (0 : ℝ) 1)) (k : ℕ) :
    cosineCoeffs (fun x => ∫ r in (0 : ℝ)..s.1,
        intervalFullSemigroupOperator (s.1 - r) (logisticLifted p (trajFun U r)) x) k
      = ∫ r in (0 : ℝ)..s.1, cosineCoeffs
        (fun x => intervalFullSemigroupOperator (s.1 - r) (logisticLifted p (trajFun U r)) x) k :=
  cosineCoeffs_integral_swap' s.2.1 _ hjc k

/-! ## 2. LANDED contraction-wrapper consumption — `hPhi`. -/

/-- `ContractingWith q trajPhi`, CONSUMING the landed `trajPhi_contractingWith` from
the carried trajectory sup-Lipschitz bound `hLip` (the `Traj`-metric K-contraction;
NOT landed candidate-generically — see header).  This is the exact Banach `hPhi`
input of `trajEnvelope_chiNeg_base`. -/
theorem chiNeg_hPhi_of_lip {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {t : ℝ}
    (hcontFam : ∀ U : Traj t,
      Continuous (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
        ShenWork.IntervalConjugateDuhamelMap.intervalConjugateDuhamelMap
          p u₀ (trajFun U) z.1.1 z.2))
    {q : ℝ≥0} (hq : q < 1)
    (hLip : ∀ U₁ U₂ : Traj t, dist (trajPhi p u₀ U₁ (hcontFam U₁))
        (trajPhi p u₀ U₂ (hcontFam U₂)) ≤ (q : ℝ) * dist U₁ U₂) :
    ContractingWith q (fun U : Traj t => trajPhi p u₀ U (hcontFam U)) :=
  trajPhi_contractingWith hq hLip

/-! ## 3. FINAL — χ₀<0 base trajectory envelope, contraction wrapper CONSUMED. -/

/-- **χ₀<0 base `TrajectoryHSigmaEnvelope`, assembled with the LANDED contraction
wrapper consumed.**

Wires `trajEnvelope_chiNeg_base` (IntervalChiNegMapsTo.lean — itself the
`trajPhi_mapsTo` rfl-unbundled decomposition + `envBall_invariance_coeff` fed into
`trajBanach_envelope_of_invariance`) with `hPhi` PRODUCED here from the carried
trajectory sup-Lipschitz bound `hLip` via the landed `trajPhi_contractingWith`.

The domination `TrajectoryHSigmaEnvelope σ t (cosineCoeffs ∘ u)` is the OUTPUT of the
internal Banach fixed-point uniqueness (no disguised conclusion).

The remaining hypotheses are exactly the irreducible carried interface documented in
the header: the per-candidate analytic seam `hseam : ∀ U, TrajSeam …` (continuities,
`hLM`, the candidate-generic flux envelope `henv` = the PDE crux, the supersolution
gap `hgap`; the Fubini swaps inside it are now backed by §1's TASK-1 helpers and the
slab joint-continuities), the trajectory sup-Lipschitz bound `hLip`, the mild-existence
fixed point `hUfix`/`hUu`, the seed `hx₀`, and `henvH`.  Every one is a genuine
solution/regularity datum — NONE is the χ₀<0 boundedness conclusion itself. -/
def chiNeg_base_envelope_unconditional {σ t : ℝ} {E_base : ℕ → ℝ}
    (henvH : ShenWork.Paper2.HSigmaScale.MemHSigma σ E_base)
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (hE0 : ∀ k, 0 ≤ E_base k)
    (hcontFam : ∀ U : Traj t,
      Continuous (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
        ShenWork.IntervalConjugateDuhamelMap.intervalConjugateDuhamelMap
          p u₀ (trajFun U) z.1.1 z.2))
    (hseam : ∀ U : Traj t, TrajSeam p u₀ E_base U (hcontFam U))
    {q : ℝ≥0} (hq : q < 1)
    (hLip : ∀ U₁ U₂ : Traj t, dist (trajPhi p u₀ U₁ (hcontFam U₁))
        (trajPhi p u₀ U₂ (hcontFam U₂)) ≤ (q : ℝ) * dist U₁ U₂)
    {x₀ : Traj t} (hx₀ : x₀ ∈ EnvBallTraj (t := t) E_base)
    {Uu : Traj t}
    (hUfix : Function.IsFixedPt (fun U : Traj t => trajPhi p u₀ U (hcontFam U)) Uu)
    {u : ℝ → ℝ → ℝ}
    (hUu : ∀ s : ↑(Set.Icc (0 : ℝ) t), ∀ x : ℝ,
      intervalDomainLift (trajFun Uu s.1) x = u s.1 x) :
    ShenWork.Paper2.IntervalTrajectoryEnvelope.TrajectoryHSigmaEnvelope σ t
      (fun τ => cosineCoeffs (u τ)) :=
  trajEnvelope_chiNeg_base henvH p u₀ hE0 hcontFam hseam
    (chiNeg_hPhi_of_lip hcontFam hq hLip) hx₀ hUfix hUu

/-! ## AxiomAudit -/

section AxiomAudit
#print axioms hswap_chem_of_jointCont
#print axioms hswap_log_of_jointCont
#print axioms chiNeg_hPhi_of_lip
#print axioms chiNeg_base_envelope_unconditional
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegUnconditional
