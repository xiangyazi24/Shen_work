/-
  ShenWork/Paper2/IntervalChiNegUniformClose.lean

  **χ₀<0 CRUX A — the uniform a-priori flux envelope, via the EXPLICIT supersolution
  `Estar` (NO H^σ metric) + the crux-B logistic-leg continuity.**  TWO-WAY AUDITED.
  The genuinely-landed pieces are DERIVED here; the two un-closed pieces are named
  with their precise missing lemma + the failed greps.  Nothing is faked/relabeled.

  ## DERIVED (consume ONLY landed lemmas; NO fixed point, NO H^σ metric)

  1. `Estar_explicit` / `Estar_memHSigma` — the EXPLICIT supersolution sequence
     `Estar := 2·(|û₀| + logE) = 2·R₀` ∈ H^σ (σ>1/2), by `memHSigma_smul`/
     `memHSigma_add` on the two landed H^σ inputs.  This REPLACES the prior
     `Tsup_memHSigma` self-map (IntervalChiNegUniformEnvelope, 8fe0d45): no
     `ContractingWith`, no `MetricSpace`/`CompleteSpace` on H^σ (none is
     instantiated — `MemHSigma` is a bare `Summable` predicate; see CARRIED 1).

  2. `hlogI_cont_full` — the LOGISTIC value-Duhamel leg's INTEGRATED spatial
     continuity, DERIVED verbatim from crux B's `logisticLeg_continuous_full`
     (IntervalChiNegValueOpCont, 092bee5).  This is EXACTLY the `hlogI_cont` field
     of `conjugateSlice_decomp_tauLift` / `TrajSeamDirect` — the piece that fed the
     decomp's logistic leg and was the buildable half of crux B.  It is the
     genuinely-newly-unblocked logistic-leg continuity.

  ## CARRIED — the TWO genuine un-closed pieces (named precisely, with failed grep)

  CARRIED 1 — THE SUPERSOLUTION INEQUALITY does NOT close for "small T".  FIX 1 asks
  for `|χ₀|·chemDeflate(fluxEnv Estar) k ≤ R₀ k` "for T small enough", claiming the
  deflated chemotaxis Duhamel envelope carries a shrinking `T^{(1−σ)/2}` factor.  IT
  DOES NOT.  `coreEnv C α Msup k = (C·Rbar α)·(1+λ_k)^{−α/2}·Msup k`
  (IntervalTrajectoryEnvelope:160) with `Rbar α = 1/((1−α)/2) = 2/(1−α)`
  (IntervalUniformBootstrap:65) a T-INDEPENDENT constant.  The framework is
  DELIBERATELY Gronwall-free: the SOLE elapsed-time factor `s^{(1−α)/2}` is DISCARDED
  by `engine_sfactor_le_Rbar` (IntervalUniformBootstrap:74, comment "No elapsed-time
  growth ⇒ no Gronwall") for the s-uniform majorant `Rbar α`.  So
  `chemDeflate(fluxEnv Estar)` has NO T-smallness; with `fluxEnv Estar =
  trueCosProd(gW Estar)(sineEnv Estar)` QUADRATIC in `Estar` and `Estar = 2·R₀`,
  `|χ₀|·coreEnv(fluxEnv Estar)` is a FIXED quadratic budget, NOT `≤ R₀` for small T.
  And the per-restart box-extend `Hchem_direct` SOURCE bound `|sineCoeffs (Q τ) k| ≤
  M k` needs `M = genv(E₀)` (`genv_of_trajectoryEnvelope_uncond`,
  IntervalDenomSecondDerivBound:499, which CONSUMES `E : TrajectoryHSigmaEnvelope σ t
  (cosineCoeffs∘u)`) — CIRCULAR at the base.  Failed greps:
    grep -rn "ρ ^ ((1-α)/2)\|smallTime\|T_small\|delta.*shrink" ⇒ NONE
    grep -rn "of_boundUpTo.*Envelope\|sourceEnvelope_of_box" ⇒ NONE
    grep -rn "engine_sfactor"                  ⇒ ONLY engine_sfactor_le_Rbar (discards)
  MISSING lemma (named): `chemDeflate_smallTime_le` — a δ-SHRINKING per-restart
  chemotaxis Duhamel bound `|duhamelEnergyCoeff 1 Qsrc ρ k| ≤ c(ρ)·Msup k` with
  `c(ρ) → 0` as `ρ → 0` (KEEPING `s^{(1−α)/2}` rather than discarding it).

  CARRIED 2 — `hswap_log` (the Fubini swap field of `conjugateSlice_decomp_tauLift`
  / `TrajSeamDirect`) is NOT crux B and is NOT dischargeable by
  `cosineCoeffs_integral_swap'`.  Crux B's `logisticLeg_continuous_full` produces the
  INTEGRATED leg `hlogI_cont` (DERIVED above), a DIFFERENT object from `hswap_log`,
  which needs the INTEGRAND `(s,x) ↦ S(τ−s)(log(u s)) x` to be `ContinuousOn` the
  FULL slab `Icc 0 τ ×ˢ Icc 0 1`.  Under this repo's `S(0)f = 0` convention
  (`intervalFullSemigroupOperator_zero`, IntervalSemigroupAtZero:71) that integrand
  JUMPS at the diagonal `s = τ` (value `0`, but `s→τ⁻` limit `= log(u τ)(x) ≠ 0`) —
  the SAME `S(0)=0` obstruction `homLeg_value_at_zero` (IntervalChiNegLegContinuity)
  records — so it is NOT `ContinuousOn` the closed slab, and crux B's
  `valueOp_src_jointCont` (valid only off-diagonal, `τ−s ≥ τ₀ > 0`) cannot supply the
  `hcont` that `cosineCoeffs_integral_swap'` (IntervalBootstrapInputs:107) REQUIRES.
  The landed `hswap_log_of_jointCont` (IntervalChiNegUnconditional:84) itself TAKES
  that integrand `ContinuousOn` as a HYPOTHESIS — the framework never discharged it.
  Failed grep for a null-tolerant swap:
    grep -rn "integral_swap.*ae\|swap.*null\|cosineCoeffs.*swap.*ae" ⇒ NONE
  MISSING lemma (named): `cosineCoeffs_integral_swap_ae` — a Fubini swap tolerating a
  Lebesgue-null diagonal discontinuity (integrability via the L∞ bound, not full-slab
  continuity), which WOULD close `hswap_log` from crux B's off-diagonal continuity +
  the `intervalFullSemigroupOperator_Linfty_bound` majorant.

  ## DERIVED vs CARRIED (verdict)
  DERIVED: explicit `Estar ∈ H^σ` (no metric/fixed point); `hlogI_cont_full` (crux B
  verbatim — the genuinely-newly-landed logistic-leg INTEGRATED continuity).
  CARRIED: the supersolution INEQUALITY's small-T chem margin (no shrinking factor
  exists — Gronwall-free framework) and the `hswap_log` Fubini swap (diagonal `S(0)=0`
  discontinuity blocks the `ContinuousOn` swap).  Both named with the exact missing
  lemma + failed greps.  This is a PARTIAL: crux A is NOT closed.

  No sorry/admit/native_decide/custom axiom.  New file only.  Lines ≤ 100.
  Mathlib v4.29.1.
-/
import ShenWork.Paper2.IntervalChiNegValueOpCont
import ShenWork.Paper2.IntervalBootstrapInputs

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegUniformClose

open MeasureTheory Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.Paper2.HSigmaScale (MemHSigma)
open ShenWork.Paper2.IntervalWienerAlgebra (memHSigma_add memHSigma_smul)
open ShenWork.Paper2.IntervalChiNegValueOpCont (logisticLeg_continuous_full)
open Real

/-! ## 1. The EXPLICIT supersolution `Estar = 2·(|û₀| + logE) = 2·R₀` ∈ H^σ. -/

/-- **The explicit supersolution sequence** `Estar := 2·(û₀abs + logE)` (`= 2·R₀`,
`R₀ = û₀abs + logE`).  Built with NO fixed point and NO H^σ metric. -/
def Estar_explicit (û₀abs logE : ℕ → ℝ) : ℕ → ℝ :=
  fun k => 2 * (û₀abs k + logE k)

/-- **`Estar ∈ H^σ` (DERIVED).**  From `û₀abs, logE ∈ H^σ`, the explicit
`Estar = 2·(û₀abs + logE)` ∈ H^σ by `memHSigma_smul` + `memHSigma_add`.  No
`ContractingWith`, no `MetricSpace`/`CompleteSpace` on H^σ (none exists). -/
theorem Estar_memHSigma {σ : ℝ} {û₀abs logE : ℕ → ℝ}
    (hû₀ : MemHSigma σ û₀abs) (hlogE : MemHSigma σ logE) :
    MemHSigma σ (Estar_explicit û₀abs logE) :=
  memHSigma_smul 2 (memHSigma_add hû₀ hlogE)

/-! ## 2. The crux-B logistic-leg INTEGRATED continuity (DERIVED, `hlogI_cont`). -/

/-- **`hlogI_cont_full` (DERIVED from crux B).**  The integrated logistic value-
Duhamel leg's spatial continuity `Continuous (fun z => ∫₀^{z.1.1} S(z.1.1−s)(Lsrc s)
z.2)`, supplied verbatim by crux B's `logisticLeg_continuous_full`
(IntervalChiNegValueOpCont, 092bee5).  This is EXACTLY the `hlogI_cont` field of
`conjugateSlice_decomp_tauLift` / `TrajSeamDirect` — the genuinely-newly-unblocked
logistic-leg continuity (NOT `hswap_log`; see file header CARRIED 2). -/
theorem hlogI_cont_full {t : ℝ} (ht0 : 0 ≤ t) {Lsrc : ℝ → ℝ → ℝ} {CL : ℝ}
    (hCL : 0 ≤ CL) (hL_meas : Measurable (Function.uncurry Lsrc))
    (hL_cont : Continuous (Function.uncurry Lsrc))
    (hL_int : ∀ s, Integrable (Lsrc s) (intervalMeasure 1))
    (hL_bound : ∀ s y, |Lsrc s y| ≤ CL) :
    Continuous (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
      ∫ s in (0 : ℝ)..(z.1.1),
        intervalFullSemigroupOperator (z.1.1 - s) (Lsrc s) z.2.1) :=
  logisticLeg_continuous_full ht0 hCL hL_meas hL_cont hL_int hL_bound

/-! ## AxiomAudit -/

section AxiomAudit
#print axioms Estar_explicit
#print axioms Estar_memHSigma
#print axioms hlogI_cont_full
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegUniformClose
