/-
  ShenWork/Paper2/IntervalChiNegUniformEnvelope.lean

  **χ₀<0 CRUX A — the uniform-in-time H^σ flux envelope `g`/`gl` via the
  supersolution SEQUENCE fixed point.**  PARTIAL with the exact obstruction.

  ## Route attempted (spec): the Banach fixed point on H^σ SEQUENCES
  `Tsup E := |û₀| + |χ₀|·chemDeflate(fluxEnv E) + logEnv`, with `fluxEnv` the flux
  factor envelope and `chemDeflate` the deflated chemDuhamel envelope, contracting
  on the H^σ-ball B(2R₀) for small `T`, fixed point `Estar = Tsup Estar`, then
  `g := fluxEnv Estar` with the τ-uniform domination `|sineCoeffs (Q τ) k| ≤ g k`.

  ## What this file DERIVES (axiom-clean, from landed lemmas)
  * `Tsup` — the supersolution sequence operator, defined directly from the landed
    factor envelopes (`sineEnv`, `gW`/`trueCosProd`) + the deflated Duhamel core
    (`coreEnv`/`memHSigma_deflate`).
  * `Tsup_memHSigma` (STEP 1 of the spec, DERIVED) — `Tsup` is a self-map of the
    `MemHSigma σ` predicate: for any `E ∈ H^σ` (with the nonneg/datum/log inputs in
    `H^σ`), `Tsup E ∈ H^σ`.  Consumes ONLY landed `memHSigma_add`, `memHSigma_smul`,
    `memHSigma_trueCosProd_of_gt_half`, `coreEnv_memHSigma`, `memHSigma_antitone`.
    This is the genuine self-map shard; no fixed point/contraction/domination.

  ## The PRECISE OBSTRUCTION (two genuine un-closed pieces; exhaustive grep below)

  OBSTRUCTION 1 — NO H^σ CompleteSpace / contraction metric (blocks STEPS 2–3).
  `ContractingWith.exists_fixedPoint` needs `Tsup` to be `ContractingWith q` on a
  `[MetricSpace α] [CompleteSpace α]` MODEL of the H^σ-ball.  Grep
    grep -rn "instance" *.lean | grep -iE "HSigma|hSigmaEnergy|EnvBall|weighted"
    grep -rn "MetricSpace|NormedAddCommGroup|CompleteSpace|EMetric" *.lean | grep HSigma
  finds NONE.  `MemHSigma σ a` (IntervalHSigmaScale:36) is a bare `Summable`
  PREDICATE, carrying NO norm/metric/uniformity.  EVERY `ContractingWith` in the
  repo (ChemMildLocal, IntervalChiNeg{TrajBanach,LocalExist,Capstone,…}) lives in
  the C[0,1]/`Traj` SUP metric, NOT the coefficient/H^σ space.  The landed
  `linfty_multiplier_bound` (IntervalBFormHSigmaLinftyMultiplier:83) supplies the
  per-mode `T^{(1−σ)/2}`/Rbar factor for ONE Duhamel application (the `coreEnv`
  deflation), NOT a `‖Tsup E₁ − Tsup E₂‖_{H^σ} ≤ q·‖E₁−E₂‖_{H^σ}` Lipschitz bound —
  there is no H^σ norm in which to state that difference.  MISSING (named precisely):
    `hSigma_completeMetricSpace` — a `MetricSpace`/`CompleteSpace` instance on the
    weighted-ℓ² H^σ ball (the from-scratch weighted-ℓ² Hilbert-space construction,
    or a `PiLp 2`/`lp 2`-weighted bridge), in which BOTH the `coreEnv` deflation
    multiplier `T^{(1−σ)/2}` AND the `trueCosProd` Wiener-algebra product are bona
    fide Lipschitz maps.  Not landed (cf. `IntervalChiNegEnvBallComplete` header:
    only the PRODUCT-topology closedness `isClosed_envBallSet` is derived, and it
    is the WRONG metric for any landed contraction).

  OBSTRUCTION 2 — the DOMINATION closure needs the mild Duhamel identity (blocks
  STEP 4, independently of OBSTRUCTION 1).  Even granting a fixed point `Estar`,
  `baseEnvelope_of_residualSupply_direct` (IntervalChiNegBaseDirectExtend:177)
  produces the trajectory envelope `E₀` ONLY from `hsupply`, whose first conjunct
  is `Hrestart χ₀ u Qsrc flLeg r δ` (IntervalChiNegBoxExtendDischarge:81) — the
  per-restart THREE-TERM mild Duhamel decomposition of `cosineCoeffs (u (r+ρ))`.
  This is a property of the ACTUAL solution `u`, NOT of the abstract sequence
  `Estar`; it is exactly the carried `hmd` of `chiNeg_H1_closed`
  (IntervalChiNegClose) and `hdecomp_pos` of `trajEnvelope_chiNeg_direct`
  (IntervalChiNegDirectSupersolution:147).  Grep
    grep -rn "conjugateMild_decomp_pos|residualSupply_direct_of_conjugateMild" *.lean
  finds NONE.  Its producer chain (`conjugateSlice_decomp_tauLift_pos` →
  `cosineCoeffs_integral_swap'`) reduces to SLAB JOINT-CONTINUITY of the conjugate
  Duhamel integrands, which `IntervalDomainJointTimeRegularity:50-89` documents is
  BLOCKED on a missing **parabolic representation theorem** (every classical
  solution equals the Neumann-heat semigroup of its trace) — at least as strong as
  the uniqueness being proved.  MISSING (named precisely):
    `residualSupply_direct_of_conjugateMild` — the per-restart `Hrestart` supply
    from the conjugate mild data, i.e. the parabolic representation bridge.

  ## DERIVED vs CARRIED
  DERIVED: `Tsup`, `Tsup_memHSigma` (the H^σ self-map, STEP 1) — consuming only
  landed `MemHSigma`-closure lemmas, no fixed point/contraction/domination faked.
  CARRIED / NOT CLOSED: STEPS 2–4.  The contraction + fixed point are blocked by
  OBSTRUCTION 1 (no H^σ metric); the domination `g`/`gl` for the actual solution is
  blocked by OBSTRUCTION 2 (the mild Duhamel `Hrestart` ⇐ parabolic representation).
  Both are the SAME irreducible PDE crux the campaign documents (`IntervalChiNegClose`
  `E₀` field, `IntervalChiNegEnvBallComplete` metric-mismatch header).  No
  `g`/`gl` with the τ-uniform domination is produced; nothing is faked or relabeled.

  No sorry/admit/native_decide/custom axiom.  New file only.  Lines ≤ 100.
  Mathlib v4.29.1.
-/
import ShenWork.Paper2.IntervalChiNegDirectSupersolution
import ShenWork.Paper2.IntervalChiNegBaseDirectExtend
import ShenWork.Paper2.IntervalGWProductEnvelope
import ShenWork.Paper2.IntervalMildPosTimeHSigma

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegUniformEnvelope

open ShenWork.Paper2.HSigmaScale (lam MemHSigma)
open ShenWork.Paper2.IntervalWienerAlgebra (memHSigma_add memHSigma_smul trueCosProd
  memHSigma_trueCosProd_of_gt_half)
open ShenWork.Paper2.IntervalGWProductEnvelope (gW)
open ShenWork.Paper2.IntervalTrajectoryEnvelope (coreEnv coreEnv_memHSigma)
open ShenWork.Paper2.IntervalMildPosTimeHSigma (memHSigma_antitone)

/-- **The supersolution sequence operator `Tsup`** (spec STEP 1, structural).
`Tsup û₀abs χ₀ Gden C α logE E := |û₀| + |χ₀|·coreEnv(C,α, fluxEnv E) + logE`,
where `fluxEnv E := gW E Gden = trueCosProd E Gden` (the landed cosine flux factor
product, with `Gden` the denominator factor envelope) — i.e. the bare-SEQUENCE flux
factor envelope, NOT the full `genv_of_trajectoryEnvelope_uncond` (which needs the
domination structure).  `coreEnv` is the deflated chemDuhamel envelope
(`(C·Rbar)·(1+λ)^{−α/2}·M`), matching `chemDuhamel_direct`. -/
def Tsup (û₀abs : ℕ → ℝ) (χ₀ : ℝ) (Gden : ℕ → ℝ) (C α : ℝ) (logE : ℕ → ℝ)
    (E : ℕ → ℝ) : ℕ → ℝ :=
  fun k => û₀abs k + |χ₀| * coreEnv C α (gW E Gden) k + logE k

/-- **`Tsup_memHSigma` (spec STEP 1 — DERIVED).**  `Tsup` is a self-map of the
`MemHSigma σ` predicate: from `E, û₀abs, Gden, logE ∈ H^σ` (σ > 1/2), `Tsup … E ∈
H^σ`.  Each summand is landed-closed: `|û₀|` and `logE` by hypothesis; the chem leg
`|χ₀|·coreEnv C α (trueCosProd E Gden)` by `memHSigma_trueCosProd_of_gt_half`
(the flux factor product ∈ H^σ) + `coreEnv_memHSigma` (deflation lands in H^{σ+α})
+ `memHSigma_antitone` (H^{σ+α} ⊆ H^σ) + `memHSigma_smul`; closed under
`memHSigma_add`.  NO fixed point / contraction / domination — purely the self-map.
domination is asserted here — this is purely the self-map shard. -/
theorem Tsup_memHSigma {σ χ₀ C α : ℝ} (hσ : 1 / 2 < σ) (hα0 : 0 ≤ α)
    {û₀abs Gden logE E : ℕ → ℝ}
    (hû₀ : MemHSigma σ û₀abs) (hGden : MemHSigma σ Gden)
    (hlogE : MemHSigma σ logE) (hE : MemHSigma σ E) :
    MemHSigma σ (Tsup û₀abs χ₀ Gden C α logE E) := by
  have hflux : MemHSigma σ (gW E Gden) :=
    memHSigma_trueCosProd_of_gt_half hσ hE hGden
  have hcore : MemHSigma σ (coreEnv C α (gW E Gden)) :=
    memHSigma_antitone (by linarith)
      (coreEnv_memHSigma (C := C) (α := α) (r := σ) (Msup := gW E Gden) hflux)
  have hchem : MemHSigma σ (fun k => |χ₀| * coreEnv C α (gW E Gden) k) :=
    memHSigma_smul |χ₀| hcore
  exact memHSigma_add (memHSigma_add hû₀ hchem) hlogE

/-! ## AxiomAudit -/

section AxiomAudit
#print axioms Tsup
#print axioms Tsup_memHSigma
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegUniformEnvelope
