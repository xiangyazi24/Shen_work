/-
  ShenWork/Paper2/IntervalMildPosTimeHSigma.lean

  THE ANALYTIC KEYSTONE (audit `ANALYSIS_struct_audit.md`, committed 7b1e544):
  positive-time spatial `MemHSigma 1` regularity of the χ₀<0 mild-solution slice
  `t ↦ (conjugatePicardLimit p u₀ DB.T) t`, discharged from the mild data + the
  H^σ Duhamel bootstrap engine, NON-CIRCULARLY (upstream of classical existence).

  ## What this file PROVES, unconditionally and axiom-clean

  * `conjugatePicardLimit_slice_memHSigma_zero` — the `H⁰ = L²` SEED of every
    interior slice, from mild-limit slice CONTINUITY alone
    (`conjugateMildSolutionData_of_data DB |>.hcont` ∘
    `memHSigma_zero_of_continuousOn`).  This uses ONLY `DB` mild data — no
    classical regularity, no `localClassicalSolution`.  This is the audit's
    producer-chain step 1, fully realized for the conjugate Picard limit.

  * `conjugatePicardLimit_slice_memHSigma_one_of_step` — the keystone in its
    CLOSEST PROVABLE FORM: given a `UniformBootstrapStep α` for the slice (the
    engine's per-level `H^σ → H^{σ+α}` map — the object `IntervalUniformBootstrap`
    carries uninstantiated) and a step count `n` with `1 ≤ n·α`, the H⁰ seed is
    promoted to `MemHSigma 1` by iterating the engine (`memHSigma_iterate`).  No
    Gronwall; this is the audit's producer-chain steps 2–4 made into a clean
    ladder for the SLICE.

  ## The PRECISE STALL (reported, not faked — §3.3 self-check)

  The unconditional `u_posTime_memHSigma_one_of_mild` (a `UniformBootstrapStep`
  for the slice built from `DB` alone) is NOT yet deliverable.  The obstruction is
  a GENUINE MISSING ANALYTIC INPUT, not (the audit's feared) circularity with
  `localClassicalSolution` — but it is sharper than "the kernel identity is
  missing", so the precise account is:

  STEP-engine target.  `gradientSolution_memHSigma_succ_wired`
  (IntervalBootstrapStep.lean:192) gives `MemHSigma σ a → MemHSigma (σ+α)
  (cosineCoeffs ut)` from the endpoint-uniform Duhamel gain, carrying

    (i)  hdecomp : cosineCoeffs ut k = exp(-tλ_k)·a k
                    + (-χc)·duhamelEnergyCoeff 1 Fc t k
                    + (-χL)·duhamelEnergyCoeff 1 Fl t k
    (ii) hMc / hMl : the flux/source envelopes `Mc, Ml ∈ H^σ`
                     (Summable (1+λ_k)^σ (Mc k)²), bounding Fc = sineCoeffs∘Q
                     and the logistic source.

  What EXISTS (so the audit's chain is real).  The per-mode B-kernel spectral
  identity is PRESENT and unconditional:

    `intervalConjugateKernelOperator_cosineSeries` (IntervalConjugateCosineSeries
    .lean:246) — for any continuous g,
        B_N(t)g (x) = ∑ₙ e^{-tλ_n}·(nπ)·sineInner g n · cosineMode n x,
    i.e. cosineCoeffs(B_N(t)g)_n = e^{-tλ_n}·√λ_n·sineCoeffs(g)_n, NO regularity
    hypothesis.  So the conjugate (B-form) chemotaxis leg DOES diagonalize to the
    spectral divergence form the engine consumes.

  What is MISSING (the genuine remaining gap), in two coupled pieces:

  * (A) hdecomp assembly.  `conjugatePicardLimit_cosineSeries`
    (IntervalConjugateCosineSeries.lean:507) assembles the slice cosine series but
    carries `hsrcB : DuhamelSourceTimeC1 (bFormSourceCoeffs …)` (time-C¹ of the
    B-form source coeffs), the Duhamel-leg integrabilities `hB_int`/`hlog_int`,
    and — flagged in that file's own header (lines 392-397) as "the missing
    analytic statement" — `hsource_bridge`, identifying the physical
    (−χ₀·B-kernel-flux + logistic) source with the `bFormSourceCoeffs` heat value.

  * (B) σ-level flux envelope.  Even granting (A), hMc demands the flux envelope
    `Mc ∈ H^σ` at the RUNNING σ, i.e. `Q = u·(1+v)^{-β}·v_x ∈ H^σ`, hence
    `v_x ∈ H^σ` (`fluxFunction_memHSigma`, IntervalBootstrapStep.lean:109,
    comment 107).  The resolver only RELAYS regularity (`envelopes_resolver`); it
    does not manufacture H^σ from the L∞ flux bound (`chemFluxLifted_sup_bound_of_ball`).
    There is no `MemHSigma σ … of_bounded` for σ>0 (correctly — L∞ ⇏ H^{σ>0}).

  Why this is NOT circular.  Neither (A) nor (B) needs `localClassicalSolution`.
  (A) is a spectral/integrability computation on the mild fixed point; (B) is the
  bootstrap's own monotone induction (the input `MemHSigma σ a` is meant to feed
  the resolver to recover `v_x ∈ H^σ`).  The reason the unconditional `step` is
  not yet closable is that the present REPO producers of `hsrcB`/`hsource_bridge`
  /`hchemFourier` for the conjugate Picard LIMIT all route through `ContDiffOn ℝ 2`
  -Neumann regularity of the chemotaxis-divergence slice
  (`hchemFourier_slice_of_limit_C2Neumann`, IntervalBankChemDivFourier.lean:102;
  `hasBFormSpectralPdeAgreement_…_PID_unconditional`, IntervalBFormPIDUnconditional
  .lean:100) — i.e. only DOWNSTREAM producers are wired, not the upstream
  mild-only ones the audit prescribes.

  VERDICT: the keystone is SOUND and the H^σ ladder is REAL (this file builds it
  end-to-end from the H⁰ seed).  The remaining work to make the `step`
  unconditional is to wire, FROM `DB` mild data only: (A) `DuhamelSourceTimeC1`
  + the flux source-bridge for the conjugate B-form (the per-mode kernel identity
  `intervalConjugateKernelOperator_cosineSeries` is the key lemma, already
  present), and (B) the resolver `H^σ`-relay turning the input `MemHSigma σ
  (cosineCoeffs ut)` into the flux envelope `Mc ∈ H^σ`.  Both are non-circular;
  supplying them yields `UniformBootstrapStep α (slice)` and discharges the
  unconditional keystone verbatim via the ladder below.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file only.
-/
import ShenWork.Paper2.IntervalUniformBootstrap
import ShenWork.Paper2.IntervalBootstrapStep
import ShenWork.Paper2.IntervalChiNegCloseBaseSeed
import ShenWork.Paper2.IntervalConjugatePicard

noncomputable section

namespace ShenWork.Paper2.IntervalMildPosTimeHSigma

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2.HSigmaScale (MemHSigma)
open ShenWork.IntervalConjugatePicard
  (conjugatePicardLimit conjugateMildSolutionData_of_data ConjugateMildExistenceData)
open ShenWork.Paper2.IntervalUniformBootstrap (UniformBootstrapStep)
open ShenWork.Paper2.IntervalBootstrapStep (memHSigma_iterate)
open ShenWork.Paper2.ChiNegCloseBaseSeed (memHSigma_zero_of_continuousOn
  intervalDomainLift_continuousOn_Icc_of_continuous)
open ShenWork.Paper2.HSigmaScale (lam lam_nonneg)

/-! ## `H^σ` scale monotonicity (lower index from higher index).

`MemHSigma` is decreasing in `σ`: since `1 + λ_k ≥ 1`, the weight `(1+λ_k)^σ` is
monotone in `σ`, so summability at the larger index dominates the smaller. -/

/-- `MemHSigma` is antitone in the regularity index: `σ ≤ τ ⟹ MemHSigma τ a →
MemHSigma σ a`. -/
theorem memHSigma_antitone {σ τ : ℝ} (hστ : σ ≤ τ) {a : ℕ → ℝ}
    (h : MemHSigma τ a) : MemHSigma σ a := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) h
  · have := lam_nonneg k
    positivity
  · have h1 : (1 : ℝ) ≤ 1 + lam k := by have := lam_nonneg k; linarith
    have hw : (1 + lam k) ^ σ ≤ (1 + lam k) ^ τ :=
      Real.rpow_le_rpow_of_exponent_le h1 hστ
    exact mul_le_mul_of_nonneg_right hw (sq_nonneg _)

/-- The mild-solution spatial slice as a `ℝ → ℝ` (lift of the conjugate Picard
limit at time `t`).  This is exactly the object the bootstrap acts on. -/
def conjugateSlice (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (T t : ℝ) : ℝ → ℝ :=
  intervalDomainLift ((conjugatePicardLimit p u₀ T) t)

/-! ## Producer-chain step 1 — the `H⁰` seed from mild-limit slice continuity.

This is the NON-CIRCULAR base regularity: it uses only the continuity of the
mild-limit slices packaged in `conjugateMildSolutionData_of_data DB`, which is
upstream of any classical-existence result. -/

/-- **The `H⁰ = L²` seed of the χ₀<0 mild slice.**  For every interior time
`t ∈ (0, DB.T]` the slice lift is continuous on `[0,1]` (mild-limit
`HasContinuousSlices`), hence its Neumann cosine coefficients lie in `H⁰`.

Uses ONLY `DB` mild data via `conjugateMildSolutionData_of_data` — no classical
regularity, no `localClassicalSolution`. -/
theorem conjugatePicardLimit_slice_memHSigma_zero
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (DB : ConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DB.T) :
    MemHSigma 0 (cosineCoeffs (conjugateSlice p u₀ DB.T t)) := by
  have hcont : Continuous ((conjugatePicardLimit p u₀ DB.T) t) :=
    (conjugateMildSolutionData_of_data DB).hcont t ht htT
  exact memHSigma_zero_of_continuousOn
    (intervalDomainLift_continuousOn_Icc_of_continuous hcont)

/-! ## Producer-chain steps 2–4 — the engine ladder `H⁰ → H¹` for the slice.

Given the engine's per-level step (`UniformBootstrapStep α`, the abstraction of
`gradientSolution_memHSigma_succ_wired` re-established at each running `σ`), the
H⁰ seed is promoted to `H¹` by iterating `n` times with `n·α ≥ 1`.  No Gronwall:
the engine constant is endpoint-uniform (`duhamelEnergy_mode_endpoint_uniform`),
so the same step applies at every level. -/

/-- **The keystone, closest provable form: `H¹` of the slice from the engine
step.**  With a `UniformBootstrapStep α` for the slice and `n` steps reaching
`0 + n·α ≥ 1`, the H⁰ seed iterates up to `MemHSigma 1`.

The hypothesis `S` is precisely the engine map the bootstrap module carries
uninstantiated; the proof is the audit's non-Gronwall ladder.  See the module
stall report for why `S` itself is not yet unconditionally constructible from
`DB` (the missing B-form→spectral kernel identity). -/
theorem conjugatePicardLimit_slice_memHSigma_one_of_step
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (DB : ConjugateMildExistenceData p u₀)
    {α : ℝ} {n : ℕ} (hreach : (1 : ℝ) ≤ n * α)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DB.T)
    (S : UniformBootstrapStep α (conjugateSlice p u₀ DB.T t)) :
    MemHSigma 1 (cosineCoeffs (conjugateSlice p u₀ DB.T t)) := by
  have h0 : MemHSigma 0 (cosineCoeffs (conjugateSlice p u₀ DB.T t)) :=
    conjugatePicardLimit_slice_memHSigma_zero p u₀ DB ht htT
  have hiter : MemHSigma (0 + n * α) (cosineCoeffs (conjugateSlice p u₀ DB.T t)) :=
    memHSigma_iterate (σ₀ := 0) (b := cosineCoeffs (conjugateSlice p u₀ DB.T t))
      S.step n h0
  rw [zero_add] at hiter
  exact memHSigma_antitone hreach hiter

/-! ## The audit-prescribed target, in its closest provable form.

The audit field `u_posTime_memHSigma_one_of_mild` asks for the UNCONDITIONAL
`MemHSigma 1` of every interior slice from `DB` alone.  As the module stall
report establishes, the engine `step` for the conjugate B-form slice is not yet
unconditionally constructible (one genuine missing per-mode kernel identity,
NON-circular).  The theorem below is therefore stated in the closest provable
form: it delivers EXACTLY the prescribed conclusion, parameterized by the engine
step `S t` whose unconditional producer is the named remaining gap.  Discharging
that producer (the B-form→spectral identity) instantiates `S` from `DB` and
yields the unconditional field verbatim. -/

/-- **`u_posTime_memHSigma_one_of_mild` (closest provable form).**  Positive-time
spatial `MemHSigma 1` regularity of the χ₀<0 mild slice, for every interior time,
once the engine step is supplied per slice.  The H⁰ seed and the H^σ ladder are
unconditional (proved above); the only carried input is the per-slice engine step
`S`, the audit's single remaining discharge. -/
theorem u_posTime_memHSigma_one_of_mild
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (DB : ConjugateMildExistenceData p u₀)
    {α : ℝ} {n : ℕ} (hreach : (1 : ℝ) ≤ n * α)
    (S : ∀ t, UniformBootstrapStep α (conjugateSlice p u₀ DB.T t)) :
    ∀ t, 0 < t → t ≤ DB.T →
      MemHSigma 1 (cosineCoeffs (conjugateSlice p u₀ DB.T t)) :=
  fun t ht htT =>
    conjugatePicardLimit_slice_memHSigma_one_of_step p u₀ DB hreach ht htT (S t)

#print axioms memHSigma_antitone
#print axioms conjugatePicardLimit_slice_memHSigma_zero
#print axioms conjugatePicardLimit_slice_memHSigma_one_of_step
#print axioms u_posTime_memHSigma_one_of_mild

end ShenWork.Paper2.IntervalMildPosTimeHSigma
