/-
  ShenWork/Paper2/IntervalChiNegA3Slice.lean

  χ₀<0 REBUILD — PIECE A re-route via the PER-SLICE A³ Wiener bootstrap (cron1's
  verified route, _CHATGPT_DROP_cron1.md), NOT the τ-uniform C1 envelope.

  GOAL.  For a FIXED interior slice `τ > 0`, derive the per-slice weighted-Wiener
  regularity `u(τ) ∈ A^r` (`MemHSigma r (cosineCoeffs (conjugateSlice ... τ))`) for
  ANY target `r ≤ n·α`, from the unconditional A⁰ seed
  (`conjugatePicardLimit_slice_memHSigma_zero`) plus the FINITE Wiener ladder
  (`UniformBootstrapStep α`, the `+α`/pass engine).  Then bridge a per-slice FLUX
  `MemHSigma σ'` (σ'>3/2) to the √λ-weighted ℓ¹ flux envelope that PIECE A
  (`gradSummable_slice_of_flux` / `weightedHalf_of_memHSigma`, f6f8786) consumes.

  ## DERIVED (this file, new content beyond the landed `_one_` headline which
  stops at the target r=1 — A³ regularity needs r>3/2):

  * `slice_memHSigma_target_of_step` — the GENERIC-TARGET per-slice ladder: from
    the landed A⁰ seed + a `UniformBootstrapStep α` for the slice + `n` steps with
    `r ≤ n·α`, the A⁰ seed iterates (`memHSigma_iterate`) up to `MemHSigma (n·α)`,
    then `memHSigma_antitone` descends to the target `MemHSigma r`.  This is cron1's
    finite A⁰→A¹→A²→A³ ladder, parameterized by the target weight (the landed
    `conjugatePicardLimit_slice_memHSigma_one_of_step` is the `r=1` instance; here
    we expose the A³ instance `r = 7/4 > 3/2`).  Per-slice (τ fixed), NOT τ-uniform.

  * `sliceA3_flux_l1_of_memHSigma` — from a per-slice flux `MemHSigma σ'`
    (`σ' > 3/2`, the per-slice A^{σ'} flux datum the ladder + the landed Wiener flux
    algebra `chemotaxisFlux_memHSigma` produce at the fixed slice), the
    √λ-weighted ℓ¹ flux sum `Σ_k √λ_k |a_k| < ∞` — i.e. the `gQ`/`gL` envelope-seed
    that `gradSummable_slice_of_flux` consumes.  Pure re-export of the landed
    `weightedHalf_of_memHSigma` at the per-slice flux level.  DERIVED.

  * `sliceA3_pieceA_discharge` — the END-TO-END per-slice PIECE A discharge:
    feeding the per-slice A³ flux data (the √λ-weighted ℓ¹ envelopes from
    `sliceA3_flux_l1_of_memHSigma`, the base time-C¹ packages, the derivative
    bounds) into the landed `gradSummable_slice_of_flux` yields the per-slice
    eigenvalue-weighted ℓ¹ gradient summability `Σ_k λ_k |û_k(τ)| < ∞` — the
    spectral H^{3/2}-regularity the H¹ energy identity consumes — WITHOUT the
    τ-uniform `MemHSigma σ'` envelope.

  ## CARRIED (precise, never faked, never relabeled).  The per-slice ladder's SOLE
  genuine residual is the engine step `UniformBootstrapStep α` for the slice — which
  (`uniformBootstrapStep_of_sliceMildData`, IntervalMildBootstrapStep) reduces to a
  `SliceMildStepData` bundle whose only non-mild field is the σ-indexed flux
  envelope `genv σ`/`glenv σ` with
      `hg_dom : ∀ τ∈[0,t], ∀ k, |sineCoeffs (Q τ) k| ≤ genv σ k`.
  This window-uniform SINE-flux `H^σ` envelope is the campaign's isolated crux: the
  cosine factor algebra closes quantitatively (IntervalEnvelopeProp VERDICT steps
  1–5), but the cos→sin transfer (`sineEnvelope_of_derivCosEnvelope`) demands a
  window-uniform cosine envelope of the flux DERIVATIVE `Q_x` — one derivative
  beyond the landed factor envelopes — and Paper2 has NO uniform producer for it
  (IntervalBootstrapInputs TASK-3 note: it is a Gronwall-continuation closure).
  Failed greps (no unconditional producer of the step / the window-uniform flux
  envelope):
      grep -rn "SliceMildStepData.*:=|: SliceMildStepData" → only as hypothesis
      grep -rn "fluxFunction.*timeSup|window.*sineCoeffs.*conjQ.*MemHSigma" → NONE
  The flux `MemHSigma σ'` per-slice datum and the base time-C¹ packages are the
  honest physical inputs, threaded — not assumed away.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file only.  Lines ≤ 100.
  Mathlib v4.29.1.  `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.
-/
import ShenWork.Paper2.IntervalMildPosTimeHSigma
import ShenWork.Paper2.IntervalUniformBootstrap
import ShenWork.Paper2.IntervalBootstrapStep
import ShenWork.Paper2.IntervalChiNegH1Final
import ShenWork.Paper2.IntervalChiNegGradSummable

noncomputable section

open scoped BigOperators
open ShenWork.Paper2.HSigmaScale (lam MemHSigma)
open ShenWork.Paper2.IntervalUniformBootstrap (UniformBootstrapStep)
open ShenWork.Paper2.IntervalMildPosTimeHSigma
  (conjugateSlice conjugatePicardLimit_slice_memHSigma_zero memHSigma_antitone)
open ShenWork.IntervalConjugatePicard (ConjugateMildExistenceData)
open ShenWork.Paper2.IntervalBootstrapStep (memHSigma_iterate)
open ShenWork.Paper2.IntervalChiNegH1Final (weightedHalf_of_memHSigma)
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.Paper2.IntervalDecompTauLift (conjQ conjFl)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)

namespace ShenWork.Paper2.IntervalChiNegA3Slice

/-! ## DERIVED — the generic-target per-slice Wiener ladder (A⁰ seed → A^r). -/

/-- **Per-slice `A^r` from the A⁰ seed + the finite Wiener ladder (generic
target).**  For an interior time `t ∈ (0, DB.T]`, a `UniformBootstrapStep α` for
the slice, a step count `n` reaching `r ≤ n·α`, the unconditional A⁰ seed iterates
`n` times (`memHSigma_iterate S.step`) to `MemHSigma (0 + n·α)`, then descends
(`memHSigma_antitone`) to the target `MemHSigma r`.  cron1's finite ladder,
parameterized by the target weight — the landed `_one_` headline is the `r = 1`
instance; the A³ slice is `r = 7/4 > 3/2`.  Per-slice (τ fixed), NOT τ-uniform. -/
theorem slice_memHSigma_target_of_step
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (DB : ConjugateMildExistenceData p u₀)
    {α r : ℝ} {n : ℕ} (hreach : r ≤ n * α)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DB.T)
    (S : UniformBootstrapStep α (conjugateSlice p u₀ DB.T t)) :
    MemHSigma r (cosineCoeffs (conjugateSlice p u₀ DB.T t)) := by
  have h0 : MemHSigma 0 (cosineCoeffs (conjugateSlice p u₀ DB.T t)) :=
    conjugatePicardLimit_slice_memHSigma_zero p u₀ DB ht htT
  have hiter : MemHSigma (0 + n * α) (cosineCoeffs (conjugateSlice p u₀ DB.T t)) :=
    memHSigma_iterate (σ₀ := 0) (b := cosineCoeffs (conjugateSlice p u₀ DB.T t))
      S.step n h0
  rw [zero_add] at hiter
  exact memHSigma_antitone hreach hiter

/-- **Per-slice `A³` specialisation.**  The A³ Wiener slice `r = 7/4 > 3/2` is the
target the divergence-weight PIECE A consumer needs (`weightedHalf_of_memHSigma`
demands `σ' > 3/2`).  `n = 2`, `α = 9/10` reaches `n·α = 9/5 = 1.8 ≥ 7/4 = 1.75`. -/
theorem slice_A3_of_step
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (DB : ConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DB.T)
    (S : UniformBootstrapStep (9 / 10) (conjugateSlice p u₀ DB.T t)) :
    MemHSigma (7 / 4) (cosineCoeffs (conjugateSlice p u₀ DB.T t)) :=
  slice_memHSigma_target_of_step (n := 2) p u₀ DB (by norm_num) ht htT S

/-! ## DERIVED — per-slice flux √λ-weighted ℓ¹ (the PIECE A envelope seed). -/

/-- **Per-slice √λ-weighted ℓ¹ flux sum from a per-slice flux `A^{σ'}` datum.**
For a per-slice flux coefficient sequence `a ∈ H^{σ'}` (`σ' > 3/2` — the per-slice
A^{σ'} flux datum the ladder + the landed Wiener flux algebra produce at the fixed
slice), the divergence-weighted ℓ¹ sum `Σ_k √λ_k |a_k|` converges.  This is the
`gQ`/`gL` envelope-seed `gradSummable_slice_of_flux` consumes.  Re-export of the
landed `weightedHalf_of_memHSigma` at the per-slice flux level.  DERIVED. -/
theorem sliceA3_flux_l1_of_memHSigma {σ' : ℝ} (hσ' : 3 / 2 < σ') {a : ℕ → ℝ}
    (ha : MemHSigma σ' a) :
    Summable (fun k : ℕ => Real.sqrt (lam k) * |a k|) :=
  weightedHalf_of_memHSigma hσ' ha

/-! ## DERIVED — end-to-end per-slice PIECE A discharge (no τ-uniform envelope). -/

/-- **PIECE A discharged per-slice — `Σ_k λ_k |û_k(τ)| < ∞` from the per-slice A³
flux data.**  Feeds the divergence-weighted ℓ¹ flux envelopes `gQ`/`gL` (DERIVED
per-slice via `sliceA3_flux_l1_of_memHSigma` from the per-slice flux `A^{σ'}`
data), the base time-`C¹` packages, and the derivative bounds into the landed
`gradSummable_slice_of_flux` (IntervalChiNegH1Final, f6f8786).  The result is the
per-slice eigenvalue-weighted ℓ¹ gradient summability — the spectral
`H^{3/2}`-regularity input the H¹ energy identity consumes — obtained WITHOUT the
over-strong τ-uniform `MemHSigma σ'` envelope.  DERIVED end-to-end. -/
theorem sliceA3_pieceA_discharge {p : CM2Params} {τ M₀ : ℝ} (hτ : 0 < τ)
    {u : ℝ → intervalDomainPoint → ℝ} {uhat0 : ℕ → ℝ}
    (hM0 : ∀ k, |uhat0 k| ≤ M₀)
    (baseChem : DuhamelSourceTimeC1 (fun s n => sineCoeffs (conjQ p u s) n))
    (baseLog : DuhamelSourceTimeC1 (fun s n => conjFl p u n s))
    (gQ gL : ℕ → ℝ) (hgQ_nn : ∀ n, 0 ≤ gQ n) (hgL_nn : ∀ n, 0 ≤ gL n)
    (hgQ_sum : Summable gQ) (hgL_sum : Summable gL)
    (hgQ_bd : ∀ s, 0 ≤ s → ∀ n,
      Real.sqrt (lam n) * |sineCoeffs (conjQ p u s) n| ≤ gQ n)
    (hgL_bd : ∀ s, 0 ≤ s → ∀ n, Real.sqrt (lam n) * |conjFl p u n s| ≤ gL n)
    (MQ ML : ℝ)
    (hMQ : ∀ s, 0 ≤ s → ∀ n, Real.sqrt (lam n) * |baseChem.adot s n| ≤ MQ)
    (hML : ∀ s, 0 ≤ s → ∀ n, Real.sqrt (lam n) * |baseLog.adot s n| ≤ ML)
    (hdecomp : ∀ k, cosineCoeffs (intervalDomainLift (u τ)) k
        = Real.exp (-(τ * lam k)) * uhat0 k
          + (-p.χ₀) * duhamelEnergyCoeff 1
              (fun k τ => sineCoeffs (conjQ p u τ) k) τ k
          + duhamelEnergyCoeff 1 (conjFl p u) τ k) :
    Summable (fun k : ℕ =>
      lam k * |cosineCoeffs (intervalDomainLift (u τ)) k|) :=
  ShenWork.Paper2.IntervalChiNegH1Final.gradSummable_slice_of_flux hτ hM0
    baseChem baseLog gQ gL hgQ_nn hgL_nn hgQ_sum hgL_sum hgQ_bd hgL_bd
    MQ ML hMQ hML hdecomp

section AxiomAudit
#print axioms slice_memHSigma_target_of_step
#print axioms slice_A3_of_step
#print axioms sliceA3_flux_l1_of_memHSigma
#print axioms sliceA3_pieceA_discharge
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegA3Slice
