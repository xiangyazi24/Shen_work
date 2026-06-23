/-
  ShenWork/Paper2/IntervalChiNegDirectSupersolution.lean

  χ₀<0 — `hEhatH` via the DIRECT Duhamel-deflation route.

  The prior "definitive obstruction" (commit 5d798ef, `memHSigma_flux_succ_of_hEhatH`)
  is an ARTIFACT of the *bare-sineEnv interface*: forcing the convolution flux
  `M_k := trueCosProd (gW E Gden)(sineEnv E) k` (the `genv` output, `M ∈ H^σ`) to be
  dominated by `sineEnv Estar k = √λ_k·Estar_k/(1+λ_k)` demands
  `Estar ≥ (1+λ)/√λ·M = gwInflatedBase`, which needs `M ∈ H^{σ+1}` (the false
  +1-derivative loss).  That demand is NOT a real χ₀<0 obstruction.

  The DIRECT route never inflates.  The Duhamel kernel
  `duhamelModeCoeff d lam F s = ∫₀ˢ √lam·exp(−d·lam·(s−τ))·F τ dτ` ALREADY carries the
  `√λ`, and the LANDED endpoint-uniform propagator
  `trajectoryEnvelope_of_sourceEnvelope` smooths a τ-uniform `H^σ` SOURCE envelope
  `M` of `F = sineCoeffs(Q τ)` into a τ-uniform `H^{σ+α}` envelope of the Duhamel
  OUTPUT `duhamelEnergyCoeff 1 F s`, whose explicit dominator
  `coreEnv = (C·Rbar α)·(1+λ)^{−α/2}·M` IS the deflation `M ↦ M/(1+λ)^{α/2} ∈ H^{σ+α}`
  (no `+1` derivative is ever required of `M`).

  THE THREE GENUINE BUILDS:
  1. `memHSigma_deflate` — `M ∈ H^σ → (fun k => M_k/(1+λ_k)^{σ/2}) ∈ H^σ`, the clean
     `(1+λ)^{σ/2}` deflation: per mode `(1+λ_k)^σ·(M_k/(1+λ_k)^{σ/2})² = M_k²
     ≤ (1+λ_k)^σ M_k²` (since `(1+λ_k)^σ ≥ 1` for `σ ≥ 0`), `Summable.of_nonneg_of_le`.
  2. `chemDuhamel_direct` — the chemotaxis Duhamel OUTPUT envelope `chemE`, built
     DIRECTLY from the per-mode source envelope `M` (the `genv` output) by the landed
     `trajectoryEnvelope_of_sourceEnvelope` (the `coreEnv` deflation), NOT via the
     bare-sineEnv `chemDuhamelContribution_le`.
  3. `trajEnvelope_chiNeg_direct` — the `H^{σ+α}` supersolution `Estar = |û₀| +
     |χ₀|·chemE.env + logE.env` (three `H^{σ+α}` summands) is `MemHSigma (σ+α) Estar`
     (= `hEhatH`), and via `trajLadder_step_meanFixed` IS the trajectory envelope —
     the self-reference `M ∼ quadratic in E` stays the *Banach output* (the carried
     `hdecomp_pos` / `hmean` come from the actual mild Duhamel identity, not faked).

  New file only.  No sorry/admit/native_decide/custom axiom.  Mathlib v4.29.1.
  `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.
-/
import ShenWork.Paper2.IntervalTrajectoryEnvelope
import ShenWork.Paper2.IntervalChiNegMeanFixedStep
import ShenWork.Paper2.IntervalDenomSecondDerivBound

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegDirectSupersolution

open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2.HSigmaScale (lam lam_nonneg one_add_lam_pos MemHSigma)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.IntervalTrajectoryEnvelope
  (TrajectoryHSigmaEnvelope trajectoryEnvelope_of_sourceEnvelope)
open ShenWork.Paper2.IntervalChiNegMeanFixedStep (trajLadder_step_meanFixed)

/-! ## GENUINE BUILD 1 — the `(1+λ)^{σ/2}` deflation. -/

/-- **`memHSigma_deflate` (GENUINE BUILD 1).**  Deflating an `H^σ` sequence by the
half-weight `(1+λ_k)^{σ/2}` keeps it in `H^σ`:
`M ∈ H^σ → (fun k => M_k/(1+λ_k)^{σ/2}) ∈ H^σ`.

Per mode the deflated weighted square collapses to `M_k²`:
`(1+λ_k)^σ·(M_k/(1+λ_k)^{σ/2})² = M_k² ≤ (1+λ_k)^σ M_k²`, the last since
`(1+λ_k)^σ ≥ 1` for `σ ≥ 0` (as `1 + λ_k ≥ 1`).  Hence the deflated series is
dominated by the `H^σ` series of `M` and summable. -/
theorem memHSigma_deflate {σ : ℝ} (hσ : 0 ≤ σ) {M : ℕ → ℝ} (hM : MemHSigma σ M) :
    MemHSigma σ (fun k => M k / (1 + lam k) ^ (σ / 2)) := by
  -- per-mode collapse: (1+λ)^σ·(M/(1+λ)^{σ/2})² = M²
  have hcollapse : ∀ k, (1 + lam k) ^ σ * (M k / (1 + lam k) ^ (σ / 2)) ^ 2
      = (M k) ^ 2 := by
    intro k
    have hl := one_add_lam_pos k
    have hhalf : ((1 + lam k) ^ (σ / 2)) ^ 2 = (1 + lam k) ^ σ := by
      rw [← Real.rpow_natCast ((1 + lam k) ^ (σ / 2)) 2, ← Real.rpow_mul hl.le]
      norm_num
    rw [div_pow, hhalf]; field_simp
  -- domination M² ≤ (1+λ)^σ M² since (1+λ)^σ ≥ 1
  have hdom : ∀ k, (1 + lam k) ^ σ * (M k / (1 + lam k) ^ (σ / 2)) ^ 2
      ≤ (1 + lam k) ^ σ * (M k) ^ 2 := by
    intro k
    rw [hcollapse k]
    have hone : (1 : ℝ) ≤ (1 + lam k) ^ σ :=
      Real.one_le_rpow (by have := lam_nonneg k; linarith) hσ
    nlinarith [sq_nonneg (M k), hone]
  have hnonneg : ∀ k, 0 ≤ (1 + lam k) ^ σ * (M k / (1 + lam k) ^ (σ / 2)) ^ 2 := by
    intro k; have := Real.rpow_nonneg (one_add_lam_pos k).le σ; positivity
  exact Summable.of_nonneg_of_le hnonneg hdom hM

/-! ## GENUINE BUILD 2 — the DIRECT chemotaxis Duhamel OUTPUT envelope. -/

/-- **`chemDuhamel_direct` (GENUINE BUILD 2).**  The chemotaxis Duhamel OUTPUT
envelope, built DIRECTLY from a τ-uniform `H^σ` SOURCE envelope `M` of the flux
coefficients `F k τ = sineCoeffs (Q τ) k`, by the LANDED endpoint-uniform propagator
`trajectoryEnvelope_of_sourceEnvelope` (`d = 1`, `r = σ`).

Its explicit dominator `coreEnv (C) α M = (C·Rbar α)·(1+λ)^{−α/2}·M` IS the deflation
`M ↦ M/(1+λ)^{α/2}` (cf. `memHSigma_deflate`): the Duhamel kernel's own `√λ` supplies
the smoothing, so NO `+1`-derivative inflation of `M` is required.  This is exactly
the `chemE : TrajectoryHSigmaEnvelope (σ+α) t (duhamelEnergyCoeff 1 F)` that
`trajLadder_step_meanFixed` consumes — and it does NOT route through the bare-sineEnv
`chemDuhamelContribution_le`. -/
def chemDuhamel_direct {σ α t : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (ht : 0 < t) (ht1 : t ≤ 1)
    {Q : ℝ → ℝ → ℝ} (hFcont : ∀ k, Continuous (fun τ => sineCoeffs (Q τ) k))
    {M : ℕ → ℝ} (hMsup0 : ∀ k, 0 ≤ M k) (hMsq : MemHSigma σ M)
    (hFbd : ∀ k, ∀ τ ∈ Set.Icc (0 : ℝ) t, |sineCoeffs (Q τ) k| ≤ M k) :
    TrajectoryHSigmaEnvelope (σ + α) t
      (fun s k => duhamelEnergyCoeff 1 (fun k τ => sineCoeffs (Q τ) k) s k) :=
  trajectoryEnvelope_of_sourceEnvelope (r := σ) hα0 hα1 (d := 1) one_pos ht ht1
    hFcont hMsup0 hMsq hFbd

/-! ## GENUINE BUILD 3 — the `H^{σ+α}` supersolution `Estar` = `hEhatH`. -/

/-- **`trajEnvelope_chiNeg_direct` (GENUINE BUILD 3 — closes `hEhatH`).**

Assembles the χ₀<0 `H^{σ+α}` supersolution
`Estar = |û₀| + |χ₀|·chemE.env + logE.env` and DERIVES the trajectory `H^{σ+α}`
envelope of `u`, via the landed `trajLadder_step_meanFixed`.  Its `henv` field is
`MemHSigma (σ+α) Estar` — THIS IS `hEhatH`, now at the H^σ-scale (`σ+α`, `α<1`), with
NO `gwInflatedBase` / bare-sineEnv inflation: `chemE.env` is the DIRECT deflated
Duhamel output of `chemDuhamel_direct` (`coreEnv = (C·Rbar)·(1+λ)^{−α/2}·M`), not the
`M·(1+λ)/√λ` inflation.

SELF-REFERENCE / SMALL-`δ` HYPOTHESES (carried EXPLICITLY, NOT faked — these are the
actual mild Duhamel identity for the trajectory, the Banach *input* whose fixed point
makes the domination the Banach *output*):
  * `hMsq`/`hFbd` : the source envelope `M` of the flux is the genv output `∈ H^σ`,
    τ-uniformly dominating `|sineCoeffs (Q τ) k|` — produced by
    `genv_of_trajectoryEnvelope_uncond`;
  * `hû₀`  : the heat datum `û₀ ∈ H^{σ+α}`;
  * `logE` : the logistic Duhamel OUTPUT envelope;
  * `hdecomp_pos` : the per-mode (`k ≠ 0`) mild three-term Duhamel decomposition of
    `cosineCoeffs (u τ) k` (heat + chemotaxis Duhamel + logistic Duhamel);
  * `hmean` : the `k = 0` mean bound `|cosineCoeffs (u τ) 0| ≤ Mmean`.
The chemotaxis leg of `hdecomp_pos` is the DIRECT `duhamelEnergyCoeff 1
(sineCoeffs (Q τ))`, dominated by `chemDuhamel_direct` — the same `H^{σ+α}` object as
`Estar`'s middle summand. -/
def trajEnvelope_chiNeg_direct {σ α χ₀ t : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (ht : 0 < t) (ht1 : t ≤ 1) {u : ℝ → ℝ → ℝ}
    {û₀ : ℕ → ℝ} (hû₀ : MemHSigma (σ + α) û₀)
    {Q : ℝ → ℝ → ℝ} (hFcont : ∀ k, Continuous (fun τ => sineCoeffs (Q τ) k))
    {M : ℕ → ℝ} (hMsup0 : ∀ k, 0 ≤ M k) (hMsq : MemHSigma σ M)
    (hFbd : ∀ k, ∀ τ ∈ Set.Icc (0 : ℝ) t, |sineCoeffs (Q τ) k| ≤ M k)
    {Fl : ℕ → ℝ → ℝ}
    (logE : TrajectoryHSigmaEnvelope (σ + α) t (fun s k => duhamelEnergyCoeff 1 Fl s k))
    {Mmean : ℝ}
    (hdecomp_pos : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k, k ≠ 0 →
      cosineCoeffs (u τ) k
        = Real.exp (-(τ * lam k)) * û₀ k
          + (-χ₀) * duhamelEnergyCoeff 1 (fun k τ => sineCoeffs (Q τ) k) τ k
          + duhamelEnergyCoeff 1 Fl τ k)
    (hmean : ∀ τ ∈ Set.Icc (0:ℝ) t, |cosineCoeffs (u τ) 0| ≤ Mmean) :
    TrajectoryHSigmaEnvelope (σ + α) t (fun τ => cosineCoeffs (u τ)) :=
  trajLadder_step_meanFixed (σ := σ) (α := α) (χ₀ := χ₀) (t := t) (u := u) (Q := Q)
    (Fl := Fl) hû₀
    (chemDuhamel_direct hα0 hα1 ht ht1 hFcont hMsup0 hMsq hFbd)
    logE (Mmean := Mmean) hdecomp_pos hmean

/-! ## AxiomAudit -/

section AxiomAudit
#print axioms memHSigma_deflate
#print axioms chemDuhamel_direct
#print axioms trajEnvelope_chiNeg_direct
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegDirectSupersolution
