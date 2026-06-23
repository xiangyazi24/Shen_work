/-
  ShenWork/Paper2/IntervalChiNegHenvEnvBall.lean

  **χ₀<0 crux A — the candidate-generic chemotaxis-flux envelope, DIRECT-route.**

  The campaign's last named obligation was `trajSeam_henv_of_envBall`: for a generic
  candidate `U ∈ EnvBallTraj E_base`, bound the chemotaxis flux against the
  supersolution-compatible envelope, DERIVED from `U ∈ EnvBall` (non-circular).

  TWO-WAY AUDIT — the bare-sineEnv `henv` is GENUINELY UNPROVABLE, NOT a real gap.
  The `TrajSeam.henv` field (IntervalChiNegMapsTo) is RIGIDLY bare-`sineEnv`-typed:
    `|sineCoeffs (chemFluxLifted p (trajFun U r)) k| ≤ sineEnv E_base k`.
  But the LANDED candidate-generic producer `genv_of_traj_denom`
  (IntervalGWProductEnvelope:218) gives the flux bound only against the gW-INFLATED
  `trueCosProd (gW E_base D.Gden) (sineEnv E_base)` — a DOUBLE Wiener convolution,
  NOT pointwise ≤ `sineEnv E_base` (`gW = trueCosProd E_base Gden` is a full
  convolution, not ≤ a delta).  Forcing the bare bound demands
  `E_base ≥ (1+λ)/√λ · M = gwInflatedBase ∈ H^{σ+1}` — the PROVEN +1-derivative loss
  (DirectSupersolution header).  So bare-sineEnv `trajSeam_henv_of_envBall` is a dead
  interface; the χ₀<0 base is closed by the DIRECT route instead.

  WHAT THIS FILE BUILDS — the direct-route candidate-generic flux envelope.
  `chemDuhamelOutput_le_of_envBall` DERIVES, from `U ∈ EnvBallTraj E_base` + the
  per-candidate resolver structure (the SAME u-specific PDE residuals the landed
  chain carries), the DEFLATED chemotaxis-Duhamel OUTPUT bound
    `|duhamelEnergyCoeff 1 (sineCoeffs ∘ chemFluxLifted p (lift (trajFun U ·))) ρ k|
        ≤ chemEenv k`,
  i.e. the `Hchem_direct` / `TrajSeamDirect.hchemD` field — via `genv_of_traj_denom`
  (candidate-generic source `M`, with `heU` SUPPLIED by `U ∈ EnvBall`, NOT global-
  keyed) ⟹ `chemDuhamel_direct` (the `coreEnv = (C·Rbar)·(1+λ)^{−α/2}·M` deflation,
  NO bare sineEnv, NO `+1` loss).  This is the cron1 invariant-envelope proof: the
  candidate's coefficients ≤ `E_base` BY CONSTRUCTION ⟹ its flux factors ≤
  `E_base`-derived envelopes ⟹ the deflated Duhamel output bound.

  ACCOUNTING.  DERIVED: the chem-Duhamel OUTPUT envelope is the genuine analytic
  content, derived non-circularly (the slice envelope `heU` from `U ∈ EnvBall`, the
  inflation absorbed by `chemDuhamel_direct`, never against bare sineEnv).  CARRIED:
  the per-candidate resolver structure (`D`/`hQ`/`hWdef`/`hbr`/`hbridge`/`hvrel`/
  `hdiv`/`hFcont`) — the u-specific divergence/resolver PDE residuals, identical to
  the landed `genv_of_traj_denom` interface, threaded as explicit hyps (never faked).

  New file only.  No sorry/admit/native_decide/custom axiom.  Lines ≤ 100.
  Mathlib v4.29.1.  `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.
-/
import ShenWork.Paper2.IntervalGWProductEnvelope
import ShenWork.Paper2.IntervalChiNegDirectSupersolution
import ShenWork.Paper2.IntervalChiNegTrajBanach

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegHenvEnvBall

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)
open ShenWork.Paper2.HSigmaScale (lam MemHSigma resolverCoeff)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.IntervalEnvelopeProp (Envelopes)
open ShenWork.Paper2.IntervalGWProductEnvelope
  (DenomUniformEnvelope gW genv_of_traj_denom)
open ShenWork.Paper2.IntervalWienerAlgebra (trueCosProd)
open ShenWork.Paper2.IntervalFluxFactorEnvelope (sineEnv)
open ShenWork.Paper2.IntervalChiNegDirectSupersolution (chemDuhamel_direct)
open ShenWork.Paper2.IntervalChiNegTrajBanach (Traj trajFun EnvBallTraj)
open ShenWork.Paper2.IntervalWienerAlgebra (CosineMulBridge)
open ShenWork.Paper2.IntervalMixedProduct (MixedMulBridge)

/-! ## The candidate slice envelope from `U ∈ EnvBall` (non-circular). -/

/-- `U ∈ EnvBallTraj E_base` gives, per slice `τ ∈ [0,t]`, the candidate-generic
cosine envelope `Envelopes E_base (cosineCoeffs (lift (trajFun U τ)))` — the
`heU` input of `genv_of_traj_denom`, NOT keyed to the global solution. -/
theorem envelopes_of_envBall {t : ℝ} {E_base : ℕ → ℝ} {U : Traj t}
    (hU : U ∈ EnvBallTraj (t := t) E_base) :
    ∀ τ ∈ Set.Icc (0 : ℝ) t,
      Envelopes E_base (cosineCoeffs (intervalDomainLift (trajFun U τ))) :=
  fun τ hτ k => hU ⟨τ, hτ⟩ k

/-! ## The DIRECT candidate-generic chem-flux Duhamel envelope. -/

/-- **`chemDuhamelOutput_le_of_envBall` — DIRECT-route `trajSeam_henv_of_envBall`.**

From `U ∈ EnvBallTraj E_base` (whose slices give `heU` — non-circular, via
`envelopes_of_envBall`) and the candidate resolver structure, `genv_of_traj_denom`
produces the candidate-generic source envelope
`M := trueCosProd (gW E_base D.Gden) (sineEnv E_base) ∈ H^σ`, τ-uniformly dominating
`|sineCoeffs (chemFluxLifted p (lift (trajFun U τ))) k|`.  `chemDuhamel_direct` then
DEFLATES it to the chem-Duhamel OUTPUT envelope `chemE.env`
(`coreEnv = (C·Rbar)·(1+λ)^{−α/2}·M`), bounding the OUTPUT coefficient — the
`Hchem_direct` / `TrajSeamDirect.hchemD` field — NO bare sineEnv, NO `+1` loss. -/
theorem chemDuhamelOutput_le_of_envBall {σ α t : ℝ} (hσ : 1 / 2 < σ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (ht : 0 < t) (ht1 : t ≤ 1)
    {E_base : ℕ → ℝ} (hE : MemHSigma σ E_base) {U : Traj t}
    (hU : U ∈ EnvBallTraj (t := t) E_base) (p : CM2Params)
    {W vx v w₂ : ℝ → ℝ → ℝ} (D : DenomUniformEnvelope σ t w₂)
    (hFcont : ∀ k, Continuous
      (fun τ => sineCoeffs (chemFluxLifted p (trajFun U τ)) k))
    (hQ : ∀ τ, chemFluxLifted p (trajFun U τ) = fun x => W τ x * vx τ x)
    (hWdef : ∀ τ, W τ = fun x => intervalDomainLift (trajFun U τ) x * w₂ τ x)
    (hbr : ∀ τ ∈ Set.Icc (0 : ℝ) t,
      CosineMulBridge (intervalDomainLift (trajFun U τ)) (w₂ τ))
    (hbridge : ∀ τ ∈ Set.Icc (0 : ℝ) t, MixedMulBridge (W τ) (vx τ))
    (hvrel : ∀ τ ∈ Set.Icc (0 : ℝ) t,
      Envelopes (resolverCoeff 1 E_base) (cosineCoeffs (v τ)))
    (hdiv : ∀ τ ∈ Set.Icc (0 : ℝ) t, ∀ k,
      |sineCoeffs (vx τ) k| = Real.sqrt (lam k) * |cosineCoeffs (v τ) k|) :
    ∃ chemEenv : ℕ → ℝ, MemHSigma (σ + α) chemEenv ∧
      ∀ ρ ∈ Set.Icc (0 : ℝ) t, ∀ k,
        |duhamelEnergyCoeff 1 (fun k τ =>
            sineCoeffs (chemFluxLifted p (trajFun U τ)) k) ρ k|
          ≤ chemEenv k := by
  -- candidate-generic source envelope M (heU SUPPLIED by U ∈ EnvBall — non-circular)
  obtain ⟨hMmem, hMdom⟩ := genv_of_traj_denom (Q := fun τ =>
      chemFluxLifted p (trajFun U τ)) (W := W) (vx := vx)
      (u := fun τ => intervalDomainLift (trajFun U τ)) (v := v) (w₂ := w₂)
      hσ hE D hQ hWdef hbr (envelopes_of_envBall hU) hbridge hvrel hdiv
  set M := trueCosProd (gW E_base D.Gden) (sineEnv E_base) with hMdef
  have hMnn : ∀ k, 0 ≤ M k := fun k =>
    le_trans (abs_nonneg _) (hMdom 0 ⟨le_refl 0, ht.le⟩ k)
  -- deflate to the chem-Duhamel OUTPUT envelope via chemDuhamel_direct
  let chemE := chemDuhamel_direct (σ := σ) (α := α) hα0 hα1 ht ht1
    (Q := fun τ => chemFluxLifted p (trajFun U τ))
    hFcont (M := M) hMnn hMmem
    (fun k τ hτ => hMdom τ hτ k)
  exact ⟨chemE.env, chemE.henv, fun ρ hρ k => chemE.hdom ρ hρ k⟩

/-! ## AxiomAudit -/

section AxiomAudit
#print axioms envelopes_of_envBall
#print axioms chemDuhamelOutput_le_of_envBall
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegHenvEnvBall
