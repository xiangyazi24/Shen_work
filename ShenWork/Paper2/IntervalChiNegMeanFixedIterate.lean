/-
  ShenWork/Paper2/IntervalChiNegMeanFixedIterate.lean

  χ₀<0 — the MEAN-FIXED σ-ladder ITERATE and the H¹ REACH, bypassing the
  GENERICALLY-FALSE `k = 0` mean-conservation row.

  `MeanStepBundle` carries every analytic field of the landed `TrajStepBridges`
  EXCEPT the unsatisfiable `hdecomp` (whose `k = 0` row is mean-conservation,
  generically false under the logistic reaction).  In its place it carries the
  SOUND `hdecomp_pos` (`k ≠ 0` rows only — the landed
  `conjugateSlice_decomp_tauLift_pos` carries `hk : k ≠ 0`) and the DIRECT mean
  bound `hmean` (`|cosineCoeffs (u τ) 0| ≤ Mmean`).  `hdecomp_pos`/`hmean` are
  σ-INDEPENDENT (they concern `u`/`û₀`/`Q`/`Fl` only), so one pair drives every
  ladder level.

  The mean-fixed step produces the flux/logistic OUTPUT envelopes exactly as
  `TrajStepBridges.step` does (`genv_of_trajectoryEnvelope_uncond` + the propagator
  `trajectoryEnvelope_of_sourceEnvelope`), then runs `trajLadder_step_meanFixed`.
  Iterating it `n` times from a base envelope and antitone-collapsing to level `1`
  yields `TrajectoryHSigmaEnvelope 1` for `u` — with the `k = 0` mean handled by the
  direct bound, NOT by the false `hzero`.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file only.
-/
import ShenWork.Paper2.IntervalChiNegMeanFixedStep
import ShenWork.Paper2.IntervalChiNegTrajectoryAssembly

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegMeanFixedIterate

open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2.HSigmaScale (lam MemHSigma resolverCoeff)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.Paper2.IntervalEnvelopeProp (Envelopes)
open ShenWork.Paper2.IntervalDenomEnvelopeResolver (resolverValue)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.IntervalTrajectoryEnvelope
  (TrajectoryHSigmaEnvelope trajectoryEnvelope_of_sourceEnvelope)
open ShenWork.Paper2.IntervalDenomSecondDerivBound (genv_of_trajectoryEnvelope_uncond)
open ShenWork.Paper2.IntervalMildPosTimeHSigma (memHSigma_antitone)
open ShenWork.Paper2.IntervalChiNegMeanFixedStep (trajLadder_step_meanFixed)

/-- The mean-fixed analytic bundle: every `TrajStepBridges` field except the false
`hdecomp`, plus the SOUND `hdecomp_pos` (`k ≠ 0`) and the DIRECT mean bound
`hmean`. -/
structure MeanStepBundle (μ σ β χ₀ t : ℝ)
    (u v : ℝ → ℝ → ℝ) (û₀ : ℕ → ℝ) (Q W vx : ℝ → ℝ → ℝ) (Fl : ℕ → ℝ → ℝ)
    (Mmean : ℝ)
    (E : TrajectoryHSigmaEnvelope σ t (fun τ => cosineCoeffs (u τ))) where
  hμ : 0 < μ
  hσ0 : 1 / 2 < σ
  hσ1 : σ < 3 / 2
  hβ : 0 ≤ β
  ht : 0 < t
  ht1 : t ≤ 1
  hû₀ : MemHSigma (σ + 1 / 4) û₀
  hvnn : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ x, 0 ≤ resolverValue μ (cosineCoeffs (u τ)) x
  hQ : ∀ τ, Q τ = fun x => W τ x * vx τ x
  hWdef : ∀ τ, W τ = fun x => u τ x
    * (1 + resolverValue μ (cosineCoeffs (u τ)) x) ^ (-β)
  hbr : ∀ τ ∈ Set.Icc (0:ℝ) t,
    ShenWork.Paper2.IntervalWienerAlgebra.CosineMulBridge (u τ)
      (fun x => (1 + resolverValue μ (cosineCoeffs (u τ)) x) ^ (-β))
  hbridge : ∀ τ ∈ Set.Icc (0:ℝ) t,
    ShenWork.Paper2.IntervalMixedProduct.MixedMulBridge (W τ) (vx τ)
  hvrel : ∀ τ ∈ Set.Icc (0:ℝ) t,
    Envelopes (resolverCoeff 1 E.env) (cosineCoeffs (v τ))
  hdiv : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k,
    |sineCoeffs (vx τ) k| = Real.sqrt (lam k) * |cosineCoeffs (v τ) k|
  hQ_cont : ∀ k, Continuous (fun τ => sineCoeffs (Q τ) k)
  L : TrajectoryHSigmaEnvelope σ t (fun τ k => Fl k τ)
  hFl_cont : ∀ k, Continuous (Fl k)
  hdecomp_pos : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k, k ≠ 0 →
    cosineCoeffs (u τ) k
      = Real.exp (-(τ * lam k)) * û₀ k
        + (-χ₀) * duhamelEnergyCoeff 1 (fun k τ => sineCoeffs (Q τ) k) τ k
        + duhamelEnergyCoeff 1 Fl τ k
  hmean : ∀ τ ∈ Set.Icc (0:ℝ) t, |cosineCoeffs (u τ) 0| ≤ Mmean

namespace MeanStepBundle

variable {μ σ β χ₀ t : ℝ} {u v : ℝ → ℝ → ℝ} {û₀ : ℕ → ℝ}
variable {Q W vx : ℝ → ℝ → ℝ} {Fl : ℕ → ℝ → ℝ} {Mmean : ℝ}
variable {E : TrajectoryHSigmaEnvelope σ t (fun τ => cosineCoeffs (u τ))}

/-- The flux SINE envelope `gQ` (same object as `TrajStepBridges.gQ`). -/
def gQ (B : MeanStepBundle μ σ β χ₀ t u v û₀ Q W vx Fl Mmean E) : ℕ → ℝ :=
  ShenWork.Paper2.IntervalWienerAlgebra.trueCosProd
    (ShenWork.Paper2.IntervalGWProductEnvelope.gW E.env
      (ShenWork.Paper2.IntervalDenomSecondDerivBound.denomUniformEnvelope_of_trajectoryEnvelope
        B.hμ B.hσ0 B.hσ1 B.hβ E B.hvnn).Gden)
    (ShenWork.Paper2.IntervalFluxFactorEnvelope.sineEnv E.env)

theorem gQ_spec (B : MeanStepBundle μ σ β χ₀ t u v û₀ Q W vx Fl Mmean E) :
    MemHSigma σ B.gQ ∧
      ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k, |sineCoeffs (Q τ) k| ≤ B.gQ k :=
  genv_of_trajectoryEnvelope_uncond B.hμ B.hσ0 B.hσ1 B.hβ E B.hvnn B.hQ B.hWdef
    B.hbr (fun τ hτ k => E.hdom τ hτ k) B.hbridge B.hvrel B.hdiv

theorem gQ_nonneg (B : MeanStepBundle μ σ β χ₀ t u v û₀ Q W vx Fl Mmean E) (k : ℕ) :
    0 ≤ B.gQ k := le_trans (abs_nonneg _) ((B.gQ_spec).2 0 ⟨le_refl 0, B.ht.le⟩ k)

/-- **THE MEAN-FIXED σ-STEP — `H^σ → H^{σ+1/4}` envelope of `u`.**  Builds the
flux/logistic OUTPUT envelopes as `TrajStepBridges.step` does, then closes via
`trajLadder_step_meanFixed` (k=0 by the direct mean bound, k≠0 by `hdecomp_pos`). -/
def step (B : MeanStepBundle μ σ β χ₀ t u v û₀ Q W vx Fl Mmean E) :
    TrajectoryHSigmaEnvelope (σ + 1 / 4) t (fun τ => cosineCoeffs (u τ)) :=
  trajLadder_step_meanFixed (σ := σ) (α := 1/4) (χ₀ := χ₀) (Q := Q) (Fl := Fl)
    B.hû₀
    (trajectoryEnvelope_of_sourceEnvelope (r := σ) (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num) (d := 1) one_pos
      B.ht B.ht1 (F := fun k τ => sineCoeffs (Q τ) k) B.hQ_cont (Msup := B.gQ)
      B.gQ_nonneg (B.gQ_spec).1 (fun k τ hτ => (B.gQ_spec).2 τ hτ k))
    (trajectoryEnvelope_of_sourceEnvelope (r := σ) (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num) (d := 1) one_pos
      B.ht B.ht1 (F := Fl) B.hFl_cont (Msup := B.L.env)
      (fun k => B.L.env_nonneg ⟨le_refl 0, B.ht.le⟩ k) B.L.henv
      (fun k τ hτ => B.L.hdom τ hτ k))
    B.hdecomp_pos B.hmean

end MeanStepBundle

/-- A σ-indexed mean-fixed bundle family. -/
abbrev MeanBundleFamily (μ β χ₀ t : ℝ) (u v : ℝ → ℝ → ℝ) (û₀ : ℕ → ℝ)
    (Q W vx : ℝ → ℝ → ℝ) (Fl : ℕ → ℝ → ℝ) (Mmean : ℝ) : Type :=
  ∀ σ : ℝ, ∀ E : TrajectoryHSigmaEnvelope σ t (fun τ => cosineCoeffs (u τ)),
    MeanStepBundle μ σ β χ₀ t u v û₀ Q W vx Fl Mmean E

/-- **THE MEAN-FIXED ITERATE.**  `n` applications of the mean-fixed σ-step. -/
def meanStep_iterate {μ β χ₀ t : ℝ} {u v : ℝ → ℝ → ℝ} {û₀ : ℕ → ℝ}
    {Q W vx : ℝ → ℝ → ℝ} {Fl : ℕ → ℝ → ℝ} {Mmean : ℝ}
    (Bf : MeanBundleFamily μ β χ₀ t u v û₀ Q W vx Fl Mmean) :
    ∀ (n : ℕ) {σ₀ : ℝ}
      (E₀ : TrajectoryHSigmaEnvelope σ₀ t (fun τ => cosineCoeffs (u τ))),
      TrajectoryHSigmaEnvelope (σ₀ + n * (1 / 4)) t (fun τ => cosineCoeffs (u τ))
  | 0, σ₀, E₀ => by simpa using E₀
  | n + 1, σ₀, E₀ => by
      have hnext := (Bf σ₀ E₀).step
      have hrec := meanStep_iterate Bf n hnext
      have hcong : σ₀ + 1 / 4 + (n : ℝ) * (1 / 4) = σ₀ + ((n : ℝ) + 1) * (1 / 4) := by ring
      rw [hcong] at hrec
      have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [hcast] at hrec
      exact hrec

/-- **REACH `H¹` (mean-fixed).**  From a base envelope at `σ₀` and the mean-fixed
family, with `n` steps overshooting `1`, reach `TrajectoryHSigmaEnvelope 1` of `u`
— the `k = 0` mean handled by the DIRECT bound, never by the false `hzero`. -/
def meanReach_H1_of_base {μ β χ₀ t : ℝ} {u v : ℝ → ℝ → ℝ} {û₀ : ℕ → ℝ}
    {Q W vx : ℝ → ℝ → ℝ} {Fl : ℕ → ℝ → ℝ} {Mmean : ℝ} {σ₀ : ℝ} (n : ℕ)
    (hreach : (1 : ℝ) ≤ σ₀ + n * (1 / 4))
    (E₀ : TrajectoryHSigmaEnvelope σ₀ t (fun τ => cosineCoeffs (u τ)))
    (Bf : MeanBundleFamily μ β χ₀ t u v û₀ Q W vx Fl Mmean) :
    TrajectoryHSigmaEnvelope 1 t (fun τ => cosineCoeffs (u τ)) where
  env := (meanStep_iterate Bf n E₀).env
  henv := memHSigma_antitone hreach (meanStep_iterate Bf n E₀).henv
  hdom := (meanStep_iterate Bf n E₀).hdom

end ShenWork.Paper2.IntervalChiNegMeanFixedIterate

namespace ShenWork.Paper2.IntervalChiNegMeanFixedIterate
#print axioms MeanStepBundle.step
#print axioms meanStep_iterate
#print axioms meanReach_H1_of_base
end ShenWork.Paper2.IntervalChiNegMeanFixedIterate
