/-
  ShenWork/Paper2/IntervalChiNegMeanFixedStep.lean

  χ₀<0 — the MEAN-FIXED σ-ladder step, bypassing the GENERICALLY-FALSE `k = 0`
  decomposition row (`hzero`/mean-conservation) used by `trajLadder_step`.

  ## THE FALSE FIELD AND THE SOUND FIX

  The landed `TrajLadderData.trajLadder_step` proves its `hdom` at EVERY mode `k`
  by rewriting `cosineCoeffs (u τ) k` with the 3-term decomposition `D.hdecomp τ
  hτ k`.  At `k = 0` BOTH Duhamel legs vanish (`√λ₀ = 0`), so that row is the
  mean-conservation identity `cosineCoeffs (u τ) 0 = û₀ 0`, which the logistic
  reaction does NOT satisfy (the mean EVOLVES).  Hence the `k = 0` row is FALSE in
  general and the whole `TrajLadderData.hdecomp` field is unsatisfiable.

  This file reproduces the step from the OUTPUT envelopes directly, WITHOUT a
  `TrajLadderData` (hence without its false `hdecomp` field):
  * the `k ≠ 0` rows use the SOUND decomposition `hdecomp_pos` (the landed
    `conjugateSlice_decomp_tauLift_pos` carries `hk : k ≠ 0`);
  * the `k = 0` mode is discharged by the DIRECT mean bound `hmean`
    (`|cosineCoeffs (u τ) 0| ≤ Mmean`, from the mild solution's uniform L∞ ball via
    `cosineCoeffs_zero_abs_le_of_bound`) — NOT by mean-conservation.

  The output envelope is `|û₀| + |χ₀|·chemEnv + logEnv` patched at coordinate `0`
  to its max with `Mmean`; a single-coordinate change preserves `H^{σ+α}`
  (`Summable.update`).  No `sorry`/`admit`/`native_decide`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalTrajectoryEnvelopeClosure

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegMeanFixedStep

open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2.HSigmaScale (lam lam_nonneg MemHSigma)
open ShenWork.Paper2.IntervalWienerAlgebra (memHSigma_add memHSigma_smul)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.IntervalTrajectoryEnvelope (TrajectoryHSigmaEnvelope)

variable {σ α χ₀ t : ℝ} {u : ℝ → ℝ → ℝ} {û₀ : ℕ → ℝ} {Q : ℝ → ℝ → ℝ} {Fl : ℕ → ℝ → ℝ}

/-- A single-coordinate change preserves `MemHSigma`. -/
theorem memHSigma_update {ρ : ℝ} {a : ℕ → ℝ} (ha : MemHSigma ρ a) (i : ℕ) (c : ℝ) :
    MemHSigma ρ (Function.update a i c) := by
  have h := (Summable.update (f := fun k => (1 + lam k) ^ ρ * (a k) ^ 2)
    ha i ((1 + lam i) ^ ρ * c ^ 2))
  refine h.congr (fun k => ?_)
  by_cases hk : k = i
  · subst hk; simp [Function.update_self]
  · simp [Function.update_of_ne hk]

/-- The summed `H^{σ+α}` envelope sequence (mirrors `TrajLadderData.ladderEnv`). -/
def meanLadderEnv (û₀ : ℕ → ℝ) (χ₀ : ℝ) (chemEnv logEnv : ℕ → ℝ) (k : ℕ) : ℝ :=
  |û₀ k| + (|χ₀| * chemEnv k + logEnv k)

/-- **THE MEAN-FIXED σ-LADDER STEP.**  From the heat datum `hû₀`, the chemotaxis-
and logistic-Duhamel OUTPUT envelopes (`chemE`, `logE`), the SOUND `k ≠ 0`
decomposition `hdecomp_pos`, and the DIRECT mean bound `hmean`, produces a
τ-uniform `H^{σ+α}` envelope of `u`.  Carries NO false `hzero`/mean-conservation
premise — the `k = 0` mode is bounded by `Mmean`, the high modes by the propagator
outputs. -/
def trajLadder_step_meanFixed
    (hû₀ : MemHSigma (σ + α) û₀)
    (chemE : TrajectoryHSigmaEnvelope (σ + α) t
      (fun s k => duhamelEnergyCoeff 1 (fun k τ => sineCoeffs (Q τ) k) s k))
    (logE : TrajectoryHSigmaEnvelope (σ + α) t (fun s k => duhamelEnergyCoeff 1 Fl s k))
    {Mmean : ℝ}
    (hdecomp_pos : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k, k ≠ 0 →
      cosineCoeffs (u τ) k
        = Real.exp (-(τ * lam k)) * û₀ k
          + (-χ₀) * duhamelEnergyCoeff 1 (fun k τ => sineCoeffs (Q τ) k) τ k
          + duhamelEnergyCoeff 1 Fl τ k)
    (hmean : ∀ τ ∈ Set.Icc (0:ℝ) t, |cosineCoeffs (u τ) 0| ≤ Mmean) :
    TrajectoryHSigmaEnvelope (σ + α) t (fun τ => cosineCoeffs (u τ)) where
  env := Function.update (meanLadderEnv û₀ χ₀ chemE.env logE.env) 0
    (max (meanLadderEnv û₀ χ₀ chemE.env logE.env 0) Mmean)
  henv := by
    have habs : MemHSigma (σ + α) (fun k => |û₀ k|) := by
      unfold MemHSigma
      refine hû₀.congr (fun k => ?_); rw [sq_abs]
    have hbase : MemHSigma (σ + α) (meanLadderEnv û₀ χ₀ chemE.env logE.env) :=
      memHSigma_add habs (memHSigma_add (memHSigma_smul |χ₀| chemE.henv) logE.henv)
    exact memHSigma_update hbase 0 _
  hdom := by
    intro τ hτ k
    by_cases hk : k = 0
    · subst hk
      rw [Function.update_self]
      exact le_trans (hmean τ hτ) (le_max_right _ _)
    · rw [Function.update_of_ne hk]
      have hdec := hdecomp_pos τ hτ k hk
      have hτ0 : (0:ℝ) ≤ τ := hτ.1
      have hexp1 : Real.exp (-(τ * lam k)) ≤ 1 := by
        apply Real.exp_le_one_iff.2
        have : 0 ≤ τ * lam k := mul_nonneg hτ0 (lam_nonneg k)
        linarith
      have hexp0 : 0 ≤ Real.exp (-(τ * lam k)) := (Real.exp_pos _).le
      have hheat : |Real.exp (-(τ * lam k)) * û₀ k| ≤ |û₀ k| := by
        rw [abs_mul, abs_of_nonneg hexp0]
        calc Real.exp (-(τ * lam k)) * |û₀ k| ≤ 1 * |û₀ k| :=
              mul_le_mul_of_nonneg_right hexp1 (abs_nonneg _)
          _ = |û₀ k| := one_mul _
      have hchem : |(-χ₀) * duhamelEnergyCoeff 1 (fun k τ => sineCoeffs (Q τ) k) τ k|
          ≤ |χ₀| * chemE.env k := by
        rw [abs_mul, abs_neg]
        exact mul_le_mul_of_nonneg_left (chemE.hdom τ hτ k) (abs_nonneg _)
      have hlog : |duhamelEnergyCoeff 1 Fl τ k| ≤ logE.env k := logE.hdom τ hτ k
      set H := Real.exp (-(τ * lam k)) * û₀ k with hH
      set Ch := (-χ₀) * duhamelEnergyCoeff 1 (fun k τ => sineCoeffs (Q τ) k) τ k with hCh
      set Lg := duhamelEnergyCoeff 1 Fl τ k with hLg
      rw [hdec]
      show |H + Ch + Lg| ≤ meanLadderEnv û₀ χ₀ chemE.env logE.env k
      unfold meanLadderEnv
      have htail : |Ch + Lg| ≤ |χ₀| * chemE.env k + logE.env k :=
        (abs_add_le _ _).trans (add_le_add hchem hlog)
      have hassoc : H + Ch + Lg = H + (Ch + Lg) := by ring
      rw [hassoc]
      exact (abs_add_le _ _).trans (add_le_add hheat htail)

end ShenWork.Paper2.IntervalChiNegMeanFixedStep

namespace ShenWork.Paper2.IntervalChiNegMeanFixedStep
#print axioms memHSigma_update
#print axioms trajLadder_step_meanFixed
end ShenWork.Paper2.IntervalChiNegMeanFixedStep
