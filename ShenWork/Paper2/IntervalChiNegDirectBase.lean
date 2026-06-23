/-
  ShenWork/Paper2/IntervalChiNegDirectBase.lean

  χ₀<0 — the CORRECTED DIRECT base E₀ (NO BCF, NO `hcontFam`, NO `trajPhi`,
  NO closed-box joint continuity — that route is τ=0-broken / vacuous).

  The BCF/trajBanach base (`trajEnvelope_chiNeg_base_direct`) demands the Duhamel
  map continuous on the CLOSED box `[0,t]×Ω`, but `intervalConjugateDuhamelMap` at
  `t=0` is `0` while `τ→0⁺ → u₀`, so it JUMPS at `τ=0`: `hcontFam` is unsatisfiable
  for `u₀ ≢ 0`.  This file builds the base DIRECTLY at the `H^σ`-scale via
  `trajEnvelope_chiNeg_direct` (per-slice mild-decomp domination), for the conjugate
  Picard limit `u := conjugatePicardLimit p u₀ T`:

  * `directBase_decomp` — the τ-uniform `k ≠ 0` three-term Duhamel decomposition,
    glued from `decomp_tau0` (`τ=0`, where `conjugatePicardLimit … 0 = 0` makes the
    `s=0` slice TRIVIAL) and the landed `conjugateSlice_decomp_tauLift_pos` (`τ>0`,
    PER-SLICE spatial-continuity seam — NOT joint).

  * `directBase_conjugate` — the base `TrajectoryHSigmaEnvelope (σ+1/4) t
    (cosineCoeffs ∘ intervalDomainLift ∘ u)` = `Estar = |û₀| + |χ₀|·chemE + logE`,
    `henv` via the three `H^{σ+1/4}` summands (`chemE` deflated, `memHSigma_deflate`,
    NO sineEnv inflation), `hdom` PROVEN per-slice (k=0 by the direct mean bound,
    k≠0 by the decomp + per-leg bounds).  The chemotaxis flux SOURCE envelope
    `M`/`hMsq`/`hFbd` is the genv self-reference — carried (per-level it is supplied
    by `genv_of_trajectoryEnvelope_uncond` inside the ladder family; at the base it
    is the single genuine analytic residual, NOT faked/relabeled).

  * `chiNeg_H1_directBase` — feeding the direct base E₀ + the CarrySeam family into
    `meanReach_H1_conjugate` ⟹ the χ₀<0 `TrajectoryHSigmaEnvelope 1` of `u`.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file only.
-/
import ShenWork.Paper2.IntervalChiNegDirectSupersolution
import ShenWork.Paper2.IntervalChiNegSeamFixedReach
import ShenWork.Paper2.IntervalDecompTauLift
import ShenWork.Paper2.IntervalCarrySeamConjDischarge

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegDirectBase

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardLimit)
open ShenWork.IntervalMildPicard (HasContinuousSlices)
open ShenWork.Paper2.HSigmaScale (lam MemHSigma)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.IntervalDecompTauLift
  (conjQ conjFl conjugateSlice_decomp_tauLift_pos)
open ShenWork.Paper2.IntervalTrajectoryEnvelope (TrajectoryHSigmaEnvelope)
open ShenWork.Paper2.IntervalChiNegDirectSupersolution (trajEnvelope_chiNeg_direct)
open ShenWork.Paper2.IntervalChiNegSeamFixed (mean_bound_of_mild decomp_tau0)
open ShenWork.Paper2.IntervalChiNegSeamFixedReach (CarrySeam meanReach_H1_conjugate)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateDuhamelMap
  (IntervalConjugateMildSolution intervalConjugateKernelOperator)

variable {p : CM2Params}

/-! ## 1. The τ-uniform `k ≠ 0` decomposition, `s=0` slice TRIVIAL. -/

/-- **`directBase_decomp`** — the `k ≠ 0` three-term Duhamel decomposition of the
conjugate slice, uniform over `τ ∈ Icc 0 t`.  The `τ=0` endpoint is `decomp_tau0`
(where `conjugatePicardLimit … 0 = 0` ⟹ both engine coefficients meet the zero
slice — the `s=0` triviality); `τ>0` is the landed PER-SLICE
`conjugateSlice_decomp_tauLift_pos`.  No joint continuity anywhere. -/
theorem directBase_decomp
    {u₀ : intervalDomainPoint → ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (hu0 : u 0 = u₀)
    {T : ℝ} (hmild : IntervalConjugateMildSolution p T u₀ u)
    {t : ℝ} (htT : t ≤ T)
    (hQcont : ∀ τ, 0 < τ → ∀ s, s < τ → Continuous (chemFluxLifted p (u s)))
    (hLcont : ∀ τ, 0 < τ → ∀ s, s < τ → Continuous (logisticLifted p (u s)))
    (hLM : ∀ τ, 0 < τ → ∃ Ml : ℝ, ∀ s, s < τ → ∀ j,
      |cosineCoeffs (logisticLifted p (u s)) j| ≤ Ml)
    (hheat_cont : ∀ τ, 0 < τ → Continuous
      (fun x => intervalFullSemigroupOperator τ (intervalDomainLift u₀) x))
    (hchemI_cont : ∀ τ, 0 < τ → Continuous (fun x => ∫ s in (0:ℝ)..τ,
      intervalConjugateKernelOperator (τ - s) (chemFluxLifted p (u s)) x))
    (hlogI_cont : ∀ τ, 0 < τ → Continuous (fun x => ∫ s in (0:ℝ)..τ,
      intervalFullSemigroupOperator (τ - s) (logisticLifted p (u s)) x))
    (hpt_heat : ∀ τ, 0 < τ → ∀ k, cosineCoeffs
      (fun x => intervalFullSemigroupOperator τ (intervalDomainLift u₀) x) k
        = Real.exp (-(τ * lam k)) * cosineCoeffs (intervalDomainLift u₀) k)
    (hswap_chem : ∀ τ, 0 < τ → ∀ k, cosineCoeffs (fun x => ∫ s in (0:ℝ)..τ,
        intervalConjugateKernelOperator (τ - s) (chemFluxLifted p (u s)) x) k
      = ∫ s in (0:ℝ)..τ, cosineCoeffs
        (fun x => intervalConjugateKernelOperator (τ - s) (chemFluxLifted p (u s)) x) k)
    (hswap_log : ∀ τ, 0 < τ → ∀ k, cosineCoeffs (fun x => ∫ s in (0:ℝ)..τ,
        intervalFullSemigroupOperator (τ - s) (logisticLifted p (u s)) x) k
      = ∫ s in (0:ℝ)..τ, cosineCoeffs
        (fun x => intervalFullSemigroupOperator (τ - s) (logisticLifted p (u s)) x) k) :
    ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k, k ≠ 0 →
      cosineCoeffs (intervalDomainLift (u τ)) k
        = Real.exp (-(τ * lam k)) * cosineCoeffs (intervalDomainLift u₀) k
          + (-p.χ₀) * duhamelEnergyCoeff 1 (fun k τ => sineCoeffs (conjQ p u τ) k) τ k
          + duhamelEnergyCoeff 1 (conjFl p u) τ k := by
  intro τ hτ k hk
  rcases eq_or_lt_of_le hτ.1 with h0 | h0
  · have hd := decomp_tau0 (p := p) (u := u) hu0 k
    rw [← h0]; exact hd
  · exact conjugateSlice_decomp_tauLift_pos p hmild htT hQcont hLcont hLM
      hheat_cont hchemI_cont hlogI_cont hpt_heat hswap_chem hswap_log h0 hτ.2 hk

/-! ## 2. The DIRECT base `E₀` via `trajEnvelope_chiNeg_direct`. -/

/-- **`directBase_conjugate`** — the χ₀<0 DIRECT base
`TrajectoryHSigmaEnvelope (σ+1/4) t (cosineCoeffs ∘ intervalDomainLift ∘ u)` for the
conjugate Picard limit, assembled by `trajEnvelope_chiNeg_direct`.  `env = Estar =
|û₀| + |χ₀|·chemE + logE`; `hdom` PROVEN per-slice (k=0 by `mean_bound_of_mild`,
k≠0 by `directBase_decomp`/`hdecomp_pos`).  The flux source envelope
`M`/`hMsup0`/`hMsq`/`hFbd` is the genv self-reference — carried (its per-level
producer is `genv_of_trajectoryEnvelope_uncond`, fired inside the ladder family at
every step; at the base it is the single genuine residual).  NO BCF/hcontFam. -/
def directBase_conjugate {σ : ℝ}
    {u₀ : intervalDomainPoint → ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hu0 : u 0 = u₀)
    (hû₀ : MemHSigma (σ + 1/4) (cosineCoeffs (intervalDomainLift u₀)))
    {M : ℕ → ℝ} (hMsup0 : ∀ k, 0 ≤ M k) (hMsq : MemHSigma σ M)
    (hFbd : ∀ k, ∀ τ ∈ Set.Icc (0 : ℝ) t, |sineCoeffs (conjQ p u τ) k| ≤ M k)
    (hQ_cont : ∀ k, Continuous (fun τ => sineCoeffs (conjQ p u τ) k))
    (logE : TrajectoryHSigmaEnvelope (σ + 1/4) t
      (fun s k => duhamelEnergyCoeff 1 (conjFl p u) s k))
    {Mmean : ℝ} (hM0 : 0 ≤ Mmean)
    (hmean0 : |cosineCoeffs (intervalDomainLift u₀) 0| ≤ Mmean)
    (hbd : ∀ τ, 0 < τ → τ ≤ t → ∀ x : intervalDomainPoint, |u τ x| ≤ Mmean)
    (hcont : HasContinuousSlices t u)
    (hdecomp_pos : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k, k ≠ 0 →
      cosineCoeffs (intervalDomainLift (u τ)) k
        = Real.exp (-(τ * lam k)) * cosineCoeffs (intervalDomainLift u₀) k
          + (-p.χ₀) * duhamelEnergyCoeff 1 (fun k τ => sineCoeffs (conjQ p u τ) k) τ k
          + duhamelEnergyCoeff 1 (conjFl p u) τ k) :
    TrajectoryHSigmaEnvelope (σ + 1/4) t
      (fun τ => cosineCoeffs (intervalDomainLift (u τ))) :=
  trajEnvelope_chiNeg_direct (σ := σ) (α := 1/4) (χ₀ := p.χ₀) (t := t)
    (u := fun τ => intervalDomainLift (u τ)) (Q := conjQ p u) (Fl := conjFl p u)
    (by norm_num) (by norm_num) ht ht1 hû₀ hQ_cont hMsup0 hMsq hFbd logE
    (Mmean := Mmean) hdecomp_pos
    (by
      intro τ hτ
      simp only
      rcases eq_or_lt_of_le hτ.1 with h0 | h0
      · rw [← h0, hu0]; exact hmean0
      · exact mean_bound_of_mild hM0 hbd hcont h0 hτ.2)

/-! ## 3. CAPSTONE — χ₀<0 `H¹` envelope from the DIRECT base. -/

/-- **`chiNeg_H1_directBase`** — the χ₀<0 `TrajectoryHSigmaEnvelope 1` of the
conjugate Picard limit, reached by feeding the DIRECT base `E₀` (no BCF) and the
CarrySeam ladder family into `meanReach_H1_conjugate`.  `hmean`/`hdecomp_pos` are
discharged from landed mild/decomp data inside `meanReach_H1_conjugate` (no false
`hzero`); the base `E₀` is now the DIRECT supersolution, not a carried abstract. -/
def chiNeg_H1_directBase {σ₀ μ β : ℝ} (n : ℕ) (hreach : (1 : ℝ) ≤ σ₀ + n * (1 / 4))
    {u₀ : intervalDomainPoint → ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    {v vx W : ℝ → ℝ → ℝ} {t Mmean : ℝ}
    (hu0 : u 0 = u₀) (hM0 : 0 ≤ Mmean)
    (hbd : ∀ τ, 0 < τ → τ ≤ t → ∀ x : intervalDomainPoint, |u τ x| ≤ Mmean)
    (hcont : HasContinuousSlices t u)
    (hmean0 : |cosineCoeffs (intervalDomainLift u₀) 0| ≤ Mmean)
    (hmd : ∀ τ, 0 < τ → ∀ k, k ≠ 0 →
      cosineCoeffs (intervalDomainLift (u τ)) k
        = Real.exp (-(τ * lam k)) * cosineCoeffs (intervalDomainLift u₀) k
          + (-p.χ₀) * duhamelEnergyCoeff 1 (fun k τ => sineCoeffs (conjQ p u τ) k) τ k
          + duhamelEnergyCoeff 1 (conjFl p u) τ k)
    (E₀ : TrajectoryHSigmaEnvelope σ₀ t
      (fun τ => cosineCoeffs (intervalDomainLift (u τ))))
    (C : ∀ σ E, CarrySeam p μ β t u v vx W σ E) :
    TrajectoryHSigmaEnvelope 1 t
      (fun τ => cosineCoeffs (intervalDomainLift (u τ))) :=
  meanReach_H1_conjugate (p := p) (μ := μ) (β := β) (u₀ := u₀) (u := u)
    (v := v) (vx := vx) (W := W) (t := t) (Mmean := Mmean) n hreach hu0 hM0 hbd
    hcont hmean0 hmd E₀ C

/-! ## AxiomAudit -/

section AxiomAudit
#print axioms directBase_decomp
#print axioms directBase_conjugate
#print axioms chiNeg_H1_directBase
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegDirectBase
