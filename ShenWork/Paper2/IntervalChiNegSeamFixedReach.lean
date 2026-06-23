/-
  ShenWork/Paper2/IntervalChiNegSeamFixedReach.lean

  χ₀<0 — the CAPSTONE: `meanReach_H1_conjugate`, reaching
  `TrajectoryHSigmaEnvelope 1` for `u = conjugatePicardLimit p u₀ DB.T` through the
  MEAN-FIXED ladder, with the k=0 mode discharged by the DIRECT mean bound
  (`mean_bound_of_mild`) and the k≠0 decomposition by the landed
  `conjugateSlice_decomp_tauLift_pos` (τ>0) glued with `decomp_tau0` (τ=0) — NO
  false `hzero`/mean-conservation anywhere.

  `hmean` and `hdecomp_pos` of `MeanStepBundle` are DISCHARGED here from landed
  mild/decomp data.  The remaining `MeanStepBundle` fields — `hvnn` (the carried
  Neumann-resolver maximum principle; FIX 2 has NO landed producer, see
  `IntervalChiNegSeamFixed`), the per-τ bridges/relays (FIX 3, dischargeable from E
  in principle but carried), the base `E₀`, the per-τ decomp residuals `hmd` — are
  carried as the explicit seam record `CarrySeam`.  `MemHSigma 1` is therefore NOT
  unconditional; the FALSE k=0 obstruction is removed.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file only.
-/
import ShenWork.Paper2.IntervalChiNegSeamFixed

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegSeamFixedReach

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardLimit)
open ShenWork.IntervalMildPicard (HasContinuousSlices)
open ShenWork.Paper2.HSigmaScale (lam MemHSigma resolverCoeff)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.Paper2.IntervalEnvelopeProp (Envelopes)
open ShenWork.Paper2.IntervalDenomEnvelopeResolver (resolverValue)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.IntervalDecompTauLift (conjQ conjFl)
open ShenWork.Paper2.IntervalTrajectoryEnvelope (TrajectoryHSigmaEnvelope)
open ShenWork.Paper2.IntervalChiNegMeanFixedIterate
  (MeanStepBundle MeanBundleFamily meanReach_H1_of_base)
open ShenWork.Paper2.IntervalChiNegSeamFixed (mean_bound_of_mild decomp_tau0)

/-- The carried per-`(σ,E)` seam of the mean-fixed bundle for the conjugate
solution: every `MeanStepBundle` field EXCEPT the discharged `hmean`/`hdecomp_pos`,
given per σ and running envelope `E`. -/
structure CarrySeam (p : CM2Params) (μ β t : ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (v vx W : ℝ → ℝ → ℝ)
    (σ : ℝ) (E : TrajectoryHSigmaEnvelope σ t
      (fun τ => cosineCoeffs (intervalDomainLift (u τ)))) where
  hμ : 0 < μ
  hσ0 : 1 / 2 < σ
  hσ1 : σ < 3 / 2
  hβ : 0 ≤ β
  ht : 0 < t
  ht1 : t ≤ 1
  hû₀ : MemHSigma (σ + 1 / 4) (cosineCoeffs (intervalDomainLift (u 0)))
  hvnn : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ x,
    0 ≤ resolverValue μ (cosineCoeffs (intervalDomainLift (u τ))) x
  hQ : ∀ τ, conjQ p u τ = fun x => W τ x * vx τ x
  hWdef : ∀ τ, W τ = fun x => intervalDomainLift (u τ) x
    * (1 + resolverValue μ (cosineCoeffs (intervalDomainLift (u τ))) x) ^ (-β)
  hbr : ∀ τ ∈ Set.Icc (0:ℝ) t,
    ShenWork.Paper2.IntervalWienerAlgebra.CosineMulBridge (intervalDomainLift (u τ))
      (fun x => (1 + resolverValue μ
        (cosineCoeffs (intervalDomainLift (u τ))) x) ^ (-β))
  hbridge : ∀ τ ∈ Set.Icc (0:ℝ) t,
    ShenWork.Paper2.IntervalMixedProduct.MixedMulBridge (W τ) (vx τ)
  hvrel : ∀ τ ∈ Set.Icc (0:ℝ) t, Envelopes (resolverCoeff 1 E.env) (cosineCoeffs (v τ))
  hdiv : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k,
    |sineCoeffs (vx τ) k| = Real.sqrt (lam k) * |cosineCoeffs (v τ) k|
  hQ_cont : ∀ k, Continuous (fun τ => sineCoeffs (conjQ p u τ) k)
  L : TrajectoryHSigmaEnvelope σ t (fun τ k => conjFl p u k τ)
  hFl_cont : ∀ k, Continuous (conjFl p u k)

variable {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
variable {μ β t Mmean : ℝ} {u : ℝ → intervalDomainPoint → ℝ} {v vx W : ℝ → ℝ → ℝ}

/-- **The mean-fixed bundle family for the conjugate solution.**  `hmean` and
`hdecomp_pos` are DISCHARGED from landed mild/decomp data; all else from the carried
seam `C`. -/
def meanBundleFamily_conjugate
    (hu0 : u 0 = u₀) (hM0 : 0 ≤ Mmean)
    (hbd : ∀ τ, 0 < τ → τ ≤ t → ∀ x : intervalDomainPoint, |u τ x| ≤ Mmean)
    (hcont : HasContinuousSlices t u)
    (hmean0 : |cosineCoeffs (intervalDomainLift u₀) 0| ≤ Mmean)
    (hmd : ∀ τ, 0 < τ → ∀ k, k ≠ 0 →
      cosineCoeffs (intervalDomainLift (u τ)) k
        = Real.exp (-(τ * lam k)) * cosineCoeffs (intervalDomainLift u₀) k
          + (-p.χ₀) * duhamelEnergyCoeff 1 (fun k τ => sineCoeffs (conjQ p u τ) k) τ k
          + duhamelEnergyCoeff 1 (conjFl p u) τ k)
    (C : ∀ σ E, CarrySeam p μ β t u v vx W σ E) :
    MeanBundleFamily μ β p.χ₀ t (fun τ => intervalDomainLift (u τ)) v
      (cosineCoeffs (intervalDomainLift u₀)) (conjQ p u) W vx (conjFl p u) Mmean :=
  fun σ E =>
    { hμ := (C σ E).hμ, hσ0 := (C σ E).hσ0, hσ1 := (C σ E).hσ1, hβ := (C σ E).hβ
      ht := (C σ E).ht, ht1 := (C σ E).ht1
      hû₀ := by simpa [hu0] using (C σ E).hû₀
      hvnn := (C σ E).hvnn, hQ := (C σ E).hQ, hWdef := (C σ E).hWdef
      hbr := (C σ E).hbr, hbridge := (C σ E).hbridge, hvrel := (C σ E).hvrel
      hdiv := (C σ E).hdiv, hQ_cont := (C σ E).hQ_cont, L := (C σ E).L
      hFl_cont := (C σ E).hFl_cont
      hdecomp_pos := by
        intro τ hτ k hk
        rcases eq_or_lt_of_le hτ.1 with h0 | h0
        · subst h0; simpa [hu0] using decomp_tau0 (p := p) (u := u) hu0 k
        · simpa [hu0] using hmd τ h0 k hk
      hmean := by
        intro τ hτ
        rcases eq_or_lt_of_le hτ.1 with h0 | h0
        · rw [← h0, hu0]; exact hmean0
        · exact mean_bound_of_mild hM0 hbd hcont h0 hτ.2 }

/-- **CAPSTONE — REACH `TrajectoryHSigmaEnvelope 1` for `conjugatePicardLimit`,
mean-fixed.**  `hmean`/`hdecomp_pos` discharged from landed data (NO false `hzero`);
the base `E₀`, the per-τ decomp residuals `hmd`, and the carried seam `C`
(incl. the genuinely-carried `hvnn` and the bridges) are the explicit frontier. -/
def meanReach_H1_conjugate {σ₀ : ℝ} (n : ℕ)
    (hreach : (1 : ℝ) ≤ σ₀ + n * (1 / 4))
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
    TrajectoryHSigmaEnvelope 1 t (fun τ => cosineCoeffs (intervalDomainLift (u τ))) :=
  meanReach_H1_of_base n hreach E₀
    (meanBundleFamily_conjugate hu0 hM0 hbd hcont hmean0 hmd C)

end ShenWork.Paper2.IntervalChiNegSeamFixedReach

namespace ShenWork.Paper2.IntervalChiNegSeamFixedReach
#print axioms meanBundleFamily_conjugate
#print axioms meanReach_H1_conjugate
end ShenWork.Paper2.IntervalChiNegSeamFixedReach
