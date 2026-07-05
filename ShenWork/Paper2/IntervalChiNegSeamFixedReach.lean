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
  (MeanStepBundle MeanBundleFamily MeanStepSupply meanReach_H1_of_base
   meanReach_H1_of_base_supply)
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

/-- Single mean-fixed bundle for the conjugate solution.  The seam record supplies
the σ-local analytic fields; this constructor discharges the mean row and the
positive-mode decomposition row. -/
def meanStepBundle_conjugate {σ : ℝ}
    (hu0 : u 0 = u₀) (hM0 : 0 ≤ Mmean)
    (hbd : ∀ τ, 0 < τ → τ ≤ t → ∀ x : intervalDomainPoint, |u τ x| ≤ Mmean)
    (hcont : HasContinuousSlices t u)
    (hmean0 : |cosineCoeffs (intervalDomainLift u₀) 0| ≤ Mmean)
    (hmd : ∀ τ, 0 < τ → ∀ k, k ≠ 0 →
      cosineCoeffs (intervalDomainLift (u τ)) k
        = Real.exp (-(τ * lam k)) * cosineCoeffs (intervalDomainLift u₀) k
          + (-p.χ₀) * duhamelEnergyCoeff 1
              (fun k τ => sineCoeffs (conjQ p u τ) k) τ k
          + duhamelEnergyCoeff 1 (conjFl p u) τ k)
    {E : TrajectoryHSigmaEnvelope σ t
      (fun τ => cosineCoeffs (intervalDomainLift (u τ)))}
    (C : CarrySeam p μ β t u v vx W σ E) :
    MeanStepBundle μ σ β p.χ₀ t (fun τ => intervalDomainLift (u τ)) v
      (cosineCoeffs (intervalDomainLift u₀)) (conjQ p u) W vx (conjFl p u) Mmean E :=
  { hμ := C.hμ, hσ0 := C.hσ0, hσ1 := C.hσ1, hβ := C.hβ
    ht := C.ht, ht1 := C.ht1
    hû₀ := by simpa [hu0] using C.hû₀
    hvnn := C.hvnn, hQ := C.hQ, hWdef := C.hWdef
    hbr := C.hbr, hbridge := C.hbridge, hvrel := C.hvrel
    hdiv := C.hdiv, hQ_cont := C.hQ_cont, L := C.L
    hFl_cont := C.hFl_cont
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

/-- Window-restricted single bundle constructor: the decomposition input is only
needed on the actual time interval. -/
def meanStepBundle_conjugate_windowHmd {σ : ℝ}
    (hu0 : u 0 = u₀) (hM0 : 0 ≤ Mmean)
    (hbd : ∀ τ, 0 < τ → τ ≤ t → ∀ x : intervalDomainPoint, |u τ x| ≤ Mmean)
    (hcont : HasContinuousSlices t u)
    (hmean0 : |cosineCoeffs (intervalDomainLift u₀) 0| ≤ Mmean)
    (hmd : ∀ τ, 0 < τ → τ ≤ t → ∀ k, k ≠ 0 →
      cosineCoeffs (intervalDomainLift (u τ)) k
        = Real.exp (-(τ * lam k)) * cosineCoeffs (intervalDomainLift u₀) k
          + (-p.χ₀) * duhamelEnergyCoeff 1
              (fun k τ => sineCoeffs (conjQ p u τ) k) τ k
          + duhamelEnergyCoeff 1 (conjFl p u) τ k)
    {E : TrajectoryHSigmaEnvelope σ t
      (fun τ => cosineCoeffs (intervalDomainLift (u τ)))}
    (C : CarrySeam p μ β t u v vx W σ E) :
    MeanStepBundle μ σ β p.χ₀ t (fun τ => intervalDomainLift (u τ)) v
      (cosineCoeffs (intervalDomainLift u₀)) (conjQ p u) W vx (conjFl p u) Mmean E :=
  { hμ := C.hμ, hσ0 := C.hσ0, hσ1 := C.hσ1, hβ := C.hβ
    ht := C.ht, ht1 := C.ht1
    hû₀ := by simpa [hu0] using C.hû₀
    hvnn := C.hvnn, hQ := C.hQ, hWdef := C.hWdef
    hbr := C.hbr, hbridge := C.hbridge, hvrel := C.hvrel
    hdiv := C.hdiv, hQ_cont := C.hQ_cont, L := C.L
    hFl_cont := C.hFl_cont
    hdecomp_pos := by
      intro τ hτ k hk
      rcases eq_or_lt_of_le hτ.1 with h0 | h0
      · subst h0; simpa [hu0] using decomp_tau0 (p := p) (u := u) hu0 k
      · simpa [hu0] using hmd τ h0 hτ.2 k hk
    hmean := by
      intro τ hτ
      rcases eq_or_lt_of_le hτ.1 with h0 | h0
      · rw [← h0, hu0]; exact hmean0
      · exact mean_bound_of_mild hM0 hbd hcont h0 hτ.2 }

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
  fun σ E => meanStepBundle_conjugate hu0 hM0 hbd hcont hmean0 hmd (C σ E)

/-- Window-restricted variant of `meanBundleFamily_conjugate`.  The `k ≠ 0`
decomposition is only required for `0 < τ ≤ t`, which matches the landed
positive-time Duhamel decomposition; the `τ = 0` row is glued by `decomp_tau0`. -/
def meanBundleFamily_conjugate_windowHmd
    (hu0 : u 0 = u₀) (hM0 : 0 ≤ Mmean)
    (hbd : ∀ τ, 0 < τ → τ ≤ t → ∀ x : intervalDomainPoint, |u τ x| ≤ Mmean)
    (hcont : HasContinuousSlices t u)
    (hmean0 : |cosineCoeffs (intervalDomainLift u₀) 0| ≤ Mmean)
    (hmd : ∀ τ, 0 < τ → τ ≤ t → ∀ k, k ≠ 0 →
      cosineCoeffs (intervalDomainLift (u τ)) k
        = Real.exp (-(τ * lam k)) * cosineCoeffs (intervalDomainLift u₀) k
          + (-p.χ₀) * duhamelEnergyCoeff 1 (fun k τ => sineCoeffs (conjQ p u τ) k) τ k
          + duhamelEnergyCoeff 1 (conjFl p u) τ k)
    (C : ∀ σ E, CarrySeam p μ β t u v vx W σ E) :
    MeanBundleFamily μ β p.χ₀ t (fun τ => intervalDomainLift (u τ)) v
      (cosineCoeffs (intervalDomainLift u₀)) (conjQ p u) W vx (conjFl p u) Mmean :=
  fun σ E => meanStepBundle_conjugate_windowHmd hu0 hM0 hbd hcont hmean0 hmd (C σ E)

/-- Exact finite seam supply for the window-restricted conjugate ladder.  The
tail is indexed by the envelope produced from the head seam, so no off-ladder
or off-envelope seam is requested. -/
def CarrySeamSupply_windowHmd
    (hu0 : u 0 = u₀) (hM0 : 0 ≤ Mmean)
    (hbd : ∀ τ, 0 < τ → τ ≤ t → ∀ x : intervalDomainPoint, |u τ x| ≤ Mmean)
    (hcont : HasContinuousSlices t u)
    (hmean0 : |cosineCoeffs (intervalDomainLift u₀) 0| ≤ Mmean)
    (hmd : ∀ τ, 0 < τ → τ ≤ t → ∀ k, k ≠ 0 →
      cosineCoeffs (intervalDomainLift (u τ)) k
        = Real.exp (-(τ * lam k)) * cosineCoeffs (intervalDomainLift u₀) k
          + (-p.χ₀) * duhamelEnergyCoeff 1
              (fun k τ => sineCoeffs (conjQ p u τ) k) τ k
          + duhamelEnergyCoeff 1 (conjFl p u) τ k) :
    (n : ℕ) → (σ : ℝ) →
      TrajectoryHSigmaEnvelope σ t (fun τ => cosineCoeffs (intervalDomainLift (u τ))) → Type
  | 0, _σ, _E => PUnit
  | n + 1, σ, E =>
      Sigma (fun C : CarrySeam p μ β t u v vx W σ E =>
        CarrySeamSupply_windowHmd hu0 hM0 hbd hcont hmean0 hmd n (σ + 1 / 4)
          (meanStepBundle_conjugate_windowHmd hu0 hM0 hbd hcont hmean0 hmd C).step)

/-- Convert the exact carried seam supply into the exact mean-step supply. -/
def carrySeamSupply_windowHmd_to_meanStepSupply
    (hu0 : u 0 = u₀) (hM0 : 0 ≤ Mmean)
    (hbd : ∀ τ, 0 < τ → τ ≤ t → ∀ x : intervalDomainPoint, |u τ x| ≤ Mmean)
    (hcont : HasContinuousSlices t u)
    (hmean0 : |cosineCoeffs (intervalDomainLift u₀) 0| ≤ Mmean)
    (hmd : ∀ τ, 0 < τ → τ ≤ t → ∀ k, k ≠ 0 →
      cosineCoeffs (intervalDomainLift (u τ)) k
        = Real.exp (-(τ * lam k)) * cosineCoeffs (intervalDomainLift u₀) k
          + (-p.χ₀) * duhamelEnergyCoeff 1
              (fun k τ => sineCoeffs (conjQ p u τ) k) τ k
          + duhamelEnergyCoeff 1 (conjFl p u) τ k) :
    ∀ (n : ℕ) {σ₀ : ℝ}
      (E₀ : TrajectoryHSigmaEnvelope σ₀ t
        (fun τ => cosineCoeffs (intervalDomainLift (u τ)))),
      CarrySeamSupply_windowHmd (p := p) (u₀ := u₀) (μ := μ) (β := β)
        (t := t) (Mmean := Mmean) (u := u) (v := v) (vx := vx) (W := W)
        hu0 hM0 hbd hcont hmean0 hmd n σ₀ E₀ →
      MeanStepSupply μ β p.χ₀ t (fun τ => intervalDomainLift (u τ)) v
        (cosineCoeffs (intervalDomainLift u₀)) (conjQ p u) W vx (conjFl p u)
        Mmean n σ₀ E₀
  | 0, _σ₀, _E₀, _S => PUnit.unit
  | n + 1, _σ₀, _E₀, S =>
      ⟨meanStepBundle_conjugate_windowHmd hu0 hM0 hbd hcont hmean0 hmd S.1,
        carrySeamSupply_windowHmd_to_meanStepSupply hu0 hM0 hbd hcont hmean0 hmd n
          (meanStepBundle_conjugate_windowHmd hu0 hM0 hbd hcont hmean0 hmd S.1).step
          S.2⟩

/-- Compatibility bridge from the old all-σ seam family to the exact finite
window-restricted seam supply. -/
def carrySeamSupply_windowHmd_of_family
    (hu0 : u 0 = u₀) (hM0 : 0 ≤ Mmean)
    (hbd : ∀ τ, 0 < τ → τ ≤ t → ∀ x : intervalDomainPoint, |u τ x| ≤ Mmean)
    (hcont : HasContinuousSlices t u)
    (hmean0 : |cosineCoeffs (intervalDomainLift u₀) 0| ≤ Mmean)
    (hmd : ∀ τ, 0 < τ → τ ≤ t → ∀ k, k ≠ 0 →
      cosineCoeffs (intervalDomainLift (u τ)) k
        = Real.exp (-(τ * lam k)) * cosineCoeffs (intervalDomainLift u₀) k
          + (-p.χ₀) * duhamelEnergyCoeff 1
              (fun k τ => sineCoeffs (conjQ p u τ) k) τ k
          + duhamelEnergyCoeff 1 (conjFl p u) τ k)
    (C : ∀ σ E, CarrySeam p μ β t u v vx W σ E) :
    ∀ (n : ℕ) {σ₀ : ℝ}
      (E₀ : TrajectoryHSigmaEnvelope σ₀ t
        (fun τ => cosineCoeffs (intervalDomainLift (u τ)))),
      CarrySeamSupply_windowHmd (p := p) (u₀ := u₀) (μ := μ) (β := β)
        (t := t) (Mmean := Mmean) (u := u) (v := v) (vx := vx) (W := W)
        hu0 hM0 hbd hcont hmean0 hmd n σ₀ E₀
  | 0, _σ₀, _E₀ => PUnit.unit
  | n + 1, σ₀, E₀ =>
      ⟨C σ₀ E₀,
        carrySeamSupply_windowHmd_of_family hu0 hM0 hbd hcont hmean0 hmd C n
          (meanStepBundle_conjugate_windowHmd hu0 hM0 hbd hcont hmean0 hmd
            (C σ₀ E₀)).step⟩

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

/-- Window-restricted capstone reach: same conclusion as `meanReach_H1_conjugate`,
but the carried `hmd` input is restricted to the actual time window `0 < τ ≤ t`. -/
def meanReach_H1_conjugate_windowHmd {σ₀ : ℝ} (n : ℕ)
    (hreach : (1 : ℝ) ≤ σ₀ + n * (1 / 4))
    (hu0 : u 0 = u₀) (hM0 : 0 ≤ Mmean)
    (hbd : ∀ τ, 0 < τ → τ ≤ t → ∀ x : intervalDomainPoint, |u τ x| ≤ Mmean)
    (hcont : HasContinuousSlices t u)
    (hmean0 : |cosineCoeffs (intervalDomainLift u₀) 0| ≤ Mmean)
    (hmd : ∀ τ, 0 < τ → τ ≤ t → ∀ k, k ≠ 0 →
      cosineCoeffs (intervalDomainLift (u τ)) k
        = Real.exp (-(τ * lam k)) * cosineCoeffs (intervalDomainLift u₀) k
          + (-p.χ₀) * duhamelEnergyCoeff 1 (fun k τ => sineCoeffs (conjQ p u τ) k) τ k
          + duhamelEnergyCoeff 1 (conjFl p u) τ k)
    (E₀ : TrajectoryHSigmaEnvelope σ₀ t
      (fun τ => cosineCoeffs (intervalDomainLift (u τ))))
    (C : ∀ σ E, CarrySeam p μ β t u v vx W σ E) :
    TrajectoryHSigmaEnvelope 1 t (fun τ => cosineCoeffs (intervalDomainLift (u τ))) :=
  meanReach_H1_of_base n hreach E₀
    (meanBundleFamily_conjugate_windowHmd hu0 hM0 hbd hcont hmean0 hmd C)

/-- Exact finite-supply capstone reach: consumes only the carried seams along the
generated mean-fixed ladder. -/
def meanReach_H1_conjugate_windowHmd_supply {σ₀ : ℝ} (n : ℕ)
    (hreach : (1 : ℝ) ≤ σ₀ + n * (1 / 4))
    (hu0 : u 0 = u₀) (hM0 : 0 ≤ Mmean)
    (hbd : ∀ τ, 0 < τ → τ ≤ t → ∀ x : intervalDomainPoint, |u τ x| ≤ Mmean)
    (hcont : HasContinuousSlices t u)
    (hmean0 : |cosineCoeffs (intervalDomainLift u₀) 0| ≤ Mmean)
    (hmd : ∀ τ, 0 < τ → τ ≤ t → ∀ k, k ≠ 0 →
      cosineCoeffs (intervalDomainLift (u τ)) k
        = Real.exp (-(τ * lam k)) * cosineCoeffs (intervalDomainLift u₀) k
          + (-p.χ₀) * duhamelEnergyCoeff 1 (fun k τ => sineCoeffs (conjQ p u τ) k) τ k
          + duhamelEnergyCoeff 1 (conjFl p u) τ k)
    (E₀ : TrajectoryHSigmaEnvelope σ₀ t
      (fun τ => cosineCoeffs (intervalDomainLift (u τ))))
    (S : CarrySeamSupply_windowHmd (p := p) (u₀ := u₀) (μ := μ) (β := β)
      (t := t) (Mmean := Mmean) (u := u) (v := v) (vx := vx) (W := W)
      hu0 hM0 hbd hcont hmean0 hmd n σ₀ E₀) :
    TrajectoryHSigmaEnvelope 1 t (fun τ => cosineCoeffs (intervalDomainLift (u τ))) :=
  meanReach_H1_of_base_supply n hreach E₀
    (carrySeamSupply_windowHmd_to_meanStepSupply hu0 hM0 hbd hcont hmean0 hmd n E₀ S)

end ShenWork.Paper2.IntervalChiNegSeamFixedReach

namespace ShenWork.Paper2.IntervalChiNegSeamFixedReach
#print axioms meanStepBundle_conjugate
#print axioms meanStepBundle_conjugate_windowHmd
#print axioms meanBundleFamily_conjugate
#print axioms meanBundleFamily_conjugate_windowHmd
#print axioms meanReach_H1_conjugate
#print axioms meanReach_H1_conjugate_windowHmd
#print axioms meanReach_H1_conjugate_windowHmd_supply
end ShenWork.Paper2.IntervalChiNegSeamFixedReach
