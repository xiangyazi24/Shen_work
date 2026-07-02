import ShenWork.Wiener.EWA.SourcePerSliceClose
import ShenWork.Wiener.EWA.SourceSynthesisL1
import ShenWork.Paper2.IntervalPicardLimitRestartWeak

noncomputable section

namespace ShenWork.EWA

open scoped BigOperators
open Set Filter Topology
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)
open ShenWork.IntervalResolverDirectTimeRegularity (HasResolverDirectSpectralData)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs)
open ShenWork.IntervalDuhamelClosedC2 (cosineCoeffSeries_contDiff_two)
open ShenWork.IntervalPicardLimitRestartWeak (DuhamelSourceL1ContOn)

variable {T : ℝ}

private theorem gPow_continuousOn_window_of_L1ContOn
    (p : CM2Params) (u_star : EWA T 1) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn
      (coupledChemDivSourceCoeffs p (realSlice u_star)) T)
    (hlog : DuhamelSourceL1ContOn
      (coupledLogisticSourceCoeffs p (realSlice u_star)) T)
    {u₀E : WA 1} {δ ρ : ℝ} (hδρ : 0 < δ - ρ)
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ)
    (hu_ball : u_star ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ)
    (hrealizes : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x =
        ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x)
    {a b : ℝ} (hab : Icc a b ⊆ Ioo (0 : ℝ) T) :
    ContinuousOn
      (Function.uncurry (gPow p (realSlice u_star)
        (fun s x =>
          ∑' n, fullSourceCoeffDot p (realSlice u_star) u₀cos s n *
            cosineMode n x)))
      (Icc a b ×ˢ Icc (0 : ℝ) 1) := by
  have hbox : Icc a b ×ˢ Icc (0 : ℝ) 1 ⊆ Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1 :=
    prod_mono hab (subset_refl _)
  have hVal : ContinuousOn
      (Function.uncurry (fun (s : ℝ) (x : ℝ) =>
        intervalDomainLift (realSlice u_star s) x))
      (Icc a b ×ˢ Icc (0 : ℝ) 1) := by
    refine ((fullSourceCoeff_jointSolutionClosed_of_L1ContOn p (realSlice u_star)
      u₀cos hu0bd hchem hlog).mono hbox).congr ?_
    intro q hq
    obtain ⟨hqs, hqx⟩ := hq
    have hs : q.1 ∈ Ioo (0 : ℝ) T := hab hqs
    simpa [Function.uncurry] using hrealizes q.1 hs q.2 hqx
  have hpow : ContinuousOn
      (Function.uncurry (fun (s : ℝ) (x : ℝ) =>
        (intervalDomainLift (realSlice u_star s) x) ^ (p.γ - 1)))
      (Icc a b ×ˢ Icc (0 : ℝ) 1) := by
    refine ContinuousOn.rpow_const hVal ?_
    intro q hq
    left
    obtain ⟨hqs, hqx⟩ := hq
    have hs : q.1 ∈ Ioo (0 : ℝ) T := hab hqs
    have hpos : 0 < intervalDomainLift (realSlice u_star q.1) q.2 := by
      rw [intervalDomainLift, dif_pos hqx]
      exact realSlice_pos hδρ hheat hu_ball ⟨hs.1.le, hs.2.le⟩ ⟨q.2, hqx⟩
    exact ne_of_gt hpos
  have hDot : ContinuousOn
      (Function.uncurry (fun (s : ℝ) (x : ℝ) =>
        ∑' n, fullSourceCoeffDot p (realSlice u_star) u₀cos s n * cosineMode n x))
      (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    (fullSourceCoeffDot_jointTimeDerivClosed_of_L1ContOn p (realSlice u_star)
      u₀cos hu0bd hchem hlog).mono hbox
  have : ContinuousOn
      (Function.uncurry (fun (s : ℝ) (x : ℝ) =>
        p.ν * p.γ * (intervalDomainLift (realSlice u_star s) x) ^ (p.γ - 1)
          * (∑' n, fullSourceCoeffDot p (realSlice u_star) u₀cos s n *
            cosineMode n x)))
      (Icc a b ×ˢ Icc (0 : ℝ) 1) := by
    have h1 : ContinuousOn
        (Function.uncurry (fun (s : ℝ) (x : ℝ) =>
          p.ν * p.γ * (intervalDomainLift (realSlice u_star s) x) ^ (p.γ - 1)))
        (Icc a b ×ˢ Icc (0 : ℝ) 1) := continuousOn_const.mul hpow
    exact h1.mul hDot
  simpa only [gPow, Function.uncurry] using this

private theorem hK1_assembled_of_L1ContOn
    (p : CM2Params) (u_star : EWA T 1) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn
      (coupledChemDivSourceCoeffs p (realSlice u_star)) T)
    (hlog : DuhamelSourceL1ContOn
      (coupledLogisticSourceCoeffs p (realSlice u_star)) T)
    {u₀E : WA 1} {δ₀ ρ : ℝ} (hδρ : 0 < δ₀ - ρ)
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ₀)
    (hu_ball : u_star ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ)
    (hsumE : ∀ t ∈ Ioo (0 : ℝ) T,
      Summable (fun n => unitIntervalCosineEigenvalue n *
        |fullSourceCoeff p (realSlice u_star) u₀cos t n|))
    (hrealizes : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x =
        ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x) :
    ∀ σ ∈ Ioo (0 : ℝ) T, ∃ δ > 0,
      (∀ᶠ s in 𝓝 σ,
          ContinuousOn
            (fun x => p.ν * (intervalDomainLift (realSlice u_star s) x) ^ p.γ)
            (Icc (0 : ℝ) 1))
        ∧ (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball σ δ,
            HasDerivAt (fun r => intervalDomainLift (realSlice u_star r) x)
              ((fun s x =>
                ∑' n, fullSourceCoeffDot p (realSlice u_star) u₀cos s n *
                  cosineMode n x) s x) s)
        ∧ (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball σ δ,
            0 < intervalDomainLift (realSlice u_star s) x)
        ∧ ContinuousOn (Function.uncurry (gPow p (realSlice u_star)
            (fun s x =>
              ∑' n, fullSourceCoeffDot p (realSlice u_star) u₀cos s n *
                cosineMode n x)))
            (Icc (σ - δ) (σ + δ) ×ˢ Icc (0 : ℝ) 1) := by
  intro σ hσ
  obtain ⟨δ, hδpos, hδsub⟩ : ∃ δ > 0, Icc (σ - δ) (σ + δ) ⊆ Ioo (0 : ℝ) T := by
    have hσ0 : 0 < σ := hσ.1
    have hσT : σ < T := hσ.2
    refine ⟨min (σ / 2) ((T - σ) / 2), lt_min (by linarith) (by linarith), ?_⟩
    intro y hy
    have h1 : σ - min (σ / 2) ((T - σ) / 2) ≤ y := hy.1
    have h2 : y ≤ σ + min (σ / 2) ((T - σ) / 2) := hy.2
    have hmin1 : min (σ / 2) ((T - σ) / 2) ≤ σ / 2 := min_le_left _ _
    have hmin2 : min (σ / 2) ((T - σ) / 2) ≤ (T - σ) / 2 :=
      min_le_right _ _
    exact ⟨by linarith, by linarith⟩
  refine ⟨δ, hδpos, ?_, ?_, ?_, ?_⟩
  · filter_upwards [isOpen_Ioo.mem_nhds hσ] with s hs
    have hcont : ContinuousOn (intervalDomainLift (realSlice u_star s))
        (Icc (0 : ℝ) 1) :=
      ((cosineCoeffSeries_contDiff_two (hsumE s hs)).continuous.continuousOn).congr
        (fun x hx => hrealizes s hs x hx)
    exact continuousOn_const.mul (hcont.rpow_const (fun _ _ => Or.inr p.hγ.le))
  · intro x hx s hs
    have hdist : |s - σ| < δ := by
      have := Metric.mem_ball.1 hs
      rwa [Real.dist_eq] at this
    have hsmem : s ∈ Icc (σ - δ) (σ + δ) := by
      have := abs_lt.1 hdist
      exact ⟨by linarith [this.1], by linarith [this.2]⟩
    have hsIoo : s ∈ Ioo (0 : ℝ) T := hδsub hsmem
    have hxIcc : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
    have hsynth := synthesis_hasDerivAt_of_L1ContOn p
      (realSlice u_star) u₀cos hu0bd hchem hlog hsIoo x
    have hagree :
        (fun r => intervalDomainLift (realSlice u_star r) x)
          =ᶠ[𝓝 s]
        (fun r =>
          ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos r n *
            cosineMode n x) :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hsIoo)
        (fun r hr => hrealizes r hr x hxIcc)
    have hd := hsynth.congr_of_eventuallyEq hagree
    simpa only using hd
  · intro x hx s hs
    have hdist : |s - σ| < δ := by
      have := Metric.mem_ball.1 hs
      rwa [Real.dist_eq] at this
    have hsmem : s ∈ Icc (σ - δ) (σ + δ) := by
      have := abs_lt.1 hdist
      exact ⟨by linarith [this.1], by linarith [this.2]⟩
    have hsIoo : s ∈ Ioo (0 : ℝ) T := hδsub hsmem
    have hxIcc : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
    rw [intervalDomainLift, dif_pos hxIcc]
    exact realSlice_pos hδρ hheat hu_ball ⟨hsIoo.1.le, hsIoo.2.le⟩ ⟨x, hxIcc⟩
  · exact gPow_continuousOn_window_of_L1ContOn p u_star u₀cos hu0bd hchem hlog
      hδρ hheat hu_ball hrealizes hδsub

theorem realSlice_Hv_closed_of_L1ContOn
    (p : CM2Params) (u_star : EWA T 1) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn
      (coupledChemDivSourceCoeffs p (realSlice u_star)) T)
    (hlog : DuhamelSourceL1ContOn
      (coupledLogisticSourceCoeffs p (realSlice u_star)) T)
    {u₀E : WA 1} {δ₀ ρ : ℝ} (hδρ : 0 < δ₀ - ρ)
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ₀)
    (hu_ball : u_star ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ)
    (hsumE : ∀ t ∈ Ioo (0 : ℝ) T,
      Summable (fun n => unitIntervalCosineEigenvalue n *
        |fullSourceCoeff p (realSlice u_star) u₀cos t n|))
    (hrealizes : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x =
        ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x)
    (C : ℝ → ℝ) (hC : ∀ t₀, 0 ≤ C t₀)
    (hdecay : ∀ t₀, 0 < t₀ → t₀ < T →
      ∀ σ ∈ Icc (t₀ / 4) ((t₀ + 3 * T) / 4), ∀ k : ℕ, 1 ≤ k →
        |cosineCoeffs (fun x =>
          p.ν * intervalDomainLift (realSlice u_star σ) x ^ p.γ) k|
          ≤ C t₀ / ((k : ℝ) * Real.pi) ^ 2)
    (ha0 : ∀ t₀, 0 < t₀ → t₀ < T →
      ∀ σ ∈ Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
        |cosineCoeffs (fun x =>
          p.ν * intervalDomainLift (realSlice u_star σ) x ^ p.γ) 0| ≤ C t₀) :
    HasResolverDirectSpectralData T
      (mildChemicalConcentration p (realSlice u_star)) p := by
  refine realSlice_resolverSpectralData_full p u_star
    (fun s x =>
      ∑' n, fullSourceCoeffDot p (realSlice u_star) u₀cos s n * cosineMode n x)
    (fun _ σ n => fullSourceCoeff p (realSlice u_star) u₀cos σ n)
    ?_ ?_ ?_ C hC hdecay ha0 ?_ ?_
  · intro t₀ ht₀ ht₀T σ hσ
    have hσIoo : σ ∈ Ioo (0 : ℝ) T :=
      ⟨lt_of_lt_of_le (by linarith) hσ.1, lt_of_le_of_lt hσ.2 (by linarith)⟩
    exact hsumE σ hσIoo
  · intro t₀ ht₀ ht₀T σ hσ x hx
    have hσIoo : σ ∈ Ioo (0 : ℝ) T :=
      ⟨lt_of_lt_of_le (by linarith) hσ.1, lt_of_le_of_lt hσ.2 (by linarith)⟩
    exact hrealizes σ hσIoo x hx
  · intro t₀ ht₀ ht₀T σ hσ x hx
    have hσIoo : σ ∈ Ioo (0 : ℝ) T :=
      ⟨lt_of_lt_of_le (by linarith) hσ.1, lt_of_le_of_lt hσ.2 (by linarith)⟩
    rw [intervalDomainLift, dif_pos hx]
    exact realSlice_pos hδρ hheat hu_ball ⟨hσIoo.1.le, hσIoo.2.le⟩ ⟨x, hx⟩
  · exact hK1_assembled_of_L1ContOn p u_star u₀cos hu0bd hchem hlog
      hδρ hheat hu_ball hsumE hrealizes
  · intro t₀ ht₀ ht₀T
    have hsub : Icc (t₀ / 4) ((t₀ + 3 * T) / 4) ⊆ Ioo (0 : ℝ) T := by
      intro y hy
      exact ⟨lt_of_lt_of_le (by linarith) hy.1, lt_of_le_of_lt hy.2 (by linarith)⟩
    exact gPow_continuousOn_window_of_L1ContOn p u_star u₀cos hu0bd hchem hlog
      hδρ hheat hu_ball hrealizes hsub

end ShenWork.EWA

#print axioms ShenWork.EWA.realSlice_Hv_closed_of_L1ContOn
