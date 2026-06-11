import ShenWork.Paper2.IntervalPicardWindowAdot
import ShenWork.PDE.IntervalDuhamelSourceTimeC1On
import ShenWork.Paper2.IntervalPicardLimitRestartWeak
import ShenWork.Paper2.IntervalPicardIterateBddRepr

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalGradientDuhamelMap (intervalGradientDuhamelMap logisticLifted)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalMildPicardRegularity (logisticSourceFun)
open ShenWork.IntervalPicardIterateTimeC1
  (logisticSourceDot picardIterate_K1_from_restart_of_representation)
open ShenWork.IntervalPicardIterateTimeC1Full
  (picardIterate_K1_full_from_restart_of_representation)
open ShenWork.IntervalPicardIterateRepresentation (iterateReprCoeff)
open ShenWork.IntervalPicardIterateRestart
  (iterateCoeff heatValue_eq_cosineSeries cosineCoeffs_of_l1_cosineSeries
   intervalGradientDuhamelMap_eq_of_chi0_zero)
open ShenWork.IntervalDuhamelSourceShift (localRestartCoeff_congr_on_Icc)
open ShenWork.IntervalSpectralSubtypeAdapter
  (intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont)
open ShenWork.IntervalSemigroupComposition (expEigSummable)
open ShenWork.IntervalTimeSoftClamp (φ φ_mem_range)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.IntervalPicardLimitRestartWeak
  (DuhamelSourceL1ContOn duhamelSpectral_eq_cosineSeries_weak
   abs_duhamelSpectralCoeff_le_weak duhamelSpectralCoeff_general_split_on)
open ShenWork.IntervalPicardLimitRestartBdd (DuhamelSourceBddOn)
open ShenWork.IntervalPicardLimitBddProducer (patchedSource)
open ShenWork.IntervalPicardIterateBddRepr
  (picardIterateRestart_general_of_sourceBdd
   cosineCoeffs_halfstep_eq_iterateCoeff_of_sourceBdd)
open ShenWork.Paper2 (cosineCoeffs_congr_on_Icc)

noncomputable section

namespace ShenWork.IntervalPicardWindowAdot

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-- Forget a closed-window `TimeC1On` source to the weak On package used by the
restart representation lemmas. -/
def sourceTimeC1On_to_l1ContOn {a : ℝ → ℕ → ℝ} {T : ℝ}
    (src : DuhamelSourceTimeC1On a 0 T) :
    DuhamelSourceL1ContOn a T where
  envelope := src.envelope
  henv_summable := src.henv_summable
  henv_bound := fun s hs hsT n => src.henv_bound s ⟨hs, hsT⟩ n
  hcont := fun n => by
    intro s hs
    exact (src.hderiv s hs n).continuousWithinAt

/-- `ℓ¹` summability of iterate coefficients from a closed-window source package. -/
theorem summable_abs_iterateCoeff_timeC1On
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    {M₀ T : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (src : DuhamelSourceTimeC1On
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k) 0 T)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    Summable (fun k => |iterateCoeff p u₀ n t k|) := by
  have srcL := sourceTimeC1On_to_l1ContOn src
  have hM0 : 0 ≤ M₀ := le_trans (abs_nonneg _) (hu₀_bound 0)
  have hhom : Summable (fun k =>
      |Real.exp (-t * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k|) := by
    refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
      ((expEigSummable ht).mul_right M₀)
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hu₀_bound k) (Real.exp_pos _).le
  have hduh : Summable (fun k =>
      |duhamelSpectralCoeff
          (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
          t k|) := by
    refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
      (srcL.henv_summable.mul_left t)
    exact abs_duhamelSpectralCoeff_le_weak srcL ht htT k
  refine (hhom.add hduh).of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
  unfold iterateCoeff
  exact abs_add_le _ _

/-- Source-subtype iterate representation driven by a closed-window source package. -/
theorem iterate_lift_eq_cosineSeries_of_sourceTimeC1On
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    (hu₀_cont : Continuous u₀)
    {M₀ T : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (src : DuhamelSourceTimeC1On
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k) 0 T)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T)
    (hLs_cont : ∀ s, 0 < s → s ≤ t →
      Continuous (intervalLogisticSource p (picardIter p u₀ n s)))
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalDomainLift (picardIter p u₀ (n + 1) t) x
      = ∑' k, iterateCoeff p u₀ n t k * cosineMode k x := by
  have hlift : intervalDomainLift (picardIter p u₀ (n + 1) t) x
      = intervalGradientDuhamelMap p u₀ (picardIter p u₀ n) t ⟨x, hx⟩ := by
    change (if hx' : x ∈ Set.Icc (0 : ℝ) 1 then
          picardIter p u₀ (n + 1) t ⟨x, hx'⟩ else 0) = _
    rw [dif_pos hx]
    rfl
  rw [hlift, intervalGradientDuhamelMap_eq_of_chi0_zero p hχ0 u₀ _ t ⟨x, hx⟩]
  have hhom : intervalFullSemigroupOperator t (intervalDomainLift u₀) x
      = ∑' k, (Real.exp (-t * (λ_ k))
          * cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k x := by
    rw [intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
          ht hu₀_cont hu₀_bound hx]
    exact heatValue_eq_cosineSeries t _ x
  set a : ℝ → ℕ → ℝ := fun s k =>
    cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k with ha
  have srcL : DuhamelSourceL1ContOn a T := by
    rw [ha]
    exact sourceTimeC1On_to_l1ContOn src
  have hTnn : 0 ≤ T := le_trans ht.le htT
  have hnn : ∀ j, 0 ≤ src.envelope j := fun j =>
    le_trans (abs_nonneg _) (src.henv_bound 0 ⟨le_rfl, hTnn⟩ j)
  have hMa : ∀ s, 0 ≤ s → s ≤ T → ∀ k, |a s k| ≤ ∑' j, src.envelope j := by
    intro s hs hsT k
    refine le_trans (src.henv_bound s ⟨hs, hsT⟩ k) ?_
    have := src.henv_summable.sum_le_tsum {k} (fun j _ => hnn j)
    simpa using this
  have hduh_integrand : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      intervalFullSemigroupOperator (t - s) (logisticLifted p (picardIter p u₀ n s)) x
        = unitIntervalCosineHeatValue (t - s) (a s) x := by
    intro s hs
    have hts : 0 < t - s := by linarith [hs.2]
    have hcont : Continuous (intervalLogisticSource p (picardIter p u₀ n s)) :=
      hLs_cont s hs.1 (le_of_lt hs.2)
    have hMs : ∀ k, |cosineCoeffs
        (intervalDomainLift (intervalLogisticSource p (picardIter p u₀ n s))) k|
        ≤ ∑' j, src.envelope j := fun k =>
      hMa s (le_of_lt hs.1) (le_trans (le_of_lt hs.2) htT) k
    have hsub := intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
      (f := intervalLogisticSource p (picardIter p u₀ n s)) hts hcont hMs hx
    simpa [ha] using hsub
  have hduh_eq : (∫ s in (0 : ℝ)..t,
        intervalFullSemigroupOperator (t - s) (logisticLifted p (picardIter p u₀ n s)) x)
      = ∫ s in (0 : ℝ)..t, unitIntervalCosineHeatValue (t - s) (a s) x := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [Set.uIoc_of_le ht.le]
    have hmem : ∀ᵐ s ∂volume, s ∈ Set.Ioc (0 : ℝ) t → s ∈ Set.Ioo (0 : ℝ) t := by
      have hnull : volume ({t} : Set ℝ) = 0 := by simp
      filter_upwards [(MeasureTheory.compl_mem_ae_iff.mpr hnull)] with s hs hsmem
      refine ⟨hsmem.1, lt_of_le_of_ne hsmem.2 ?_⟩
      intro hst
      exact hs (by simp [hst])
    filter_upwards [hmem] with s hs hsIoc
    exact hduh_integrand s (hs hsIoc)
  rw [hhom, hduh_eq, duhamelSpectral_eq_cosineSeries_weak srcL ht htT]
  have hcosbd : ∀ (c : ℕ → ℝ) (k : ℕ), ‖c k * cosineMode k x‖ ≤ |c k| := by
    intro c k
    rw [Real.norm_eq_abs, abs_mul]
    calc |c k| * |cosineMode k x| ≤ |c k| * 1 := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          simpa [cosineMode] using Real.abs_cos_le_one ((k : ℝ) * Real.pi * x)
      _ = |c k| := mul_one _
  have hsum_hom : Summable (fun k =>
      (Real.exp (-t * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k)
        * cosineMode k x) := by
    refine Summable.of_norm_bounded ?_ (hcosbd _)
    refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
      ((expEigSummable ht).mul_right M₀)
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hu₀_bound k) (Real.exp_pos _).le
  have hsum_duh : Summable (fun k =>
      duhamelSpectralCoeff a t k * cosineMode k x) := by
    refine Summable.of_norm_bounded ?_ (hcosbd _)
    refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
      (srcL.henv_summable.mul_left t)
    exact abs_duhamelSpectralCoeff_le_weak srcL ht htT k
  rw [← Summable.tsum_add hsum_hom hsum_duh]
  refine tsum_congr (fun k => ?_)
  unfold iterateCoeff
  rw [ha]
  ring

/-- Source-subtype coefficient extraction from a closed-window source package. -/
theorem cosineCoeffs_halfstep_eq_iterateCoeff_of_sourceTimeC1On
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    (hu₀_cont : Continuous u₀)
    {M₀ T : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (src : DuhamelSourceTimeC1On
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k) 0 T)
    {τ : ℝ} (hτ : 0 < τ) (hτT : τ ≤ T)
    (hLs_cont : ∀ s, 0 < s → s ≤ τ →
      Continuous (intervalLogisticSource p (picardIter p u₀ n s)))
    (k : ℕ) :
    cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) τ)) k
      = iterateCoeff p u₀ n τ k := by
  have hrepr : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (picardIter p u₀ (n + 1) τ) x
        = ∑' j, iterateCoeff p u₀ n τ j * cosineMode j x := fun x hx =>
    iterate_lift_eq_cosineSeries_of_sourceTimeC1On p hχ0 u₀ n hu₀_cont
      hu₀_bound src hτ hτT hLs_cont hx
  rw [cosineCoeffs_congr_on_Icc hrepr k]
  exact cosineCoeffs_of_l1_cosineSeries
    (summable_abs_iterateCoeff_timeC1On p u₀ n hu₀_bound src hτ hτT) k

/-- General-offset iterate restart identity from a closed-window source package. -/
theorem picardIterateRestart_general_on
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    (hu₀_cont : Continuous u₀)
    {M₀ T : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (src : DuhamelSourceTimeC1On
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k) 0 T)
    {τ s : ℝ} (hτ : 0 < τ) (hτs : τ < s) (hsT : s ≤ T)
    (hLs_cont : ∀ r, 0 < r → r ≤ s →
      Continuous (intervalLogisticSource p (picardIter p u₀ n r))) :
    Set.EqOn (intervalDomainLift (picardIter p u₀ (n + 1) s))
      (fun x => ∑' k,
        localRestartCoeff
          (cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) τ)))
          (fun σ k => cosineCoeffs (logisticLifted p (picardIter p u₀ n (τ + σ))) k)
          (s - τ) k * cosineMode k x)
      (Set.Icc (0 : ℝ) 1) := by
  have hs : 0 < s := lt_trans hτ hτs
  have srcL := sourceTimeC1On_to_l1ContOn src
  intro x hx
  rw [iterate_lift_eq_cosineSeries_of_sourceTimeC1On p hχ0 u₀ n hu₀_cont
        hu₀_bound src hs hsT hLs_cont hx]
  refine tsum_congr (fun k => ?_)
  congr 1
  have hbase : cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) τ)) k
      = iterateCoeff p u₀ n τ k :=
    cosineCoeffs_halfstep_eq_iterateCoeff_of_sourceTimeC1On p hχ0 u₀ n hu₀_cont
      hu₀_bound src hτ (le_trans hτs.le hsT)
      (fun r hr hrτ => hLs_cont r hr (le_trans hrτ hτs.le)) k
  unfold iterateCoeff localRestartCoeff
  rw [hbase]
  unfold iterateCoeff
  have hsplit := duhamelSpectralCoeff_general_split_on
    (a := fun r k => cosineCoeffs (logisticLifted p (picardIter p u₀ n r)) k)
    srcL.hcont hτ.le hτs.le hsT k
  have hexp : Real.exp (-s * (λ_ k))
      = Real.exp (-(s - τ) * (λ_ k)) * Real.exp (-τ * (λ_ k)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp, hsplit]
  ring

/-- `windowAdotLegs_step` with from-zero representation driven by the patched
bounded source on `[0,T]`. -/
theorem windowAdotLegs_step_on
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    {M T A₂ : ℝ}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hMnn : 0 ≤ M) (hA₂nn : 0 ≤ A₂)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M)
    (hsrc0_n : DuhamelSourceBddOn
      (patchedSource p u₀ (picardIter p u₀ n)) T)
    (hLs_cont : ∀ r, 0 < r → r ≤ T →
      Continuous (intervalLogisticSource p (picardIter p u₀ n r)))
    (hrepr_sum : ∀ σ, 0 < σ → σ ≤ T →
      Summable (fun k => unitIntervalCosineEigenvalue k * |iterateReprCoeff p u₀ n σ k|))
    (hrepr_agree : ∀ σ, 0 < σ → σ ≤ T →
      Set.EqOn (intervalDomainLift (picardIter p u₀ n σ))
        (fun x => ∑' k, iterateReprCoeff p u₀ n σ k * cosineMode k x)
        (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ σ, 0 < σ → σ ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (picardIter p u₀ n σ) x)
    (hub : ∀ σ, 0 < σ → σ ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (picardIter p u₀ n σ) x ≤ M)
    (hG1 : ∀ σ, 0 < σ → σ ≤ T → ∀ x : ℝ,
      |deriv (intervalDomainLift (picardIter p u₀ n σ)) x|
        ≤ ShenWork.IntervalPicardIterateUniform.G1profile p M σ)
    (hG2 : ∀ σ, 0 < σ → σ ≤ T → ∀ x : ℝ,
      |deriv (deriv (intervalDomainLift (picardIter p u₀ n σ))) x|
        ≤ ShenWork.IntervalPicardIterateUniform.G2profile A₂ σ)
    (hpos1 : ∀ σ, 0 < σ → σ ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (picardIter p u₀ (n + 1) σ) x)
    (hub1 : ∀ σ, 0 < σ → σ ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (picardIter p u₀ (n + 1) σ) x ≤ M)
    (hcontSlice1 : ∀ σ, 0 < σ → σ ≤ T →
      ContinuousOn (intervalDomainLift (picardIter p u₀ (n + 1) σ))
        (Set.Icc (0 : ℝ) 1))
    (prev : ∀ c' d', 0 < c' → c' ≤ d' → d' < T → WindowAdotLegs p u₀ n c' d') :
    ∀ lo hi, 0 < lo → lo ≤ hi → hi < T → WindowAdotLegs p u₀ (n + 1) lo hi := by
  intro lo hi hlo hlohi hhiT
  classical
  set τ : ℝ := lo / 2 with hτdef
  set c' : ℝ := lo / 4 with hc'def
  set d : ℝ := (hi + T) / 2 with hddef
  set d' : ℝ := (hi + 3 * T) / 4 with hd'def
  set t₁ : ℝ := 3 * lo / 4 with ht₁def
  have hτpos : 0 < τ := by rw [hτdef]; linarith
  have hc'pos : 0 < c' := by rw [hc'def]; linarith
  have hc'τ : c' < τ := by rw [hc'def, hτdef]; linarith
  have hcd : τ ≤ d := by rw [hτdef, hddef]; linarith
  have hdd' : d < d' := by rw [hddef, hd'def]; linarith
  have hd'Tlt : d' < T := by rw [hd'def]; linarith
  have hd'T : d' ≤ T := le_of_lt hd'Tlt
  have hc'd' : c' ≤ d' := le_of_lt (lt_trans hc'τ (lt_of_le_of_lt hcd hdd'))
  have hτt₁ : τ < t₁ := by rw [hτdef, ht₁def]; linarith
  have ht₁lo : t₁ < lo := by rw [ht₁def]; linarith
  have ht₁pos : 0 < t₁ := lt_trans hτpos hτt₁
  have hhid : hi < d := by rw [hddef]; linarith
  have ht₁d : t₁ ≤ d := le_of_lt (lt_trans ht₁lo (lt_of_le_of_lt hlohi hhid))
  have hcd'_pos : ∀ σ ∈ Set.Icc c' d', 0 < σ := fun σ hσ => lt_of_lt_of_le hc'pos hσ.1
  have hcd'_T : ∀ σ ∈ Set.Icc c' d', σ ≤ T := fun σ hσ => le_trans hσ.2 hd'T
  set G1s : ℝ := ShenWork.IntervalPicardWdataAssembly.G1win p M c' d' with hG1sdef
  set G2s : ℝ := ShenWork.IntervalPicardWdataAssembly.G2win A₂ c' with hG2sdef
  have hG1w : ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (picardIter p u₀ n σ)) x| ≤ G1s := by
    intro σ hσ x _hx
    exact le_trans (hG1 σ (hcd'_pos σ hσ) (hcd'_T σ hσ) x)
      (ShenWork.IntervalPicardWdataAssembly.G1profile_le_G1win hMnn hc'pos hσ.1 hσ.2)
  have hG2w : ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (picardIter p u₀ n σ))) x| ≤ G2s := by
    intro σ hσ x _hx
    exact le_trans (hG2 σ (hcd'_pos σ hσ) (hcd'_T σ hσ) x)
      (ShenWork.IntervalPicardWdataAssembly.G2profile_le_G2win hA₂nn hc'pos hσ.1)
  obtain ⟨adotn, hadotn_deriv, ⟨Mdotn, hadotn_bound⟩, hadotn_cont⟩ :=
    prev c' d' hc'pos hc'd' hd'Tlt
  have hbsumW : ∀ σ ∈ Set.Icc c' d',
      Summable (fun k => unitIntervalCosineEigenvalue k * |iterateReprCoeff p u₀ n σ k|) :=
    fun σ hσ => hrepr_sum σ (hcd'_pos σ hσ) (hcd'_T σ hσ)
  have hagreeW : ∀ σ ∈ Set.Icc c' d',
      Set.EqOn (intervalDomainLift (picardIter p u₀ n σ))
        (fun x => ∑' k, iterateReprCoeff p u₀ n σ k * cosineMode k x)
        (Set.Icc (0 : ℝ) 1) :=
    fun σ hσ => hrepr_agree σ (hcd'_pos σ hσ) (hcd'_T σ hσ)
  have hposW : ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (picardIter p u₀ n σ) x :=
    fun σ hσ x hx => hpos σ (hcd'_pos σ hσ) (hcd'_T σ hσ) x hx
  have hubW : ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (picardIter p u₀ n σ) x ≤ M :=
    fun σ hσ x hx => hub σ (hcd'_pos σ hσ) (hcd'_T σ hσ) x hx
  set aC : ℝ → ℕ → ℝ := fun σ k => cosineCoeffs (logisticSourceFun p.a p.b p.α
      (intervalDomainLift (picardIter p u₀ n (φ c' τ d d' (τ + σ))))) k with haCdef
  have srcC : ShenWork.IntervalDuhamelClosedC2.DuhamelSourceTimeC1 aC :=
    ShenWork.Paper2.ClampedSourceRepresentation.clampedSource_duhamelSourceTimeC1
      p (picardIter p u₀ n) hα ha hb
      (τ := τ) (c' := c') (c := τ) (d := d) (d' := d') hc'τ hcd hdd'
      (iterateReprCoeff p u₀ n) hbsumW hagreeW hposW hubW hG1w hG2w
      adotn hadotn_deriv hadotn_cont hadotn_bound
  set U : Set ℝ := Set.Ioo t₁ d with hUdef
  have hU_open : IsOpen U := isOpen_Ioo
  have hU_sub : U ⊆ Set.Ioo t₁ d := le_refl _
  have hU_off : U ⊆ Set.Ioi τ := fun s hs => lt_trans hτt₁ hs.1
  have hUmem : ∀ s ∈ U, 0 < s ∧ s ≤ T := fun s hs =>
    ⟨lt_trans ht₁pos hs.1, le_of_lt (lt_of_lt_of_le hs.2 (hdd'.le.trans hd'T))⟩
  have hsubLoHi : Set.Icc lo hi ⊆ U := fun s hs =>
    ⟨lt_of_lt_of_le ht₁lo hs.1, lt_of_le_of_lt hs.2 hhid⟩
  set a₀ : ℕ → ℝ := cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) τ))
    with ha₀def
  have hcontC : ∀ k, Continuous (fun s => aC s k) := fun k =>
    continuous_iff_continuousAt.2 (fun s => (srcC.hderiv s k).continuousAt)
  have hTpos : 0 < T := lt_of_lt_of_le hτpos (hcd.trans (hdd'.le.trans hd'T))
  have hG1s_nn : 0 ≤ G1s :=
    ShenWork.IntervalPicardWdataAssembly.G1win_nonneg hMnn hc'pos (le_trans hc'pos.le hc'd')
  have hG2s_nn : 0 ≤ G2s :=
    ShenWork.IntervalPicardWdataAssembly.G2win_nonneg hA₂nn hc'pos
  set Bwin : ℝ :=
    ShenWork.IntervalPicardWeightedC2Bootstrap.windowSourceConst p M G1s G2s with hBwindef
  have hBwin_nn : 0 ≤ Bwin :=
    ShenWork.IntervalPicardWeightedC2Bootstrap.windowSourceConst_nonneg p hα hMnn
      hG1s_nn hG2s_nn
  have hdecay : ∀ s, 0 ≤ s → ∀ k : ℕ, 1 ≤ k →
      |aC s k| ≤ 2 * (Bwin / 2) / ((k : ℝ) * Real.pi) ^ 2 := by
    intro s _hs k hk
    rw [show (2 : ℝ) * (Bwin / 2) = Bwin by ring]
    have hΦmem : φ c' τ d d' (τ + s) ∈ Set.Icc c' d' :=
      φ_mem_range hc'τ hcd hdd' (τ + s)
    set σΦ := φ c' τ d d' (τ + s) with hσΦdef
    have hdec := ShenWork.IntervalPicardWeightedC2Bootstrap.slice_source_coeff_decay
      p (M := M) (G1 := G1s) (G2 := G2s) hα
      (iterateReprCoeff p u₀ n σΦ) (hbsumW σΦ hΦmem) (hagreeW σΦ hΦmem)
      (hposW σΦ hΦmem) (hubW σΦ hΦmem)
      (fun x hx => hG1w σΦ hΦmem x hx) (fun x hx => hG2w σΦ hΦmem x hx) k hk
    exact hdec
  have hagreeU : ∀ s ∈ U, ∀ x : intervalDomainPoint,
      intervalDomainLift (picardIter p u₀ (n + 1) s) x.1
        = ∑' k, localRestartCoeff a₀ aC (s - τ) k * cosineMode k x.1 := by
    intro s hs x
    have hsmem := hUmem s hs
    have hτs : τ < s := lt_trans hτt₁ hs.1
    have hsd : s < d := hs.2
    have hx : x.1 ∈ Set.Icc (0 : ℝ) 1 := x.2
    have hgen := picardIterateRestart_general_of_sourceBdd p hχ0 u₀ n hu₀_cont hu₀_bound
      hsrc0_n hτpos hτs hsmem.2
      (fun r hr hrs => hLs_cont r hr (le_trans hrs hsmem.2)) hx
    rw [hgen]
    refine tsum_congr (fun k => ?_)
    congr 1
    refine localRestartCoeff_congr_on_Icc (by linarith) (fun σ hσ m => ?_) k
    have hmem_cd : τ + σ ∈ Set.Icc τ d :=
      ⟨by linarith [hσ.1], by linarith [hσ.2, hsd.le]⟩
    change cosineCoeffs (logisticLifted p (picardIter p u₀ n (τ + σ))) m = aC σ m
    rw [haCdef]
    simp only
    rw [ShenWork.IntervalTimeSoftClamp.φ_eq_id_on hc'τ hdd' hmem_cd]
    exact ShenWork.Paper2.cosineCoeffs_congr_on_Icc
      (ShenWork.IntervalMildPicardRegularity.logisticLifted_eq_logisticSourceFun_on_Icc
        p (picardIter p u₀ n (τ + σ))) m
  have ha₀_bound : ∀ k, |a₀ k| ≤ 2 * M := by
    intro k
    rw [ha₀def]
    have hgc : ContinuousOn (intervalDomainLift (picardIter p u₀ (n + 1) τ))
        (Set.Icc (0 : ℝ) 1) := hcontSlice1 τ hτpos (hcd.trans (hdd'.le.trans hd'T))
    have hbd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |intervalDomainLift (picardIter p u₀ (n + 1) τ) x| ≤ M := by
      intro x hx
      rw [abs_of_pos (hpos1 τ hτpos (hcd.trans (hdd'.le.trans hd'T)) x hx)]
      exact hub1 τ hτpos (hcd.trans (hdd'.le.trans hd'T)) x hx
    exact ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
      hgc hMnn hbd k
  have hposU : ∀ s ∈ U, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (picardIter p u₀ (n + 1) s) x :=
    fun s hs x hx => hpos1 s (hUmem s hs).1 (hUmem s hs).2 x hx
  have hubU : ∀ s ∈ U, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (picardIter p u₀ (n + 1) s) x ≤ M :=
    fun s hs x hx => hub1 s (hUmem s hs).1 (hUmem s hs).2 x hx
  have hC2contU : ∀ s ∈ U,
      ContinuousOn (intervalDomainLift (picardIter p u₀ (n + 1) s)) (Set.Icc (0 : ℝ) 1) :=
    fun s hs => hcontSlice1 s (hUmem s hs).1 (hUmem s hs).2
  obtain ⟨hderiv, hbound, hcont⟩ :=
    picardIterate_K1_full_from_restart_of_representation
      (p := p) (w := picardIter p u₀ (n + 1)) hα ha hb
      (M₀ := 2 * M) (by linarith) ha₀_bound
      srcC (B := Bwin / 2) (by linarith)
      hdecay hcontC
      (offset := τ) (t₁ := t₁) (t₂ := d) hτt₁ ht₁d
      hU_open hU_sub hU_off hagreeU (M := M) hposU hubU hC2contU
  refine ⟨fun σ k => cosineCoeffs
      (fun x => logisticSourceDot a₀ aC p (picardIter p u₀ (n + 1)) τ σ x) k, ?_, ?_, ?_⟩
  · intro σ hσ k
    exact hderiv σ (hsubLoHi hσ) k
  · refine ⟨_, fun σ hσ k => hbound σ (hsubLoHi hσ) k⟩
  · intro k
    exact (hcont k).mono hsubLoHi

end ShenWork.IntervalPicardWindowAdot
