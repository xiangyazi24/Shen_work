/-
Green/ODE regularity bridge: continuous source → R' has derivative μR - ρ(u).

Uses the integrated weak ODE identity (spectral weak equation + Parseval) and
Mathlib's FTC (integral_hasDerivAt_right) to bypass termwise differentiation
of the gradient series (which would require ∑|c_k|(kπ)² < ∞).

Source: ChatGPT Q3970 (green_ode_bridge) + Q3971 (continuity).
-/
import ShenWork.Paper2.IntervalResolverWeakLapBound
import ShenWork.Paper2.IntervalMildPicardRegularity
import ShenWork.Paper2.IntervalDuhamelIntegrability
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Normed.Group.FunctionSeries

open MeasureTheory intervalIntegral
open ShenWork.IntervalDomain
open ShenWork.PDE
open ShenWork.Paper2
open ShenWork.IntervalResolverWeakBounds
open ShenWork.HeatKernelGradientEstimates
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open scoped Topology BigOperators ENNReal

noncomputable section

namespace ShenWork.IntervalResolverWeakBounds

/-! ### Continuity infrastructure (from IntervalResolverContinuity, inlined) -/

def resolverValueSeriesReal (p : CM2Params)
    (u : intervalDomainPoint → ℝ) : ℝ → ℝ :=
  fun z => ∑' k : ℕ,
    (intervalNeumannResolverCoeff p u k).re * unitIntervalCosineMode k z

def resolverPhysicalSourceReal (p : CM2Params)
    (u : intervalDomainPoint → ℝ) : ℝ → ℝ :=
  fun z => p.ν * (positivePart (intervalDomainLift u z)) ^ p.γ

def resolverLapPhysicalPlain (p : CM2Params)
    (u : intervalDomainPoint → ℝ) : ℝ → ℝ :=
  fun z => p.μ * resolverValueSeriesReal p u z - resolverPhysicalSourceReal p u z

private theorem resolverPhysicalSourceReal_continuousOn
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (resolverPhysicalSourceReal p u) (Set.Icc (0 : ℝ) 1) := by
  have hpp :
      ContinuousOn (fun z : ℝ => positivePart (intervalDomainLift u z))
        (Set.Icc (0 : ℝ) 1) := by
    simpa [positivePart] using
      ContinuousOn.sup hUcont
        (continuousOn_const :
          ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Set.Icc 0 1))
  have hpow :
      ContinuousOn
        (fun z : ℝ => (positivePart (intervalDomainLift u z)) ^ p.γ)
        (Set.Icc (0 : ℝ) 1) :=
    hpp.rpow_const (fun z hz => Or.inr p.hγ.le)
  simpa [resolverPhysicalSourceReal] using continuousOn_const.mul hpow

private theorem resolverCoeff_re_abs_summable_of_continuousOn
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1)) :
    Summable fun k : ℕ => |(intervalNeumannResolverCoeff p u k).re| := by
  have hsrcL2 :
      Summable fun k : ℕ => ((intervalNeumannResolverSourceCoeff p u k).re) ^ 2 := by
    simpa [ShenWork.Paper2.intervalNeumannResolverSourceCoeff_zero] using
      resolverSourceCoeff_re_sq_summable_of_continuousOn p hUcont
  have hseries0 :
      Summable fun k : ℕ =>
        (intervalNeumannResolverCoeff p u k).re * unitIntervalCosineMode k (0 : ℝ) :=
    resolver_cosineSeries_summable_of_sourceL2 p hsrcL2 0
  simpa [unitIntervalCosineMode, Real.norm_eq_abs] using hseries0.norm

private theorem resolverValueSeriesReal_continuous_of_continuousOn
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1)) :
    Continuous (resolverValueSeriesReal p u) := by
  classical
  let c : ℕ → ℝ := fun k => (intervalNeumannResolverCoeff p u k).re
  let f : ℕ → ℝ → ℝ := fun k z => c k * unitIntervalCosineMode k z
  let M' : ℕ → ℝ := fun k => |c k|
  have hM : Summable M' :=
    resolverCoeff_re_abs_summable_of_continuousOn p hUcont
  have hf : ∀ k : ℕ, Continuous (f k) := by
    intro k; dsimp [f, c]
    unfold unitIntervalCosineMode; fun_prop
  have hbound : ∀ k z, ‖f k z‖ ≤ M' k := by
    intro k z; dsimp [f, M', c]
    have hcos : |unitIntervalCosineMode k z| ≤ 1 := by
      unfold unitIntervalCosineMode; exact Real.abs_cos_le_one _
    calc ‖(intervalNeumannResolverCoeff p u k).re * unitIntervalCosineMode k z‖
        = |(intervalNeumannResolverCoeff p u k).re| * |unitIntervalCosineMode k z| := by
            rw [Real.norm_eq_abs, abs_mul]
      _ ≤ |(intervalNeumannResolverCoeff p u k).re| * 1 :=
          mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
      _ = |(intervalNeumannResolverCoeff p u k).re| := by ring
  simpa [resolverValueSeriesReal, f, c] using continuous_tsum hf hM hbound

private theorem resolverLapPhysicalPlain_continuousAt_of_continuousOn
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    ContinuousAt (resolverLapPhysicalPlain p u) x := by
  have hR : ContinuousAt (resolverValueSeriesReal p u) x :=
    (resolverValueSeriesReal_continuous_of_continuousOn p hUcont).continuousAt
  have hS : ContinuousAt (resolverPhysicalSourceReal p u) x := by
    have hsrc_on := resolverPhysicalSourceReal_continuousOn p hUcont
    have hIcc_nhds : Set.Icc (0 : ℝ) 1 ∈ 𝓝 x :=
      Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Ioo hx) Set.Ioo_subset_Icc_self
    exact hsrc_on.continuousAt hIcc_nhds
  simpa [resolverLapPhysicalPlain] using (hR.const_mul p.μ).sub hS

/-! ### Physical Laplacian (piecewise) and its continuity -/

def resolverLapPhysicalReal (p : CM2Params)
    (u : intervalDomainPoint → ℝ) (x : ℝ) : ℝ :=
  if hx : x ∈ Set.Icc (0 : ℝ) 1 then
    resolverLapPhysical p u ⟨x, hx⟩
  else
    0

theorem resolverLapPhysicalReal_continuousAt_of_continuousOn
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    ContinuousAt (resolverLapPhysicalReal p u) x := by
  have hplain : ContinuousAt (resolverLapPhysicalPlain p u) x :=
    resolverLapPhysicalPlain_continuousAt_of_continuousOn p hUcont hx
  have hIoo_nhds : Set.Ioo (0 : ℝ) 1 ∈ 𝓝 x :=
    IsOpen.mem_nhds isOpen_Ioo hx
  have hlocal :
      resolverLapPhysicalReal p u =ᶠ[𝓝 x] resolverLapPhysicalPlain p u := by
    filter_upwards [hIoo_nhds] with z hz
    have hzIcc : z ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hz
    simp [resolverLapPhysicalReal, resolverLapPhysicalPlain, resolverLapPhysical,
      resolverValueSeriesReal, resolverPhysicalSourceReal, resolverPositiveSourceLifted,
      intervalNeumannResolverR, unitIntervalCosineMode, hzIcc]
  exact hplain.congr_of_eventuallyEq hlocal

/-! ### Pairing helpers for the integrated ODE identity -/

private theorem intervalMeasure_one_integral_eq_intervalIntegral (f : ℝ → ℝ) :
    (∫ y, f y ∂ intervalMeasure 1) = ∫ y in (0 : ℝ)..1, f y := by
  simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
  change (∫ y in Set.Icc (0 : ℝ) 1, f y ∂volume) = ∫ y in (0 : ℝ)..1, f y
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]

private theorem intervalMeasure_one_integral_eq_intervalIntegral_complex
    (f : ℝ → ℂ) :
    (∫ y, f y ∂ intervalMeasure 1) = ∫ y in (0 : ℝ)..1, f y := by
  simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
  change (∫ y in Set.Icc (0 : ℝ) 1, f y ∂volume) = ∫ y in (0 : ℝ)..1, f y
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]

private lemma memLp_two_of_continuousOn_Icc
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) :
    MemLp f (2 : ℝ≥0∞) (intervalMeasure 1) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hfm : AEStronglyMeasurable f (intervalMeasure 1) :=
    ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
      hf
  refine MemLp.of_bound hfm C ?_
  unfold intervalMeasure ShenWork.IntervalDomain.intervalSet
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  simpa [Real.norm_eq_abs] using hC x hx

private lemma memLp_two_of_aestronglyMeasurable_bound_Icc
    {φ : ℝ → ℝ}
    (hφm : AEStronglyMeasurable φ (intervalMeasure 1))
    {Cφ : ℝ} (hφb : ∀ x ∈ Set.Icc (0 : ℝ) 1, |φ x| ≤ Cφ) :
    MemLp φ (2 : ℝ≥0∞) (intervalMeasure 1) := by
  refine MemLp.of_bound hφm Cφ ?_
  unfold intervalMeasure ShenWork.IntervalDomain.intervalSet
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  simpa [Real.norm_eq_abs] using hφb x hx

private def bridgeCosineTestCoeff (φ : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, unitIntervalCosineMode n x * φ x

private theorem bridge_integral_tsum_pairing
    {w ψ : ℝ → ℝ} {c B : ℕ → ℝ} {e : ℕ → ℝ → ℝ} {Cψ : ℝ}
    (he : ∀ n, Continuous (e n))
    (heB : ∀ n, ∀ x ∈ Set.Icc (0 : ℝ) 1, |e n x| ≤ B n)
    (hsum : Summable (fun n => |c n| * B n))
    (hrep : ∀ x ∈ Set.Icc (0 : ℝ) 1, w x = ∑' n, c n * e n x)
    (hψm : AEStronglyMeasurable ψ (intervalMeasure 1))
    (hψb : ∀ x ∈ Set.Icc (0 : ℝ) 1, |ψ x| ≤ Cψ) :
    (∫ x, w x * ψ x ∂ intervalMeasure 1)
      = ∑' n, c n * ∫ x in (0 : ℝ)..1, e n x * ψ x := by
  classical
  have h01 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    Set.left_mem_Icc.mpr (by norm_num)
  have hCψ : 0 ≤ Cψ :=
    le_trans (abs_nonneg _) (hψb 0 h01)
  set F : ℕ → ℝ → ℝ := fun n x => c n * (e n x * ψ x) with hF
  have hmemae : ∀ᵐ x ∂ intervalMeasure 1, x ∈ Set.Icc (0 : ℝ) 1 := by
    simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
    exact ae_restrict_mem measurableSet_Icc
  have hcong :
      (fun x => w x * ψ x) =ᵐ[intervalMeasure 1] fun x => ∑' n, F n x := by
    filter_upwards [hmemae] with x hx
    rw [hrep x hx, ← tsum_mul_right]
    exact tsum_congr fun n => by simp only [hF]; ring
  have hFm : ∀ n, AEStronglyMeasurable (F n) (intervalMeasure 1) := fun n =>
    (((he n).aestronglyMeasurable).mul hψm).const_mul (c n)
  have hBnn : ∀ n, 0 ≤ B n := fun n =>
    le_trans (abs_nonneg _) (heB n 0 h01)
  have hFbound : ∀ n, ∀ᵐ x ∂ intervalMeasure 1,
      ‖F n x‖ ≤ |c n| * B n * Cψ := by
    intro n
    filter_upwards [hmemae] with x hx
    have h1 : |e n x| ≤ B n := heB n x hx
    have h2 : |ψ x| ≤ Cψ := hψb x hx
    calc ‖F n x‖ = |c n| * (|e n x| * |ψ x|) := by
          rw [Real.norm_eq_abs]
          simp only [hF, abs_mul]
      _ ≤ |c n| * (B n * Cψ) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul h1 h2 (abs_nonneg _) (hBnn n)) (abs_nonneg _)
      _ = |c n| * B n * Cψ := by ring
  have hFint : ∀ n, Integrable (F n) (intervalMeasure 1) := fun n =>
    Integrable.mono' (integrable_const _) (hFm n) (hFbound n)
  have hμ : (intervalMeasure 1).real Set.univ = 1 := by
    rw [intervalMeasure, ShenWork.IntervalDomain.intervalSet,
      measureReal_restrict_apply_univ, measureReal_def, Real.volume_Icc]
    simp
  have hFsum : Summable (fun n => ∫ x, ‖F n x‖ ∂ intervalMeasure 1) := by
    refine Summable.of_nonneg_of_le
      (fun n => integral_nonneg fun x => norm_nonneg _)
      (fun n => ?_) (hsum.mul_right Cψ)
    calc ∫ x, ‖F n x‖ ∂ intervalMeasure 1
        ≤ ∫ _x, |c n| * B n * Cψ ∂ intervalMeasure 1 :=
          integral_mono_ae ((hFint n).norm) (integrable_const _) (hFbound n)
      _ = |c n| * B n * Cψ := by
          rw [MeasureTheory.integral_const, hμ]
          simp
  calc (∫ x, w x * ψ x ∂ intervalMeasure 1)
      = ∫ x, (∑' n, F n x) ∂ intervalMeasure 1 := integral_congr_ae hcong
    _ = ∑' n, ∫ x, F n x ∂ intervalMeasure 1 :=
        (integral_tsum_of_summable_integral_norm hFint hFsum).symm
    _ = ∑' n, c n * ∫ x in (0 : ℝ)..1, e n x * ψ x := by
        refine tsum_congr fun n => ?_
        simp only [hF]
        rw [MeasureTheory.integral_const_mul,
          intervalMeasure_one_integral_eq_intervalIntegral]

private theorem bridge_cosine_parseval_pairing
    {f φ : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hφm : AEStronglyMeasurable φ (intervalMeasure 1))
    {Cφ : ℝ} (hφb : ∀ x ∈ Set.Icc (0 : ℝ) 1, |φ x| ≤ Cφ) :
    Summable (fun n : ℕ => cosineCoeffs f n * bridgeCosineTestCoeff φ n) ∧
      (∑' n : ℕ, cosineCoeffs f n * bridgeCosineTestCoeff φ n)
        = ∫ x in (0 : ℝ)..1, f x * φ x := by
  classical
  have hFmemC :
      MemLp (fun x : ℝ => (f x : ℂ)) (2 : ℝ≥0∞) (intervalMeasure 1) :=
    (memLp_two_of_continuousOn_Icc hf).ofReal
  have hΦmemC :
      MemLp (fun x : ℝ => (φ x : ℂ)) (2 : ℝ≥0∞) (intervalMeasure 1) :=
    (memLp_two_of_aestronglyMeasurable_bound_Icc hφm hφb).ofReal
  let F : Lp ℂ 2 (intervalMeasure 1) :=
    hFmemC.toLp (fun x : ℝ => (f x : ℂ))
  let Φ : Lp ℂ 2 (intervalMeasure 1) :=
    hΦmemC.toLp (fun x : ℝ => (φ x : ℂ))
  have hFcoe :
      F =ᵐ[intervalMeasure 1] fun x : ℝ => (f x : ℂ) := by
    simpa [F] using
      MemLp.coeFn_toLp (μ := intervalMeasure 1)
        hFmemC
  have hΦcoe :
      Φ =ᵐ[intervalMeasure 1] fun x : ℝ => (φ x : ℂ) := by
    simpa [Φ] using
      MemLp.coeFn_toLp (μ := intervalMeasure 1)
        hΦmemC
  have hrawF : ∀ n : ℕ,
      inner ℂ (unitIntervalCosineLp n) F =
        ((∫ x in (0 : ℝ)..1,
          Real.cos ((n : ℝ) * Real.pi * x) * f x : ℝ) : ℂ) := by
    intro n
    rw [unitIntervalCosineLp_inner_eq_coeff]
    rw [← intervalMeasure_one_integral_eq_intervalIntegral_complex]
    calc
      (∫ x,
          (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * F x
          ∂ intervalMeasure 1)
          =
        ∫ x,
          (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * (f x : ℂ)
          ∂ intervalMeasure 1 := by
            exact integral_congr_ae
              (hFcoe.mono fun x hx => by
                simpa using congrArg
                  (fun z : ℂ =>
                    (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * z) hx)
      _ =
        ∫ x in (0 : ℝ)..1,
          (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * (f x : ℂ) := by
            exact intervalMeasure_one_integral_eq_intervalIntegral_complex _
      _ = ((∫ x in (0 : ℝ)..1,
          Real.cos ((n : ℝ) * Real.pi * x) * f x : ℝ) : ℂ) := by
            rw [← intervalIntegral.integral_ofReal]
            congr 1
            funext x
            simp
  have hrawΦ : ∀ n : ℕ,
      inner ℂ (unitIntervalCosineLp n) Φ =
        ((bridgeCosineTestCoeff φ n : ℝ) : ℂ) := by
    intro n
    rw [unitIntervalCosineLp_inner_eq_coeff]
    rw [← intervalMeasure_one_integral_eq_intervalIntegral_complex]
    calc
      (∫ x,
          (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * Φ x
          ∂ intervalMeasure 1)
          =
        ∫ x,
          (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * (φ x : ℂ)
          ∂ intervalMeasure 1 := by
            exact integral_congr_ae
              (hΦcoe.mono fun x hx => by
                simpa using congrArg
                  (fun z : ℂ =>
                    (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * z) hx)
      _ =
        ∫ x in (0 : ℝ)..1,
          (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * (φ x : ℂ) := by
            exact intervalMeasure_one_integral_eq_intervalIntegral_complex _
      _ = ((bridgeCosineTestCoeff φ n : ℝ) : ℂ) := by
            rw [bridgeCosineTestCoeff]
            rw [← intervalIntegral.integral_ofReal]
            congr 1
            funext x
            simp [unitIntervalCosineMode]
  have hrawF_right : ∀ n : ℕ,
      inner ℂ F (unitIntervalCosineLp n) =
        ((∫ x in (0 : ℝ)..1,
          Real.cos ((n : ℝ) * Real.pi * x) * f x : ℝ) : ℂ) := by
    intro n
    rw [← inner_conj_symm, hrawF n]
    simp
  have hterm : ∀ n : ℕ,
      inner ℂ F (unitIntervalNormalizedCosineLp n) *
          inner ℂ (unitIntervalNormalizedCosineLp n) Φ
        =
      ((cosineCoeffs f n * bridgeCosineTestCoeff φ n : ℝ) : ℂ) := by
    intro n
    by_cases hn : n = 0
    · subst n
      rw [show unitIntervalNormalizedCosineLp 0 = unitIntervalCosineLp 0 by
        simp [unitIntervalNormalizedCosineLp]]
      rw [hrawF_right 0, hrawΦ 0,
        ShenWork.IntervalMildPicardRegularity.cosineCoeffs_zero_eq_integral]
      simp [bridgeCosineTestCoeff, unitIntervalCosineMode]
    · have hnorm :
        unitIntervalNormalizedCosineLp n =
          (Real.sqrt 2 : ℂ) • unitIntervalCosineLp n := by
          simp [unitIntervalNormalizedCosineLp, hn]
      rw [hnorm, inner_smul_right, inner_smul_left, hrawF_right n, hrawΦ n]
      rw [ShenWork.IntervalMildPicardRegularity.cosineCoeffs_pos_eq_integral hn]
      simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
      set A : ℂ :=
        ((∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * f x : ℝ) : ℂ)
      set B : ℂ := ((bridgeCosineTestCoeff φ n : ℝ) : ℂ)
      change (Real.sqrt 2 : ℂ) * A *
          ((starRingEnd ℂ) (Real.sqrt 2 : ℂ) * B) =
        2 * A * B
      have hsqrt_star :
          (starRingEnd ℂ) (Real.sqrt 2 : ℂ) = (Real.sqrt 2 : ℂ) := by
        simp
      have hsqrt_sq_complex : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
        norm_num [← Complex.ofReal_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      rw [hsqrt_star]
      calc
        (Real.sqrt 2 : ℂ) * A * ((Real.sqrt 2 : ℂ) * B)
            = ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) * (A * B) := by ring
        _ = 2 * (A * B) := by rw [hsqrt_sq_complex]
        _ = 2 * A * B := by ring
  have hinner :
      inner ℂ F Φ =
        ((∫ x in (0 : ℝ)..1, f x * φ x : ℝ) : ℂ) := by
    rw [L2.inner_def]
    calc
      (∫ x, inner ℂ (F x) (Φ x) ∂ intervalMeasure 1)
          =
        ∫ x, ((f x * φ x : ℝ) : ℂ) ∂ intervalMeasure 1 := by
          refine integral_congr_ae ?_
          filter_upwards [hFcoe, hΦcoe] with x hxF hxΦ
          rw [hxF, hxΦ]
          simp [RCLike.inner_apply]
          ring
      _ =
        ∫ x in (0 : ℝ)..1, ((f x * φ x : ℝ) : ℂ) := by
          exact intervalMeasure_one_integral_eq_intervalIntegral_complex _
      _ = ((∫ x in (0 : ℝ)..1, f x * φ x : ℝ) : ℂ) := by
          exact intervalIntegral.integral_ofReal
            (a := (0 : ℝ)) (b := 1) (μ := volume)
            (f := fun x : ℝ => f x * φ x)
  have hsumC :
      Summable fun n : ℕ =>
        ((cosineCoeffs f n * bridgeCosineTestCoeff φ n : ℝ) : ℂ) := by
    simpa [unitIntervalCosineHilbertBasis, hterm] using
      (unitIntervalCosineHilbertBasis.summable_inner_mul_inner F Φ)
  have htsumC :
      (∑' n : ℕ,
        ((cosineCoeffs f n * bridgeCosineTestCoeff φ n : ℝ) : ℂ))
        = ((∫ x in (0 : ℝ)..1, f x * φ x : ℝ) : ℂ) := by
    calc
      (∑' n : ℕ,
        ((cosineCoeffs f n * bridgeCosineTestCoeff φ n : ℝ) : ℂ))
          =
        ∑' n : ℕ,
          inner ℂ F (unitIntervalNormalizedCosineLp n) *
            inner ℂ (unitIntervalNormalizedCosineLp n) Φ := by
            exact tsum_congr fun n => (hterm n).symm
      _ = inner ℂ F Φ := by
          simpa [unitIntervalCosineHilbertBasis] using
            unitIntervalCosineHilbertBasis.tsum_inner_mul_inner F Φ
      _ = ((∫ x in (0 : ℝ)..1, f x * φ x : ℝ) : ℂ) := hinner
  constructor
  · exact Complex.summable_ofReal.mp hsumC
  · apply Complex.ofReal_injective
    rw [Complex.ofReal_tsum]
    exact htsumC

private lemma integral_intervalMeasure_mul_indicator_Ioc_eq_intervalIntegral_of_le
    {f : ℝ → ℝ} {a b : ℝ}
    (ha0 : 0 ≤ a) (hb1 : b ≤ 1) (hab : a ≤ b) :
    (∫ x, f x * (Set.Ioc a b).indicator (fun _ : ℝ => (1 : ℝ)) x
        ∂ intervalMeasure 1)
      = ∫ x in a..b, f x := by
  classical
  have hsub : Set.Ioc a b ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨ha0.trans hx.1.le, hx.2.trans hb1⟩
  have hmul :
      (fun x : ℝ => f x * (Set.Ioc a b).indicator (fun _ : ℝ => (1 : ℝ)) x)
        = (Set.Ioc a b).indicator f := by
    ext x
    by_cases hx : x ∈ Set.Ioc a b <;> simp [hx]
  have hinter :
      Set.Ioc a b ∩ Set.Icc (0 : ℝ) 1 = Set.Ioc a b :=
    Set.inter_eq_left.mpr hsub
  rw [hmul]
  rw [MeasureTheory.integral_indicator measurableSet_Ioc]
  rw [intervalIntegral.integral_of_le hab]
  simp [intervalMeasure, intervalSet, Measure.restrict_restrict, hinter]

private lemma integral_zero_one_mul_indicator_Ioc_eq_intervalIntegral_of_le
    {f : ℝ → ℝ} {a b : ℝ}
    (ha0 : 0 < a) (hb1 : b < 1) (hab : a ≤ b) :
    (∫ x in (0 : ℝ)..1,
        f x * (Set.Ioc a b).indicator (fun _ : ℝ => (1 : ℝ)) x)
      = ∫ x in a..b, f x := by
  classical
  have hsub : Set.Ioc a b ⊆ Set.Ioc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨lt_trans ha0 hx.1, hx.2.trans hb1.le⟩
  have hmul :
      (fun x : ℝ => f x * (Set.Ioc a b).indicator (fun _ : ℝ => (1 : ℝ)) x)
        = (Set.Ioc a b).indicator f := by
    ext x
    by_cases hx : x ∈ Set.Ioc a b <;> simp [hx]
  have hinter :
      Set.Ioc a b ∩ Set.Ioc (0 : ℝ) 1 = Set.Ioc a b :=
    Set.inter_eq_left.mpr hsub
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [hmul]
  rw [MeasureTheory.integral_indicator measurableSet_Ioc]
  rw [intervalIntegral.integral_of_le hab]
  simp [Measure.restrict_restrict, hinter]

private lemma unitIntervalCosineMode_intervalIntegral_abs_le_one_of_le
    (k : ℕ) {a b : ℝ} (ha0 : 0 ≤ a) (hb1 : b ≤ 1) (hab : a ≤ b) :
    |∫ x in a..b, unitIntervalCosineMode k x| ≤ 1 := by
  have hcont : Continuous fun x : ℝ => unitIntervalCosineMode k x := by
    unfold unitIntervalCosineMode
    fun_prop
  have hnorm_int :
      IntervalIntegrable (fun x : ℝ => ‖unitIntervalCosineMode k x‖) volume a b :=
    hcont.norm.intervalIntegrable a b
  have hnorm_le :=
    intervalIntegral.norm_integral_le_integral_norm
      (μ := volume) (f := fun x : ℝ => unitIntervalCosineMode k x) hab
  have hmono :
      (∫ x in a..b, ‖unitIntervalCosineMode k x‖)
        ≤ ∫ _x in a..b, (1 : ℝ) := by
    refine intervalIntegral.integral_mono_on hab hnorm_int
      intervalIntegral.intervalIntegrable_const ?_
    intro x _hx
    simpa [Real.norm_eq_abs, unitIntervalCosineMode] using
      Real.abs_cos_le_one ((k : ℝ) * Real.pi * x)
  have hlen : b - a ≤ 1 := by linarith
  have hconst :
      (∫ _x in a..b, (1 : ℝ)) ≤ 1 := by
    simpa [intervalIntegral.integral_of_le hab] using hlen
  have hmain : ‖∫ x in a..b, unitIntervalCosineMode k x‖ ≤ 1 :=
    hnorm_le.trans (hmono.trans hconst)
  simpa [Real.norm_eq_abs] using hmain

private lemma cosineCoeffs_congr_on_Icc
    {f g : ℝ → ℝ}
    (hfg : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x = g x) (k : ℕ) :
    cosineCoeffs f k = cosineCoeffs g k := by
  classical
  by_cases hk : k = 0
  · subst k
    rw [ShenWork.IntervalMildPicardRegularity.cosineCoeffs_zero_eq_integral,
      ShenWork.IntervalMildPicardRegularity.cosineCoeffs_zero_eq_integral]
    refine intervalIntegral.integral_congr ?_
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    exact hfg x hxIcc
  · rw [ShenWork.IntervalMildPicardRegularity.cosineCoeffs_pos_eq_integral hk,
      ShenWork.IntervalMildPicardRegularity.cosineCoeffs_pos_eq_integral hk]
    congr 1
    refine intervalIntegral.integral_congr ?_
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    change Real.cos ((k : ℝ) * Real.pi * x) * f x =
      Real.cos ((k : ℝ) * Real.pi * x) * g x
    rw [hfg x hxIcc]

private lemma resolverPhysicalSourceReal_eq_sourceBare_on_Icc
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hUnonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift u x) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      resolverPhysicalSourceReal p u x =
        p.ν * intervalDomainLift u x ^ p.γ := by
  intro x hx
  have hpp :
      positivePart (intervalDomainLift u x) = intervalDomainLift u x :=
    positivePart_eq_self_of_nonneg (hUnonneg x hx)
  simp [resolverPhysicalSourceReal, hpp]

private lemma resolverPhysicalSourceReal_cosineCoeff_eq
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hUnonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift u x)
    (k : ℕ) :
    cosineCoeffs (resolverPhysicalSourceReal p u) k =
      (intervalNeumannResolverSourceCoeff p u k).re := by
  calc
    cosineCoeffs (resolverPhysicalSourceReal p u) k
        = cosineCoeffs (fun x : ℝ => p.ν * intervalDomainLift u x ^ p.γ) k :=
          cosineCoeffs_congr_on_Icc
            (resolverPhysicalSourceReal_eq_sourceBare_on_Icc p hUnonneg) k
    _ = (intervalNeumannResolverSourceCoeff p u k).re := by
          simp [cosineCoeffs, intervalNeumannResolverSourceCoeff]

private theorem resolverValueSeriesReal_integral_tsum_of_le_bridge
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    {a b : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : b ∈ Set.Ioo (0 : ℝ) 1)
    (hab : a ≤ b) :
    Summable (fun k : ℕ =>
      (intervalNeumannResolverCoeff p u k).re *
        ∫ x in a..b, unitIntervalCosineMode k x) ∧
    (∫ x in a..b, resolverValueSeriesReal p u x)
      =
    ∑' k : ℕ,
      (intervalNeumannResolverCoeff p u k).re *
        ∫ x in a..b, unitIntervalCosineMode k x := by
  classical
  let C : ℕ → ℝ := fun k => (intervalNeumannResolverCoeff p u k).re
  let E : ℕ → ℝ → ℝ := fun k x => unitIntervalCosineMode k x
  let B : ℕ → ℝ := fun _ => (1 : ℝ)
  let ψ : ℝ → ℝ := (Set.Ioc a b).indicator (fun _ : ℝ => (1 : ℝ))
  have he : ∀ n : ℕ, Continuous (E n) := by
    intro n; dsimp [E]; unfold unitIntervalCosineMode; fun_prop
  have heB : ∀ n : ℕ, ∀ x ∈ Set.Icc (0 : ℝ) 1, |E n x| ≤ B n := by
    intro n x _
    dsimp [E, B]
    simpa [unitIntervalCosineMode] using Real.abs_cos_le_one ((n : ℝ) * Real.pi * x)
  have hsum : Summable (fun n : ℕ => |C n| * B n) := by
    simpa [B, C] using resolverCoeff_re_abs_summable_of_continuousOn p hUcont
  have hrep : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      resolverValueSeriesReal p u x = ∑' n : ℕ, C n * E n x := by
    intro x _; simp [resolverValueSeriesReal, C, E]
  have hψm : AEStronglyMeasurable ψ (intervalMeasure 1) := by
    exact ((measurable_const : Measurable (fun _ : ℝ => (1 : ℝ))).indicator
      measurableSet_Ioc).aestronglyMeasurable
  have hψb : ∀ x ∈ Set.Icc (0 : ℝ) 1, |ψ x| ≤ (1 : ℝ) := by
    intro x _; by_cases hxab : x ∈ Set.Ioc a b <;> simp [ψ, hxab]
  have hpair := bridge_integral_tsum_pairing
    (w := resolverValueSeriesReal p u) (ψ := ψ) (c := C) (B := B) (e := E) (Cψ := 1)
    he heB hsum hrep hψm hψb
  have hleft :
      (∫ x, resolverValueSeriesReal p u x * ψ x ∂ intervalMeasure 1)
        = ∫ x in a..b, resolverValueSeriesReal p u x := by
    simpa [ψ] using
      integral_intervalMeasure_mul_indicator_Ioc_eq_intervalIntegral_of_le
        (f := resolverValueSeriesReal p u) ha.1.le hb.2.le hab
  have hright :
      (∑' n : ℕ, C n * ∫ x in (0 : ℝ)..1, E n x * ψ x)
        = ∑' n : ℕ, C n * ∫ x in a..b, E n x := by
    apply tsum_congr; intro n; congr 1
    simpa [ψ, E] using
      integral_zero_one_mul_indicator_Ioc_eq_intervalIntegral_of_le
        (f := E n) ha.1 hb.2 hab
  have htermsum :
      Summable (fun k : ℕ =>
        (intervalNeumannResolverCoeff p u k).re *
          ∫ x in a..b, unitIntervalCosineMode k x) := by
    have hbase :
        Summable fun k : ℕ => |(intervalNeumannResolverCoeff p u k).re| :=
      resolverCoeff_re_abs_summable_of_continuousOn p hUcont
    refine Summable.of_norm_bounded hbase ?_
    intro k
    have hJ :
        |∫ x in a..b, unitIntervalCosineMode k x| ≤ 1 :=
      unitIntervalCosineMode_intervalIntegral_abs_le_one_of_le
        k ha.1.le hb.2.le hab
    calc
      ‖(intervalNeumannResolverCoeff p u k).re *
          ∫ x in a..b, unitIntervalCosineMode k x‖
          =
        |(intervalNeumannResolverCoeff p u k).re| *
          |∫ x in a..b, unitIntervalCosineMode k x| := by
            rw [Real.norm_eq_abs, abs_mul]
      _ ≤ |(intervalNeumannResolverCoeff p u k).re| * 1 :=
          mul_le_mul_of_nonneg_left hJ (abs_nonneg _)
      _ = |(intervalNeumannResolverCoeff p u k).re| := by ring
  refine ⟨htermsum, ?_⟩
  calc
    ∫ x in a..b, resolverValueSeriesReal p u x
        = ∫ x, resolverValueSeriesReal p u x * ψ x ∂ intervalMeasure 1 := hleft.symm
    _ = ∑' n : ℕ, C n * ∫ x in (0 : ℝ)..1, E n x * ψ x := hpair
    _ = ∑' n : ℕ, C n * ∫ x in a..b, E n x := hright
    _ = ∑' k : ℕ,
        (intervalNeumannResolverCoeff p u k).re *
          ∫ x in a..b, unitIntervalCosineMode k x := by simp [C, E]

private theorem resolverPhysicalSourceReal_integral_tsum_of_le_bridge
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    (hUnonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift u x)
    {a b : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : b ∈ Set.Ioo (0 : ℝ) 1)
    (hab : a ≤ b) :
    Summable (fun k : ℕ =>
      (intervalNeumannResolverSourceCoeff p u k).re *
        ∫ x in a..b, unitIntervalCosineMode k x) ∧
    (∫ x in a..b, resolverPhysicalSourceReal p u x)
      =
    ∑' k : ℕ,
      (intervalNeumannResolverSourceCoeff p u k).re *
        ∫ x in a..b, unitIntervalCosineMode k x := by
  classical
  let ψ : ℝ → ℝ := (Set.Ioc a b).indicator (fun _ : ℝ => (1 : ℝ))
  have hψm : AEStronglyMeasurable ψ (intervalMeasure 1) := by
    exact ((measurable_const : Measurable (fun _ : ℝ => (1 : ℝ))).indicator
      measurableSet_Ioc).aestronglyMeasurable
  have hψb : ∀ x ∈ Set.Icc (0 : ℝ) 1, |ψ x| ≤ (1 : ℝ) := by
    intro x _; by_cases hxab : x ∈ Set.Ioc a b <;> simp [ψ, hxab]
  have hparse := bridge_cosine_parseval_pairing
    (f := resolverPhysicalSourceReal p u) (φ := ψ)
    (resolverPhysicalSourceReal_continuousOn p hUcont) hψm hψb
  have htest : ∀ k : ℕ,
      bridgeCosineTestCoeff ψ k =
        ∫ x in a..b, unitIntervalCosineMode k x := by
    intro k
    simpa [bridgeCosineTestCoeff, ψ] using
      integral_zero_one_mul_indicator_Ioc_eq_intervalIntegral_of_le
        (f := unitIntervalCosineMode k) ha.1 hb.2 hab
  have htermsum :
      Summable (fun k : ℕ =>
        (intervalNeumannResolverSourceCoeff p u k).re *
          ∫ x in a..b, unitIntervalCosineMode k x) := by
    refine hparse.1.congr ?_
    intro k
    rw [resolverPhysicalSourceReal_cosineCoeff_eq p hUnonneg k, htest k]
  refine ⟨htermsum, ?_⟩
  calc
    ∫ x in a..b, resolverPhysicalSourceReal p u x
        = ∫ x in (0 : ℝ)..1, resolverPhysicalSourceReal p u x * ψ x := by
          exact (integral_zero_one_mul_indicator_Ioc_eq_intervalIntegral_of_le
            (f := resolverPhysicalSourceReal p u) ha.1 hb.2 hab).symm
    _ = ∑' k : ℕ,
          cosineCoeffs (resolverPhysicalSourceReal p u) k *
            bridgeCosineTestCoeff ψ k := hparse.2.symm
    _ = ∑' k : ℕ,
          (intervalNeumannResolverSourceCoeff p u k).re *
            ∫ x in a..b, unitIntervalCosineMode k x := by
          refine tsum_congr fun k => ?_
          rw [resolverPhysicalSourceReal_cosineCoeff_eq p hUnonneg k, htest k]

/-! ### Integrated weak ODE and FTC bridge -/

/-!
The bridge lemmas below isolate the analytic work for the continuous-source
route.

* `resolverGradReal_sub_eq_tsum_lapCoeff_pairing` is Part 1 of the intended
  proof: telescope the absolutely summable gradient sine series, apply the
  one-mode FTC, then use `intervalNeumannResolverCoeff_elliptic` to rewrite
  `-λₖ cₖ` as `μ cₖ - âₖ`.
* `integral_lapPhysicalReal_eq_tsum_lapCoeff_pairing` is Part 2: use
  `cosine_parseval_pairing` from `IntervalTruncatedTestedSpectral` with
  `φ = Set.indicator (Set.Ioc a b) (fun _ => 1)` for both the resolver value
  and physical source, then bridge the cosine coefficients back to
  `(intervalNeumannResolverCoeff p u k).re` and
  `(intervalNeumannResolverSourceCoeff p u k).re`.

The Part 2 Parseval/coefficient-matching bridge remains a deliberately named
residual rather than being hidden inside the main theorem.
-/

private lemma resolverCoeff_re_neg_lap_eq
    (p : CM2Params) (u : intervalDomainPoint → ℝ) (k : ℕ) :
    -(((k : ℝ) * Real.pi) ^ 2) *
        (intervalNeumannResolverCoeff p u k).re =
      p.μ * (intervalNeumannResolverCoeff p u k).re -
        (intervalNeumannResolverSourceCoeff p u k).re := by
  have hellRe :
      (p.μ + ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue k) *
          (intervalNeumannResolverCoeff p u k).re =
        (intervalNeumannResolverSourceCoeff p u k).re := by
    have hcast :
        ((p.μ : ℂ) +
            (ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue k : ℂ)) =
          (((p.μ +
            ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue k : ℝ)) : ℂ) := by
      push_cast
      ring
    have hk := congrArg Complex.re (intervalNeumannResolverCoeff_elliptic p u k)
    rw [hcast, Complex.re_ofReal_mul] at hk
    exact hk
  have hlam :
      ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue k =
        ((k : ℝ) * Real.pi) ^ 2 := by
    show ((k : ℝ) ^ 2 * Real.pi ^ 2) = _
    ring
  rw [hlam] at hellRe
  linarith

private lemma gradMode_sub_eq_neg_lap_integral_cosine
    (k : ℕ) (a b : ℝ) :
    (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * b)) -
        (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * a))
      =
    -(((k : ℝ) * Real.pi) ^ 2) *
      ∫ t in a..b, unitIntervalCosineMode k t := by
  set K : ℝ := (k : ℝ) * Real.pi with hK
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => -K * Real.sin (K * y))
        (-K ^ 2 * unitIntervalCosineMode k x) x := by
    intro x _hx
    have hlin : HasDerivAt (fun y : ℝ => K * y) K x := by
      simpa using (hasDerivAt_id x).const_mul K
    have hsin :
        HasDerivAt (fun y : ℝ => Real.sin (K * y))
          (Real.cos (K * x) * K) x :=
      (Real.hasDerivAt_sin (K * x)).comp x hlin
    have hmain := hsin.const_mul (-K)
    convert hmain using 1
    · rw [unitIntervalCosineMode, hK]
      ring
  have hint :
      IntervalIntegrable
        (fun x : ℝ => -K ^ 2 * unitIntervalCosineMode k x) volume a b := by
    have hcont :
        Continuous (fun x : ℝ => -K ^ 2 * unitIntervalCosineMode k x) := by
      unfold unitIntervalCosineMode
      fun_prop
    exact hcont.intervalIntegrable a b
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_const_mul] at hFTC
  rw [hK] at hFTC
  exact hFTC.symm

private theorem resolverGradReal_sub_eq_tsum_lapCoeff_pairing
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    {a b : ℝ} :
    resolverGradReal p u b - resolverGradReal p u a
      =
    ∑' k : ℕ,
      (p.μ * (intervalNeumannResolverCoeff p u k).re -
        (intervalNeumannResolverSourceCoeff p u k).re) *
        ∫ t in a..b, unitIntervalCosineMode k t := by
  classical
  have hsrcL2 :
      Summable fun k : ℕ => ((intervalNeumannResolverSourceCoeff p u k).re) ^ 2 := by
    simpa [ShenWork.Paper2.intervalNeumannResolverSourceCoeff_zero] using
      resolverSourceCoeff_re_sq_summable_of_continuousOn p hUcont
  have hsum_b := resolver_sineSeries_summable_of_sourceL2 p hsrcL2 b
  have hsum_a := resolver_sineSeries_summable_of_sourceL2 p hsrcL2 a
  calc
    resolverGradReal p u b - resolverGradReal p u a
        =
        ∑' k : ℕ,
          (
          (intervalNeumannResolverCoeff p u k).re *
              (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * b)) -
            (intervalNeumannResolverCoeff p u k).re *
              (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * a))) := by
          unfold resolverGradReal
          rw [← hsum_b.tsum_sub hsum_a]
    _ = ∑' k : ℕ,
          (intervalNeumannResolverCoeff p u k).re *
            ((-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * b)) -
              (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * a))) := by
          refine tsum_congr fun k => ?_
          ring
    _ = ∑' k : ℕ,
          (p.μ * (intervalNeumannResolverCoeff p u k).re -
            (intervalNeumannResolverSourceCoeff p u k).re) *
            ∫ t in a..b, unitIntervalCosineMode k t := by
          refine tsum_congr fun k => ?_
          rw [gradMode_sub_eq_neg_lap_integral_cosine k a b]
          calc
            (intervalNeumannResolverCoeff p u k).re *
                (-(((k : ℝ) * Real.pi) ^ 2) *
                  ∫ t in a..b, unitIntervalCosineMode k t)
                =
              (-(((k : ℝ) * Real.pi) ^ 2) *
                  (intervalNeumannResolverCoeff p u k).re) *
                ∫ t in a..b, unitIntervalCosineMode k t := by
                ring
            _ =
              (p.μ * (intervalNeumannResolverCoeff p u k).re -
                (intervalNeumannResolverSourceCoeff p u k).re) *
                ∫ t in a..b, unitIntervalCosineMode k t := by
                rw [resolverCoeff_re_neg_lap_eq p u k]

private theorem integral_lapPhysicalReal_eq_tsum_lapCoeff_pairing_of_le
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    (hUnonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift u x)
    {a b : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : b ∈ Set.Ioo (0 : ℝ) 1)
    (hab : a ≤ b) :
    (∫ t in a..b, resolverLapPhysicalReal p u t)
      =
    ∑' k : ℕ,
      (p.μ * (intervalNeumannResolverCoeff p u k).re -
        (intervalNeumannResolverSourceCoeff p u k).re) *
        ∫ t in a..b, unitIntervalCosineMode k t := by
  classical
  obtain ⟨hRsum, hRint_eq⟩ :=
    resolverValueSeriesReal_integral_tsum_of_le_bridge p hUcont ha hb hab
  obtain ⟨hSsum, hSint_eq⟩ :=
    resolverPhysicalSourceReal_integral_tsum_of_le_bridge
      p hUcont hUnonneg ha hb hab
  have huIcc_sub : Set.uIcc a b ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    have hxab : x ∈ Set.Icc a b := by
      simpa [Set.uIcc_of_le hab] using hx
    exact ⟨ha.1.le.trans hxab.1, hxab.2.trans hb.2.le⟩
  have hR_intervalIntegrable :
      IntervalIntegrable (resolverValueSeriesReal p u) volume a b :=
    (resolverValueSeriesReal_continuous_of_continuousOn p hUcont).intervalIntegrable a b
  have hS_intervalIntegrable :
      IntervalIntegrable (resolverPhysicalSourceReal p u) volume a b := by
    exact ((resolverPhysicalSourceReal_continuousOn p hUcont).mono huIcc_sub).intervalIntegrable
  have hLap_eq :
      (∫ t in a..b, resolverLapPhysicalReal p u t)
        =
      ∫ t in a..b,
        (p.μ * resolverValueSeriesReal p u t - resolverPhysicalSourceReal p u t) := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    have hxab : x ∈ Set.Icc a b := by
      simpa [Set.uIcc_of_le hab] using hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨ha.1.le.trans hxab.1, hxab.2.trans hb.2.le⟩
    simp [resolverLapPhysicalReal, resolverLapPhysical, resolverPositiveSourceLifted,
      resolverPhysicalSourceReal, resolverValueSeriesReal, intervalNeumannResolverR, hxIcc]
  have hμRsum :
      Summable (fun k : ℕ =>
        p.μ *
          ((intervalNeumannResolverCoeff p u k).re *
            ∫ t in a..b, unitIntervalCosineMode k t)) :=
    hRsum.mul_left p.μ
  have hR_const_mul :
      (∫ x in a..b, p.μ * resolverValueSeriesReal p u x)
        = p.μ * (∫ x in a..b, resolverValueSeriesReal p u x) := by
    exact intervalIntegral.integral_const_mul
      (a := a) (b := b) (μ := volume)
      p.μ (fun x : ℝ => resolverValueSeriesReal p u x)
  have hlinear :
      (∫ x in a..b,
        (p.μ * resolverValueSeriesReal p u x - resolverPhysicalSourceReal p u x))
        =
      p.μ * (∫ x in a..b, resolverValueSeriesReal p u x)
        - (∫ x in a..b, resolverPhysicalSourceReal p u x) := by
    rw [intervalIntegral.integral_sub
      (hR_intervalIntegrable.const_mul p.μ) hS_intervalIntegrable]
    exact congrArg
      (fun z : ℝ => z - (∫ x in a..b, resolverPhysicalSourceReal p u x))
      hR_const_mul
  have hseries_sub :
      p.μ * (∫ x in a..b, resolverValueSeriesReal p u x)
        - (∫ x in a..b, resolverPhysicalSourceReal p u x)
        =
      p.μ * (∑' k : ℕ,
        (intervalNeumannResolverCoeff p u k).re *
          ∫ x in a..b, unitIntervalCosineMode k x)
        - (∑' k : ℕ,
          (intervalNeumannResolverSourceCoeff p u k).re *
            ∫ x in a..b, unitIntervalCosineMode k x) := by
    exact congrArg₂ (fun R S : ℝ => p.μ * R - S) hRint_eq hSint_eq
  calc
    ∫ t in a..b, resolverLapPhysicalReal p u t
        =
      ∫ t in a..b,
        (p.μ * resolverValueSeriesReal p u t - resolverPhysicalSourceReal p u t) := hLap_eq
    _ =
      p.μ * (∫ t in a..b, resolverValueSeriesReal p u t)
        - (∫ t in a..b, resolverPhysicalSourceReal p u t) := hlinear
    _ =
      p.μ * (∑' k : ℕ,
        (intervalNeumannResolverCoeff p u k).re *
          ∫ t in a..b, unitIntervalCosineMode k t)
        - (∑' k : ℕ,
          (intervalNeumannResolverSourceCoeff p u k).re *
            ∫ t in a..b, unitIntervalCosineMode k t) := by
          exact hseries_sub
    _ =
      (∑' k : ℕ,
        p.μ *
          ((intervalNeumannResolverCoeff p u k).re *
            ∫ t in a..b, unitIntervalCosineMode k t))
        - (∑' k : ℕ,
          (intervalNeumannResolverSourceCoeff p u k).re *
            ∫ t in a..b, unitIntervalCosineMode k t) := by
          rw [tsum_mul_left]
    _ =
      ∑' k : ℕ,
        ((p.μ *
          ((intervalNeumannResolverCoeff p u k).re *
            ∫ t in a..b, unitIntervalCosineMode k t)) -
          (intervalNeumannResolverSourceCoeff p u k).re *
            ∫ t in a..b, unitIntervalCosineMode k t) := by
          exact (hμRsum.tsum_sub hSsum).symm
    _ =
      ∑' k : ℕ,
        (p.μ * (intervalNeumannResolverCoeff p u k).re -
          (intervalNeumannResolverSourceCoeff p u k).re) *
          ∫ t in a..b, unitIntervalCosineMode k t := by
          refine tsum_congr fun k => ?_
          ring

private theorem integral_lapPhysicalReal_eq_tsum_lapCoeff_pairing
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    (hUnonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift u x)
    {a b : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : b ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ t in a..b, resolverLapPhysicalReal p u t)
      =
    ∑' k : ℕ,
      (p.μ * (intervalNeumannResolverCoeff p u k).re -
        (intervalNeumannResolverSourceCoeff p u k).re) *
        ∫ t in a..b, unitIntervalCosineMode k t := by
  classical
  by_cases hab : a ≤ b
  · exact integral_lapPhysicalReal_eq_tsum_lapCoeff_pairing_of_le
      p hUcont hUnonneg ha hb hab
  · have hba : b ≤ a := le_of_not_ge hab
    have hswap :=
      integral_lapPhysicalReal_eq_tsum_lapCoeff_pairing_of_le
        p hUcont hUnonneg hb ha hba
    calc
      ∫ t in a..b, resolverLapPhysicalReal p u t
          = -(∫ t in b..a, resolverLapPhysicalReal p u t) := by
            rw [intervalIntegral.integral_symm b a]
      _ = -(∑' k : ℕ,
            (p.μ * (intervalNeumannResolverCoeff p u k).re -
              (intervalNeumannResolverSourceCoeff p u k).re) *
              ∫ t in b..a, unitIntervalCosineMode k t) := by
            rw [hswap]
      _ = ∑' k : ℕ,
            (p.μ * (intervalNeumannResolverCoeff p u k).re -
              (intervalNeumannResolverSourceCoeff p u k).re) *
              ∫ t in a..b, unitIntervalCosineMode k t := by
            have hterm :
                (fun k : ℕ =>
                  (p.μ * (intervalNeumannResolverCoeff p u k).re -
                    (intervalNeumannResolverSourceCoeff p u k).re) *
                    ∫ t in b..a, unitIntervalCosineMode k t)
                  =
                fun k : ℕ =>
                  -((p.μ * (intervalNeumannResolverCoeff p u k).re -
                    (intervalNeumannResolverSourceCoeff p u k).re) *
                    ∫ t in a..b, unitIntervalCosineMode k t) := by
              funext k
              rw [intervalIntegral.integral_symm a b]
              ring
            rw [hterm, tsum_neg]
            simp

theorem resolverGradReal_sub_eq_integral_lapPhysicalReal
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    (hUnonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift u x)
    {a b : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : b ∈ Set.Ioo (0 : ℝ) 1) :
    resolverGradReal p u b - resolverGradReal p u a
      = ∫ t in a..b, resolverLapPhysicalReal p u t := by
  calc
    resolverGradReal p u b - resolverGradReal p u a
        = ∑' k : ℕ,
            (p.μ * (intervalNeumannResolverCoeff p u k).re -
              (intervalNeumannResolverSourceCoeff p u k).re) *
              ∫ t in a..b, unitIntervalCosineMode k t :=
          resolverGradReal_sub_eq_tsum_lapCoeff_pairing p hUcont
    _ = ∫ t in a..b, resolverLapPhysicalReal p u t :=
          (integral_lapPhysicalReal_eq_tsum_lapCoeff_pairing
            p hUcont hUnonneg ha hb).symm

theorem resolverGradReal_eventually_eq_primitive
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    (hUnonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift u x)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    (fun z : ℝ => resolverGradReal p u z)
      =ᶠ[𝓝 x]
    (fun z : ℝ => resolverGradReal p u x
      + ∫ t in x..z, resolverLapPhysicalReal p u t) := by
  have hIoo_mem : Set.Ioo (0 : ℝ) 1 ∈ 𝓝 x :=
    IsOpen.mem_nhds isOpen_Ioo hx
  filter_upwards [hIoo_mem] with z hz
  have h := resolverGradReal_sub_eq_integral_lapPhysicalReal
    p hUcont hUnonneg hx hz
  linarith

theorem resolverGradReal_hasDerivAt_physicalLap_of_continuousOn_via_FTC
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    (hUnonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift u x)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun z : ℝ => resolverGradReal p u z)
      (resolverLapPhysical p u ⟨x, Set.Ioo_subset_Icc_self hx⟩) x := by
  let q : ℝ → ℝ := resolverLapPhysicalReal p u
  have hq_cont : ContinuousAt q x :=
    resolverLapPhysicalReal_continuousAt_of_continuousOn p hUcont hx
  have hq_int : IntervalIntegrable q volume x x :=
    by
      rw [intervalIntegrable_iff]
      simp
  have hq_meas : StronglyMeasurableAtFilter q (𝓝 x) :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
      (fun y hy => resolverLapPhysicalReal_continuousAt_of_continuousOn p hUcont hy)
      x hx
  have hFTC :
      HasDerivAt (fun z : ℝ => ∫ t in x..z, q t) (q x) x :=
    intervalIntegral.integral_hasDerivAt_right hq_int hq_meas hq_cont
  have hprim :
      HasDerivAt
        (fun z : ℝ => resolverGradReal p u x + ∫ t in x..z, q t)
        (q x) x := by
    simpa using hFTC.const_add (resolverGradReal p u x)
  have hev :
      (fun z : ℝ => resolverGradReal p u z)
        =ᶠ[𝓝 x]
      (fun z : ℝ => resolverGradReal p u x + ∫ t in x..z, q t) :=
    resolverGradReal_eventually_eq_primitive p hUcont hUnonneg hx
  have hq_x : q x = resolverLapPhysical p u ⟨x, Set.Ioo_subset_Icc_self hx⟩ := by
    simp [q, resolverLapPhysicalReal, Set.Ioo_subset_Icc_self hx]
  rw [← hq_x]
  exact hprim.congr_of_eventuallyEq hev

end ShenWork.IntervalResolverWeakBounds
