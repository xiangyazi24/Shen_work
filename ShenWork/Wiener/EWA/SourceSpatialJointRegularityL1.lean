/-
  ShenWork/Wiener/EWA/SourceSpatialJointRegularityL1.lean

  L1ContOn-compatible joint (t,x)-continuity of the first and second spatial
  derivatives of the chi0<0 source-form solution synthesis.
-/
import ShenWork.Wiener.EWA.SourceSpatialJointRegularity
import ShenWork.Wiener.EWA.SourceSynthesisL1
import ShenWork.Paper2.IntervalPicardLimitRestartWeak

noncomputable section

namespace ShenWork.EWA

open ShenWork.IntervalDuhamelClosedC2
  (duhamelSpectralCoeff cosineCoeffSeries_grad_hasDerivAt
   cosineCoeffSeries_grad2_hasDerivAt)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs)
open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.IntervalPicardLimitRestartWeak
  (DuhamelSourceL1ContOn abs_duhamelSpectralCoeff_le_weak)
open ShenWork.CosineSpectrum
  (cosineMode cosineMode_deriv cosineMode_second_deriv)
open ShenWork.HeatKernelGradientEstimates
  (unitIntervalCosineHeatTrace_single_exp_summable)
open ShenWork.IntervalMildRegularityBootstrap
  (unitIntervalCosineEigenvalue_mul_exp_summable)
open Set Filter Topology

/-! ## Auxiliary lemmas -/

private theorem npi_le_one_add_eigenvalue (n : ℕ) :
    (n : ℝ) * Real.pi ≤
      1 + unitIntervalCosineEigenvalue n := by
  unfold unitIntervalCosineEigenvalue
  nlinarith [sq_nonneg ((n : ℝ) * Real.pi - 1)]

private theorem eigenvalue_mul_abs_duhamelCoeff_le_of_L1ContOn
    {a : ℝ → ℕ → ℝ} {T : ℝ} (src : DuhamelSourceL1ContOn a T)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (n : ℕ) :
    unitIntervalCosineEigenvalue n *
      |duhamelSpectralCoeff a t n| ≤ src.envelope n :=
  eigenvalue_mul_abs_duhamelSpectralCoeff_le_envelope src ht htT n

private theorem fullSourceCoeff_continuousOn_Ioo_of_L1ContOn
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (u₀cos : ℕ → ℝ)
    (hchem : DuhamelSourceL1ContOn
      (coupledChemDivSourceCoeffs p u) T)
    (hlog : DuhamelSourceL1ContOn
      (coupledLogisticSourceCoeffs p u) T)
    (n : ℕ) : ContinuousOn
      (fun t : ℝ => fullSourceCoeff p u u₀cos t n)
      (Ioo (0 : ℝ) T) := by
  have hH : ContinuousOn
      (fun t : ℝ =>
        Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n)
      (Ioo (0 : ℝ) T) :=
    (((Real.continuous_exp.comp
      (continuous_id.neg.mul continuous_const)).mul
      continuous_const).continuousOn)
  have hC : ContinuousOn
      (fun t : ℝ =>
        (-p.χ₀) *
          duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n)
      (Ioo (0 : ℝ) T) :=
    continuous_const.continuousOn.mul
      (duhamelSpectralCoeff_continuous_of_L1ContOn hchem n)
  have hL : ContinuousOn
      (fun t : ℝ =>
        duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) t n)
      (Ioo (0 : ℝ) T) :=
    duhamelSpectralCoeff_continuous_of_L1ContOn hlog n
  simpa only [fullSourceCoeff] using (hH.add hC).add hL

/-! ## Shared norm bound infrastructure -/

/-- Triangle inequality for the three-leg split. -/
private theorem fullSource_triangle (H χ₀ Bc Bl : ℝ) :
    |H + (-χ₀) * Bc + Bl| ≤
      |H| + |χ₀| * |Bc| + |Bl| := by
  calc |H + (-χ₀) * Bc + Bl|
      ≤ |H + (-χ₀) * Bc| + |Bl| := abs_add_le _ _
    _ ≤ (|H| + |(-χ₀) * Bc|) + |Bl| := by
        gcongr; exact abs_add_le _ _
    _ = |H| + |χ₀| * |Bc| + |Bl| := by
        congr 1; congr 1; rw [abs_mul, abs_neg]

/-! ## First spatial derivative (gradient) -/

set_option maxHeartbeats 1200000 in
private theorem fullSourceCoeff_gradJC_of_L1ContOn
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn
      (coupledChemDivSourceCoeffs p u) T)
    (hlog : DuhamelSourceL1ContOn
      (coupledLogisticSourceCoeffs p u) T) :
    ContinuousOn (fun q : ℝ × ℝ => ∑' n,
      fullSourceCoeff p u u₀cos q.1 n *
        (-((n : ℝ) * Real.pi) *
          Real.sin ((n : ℝ) * Real.pi * q.2)))
      (Ioo (0 : ℝ) T ×ˢ univ) := by
  apply continuousOn_of_forall_continuousAt
  intro p₀ hp₀
  obtain ⟨hp₀1, _⟩ := mem_prod.1 hp₀
  obtain ⟨hp₀pos, hp₀T⟩ := mem_Ioo.1 hp₀1
  have h0T : (0 : ℝ) ≤ T := le_of_lt (lt_trans hp₀pos hp₀T)
  set c := p₀.1 / 2 with hc_def
  set Tb := (p₀.1 + T) / 2 with hTb_def
  have hc : 0 < c := by rw [hc_def]; linarith
  have hTbT : Tb < T := by rw [hTb_def]; linarith
  have hTb_pos : 0 < Tb := by rw [hTb_def]; linarith
  suffices h : ContinuousOn (fun q : ℝ × ℝ => ∑' n,
      fullSourceCoeff p u u₀cos q.1 n *
        (-((n : ℝ) * Real.pi) *
          Real.sin ((n : ℝ) * Real.pi * q.2)))
      (Ioo c Tb ×ˢ univ) from
    h.continuousAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds
        (mem_prod.2
          ⟨mem_Ioo.2 ⟨by rw [hc_def]; linarith,
            by rw [hTb_def]; linarith⟩,
           mem_univ _⟩))
  apply continuousOn_tsum
    (u := fun n =>
      Mu0 *
        (Real.exp
          (-c * unitIntervalCosineEigenvalue n) +
        unitIntervalCosineEigenvalue n *
          Real.exp
            (-c * unitIntervalCosineEigenvalue n)) +
      (|p.χ₀| + 1) *
        ((Tb + 1) *
          (hchem.envelope n + hlog.envelope n)))
  · -- (1) each summand ContinuousOn
    intro n; apply ContinuousOn.mul
    · exact ((fullSourceCoeff_continuousOn_Ioo_of_L1ContOn
        p u u₀cos hchem hlog n).comp
          continuous_fst.continuousOn (fun q hq => by
            obtain ⟨ht, _⟩ := mem_prod.1 hq
            exact ⟨lt_trans hc (mem_Ioo.1 ht).1,
              lt_trans (mem_Ioo.1 ht).2 hTbT⟩))
    · exact (continuous_const.mul
        (Real.continuous_sin.comp
          (continuous_const.mul continuous_snd))
        ).continuousOn
  · -- (2) summable majorant
    exact (((unitIntervalCosineHeatTrace_single_exp_summable
        hc).add
      (unitIntervalCosineEigenvalue_mul_exp_summable
        hc)).mul_left Mu0).add
      (((hchem.henv_summable.add
        hlog.henv_summable).mul_left (Tb + 1)).mul_left
          (|p.χ₀| + 1))
  · -- (3) norm bound per term
    intro n q hq
    obtain ⟨ht, _⟩ := mem_prod.1 hq
    obtain ⟨hct, htTb⟩ := mem_Ioo.1 ht
    have ht_pos : 0 < q.1 := lt_trans hc hct
    have htT : q.1 ≤ T := (lt_trans htTb hTbT).le
    have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue; positivity
    rw [Real.norm_eq_abs, abs_mul]
    have hmode : |-((n : ℝ) * Real.pi) *
        Real.sin ((n : ℝ) * Real.pi * q.2)| ≤
        (n : ℝ) * Real.pi := by
      rw [abs_mul, abs_neg, abs_of_nonneg
        (by positivity : (0 : ℝ) ≤ (n : ℝ) * Real.pi)]
      exact mul_le_of_le_one_right
        (by positivity) (Real.abs_sin_le_one _)
    simp only [fullSourceCoeff]
    set H := Real.exp
      (-q.1 * unitIntervalCosineEigenvalue n) *
      u₀cos n
    set Bc := duhamelSpectralCoeff
      (coupledChemDivSourceCoeffs p u) q.1 n
    set Bl := duhamelSpectralCoeff
      (coupledLogisticSourceCoeffs p u) q.1 n
    have htri := fullSource_triangle H p.χ₀ Bc Bl
    have henv_c_nn : 0 ≤ hchem.envelope n :=
      le_trans (abs_nonneg _)
        (hchem.henv_bound 0 le_rfl h0T n)
    have henv_l_nn : 0 ≤ hlog.envelope n :=
      le_trans (abs_nonneg _)
        (hlog.henv_bound 0 le_rfl h0T n)
    -- |H| ≤ Mu0 exp(-cλ)
    have hH : |H| ≤ Mu0 *
        Real.exp
          (-c * unitIntervalCosineEigenvalue n) := by
      simp only [H, abs_mul,
        abs_of_nonneg (Real.exp_nonneg _)]
      calc _ ≤ Real.exp
            (-c * unitIntervalCosineEigenvalue n) *
            Mu0 :=
          mul_le_mul
            (Real.exp_le_exp_of_le (by nlinarith))
            (hu0bd n) (abs_nonneg _) (Real.exp_nonneg _)
        _ = _ := by ring
    -- |Bc|, |Bl| ≤ Tb · envelope
    have hBc : |Bc| ≤ Tb * hchem.envelope n :=
      le_trans
        (by
          simpa [Bc] using
            abs_duhamelSpectralCoeff_le_weak hchem ht_pos htT n)
        (mul_le_mul_of_nonneg_right (le_of_lt htTb) henv_c_nn)
    have hBl : |Bl| ≤ Tb * hlog.envelope n :=
      le_trans
        (by
          simpa [Bl] using
            abs_duhamelSpectralCoeff_le_weak hlog ht_pos htT n)
        (mul_le_mul_of_nonneg_right (le_of_lt htTb) henv_l_nn)
    -- Parabolic gain: λ|Bc|, λ|Bl| bounds
    have hEc :
        unitIntervalCosineEigenvalue n * |Bc| ≤ hchem.envelope n := by
      simpa [Bc] using
        eigenvalue_mul_abs_duhamelCoeff_le_of_L1ContOn
          hchem ht_pos htT n
    have hEl :
        unitIntervalCosineEigenvalue n * |Bl| ≤ hlog.envelope n := by
      simpa [Bl] using
        eigenvalue_mul_abs_duhamelCoeff_le_of_L1ContOn
          hlog ht_pos htT n
    -- (1+λ)|Bc| ≤ (Tb+1)·env_c
    have hNc :
        (1 + unitIntervalCosineEigenvalue n) * |Bc| ≤
        (Tb + 1) * hchem.envelope n := by
      have : (1 + unitIntervalCosineEigenvalue n) *
          |Bc| = |Bc| +
          unitIntervalCosineEigenvalue n * |Bc| := by
        ring
      rw [this]
      nlinarith [hBc, hEc]
    have hNl :
        (1 + unitIntervalCosineEigenvalue n) * |Bl| ≤
        (Tb + 1) * hlog.envelope n := by
      have : (1 + unitIntervalCosineEigenvalue n) *
          |Bl| = |Bl| +
          unitIntervalCosineEigenvalue n * |Bl| := by
        ring
      rw [this]
      nlinarith [hBl, hEl]
    -- (1+λ)|H| ≤ Mu0·(e^{-cλ} + λe^{-cλ})
    have hNH :
        (1 + unitIntervalCosineEigenvalue n) * |H| ≤
        Mu0 *
          (Real.exp
            (-c * unitIntervalCosineEigenvalue n) +
          unitIntervalCosineEigenvalue n *
            Real.exp
              (-c * unitIntervalCosineEigenvalue n)
          ) := by
      have : (1 + unitIntervalCosineEigenvalue n) *
          |H| = |H| +
          unitIntervalCosineEigenvalue n * |H| := by
        ring
      linarith [mul_le_mul_of_nonneg_left hH hlam]
    have hchi := abs_nonneg p.χ₀
    have hTb1_nn : 0 ≤ Tb + 1 := by linarith [hTb_pos]
    -- Main chain:
    have step1 :
        |H + (-p.χ₀) * Bc + Bl| *
          |-((n : ℝ) * Real.pi) *
            Real.sin ((n : ℝ) * Real.pi * q.2)| ≤
        (1 + unitIntervalCosineEigenvalue n) * |H| +
          |p.χ₀| *
            ((1 + unitIntervalCosineEigenvalue n) *
              |Bc|) +
          (1 + unitIntervalCosineEigenvalue n) *
            |Bl| := by
      have hcoeff_nn : 0 ≤ |H| + |p.χ₀| * |Bc| +
          |Bl| := by positivity
      calc |H + (-p.χ₀) * Bc + Bl| *
            |-((n : ℝ) * Real.pi) *
              Real.sin ((n : ℝ) * Real.pi * q.2)|
          ≤ (|H| + |p.χ₀| * |Bc| + |Bl|) *
              ((n : ℝ) * Real.pi) :=
            mul_le_mul htri hmode (abs_nonneg _)
              hcoeff_nn
        _ ≤ (|H| + |p.χ₀| * |Bc| + |Bl|) *
              (1 + unitIntervalCosineEigenvalue n) :=
            mul_le_mul_of_nonneg_left
              (npi_le_one_add_eigenvalue n) hcoeff_nn
        _ = (1 + unitIntervalCosineEigenvalue n) *
              |H| +
            |p.χ₀| *
              ((1 + unitIntervalCosineEigenvalue n) *
                |Bc|) +
            (1 + unitIntervalCosineEigenvalue n) *
              |Bl| := by ring
    have step2 :
        (1 + unitIntervalCosineEigenvalue n) * |H| +
          |p.χ₀| *
            ((1 + unitIntervalCosineEigenvalue n) *
              |Bc|) +
          (1 + unitIntervalCosineEigenvalue n) *
            |Bl| ≤
        Mu0 *
          (Real.exp
            (-c * unitIntervalCosineEigenvalue n) +
          unitIntervalCosineEigenvalue n *
            Real.exp
              (-c * unitIntervalCosineEigenvalue n)) +
        |p.χ₀| * ((Tb + 1) * hchem.envelope n) +
        ((Tb + 1) * hlog.envelope n) := by
      gcongr
    have step3 :
        Mu0 *
          (Real.exp
            (-c * unitIntervalCosineEigenvalue n) +
          unitIntervalCosineEigenvalue n *
            Real.exp
              (-c * unitIntervalCosineEigenvalue n)) +
        |p.χ₀| * ((Tb + 1) * hchem.envelope n) +
        ((Tb + 1) * hlog.envelope n) ≤
        Mu0 *
          (Real.exp
            (-c * unitIntervalCosineEigenvalue n) +
          unitIntervalCosineEigenvalue n *
            Real.exp
              (-c * unitIntervalCosineEigenvalue n)) +
        (|p.χ₀| + 1) *
          ((Tb + 1) *
            (hchem.envelope n + hlog.envelope n)) := by
      nlinarith [
        mul_nonneg hTb1_nn henv_c_nn,
        mul_nonneg hTb1_nn henv_l_nn,
        mul_nonneg hchi (mul_nonneg hTb1_nn henv_l_nn)]
    linarith

/-! ## Second spatial derivative -/

set_option maxHeartbeats 1200000 in
private theorem fullSourceCoeff_grad2JC_of_L1ContOn
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn
      (coupledChemDivSourceCoeffs p u) T)
    (hlog : DuhamelSourceL1ContOn
      (coupledLogisticSourceCoeffs p u) T) :
    ContinuousOn (fun q : ℝ × ℝ => ∑' n,
      fullSourceCoeff p u u₀cos q.1 n *
        (-(((n : ℝ) * Real.pi) ^ 2) *
          Real.cos ((n : ℝ) * Real.pi * q.2)))
      (Ioo (0 : ℝ) T ×ˢ univ) := by
  apply continuousOn_of_forall_continuousAt
  intro p₀ hp₀
  obtain ⟨hp₀1, _⟩ := mem_prod.1 hp₀
  obtain ⟨hp₀pos, hp₀T⟩ := mem_Ioo.1 hp₀1
  have h0T : (0 : ℝ) ≤ T := le_of_lt (lt_trans hp₀pos hp₀T)
  set c := p₀.1 / 2 with hc_def
  set Tb := (p₀.1 + T) / 2 with hTb_def
  have hc : 0 < c := by rw [hc_def]; linarith
  have hTbT : Tb < T := by rw [hTb_def]; linarith
  suffices h : ContinuousOn (fun q : ℝ × ℝ => ∑' n,
      fullSourceCoeff p u u₀cos q.1 n *
        (-(((n : ℝ) * Real.pi) ^ 2) *
          Real.cos ((n : ℝ) * Real.pi * q.2)))
      (Ioo c Tb ×ˢ univ) from
    h.continuousAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds
        (mem_prod.2
          ⟨mem_Ioo.2 ⟨by rw [hc_def]; linarith,
            by rw [hTb_def]; linarith⟩,
           mem_univ _⟩))
  apply continuousOn_tsum
    (u := fun n =>
      Mu0 *
        (unitIntervalCosineEigenvalue n *
          Real.exp
            (-c * unitIntervalCosineEigenvalue n)) +
      (|p.χ₀| + 1) *
        (hchem.envelope n + hlog.envelope n))
  · intro n; apply ContinuousOn.mul
    · exact ((fullSourceCoeff_continuousOn_Ioo_of_L1ContOn
        p u u₀cos hchem hlog n).comp
          continuous_fst.continuousOn (fun q hq => by
            obtain ⟨ht, _⟩ := mem_prod.1 hq
            exact ⟨lt_trans hc (mem_Ioo.1 ht).1,
              lt_trans (mem_Ioo.1 ht).2 hTbT⟩))
    · exact (continuous_const.mul
        (Real.continuous_cos.comp
          (continuous_const.mul continuous_snd))
        ).continuousOn
  · exact
      ((unitIntervalCosineEigenvalue_mul_exp_summable
        hc).mul_left Mu0).add
      ((hchem.henv_summable.add
        hlog.henv_summable).mul_left (|p.χ₀| + 1))
  · intro n q hq
    obtain ⟨ht, _⟩ := mem_prod.1 hq
    obtain ⟨hct, htTb⟩ := mem_Ioo.1 ht
    have ht_pos : 0 < q.1 := lt_trans hc hct
    have htT : q.1 ≤ T := (lt_trans htTb hTbT).le
    have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue; positivity
    rw [Real.norm_eq_abs, abs_mul]
    have hmode :
        |-(((n : ℝ) * Real.pi) ^ 2) *
          Real.cos ((n : ℝ) * Real.pi * q.2)| ≤
        unitIntervalCosineEigenvalue n := by
      rw [abs_mul, abs_neg,
        abs_of_nonneg (sq_nonneg _)]
      calc ((n : ℝ) * Real.pi) ^ 2 *
            |Real.cos ((n : ℝ) * Real.pi * q.2)|
          ≤ ((n : ℝ) * Real.pi) ^ 2 * 1 := by
            gcongr; exact Real.abs_cos_le_one _
        _ = unitIntervalCosineEigenvalue n := by
            unfold unitIntervalCosineEigenvalue; ring
    simp only [fullSourceCoeff]
    set H := Real.exp
      (-q.1 * unitIntervalCosineEigenvalue n) *
      u₀cos n
    set Bc := duhamelSpectralCoeff
      (coupledChemDivSourceCoeffs p u) q.1 n
    set Bl := duhamelSpectralCoeff
      (coupledLogisticSourceCoeffs p u) q.1 n
    have htri := fullSource_triangle H p.χ₀ Bc Bl
    have henv_c_nn : 0 ≤ hchem.envelope n :=
      le_trans (abs_nonneg _)
        (hchem.henv_bound 0 le_rfl h0T n)
    have henv_l_nn : 0 ≤ hlog.envelope n :=
      le_trans (abs_nonneg _)
        (hlog.henv_bound 0 le_rfl h0T n)
    have hH : |H| ≤ Mu0 *
        Real.exp
          (-c * unitIntervalCosineEigenvalue n) := by
      simp only [H, abs_mul,
        abs_of_nonneg (Real.exp_nonneg _)]
      calc _ ≤ Real.exp
            (-c * unitIntervalCosineEigenvalue n) *
            Mu0 :=
          mul_le_mul
            (Real.exp_le_exp_of_le (by nlinarith))
            (hu0bd n) (abs_nonneg _) (Real.exp_nonneg _)
        _ = _ := by ring
    have hEc :
        unitIntervalCosineEigenvalue n * |Bc| ≤ hchem.envelope n := by
      simpa [Bc] using
        eigenvalue_mul_abs_duhamelCoeff_le_of_L1ContOn
          hchem ht_pos htT n
    have hEl :
        unitIntervalCosineEigenvalue n * |Bl| ≤ hlog.envelope n := by
      simpa [Bl] using
        eigenvalue_mul_abs_duhamelCoeff_le_of_L1ContOn
          hlog ht_pos htT n
    have hchi := abs_nonneg p.χ₀
    -- λ|H| ≤ Mu0 · λ e^{-cλ}
    have hNH :
        unitIntervalCosineEigenvalue n * |H| ≤
        Mu0 * (unitIntervalCosineEigenvalue n *
          Real.exp
            (-c * unitIntervalCosineEigenvalue n)
        ) := by
      calc _ ≤ unitIntervalCosineEigenvalue n *
            (Mu0 * Real.exp
              (-c * unitIntervalCosineEigenvalue n)
            ) := mul_le_mul_of_nonneg_left hH hlam
        _ = _ := by ring
    have step1 :
        |H + (-p.χ₀) * Bc + Bl| *
          |-(((n : ℝ) * Real.pi) ^ 2) *
            Real.cos ((n : ℝ) * Real.pi * q.2)| ≤
        unitIntervalCosineEigenvalue n * |H| +
          |p.χ₀| *
            (unitIntervalCosineEigenvalue n * |Bc|) +
          unitIntervalCosineEigenvalue n * |Bl| := by
      calc _ ≤ (|H| + |p.χ₀| * |Bc| + |Bl|) *
            unitIntervalCosineEigenvalue n :=
          mul_le_mul htri hmode (abs_nonneg _)
            (by positivity)
        _ = _ := by ring
    have step2 :
        unitIntervalCosineEigenvalue n * |H| +
          |p.χ₀| *
            (unitIntervalCosineEigenvalue n * |Bc|) +
          unitIntervalCosineEigenvalue n * |Bl| ≤
        Mu0 * (unitIntervalCosineEigenvalue n *
          Real.exp
            (-c * unitIntervalCosineEigenvalue n)) +
        |p.χ₀| * hchem.envelope n +
        hlog.envelope n := by
      gcongr
    have step3 :
        Mu0 * (unitIntervalCosineEigenvalue n *
          Real.exp
            (-c * unitIntervalCosineEigenvalue n)) +
        |p.χ₀| * hchem.envelope n +
        hlog.envelope n ≤
        Mu0 * (unitIntervalCosineEigenvalue n *
          Real.exp
            (-c * unitIntervalCosineEigenvalue n)) +
        (|p.χ₀| + 1) *
          (hchem.envelope n + hlog.envelope n) := by
      nlinarith [henv_c_nn, henv_l_nn,
        mul_nonneg hchi henv_l_nn]
    linarith

/-! ## Deriv connection -/

private theorem gradSeries_eq_deriv {b : ℕ → ℝ}
    (hb : Summable (fun n =>
      unitIntervalCosineEigenvalue n * |b n|))
    (x : ℝ) :
    (∑' n, b n * (-((n : ℝ) * Real.pi) *
      Real.sin ((n : ℝ) * Real.pi * x))) =
    deriv (fun y => ∑' n, b n * cosineMode n y)
      x :=
  (HasDerivAt.deriv
    (cosineCoeffSeries_grad_hasDerivAt hb x)).symm

private theorem grad2Series_eq_deriv2 {b : ℕ → ℝ}
    (hb : Summable (fun n =>
      unitIntervalCosineEigenvalue n * |b n|))
    (x : ℝ) :
    (∑' n, b n * (-(((n : ℝ) * Real.pi) ^ 2) *
      Real.cos ((n : ℝ) * Real.pi * x))) =
    deriv (fun y => deriv (fun z =>
      ∑' n, b n * cosineMode n z) y) x := by
  have h1 : (fun y => deriv (fun z =>
      ∑' n, b n * cosineMode n z) y) =
    (fun y => ∑' n, b n *
      (-((n : ℝ) * Real.pi) *
        Real.sin ((n : ℝ) * Real.pi * y))) := by
    funext y; exact HasDerivAt.deriv
      (cosineCoeffSeries_grad_hasDerivAt hb y)
  rw [h1]
  exact (HasDerivAt.deriv
    (cosineCoeffSeries_grad2_hasDerivAt hb x)).symm

/-! ## The L1ContOn frontier theorems -/

theorem fullSourceCoeff_jointGradClosed_of_L1ContOn
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (u₀cos : ℕ → ℝ)
    {Mu0 : ℝ} (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn
      (coupledChemDivSourceCoeffs p u) T)
    (hlog : DuhamelSourceL1ContOn
      (coupledLogisticSourceCoeffs p u) T)
    (hsumE : ∀ t ∈ Ioo (0 : ℝ) T,
      Summable (fun n =>
        unitIntervalCosineEigenvalue n *
          |fullSourceCoeff p u u₀cos t n|)) :
    ContinuousOn (Function.uncurry (fun t x =>
      deriv (fun y => ∑' n,
        fullSourceCoeff p u u₀cos t n *
          cosineMode n y) x))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) := by
  have hgJC := fullSourceCoeff_gradJC_of_L1ContOn
    p u u₀cos hu0bd hchem hlog
  refine ((hgJC.mono (prod_mono
    (subset_refl _) (subset_univ _))).congr (fun q hq => ?_))
  change Function.uncurry _ q = _
  simp only [Function.uncurry]
  exact (gradSeries_eq_deriv
    (hsumE q.1 (mem_prod.1 hq).1) q.2).symm

theorem fullSourceCoeff_jointGrad2Closed_of_L1ContOn
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (u₀cos : ℕ → ℝ)
    {Mu0 : ℝ} (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn
      (coupledChemDivSourceCoeffs p u) T)
    (hlog : DuhamelSourceL1ContOn
      (coupledLogisticSourceCoeffs p u) T)
    (hsumE : ∀ t ∈ Ioo (0 : ℝ) T,
      Summable (fun n =>
        unitIntervalCosineEigenvalue n *
          |fullSourceCoeff p u u₀cos t n|)) :
    ContinuousOn (Function.uncurry (fun t x =>
      deriv (fun y => deriv (fun z => ∑' n,
        fullSourceCoeff p u u₀cos t n *
          cosineMode n z) y) x))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) := by
  have hg2JC := fullSourceCoeff_grad2JC_of_L1ContOn
    p u u₀cos hu0bd hchem hlog
  refine ((hg2JC.mono (prod_mono
    (subset_refl _) (subset_univ _))).congr (fun q hq => ?_))
  change Function.uncurry _ q = _
  simp only [Function.uncurry]
  exact (grad2Series_eq_deriv2
    (hsumE q.1 (mem_prod.1 hq).1) q.2).symm

end ShenWork.EWA

#print axioms ShenWork.EWA.fullSourceCoeff_jointGradClosed_of_L1ContOn
#print axioms ShenWork.EWA.fullSourceCoeff_jointGrad2Closed_of_L1ContOn
