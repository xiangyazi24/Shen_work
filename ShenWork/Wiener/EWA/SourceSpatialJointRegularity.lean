/-
  ShenWork/Wiener/EWA/SourceSpatialJointRegularity.lean

  Joint (t,x)-continuity of the first and second SPATIAL
  derivatives of the χ₀<0 source-form solution synthesis.
-/
import ShenWork.Wiener.EWA.SourceJointRegularity

noncomputable section

namespace ShenWork.EWA

open ShenWork.IntervalDuhamelClosedC2
  (duhamelSpectralCoeff DuhamelSourceTimeC1
    duhamelGainIntegral_summable duhamelCoeff_eigenvalue_mul
    cosineCoeffSeries_grad_hasDerivAt
    cosineCoeffSeries_grad2_hasDerivAt)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs)
open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.IntervalPicardIterateRestart
  (abs_duhamelSpectralCoeff_le)
open ShenWork.CosineSpectrum
  (cosineMode cosineMode_deriv cosineMode_second_deriv)
open ShenWork.IntervalSourceCoefficientTimeC1
  (duhamelSpectralCoeff_hasDerivAt
   duhamelSpectralCoeff_deriv_summable_uniform_bound)
open ShenWork.IntervalDomainRegularityBootstrap
  (reciprocalSquareTerm reciprocalSquareTerm_summable)
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

private theorem fullSourceCoeff_continuous
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (u₀cos : ℕ → ℝ)
    (hchem : DuhamelSourceTimeC1
      (coupledChemDivSourceCoeffs p u))
    (hlog : DuhamelSourceTimeC1
      (coupledLogisticSourceCoeffs p u))
    (n : ℕ) : Continuous
      (fun t : ℝ => fullSourceCoeff p u u₀cos t n) := by
  simp only [fullSourceCoeff]
  exact ((((Real.continuous_exp.comp
    (continuous_id.neg.mul continuous_const)).mul
    continuous_const).add
    (continuous_const.mul
      (continuous_iff_continuousAt.2 fun t =>
        (duhamelSpectralCoeff_hasDerivAt hchem t n
          ).continuousAt))).add
    (continuous_iff_continuousAt.2 fun t =>
      (duhamelSpectralCoeff_hasDerivAt hlog t n
        ).continuousAt))

private theorem eigenvalue_mul_abs_duhamelCoeff_le
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {t : ℝ} (ht : 0 < t) (n : ℕ) :
    unitIntervalCosineEigenvalue n *
      |duhamelSpectralCoeff a t n| ≤
    2 * src.envelope n +
      src.derivBound * reciprocalSquareTerm n := by
  have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue; positivity
  have hkey : unitIntervalCosineEigenvalue n *
      |duhamelSpectralCoeff a t n| ≤
    |a t n| + |a t n -
      unitIntervalCosineEigenvalue n *
        duhamelSpectralCoeff a t n| := by
    rw [show unitIntervalCosineEigenvalue n *
        |duhamelSpectralCoeff a t n| =
        |unitIntervalCosineEigenvalue n *
          duhamelSpectralCoeff a t n| from by
      rw [abs_mul, abs_of_nonneg hlam]]
    calc |unitIntervalCosineEigenvalue n *
          duhamelSpectralCoeff a t n|
        = |a t n - (a t n -
          unitIntervalCosineEigenvalue n *
            duhamelSpectralCoeff a t n)| := by
          congr 1; ring
      _ ≤ |a t n| + |-(a t n -
          unitIntervalCosineEigenvalue n *
            duhamelSpectralCoeff a t n)| :=
          abs_add_le _ _
      _ = |a t n| + |a t n -
          unitIntervalCosineEigenvalue n *
            duhamelSpectralCoeff a t n| := by
          rw [abs_neg]
  calc unitIntervalCosineEigenvalue n *
        |duhamelSpectralCoeff a t n|
      ≤ |a t n| + |a t n -
          unitIntervalCosineEigenvalue n *
            duhamelSpectralCoeff a t n| := hkey
    _ ≤ src.envelope n + (src.envelope n +
        src.derivBound * reciprocalSquareTerm n) := by
        gcongr
        · exact src.henv_bound t ht.le n
        · exact
            duhamelSpectralCoeff_deriv_summable_uniform_bound
              src ht.le n
    _ = 2 * src.envelope n +
        src.derivBound * reciprocalSquareTerm n := by
        ring

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
private theorem fullSourceCoeff_gradJC
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1
      (coupledChemDivSourceCoeffs p u))
    (hlog : DuhamelSourceTimeC1
      (coupledLogisticSourceCoeffs p u)) :
    ContinuousOn (fun q : ℝ × ℝ => ∑' n,
      fullSourceCoeff p u u₀cos q.1 n *
        (-((n : ℝ) * Real.pi) *
          Real.sin ((n : ℝ) * Real.pi * q.2)))
      (Ioi (0 : ℝ) ×ˢ univ) := by
  apply continuousOn_of_forall_continuousAt
  intro p₀ hp₀
  obtain ⟨hp₀1, _⟩ := mem_prod.1 hp₀
  have hp₀pos : 0 < p₀.1 := mem_Ioi.1 hp₀1
  set c := p₀.1 / 2 with hc_def
  set Tb := p₀.1 + 1 with hTb_def
  have hc : 0 < c := by positivity
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
        ((Tb + 2) *
          (hchem.envelope n + hlog.envelope n) +
        (hchem.derivBound + hlog.derivBound) *
          reciprocalSquareTerm n))
  · -- (1) each summand ContinuousOn
    intro n; apply ContinuousOn.mul
    · exact ((fullSourceCoeff_continuous p u u₀cos
        hchem hlog n).comp continuous_fst).continuousOn
    · exact (continuous_const.mul
        (Real.continuous_sin.comp
          (continuous_const.mul continuous_snd))
        ).continuousOn
  · -- (2) summable majorant
    exact (((unitIntervalCosineHeatTrace_single_exp_summable
        hc).add
      (unitIntervalCosineEigenvalue_mul_exp_summable
        hc)).mul_left Mu0).add
      ((((hchem.henv_summable.add
        hlog.henv_summable).mul_left (Tb + 2)).add
        (reciprocalSquareTerm_summable.mul_left
          (hchem.derivBound +
            hlog.derivBound))).mul_left (|p.χ₀| + 1))
  · -- (3) norm bound per term
    intro n q hq
    obtain ⟨ht, _⟩ := mem_prod.1 hq
    obtain ⟨hct, htTb⟩ := mem_Ioo.1 ht
    have ht_pos : 0 < q.1 := lt_trans hc hct
    have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue; positivity
    rw [Real.norm_eq_abs, abs_mul]
    -- |−nπ sin(nπx)| ≤ nπ
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
        (abs_duhamelSpectralCoeff_le hchem ht_pos n)
        (mul_le_mul_of_nonneg_right (le_of_lt htTb)
          (le_trans (abs_nonneg _)
            (hchem.henv_bound 0 le_rfl n)))
    have hBl : |Bl| ≤ Tb * hlog.envelope n :=
      le_trans
        (abs_duhamelSpectralCoeff_le hlog ht_pos n)
        (mul_le_mul_of_nonneg_right (le_of_lt htTb)
          (le_trans (abs_nonneg _)
            (hlog.henv_bound 0 le_rfl n)))
    -- IBP: λ|Bc|, λ|Bl| bounds
    have hEc :=
      eigenvalue_mul_abs_duhamelCoeff_le hchem ht_pos n
    have hEl :=
      eigenvalue_mul_abs_duhamelCoeff_le hlog ht_pos n
    -- (1+λ)|Bc| ≤ (Tb+2)·env_c + dB_c·recip
    have hNc :
        (1 + unitIntervalCosineEigenvalue n) * |Bc| ≤
        (Tb + 2) * hchem.envelope n +
          hchem.derivBound *
            reciprocalSquareTerm n := by
      have : (1 + unitIntervalCosineEigenvalue n) *
          |Bc| = |Bc| +
          unitIntervalCosineEigenvalue n * |Bc| := by
        ring
      linarith [hBc]
    have hNl :
        (1 + unitIntervalCosineEigenvalue n) * |Bl| ≤
        (Tb + 2) * hlog.envelope n +
          hlog.derivBound *
            reciprocalSquareTerm n := by
      have : (1 + unitIntervalCosineEigenvalue n) *
          |Bl| = |Bl| +
          unitIntervalCosineEigenvalue n * |Bl| := by
        ring
      linarith [hBl]
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
    -- Positivity
    have hchi := abs_nonneg p.χ₀
    have hrec_nn : 0 ≤ reciprocalSquareTerm n := by
      unfold reciprocalSquareTerm; positivity
    have henv_c_nn :=
      le_trans (abs_nonneg _)
        (hchem.henv_bound 0 le_rfl n)
    have henv_l_nn :=
      le_trans (abs_nonneg _)
        (hlog.henv_bound 0 le_rfl n)
    have hdb_c_nn : 0 ≤ hchem.derivBound :=
      le_trans (abs_nonneg _)
        (hchem.hderivBound 0 le_rfl 0)
    have hdb_l_nn : 0 ≤ hlog.derivBound :=
      le_trans (abs_nonneg _)
        (hlog.hderivBound 0 le_rfl 0)
    -- Main chain:
    -- |coeff|·|mode| ≤ (|H|+|χ₀||Bc|+|Bl|)·nπ
    --   ≤ (|H|+|χ₀||Bc|+|Bl|)·(1+λ)  [since nπ≤1+λ]
    --   = (1+λ)|H| + |χ₀|·(1+λ)|Bc| + (1+λ)|Bl|
    --   ≤ heatMaj + |χ₀|·chemMaj + logMaj
    --   ≤ heatMaj + (|χ₀|+1)·totalMaj
    -- Step 1
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
    -- Step 2: bound each piece
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
        |p.χ₀| *
          ((Tb + 2) * hchem.envelope n +
          hchem.derivBound *
            reciprocalSquareTerm n) +
        ((Tb + 2) * hlog.envelope n +
          hlog.derivBound *
            reciprocalSquareTerm n) := by
      gcongr
    -- Step 3: absorb into (|χ₀|+1) factor
    have step3 :
        Mu0 *
          (Real.exp
            (-c * unitIntervalCosineEigenvalue n) +
          unitIntervalCosineEigenvalue n *
            Real.exp
              (-c * unitIntervalCosineEigenvalue n)) +
        |p.χ₀| *
          ((Tb + 2) * hchem.envelope n +
          hchem.derivBound *
            reciprocalSquareTerm n) +
        ((Tb + 2) * hlog.envelope n +
          hlog.derivBound *
            reciprocalSquareTerm n) ≤
        Mu0 *
          (Real.exp
            (-c * unitIntervalCosineEigenvalue n) +
          unitIntervalCosineEigenvalue n *
            Real.exp
              (-c * unitIntervalCosineEigenvalue n)) +
        (|p.χ₀| + 1) *
          ((Tb + 2) *
            (hchem.envelope n + hlog.envelope n) +
          (hchem.derivBound + hlog.derivBound) *
            reciprocalSquareTerm n) := by
      nlinarith [
        mul_nonneg hchi henv_l_nn,
        mul_nonneg hchi hrec_nn,
        mul_nonneg hchi
          (mul_nonneg
            (by linarith : (0 : ℝ) ≤ Tb + 2)
            henv_l_nn),
        mul_nonneg hchi
          (mul_nonneg hdb_l_nn hrec_nn),
        mul_nonneg
          (by linarith : (0 : ℝ) ≤ Tb + 2)
          henv_c_nn,
        mul_nonneg hdb_c_nn hrec_nn]
    linarith

/-! ## Second spatial derivative -/

set_option maxHeartbeats 1200000 in
private theorem fullSourceCoeff_grad2JC
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1
      (coupledChemDivSourceCoeffs p u))
    (hlog : DuhamelSourceTimeC1
      (coupledLogisticSourceCoeffs p u)) :
    ContinuousOn (fun q : ℝ × ℝ => ∑' n,
      fullSourceCoeff p u u₀cos q.1 n *
        (-(((n : ℝ) * Real.pi) ^ 2) *
          Real.cos ((n : ℝ) * Real.pi * q.2)))
      (Ioi (0 : ℝ) ×ˢ univ) := by
  apply continuousOn_of_forall_continuousAt
  intro p₀ hp₀
  obtain ⟨hp₀1, _⟩ := mem_prod.1 hp₀
  have hp₀pos : 0 < p₀.1 := mem_Ioi.1 hp₀1
  set c := p₀.1 / 2 with hc_def
  set Tb := p₀.1 + 1 with hTb_def
  have hc : 0 < c := by positivity
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
  -- (nπ)² = λₙ, so |mode| ≤ λₙ
  apply continuousOn_tsum
    (u := fun n =>
      Mu0 *
        (unitIntervalCosineEigenvalue n *
          Real.exp
            (-c * unitIntervalCosineEigenvalue n)) +
      (|p.χ₀| + 1) *
        (2 * (hchem.envelope n + hlog.envelope n) +
        (hchem.derivBound + hlog.derivBound) *
          reciprocalSquareTerm n))
  · intro n; apply ContinuousOn.mul
    · exact ((fullSourceCoeff_continuous p u u₀cos
        hchem hlog n).comp continuous_fst).continuousOn
    · exact (continuous_const.mul
        (Real.continuous_cos.comp
          (continuous_const.mul continuous_snd))
        ).continuousOn
  · exact
      ((unitIntervalCosineEigenvalue_mul_exp_summable
        hc).mul_left Mu0).add
      ((((hchem.henv_summable.add
        hlog.henv_summable).mul_left 2).add
        (reciprocalSquareTerm_summable.mul_left
          (hchem.derivBound +
            hlog.derivBound))).mul_left (|p.χ₀| + 1))
  · intro n q hq
    obtain ⟨ht, _⟩ := mem_prod.1 hq
    obtain ⟨hct, _⟩ := mem_Ioo.1 ht
    have ht_pos : 0 < q.1 := lt_trans hc hct
    have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue; positivity
    rw [Real.norm_eq_abs, abs_mul]
    -- |−(nπ)² cos(nπx)| ≤ λₙ
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
    have hEc :=
      eigenvalue_mul_abs_duhamelCoeff_le hchem ht_pos n
    have hEl :=
      eigenvalue_mul_abs_duhamelCoeff_le hlog ht_pos n
    have hchi := abs_nonneg p.χ₀
    have hrec_nn : 0 ≤ reciprocalSquareTerm n := by
      unfold reciprocalSquareTerm; positivity
    have henv_c_nn :=
      le_trans (abs_nonneg _)
        (hchem.henv_bound 0 le_rfl n)
    have henv_l_nn :=
      le_trans (abs_nonneg _)
        (hlog.henv_bound 0 le_rfl n)
    have hdb_c_nn : 0 ≤ hchem.derivBound :=
      le_trans (abs_nonneg _)
        (hchem.hderivBound 0 le_rfl 0)
    have hdb_l_nn : 0 ≤ hlog.derivBound :=
      le_trans (abs_nonneg _)
        (hlog.hderivBound 0 le_rfl 0)
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
    -- Step 1: product ≤ expanded form
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
    -- Step 2: bound each piece
    have step2 :
        unitIntervalCosineEigenvalue n * |H| +
          |p.χ₀| *
            (unitIntervalCosineEigenvalue n * |Bc|) +
          unitIntervalCosineEigenvalue n * |Bl| ≤
        Mu0 * (unitIntervalCosineEigenvalue n *
          Real.exp
            (-c * unitIntervalCosineEigenvalue n)) +
        |p.χ₀| *
          (2 * hchem.envelope n +
          hchem.derivBound *
            reciprocalSquareTerm n) +
        (2 * hlog.envelope n +
          hlog.derivBound *
            reciprocalSquareTerm n) := by
      gcongr
    -- Step 3: absorb |χ₀| → (|χ₀|+1)
    have step3 :
        Mu0 * (unitIntervalCosineEigenvalue n *
          Real.exp
            (-c * unitIntervalCosineEigenvalue n)) +
        |p.χ₀| *
          (2 * hchem.envelope n +
          hchem.derivBound *
            reciprocalSquareTerm n) +
        (2 * hlog.envelope n +
          hlog.derivBound *
            reciprocalSquareTerm n) ≤
        Mu0 * (unitIntervalCosineEigenvalue n *
          Real.exp
            (-c * unitIntervalCosineEigenvalue n)) +
        (|p.χ₀| + 1) *
          (2 * (hchem.envelope n + hlog.envelope n) +
          (hchem.derivBound + hlog.derivBound) *
            reciprocalSquareTerm n) := by
      nlinarith [
        mul_nonneg hchi henv_l_nn,
        mul_nonneg hchi hrec_nn,
        mul_nonneg hchi
          (mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
            henv_l_nn),
        mul_nonneg hchi
          (mul_nonneg hdb_l_nn hrec_nn),
        mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
          henv_c_nn,
        mul_nonneg hdb_c_nn hrec_nn]
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

/-! ## THE FRONTIER THEOREMS -/

theorem fullSourceCoeff_jointGradClosed
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (u₀cos : ℕ → ℝ)
    {Mu0 : ℝ} (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1
      (coupledChemDivSourceCoeffs p u))
    (hlog : DuhamelSourceTimeC1
      (coupledLogisticSourceCoeffs p u))
    {T : ℝ} (hsumE : ∀ t ∈ Ioo (0 : ℝ) T,
      Summable (fun n =>
        unitIntervalCosineEigenvalue n *
          |fullSourceCoeff p u u₀cos t n|)) :
    ContinuousOn (Function.uncurry (fun t x =>
      deriv (fun y => ∑' n,
        fullSourceCoeff p u u₀cos t n *
          cosineMode n y) x))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) := by
  have hgJC := fullSourceCoeff_gradJC
    p u u₀cos hu0bd hchem hlog
  refine ((hgJC.mono (prod_mono
    (fun _ ht => mem_Ioi.2 (mem_Ioo.1 ht).1)
    (subset_univ _))).congr (fun q hq => ?_))
  change Function.uncurry _ q = _
  simp only [Function.uncurry]
  exact (gradSeries_eq_deriv
    (hsumE q.1 (mem_prod.1 hq).1) q.2).symm

theorem fullSourceCoeff_jointGrad2Closed
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (u₀cos : ℕ → ℝ)
    {Mu0 : ℝ} (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1
      (coupledChemDivSourceCoeffs p u))
    (hlog : DuhamelSourceTimeC1
      (coupledLogisticSourceCoeffs p u))
    {T : ℝ} (hsumE : ∀ t ∈ Ioo (0 : ℝ) T,
      Summable (fun n =>
        unitIntervalCosineEigenvalue n *
          |fullSourceCoeff p u u₀cos t n|)) :
    ContinuousOn (Function.uncurry (fun t x =>
      deriv (fun y => deriv (fun z => ∑' n,
        fullSourceCoeff p u u₀cos t n *
          cosineMode n z) y) x))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) := by
  have hg2JC := fullSourceCoeff_grad2JC
    p u u₀cos hu0bd hchem hlog
  refine ((hg2JC.mono (prod_mono
    (fun _ ht => mem_Ioi.2 (mem_Ioo.1 ht).1)
    (subset_univ _))).congr (fun q hq => ?_))
  change Function.uncurry _ q = _
  simp only [Function.uncurry]
  exact (grad2Series_eq_deriv2
    (hsumE q.1 (mem_prod.1 hq).1) q.2).symm

end ShenWork.EWA

#print axioms ShenWork.EWA.fullSourceCoeff_jointGradClosed
#print axioms ShenWork.EWA.fullSourceCoeff_jointGrad2Closed
