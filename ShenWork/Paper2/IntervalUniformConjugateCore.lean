import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.Paper2.IntervalMildPicardThreshold
import ShenWork.PDE.HeatKernelGradientEstimates
import ShenWork.PDE.IntervalChemFluxLipschitz
import ShenWork.PDE.IntervalFullKernelSupBound
import ShenWork.PDE.IntervalLogisticLipschitz
import ShenWork.Paper2.IntervalTruncatedLogisticLipschitz

open MeasureTheory Set
open scoped Topology

set_option maxHeartbeats 800000

noncomputable section

namespace ShenWork.IntervalConjugatePicard

open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator intervalFullSemigroupOperator_Linfty_bound)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateDuhamelMap intervalConjugateKernelOperator)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant heatGradientLinftyLinftyConstant_nonneg)
open ShenWork.IntervalMildPicardThreshold
  (intervalDomainLift_measurable_of_continuous')

/-- Uniform, floor-free conjugate Picard budget on the sup-norm ball.

`M0` is the datum bound supplied outside the datum quantifier, and `R = 2*M0`
is the Picard ball radius.  The fields record the part of the conjugate core
whose time choice is purely a function of `(p,M0)`: base heat-ball control,
the maps-to budget assembled from Duhamel leg bounds, and the contraction
budget. -/
structure UniformConjugateMildExistenceCore (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ) where
  T : ℝ
  M0 : ℝ
  R : ℝ
  K : ℝ
  C₀ : ℝ
  CQ : ℝ
  CL : ℝ
  CQsup : ℝ
  CLsup : ℝ
  hT : 0 < T
  hM0 : 0 < M0
  hR : 0 < R
  hK : K < 1
  hK_nn : 0 ≤ K
  hC₀ : 0 ≤ C₀
  hCQ : 0 ≤ CQ
  hCL : 0 ≤ CL
  hCQsup : 0 ≤ CQsup
  hCLsup : 0 ≤ CLsup
  hCQsup_eq :
    CQsup = R *
      (Real.sqrt (∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
          (2 * (p.ν * R ^ p.γ)))
  hCLsup_eq : CLsup = R * (p.a + p.b * R ^ p.α)
  hCQ_eq : CQ =
    Real.sqrt (∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
          (2 * (p.ν * R ^ p.γ)) +
      R * (Real.sqrt (∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
          (2 * (p.ν * (p.γ * R ^ (p.γ - 1))))) +
      R * (Real.sqrt (∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
          (2 * (p.ν * R ^ p.γ))) * p.β *
        (Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) *
            (2 * (p.ν * (p.γ * R ^ (p.γ - 1)))))
  hCL_lip : ∀ r r' : ℝ, |r| ≤ R → |r'| ≤ R →
    |ShenWork.Paper2.BFormPositiveDatumNegPart.truncatedLogisticLocal p r -
      ShenWork.Paper2.BFormPositiveDatumNegPart.truncatedLogisticLocal p r'|
        ≤ CL * |r - r'|
  hR_eq : R = 2 * M0
  hC₀_eq : C₀ = 2 * R
  hK_eq :
    K =
      |p.χ₀| * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * CQ)
        + T * CL
  hbase_ball : ∀ x, |u₀ x| ≤ M0
  hbase_cont : Continuous u₀
  hbase_picard_ball : ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
    |conjugatePicardIter p u₀ 0 t x| ≤ R
  hmapsTo_budget :
    M0 + (|p.χ₀| *
      (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * CQsup)
        + T * CLsup) ≤ R
  hmapsTo : ∀ (w : ℝ → intervalDomainPoint → ℝ),
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |∫ s in (0 : ℝ)..t,
          intervalConjugateKernelOperator (t - s) (chemFluxLifted p (w s)) x.1|
        ≤ heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * CQsup →
      |∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1|
        ≤ T * CLsup →
      |intervalConjugateDuhamelMap p u₀ w t x| ≤ R
  hcontr : |p.χ₀| *
      (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * CQ)
        + T * CL < 1
  hcont_preserved : Continuous u₀
  hmeas_preserved : Measurable (intervalDomainLift u₀)

/-- Uniform existence of the floor-free conjugate core.  The time `T` is chosen
before `u₀` is introduced, and depends only on `p` and the external sup bound
`M`. -/
theorem uniformConjugateMildExistenceCore_exists
    (p : CM2Params) (hα_ge : 1 ≤ p.α) (hγ_ge : 1 ≤ p.γ)
    (M : ℝ) (hM : 0 < M) :
    ∃ T : ℝ, 0 < T ∧
      ∀ {u₀ : intervalDomainPoint → ℝ},
        Continuous u₀ → (∀ x, |u₀ x| ≤ M) →
          ∃ C : UniformConjugateMildExistenceCore p u₀, C.T = T := by
  classical
  set R : ℝ := 2 * M with hRdef
  have hR_pos : 0 < R := by rw [hRdef]; linarith
  have hR_nn : 0 ≤ R := hR_pos.le
  have hM_le_R : M ≤ R := by rw [hRdef]; linarith
  obtain ⟨CL, hCL_nn, hCL_lip⟩ :=
    ShenWork.Paper2.TruncatedLogisticLipschitz.truncatedLogisticLocal_lipschitz_on_bounded
      p hα_ge hR_nn
  set C_RG : ℝ := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * R ^ p.γ)) with hCRG
  have hC_RG_nn : 0 ≤ C_RG :=
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (mul_nonneg p.hν.le (Real.rpow_nonneg hR_nn _)))
  set CQsup : ℝ := R * C_RG with hCQsup
  have hCQsup_nn : 0 ≤ CQsup := mul_nonneg hR_nn hC_RG_nn
  set C_RGL : ℝ := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * (p.γ * R ^ (p.γ - 1)))) with hCRGL
  set C_RV : ℝ := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) *
        (2 * (p.ν * (p.γ * R ^ (p.γ - 1)))) with hCRV
  have hC_RGL_nn : 0 ≤ C_RGL :=
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (mul_nonneg p.hν.le
        (mul_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hγ_ge)
          (Real.rpow_nonneg hR_nn _))))
  have hC_RV_nn : 0 ≤ C_RV :=
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (mul_nonneg p.hν.le
        (mul_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hγ_ge)
          (Real.rpow_nonneg hR_nn _))))
  set CQ : ℝ := C_RG + R * C_RGL + R * C_RG * p.β * C_RV with hCQ
  have hCQ_nn : 0 ≤ CQ :=
    add_nonneg (add_nonneg hC_RG_nn (mul_nonneg hR_nn hC_RGL_nn))
      (mul_nonneg (mul_nonneg (mul_nonneg hR_nn hC_RG_nn) p.hβ) hC_RV_nn)
  set CLsup : ℝ := R * (p.a + p.b * R ^ p.α) with hCLsup
  have hCLsup_nn : 0 ≤ CLsup :=
    mul_nonneg hR_nn (add_nonneg p.ha (mul_nonneg p.hb (Real.rpow_nonneg hR_nn _)))
  set Cg : ℝ := heatGradientLinftyLinftyConstant with hCg
  have hCg_nn : 0 ≤ Cg := heatGradientLinftyLinftyConstant_nonneg
  set CQmax : ℝ := max CQ CQsup with hCQmax
  have hCQmax_nn : 0 ≤ CQmax := le_max_of_le_left hCQ_nn
  set CLmax : ℝ := max CL CLsup with hCLmax
  have hCLmax_nn : 0 ≤ CLmax := le_max_of_le_left hCL_nn
  set A : ℝ := |p.χ₀| * (Cg * 2 * CQmax) + 1 with hA
  set Bc : ℝ := CLmax + 1 with hBc
  have hA_nn : 0 ≤ A := by
    rw [hA]
    have hmain := mul_nonneg (abs_nonneg p.χ₀)
      (mul_nonneg (mul_nonneg hCg_nn (by norm_num : (0 : ℝ) ≤ 2)) hCQmax_nn)
    linarith
  have hBc_nn : 0 ≤ Bc := by rw [hBc]; linarith
  set δ : ℝ := min 1 M with hδ
  have hδ_pos : 0 < δ := lt_min one_pos hM
  obtain ⟨T, hT_pos, hAT⟩ := exists_small_contraction_time_target hA_nn hBc_nn hδ_pos
  have hsqrt_nn : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
  have hbudget_mono : ∀ c l : ℝ, 0 ≤ c → 0 ≤ l → c ≤ CQmax → l ≤ CLmax →
      |p.χ₀| * (Cg * (2 * Real.sqrt T) * c) + T * l ≤ A * Real.sqrt T + Bc * T := by
    intro c l hc _hl hcle hlle
    have hstep : Cg * (2 * Real.sqrt T) * c ≤ Cg * 2 * CQmax * Real.sqrt T := by
      have hcg2 : 0 ≤ Cg * 2 := by positivity
      nlinarith [mul_nonneg hcg2 hsqrt_nn, hcle, hc, hCg_nn]
    have h1 : |p.χ₀| * (Cg * (2 * Real.sqrt T) * c) ≤
        |p.χ₀| * (Cg * 2 * CQmax) * Real.sqrt T := by
      calc |p.χ₀| * (Cg * (2 * Real.sqrt T) * c)
          ≤ |p.χ₀| * (Cg * 2 * CQmax * Real.sqrt T) :=
            mul_le_mul_of_nonneg_left hstep (abs_nonneg _)
        _ = |p.χ₀| * (Cg * 2 * CQmax) * Real.sqrt T := by ring
    have h2 : T * l ≤ T * CLmax := mul_le_mul_of_nonneg_left hlle hT_pos.le
    calc |p.χ₀| * (Cg * (2 * Real.sqrt T) * c) + T * l
        ≤ |p.χ₀| * (Cg * 2 * CQmax) * Real.sqrt T + T * CLmax := by linarith
      _ ≤ A * Real.sqrt T + Bc * T := by
        rw [hA, hBc]; nlinarith [hsqrt_nn, hT_pos.le, hCLmax_nn]
  have hK_lt_one : |p.χ₀| * (Cg * (2 * Real.sqrt T) * CQ) + T * CL < 1 := by
    have hb := hbudget_mono CQ CL hCQ_nn hCL_nn (le_max_left _ _) (le_max_left _ _)
    exact lt_of_le_of_lt hb (lt_of_lt_of_le hAT (min_le_left _ _))
  have hmapsto_budget :
      M + (|p.χ₀| * (Cg * (2 * Real.sqrt T) * CQsup) + T * CLsup) ≤ R := by
    have hb := hbudget_mono CQsup CLsup hCQsup_nn hCLsup_nn
      (le_max_right _ _) (le_max_right _ _)
    have hcorr : |p.χ₀| * (Cg * (2 * Real.sqrt T) * CQsup) + T * CLsup ≤ M :=
      le_trans (le_of_lt (lt_of_le_of_lt hb hAT)) (min_le_right _ _)
    rw [hRdef]; linarith
  refine ⟨T, hT_pos, ?_⟩
  intro u₀ hu₀_cont hu₀_bound
  have hLift_bound : ∀ y, |intervalDomainLift u₀ y| ≤ M := by
    intro y
    unfold intervalDomainLift
    split_ifs with hy
    · exact hu₀_bound ⟨y, hy⟩
    · simp; exact hM.le
  have hLift_meas : Measurable (intervalDomainLift u₀) :=
    intervalDomainLift_measurable_of_continuous' hu₀_cont
  let C : UniformConjugateMildExistenceCore p u₀ := {
    T := T, M0 := M, R := R
    K := |p.χ₀| * (Cg * (2 * Real.sqrt T) * CQ) + T * CL
    C₀ := 2 * R, CQ := CQ, CL := CL, CQsup := CQsup, CLsup := CLsup
    hT := hT_pos, hM0 := hM, hR := hR_pos
    hK := hK_lt_one
    hK_nn := by
      have h1 : 0 ≤ |p.χ₀| * (Cg * (2 * Real.sqrt T) * CQ) :=
        mul_nonneg (abs_nonneg _)
          (mul_nonneg (mul_nonneg hCg_nn (mul_nonneg (by norm_num) hsqrt_nn)) hCQ_nn)
      have h2 : 0 ≤ T * CL := mul_nonneg hT_pos.le hCL_nn
      linarith
    hC₀ := by linarith [hR_pos]
    hCQ := hCQ_nn, hCL := hCL_nn, hCQsup := hCQsup_nn, hCLsup := hCLsup_nn
    hCQsup_eq := by rw [hCQsup, hCRG]
    hCLsup_eq := hCLsup
    hCQ_eq := by rw [hCQ, hCRG, hCRGL, hCRV]
    hCL_lip := hCL_lip
    hR_eq := hRdef
    hC₀_eq := rfl
    hK_eq := by rw [hCg]
    hbase_ball := hu₀_bound
    hbase_cont := hu₀_cont
    hbase_picard_ball := by
      intro t ht _htT x
      simp only [conjugatePicardIter]
      exact le_trans (intervalFullSemigroupOperator_Linfty_bound ht hM.le hLift_bound x.1)
        hM_le_R
    hmapsTo_budget := by simpa [hCg] using hmapsto_budget
    hmapsTo := by
      intro w t ht htT x hchem hlog
      have hH : |intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1| ≤ M :=
        intervalFullSemigroupOperator_Linfty_bound ht hM.le hLift_bound x.1
      have hB : |(-p.χ₀) * (∫ s in (0 : ℝ)..t,
          intervalConjugateKernelOperator (t - s) (chemFluxLifted p (w s)) x.1)|
          ≤ |p.χ₀| * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * CQsup) := by
        rw [abs_mul, abs_neg]
        exact mul_le_mul_of_nonneg_left hchem (abs_nonneg _)
      have hsplit : intervalConjugateDuhamelMap p u₀ w t x
          = intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
            + (-p.χ₀) * (∫ s in (0 : ℝ)..t,
                intervalConjugateKernelOperator (t - s) (chemFluxLifted p (w s)) x.1)
            + ∫ s in (0 : ℝ)..t,
                intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1 := rfl
      rw [hsplit]
      refine le_trans (abs_add_le _ _) ?_
      refine le_trans (add_le_add (le_trans (abs_add_le _ _) (add_le_add hH hB)) hlog) ?_
      have hbudget : M +
          (|p.χ₀| * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * CQsup)
            + T * CLsup) ≤ R := by
        simpa [hCg] using hmapsto_budget
      linarith
    hcontr := by simpa [hCg] using hK_lt_one
    hcont_preserved := hu₀_cont
    hmeas_preserved := hLift_meas
  }
  exact ⟨C, rfl⟩

end ShenWork.IntervalConjugatePicard
