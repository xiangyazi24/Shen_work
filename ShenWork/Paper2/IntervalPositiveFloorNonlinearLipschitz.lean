import ShenWork.Paper2.IntervalConjugatePicardFloorCore
import ShenWork.Paper2.IntervalConjugateFluxDiffBall
import ShenWork.Paper2.IntervalConjugateLogisticDiffBall
import ShenWork.Paper2.IntervalDomainL2StaticVDifference

/-!
# Nonlinear Lipschitz estimates on a positive floor

These are the arbitrary-positive-exponent replacements for the old
`alpha,gamma >= 1` estimates on `[0,M]`.
-/

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace ShenWork.IntervalPositiveFloorNonlinearLipschitz

open ShenWork.IntervalDomain
open ShenWork.PDE
open ShenWork.Paper2
open ShenWork.IntervalResolverWeakBounds
open ShenWork.PDE.ResolventEstimate
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)
open ShenWork.IntervalConjugateFluxDiffBall
open ShenWork.IntervalChemFluxLipschitz (chemFlux_div_lipschitz)
open ShenWork.IntervalNeumannFullKernel

def powerLip (q c M : ℝ) : ℝ :=
  q * (c ^ (q - 1) + M ^ (q - 1))

theorem powerLip_nonneg {q c M : ℝ} (hq : 0 < q) (hc : 0 < c) (hcM : c ≤ M) :
    0 ≤ powerLip q c M := by
  unfold powerLip
  exact mul_nonneg hq.le (add_nonneg (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg (hc.le.trans hcM) _))

theorem resolverR_nonneg_of_continuous_nonneg
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hu_cont : Continuous u) (hu_nn : ∀ x, 0 ≤ u x)
    (y : intervalDomainPoint) :
    0 ≤ intervalNeumannResolverR p u y := by
  have hcont_u : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have : Set.restrict (Set.Icc (0:ℝ) 1) (intervalDomainLift u) = u := by
      ext ⟨x, hx⟩
      simp [Set.restrict, intervalDomainLift, hx]
      rfl
    rw [this]
    exact hu_cont
  have hcont_src : Continuous (fun x : intervalDomainPoint ↦ p.ν * (u x) ^ p.γ) :=
    continuous_const.mul (hu_cont.rpow_const (fun _ ↦ Or.inr p.hγ.le))
  set clip : ℝ → intervalDomainPoint := fun x ↦
    ⟨max 0 (min x 1), le_max_left 0 _,
      max_le (by norm_num) (min_le_right x 1)⟩
  have hclip_cont : Continuous clip :=
    Continuous.subtype_mk (continuous_const.max (continuous_id.min continuous_const)) _
  set f : ℝ → ℝ := (fun x : intervalDomainPoint ↦ p.ν * (u x) ^ p.γ) ∘ clip
  have hf_cont : Continuous f := hcont_src.comp hclip_cont
  have hf_nonneg : ∀ z, 0 ≤ f z := fun z ↦
    mul_nonneg p.hν.le (Real.rpow_nonneg (hu_nn _) _)
  have hf_coeff : ∀ k, cosineCoeffs f k =
      (intervalNeumannResolverSourceCoeff p u k).re := by
    intro k
    have hsrc_eq : (intervalNeumannResolverSourceCoeff p u k).re =
        cosineCoeffs (fun x ↦ p.ν * intervalDomainLift u x ^ p.γ) k := by
      simp [cosineCoeffs, intervalNeumannResolverSourceCoeff, Complex.ofReal_re]
    rw [hsrc_eq]
    exact cosineCoeffs_congr_on_Icc (fun x hx ↦ by
      simp only [f, Function.comp, clip]
      have hclip_eq : max 0 (min x 1) = x := by
        rw [min_eq_left hx.2, max_eq_right hx.1]
      simp only [hclip_eq, intervalDomainLift, dif_pos (Set.mem_Icc.mpr hx)]) k
  have ha_sq : Summable (fun k ↦ (cosineCoeffs f k) ^ 2) := by
    have h := resolverSourceCoeff_re_sq_summable_of_continuousOn p hcont_u
    simp only [intervalNeumannResolverSourceCoeff_zero, sub_zero] at h
    exact h.congr (fun k ↦ by rw [hf_coeff])
  exact ShenWork.IntervalResolverPositivity.intervalNeumannResolverR_nonneg_of_nonneg_source
    hf_cont hf_nonneg hf_coeff ha_sq y

theorem source_coeffL2Norm_diff_le_of_pos_bounded
    (p : CM2Params) {u₁ u₂ : intervalDomainPoint → ℝ} {c M D : ℝ}
    (hc : 0 < c)
    (hUc₁ : ContinuousOn (intervalDomainLift u₁) (Set.Icc (0:ℝ) 1))
    (hUc₂ : ContinuousOn (intervalDomainLift u₂) (Set.Icc (0:ℝ) 1))
    (hmem₁ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift u₁ x ∈ Set.Icc c M)
    (hmem₂ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift u₂ x ∈ Set.Icc c M)
    (hD : ∀ x ∈ Set.Icc (0:ℝ) 1,
      |intervalDomainLift u₁ x - intervalDomainLift u₂ x| ≤ D) :
    coeffL2Norm (fun k : ℕ ↦ intervalNeumannResolverSourceCoeff p u₁ k -
        intervalNeumannResolverSourceCoeff p u₂ k)
      ≤ 2 * (p.ν * powerLip p.γ c M * D) := by
  have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hcM : c ≤ M := (hmem₁ 0 h0).1.trans (hmem₁ 0 h0).2
  have hDnn : 0 ≤ D := (abs_nonneg _).trans (hD 0 h0)
  have hLnn : 0 ≤ powerLip p.γ c M := powerLip_nonneg p.hγ hc hcM
  set Lc : ℝ := p.ν * powerLip p.γ c M * D with hLc
  have hLcnn : 0 ≤ Lc := mul_nonneg (mul_nonneg p.hν.le hLnn) hDnn
  have hg₁ : ContinuousOn (fun x : ℝ ↦ p.ν * intervalDomainLift u₁ x ^ p.γ)
      (Set.Icc (0:ℝ) 1) :=
    continuousOn_const.mul (hUc₁.rpow_const (fun _ _ ↦ Or.inr p.hγ.le))
  have hg₂ : ContinuousOn (fun x : ℝ ↦ p.ν * intervalDomainLift u₂ x ^ p.γ)
      (Set.Icc (0:ℝ) 1) :=
    continuousOn_const.mul (hUc₂.rpow_const (fun _ _ ↦ Or.inr p.hγ.le))
  have hcore := sourceCoeff_diff_energy_le_integral_of_continuousOn p hg₁ hg₂
  have hpt : ∀ x ∈ Set.Icc (0:ℝ) 1,
      (p.ν * intervalDomainLift u₁ x ^ p.γ - p.ν * intervalDomainLift u₂ x ^ p.γ) ^ 2
        ≤ Lc ^ 2 := by
    intro x hx
    have hp := rpow_lipschitz_on_pos_Icc p.hγ hc (hmem₁ x hx) (hmem₂ x hx)
    have habs : |p.ν * intervalDomainLift u₁ x ^ p.γ -
        p.ν * intervalDomainLift u₂ x ^ p.γ| ≤ Lc := by
      rw [← mul_sub, abs_mul, abs_of_nonneg p.hν.le, hLc]
      calc
        p.ν * |intervalDomainLift u₁ x ^ p.γ - intervalDomainLift u₂ x ^ p.γ|
            ≤ p.ν * (powerLip p.γ c M * |intervalDomainLift u₁ x - intervalDomainLift u₂ x|) :=
              mul_le_mul_of_nonneg_left hp p.hν.le
        _ ≤ p.ν * (powerLip p.γ c M * D) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hD x hx) hLnn) p.hν.le
        _ = p.ν * powerLip p.γ c M * D := by ring
    nlinarith [abs_nonneg (p.ν * intervalDomainLift u₁ x ^ p.γ -
      p.ν * intervalDomainLift u₂ x ^ p.γ),
      sq_abs (p.ν * intervalDomainLift u₁ x ^ p.γ -
        p.ν * intervalDomainLift u₂ x ^ p.γ), habs, hLcnn]
  have hgcont : ContinuousOn (fun x : ℝ ↦
      (p.ν * intervalDomainLift u₁ x ^ p.γ -
        p.ν * intervalDomainLift u₂ x ^ p.γ) ^ 2) (Set.uIcc (0:ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact (hg₁.sub hg₂).pow 2
  have hint : (∫ x in (0:ℝ)..1,
      (p.ν * intervalDomainLift u₁ x ^ p.γ - p.ν * intervalDomainLift u₂ x ^ p.γ) ^ 2)
      ≤ Lc ^ 2 := by
    have hcI : IntervalIntegrable (fun _ : ℝ ↦ Lc ^ 2) volume 0 1 :=
      (continuous_const : Continuous (fun _ : ℝ ↦ Lc ^ 2)).intervalIntegrable 0 1
    have hi := intervalIntegral.integral_mono_on (by norm_num)
      hgcont.intervalIntegrable
      hcI hpt
    simpa [intervalIntegral.integral_const] using hi
  rw [coeffL2Norm]
  have he : coeffL2Energy (fun k : ℕ ↦ intervalNeumannResolverSourceCoeff p u₁ k -
      intervalNeumannResolverSourceCoeff p u₂ k) ≤ (2 * Lc) ^ 2 := by
    refine hcore.trans ?_
    nlinarith [hint]
  calc
    Real.sqrt (coeffL2Energy (fun k : ℕ ↦ intervalNeumannResolverSourceCoeff p u₁ k -
      intervalNeumannResolverSourceCoeff p u₂ k))
        ≤ Real.sqrt ((2 * Lc) ^ 2) := Real.sqrt_le_sqrt he
    _ = 2 * Lc := by rw [Real.sqrt_sq (mul_nonneg (by norm_num) hLcnn)]
    _ = 2 * (p.ν * powerLip p.γ c M * D) := by rw [hLc]

theorem resolverValue_diff_sup_le_of_pos_bounded
    (p : CM2Params) {u₁ u₂ : intervalDomainPoint → ℝ} {c M D : ℝ}
    (hc : 0 < c)
    (hUc₁ : ContinuousOn (intervalDomainLift u₁) (Set.Icc (0:ℝ) 1))
    (hUc₂ : ContinuousOn (intervalDomainLift u₂) (Set.Icc (0:ℝ) 1))
    (hmem₁ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift u₁ x ∈ Set.Icc c M)
    (hmem₂ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift u₂ x ∈ Set.Icc c M)
    (hD : ∀ x ∈ Set.Icc (0:ℝ) 1, |intervalDomainLift u₁ x - intervalDomainLift u₂ x| ≤ D)
    (x : intervalDomainPoint) :
    |intervalNeumannResolverR p u₁ x - intervalNeumannResolverR p u₂ x| ≤
      Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) *
        (2 * (p.ν * powerLip p.γ c M * D)) := by
  have hsrc := resolverSourceCoeff_diff_re_sq_summable_of_continuousOn p hUc₁ hUc₂
  have hl₁ : Summable (fun k : ℕ ↦ ((intervalNeumannResolverSourceCoeff p u₁ k).re) ^ 2) := by
    simpa [intervalNeumannResolverSourceCoeff_zero, sub_zero] using
      resolverSourceCoeff_re_sq_summable_of_continuousOn p hUc₁
  have hl₂ : Summable (fun k : ℕ ↦ ((intervalNeumannResolverSourceCoeff p u₂ k).re) ^ 2) := by
    simpa [intervalNeumannResolverSourceCoeff_zero, sub_zero] using
      resolverSourceCoeff_re_sq_summable_of_continuousOn p hUc₂
  have hb := intervalNeumannResolverR_sup_lipschitz p u₁ u₂ hsrc x
    (resolver_cosineSeries_summable_of_sourceL2 p hl₁ x.1)
    (resolver_cosineSeries_summable_of_sourceL2 p hl₂ x.1)
  exact hb.trans (mul_le_mul_of_nonneg_left
    (source_coeffL2Norm_diff_le_of_pos_bounded p hc hUc₁ hUc₂ hmem₁ hmem₂ hD)
    (Real.sqrt_nonneg _))

theorem resolverGrad_diff_sup_le_of_pos_bounded
    (p : CM2Params) {u₁ u₂ : intervalDomainPoint → ℝ} {c M D : ℝ}
    (hc : 0 < c)
    (hUc₁ : ContinuousOn (intervalDomainLift u₁) (Set.Icc (0:ℝ) 1))
    (hUc₂ : ContinuousOn (intervalDomainLift u₂) (Set.Icc (0:ℝ) 1))
    (hmem₁ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift u₁ x ∈ Set.Icc c M)
    (hmem₂ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift u₂ x ∈ Set.Icc c M)
    (hD : ∀ x ∈ Set.Icc (0:ℝ) 1, |intervalDomainLift u₁ x - intervalDomainLift u₂ x| ≤ D)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    |resolverGradReal p u₁ x - resolverGradReal p u₂ x| ≤
      Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * powerLip p.γ c M * D)) := by
  have hsrc := resolverSourceCoeff_diff_re_sq_summable_of_continuousOn p hUc₁ hUc₂
  have hl₁ : Summable (fun k : ℕ ↦ ((intervalNeumannResolverSourceCoeff p u₁ k).re) ^ 2) := by
    simpa [intervalNeumannResolverSourceCoeff_zero, sub_zero] using
      resolverSourceCoeff_re_sq_summable_of_continuousOn p hUc₁
  have hl₂ : Summable (fun k : ℕ ↦ ((intervalNeumannResolverSourceCoeff p u₂ k).re) ^ 2) := by
    simpa [intervalNeumannResolverSourceCoeff_zero, sub_zero] using
      resolverSourceCoeff_re_sq_summable_of_continuousOn p hUc₂
  have hb := intervalNeumannResolverR_grad_sup_lipschitz p u₁ u₂ hsrc ⟨x, hx⟩
    (resolver_sineSeries_summable_of_sourceL2 p hl₁ x)
    (resolver_sineSeries_summable_of_sourceL2 p hl₂ x)
  rw [resolverGradReal_eq p u₁ ⟨x, hx⟩, resolverGradReal_eq p u₂ ⟨x, hx⟩]
  exact hb.trans (mul_le_mul_of_nonneg_left
    (source_coeffL2Norm_diff_le_of_pos_bounded p hc hUc₁ hUc₂ hmem₁ hmem₂ hD)
    (Real.sqrt_nonneg _))

/-- Chemotaxis flux is Lipschitz on a continuous positive cone `c ≤ u,w ≤ M`,
for every positive source exponent `γ`. -/
theorem chemFluxLifted_diff_bound_of_pos_slice
    (p : CM2Params) {c M d : ℝ} (hc : 0 < c) (hcM : c ≤ M) (hd_nn : 0 ≤ d)
    {u w : intervalDomainPoint → ℝ}
    (hu_bound : ∀ x, |u x| ≤ M) (hu_floor : ∀ x, c ≤ u x) (hu_cont : Continuous u)
    (hw_bound : ∀ x, |w x| ≤ M) (hw_floor : ∀ x, c ≤ w x) (hw_cont : Continuous w)
    (hd : ∀ x, |u x - w x| ≤ d) (y : ℝ) :
    |chemFluxLifted p u y - chemFluxLifted p w y| ≤
      (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
          (2 * (p.ν * M ^ p.γ)) +
        M * (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
          (2 * (p.ν * powerLip p.γ c M))) +
        M * (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
          (2 * (p.ν * M ^ p.γ))) * p.β *
          (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) *
            (2 * (p.ν * powerLip p.γ c M)))) * d := by
  set C_RG := Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
    (2 * (p.ν * M ^ p.γ)) with hCRG
  set C_RGL := Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
    (2 * (p.ν * powerLip p.γ c M)) with hCRGL
  set C_RV := Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) *
    (2 * (p.ν * powerLip p.γ c M)) with hCRV
  have hM : 0 < M := hc.trans_le hcM
  have hLip : 0 ≤ powerLip p.γ c M := powerLip_nonneg p.hγ hc hcM
  have hC_RG_nn : 0 ≤ C_RG :=
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (mul_nonneg p.hν.le (Real.rpow_nonneg hM.le _)))
  have hC_RGL_nn : 0 ≤ C_RGL :=
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (mul_nonneg p.hν.le hLip))
  have hC_RV_nn : 0 ≤ C_RV :=
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (mul_nonneg p.hν.le hLip))
  have hC_Q_nn : 0 ≤ C_RG + M * C_RGL + M * C_RG * p.β * C_RV :=
    add_nonneg (add_nonneg hC_RG_nn (mul_nonneg hM.le hC_RGL_nn))
      (mul_nonneg (mul_nonneg (mul_nonneg hM.le hC_RG_nn) p.hβ) hC_RV_nn)
  show |chemFluxLifted p u y - chemFluxLifted p w y| ≤
    (C_RG + M * C_RGL + M * C_RG * p.β * C_RV) * d
  unfold chemFluxLifted
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
  · have hcont_u : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1) := by
      rw [continuousOn_iff_continuous_restrict]
      have : Set.restrict (Set.Icc (0:ℝ) 1) (intervalDomainLift u) = u := by
        ext ⟨x, hx⟩
        simp [Set.restrict, intervalDomainLift, hx]
        rfl
      rw [this]
      exact hu_cont
    have hcont_w : ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) := by
      rw [continuousOn_iff_continuous_restrict]
      have : Set.restrict (Set.Icc (0:ℝ) 1) (intervalDomainLift w) = w := by
        ext ⟨x, hx⟩
        simp [Set.restrict, intervalDomainLift, hx]
        rfl
      rw [this]
      exact hw_cont
    have hmem_u : ∀ x ∈ Set.Icc (0:ℝ) 1,
        intervalDomainLift u x ∈ Set.Icc c M := by
      intro x hx
      constructor
      · simpa [intervalDomainLift, hx] using hu_floor ⟨x, hx⟩
      · simp [intervalDomainLift, hx]
        exact (abs_le.mp (hu_bound ⟨x, hx⟩)).2
    have hmem_w : ∀ x ∈ Set.Icc (0:ℝ) 1,
        intervalDomainLift w x ∈ Set.Icc c M := by
      intro x hx
      constructor
      · simpa [intervalDomainLift, hx] using hw_floor ⟨x, hx⟩
      · simp [intervalDomainLift, hx]
        exact (abs_le.mp (hw_bound ⟨x, hx⟩)).2
    have hlift_diff : ∀ x ∈ Set.Icc (0:ℝ) 1,
        |intervalDomainLift u x - intervalDomainLift w x| ≤ d := by
      intro x hx
      simpa [intervalDomainLift, hx] using hd ⟨x, hx⟩
    have ha₂ : |intervalDomainLift w y| ≤ M := by
      simpa [intervalDomainLift, hy] using hw_bound ⟨y, hy⟩
    have had : |intervalDomainLift u y - intervalDomainLift w y| ≤ d :=
      hlift_diff y hy
    have hg₁ : |resolverGradReal p u y| ≤ C_RG :=
      resolverGrad_sup_le_of_bounded p hcont_u
        (fun x hx ↦ hc.le.trans (hmem_u x hx).1)
        (fun x hx ↦ (hmem_u x hx).2) hy
    have hg₂ : |resolverGradReal p w y| ≤ C_RG :=
      resolverGrad_sup_le_of_bounded p hcont_w
        (fun x hx ↦ hc.le.trans (hmem_w x hx).1)
        (fun x hx ↦ (hmem_w x hx).2) hy
    have hgd : |resolverGradReal p u y - resolverGradReal p w y| ≤ C_RGL * d := by
      have h := resolverGrad_diff_sup_le_of_pos_bounded
        p hc hcont_u hcont_w hmem_u hmem_w hlift_diff hy
      calc
        |resolverGradReal p u y - resolverGradReal p w y| ≤
            Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
              (2 * (p.ν * powerLip p.γ c M * d)) := h
        _ = C_RGL * d := by rw [hCRGL]; ring
    have hv₁ : 0 ≤ intervalDomainLift (intervalNeumannResolverR p u) y := by
      simp [intervalDomainLift, hy]
      exact resolverR_nonneg_of_continuous_nonneg p hu_cont
        (fun x ↦ (by linarith [hu_floor x] : 0 ≤ u x)) ⟨y, hy⟩
    have hv₂ : 0 ≤ intervalDomainLift (intervalNeumannResolverR p w) y := by
      simp [intervalDomainLift, hy]
      exact resolverR_nonneg_of_continuous_nonneg p hw_cont
        (fun x ↦ (by linarith [hw_floor x] : 0 ≤ w x)) ⟨y, hy⟩
    have hvd : |intervalDomainLift (intervalNeumannResolverR p u) y -
        intervalDomainLift (intervalNeumannResolverR p w) y| ≤ C_RV * d := by
      simp [intervalDomainLift, hy]
      have h := resolverValue_diff_sup_le_of_pos_bounded
        p hc hcont_u hcont_w hmem_u hmem_w hlift_diff ⟨y, hy⟩
      calc
        |intervalNeumannResolverR p u ⟨y, hy⟩ - intervalNeumannResolverR p w ⟨y, hy⟩| ≤
            Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) *
              (2 * (p.ν * powerLip p.γ c M * d)) := h
        _ = C_RV * d := by rw [hCRV]; ring
    exact chemFlux_div_lipschitz p.hβ ha₂ hg₁ hg₂ hv₁ hv₂ had hgd hvd hC_RG_nn
  · simp [intervalDomainLift, hy, zero_mul, sub_self, abs_zero]
    exact mul_nonneg hC_Q_nn hd_nn

theorem logisticReaction_lipschitz_on_pos_Icc
    (p : CM2Params) {c M r s : ℝ} (hc : 0 < c)
    (hr : r ∈ Set.Icc c M) (hs : s ∈ Set.Icc c M) :
    |r * (p.a - p.b * r ^ p.α) - s * (p.a - p.b * s ^ p.α)| ≤
      (p.a + p.b * powerLip (p.α + 1) c M) * |r - s| := by
  have hrpos : 0 < r := hc.trans_le hr.1
  have hspos : 0 < s := hc.trans_le hs.1
  have hpowdiff := rpow_lipschitz_on_pos_Icc
    (γ := p.α + 1) (δ := c) (M := M) (a := r) (b := s)
    (by linarith [p.hα]) hc hr hs
  have hpowdiff' : |r ^ (p.α + 1) - s ^ (p.α + 1)| ≤
      powerLip (p.α + 1) c M * |r - s| := by
    simpa [powerLip] using hpowdiff
  have hmain :
      r * (p.a - p.b * r ^ p.α) - s * (p.a - p.b * s ^ p.α) =
        p.a * (r - s) - p.b * (r ^ (p.α + 1) - s ^ (p.α + 1)) := by
    rw [Real.rpow_add_one (ne_of_gt hrpos), Real.rpow_add_one (ne_of_gt hspos)]
    ring
  rw [hmain]
  calc
    |p.a * (r - s) - p.b * (r ^ (p.α + 1) - s ^ (p.α + 1))|
        ≤ |p.a * (r - s)| + |p.b * (r ^ (p.α + 1) - s ^ (p.α + 1))| :=
          abs_sub _ _
    _ = p.a * |r - s| + p.b * |r ^ (p.α + 1) - s ^ (p.α + 1)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg p.ha, abs_of_nonneg p.hb]
    _ ≤ p.a * |r - s| + p.b * (powerLip (p.α + 1) c M * |r - s|) := by
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hpowdiff' p.hb)
    _ = (p.a + p.b * powerLip (p.α + 1) c M) * |r - s| := by ring

#print axioms source_coeffL2Norm_diff_le_of_pos_bounded
#print axioms resolverValue_diff_sup_le_of_pos_bounded
#print axioms resolverGrad_diff_sup_le_of_pos_bounded
#print axioms chemFluxLifted_diff_bound_of_pos_slice
#print axioms logisticReaction_lipschitz_on_pos_Icc

end ShenWork.IntervalPositiveFloorNonlinearLipschitz

end
