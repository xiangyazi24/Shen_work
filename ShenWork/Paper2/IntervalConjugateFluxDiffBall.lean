/-
  ShenWork/Paper2/IntervalConjugateFluxDiffBall.lean

  Per-slice chemotaxis-flux Lipschitz bound on the nonnegative `M`-ball, factored
  out of the gradient-route threshold proof.  This is kernel-independent (only
  about `chemFluxLifted`), so it serves both the gradient `hcontr` and the
  conjugate-Core `hflux_diff_bound` field.

    `|Q(u)(y) − Q(w)(y)| ≤ C_Q_lip · d`,
    `C_Q_lip = C_RG + M·C_RGL + M·C_RG·β·C_RV`,

  for continuous nonnegative `M`-bounded `u`, `w` with `|u−w| ≤ d` on `[0,1]`.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New names only.
-/
import ShenWork.Paper2.IntervalConjugateChemFluxIntegrable

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace ShenWork.IntervalConjugateFluxDiffBall

open ShenWork.IntervalDomain
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)
open ShenWork.PDE
open ShenWork.IntervalResolverGradientBridge
open ShenWork.IntervalResolverWeakBounds
open ShenWork.Paper2
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalResolverPositivity
open ShenWork.IntervalChemFluxLipschitz (chemFlux_div_lipschitz)

/-- Resolver value `R(u)(y) ≥ 0` for a continuous nonnegative source. -/
private theorem resolverR_nonneg_of_ball
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hu_cont : Continuous u) (hu_nn : ∀ x, 0 ≤ u x)
    {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ intervalNeumannResolverR p u ⟨y, hy⟩ := by
  have hcont_u : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have : Set.restrict (Set.Icc (0:ℝ) 1) (intervalDomainLift u) = u := by
      ext ⟨x, hx⟩; simp [Set.restrict, intervalDomainLift, hx]; rfl
    rw [this]; exact hu_cont
  have hcont_src : Continuous (fun x : intervalDomainPoint ↦ p.ν * (u x) ^ p.γ) :=
    continuous_const.mul (hu_cont.rpow_const (fun x ↦ Or.inr p.hγ.le))
  set clip : ℝ → intervalDomainPoint := fun x ↦
    ⟨max 0 (min x 1), le_max_left 0 _, max_le (by norm_num) (min_le_right x 1)⟩
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
  have hâ : Summable (fun k ↦ (cosineCoeffs f k) ^ 2) := by
    have h := resolverSourceCoeff_re_sq_summable_of_continuousOn p hcont_u
    simp only [intervalNeumannResolverSourceCoeff_zero, sub_zero] at h
    exact h.congr (fun k ↦ by rw [hf_coeff])
  exact intervalNeumannResolverR_nonneg_of_nonneg_source hf_cont hf_nonneg hf_coeff hâ ⟨y, hy⟩

/-- **Per-slice ball chemotaxis-flux Lipschitz bound.** -/
theorem chemFluxLifted_diff_bound_of_ball_slice
    (p : CM2Params) (hγ_ge : 1 ≤ p.γ) {M d : ℝ} (hM : 0 < M) (hd_nn : 0 ≤ d)
    {u w : intervalDomainPoint → ℝ}
    (hu_bound : ∀ x, |u x| ≤ M) (hu_nn : ∀ x, 0 ≤ u x) (hu_cont : Continuous u)
    (hw_bound : ∀ x, |w x| ≤ M) (hw_nn : ∀ x, 0 ≤ w x) (hw_cont : Continuous w)
    (hd : ∀ x, |u x - w x| ≤ d) (y : ℝ) :
    |chemFluxLifted p u y - chemFluxLifted p w y|
      ≤ (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2)
            * (2 * (p.ν * M ^ p.γ))
          + M * (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2)
            * (2 * (p.ν * (p.γ * M ^ (p.γ - 1)))))
          + M * (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2)
            * (2 * (p.ν * M ^ p.γ))) * p.β
            * (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2)
              * (2 * (p.ν * (p.γ * M ^ (p.γ - 1)))))) * d := by
  set C_RG := Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2)
    * (2 * (p.ν * M ^ p.γ)) with hCRG
  set C_RGL := Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2)
    * (2 * (p.ν * (p.γ * M ^ (p.γ - 1)))) with hCRGL
  set C_RV := Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2)
    * (2 * (p.ν * (p.γ * M ^ (p.γ - 1)))) with hCRV
  have hC_RG_nn : 0 ≤ C_RG :=
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (mul_nonneg p.hν.le (Real.rpow_nonneg hM.le _)))
  have hC_Q_lip_nn : 0 ≤ C_RG + M * C_RGL + M * C_RG * p.β * C_RV := by
    have hC_RGL_nn : 0 ≤ C_RGL :=
      mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (by norm_num) (mul_nonneg p.hν.le
          (mul_nonneg p.hγ.le (Real.rpow_nonneg hM.le _))))
    have hC_RV_nn : 0 ≤ C_RV :=
      mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (by norm_num) (mul_nonneg p.hν.le
          (mul_nonneg p.hγ.le (Real.rpow_nonneg hM.le _))))
    exact add_nonneg (add_nonneg hC_RG_nn (mul_nonneg hM.le hC_RGL_nn))
      (mul_nonneg (mul_nonneg (mul_nonneg hM.le hC_RG_nn) p.hβ) hC_RV_nn)
  show |chemFluxLifted p u y - chemFluxLifted p w y|
      ≤ (C_RG + M * C_RGL + M * C_RG * p.β * C_RV) * d
  unfold chemFluxLifted
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
  · have hcont_u : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1) := by
      rw [continuousOn_iff_continuous_restrict]
      have : Set.restrict (Set.Icc (0:ℝ) 1) (intervalDomainLift u) = u := by
        ext ⟨x, hx⟩; simp [Set.restrict, intervalDomainLift, hx]; rfl
      rw [this]; exact hu_cont
    have hcont_w : ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) := by
      rw [continuousOn_iff_continuous_restrict]
      have : Set.restrict (Set.Icc (0:ℝ) 1) (intervalDomainLift w) = w := by
        ext ⟨x, hx⟩; simp [Set.restrict, intervalDomainLift, hx]; rfl
      rw [this]; exact hw_cont
    have hmem_u : ∀ x ∈ Set.Icc (0:ℝ) 1,
        intervalDomainLift u x ∈ Set.Icc (0:ℝ) M := by
      intro x hx; constructor
      · simp [intervalDomainLift, hx]; exact hu_nn ⟨x, hx⟩
      · simp [intervalDomainLift, hx]; exact (abs_le.mp (hu_bound ⟨x, hx⟩)).2
    have hmem_w : ∀ x ∈ Set.Icc (0:ℝ) 1,
        intervalDomainLift w x ∈ Set.Icc (0:ℝ) M := by
      intro x hx; constructor
      · simp [intervalDomainLift, hx]; exact hw_nn ⟨x, hx⟩
      · simp [intervalDomainLift, hx]; exact (abs_le.mp (hw_bound ⟨x, hx⟩)).2
    have hlift_diff : ∀ x ∈ Set.Icc (0:ℝ) 1,
        |intervalDomainLift u x - intervalDomainLift w x| ≤ d := by
      intro x hx; simp [intervalDomainLift, hx]; exact hd ⟨x, hx⟩
    have ha₂ : |intervalDomainLift w y| ≤ M := by
      simp [intervalDomainLift, hy]; exact hw_bound ⟨y, hy⟩
    have had : |intervalDomainLift u y - intervalDomainLift w y| ≤ d := hlift_diff y hy
    have hg₁ : |resolverGradReal p u y| ≤ C_RG :=
      resolverGrad_sup_le_of_bounded p hcont_u
        (fun x hx => (hmem_u x hx).1) (fun x hx => (hmem_u x hx).2) hy
    have hg₂ : |resolverGradReal p w y| ≤ C_RG :=
      resolverGrad_sup_le_of_bounded p hcont_w
        (fun x hx => (hmem_w x hx).1) (fun x hx => (hmem_w x hx).2) hy
    have hgd : |resolverGradReal p u y - resolverGradReal p w y| ≤ C_RGL * d := by
      have h := resolverGrad_diff_sup_le_of_bounded
        p hγ_ge hcont_u hcont_w hmem_u hmem_w hlift_diff hy
      calc |resolverGradReal p u y - resolverGradReal p w y|
          ≤ Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * (p.ν * (p.γ * M ^ (p.γ - 1)) * d)) := h
        _ = C_RGL * d := by rw [hCRGL]; ring
    have hv₁ : 0 ≤ intervalDomainLift (intervalNeumannResolverR p u) y := by
      simp [intervalDomainLift, hy]; exact resolverR_nonneg_of_ball p hu_cont hu_nn hy
    have hv₂ : 0 ≤ intervalDomainLift (intervalNeumannResolverR p w) y := by
      simp [intervalDomainLift, hy]; exact resolverR_nonneg_of_ball p hw_cont hw_nn hy
    have hvd : |intervalDomainLift (intervalNeumannResolverR p u) y
        - intervalDomainLift (intervalNeumannResolverR p w) y| ≤ C_RV * d := by
      simp [intervalDomainLift, hy]
      have h := resolverValue_diff_sup_le_of_bounded
        p hγ_ge hcont_u hcont_w hmem_u hmem_w hlift_diff ⟨y, hy⟩
      calc |intervalNeumannResolverR p u ⟨y, hy⟩ - intervalNeumannResolverR p w ⟨y, hy⟩|
          ≤ Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) *
            (2 * (p.ν * (p.γ * M ^ (p.γ - 1)) * d)) := h
        _ = C_RV * d := by rw [hCRV]; ring
    exact chemFlux_div_lipschitz p.hβ ha₂ hg₁ hg₂ hv₁ hv₂ had hgd hvd hC_RG_nn
  · simp [intervalDomainLift, hy, zero_mul, sub_self, abs_zero]
    exact mul_nonneg hC_Q_lip_nn hd_nn

end ShenWork.IntervalConjugateFluxDiffBall
