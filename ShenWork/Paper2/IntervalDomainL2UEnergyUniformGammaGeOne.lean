/-
  Uniform (τ-independent, **`M`-only**, no `δ>0`) energy differential inequality for the
  `γ ≥ 1` regime (Piece 2′).

  This is the γ≥1-only **strengthening** of `IntervalDomainL2UEnergyUniform`: when
  `1 ≤ p.γ`, the local Lipschitz constant of `x ↦ x^γ` on `[0,M]` is `L_γ = γ·M^{γ-1}`
  (well-defined since `γ-1 ≥ 0`), with NO positive lower bound `δ` needed.  The whole
  chain (`source_integral_le_Eu_uniform_zeroM` → `static_v_*_L2_le_Eu_uniform_zeroM` →
  `flux_diff_L2_le_Eu_uniform_zeroM` → `intervalDomainL2U_energy_diffIneq_bound_uniform_explicit_zeroM`
  → `gronwall_const_of_uniformLiftBoundZeroM` → `GlobalSolutionGluingFromReachability_of_regime_gammaGeOne`)
  is the δ-free analogue of the general chain, structurally identical except the
  Lipschitz constant `L_γ` is the single term `γ·M^{γ-1}` (vs `γ·(δ^{γ-1}+M^{γ-1})`).

  No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainL2UEnergyUniform

open MeasureTheory intervalIntegral
open ShenWork.IntervalDomain
open ShenWork.PDE ShenWork.IntervalEllipticCharacterization
open ShenWork.PDE.ResolventEstimate
open ShenWork.IntervalResolverGradientBridge
open scoped Topology BigOperators

namespace ShenWork.Paper2

noncomputable section

/-! ## `[0,M]`-Lipschitz of `x ↦ x^γ` for `γ ≥ 1`

For `γ ≥ 1` and `a, b ∈ [0, M]`, `|a^γ − b^γ| ≤ γ·M^{γ−1}·|a−b|`.  The derivative
`γ·x^{γ−1}` is well-defined (no `x ≠ 0` needed since `γ-1 ≥ 0` lets us invoke
`Real.hasDerivAt_rpow_const (Or.inr hγ_ge_one)`), and is bounded by `γ·M^{γ−1}` on `[0,M]`
since `γ-1 ≥ 0` makes `x^{γ-1}` monotone increasing.  Plain MVT on the convex `Icc 0 M`. -/
theorem rpow_lipschitz_on_Icc_zeroM_of_one_le_gamma
    {γ M : ℝ} (hγ : 1 ≤ γ) (hMnn : 0 ≤ M) {a b : ℝ}
    (ha : a ∈ Set.Icc (0:ℝ) M) (hb : b ∈ Set.Icc (0:ℝ) M) :
    |a ^ γ - b ^ γ| ≤ γ * M ^ (γ - 1) * |a - b| := by
  set L : ℝ := γ * M ^ (γ - 1) with hL
  -- Derivative bound on `Icc 0 M`.
  have hbound : ∀ x ∈ Set.Icc (0:ℝ) M, ‖γ * x ^ (γ - 1)‖ ≤ L := by
    intro x hx
    have hxnn : 0 ≤ x := hx.1
    have hxle : x ≤ M := hx.2
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      have : 0 ≤ γ := le_trans zero_le_one hγ
      have : 0 ≤ x ^ (γ - 1) := Real.rpow_nonneg hxnn _
      positivity)]
    -- `x^(γ-1) ≤ M^(γ-1)` (monotone since `γ-1 ≥ 0`).
    have hxbound : x ^ (γ - 1) ≤ M ^ (γ - 1) :=
      Real.rpow_le_rpow hxnn hxle (by linarith)
    have hγnn : 0 ≤ γ := le_trans zero_le_one hγ
    have : γ * x ^ (γ - 1) ≤ γ * M ^ (γ - 1) :=
      mul_le_mul_of_nonneg_left hxbound hγnn
    rwa [hL]
  -- MVT on the convex `Icc 0 M`.
  have hconv : Convex ℝ (Set.Icc (0:ℝ) M) := convex_Icc 0 M
  have hderiv : ∀ x ∈ Set.Icc (0:ℝ) M,
      HasDerivWithinAt (fun y : ℝ => y ^ γ) (γ * x ^ (γ - 1)) (Set.Icc (0:ℝ) M) x := by
    intro x _
    -- For `γ ≥ 1`, the `Or.inr` branch of `Real.hasDerivAt_rpow_const` applies (no `x ≠ 0`).
    exact (Real.hasDerivAt_rpow_const (Or.inr hγ)).hasDerivWithinAt
  have hmvt := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hb ha
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  exact hmvt

/-! ## Source-integral bound with `[0,M]` (γ≥1 variant) -/

/-- **Uniform source-difference `L²` mass, `γ≥1` zero-lower-bound variant.**  With
`lift(uᵢ τ) ∈ [0,M]` on `[0,1]` (NO `δ>0` needed) and `γ ≥ 1`, the source difference
`L²` mass is `≤ (ν·γ·M^{γ-1})²·E_u`.  Proven directly from
`rpow_lipschitz_on_Icc_zeroM_of_one_le_gamma`. -/
theorem source_integral_le_Eu_uniform_zeroM
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {M τ : ℝ} (hMnn : 0 ≤ M) (hγ_ge_one : 1 ≤ p.γ)
    (hmem₁ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₁ τ) x ∈ Set.Icc (0:ℝ) M)
    (hmem₂ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₂ τ) x ∈ Set.Icc (0:ℝ) M)
    (hτ₁ : τ ∈ Set.Ioo (0 : ℝ) T₁) (hτ₂ : τ ∈ Set.Ioo (0 : ℝ) T₂) :
    (∫ x in (0:ℝ)..1, (p.ν * intervalDomainLift (u₁ τ) x ^ p.γ
        - p.ν * intervalDomainLift (u₂ τ) x ^ p.γ) ^ 2)
      ≤ (p.ν * (p.γ * M ^ (p.γ - 1))) ^ 2 *
          intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ := by
  classical
  set L : ℝ := p.γ * M ^ (p.γ - 1) with hLdef
  have hptwise : ∀ x ∈ Set.Icc (0:ℝ) 1,
      (p.ν * intervalDomainLift (u₁ τ) x ^ p.γ
        - p.ν * intervalDomainLift (u₂ τ) x ^ p.γ) ^ 2
      ≤ (p.ν * L) ^ 2 *
        (intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x) ^ 2 := by
    intro x hxIcc
    have hlip := rpow_lipschitz_on_Icc_zeroM_of_one_le_gamma hγ_ge_one hMnn
      (hmem₁ x hxIcc) (hmem₂ x hxIcc)
    have habs : |intervalDomainLift (u₁ τ) x ^ p.γ - intervalDomainLift (u₂ τ) x ^ p.γ|
        ≤ L * |intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x| := hlip
    have hsq := mul_self_le_mul_self (abs_nonneg _) habs
    have hsq2 : (intervalDomainLift (u₁ τ) x ^ p.γ - intervalDomainLift (u₂ τ) x ^ p.γ) ^ 2
        ≤ L ^ 2 * (intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x) ^ 2 := by
      rw [← sq_abs (intervalDomainLift (u₁ τ) x ^ p.γ - intervalDomainLift (u₂ τ) x ^ p.γ),
          ← sq_abs (intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x)]
      calc |intervalDomainLift (u₁ τ) x ^ p.γ - intervalDomainLift (u₂ τ) x ^ p.γ| ^ 2
          = |intervalDomainLift (u₁ τ) x ^ p.γ - intervalDomainLift (u₂ τ) x ^ p.γ| *
            |intervalDomainLift (u₁ τ) x ^ p.γ - intervalDomainLift (u₂ τ) x ^ p.γ| := by ring
        _ ≤ (L * |intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x|) *
            (L * |intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x|) := hsq
        _ = L ^ 2 * |intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x| ^ 2 := by ring
    have hνsq : (0:ℝ) ≤ p.ν ^ 2 := by positivity
    calc (p.ν * intervalDomainLift (u₁ τ) x ^ p.γ
            - p.ν * intervalDomainLift (u₂ τ) x ^ p.γ) ^ 2
        = p.ν ^ 2 *
            (intervalDomainLift (u₁ τ) x ^ p.γ - intervalDomainLift (u₂ τ) x ^ p.γ) ^ 2 := by ring
      _ ≤ p.ν ^ 2 *
            (L ^ 2 * (intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq2 hνsq
      _ = (p.ν * L) ^ 2 *
            (intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x) ^ 2 := by ring
  have hEu : intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ
      = ∫ x in (0:ℝ)..1,
        (intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x) ^ 2 := by
    unfold intervalDomainClassicalL2DifferenceEnergyU
    show intervalDomainIntegral (fun x => (u₁ τ x - u₂ τ x) ^ 2)
      = ∫ x in (0:ℝ)..1, (intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x) ^ 2
    unfold intervalDomainIntegral
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    simp only [intervalDomainLift, hx, dif_pos]
  rw [hEu, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ hptwise
  · have hc1 := source_continuousOn_Icc hsol₁ hτ₁
    have hc2 := source_continuousOn_Icc hsol₂ hτ₂
    have : ContinuousOn (fun x => (p.ν * intervalDomainLift (u₁ τ) x ^ p.γ
        - p.ν * intervalDomainLift (u₂ τ) x ^ p.γ) ^ 2) (Set.uIcc (0:ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact ((hc1.sub hc2).pow 2)
    exact this.intervalIntegrable
  · have hcu1 : ContinuousOn (intervalDomainLift (u₁ τ)) (Set.Icc (0:ℝ) 1) :=
      ((hsol₁.regularity.2.2.2.2.2.2.1 τ hτ₁).1.1).continuousOn
    have hcu2 : ContinuousOn (intervalDomainLift (u₂ τ)) (Set.Icc (0:ℝ) 1) :=
      ((hsol₂.regularity.2.2.2.2.2.2.1 τ hτ₂).1.1).continuousOn
    have : ContinuousOn (fun x => (p.ν * L) ^ 2 *
        (intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x) ^ 2)
        (Set.uIcc (0:ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact continuousOn_const.mul ((hcu1.sub hcu2).pow 2)
    exact this.intervalIntegrable

/-! ## Static `v`-control with `[0,M]` (γ≥1 variants)

These mirror `static_v_value_L2_le_Eu_uniform` / `static_v_grad_L2_le_Eu_uniform` but
replace `source_integral_le_Eu_uniform_q` by `source_integral_le_Eu_uniform_zeroM`.  The
constant becomes `(ν·γ·M^{γ-1})²` (vs `(ν·γ·(δ^{γ-1}+M^{γ-1}))²`). -/

/-- **Uniform static `v`-value control, γ≥1 zero-lower-bound variant.**  With
`lift(uᵢ τ) ∈ [0,M]` on `[0,1]` and `γ≥1`,
`∫₀¹(lift v₁ − lift v₂)² ≤ Cval_unif_zeroM · E_u` with explicit τ-independent
`Cval_unif_zeroM = (∑ₖ weightₖ²)·4·(ν·γ·M^{γ-1})²`. -/
theorem static_v_value_L2_le_Eu_uniform_zeroM
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {M τ : ℝ} (hMnn : 0 ≤ M) (hγ_ge_one : 1 ≤ p.γ)
    (hmem₁ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₁ τ) x ∈ Set.Icc (0:ℝ) M)
    (hmem₂ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₂ τ) x ∈ Set.Icc (0:ℝ) M)
    (hτ₁ : τ ∈ Set.Ioo (0 : ℝ) T₁) (hτ₂ : τ ∈ Set.Ioo (0 : ℝ) T₂) :
    (∫ x in (0:ℝ)..1,
      (intervalDomainLift (v₁ τ) x - intervalDomainLift (v₂ τ) x) ^ 2)
      ≤ ((Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2)) ^ 2 * 4 *
          (p.ν * (p.γ * M ^ (p.γ - 1))) ^ 2) *
        intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ := by
  classical
  set Csup2 : ℝ := (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2)) ^ 2
    with hCsup2
  set A : ℕ → ℂ := fun k => intervalNeumannResolverSourceCoeff p (u₁ τ) k -
    intervalNeumannResolverSourceCoeff p (u₂ τ) k with hA
  have hCsup2_nn : 0 ≤ Csup2 := by rw [hCsup2]; positivity
  have hCe_nn : 0 ≤ coeffL2Energy A := by
    unfold coeffL2Energy; exact tsum_nonneg (fun k => by positivity)
  have hsrc := source_resolverCoeff_re_sq_summable hsol₁ hsol₂ hτ₁ hτ₂
  set B : ℝ := Csup2 * coeffL2Energy A with hB
  have hpt : ∀ x ∈ Set.Ioo (0:ℝ) 1,
      (intervalDomainLift (v₁ τ) x - intervalDomainLift (v₂ τ) x) ^ 2 ≤ B := by
    intro x hxIoo
    have h1 := solution_v_eq_resolver_pointwise_unconditional hsol₁ hτ₁ hxIoo
    have h2 := solution_v_eq_resolver_pointwise_unconditional hsol₂ hτ₂ hxIoo
    have hsum₁ := solution_resolver_cosineSeries_summable hsol₁ hτ₁ x
    have hsum₂ := solution_resolver_cosineSeries_summable hsol₂ hτ₂ x
    have hbound := intervalNeumannResolverR_sup_lipschitz p (u₁ τ) (u₂ τ) hsrc
      ⟨x, Set.Ioo_subset_Icc_self hxIoo⟩ hsum₁ hsum₂
    rw [← h1, ← h2]
    have hge : |intervalNeumannResolverR p (u₁ τ) ⟨x, Set.Ioo_subset_Icc_self hxIoo⟩ -
        intervalNeumannResolverR p (u₂ τ) ⟨x, Set.Ioo_subset_Icc_self hxIoo⟩|
        ≤ Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) *
          coeffL2Norm A := hbound
    have hsq := mul_self_le_mul_self (abs_nonneg _) hge
    rw [← sq_abs]
    calc |intervalNeumannResolverR p (u₁ τ) ⟨x, Set.Ioo_subset_Icc_self hxIoo⟩ -
            intervalNeumannResolverR p (u₂ τ) ⟨x, Set.Ioo_subset_Icc_self hxIoo⟩| ^ 2
        = |intervalNeumannResolverR p (u₁ τ) ⟨x, Set.Ioo_subset_Icc_self hxIoo⟩ -
            intervalNeumannResolverR p (u₂ τ) ⟨x, Set.Ioo_subset_Icc_self hxIoo⟩| *
          |intervalNeumannResolverR p (u₁ τ) ⟨x, Set.Ioo_subset_Icc_self hxIoo⟩ -
            intervalNeumannResolverR p (u₂ τ) ⟨x, Set.Ioo_subset_Icc_self hxIoo⟩| := by ring
      _ ≤ (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) * coeffL2Norm A) *
          (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) * coeffL2Norm A) := hsq
      _ = B := by
          have hWnn : 0 ≤ ∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2 :=
            tsum_nonneg (fun k => sq_nonneg _)
          rw [hB, hCsup2]; unfold coeffL2Norm
          rw [Real.sq_sqrt hWnn,
            show (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) *
                Real.sqrt (coeffL2Energy A)) *
              (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) *
                Real.sqrt (coeffL2Energy A))
              = (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) *
                  Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2)) *
                (Real.sqrt (coeffL2Energy A) * Real.sqrt (coeffL2Energy A)) by ring,
            Real.mul_self_sqrt hWnn, Real.mul_self_sqrt hCe_nn]
  have hintLHS : IntervalIntegrable
      (fun x => (intervalDomainLift (v₁ τ) x - intervalDomainLift (v₂ τ) x) ^ 2) volume 0 1 := by
    have hc1 : ContinuousOn (intervalDomainLift (v₁ τ)) (Set.Icc (0:ℝ) 1) :=
      ((hsol₁.regularity.2.2.2.2.2.2.1 τ hτ₁).2.1).continuousOn
    have hc2 : ContinuousOn (intervalDomainLift (v₂ τ)) (Set.Icc (0:ℝ) 1) :=
      ((hsol₂.regularity.2.2.2.2.2.2.1 τ hτ₂).2.1).continuousOn
    have : ContinuousOn (fun x => (intervalDomainLift (v₁ τ) x -
        intervalDomainLift (v₂ τ) x) ^ 2) (Set.uIcc (0:ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact (hc1.sub hc2).pow 2
    exact this.intervalIntegrable
  have hle_int : (∫ x in (0:ℝ)..1,
        (intervalDomainLift (v₁ τ) x - intervalDomainLift (v₂ τ) x) ^ 2) ≤ B := by
    have hBI : IntervalIntegrable (fun _ : ℝ => B) volume 0 1 :=
      (continuous_const).intervalIntegrable 0 1
    have hmono : (∫ x in (0:ℝ)..1,
        (intervalDomainLift (v₁ τ) x - intervalDomainLift (v₂ τ) x) ^ 2)
        ≤ ∫ _ in (0:ℝ)..1, B := by
      refine intervalIntegral.integral_mono_ae_restrict (by norm_num) hintLHS hBI ?_
      refine (ae_restrict_iff' (measurableSet_Icc (a := (0:ℝ)) (b := 1))).2 ?_
      have hnull : volume (insert (0:ℝ) ({(1:ℝ)} : Set ℝ)) = 0 :=
        Set.Finite.measure_zero ((Set.finite_singleton (1:ℝ)).insert (0:ℝ)) volume
      refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      push_neg at hx
      obtain ⟨hxIcc, hne⟩ := hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      by_contra hcon
      push_neg at hcon
      obtain ⟨hx0, hx1⟩ := hcon
      exact absurd (hpt x ⟨lt_of_le_of_ne hxIcc.1 (Ne.symm hx0),
        lt_of_le_of_ne hxIcc.2 hx1⟩) (not_le.mpr hne)
    have hconst : (∫ _x in (0:ℝ)..1, B ∂volume) = B := by
      rw [intervalIntegral.integral_const, sub_zero, one_smul]
    rwa [hconst] at hmono
  have hEnergy_le := sourceCoeff_diff_energy_le_integral hsol₁ hsol₂ hτ₁ hτ₂
  have hsrcint := source_integral_le_Eu_uniform_zeroM hsol₁ hsol₂ hMnn hγ_ge_one
    hmem₁ hmem₂ hτ₁ hτ₂
  set L : ℝ := p.γ * M ^ (p.γ - 1) with hLdef
  have hEu_nn : 0 ≤ intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ :=
    intervalDomainClassicalL2DifferenceEnergyU_nonneg u₁ u₂ τ
  refine hle_int.trans ?_
  have hstep1 : B ≤ Csup2 * (4 * ∫ x in (0:ℝ)..1,
      (p.ν * intervalDomainLift (u₁ τ) x ^ p.γ
        - p.ν * intervalDomainLift (u₂ τ) x ^ p.γ) ^ 2) := by
    rw [hB]; exact mul_le_mul_of_nonneg_left hEnergy_le hCsup2_nn
  calc B ≤ Csup2 * (4 * ∫ x in (0:ℝ)..1,
        (p.ν * intervalDomainLift (u₁ τ) x ^ p.γ
          - p.ν * intervalDomainLift (u₂ τ) x ^ p.γ) ^ 2) := hstep1
    _ ≤ Csup2 * (4 * ((p.ν * L) ^ 2 *
          intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ)) := by
        apply mul_le_mul_of_nonneg_left _ hCsup2_nn
        apply mul_le_mul_of_nonneg_left hsrcint (by norm_num)
    _ = (Csup2 * 4 * (p.ν * L) ^ 2) *
          intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ := by ring

/-- **Uniform static `v`-gradient control, γ≥1 zero-lower-bound variant.** -/
theorem static_v_grad_L2_le_Eu_uniform_zeroM
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {M τ : ℝ} (hMnn : 0 ≤ M) (hγ_ge_one : 1 ≤ p.γ)
    (hmem₁ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₁ τ) x ∈ Set.Icc (0:ℝ) M)
    (hmem₂ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₂ τ) x ∈ Set.Icc (0:ℝ) M)
    (hτ₁ : τ ∈ Set.Ioo (0 : ℝ) T₁) (hτ₂ : τ ∈ Set.Ioo (0 : ℝ) T₂) :
    (∫ x in (0:ℝ)..1,
      (resolverGradReal p (u₁ τ) x - resolverGradReal p (u₂ τ) x) ^ 2)
      ≤ ((Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2)) ^ 2 * 4 *
          (p.ν * (p.γ * M ^ (p.γ - 1))) ^ 2) *
        intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ := by
  classical
  set Cg2 : ℝ := (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2)) ^ 2
    with hCg2
  set A : ℕ → ℂ := fun k => intervalNeumannResolverSourceCoeff p (u₁ τ) k -
    intervalNeumannResolverSourceCoeff p (u₂ τ) k with hA
  have hCg2_nn : 0 ≤ Cg2 := by rw [hCg2]; positivity
  have hCe_nn : 0 ≤ coeffL2Energy A := by
    unfold coeffL2Energy; exact tsum_nonneg (fun k => by positivity)
  have hsrc := source_resolverCoeff_re_sq_summable hsol₁ hsol₂ hτ₁ hτ₂
  set B : ℝ := Cg2 * coeffL2Energy A with hB
  have hpt : ∀ x ∈ Set.Icc (0:ℝ) 1,
      (resolverGradReal p (u₁ τ) x - resolverGradReal p (u₂ τ) x) ^ 2 ≤ B := by
    intro x hx
    have hsum₁ := solution_resolver_sineSeries_summable hsol₁ hτ₁ x
    have hsum₂ := solution_resolver_sineSeries_summable hsol₂ hτ₂ x
    have hbound := intervalNeumannResolverR_grad_sup_lipschitz p (u₁ τ) (u₂ τ) hsrc
      ⟨x, hx⟩ hsum₁ hsum₂
    rw [resolverGradReal_eq p (u₁ τ) ⟨x, hx⟩, resolverGradReal_eq p (u₂ τ) ⟨x, hx⟩]
    have hge : |intervalNeumannResolverRGrad p (u₁ τ) ⟨x, hx⟩ -
        intervalNeumannResolverRGrad p (u₂ τ) ⟨x, hx⟩|
        ≤ Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
          coeffL2Norm A := hbound
    have hsq := mul_self_le_mul_self (abs_nonneg _) hge
    rw [← sq_abs]
    calc |intervalNeumannResolverRGrad p (u₁ τ) ⟨x, hx⟩ -
            intervalNeumannResolverRGrad p (u₂ τ) ⟨x, hx⟩| ^ 2
        = |intervalNeumannResolverRGrad p (u₁ τ) ⟨x, hx⟩ -
            intervalNeumannResolverRGrad p (u₂ τ) ⟨x, hx⟩| *
          |intervalNeumannResolverRGrad p (u₁ τ) ⟨x, hx⟩ -
            intervalNeumannResolverRGrad p (u₂ τ) ⟨x, hx⟩| := by ring
      _ ≤ (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) * coeffL2Norm A) *
          (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) * coeffL2Norm A) := hsq
      _ = B := by
          have hWnn : 0 ≤ ∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2 :=
            tsum_nonneg (fun k => sq_nonneg _)
          rw [hB, hCg2]; unfold coeffL2Norm
          rw [Real.sq_sqrt hWnn,
            show (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
                Real.sqrt (coeffL2Energy A)) *
              (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
                Real.sqrt (coeffL2Energy A))
              = (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
                  Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2)) *
                (Real.sqrt (coeffL2Energy A) * Real.sqrt (coeffL2Energy A)) by ring,
            Real.mul_self_sqrt hWnn, Real.mul_self_sqrt hCe_nn]
  have hcontGrad : ∀ {Tj : ℝ} {uj vj : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p Tj uj vj →
      τ ∈ Set.Ioo (0:ℝ) Tj →
      Continuous (fun x : ℝ => resolverGradReal p (uj τ) x) := by
    intro Tj uj vj hsolj hτj
    have hdecay := sourceCoeffQuadraticDecay_of_solution hsolj hτj
    have hmaj := resolverGrad_majorant_summable_of_sourceDecay hdecay.C_nonneg hdecay.decay
    refine continuous_tsum (fun k => ?_) hmaj (fun k x => ?_)
    · exact continuous_const.mul (continuous_const.mul
        (Real.continuous_sin.comp (by fun_prop)))
    · rw [Real.norm_eq_abs, abs_mul]
      have hsin : |(-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * x))|
          ≤ (k : ℝ) * Real.pi := by
        rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ)),
          abs_of_nonneg Real.pi_pos.le]
        have h1 : |Real.sin ((k : ℝ) * Real.pi * x)| ≤ 1 := Real.abs_sin_le_one _
        nlinarith [mul_nonneg (Nat.cast_nonneg k) Real.pi_pos.le, abs_nonneg
          (Real.sin ((k : ℝ) * Real.pi * x)), h1]
      exact mul_le_mul_of_nonneg_left hsin (abs_nonneg _)
  have hc1 := hcontGrad hsol₁ hτ₁
  have hc2 := hcontGrad hsol₂ hτ₂
  have hintLHS : IntervalIntegrable
      (fun x => (resolverGradReal p (u₁ τ) x - resolverGradReal p (u₂ τ) x) ^ 2) volume 0 1 :=
    ((hc1.sub hc2).pow 2).intervalIntegrable _ _
  have hle_int : (∫ x in (0:ℝ)..1,
        (resolverGradReal p (u₁ τ) x - resolverGradReal p (u₂ τ) x) ^ 2) ≤ B := by
    have hBI : IntervalIntegrable (fun _ : ℝ => B) volume 0 1 :=
      (continuous_const).intervalIntegrable 0 1
    have hmono : (∫ x in (0:ℝ)..1,
        (resolverGradReal p (u₁ τ) x - resolverGradReal p (u₂ τ) x) ^ 2)
        ≤ ∫ _ in (0:ℝ)..1, B :=
      intervalIntegral.integral_mono_on (by norm_num) hintLHS hBI hpt
    have hconst : (∫ _x in (0:ℝ)..1, B ∂volume) = B := by
      rw [intervalIntegral.integral_const, sub_zero, one_smul]
    rwa [hconst] at hmono
  have hEnergy_le := sourceCoeff_diff_energy_le_integral hsol₁ hsol₂ hτ₁ hτ₂
  have hsrcint := source_integral_le_Eu_uniform_zeroM hsol₁ hsol₂ hMnn hγ_ge_one
    hmem₁ hmem₂ hτ₁ hτ₂
  set L : ℝ := p.γ * M ^ (p.γ - 1) with hLdef
  have hEu_nn : 0 ≤ intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ :=
    intervalDomainClassicalL2DifferenceEnergyU_nonneg u₁ u₂ τ
  refine hle_int.trans ?_
  have hstep1 : B ≤ Cg2 * (4 * ∫ x in (0:ℝ)..1,
      (p.ν * intervalDomainLift (u₁ τ) x ^ p.γ
        - p.ν * intervalDomainLift (u₂ τ) x ^ p.γ) ^ 2) := by
    rw [hB]; exact mul_le_mul_of_nonneg_left hEnergy_le hCg2_nn
  calc B ≤ Cg2 * (4 * ∫ x in (0:ℝ)..1,
        (p.ν * intervalDomainLift (u₁ τ) x ^ p.γ
          - p.ν * intervalDomainLift (u₂ τ) x ^ p.γ) ^ 2) := hstep1
    _ ≤ Cg2 * (4 * ((p.ν * L) ^ 2 *
          intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ)) := by
        apply mul_le_mul_of_nonneg_left _ hCg2_nn
        apply mul_le_mul_of_nonneg_left hsrcint (by norm_num)
    _ = (Cg2 * 4 * (p.ν * L) ^ 2) *
          intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ := by ring

/-! ## Explicit flux constant and per-time differential inequality (γ≥1 variant) -/

/-- Explicit τ-independent uniform static gradient-control constant `Cgrad_zeroM(M)`. -/
def CgradQuantZeroM (p : CM2Params) (M : ℝ) : ℝ :=
  (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2)) ^ 2 * 4 *
    (p.ν * (p.γ * M ^ (p.γ - 1))) ^ 2

/-- Explicit τ-independent uniform static value-control constant `Cval_zeroM(M)`. -/
def CvalQuantZeroM (p : CM2Params) (M : ℝ) : ℝ :=
  (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2)) ^ 2 * 4 *
    (p.ν * (p.γ * M ^ (p.γ - 1))) ^ 2

/-- Explicit τ-independent flux constant `Cflux_zeroM(M)`. -/
def CfluxQuantZeroM (p : CM2Params) (M : ℝ) : ℝ :=
  3 * ((FgQuant p M)^2 + M^2 * CgradQuantZeroM p M +
    (M * FgQuant p M * p.β)^2 * CvalQuantZeroM p M)

lemma CgradQuantZeroM_nonneg (p : CM2Params) (M : ℝ) : 0 ≤ CgradQuantZeroM p M := by
  rw [CgradQuantZeroM]; positivity

lemma CvalQuantZeroM_nonneg (p : CM2Params) (M : ℝ) : 0 ≤ CvalQuantZeroM p M := by
  rw [CvalQuantZeroM]; positivity

lemma CfluxQuantZeroM_nonneg (p : CM2Params) {M : ℝ} (hMnn : 0 ≤ M) :
    0 ≤ CfluxQuantZeroM p M := by
  rw [CfluxQuantZeroM]
  have h1 := FgQuant_nonneg p hMnn
  have h2 := CgradQuantZeroM_nonneg p M
  have h3 := CvalQuantZeroM_nonneg p M
  positivity

/-- **Uniform chemotaxis-flux `L²`-difference bound, γ≥1 zero-lower-bound variant.**
With `lift(uᵢ τ) ∈ [0,M]` on `[0,1]` and `γ ≥ 1`,

  `∫₀¹ (flux₁ − flux₂)² ≤ Cflux_zeroM(M) · E_u`.

Same proof as `flux_diff_L2_le_Eu_uniform` with `[0,M]` instead of `[δ,M]`. -/
theorem flux_diff_L2_le_Eu_uniform_zeroM
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {M τ : ℝ} (hMnn : 0 ≤ M) (hγ_ge_one : 1 ≤ p.γ)
    (hmem₁ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₁ τ) x ∈ Set.Icc (0:ℝ) M)
    (hmem₂ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₂ τ) x ∈ Set.Icc (0:ℝ) M)
    (hτ₁ : τ ∈ Set.Ioo (0 : ℝ) T₁) (hτ₂ : τ ∈ Set.Ioo (0 : ℝ) T₂) :
      (∫ y in (0:ℝ)..1,
        (intervalFlux p (u₁ τ) (v₁ τ) y - intervalFlux p (u₂ τ) (v₂ τ) y) ^ 2)
        ≤ CfluxQuantZeroM p M * intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ := by
  classical
  set Eu : ℝ := intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ with hEu
  have hEu_nn : 0 ≤ Eu := intervalDomainClassicalL2DifferenceEnergyU_nonneg u₁ u₂ τ
  have hv₁nn : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ intervalDomainLift (v₁ τ) x :=
    solution_lift_v_nonneg_Icc hsol₁ hτ₁
  have hv₂nn : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ intervalDomainLift (v₂ τ) x :=
    solution_lift_v_nonneg_Icc hsol₂ hτ₂
  have hub₁ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₁ τ) x ≤ M :=
    fun x hx => (hmem₁ x hx).2
  have hub₂ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₂ τ) x ≤ M :=
    fun x hx => (hmem₂ x hx).2
  set Fg : ℝ := Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
    (2 * (p.ν * M ^ p.γ)) with hFg
  have hMγnn : 0 ≤ M ^ p.γ := Real.rpow_nonneg hMnn p.γ
  have hFgnn : 0 ≤ Fg := by
    rw [hFg]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (by have := mul_nonneg p.hν.le hMγnn; linarith)
  have hβnn : 0 ≤ p.β := p.hβ
  have hU₁ : ∀ x ∈ Set.Icc (0:ℝ) 1, |intervalDomainLift (u₁ τ) x| ≤ M := by
    intro x hx
    have hpos : 0 < intervalDomainLift (u₁ τ) x := solution_lift_pos hsol₁ hτ₁ x hx
    rw [abs_of_pos hpos]; exact hub₁ x hx
  have hU₂ : ∀ x ∈ Set.Icc (0:ℝ) 1, |intervalDomainLift (u₂ τ) x| ≤ M := by
    intro x hx
    have hpos : 0 < intervalDomainLift (u₂ τ) x := solution_lift_pos hsol₂ hτ₂ x hx
    rw [abs_of_pos hpos]; exact hub₂ x hx
  have hG₁ : ∀ x ∈ Set.Icc (0:ℝ) 1, |resolverGradReal p (u₁ τ) x| ≤ Fg := by
    intro x hx; exact resolverGrad_sup_le_of_ub hsol₁ hτ₁ hub₁ hx
  have hG₂ : ∀ x ∈ Set.Icc (0:ℝ) 1, |resolverGradReal p (u₂ τ) x| ≤ Fg := by
    intro x hx; exact resolverGrad_sup_le_of_ub hsol₂ hτ₂ hub₂ hx
  have hpt : ∀ y ∈ Set.Ioo (0:ℝ) 1,
      |intervalFluxRepr p (u₁ τ) (v₁ τ) y - intervalFluxRepr p (u₂ τ) (v₂ τ) y|
        ≤ Fg * |intervalDomainLift (u₁ τ) y - intervalDomainLift (u₂ τ) y|
          + M * |resolverGradReal p (u₁ τ) y - resolverGradReal p (u₂ τ) y|
          + M * Fg * p.β
              * |intervalDomainLift (v₁ τ) y - intervalDomainLift (v₂ τ) y| := by
    intro y hy
    have hyIcc : y ∈ Set.Icc (0:ℝ) 1 := Set.Ioo_subset_Icc_self hy
    have ha₁ := hU₁ y hyIcc
    have ha₂ := hU₂ y hyIcc
    have hg₁ := hG₁ y hyIcc
    have hg₂ := hG₂ y hyIcc
    have hq₁ := chemQuotient_mem_Ioc hβnn (hv₁nn y hyIcc)
    have hq₂ := chemQuotient_mem_Ioc hβnn (hv₂nn y hyIcc)
    have hqLip := chemQuotient_lipschitz hβnn (hv₁nn y hyIcc) (hv₂nn y hyIcc)
    have := flux_diff_pointwise_bound
      (a₁ := intervalDomainLift (u₁ τ) y) (a₂ := intervalDomainLift (u₂ τ) y)
      (g₁ := resolverGradReal p (u₁ τ) y) (g₂ := resolverGradReal p (u₂ τ) y)
      (q₁ := (1 + intervalDomainLift (v₁ τ) y) ^ (-p.β))
      (q₂ := (1 + intervalDomainLift (v₂ τ) y) ^ (-p.β))
      (v₁ := intervalDomainLift (v₁ τ) y) (v₂ := intervalDomainLift (v₂ τ) y)
      (U := M) (G := Fg) (Lq := p.β)
      ha₁ ha₂ hg₁ hg₂ hq₁.1.le hq₁.2 hq₂.1.le hq₂.2 hMnn hFgnn hqLip
    simpa only [intervalFluxRepr] using this
  set a := fun y => (intervalDomainLift (u₁ τ) y - intervalDomainLift (u₂ τ) y) with ha
  set gg := fun y => (resolverGradReal p (u₁ τ) y - resolverGradReal p (u₂ τ) y) with hgg
  set vv := fun y => (intervalDomainLift (v₁ τ) y - intervalDomainLift (v₂ τ) y) with hvv
  have hsq : ∀ y ∈ Set.Ioo (0:ℝ) 1,
      (intervalFluxRepr p (u₁ τ) (v₁ τ) y - intervalFluxRepr p (u₂ τ) (v₂ τ) y) ^ 2
        ≤ 3 * (Fg^2 * (a y)^2 + M^2 * (gg y)^2 + (M*Fg*p.β)^2 * (vv y)^2) := by
    intro y hy
    have hb := hpt y hy
    set X := Fg * |a y| with hX
    set Y := M * |gg y| with hY
    set Z := M * Fg * p.β * |vv y| with hZ
    have hXnn : 0 ≤ X := by rw [hX]; positivity
    have hYnn : 0 ≤ Y := by rw [hY]; positivity
    have hZnn : 0 ≤ Z := by rw [hZ]; positivity
    have hb' : |intervalFluxRepr p (u₁ τ) (v₁ τ) y - intervalFluxRepr p (u₂ τ) (v₂ τ) y|
        ≤ X + Y + Z := hb
    have hsq0 : (intervalFluxRepr p (u₁ τ) (v₁ τ) y
          - intervalFluxRepr p (u₂ τ) (v₂ τ) y) ^ 2
        ≤ (X + Y + Z) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb' 2
    refine hsq0.trans ?_
    have hexp : (X + Y + Z) ^ 2 ≤ 3 * (X^2 + Y^2 + Z^2) := by
      nlinarith [sq_nonneg (X-Y), sq_nonneg (Y-Z), sq_nonneg (X-Z)]
    refine hexp.trans ?_
    have hXsq : X^2 = Fg^2 * (a y)^2 := by rw [hX]; rw [mul_pow, sq_abs]
    have hYsq : Y^2 = M^2 * (gg y)^2 := by rw [hY]; rw [mul_pow, sq_abs]
    have hZsq : Z^2 = (M*Fg*p.β)^2 * (vv y)^2 := by rw [hZ]; rw [mul_pow, sq_abs]
    rw [hXsq, hYsq, hZsq]
  have hflux_eq : (∫ y in (0:ℝ)..1,
        (intervalFlux p (u₁ τ) (v₁ τ) y - intervalFlux p (u₂ τ) (v₂ τ) y) ^ 2)
      = ∫ y in (0:ℝ)..1,
        (intervalFluxRepr p (u₁ τ) (v₁ τ) y - intervalFluxRepr p (u₂ τ) (v₂ τ) y) ^ 2 := by
    refine intervalIntegral.integral_congr_ae ?_
    have hnull : volume ({(1:ℝ)} : Set ℝ) = 0 := Real.volume_singleton
    refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
    intro y hy
    simp only [Set.mem_setOf_eq] at hy
    push_neg at hy
    obtain ⟨hyIoc0, hne⟩ := hy
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hyIoc0
    simp only [Set.mem_singleton_iff]
    by_contra hy1
    have hyIoo : y ∈ Set.Ioo (0:ℝ) 1 := ⟨hyIoc0.1, lt_of_le_of_ne hyIoc0.2 hy1⟩
    exact hne (by rw [intervalFlux_eq_repr_interior hsol₁ hτ₁ hv₁nn hyIoo,
      intervalFlux_eq_repr_interior hsol₂ hτ₂ hv₂nn hyIoo])
  have hcontR : ContinuousOn
      (fun y => (intervalFluxRepr p (u₁ τ) (v₁ τ) y
        - intervalFluxRepr p (u₂ τ) (v₂ τ) y) ^ 2) (Set.uIcc (0:ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact (((intervalFluxRepr_continuousOn hsol₁ hτ₁ hv₁nn).sub
      (intervalFluxRepr_continuousOn hsol₂ hτ₂ hv₂nn)).pow 2)
  have hintR : IntervalIntegrable
      (fun y => (intervalFluxRepr p (u₁ τ) (v₁ τ) y
        - intervalFluxRepr p (u₂ τ) (v₂ τ) y) ^ 2) volume 0 1 :=
    hcontR.intervalIntegrable
  have hCg := static_v_grad_L2_le_Eu_uniform_zeroM hsol₁ hsol₂ hMnn hγ_ge_one
    hmem₁ hmem₂ hτ₁ hτ₂
  have hCv := static_v_value_L2_le_Eu_uniform_zeroM hsol₁ hsol₂ hMnn hγ_ge_one
    hmem₁ hmem₂ hτ₁ hτ₂
  set Cg : ℝ := (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2)) ^ 2 * 4 *
    (p.ν * (p.γ * M ^ (p.γ - 1))) ^ 2 with hCgdef
  set Cv : ℝ := (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2)) ^ 2 * 4 *
    (p.ν * (p.γ * M ^ (p.γ - 1))) ^ 2 with hCvdef
  have hCgnn : 0 ≤ Cg := by rw [hCgdef]; positivity
  have hCvnn : 0 ≤ Cv := by rw [hCvdef]; positivity
  have hcont_u₁ : ContinuousOn (intervalDomainLift (u₁ τ)) (Set.Icc (0:ℝ) 1) :=
    ((hsol₁.regularity.2.2.2.2.2.2.1 τ hτ₁).1.1).continuousOn
  have hcont_u₂ : ContinuousOn (intervalDomainLift (u₂ τ)) (Set.Icc (0:ℝ) 1) :=
    ((hsol₂.regularity.2.2.2.2.2.2.1 τ hτ₂).1.1).continuousOn
  have hcont_v₁ : ContinuousOn (intervalDomainLift (v₁ τ)) (Set.Icc (0:ℝ) 1) :=
    ((hsol₁.regularity.2.2.2.2.2.2.1 τ hτ₁).2.1).continuousOn
  have hcont_v₂ : ContinuousOn (intervalDomainLift (v₂ τ)) (Set.Icc (0:ℝ) 1) :=
    ((hsol₂.regularity.2.2.2.2.2.2.1 τ hτ₂).2.1).continuousOn
  have hcg₁ := resolverGradReal_continuous hsol₁ hτ₁
  have hcg₂ := resolverGradReal_continuous hsol₂ hτ₂
  have hint_a : IntervalIntegrable (fun y => (a y)^2) volume 0 1 := by
    rw [ha]
    have : ContinuousOn (fun y => (intervalDomainLift (u₁ τ) y
        - intervalDomainLift (u₂ τ) y)^2) (Set.uIcc (0:ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact (hcont_u₁.sub hcont_u₂).pow 2
    exact this.intervalIntegrable
  have hint_g : IntervalIntegrable (fun y => (gg y)^2) volume 0 1 := by
    rw [hgg]; exact (((hcg₁.sub hcg₂).pow 2)).intervalIntegrable _ _
  have hint_v : IntervalIntegrable (fun y => (vv y)^2) volume 0 1 := by
    rw [hvv]
    have : ContinuousOn (fun y => (intervalDomainLift (v₁ τ) y
        - intervalDomainLift (v₂ τ) y)^2) (Set.uIcc (0:ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact (hcont_v₁.sub hcont_v₂).pow 2
    exact this.intervalIntegrable
  set RHSfun := fun y => 3 * (Fg^2 * (a y)^2 + M^2 * (gg y)^2 + (M*Fg*p.β)^2 * (vv y)^2)
    with hRHSfun
  have hint_RHS : IntervalIntegrable RHSfun volume 0 1 := by
    rw [hRHSfun]
    exact (((hint_a.const_mul (Fg^2)).add (hint_g.const_mul (M^2))).add
      (hint_v.const_mul ((M*Fg*p.β)^2))).const_mul 3
  have hmono : (∫ y in (0:ℝ)..1,
        (intervalFluxRepr p (u₁ τ) (v₁ τ) y
          - intervalFluxRepr p (u₂ τ) (v₂ τ) y) ^ 2)
      ≤ ∫ y in (0:ℝ)..1, RHSfun y := by
    have hae : (fun y => (intervalFluxRepr p (u₁ τ) (v₁ τ) y
          - intervalFluxRepr p (u₂ τ) (v₂ τ) y) ^ 2)
        ≤ᵐ[volume.restrict (Set.Icc (0:ℝ) 1)] RHSfun := by
      have hmeas : MeasurableSet (Set.Icc (0:ℝ) 1) := measurableSet_Icc
      refine (ae_restrict_iff' (μ := volume) hmeas).2 ?_
      have hnull : volume (insert (0:ℝ) ({(1:ℝ)} : Set ℝ)) = 0 :=
        Set.Finite.measure_zero
          ((Set.finite_singleton (1:ℝ)).insert (0:ℝ)) volume
      refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
      intro y hy
      simp only [Set.mem_setOf_eq] at hy
      push_neg at hy
      obtain ⟨hyIcc, hne⟩ := hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      by_contra hcon
      push_neg at hcon
      obtain ⟨hy0, hy1⟩ := hcon
      exact absurd (hsq y ⟨lt_of_le_of_ne hyIcc.1 (Ne.symm hy0),
        lt_of_le_of_ne hyIcc.2 hy1⟩) (not_le.mpr hne)
    exact intervalIntegral.integral_mono_ae_restrict (by norm_num) hintR hint_RHS hae
  have hCflux_eq : CfluxQuantZeroM p M = 3 * (Fg^2 + M^2 * Cg + (M*Fg*p.β)^2 * Cv) := by
    rw [CfluxQuantZeroM, hFg, hCgdef, hCvdef, FgQuant, CgradQuantZeroM, CvalQuantZeroM]
  rw [hCflux_eq, hflux_eq]
  refine hmono.trans ?_
  have hRHSint : (∫ y in (0:ℝ)..1, RHSfun y)
      = 3 * (Fg^2 * (∫ y in (0:ℝ)..1, (a y)^2)
        + M^2 * (∫ y in (0:ℝ)..1, (gg y)^2)
        + (M*Fg*p.β)^2 * (∫ y in (0:ℝ)..1, (vv y)^2)) := by
    rw [hRHSfun]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_add
        ((hint_a.const_mul (Fg^2)).add (hint_g.const_mul (M^2))) (hint_v.const_mul _),
      intervalIntegral.integral_add (hint_a.const_mul (Fg^2)) (hint_g.const_mul (M^2)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [hRHSint]
  have hIa : (∫ y in (0:ℝ)..1, (a y)^2) = Eu := by
    rw [ha, hEu]; exact lift_u_diff_sq_integral_eq_Eu u₁ u₂ τ
  have hIg : (∫ y in (0:ℝ)..1, (gg y)^2) ≤ Cg * Eu := by rw [hgg, hEu, hCgdef]; exact hCg
  have hIv : (∫ y in (0:ℝ)..1, (vv y)^2) ≤ Cv * Eu := by rw [hvv, hEu, hCvdef]; exact hCv
  rw [hIa]
  have hMFβsq_nn : 0 ≤ (M*Fg*p.β)^2 := sq_nonneg _
  have hM2nn : 0 ≤ M^2 := sq_nonneg _
  calc 3 * (Fg^2 * Eu + M^2 * (∫ y in (0:ℝ)..1, (gg y)^2)
        + (M*Fg*p.β)^2 * (∫ y in (0:ℝ)..1, (vv y)^2))
      ≤ 3 * (Fg^2 * Eu + M^2 * (Cg * Eu) + (M*Fg*p.β)^2 * (Cv * Eu)) := by
        have h1 : M^2 * (∫ y in (0:ℝ)..1, (gg y)^2) ≤ M^2 * (Cg * Eu) :=
          mul_le_mul_of_nonneg_left hIg hM2nn
        have h2 : (M*Fg*p.β)^2 * (∫ y in (0:ℝ)..1, (vv y)^2)
            ≤ (M*Fg*p.β)^2 * (Cv * Eu) :=
          mul_le_mul_of_nonneg_left hIv hMFβsq_nn
        nlinarith [h1, h2]
    _ = 3 * (Fg^2 + M^2 * Cg + (M*Fg*p.β)^2 * Cv) * Eu := by ring

/-- **Uniform per-time energy differential inequality, γ≥1 zero-lower-bound variant.**
With `lift(uᵢ τ) ∈ [0,M]` on `[0,1]` and `γ ≥ 1`,

  `∫₀¹ Eprime(τ) ≤ K · E_u(τ)`

with `K = χ₀²·Cflux_zeroM(M) + 2·L`, the τ-independent constant
(the flux part from `flux_diff_L2_le_Eu_uniform_zeroM`, the reaction part from
`intervalLogisticSource_lipschitz p (M+1)`). -/
theorem intervalDomainL2U_energy_diffIneq_bound_uniform_explicit_zeroM
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {M τ L : ℝ} (hMnn : 0 ≤ M) (hγ_ge_one : 1 ≤ p.γ)
    (hmem₁ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₁ τ) x ∈ Set.Icc (0:ℝ) M)
    (hmem₂ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₂ τ) x ∈ Set.Icc (0:ℝ) M)
    (hLip : ∀ a b : ℝ, |a| ≤ M + 1 → |b| ≤ M + 1 →
      |a * (p.a - p.b * a ^ p.α) - b * (p.a - p.b * b ^ p.α)| ≤ L * |a - b|)
    (hτ : τ ∈ Set.Ioo (0 : ℝ) (min T₁ T₂)) :
      (∫ y in (0:ℝ)..1, intervalDomainUEnergyIntegrandDeriv u₁ u₂ τ y)
        ≤ (p.χ₀ ^ 2 * CfluxQuantZeroM p M + 2 * L) *
          intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ := by
  classical
  have hτ₁ : τ ∈ Set.Ioo (0:ℝ) T₁ := ⟨hτ.1, lt_of_lt_of_le hτ.2 (min_le_left _ _)⟩
  have hτ₂ : τ ∈ Set.Ioo (0:ℝ) T₂ := ⟨hτ.1, lt_of_lt_of_le hτ.2 (min_le_right _ _)⟩
  set Eu : ℝ := intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ with hEu
  have hEu_nn : 0 ≤ Eu := intervalDomainClassicalL2DifferenceEnergyU_nonneg u₁ u₂ τ
  set wL : ℝ → ℝ := fun y => intervalDomainLift (u₁ τ) y - intervalDomainLift (u₂ τ) y with hwL
  set dwL : ℝ → ℝ := fun y => deriv (intervalDomainLift (u₁ τ)) y
      - deriv (intervalDomainLift (u₂ τ)) y with hdwL
  set Lap : ℝ → ℝ := fun y => deriv (fun z => deriv (intervalDomainLift (u₁ τ)) z) y
      - deriv (fun z => deriv (intervalDomainLift (u₂ τ)) z) y with hLap
  set Fd : ℝ → ℝ := fun y => deriv (intervalFlux p (u₁ τ) (v₁ τ)) y
      - deriv (intervalFlux p (u₂ τ) (v₂ τ)) y with hFd
  set Flx : ℝ → ℝ := fun y => intervalFlux p (u₁ τ) (v₁ τ) y - intervalFlux p (u₂ τ) (v₂ τ) y
    with hFlx
  set Rx : ℝ → ℝ := fun y => intervalDomainLift (u₁ τ) y
        * (p.a - p.b * intervalDomainLift (u₁ τ) y ^ p.α)
      - intervalDomainLift (u₂ τ) y * (p.a - p.b * intervalDomainLift (u₂ τ) y ^ p.α) with hRx
  have hintegrand : Set.EqOn (intervalDomainUEnergyIntegrandDeriv u₁ u₂ τ)
      (fun y => 2 * wL y * (Lap y - p.χ₀ * Fd y + Rx y)) (Set.Ioo (0:ℝ) 1) := by
    intro y hy
    unfold intervalDomainUEnergyIntegrandDeriv
    rw [intervalDomainLift_uDiff_eq u₁ u₂ τ y,
      intervalDomainUEnergy_timeDeriv_pde hsol₁ hsol₂ hτ hy]
  have hwLcont : ContinuousOn wL (Set.uIcc (0:ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact (((hsol₁.regularity.2.2.2.2.2.2.1 τ hτ₁).1.1).continuousOn).sub
      (((hsol₂.regularity.2.2.2.2.2.2.1 τ hτ₂).1.1).continuousOn)
  have hwLcontI : ContinuousOn wL (Set.Icc (0:ℝ) 1) := by
    rw [← Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hwLcont
  have hdwLint : IntervalIntegrable dwL volume 0 1 := by
    have : ContinuousOn dwL (Set.uIcc (0:ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact (solution_deriv_lift_continuousOn_Icc hsol₁ hτ₁).sub
        (solution_deriv_lift_continuousOn_Icc hsol₂ hτ₂)
    exact this.intervalIntegrable
  have hLapint : IntervalIntegrable Lap volume 0 1 :=
    (solution_lap_lift_intervalIntegrable hsol₁ hτ₁).sub
      (solution_lap_lift_intervalIntegrable hsol₂ hτ₂)
  have hFdint : IntervalIntegrable Fd volume 0 1 :=
    (solution_deriv_flux_intervalIntegrable hsol₁ hτ₁).sub
      (solution_deriv_flux_intervalIntegrable hsol₂ hτ₂)
  have hRxcont : ContinuousOn Rx (Set.uIcc (0:ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    have hcu : ∀ (u : ℝ → intervalDomainPoint → ℝ) {Tj : ℝ}
        {vj : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p Tj u vj → τ ∈ Set.Ioo (0:ℝ) Tj →
        ContinuousOn (fun y => intervalDomainLift (u τ) y
          * (p.a - p.b * intervalDomainLift (u τ) y ^ p.α)) (Set.Icc (0:ℝ) 1) := by
      intro u Tj vj hsolj htj
      have hc : ContinuousOn (intervalDomainLift (u τ)) (Set.Icc (0:ℝ) 1) :=
        ((hsolj.regularity.2.2.2.2.2.2.1 τ htj).1.1).continuousOn
      have hpow : ContinuousOn (fun y => intervalDomainLift (u τ) y ^ p.α) (Set.Icc (0:ℝ) 1) :=
        hc.rpow_const (fun y hy => Or.inl (ne_of_gt (solution_lift_pos hsolj htj y hy)))
      exact hc.mul (continuousOn_const.sub (continuousOn_const.mul hpow))
    exact (hcu u₁ hsol₁ hτ₁).sub (hcu u₂ hsol₂ hτ₂)
  have hwLLap : IntervalIntegrable (fun y => wL y * Lap y) volume 0 1 :=
    hLapint.continuousOn_mul hwLcont
  have hwLFd : IntervalIntegrable (fun y => wL y * Fd y) volume 0 1 :=
    hFdint.continuousOn_mul hwLcont
  have hwLRx : IntervalIntegrable (fun y => wL y * Rx y) volume 0 1 := by
    have hRxint : IntervalIntegrable Rx volume 0 1 := hRxcont.intervalIntegrable
    exact hRxint.continuousOn_mul hwLcont
  have hIeq : (∫ y in (0:ℝ)..1, intervalDomainUEnergyIntegrandDeriv u₁ u₂ τ y)
      = ∫ y in (0:ℝ)..1, 2 * wL y * (Lap y - p.χ₀ * Fd y + Rx y) := by
    refine intervalIntegral.integral_congr_ae ?_
    have hnull : volume ({(1:ℝ)} : Set ℝ) = 0 := Real.volume_singleton
    refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
    intro y hy
    simp only [Set.mem_setOf_eq] at hy
    push_neg at hy
    obtain ⟨hyIoc0, hne⟩ := hy
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hyIoc0
    simp only [Set.mem_singleton_iff]
    by_contra hy1
    exact hne (hintegrand ⟨hyIoc0.1, lt_of_le_of_ne hyIoc0.2 hy1⟩)
  have hsplit : (∫ y in (0:ℝ)..1, 2 * wL y * (Lap y - p.χ₀ * Fd y + Rx y))
      = 2 * (∫ y in (0:ℝ)..1, wL y * Lap y)
        - 2 * p.χ₀ * (∫ y in (0:ℝ)..1, wL y * Fd y)
        + 2 * (∫ y in (0:ℝ)..1, wL y * Rx y) := by
    have hcongr : (fun y => 2 * wL y * (Lap y - p.χ₀ * Fd y + Rx y))
        = fun y => 2 * (wL y * Lap y) + (- (2 * p.χ₀)) * (wL y * Fd y)
            + 2 * (wL y * Rx y) := by
      funext y; ring
    rw [hcongr]
    rw [intervalIntegral.integral_add
        ((hwLLap.const_mul 2).add (hwLFd.const_mul (-(2*p.χ₀)))) (hwLRx.const_mul 2),
      intervalIntegral.integral_add (hwLLap.const_mul 2) (hwLFd.const_mul (-(2*p.χ₀))),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    ring
  have hdiss := uDiff_dissipation hsol₁ hsol₂ hτ₁ hτ₂
  have hchem := uDiff_chemotaxis_ibp hsol₁ hsol₂ hτ₁ hτ₂
  set D : ℝ := ∫ y in (0:ℝ)..1, (dwL y) ^ 2 with hD
  have hD_nn : 0 ≤ D := by
    rw [hD]; refine intervalIntegral.integral_nonneg (by norm_num) (fun y _ => by positivity)
  have hwLLap_eq : (∫ y in (0:ℝ)..1, wL y * Lap y) = - D := by
    rw [hD]; exact hdiss
  have hwLFd_eq : (∫ y in (0:ℝ)..1, wL y * Fd y)
      = - ∫ y in (0:ℝ)..1, dwL y * Flx y := hchem
  set Cflux : ℝ := CfluxQuantZeroM p M with hCfluxdef
  have hCflux_nn : 0 ≤ Cflux := by rw [hCfluxdef]; exact CfluxQuantZeroM_nonneg p hMnn
  have hCflux := flux_diff_L2_le_Eu_uniform_zeroM hsol₁ hsol₂ hMnn hγ_ge_one
    hmem₁ hmem₂ hτ₁ hτ₂
  set Sflx : ℝ := ∫ y in (0:ℝ)..1, (Flx y) ^ 2 with hSflx
  have hSflx_eq : Sflx ≤ Cflux * Eu := by rw [hSflx, hEu, hFlx, hCfluxdef]; exact hCflux
  have hSflx_nn : 0 ≤ Sflx := by
    rw [hSflx]; refine intervalIntegral.integral_nonneg (by norm_num) (fun y _ => by positivity)
  have hFlxcont : ContinuousOn Flx (Set.uIcc (0:ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact ((flux_contDiffOn_Icc hsol₁ hτ₁).continuousOn).sub
      ((flux_contDiffOn_Icc hsol₂ hτ₂).continuousOn)
  have hdwLcont : ContinuousOn dwL (Set.uIcc (0:ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact (solution_deriv_lift_continuousOn_Icc hsol₁ hτ₁).sub
      (solution_deriv_lift_continuousOn_Icc hsol₂ hτ₂)
  have hdwLFxint : IntervalIntegrable (fun y => dwL y * Flx y) volume 0 1 :=
    (hdwLint.mul_continuousOn hFlxcont)
  have hdwLsqint : IntervalIntegrable (fun y => (dwL y) ^ 2) volume 0 1 := by
    have : ContinuousOn (fun y => (dwL y) ^ 2) (Set.uIcc (0:ℝ) 1) := hdwLcont.pow 2
    exact this.intervalIntegrable
  have hFlxsqint : IntervalIntegrable (fun y => (Flx y) ^ 2) volume 0 1 := by
    have : ContinuousOn (fun y => (Flx y) ^ 2) (Set.uIcc (0:ℝ) 1) := hFlxcont.pow 2
    exact this.intervalIntegrable
  have hYoung : 2 * p.χ₀ * (∫ y in (0:ℝ)..1, dwL y * Flx y) ≤ D + p.χ₀ ^ 2 * Sflx := by
    have hptw : ∀ y, 2 * p.χ₀ * (dwL y * Flx y) ≤ (dwL y) ^ 2 + p.χ₀ ^ 2 * (Flx y) ^ 2 := by
      intro y; nlinarith [sq_nonneg (dwL y - p.χ₀ * Flx y)]
    have hmono : (∫ y in (0:ℝ)..1, 2 * p.χ₀ * (dwL y * Flx y))
        ≤ ∫ y in (0:ℝ)..1, ((dwL y) ^ 2 + p.χ₀ ^ 2 * (Flx y) ^ 2) := by
      refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ (fun y _ => hptw y)
      · exact hdwLFxint.const_mul _
      · exact hdwLsqint.add (hFlxsqint.const_mul _)
    rw [intervalIntegral.integral_const_mul] at hmono
    rw [intervalIntegral.integral_add hdwLsqint (hFlxsqint.const_mul _),
      intervalIntegral.integral_const_mul] at hmono
    rw [hD, hSflx]; linarith
  have hwL2int : IntervalIntegrable (fun y => wL y ^ 2) volume 0 1 := by
    have : ContinuousOn (fun y => wL y ^ 2) (Set.uIcc (0:ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hwLcontI.pow 2
    exact this.intervalIntegrable
  have hwL2_eq_Eu : (∫ y in (0:ℝ)..1, wL y ^ 2) = Eu := by
    rw [hEu, ← lift_u_diff_sq_integral_eq_Eu u₁ u₂ τ]
  have hRxbound : ∀ y ∈ Set.Icc (0:ℝ) 1, |Rx y| ≤ L * |wL y| := by
    intro y hy
    have ha₁ : |intervalDomainLift (u₁ τ) y| ≤ M + 1 := by
      have hpos : 0 < intervalDomainLift (u₁ τ) y := solution_lift_pos hsol₁ hτ₁ y hy
      rw [abs_of_pos hpos]; have := (hmem₁ y hy).2; linarith
    have ha₂ : |intervalDomainLift (u₂ τ) y| ≤ M + 1 := by
      have hpos : 0 < intervalDomainLift (u₂ τ) y := solution_lift_pos hsol₂ hτ₂ y hy
      rw [abs_of_pos hpos]; have := (hmem₂ y hy).2; linarith
    have := hLip (intervalDomainLift (u₁ τ) y) (intervalDomainLift (u₂ τ) y) ha₁ ha₂
    rw [hRx, hwL]; exact this
  have hptwRx : ∀ y ∈ Set.Icc (0:ℝ) 1, wL y * Rx y ≤ L * wL y ^ 2 := by
    intro y hy
    have h1 : wL y * Rx y ≤ |wL y * Rx y| := le_abs_self _
    have h2 : |wL y * Rx y| ≤ L * wL y ^ 2 := by
      rw [abs_mul]
      calc |wL y| * |Rx y| ≤ |wL y| * (L * |wL y|) :=
            mul_le_mul_of_nonneg_left (hRxbound y hy) (abs_nonneg _)
        _ = L * (|wL y| * |wL y|) := by ring
        _ = L * wL y ^ 2 := by rw [abs_mul_abs_self]; ring
    exact le_trans h1 h2
  have hLwL2int : IntervalIntegrable (fun y => L * wL y ^ 2) volume 0 1 := hwL2int.const_mul L
  have hwLRx_le : (∫ y in (0:ℝ)..1, wL y * Rx y) ≤ L * Eu := by
    have hmono := intervalIntegral.integral_mono_on (by norm_num) hwLRx hLwL2int hptwRx
    rw [intervalIntegral.integral_const_mul, hwL2_eq_Eu] at hmono
    exact hmono
  rw [show p.χ₀ ^ 2 * CfluxQuantZeroM p M + 2 * L = p.χ₀ ^ 2 * Cflux + 2 * L from by rw [hCfluxdef]]
  rw [hIeq, hsplit, hwLLap_eq, hwLFd_eq]
  have hkey : 2 * (-D) - 2 * p.χ₀ * (- ∫ y in (0:ℝ)..1, dwL y * Flx y)
      + 2 * (∫ y in (0:ℝ)..1, wL y * Rx y)
      ≤ (p.χ₀ ^ 2 * Cflux + 2 * L) * Eu := by
    have h1 : 2 * p.χ₀ * (∫ y in (0:ℝ)..1, dwL y * Flx y) ≤ D + p.χ₀ ^ 2 * Sflx := hYoung
    have h2 : (∫ y in (0:ℝ)..1, wL y * Rx y) ≤ L * Eu := hwLRx_le
    have h3 : p.χ₀ ^ 2 * Sflx ≤ p.χ₀ ^ 2 * (Cflux * Eu) :=
      mul_le_mul_of_nonneg_left hSflx_eq (by positivity)
    nlinarith [hD_nn, h1, h2, h3]
  exact hkey

/-! ## The γ≥1 uniform lift-bound datum and the final gluing theorem -/

/-- **The γ≥1 uniform UPPER-only lift-bound datum.**  For every solution pair sharing an
initial trace, the lifts stay in a fixed `[0,M]` on `[0,1]` over the whole overlap
interior.  NO positive lower bound required.  This is the genuinely-weaker hypothesis
made possible by `γ ≥ 1` (the source `x↦x^γ` Lipschitz constant `γ·M^{γ-1}` does not
require δ>0). -/
structure IntervalDomainUniformLiftBoundZeroM (p : CM2Params) : Prop where
  bound :
    ∀ {u₀ : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
      ∀ {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
      IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
      InitialTrace intervalDomain u₀ u₁ →
      InitialTrace intervalDomain u₀ u₂ →
        ∃ M : ℝ, 0 ≤ M ∧ ∀ τ, 0 < τ → τ < min T₁ T₂ →
          (∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₁ τ) x ∈ Set.Icc (0:ℝ) M) ∧
          (∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₂ τ) x ∈ Set.Icc (0:ℝ) M)

/-- **The uniform Grönwall constant, γ≥1, from the upper-only lift bound.**
With `γ ≥ 1` and a uniform `[0,M]` bound on the overlap interior, there is a SINGLE
τ-independent `K ≥ 0` with `∫ Eprime(τ) ≤ K·E_u(τ)` for every interior `τ`.
`K = χ₀²·Cflux_zeroM(M) + 2·L_react(M+1)`. -/
theorem gronwall_const_of_uniformLiftBoundZeroM
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    (hγ_ge_one : 1 ≤ p.γ)
    {M : ℝ} (hMnn : 0 ≤ M)
    (hbnd : ∀ τ, 0 < τ → τ < min T₁ T₂ →
      (∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₁ τ) x ∈ Set.Icc (0:ℝ) M) ∧
      (∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₂ τ) x ∈ Set.Icc (0:ℝ) M)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ τ, 0 < τ → τ < min T₁ T₂ →
      (∫ y in (0:ℝ)..1, intervalDomainUEnergyIntegrandDeriv u₁ u₂ τ y)
        ≤ K * intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ := by
  classical
  by_cases hne : ∃ τ : ℝ, 0 < τ ∧ τ < min T₁ T₂
  · obtain ⟨τ₀, hτ₀0, hτ₀1⟩ := hne
    have hMm_pos : 0 < M + 1 := by linarith
    obtain ⟨L, hLpos, hLip⟩ :=
      ShenWork.IntervalDomainExistence.intervalLogisticSource_lipschitz p hMm_pos
    refine ⟨p.χ₀ ^ 2 * CfluxQuantZeroM p M + 2 * L, by
      have := CfluxQuantZeroM_nonneg (p := p) hMnn; positivity, ?_⟩
    intro τ hτ0 hτ1
    have hτmem : τ ∈ Set.Ioo (0:ℝ) (min T₁ T₂) := ⟨hτ0, hτ1⟩
    obtain ⟨hb1, hb2⟩ := hbnd τ hτ0 hτ1
    exact intervalDomainL2U_energy_diffIneq_bound_uniform_explicit_zeroM
      hsol₁ hsol₂ hMnn hγ_ge_one hb1 hb2 hLip hτmem
  · refine ⟨0, le_refl _, ?_⟩
    intro τ hτ0 hτ1
    exact absurd ⟨τ, hτ0, hτ1⟩ hne

/-- **Boundedness hypothesis from the γ≥1 upper-only uniform lift bound.**
The full `IntervalDomainL2UBoundednessHypothesis` is constructed from the
`γ≥1` upper-only bound `IntervalDomainUniformLiftBoundZeroM` plus the
genuinely-independent bounded shared initial datum `hdatum`. -/
def boundednessHypothesis_of_uniformSupBoundZeroM
    {p : CM2Params}
    (hγ_ge_one : 1 ≤ p.γ)
    (hbnd : IntervalDomainUniformLiftBoundZeroM p) :
    IntervalDomainL2UBoundednessHypothesis p where
  datumBdd := fun {_u₀} hu₀ {_T₁} {_T₂} {_u₁} {_v₁} {_u₂} {_v₂}
      _hsol₁ _hsol₂ _htr₁ _htr₂ =>
    hu₀.admissible.1
  gronwall := by
    intro u₀ hu₀ T₁ T₂ u₁ v₁ u₂ v₂ hsol₁ hsol₂ htr₁ htr₂
    obtain ⟨M, hMnn, hb⟩ := hbnd.bound hu₀ hsol₁ hsol₂ htr₁ htr₂
    exact gronwall_const_of_uniformLiftBoundZeroM hsol₁ hsol₂ hγ_ge_one hMnn hb

/-- Instance-facing γ≥1 upper-only lift-bound to boundedness-hypothesis bridge. -/
def boundednessHypothesis_of_uniformSupBoundZeroMFact
    {p : CM2Params}
    [hγ_ge_one : Fact (1 ≤ p.γ)]
    [hbnd : Fact (IntervalDomainUniformLiftBoundZeroM p)] :
    IntervalDomainL2UBoundednessHypothesis p :=
  boundednessHypothesis_of_uniformSupBoundZeroM hγ_ge_one.out hbnd.out

/-- **The γ≥1 upper-only lift bound from the Theorem-1.1 regime + bounded datum.**
Under the negative-sensitivity regime (`χ₀ ≤ 0`, `0 < a`, `0 < b`), with a positive
bounded shared initial datum (supplied by `hpos`, `hdatum`), the upper-only datum
`IntervalDomainUniformLiftBoundZeroM p` holds: the common upper bound is
`M = max (supNorm u₀, (a/b)^{1/α})`, derived from the proven sup-norm bound.  The lower
bound is just `0` (strict positivity is only used for the membership, not for the
constant `L_γ`). -/
theorem uniformLiftBoundZeroM_of_regime
    (p : CM2Params)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b) :
    IntervalDomainUniformLiftBoundZeroM p where
  bound := by
    intro u₀ hu₀ T₁ T₂ u₁ v₁ u₂ v₂ hsol₁ hsol₂ htr₁ htr₂
    have hbddu₀ : BddAbove (Set.range (fun x : intervalDomainPoint => |u₀ x|)) :=
      hu₀.admissible.1
    set M : ℝ := max (intervalDomainSupNorm u₀) ((p.a / p.b) ^ (1 / p.α)) with hMdef
    have hub₁ := uniform_lift_upper_bound_of_regime p hχ ha hb hu₀ hbddu₀
      hsol₁.T_pos hsol₁ htr₁
    have hub₂ := uniform_lift_upper_bound_of_regime p hχ ha hb hu₀ hbddu₀
      hsol₂.T_pos hsol₂ htr₂
    -- `M ≥ 0` directly from its definition: `(a/b)^{1/α} ≥ 0` by `Real.rpow_nonneg`,
    -- so the `max` is `≥ 0`.
    have hMnn : 0 ≤ M := by
      have hab_nn : 0 ≤ p.a / p.b := div_nonneg ha.le hb.le
      have hrpow_nn : 0 ≤ (p.a / p.b) ^ (1 / p.α) := Real.rpow_nonneg hab_nn _
      exact le_max_of_le_right hrpow_nn
    refine ⟨M, hMnn, ?_⟩
    intro τ hτ0 hτmin
    have hτ1 : τ < T₁ := lt_of_lt_of_le hτmin (min_le_left _ _)
    have hτ2 : τ < T₂ := lt_of_lt_of_le hτmin (min_le_right _ _)
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · exact ⟨(solution_lift_pos hsol₁ ⟨hτ0, hτ1⟩ x hx).le, (hub₁ τ hτ0 hτ1 x hx).2⟩
    · exact ⟨(solution_lift_pos hsol₂ ⟨hτ0, hτ2⟩ x hx).le, (hub₂ τ hτ0 hτ2 x hx).2⟩

/-- Instance-facing regime-to-γ≥1-upper-only-lift-bound bridge. -/
theorem uniformLiftBoundZeroM_of_regimeFact
    (p : CM2Params)
    [hχ : Fact (p.χ₀ ≤ 0)] [ha : Fact (0 < p.a)] [hb : Fact (0 < p.b)] :
    IntervalDomainUniformLiftBoundZeroM p :=
  uniformLiftBoundZeroM_of_regime p hχ.out ha.out hb.out

/-- **Global-solution gluing from reachability, fully unconditional for `γ ≥ 1` modulo
the parameter regime + positive initial datum.**

Under the Theorem-1.1 negative-sensitivity regime (`χ₀ ≤ 0`, `0 < a`, `0 < b`) and the
`γ ≥ 1` regime (`1 ≤ p.γ`), given for each solution pair sharing an initial trace:

* `hpos` — the shared datum is a positive initial datum.

Datum-boundedness is now FOLDED IN: with the strengthened `intervalDomain.initialAdmissible`
(`fun u₀ => BddAbove (range |u₀|)`), `hpos.admissible` directly supplies the bounded-datum
hypothesis (no separate `hdatum` argument).

NO `δ>0` lower bound is required: the source `x↦x^γ` Lipschitz constant on `[0,M]` is
`L_γ = γ·M^{γ-1}` (well-defined since `γ-1 ≥ 0`), τ-independent.  The upper bound
`M = max (supNorm u₀, (a/b)^{1/α})` is DERIVED from the proven sup-norm bound. -/
theorem GlobalSolutionGluingFromReachability_of_regime_gammaGeOne
    (p : CM2Params)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b) (hγ_ge_one : 1 ≤ p.γ) :
    ShenWork.IntervalDomainExistence.GlobalSolutionGluingFromReachability p :=
  GlobalSolutionGluingFromReachability_of_bounded p
    (boundednessHypothesis_of_uniformSupBoundZeroM hγ_ge_one
      (uniformLiftBoundZeroM_of_regime p hχ ha hb))

/-- Instance-facing γ≥1 regime gluing theorem. -/
theorem GlobalSolutionGluingFromReachability_of_regime_gammaGeOneFact
    (p : CM2Params)
    [hχ : Fact (p.χ₀ ≤ 0)] [ha : Fact (0 < p.a)] [hb : Fact (0 < p.b)]
    [hγ_ge_one : Fact (1 ≤ p.γ)] :
    ShenWork.IntervalDomainExistence.GlobalSolutionGluingFromReachability p :=
  GlobalSolutionGluingFromReachability_of_regime_gammaGeOne
    p hχ.out ha.out hb.out hγ_ge_one.out

end

end ShenWork.Paper2
