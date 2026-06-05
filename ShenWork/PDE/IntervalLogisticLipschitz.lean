/-
  ShenWork/PDE/IntervalLogisticLipschitz.lean

  T7 existence — **Atom C (reaction part)**: the logistic reaction
  `x ↦ x·(a − b·x^α)` is Lipschitz on the trajectory ball `[-M,M]`.

  This is exactly the scalar `hL_lip` slot consumed by
  `localExistence_of_coupledDuhamel_resolver_estimates_and_regularization`
  (`ShenWork/PDE/IntervalDomainExistence.lean`):

      hL_lip : ∀ a b, |a| ≤ M → |b| ≤ M →
        |a·(p.a − p.b·a^α) − b·(p.a − p.b·b^α)| ≤ L·|a − b|.

  The Lipschitz constant is `L = p.a + p.b·(1+α)·M^α`, the sup of `|f'|` on the
  ball, with `f'(x) = p.a − p.b·(1+α)·x^α`.  Proof by the mean-value bound
  `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`, adapting the normalized
  whole-line lemma `MildSolution.logistic_lipschitz_on_bounded` to general
  `CM2Params` coefficients (`p.a ≥ 0`, `p.b ≥ 0`).

  Regime: `1 ≤ p.α` is taken as an explicit hypothesis (NOT smuggled) — it is
  what makes `x ↦ x^α` differentiable up to `x = 0` and at negative `x` via the
  `Real.hasDerivAt_rpow_const` `1 ≤ p` branch, so the reaction is genuinely `C¹`
  on the two-sided ball.

  No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.Paper2.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open Set Real

noncomputable section

namespace ShenWork.IntervalLogisticLipschitz

/-- **Atom C — logistic reaction Lipschitz on the ball.**  For `1 ≤ p.α` and
`0 < M`, the reaction `x ↦ x·(p.a − p.b·x^α)` is Lipschitz on `[-M,M]` with an
explicit positive constant `L = p.a + p.b·(1+α)·M^α + 1`.  Discharges the
`hL_lip` hypothesis of the coupled-Duhamel local-existence reduction. -/
theorem intervalLogisticReaction_lipschitz_on_bounded
    (p : CM2Params) (hα : 1 ≤ p.α) {M : ℝ} (hM : 0 < M) :
    ∃ L > 0, ∀ u₁ u₂ : ℝ, |u₁| ≤ M → |u₂| ≤ M →
      |u₁ * (p.a - p.b * u₁ ^ p.α) - u₂ * (p.a - p.b * u₂ ^ p.α)|
        ≤ L * |u₁ - u₂| := by
  set α := p.α with hα_def
  have hα0 : 0 ≤ α := by linarith
  have hαm1 : 0 ≤ α - 1 := by linarith
  have hM0 : 0 ≤ M := le_of_lt hM
  -- the mean-value Lipschitz constant `C = sup_{[-M,M]} |f'|`
  set C : ℝ := p.a + p.b * (1 + α) * M ^ α with hC_def
  have hMα_nonneg : 0 ≤ M ^ α := Real.rpow_nonneg hM0 α
  have hC_nonneg : 0 ≤ C := by
    have : 0 ≤ p.b * (1 + α) * M ^ α :=
      mul_nonneg (mul_nonneg p.hb (by linarith)) hMα_nonneg
    have := add_nonneg p.ha this
    simpa [hC_def] using this
  refine ⟨C + 1, by linarith, ?_⟩
  intro u₁ u₂ hu₁ hu₂
  -- the reaction and its derivative field on `[-M,M]`
  set f : ℝ → ℝ := fun x => x * (p.a - p.b * x ^ α) with hf_def
  set fp : ℝ → ℝ := fun x => 1 * (p.a - p.b * x ^ α)
      + x * (0 - p.b * (α * x ^ (α - 1))) with hfp_def
  have hu₁s : u₁ ∈ Set.Icc (-M) M := abs_le.mp hu₁
  have hu₂s : u₂ ∈ Set.Icc (-M) M := abs_le.mp hu₂
  have hder : ∀ x ∈ Set.Icc (-M) M,
      HasDerivWithinAt f (fp x) (Set.Icc (-M) M) x := by
    intro x _hx
    have hp : HasDerivAt (fun y : ℝ => y ^ α) (α * x ^ (α - 1)) x :=
      Real.hasDerivAt_rpow_const (x := x) (p := α) (Or.inr hα)
    have hsub : HasDerivAt (fun y : ℝ => p.a - p.b * y ^ α)
        (0 - p.b * (α * x ^ (α - 1))) x :=
      (hasDerivAt_const x p.a).sub (hp.const_mul p.b)
    have hmul : HasDerivAt f
        (1 * (p.a - p.b * x ^ α) + x * (0 - p.b * (α * x ^ (α - 1)))) x := by
      simpa [hf_def] using (hasDerivAt_id' x).fun_mul hsub
    simpa [hfp_def] using hmul.hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Icc (-M) M, ‖fp x‖ ≤ C := by
    intro x hx
    have hxabs : |x| ≤ M := abs_le.mpr hx
    have hxpow : |x ^ α| ≤ M ^ α := by
      calc |x ^ α| ≤ |x| ^ α := Real.abs_rpow_le_abs_rpow x α
        _ ≤ M ^ α := Real.rpow_le_rpow (abs_nonneg x) hxabs hα0
    have hxpowm1 : |x ^ (α - 1)| ≤ M ^ (α - 1) := by
      calc |x ^ (α - 1)| ≤ |x| ^ (α - 1) := Real.abs_rpow_le_abs_rpow x (α - 1)
        _ ≤ M ^ (α - 1) := Real.rpow_le_rpow (abs_nonneg x) hxabs hαm1
    have hMpow : M ^ (α - 1) * M = M ^ α := by
      rw [← Real.rpow_add_one (ne_of_gt hM) (α - 1)]; congr 1; ring
    -- `|first term| = |p.a − p.b·x^α| ≤ p.a + p.b·M^α`
    have hterm1 : |1 * (p.a - p.b * x ^ α)| ≤ p.a + p.b * M ^ α := by
      simp only [one_mul]
      calc |p.a - p.b * x ^ α| ≤ |p.a| + |p.b * x ^ α| := abs_sub _ _
        _ = p.a + p.b * |x ^ α| := by
            rw [abs_of_nonneg p.ha, abs_mul, abs_of_nonneg p.hb]
        _ ≤ p.a + p.b * M ^ α := by
            linarith [mul_le_mul_of_nonneg_left hxpow p.hb]
    -- `|second term| = |x|·p.b·α·|x^{α-1}| ≤ p.b·α·M^α`
    have hterm2 : |x * (0 - p.b * (α * x ^ (α - 1)))| ≤ p.b * α * M ^ α := by
      rw [abs_mul]
      have hsnd : |0 - p.b * (α * x ^ (α - 1))| = p.b * α * |x ^ (α - 1)| := by
        rw [zero_sub, abs_neg, abs_mul, abs_of_nonneg p.hb, abs_mul,
          abs_of_nonneg hα0]; ring
      rw [hsnd]
      have hinner : p.b * α * |x ^ (α - 1)| ≤ p.b * α * M ^ (α - 1) :=
        mul_le_mul_of_nonneg_left hxpowm1 (mul_nonneg p.hb hα0)
      calc |x| * (p.b * α * |x ^ (α - 1)|)
          ≤ M * (p.b * α * M ^ (α - 1)) :=
            mul_le_mul hxabs hinner
              (mul_nonneg (mul_nonneg p.hb hα0) (abs_nonneg _)) hM0
        _ = p.b * α * M ^ α := by rw [← hMpow]; ring
    calc ‖fp x‖ = |1 * (p.a - p.b * x ^ α)
            + x * (0 - p.b * (α * x ^ (α - 1)))| := by
          rw [Real.norm_eq_abs, hfp_def]
      _ ≤ |1 * (p.a - p.b * x ^ α)|
            + |x * (0 - p.b * (α * x ^ (α - 1)))| := abs_add_le _ _
      _ ≤ (p.a + p.b * M ^ α) + p.b * α * M ^ α := add_le_add hterm1 hterm2
      _ = C := by rw [hC_def]; ring
  have hmv : ‖f u₁ - f u₂‖ ≤ C * ‖u₁ - u₂‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      hder hbound (convex_Icc (-M) M) hu₂s hu₁s
  have hCle : C * |u₁ - u₂| ≤ (C + 1) * |u₁ - u₂| := by
    have : (0 : ℝ) ≤ |u₁ - u₂| := abs_nonneg _
    nlinarith [this]
  calc |u₁ * (p.a - p.b * u₁ ^ α) - u₂ * (p.a - p.b * u₂ ^ α)|
      = ‖f u₁ - f u₂‖ := by rw [Real.norm_eq_abs, hf_def]
    _ ≤ C * ‖u₁ - u₂‖ := hmv
    _ = C * |u₁ - u₂| := by rw [Real.norm_eq_abs]
    _ ≤ (C + 1) * |u₁ - u₂| := hCle

/-- **One-sided logistic Lipschitz for α > 0 on [0,M].**  For any `CM2Params` (so
`0 < p.α`), the reaction `x ↦ x·(p.a − p.b·x^α)` is Lipschitz on `[0,M]`.
The key is rewriting as `a·x − b·x^{1+α}` which is C¹ everywhere since
`1 + α > 1`, bypassing the `1 ≤ α` requirement of the two-sided version. -/
theorem intervalLogisticReaction_lipschitz_on_nonneg_bounded
    (p : CM2Params) {M : ℝ} (hM : 0 < M) :
    ∃ L > 0, ∀ u₁ u₂ : ℝ, 0 ≤ u₁ → u₁ ≤ M → 0 ≤ u₂ → u₂ ≤ M →
      |u₁ * (p.a - p.b * u₁ ^ p.α) - u₂ * (p.a - p.b * u₂ ^ p.α)|
        ≤ L * |u₁ - u₂| := by
  set α := p.α with hα_def
  have hα : 0 < α := p.hα
  have h1α : 1 ≤ 1 + α := by linarith
  have h1α_ne : (1 : ℝ) + α ≠ 0 := by linarith
  have hα0 : 0 ≤ α := hα.le
  have hM0 : 0 ≤ M := hM.le
  set C : ℝ := p.a + p.b * ((1 + α) * M ^ α) with hC_def
  have hMα_nn : 0 ≤ M ^ α := Real.rpow_nonneg hM0 α
  have hC_nn : 0 ≤ C := by
    have : 0 ≤ p.b * ((1 + α) * M ^ α) :=
      mul_nonneg p.hb (mul_nonneg (by linarith) hMα_nn)
    linarith [p.ha]
  refine ⟨C + 1, by linarith, ?_⟩
  intro u₁ u₂ hu₁_nn hu₁_le hu₂_nn hu₂_le
  set g : ℝ → ℝ := fun x => p.a * x - p.b * x ^ (1 + α) with hg_def
  set gp : ℝ → ℝ := fun x => p.a - p.b * ((1 + α) * x ^ α) with hgp_def
  have hu₁s : u₁ ∈ Set.Icc 0 M := ⟨hu₁_nn, hu₁_le⟩
  have hu₂s : u₂ ∈ Set.Icc 0 M := ⟨hu₂_nn, hu₂_le⟩
  have hder : ∀ x ∈ Set.Icc 0 M,
      HasDerivWithinAt g (gp x) (Set.Icc 0 M) x := by
    intro x _hx
    have hpow : HasDerivAt (fun y => y ^ (1 + α)) ((1 + α) * x ^ ((1 + α) - 1)) x :=
      Real.hasDerivAt_rpow_const (x := x) (p := 1 + α) (Or.inr h1α)
    have hpow' : HasDerivAt (fun y => y ^ (1 + α)) ((1 + α) * x ^ α) x := by
      convert hpow using 2; ring
    have h1 : HasDerivAt (fun y => p.a * y) p.a x := by
      simpa using (hasDerivAt_id x).const_mul p.a
    have h2 : HasDerivAt (fun y => p.b * y ^ (1 + α)) (p.b * ((1 + α) * x ^ α)) x :=
      hpow'.const_mul p.b
    exact (h1.sub h2).hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Icc 0 M, ‖gp x‖ ≤ C := by
    intro x hx
    have hx_nn : 0 ≤ x := hx.1
    have hxα_nn : 0 ≤ x ^ α := Real.rpow_nonneg hx_nn α
    have hxα_le : x ^ α ≤ M ^ α := Real.rpow_le_rpow hx_nn hx.2 hα0
    have hterm_nn : 0 ≤ p.b * ((1 + α) * x ^ α) :=
      mul_nonneg p.hb (mul_nonneg (by linarith) hxα_nn)
    have hterm_le : p.b * ((1 + α) * x ^ α) ≤ p.b * ((1 + α) * M ^ α) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hxα_le (by linarith)) p.hb
    have hMterm_nn : 0 ≤ p.b * ((1 + α) * M ^ α) :=
      mul_nonneg p.hb (mul_nonneg (by linarith) hMα_nn)
    rw [Real.norm_eq_abs, hgp_def, abs_le]
    exact ⟨by linarith [p.ha], by linarith⟩
  have hmv : ‖g u₁ - g u₂‖ ≤ C * ‖u₁ - u₂‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      hder hbound (convex_Icc 0 M) hu₂s hu₁s
  have heq : ∀ x, 0 ≤ x → x * (p.a - p.b * x ^ α) = g x := by
    intro x hx
    simp only [hg_def]
    rw [Real.rpow_one_add' hx h1α_ne, mul_sub, mul_comm x p.a, mul_left_comm x p.b]
  rw [heq u₁ hu₁_nn, heq u₂ hu₂_nn]
  calc |g u₁ - g u₂| = ‖g u₁ - g u₂‖ := (Real.norm_eq_abs _).symm
    _ ≤ C * ‖u₁ - u₂‖ := hmv
    _ = C * |u₁ - u₂| := by rw [Real.norm_eq_abs]
    _ ≤ (C + 1) * |u₁ - u₂| := by nlinarith [abs_nonneg (u₁ - u₂)]

end ShenWork.IntervalLogisticLipschitz
