import ShenWork.Paper1.WholeLineCauchyBUC
import Mathlib.Analysis.Calculus.MeanValue

open Filter Topology MeasureTheory Real Set
open scoped BoundedContinuousFunction

noncomputable section

namespace ShenWork.Paper1

/-!
# Truncated Cauchy nonlinearities as genuine BUC maps
-/

/-- The product of two bounded uniformly continuous real functions is
uniformly continuous. -/
theorem uniformContinuous_mul_of_bounded
    {f g : ℝ → ℝ} {A B : ℝ}
    (hf : UniformContinuous f) (hg : UniformContinuous g)
    (hf_bound : ∀ x, |f x| ≤ A) (hg_bound : ∀ x, |g x| ≤ B) :
    UniformContinuous (fun x => f x * g x) := by
  have hA : 0 ≤ A := (abs_nonneg (f 0)).trans (hf_bound 0)
  have hB : 0 ≤ B := (abs_nonneg (g 0)).trans (hg_bound 0)
  rw [Metric.uniformContinuous_iff] at hf hg ⊢
  intro ε hε
  let q := ε / (A + B + 1)
  have hden : 0 < A + B + 1 := by linarith
  have hq : 0 < q := div_pos hε hden
  rcases hf q hq with ⟨δf, hδf, hfu⟩
  rcases hg q hq with ⟨δg, hδg, hgu⟩
  refine ⟨min δf δg, lt_min hδf hδg, ?_⟩
  intro x y hxy
  have hfd : |f x - f y| < q := by
    simpa [Real.dist_eq] using hfu (lt_of_lt_of_le hxy (min_le_left _ _))
  have hgd : |g x - g y| < q := by
    simpa [Real.dist_eq] using hgu (lt_of_lt_of_le hxy (min_le_right _ _))
  have hprod :
      |f x * g x - f y * g y| ≤ A * |g x - g y| + B * |f x - f y| := by
    calc
      |f x * g x - f y * g y| =
          |f x * (g x - g y) + (f x - f y) * g y| := by ring_nf
      _ ≤ |f x| * |g x - g y| + |f x - f y| * |g y| := by
        simpa only [abs_mul] using
          abs_add_le (f x * (g x - g y)) ((f x - f y) * g y)
      _ ≤ A * |g x - g y| + B * |f x - f y| := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right (hf_bound x) (abs_nonneg _))
          (by
            calc
              |f x - f y| * |g y| ≤ |f x - f y| * B :=
                mul_le_mul_of_nonneg_left (hg_bound y) (abs_nonneg _)
              _ = B * |f x - f y| := by ring)
  have hsum : A * |g x - g y| + B * |f x - f y| ≤ (A + B) * q := by
    calc
      A * |g x - g y| + B * |f x - f y| ≤ A * q + B * q :=
        add_le_add
          (mul_le_mul_of_nonneg_left hgd.le hA)
          (mul_le_mul_of_nonneg_left hfd.le hB)
      _ = (A + B) * q := by ring
  have hratio : (A + B) / (A + B + 1) < 1 := by
    exact (div_lt_one hden).2 (by linarith)
  have hqeps : (A + B) * q < ε := by
    calc
      (A + B) * q = ε * ((A + B) / (A + B + 1)) := by
        dsimp [q]
        ring
      _ < ε * 1 := mul_lt_mul_of_pos_left hratio hε
      _ = ε := mul_one ε
  simpa [Real.dist_eq] using lt_of_le_of_lt hprod (lt_of_le_of_lt hsum hqeps)

/-- The resolver gradient of a profile in `[0,M]` is globally Lipschitz in
space, with the elliptic-equation bound `2 M^gamma`. -/
theorem frozenElliptic_deriv_lipschitz_of_Icc
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) {u : ℝ → ℝ}
    (hu : IsCUnifBdd u) (huM : ∀ x, u x ∈ Set.Icc (0 : ℝ) M) :
    LipschitzWith (Real.toNNReal (2 * M ^ p.γ))
      (deriv (frozenElliptic p u)) := by
  have hMγ : 0 ≤ M ^ p.γ := Real.rpow_nonneg hM _
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x => frozenElliptic_deriv_differentiableAt p hu (fun y => (huM y).1) x)
  intro x
  rw [← NNReal.coe_le_coe, coe_nnnorm,
    Real.coe_toNNReal _ (mul_nonneg (by norm_num) hMγ)]
  rw [Real.norm_eq_abs, frozenElliptic_deriv_deriv_eq p hu (fun y => (huM y).1) x]
  have hpow0 : 0 ≤ (u x) ^ p.γ := Real.rpow_nonneg (huM x).1 _
  have hpowM : (u x) ^ p.γ ≤ M ^ p.γ :=
    Real.rpow_le_rpow (huM x).1 (huM x).2 (by linarith [p.hγ])
  have hV0 : 0 ≤ frozenElliptic p u x :=
    frozenElliptic_nonneg p (fun y => (huM y).1) x
  have hVM : frozenElliptic p u x ≤ M ^ p.γ :=
    frozenElliptic_le_of_rpow_le p hMγ hu.1 (fun y => (huM y).1)
      (fun y => Real.rpow_le_rpow (huM y).1 (huM y).2 (by linarith [p.hγ])) x
  calc
    |frozenElliptic p u x - (u x) ^ p.γ| ≤
        |frozenElliptic p u x| + |(u x) ^ p.γ| := abs_sub _ _
    _ = frozenElliptic p u x + (u x) ^ p.γ := by
      rw [abs_of_nonneg hV0, abs_of_nonneg hpow0]
    _ ≤ 2 * M ^ p.γ := by linarith

theorem wholeLineCauchyTruncatedFlux_uniformContinuous
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) (u : WholeLineBUC) :
    UniformContinuous (wholeLineCauchyTruncatedFlux p M (u.1 : ℝ → ℝ)) := by
  let c : ℝ → ℝ := wholeLineCauchyClampProfile M (u.1 : ℝ → ℝ)
  have huIs : IsCUnifBdd (u.1 : ℝ → ℝ) := WholeLineBUC.isCUnifBdd u
  have hcIs : IsCUnifBdd c :=
    wholeLineCauchyClampProfile_isCUnifBdd hM huIs
  have hcM : ∀ x, c x ∈ Set.Icc (0 : ℝ) M :=
    wholeLineCauchyClampProfile_mem_Icc hM (u.1 : ℝ → ℝ)
  have hpow_uc : UniformContinuous (fun x => (c x) ^ p.m) := by
    have h := (rpowTrunc_lipschitz p.hm hM).uniformContinuous.comp u.2
    simpa [c, rpowTrunc, wholeLineCauchyClampProfile] using h
  have hpow_bound : ∀ x, |(c x) ^ p.m| ≤ M ^ p.m := by
    intro x
    rw [abs_of_nonneg (Real.rpow_nonneg (hcM x).1 _)]
    exact Real.rpow_le_rpow (hcM x).1 (hcM x).2 (by linarith [p.hm])
  have hR_uc : UniformContinuous (deriv (frozenElliptic p c)) :=
    (frozenElliptic_deriv_lipschitz_of_Icc p hM hcIs hcM).uniformContinuous
  have hR_bound : ∀ x, |deriv (frozenElliptic p c) x| ≤ M ^ p.γ :=
    frozenElliptic_deriv_abs_le_rpow_of_Icc p hM hcIs hcM
  simpa [wholeLineCauchyTruncatedFlux, wholeLineChemotaxisFlux, c] using
    uniformContinuous_mul_of_bounded hpow_uc hR_uc hpow_bound hR_bound

/-- Scalar form of the globally truncated shifted reaction. -/
def wholeLineCauchyTruncatedReactionScalar
    (p : CMParams) (M s : ℝ) : ℝ :=
  clampIcc M s + reactionFun p.α (clampIcc M s)

theorem wholeLineCauchyTruncatedReactionScalar_lipschitz
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) :
    LipschitzWith (Real.toNNReal (1 + reactionLip p.α M))
      (wholeLineCauchyTruncatedReactionScalar p M) := by
  have hL : 0 ≤ 1 + reactionLip p.α M := by
    linarith [reactionLip_nonneg p.hα hM]
  refine LipschitzWith.of_dist_le_mul ?_
  intro a b
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hL]
  simpa [wholeLineCauchyTruncatedReactionScalar,
    wholeLineCauchyTruncatedReaction, wholeLineCauchyShiftedReaction,
    wholeLineCauchyClampProfile, wholeLineLogisticSource] using
    wholeLineCauchyTruncatedReaction_diff_abs_le p hM
      (u := fun _ => a) (w := fun _ => b) (D := |a - b|)
      (fun _ => le_rfl) 0

theorem wholeLineCauchyTruncatedReaction_uniformContinuous
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) (u : WholeLineBUC) :
    UniformContinuous (wholeLineCauchyTruncatedReaction p M (u.1 : ℝ → ℝ)) := by
  have h := (wholeLineCauchyTruncatedReactionScalar_lipschitz p hM).uniformContinuous.comp u.2
  simpa [wholeLineCauchyTruncatedReactionScalar,
    wholeLineCauchyTruncatedReaction, wholeLineCauchyShiftedReaction,
    wholeLineCauchyClampProfile, wholeLineLogisticSource] using h

/-- The truncated flux as an element of the complete BUC phase space. -/
def wholeLineCauchyTruncatedFluxBUC
    (p : CMParams) (M : ℝ) (hM : 0 ≤ M) (u : WholeLineBUC) : WholeLineBUC :=
  wholeLineBUCOfUniformBound
    (wholeLineCauchyTruncatedFlux p M (u.1 : ℝ → ℝ))
    (wholeLineCauchyTruncatedFlux_uniformContinuous p hM u)
    (M ^ p.m * M ^ p.γ)
    (wholeLineCauchyTruncatedFlux_abs_le p hM (WholeLineBUC.isCUnifBdd u))

/-- The truncated shifted reaction as an element of BUC. -/
def wholeLineCauchyTruncatedReactionBUC
    (p : CMParams) (M : ℝ) (hM : 0 ≤ M) (u : WholeLineBUC) : WholeLineBUC :=
  wholeLineBUCOfUniformBound
    (wholeLineCauchyTruncatedReaction p M (u.1 : ℝ → ℝ))
    (wholeLineCauchyTruncatedReaction_uniformContinuous p hM u)
    (M + M * (1 + M ^ p.α))
    (wholeLineCauchyTruncatedReaction_abs_le p hM (u.1 : ℝ → ℝ))

@[simp] theorem wholeLineCauchyTruncatedFluxBUC_apply
    (p : CMParams) (M : ℝ) (hM : 0 ≤ M) (u : WholeLineBUC) (x : ℝ) :
    (wholeLineCauchyTruncatedFluxBUC p M hM u).1 x =
      wholeLineCauchyTruncatedFlux p M (u.1 : ℝ → ℝ) x :=
  rfl

@[simp] theorem wholeLineCauchyTruncatedReactionBUC_apply
    (p : CMParams) (M : ℝ) (hM : 0 ≤ M) (u : WholeLineBUC) (x : ℝ) :
    (wholeLineCauchyTruncatedReactionBUC p M hM u).1 x =
      wholeLineCauchyTruncatedReaction p M (u.1 : ℝ → ℝ) x :=
  rfl

theorem WholeLineBUC.pointwise_abs_sub_le_dist
    (u w : WholeLineBUC) (x : ℝ) :
    |u.1 x - w.1 x| ≤ dist u w := by
  change dist (u.1 x) (w.1 x) ≤ dist u.1 w.1
  exact BoundedContinuousFunction.dist_coe_le_dist x

theorem wholeLineCauchyTruncatedFluxBUC_dist_le
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) (u w : WholeLineBUC) :
    dist (wholeLineCauchyTruncatedFluxBUC p M hM u)
        (wholeLineCauchyTruncatedFluxBUC p M hM w) ≤
      wholeLineCauchyFluxLip p M * dist u w := by
  change dist
      (wholeLineCauchyTruncatedFluxBUC p M hM u).1
      (wholeLineCauchyTruncatedFluxBUC p M hM w).1 ≤ _
  rw [BoundedContinuousFunction.dist_le_iff_of_nonempty]
  intro x
  rw [Real.dist_eq, wholeLineCauchyTruncatedFluxBUC_apply,
    wholeLineCauchyTruncatedFluxBUC_apply]
  exact wholeLineCauchyTruncatedFlux_diff_abs_le p hM
    (WholeLineBUC.isCUnifBdd u) (WholeLineBUC.isCUnifBdd w)
    (fun y => WholeLineBUC.pointwise_abs_sub_le_dist u w y) x

theorem wholeLineCauchyTruncatedReactionBUC_dist_le
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) (u w : WholeLineBUC) :
    dist (wholeLineCauchyTruncatedReactionBUC p M hM u)
        (wholeLineCauchyTruncatedReactionBUC p M hM w) ≤
      (1 + reactionLip p.α M) * dist u w := by
  change dist
      (wholeLineCauchyTruncatedReactionBUC p M hM u).1
      (wholeLineCauchyTruncatedReactionBUC p M hM w).1 ≤ _
  rw [BoundedContinuousFunction.dist_le_iff_of_nonempty]
  intro x
  rw [Real.dist_eq, wholeLineCauchyTruncatedReactionBUC_apply,
    wholeLineCauchyTruncatedReactionBUC_apply]
  exact wholeLineCauchyTruncatedReaction_diff_abs_le p hM
    (fun y => WholeLineBUC.pointwise_abs_sub_le_dist u w y) x

theorem wholeLineCauchyTruncatedFluxBUC_lipschitz
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) :
    LipschitzWith (Real.toNNReal (wholeLineCauchyFluxLip p M))
      (wholeLineCauchyTruncatedFluxBUC p M hM) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro u w
  rw [Real.coe_toNNReal _ (wholeLineCauchyFluxLip_nonneg p hM)]
  exact wholeLineCauchyTruncatedFluxBUC_dist_le p hM u w

theorem wholeLineCauchyTruncatedReactionBUC_lipschitz
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) :
    LipschitzWith (Real.toNNReal (1 + reactionLip p.α M))
      (wholeLineCauchyTruncatedReactionBUC p M hM) := by
  have hL : 0 ≤ 1 + reactionLip p.α M := by
    linarith [reactionLip_nonneg p.hα hM]
  refine LipschitzWith.of_dist_le_mul ?_
  intro u w
  rw [Real.coe_toNNReal _ hL]
  exact wholeLineCauchyTruncatedReactionBUC_dist_le p hM u w

section WholeLineCauchyBUCSourcesAxiomAudit

#print axioms uniformContinuous_mul_of_bounded
#print axioms frozenElliptic_deriv_lipschitz_of_Icc
#print axioms wholeLineCauchyTruncatedFlux_uniformContinuous
#print axioms wholeLineCauchyTruncatedReactionScalar_lipschitz
#print axioms wholeLineCauchyTruncatedReaction_uniformContinuous
#print axioms wholeLineCauchyTruncatedFluxBUC
#print axioms wholeLineCauchyTruncatedReactionBUC
#print axioms WholeLineBUC.pointwise_abs_sub_le_dist
#print axioms wholeLineCauchyTruncatedFluxBUC_lipschitz
#print axioms wholeLineCauchyTruncatedReactionBUC_lipschitz

end WholeLineCauchyBUCSourcesAxiomAudit

end ShenWork.Paper1
