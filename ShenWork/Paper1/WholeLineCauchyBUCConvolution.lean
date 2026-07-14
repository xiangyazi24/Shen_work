import ShenWork.Paper1.WholeLineCauchyBUCSources
import ShenWork.Paper1.WaveRotheTrap

open Filter Topology MeasureTheory Real Set
open scoped BoundedContinuousFunction

noncomputable section

namespace ShenWork.Paper1

/-!
# Integrable convolution kernels on `BUC(ℝ)`

The bounded-continuous convolution engine already used by the Rothe scheme
actually preserves uniform continuity.  This file records that stronger fact
and promotes convolution to a genuine Lipschitz self-map of the complete BUC
phase space.
-/

theorem kernelConvVal_uniformContinuous
    {K : ℝ → ℝ} (hK_int : Integrable K) (g : WholeLineBUC) :
    UniformContinuous (kernelConvVal K g.1) := by
  have hA : 0 ≤ ∫ z : ℝ, |K z| := integral_nonneg fun z => abs_nonneg (K z)
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  let A : ℝ := ∫ z : ℝ, |K z|
  let q : ℝ := ε / (A + 1)
  have hden : 0 < A + 1 := by dsimp [A]; linarith
  have hq : 0 < q := div_pos hε hden
  have hgUC : UniformContinuous (g.1 : ℝ → ℝ) := g.2
  rw [Metric.uniformContinuous_iff] at hgUC
  rcases hgUC q hq with ⟨δ, hδ, hg⟩
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy
  have hshift : ∀ z : ℝ, |g.1 (x - z) - g.1 (y - z)| < q := by
    intro z
    have harg : dist (x - z) (y - z) < δ := by
      simpa [Real.dist_eq] using hxy
    simpa [Real.dist_eq] using hg harg
  have hx_int : Integrable (fun z : ℝ => K z * g.1 (x - z)) := by
    refine hK_int.mul_bdd (c := ‖g.1‖)
      (g.1.continuous.comp (by fun_prop)).aestronglyMeasurable ?_
    exact Eventually.of_forall fun z => by
      simpa [Real.norm_eq_abs] using g.1.norm_coe_le_norm (x - z)
  have hy_int : Integrable (fun z : ℝ => K z * g.1 (y - z)) := by
    refine hK_int.mul_bdd (c := ‖g.1‖)
      (g.1.continuous.comp (by fun_prop)).aestronglyMeasurable ?_
    exact Eventually.of_forall fun z => by
      simpa [Real.norm_eq_abs] using g.1.norm_coe_le_norm (y - z)
  have hdiff_int : Integrable
      (fun z : ℝ => K z * g.1 (x - z) - K z * g.1 (y - z)) :=
    hx_int.sub hy_int
  have hmajor_int : Integrable (fun z : ℝ => |K z| * q) :=
    hK_int.abs.mul_const q
  have hmono :
      (∫ z : ℝ, |K z * g.1 (x - z) - K z * g.1 (y - z)|) ≤
        ∫ z : ℝ, |K z| * q := by
    apply integral_mono hdiff_int.abs hmajor_int
    intro z
    change |K z * g.1 (x - z) - K z * g.1 (y - z)| ≤ |K z| * q
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left (hshift z).le (abs_nonneg (K z))
  have hnorm :
      |∫ z : ℝ, K z * g.1 (x - z) - K z * g.1 (y - z)| ≤
        ∫ z : ℝ, |K z * g.1 (x - z) - K z * g.1 (y - z)| := by
    simpa [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (fun z : ℝ =>
        K z * g.1 (x - z) - K z * g.1 (y - z))
  have hratio : A / (A + 1) < 1 := by
    exact (div_lt_one hden).2 (by dsimp [A]; linarith)
  have hAq : A * q < ε := by
    calc
      A * q = ε * (A / (A + 1)) := by
        dsimp [q]
        ring
      _ < ε * 1 := mul_lt_mul_of_pos_left hratio hε
      _ = ε := mul_one ε
  rw [Real.dist_eq, kernelConvVal_eq_shift K g.1 x,
    kernelConvVal_eq_shift K g.1 y, ← integral_sub hx_int hy_int]
  have hmajor_eq : (∫ z : ℝ, |K z| * q) = A * q := by
    rw [integral_mul_const]
  exact lt_of_le_of_lt (hnorm.trans (hmono.trans_eq hmajor_eq)) hAq

/-- Convolution by a continuous integrable kernel as an element of BUC. -/
def kernelConvBUC
    {K : ℝ → ℝ} (hK_cont : Continuous K) (hK_int : Integrable K)
    (g : WholeLineBUC) : WholeLineBUC :=
  ⟨greenConvBCF hK_cont hK_int g.1,
    kernelConvVal_uniformContinuous hK_int g⟩

@[simp] theorem kernelConvBUC_apply
    {K : ℝ → ℝ} (hK_cont : Continuous K) (hK_int : Integrable K)
    (g : WholeLineBUC) (x : ℝ) :
    (kernelConvBUC hK_cont hK_int g).1 x = kernelConvVal K g.1 x :=
  rfl

theorem kernelConvBUC_dist_le
    {K : ℝ → ℝ} (hK_cont : Continuous K) (hK_int : Integrable K)
    (g₁ g₂ : WholeLineBUC) :
    dist (kernelConvBUC hK_cont hK_int g₁)
        (kernelConvBUC hK_cont hK_int g₂) ≤
      (∫ z : ℝ, |K z|) * dist g₁ g₂ := by
  change dist
      (greenConvBCF hK_cont hK_int g₁.1)
      (greenConvBCF hK_cont hK_int g₂.1) ≤ _
  rw [BoundedContinuousFunction.dist_le_iff_of_nonempty]
  intro x
  simpa only [greenConvBCF_apply] using
    kernelConvVal_dist_le hK_cont hK_int g₁.1 g₂.1 x

theorem kernelConvBUC_lipschitz
    {K : ℝ → ℝ} (hK_cont : Continuous K) (hK_int : Integrable K) :
    LipschitzWith (Real.toNNReal (∫ z : ℝ, |K z|))
      (kernelConvBUC hK_cont hK_int) := by
  have hA : 0 ≤ ∫ z : ℝ, |K z| := integral_nonneg fun z => abs_nonneg (K z)
  refine LipschitzWith.of_dist_le_mul ?_
  intro g₁ g₂
  rw [Real.coe_toNNReal _ hA]
  exact kernelConvBUC_dist_le hK_cont hK_int g₁ g₂

section WholeLineCauchyBUCConvolutionAxiomAudit

#print axioms kernelConvVal_uniformContinuous
#print axioms kernelConvBUC
#print axioms kernelConvBUC_dist_le
#print axioms kernelConvBUC_lipschitz

end WholeLineCauchyBUCConvolutionAxiomAudit

end ShenWork.Paper1
