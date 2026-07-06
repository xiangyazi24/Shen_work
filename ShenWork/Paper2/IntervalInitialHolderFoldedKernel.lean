/-
  ShenWork/Paper2/IntervalInitialHolderFoldedKernel.lean

  First real-space folded-kernel atoms for producing the common folded-noise
  interface used by `IntervalInitialHolder`.
-/
import ShenWork.Paper2.IntervalInitialHolder
import ShenWork.PDE.IntervalFullKernelMass

open MeasureTheory
open scoped Real Topology

namespace ShenWork.Paper2

noncomputable section

open ShenWork.IntervalDomain (intervalDomainPoint)
open AddSubgroup

/-- Adding an integer multiple of the period does not change the period-2
additive-circle point. -/
theorem addCircle_two_coe_add_period_eq (a : ℝ) (k : ℤ) :
    (((a + 2 * (k : ℝ) : ℝ) : AddCircle (2 : ℝ))) =
      (a : AddCircle (2 : ℝ)) := by
  rw [← sub_eq_zero]
  rw [← QuotientAddGroup.mk_sub]
  simp only [add_sub_cancel_left, QuotientAddGroup.eq_zero_iff]
  rw [mul_comm, ← zsmul_eq_mul]
  exact AddSubgroup.zsmul_mem_zmultiples (2 : ℝ) k

/-- Folding `y + 2k` on the period-2 circle gives `y` for `y ∈ [0,1]`. -/
theorem addCircleTwoFoldPoint_coe_add_period_eq
    {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) (k : ℤ) :
    (addCircleTwoFoldPoint (((y + 2 * (k : ℝ) : ℝ) : AddCircle (2 : ℝ)))).1 =
      y := by
  have hper := addCircle_two_coe_add_period_eq y k
  have hdist := addCircle_two_dist_coe_eq_abs_Icc hy
    (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
  rw [hper]
  simpa [addCircleTwoFoldPoint, abs_of_nonneg hy.1] using hdist

/-- Folding `-y + 2k` on the period-2 circle gives `y` for `y ∈ [0,1]`. -/
theorem addCircleTwoFoldPoint_neg_add_period_eq
    {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) (k : ℤ) :
    (addCircleTwoFoldPoint (((-y + 2 * (k : ℝ) : ℝ) : AddCircle (2 : ℝ)))).1 =
      y := by
  have hper := addCircle_two_coe_add_period_eq (-y) k
  have habs_le : |(-y) - 0| ≤ 1 := by
    rw [sub_zero, abs_neg, abs_of_nonneg hy.1]
    exact hy.2
  have hdist :=
    addCircle_two_dist_coe_eq_abs_of_abs_le_one (x := -y) (y := 0) habs_le
  rw [hper]
  simpa [addCircleTwoFoldPoint, abs_of_nonneg hy.1] using hdist

/-- The real-line folded Gaussian representation candidate for the interval
Neumann semigroup. -/
noncomputable def foldedHeatIntegral
    (t : ℝ) (x : intervalDomainPoint) (f : ℝ → ℝ) : ℝ :=
  ∫ z : ℝ, heatKernel t z * f (addCircleTwoFoldTranslatePoint x z).1

/-- The folded translate coordinate is Borel-measurable in the real noise
variable. -/
theorem addCircleTwoFoldTranslatePoint_coord_measurable
    (x : intervalDomainPoint) :
    Measurable (fun z : ℝ => (addCircleTwoFoldTranslatePoint x z).1) := by
  unfold addCircleTwoFoldTranslatePoint addCircleTwoFoldPoint
  exact (Continuous.dist
    ((AddCircle.continuous_mk' (2 : ℝ)).comp (continuous_const.add continuous_id))
    continuous_const).measurable

/-- A bounded measurable datum gives an integrable folded heat integrand on the
real noise line. -/
theorem foldedHeat_integrable_of_bounded
    {t : ℝ} (ht : 0 < t) (x : intervalDomainPoint)
    {f : ℝ → ℝ} {M : ℝ}
    (hf_meas : Measurable f) (hf_bound : ∀ y, |f y| ≤ M) :
    Integrable
      (fun z : ℝ => heatKernel t z * f (addCircleTwoFoldTranslatePoint x z).1) := by
  have hf_comp :
      AEStronglyMeasurable
        (fun z : ℝ => f (addCircleTwoFoldTranslatePoint x z).1) volume :=
    (hf_meas.comp (addCircleTwoFoldTranslatePoint_coord_measurable x)).aestronglyMeasurable
  exact (heatKernel_integrable ht).mul_bdd hf_comp
    (Filter.Eventually.of_forall fun z => by
      simpa [Real.norm_eq_abs] using hf_bound (addCircleTwoFoldTranslatePoint x z).1)

/-- On one period-2 cell in the real noise variable, the folded real-line
integral is exactly the sum of the two image branches over `[0,1]`. -/
theorem foldedHeat_cell_integral_eq_two_branches
    (t : ℝ) (x : intervalDomainPoint) (f : ℝ → ℝ) (k : ℤ)
    (hG : Integrable
      (fun z : ℝ => heatKernel t z * f (addCircleTwoFoldTranslatePoint x z).1)) :
    (∫ z in Set.Ioc (-x.1 + 2 * (k : ℝ) - 1) (-x.1 + 2 * (k : ℝ) + 1),
        heatKernel t z * f (addCircleTwoFoldTranslatePoint x z).1)
      =
        (∫ y in (0 : ℝ)..1, heatKernel t (-x.1 - y + 2 * (k : ℝ)) * f y)
          + (∫ y in (0 : ℝ)..1, heatKernel t (-x.1 + y + 2 * (k : ℝ)) * f y) := by
  set G : ℝ → ℝ := fun z => heatKernel t z * f (addCircleTwoFoldTranslatePoint x z).1
  have hcell := ShenWork.cell_integral_eq (g := G) hG (-x.1) k
  rw [← hcell]
  congr 1
  · refine intervalIntegral.integral_congr (fun y hy => ?_)
    have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy
    have hfold :
        (addCircleTwoFoldTranslatePoint x (-x.1 - y + 2 * (k : ℝ))).1 = y := by
      unfold addCircleTwoFoldTranslatePoint
      have harg : x.1 + (-x.1 - y + 2 * (k : ℝ)) = -y + 2 * (k : ℝ) := by
        ring
      rw [harg]
      exact addCircleTwoFoldPoint_neg_add_period_eq hyIcc k
    simp [G, hfold]
  · refine intervalIntegral.integral_congr (fun y hy => ?_)
    have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy
    have hfold :
        (addCircleTwoFoldTranslatePoint x (-x.1 + y + 2 * (k : ℝ))).1 = y := by
      unfold addCircleTwoFoldTranslatePoint
      have harg : x.1 + (-x.1 + y + 2 * (k : ℝ)) = y + 2 * (k : ℝ) := by
        ring
      rw [harg]
      exact addCircleTwoFoldPoint_coe_add_period_eq hyIcc k
    simp [G, hfold]

/-- Bounded measurable version of `foldedHeat_cell_integral_eq_two_branches`. -/
theorem foldedHeat_cell_integral_eq_two_branches_of_bounded
    {t : ℝ} (ht : 0 < t) (x : intervalDomainPoint) (f : ℝ → ℝ) (k : ℤ)
    {M : ℝ} (hf_meas : Measurable f) (hf_bound : ∀ y, |f y| ≤ M) :
    (∫ z in Set.Ioc (-x.1 + 2 * (k : ℝ) - 1) (-x.1 + 2 * (k : ℝ) + 1),
        heatKernel t z * f (addCircleTwoFoldTranslatePoint x z).1)
      =
        (∫ y in (0 : ℝ)..1, heatKernel t (-x.1 - y + 2 * (k : ℝ)) * f y)
          + (∫ y in (0 : ℝ)..1, heatKernel t (-x.1 + y + 2 * (k : ℝ)) * f y) :=
  foldedHeat_cell_integral_eq_two_branches t x f k
    (foldedHeat_integrable_of_bounded ht x hf_meas hf_bound)

/-- The two folded image-branch lattice sums are the two full-kernel branches,
after the involutive reindexing `k ↦ -k` and the evenness of `heatKernel`. -/
theorem foldedHeat_branch_tsum_reindex
    (t : ℝ) (x : intervalDomainPoint) (f : ℝ → ℝ)
    (hA : Summable (fun k : ℤ =>
      ∫ y in (0 : ℝ)..1, heatKernel t (-x.1 - y + 2 * (k : ℝ)) * f y))
    (hB : Summable (fun k : ℤ =>
      ∫ y in (0 : ℝ)..1, heatKernel t (-x.1 + y + 2 * (k : ℝ)) * f y)) :
    (∑' k : ℤ,
        ((∫ y in (0 : ℝ)..1, heatKernel t (-x.1 - y + 2 * (k : ℝ)) * f y)
          + (∫ y in (0 : ℝ)..1, heatKernel t (-x.1 + y + 2 * (k : ℝ)) * f y)))
      =
        (∑' k : ℤ,
          ∫ y in (0 : ℝ)..1, heatKernel t (x.1 - y + 2 * (k : ℝ)) * f y)
          + (∑' k : ℤ,
            ∫ y in (0 : ℝ)..1, heatKernel t (x.1 + y + 2 * (k : ℝ)) * f y) := by
  set A : ℤ → ℝ := fun k =>
    ∫ y in (0 : ℝ)..1, heatKernel t (-x.1 - y + 2 * (k : ℝ)) * f y
  set B : ℤ → ℝ := fun k =>
    ∫ y in (0 : ℝ)..1, heatKernel t (-x.1 + y + 2 * (k : ℝ)) * f y
  set C : ℤ → ℝ := fun k =>
    ∫ y in (0 : ℝ)..1, heatKernel t (x.1 - y + 2 * (k : ℝ)) * f y
  set D : ℤ → ℝ := fun k =>
    ∫ y in (0 : ℝ)..1, heatKernel t (x.1 + y + 2 * (k : ℝ)) * f y
  have hAeq : A = D ∘ Equiv.neg ℤ := by
    funext k
    simp only [A, D, Function.comp, Equiv.neg_apply]
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    congr 1
    rw [← heatKernel_neg t (x.1 + y + 2 * ((-k : ℤ) : ℝ))]
    congr 1
    push_cast
    ring
  have hBeq : B = C ∘ Equiv.neg ℤ := by
    funext k
    simp only [B, C, Function.comp, Equiv.neg_apply]
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    congr 1
    rw [← heatKernel_neg t (x.1 - y + 2 * ((-k : ℤ) : ℝ))]
    congr 1
    push_cast
    ring
  have hAt : (∑' k : ℤ, A k) = ∑' k : ℤ, D k := by
    rw [hAeq]
    exact Equiv.tsum_eq (Equiv.neg ℤ) D
  have hBt : (∑' k : ℤ, B k) = ∑' k : ℤ, C k := by
    rw [hBeq]
    exact Equiv.tsum_eq (Equiv.neg ℤ) C
  rw [show (fun k : ℤ =>
        (∫ y in (0 : ℝ)..1, heatKernel t (-x.1 - y + 2 * (k : ℝ)) * f y)
          + (∫ y in (0 : ℝ)..1, heatKernel t (-x.1 + y + 2 * (k : ℝ)) * f y))
      = fun k => A k + B k by rfl,
    Summable.tsum_add hA hB, hAt, hBt, add_comm]

/-- The folded real-line heat integral equals the sum of the two full-kernel
image-branch lattice sums, assuming the folded branch sums are summable. -/
theorem foldedHeatIntegral_eq_fullKernel_branch_tsums
    (t : ℝ) (x : intervalDomainPoint) (f : ℝ → ℝ)
    (hG : Integrable
      (fun z : ℝ => heatKernel t z * f (addCircleTwoFoldTranslatePoint x z).1))
    (hA : Summable (fun k : ℤ =>
      ∫ y in (0 : ℝ)..1, heatKernel t (-x.1 - y + 2 * (k : ℝ)) * f y))
    (hB : Summable (fun k : ℤ =>
      ∫ y in (0 : ℝ)..1, heatKernel t (-x.1 + y + 2 * (k : ℝ)) * f y)) :
    foldedHeatIntegral t x f =
      (∑' k : ℤ,
        ∫ y in (0 : ℝ)..1,
          heatKernel t (x.1 - y + 2 * (k : ℝ)) * f y)
      +
      (∑' k : ℤ,
        ∫ y in (0 : ℝ)..1,
          heatKernel t (x.1 + y + 2 * (k : ℝ)) * f y) := by
  unfold foldedHeatIntegral
  have htiling := ShenWork.integral_eq_tsum_integral_Ioc_offset
    (-x.1 - 1) hG
  rw [htiling]
  have hcell :
      (fun k : ℤ =>
        ∫ z in Set.Ioc ((-x.1 - 1) + 2 * (k : ℝ))
            ((-x.1 - 1) + 2 * (k : ℝ) + 2),
          heatKernel t z * f (addCircleTwoFoldTranslatePoint x z).1)
        =
      (fun k : ℤ =>
        (∫ y in (0 : ℝ)..1,
          heatKernel t (-x.1 - y + 2 * (k : ℝ)) * f y)
        +
        (∫ y in (0 : ℝ)..1,
          heatKernel t (-x.1 + y + 2 * (k : ℝ)) * f y)) := by
    funext k
    convert foldedHeat_cell_integral_eq_two_branches t x f k hG using 1
    ring_nf
  rw [hcell]
  exact foldedHeat_branch_tsum_reindex t x f hA hB

/-- Bounded-measurable version of
`foldedHeatIntegral_eq_fullKernel_branch_tsums`. -/
theorem foldedHeatIntegral_eq_fullKernel_branch_tsums_of_bounded
    {t : ℝ} (ht : 0 < t) (x : intervalDomainPoint) {f : ℝ → ℝ} {M : ℝ}
    (hf_meas : Measurable f) (hf_bound : ∀ y, |f y| ≤ M)
    (hA : Summable (fun k : ℤ =>
      ∫ y in (0 : ℝ)..1, heatKernel t (-x.1 - y + 2 * (k : ℝ)) * f y))
    (hB : Summable (fun k : ℤ =>
      ∫ y in (0 : ℝ)..1, heatKernel t (-x.1 + y + 2 * (k : ℝ)) * f y)) :
    foldedHeatIntegral t x f =
      (∑' k : ℤ,
        ∫ y in (0 : ℝ)..1,
          heatKernel t (x.1 - y + 2 * (k : ℝ)) * f y)
      +
      (∑' k : ℤ,
        ∫ y in (0 : ℝ)..1,
          heatKernel t (x.1 + y + 2 * (k : ℝ)) * f y) :=
  foldedHeatIntegral_eq_fullKernel_branch_tsums t x f
    (foldedHeat_integrable_of_bounded ht x hf_meas hf_bound) hA hB

/-- Image-branch `tsum`/interval-integral interchange for the full Neumann
kernel. This is the remaining bridge between the method-of-images branch sums
and `intervalFullSemigroupOperator`. -/
def FullKernelImageBranchInterchange
    (t : ℝ) (x : intervalDomainPoint) (f : ℝ → ℝ) : Prop :=
  ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t f x.1 =
    (∑' k : ℤ,
      ∫ y in (0 : ℝ)..1,
        heatKernel t (x.1 - y + 2 * (k : ℝ)) * f y)
    +
    (∑' k : ℤ,
      ∫ y in (0 : ℝ)..1,
        heatKernel t (x.1 + y + 2 * (k : ℝ)) * f y)

/-- Folded heat equals the existing full-kernel Neumann semigroup once the
image-branch interchange is supplied. -/
theorem foldedHeatIntegral_eq_intervalFullSemigroupOperator_of_branch_interchange
    (t : ℝ) (x : intervalDomainPoint) (f : ℝ → ℝ)
    (hG : Integrable
      (fun z : ℝ => heatKernel t z * f (addCircleTwoFoldTranslatePoint x z).1))
    (hA : Summable (fun k : ℤ =>
      ∫ y in (0 : ℝ)..1, heatKernel t (-x.1 - y + 2 * (k : ℝ)) * f y))
    (hB : Summable (fun k : ℤ =>
      ∫ y in (0 : ℝ)..1, heatKernel t (-x.1 + y + 2 * (k : ℝ)) * f y))
    (hI : FullKernelImageBranchInterchange t x f) :
    foldedHeatIntegral t x f =
      ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t f x.1 := by
  exact (foldedHeatIntegral_eq_fullKernel_branch_tsums t x f hG hA hB).trans hI.symm

end

end ShenWork.Paper2
