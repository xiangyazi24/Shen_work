/-
  ShenWork/Paper2/IntervalInitialHolderFoldedKernel.lean

  First real-space folded-kernel atoms for producing the common folded-noise
  interface used by `IntervalInitialHolder`.
-/
import ShenWork.Paper2.IntervalInitialHolder
import ShenWork.PDE.IntervalFullKernelMass

open MeasureTheory
open scoped Real Topology ENNReal NNReal

namespace ShenWork.Paper2

noncomputable section

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
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

/-- The positive-time heat kernel as an `NNReal` density. -/
noncomputable def heatKernelNN (t : ℝ) (ht : 0 < t) (z : ℝ) : NNReal :=
  ⟨heatKernel t z, heatKernel_nonneg ht z⟩

/-- The full-line Gaussian noise law at positive time. -/
noncomputable def heatKernelNoiseMeasure (t : ℝ) (ht : 0 < t) : Measure ℝ :=
  volume.withDensity fun z => (heatKernelNN t ht z : ENNReal)

theorem heatKernelNN_measurable {t : ℝ} (ht : 0 < t) :
    Measurable (heatKernelNN t ht) := by
  exact Measurable.subtype_mk (by unfold heatKernel; fun_prop)

/-- The heat-kernel density has total mass one, hence defines a probability
measure. -/
theorem heatKernelNoiseMeasure_isProbability {t : ℝ} (ht : 0 < t) :
    IsProbabilityMeasure (heatKernelNoiseMeasure t ht) := by
  rw [isProbabilityMeasure_iff]
  have hint : Integrable (fun z : ℝ => (heatKernelNN t ht z : ℝ)) volume := by
    simpa [heatKernelNN] using heatKernel_integrable ht
  calc
    (heatKernelNoiseMeasure t ht) Set.univ
        = ∫⁻ z in Set.univ, (heatKernelNN t ht z : ENNReal) ∂volume := by
          dsimp [heatKernelNoiseMeasure]
          rw [withDensity_apply _ MeasurableSet.univ]
    _ = ∫⁻ z : ℝ, (heatKernelNN t ht z : ENNReal) ∂volume := by
          rw [Measure.restrict_univ]
    _ = ENNReal.ofReal (∫ z : ℝ, (heatKernelNN t ht z : ℝ) ∂volume) := by
          exact lintegral_coe_eq_integral (heatKernelNN t ht) hint
    _ = ENNReal.ofReal (∫ z : ℝ, heatKernel t z ∂volume) := by
          simp [heatKernelNN]
    _ = 1 := by
          rw [heatKernel_integral_eq_one ht, ENNReal.ofReal_one]

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

/-- Bounded measurable folded data are integrable under the heat-kernel noise
law. -/
theorem heatKernelNoiseMeasure_fold_integrable_of_bounded
    {t : ℝ} (ht : 0 < t) (x : intervalDomainPoint)
    {f : ℝ → ℝ} {M : ℝ}
    (hf_meas : Measurable f) (hf_bound : ∀ y, |f y| ≤ M) :
    Integrable (fun z : ℝ => f (addCircleTwoFoldTranslatePoint x z).1)
      (heatKernelNoiseMeasure t ht) := by
  have hweighted :
      Integrable (fun z : ℝ =>
        heatKernelNN t ht z • f (addCircleTwoFoldTranslatePoint x z).1) volume := by
    change Integrable (fun z : ℝ =>
      (heatKernelNN t ht z : ℝ) * f (addCircleTwoFoldTranslatePoint x z).1) volume
    simpa [heatKernelNN] using
      (foldedHeat_integrable_of_bounded ht x hf_meas hf_bound)
  exact (integrable_withDensity_iff_integrable_smul (μ := volume)
    (heatKernelNN_measurable ht)).2 hweighted

/-- Integrating a folded translate against the heat-kernel noise law is exactly
the folded real-line heat integral. -/
theorem heatKernelNoiseMeasure_integral_eq_foldedHeatIntegral
    {t : ℝ} (ht : 0 < t) (x : intervalDomainPoint) (f : ℝ → ℝ) :
    (∫ z : ℝ, f (addCircleTwoFoldTranslatePoint x z).1
        ∂(heatKernelNoiseMeasure t ht)) =
      foldedHeatIntegral t x f := by
  unfold foldedHeatIntegral heatKernelNoiseMeasure
  calc
    (∫ z : ℝ, f (addCircleTwoFoldTranslatePoint x z).1
        ∂(volume.withDensity fun z => (heatKernelNN t ht z : ENNReal)))
        =
      ∫ z : ℝ, heatKernelNN t ht z •
        f (addCircleTwoFoldTranslatePoint x z).1 ∂volume := by
          simpa using integral_withDensity_eq_integral_smul (μ := volume)
            (heatKernelNN_measurable ht)
            (fun z : ℝ => f (addCircleTwoFoldTranslatePoint x z).1)
    _ = ∫ z : ℝ, heatKernel t z *
          f (addCircleTwoFoldTranslatePoint x z).1 ∂volume := by
        change (∫ z : ℝ, (heatKernelNN t ht z : ℝ) *
            f (addCircleTwoFoldTranslatePoint x z).1 ∂volume)
          =
          ∫ z : ℝ, heatKernel t z *
            f (addCircleTwoFoldTranslatePoint x z).1 ∂volume
        simp [heatKernelNN]

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

/-- A bounded measurable factor is harmless against one translated reflected
heat branch on `[0,1]`. -/
theorem heatKernel_sub_branch_abs_integral_mul_bounded_le
    {t : ℝ} (ht : 0 < t) (a : ℝ) {f : ℝ → ℝ} {M : ℝ}
    (hf_meas : Measurable f) (hf_bound : ∀ y, |f y| ≤ M) :
    |∫ y in (0 : ℝ)..1, heatKernel t (a - y) * f y|
      ≤ M * ∫ y in (0 : ℝ)..1, heatKernel t (a - y) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hprod_int : IntervalIntegrable
      (fun y : ℝ => heatKernel t (a - y) * f y) volume 0 1 := by
    exact ((heatKernel_translated_integrable ht a).mul_bdd
      hf_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        simpa [Real.norm_eq_abs] using hf_bound y)).intervalIntegrable
  have hkernel_cont : Continuous (fun y : ℝ => heatKernel t (a - y)) := by
    unfold heatKernel
    fun_prop
  have hkernel_int : IntervalIntegrable
      (fun y : ℝ => heatKernel t (a - y)) volume 0 1 :=
    hkernel_cont.intervalIntegrable 0 1
  have hbound_int : IntervalIntegrable
      (fun y : ℝ => M * heatKernel t (a - y)) volume 0 1 :=
    hkernel_int.const_mul M
  calc
    |∫ y in (0 : ℝ)..1, heatKernel t (a - y) * f y|
        ≤ ∫ y in (0 : ℝ)..1, |heatKernel t (a - y) * f y| :=
          intervalIntegral.abs_integral_le_integral_abs h01
    _ ≤ ∫ y in (0 : ℝ)..1, M * heatKernel t (a - y) := by
        refine intervalIntegral.integral_mono_on h01 hprod_int.abs hbound_int ?_
        intro y _hy
        rw [abs_mul, abs_of_nonneg (heatKernel_nonneg ht (a - y))]
        calc
          heatKernel t (a - y) * |f y| ≤ heatKernel t (a - y) * M :=
            mul_le_mul_of_nonneg_left (hf_bound y) (heatKernel_nonneg ht (a - y))
          _ = M * heatKernel t (a - y) := by ring
    _ = M * ∫ y in (0 : ℝ)..1, heatKernel t (a - y) := by
        rw [intervalIntegral.integral_const_mul]

/-- A bounded measurable factor is harmless against one translated direct
heat branch on `[0,1]`. -/
theorem heatKernel_add_branch_abs_integral_mul_bounded_le
    {t : ℝ} (ht : 0 < t) (a : ℝ) {f : ℝ → ℝ} {M : ℝ}
    (hf_meas : Measurable f) (hf_bound : ∀ y, |f y| ≤ M) :
    |∫ y in (0 : ℝ)..1, heatKernel t (a + y) * f y|
      ≤ M * ∫ y in (0 : ℝ)..1, heatKernel t (a + y) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hprod_int : IntervalIntegrable
      (fun y : ℝ => heatKernel t (a + y) * f y) volume 0 1 := by
    exact (((heatKernel_integrable ht).comp_add_left a).mul_bdd
      hf_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        simpa [Real.norm_eq_abs] using hf_bound y)).intervalIntegrable
  have hkernel_cont : Continuous (fun y : ℝ => heatKernel t (a + y)) := by
    unfold heatKernel
    fun_prop
  have hkernel_int : IntervalIntegrable
      (fun y : ℝ => heatKernel t (a + y)) volume 0 1 :=
    hkernel_cont.intervalIntegrable 0 1
  have hbound_int : IntervalIntegrable
      (fun y : ℝ => M * heatKernel t (a + y)) volume 0 1 :=
    hkernel_int.const_mul M
  calc
    |∫ y in (0 : ℝ)..1, heatKernel t (a + y) * f y|
        ≤ ∫ y in (0 : ℝ)..1, |heatKernel t (a + y) * f y| :=
          intervalIntegral.abs_integral_le_integral_abs h01
    _ ≤ ∫ y in (0 : ℝ)..1, M * heatKernel t (a + y) := by
        refine intervalIntegral.integral_mono_on h01 hprod_int.abs hbound_int ?_
        intro y _hy
        rw [abs_mul, abs_of_nonneg (heatKernel_nonneg ht (a + y))]
        calc
          heatKernel t (a + y) * |f y| ≤ heatKernel t (a + y) * M :=
            mul_le_mul_of_nonneg_left (hf_bound y) (heatKernel_nonneg ht (a + y))
          _ = M * heatKernel t (a + y) := by ring
    _ = M * ∫ y in (0 : ℝ)..1, heatKernel t (a + y) := by
        rw [intervalIntegral.integral_const_mul]

/-- Bounded data make the two folded branch integral sequences summable. -/
theorem foldedHeat_branch_summable_of_bounded
    {t : ℝ} (ht : 0 < t) (x : intervalDomainPoint) {f : ℝ → ℝ} {M : ℝ}
    (_hM : 0 ≤ M) (hf_meas : Measurable f) (hf_bound : ∀ y, |f y| ≤ M) :
    Summable (fun k : ℤ =>
      ∫ y in (0 : ℝ)..1, heatKernel t (-x.1 - y + 2 * (k : ℝ)) * f y) ∧
    Summable (fun k : ℤ =>
      ∫ y in (0 : ℝ)..1, heatKernel t (-x.1 + y + 2 * (k : ℝ)) * f y) := by
  set A : ℤ → ℝ := fun k =>
    ∫ y in (0 : ℝ)..1, heatKernel t (-x.1 - y + 2 * (k : ℝ))
  set B : ℤ → ℝ := fun k =>
    ∫ y in (0 : ℝ)..1, heatKernel t (-x.1 + y + 2 * (k : ℝ))
  have hA_nonneg : ∀ k : ℤ, 0 ≤ A k := by
    intro k
    exact intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1)
      (fun y _hy => heatKernel_nonneg ht (-x.1 - y + 2 * (k : ℝ)))
  have hB_nonneg : ∀ k : ℤ, 0 ≤ B k := by
    intro k
    exact intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1)
      (fun y _hy => heatKernel_nonneg ht (-x.1 + y + 2 * (k : ℝ)))
  have hAB : Summable (fun k : ℤ => A k + B k) := by
    simpa [A, B] using
      (ShenWork.IntervalNeumannFullKernel.summable_cell_heat_interval_integral ht (-x.1))
  have hA_sum : Summable A :=
    Summable.of_nonneg_of_le hA_nonneg
      (fun k => le_add_of_nonneg_right (hB_nonneg k)) hAB
  have hB_sum : Summable B :=
    Summable.of_nonneg_of_le hB_nonneg
      (fun k => le_add_of_nonneg_left (hA_nonneg k)) hAB
  constructor
  · refine Summable.of_norm_bounded (g := fun k : ℤ => M * A k)
      (hA_sum.mul_left M) ?_
    intro k
    rw [Real.norm_eq_abs]
    have hle := heatKernel_sub_branch_abs_integral_mul_bounded_le
      ht (-x.1 + 2 * (k : ℝ)) hf_meas hf_bound
    simpa [A, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hle
  · refine Summable.of_norm_bounded (g := fun k : ℤ => M * B k)
      (hB_sum.mul_left M) ?_
    intro k
    rw [Real.norm_eq_abs]
    have hle := heatKernel_add_branch_abs_integral_mul_bounded_le
      ht (-x.1 + 2 * (k : ℝ)) hf_meas hf_bound
    simpa [B, add_comm, add_left_comm, add_assoc] using hle

/-- Bounded data make the two full image-branch integral sequences summable. -/
theorem fullKernel_image_branch_summable_of_bounded
    {t : ℝ} (ht : 0 < t) (x : ℝ) {f : ℝ → ℝ} {M : ℝ}
    (_hM : 0 ≤ M) (hf_meas : Measurable f) (hf_bound : ∀ y, |f y| ≤ M) :
    Summable (fun k : ℤ =>
      ∫ y in (0 : ℝ)..1, heatKernel t (x - y + 2 * (k : ℝ)) * f y) ∧
    Summable (fun k : ℤ =>
      ∫ y in (0 : ℝ)..1, heatKernel t (x + y + 2 * (k : ℝ)) * f y) := by
  set A : ℤ → ℝ := fun k =>
    ∫ y in (0 : ℝ)..1, heatKernel t (x - y + 2 * (k : ℝ))
  set B : ℤ → ℝ := fun k =>
    ∫ y in (0 : ℝ)..1, heatKernel t (x + y + 2 * (k : ℝ))
  have hA_nonneg : ∀ k : ℤ, 0 ≤ A k := by
    intro k
    exact intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1)
      (fun y _hy => heatKernel_nonneg ht (x - y + 2 * (k : ℝ)))
  have hB_nonneg : ∀ k : ℤ, 0 ≤ B k := by
    intro k
    exact intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1)
      (fun y _hy => heatKernel_nonneg ht (x + y + 2 * (k : ℝ)))
  have hAB : Summable (fun k : ℤ => A k + B k) := by
    simpa [A, B] using
      (ShenWork.IntervalNeumannFullKernel.summable_cell_heat_interval_integral ht x)
  have hA_sum : Summable A :=
    Summable.of_nonneg_of_le hA_nonneg
      (fun k => le_add_of_nonneg_right (hB_nonneg k)) hAB
  have hB_sum : Summable B :=
    Summable.of_nonneg_of_le hB_nonneg
      (fun k => le_add_of_nonneg_left (hA_nonneg k)) hAB
  constructor
  · refine Summable.of_norm_bounded (g := fun k : ℤ => M * A k)
      (hA_sum.mul_left M) ?_
    intro k
    rw [Real.norm_eq_abs]
    have hle := heatKernel_sub_branch_abs_integral_mul_bounded_le
      ht (x + 2 * (k : ℝ)) hf_meas hf_bound
    simpa [A, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hle
  · refine Summable.of_norm_bounded (g := fun k : ℤ => M * B k)
      (hB_sum.mul_left M) ?_
    intro k
    rw [Real.norm_eq_abs]
    have hle := heatKernel_add_branch_abs_integral_mul_bounded_le
      ht (x + 2 * (k : ℝ)) hf_meas hf_bound
    simpa [B, add_comm, add_left_comm, add_assoc] using hle

/-- Norm-integral domination for one full-kernel image cell after multiplication
by a bounded datum. -/
theorem fullKernel_image_integral_norm_hk_le_mass_mul
    {t : ℝ} (ht : 0 < t) (x : ℝ) {f : ℝ → ℝ} {M : ℝ}
    (hf_bound : ∀ y, |f y| ≤ M) (k : ℤ) :
    (∫ y,
        ‖((heatKernel t (x - y + 2 * (k : ℝ))
            + heatKernel t (x + y + 2 * (k : ℝ))) * f y)‖
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
      ≤ M *
        ((∫ y in (0 : ℝ)..1, heatKernel t (x - y + 2 * (k : ℝ)))
          + (∫ y in (0 : ℝ)..1, heatKernel t (x + y + 2 * (k : ℝ)))) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  set A : ℝ → ℝ := fun y => heatKernel t (x - y + 2 * (k : ℝ))
  set B : ℝ → ℝ := fun y => heatKernel t (x + y + 2 * (k : ℝ))
  have hAii : IntervalIntegrable A volume 0 1 := by
    have hAcont : Continuous A := by
      unfold A heatKernel
      fun_prop
    exact hAcont.intervalIntegrable 0 1
  have hBii : IntervalIntegrable B volume 0 1 := by
    have hBcont : Continuous B := by
      unfold B heatKernel
      fun_prop
    exact hBcont.intervalIntegrable 0 1
  have hupper_int : Integrable
      (fun y : ℝ => M * (A y + B y)) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le h01).mp (hAii.add hBii)).const_mul M
  calc
    (∫ y, ‖((A y + B y) * f y)‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
        ≤ ∫ y, M * (A y + B y) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun y => norm_nonneg _)
            hupper_int
            (Filter.Eventually.of_forall fun y => ?_)
          have hK_nonneg : 0 ≤ A y + B y := by
            exact add_nonneg (by simpa [A] using heatKernel_nonneg ht (x - y + 2 * (k : ℝ)))
              (by simpa [B] using heatKernel_nonneg ht (x + y + 2 * (k : ℝ)))
          change ‖(A y + B y) * f y‖ ≤ M * (A y + B y)
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK_nonneg]
          calc
            (A y + B y) * |f y| ≤ (A y + B y) * M :=
              mul_le_mul_of_nonneg_left (hf_bound y) hK_nonneg
            _ = M * (A y + B y) := by ring
    _ = M * ∫ y, A y + B y ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
        rw [MeasureTheory.integral_const_mul]
    _ = M *
        ((∫ y in (0 : ℝ)..1, heatKernel t (x - y + 2 * (k : ℝ)))
          + (∫ y in (0 : ℝ)..1, heatKernel t (x + y + 2 * (k : ℝ)))) := by
        congr 1
        rw [← intervalIntegral.integral_of_le h01]
        simpa [A, B] using intervalIntegral.integral_add hAii hBii

/-- Interchange the full image-kernel branch `tsum` with the `[0,1]` integral
after multiplication by a bounded measurable datum. -/
theorem fullKernel_image_integral_tsum_mul_of_bounded
    {t : ℝ} (ht : 0 < t) (x : ℝ) {f : ℝ → ℝ} {M : ℝ}
    (_hM : 0 ≤ M) (hf_meas : Measurable f) (hf_bound : ∀ y, |f y| ≤ M) :
    (∫ y in (0 : ℝ)..1,
        ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel t x y * f y)
      =
    ∑' k : ℤ,
      ∫ y in (0 : ℝ)..1,
        (heatKernel t (x - y + 2 * (k : ℝ))
          + heatKernel t (x + y + 2 * (k : ℝ))) * f y := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  let μ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  set hk : ℤ → ℝ → ℝ := fun k y =>
    (heatKernel t (x - y + 2 * (k : ℝ))
      + heatKernel t (x + y + 2 * (k : ℝ))) * f y with hk_def
  have hμint : ∀ k : ℤ, Integrable (hk k) μ := by
    intro k
    have hAprod : IntervalIntegrable
        (fun y : ℝ => heatKernel t (x - y + 2 * (k : ℝ)) * f y) volume 0 1 := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        ((heatKernel_translated_integrable ht (x + 2 * (k : ℝ))).mul_bdd
          hf_meas.aestronglyMeasurable
          (Filter.Eventually.of_forall fun y => by
            simpa [Real.norm_eq_abs] using hf_bound y)).intervalIntegrable
    have hBprod : IntervalIntegrable
        (fun y : ℝ => heatKernel t (x + y + 2 * (k : ℝ)) * f y) volume 0 1 := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (((heatKernel_integrable ht).comp_add_left (x + 2 * (k : ℝ))).mul_bdd
          hf_meas.aestronglyMeasurable
          (Filter.Eventually.of_forall fun y => by
            simpa [Real.norm_eq_abs] using hf_bound y)).intervalIntegrable
    have hsum : IntervalIntegrable (hk k) volume 0 1 := by
      convert hAprod.add hBprod using 1
      funext y
      rw [hk_def]
      ring
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h01).mp hsum
  set mass : ℤ → ℝ := fun k =>
    (∫ y in (0 : ℝ)..1, heatKernel t (x - y + 2 * (k : ℝ)))
      + (∫ y in (0 : ℝ)..1, heatKernel t (x + y + 2 * (k : ℝ)))
  have hmass_sum : Summable mass := by
    simpa [mass] using
      (ShenWork.IntervalNeumannFullKernel.summable_cell_heat_interval_integral ht x)
  have hμsum : Summable (fun k : ℤ => ∫ y, ‖hk k y‖ ∂μ) := by
    refine Summable.of_nonneg_of_le
      (fun k => MeasureTheory.integral_nonneg fun y => norm_nonneg _)
      ?_ (hmass_sum.mul_left M)
    intro k
    simpa [μ, hk_def, mass] using
      (fullKernel_image_integral_norm_hk_le_mass_mul (t := t) ht (x := x)
        (f := f) (M := M) hf_bound k)
  have key := MeasureTheory.integral_tsum_of_summable_integral_norm
    (μ := μ) (F := hk) hμint hμsum
  calc
    (∫ y in (0 : ℝ)..1,
        ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel t x y * f y)
        = ∫ y, (∑' k : ℤ, hk k y) ∂μ := by
          rw [intervalIntegral.integral_of_le h01]
          refine MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall fun y => ?_)
          unfold ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel
          rw [hk_def]
          change ((∑' (k : ℤ),
              (heatKernel t (x - y + 2 * (k : ℝ))
                + heatKernel t (x + y + 2 * (k : ℝ)))) * f y)
            =
              ∑' (k : ℤ),
                ((heatKernel t (x - y + 2 * (k : ℝ))
                  + heatKernel t (x + y + 2 * (k : ℝ))) * f y)
          rw [tsum_mul_right]
    _ = ∑' k : ℤ, ∫ y, hk k y ∂μ := key.symm
    _ = ∑' k : ℤ,
        ∫ y in (0 : ℝ)..1,
          (heatKernel t (x - y + 2 * (k : ℝ))
            + heatKernel t (x + y + 2 * (k : ℝ))) * f y := by
          refine tsum_congr (fun k => ?_)
          rw [← intervalIntegral.integral_of_le h01]

/-- Bounded measurable data allow image-branch `tsum`/interval-integral
interchange for the full Neumann kernel. -/
theorem FullKernelImageBranchInterchange_of_bounded
    {t : ℝ} (ht : 0 < t) (x : intervalDomainPoint) {f : ℝ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hf_meas : Measurable f) (hf_bound : ∀ y, |f y| ≤ M) :
    FullKernelImageBranchInterchange t x f := by
  unfold FullKernelImageBranchInterchange
  rw [ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator]
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hconv :
      (∫ y,
          ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel t x.1 y * f y
            ∂ShenWork.IntervalDomain.intervalMeasure 1)
        =
        ∫ y in (0 : ℝ)..1,
          ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel t x.1 y * f y := by
    rw [intervalIntegral.integral_of_le h01]
    simp only [ShenWork.IntervalDomain.intervalMeasure, ShenWork.IntervalDomain.intervalSet]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hconv]
  rw [fullKernel_image_integral_tsum_mul_of_bounded
    (t := t) ht (x := x.1) (f := f) (M := M) hM hf_meas hf_bound]
  have hbranches := fullKernel_image_branch_summable_of_bounded
    (t := t) ht (x := x.1) (f := f) (M := M) hM hf_meas hf_bound
  calc
    (∑' k : ℤ,
      ∫ y in (0 : ℝ)..1,
        (heatKernel t (x.1 - y + 2 * (k : ℝ))
          + heatKernel t (x.1 + y + 2 * (k : ℝ))) * f y)
        =
      ∑' k : ℤ,
        ((∫ y in (0 : ℝ)..1,
            heatKernel t (x.1 - y + 2 * (k : ℝ)) * f y)
          + (∫ y in (0 : ℝ)..1,
            heatKernel t (x.1 + y + 2 * (k : ℝ)) * f y)) := by
        refine tsum_congr (fun k => ?_)
        have hAprod : IntervalIntegrable
            (fun y : ℝ => heatKernel t (x.1 - y + 2 * (k : ℝ)) * f y)
            volume 0 1 := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            ((heatKernel_translated_integrable ht (x.1 + 2 * (k : ℝ))).mul_bdd
              hf_meas.aestronglyMeasurable
              (Filter.Eventually.of_forall fun y => by
                simpa [Real.norm_eq_abs] using hf_bound y)).intervalIntegrable
        have hBprod : IntervalIntegrable
            (fun y : ℝ => heatKernel t (x.1 + y + 2 * (k : ℝ)) * f y)
            volume 0 1 := by
          simpa [add_comm, add_left_comm, add_assoc] using
            (((heatKernel_integrable ht).comp_add_left (x.1 + 2 * (k : ℝ))).mul_bdd
              hf_meas.aestronglyMeasurable
              (Filter.Eventually.of_forall fun y => by
                simpa [Real.norm_eq_abs] using hf_bound y)).intervalIntegrable
        rw [show (fun y : ℝ =>
            (heatKernel t (x.1 - y + 2 * (k : ℝ))
              + heatKernel t (x.1 + y + 2 * (k : ℝ))) * f y)
            =
            (fun y : ℝ =>
              heatKernel t (x.1 - y + 2 * (k : ℝ)) * f y
                + heatKernel t (x.1 + y + 2 * (k : ℝ)) * f y) from by
              funext y
              ring]
        exact intervalIntegral.integral_add hAprod hBprod
    _ =
      (∑' k : ℤ,
        ∫ y in (0 : ℝ)..1,
          heatKernel t (x.1 - y + 2 * (k : ℝ)) * f y)
      +
      (∑' k : ℤ,
        ∫ y in (0 : ℝ)..1,
          heatKernel t (x.1 + y + 2 * (k : ℝ)) * f y) :=
        Summable.tsum_add hbranches.1 hbranches.2

/-- Final bounded-data bridge from the folded real-line heat representation to
the existing full-kernel Neumann semigroup operator. -/
theorem foldedHeatIntegral_eq_intervalFullSemigroupOperator_of_bounded
    {t : ℝ} (ht : 0 < t) (x : intervalDomainPoint) {f : ℝ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hf_meas : Measurable f) (hf_bound : ∀ y, |f y| ≤ M) :
    foldedHeatIntegral t x f =
      ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t f x.1 := by
  obtain ⟨hA, hB⟩ :=
    foldedHeat_branch_summable_of_bounded ht x hM hf_meas hf_bound
  exact foldedHeatIntegral_eq_intervalFullSemigroupOperator_of_branch_interchange
    t x f
    (foldedHeat_integrable_of_bounded ht x hf_meas hf_bound)
    hA hB
    (FullKernelImageBranchInterchange_of_bounded ht x hM hf_meas hf_bound)

/-- Bounded measurable data provide the common folded-noise representation used by
the initial-leg Holder interface.  The shared noise law is the full-line
Gaussian density, then both interval points are obtained by period-2 folding of
the translated noise. -/
noncomputable def NeumannHeatCommonFoldNoiseFor_of_bounded
    {t : ℝ} (ht : 0 < t) (x y : intervalDomainPoint)
    {f : ℝ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hf_meas : Measurable f) (hf_bound : ∀ y, |f y| ≤ M) :
    NeumannHeatCommonFoldNoiseFor t x y f := by
  refine
    { ν := heatKernelNoiseMeasure t ht
      prob := heatKernelNoiseMeasure_isProbability ht
      fx_integrable := ?_
      fy_integrable := ?_
      sx_eq := ?_
      sy_eq := ?_ }
  · change Integrable (fun z : ℝ => f (addCircleTwoFoldTranslatePoint x z).1)
      (heatKernelNoiseMeasure t ht)
    exact heatKernelNoiseMeasure_fold_integrable_of_bounded ht x hf_meas hf_bound
  · change Integrable (fun z : ℝ => f (addCircleTwoFoldTranslatePoint y z).1)
      (heatKernelNoiseMeasure t ht)
    exact heatKernelNoiseMeasure_fold_integrable_of_bounded ht y hf_meas hf_bound
  · calc
      ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t f x.1 =
          foldedHeatIntegral t x f := by
        exact (foldedHeatIntegral_eq_intervalFullSemigroupOperator_of_bounded
          ht x hM hf_meas hf_bound).symm
      _ =
          ∫ z : ℝ, f (addCircleTwoFoldTranslatePoint x z).1
            ∂(heatKernelNoiseMeasure t ht) := by
        exact (heatKernelNoiseMeasure_integral_eq_foldedHeatIntegral ht x f).symm
  · calc
      ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t f y.1 =
          foldedHeatIntegral t y f := by
        exact (foldedHeatIntegral_eq_intervalFullSemigroupOperator_of_bounded
          ht y hM hf_meas hf_bound).symm
      _ =
          ∫ z : ℝ, f (addCircleTwoFoldTranslatePoint y z).1
            ∂(heatKernelNoiseMeasure t ht) := by
        exact (heatKernelNoiseMeasure_integral_eq_foldedHeatIntegral ht y f).symm

/-- A pointwise bound on interval-domain data extends to the zero extension on
the real line. -/
theorem intervalDomainLift_abs_bound_of_interval_bound
    {u₀ : intervalDomainPoint → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hu₀_bound : ∀ x : intervalDomainPoint, |u₀ x| ≤ M) :
    ∀ y : ℝ, |intervalDomainLift u₀ y| ≤ M := by
  intro y
  unfold intervalDomainLift
  split_ifs with hy
  · exact hu₀_bound ⟨y, hy⟩
  · simpa using hM

/-- Bounded measurable initial data can use the heat-kernel folded-noise
producer directly, so the initial-leg Holder theorem no longer needs an
external common-noise `hplan`. -/
theorem InitialLegUniformHolderAtZero_of_bounded_initialDatumHolder
    {u₀ : intervalDomainPoint → ℝ} {T θ H₀ M : ℝ}
    (hθ0 : 0 < θ) (hH₀ : 0 ≤ H₀)
    (hM : 0 ≤ M) (hholder : InitialDatumHolder u₀ θ H₀)
    (hu₀_meas : Measurable (intervalDomainLift u₀))
    (hu₀_bound : ∀ x : intervalDomainPoint, |u₀ x| ≤ M) :
    InitialLegUniformHolderAtZero u₀ T θ H₀ := by
  have hlift_bound : ∀ y : ℝ, |intervalDomainLift u₀ y| ≤ M :=
    intervalDomainLift_abs_bound_of_interval_bound hM hu₀_bound
  exact InitialLegUniformHolderAtZero_of_common_fold_noise
    hθ0 hH₀ hholder
    (fun t ht _htT x y =>
      NeumannHeatCommonFoldNoiseFor_of_bounded
        ht x y hM hu₀_meas hlift_bound)

/-- Small-time mild Holder wrapper for bounded measurable initial data, using
the concrete heat-kernel folded-noise law. -/
theorem mild_orderBox_smallTime_holder_of_bounded_initialDatumHolder
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ShenWork.IntervalMildPicard.GradientMildSolutionData p u₀)
    {θ H₀ M : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hH₀ : 0 ≤ H₀)
    (hM : 0 ≤ M) (hholder : InitialDatumHolder u₀ θ H₀)
    (hu₀_meas : Measurable (intervalDomainLift u₀))
    (hu₀_bound : ∀ x : intervalDomainPoint, |u₀ x| ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t, 0 < t → t ≤ D.T → ∀ x y : intervalDomainPoint,
      |D.u t x - D.u t y| ≤ K * |x.1 - y.1| ^ θ := by
  exact mild_orderBox_smallTime_holder_of_initialLeg_holder D hθ0 hθ1 hH₀
    (InitialLegUniformHolderAtZero_of_bounded_initialDatumHolder
      hθ0 hH₀ hM hholder hu₀_meas hu₀_bound)

end

end ShenWork.Paper2
