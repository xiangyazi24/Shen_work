/-
  Variational negative-part energy estimates for the faithful truncated limit.

  This module deliberately works with right increments of the mild formula.
  In particular, it does not reconstruct a pointwise time derivative.
-/

import ShenWork.Paper2.IntervalBFormCron2RegularNegativePartEnergyA2
import ShenWork.Paper2.IntervalBFormCron2BNDuality
import ShenWork.PDE.IntervalFullKernelSupBound
import ShenWork.PDE.IntervalFullKernelSourceIBP
import ShenWork.PDE.IntervalConjugateKernelMassDefect
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

open Filter Topology Set MeasureTheory
open scoped BigOperators Topology

noncomputable section

namespace ShenWork.Paper2.IntervalNegativePartWeakEnergy

open ShenWork.IntervalDomain (intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
  (intervalNeumannFullKernel intervalNeumannConjugateKernel
   intervalFullSemigroupOperator)
open ShenWork.Paper2.BFormPositiveDatumNegPart

private lemma one_sub_exp_neg_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ 1 - Real.exp (-x) := by
  rw [sub_nonneg, Real.exp_le_one_iff]
  linarith

private lemma one_sub_exp_neg_le_one {x : ℝ} :
    1 - Real.exp (-x) ≤ 1 := by
  linarith [Real.exp_pos (-x)]

private lemma one_sub_exp_neg_le {x : ℝ} (_hx : 0 ≤ x) :
    1 - Real.exp (-x) ≤ x := by
  linarith [Real.one_sub_le_exp_neg x]

private lemma one_sub_exp_neg_sq_le {x : ℝ} (hx : 0 ≤ x) :
    (1 - Real.exp (-x)) ^ 2 ≤ x := by
  have h0 := one_sub_exp_neg_nonneg hx
  have h1 := one_sub_exp_neg_le_one (x := x)
  have hx' := one_sub_exp_neg_le hx
  nlinarith

private lemma one_sub_exp_neg_sq_le_sq {x : ℝ} (hx : 0 ≤ x) :
    (1 - Real.exp (-x)) ^ 2 ≤ x ^ 2 := by
  have h0 := one_sub_exp_neg_nonneg hx
  have hx' := one_sub_exp_neg_le hx
  nlinarith

/-- If the normalized cosine coefficients have one weighted square moment,
then the squared heat-orbit increment is `o(h)` as `h → 0+`.  This is the
coefficient form of `‖S(h)f - f‖₂ = o(√h)` for `f ∈ H¹`. -/
theorem cosineHeatIncrement_sq_div_tendsto_zero
    (a : ℕ → ℝ)
    (ha : Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n * |a n| ^ 2)) :
    Tendsto
      (fun h : ℝ => ∑' n : ℕ,
        ((Real.exp (-h * unitIntervalCosineEigenvalue n) - 1) * a n) ^ 2 / h)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  let term : ℝ → ℕ → ℝ := fun h n =>
    ((Real.exp (-h * unitIntervalCosineEigenvalue n) - 1) * a n) ^ 2 / h
  have hterm : ∀ n : ℕ, Tendsto (fun h => term h n)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    intro n
    have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity
    have hright : Tendsto
        (fun h : ℝ => h * unitIntervalCosineEigenvalue n ^ 2 * |a n| ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have hid : Tendsto (fun h : ℝ => h)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      convert
        (hid.mul_const (unitIntervalCosineEigenvalue n ^ 2 * |a n| ^ 2))
          using 1
      · funext h
        rw [sq_abs]
        ring
      · ring
    refine squeeze_zero' ?_ ?_ hright
    · filter_upwards [self_mem_nhdsWithin] with h hh
      dsimp [term]
      exact div_nonneg (sq_nonneg _) hh.le
    · filter_upwards [self_mem_nhdsWithin] with h hh
      have hh0 : 0 ≤ h := hh.le
      have hx : 0 ≤ h * unitIntervalCosineEigenvalue n :=
        mul_nonneg hh0 hlam
      have hsquare := one_sub_exp_neg_sq_le_sq hx
      dsimp [term]
      rw [show Real.exp (-h * unitIntervalCosineEigenvalue n) - 1 =
          -(1 - Real.exp (-(h * unitIntervalCosineEigenvalue n))) by ring]
      have habs : a n ^ 2 = |a n| ^ 2 := by rw [sq_abs]
      rw [mul_pow, neg_sq, habs]
      have hhpos : 0 < h := hh
      apply (div_le_iff₀ hhpos).2
      nlinarith [mul_nonneg (sq_nonneg (h * unitIntervalCosineEigenvalue n))
        (sq_nonneg |a n|)]
  have hbound : Filter.Eventually
      (fun h => ∀ n : ℕ,
        ‖term h n‖ ≤ unitIntervalCosineEigenvalue n * |a n| ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    intro n
    have hhpos : 0 < h := hh
    have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity
    have hx : 0 ≤ h * unitIntervalCosineEigenvalue n :=
      mul_nonneg hhpos.le hlam
    have hsquare := one_sub_exp_neg_sq_le hx
    have hterm_nonneg : 0 ≤ term h n := by
      dsimp [term]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hterm_nonneg]
    dsimp [term]
    rw [show Real.exp (-h * unitIntervalCosineEigenvalue n) - 1 =
        -(1 - Real.exp (-(h * unitIntervalCosineEigenvalue n))) by ring]
    have habs : a n ^ 2 = |a n| ^ 2 := by rw [sq_abs]
    rw [mul_pow, neg_sq, habs]
    apply (div_le_iff₀ hhpos).2
    nlinarith [sq_nonneg |a n|]
  have h := tendsto_tsum_of_dominated_convergence
    (f := term) (g := fun _ : ℕ => (0 : ℝ))
    (bound := fun n : ℕ =>
      unitIntervalCosineEigenvalue n * |a n| ^ 2)
    ha hterm hbound
  simpa [term] using h

/-! ## Markov contraction of the negative-part energy -/

private theorem negativePart_sq_convexOn :
    ConvexOn ℝ (Set.univ : Set ℝ) (fun r => (negativePart r) ^ 2) := by
  have hdiff : Differentiable ℝ (fun r : ℝ => (negativePart r) ^ 2) :=
    fun r => (negativePart_sq_hasDerivAt r).differentiableAt
  have hmono : Monotone (fun r : ℝ => -2 * negativePart r) := by
    intro a b hab
    have hanti : negativePart b ≤ negativePart a := by
      unfold negativePart
      exact max_le_max (neg_le_neg hab) le_rfl
    nlinarith
  apply Monotone.convexOn_univ_of_deriv hdiff
  simpa [negativePart_sq_deriv] using hmono

private theorem negativePart_sq_continuous :
    Continuous (fun r : ℝ => (negativePart r) ^ 2) :=
  negativePart_continuous.pow 2

private theorem intervalNeumannFullKernel_joint_measurable
    {t : ℝ} (ht : 0 < t) :
    Measurable (fun p : ℝ × ℝ => intervalNeumannFullKernel t p.1 p.2) := by
  set g : ℤ → ℝ × ℝ → ℝ := fun k p =>
    heatKernel t
        (p.1 - p.2 + 2 * (k : ℝ)) +
      heatKernel t
        (p.1 + p.2 + 2 * (k : ℝ)) with hg
  have hg_meas : ∀ k, Measurable (g k) := by
    intro k
    simp only [g]
    unfold heatKernel
    fun_prop
  have hg_sum : ∀ p, Summable (fun k : ℤ => g k p) := by
    intro p
    exact
      (ShenWork.IntervalNeumannFullKernel.latticeGaussianSummable
        ht (p.1 - p.2)).add
      (ShenWork.IntervalNeumannFullKernel.latticeGaussianSummable
        ht (p.1 + p.2))
  have hmeas :=
    ShenWork.IntervalNeumannFullKernel.measurable_tsum_int_of_summable
      hg_meas hg_sum
  have hfun :
      (fun p : ℝ × ℝ => intervalNeumannFullKernel t p.1 p.2) =
        fun p => ∑' k : ℤ, g k p := by
    funext p
    rfl
  rw [hfun]
  exact hmeas

/-- Jensen's inequality for the convex map `r ↦ (r₋)²` under one
positive-time Neumann heat kernel. -/
theorem negativePart_sq_intervalFullSemigroupOperator_le
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} {M : ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    (hf_bdd : ∀ y, |f y| ≤ M) (x : ℝ) :
    (negativePart (intervalFullSemigroupOperator t f x)) ^ 2 ≤
      intervalFullSemigroupOperator t
        (fun y => (negativePart (f y)) ^ 2) x := by
  let K : ℝ → ℝ := fun y => intervalNeumannFullKernel t x y
  let Kd : ℝ → ENNReal := fun y => ENNReal.ofReal (K y)
  let μK := (intervalMeasure 1).withDensity Kd
  have hK_nn : ∀ y, 0 ≤ K y := fun y =>
    ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_nonneg ht x y
  have hK_int : Integrable K (intervalMeasure 1) := by
    simpa [K] using
      ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_integrable ht x
  have hKd_aem : AEMeasurable Kd (intervalMeasure 1) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      hK_int.aestronglyMeasurable.aemeasurable
  have hKd_ae_lt : Filter.Eventually (fun y => Kd y < ⊤)
      (ae (intervalMeasure 1)) :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hKd_toReal : ∀ y, (Kd y).toReal = K y := by
    intro y
    simp [Kd, ENNReal.toReal_ofReal (hK_nn y)]
  have hmassK : ∫ y, K y ∂(intervalMeasure 1) = 1 := by
    simpa [K] using
      ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_intervalMeasure_integral_eq_one
        ht x
  have hμK_mass : μK Set.univ = 1 := by
    rw [show μK = (intervalMeasure 1).withDensity Kd from rfl,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hK_int
        (Filter.Eventually.of_forall hK_nn)]
    simp [hmassK]
  letI : IsProbabilityMeasure μK := ⟨hμK_mass⟩
  have hM_nonneg : 0 ≤ M :=
    le_trans (abs_nonneg (f 0)) (hf_bdd 0)
  let g : ℝ → ℝ := fun r => (negativePart r) ^ 2
  have hg_meas : AEStronglyMeasurable (fun y => g (f y))
      (intervalMeasure 1) :=
    negativePart_sq_continuous.comp_aestronglyMeasurable hf_meas
  have hg_bdd : ∀ y, |g (f y)| ≤ M ^ 2 := by
    intro y
    have hn : |negativePart (f y)| ≤ M :=
      (negativePart_abs_le_abs (f y)).trans (hf_bdd y)
    have hs : (negativePart (f y)) ^ 2 ≤ M ^ 2 := by
      rw [sq_le_sq]
      simpa [abs_of_nonneg hM_nonneg] using hn
    change |(negativePart (f y)) ^ 2| ≤ M ^ 2
    rw [abs_of_nonneg (sq_nonneg _)]
    exact hs
  have hKf_int : Integrable (fun y => K y * f y) (intervalMeasure 1) := by
    have hmul : Integrable (fun y => f y * K y) (intervalMeasure 1) :=
      hK_int.bdd_mul hf_meas
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs]
          exact hf_bdd y)
    exact hmul.congr (Eventually.of_forall fun y => by ring)
  have hKg_int : Integrable (fun y => K y * g (f y))
      (intervalMeasure 1) := by
    have hmul : Integrable (fun y => g (f y) * K y) (intervalMeasure 1) :=
      hK_int.bdd_mul hg_meas
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs]
          exact hg_bdd y)
    exact hmul.congr (Eventually.of_forall fun y => by ring)
  have hf_int_μK : Integrable f μK := by
    rw [show μK = (intervalMeasure 1).withDensity Kd from rfl,
      integrable_withDensity_iff_integrable_smul₀' hKd_aem hKd_ae_lt,
      show (fun y => (Kd y).toReal • f y) = fun y => K y * f y by
        ext y
        simp [hKd_toReal, smul_eq_mul]]
    exact hKf_int
  have hg_int_μK : Integrable (fun y => g (f y)) μK := by
    rw [show μK = (intervalMeasure 1).withDensity Kd from rfl,
      integrable_withDensity_iff_integrable_smul₀' hKd_aem hKd_ae_lt,
      show (fun y => (Kd y).toReal • g (f y)) =
          fun y => K y * g (f y) by
        ext y
        simp [hKd_toReal, smul_eq_mul]]
    exact hKg_int
  have hint_rel : ∀ q : ℝ → ℝ,
      ∫ y, q y ∂μK = ∫ y, K y * q y ∂(intervalMeasure 1) := by
    intro q
    rw [show μK = (intervalMeasure 1).withDensity Kd from rfl,
      integral_withDensity_eq_integral_toReal_smul₀ hKd_aem hKd_ae_lt]
    congr 1
    ext y
    simp [hKd_toReal, smul_eq_mul]
  have hJ := negativePart_sq_convexOn.map_integral_le
    negativePart_sq_continuous.continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun y => Set.mem_univ (f y))
    hf_int_μK hg_int_μK
  rw [hint_rel f, hint_rel (fun y => g (f y))] at hJ
  simpa [intervalFullSemigroupOperator, K, g, Function.comp_def] using hJ

/-- The full Neumann semigroup preserves the spatial integral of a bounded
measurable input. -/
theorem intervalFullSemigroupOperator_integral_eq
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    (hf_int : Integrable f (intervalMeasure 1)) :
    (∫ x, intervalFullSemigroupOperator t f x ∂(intervalMeasure 1)) =
      ∫ y, f y ∂(intervalMeasure 1) := by
  let μ := intervalMeasure 1
  let F : ℝ × ℝ → ℝ := fun p =>
    intervalNeumannFullKernel t p.1 p.2 * f p.2
  have hF_meas : AEStronglyMeasurable F (μ.prod μ) := by
    exact
      (intervalNeumannFullKernel_joint_measurable ht).aestronglyMeasurable.mul
        hf_meas.comp_snd
  have hF_int : Integrable F (μ.prod μ) := by
    refine (MeasureTheory.integrable_prod_iff' hF_meas).2 ⟨?_, ?_⟩
    · refine Filter.Eventually.of_forall (fun y => ?_)
      have hK : Integrable (fun x => intervalNeumannFullKernel t x y) μ := by
        have h :=
          ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_integrable
            ht y
        exact h.congr (Eventually.of_forall fun x =>
          ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_symm
            ht y x)
      exact hK.mul_const (f y)
    · have hinner :
          (fun y => ∫ x, ‖F (x, y)‖ ∂μ) = fun y => |f y| := by
        funext y
        calc
          (∫ x, ‖F (x, y)‖ ∂μ) =
              (∫ x, intervalNeumannFullKernel t x y ∂μ) * |f y| := by
            rw [← integral_mul_const]
            apply integral_congr_ae
            refine Filter.Eventually.of_forall (fun x => ?_)
            simp only [F, Real.norm_eq_abs, abs_mul]
            rw [abs_of_nonneg
              (ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_nonneg
                ht x y)]
          _ = 1 * |f y| := by
            rw [show (∫ x, intervalNeumannFullKernel t x y ∂μ) = 1 by
              calc
                (∫ x, intervalNeumannFullKernel t x y ∂μ) =
                    ∫ x, intervalNeumannFullKernel t y x ∂μ := by
                      apply integral_congr_ae
                      exact Filter.Eventually.of_forall fun x =>
                        ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_symm
                          ht x y
                _ = 1 :=
                  ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_intervalMeasure_integral_eq_one
                    ht y]
          _ = |f y| := one_mul _
      rw [hinner]
      exact hf_int.norm
  have hswap := MeasureTheory.integral_integral_swap
    (μ := μ) (ν := μ) (f := fun x y => F (x, y)) hF_int
  unfold intervalFullSemigroupOperator
  calc
    (∫ x, ∫ y, intervalNeumannFullKernel t x y * f y ∂μ ∂μ) =
        ∫ y, ∫ x, F (x, y) ∂μ ∂μ := hswap
    _ = ∫ y, f y ∂μ := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall (fun y => ?_)
      calc
        (∫ x, F (x, y) ∂μ) =
            (∫ x, intervalNeumannFullKernel t x y ∂μ) * f y := by
          simp only [F]
          rw [integral_mul_const]
        _ = 1 * f y := by
          rw [show (∫ x, intervalNeumannFullKernel t x y ∂μ) = 1 by
            calc
              (∫ x, intervalNeumannFullKernel t x y ∂μ) =
                  ∫ x, intervalNeumannFullKernel t y x ∂μ := by
                    apply integral_congr_ae
                    exact Filter.Eventually.of_forall fun x =>
                      ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_symm
                        ht x y
              _ = 1 :=
                ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_intervalMeasure_integral_eq_one
                  ht y]
        _ = f y := one_mul _

/-- Self-adjointness of the full Neumann heat operator on bounded integrable
profiles.  The statement is kept at the concrete integral level needed by the
weak Duhamel endpoint argument. -/
theorem intervalFullSemigroupOperator_pairing_comm
    {t : ℝ} (ht : 0 < t) {f g : ℝ → ℝ} {Cf Cg : ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    (hg_meas : AEStronglyMeasurable g (intervalMeasure 1))
    (hf_bound : ∀ y, |f y| ≤ Cf) (hg_bound : ∀ x, |g x| ≤ Cg) :
    (∫ x, intervalFullSemigroupOperator t f x * g x
      ∂(intervalMeasure 1)) =
      ∫ y, f y * intervalFullSemigroupOperator t g y
        ∂(intervalMeasure 1) := by
  let μ := intervalMeasure 1
  let K : ℝ × ℝ → ℝ := fun q =>
    intervalNeumannFullKernel t q.1 q.2
  have hK_meas : AEStronglyMeasurable K (μ.prod μ) :=
    (intervalNeumannFullKernel_joint_measurable ht).aestronglyMeasurable
  have hK_int : Integrable K (μ.prod μ) := by
    refine (MeasureTheory.integrable_prod_iff' hK_meas).2 ⟨?_, ?_⟩
    · refine Filter.Eventually.of_forall (fun y => ?_)
      have h :=
        ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_integrable
          ht y
      exact h.congr (Eventually.of_forall fun x =>
        ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_symm ht y x)
    · have hinner :
          (fun y => ∫ x, ‖K (x, y)‖ ∂μ) = fun _ : ℝ => 1 := by
        funext y
        calc
          (∫ x, ‖K (x, y)‖ ∂μ) =
              ∫ x, intervalNeumannFullKernel t x y ∂μ := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x => by
              change ‖intervalNeumannFullKernel t x y‖ =
                intervalNeumannFullKernel t x y
              rw [Real.norm_eq_abs, abs_of_nonneg
                (ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_nonneg
                  ht x y)]
          _ = ∫ x, intervalNeumannFullKernel t y x ∂μ := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x =>
              ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_symm
                ht x y
          _ = 1 :=
            ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_intervalMeasure_integral_eq_one
              ht y
      rw [hinner]
      exact integrable_const _
  have hCf : 0 ≤ Cf := (abs_nonneg (f 0)).trans (hf_bound 0)
  have hCg : 0 ≤ Cg := (abs_nonneg (g 0)).trans (hg_bound 0)
  have hKf : Integrable (fun q : ℝ × ℝ => K q * f q.2) (μ.prod μ) := by
    have hmul := hK_int.bdd_mul hf_meas.comp_snd
      (Filter.Eventually.of_forall fun q => by
        rw [Real.norm_eq_abs]
        exact hf_bound q.2)
    exact hmul.congr (Eventually.of_forall fun q => by ring)
  have hF : Integrable
      (fun q : ℝ × ℝ => K q * f q.2 * g q.1) (μ.prod μ) := by
    have hmul := hKf.bdd_mul hg_meas.comp_fst
      (Filter.Eventually.of_forall fun q => by
        rw [Real.norm_eq_abs]
        exact hg_bound q.1)
    exact hmul.congr (Eventually.of_forall fun q => by ring)
  have hswap := MeasureTheory.integral_integral_swap
    (f := fun x y => K (x, y) * f y * g x) hF
  unfold intervalFullSemigroupOperator
  calc
    (∫ x, (∫ y, intervalNeumannFullKernel t x y * f y ∂μ) * g x ∂μ) =
        ∫ x, ∫ y, K (x, y) * f y * g x ∂μ ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change (∫ y, intervalNeumannFullKernel t x y * f y ∂μ) * g x =
          ∫ y, K (x, y) * f y * g x ∂μ
        rw [← integral_mul_const]
    _ = ∫ y, ∫ x, K (x, y) * f y * g x ∂μ ∂μ := hswap
    _ = ∫ y, f y * (∫ x, intervalNeumannFullKernel t y x * g x ∂μ)
          ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        change (∫ x, K (x, y) * f y * g x ∂μ) =
          f y * (∫ x, intervalNeumannFullKernel t y x * g x ∂μ)
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          change intervalNeumannFullKernel t x y * f y * g x =
            f y * (intervalNeumannFullKernel t y x * g x)
          rw [ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_symm
            ht x y]
          ring

/-! ## Self-adjoint conjugate/Dirichlet heat operator -/

/-- The signed conjugate kernel is symmetric in its two spatial variables.
Equivalently, its negative is the usual Dirichlet heat kernel. -/
theorem intervalNeumannConjugateKernel_symm
    {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    intervalNeumannConjugateKernel t x y =
      intervalNeumannConjugateKernel t y x := by
  have hreflect :
      ShenWork.IntervalNeumannFullKernel.intervalNeumannReflectedKernelPart
          t x y =
        ShenWork.IntervalNeumannFullKernel.intervalNeumannReflectedKernelPart
          t y x := by
    unfold ShenWork.IntervalNeumannFullKernel.intervalNeumannReflectedKernelPart
    congr 1
    funext k
    rw [add_comm x y]
  apply neg_injective
  calc
    -intervalNeumannConjugateKernel t x y =
        intervalNeumannFullKernel t x y -
          2 * ShenWork.IntervalNeumannFullKernel.intervalNeumannReflectedKernelPart
            t x y :=
      ShenWork.IntervalNeumannFullKernel.neg_conjugateKernel_eq_full_sub_two_reflected
        ht x y
    _ = intervalNeumannFullKernel t y x -
          2 * ShenWork.IntervalNeumannFullKernel.intervalNeumannReflectedKernelPart
            t y x := by
      rw [ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_symm
        ht x y, hreflect]
    _ = -intervalNeumannConjugateKernel t y x :=
      (ShenWork.IntervalNeumannFullKernel.neg_conjugateKernel_eq_full_sub_two_reflected
        ht y x).symm

private theorem intervalNeumannConjugateKernel_joint_measurable
    {t : ℝ} (ht : 0 < t) :
    Measurable (fun p : ℝ × ℝ =>
      intervalNeumannConjugateKernel t p.1 p.2) := by
  set g : ℤ → ℝ × ℝ → ℝ := fun k p =>
    -heatKernel t (p.1 - p.2 + 2 * (k : ℝ)) +
      heatKernel t (p.1 + p.2 + 2 * (k : ℝ)) with hg
  have hg_meas : ∀ k, Measurable (g k) := by
    intro k
    simp only [g]
    unfold heatKernel
    fun_prop
  have hg_sum : ∀ p, Summable (fun k : ℤ => g k p) := by
    intro p
    exact
      (ShenWork.IntervalNeumannFullKernel.latticeGaussianSummable
        ht (p.1 - p.2)).neg.add
      (ShenWork.IntervalNeumannFullKernel.latticeGaussianSummable
        ht (p.1 + p.2))
  have hmeas :=
    ShenWork.IntervalNeumannFullKernel.measurable_tsum_int_of_summable
      hg_meas hg_sum
  have hfun :
      (fun p : ℝ × ℝ => intervalNeumannConjugateKernel t p.1 p.2) =
        fun p => ∑' k : ℤ, g k p := by
    funext p
    rfl
  rw [hfun]
  exact hmeas

/-- The Dirichlet heat operator written in the repository's signed conjugate
kernel convention. -/
def intervalConjugateApproxOperator (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(∫ y in (0 : ℝ)..1,
    f y * intervalNeumannConjugateKernel t x y)

private theorem intervalMeasure_integral_eq_intervalIntegral
    (f : ℝ → ℝ) :
    (∫ y, f y ∂intervalMeasure 1) = ∫ y in (0 : ℝ)..1, f y := by
  simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
  change (∫ y in Set.Icc (0 : ℝ) 1, f y ∂volume) =
    ∫ y in (0 : ℝ)..1, f y
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]

private theorem intervalConjugateApproxOperator_eq_measure_integral
    (t : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    intervalConjugateApproxOperator t f x =
      ∫ y, (-intervalNeumannConjugateKernel t x y) * f y
        ∂intervalMeasure 1 := by
  rw [intervalMeasure_integral_eq_intervalIntegral]
  unfold intervalConjugateApproxOperator
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro y _hy
  ring

private theorem neg_conjugateKernel_integrable_prod
    {t : ℝ} (ht : 0 < t) :
    Integrable
      (fun q : ℝ × ℝ =>
        -intervalNeumannConjugateKernel t q.1 q.2)
      ((intervalMeasure 1).prod (intervalMeasure 1)) := by
  let μ := intervalMeasure 1
  let D : ℝ × ℝ → ℝ := fun q =>
    -intervalNeumannConjugateKernel t q.1 q.2
  let K : ℝ × ℝ → ℝ := fun q =>
    intervalNeumannFullKernel t q.1 q.2
  have hD_meas : AEStronglyMeasurable D (μ.prod μ) :=
    (intervalNeumannConjugateKernel_joint_measurable ht).neg.aestronglyMeasurable
  have hK_meas : AEStronglyMeasurable K (μ.prod μ) :=
    (intervalNeumannFullKernel_joint_measurable ht).aestronglyMeasurable
  have hK_int : Integrable K (μ.prod μ) := by
    refine (MeasureTheory.integrable_prod_iff' hK_meas).2 ⟨?_, ?_⟩
    · refine Filter.Eventually.of_forall (fun y => ?_)
      have h :=
        ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_integrable
          ht y
      exact h.congr (Eventually.of_forall fun x =>
        ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_symm ht y x)
    · have hinner :
          (fun y => ∫ x, ‖K (x, y)‖ ∂μ) = fun _ : ℝ => 1 := by
        funext y
        calc
          (∫ x, ‖K (x, y)‖ ∂μ) =
              ∫ x, intervalNeumannFullKernel t x y ∂μ := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x => by
              change ‖intervalNeumannFullKernel t x y‖ =
                intervalNeumannFullKernel t x y
              rw [Real.norm_eq_abs, abs_of_nonneg
                (ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_nonneg
                  ht x y)]
          _ = ∫ x, intervalNeumannFullKernel t y x ∂μ := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x =>
              ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_symm
                ht x y
          _ = 1 :=
            ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_intervalMeasure_integral_eq_one
              ht y
      rw [hinner]
      exact integrable_const _
  exact hK_int.mono' hD_meas (Filter.Eventually.of_forall fun q => by
    change |-intervalNeumannConjugateKernel t q.1 q.2| ≤
      intervalNeumannFullKernel t q.1 q.2
    rw [abs_neg]
    exact ShenWork.IntervalNeumannFullKernel.abs_conjugateKernel_le
      ht q.1 q.2)

/-- Self-adjointness of the conjugate/Dirichlet heat operator on bounded
measurable profiles. -/
theorem intervalConjugateApproxOperator_pairing_comm
    {t : ℝ} (ht : 0 < t) {f g : ℝ → ℝ} {Cf Cg : ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    (hg_meas : AEStronglyMeasurable g (intervalMeasure 1))
    (hf_bound : ∀ y, |f y| ≤ Cf) (hg_bound : ∀ x, |g x| ≤ Cg) :
    (∫ x, intervalConjugateApproxOperator t f x * g x
      ∂intervalMeasure 1) =
      ∫ y, f y * intervalConjugateApproxOperator t g y
        ∂intervalMeasure 1 := by
  let μ := intervalMeasure 1
  let D : ℝ × ℝ → ℝ := fun q =>
    -intervalNeumannConjugateKernel t q.1 q.2
  have hD_int : Integrable D (μ.prod μ) := by
    simpa [D, μ] using neg_conjugateKernel_integrable_prod ht
  have hDf : Integrable (fun q : ℝ × ℝ => D q * f q.2) (μ.prod μ) :=
    (hD_int.bdd_mul hf_meas.comp_snd
      (Filter.Eventually.of_forall fun q => by
        rw [Real.norm_eq_abs]
        exact hf_bound q.2)).congr
      (Eventually.of_forall fun _ => by ring)
  have hF : Integrable
      (fun q : ℝ × ℝ => D q * f q.2 * g q.1) (μ.prod μ) :=
    (hDf.bdd_mul hg_meas.comp_fst
      (Filter.Eventually.of_forall fun q => by
        rw [Real.norm_eq_abs]
        exact hg_bound q.1)).congr
      (Eventually.of_forall fun _ => by ring)
  have hswap := MeasureTheory.integral_integral_swap
    (f := fun x y => D (x, y) * f y * g x) hF
  simp only [intervalConjugateApproxOperator_eq_measure_integral]
  calc
    (∫ x, (∫ y, (-intervalNeumannConjugateKernel t x y) * f y ∂μ) * g x
        ∂μ) =
        ∫ x, ∫ y, D (x, y) * f y * g x ∂μ ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change (∫ y, D (x, y) * f y ∂μ) * g x =
          ∫ y, D (x, y) * f y * g x ∂μ
        rw [← integral_mul_const]
    _ = ∫ y, ∫ x, D (x, y) * f y * g x ∂μ ∂μ := hswap
    _ = ∫ y, f y *
          (∫ x, (-intervalNeumannConjugateKernel t y x) * g x ∂μ)
          ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        change (∫ x, D (x, y) * f y * g x ∂μ) =
          f y * (∫ x, D (y, x) * g x ∂μ)
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          change (-intervalNeumannConjugateKernel t x y) * f y * g x =
            f y * ((-intervalNeumannConjugateKernel t y x) * g x)
          rw [intervalNeumannConjugateKernel_symm ht x y]
          ring

/-- The conjugate/Dirichlet heat operator is integrable on the interval for
every bounded measurable input. -/
theorem intervalConjugateApproxOperator_integrable_of_bound
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} {Cf : ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    (hf_bound : ∀ y, |f y| ≤ Cf) :
    Integrable (intervalConjugateApproxOperator t f) (intervalMeasure 1) := by
  let μ := intervalMeasure 1
  let D : ℝ × ℝ → ℝ := fun q =>
    -intervalNeumannConjugateKernel t q.1 q.2
  have hD_int : Integrable D (μ.prod μ) := by
    simpa [D, μ] using neg_conjugateKernel_integrable_prod ht
  have hDf : Integrable (fun q : ℝ × ℝ => D q * f q.2) (μ.prod μ) :=
    (hD_int.bdd_mul hf_meas.comp_snd
      (Filter.Eventually.of_forall fun q => by
        rw [Real.norm_eq_abs]
        exact hf_bound q.2)).congr
      (Eventually.of_forall fun _ => by ring)
  have hinner := hDf.integral_prod_left
  exact hinner.congr (Eventually.of_forall fun x => by
    symm
    exact intervalConjugateApproxOperator_eq_measure_integral t f x)

/-- The negative-part energy is contractive under every positive-time
Neumann heat step. -/
theorem negativePartEnergy_semigroup_le
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} {M : ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    (hf_bdd : ∀ y, |f y| ≤ M) :
    (∫ x, (negativePart (intervalFullSemigroupOperator t f x)) ^ 2
      ∂(intervalMeasure 1)) ≤
      ∫ x, (negativePart (f x)) ^ 2 ∂(intervalMeasure 1) := by
  have hM : 0 ≤ M := le_trans (abs_nonneg (f 0)) (hf_bdd 0)
  let g : ℝ → ℝ := fun x => (negativePart (f x)) ^ 2
  have hg_meas : AEStronglyMeasurable g (intervalMeasure 1) :=
    negativePart_sq_continuous.comp_aestronglyMeasurable hf_meas
  have hg_bdd : ∀ y, |g y| ≤ M ^ 2 := by
    intro y
    have hn : |negativePart (f y)| ≤ M :=
      (negativePart_abs_le_abs (f y)).trans (hf_bdd y)
    have hs : (negativePart (f y)) ^ 2 ≤ M ^ 2 := by
      rw [sq_le_sq]
      simpa [abs_of_nonneg hM] using hn
    change |(negativePart (f y)) ^ 2| ≤ M ^ 2
    rw [abs_of_nonneg (sq_nonneg _)]
    exact hs
  have hg_int : Integrable g (intervalMeasure 1) :=
    ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound
      hg_meas hg_bdd
  calc
    (∫ x, (negativePart (intervalFullSemigroupOperator t f x)) ^ 2
        ∂(intervalMeasure 1)) ≤
        ∫ x, intervalFullSemigroupOperator t g x
          ∂(intervalMeasure 1) := by
      exact integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        (by
          have hSmeas : AEStronglyMeasurable
              (fun x => intervalFullSemigroupOperator t g x)
              (intervalMeasure 1) := by
            exact
              (ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_continuous_of_bounded
                ht (sq_nonneg M) hg_bdd hg_meas).aestronglyMeasurable
          exact ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound
            hSmeas (fun x =>
              ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
                ht (sq_nonneg M) hg_bdd x))
        (Filter.Eventually.of_forall fun x =>
          negativePart_sq_intervalFullSemigroupOperator_le
            ht hf_meas hf_bdd x)
    _ = ∫ x, g x ∂(intervalMeasure 1) :=
      intervalFullSemigroupOperator_integral_eq ht hg_meas hg_int
    _ = ∫ x, (negativePart (f x)) ^ 2 ∂(intervalMeasure 1) := rfl

/-! ## Uniform heat-gradient control for an absolutely continuous test -/

/-- The source-side integration-by-parts formula for an absolutely continuous
profile.  This is the Sobolev-level version of the repository's C¹ formula:
no derivative is requested at the kink points of a truncation. -/
theorem deriv_intervalFullSemigroupOperator_eq_neg_conjugateKernel_of_ac
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    {Cf : ℝ} (hf_bound : ∀ y, |f y| ≤ Cf)
    (hf_ac : AbsolutelyContinuousOnInterval f 0 1) (x : ℝ) :
    deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) x =
      -(∫ y in (0 : ℝ)..1,
          deriv f y * intervalNeumannConjugateKernel t x y) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  rw [(ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_hasDerivAt_fst
    ht hf_meas hf_bound x).deriv]
  have hmeasure :
      (∫ y,
          deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x * f y
            ∂(intervalMeasure 1)) =
        ∫ y in (0 : ℝ)..1,
          f y * deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x := by
    simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le h01]
    exact intervalIntegral.integral_congr (fun y _ => by ring)
  rw [hmeasure]
  let K : ℝ → ℝ := fun y => intervalNeumannConjugateKernel t x y
  have hK_ac : AbsolutelyContinuousOnInterval K 0 1 := by
    let dK : ℝ → ℝ := fun y =>
      deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x
    have hdK_cont : ContinuousOn dK (Set.Icc (0 : ℝ) 1) := by
      simpa [dK] using
        ShenWork.IntervalNeumannFullKernel.continuousOn_deriv_intervalNeumannFullKernel_fst
          ht x
    obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hdK_cont
    let C : ℝ := max B 0
    have hC : 0 ≤ C := le_max_right _ _
    have hdK_bound : ∀ y ∈ Set.Icc (0 : ℝ) 1, |dK y| ≤ C := by
      intro y hy
      exact (Real.norm_eq_abs (dK y) ▸ hB y hy).trans (le_max_left _ _)
    have hK_has : ∀ y : ℝ, HasDerivAt K (dK y) y := by
      intro y
      have h :=
        ShenWork.IntervalNeumannFullKernel.hasDerivAt_conjugateKernel_snd ht x y
      rw [← (ShenWork.IntervalNeumannFullKernel.hasDerivAt_intervalNeumannFullKernel_fst
        ht x y).deriv] at h
      simpa [K, dK] using h
    have hK_lip_open : LipschitzOnWith ⟨C, hC⟩ K (Set.Ioo (0 : ℝ) 1) := by
      apply Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
        (convex_Ioo (0 : ℝ) 1)
      · intro y _hy
        exact (hK_has y).hasDerivWithinAt
      · intro y hy
        exact_mod_cast (show ‖dK y‖ ≤ C by
          simpa [Real.norm_eq_abs] using
            hdK_bound y (Set.Ioo_subset_Icc_self hy))
    have hK_lip : LipschitzOnWith ⟨C, hC⟩ K (Set.Icc (0 : ℝ) 1) := by
      rw [← closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
      exact hK_lip_open.closure (by
        simpa [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1), K] using
          ShenWork.IntervalNeumannFullKernel.continuousOn_conjugateKernel_snd
            ht x)
    have hK_lip_u : LipschitzOnWith ⟨C, hC⟩ K (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hK_lip
    exact hK_lip_u.absolutelyContinuousOnInterval
  have hKderiv : ∀ y ∈ Set.uIcc (0 : ℝ) 1,
      deriv K y =
        deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x := by
    intro y _hy
    have h := ShenWork.IntervalNeumannFullKernel.hasDerivAt_conjugateKernel_snd
      ht x y
    rw [← (ShenWork.IntervalNeumannFullKernel.hasDerivAt_intervalNeumannFullKernel_fst
      ht x y).deriv] at h
    simpa [K] using h.deriv
  calc
    (∫ y in (0 : ℝ)..1,
        f y * deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x) =
        ∫ y in (0 : ℝ)..1, f y * deriv K y := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with y hy
      rw [Set.uIoc_of_le h01] at hy
      have hyu : y ∈ Set.uIcc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le h01] using (show y ∈ Set.Icc (0 : ℝ) 1 from
          ⟨hy.1.le, hy.2⟩)
      rw [hKderiv y hyu]
    _ = f 1 * K 1 - f 0 * K 0 -
        ∫ y in (0 : ℝ)..1, deriv f y * K y :=
      hf_ac.integral_mul_deriv_eq_deriv_mul hK_ac
    _ = -(∫ y in (0 : ℝ)..1,
        deriv f y * intervalNeumannConjugateKernel t x y) := by
      simp [K, ShenWork.IntervalNeumannFullKernel.conjugateKernel_at_one ht x,
        ShenWork.IntervalNeumannFullKernel.conjugateKernel_at_zero]

/-- Neumann heat flow does not enlarge the spatial Lipschitz envelope of an
absolutely continuous profile.  The derivative bound is only required almost
everywhere, so it applies directly to the negative-part test. -/
theorem abs_deriv_intervalFullSemigroupOperator_le_of_ac
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    {Cf : ℝ} (hf_bound : ∀ y, |f y| ≤ Cf)
    (hf_ac : AbsolutelyContinuousOnInterval f 0 1)
    {G : ℝ} (hG : 0 ≤ G)
    (hf_deriv_bound : ∀ᵐ y ∂volume, |deriv f y| ≤ G)
    (x : ℝ) :
    |deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) x| ≤ G := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  rw [deriv_intervalFullSemigroupOperator_eq_neg_conjugateKernel_of_ac
    ht hf_meas hf_bound hf_ac x, abs_neg]
  have hprod_int : IntervalIntegrable
      (fun y : ℝ => deriv f y * intervalNeumannConjugateKernel t x y)
      volume 0 1 :=
    hf_ac.intervalIntegrable_deriv.mul_continuousOn (by
      simpa [Set.uIcc_of_le h01] using
        ShenWork.IntervalNeumannFullKernel.continuousOn_conjugateKernel_snd ht x)
  have hK_int : IntervalIntegrable
      (fun y : ℝ => G * |intervalNeumannConjugateKernel t x y|)
      volume 0 1 := by
    exact
      ((by
        simpa [Set.uIcc_of_le h01] using
          (ShenWork.IntervalNeumannFullKernel.continuousOn_conjugateKernel_snd
            ht x).abs : ContinuousOn
              (fun y : ℝ => |intervalNeumannConjugateKernel t x y|)
              (Set.uIcc (0 : ℝ) 1)).intervalIntegrable).const_mul G
  calc
    |∫ y in (0 : ℝ)..1,
        deriv f y * intervalNeumannConjugateKernel t x y|
        ≤ ∫ y in (0 : ℝ)..1,
            |deriv f y * intervalNeumannConjugateKernel t x y| :=
          intervalIntegral.abs_integral_le_integral_abs h01
    _ ≤ ∫ y in (0 : ℝ)..1,
          G * |intervalNeumannConjugateKernel t x y| := by
        apply intervalIntegral.integral_mono_ae h01 hprod_int.abs hK_int
        filter_upwards [hf_deriv_bound] with y hy
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right hy (abs_nonneg _)
    _ = G * ∫ y in (0 : ℝ)..1,
          |intervalNeumannConjugateKernel t x y| := by
        rw [intervalIntegral.integral_const_mul]
    _ ≤ G * 1 := mul_le_mul_of_nonneg_left
      (ShenWork.IntervalNeumannFullKernel.conjugateKernel_L1_bound ht x) hG
    _ = G := mul_one G

/-- Supporting-line inequality at the final point for the convex negative-part
square. -/
theorem negativePart_sq_sub_le_final (a b : ℝ) :
    (negativePart b) ^ 2 - (negativePart a) ^ 2 ≤
      (-2 * negativePart b) * (b - a) := by
  by_cases hb : 0 ≤ b
  · rw [negativePart_eq_zero_of_nonneg hb]
    norm_num [pow_two]
    exact mul_nonneg (negativePart_nonneg a) (negativePart_nonneg a)
  · have hb' : b ≤ 0 := (le_of_lt (lt_of_not_ge hb))
    rw [negativePart_eq_neg_of_nonpos hb']
    by_cases ha : 0 ≤ a
    · rw [negativePart_eq_zero_of_nonneg ha]
      nlinarith
    · have ha' : a ≤ 0 := le_of_lt (lt_of_not_ge ha)
      rw [negativePart_eq_neg_of_nonpos ha']
      nlinarith [sq_nonneg (b - a)]

/-- Backward energy increment estimate for a mild restart.  The homogeneous
heat leg contributes no increase; only the restart remainder is paired with
the final negative-part test. -/
theorem negativePartEnergy_sub_le_remainder_pairing
    {h : ℝ} (hh : 0 < h) {f u z : ℝ → ℝ} {M : ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    (hf_bdd : ∀ y, |f y| ≤ M)
    (hu_repr : ∀ᵐ x ∂intervalMeasure 1,
      u x = intervalFullSemigroupOperator h f x + z x)
    (huE : Integrable (fun x => (negativePart (u x)) ^ 2)
      (intervalMeasure 1))
    (hSE : Integrable
      (fun x => (negativePart (intervalFullSemigroupOperator h f x)) ^ 2)
      (intervalMeasure 1))
    (hpair : Integrable (fun x => (-2 * negativePart (u x)) * z x)
      (intervalMeasure 1)) :
    (∫ x, (negativePart (u x)) ^ 2 ∂(intervalMeasure 1)) -
        ∫ x, (negativePart (f x)) ^ 2 ∂(intervalMeasure 1) ≤
      ∫ x, (-2 * negativePart (u x)) * z x ∂(intervalMeasure 1) := by
  have hpoint : ∀ᵐ x ∂intervalMeasure 1,
      (negativePart (u x)) ^ 2 -
          (negativePart (intervalFullSemigroupOperator h f x)) ^ 2 ≤
        (-2 * negativePart (u x)) * z x := by
    filter_upwards [hu_repr] with x hx
    have h := negativePart_sq_sub_le_final
      (intervalFullSemigroupOperator h f x) (u x)
    simpa [hx] using h
  have hlocal :
      (∫ x, (negativePart (u x)) ^ 2 ∂(intervalMeasure 1)) -
          ∫ x, (negativePart (intervalFullSemigroupOperator h f x)) ^ 2
            ∂(intervalMeasure 1) ≤
        ∫ x, (-2 * negativePart (u x)) * z x
          ∂(intervalMeasure 1) := by
    rw [← integral_sub huE hSE]
    exact integral_mono_ae (huE.sub hSE) hpair hpoint
  have hheat := negativePartEnergy_semigroup_le hh hf_meas hf_bdd
  linarith

/-! ## Backward derivatives and Gronwall -/

/-- A limit of backward difference quotients is the left derivative. -/
theorem hasDerivWithinAt_Iic_of_backwardSlope
    {E : ℝ → ℝ} {t d : ℝ}
    (h : Tendsto (fun q : ℝ => q⁻¹ * (E t - E (t - q)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds d)) :
    HasDerivWithinAt E d (Set.Iic t) t := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hset : Set.Iic t \ {t} = Set.Iio t := by
    ext x
    simp
  rw [hset]
  let e : ℝ ≃ₜ ℝ := Homeomorph.subLeft t
  have hm : Filter.map e (nhdsWithin 0 (Set.Ioi 0)) =
      nhdsWithin t (Set.Iio t) := by
    have hm' := e.isEmbedding.map_nhdsWithin_eq (Set.Ioi (0 : ℝ)) 0
    simpa [e] using hm'
  rw [← hm, tendsto_map'_iff]
  convert h using 1
  funext q
  simp only [e, Homeomorph.subLeft_apply, slope, Function.comp_def,
    vsub_eq_sub, smul_eq_mul]
  ring

/-- The left derivative is equivalently the limit of backward difference
quotients. -/
theorem HasDerivWithinAt.tendsto_backwardSlope_Iic
    {E : ℝ → ℝ} {t d : ℝ}
    (h : HasDerivWithinAt E d (Set.Iic t) t) :
    Tendsto (fun q : ℝ => q⁻¹ * (E t - E (t - q)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds d) := by
  have hslope : Tendsto (slope E t) (nhdsWithin t (Set.Iio t)) (nhds d) := by
    have hs := (hasDerivWithinAt_iff_tendsto_slope).1 h
    have hset : Set.Iic t \ {t} = Set.Iio t := by
      ext x
      simp
    rwa [hset] at hs
  have hsub : Tendsto (fun q : ℝ => t - q)
      (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin t (Set.Iio t)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hc : ContinuousAt (fun q : ℝ => t - q) 0 :=
        continuousAt_const.sub continuousAt_id
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with q hq
      exact sub_lt_self t (show 0 < q from hq)
  have hs := hslope.comp hsub
  convert hs using 1
  funext q
  change q⁻¹ * (E t - E (t - q)) =
    (t - q - t)⁻¹ * (E (t - q) - E t)
  rw [show t - q - t = -q by ring, inv_neg]
  ring

/-- A two-sided derivative controls the backward difference quotient. -/
theorem HasDerivAt.tendsto_backwardSlope
    {E : ℝ → ℝ} {t d : ℝ} (h : HasDerivAt E d t) :
    Tendsto (fun q : ℝ => q⁻¹ * (E t - E (t - q)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds d) := by
  have hneg : Tendsto (fun q : ℝ => -q)
      (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Iio 0)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · simpa using
        ((continuousAt_id.neg : ContinuousAt (fun q : ℝ => -q) 0).tendsto.mono_left
          nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with q hq
      exact neg_lt_zero.mpr (show 0 < q from hq)
  have hs := h.tendsto_slope_zero_left.comp hneg
  convert hs using 1
  funext q
  simp only [Function.comp_apply, inv_neg, neg_smul, smul_eq_mul]
  ring

/-- A locally integrable scalar function with a left limit has the same left
limit under backward interval averaging.  The endpoint is updated before
applying FTC, so the statement remains valid when the original function has
an unrelated value at the endpoint. -/
theorem left_intervalAverage_tendsto
    {F : ℝ → ℝ} {c t L : ℝ} (hct : c < t)
    (hFint : IntervalIntegrable F volume c t)
    (hFmeas : AEStronglyMeasurable F (volume.restrict (Set.uIoc c t)))
    (hFlim : Tendsto F (nhdsWithin t (Set.Iio t)) (nhds L)) :
    Tendsto (fun q : ℝ => q⁻¹ * ∫ s in (t - q)..t, F s)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  classical
  let Fu : ℝ → ℝ := Function.update F t L
  have hFu_ae : Fu =ᵐ[volume.restrict (Set.uIoc c t)] F := by
    filter_upwards [(Measure.ae_ne volume t).filter_mono ae_restrict_le] with x hx
    simp [Fu, Function.update_of_ne hx]
  have hFu_meas : AEStronglyMeasurable Fu
      (volume.restrict (Set.uIoc c t)) :=
    hFmeas.congr hFu_ae.symm
  have hFu_int : IntervalIntegrable Fu volume c t := by
    rw [intervalIntegrable_iff] at hFint ⊢
    exact hFint.congr hFu_ae.symm
  have hFu_cont : ContinuousWithinAt Fu (Set.Iic t) t := by
    rw [continuousWithinAt_update_same]
    have hset : Set.Iic t \ {t} = Set.Iio t := by
      ext x
      simp
    rwa [hset]
  have hHderiv : HasDerivWithinAt
      (fun u => ∫ s in c..u, Fu s) L (Set.Iic t) t := by
    have hFu_at : StronglyMeasurableAtFilter Fu
        (nhdsWithin t (Set.Iic t)) volume :=
      AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem hFu_meas (by
        simpa [Set.uIoc_of_le hct.le] using Ioc_mem_nhdsLE hct)
    simpa [Fu] using
      (intervalIntegral.integral_hasDerivWithinAt_right
        (s := Set.Iic t) (t := Set.Iic t) hFu_int
        hFu_at hFu_cont)
  have hHback := HasDerivWithinAt.tendsto_backwardSlope_Iic hHderiv
  refine hHback.congr' ?_
  have hsmall : ∀ᶠ q in nhdsWithin 0 (Set.Ioi 0), q < t - c :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Iio_mem_nhds (sub_pos.mpr hct))
  filter_upwards [self_mem_nhdsWithin, hsmall] with q hq hqsmall
  have hq0 : 0 < q := hq
  have hcq : c ≤ t - q := by linarith
  have hqt : t - q ≤ t := by linarith
  have hleft : IntervalIntegrable Fu volume c (t - q) := by
    apply IntervalIntegrable.mono_set hFu_int
    rw [Set.uIcc_of_le hcq, Set.uIcc_of_le hct.le]
    exact Set.Icc_subset_Icc le_rfl hqt
  have hright : IntervalIntegrable Fu volume (t - q) t := by
    apply IntervalIntegrable.mono_set hFu_int
    rw [Set.uIcc_of_le hqt, Set.uIcc_of_le hct.le]
    exact Set.Icc_subset_Icc hcq le_rfl
  have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
  have htail : (∫ s in (t - q)..t, Fu s) = ∫ s in (t - q)..t, F s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [(Measure.ae_ne volume t)] with s hs _hsI
    simp [Fu, Function.update_of_ne hs]
  rw [← htail, ← hadd]
  ring

/-- Backward zero-Gronwall in Mathlib's native fencing form.  The hypothesis
is the frequently-small left-slope statement; after reversing time it is
exactly the right-slope hypothesis of
`image_le_of_liminf_slope_right_le_deriv_boundary`. -/
theorem backward_gronwall_zero_of_liminf_left_slope
    {T : ℝ} (hT : 0 ≤ T) {W : ℝ → ℝ}
    (hW_cont : ContinuousOn W (Set.Icc (0 : ℝ) T))
    (hW_nonneg : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ W t)
    (hW0 : W 0 = 0)
    (hleft : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ r : ℝ, 0 < r →
      ∃ᶠ q in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (W t - W (t - q)) / q < r) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, W t = 0 := by
  intro t ht
  by_cases ht0 : t = 0
  · simpa [ht0] using hW0
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  let F : ℝ → ℝ := fun s => -W (t - s)
  let B : ℝ → ℝ := fun _ => -W t
  let B' : ℝ → ℝ := fun _ => 0
  have hmap : Set.MapsTo (fun s : ℝ => t - s)
      (Set.Icc (0 : ℝ) t) (Set.Icc (0 : ℝ) T) := by
    intro s hs
    change t - s ∈ Set.Icc (0 : ℝ) T
    constructor <;> linarith [hs.1, hs.2, ht.2]
  have hFcont : ContinuousOn F (Set.Icc (0 : ℝ) t) :=
    (hW_cont.comp (continuous_const.sub continuous_id).continuousOn hmap).neg
  have hinit : F 0 ≤ B 0 := by simp [F, B]
  have hBcont : ContinuousOn B (Set.Icc (0 : ℝ) t) := continuousOn_const
  have hBderiv : ∀ x ∈ Set.Ico (0 : ℝ) t,
      HasDerivWithinAt B (B' x) (Set.Ici x) x := by
    intro x _hx
    simpa [B, B'] using
      (hasDerivWithinAt_const (x := x) (s := Set.Ici x) (c := -W t))
  have hslope : ∀ x ∈ Set.Ico (0 : ℝ) t, ∀ r : ℝ, B' x < r →
      ∃ᶠ z in nhdsWithin x (Set.Ioi x), slope F x z < r := by
    intro x hx r hr
    have htx : t - x ∈ Set.Ioc (0 : ℝ) T := by
      constructor <;> linarith [hx.1, hx.2, ht.2]
    have hq := hleft (t - x) htx r (by simpa [B'] using hr)
    rw [← show x + 0 = x by ring, ← Filter.map_add_left_nhdsGT, frequently_map]
    exact hq.mono fun q hqsmall => by
      have heq : slope F x (x + q) =
          (W (t - x) - W (t - x - q)) / q := by
        unfold F slope
        simp only [vsub_eq_sub, smul_eq_mul, div_eq_mul_inv]
        rw [show x + q - x = q by ring,
          show t - (x + q) = t - x - q by ring]
        ring
      simpa only [add_zero, heq] using hqsmall
  have hfence := image_le_of_liminf_slope_right_le_deriv_boundary
    hFcont hinit hBcont hBderiv hslope
  have hend := hfence (Set.right_mem_Icc.mpr htpos.le)
  have hWt_le : W t ≤ 0 := by
    simpa [F, B, hW0] using hend
  exact le_antisymm hWt_le (hW_nonneg t ht)

/-- Adapter from a convergent upper bound for backward energy quotients to the
native frequently-small-slope fencing lemma above. -/
theorem backward_gronwall_zero_of_upper_tendsto
    {E : ℝ → ℝ} {K T : ℝ} (hT : 0 ≤ T)
    (hcont : ContinuousOn E (Set.Icc (0 : ℝ) T))
    (hnonneg : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ E t)
    (hE0 : E 0 = 0)
    (hupper : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ d : ℝ, ∃ R : ℝ → ℝ,
      d ≤ K * E t ∧
      Tendsto R (nhdsWithin 0 (Set.Ioi 0)) (nhds d) ∧
      ∀ᶠ q in nhdsWithin 0 (Set.Ioi 0),
        q⁻¹ * (E t - E (t - q)) ≤ R q) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, E t = 0 := by
  let W : ℝ → ℝ := fun t => Real.exp (-K * t) * E t
  have hWcont : ContinuousOn W (Set.Icc (0 : ℝ) T) := by
    have hinner : Continuous (fun t : ℝ => -K * t) :=
      continuous_const.mul continuous_id
    have hexp : Continuous (fun t : ℝ => Real.exp (-K * t)) :=
      Real.continuous_exp.comp hinner
    exact hexp.continuousOn.mul hcont
  have hWnonneg : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ W t := by
    intro t ht
    exact mul_nonneg (Real.exp_pos _).le (hnonneg t ht)
  have hW0 : W 0 = 0 := by simp [W, hE0]
  have hWleft : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ r : ℝ, 0 < r →
      ∃ᶠ q in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (W t - W (t - q)) / q < r := by
    intro t ht r hr
    obtain ⟨d, R, hd, hR, hquot⟩ := hupper t ht
    let A : ℝ := Real.exp (-K * t)
    let G : ℝ → ℝ := fun x => Real.exp (-K * x)
    let C : ℝ → ℝ := fun q =>
      A * R q + (q⁻¹ * (G t - G (t - q))) * E (t - q)
    have hGderiv : HasDerivAt G (-K * A) t := by
      have hinner : HasDerivAt (fun x : ℝ => -K * x) (-K) t := by
        convert (hasDerivAt_id t).const_mul (-K) using 1 <;> ring
      simpa [G, A, mul_comm] using hinner.exp
    have hGback : Tendsto (fun q : ℝ => q⁻¹ * (G t - G (t - q)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (-K * A)) :=
      HasDerivAt.tendsto_backwardSlope hGderiv
    have hsub : Tendsto (fun q : ℝ => t - q)
        (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin t (Set.Icc (0 : ℝ) T)) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have hc : ContinuousAt (fun q : ℝ => t - q) 0 :=
          continuousAt_const.sub continuousAt_id
        simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
      · have hsmall : ∀ᶠ q in nhdsWithin 0 (Set.Ioi 0), q < t :=
          Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds ht.1)
        filter_upwards [self_mem_nhdsWithin, hsmall] with q hq hqt
        have hq0 : 0 < q := hq
        constructor <;> linarith [ht.2]
    have hEsub : Tendsto (fun q : ℝ => E (t - q))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (E t)) :=
      (show Tendsto E (nhdsWithin t (Set.Icc (0 : ℝ) T)) (nhds (E t)) from
        hcont t ⟨ht.1.le, ht.2⟩).comp hsub
    have hC : Tendsto C (nhdsWithin 0 (Set.Ioi 0))
        (nhds (A * d + (-K * A) * E t)) := by
      simpa [C] using (tendsto_const_nhds.mul hR).add (hGback.mul hEsub)
    have hApos : 0 < A := Real.exp_pos _
    have hClim_le : A * d + (-K * A) * E t ≤ 0 := by
      have hm := mul_le_mul_of_nonneg_left hd hApos.le
      linarith
    have hCsmall : ∀ᶠ q in nhdsWithin 0 (Set.Ioi 0), C q < r :=
      hC (Iio_mem_nhds (hClim_le.trans_lt hr))
    have hWupper : ∀ᶠ q in nhdsWithin 0 (Set.Ioi 0),
        (W t - W (t - q)) / q ≤ C q := by
      filter_upwards [hquot] with q hq
      have hdecomp : (W t - W (t - q)) / q =
          A * (q⁻¹ * (E t - E (t - q))) +
            (q⁻¹ * (G t - G (t - q))) * E (t - q) := by
        simp only [W, G, A, div_eq_mul_inv]
        ring
      rw [hdecomp]
      dsimp only [C]
      exact add_le_add (mul_le_mul_of_nonneg_left hq hApos.le) (le_refl _)
    have hev : ∀ᶠ q in nhdsWithin 0 (Set.Ioi 0),
        (W t - W (t - q)) / q < r := by
      filter_upwards [hWupper, hCsmall] with q hq hqr
      exact hq.trans_lt hqr
    letI : (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))).NeBot :=
      nhdsGT_neBot (0 : ℝ)
    exact hev.frequently
  have hWzero := backward_gronwall_zero_of_liminf_left_slope
    hT hWcont hWnonneg hW0 hWleft
  intro t ht
  have hz := hWzero t ht
  dsimp [W] at hz
  exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt (Real.exp_pos _))

/-- Backward upper-slope Gronwall in the form produced by a variational mild
restart.  The backward quotient need not converge: it is enough that it is
eventually bounded by a quantity converging to some `d ≤ K E(r)`.

The proof exponentially weights `E`, takes a maximum on the compact time
interval, and uses a slightly stronger weight `K + 1`.  At a positive maximum
the backward quotient is nonnegative, while the assumed upper slope makes it
strictly negative. -/
theorem nonpos_of_backward_upper_tendsto
    {E : ℝ → ℝ} {K a b : ℝ}
    (hab : a ≤ b)
    (hcont : ContinuousOn E (Set.Icc a b))
    (hupper : ∀ r ∈ Set.Ioc a b, ∃ d : ℝ, ∃ R : ℝ → ℝ,
      d ≤ K * E r ∧
      Tendsto R (nhdsWithin 0 (Set.Ioi 0)) (nhds d) ∧
      ∀ᶠ q in nhdsWithin 0 (Set.Ioi 0),
        q⁻¹ * (E r - E (r - q)) ≤ R q)
    (hEa : E a ≤ 0) :
    E b ≤ 0 := by
  let lam : ℝ := K + 1
  let W : ℝ → ℝ := fun r => Real.exp (-lam * (r - a)) * E r
  have hweight_cont : Continuous (fun r : ℝ => Real.exp (-lam * (r - a))) := by
    fun_prop
  have hWcont : ContinuousOn W (Set.Icc a b) := by
    exact hweight_cont.continuousOn.mul hcont
  obtain ⟨r, hr, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hab) hWcont
  by_contra hb
  have hEb : 0 < E b := lt_of_not_ge hb
  have hWb : 0 < W b := mul_pos (Real.exp_pos _) hEb
  have hWr : 0 < W r := hWb.trans_le (hmax (Set.right_mem_Icc.mpr hab))
  have hEr : 0 < E r := by
    rcases mul_pos_iff.mp hWr with hpos | hneg
    · exact hpos.2
    · exact False.elim ((not_lt_of_ge (Real.exp_pos _).le) hneg.1)
  have har : a < r := by
    by_contra har
    have hra : r = a := le_antisymm (not_lt.mp har) hr.1
    subst r
    have : W a ≤ 0 := by simpa [W] using hEa
    exact (not_lt_of_ge this) hWr
  have hrIoc : r ∈ Set.Ioc a b := ⟨har, hr.2⟩
  obtain ⟨d, R, hd, hR, hquot⟩ := hupper r hrIoc
  let A : ℝ := Real.exp (-lam * (r - a))
  let G : ℝ → ℝ := fun x => Real.exp (-lam * (x - a))
  let B : ℝ → ℝ := fun q =>
    A * R q + (q⁻¹ * (G r - G (r - q))) * E (r - q)
  have hGderiv : HasDerivAt G (-lam * A) r := by
    have hinner : HasDerivAt (fun x : ℝ => -lam * (x - a)) (-lam) r := by
      convert ((hasDerivAt_id r).sub_const a).const_mul (-lam) using 1 <;> ring
    simpa [G, A, mul_comm] using hinner.exp
  have hGback : Tendsto (fun q : ℝ => q⁻¹ * (G r - G (r - q)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-lam * A)) :=
    HasDerivAt.tendsto_backwardSlope hGderiv
  have hsub : Tendsto (fun q : ℝ => r - q)
      (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin r (Set.Icc a b)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hc : ContinuousAt (fun q : ℝ => r - q) 0 :=
        continuousAt_const.sub continuousAt_id
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    · have hlt : Set.Iio (r - a) ∈ nhds 0 := Iio_mem_nhds (sub_pos.mpr har)
      have hlt' : ∀ᶠ q in nhdsWithin 0 (Set.Ioi 0), q < r - a :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds hlt
      filter_upwards [self_mem_nhdsWithin, hlt'] with q hq hqr
      have hq0 : 0 < q := hq
      constructor <;> linarith [hr.2]
  have hEsub : Tendsto (fun q : ℝ => E (r - q))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (E r)) :=
    (show Tendsto E (nhdsWithin r (Set.Icc a b)) (nhds (E r)) from
      hcont r hr).comp hsub
  have hB : Tendsto B (nhdsWithin 0 (Set.Ioi 0))
      (nhds (A * d + (-lam * A) * E r)) := by
    simpa [B] using (tendsto_const_nhds.mul hR).add (hGback.mul hEsub)
  have hApos : 0 < A := Real.exp_pos _
  have hBlimneg : A * d + (-lam * A) * E r < 0 := by
    have hm := mul_le_mul_of_nonneg_left hd hApos.le
    dsimp [lam]
    nlinarith
  have hBneg : ∀ᶠ q in nhdsWithin 0 (Set.Ioi 0), B q < 0 :=
    hB (Iio_mem_nhds hBlimneg)
  have hsmall : ∀ᶠ q in nhdsWithin 0 (Set.Ioi 0), q < r - a := by
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Iio_mem_nhds (sub_pos.mpr har))
  have hmem : ∀ᶠ q : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      q ∈ Set.Ioi (0 : ℝ) :=
    self_mem_nhdsWithin
  letI : (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))).NeBot :=
    nhdsGT_neBot (0 : ℝ)
  obtain ⟨q, hq, hqsmall, hqE, hqB⟩ :=
    (hmem.and (hsmall.and (hquot.and hBneg))).exists
  have hq0 : 0 < q := hq
  have hrq_mem : r - q ∈ Set.Icc a b := by
    constructor <;> linarith [hr.2]
  have hWmono : W (r - q) ≤ W r := hmax hrq_mem
  have hWquot_nonneg : 0 ≤ q⁻¹ * (W r - W (r - q)) :=
    mul_nonneg (inv_nonneg.mpr hq.le) (sub_nonneg.mpr hWmono)
  have hWquot_le : q⁻¹ * (W r - W (r - q)) ≤ B q := by
    have hA : G r = A := rfl
    have hdecomp :
        q⁻¹ * (W r - W (r - q)) =
          A * (q⁻¹ * (E r - E (r - q))) +
            (q⁻¹ * (G r - G (r - q))) * E (r - q) := by
      simp only [W, G, A]
      ring
    rw [hdecomp]
    dsimp only [B]
    exact add_le_add (mul_le_mul_of_nonneg_left hqE hApos.le) (le_refl _)
  linarith

/-- Gronwall from left derivatives.  This is the natural scalar closure for a
backward mild-restart estimate: reflect the interval and negate the energy,
then apply the repository's right-derivative Gronwall theorem. -/
theorem gronwall_exp_of_backward_deriv
    {E D : ℝ → ℝ} {K a b : ℝ}
    (hab : a ≤ b)
    (hcont : ContinuousOn E (Set.Icc a b))
    (hleft : ∀ r ∈ Set.Ioc a b,
      HasDerivWithinAt E (D r) (Set.Iic r) r)
    (hbound : ∀ r ∈ Set.Ioc a b, D r ≤ K * E r) :
    E b ≤ E a * Real.exp (K * (b - a)) := by
  let c : ℝ := a + b
  let R : ℝ → ℝ := fun x => -E (c - x)
  let RD : ℝ → ℝ := fun x => D (c - x)
  have hmap : Set.MapsTo (fun x : ℝ => c - x)
      (Set.Icc a b) (Set.Icc a b) := by
    intro x hx
    dsimp [c]
    constructor <;> linarith [hx.1, hx.2]
  have hRcont : ContinuousOn R (Set.Icc a b) := by
    exact (hcont.comp (continuous_const.sub continuous_id).continuousOn hmap).neg
  have hRderiv : ∀ x ∈ Set.Ico a b,
      HasDerivWithinAt R (RD x) (Set.Ici x) x := by
    intro x hx
    have hr : c - x ∈ Set.Ioc a b := by
      dsimp [c]
      constructor <;> linarith [hx.1, hx.2]
    have hg : HasDerivWithinAt (fun q : ℝ => c - q) (-1)
        (Set.Ici x) x := by
      simpa using
        (hasDerivWithinAt_const (x := x) (s := Set.Ici x) (c := c)).sub
          (hasDerivWithinAt_id (x := x) (s := Set.Ici x))
    have hmaps : Set.MapsTo (fun q : ℝ => c - q)
        (Set.Ici x) (Set.Iic (c - x)) := by
      intro q hq
      simp only [Set.mem_Ici] at hq
      simp only [Set.mem_Iic]
      linarith
    have hc := (hleft (c - x) hr).comp x hg hmaps
    have hn := hc.neg
    simpa [R, RD] using hn
  have hRbound : ∀ x ∈ Set.Ico a b, RD x ≤ (-K) * R x := by
    intro x hx
    have hr : c - x ∈ Set.Ioc a b := by
      dsimp [c]
      constructor <;> linarith [hx.1, hx.2]
    simpa [R, RD] using hbound (c - x) hr
  have hgr := ShenWork.Paper2.intervalDomainL2_gronwall_exp_of_diffIneq
    (E := R) (E' := RD) (K := -K) hab hRcont hRderiv hRbound
  dsimp [R, c] at hgr
  have hexp : Real.exp ((-K) * (b - a)) *
      Real.exp (K * (b - a)) = 1 := by
    calc
      _ = Real.exp 0 := by rw [← Real.exp_add]; congr 1 <;> ring
      _ = 1 := Real.exp_zero
  have hm := mul_le_mul_of_nonneg_right hgr
    (Real.exp_nonneg (K * (b - a)))
  rw [mul_assoc, hexp, mul_one] at hm
  simpa [mul_comm, mul_left_comm, mul_assoc] using (neg_le_neg hm)

end ShenWork.Paper2.IntervalNegativePartWeakEnergy
