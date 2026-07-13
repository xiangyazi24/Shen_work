import ShenWork.Paper1.Lemma25Helpers
import ShenWork.Paper1.WaveRotheStep
import Mathlib.MeasureTheory.Function.L2Space

open Filter Topology MeasureTheory

noncomputable section

namespace ShenWork.Paper1

lemma sq_integral_abs_mul_le_global
    {f g : ℝ → ℝ}
    (hf_sq : Integrable (fun y => f y ^ 2))
    (hg_sq : Integrable (fun y => g y ^ 2))
    (hfg : Integrable (fun y => |f y * g y|)) :
    (∫ y : ℝ, |f y * g y|) ^ 2 ≤
      (∫ y : ℝ, f y ^ 2) * (∫ y : ℝ, g y ^ 2) := by
  set A := ∫ y : ℝ, f y ^ 2 with hA_def
  set B := ∫ y : ℝ, |f y * g y| with hB_def
  set C := ∫ y : ℝ, g y ^ 2 with hC_def
  have hA_nn : 0 ≤ A := integral_nonneg fun _ => sq_nonneg _
  have hB_nn : 0 ≤ B := integral_nonneg fun _ => abs_nonneg _
  have hC_nn : 0 ≤ C := integral_nonneg fun _ => sq_nonneg _
  suffices hdisc : ∀ t : ℝ, 0 ≤ A - 2 * t * B + t ^ 2 * C by
    by_cases hC_pos : 0 < C
    · have h := hdisc (B / C)
      nlinarith [sq_nonneg (B - B / C * C), div_mul_cancel₀ B (ne_of_gt hC_pos)]
    · have hC0 : C = 0 := le_antisymm (not_lt.mp hC_pos) hC_nn
      rw [hC0, mul_zero]
      suffices hB0 : B = 0 by rw [hB0]; simp
      by_contra hBne
      have hBp : 0 < B := hB_nn.lt_of_ne' hBne
      have h := hdisc ((A + 1) / (2 * B))
      have h2B_ne : (2 : ℝ) * B ≠ 0 := by positivity
      nlinarith [div_mul_cancel₀ (A + 1) h2B_ne]
  intro t
  have h_integrand_eq : ∀ y,
      (|f y| - t * |g y|) ^ 2 =
        f y ^ 2 + (-(2 * t) * |f y * g y| + t ^ 2 * g y ^ 2) := by
    intro y
    rw [abs_mul]
    nlinarith [sq_abs (f y), sq_abs (g y)]
  have h_int_sq : Integrable (fun y => (|f y| - t * |g y|) ^ 2) := by
    refine (hf_sq.add ((hfg.const_mul (-(2 * t))).add
      (hg_sq.const_mul (t ^ 2)))).congr ?_
    exact Filter.Eventually.of_forall fun y => (h_integrand_eq y).symm
  have h_nonneg : 0 ≤ ∫ y : ℝ, (|f y| - t * |g y|) ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have h_integral_eq :
      (∫ y : ℝ, (|f y| - t * |g y|) ^ 2) =
        A - 2 * t * B + t ^ 2 * C := by
    have hsum_int := (hfg.const_mul (-(2 * t))).add (hg_sq.const_mul (t ^ 2))
    rw [integral_congr_ae (Filter.Eventually.of_forall h_integrand_eq)]
    calc
      (∫ y : ℝ, f y ^ 2 + (-(2 * t) * |f y * g y| + t ^ 2 * g y ^ 2)) =
          (∫ y : ℝ, f y ^ 2) +
            ∫ y : ℝ, (-(2 * t) * |f y * g y| + t ^ 2 * g y ^ 2) :=
        integral_add hf_sq hsum_int
      _ = (∫ y : ℝ, f y ^ 2) +
            ((∫ y : ℝ, -(2 * t) * |f y * g y|) +
              ∫ y : ℝ, t ^ 2 * g y ^ 2) := by
        rw [integral_add (hfg.const_mul (-(2 * t))) (hg_sq.const_mul (t ^ 2))]
      _ = A - 2 * t * B + t ^ 2 * C := by
        rw [integral_const_mul, integral_const_mul]
        simp only [hA_def, hB_def, hC_def]
        ring
  rw [h_integral_eq] at h_nonneg
  exact h_nonneg

/-- A nonnegative doubly-stochastic integral kernel is an `L²` contraction.
This is the continuous Schur/Jensen estimate used by the two-sided and
one-sided exponential Green kernels in Lemma 5.3. -/
theorem markovKernel_l2_contraction
    (K : ℝ → ℝ → ℝ) (q : ℝ → ℝ)
    (hK_meas : Measurable (Function.uncurry K))
    (hK_nn : ∀ x y, 0 ≤ K x y)
    (hrow_int : ∀ x, Integrable (K x))
    (hrow_mass : ∀ x, ∫ y : ℝ, K x y = 1)
    (hcol_int : ∀ y, Integrable (fun x => K x y))
    (hcol_mass : ∀ y, ∫ x : ℝ, K x y = 1)
    (hq_meas : Measurable q)
    (hq_sq : Integrable (fun y => q y ^ 2)) :
    Integrable (fun x => (∫ y : ℝ, K x y * |q y|) ^ 2) ∧
      (∫ x : ℝ, (∫ y : ℝ, K x y * |q y|) ^ 2) ≤
        ∫ y : ℝ, q y ^ 2 := by
  let J : ℝ × ℝ → ℝ := fun z => K z.1 z.2 * q z.2 ^ 2
  have hJ_meas : Measurable J := by
    dsimp [J]
    fun_prop
  have hJ_int : Integrable J (volume.prod volume) := by
    refine (integrable_prod_iff' hJ_meas.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · exact Filter.Eventually.of_forall fun y => by
        have heq : (fun x => J (x, y)) = fun x => q y ^ 2 * K x y := by
          funext x
          dsimp [J]
          ring
        rw [heq]
        exact (hcol_int y).const_mul (q y ^ 2)
    · have heq :
          (fun y => ∫ x : ℝ, ‖J (x, y)‖) = fun y => q y ^ 2 := by
        funext y
        have hnorm : (fun x => ‖J (x, y)‖) = fun x => q y ^ 2 * K x y := by
          funext x
          rw [Real.norm_eq_abs, abs_of_nonneg]
          · dsimp [J]
            ring
          · exact mul_nonneg (hK_nn x y) (sq_nonneg _)
        rw [hnorm, integral_const_mul, hcol_mass]
        ring
      rw [heq]
      exact hq_sq
  let T : ℝ → ℝ := fun x => ∫ y : ℝ, K x y * |q y|
  let R : ℝ → ℝ := fun x => ∫ y : ℝ, J (x, y)
  have hT_strong : StronglyMeasurable T := by
    apply StronglyMeasurable.integral_prod_right
    have : Measurable
        (Function.uncurry (fun x y => K x y * |q y|)) := by
      fun_prop
    exact this.stronglyMeasurable
  have hR_int : Integrable R := by
    exact hJ_int.integral_prod_left
  have hpoint : ∀ᵐ x : ℝ, T x ^ 2 ≤ R x := by
    filter_upwards [hJ_int.prod_right_ae] with x hx
    let f : ℝ → ℝ := fun y => Real.sqrt (K x y)
    let g : ℝ → ℝ := fun y => Real.sqrt (K x y) * |q y|
    have hf_sq : Integrable (fun y => f y ^ 2) := by
      refine (hrow_int x).congr (Filter.Eventually.of_forall fun y => ?_)
      dsimp [f]
      exact (Real.sq_sqrt (hK_nn x y)).symm
    have hg_sq : Integrable (fun y => g y ^ 2) := by
      refine hx.congr (Filter.Eventually.of_forall fun y => ?_)
      dsimp [g, J]
      rw [mul_pow, Real.sq_sqrt (hK_nn x y), sq_abs]
    have hf_mem : MemLp f 2 volume :=
      (memLp_two_iff_integrable_sq (by fun_prop)).2 hf_sq
    have hg_mem : MemLp g 2 volume :=
      (memLp_two_iff_integrable_sq (by fun_prop)).2 hg_sq
    have hfg : Integrable (fun y => |f y * g y|) := by
      have hmul : Integrable (f * g) := hf_mem.integrable_mul hg_mem
      simpa [Pi.mul_apply, Real.norm_eq_abs] using hmul.norm
    have hcs := sq_integral_abs_mul_le_global hf_sq hg_sq hfg
    have hleft : (∫ y : ℝ, |f y * g y|) = T x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        dsimp [f, g, T]
        rw [← mul_assoc, ← pow_two, Real.sq_sqrt (hK_nn x y)]
        exact abs_of_nonneg (mul_nonneg (hK_nn x y) (abs_nonneg _))
    have hfirst : (∫ y : ℝ, f y ^ 2) = 1 := by
      have heq : (fun y => f y ^ 2) = K x := by
        funext y
        dsimp [f]
        exact Real.sq_sqrt (hK_nn x y)
      rw [heq, hrow_mass]
    have hsecond : (∫ y : ℝ, g y ^ 2) = R x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        dsimp [g, R, J]
        rw [mul_pow, Real.sq_sqrt (hK_nn x y), sq_abs]
    rw [hleft, hfirst, one_mul, hsecond] at hcs
    exact hcs
  have hT_sq_int : Integrable (fun x => T x ^ 2) := by
    refine hR_int.mono' (hT_strong.pow 2).aestronglyMeasurable ?_
    filter_upwards [hpoint] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hx
  have hmain : (∫ x : ℝ, T x ^ 2) ≤ ∫ x : ℝ, R x :=
    integral_mono_ae hT_sq_int hR_int hpoint
  have hR_eq : (∫ x : ℝ, R x) = ∫ y : ℝ, q y ^ 2 := by
    dsimp [R]
    rw [integral_integral_swap hJ_int]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      change (∫ x : ℝ, J (x, y)) = q y ^ 2
      have heq : (fun x => J (x, y)) = fun x => q y ^ 2 * K x y := by
        funext x
        dsimp [J]
        ring
      rw [heq, integral_const_mul, hcol_mass]
      ring
  rw [hR_eq] at hmain
  exact ⟨by simpa [T] using hT_sq_int, by simpa [T] using hmain⟩

lemma kernel_mul_abs_integrable_of_sq_integrable
    (K q : ℝ → ℝ) {C : ℝ}
    (hK_int : Integrable K) (hK_meas : Measurable K) (hK_nn : ∀ y, 0 ≤ K y)
    (hK_le : ∀ y, K y ≤ C)
    (hq_meas : Measurable q) (hq_sq : Integrable (fun y => q y ^ 2)) :
    Integrable (fun y => K y * |q y|) := by
  have hKq_sq : Integrable (fun y => K y * q y ^ 2) := by
    have hraw := hq_sq.mul_bdd hK_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hK_nn y)]
        exact hK_le y)
    refine hraw.congr (Filter.Eventually.of_forall fun y => ?_)
    ring
  let f : ℝ → ℝ := fun y => Real.sqrt (K y)
  let g : ℝ → ℝ := fun y => Real.sqrt (K y) * |q y|
  have hf_sq : Integrable (fun y => f y ^ 2) := by
    refine hK_int.congr (Filter.Eventually.of_forall fun y => ?_)
    dsimp [f]
    exact (Real.sq_sqrt (hK_nn y)).symm
  have hg_sq : Integrable (fun y => g y ^ 2) := by
    refine hKq_sq.congr (Filter.Eventually.of_forall fun y => ?_)
    dsimp [g]
    rw [mul_pow, Real.sq_sqrt (hK_nn y), sq_abs]
  have hf_mem : MemLp f 2 volume :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 hf_sq
  have hg_mem : MemLp g 2 volume :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 hg_sq
  have hmul : Integrable (f * g) := hf_mem.integrable_mul hg_mem
  refine hmul.congr (Filter.Eventually.of_forall fun y => ?_)
  dsimp [f, g]
  rw [← mul_assoc, ← pow_two, Real.sq_sqrt (hK_nn y)]

def laplaceMarkovKernel (a : ℝ) (x y : ℝ) : ℝ :=
  a / 2 * Real.exp (-a * |x - y|)

lemma laplaceMarkovKernel_measurable (a : ℝ) :
    Measurable (Function.uncurry (laplaceMarkovKernel a)) := by
  unfold laplaceMarkovKernel Function.uncurry
  fun_prop

lemma laplaceMarkovKernel_nonneg {a : ℝ} (ha : 0 ≤ a) (x y : ℝ) :
    0 ≤ laplaceMarkovKernel a x y :=
  mul_nonneg (div_nonneg ha zero_le_two) (Real.exp_nonneg _)

lemma laplaceMarkovKernel_le {a : ℝ} (ha : 0 ≤ a) (x y : ℝ) :
    laplaceMarkovKernel a x y ≤ a / 2 := by
  unfold laplaceMarkovKernel
  have hnonpos : -a * |x - y| ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (abs_nonneg _)
  have hexp : Real.exp (-a * |x - y|) ≤ 1 :=
    Real.exp_le_one_iff.mpr hnonpos
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hexp (div_nonneg ha zero_le_two)

lemma laplaceMarkovKernel_row_integrable {a : ℝ} (ha : 0 < a) (x : ℝ) :
    Integrable (laplaceMarkovKernel a x) := by
  unfold laplaceMarkovKernel
  exact (kernel_exp_neg_mul_abs_integrable ha x).const_mul (a / 2)

lemma laplaceMarkovKernel_row_mass {a : ℝ} (ha : 0 < a) (x : ℝ) :
    ∫ y : ℝ, laplaceMarkovKernel a x y = 1 := by
  unfold laplaceMarkovKernel
  rw [integral_const_mul, integral_exp_neg_mul_abs_sub ha]
  field_simp [ne_of_gt ha]

lemma laplaceMarkovKernel_col_integrable {a : ℝ} (ha : 0 < a) (y : ℝ) :
    Integrable (fun x => laplaceMarkovKernel a x y) := by
  have h := (kernel_exp_neg_mul_abs_integrable ha y).const_mul (a / 2)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [laplaceMarkovKernel]
  rw [abs_sub_comm x y]

lemma laplaceMarkovKernel_col_mass {a : ℝ} (ha : 0 < a) (y : ℝ) :
    ∫ x : ℝ, laplaceMarkovKernel a x y = 1 := by
  have h := laplaceMarkovKernel_row_mass ha y
  simpa [laplaceMarkovKernel, abs_sub_comm] using h

theorem laplaceMarkovKernel_l2_contraction
    {a : ℝ} (ha : 0 < a) {q : ℝ → ℝ}
    (hq_meas : Measurable q) (hq_sq : Integrable (fun y => q y ^ 2)) :
    Integrable
        (fun x => (∫ y : ℝ, laplaceMarkovKernel a x y * |q y|) ^ 2) ∧
      (∫ x : ℝ, (∫ y : ℝ, laplaceMarkovKernel a x y * |q y|) ^ 2) ≤
        ∫ y : ℝ, q y ^ 2 := by
  exact markovKernel_l2_contraction (laplaceMarkovKernel a) q
    (laplaceMarkovKernel_measurable a)
    (laplaceMarkovKernel_nonneg ha.le)
    (laplaceMarkovKernel_row_integrable ha)
    (laplaceMarkovKernel_row_mass ha)
    (laplaceMarkovKernel_col_integrable ha)
    (laplaceMarkovKernel_col_mass ha)
    hq_meas hq_sq

lemma laplaceMarkovKernel_mul_abs_integrable
    {a : ℝ} (ha : 0 < a) {q : ℝ → ℝ}
    (hq_meas : Measurable q) (hq_sq : Integrable (fun y => q y ^ 2)) (x : ℝ) :
    Integrable (fun y => laplaceMarkovKernel a x y * |q y|) :=
  kernel_mul_abs_integrable_of_sq_integrable
    (laplaceMarkovKernel a x) q
    (laplaceMarkovKernel_row_integrable ha x)
    ((laplaceMarkovKernel_measurable a).comp
      (measurable_const.prodMk measurable_id))
    (laplaceMarkovKernel_nonneg ha.le x)
    (laplaceMarkovKernel_le ha.le x)
    hq_meas hq_sq

def leftExpMarkovKernel (a : ℝ) (x y : ℝ) : ℝ :=
  if y < x then a * Real.exp (-a * (x - y)) else 0

lemma leftExpMarkovKernel_measurable (a : ℝ) :
    Measurable (Function.uncurry (leftExpMarkovKernel a)) := by
  unfold leftExpMarkovKernel Function.uncurry
  refine Measurable.ite (measurableSet_lt measurable_snd measurable_fst) ?_ measurable_const
  fun_prop

lemma leftExpMarkovKernel_nonneg {a : ℝ} (ha : 0 ≤ a) (x y : ℝ) :
    0 ≤ leftExpMarkovKernel a x y := by
  unfold leftExpMarkovKernel
  split_ifs
  · positivity
  · exact le_rfl

lemma leftExpMarkovKernel_le {a : ℝ} (ha : 0 ≤ a) (x y : ℝ) :
    leftExpMarkovKernel a x y ≤ a := by
  unfold leftExpMarkovKernel
  split_ifs with h
  · have hxy : 0 ≤ x - y := sub_nonneg.mpr (le_of_lt h)
    have hnonpos : -a * (x - y) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) hxy
    have hexp : Real.exp (-a * (x - y)) ≤ 1 :=
      Real.exp_le_one_iff.mpr hnonpos
    exact mul_le_of_le_one_right ha hexp
  · exact ha

lemma leftExpMarkovKernel_row_integrable {a : ℝ} (ha : 0 < a) (x : ℝ) :
    Integrable (leftExpMarkovKernel a x) := by
  let base : ℝ → ℝ := fun y => a * Real.exp (-a * (x - y))
  have hbaseIic : IntegrableOn base (Set.Iic x) := by
    have h := (integrableOn_exp_mul_Iic ha x).const_mul
      (a * Real.exp (-a * x))
    refine MeasureTheory.IntegrableOn.congr_fun h ?_ measurableSet_Iic
    intro y _hy
    dsimp [base]
    rw [show -a * (x - y) = -a * x + a * y by ring, Real.exp_add]
    ring
  have hbaseIio : IntegrableOn base (Set.Iio x) :=
    hbaseIic.mono_set Set.Iio_subset_Iic_self
  have hind := hbaseIio.integrable_indicator measurableSet_Iio
  have hfun : leftExpMarkovKernel a x = (Set.Iio x).indicator base := by
    funext y
    simp [leftExpMarkovKernel, base, Set.indicator]
  rw [hfun]
  exact hind

lemma leftExpMarkovKernel_row_mass {a : ℝ} (ha : 0 < a) (x : ℝ) :
    ∫ y : ℝ, leftExpMarkovKernel a x y = 1 := by
  let base : ℝ → ℝ := fun y => a * Real.exp (-a * (x - y))
  have hfun : leftExpMarkovKernel a x = (Set.Iio x).indicator base := by
    funext y
    simp [leftExpMarkovKernel, base, Set.indicator]
  rw [hfun, integral_indicator measurableSet_Iio,
    ← MeasureTheory.integral_Iic_eq_integral_Iio]
  have heq : base = fun y => (a * Real.exp (-a * x)) * Real.exp (a * y) := by
    funext y
    dsimp [base]
    rw [show -a * (x - y) = -a * x + a * y by ring, Real.exp_add]
    ring
  rw [heq, integral_const_mul, integral_exp_mul_Iic ha]
  field_simp [ne_of_gt ha, Real.exp_ne_zero]
  rw [← Real.exp_add]
  simp

lemma leftExpMarkovKernel_col_integrable {a : ℝ} (ha : 0 < a) (y : ℝ) :
    Integrable (fun x => leftExpMarkovKernel a x y) := by
  let base : ℝ → ℝ := fun x => a * Real.exp (-a * (x - y))
  have hbaseIoi : IntegrableOn base (Set.Ioi y) := by
    have hneg : -a < 0 := neg_neg_iff_pos.mpr ha
    have h := (integrableOn_exp_mul_Ioi hneg y).const_mul
      (a * Real.exp (a * y))
    refine MeasureTheory.IntegrableOn.congr_fun h ?_ measurableSet_Ioi
    intro x _hx
    dsimp [base]
    rw [show -a * (x - y) = a * y + -a * x by ring, Real.exp_add]
    ring
  have hind := hbaseIoi.integrable_indicator measurableSet_Ioi
  have hfun : (fun x => leftExpMarkovKernel a x y) =
      (Set.Ioi y).indicator base := by
    funext x
    simp [leftExpMarkovKernel, base, Set.indicator]
  rw [hfun]
  exact hind

lemma leftExpMarkovKernel_col_mass {a : ℝ} (ha : 0 < a) (y : ℝ) :
    ∫ x : ℝ, leftExpMarkovKernel a x y = 1 := by
  let base : ℝ → ℝ := fun x => a * Real.exp (-a * (x - y))
  have hfun : (fun x => leftExpMarkovKernel a x y) =
      (Set.Ioi y).indicator base := by
    funext x
    simp [leftExpMarkovKernel, base, Set.indicator]
  rw [hfun, integral_indicator measurableSet_Ioi]
  have heq : base = fun x => (a * Real.exp (a * y)) * Real.exp (-a * x) := by
    funext x
    dsimp [base]
    rw [show -a * (x - y) = a * y + -a * x by ring, Real.exp_add]
    ring
  have hneg : -a < 0 := neg_neg_iff_pos.mpr ha
  rw [heq, integral_const_mul, integral_exp_mul_Ioi hneg]
  field_simp [ne_of_gt ha, Real.exp_ne_zero]
  rw [← Real.exp_add]
  simp

def rightExpMarkovKernel (a : ℝ) (x y : ℝ) : ℝ :=
  leftExpMarkovKernel a y x

lemma rightExpMarkovKernel_measurable (a : ℝ) :
    Measurable (Function.uncurry (rightExpMarkovKernel a)) := by
  simpa [rightExpMarkovKernel, Function.uncurry] using
    (leftExpMarkovKernel_measurable a).comp measurable_swap

theorem leftExpMarkovKernel_l2_contraction
    {a : ℝ} (ha : 0 < a) {q : ℝ → ℝ}
    (hq_meas : Measurable q) (hq_sq : Integrable (fun y => q y ^ 2)) :
    Integrable
        (fun x => (∫ y : ℝ, leftExpMarkovKernel a x y * |q y|) ^ 2) ∧
      (∫ x : ℝ, (∫ y : ℝ, leftExpMarkovKernel a x y * |q y|) ^ 2) ≤
        ∫ y : ℝ, q y ^ 2 := by
  exact markovKernel_l2_contraction (leftExpMarkovKernel a) q
    (leftExpMarkovKernel_measurable a)
    (leftExpMarkovKernel_nonneg ha.le)
    (leftExpMarkovKernel_row_integrable ha)
    (leftExpMarkovKernel_row_mass ha)
    (leftExpMarkovKernel_col_integrable ha)
    (leftExpMarkovKernel_col_mass ha)
    hq_meas hq_sq

lemma leftExpMarkovKernel_mul_abs_integrable
    {a : ℝ} (ha : 0 < a) {q : ℝ → ℝ}
    (hq_meas : Measurable q) (hq_sq : Integrable (fun y => q y ^ 2)) (x : ℝ) :
    Integrable (fun y => leftExpMarkovKernel a x y * |q y|) :=
  kernel_mul_abs_integrable_of_sq_integrable
    (leftExpMarkovKernel a x) q
    (leftExpMarkovKernel_row_integrable ha x)
    ((leftExpMarkovKernel_measurable a).comp
      (measurable_const.prodMk measurable_id))
    (leftExpMarkovKernel_nonneg ha.le x)
    (leftExpMarkovKernel_le ha.le x)
    hq_meas hq_sq

theorem rightExpMarkovKernel_l2_contraction
    {a : ℝ} (ha : 0 < a) {q : ℝ → ℝ}
    (hq_meas : Measurable q) (hq_sq : Integrable (fun y => q y ^ 2)) :
    Integrable
        (fun x => (∫ y : ℝ, rightExpMarkovKernel a x y * |q y|) ^ 2) ∧
      (∫ x : ℝ, (∫ y : ℝ, rightExpMarkovKernel a x y * |q y|) ^ 2) ≤
        ∫ y : ℝ, q y ^ 2 := by
  exact markovKernel_l2_contraction (rightExpMarkovKernel a) q
    (rightExpMarkovKernel_measurable a)
    (fun x y => leftExpMarkovKernel_nonneg ha.le y x)
    (leftExpMarkovKernel_col_integrable ha)
    (leftExpMarkovKernel_col_mass ha)
    (leftExpMarkovKernel_row_integrable ha)
    (leftExpMarkovKernel_row_mass ha)
    hq_meas hq_sq

lemma rightExpMarkovKernel_mul_abs_integrable
    {a : ℝ} (ha : 0 < a) {q : ℝ → ℝ}
    (hq_meas : Measurable q) (hq_sq : Integrable (fun y => q y ^ 2)) (x : ℝ) :
    Integrable (fun y => rightExpMarkovKernel a x y * |q y|) :=
  kernel_mul_abs_integrable_of_sq_integrable
    (rightExpMarkovKernel a x) q
    (leftExpMarkovKernel_col_integrable ha x)
    (by
      simpa [rightExpMarkovKernel] using
        (leftExpMarkovKernel_measurable a).comp
          (measurable_id.prodMk measurable_const))
    (fun y => leftExpMarkovKernel_nonneg ha.le y x)
    (fun y => leftExpMarkovKernel_le ha.le y x)
    hq_meas hq_sq

lemma abs_rpow_sub_rpow_le_of_mem_Icc
    {gamma M a b : ℝ} (hgamma : 1 ≤ gamma) (hM : 0 ≤ M)
    (ha : a ∈ Set.Icc (0 : ℝ) M) (hb : b ∈ Set.Icc (0 : ℝ) M) :
    |a ^ gamma - b ^ gamma| ≤ gamma * M ^ (gamma - 1) * |a - b| := by
  have hLip := rpow_m_lipschitz_on_Icc hgamma hM
  have h := hLip.dist_le_mul a ha b hb
  have hL_nn : 0 ≤ rpowLip gamma M := rpowLip_nonneg hgamma hM
  have hcoe : ((Real.toNNReal (rpowLip gamma M) : NNReal) : ℝ) =
      rpowLip gamma M := Real.coe_toNNReal _ hL_nn
  rw [hcoe] at h
  simpa [rpowLip, Real.dist_eq] using h

/-- The pointwise power Lipschitz estimate transports the weighted `L²`
control of `u₂-u₁` to the weighted elliptic source `u₂^γ-u₁^γ`. -/
lemma weighted_power_difference_sq_integrable_and_bound
    {gamma M eta : ℝ} (hgamma : 1 ≤ gamma) (hM : 0 ≤ M)
    {u1 u2 : ℝ → ℝ}
    (hu1 : IsCUnifBdd u1) (hu2 : IsCUnifBdd u2)
    (hu1_mem : ∀ x, u1 x ∈ Set.Icc (0 : ℝ) M)
    (hu2_mem : ∀ x, u2 x ∈ Set.Icc (0 : ℝ) M)
    (hclose : Integrable
      (fun x => Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2)) :
    let q := fun x => Real.exp (eta * x) * (u2 x ^ gamma - u1 x ^ gamma)
    let L := gamma * M ^ (gamma - 1)
    Integrable (fun x => q x ^ 2) ∧
      (∫ x : ℝ, q x ^ 2) ≤ L ^ 2 *
        ∫ x : ℝ, Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2 := by
  dsimp only
  let q : ℝ → ℝ :=
    fun x => Real.exp (eta * x) * (u2 x ^ gamma - u1 x ^ gamma)
  let L : ℝ := gamma * M ^ (gamma - 1)
  have hgamma_nonneg : 0 ≤ gamma := le_trans zero_le_one hgamma
  have hpow1_cont : Continuous (fun x => u1 x ^ gamma) :=
    hu1.1.rpow_const (fun _ => Or.inr hgamma_nonneg)
  have hpow2_cont : Continuous (fun x => u2 x ^ gamma) :=
    hu2.1.rpow_const (fun _ => Or.inr hgamma_nonneg)
  have hq_cont : Continuous q := by
    dsimp [q]
    have hexp_cont : Continuous (fun x : ℝ => Real.exp (eta * x)) := by
      fun_prop
    exact hexp_cont.mul (hpow2_cont.sub hpow1_cont)
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg hgamma_nonneg (Real.rpow_nonneg hM _)
  have hq_sq_eq : ∀ x,
      q x ^ 2 = Real.exp (2 * eta * x) *
        |u2 x ^ gamma - u1 x ^ gamma| ^ 2 := by
    intro x
    dsimp [q]
    rw [mul_pow,
      show Real.exp (eta * x) ^ 2 = Real.exp (eta * x + eta * x) by
        rw [pow_two, ← Real.exp_add],
      show eta * x + eta * x = 2 * eta * x by ring, sq_abs]
  have hpoint : ∀ x, q x ^ 2 ≤ L ^ 2 *
      (Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2) := by
    intro x
    have hs := abs_rpow_sub_rpow_le_of_mem_Icc
      hgamma hM (hu2_mem x) (hu1_mem x)
    have hs_sq : |u2 x ^ gamma - u1 x ^ gamma| ^ 2 ≤
        L ^ 2 * |u2 x - u1 x| ^ 2 := by
      have := (sq_le_sq₀ (abs_nonneg _)
        (mul_nonneg hL_nonneg (abs_nonneg _))).mpr (by simpa [L] using hs)
      simpa [mul_pow] using this
    rw [hq_sq_eq]
    have hexp_nn : 0 ≤ Real.exp (2 * eta * x) := Real.exp_nonneg _
    calc
      Real.exp (2 * eta * x) * |u2 x ^ gamma - u1 x ^ gamma| ^ 2
          ≤ Real.exp (2 * eta * x) *
              (L ^ 2 * |u2 x - u1 x| ^ 2) :=
        mul_le_mul_of_nonneg_left hs_sq hexp_nn
      _ = L ^ 2 *
          (Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2) := by ring
  have hdom : Integrable (fun x => L ^ 2 *
      (Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2)) :=
    hclose.const_mul (L ^ 2)
  have hq_sq_int : Integrable (fun x => q x ^ 2) := by
    refine Integrable.mono' hdom (hq_cont.pow 2).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpoint x
  refine ⟨hq_sq_int, ?_⟩
  calc
    (∫ x : ℝ, q x ^ 2) ≤
        ∫ x : ℝ, L ^ 2 *
          (Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2) :=
      integral_mono hq_sq_int hdom hpoint
    _ = L ^ 2 *
        ∫ x : ℝ, Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2 := by
      rw [integral_const_mul]

lemma rpow_difference_isCUnifBdd
    {gamma M : ℝ} (hgamma : 1 ≤ gamma)
    {u1 u2 : ℝ → ℝ}
    (hu1 : IsCUnifBdd u1) (hu2 : IsCUnifBdd u2)
    (hu1_mem : ∀ x, u1 x ∈ Set.Icc (0 : ℝ) M)
    (hu2_mem : ∀ x, u2 x ∈ Set.Icc (0 : ℝ) M) :
    IsCUnifBdd (fun x => u2 x ^ gamma - u1 x ^ gamma) := by
  have hgamma_nonneg : 0 ≤ gamma := le_trans zero_le_one hgamma
  have hpow1_cont : Continuous (fun x => u1 x ^ gamma) :=
    hu1.1.rpow_const (fun _ => Or.inr hgamma_nonneg)
  have hpow2_cont : Continuous (fun x => u2 x ^ gamma) :=
    hu2.1.rpow_const (fun _ => Or.inr hgamma_nonneg)
  refine ⟨hpow2_cont.sub hpow1_cont, 2 * M ^ gamma, ?_⟩
  intro x
  have hp1_nn : 0 ≤ u1 x ^ gamma := Real.rpow_nonneg (hu1_mem x).1 _
  have hp2_nn : 0 ≤ u2 x ^ gamma := Real.rpow_nonneg (hu2_mem x).1 _
  have hp1_le : u1 x ^ gamma ≤ M ^ gamma :=
    Real.rpow_le_rpow (hu1_mem x).1 (hu1_mem x).2 hgamma_nonneg
  have hp2_le : u2 x ^ gamma ≤ M ^ gamma :=
    Real.rpow_le_rpow (hu2_mem x).1 (hu2_mem x).2 hgamma_nonneg
  calc
    |u2 x ^ gamma - u1 x ^ gamma| ≤
        |u2 x ^ gamma| + |u1 x ^ gamma| := abs_sub _ _
    _ = u2 x ^ gamma + u1 x ^ gamma := by
      rw [abs_of_nonneg hp2_nn, abs_of_nonneg hp1_nn]
    _ ≤ 2 * M ^ gamma := by linarith

/-- The exponential conjugation of the whole-line Green kernel is dominated
by the normalized Laplace probability kernel with residual rate `1-η`. -/
lemma weighted_laplace_kernel_pointwise_le
    {eta : ℝ} (heta_nonneg : 0 ≤ eta) (heta_one : eta < 1)
    (x y s : ℝ) :
    (1 / 2 : ℝ) * Real.exp (eta * x) *
        (Real.exp (-|x - y|) * |s|) ≤
      1 / (1 - eta) * laplaceMarkovKernel (1 - eta) x y *
        |Real.exp (eta * y) * s| := by
  have ha : 0 < 1 - eta := sub_pos.mpr heta_one
  have hxy : x - y ≤ |x - y| := le_abs_self _
  have heta_xy : eta * (x - y) ≤ eta * |x - y| :=
    mul_le_mul_of_nonneg_left hxy heta_nonneg
  have harg : eta * x - |x - y| ≤
      -(1 - eta) * |x - y| + eta * y := by
    linarith
  have hexp : Real.exp (eta * x - |x - y|) ≤
      Real.exp (-(1 - eta) * |x - y| + eta * y) :=
    Real.exp_le_exp.mpr harg
  calc
    (1 / 2 : ℝ) * Real.exp (eta * x) *
          (Real.exp (-|x - y|) * |s|) =
        (1 / 2 : ℝ) * Real.exp (eta * x - |x - y|) * |s| := by
      rw [show eta * x - |x - y| = eta * x + -|x - y| by ring,
        Real.exp_add]
      ring
    _ ≤ (1 / 2 : ℝ) *
          Real.exp (-(1 - eta) * |x - y| + eta * y) * |s| := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp (by norm_num)) (abs_nonneg _)
    _ = 1 / (1 - eta) * laplaceMarkovKernel (1 - eta) x y *
          |Real.exp (eta * y) * s| := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _),
        Real.exp_add]
      unfold laplaceMarkovKernel
      field_simp [ne_of_gt ha]

/-- Pointwise weighted Green-potential domination by the residual-rate
Laplace probability kernel. -/
lemma weighted_Psi_value_pointwise_le
    {eta : ℝ} (heta_nonneg : 0 ≤ eta) (heta_one : eta < 1)
    {s : ℝ → ℝ} (hs : IsCUnifBdd s)
    (hq_sq : Integrable
      (fun y => (Real.exp (eta * y) * s y) ^ 2)) (x : ℝ) :
    |Real.exp (eta * x) * Psi s 1 1 x| ≤
      1 / (1 - eta) *
        ∫ y : ℝ, laplaceMarkovKernel (1 - eta) x y *
          |Real.exp (eta * y) * s y| := by
  have ha : 0 < 1 - eta := sub_pos.mpr heta_one
  let q : ℝ → ℝ := fun y => Real.exp (eta * y) * s y
  have hq_meas : Measurable q := by
    dsimp [q]
    exact ((by fun_prop : Continuous fun y : ℝ => Real.exp (eta * y)).mul hs.1).measurable
  have hsource_int : Integrable
      (fun y : ℝ => Real.exp (-|x - y|) * s y) := by
    simpa [Real.sqrt_one] using
      (Psi_kernel_integrable_of_isCUnifBdd (l := 1) one_pos hs x)
  have hsource_abs_int : Integrable
      (fun y : ℝ => Real.exp (-|x - y|) * |s y|) := by
    have h := hsource_int.norm
    simpa [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using h
  have hmarkov_int : Integrable
      (fun y => laplaceMarkovKernel (1 - eta) x y * |q y|) :=
    laplaceMarkovKernel_mul_abs_integrable ha hq_meas hq_sq x
  have hleft_int : Integrable
      (fun y => (1 / 2 : ℝ) * Real.exp (eta * x) *
        (Real.exp (-|x - y|) * |s y|)) :=
    hsource_abs_int.const_mul ((1 / 2 : ℝ) * Real.exp (eta * x))
  have hright_int : Integrable
      (fun y => 1 / (1 - eta) *
        (laplaceMarkovKernel (1 - eta) x y * |q y|)) :=
    hmarkov_int.const_mul (1 / (1 - eta))
  have habs_integral :
      |∫ y : ℝ, Real.exp (-|x - y|) * s y| ≤
        ∫ y : ℝ, Real.exp (-|x - y|) * |s y| := by
    calc
      |∫ y : ℝ, Real.exp (-|x - y|) * s y| =
          ‖∫ y : ℝ, Real.exp (-|x - y|) * s y‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ ∫ y : ℝ, ‖Real.exp (-|x - y|) * s y‖ :=
        norm_integral_le_integral_norm _
      _ = ∫ y : ℝ, Real.exp (-|x - y|) * |s y| := by
        apply integral_congr_ae
        filter_upwards with y
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    |Real.exp (eta * x) * Psi s 1 1 x| =
        (1 / 2 : ℝ) * Real.exp (eta * x) *
          |∫ y : ℝ, Real.exp (-|x - y|) * s y| := by
      unfold Psi
      simp only [Real.sqrt_one, mul_one]
      rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      ring
    _ ≤ (1 / 2 : ℝ) * Real.exp (eta * x) *
          ∫ y : ℝ, Real.exp (-|x - y|) * |s y| := by
      exact mul_le_mul_of_nonneg_left habs_integral
        (mul_nonneg (by norm_num) (Real.exp_nonneg _))
    _ = ∫ y : ℝ, (1 / 2 : ℝ) * Real.exp (eta * x) *
          (Real.exp (-|x - y|) * |s y|) := by
      rw [integral_const_mul]
    _ ≤ ∫ y : ℝ, 1 / (1 - eta) *
          (laplaceMarkovKernel (1 - eta) x y * |q y|) := by
      exact integral_mono hleft_int hright_int fun y => by
        simpa [q, mul_assoc] using
          weighted_laplace_kernel_pointwise_le heta_nonneg heta_one x y (s y)
    _ = 1 / (1 - eta) *
          ∫ y : ℝ, laplaceMarkovKernel (1 - eta) x y * |q y| := by
      rw [integral_const_mul]
    _ = 1 / (1 - eta) *
          ∫ y : ℝ, laplaceMarkovKernel (1 - eta) x y *
            |Real.exp (eta * y) * s y| := by
      rfl

/-- Weighted `L²` resolvent estimate for a signed bounded source.  This is the
value half of the paper's Lemma 5.3, before applying the power Lipschitz bound. -/
theorem weighted_Psi_value_l2_bound
    {eta : ℝ} (heta_nonneg : 0 ≤ eta) (heta_one : eta < 1)
    {s : ℝ → ℝ} (hs : IsCUnifBdd s)
    (hq_sq : Integrable
      (fun y => (Real.exp (eta * y) * s y) ^ 2)) :
    Integrable
        (fun x => |Real.exp (eta * x) * Psi s 1 1 x| ^ 2) ∧
      (∫ x : ℝ, |Real.exp (eta * x) * Psi s 1 1 x| ^ 2) ≤
        1 / (1 - eta) ^ 2 *
          ∫ y : ℝ, (Real.exp (eta * y) * s y) ^ 2 := by
  have ha : 0 < 1 - eta := sub_pos.mpr heta_one
  let q : ℝ → ℝ := fun y => Real.exp (eta * y) * s y
  let T : ℝ → ℝ := fun x =>
    ∫ y : ℝ, laplaceMarkovKernel (1 - eta) x y * |q y|
  have hq_meas : Measurable q := by
    dsimp [q]
    exact ((by fun_prop : Continuous fun y : ℝ => Real.exp (eta * y)).mul hs.1).measurable
  have hT_contract := laplaceMarkovKernel_l2_contraction ha hq_meas hq_sq
  have hT_sq_int : Integrable (fun x => T x ^ 2) := by
    simpa [T] using hT_contract.1
  have hT_sq_le : (∫ x : ℝ, T x ^ 2) ≤ ∫ y : ℝ, q y ^ 2 := by
    simpa [T] using hT_contract.2
  have hc_nonneg : 0 ≤ 1 / (1 - eta) := by positivity
  have hV_cont : Continuous (fun x => Real.exp (eta * x) * Psi s 1 1 x) :=
    (by fun_prop : Continuous fun x : ℝ => Real.exp (eta * x)).mul
      (Psi_continuous one_pos one_pos hs)
  have hdom_int : Integrable
      (fun x => (1 / (1 - eta)) ^ 2 * T x ^ 2) :=
    hT_sq_int.const_mul ((1 / (1 - eta)) ^ 2)
  have hpoint : ∀ x,
      |Real.exp (eta * x) * Psi s 1 1 x| ^ 2 ≤
        (1 / (1 - eta)) ^ 2 * T x ^ 2 := by
    intro x
    have hT_nonneg : 0 ≤ T x := by
      dsimp [T]
      exact integral_nonneg fun y =>
        mul_nonneg (laplaceMarkovKernel_nonneg ha.le x y) (abs_nonneg _)
    have hraw := weighted_Psi_value_pointwise_le
      heta_nonneg heta_one hs hq_sq x
    have hraw' : |Real.exp (eta * x) * Psi s 1 1 x| ≤
        (1 / (1 - eta)) * T x := by
      simpa [q, T] using hraw
    have hsquare := (sq_le_sq₀
      (abs_nonneg (Real.exp (eta * x) * Psi s 1 1 x))
      (mul_nonneg hc_nonneg hT_nonneg)).mpr hraw'
    simpa [mul_pow] using hsquare
  have hV_sq_int : Integrable
      (fun x => |Real.exp (eta * x) * Psi s 1 1 x| ^ 2) := by
    refine Integrable.mono' hdom_int (hV_cont.abs.pow 2).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpoint x
  refine ⟨hV_sq_int, ?_⟩
  calc
    (∫ x : ℝ, |Real.exp (eta * x) * Psi s 1 1 x| ^ 2) ≤
        ∫ x : ℝ, (1 / (1 - eta)) ^ 2 * T x ^ 2 :=
      integral_mono hV_sq_int hdom_int hpoint
    _ = (1 / (1 - eta)) ^ 2 * ∫ x : ℝ, T x ^ 2 := by
      rw [integral_const_mul]
    _ ≤ (1 / (1 - eta)) ^ 2 * ∫ y : ℝ, q y ^ 2 :=
      mul_le_mul_of_nonneg_left hT_sq_le (sq_nonneg _)
    _ = 1 / (1 - eta) ^ 2 *
          ∫ y : ℝ, (Real.exp (eta * y) * s y) ^ 2 := by
      dsimp [q]
      field_simp [ne_of_gt ha]

/-- The kernel splitting formula does not need a sign assumption on the
source.  The older public lemma carries such an assumption although its proof
never uses it; this signed version exposes the actual analytic statement. -/
theorem Psi_kernel_splitting_signed {u : ℝ → ℝ}
    (hu : IsCUnifBdd u) (x : ℝ) :
    Psi u 1 1 x =
      1 / 2 * (Real.exp (-1 * x) *
          (∫ y in Set.Iic x, Real.exp (1 * y) * u y) +
        Real.exp (1 * x) *
          (∫ y in Set.Ioi x, Real.exp (-1 * y) * u y)) := by
  let A : ℝ :=
    Real.exp (-1 * x) * (∫ y in Set.Iic x, Real.exp (1 * y) * u y)
  let B : ℝ :=
    Real.exp (1 * x) * (∫ y in Set.Ioi x, Real.exp (-1 * y) * u y)
  obtain ⟨M, hMbound⟩ := hu.2
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg (u 0)) (hMbound 0)
  have hiu : Integrable
      (fun y : ℝ => Real.exp (-Real.sqrt (1 : ℝ) * |x - y|) * u y) :=
    psi_kernel_mul_bounded_integrable (by norm_num : (0 : ℝ) < 1)
      hM_nonneg hMbound x hu.1.aestronglyMeasurable
  have hkernel_split :
      (∫ y : ℝ, Real.exp (-Real.sqrt (1 : ℝ) * |x - y|) * u y) = A + B := by
    have hsplit :=
      MeasureTheory.integral_add_compl (s := Set.Iic x) measurableSet_Iic hiu
    simp only [Set.compl_Iic] at hsplit
    have hleft :
        ∫ y in Set.Iic x,
            Real.exp (-Real.sqrt (1 : ℝ) * |x - y|) * u y = A := by
      have hleft_eq : Set.EqOn
          (fun y : ℝ => Real.exp (-Real.sqrt (1 : ℝ) * |x - y|) * u y)
          (fun y : ℝ => Real.exp (-1 * x) * (Real.exp (1 * y) * u y))
          (Set.Iic x) := by
        intro y hy
        have hyx : y ≤ x := by simpa using hy
        change Real.exp (-Real.sqrt (1 : ℝ) * |x - y|) * u y =
          Real.exp (-1 * x) * (Real.exp (1 * y) * u y)
        rw [Real.sqrt_one, abs_of_nonneg (sub_nonneg.mpr hyx),
          show -1 * (x - y) = -1 * x + 1 * y by ring, Real.exp_add]
        ring
      calc
        ∫ y in Set.Iic x,
              Real.exp (-Real.sqrt (1 : ℝ) * |x - y|) * u y =
            ∫ y in Set.Iic x,
              Real.exp (-1 * x) * (Real.exp (1 * y) * u y) := by
          exact MeasureTheory.setIntegral_congr_fun measurableSet_Iic hleft_eq
        _ = Real.exp (-1 * x) *
              ∫ y in Set.Iic x, Real.exp (1 * y) * u y := by
          rw [integral_const_mul]
        _ = A := rfl
    have hright :
        ∫ y in Set.Ioi x,
            Real.exp (-Real.sqrt (1 : ℝ) * |x - y|) * u y = B := by
      have hright_eq : Set.EqOn
          (fun y : ℝ => Real.exp (-Real.sqrt (1 : ℝ) * |x - y|) * u y)
          (fun y : ℝ => Real.exp (1 * x) * (Real.exp (-1 * y) * u y))
          (Set.Ioi x) := by
        intro y hy
        have hxy : x < y := by simpa using hy
        change Real.exp (-Real.sqrt (1 : ℝ) * |x - y|) * u y =
          Real.exp (1 * x) * (Real.exp (-1 * y) * u y)
        rw [Real.sqrt_one, abs_of_nonpos (sub_nonpos.mpr (le_of_lt hxy)),
          show -1 * -(x - y) = 1 * x + -1 * y by ring, Real.exp_add]
        ring
      calc
        ∫ y in Set.Ioi x,
              Real.exp (-Real.sqrt (1 : ℝ) * |x - y|) * u y =
            ∫ y in Set.Ioi x,
              Real.exp (1 * x) * (Real.exp (-1 * y) * u y) := by
          exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hright_eq
        _ = Real.exp (1 * x) *
              ∫ y in Set.Ioi x, Real.exp (-1 * y) * u y := by
          rw [integral_const_mul]
        _ = B := rfl
    calc
      ∫ y : ℝ, Real.exp (-Real.sqrt (1 : ℝ) * |x - y|) * u y =
          (∫ y in Set.Iic x,
              Real.exp (-Real.sqrt (1 : ℝ) * |x - y|) * u y) +
            ∫ y in Set.Ioi x,
              Real.exp (-Real.sqrt (1 : ℝ) * |x - y|) * u y := hsplit.symm
      _ = A + B := by rw [hleft, hright]
  unfold Psi
  rw [hkernel_split]
  dsimp only [A, B]
  simp only [Real.sqrt_one]
  ring

lemma leftExpMarkovKernel_weighted_source_integral
    (eta x : ℝ) (s : ℝ → ℝ) :
    (∫ y : ℝ, leftExpMarkovKernel (1 - eta) x y *
        (Real.exp (eta * y) * s y)) =
      (1 - eta) * Real.exp (-(1 - eta) * x) *
        ∫ y in Set.Iic x, Real.exp (1 * y) * s y := by
  let base : ℝ → ℝ := fun y =>
    (1 - eta) * Real.exp (-(1 - eta) * (x - y)) *
      (Real.exp (eta * y) * s y)
  have hfun : (fun y => leftExpMarkovKernel (1 - eta) x y *
      (Real.exp (eta * y) * s y)) = (Set.Iio x).indicator base := by
    funext y
    simp [leftExpMarkovKernel, base, Set.indicator]
  rw [hfun, integral_indicator measurableSet_Iio,
    ← MeasureTheory.integral_Iic_eq_integral_Iio]
  have heq : base = fun y =>
      ((1 - eta) * Real.exp (-(1 - eta) * x)) *
        (Real.exp (1 * y) * s y) := by
    funext y
    dsimp [base]
    rw [show -(1 - eta) * (x - y) =
        -(1 - eta) * x + (1 - eta) * y by ring, Real.exp_add]
    calc
      (1 - eta) *
          (Real.exp (-(1 - eta) * x) * Real.exp ((1 - eta) * y)) *
          (Real.exp (eta * y) * s y) =
          ((1 - eta) * Real.exp (-(1 - eta) * x)) *
            ((Real.exp ((1 - eta) * y) * Real.exp (eta * y)) * s y) := by
        ring
      _ = ((1 - eta) * Real.exp (-(1 - eta) * x)) *
            (Real.exp (1 * y) * s y) := by
        rw [← Real.exp_add]
        congr 3
        ring
  rw [heq, integral_const_mul]

lemma rightExpMarkovKernel_weighted_source_integral
    (eta x : ℝ) (s : ℝ → ℝ) :
    (∫ y : ℝ, rightExpMarkovKernel (1 + eta) x y *
        (Real.exp (eta * y) * s y)) =
      (1 + eta) * Real.exp ((1 + eta) * x) *
        ∫ y in Set.Ioi x, Real.exp (-1 * y) * s y := by
  let base : ℝ → ℝ := fun y =>
    (1 + eta) * Real.exp (-(1 + eta) * (y - x)) *
      (Real.exp (eta * y) * s y)
  have hfun : (fun y => rightExpMarkovKernel (1 + eta) x y *
      (Real.exp (eta * y) * s y)) = (Set.Ioi x).indicator base := by
    funext y
    simp [rightExpMarkovKernel, leftExpMarkovKernel, base, Set.indicator]
  rw [hfun, integral_indicator measurableSet_Ioi]
  have heq : base = fun y =>
      ((1 + eta) * Real.exp ((1 + eta) * x)) *
        (Real.exp (-1 * y) * s y) := by
    funext y
    dsimp [base]
    rw [show -(1 + eta) * (y - x) =
        (1 + eta) * x + -(1 + eta) * y by ring, Real.exp_add]
    calc
      (1 + eta) *
          (Real.exp ((1 + eta) * x) * Real.exp (-(1 + eta) * y)) *
          (Real.exp (eta * y) * s y) =
          ((1 + eta) * Real.exp ((1 + eta) * x)) *
            ((Real.exp (-(1 + eta) * y) * Real.exp (eta * y)) * s y) := by
        ring
      _ = ((1 + eta) * Real.exp ((1 + eta) * x)) *
            (Real.exp (-1 * y) * s y) := by
        rw [← Real.exp_add]
        congr 3
        ring
  rw [heq, integral_const_mul]

/-- Exact conjugated derivative formula.  The two pieces are normalized
one-sided exponential probability kernels, so each is an `L²` contraction. -/
theorem weighted_Psi_deriv_eq_markov
    (eta : ℝ) {s : ℝ → ℝ} (hs : IsCUnifBdd s) (x : ℝ) :
    deriv (fun z => Real.exp (eta * z) * Psi s 1 1 z) x =
      -(1 / 2 : ℝ) *
          (∫ y : ℝ, leftExpMarkovKernel (1 - eta) x y *
            (Real.exp (eta * y) * s y)) +
        (1 / 2 : ℝ) *
          (∫ y : ℝ, rightExpMarkovKernel (1 + eta) x y *
            (Real.exp (eta * y) * s y)) := by
  let L : ℝ := ∫ y in Set.Iic x, Real.exp (1 * y) * s y
  let R : ℝ := ∫ y in Set.Ioi x, Real.exp (-1 * y) * s y
  have hexp : HasDerivAt (fun z : ℝ => Real.exp (eta * z))
      (eta * Real.exp (eta * x)) x := by
    simpa only [id_eq, mul_one, one_mul, mul_comm] using
      (((hasDerivAt_id x).const_mul eta).exp)
  have hpsiDiff : DifferentiableAt ℝ (fun z => Psi s 1 1 z) x :=
    (Psi_differentiable one_pos one_pos hs) x
  have hprod := hexp.mul hpsiDiff.hasDerivAt
  have hprod_deriv :
      deriv (fun z => Real.exp (eta * z) * Psi s 1 1 z) x =
        eta * Real.exp (eta * x) * Psi s 1 1 x +
          Real.exp (eta * x) * deriv (fun z => Psi s 1 1 z) x := by
    exact hprod.deriv
  have hpsi := Psi_kernel_splitting_signed hs x
  have hpsi' := Psi_derivative_formula_general
    (u := s) (l := 1) (mu := 1) one_pos one_pos hs x
  simp only [Real.sqrt_one] at hpsi'
  have hexp_left : Real.exp (eta * x) * Real.exp (-1 * x) =
      Real.exp ((eta - 1) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexp_right : Real.exp (eta * x) * Real.exp (1 * x) =
      Real.exp ((eta + 1) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hderLR :
      deriv (fun z => Real.exp (eta * z) * Psi s 1 1 z) x =
        ((eta - 1) / 2) * Real.exp ((eta - 1) * x) * L +
          ((eta + 1) / 2) * Real.exp ((eta + 1) * x) * R := by
    rw [hprod_deriv, hpsi, hpsi']
    dsimp only [L, R]
    rw [← hexp_left, ← hexp_right]
    ring
  rw [hderLR,
    leftExpMarkovKernel_weighted_source_integral eta x s,
    rightExpMarkovKernel_weighted_source_integral eta x s]
  rw [show -(1 - eta) * x = (eta - 1) * x by ring,
    show (1 + eta) * x = (eta + 1) * x by ring]
  ring

/-- Weighted `L²` estimate for the derivative of the conjugated resolvent.
The constant `1` is stronger than the paper's `1/(1-η²)` constant. -/
theorem weighted_Psi_deriv_l2_bound
    {eta : ℝ} (heta_pos : 0 < eta) (heta_one : eta < 1)
    {s : ℝ → ℝ} (hs : IsCUnifBdd s)
    (hq_sq : Integrable
      (fun y => (Real.exp (eta * y) * s y) ^ 2)) :
    Integrable
        (fun x =>
          |deriv (fun z => Real.exp (eta * z) * Psi s 1 1 z) x| ^ 2) ∧
      (∫ x : ℝ,
          |deriv (fun z => Real.exp (eta * z) * Psi s 1 1 z) x| ^ 2) ≤
        ∫ y : ℝ, (Real.exp (eta * y) * s y) ^ 2 := by
  have ha : 0 < 1 - eta := sub_pos.mpr heta_one
  have hb : 0 < 1 + eta := by linarith
  let q : ℝ → ℝ := fun y => Real.exp (eta * y) * s y
  let A : ℝ → ℝ := fun x =>
    ∫ y : ℝ, leftExpMarkovKernel (1 - eta) x y * q y
  let B : ℝ → ℝ := fun x =>
    ∫ y : ℝ, rightExpMarkovKernel (1 + eta) x y * q y
  let AL : ℝ → ℝ := fun x =>
    ∫ y : ℝ, leftExpMarkovKernel (1 - eta) x y * |q y|
  let BR : ℝ → ℝ := fun x =>
    ∫ y : ℝ, rightExpMarkovKernel (1 + eta) x y * |q y|
  have hq_meas : Measurable q := by
    dsimp [q]
    exact ((by fun_prop : Continuous fun y : ℝ => Real.exp (eta * y)).mul hs.1).measurable
  have hAL_contract := leftExpMarkovKernel_l2_contraction ha hq_meas hq_sq
  have hBR_contract := rightExpMarkovKernel_l2_contraction hb hq_meas hq_sq
  have hAL_sq_int : Integrable (fun x => AL x ^ 2) := by
    simpa [AL] using hAL_contract.1
  have hBR_sq_int : Integrable (fun x => BR x ^ 2) := by
    simpa [BR] using hBR_contract.1
  have hAL_sq_le : (∫ x : ℝ, AL x ^ 2) ≤ ∫ y : ℝ, q y ^ 2 := by
    simpa [AL] using hAL_contract.2
  have hBR_sq_le : (∫ x : ℝ, BR x ^ 2) ≤ ∫ y : ℝ, q y ^ 2 := by
    simpa [BR] using hBR_contract.2
  have hA_strong : StronglyMeasurable A := by
    apply StronglyMeasurable.integral_prod_right
    have hmeas : Measurable (Function.uncurry
        (fun x y => leftExpMarkovKernel (1 - eta) x y * q y)) :=
      (leftExpMarkovKernel_measurable (1 - eta)).mul
        (hq_meas.comp measurable_snd)
    exact hmeas.stronglyMeasurable
  have hB_strong : StronglyMeasurable B := by
    apply StronglyMeasurable.integral_prod_right
    have hmeas : Measurable (Function.uncurry
        (fun x y => rightExpMarkovKernel (1 + eta) x y * q y)) :=
      (rightExpMarkovKernel_measurable (1 + eta)).mul
        (hq_meas.comp measurable_snd)
    exact hmeas.stronglyMeasurable
  have hA_abs : ∀ x, |A x| ≤ AL x := by
    intro x
    calc
      |A x| = ‖∫ y : ℝ, leftExpMarkovKernel (1 - eta) x y * q y‖ := by
        rw [Real.norm_eq_abs]
      _ ≤ ∫ y : ℝ, ‖leftExpMarkovKernel (1 - eta) x y * q y‖ :=
        norm_integral_le_integral_norm _
      _ = AL x := by
        dsimp [AL]
        apply integral_congr_ae
        filter_upwards with y
        rw [abs_mul,
          abs_of_nonneg (leftExpMarkovKernel_nonneg ha.le x y)]
  have hB_abs : ∀ x, |B x| ≤ BR x := by
    intro x
    calc
      |B x| = ‖∫ y : ℝ, rightExpMarkovKernel (1 + eta) x y * q y‖ := by
        rw [Real.norm_eq_abs]
      _ ≤ ∫ y : ℝ, ‖rightExpMarkovKernel (1 + eta) x y * q y‖ :=
        norm_integral_le_integral_norm _
      _ = BR x := by
        dsimp [BR]
        apply integral_congr_ae
        filter_upwards with y
        rw [abs_mul]
        have hK : 0 ≤ rightExpMarkovKernel (1 + eta) x y :=
          leftExpMarkovKernel_nonneg hb.le y x
        rw [abs_of_nonneg hK]
  have hder_eq : ∀ x,
      deriv (fun z => Real.exp (eta * z) * Psi s 1 1 z) x =
        -(1 / 2 : ℝ) * A x + (1 / 2 : ℝ) * B x := by
    intro x
    simpa [A, B, q] using weighted_Psi_deriv_eq_markov eta hs x
  have hder_strong : AEStronglyMeasurable
      (fun x => deriv (fun z => Real.exp (eta * z) * Psi s 1 1 z) x) := by
    have hR : StronglyMeasurable
        (fun x => -(1 / 2 : ℝ) * A x + (1 / 2 : ℝ) * B x) :=
      (hA_strong.const_mul _).add (hB_strong.const_mul _)
    exact hR.aestronglyMeasurable.congr
      (Filter.Eventually.of_forall fun x => (hder_eq x).symm)
  have hAL_nonneg : ∀ x, 0 ≤ AL x := fun x => by
    dsimp [AL]
    exact integral_nonneg fun y =>
      mul_nonneg (leftExpMarkovKernel_nonneg ha.le x y) (abs_nonneg _)
  have hBR_nonneg : ∀ x, 0 ≤ BR x := fun x => by
    dsimp [BR]
    exact integral_nonneg fun y =>
      mul_nonneg (leftExpMarkovKernel_nonneg hb.le y x) (abs_nonneg _)
  have hpoint : ∀ x,
      |deriv (fun z => Real.exp (eta * z) * Psi s 1 1 z) x| ^ 2 ≤
        (1 / 2 : ℝ) * AL x ^ 2 + (1 / 2 : ℝ) * BR x ^ 2 := by
    intro x
    have habs :
        |deriv (fun z => Real.exp (eta * z) * Psi s 1 1 z) x| ≤
          (AL x + BR x) / 2 := by
      rw [hder_eq x]
      calc
        |-(1 / 2 : ℝ) * A x + (1 / 2 : ℝ) * B x| ≤
            |-(1 / 2 : ℝ) * A x| + |(1 / 2 : ℝ) * B x| := abs_add_le _ _
        _ = (1 / 2 : ℝ) * |A x| + (1 / 2 : ℝ) * |B x| := by
          rw [abs_mul, abs_mul]
          norm_num
        _ ≤ (1 / 2 : ℝ) * AL x + (1 / 2 : ℝ) * BR x := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (hA_abs x) (by norm_num))
            (mul_le_mul_of_nonneg_left (hB_abs x) (by norm_num))
        _ = (AL x + BR x) / 2 := by ring
    have hright_nn : 0 ≤ (AL x + BR x) / 2 :=
      div_nonneg (add_nonneg (hAL_nonneg x) (hBR_nonneg x)) (by norm_num)
    have hsquare := (sq_le_sq₀ (abs_nonneg _) hright_nn).mpr habs
    calc
      |deriv (fun z => Real.exp (eta * z) * Psi s 1 1 z) x| ^ 2 ≤
          ((AL x + BR x) / 2) ^ 2 := hsquare
      _ ≤ (1 / 2 : ℝ) * AL x ^ 2 + (1 / 2 : ℝ) * BR x ^ 2 := by
        nlinarith [sq_nonneg (AL x - BR x)]
  have hdom_int : Integrable
      (fun x => (1 / 2 : ℝ) * AL x ^ 2 + (1 / 2 : ℝ) * BR x ^ 2) :=
    (hAL_sq_int.const_mul (1 / 2)).add (hBR_sq_int.const_mul (1 / 2))
  have hder_sq_int : Integrable
      (fun x =>
        |deriv (fun z => Real.exp (eta * z) * Psi s 1 1 z) x| ^ 2) := by
    have hder_sq_meas : AEStronglyMeasurable
        (fun x =>
          |deriv (fun z => Real.exp (eta * z) * Psi s 1 1 z) x| ^ 2) := by
      simpa only [Pi.pow_apply, Real.norm_eq_abs] using hder_strong.norm.pow 2
    refine Integrable.mono' hdom_int hder_sq_meas ?_
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpoint x
  refine ⟨hder_sq_int, ?_⟩
  calc
    (∫ x : ℝ,
        |deriv (fun z => Real.exp (eta * z) * Psi s 1 1 z) x| ^ 2) ≤
        ∫ x : ℝ,
          ((1 / 2 : ℝ) * AL x ^ 2 + (1 / 2 : ℝ) * BR x ^ 2) :=
      integral_mono hder_sq_int hdom_int hpoint
    _ = (1 / 2 : ℝ) * (∫ x : ℝ, AL x ^ 2) +
          (1 / 2 : ℝ) * (∫ x : ℝ, BR x ^ 2) := by
      rw [integral_add (hAL_sq_int.const_mul (1 / 2))
        (hBR_sq_int.const_mul (1 / 2)), integral_const_mul,
        integral_const_mul]
    _ ≤ ∫ y : ℝ, q y ^ 2 := by linarith
    _ = ∫ y : ℝ, (Real.exp (eta * y) * s y) ^ 2 := by rfl

/-- Full arbitrary-pair proof of the paper's Lemma 5.3.  Unlike the older
same-power branches, this derives both estimates for genuinely distinct
profiles from the Green kernel. -/
theorem Lemma_5_3_proved : Lemma_5_3 := by
  intro gamma M eta hgamma hM heta_pos heta_one
  intro u1 u2 hu1 hu2 hu1_bounds hu2_bounds hclose
  dsimp only
  let s : ℝ → ℝ := fun x => u2 x ^ gamma - u1 x ^ gamma
  let q : ℝ → ℝ := fun x => Real.exp (eta * x) * s x
  let L : ℝ := gamma * M ^ (gamma - 1)
  have hM_nonneg : 0 ≤ M := le_trans zero_le_one hM
  have hu1_mem : ∀ x, u1 x ∈ Set.Icc (0 : ℝ) M := hu1_bounds
  have hu2_mem : ∀ x, u2 x ∈ Set.Icc (0 : ℝ) M := hu2_bounds
  have hs : IsCUnifBdd s := by
    dsimp [s]
    exact rpow_difference_isCUnifBdd hgamma hu1 hu2 hu1_mem hu2_mem
  have hq_data := weighted_power_difference_sq_integrable_and_bound
    hgamma hM_nonneg hu1 hu2 hu1_mem hu2_mem hclose
  have hq_sq : Integrable (fun x => q x ^ 2) := by
    simpa [q, s] using hq_data.1
  have hq_bound : (∫ x : ℝ, q x ^ 2) ≤ L ^ 2 *
      ∫ x : ℝ, Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2 := by
    simpa [q, s, L] using hq_data.2
  have hL_sq : L ^ 2 = gamma ^ 2 * M ^ (2 * (gamma - 1)) := by
    dsimp [L]
    calc
      (gamma * M ^ (gamma - 1)) ^ 2 =
          gamma ^ 2 * (M ^ (gamma - 1)) ^ 2 := by ring
      _ = gamma ^ 2 * M ^ ((gamma - 1) * (2 : ℝ)) := by
        rw [Real.rpow_mul hM_nonneg, Real.rpow_two]
      _ = gamma ^ 2 * M ^ (2 * (gamma - 1)) := by
        congr 2
        ring
  have hU_sq : ∀ x,
      |Real.exp (eta * x) * (u2 x - u1 x)| ^ 2 =
        Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2 := by
    intro x
    rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_pow,
      show Real.exp (eta * x) ^ 2 = Real.exp (2 * eta * x) by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring]
  have hU_integral :
      (∫ x : ℝ, |Real.exp (eta * x) * (u2 x - u1 x)| ^ 2) =
        ∫ x : ℝ, Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2 := by
    exact integral_congr_ae (Filter.Eventually.of_forall hU_sq)
  have hvalue := weighted_Psi_value_l2_bound
    heta_pos.le heta_one hs hq_sq
  have hderiv := weighted_Psi_deriv_l2_bound heta_pos heta_one hs hq_sq
  have hinput_nonneg :
      0 ≤ ∫ x : ℝ, Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2 :=
    integral_nonneg fun x => mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)
  have hsource_budget_nonneg : 0 ≤ L ^ 2 *
      ∫ x : ℝ, Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2 :=
    mul_nonneg (sq_nonneg _) hinput_nonneg
  constructor
  · calc
      (∫ x : ℝ,
          |Real.exp (eta * x) * Psi s 1 1 x| ^ 2) ≤
          1 / (1 - eta) ^ 2 * ∫ x : ℝ, q x ^ 2 := by
        simpa [q, s] using hvalue.2
      _ ≤ 1 / (1 - eta) ^ 2 *
          (L ^ 2 *
            ∫ x : ℝ, Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2) :=
        mul_le_mul_of_nonneg_left hq_bound (by positivity)
      _ = gamma ^ 2 * M ^ (2 * (gamma - 1)) / (1 - eta) ^ 2 *
          ∫ x : ℝ, |Real.exp (eta * x) * (u2 x - u1 x)| ^ 2 := by
        rw [hL_sq, hU_integral]
        ring
  · have hd_pos : 0 < 1 - eta ^ 2 := by nlinarith [sq_nonneg (eta - 1)]
    have hd_le_one : 1 - eta ^ 2 ≤ 1 := by nlinarith [sq_nonneg eta]
    have hone_le : 1 ≤ 1 / (1 - eta ^ 2) :=
      one_le_one_div hd_pos hd_le_one
    calc
      (∫ x : ℝ,
          |deriv (fun z => Real.exp (eta * z) * Psi s 1 1 z) x| ^ 2) ≤
          ∫ x : ℝ, q x ^ 2 := by
        simpa [q, s] using hderiv.2
      _ ≤ L ^ 2 *
          ∫ x : ℝ, Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2 :=
        hq_bound
      _ ≤ (1 / (1 - eta ^ 2)) *
          (L ^ 2 *
            ∫ x : ℝ, Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2) := by
        exact le_mul_of_one_le_left hsource_budget_nonneg hone_le
      _ = gamma ^ 2 * M ^ (2 * (gamma - 1)) / (1 - eta ^ 2) *
          ∫ x : ℝ, |Real.exp (eta * x) * (u2 x - u1 x)| ^ 2 := by
        rw [hL_sq, hU_integral]
        ring

section Lemma53AxiomAudit
#print axioms Lemma_5_3_proved
end Lemma53AxiomAudit

end ShenWork.Paper1
