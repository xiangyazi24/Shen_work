import ShenWork.Paper1.WholeLineChiLargeWeightedL2Smoothing
import ShenWork.Paper1.WholeLineChiLargeLpGradientSmoothing

/-!
# Weighted `L^(4/3) -> L∞` heat-gradient smoothing

For the normalized critical equation the admissible local moment can be fixed
at `P = 4/3` throughout the strict range `chi < 4`.  Its Hölder conjugate is
`4`; the derivative heat-kernel norm then has the integrable singularity
`t^(-7/8)`.  The translated exponential weight is split in the proportions
`3/4` and `1/4`, so the source weight raised to `4/3` is exactly the original
localizing weight.
-/

open Filter MeasureTheory Real Set
open scoped ENNReal

noncomputable section

namespace ShenWork.Paper1

/-- Exact upper bound used for the weighted `L⁴` norm of a translated heat
kernel derivative row. -/
def wholeLineWeightedHeatDerivL4NormBound (t rho : ℝ) : ℝ :=
  (wholeLineWeightedHeatDerivL2PointConstant t rho ^ 2 *
    Real.sqrt (Real.pi / (1 / (8 * t)))) ^ (1 / 4 : ℝ)

/-- The fourth power of the weighted derivative row is integrable and is
controlled by the square of the existing point constant. -/
theorem weighted_heatKernel_deriv_four_integrable_and_bound
    {t rho : ℝ} (ht : 0 < t) (hrho : 0 ≤ rho) (x : ℝ) :
    Integrable (fun y : ℝ =>
      ‖deriv (fun z : ℝ => heatKernel t (z - y)) x *
        wholeLineChiLargeKernelHalfWeight rho x y‖ ^ (4 : ℝ)) ∧
      (∫ y : ℝ,
        ‖deriv (fun z : ℝ => heatKernel t (z - y)) x *
          wholeLineChiLargeKernelHalfWeight rho x y‖ ^ (4 : ℝ)) ≤
        wholeLineWeightedHeatDerivL2PointConstant t rho ^ 2 *
          Real.sqrt (Real.pi / (1 / (8 * t))) := by
  let A : ℝ → ℝ := fun y =>
    deriv (fun z : ℝ => heatKernel t (z - y)) x *
      wholeLineChiLargeKernelHalfWeight rho x y
  let C : ℝ := wholeLineWeightedHeatDerivL2PointConstant t rho
  have hC : 0 ≤ C := wholeLineWeightedHeatDerivL2PointConstant_nonneg t rho
  have hA2int : Integrable (fun y : ℝ => ‖A y‖ ^ (2 : ℝ)) := by
    simpa [A] using weighted_heatKernel_deriv_sq_integrable ht hrho x
  have hmajor : Integrable (fun y : ℝ => C * ‖A y‖ ^ (2 : ℝ)) :=
    hA2int.const_mul C
  have hA2point : ∀ y, ‖A y‖ ^ (2 : ℝ) ≤ C := by
    intro y
    have hraw := weighted_heatKernel_deriv_sq_pointwise ht hrho x y
    have hexp : Real.exp (-(x - y) ^ 2 / (8 * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (sq_nonneg (x - y))) (by positivity)
    have hmul := mul_le_mul_of_nonneg_left hexp hC
    simpa [A, C, Real.rpow_natCast] using hraw.trans hmul
  have hpoint : ∀ y, ‖A y‖ ^ (4 : ℝ) ≤ C * ‖A y‖ ^ (2 : ℝ) := by
    intro y
    have hA20 : 0 ≤ ‖A y‖ ^ (2 : ℝ) :=
      Real.rpow_nonneg (norm_nonneg _) _
    have hmul := mul_le_mul_of_nonneg_right (hA2point y) hA20
    rw [show (4 : ℝ) = (2 : ℝ) + 2 by norm_num,
      Real.rpow_add_of_nonneg (norm_nonneg _) (by norm_num) (by norm_num)]
    simpa [mul_comm] using hmul
  have hA4int : Integrable (fun y : ℝ => ‖A y‖ ^ (4 : ℝ)) := by
    refine hmajor.mono' ?_ ?_
    · have hAcont : Continuous A := by
        have hderivCont : Continuous (fun y : ℝ =>
            deriv (fun z : ℝ => heatKernel t (z - y)) x) := by
          have hbase :=
            ShenWork.IntervalNeumannFullKernel.continuous_deriv_heatKernel ht
          have heq : (fun y : ℝ =>
              deriv (fun z : ℝ => heatKernel t (z - y)) x) =
                fun y : ℝ => deriv (fun z : ℝ => heatKernel t z) (x - y) := by
            funext y
            rw [deriv_heatKernel_translated_left ht x y,
              deriv_heatKernel ht (x - y)]
          rw [heq]
          exact hbase.comp (continuous_const.sub continuous_id)
        apply hderivCont.mul
        unfold wholeLineChiLargeKernelHalfWeight
        exact Real.continuous_exp.comp
          (continuous_const.mul
            (contDiff_two_regDist.continuous.comp
              (continuous_id.sub continuous_const)))
      exact (hAcont.norm.rpow_const
        (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 4))).aestronglyMeasurable
    · filter_upwards [] with y
      rw [Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) 4)]
      exact hpoint y
  have hA2bound := weighted_heatKernel_deriv_sq_integral_le ht hrho x
  refine ⟨by simpa [A] using hA4int, ?_⟩
  calc
    (∫ y : ℝ, ‖A y‖ ^ (4 : ℝ)) ≤
        ∫ y : ℝ, C * ‖A y‖ ^ (2 : ℝ) :=
      integral_mono hA4int hmajor hpoint
    _ = C * ∫ y : ℝ, ‖A y‖ ^ (2 : ℝ) := by
      rw [integral_const_mul]
    _ ≤ C * (C * Real.sqrt (Real.pi / (1 / (8 * t)))) :=
      mul_le_mul_of_nonneg_left (by simpa [A, C] using hA2bound) hC
    _ = C ^ 2 * Real.sqrt (Real.pi / (1 / (8 * t))) := by ring_nf

theorem weighted_heatKernel_deriv_memLp_four
    {t rho : ℝ} (ht : 0 < t) (hrho : 0 ≤ rho) (x : ℝ) :
    MemLp (fun y : ℝ =>
      deriv (fun z : ℝ => heatKernel t (z - y)) x *
        wholeLineChiLargeKernelHalfWeight rho x y)
      (ENNReal.ofReal 4) volume := by
  let A : ℝ → ℝ := fun y =>
    deriv (fun z : ℝ => heatKernel t (z - y)) x *
      wholeLineChiLargeKernelHalfWeight rho x y
  have hAcont : Continuous A := by
    have hderivCont : Continuous (fun y : ℝ =>
        deriv (fun z : ℝ => heatKernel t (z - y)) x) := by
      have hbase :=
        ShenWork.IntervalNeumannFullKernel.continuous_deriv_heatKernel ht
      have heq : (fun y : ℝ =>
          deriv (fun z : ℝ => heatKernel t (z - y)) x) =
            fun y : ℝ => deriv (fun z : ℝ => heatKernel t z) (x - y) := by
        funext y
        rw [deriv_heatKernel_translated_left ht x y,
          deriv_heatKernel ht (x - y)]
      rw [heq]
      exact hbase.comp (continuous_const.sub continuous_id)
    apply hderivCont.mul
    unfold wholeLineChiLargeKernelHalfWeight
    exact Real.continuous_exp.comp
      (continuous_const.mul
        (contDiff_two_regDist.continuous.comp
          (continuous_id.sub continuous_const)))
  apply (integrable_norm_rpow_iff hAcont.aestronglyMeasurable
    (by norm_num) (by norm_num)).mp
  simpa [A] using
    (weighted_heatKernel_deriv_four_integrable_and_bound ht hrho x).1

/-- Weighted `L⁴` norm bound, obtained by taking the fourth root of the
previous integral estimate. -/
theorem weighted_heatKernel_deriv_L4_norm_le
    {t rho : ℝ} (ht : 0 < t) (hrho : 0 ≤ rho) (x : ℝ) :
    (∫ y : ℝ,
      ‖deriv (fun z : ℝ => heatKernel t (z - y)) x *
        wholeLineChiLargeKernelHalfWeight rho x y‖ ^ (4 : ℝ)) ^
          (1 / 4 : ℝ) ≤ wholeLineWeightedHeatDerivL4NormBound t rho := by
  unfold wholeLineWeightedHeatDerivL4NormBound
  exact Real.rpow_le_rpow
    (integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg _) _)
    (weighted_heatKernel_deriv_four_integrable_and_bound ht hrho x).2
    (by norm_num)

theorem inv_sq_mul_rpow_neg_three_halves_eq_rpow_neg_seven_halves
    {t : ℝ} (ht : 0 < t) :
    (1 / t) ^ 2 * t ^ (-3 / 2 : ℝ) = t ^ (-7 / 2 : ℝ) := by
  rw [one_div, ← Real.rpow_neg_one,
    ← Real.rpow_mul_natCast ht.le (-1) 2,
    ← Real.rpow_add ht]
  congr 1
  norm_num

/-- The weighted `L⁴` norm has the expected `t^(-7/8)` singularity. -/
theorem wholeLineWeightedHeatDerivL4NormBound_le
    {t rho : ℝ} (ht : 0 < t) :
    wholeLineWeightedHeatDerivL4NormBound t rho ≤
      2 * Real.exp (rho / 2) * Real.exp (rho ^ 2 * t) *
        t ^ (-7 / 8 : ℝ) := by
  let H := ShenWork.IntervalNeumannFullKernel.heatGradPointwiseBound t
  let G := Real.sqrt (Real.pi / (1 / (8 * t)))
  let C := wholeLineWeightedHeatDerivL2PointConstant t rho
  let I := C ^ 2 * G
  let V := 16 * Real.exp (2 * rho) * Real.exp (4 * rho ^ 2 * t) *
    t ^ (-7 / 2 : ℝ)
  have hI0 : 0 ≤ I := by dsimp [I, C, G]; positivity
  have hV0 : 0 ≤ V := by dsimp [V]; positivity
  have hH0 : 0 ≤ H := by
    dsimp [H]
    unfold ShenWork.IntervalNeumannFullKernel.heatGradPointwiseBound
    positivity
  have hHsq : H ^ 2 ≤ (1 / t) ^ 2 :=
    pow_le_pow_left₀ hH0 (by simpa [H] using heatGradPointwiseBound_le_inv ht) 2
  have hcore : H ^ 4 * G ≤ 16 * t ^ (-7 / 2 : ℝ) := by
    have hHG := heatGrad_sq_mul_gaussianMassRoot_le ht
    have hprod := mul_le_mul hHsq hHG
      (mul_nonneg (sq_nonneg H) (Real.sqrt_nonneg _))
      (sq_nonneg (1 / t))
    calc
      H ^ 4 * G = H ^ 2 * (H ^ 2 * G) := by ring_nf
      _ ≤ (1 / t) ^ 2 * (16 * t ^ (-3 / 2 : ℝ)) := hprod
      _ = 16 * t ^ (-7 / 2 : ℝ) := by
        rw [← inv_sq_mul_rpow_neg_three_halves_eq_rpow_neg_seven_halves ht]
        ring_nf
  have hIV : I ≤ V := by
    dsimp [I, V, C, G]
    unfold wholeLineWeightedHeatDerivL2PointConstant
    calc
      (Real.exp rho * H ^ 2 * Real.exp (2 * rho ^ 2 * t)) ^ 2 * G =
          (Real.exp rho ^ 2 * Real.exp (2 * rho ^ 2 * t) ^ 2) *
            (H ^ 4 * G) := by ring_nf
      _ ≤ (Real.exp rho ^ 2 * Real.exp (2 * rho ^ 2 * t) ^ 2) *
          (16 * t ^ (-7 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hcore (by positivity)
      _ = 16 * Real.exp (2 * rho) * Real.exp (4 * rho ^ 2 * t) *
          t ^ (-7 / 2 : ℝ) := by
        rw [show Real.exp rho ^ 2 = Real.exp (2 * rho) by
          rw [pow_two, ← Real.exp_add]; congr 1; ring_nf]
        rw [show Real.exp (2 * rho ^ 2 * t) ^ 2 =
            Real.exp (4 * rho ^ 2 * t) by
          rw [pow_two, ← Real.exp_add]; congr 1; ring_nf]
        ring_nf
  have hroot := Real.rpow_le_rpow hI0 hIV (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hrootV : V ^ (1 / 4 : ℝ) =
      2 * Real.exp (rho / 2) * Real.exp (rho ^ 2 * t) *
        t ^ (-7 / 8 : ℝ) := by
    dsimp [V]
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity)]
    rw [show (16 : ℝ) ^ (1 / 4 : ℝ) = 2 by
      simpa [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num,
        show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num] using
          (Real.pow_rpow_inv_natCast (x := (2 : ℝ)) (n := 4)
            (by norm_num) (by norm_num))]
    rw [show Real.exp (2 * rho) ^ (1 / 4 : ℝ) =
        Real.exp (rho / 2) by
      rw [← Real.exp_mul]; congr 1; ring_nf]
    rw [show Real.exp (4 * rho ^ 2 * t) ^ (1 / 4 : ℝ) =
        Real.exp (rho ^ 2 * t) by
      rw [← Real.exp_mul]; congr 1; ring_nf]
    rw [show (t ^ (-7 / 2 : ℝ)) ^ (1 / 4 : ℝ) =
        t ^ (-7 / 8 : ℝ) by
      rw [← Real.rpow_mul ht.le]; congr 1; ring_nf]
  unfold wholeLineWeightedHeatDerivL4NormBound
  change I ^ (1 / 4 : ℝ) ≤ _
  exact hroot.trans_eq hrootV

/-- The shifted semigroup makes the weighted `L⁴` derivative norm integrable
in time whenever the weight rate is below one. -/
theorem damped_wholeLineWeightedHeatDerivL4NormBound_integrableOn_Ioi
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) :
    IntegrableOn
      (fun t : ℝ => Real.exp (-t) *
        wholeLineWeightedHeatDerivL4NormBound t rho)
      (Set.Ioi 0) := by
  have hgap : 0 < 1 - rho ^ 2 := by nlinarith
  let D : ℝ := 2 * Real.exp (rho / 2)
  let g : ℝ → ℝ := fun t =>
    t ^ (-(7 / 8 : ℝ)) * Real.exp (-(1 - rho ^ 2) * t)
  have hg : IntegrableOn g (Set.Ioi 0) := by
    simpa [g] using
      (ShenWork.PDE.rpow_neg_mul_exp_integrableOn_Ioi
        (theta := (7 / 8 : ℝ)) (nu := 1 - rho ^ 2)
        (by norm_num) (by norm_num) hgap)
  have hmajor : IntegrableOn (fun t => D * g t) (Set.Ioi 0) :=
    hg.const_mul D
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => Real.exp (-t) *
        wholeLineWeightedHeatDerivL4NormBound t rho)
      (volume.restrict (Set.Ioi 0)) := by
    unfold wholeLineWeightedHeatDerivL4NormBound
      wholeLineWeightedHeatDerivL2PointConstant
      ShenWork.IntervalNeumannFullKernel.heatGradPointwiseBound
    measurability
  refine hmajor.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  have hnorm0 : 0 ≤ wholeLineWeightedHeatDerivL4NormBound t rho := by
    unfold wholeLineWeightedHeatDerivL4NormBound
    positivity
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) hnorm0)]
  have hraw := mul_le_mul_of_nonneg_left
    (wholeLineWeightedHeatDerivL4NormBound_le (t := t) (rho := rho) ht0)
    (Real.exp_nonneg (-t))
  have hexp : Real.exp (-t) * Real.exp (rho ^ 2 * t) =
      Real.exp (-(1 - rho ^ 2) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring_nf
  calc
    Real.exp (-t) * wholeLineWeightedHeatDerivL4NormBound t rho ≤
        Real.exp (-t) *
          (2 * Real.exp (rho / 2) * Real.exp (rho ^ 2 * t) *
            t ^ (-7 / 8 : ℝ)) := hraw
    _ = D * g t := by
      dsimp [D, g]
      calc
        Real.exp (-t) *
            (2 * Real.exp (rho / 2) * Real.exp (rho ^ 2 * t) *
              t ^ (-7 / 8 : ℝ)) =
            2 * Real.exp (rho / 2) * t ^ (-7 / 8 : ℝ) *
              (Real.exp (-t) * Real.exp (rho ^ 2 * t)) := by ring_nf
        _ = 2 * Real.exp (rho / 2) *
            (t ^ (-(7 / 8 : ℝ)) * Real.exp (-(1 - rho ^ 2) * t)) := by
          rw [hexp]
          ring_nf

/-! ## The weighted `L^(4/3)` source -/

def wholeLineFourThirdWeightRate (κ : ℝ) : ℝ := 3 * κ / 2

theorem sourceHalfWeight_four_thirds_eq_localizingWeightAt
    (κ x y : ℝ) :
    wholeLineChiLargeSourceHalfWeight
        (wholeLineFourThirdWeightRate κ) x y ^ (4 / 3 : ℝ) =
      localizingWeightAt κ x y := by
  unfold wholeLineChiLargeSourceHalfWeight wholeLineFourThirdWeightRate
    localizingWeightAt localizingWeight
  rw [← Real.exp_mul]
  congr 1
  ring_nf

/-- A local `L^(4/3)` moment becomes a genuine global weighted source norm
after inserting the complementary exponential weight. -/
theorem weighted_source_fourThird_integrable_and_bound
    {κ K L : ℝ} {u : ℝ → ℝ} {F : ℝ → ℝ}
    (hκ : 0 < κ) (hL : 0 ≤ L)
    (huC : IsCUnifBdd u)
    (hF : Continuous F)
    (hpoint : ∀ y,
      |F y| ^ (4 / 3 : ℝ) ≤
        L ^ (4 / 3 : ℝ) * (1 + (u y) ^ (4 / 3 : ℝ)))
    (x : ℝ)
    (hmoment :
      (∫ y : ℝ, (u y) ^ (4 / 3 : ℝ) *
        localizingWeightAt κ x y) ≤ K) :
    Integrable (fun y : ℝ =>
        ‖F y * wholeLineChiLargeSourceHalfWeight
          (wholeLineFourThirdWeightRate κ) x y‖ ^ (4 / 3 : ℝ)) ∧
      (∫ y : ℝ,
        ‖F y * wholeLineChiLargeSourceHalfWeight
          (wholeLineFourThirdWeightRate κ) x y‖ ^ (4 / 3 : ℝ)) ≤
        L ^ (4 / 3 : ℝ) * (K + 2 / κ) := by
  have hmomentInt : Integrable (fun y : ℝ =>
      (u y) ^ (4 / 3 : ℝ) * localizingWeightAt κ x y) :=
    wholeLineLocalLpIntegrable_of_isCUnifBdd
      (u := fun _ => u) (t := 0) (by norm_num) hκ huC
  have hweightInt := localizingWeightAt_integrable hκ x
  let rho : ℝ := wholeLineFourThirdWeightRate κ
  let S : ℝ → ℝ := fun y =>
    F y * wholeLineChiLargeSourceHalfWeight rho x y
  let G : ℝ → ℝ := fun y => L ^ (4 / 3 : ℝ) *
    ((u y) ^ (4 / 3 : ℝ) * localizingWeightAt κ x y +
      localizingWeightAt κ x y)
  have hG : Integrable G := by
    dsimp [G]
    exact (hmomentInt.add hweightInt).const_mul (L ^ (4 / 3 : ℝ))
  have hScont : Continuous S := by
    apply hF.mul
    unfold wholeLineChiLargeSourceHalfWeight
    exact Real.continuous_exp.comp
      (continuous_const.mul
        (contDiff_two_regDist.continuous.comp
          (continuous_id.sub continuous_const)))
  have hdom : ∀ y, ‖S y‖ ^ (4 / 3 : ℝ) ≤ G y := by
    intro y
    have hw0 : 0 ≤ localizingWeightAt κ x y :=
      (localizingWeightAt_pos κ x y).le
    have hweight :
        ‖wholeLineChiLargeSourceHalfWeight rho x y‖ ^ (4 / 3 : ℝ) =
          localizingWeightAt κ x y := by
      rw [Real.norm_eq_abs,
        abs_of_pos (by unfold wholeLineChiLargeSourceHalfWeight; positivity)]
      simpa [rho] using sourceHalfWeight_four_thirds_eq_localizingWeightAt κ x y
    rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _), hweight,
      Real.norm_eq_abs]
    dsimp [G]
    calc
      |F y| ^ (4 / 3 : ℝ) * localizingWeightAt κ x y ≤
          (L ^ (4 / 3 : ℝ) * (1 + (u y) ^ (4 / 3 : ℝ))) *
            localizingWeightAt κ x y :=
        mul_le_mul_of_nonneg_right (hpoint y) hw0
      _ = L ^ (4 / 3 : ℝ) *
          ((u y) ^ (4 / 3 : ℝ) * localizingWeightAt κ x y +
            localizingWeightAt κ x y) := by ring_nf
  have hSint : Integrable (fun y => ‖S y‖ ^ (4 / 3 : ℝ)) := by
    refine hG.mono' (hScont.norm.rpow_const
      (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 4 / 3))).aestronglyMeasurable ?_
    filter_upwards [] with y
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact hdom y
  refine ⟨by simpa [S, rho] using hSint, ?_⟩
  calc
    (∫ y, ‖S y‖ ^ (4 / 3 : ℝ)) ≤ ∫ y, G y :=
      integral_mono hSint hG hdom
    _ = L ^ (4 / 3 : ℝ) *
        ((∫ y, (u y) ^ (4 / 3 : ℝ) * localizingWeightAt κ x y) +
          ∫ y, localizingWeightAt κ x y) := by
      dsimp [G]
      rw [integral_const_mul, integral_add hmomentInt hweightInt]
    _ ≤ L ^ (4 / 3 : ℝ) * (K + 2 / κ) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hmoment (integral_localizingWeightAt_le_two_div hκ x))
        (Real.rpow_nonneg hL _)

theorem weighted_source_memLp_fourThird
    {κ K L : ℝ} {u : ℝ → ℝ} {F : ℝ → ℝ}
    (hκ : 0 < κ) (hL : 0 ≤ L)
    (huC : IsCUnifBdd u)
    (hF : Continuous F)
    (hpoint : ∀ y,
      |F y| ^ (4 / 3 : ℝ) ≤
        L ^ (4 / 3 : ℝ) * (1 + (u y) ^ (4 / 3 : ℝ)))
    (x : ℝ)
    (hmoment :
      (∫ y : ℝ, (u y) ^ (4 / 3 : ℝ) *
        localizingWeightAt κ x y) ≤ K) :
    MemLp (fun y : ℝ =>
      F y * wholeLineChiLargeSourceHalfWeight
        (wholeLineFourThirdWeightRate κ) x y)
      (ENNReal.ofReal (4 / 3 : ℝ)) volume := by
  let S : ℝ → ℝ := fun y =>
    F y * wholeLineChiLargeSourceHalfWeight
      (wholeLineFourThirdWeightRate κ) x y
  have hScont : Continuous S := by
    apply hF.mul
    unfold wholeLineChiLargeSourceHalfWeight
    exact Real.continuous_exp.comp
      (continuous_const.mul
        (contDiff_two_regDist.continuous.comp
          (continuous_id.sub continuous_const)))
  apply (integrable_norm_rpow_iff hScont.aestronglyMeasurable
    (by norm_num) (by norm_num)).mp
  simpa [S, ENNReal.toReal_ofReal
    (by norm_num : (0 : ℝ) ≤ 4 / 3)] using
    (weighted_source_fourThird_integrable_and_bound
      hκ hL huC hF hpoint x hmoment).1

/-- In the normalized mobility case, a bounded resolver gradient controls
the `4/3` power of the chemotaxis flux by the matching population moment. -/
theorem wholeLineChemotaxisFlux_fourThird_le_of_gradient_m_one
    (p : CMParams) (hm : p.m = 1)
    {L : ℝ} {u : ℝ → ℝ} (hL : 0 ≤ L)
    (hu0 : ∀ y, 0 ≤ u y)
    (hgrad : ∀ y, |deriv (frozenElliptic p u) y| ≤ L)
    (y : ℝ) :
    |wholeLineChemotaxisFlux p u y| ^ (4 / 3 : ℝ) ≤
      L ^ (4 / 3 : ℝ) * (1 + (u y) ^ (4 / 3 : ℝ)) := by
  have hflux : |wholeLineChemotaxisFlux p u y| ≤ u y * L := by
    rw [wholeLineChemotaxisFlux, hm, Real.rpow_one, abs_mul,
      abs_of_nonneg (hu0 y)]
    exact mul_le_mul_of_nonneg_left (hgrad y) (hu0 y)
  have hpow := Real.rpow_le_rpow (abs_nonneg _) hflux
    (by norm_num : (0 : ℝ) ≤ 4 / 3)
  calc
    |wholeLineChemotaxisFlux p u y| ^ (4 / 3 : ℝ) ≤
        (u y * L) ^ (4 / 3 : ℝ) := hpow
    _ = L ^ (4 / 3 : ℝ) * (u y) ^ (4 / 3 : ℝ) := by
      rw [Real.mul_rpow (hu0 y) hL]
      ring_nf
    _ ≤ L ^ (4 / 3 : ℝ) * (1 + (u y) ^ (4 / 3 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left zero_le_one) (Real.rpow_nonneg hL _)

/-! ## Weighted Hölder convolution -/

/-- Hölder's inequality with the weighted conjugate pair `4` and `4/3`. -/
theorem weighted_heatKernel_deriv_convolution_fourThird_abs_le
    {t κ B : ℝ} (ht : 0 < t) (hκ : 0 ≤ κ)
    {F : ℝ → ℝ} (hF : Continuous F) (x : ℝ)
    (hFint : Integrable (fun y : ℝ =>
      ‖F y * wholeLineChiLargeSourceHalfWeight
        (wholeLineFourThirdWeightRate κ) x y‖ ^ (4 / 3 : ℝ)))
    (hFbound :
      (∫ y : ℝ, ‖F y * wholeLineChiLargeSourceHalfWeight
        (wholeLineFourThirdWeightRate κ) x y‖ ^ (4 / 3 : ℝ)) ≤ B) :
    |∫ y : ℝ,
        deriv (fun z : ℝ => heatKernel t (z - y)) x * F y| ≤
      wholeLineWeightedHeatDerivL4NormBound t
          (wholeLineFourThirdWeightRate κ) * B ^ (3 / 4 : ℝ) := by
  let rho : ℝ := wholeLineFourThirdWeightRate κ
  let A : ℝ → ℝ := fun y =>
    deriv (fun z : ℝ => heatKernel t (z - y)) x *
      wholeLineChiLargeKernelHalfWeight rho x y
  let S : ℝ → ℝ := fun y =>
    F y * wholeLineChiLargeSourceHalfWeight rho x y
  have hrho : 0 ≤ rho := by dsimp [rho, wholeLineFourThirdWeightRate]; positivity
  have hAmem : MemLp A (ENNReal.ofReal 4) volume := by
    simpa [A] using weighted_heatKernel_deriv_memLp_four ht hrho x
  have hScont : Continuous S := by
    apply hF.mul
    unfold wholeLineChiLargeSourceHalfWeight
    exact Real.continuous_exp.comp
      (continuous_const.mul
        (contDiff_two_regDist.continuous.comp
          (continuous_id.sub continuous_const)))
  have hSmem : MemLp S (ENNReal.ofReal (4 / 3 : ℝ)) volume := by
    apply (integrable_norm_rpow_iff hScont.aestronglyMeasurable
      (by norm_num) (by norm_num)).mp
    simpa [S, rho, ENNReal.toReal_ofReal
      (by norm_num : (0 : ℝ) ≤ 4 / 3)] using hFint
  have hpq : (4 : ℝ).HolderConjugate (4 / 3 : ℝ) :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hholder :
      (∫ y, ‖A y‖ * ‖S y‖) ≤
        (∫ y, ‖A y‖ ^ (4 : ℝ)) ^ (1 / 4 : ℝ) *
          (∫ y, ‖S y‖ ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) := by
    have hraw := integral_mul_norm_le_Lp_mul_Lq hpq hAmem hSmem
    norm_num at hraw ⊢
    exact hraw
  have hAroot := weighted_heatKernel_deriv_L4_norm_le ht hrho x
  have hSroot :
      (∫ y, ‖S y‖ ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) ≤
        B ^ (3 / 4 : ℝ) := by
    exact Real.rpow_le_rpow
      (integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg _) _)
      (by simpa [S, rho] using hFbound) (by norm_num)
  have hproduct :
      (∫ y, ‖A y‖ ^ (4 : ℝ)) ^ (1 / 4 : ℝ) *
          (∫ y, ‖S y‖ ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) ≤
        wholeLineWeightedHeatDerivL4NormBound t rho *
          B ^ (3 / 4 : ℝ) := by
    exact mul_le_mul hAroot hSroot
      (Real.rpow_nonneg (integral_nonneg fun y =>
        Real.rpow_nonneg (norm_nonneg _) _) _)
      (by unfold wholeLineWeightedHeatDerivL4NormBound; positivity)
  have hfactor : (fun y =>
      deriv (fun z : ℝ => heatKernel t (z - y)) x * F y) =
      fun y => A y * S y := by
    funext y
    dsimp [A, S]
    rw [show
        (deriv (fun z : ℝ => heatKernel t (z - y)) x *
            wholeLineChiLargeKernelHalfWeight rho x y) *
          (F y * wholeLineChiLargeSourceHalfWeight rho x y) =
        (deriv (fun z : ℝ => heatKernel t (z - y)) x * F y) *
          (wholeLineChiLargeKernelHalfWeight rho x y *
            wholeLineChiLargeSourceHalfWeight rho x y) by ac_rfl,
      kernelHalfWeight_mul_sourceHalfWeight, mul_one]
  rw [hfactor]
  calc
    |∫ y, A y * S y| = ‖∫ y, A y * S y‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∫ y, ‖A y * S y‖ := norm_integral_le_integral_norm _
    _ = ∫ y, ‖A y‖ * ‖S y‖ := by
      congr 1
      funext y
      rw [norm_mul]
    _ ≤ (∫ y, ‖A y‖ ^ (4 : ℝ)) ^ (1 / 4 : ℝ) *
          (∫ y, ‖S y‖ ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) := hholder
    _ ≤ wholeLineWeightedHeatDerivL4NormBound t rho *
          B ^ (3 / 4 : ℝ) := hproduct

/-- Concrete normalized chemotaxis-flux convolution estimate. -/
theorem weighted_chemotaxisFlux_convolution_fourThird_abs_le
    (p : CMParams) (hm : p.m = 1)
    {κ K L t : ℝ} (hκ : 0 < κ) (hL : 0 ≤ L) (ht : 0 < t)
    {u : ℝ → ℝ} (huC : IsCUnifBdd u) (hu0 : ∀ y, 0 ≤ u y)
    (hfluxC : Continuous (wholeLineChemotaxisFlux p u))
    (hgrad : ∀ y, |deriv (frozenElliptic p u) y| ≤ L)
    (x : ℝ)
    (hmoment :
      (∫ y : ℝ, (u y) ^ (4 / 3 : ℝ) *
        localizingWeightAt κ x y) ≤ K) :
    |∫ y : ℝ,
        deriv (fun z : ℝ => heatKernel t (z - y)) x *
          wholeLineChemotaxisFlux p u y| ≤
      wholeLineWeightedHeatDerivL4NormBound t
          (wholeLineFourThirdWeightRate κ) *
        (L ^ (4 / 3 : ℝ) * (K + 2 / κ)) ^ (3 / 4 : ℝ) := by
  have hsource := weighted_source_fourThird_integrable_and_bound
    hκ hL huC hfluxC
      (wholeLineChemotaxisFlux_fourThird_le_of_gradient_m_one
        p hm hL hu0 hgrad) x hmoment
  exact weighted_heatKernel_deriv_convolution_fourThird_abs_le
    ht hκ.le hfluxC x hsource.1 hsource.2

section AxiomAudit

#print axioms weighted_heatKernel_deriv_four_integrable_and_bound
#print axioms weighted_heatKernel_deriv_memLp_four
#print axioms wholeLineWeightedHeatDerivL4NormBound_le
#print axioms
  damped_wholeLineWeightedHeatDerivL4NormBound_integrableOn_Ioi
#print axioms weighted_source_fourThird_integrable_and_bound
#print axioms wholeLineChemotaxisFlux_fourThird_le_of_gradient_m_one
#print axioms weighted_heatKernel_deriv_convolution_fourThird_abs_le
#print axioms weighted_chemotaxisFlux_convolution_fourThird_abs_le

end AxiomAudit

end ShenWork.Paper1
