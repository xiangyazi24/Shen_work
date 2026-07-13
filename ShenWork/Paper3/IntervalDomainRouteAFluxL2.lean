/- Route-(a) `H¹` flux remainder estimate with second derivatives in `L²`. -/
import ShenWork.Paper3.IntervalDomainL2ProductBounds

namespace ShenWork.Paper3

open MeasureTheory Set Real
open ShenWork.IntervalDomain

noncomputable section

/-- Physical data after the seven-term product rule.  Only the three elliptic
second derivatives are measured in `L²`; all other factors are controlled by
the strong `C¹` trace. -/
structure EliminatedFluxDerivativeRouteAL2Data where
  bounds : EliminatedFluxDerivativeRouteABounds
  qStar : ℝ
  Cz1xx : ℝ
  Cz2xx : ℝ
  Czxx : ℝ
  profile : ℝ → ℝ
  z1xx : ℝ → ℝ
  z2xx : ℝ → ℝ
  zxx : ℝ → ℝ
  Cz1xx_nonneg : 0 ≤ Cz1xx
  Cz2xx_nonneg : 0 ≤ Cz2xx
  Czxx_nonneg : 0 ≤ Czxx
  profile_memLp : MemLp profile 2 (intervalMeasure 1)
  z1xx_memLp : MemLp z1xx 2 (intervalMeasure 1)
  z2xx_memLp : MemLp z2xx 2 (intervalMeasure 1)
  zxx_memLp : MemLp zxx 2 (intervalMeasure 1)
  profile_bound : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    |profile x| ≤
      eliminatedFluxDerivativeRouteAConstant bounds qStar * bounds.M * bounds.L +
        |qStar| * bounds.M * |z1xx x| +
        bounds.U * |qStar| * |z2xx x| +
        bounds.U * bounds.Cq * bounds.L * |zxx x|
  z1xx_l2 : intervalL2Size z1xx ≤ Cz1xx * bounds.L
  z2xx_l2 : intervalL2Size z2xx ≤ Cz2xx * bounds.M * bounds.L
  zxx_l2 : intervalL2Size zxx ≤ Czxx * bounds.L

namespace EliminatedFluxDerivativeRouteAL2Data

def l2Constant (H : EliminatedFluxDerivativeRouteAL2Data) : ℝ :=
  let s := Real.sqrt 2
  let K0 := eliminatedFluxDerivativeRouteAConstant H.bounds H.qStar
  s * (s * (s * (K0 + |H.qStar| * H.Cz1xx) +
    H.bounds.U * |H.qStar| * H.Cz2xx) +
      H.bounds.U * H.bounds.Cq * H.Czxx)

theorem l2Constant_nonneg (H : EliminatedFluxDerivativeRouteAL2Data) :
    0 ≤ H.l2Constant := by
  dsimp [l2Constant]
  have hK0 : 0 ≤ eliminatedFluxDerivativeRouteAConstant H.bounds H.qStar :=
    eliminatedFluxDerivativeRouteAConstant_nonneg
    H.bounds H.qStar
  have ha : 0 ≤ |H.qStar| * H.Cz1xx :=
    mul_nonneg (abs_nonneg _) H.Cz1xx_nonneg
  have hb : 0 ≤ H.bounds.U * |H.qStar| * H.Cz2xx :=
    mul_nonneg (mul_nonneg H.bounds.U_nonneg (abs_nonneg _))
      H.Cz2xx_nonneg
  have hc : 0 ≤ H.bounds.U * H.bounds.Cq * H.Czxx :=
    mul_nonneg (mul_nonneg H.bounds.U_nonneg H.bounds.Cq_nonneg)
      H.Czxx_nonneg
  exact mul_nonneg (Real.sqrt_nonneg _)
    (add_nonneg
      (mul_nonneg (Real.sqrt_nonneg _)
        (add_nonneg
          (mul_nonneg (Real.sqrt_nonneg _) (add_nonneg hK0 ha)) hb)) hc)

/-- The exact route-(a) output `‖∂x G(w)‖₂ ≤ C M L`. -/
theorem intervalL2Size_le (H : EliminatedFluxDerivativeRouteAL2Data) :
    intervalL2Size H.profile ≤ H.l2Constant * H.bounds.M * H.bounds.L := by
  let K0 := eliminatedFluxDerivativeRouteAConstant H.bounds H.qStar
  let f0 : ℝ → ℝ := fun _x => K0 * H.bounds.M * H.bounds.L
  let f1 : ℝ → ℝ := fun x => |H.qStar| * H.bounds.M * |H.z1xx x|
  let f2 : ℝ → ℝ := fun x => H.bounds.U * |H.qStar| * |H.z2xx x|
  let f3 : ℝ → ℝ := fun x => H.bounds.U * H.bounds.Cq * H.bounds.L * |H.zxx x|
  let g : ℝ → ℝ := fun x => ((f0 x + f1 x) + f2 x) + f3 x
  have hK0 : 0 ≤ K0 :=
    eliminatedFluxDerivativeRouteAConstant_nonneg H.bounds H.qStar
  have hc0 : 0 ≤ K0 * H.bounds.M * H.bounds.L :=
    mul_nonneg (mul_nonneg hK0 H.bounds.M_nonneg) H.bounds.L_nonneg
  have hf0 : MemLp f0 2 (intervalMeasure 1) := by
    exact memLp_const _
  have hz1abs : MemLp (fun x => |H.z1xx x|) 2 (intervalMeasure 1) := by
    simpa only [Pi.abs_apply] using H.z1xx_memLp.abs
  have hz2abs : MemLp (fun x => |H.z2xx x|) 2 (intervalMeasure 1) := by
    simpa only [Pi.abs_apply] using H.z2xx_memLp.abs
  have hzabs : MemLp (fun x => |H.zxx x|) 2 (intervalMeasure 1) := by
    simpa only [Pi.abs_apply] using H.zxx_memLp.abs
  have hf1 : MemLp f1 2 (intervalMeasure 1) := by
    simpa [f1] using hz1abs.const_mul (|H.qStar| * H.bounds.M)
  have hf2 : MemLp f2 2 (intervalMeasure 1) := by
    simpa [f2] using hz2abs.const_mul (H.bounds.U * |H.qStar|)
  have hf3 : MemLp f3 2 (intervalMeasure 1) := by
    simpa [f3] using hzabs.const_mul
      (H.bounds.U * H.bounds.Cq * H.bounds.L)
  have hf01 : MemLp (fun x => f0 x + f1 x) 2 (intervalMeasure 1) := hf0.add hf1
  have hf012 : MemLp (fun x => (f0 x + f1 x) + f2 x) 2
      (intervalMeasure 1) := hf01.add hf2
  have hg : MemLp g 2 (intervalMeasure 1) := by
    simpa [g] using hf012.add hf3
  have hg_nonneg : ∀ x, 0 ≤ g x := by
    intro x
    dsimp [g, f0, f1, f2, f3]
    have h1 : 0 ≤ |H.qStar| * H.bounds.M * |H.z1xx x| :=
      mul_nonneg (mul_nonneg (abs_nonneg _) H.bounds.M_nonneg) (abs_nonneg _)
    have h2 : 0 ≤ H.bounds.U * |H.qStar| * |H.z2xx x| :=
      mul_nonneg (mul_nonneg H.bounds.U_nonneg (abs_nonneg _)) (abs_nonneg _)
    have h3 : 0 ≤ H.bounds.U * H.bounds.Cq * H.bounds.L * |H.zxx x| := by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg H.bounds.U_nonneg H.bounds.Cq_nonneg)
          H.bounds.L_nonneg) (abs_nonneg _)
    linarith
  have hprofile_g : intervalL2Size H.profile ≤ intervalL2Size g := by
    simpa using
      (intervalL2Size_le_of_pointwise_mul (B := 1) (by norm_num)
        H.profile_memLp hg (by
          intro x hx
          have hp := H.profile_bound x hx
          dsimp [g, f0, f1, f2, f3, K0]
          rw [one_mul, abs_of_nonneg (hg_nonneg x)]
          exact hp))
  have hf0size : intervalL2Size f0 = K0 * H.bounds.M * H.bounds.L := by
    simpa [f0] using intervalL2Size_const hc0
  have hf1size : intervalL2Size f1 ≤
      (|H.qStar| * H.Cz1xx) * H.bounds.M * H.bounds.L := by
    have hmul := intervalL2Size_le_of_pointwise_mul
      (B := |H.qStar| * H.bounds.M)
      (mul_nonneg (abs_nonneg _) H.bounds.M_nonneg)
      hf1 H.z1xx_memLp (by
        intro x _
        dsimp [f1]
        simp only [abs_mul, abs_abs,
          abs_of_nonneg H.bounds.M_nonneg]
        exact le_rfl)
    calc
      intervalL2Size f1 ≤
          (|H.qStar| * H.bounds.M) * intervalL2Size H.z1xx := hmul
      _ ≤ (|H.qStar| * H.bounds.M) * (H.Cz1xx * H.bounds.L) :=
        mul_le_mul_of_nonneg_left H.z1xx_l2
          (mul_nonneg (abs_nonneg _) H.bounds.M_nonneg)
      _ = _ := by ring
  have hf2size : intervalL2Size f2 ≤
      (H.bounds.U * |H.qStar| * H.Cz2xx) * H.bounds.M * H.bounds.L := by
    have hmul := intervalL2Size_le_of_pointwise_mul
      (B := H.bounds.U * |H.qStar|)
      (mul_nonneg H.bounds.U_nonneg (abs_nonneg _))
      hf2 H.z2xx_memLp (by
        intro x _
        dsimp [f2]
        simp only [abs_mul, abs_abs,
          abs_of_nonneg H.bounds.U_nonneg]
        exact le_rfl)
    calc
      intervalL2Size f2 ≤
          (H.bounds.U * |H.qStar|) * intervalL2Size H.z2xx := hmul
      _ ≤ (H.bounds.U * |H.qStar|) *
          (H.Cz2xx * H.bounds.M * H.bounds.L) :=
        mul_le_mul_of_nonneg_left H.z2xx_l2
          (mul_nonneg H.bounds.U_nonneg (abs_nonneg _))
      _ = _ := by ring
  have hf3size : intervalL2Size f3 ≤
      (H.bounds.U * H.bounds.Cq * H.Czxx) * H.bounds.M * H.bounds.L := by
    have hcoef : 0 ≤ H.bounds.U * H.bounds.Cq * H.bounds.L :=
      mul_nonneg (mul_nonneg H.bounds.U_nonneg H.bounds.Cq_nonneg)
        H.bounds.L_nonneg
    have hmul := intervalL2Size_le_of_pointwise_mul
      (B := H.bounds.U * H.bounds.Cq * H.bounds.L)
      hcoef hf3 H.zxx_memLp (by
        intro x _
        dsimp [f3]
        rw [abs_mul, abs_abs, abs_of_nonneg hcoef])
    have hraw : intervalL2Size f3 ≤
        H.bounds.U * H.bounds.Cq * H.Czxx *
          (H.bounds.L * H.bounds.L) := by
      calc
        intervalL2Size f3 ≤
            (H.bounds.U * H.bounds.Cq * H.bounds.L) *
              intervalL2Size H.zxx := hmul
        _ ≤ (H.bounds.U * H.bounds.Cq * H.bounds.L) *
            (H.Czxx * H.bounds.L) :=
          mul_le_mul_of_nonneg_left H.zxx_l2 hcoef
        _ = _ := by ring
    have hLL : H.bounds.L * H.bounds.L ≤ H.bounds.M * H.bounds.L :=
      mul_le_mul_of_nonneg_right H.bounds.L_le_M H.bounds.L_nonneg
    calc
      intervalL2Size f3 ≤
          H.bounds.U * H.bounds.Cq * H.Czxx *
            (H.bounds.L * H.bounds.L) := hraw
      _ ≤ H.bounds.U * H.bounds.Cq * H.Czxx *
          (H.bounds.M * H.bounds.L) :=
        mul_le_mul_of_nonneg_left hLL
          (mul_nonneg (mul_nonneg H.bounds.U_nonneg H.bounds.Cq_nonneg)
            H.Czxx_nonneg)
      _ = _ := by ring
  have h01 := intervalL2Size_add_le hf0 hf1
  have h012 := intervalL2Size_add_le hf01 hf2
  have h0123 := intervalL2Size_add_le hf012 hf3
  calc
    intervalL2Size H.profile ≤ intervalL2Size g := hprofile_g
    _ ≤ Real.sqrt 2 *
        (Real.sqrt 2 *
          (Real.sqrt 2 * (intervalL2Size f0 + intervalL2Size f1) +
            intervalL2Size f2) + intervalL2Size f3) := by
      dsimp [g]
      calc
        intervalL2Size (fun x => ((f0 x + f1 x) + f2 x) + f3 x) ≤
            Real.sqrt 2 *
              (intervalL2Size (fun x => (f0 x + f1 x) + f2 x) +
                intervalL2Size f3) := h0123
        _ ≤ Real.sqrt 2 *
            (Real.sqrt 2 *
              (intervalL2Size (fun x => f0 x + f1 x) + intervalL2Size f2) +
                intervalL2Size f3) := by gcongr
        _ ≤ Real.sqrt 2 *
            (Real.sqrt 2 *
              (Real.sqrt 2 * (intervalL2Size f0 + intervalL2Size f1) +
                intervalL2Size f2) + intervalL2Size f3) := by gcongr
    _ ≤ Real.sqrt 2 *
        (Real.sqrt 2 *
          (Real.sqrt 2 *
            ((K0 + |H.qStar| * H.Cz1xx) * H.bounds.M * H.bounds.L) +
              (H.bounds.U * |H.qStar| * H.Cz2xx) *
                H.bounds.M * H.bounds.L) +
            (H.bounds.U * H.bounds.Cq * H.Czxx) *
              H.bounds.M * H.bounds.L) := by
      rw [hf0size]
      have hpair : K0 * H.bounds.M * H.bounds.L + intervalL2Size f1 ≤
          (K0 + |H.qStar| * H.Cz1xx) * H.bounds.M * H.bounds.L := by
        calc
          _ ≤ K0 * H.bounds.M * H.bounds.L +
              (|H.qStar| * H.Cz1xx) * H.bounds.M * H.bounds.L :=
            add_le_add_right hf1size _
          _ = _ := by ring
      gcongr <;> assumption
    _ = H.l2Constant * H.bounds.M * H.bounds.L := by
      unfold l2Constant
      dsimp only
      ring

#print axioms EliminatedFluxDerivativeRouteAL2Data.intervalL2Size_le

end EliminatedFluxDerivativeRouteAL2Data

end

end ShenWork.Paper3
