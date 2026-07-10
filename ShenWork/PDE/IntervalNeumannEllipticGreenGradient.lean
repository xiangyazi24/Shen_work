import ShenWork.PDE.IntervalNeumannEllipticGreen

/-!
# Gradient `L¹` bound for the explicit Neumann elliptic Green kernel
-/

noncomputable section

open Set
open scoped Topology

namespace ShenWork.PDE

private theorem ae_eq_of_eqOn_Ioo_of_le {F G : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (h : Set.EqOn F G (Set.Ioo a b)) :
    F =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)] G := by
  rw [Set.uIoc_of_le hab]
  refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).2 ?_
  filter_upwards
    [(MeasureTheory.Ioo_ae_eq_Ioc
      (a := a) (b := b) (μ := MeasureTheory.volume)).symm] with y hy hyIoc
  exact h (hy.mp hyIoc)

private theorem intervalIntegral_congr_eqOn_Ioo_of_le {F G : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (h : Set.EqOn F G (Set.Ioo a b)) :
    (∫ y in a..b, F y) = ∫ y in a..b, G y := by
  exact intervalIntegral.integral_congr_ae_restrict
    (ae_eq_of_eqOn_Ioo_of_le hab h)

private theorem intervalIntegrable_congr_eqOn_Ioo_of_le {F G : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hF : IntervalIntegrable F MeasureTheory.volume a b)
    (h : Set.EqOn F G (Set.Ioo a b)) :
    IntervalIntegrable G MeasureTheory.volume a b :=
  hF.congr_ae (ae_eq_of_eqOn_Ioo_of_le hab h)

private lemma two_sinh_mul_sinh_le_sinh {α x : ℝ}
    (hα : 0 < α) (_hx0 : 0 ≤ x) (_hx1 : x ≤ 1) :
    2 * Real.sinh (α * x) * Real.sinh (α * (1 - x)) ≤ Real.sinh α := by
  have hprod :
      2 * Real.sinh (α * x) * Real.sinh (α * (1 - x)) =
        Real.cosh (α * x + α * (1 - x)) -
          Real.cosh (α * x - α * (1 - x)) := by
    rw [Real.cosh_add, Real.cosh_sub]
    ring
  have hsum : α * x + α * (1 - x) = α := by ring
  have hcoshge : 1 ≤ Real.cosh (α * x - α * (1 - x)) :=
    Real.one_le_cosh _
  have hcosh_sinh : Real.cosh α - 1 ≤ Real.sinh α := by
    have hexp : Real.exp (-α) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    have hcs : Real.cosh α - Real.sinh α = Real.exp (-α) :=
      Real.cosh_sub_sinh α
    linarith
  calc
    2 * Real.sinh (α * x) * Real.sinh (α * (1 - x))
        = Real.cosh α - Real.cosh (α * x - α * (1 - x)) := by
          rw [hprod, hsum]
    _ ≤ Real.cosh α - 1 := sub_le_sub_left hcoshge _
    _ ≤ Real.sinh α := hcosh_sinh

/-- Exact `L¹` mass of the packaged `x`-derivative of the Neumann Green kernel. -/
theorem neumannEllipticGreenDx_l1_eq {μ x : ℝ}
    (hμ : 0 < μ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∫ y in (0 : ℝ)..1, |neumannEllipticGreenDx μ x y| =
      2 * Real.sinh (Real.sqrt μ * x) *
        Real.sinh (Real.sqrt μ * (1 - x)) /
          (Real.sqrt μ * Real.sinh (Real.sqrt μ)) := by
  rcases em (x = 0 ∨ x = 1) with hxend | hxint
  · rcases hxend with rfl | rfl <;> simp [neumannEllipticGreenDx]
  let α := Real.sqrt μ
  have hαpos : 0 < α := by simpa [α] using Real.sqrt_pos_of_pos hμ
  have hαne : α ≠ 0 := ne_of_gt hαpos
  have hsinhpos : 0 < Real.sinh α := Real.sinh_pos_iff.mpr hαpos
  let F : ℝ → ℝ := fun y => |neumannEllipticGreenDx μ x y|
  let L : ℝ → ℝ := fun y =>
    Real.cosh (α * y) * (Real.sinh (α * (1 - x)) / Real.sinh α)
  let R : ℝ → ℝ := fun y =>
    Real.cosh (α * (1 - y)) * (Real.sinh (α * x) / Real.sinh α)
  have hLint : IntervalIntegrable L MeasureTheory.volume 0 x :=
    (by fun_prop : Continuous L).intervalIntegrable 0 x
  have hRint : IntervalIntegrable R MeasureTheory.volume x 1 :=
    (by fun_prop : Continuous R).intervalIntegrable x 1
  have hFL : Set.EqOn L F (Set.Ioo (0 : ℝ) x) := by
    intro y hy
    have hnot : ¬ x < y := not_lt_of_ge hy.2.le
    have hsarg : 0 ≤ α * (1 - x) :=
      mul_nonneg hαpos.le (sub_nonneg.mpr hx1)
    have hQ : 0 ≤
        Real.cosh (α * y) *
          (Real.sinh (α * (1 - x)) / Real.sinh α) := by
      exact mul_nonneg (Real.cosh_pos _).le
        (div_nonneg (Real.sinh_nonneg_iff.mpr hsarg) hsinhpos.le)
    dsimp [L, F]
    rw [show neumannEllipticGreenDx μ x y =
        -Real.cosh (α * y) * Real.sinh (α * (1 - x)) / Real.sinh α by
          simp [neumannEllipticGreenDx, α, hxint, hnot]]
    rw [show -Real.cosh (α * y) * Real.sinh (α * (1 - x)) / Real.sinh α =
        -(Real.cosh (α * y) *
          (Real.sinh (α * (1 - x)) / Real.sinh α)) by ring]
    rw [abs_neg, abs_of_nonneg hQ]
  have hFR : Set.EqOn R F (Set.Ioo x (1 : ℝ)) := by
    intro y hy
    have hsarg : 0 ≤ α * x := mul_nonneg hαpos.le hx0
    have hQ : 0 ≤
        Real.cosh (α * (1 - y)) * (Real.sinh (α * x) / Real.sinh α) := by
      exact mul_nonneg (Real.cosh_pos _).le
        (div_nonneg (Real.sinh_nonneg_iff.mpr hsarg) hsinhpos.le)
    dsimp [R, F]
    rw [show neumannEllipticGreenDx μ x y =
        Real.sinh (α * x) * Real.cosh (α * (1 - y)) / Real.sinh α by
          simp [neumannEllipticGreenDx, α, hxint, hy.1]]
    rw [show Real.sinh (α * x) * Real.cosh (α * (1 - y)) / Real.sinh α =
        Real.cosh (α * (1 - y)) * (Real.sinh (α * x) / Real.sinh α) by ring]
    rw [abs_of_nonneg hQ]
  have hF0x : IntervalIntegrable F MeasureTheory.volume 0 x :=
    intervalIntegrable_congr_eqOn_Ioo_of_le hx0 hLint hFL
  have hFx1 : IntervalIntegrable F MeasureTheory.volume x 1 :=
    intervalIntegrable_congr_eqOn_Ioo_of_le hx1 hRint hFR
  have hleft : ∫ y in (0 : ℝ)..x, F y =
      (Real.sinh (α * x) / α - Real.sinh (α * 0) / α) *
        (Real.sinh (α * (1 - x)) / Real.sinh α) := by
    calc
      ∫ y in (0 : ℝ)..x, F y = ∫ y in (0 : ℝ)..x, L y := by
        exact intervalIntegral_congr_eqOn_Ioo_of_le hx0 hFL.symm
      _ = (∫ y in (0 : ℝ)..x, Real.cosh (α * y)) *
            (Real.sinh (α * (1 - x)) / Real.sinh α) := by
        rw [← intervalIntegral.integral_mul_const]
      _ = _ := by rw [integral_cosh_mul hαne]
  have hright : ∫ y in x..(1 : ℝ), F y =
      (Real.sinh (α * (1 - x)) / α - Real.sinh (α * (1 - 1)) / α) *
        (Real.sinh (α * x) / Real.sinh α) := by
    calc
      ∫ y in x..(1 : ℝ), F y = ∫ y in x..(1 : ℝ), R y := by
        exact intervalIntegral_congr_eqOn_Ioo_of_le hx1 hFR.symm
      _ = (∫ y in x..(1 : ℝ), Real.cosh (α * (1 - y))) *
            (Real.sinh (α * x) / Real.sinh α) := by
        rw [← intervalIntegral.integral_mul_const]
      _ = _ := by
        rw [integral_cosh_one_sub hαne]
        ring
  rw [← intervalIntegral.integral_add_adjacent_intervals hF0x hFx1, hleft, hright]
  simp only [Real.sinh_zero, mul_zero, sub_self, zero_div, sub_zero]
  have hsum :
      (Real.sinh (α * x) / α) *
          (Real.sinh (α * (1 - x)) / Real.sinh α) +
        (Real.sinh (α * (1 - x)) / α) *
          (Real.sinh (α * x) / Real.sinh α) =
        2 * Real.sinh (α * x) * Real.sinh (α * (1 - x)) /
          (α * Real.sinh α) := by
    ring
  simpa [α] using hsum

/-- Uniform `L¹` bound for the Green-kernel gradient on `[0,1]`. -/
theorem neumannEllipticGreenDx_l1_le {μ : ℝ} (hμ : 0 < μ) :
    ∀ x ∈ Icc (0 : ℝ) 1,
      ∫ y in (0 : ℝ)..1, |neumannEllipticGreenDx μ x y| ≤ 1 / Real.sqrt μ := by
  intro x hx
  let α := Real.sqrt μ
  have hαpos : 0 < α := by simpa [α] using Real.sqrt_pos_of_pos hμ
  have hsinhpos : 0 < Real.sinh α := Real.sinh_pos_iff.mpr hαpos
  have hdenpos : 0 < α * Real.sinh α := mul_pos hαpos hsinhpos
  rw [neumannEllipticGreenDx_l1_eq hμ hx.1 hx.2]
  change 2 * Real.sinh (α * x) * Real.sinh (α * (1 - x)) /
      (α * Real.sinh α) ≤ 1 / α
  rw [div_le_iff₀ hdenpos]
  have hmul : (1 / α) * (α * Real.sinh α) = Real.sinh α := by
    field_simp [ne_of_gt hαpos]
  rw [hmul]
  exact two_sinh_mul_sinh_le_sinh hαpos hx.1 hx.2

#print axioms neumannEllipticGreenDx_l1_eq
#print axioms neumannEllipticGreenDx_l1_le

end ShenWork.PDE
