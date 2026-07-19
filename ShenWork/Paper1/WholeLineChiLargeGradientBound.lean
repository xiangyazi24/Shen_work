import ShenWork.Paper1.WholeLineLocalMomentBound
import ShenWork.Paper1.WaveFrozenEllipticDep

/-!
# A uniform signal-gradient bound from the local moment

This is stage 2 of the large-chemotaxis bootstrap in Paper 1, §3.1.  The
Green-kernel derivative is dominated by `exp (-|x-y|)`.  When `0 < κ < 1`,
that kernel is in turn dominated by a centre-matched translated localizing
weight.  The uniform weighted `L^P` moment, with `P > γ`, then bounds the
resolver gradient pointwise and uniformly in space and time.
-/

open Filter MeasureTheory Real Set Topology

noncomputable section

namespace ShenWork.Paper1

def UniformSignalGradientBounded
    (v : ℝ → ℝ → ℝ) (T C : ℝ) : Prop :=
  ∀ t ∈ Ico (0 : ℝ) T, ∀ x : ℝ, |deriv (v t) x| ≤ C

def UniformPositiveTimeSignalGradientBounded
    (v : ℝ → ℝ → ℝ) (T C : ℝ) : Prop :=
  ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : ℝ, |deriv (v t) x| ≤ C

theorem regDist_le_one_add_abs (z : ℝ) :
    regDist z ≤ 1 + |z| := by
  have hreg := (regDist_pos z).le
  have habs := abs_nonneg z
  nlinarith [regDist_sq z, sq_abs z]

/-- The Green derivative kernel is dominated by the translated weight whose
centre is the evaluation point. -/
theorem exp_neg_abs_le_exp_mul_localizingWeightAt
    {κ : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1) (x y : ℝ) :
    Real.exp (-|x - y|) ≤
      Real.exp κ * localizingWeightAt κ x y := by
  have hr := regDist_le_one_add_abs (y - x)
  have habs : |y - x| = |x - y| := abs_sub_comm y x
  have hscaled : κ * regDist (y - x) ≤ κ * (1 + |y - x|) :=
    mul_le_mul_of_nonneg_left hr hκ
  have hkabs : κ * |y - x| ≤ |y - x| := by
    nlinarith [mul_le_mul_of_nonneg_right hκ1 (abs_nonneg (y - x))]
  unfold localizingWeightAt localizingWeight
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [habs] at hscaled hkabs
  nlinarith

theorem rpow_le_one_add_rpow_of_exponent_le
    {z r s : ℝ} (hz : 0 ≤ z) (hr : 0 ≤ r) (hrs : r ≤ s) :
    z ^ r ≤ 1 + z ^ s := by
  by_cases hz1 : z ≤ 1
  · have h := Real.rpow_le_one hz hz1 hr
    exact h.trans (le_add_of_nonneg_right (Real.rpow_nonneg hz s))
  · have h1 : 1 ≤ z := le_of_not_ge hz1
    have h := Real.rpow_le_rpow_of_exponent_le h1 hrs
    exact h.trans (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1))

def wholeLineChiLargeGradientConstant (κ K : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.exp κ * (K + 2 / κ)

/-- Fixed-time pointwise resolver-gradient estimate obtained directly from
the centre-matched local moment. -/
theorem frozenElliptic_deriv_abs_le_of_localMoment
    (p : CMParams) {P κ K : ℝ} {u : ℝ → ℝ}
    (hPγ : p.γ ≤ P) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hu : IsCUnifBdd u) (hu_nonneg : ∀ y, 0 ≤ u y)
    (hmoment : ∀ x : ℝ,
      (∫ y : ℝ, (u y) ^ P * localizingWeightAt κ x y) ≤ K)
    (x : ℝ) :
    |deriv (frozenElliptic p u) x| ≤
      wholeLineChiLargeGradientConstant κ K := by
  have hP0 : 0 ≤ P := le_trans (le_trans zero_le_one p.hγ) hPγ
  have hmoment_int : Integrable (fun y : ℝ =>
      (u y) ^ P * localizingWeightAt κ x y) :=
    wholeLineLocalLpIntegrable_of_isCUnifBdd hP0 hκ
      (u := fun _ => u) (t := 0) hu
  have hweight_int := localizingWeightAt_integrable hκ x
  let G : ℝ → ℝ := fun y => Real.exp κ *
    ((u y) ^ P * localizingWeightAt κ x y +
      localizingWeightAt κ x y)
  have hGint : Integrable G := by
    dsimp [G]
    exact (hmoment_int.add hweight_int).const_mul (Real.exp κ)
  have hkernel_int : Integrable (fun y : ℝ =>
      frozenEllipticDerivKernel x y * (u y) ^ p.γ) := by
    exact frozenEllipticDerivKernel_mul_integrable
      (rpow_cunif_bdd_of_nonneg p hu hu_nonneg) x
  have hpoint : ∀ y : ℝ,
      ‖frozenEllipticDerivKernel x y * (u y) ^ p.γ‖ ≤ G y := by
    intro y
    have hk := frozenEllipticDerivKernel_abs_le x y
    have hw := exp_neg_abs_le_exp_mul_localizingWeightAt hκ.le hκ1 x y
    have hup := rpow_le_one_add_rpow_of_exponent_le
      (hu_nonneg y) (le_trans zero_le_one p.hγ) hPγ
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (hu_nonneg y) p.γ)]
    dsimp [G]
    calc
      |frozenEllipticDerivKernel x y| * (u y) ^ p.γ ≤
          Real.exp (-|x - y|) * (u y) ^ p.γ :=
        mul_le_mul_of_nonneg_right hk
          (Real.rpow_nonneg (hu_nonneg y) p.γ)
      _ ≤ (Real.exp κ * localizingWeightAt κ x y) *
          (1 + (u y) ^ P) :=
        mul_le_mul hw hup (Real.rpow_nonneg (hu_nonneg y) p.γ)
          (mul_nonneg (Real.exp_pos κ).le
            (localizingWeightAt_pos κ x y).le)
      _ = Real.exp κ *
          ((u y) ^ P * localizingWeightAt κ x y +
            localizingWeightAt κ x y) := by ring
  have hintegral :
      |∫ y : ℝ, frozenEllipticDerivKernel x y * (u y) ^ p.γ| ≤
        ∫ y : ℝ, G y := by
    change ‖∫ y : ℝ,
      frozenEllipticDerivKernel x y * (u y) ^ p.γ‖ ≤ _
    exact norm_integral_le_of_norm_le hGint (Eventually.of_forall hpoint)
  have hGbound :
      (∫ y : ℝ, G y) ≤ Real.exp κ * (K + 2 / κ) := by
    dsimp [G]
    rw [integral_const_mul, integral_add hmoment_int hweight_int]
    exact mul_le_mul_of_nonneg_left
      (add_le_add (hmoment x) (integral_localizingWeightAt_le_two_div hκ x))
      (Real.exp_pos κ).le
  rw [frozenElliptic_deriv_eq_kernel_integral p hu hu_nonneg]
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  unfold wholeLineChiLargeGradientConstant
  nlinarith [hintegral.trans hGbound]

structure WholeLineChiLargeGradientData
    (p : CMParams) (P κ T K : ℝ) (u v : ℝ → ℝ → ℝ) : Prop where
  hPγ : p.γ < P
  hκ : 0 < κ
  hκ1 : κ ≤ 1
  localMoment : UniformlyLocalLpBounded P κ u T K
  u_slice_isCUnifBdd : ∀ t ∈ Ico (0 : ℝ) T, IsCUnifBdd (u t)
  u_nonnegative : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : ℝ, 0 ≤ u t x
  resolver : ∀ t ∈ Ico (0 : ℝ) T, v t = frozenElliptic p (u t)

theorem WholeLineChiLargeGradientData.uniformSignalGradientBounded
    {p : CMParams} {P κ T K : ℝ} {u v : ℝ → ℝ → ℝ}
    (H : WholeLineChiLargeGradientData p P κ T K u v) :
    UniformSignalGradientBounded v T
      (wholeLineChiLargeGradientConstant κ K) := by
  intro t ht x
  rw [H.resolver t ht]
  exact frozenElliptic_deriv_abs_le_of_localMoment p H.hPγ.le H.hκ H.hκ1
    (H.u_slice_isCUnifBdd t ht) (H.u_nonnegative t ht)
    (fun x₀ => H.localMoment t ht x₀) x

/-- Direct stage-1-to-stage-2 bridge.  The L3 package supplies all positive
time resolver data, so no additional analytic hypothesis is introduced here. -/
theorem WholeLineLocalMomentBoundData.uniformPositiveTimeSignalGradientBounded
    {p : CMParams} {P κ T U₀ : ℝ} {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentBoundData p P κ T U₀ u v) :
    UniformPositiveTimeSignalGradientBounded v T
      (wholeLineChiLargeGradientConstant κ
        (wholeLineLocalMomentUniformBound p P κ U₀)) := by
  have hPγ : p.γ < P :=
    lt_of_le_of_lt (le_trans (le_max_right p.m p.γ)
      (le_max_right 1 (max p.m p.γ))) H.hP
  have hκ1 : κ ≤ 1 := by linarith [H.hκhalf]
  intro t ht x
  rw [H.resolver t ht]
  exact frozenElliptic_deriv_abs_le_of_localMoment p hPγ.le H.hκ hκ1
    (H.u_slice_isCUnifBdd t ht)
    (H.u_nonnegative t ⟨ht.1.le, ht.2.le⟩)
    (fun x₀ => H.uniformlyLocalLpBounded t ⟨ht.1.le, ht.2⟩ x₀) x

section AxiomAudit

#print axioms frozenElliptic_deriv_abs_le_of_localMoment
#print axioms WholeLineChiLargeGradientData.uniformSignalGradientBounded
#print axioms WholeLineLocalMomentBoundData.uniformPositiveTimeSignalGradientBounded

end AxiomAudit

end ShenWork.Paper1
