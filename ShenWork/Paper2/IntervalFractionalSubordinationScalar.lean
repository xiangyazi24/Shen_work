import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Scalar and Banach-space estimates for fractional heat subordination

For `0 < σ < 1`, the useful form of subordination after one heat derivative is

`x^σ exp (-t x) = Γ(1-σ)⁻¹ ∫₀∞ s⁻σ x exp (-(t+s)x) ds`.

The accompanying Banach-space estimate is deliberately independent of any
functional calculus.  Its only analytic input is an integer-order heat bound
of size `(t+s)⁻¹`; Bochner's `norm_integral_le_integral_norm` then supplies the
Minkowski step.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace ShenWork.Paper2.IntervalFractionalSubordinationScalar

/-- The normalizing constant in the derivative form of fractional
subordination. -/
def fractionalSubordinationConstant (sigma : ℝ) : ℝ :=
  (Real.Gamma (1 - sigma))⁻¹

/-- The scalar integrand in the derivative form of heat subordination. -/
def fractionalHeatDerivativeIntegrand (sigma t x s : ℝ) : ℝ :=
  s ^ (-sigma) * (x * Real.exp (-((t + s) * x)))

/-- Mode-by-mode Gamma identity behind fractional heat subordination. -/
theorem integral_fractionalHeatDerivativeIntegrand
    {sigma t x : ℝ} (_hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hx : 0 < x) :
    (∫ s : ℝ in Set.Ioi 0,
        fractionalHeatDerivativeIntegrand sigma t x s) =
      Real.Gamma (1 - sigma) *
        (x ^ sigma * Real.exp (-(t * x))) := by
  have ha : 0 < 1 - sigma := by linarith
  have hgamma := Real.integral_rpow_mul_exp_neg_mul_Ioi ha hx
  have hintegrand :
      (fun s : ℝ => fractionalHeatDerivativeIntegrand sigma t x s) =
        fun s => (x * Real.exp (-(t * x))) *
          (s ^ ((1 - sigma) - 1) * Real.exp (-(x * s))) := by
    funext s
    rw [fractionalHeatDerivativeIntegrand]
    have hexp : Real.exp (-((t + s) * x)) =
        Real.exp (-(t * x)) * Real.exp (-(x * s)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    have hexponent : (1 - sigma) - 1 = -sigma := by ring
    rw [hexponent]
    ring
  rw [hintegrand, MeasureTheory.integral_const_mul, hgamma]
  have hpow : x * (1 / x) ^ (1 - sigma) = x ^ sigma := by
    calc
      x * (1 / x) ^ (1 - sigma) =
          x ^ (1 : ℝ) / x ^ (1 - sigma) := by
            rw [one_div, Real.inv_rpow hx.le, Real.rpow_one,
              div_eq_mul_inv]
      _ = x ^ ((1 : ℝ) - (1 - sigma)) :=
        (Real.rpow_sub hx 1 (1 - sigma)).symm
      _ = x ^ sigma := by ring_nf
  calc
    (x * Real.exp (-(t * x))) *
        ((1 / x) ^ (1 - sigma) * Real.Gamma (1 - sigma)) =
        Real.Gamma (1 - sigma) *
          ((x * (1 / x) ^ (1 - sigma)) * Real.exp (-(t * x))) := by
            ring
    _ = Real.Gamma (1 - sigma) *
        (x ^ sigma * Real.exp (-(t * x))) := by rw [hpow]

/-- Exact scalar subordination identity on every strictly positive spectral
mode. -/
theorem fractionalHeat_subordination_scalar
    {sigma t x : ℝ} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hx : 0 < x) :
    fractionalSubordinationConstant sigma *
        (∫ s : ℝ in Set.Ioi 0,
          fractionalHeatDerivativeIntegrand sigma t x s) =
      x ^ sigma * Real.exp (-(t * x)) := by
  rw [integral_fractionalHeatDerivativeIntegrand hsigma0 hsigma1 hx]
  unfold fractionalSubordinationConstant
  have hGamma : Real.Gamma (1 - sigma) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  field_simp

/-- The constant Neumann mode is also covered: both sides vanish because
`sigma > 0`. -/
theorem fractionalHeat_subordination_scalar_zero
    {sigma t : ℝ} (hsigma0 : 0 < sigma) :
    fractionalSubordinationConstant sigma *
        (∫ s : ℝ in Set.Ioi 0,
          fractionalHeatDerivativeIntegrand sigma t 0 s) =
      (0 : ℝ) ^ sigma * Real.exp (-(t * 0)) := by
  simp [fractionalHeatDerivativeIntegrand,
    Real.zero_rpow hsigma0.ne']

/-- Scalar subordination on every nonnegative spectral value, including the
zero Neumann mode. -/
theorem fractionalHeat_subordination_scalar_nonneg
    {sigma t x : ℝ} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hx : 0 ≤ x) :
    fractionalSubordinationConstant sigma *
        (∫ s : ℝ in Set.Ioi 0,
          fractionalHeatDerivativeIntegrand sigma t x s) =
      x ^ sigma * Real.exp (-(t * x)) := by
  rcases hx.eq_or_lt with rfl | hx
  · exact fractionalHeat_subordination_scalar_zero hsigma0
  · exact fractionalHeat_subordination_scalar hsigma0 hsigma1 hx

/-! ## The scalar majorant used in the Bochner estimate -/

/-- Split majorant for `s⁻σ (t+s)⁻¹`.  The split at `s=t` isolates the two
integrable endpoint powers. -/
def fractionalDerivativeMajorant (sigma t s : ℝ) : ℝ :=
  if s ≤ t then t⁻¹ * s ^ (-sigma) else s ^ (-sigma - 1)

theorem fractionalDerivativeMajorant_nonneg
    {sigma t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    0 ≤ fractionalDerivativeMajorant sigma t s := by
  unfold fractionalDerivativeMajorant
  split_ifs <;> positivity

/-- The actual derivative-subordination weight is bounded by the split
majorant. -/
theorem fractionalDerivativeWeight_le_majorant
    {sigma t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    s ^ (-sigma) * (t + s) ^ (-(1 : ℝ)) ≤
      fractionalDerivativeMajorant sigma t s := by
  unfold fractionalDerivativeMajorant
  by_cases hst : s ≤ t
  · rw [if_pos hst, Real.rpow_neg_one]
    calc
      s ^ (-sigma) * (t + s)⁻¹ ≤ s ^ (-sigma) * t⁻¹ :=
        mul_le_mul_of_nonneg_left
          ((inv_le_inv₀ (by linarith : 0 < t + s) ht).2 (by linarith))
          (Real.rpow_nonneg hs.le _)
      _ = t⁻¹ * s ^ (-sigma) := mul_comm _ _
  · rw [if_neg hst, Real.rpow_neg_one]
    have hts : s ≤ t + s := by linarith
    calc
      s ^ (-sigma) * (t + s)⁻¹ ≤ s ^ (-sigma) * s⁻¹ :=
        mul_le_mul_of_nonneg_left
          ((inv_le_inv₀ (by linarith : 0 < t + s) hs).2 hts)
          (Real.rpow_nonneg hs.le _)
      _ = s ^ (-sigma - 1) := by
        rw [← Real.rpow_neg_one s, ← Real.rpow_add hs]
        congr 1

theorem fractionalDerivativeMajorant_integrableOn
    {sigma t : ℝ} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (ht : 0 < t) :
    IntegrableOn (fractionalDerivativeMajorant sigma t) (Set.Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi ht.le, integrableOn_union]
  constructor
  · have hnear : IntegrableOn (fun s : ℝ => s ^ (-sigma))
        (Set.Ioc 0 t) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mp
        (intervalIntegral.intervalIntegrable_rpow'
          (a := (0 : ℝ)) (b := t) (by linarith : -1 < -sigma))
    refine IntegrableOn.congr_fun (hnear.const_mul t⁻¹) ?_ measurableSet_Ioc
    intro s hs
    simp [fractionalDerivativeMajorant, hs.2]
  · have htail : IntegrableOn (fun s : ℝ => s ^ (-sigma - 1))
        (Set.Ioi t) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) ht
    refine IntegrableOn.congr_fun htail ?_ measurableSet_Ioi
    intro s hs
    simp [fractionalDerivativeMajorant,
      not_le_of_gt (Set.mem_Ioi.mp hs)]

/-- Exact integral of the split majorant. -/
theorem integral_fractionalDerivativeMajorant
    {sigma t : ℝ} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (ht : 0 < t) :
    (∫ s : ℝ in Set.Ioi 0, fractionalDerivativeMajorant sigma t s) =
      (1 / (1 - sigma) + 1 / sigma) * t ^ (-sigma) := by
  have hnear : IntegrableOn (fractionalDerivativeMajorant sigma t)
      (Set.Ioc 0 t) :=
    (fractionalDerivativeMajorant_integrableOn hsigma0 hsigma1 ht).mono
      (Set.Ioc_subset_Ioi_self) le_rfl
  have htail : IntegrableOn (fractionalDerivativeMajorant sigma t)
      (Set.Ioi t) :=
    (fractionalDerivativeMajorant_integrableOn hsigma0 hsigma1 ht).mono
      (Set.Ioi_subset_Ioi ht.le) le_rfl
  rw [← Ioc_union_Ioi_eq_Ioi ht.le,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hnear htail]
  have hnear_eval :
      (∫ s : ℝ in Set.Ioc 0 t, fractionalDerivativeMajorant sigma t s) =
        (1 / (1 - sigma)) * t ^ (-sigma) := by
    have heq : (∫ s : ℝ in Set.Ioc 0 t,
        fractionalDerivativeMajorant sigma t s) =
        ∫ s : ℝ in Set.Ioc 0 t, t⁻¹ * s ^ (-sigma) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      simp [fractionalDerivativeMajorant, hs.2]
    rw [heq, ← intervalIntegral.integral_of_le ht.le,
      intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by linarith : -1 < -sigma))]
    have hpow : t⁻¹ * t ^ (1 - sigma) = t ^ (-sigma) := by
      rw [← Real.rpow_neg_one t, ← Real.rpow_add ht]
      congr 1
      ring
    rw [Real.zero_rpow (by linarith : -sigma + 1 ≠ 0), sub_zero,
      show -sigma + 1 = 1 - sigma by ring]
    calc
      t⁻¹ * (t ^ (1 - sigma) / (1 - sigma)) =
          (t⁻¹ * t ^ (1 - sigma)) / (1 - sigma) := by ring
      _ = t ^ (-sigma) / (1 - sigma) := by rw [hpow]
      _ = (1 / (1 - sigma)) * t ^ (-sigma) := by ring
  have htail_eval :
      (∫ s : ℝ in Set.Ioi t, fractionalDerivativeMajorant sigma t s) =
        (1 / sigma) * t ^ (-sigma) := by
    have heq : (∫ s : ℝ in Set.Ioi t,
        fractionalDerivativeMajorant sigma t s) =
        ∫ s : ℝ in Set.Ioi t, s ^ (-sigma - 1) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      simp [fractionalDerivativeMajorant,
        not_le_of_gt (Set.mem_Ioi.mp hs)]
    rw [heq, integral_Ioi_rpow_of_lt (by linarith) ht]
    rw [show -sigma - 1 + 1 = -sigma by ring]
    field_simp [hsigma0.ne']
  rw [hnear_eval, htail_eval]
  ring

/-! ## Banach-valued Minkowski step -/

theorem fractionalSubordinationConstant_pos
    {sigma : ℝ} (hsigma1 : sigma < 1) :
    0 < fractionalSubordinationConstant sigma := by
  unfold fractionalSubordinationConstant
  exact inv_pos.mpr (Real.Gamma_pos_of_pos (by linarith))

/-- The derivative-subordination Bochner integral.  The ambient Banach space
can in particular be a genuine `Lp` space. -/
def fractionalDerivativeBochner
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (sigma : ℝ) (F : ℝ → E) : E :=
  fractionalSubordinationConstant sigma •
    ∫ s : ℝ in Set.Ioi 0, s ^ (-sigma) • F s

/-- Abstract Minkowski estimate for derivative subordination.  Its hypotheses
are exactly strong measurability in the time parameter and the integer-order
heat estimate `‖F(s)‖ ≤ C (t+s)⁻¹ N`. -/
theorem norm_fractionalDerivativeBochner_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {sigma t C N : ℝ} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (ht : 0 < t) (hC : 0 ≤ C) (hN : 0 ≤ N) (F : ℝ → E)
    (hFmeas : AEStronglyMeasurable (fun s : ℝ => s ^ (-sigma) • F s)
      (volume.restrict (Set.Ioi 0)))
    (hFbound : ∀ s, 0 < s →
      ‖F s‖ ≤ C * (t + s) ^ (-(1 : ℝ)) * N) :
    ‖fractionalDerivativeBochner sigma F‖ ≤
      fractionalSubordinationConstant sigma * C *
        (1 / (1 - sigma) + 1 / sigma) * t ^ (-sigma) * N := by
  let M : ℝ → ℝ := fractionalDerivativeMajorant sigma t
  let g : ℝ → ℝ := fun s => (C * N) * M s
  let G : ℝ → E := fun s => s ^ (-sigma) • F s
  have hg : Integrable g (volume.restrict (Set.Ioi 0)) := by
    dsimp [g, M]
    exact (fractionalDerivativeMajorant_integrableOn hsigma0 hsigma1 ht).const_mul
      (C * N)
  have hdom : ∀ᵐ s ∂(volume.restrict (Set.Ioi 0)), ‖G s‖ ≤ g s := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
    exact Filter.Eventually.of_forall fun s hs => by
      have hs0 : 0 < s := Set.mem_Ioi.mp hs
      dsimp [G, g, M]
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos hs0 _)]
      calc
        s ^ (-sigma) * ‖F s‖ ≤
            s ^ (-sigma) * (C * (t + s) ^ (-(1 : ℝ)) * N) :=
          mul_le_mul_of_nonneg_left (hFbound s hs0)
            (Real.rpow_nonneg hs0.le _)
        _ = (C * N) *
            (s ^ (-sigma) * (t + s) ^ (-(1 : ℝ))) := by ring
        _ ≤ (C * N) * fractionalDerivativeMajorant sigma t s :=
          mul_le_mul_of_nonneg_left
            (fractionalDerivativeWeight_le_majorant ht hs0)
            (mul_nonneg hC hN)
  have hGmeas : AEStronglyMeasurable G
      (volume.restrict (Set.Ioi 0)) := by
    simpa [G] using hFmeas
  have hG : Integrable G (volume.restrict (Set.Ioi 0)) :=
    hg.mono' hGmeas hdom
  have hnorm :
      ‖∫ s : ℝ in Set.Ioi 0, G s‖ ≤
        (C * N) * (1 / (1 - sigma) + 1 / sigma) * t ^ (-sigma) := by
    calc
      ‖∫ s : ℝ in Set.Ioi 0, G s‖ ≤
          ∫ s : ℝ in Set.Ioi 0, ‖G s‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ s : ℝ in Set.Ioi 0, g s :=
        integral_mono_ae hG.norm hg hdom
      _ = (C * N) *
          ∫ s : ℝ in Set.Ioi 0,
            fractionalDerivativeMajorant sigma t s := by
        rw [MeasureTheory.integral_const_mul]
      _ = (C * N) *
          ((1 / (1 - sigma) + 1 / sigma) * t ^ (-sigma)) := by
        rw [integral_fractionalDerivativeMajorant hsigma0 hsigma1 ht]
      _ = (C * N) * (1 / (1 - sigma) + 1 / sigma) *
          t ^ (-sigma) := by ring
  have hc0 : 0 ≤ fractionalSubordinationConstant sigma :=
    (fractionalSubordinationConstant_pos hsigma1).le
  unfold fractionalDerivativeBochner
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
  calc
    fractionalSubordinationConstant sigma *
        ‖∫ s : ℝ in Set.Ioi 0, G s‖ ≤
      fractionalSubordinationConstant sigma *
        ((C * N) * (1 / (1 - sigma) + 1 / sigma) * t ^ (-sigma)) :=
      mul_le_mul_of_nonneg_left hnorm hc0
    _ = fractionalSubordinationConstant sigma * C *
        (1 / (1 - sigma) + 1 / sigma) * t ^ (-sigma) * N := by ring

#print axioms fractionalHeat_subordination_scalar_nonneg
#print axioms integral_fractionalDerivativeMajorant
#print axioms norm_fractionalDerivativeBochner_le

end ShenWork.Paper2.IntervalFractionalSubordinationScalar
