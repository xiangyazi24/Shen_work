/-
  ShenWork/PaperOne/WholeLineChemotaxisCrossControl.lean

  Whole-line chemotaxis cross-control after the barrier IBP:

    -χ ∫ φ_x · U^m V_x
      ≤ 1/2 ∫ (φ_x)^2 + K · E.

  The analytic input not proved here is the regularity/decay package that
  supplies the post-IBP form, the support relation for φ_x, and the
  excess-set/E control.  The V_x bound is carried as a field, matching the
  bounded-domain cross-control atom's regularity-bound style.

  The file uses only theorem-proved Lean terms.
-/
import ShenWork.PaperOne.WholeLineBarrierEnergyFrontierUpper

open MeasureTheory Filter

noncomputable section

namespace ShenWork.PaperOne

/-- Indicator of the strict excess set of a barrier test function.  It is kept
as an `ℝ`-valued function so the excess-set/E control can be stated directly as
an ordinary Bochner integral. -/
def wholeLineExcessIndicator (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  if 0 < φ x then 1 else 0

/-- The post-IBP chemotaxis weight `U^m V_x` for a fixed time slice. -/
def wholeLineChemotaxisWeight (p : CMParams) (U Vx : ℝ → ℝ) (x : ℝ) : ℝ :=
  (U x) ^ p.m * Vx x

/-- The same weight restricted to the excess set. -/
def wholeLineRestrictedChemotaxisWeight
    (p : CMParams) (φ U Vx : ℝ → ℝ) (x : ℝ) : ℝ :=
  wholeLineChemotaxisWeight p U Vx x * wholeLineExcessIndicator φ x

/-- Whole-line gradient dissipation for the barrier test derivative. -/
def wholeLineGradientDissipation (φx : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ, φx x * φx x

/-- Bounds used by the whole-line chemotaxis cross-control atom.

`Vx_bound` is deliberately a hypothesis field: the resolvent estimate proving
such a bound is a separate atom. -/
structure WholeLineChemotaxisCrossBounds
    (p : CMParams) (φ U Vx : ℝ → ℝ) (E : ℝ) where
  Umax : ℝ
  B : ℝ
  Cexcess : ℝ
  Umax_nonneg : 0 ≤ Umax
  B_nonneg : 0 ≤ B
  Cexcess_nonneg : 0 ≤ Cexcess
  U_nonneg : ∀ x, 0 ≤ U x
  U_le_Umax : ∀ x, U x ≤ Umax
  Vx_bound : ∀ x, |Vx x| ≤ B
  excess_indicator_integrable : Integrable (wholeLineExcessIndicator φ)
  excess_indicator_energy_control :
    (∫ x : ℝ, wholeLineExcessIndicator φ x) ≤ Cexcess * E

namespace WholeLineChemotaxisCrossBounds

/-- Explicit Gronwall coefficient coming from Young plus `L∞` and
excess-set/E control. -/
def K {p : CMParams} {φ U Vx : ℝ → ℝ} {E : ℝ}
    (H : WholeLineChemotaxisCrossBounds p φ U Vx E) : ℝ :=
  (p.χ ^ 2 / 2) * ((H.Umax ^ p.m * H.B) * (H.Umax ^ p.m * H.B)) * H.Cexcess

theorem K_nonneg {p : CMParams} {φ U Vx : ℝ → ℝ} {E : ℝ}
    (H : WholeLineChemotaxisCrossBounds p φ U Vx E) : 0 ≤ H.K := by
  have hcoef : 0 ≤ p.χ ^ 2 / 2 := by
    exact div_nonneg (sq_nonneg p.χ) (by norm_num)
  exact mul_nonneg (mul_nonneg hcoef (mul_self_nonneg (H.Umax ^ p.m * H.B)))
    H.Cexcess_nonneg

end WholeLineChemotaxisCrossBounds

/-- Pointwise Young inequality in the normalization used by the cross-control:
`-χ ab ≤ 1/2 a² + χ²/2 b²`. -/
private theorem chemotaxis_young_pointwise (χ a b : ℝ) :
    -χ * (a * b) ≤ (1 / 2) * (a * a) + (χ ^ 2 / 2) * (b * b) := by
  have hle_abs : -χ * (a * b) ≤ |χ| * |a * b| := by
    calc
      -χ * (a * b) ≤ |-χ * (a * b)| := le_abs_self _
      _ = |χ| * |a * b| := by simp [abs_mul]
  have hyoung : |χ| * |a * b| ≤ (1 / 2) * (a * a) + (χ ^ 2 / 2) * (b * b) := by
    rw [abs_mul]
    have hs : 0 ≤ (|a| - |χ| * |b|) ^ 2 := sq_nonneg _
    have hχsq : |χ| ^ 2 = χ ^ 2 := sq_abs χ
    have hasq : |a| ^ 2 = a ^ 2 := sq_abs a
    have hbsq : |b| ^ 2 = b ^ 2 := sq_abs b
    nlinarith
  exact le_trans hle_abs hyoung

/-- Pure whole-line Young absorption for a supplied post-IBP weight. -/
theorem wholeLine_chemotaxisCrossControl_young
    {χ K E : ℝ} {φx W : ℝ → ℝ}
    (hφx_sq_int : Integrable (fun x : ℝ => φx x * φx x))
    (hW_sq_int : Integrable (fun x : ℝ => W x * W x))
    (hcross_int : Integrable (fun x : ℝ => φx x * W x))
    (hW_control :
      (χ ^ 2 / 2) * (∫ x : ℝ, W x * W x) ≤ K * E) :
    -χ * (∫ x : ℝ, φx x * W x) ≤
      (1 / 2) * wholeLineGradientDissipation φx + K * E := by
  have hleft_int : Integrable (fun x : ℝ => -χ * (φx x * W x)) :=
    hcross_int.const_mul _
  have hright_int : Integrable
      (fun x : ℝ => (1 / 2) * (φx x * φx x) + (χ ^ 2 / 2) * (W x * W x)) :=
    (hφx_sq_int.const_mul _).add (hW_sq_int.const_mul _)
  have hmono :
      (∫ x : ℝ, -χ * (φx x * W x)) ≤
        ∫ x : ℝ, (1 / 2) * (φx x * φx x) + (χ ^ 2 / 2) * (W x * W x) :=
    integral_mono hleft_int hright_int
      (fun x => chemotaxis_young_pointwise χ (φx x) (W x))
  calc
    -χ * (∫ x : ℝ, φx x * W x)
        = ∫ x : ℝ, -χ * (φx x * W x) := by
          rw [integral_const_mul]
    _ ≤ ∫ x : ℝ, (1 / 2) * (φx x * φx x) + (χ ^ 2 / 2) * (W x * W x) := hmono
    _ = (1 / 2) * wholeLineGradientDissipation φx +
          (χ ^ 2 / 2) * (∫ x : ℝ, W x * W x) := by
          rw [integral_add (hφx_sq_int.const_mul _) (hW_sq_int.const_mul _)]
          rw [integral_const_mul, integral_const_mul, wholeLineGradientDissipation]
    _ ≤ (1 / 2) * wholeLineGradientDissipation φx + K * E :=
          by
            have h := add_le_add_left hW_control
              ((1 / 2) * wholeLineGradientDissipation φx)
            simpa [add_comm, add_left_comm, add_assoc] using h

/-- The `L∞` consequence of the `U` bound and the carried `V_x` bound. -/
private theorem wholeLineChemotaxisWeight_abs_le
    (p : CMParams) {φ U Vx : ℝ → ℝ} {E : ℝ}
    (H : WholeLineChemotaxisCrossBounds p φ U Vx E) (x : ℝ) :
    |wholeLineChemotaxisWeight p U Vx x| ≤ H.Umax ^ p.m * H.B := by
  have hm_nonneg : 0 ≤ p.m := le_trans zero_le_one p.hm
  have hUpow_nonneg : 0 ≤ (U x) ^ p.m :=
    Real.rpow_nonneg (H.U_nonneg x) _
  have hUmaxpow_nonneg : 0 ≤ H.Umax ^ p.m :=
    Real.rpow_nonneg H.Umax_nonneg _
  have hUpow_le : (U x) ^ p.m ≤ H.Umax ^ p.m :=
    Real.rpow_le_rpow (H.U_nonneg x) (H.U_le_Umax x) hm_nonneg
  calc
    |wholeLineChemotaxisWeight p U Vx x|
        = (U x) ^ p.m * |Vx x| := by
          simp [wholeLineChemotaxisWeight, abs_mul, abs_of_nonneg hUpow_nonneg]
    _ ≤ H.Umax ^ p.m * H.B :=
        mul_le_mul hUpow_le (H.Vx_bound x) (abs_nonneg _) hUmaxpow_nonneg

/-- Square of the restricted weight is bounded by the `L∞` square times the
excess indicator. -/
private theorem wholeLineRestrictedChemotaxisWeight_sq_le
    (p : CMParams) {φ U Vx : ℝ → ℝ} {E : ℝ}
    (H : WholeLineChemotaxisCrossBounds p φ U Vx E) (x : ℝ) :
    wholeLineRestrictedChemotaxisWeight p φ U Vx x *
        wholeLineRestrictedChemotaxisWeight p φ U Vx x ≤
      ((H.Umax ^ p.m * H.B) * (H.Umax ^ p.m * H.B)) *
        wholeLineExcessIndicator φ x := by
  by_cases hx : 0 < φ x
  · have hA_nonneg : 0 ≤ H.Umax ^ p.m * H.B :=
      mul_nonneg (Real.rpow_nonneg H.Umax_nonneg _) H.B_nonneg
    have habs := wholeLineChemotaxisWeight_abs_le p H x
    have hsq :
        wholeLineChemotaxisWeight p U Vx x ^ 2 ≤ (H.Umax ^ p.m * H.B) ^ 2 := by
      exact sq_le_sq.mpr (by simpa [abs_of_nonneg hA_nonneg] using habs)
    calc
      wholeLineRestrictedChemotaxisWeight p φ U Vx x *
          wholeLineRestrictedChemotaxisWeight p φ U Vx x
          = wholeLineChemotaxisWeight p U Vx x ^ 2 := by
            simp [wholeLineRestrictedChemotaxisWeight, wholeLineExcessIndicator, hx, pow_two]
      _ ≤ (H.Umax ^ p.m * H.B) ^ 2 := hsq
      _ = ((H.Umax ^ p.m * H.B) * (H.Umax ^ p.m * H.B)) *
            wholeLineExcessIndicator φ x := by
            simp [wholeLineExcessIndicator, hx, pow_two]
  · simp [wholeLineRestrictedChemotaxisWeight, wholeLineExcessIndicator, hx]

/-- The restricted weight square is controlled by `K·E` with the Young
coefficient included. -/
private theorem wholeLineRestrictedChemotaxisWeight_sq_integral_control
    (p : CMParams) {φ U Vx : ℝ → ℝ} {E : ℝ}
    (H : WholeLineChemotaxisCrossBounds p φ U Vx E)
    (hrestricted_sq_int : Integrable (fun x : ℝ =>
      wholeLineRestrictedChemotaxisWeight p φ U Vx x *
      wholeLineRestrictedChemotaxisWeight p φ U Vx x)) :
    (p.χ ^ 2 / 2) *
        (∫ x : ℝ,
          wholeLineRestrictedChemotaxisWeight p φ U Vx x *
          wholeLineRestrictedChemotaxisWeight p φ U Vx x) ≤
      H.K * E := by
  set A2 : ℝ := (H.Umax ^ p.m * H.B) * (H.Umax ^ p.m * H.B) with hA2
  have hA2_nonneg : 0 ≤ A2 := by
    rw [hA2]
    exact mul_self_nonneg _
  have hright_int : Integrable (fun x : ℝ => A2 * wholeLineExcessIndicator φ x) :=
    H.excess_indicator_integrable.const_mul _
  have hsq_bound :
      (∫ x : ℝ,
        wholeLineRestrictedChemotaxisWeight p φ U Vx x *
        wholeLineRestrictedChemotaxisWeight p φ U Vx x) ≤
        ∫ x : ℝ, A2 * wholeLineExcessIndicator φ x := by
    refine integral_mono hrestricted_sq_int hright_int ?_
    intro x
    simpa [A2, hA2] using wholeLineRestrictedChemotaxisWeight_sq_le p H x
  have hright_eval :
      (∫ x : ℝ, A2 * wholeLineExcessIndicator φ x)
        = A2 * (∫ x : ℝ, wholeLineExcessIndicator φ x) := by
    rw [integral_const_mul]
  have hsq_control :
      (∫ x : ℝ,
        wholeLineRestrictedChemotaxisWeight p φ U Vx x *
        wholeLineRestrictedChemotaxisWeight p φ U Vx x) ≤
        A2 * (H.Cexcess * E) := by
    calc
      (∫ x : ℝ,
        wholeLineRestrictedChemotaxisWeight p φ U Vx x *
        wholeLineRestrictedChemotaxisWeight p φ U Vx x)
          ≤ ∫ x : ℝ, A2 * wholeLineExcessIndicator φ x := hsq_bound
      _ = A2 * (∫ x : ℝ, wholeLineExcessIndicator φ x) := hright_eval
      _ ≤ A2 * (H.Cexcess * E) :=
          mul_le_mul_of_nonneg_left H.excess_indicator_energy_control hA2_nonneg
  have hcoef_nonneg : 0 ≤ p.χ ^ 2 / 2 := by
    exact div_nonneg (sq_nonneg p.χ) (by norm_num)
  calc
    (p.χ ^ 2 / 2) *
        (∫ x : ℝ,
          wholeLineRestrictedChemotaxisWeight p φ U Vx x *
          wholeLineRestrictedChemotaxisWeight p φ U Vx x)
        ≤ (p.χ ^ 2 / 2) * (A2 * (H.Cexcess * E)) :=
          mul_le_mul_of_nonneg_left hsq_control hcoef_nonneg
    _ = H.K * E := by
          rw [WholeLineChemotaxisCrossBounds.K, hA2]
          ring

/-- **Whole-line chemotaxis cross-control, post-IBP form.**

If `φ_x` is supported on the strict excess set, `U` is bounded by `Umax`,
`V_x` is bounded by the field `B`, and the excess indicator is controlled by
the energy `E`, then the chemotaxis cross term is absorbed into half of the
diffusion dissipation plus `K·E`. -/
theorem wholeLine_chemotaxisCrossControl_postIBP
    (p : CMParams) {φ φx U Vx : ℝ → ℝ} {E : ℝ}
    (H : WholeLineChemotaxisCrossBounds p φ U Vx E)
    (hφx_zero_off_excess : ∀ x, ¬ 0 < φ x → φx x = 0)
    (hφx_sq_int : Integrable (fun x : ℝ => φx x * φx x))
    (hcross_int : Integrable (fun x : ℝ =>
      φx x * wholeLineChemotaxisWeight p U Vx x))
    (hrestricted_sq_int : Integrable (fun x : ℝ =>
      wholeLineRestrictedChemotaxisWeight p φ U Vx x *
      wholeLineRestrictedChemotaxisWeight p φ U Vx x)) :
    -p.χ * (∫ x : ℝ, φx x * wholeLineChemotaxisWeight p U Vx x) ≤
      (1 / 2) * wholeLineGradientDissipation φx + H.K * E := by
  have hcross_eq :
      (∫ x : ℝ, φx x * wholeLineChemotaxisWeight p U Vx x)
        = ∫ x : ℝ, φx x * wholeLineRestrictedChemotaxisWeight p φ U Vx x := by
    refine integral_congr_ae (Eventually.of_forall ?_)
    intro x
    by_cases hx : 0 < φ x
    · simp [wholeLineRestrictedChemotaxisWeight, wholeLineExcessIndicator, hx]
    · have hzero := hφx_zero_off_excess x hx
      simp [wholeLineRestrictedChemotaxisWeight, wholeLineExcessIndicator, hx, hzero]
  have hrestricted_cross_int : Integrable (fun x : ℝ =>
      φx x * wholeLineRestrictedChemotaxisWeight p φ U Vx x) := by
    refine hcross_int.congr ?_
    refine Eventually.of_forall ?_
    intro x
    by_cases hx : 0 < φ x
    · simp [wholeLineRestrictedChemotaxisWeight, wholeLineExcessIndicator, hx]
    · have hzero := hφx_zero_off_excess x hx
      simp [wholeLineRestrictedChemotaxisWeight, wholeLineExcessIndicator, hx, hzero]
  rw [hcross_eq]
  exact wholeLine_chemotaxisCrossControl_young
    (χ := p.χ) (K := H.K) (E := E)
    (φx := φx) (W := wholeLineRestrictedChemotaxisWeight p φ U Vx)
    hφx_sq_int hrestricted_sq_int hrestricted_cross_int
    (wholeLineRestrictedChemotaxisWeight_sq_integral_control p H hrestricted_sq_int)

/-- Existential form of the post-IBP cross-control with an explicitly nonnegative
Gronwall coefficient. -/
theorem wholeLine_chemotaxisCrossControl_postIBP_exists
    (p : CMParams) {φ φx U Vx : ℝ → ℝ} {E : ℝ}
    (H : WholeLineChemotaxisCrossBounds p φ U Vx E)
    (hφx_zero_off_excess : ∀ x, ¬ 0 < φ x → φx x = 0)
    (hφx_sq_int : Integrable (fun x : ℝ => φx x * φx x))
    (hcross_int : Integrable (fun x : ℝ =>
      φx x * wholeLineChemotaxisWeight p U Vx x))
    (hrestricted_sq_int : Integrable (fun x : ℝ =>
      wholeLineRestrictedChemotaxisWeight p φ U Vx x *
      wholeLineRestrictedChemotaxisWeight p φ U Vx x)) :
    ∃ K : ℝ, 0 ≤ K ∧
      -p.χ * (∫ x : ℝ, φx x * wholeLineChemotaxisWeight p U Vx x) ≤
        (1 / 2) * wholeLineGradientDissipation φx + K * E := by
  exact ⟨H.K, H.K_nonneg,
    wholeLine_chemotaxisCrossControl_postIBP p H hφx_zero_off_excess
      hφx_sq_int hcross_int hrestricted_sq_int⟩

#print axioms wholeLine_chemotaxisCrossControl_young
#print axioms wholeLine_chemotaxisCrossControl_postIBP
#print axioms wholeLine_chemotaxisCrossControl_postIBP_exists

end ShenWork.PaperOne
