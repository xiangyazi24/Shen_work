import ShenWork.PaperOne.WholeLineFrozenSignal
import ShenWork.PaperOne.WholeLineUpperBarrierEnergyStepsBuilder

open MeasureTheory Filter

noncomputable section

namespace ShenWork.PaperOne

/-- The explicit excess-set constant controlling the restricted chemotaxis
weight square. -/
def wholeLineChemotaxisRestrictedCgrad
    {p : CMParams} {φ U Vx : ℝ → ℝ} {E : ℝ}
    (H : WholeLineChemotaxisCrossBounds p φ U Vx E) : ℝ :=
  ((H.Umax ^ p.m * H.B) * (H.Umax ^ p.m * H.B)) * H.Cexcess

theorem wholeLineChemotaxisRestrictedCgrad_nonneg
    {p : CMParams} {φ U Vx : ℝ → ℝ} {E : ℝ}
    (H : WholeLineChemotaxisCrossBounds p φ U Vx E) :
    0 ≤ wholeLineChemotaxisRestrictedCgrad H := by
  have hA2 : 0 ≤ (H.Umax ^ p.m * H.B) * (H.Umax ^ p.m * H.B) :=
    mul_self_nonneg _
  exact mul_nonneg hA2 H.Cexcess_nonneg

theorem wholeLineChemotaxisWeight_abs_le_bound
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

theorem wholeLineRestrictedChemotaxisWeight_sq_le_bound
    (p : CMParams) {φ U Vx : ℝ → ℝ} {E : ℝ}
    (H : WholeLineChemotaxisCrossBounds p φ U Vx E) (x : ℝ) :
    wholeLineRestrictedChemotaxisWeight p φ U Vx x *
        wholeLineRestrictedChemotaxisWeight p φ U Vx x ≤
      ((H.Umax ^ p.m * H.B) * (H.Umax ^ p.m * H.B)) *
        wholeLineExcessIndicator φ x := by
  by_cases hx : 0 < φ x
  · have hA_nonneg : 0 ≤ H.Umax ^ p.m * H.B :=
      mul_nonneg (Real.rpow_nonneg H.Umax_nonneg _) H.B_nonneg
    have habs := wholeLineChemotaxisWeight_abs_le_bound p H x
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

/-- Flux-gradient control for the restricted chemotaxis weight.  The only
measure-theoretic input is the named excess-set/E control carried by `H`. -/
theorem wholeLineRestrictedChemotaxisWeight_gradient_control
    (p : CMParams) {φ U Vx : ℝ → ℝ} {E : ℝ}
    (H : WholeLineChemotaxisCrossBounds p φ U Vx E)
    (hrestricted_sq_int : Integrable (fun x : ℝ =>
      wholeLineRestrictedChemotaxisWeight p φ U Vx x *
      wholeLineRestrictedChemotaxisWeight p φ U Vx x)) :
    wholeLineGradientDissipation (wholeLineRestrictedChemotaxisWeight p φ U Vx) ≤
      wholeLineChemotaxisRestrictedCgrad H * E := by
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
    simpa [A2, hA2] using wholeLineRestrictedChemotaxisWeight_sq_le_bound p H x
  have hright_eval :
      (∫ x : ℝ, A2 * wholeLineExcessIndicator φ x)
        = A2 * (∫ x : ℝ, wholeLineExcessIndicator φ x) := by
    rw [integral_const_mul]
  calc
    wholeLineGradientDissipation (wholeLineRestrictedChemotaxisWeight p φ U Vx)
        = ∫ x : ℝ,
          wholeLineRestrictedChemotaxisWeight p φ U Vx x *
          wholeLineRestrictedChemotaxisWeight p φ U Vx x := rfl
    _ ≤ ∫ x : ℝ, A2 * wholeLineExcessIndicator φ x := hsq_bound
    _ = A2 * (∫ x : ℝ, wholeLineExcessIndicator φ x) := hright_eval
    _ ≤ A2 * (H.Cexcess * E) :=
        mul_le_mul_of_nonneg_left H.excess_indicator_energy_control hA2_nonneg
    _ = wholeLineChemotaxisRestrictedCgrad H * E := by
        rw [wholeLineChemotaxisRestrictedCgrad, hA2]
        ring

theorem frozenSignal_Vx_bound_one {γ : ℝ} (hγ : 1 ≤ γ) {u : ℝ → ℝ}
    (hu_cont : Continuous u) (hu_nonneg : ∀ x, 0 ≤ u x)
    (hu_le_one : ∀ x, u x ≤ 1) :
    ∀ x, |deriv (frozenSignal γ u) x| ≤ 1 := by
  intro x
  exact frozenSignal_grad_bound hγ hu_cont hu_nonneg hu_le_one x

/-- Cross-control bounds for a frozen signal, with `B = 1` supplied by
`frozenSignal_grad_bound`. -/
def wholeLineFrozenSignalCrossBounds
    (p : CMParams) {φ U u : ℝ → ℝ} {E Umax Cexcess : ℝ}
    (hUmax_nonneg : 0 ≤ Umax)
    (hCexcess_nonneg : 0 ≤ Cexcess)
    (hU_nonneg : ∀ x, 0 ≤ U x)
    (hU_le_Umax : ∀ x, U x ≤ Umax)
    (hu_cont : Continuous u)
    (hu_nonneg : ∀ x, 0 ≤ u x)
    (hu_le_one : ∀ x, u x ≤ 1)
    (hexcess_int : Integrable (wholeLineExcessIndicator φ))
    (hexcess_energy_control :
      (∫ x : ℝ, wholeLineExcessIndicator φ x) ≤ Cexcess * E) :
    WholeLineChemotaxisCrossBounds p φ U
      (fun x : ℝ => deriv (frozenSignal p.γ u) x) E where
  Umax := Umax
  B := 1
  Cexcess := Cexcess
  Umax_nonneg := hUmax_nonneg
  B_nonneg := by norm_num
  Cexcess_nonneg := hCexcess_nonneg
  U_nonneg := hU_nonneg
  U_le_Umax := hU_le_Umax
  Vx_bound := frozenSignal_Vx_bound_one p.hγ hu_cont hu_nonneg hu_le_one
  excess_indicator_integrable := hexcess_int
  excess_indicator_energy_control := hexcess_energy_control

def wholeLineFrozenSignalRestrictedCgrad
    (p : CMParams) (Umax Cexcess : ℝ) : ℝ :=
  ((Umax ^ p.m * 1) * (Umax ^ p.m * 1)) * Cexcess

def wholeLineFrozenSignalCrossAtomK
    (p : CMParams) (Umax Cexcess : ℝ) : ℝ :=
  (p.χ ^ 2 / 2) * ((Umax ^ p.m * 1) * (Umax ^ p.m * 1)) * Cexcess

def wholeLineFrozenSignalCrossK
    (p : CMParams) (Umax Cexcess Cgrad : ℝ) : ℝ :=
  Cgrad + 2 * wholeLineFrozenSignalCrossAtomK p Umax Cexcess

theorem wholeLineFrozenSignalRestrictedCgrad_eq_bounds
    (p : CMParams) {φ U u : ℝ → ℝ} {E Umax Cexcess : ℝ}
    (hUmax_nonneg : 0 ≤ Umax)
    (hCexcess_nonneg : 0 ≤ Cexcess)
    (hU_nonneg : ∀ x, 0 ≤ U x)
    (hU_le_Umax : ∀ x, U x ≤ Umax)
    (hu_cont : Continuous u)
    (hu_nonneg : ∀ x, 0 ≤ u x)
    (hu_le_one : ∀ x, u x ≤ 1)
    (hexcess_int : Integrable (wholeLineExcessIndicator φ))
    (hexcess_energy_control :
      (∫ x : ℝ, wholeLineExcessIndicator φ x) ≤ Cexcess * E) :
    wholeLineChemotaxisRestrictedCgrad
        (wholeLineFrozenSignalCrossBounds p hUmax_nonneg hCexcess_nonneg
          hU_nonneg hU_le_Umax hu_cont hu_nonneg hu_le_one
          hexcess_int hexcess_energy_control)
      = wholeLineFrozenSignalRestrictedCgrad p Umax Cexcess := by
  rfl

theorem wholeLineFrozenSignal_restricted_gradient_control
    (p : CMParams) {φ U u : ℝ → ℝ} {E Umax Cexcess : ℝ}
    (hUmax_nonneg : 0 ≤ Umax)
    (hCexcess_nonneg : 0 ≤ Cexcess)
    (hU_nonneg : ∀ x, 0 ≤ U x)
    (hU_le_Umax : ∀ x, U x ≤ Umax)
    (hu_cont : Continuous u)
    (hu_nonneg : ∀ x, 0 ≤ u x)
    (hu_le_one : ∀ x, u x ≤ 1)
    (hexcess_int : Integrable (wholeLineExcessIndicator φ))
    (hexcess_energy_control :
      (∫ x : ℝ, wholeLineExcessIndicator φ x) ≤ Cexcess * E)
    (hrestricted_sq_int : Integrable (fun x : ℝ =>
      wholeLineRestrictedChemotaxisWeight p φ U
          (fun y : ℝ => deriv (frozenSignal p.γ u) y) x *
        wholeLineRestrictedChemotaxisWeight p φ U
          (fun y : ℝ => deriv (frozenSignal p.γ u) y) x)) :
    wholeLineGradientDissipation
        (wholeLineRestrictedChemotaxisWeight p φ U
          (fun y : ℝ => deriv (frozenSignal p.γ u) y)) ≤
      wholeLineFrozenSignalRestrictedCgrad p Umax Cexcess * E := by
  have h :=
    wholeLineRestrictedChemotaxisWeight_gradient_control p
      (wholeLineFrozenSignalCrossBounds p hUmax_nonneg hCexcess_nonneg
        hU_nonneg hU_le_Umax hu_cont hu_nonneg hu_le_one
        hexcess_int hexcess_energy_control)
      hrestricted_sq_int
  simpa [wholeLineFrozenSignalRestrictedCgrad, wholeLineChemotaxisRestrictedCgrad,
    wholeLineFrozenSignalCrossBounds] using h

theorem wholeLineChemotaxis_K_control_self
    {p : CMParams} {φ U Vx : ℝ → ℝ} {E Cgrad : ℝ}
    (H : WholeLineChemotaxisCrossBounds p φ U Vx E) :
    Cgrad + 2 * H.K ≤ Cgrad + 2 * H.K := by
  rfl

theorem wholeLineFrozenSignal_K_control
    (p : CMParams) {φ U u : ℝ → ℝ} {E Umax Cexcess Cgrad : ℝ}
    (hUmax_nonneg : 0 ≤ Umax)
    (hCexcess_nonneg : 0 ≤ Cexcess)
    (hU_nonneg : ∀ x, 0 ≤ U x)
    (hU_le_Umax : ∀ x, U x ≤ Umax)
    (hu_cont : Continuous u)
    (hu_nonneg : ∀ x, 0 ≤ u x)
    (hu_le_one : ∀ x, u x ≤ 1)
    (hexcess_int : Integrable (wholeLineExcessIndicator φ))
    (hexcess_energy_control :
      (∫ x : ℝ, wholeLineExcessIndicator φ x) ≤ Cexcess * E) :
    Cgrad + 2 *
        (wholeLineFrozenSignalCrossBounds p hUmax_nonneg hCexcess_nonneg
          hU_nonneg hU_le_Umax hu_cont hu_nonneg hu_le_one
          hexcess_int hexcess_energy_control).K ≤
      wholeLineFrozenSignalCrossK p Umax Cexcess Cgrad := by
  rfl

/-- Time-dependent notation for the frozen elliptic signal generated by `U`. -/
def wholeLineFrozenSignalTime (p : CMParams) (U : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t => frozenSignal p.γ (U t)

def wholeLineUpperFrozenSignalCrossBounds
    (p : CMParams) {T : ℝ} {U : ℝ → ℝ → ℝ} {hi Umax Cexcess : ℝ}
    (hUmax_nonneg : 0 ≤ Umax)
    (hCexcess_nonneg : 0 ≤ Cexcess)
    (hU_nonneg : ∀ t x, 0 ≤ U t x)
    (hU_le_one : ∀ t x, U t x ≤ 1)
    (hU_le_Umax : ∀ t x, U t x ≤ Umax)
    (hU_cont : ∀ t, 0 < t → t < T → Continuous (U t))
    (hexcess_int : ∀ t, 0 < t → t < T →
      Integrable (wholeLineExcessIndicator (wholeLineUpperBarrierTest U hi t)))
    (hexcess_energy_control : ∀ t, 0 < t → t < T →
      (∫ x : ℝ, wholeLineExcessIndicator (wholeLineUpperBarrierTest U hi t) x) ≤
        Cexcess * wholeLineUpperExcessEnergy U hi t) :
    ∀ t, 0 < t → t < T →
      WholeLineChemotaxisCrossBounds p
        (wholeLineUpperBarrierTest U hi t) (U t)
        (fun x : ℝ => deriv ((wholeLineFrozenSignalTime p U) t) x)
        (wholeLineUpperExcessEnergy U hi t) := by
  intro t ht0 htT
  exact wholeLineFrozenSignalCrossBounds p hUmax_nonneg hCexcess_nonneg
    (hU_nonneg t) (hU_le_Umax t) (hU_cont t ht0 htT)
    (hU_nonneg t) (hU_le_one t)
    (hexcess_int t ht0 htT) (hexcess_energy_control t ht0 htT)

def wholeLineLowerFrozenSignalCrossBounds
    (p : CMParams) {T : ℝ} {U : ℝ → ℝ → ℝ} {lo Umax Cexcess : ℝ}
    (hUmax_nonneg : 0 ≤ Umax)
    (hCexcess_nonneg : 0 ≤ Cexcess)
    (hU_nonneg : ∀ t x, 0 ≤ U t x)
    (hU_le_one : ∀ t x, U t x ≤ 1)
    (hU_le_Umax : ∀ t x, U t x ≤ Umax)
    (hU_cont : ∀ t, 0 < t → t < T → Continuous (U t))
    (hexcess_int : ∀ t, 0 < t → t < T →
      Integrable (wholeLineExcessIndicator (wholeLineLowerBarrierTest U lo t)))
    (hexcess_energy_control : ∀ t, 0 < t → t < T →
      (∫ x : ℝ, wholeLineExcessIndicator (wholeLineLowerBarrierTest U lo t) x) ≤
        Cexcess * wholeLineLowerDeficitEnergy U lo t) :
    ∀ t, 0 < t → t < T →
      WholeLineChemotaxisCrossBounds p
        (wholeLineLowerBarrierTest U lo t) (U t)
        (fun x : ℝ => deriv ((wholeLineFrozenSignalTime p U) t) x)
        (wholeLineLowerDeficitEnergy U lo t) := by
  intro t ht0 htT
  exact wholeLineFrozenSignalCrossBounds p hUmax_nonneg hCexcess_nonneg
    (hU_nonneg t) (hU_le_Umax t) (hU_cont t ht0 htT)
    (hU_nonneg t) (hU_le_one t)
    (hexcess_int t ht0 htT) (hexcess_energy_control t ht0 htT)

theorem wholeLineUpperFrozenSignal_restricted_gradient_control
    (p : CMParams) {T : ℝ} {U : ℝ → ℝ → ℝ} {hi Umax Cexcess : ℝ}
    (hUmax_nonneg : 0 ≤ Umax)
    (hCexcess_nonneg : 0 ≤ Cexcess)
    (hU_nonneg : ∀ t x, 0 ≤ U t x)
    (hU_le_one : ∀ t x, U t x ≤ 1)
    (hU_le_Umax : ∀ t x, U t x ≤ Umax)
    (hU_cont : ∀ t, 0 < t → t < T → Continuous (U t))
    (hexcess_int : ∀ t, 0 < t → t < T →
      Integrable (wholeLineExcessIndicator (wholeLineUpperBarrierTest U hi t)))
    (hexcess_energy_control : ∀ t, 0 < t → t < T →
      (∫ x : ℝ, wholeLineExcessIndicator (wholeLineUpperBarrierTest U hi t) x) ≤
        Cexcess * wholeLineUpperExcessEnergy U hi t)
    (hrestricted_sq_int : ∀ t, 0 < t → t < T →
      Integrable (fun x : ℝ =>
        wholeLineRestrictedChemotaxisWeight p
            (wholeLineUpperBarrierTest U hi t) (U t)
            (fun y : ℝ => deriv ((wholeLineFrozenSignalTime p U) t) y) x *
          wholeLineRestrictedChemotaxisWeight p
            (wholeLineUpperBarrierTest U hi t) (U t)
            (fun y : ℝ => deriv ((wholeLineFrozenSignalTime p U) t) y) x)) :
    ∀ t, 0 < t → t < T →
      wholeLineGradientDissipation
          (wholeLineRestrictedChemotaxisWeight p
            (wholeLineUpperBarrierTest U hi t) (U t)
            (fun y : ℝ => deriv ((wholeLineFrozenSignalTime p U) t) y)) ≤
        wholeLineFrozenSignalRestrictedCgrad p Umax Cexcess *
          wholeLineUpperExcessEnergy U hi t := by
  intro t ht0 htT
  exact wholeLineFrozenSignal_restricted_gradient_control p
    hUmax_nonneg hCexcess_nonneg (hU_nonneg t) (hU_le_Umax t)
    (hU_cont t ht0 htT) (hU_nonneg t) (hU_le_one t)
    (hexcess_int t ht0 htT) (hexcess_energy_control t ht0 htT)
    (hrestricted_sq_int t ht0 htT)

theorem wholeLineLowerFrozenSignal_restricted_gradient_control
    (p : CMParams) {T : ℝ} {U : ℝ → ℝ → ℝ} {lo Umax Cexcess : ℝ}
    (hUmax_nonneg : 0 ≤ Umax)
    (hCexcess_nonneg : 0 ≤ Cexcess)
    (hU_nonneg : ∀ t x, 0 ≤ U t x)
    (hU_le_one : ∀ t x, U t x ≤ 1)
    (hU_le_Umax : ∀ t x, U t x ≤ Umax)
    (hU_cont : ∀ t, 0 < t → t < T → Continuous (U t))
    (hexcess_int : ∀ t, 0 < t → t < T →
      Integrable (wholeLineExcessIndicator (wholeLineLowerBarrierTest U lo t)))
    (hexcess_energy_control : ∀ t, 0 < t → t < T →
      (∫ x : ℝ, wholeLineExcessIndicator (wholeLineLowerBarrierTest U lo t) x) ≤
        Cexcess * wholeLineLowerDeficitEnergy U lo t)
    (hrestricted_sq_int : ∀ t, 0 < t → t < T →
      Integrable (fun x : ℝ =>
        wholeLineRestrictedChemotaxisWeight p
            (wholeLineLowerBarrierTest U lo t) (U t)
            (fun y : ℝ => deriv ((wholeLineFrozenSignalTime p U) t) y) x *
          wholeLineRestrictedChemotaxisWeight p
            (wholeLineLowerBarrierTest U lo t) (U t)
            (fun y : ℝ => deriv ((wholeLineFrozenSignalTime p U) t) y) x)) :
    ∀ t, 0 < t → t < T →
      wholeLineGradientDissipation
          (wholeLineRestrictedChemotaxisWeight p
            (wholeLineLowerBarrierTest U lo t) (U t)
            (fun y : ℝ => deriv ((wholeLineFrozenSignalTime p U) t) y)) ≤
        wholeLineFrozenSignalRestrictedCgrad p Umax Cexcess *
          wholeLineLowerDeficitEnergy U lo t := by
  intro t ht0 htT
  exact wholeLineFrozenSignal_restricted_gradient_control p
    hUmax_nonneg hCexcess_nonneg (hU_nonneg t) (hU_le_Umax t)
    (hU_cont t ht0 htT) (hU_nonneg t) (hU_le_one t)
    (hexcess_int t ht0 htT) (hexcess_energy_control t ht0 htT)
    (hrestricted_sq_int t ht0 htT)

theorem wholeLineUpperFrozenSignal_K_control
    (p : CMParams) {T : ℝ} {U : ℝ → ℝ → ℝ} {hi Umax Cexcess Cgrad : ℝ}
    (hUmax_nonneg : 0 ≤ Umax)
    (hCexcess_nonneg : 0 ≤ Cexcess)
    (hU_nonneg : ∀ t x, 0 ≤ U t x)
    (hU_le_one : ∀ t x, U t x ≤ 1)
    (hU_le_Umax : ∀ t x, U t x ≤ Umax)
    (hU_cont : ∀ t, 0 < t → t < T → Continuous (U t))
    (hexcess_int : ∀ t, 0 < t → t < T →
      Integrable (wholeLineExcessIndicator (wholeLineUpperBarrierTest U hi t)))
    (hexcess_energy_control : ∀ t, 0 < t → t < T →
      (∫ x : ℝ, wholeLineExcessIndicator (wholeLineUpperBarrierTest U hi t) x) ≤
        Cexcess * wholeLineUpperExcessEnergy U hi t) :
    ∀ t (ht0 : 0 < t) (htT : t < T),
      Cgrad + 2 *
          (wholeLineUpperFrozenSignalCrossBounds p hUmax_nonneg hCexcess_nonneg
            hU_nonneg hU_le_one hU_le_Umax hU_cont
            hexcess_int hexcess_energy_control t ht0 htT).K ≤
        wholeLineFrozenSignalCrossK p Umax Cexcess Cgrad := by
  intro t ht0 htT
  rfl

theorem wholeLineLowerFrozenSignal_K_control
    (p : CMParams) {T : ℝ} {U : ℝ → ℝ → ℝ} {lo Umax Cexcess Cgrad : ℝ}
    (hUmax_nonneg : 0 ≤ Umax)
    (hCexcess_nonneg : 0 ≤ Cexcess)
    (hU_nonneg : ∀ t x, 0 ≤ U t x)
    (hU_le_one : ∀ t x, U t x ≤ 1)
    (hU_le_Umax : ∀ t x, U t x ≤ Umax)
    (hU_cont : ∀ t, 0 < t → t < T → Continuous (U t))
    (hexcess_int : ∀ t, 0 < t → t < T →
      Integrable (wholeLineExcessIndicator (wholeLineLowerBarrierTest U lo t)))
    (hexcess_energy_control : ∀ t, 0 < t → t < T →
      (∫ x : ℝ, wholeLineExcessIndicator (wholeLineLowerBarrierTest U lo t) x) ≤
        Cexcess * wholeLineLowerDeficitEnergy U lo t) :
    ∀ t (ht0 : 0 < t) (htT : t < T),
      Cgrad + 2 *
          (wholeLineLowerFrozenSignalCrossBounds p hUmax_nonneg hCexcess_nonneg
            hU_nonneg hU_le_one hU_le_Umax hU_cont
            hexcess_int hexcess_energy_control t ht0 htT).K ≤
        wholeLineFrozenSignalCrossK p Umax Cexcess Cgrad := by
  intro t ht0 htT
  rfl

#print axioms wholeLineRestrictedChemotaxisWeight_gradient_control
#print axioms frozenSignal_Vx_bound_one
#print axioms wholeLineFrozenSignalCrossBounds
#print axioms wholeLineFrozenSignal_restricted_gradient_control
#print axioms wholeLineFrozenSignal_K_control
#print axioms wholeLineUpperFrozenSignal_restricted_gradient_control
#print axioms wholeLineLowerFrozenSignal_restricted_gradient_control
#print axioms wholeLineUpperFrozenSignal_K_control
#print axioms wholeLineLowerFrozenSignal_K_control

end ShenWork.PaperOne
