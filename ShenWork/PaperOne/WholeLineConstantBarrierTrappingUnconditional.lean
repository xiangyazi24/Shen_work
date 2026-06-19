import ShenWork.PaperOne.WholeLineChemotaxisIBP
import ShenWork.PaperOne.WholeLineChemotaxisResidualDischarge

open Filter MeasureTheory
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

def wholeLineUpperFrozenRestrictedFlux
    (p : CMParams) (U : ℝ → ℝ → ℝ) (hi t x : ℝ) : ℝ :=
  wholeLineRestrictedChemotaxisWeight p (wholeLineUpperBarrierTest U hi t) (U t)
    (fun y : ℝ => deriv ((wholeLineFrozenSignalTime p U) t) y) x

def wholeLineLowerFrozenRestrictedFlux
    (p : CMParams) (U : ℝ → ℝ → ℝ) (lo t x : ℝ) : ℝ :=
  wholeLineRestrictedChemotaxisWeight p (wholeLineLowerBarrierTest U lo t) (U t)
    (fun y : ℝ => deriv ((wholeLineFrozenSignalTime p U) t) y) x

theorem wholeLineClassicalSolution_u_slice_continuous
    {p : CMParams} {T : ℝ} {U V : ℝ → ℝ → ℝ}
    (hsol : IsClassicalSolution p T U V) :
    ∀ t, 0 < t → t < T → Continuous (U t) := by
  intro t ht0 htT
  rw [continuous_iff_continuousAt]
  intro x
  exact (hsol.u_smooth t x ht0 htT).2.continuousAt

theorem wholeLineFrozenSignalRestrictedCgrad_one_nonneg
    (p : CMParams) {Cexcess : ℝ} (hCexcess_nonneg : 0 ≤ Cexcess) :
    0 ≤ wholeLineFrozenSignalRestrictedCgrad p 1 Cexcess := by
  unfold wholeLineFrozenSignalRestrictedCgrad
  exact mul_nonneg (mul_self_nonneg _) hCexcess_nonneg

theorem wholeLineFrozenSignalCrossAtomK_one_nonneg
    (p : CMParams) {Cexcess : ℝ} (hCexcess_nonneg : 0 ≤ Cexcess) :
    0 ≤ wholeLineFrozenSignalCrossAtomK p 1 Cexcess := by
  unfold wholeLineFrozenSignalCrossAtomK
  exact mul_nonneg
    (mul_nonneg (div_nonneg (sq_nonneg p.χ) (by norm_num)) (mul_self_nonneg _))
    hCexcess_nonneg

theorem wholeLineFrozenSignalCrossK_one_nonneg
    (p : CMParams) {Cexcess : ℝ} (hCexcess_nonneg : 0 ≤ Cexcess) :
    0 ≤ wholeLineFrozenSignalCrossK p 1 Cexcess
      (wholeLineFrozenSignalRestrictedCgrad p 1 Cexcess) := by
  unfold wholeLineFrozenSignalCrossK
  exact add_nonneg
    (wholeLineFrozenSignalRestrictedCgrad_one_nonneg p hCexcess_nonneg)
    (mul_nonneg (by norm_num)
      (wholeLineFrozenSignalCrossAtomK_one_nonneg p hCexcess_nonneg))

theorem wholeLineRestrictedChemotaxisWeight_mul_weight_integrable
    (p : CMParams) {φ U Vx : ℝ → ℝ}
    (hrestricted_sq_int : Integrable (fun x : ℝ =>
      wholeLineRestrictedChemotaxisWeight p φ U Vx x *
      wholeLineRestrictedChemotaxisWeight p φ U Vx x) volume) :
    Integrable (fun x : ℝ =>
      wholeLineRestrictedChemotaxisWeight p φ U Vx x *
      wholeLineChemotaxisWeight p U Vx x) volume := by
  refine hrestricted_sq_int.congr (Eventually.of_forall ?_)
  intro x
  by_cases hx : 0 < φ x
  · simp [wholeLineRestrictedChemotaxisWeight, wholeLineExcessIndicator, hx]
  · simp [wholeLineRestrictedChemotaxisWeight, wholeLineExcessIndicator, hx]

theorem wholeLineLowerBarrier_chemotaxis_postIBP_field
    (p : CMParams) {T : ℝ} {U V : ℝ → ℝ → ℝ} {lo : ℝ}
    (flux : ℝ → ℝ → ℝ)
    (hφ_deriv : ∀ t, 0 < t → t < T → ∀ x ∈ tsupport
        (wholeLineChemotaxisWeight p (U t) (fun y : ℝ => deriv (V t) y)),
        HasDerivAt (wholeLineLowerBarrierTest U lo t) (flux t x) x)
    (hweight_deriv : ∀ t, 0 < t → t < T → ∀ x ∈ tsupport
        (wholeLineLowerBarrierTest U lo t),
        HasDerivAt
          (wholeLineChemotaxisWeight p (U t) (fun y : ℝ => deriv (V t) y))
          (deriv (wholeLineChemotaxisWeight p (U t) (fun y : ℝ => deriv (V t) y)) x) x)
    (hlhs_int : ∀ t, 0 < t → t < T → Integrable (fun x : ℝ =>
      wholeLineLowerBarrierTest U lo t x *
        deriv (wholeLineChemotaxisWeight p (U t) (fun y : ℝ => deriv (V t) y)) x))
    (hflux_int : ∀ t, 0 < t → t < T → Integrable (fun x : ℝ =>
      flux t x * wholeLineChemotaxisWeight p (U t) (fun y : ℝ => deriv (V t) y) x))
    (hdecay_bot : ∀ t, 0 < t → t < T → Tendsto (fun x : ℝ =>
      wholeLineLowerBarrierTest U lo t x *
        wholeLineChemotaxisWeight p (U t) (fun y : ℝ => deriv (V t) y) x) atBot (𝓝 0))
    (hdecay_top : ∀ t, 0 < t → t < T → Tendsto (fun x : ℝ =>
      wholeLineLowerBarrierTest U lo t x *
        wholeLineChemotaxisWeight p (U t) (fun y : ℝ => deriv (V t) y) x) atTop (𝓝 0)) :
    ∀ t, 0 < t → t < T →
      -wholeLineLowerBarrierChemotaxisTerm p U V lo t =
        ∫ x : ℝ, flux t x *
          wholeLineChemotaxisWeight p (U t) (fun y : ℝ => deriv (V t) y) x := by
  intro t ht0 htT
  let φ := wholeLineLowerBarrierTest U lo t
  let g := wholeLineChemotaxisWeight p (U t) (fun y : ℝ => deriv (V t) y)
  have hIBP := wholeLine_chemotaxis_postIBP_with_derivatives φ (flux t) g
    (fun x : ℝ => deriv g x) (hφ_deriv t ht0 htT)
    (hweight_deriv t ht0 htT) (hlhs_int t ht0 htT)
    (hflux_int t ht0 htT) (hdecay_bot t ht0 htT) (hdecay_top t ht0 htT)
  calc
    -wholeLineLowerBarrierChemotaxisTerm p U V lo t
        = -(∫ x : ℝ, φ x * deriv g x) := by
          rfl
    _ = ∫ x : ℝ, flux t x *
        wholeLineChemotaxisWeight p (U t) (fun y : ℝ => deriv (V t) y) x := by
          rw [hIBP]
          simp [g]

theorem wholeLineUpperExcess_square_integrable_of_timeData
    {T : ℝ} {U : ℝ → ℝ → ℝ} {hi t : ℝ}
    (H : WholeLineUpperTimeLeibnizData T U hi)
    (ht0 : 0 < t) (htT : t < T) :
    Integrable (fun x : ℝ => (max (U t x - hi) 0) ^ 2) volume := by
  have h := (H.F_int t ht0 htT).const_mul (2 : ℝ)
  simpa [wholeLineHalfEnergyIntegrand, wholeLineUpperExcessProfile] using h

theorem wholeLineLowerDeficit_square_integrable_of_timeData
    {T : ℝ} {U : ℝ → ℝ → ℝ} {lo t : ℝ}
    (H : WholeLineLowerTimeLeibnizData T U lo)
    (ht0 : 0 < t) (htT : t < T) :
    Integrable (fun x : ℝ => (max (lo - U t x) 0) ^ 2) volume := by
  have h := (H.F_int t ht0 htT).const_mul (2 : ℝ)
  simpa [wholeLineHalfEnergyIntegrand, wholeLineLowerDeficitProfile] using h

theorem wholeLineUpperExcessEnergy_zero_controls_of_integrable
    {U : ℝ → ℝ → ℝ} {hi t : ℝ}
    (hU_cont : Continuous (U t))
    (hint : Integrable (fun x : ℝ => (max (U t x - hi) 0) ^ 2) volume)
    (hE : wholeLineUpperExcessEnergy U hi t = 0) :
    ∀ x, U t x ≤ hi := by
  have hnonneg : 0 ≤ fun x : ℝ => (max (U t x - hi) 0) ^ 2 :=
    fun x => sq_nonneg _
  have hintegral :
      (∫ x : ℝ, (max (U t x - hi) 0) ^ 2) = 0 := by
    simpa [wholeLineUpperExcessEnergy] using hE
  have hae :
      (fun x : ℝ => (max (U t x - hi) 0) ^ 2) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg hnonneg hint).1 hintegral
  have htest_cont : Continuous (fun x : ℝ => max (U t x - hi) 0) :=
    ((hU_cont.sub continuous_const).max continuous_const)
  have hsquare_cont : Continuous (fun x : ℝ => (max (U t x - hi) 0) ^ 2) := by
    simpa [pow_two] using htest_cont.mul htest_cont
  have hzero_fun :
      (fun x : ℝ => (max (U t x - hi) 0) ^ 2) = fun _ : ℝ => 0 :=
    MeasureTheory.Measure.eq_of_ae_eq (μ := volume) hae hsquare_cont continuous_const
  intro x
  have hsquare_zero : (max (U t x - hi) 0) ^ 2 = 0 :=
    congr_fun hzero_fun x
  have hmax_zero : max (U t x - hi) 0 = 0 := by
    nlinarith [sq_nonneg (max (U t x - hi) 0)]
  have hle : U t x - hi ≤ 0 := by
    have hlemax : U t x - hi ≤ max (U t x - hi) 0 := le_max_left _ _
    simpa [hmax_zero] using hlemax
  linarith

theorem wholeLineLowerDeficitEnergy_zero_controls_of_integrable
    {U : ℝ → ℝ → ℝ} {lo t : ℝ}
    (hU_cont : Continuous (U t))
    (hint : Integrable (fun x : ℝ => (max (lo - U t x) 0) ^ 2) volume)
    (hE : wholeLineLowerDeficitEnergy U lo t = 0) :
    ∀ x, lo ≤ U t x := by
  have hnonneg : 0 ≤ fun x : ℝ => (max (lo - U t x) 0) ^ 2 :=
    fun x => sq_nonneg _
  have hintegral :
      (∫ x : ℝ, (max (lo - U t x) 0) ^ 2) = 0 := by
    simpa [wholeLineLowerDeficitEnergy] using hE
  have hae :
      (fun x : ℝ => (max (lo - U t x) 0) ^ 2) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg hnonneg hint).1 hintegral
  have htest_cont : Continuous (fun x : ℝ => max (lo - U t x) 0) :=
    ((continuous_const.sub hU_cont).max continuous_const)
  have hsquare_cont : Continuous (fun x : ℝ => (max (lo - U t x) 0) ^ 2) := by
    simpa [pow_two] using htest_cont.mul htest_cont
  have hzero_fun :
      (fun x : ℝ => (max (lo - U t x) 0) ^ 2) = fun _ : ℝ => 0 :=
    MeasureTheory.Measure.eq_of_ae_eq (μ := volume) hae hsquare_cont continuous_const
  intro x
  have hsquare_zero : (max (lo - U t x) 0) ^ 2 = 0 :=
    congr_fun hzero_fun x
  have hmax_zero : max (lo - U t x) 0 = 0 := by
    nlinarith [sq_nonneg (max (lo - U t x) 0)]
  have hle : lo - U t x ≤ 0 := by
    have hlemax : lo - U t x ≤ max (lo - U t x) 0 := le_max_left _ _
    simpa [hmax_zero] using hlemax
  linarith

structure WholeLineConstantBarrierTrappingRegularityData
    (p : CMParams) (T : ℝ) (U : ℝ → ℝ → ℝ) (lo hi Cexcess : ℝ) where
  solution : IsClassicalSolution p T U (wholeLineFrozenSignalTime p U)
  Cexcess_nonneg : 0 ≤ Cexcess
  U_nonneg : ∀ t x, 0 ≤ U t x
  U_le_one : ∀ t x, U t x ≤ 1
  upper_cont : ∀ s t, 0 < s → s ≤ t → t < T →
    ContinuousOn (wholeLineUpperExcessEnergy U hi) (Set.Icc s t)
  lower_cont : ∀ s t, 0 < s → s ≤ t → t < T →
    ContinuousOn (wholeLineLowerDeficitEnergy U lo) (Set.Icc s t)
  upper_initial : ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → s < T →
    wholeLineUpperExcessEnergy U hi s < ε
  lower_initial : ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → s < T →
    wholeLineLowerDeficitEnergy U lo s < ε
  upper_time : WholeLineUpperTimeLeibnizData T U hi
  lower_time : WholeLineLowerTimeLeibnizData T U lo
  upper_pde :
    WholeLineUpperPDESubstitutionData p T U (wholeLineFrozenSignalTime p U) hi
  lower_pde :
    WholeLineLowerPDESubstitutionData p T U (wholeLineFrozenSignalTime p U) lo
  upper_diffusion : WholeLineUpperDiffusionIBPData T U hi
  lower_diffusion : WholeLineLowerDiffusionIBPData T U lo
  upper_excess_indicator_integrable : ∀ t, 0 < t → t < T →
    Integrable (wholeLineExcessIndicator (wholeLineUpperBarrierTest U hi t)) volume
  lower_excess_indicator_integrable : ∀ t, 0 < t → t < T →
    Integrable (wholeLineExcessIndicator (wholeLineLowerBarrierTest U lo t)) volume
  upper_excess_indicator_energy_control : ∀ t, 0 < t → t < T →
    (∫ x : ℝ, wholeLineExcessIndicator (wholeLineUpperBarrierTest U hi t) x) ≤
      Cexcess * wholeLineUpperExcessEnergy U hi t
  lower_excess_indicator_energy_control : ∀ t, 0 < t → t < T →
    (∫ x : ℝ, wholeLineExcessIndicator (wholeLineLowerBarrierTest U lo t) x) ≤
      Cexcess * wholeLineLowerDeficitEnergy U lo t
  upper_restricted_sq_int : ∀ t, 0 < t → t < T →
    Integrable (fun x : ℝ =>
      wholeLineUpperFrozenRestrictedFlux p U hi t x *
      wholeLineUpperFrozenRestrictedFlux p U hi t x) volume
  lower_restricted_sq_int : ∀ t, 0 < t → t < T →
    Integrable (fun x : ℝ =>
      wholeLineLowerFrozenRestrictedFlux p U lo t x *
      wholeLineLowerFrozenRestrictedFlux p U lo t x) volume
  upper_chem_profile_deriv : ∀ t, 0 < t → t < T → ∀ x ∈ tsupport
      (wholeLineChemotaxisWeight p (U t)
        (fun y : ℝ => deriv ((wholeLineFrozenSignalTime p U) t) y)),
      HasDerivAt (wholeLineUpperBarrierTest U hi t)
        (-(wholeLineUpperFrozenRestrictedFlux p U hi t x)) x
  lower_chem_profile_deriv : ∀ t, 0 < t → t < T → ∀ x ∈ tsupport
      (wholeLineChemotaxisWeight p (U t)
        (fun y : ℝ => deriv ((wholeLineFrozenSignalTime p U) t) y)),
      HasDerivAt (wholeLineLowerBarrierTest U lo t)
        (wholeLineLowerFrozenRestrictedFlux p U lo t x) x
  upper_chem_weight_deriv : ∀ t, 0 < t → t < T → ∀ x ∈ tsupport
      (wholeLineUpperBarrierTest U hi t),
      HasDerivAt
        (wholeLineChemotaxisWeight p (U t)
          (fun y : ℝ => deriv ((wholeLineFrozenSignalTime p U) t) y))
        (deriv (wholeLineChemotaxisWeight p (U t)
          (fun y : ℝ => deriv ((wholeLineFrozenSignalTime p U) t) y)) x) x
  lower_chem_weight_deriv : ∀ t, 0 < t → t < T → ∀ x ∈ tsupport
      (wholeLineLowerBarrierTest U lo t),
      HasDerivAt
        (wholeLineChemotaxisWeight p (U t)
          (fun y : ℝ => deriv ((wholeLineFrozenSignalTime p U) t) y))
        (deriv (wholeLineChemotaxisWeight p (U t)
          (fun y : ℝ => deriv ((wholeLineFrozenSignalTime p U) t) y)) x) x
  upper_chem_lhs_int : ∀ t, 0 < t → t < T → Integrable (fun x : ℝ =>
    wholeLineUpperBarrierTest U hi t x *
      deriv (wholeLineChemotaxisWeight p (U t)
        (fun y : ℝ => deriv ((wholeLineFrozenSignalTime p U) t) y)) x) volume
  lower_chem_lhs_int : ∀ t, 0 < t → t < T → Integrable (fun x : ℝ =>
    wholeLineLowerBarrierTest U lo t x *
      deriv (wholeLineChemotaxisWeight p (U t)
        (fun y : ℝ => deriv ((wholeLineFrozenSignalTime p U) t) y)) x) volume
  upper_chem_decay_bot : ∀ t, 0 < t → t < T → Tendsto (fun x : ℝ =>
    wholeLineUpperBarrierTest U hi t x *
      wholeLineChemotaxisWeight p (U t)
        (fun y : ℝ => deriv ((wholeLineFrozenSignalTime p U) t) y) x) atBot (𝓝 0)
  upper_chem_decay_top : ∀ t, 0 < t → t < T → Tendsto (fun x : ℝ =>
    wholeLineUpperBarrierTest U hi t x *
      wholeLineChemotaxisWeight p (U t)
        (fun y : ℝ => deriv ((wholeLineFrozenSignalTime p U) t) y) x) atTop (𝓝 0)
  lower_chem_decay_bot : ∀ t, 0 < t → t < T → Tendsto (fun x : ℝ =>
    wholeLineLowerBarrierTest U lo t x *
      wholeLineChemotaxisWeight p (U t)
        (fun y : ℝ => deriv ((wholeLineFrozenSignalTime p U) t) y) x) atBot (𝓝 0)
  lower_chem_decay_top : ∀ t, 0 < t → t < T → Tendsto (fun x : ℝ =>
    wholeLineLowerBarrierTest U lo t x *
      wholeLineChemotaxisWeight p (U t)
        (fun y : ℝ => deriv ((wholeLineFrozenSignalTime p U) t) y) x) atTop (𝓝 0)

def wholeLineUpperFrozenChemotaxisCrossData
    {p : CMParams} {T : ℝ} {U : ℝ → ℝ → ℝ} {lo hi Cexcess : ℝ}
    (H : WholeLineConstantBarrierTrappingRegularityData p T U lo hi Cexcess) :
    WholeLineUpperChemotaxisCrossData p T U (wholeLineFrozenSignalTime p U) hi
      (wholeLineFrozenSignalCrossK p 1 Cexcess
        (wholeLineFrozenSignalRestrictedCgrad p 1 Cexcess))
      (wholeLineFrozenSignalRestrictedCgrad p 1 Cexcess) where
  flux := wholeLineUpperFrozenRestrictedFlux p U hi
  bounds := by
    intro t ht0 htT
    exact wholeLineFrozenSignalCrossBounds p (by norm_num) H.Cexcess_nonneg
      (H.U_nonneg t) (H.U_le_one t)
      (wholeLineClassicalSolution_u_slice_continuous H.solution t ht0 htT)
      (H.U_nonneg t) (H.U_le_one t)
      (H.upper_excess_indicator_integrable t ht0 htT)
      (H.upper_excess_indicator_energy_control t ht0 htT)
  postIBP := by
    intro t ht0 htT
    exact wholeLineUpperBarrier_chemotaxis_postIBP_field p
      (wholeLineUpperFrozenRestrictedFlux p U hi)
      H.upper_chem_profile_deriv H.upper_chem_weight_deriv
      H.upper_chem_lhs_int
      (fun s hs0 hsT =>
        wholeLineRestrictedChemotaxisWeight_mul_weight_integrable p
          (φ := wholeLineUpperBarrierTest U hi s)
          (U := U s)
          (Vx := fun y : ℝ => deriv ((wholeLineFrozenSignalTime p U) s) y)
          (by
            simpa [wholeLineUpperFrozenRestrictedFlux]
              using H.upper_restricted_sq_int s hs0 hsT))
      H.upper_chem_decay_bot H.upper_chem_decay_top t ht0 htT
  zero_off_excess := by
    intro t ht0 htT x hx
    simp [wholeLineUpperFrozenRestrictedFlux, wholeLineRestrictedChemotaxisWeight,
      wholeLineExcessIndicator, hx]
  flux_sq_int := by
    intro t ht0 htT
    simpa [wholeLineUpperFrozenRestrictedFlux] using
      H.upper_restricted_sq_int t ht0 htT
  cross_int := by
    intro t ht0 htT
    exact wholeLineRestrictedChemotaxisWeight_mul_weight_integrable p
      (φ := wholeLineUpperBarrierTest U hi t)
      (U := U t)
      (Vx := fun y : ℝ => deriv ((wholeLineFrozenSignalTime p U) t) y)
      (by
        simpa [wholeLineUpperFrozenRestrictedFlux] using
          H.upper_restricted_sq_int t ht0 htT)
  restricted_sq_int := by
    intro t ht0 htT
    simpa [wholeLineUpperFrozenRestrictedFlux] using
      H.upper_restricted_sq_int t ht0 htT
  gradient_control := by
    intro t ht0 htT
    exact wholeLineFrozenSignal_restricted_gradient_control p (by norm_num)
      H.Cexcess_nonneg (H.U_nonneg t) (H.U_le_one t)
      (wholeLineClassicalSolution_u_slice_continuous H.solution t ht0 htT)
      (H.U_nonneg t) (H.U_le_one t)
      (H.upper_excess_indicator_integrable t ht0 htT)
      (H.upper_excess_indicator_energy_control t ht0 htT)
      (by
        simpa [wholeLineUpperFrozenRestrictedFlux] using
          H.upper_restricted_sq_int t ht0 htT)
  K_control := by
    intro t ht0 htT
    exact wholeLineFrozenSignal_K_control p (by norm_num) H.Cexcess_nonneg
      (H.U_nonneg t) (H.U_le_one t)
      (wholeLineClassicalSolution_u_slice_continuous H.solution t ht0 htT)
      (H.U_nonneg t) (H.U_le_one t)
      (H.upper_excess_indicator_integrable t ht0 htT)
      (H.upper_excess_indicator_energy_control t ht0 htT)

def wholeLineLowerFrozenChemotaxisCrossData
    {p : CMParams} {T : ℝ} {U : ℝ → ℝ → ℝ} {lo hi Cexcess : ℝ}
    (H : WholeLineConstantBarrierTrappingRegularityData p T U lo hi Cexcess) :
    WholeLineLowerChemotaxisCrossData p T U (wholeLineFrozenSignalTime p U) lo
      (wholeLineFrozenSignalCrossK p 1 Cexcess
        (wholeLineFrozenSignalRestrictedCgrad p 1 Cexcess))
      (wholeLineFrozenSignalRestrictedCgrad p 1 Cexcess) where
  flux := wholeLineLowerFrozenRestrictedFlux p U lo
  bounds := by
    intro t ht0 htT
    exact wholeLineFrozenSignalCrossBounds p (by norm_num) H.Cexcess_nonneg
      (H.U_nonneg t) (H.U_le_one t)
      (wholeLineClassicalSolution_u_slice_continuous H.solution t ht0 htT)
      (H.U_nonneg t) (H.U_le_one t)
      (H.lower_excess_indicator_integrable t ht0 htT)
      (H.lower_excess_indicator_energy_control t ht0 htT)
  postIBP := by
    intro t ht0 htT
    exact wholeLineLowerBarrier_chemotaxis_postIBP_field p
      (wholeLineLowerFrozenRestrictedFlux p U lo)
      H.lower_chem_profile_deriv H.lower_chem_weight_deriv
      H.lower_chem_lhs_int
      (fun s hs0 hsT =>
        wholeLineRestrictedChemotaxisWeight_mul_weight_integrable p
          (φ := wholeLineLowerBarrierTest U lo s)
          (U := U s)
          (Vx := fun y : ℝ => deriv ((wholeLineFrozenSignalTime p U) s) y)
          (by
            simpa [wholeLineLowerFrozenRestrictedFlux]
              using H.lower_restricted_sq_int s hs0 hsT))
      H.lower_chem_decay_bot H.lower_chem_decay_top t ht0 htT
  zero_off_excess := by
    intro t ht0 htT x hx
    simp [wholeLineLowerFrozenRestrictedFlux, wholeLineRestrictedChemotaxisWeight,
      wholeLineExcessIndicator, hx]
  flux_sq_int := by
    intro t ht0 htT
    simpa [wholeLineLowerFrozenRestrictedFlux] using
      H.lower_restricted_sq_int t ht0 htT
  cross_int := by
    intro t ht0 htT
    exact wholeLineRestrictedChemotaxisWeight_mul_weight_integrable p
      (φ := wholeLineLowerBarrierTest U lo t)
      (U := U t)
      (Vx := fun y : ℝ => deriv ((wholeLineFrozenSignalTime p U) t) y)
      (by
        simpa [wholeLineLowerFrozenRestrictedFlux] using
          H.lower_restricted_sq_int t ht0 htT)
  restricted_sq_int := by
    intro t ht0 htT
    simpa [wholeLineLowerFrozenRestrictedFlux] using
      H.lower_restricted_sq_int t ht0 htT
  gradient_control := by
    intro t ht0 htT
    exact wholeLineFrozenSignal_restricted_gradient_control p (by norm_num)
      H.Cexcess_nonneg (H.U_nonneg t) (H.U_le_one t)
      (wholeLineClassicalSolution_u_slice_continuous H.solution t ht0 htT)
      (H.U_nonneg t) (H.U_le_one t)
      (H.lower_excess_indicator_integrable t ht0 htT)
      (H.lower_excess_indicator_energy_control t ht0 htT)
      (by
        simpa [wholeLineLowerFrozenRestrictedFlux] using
          H.lower_restricted_sq_int t ht0 htT)
  K_control := by
    intro t ht0 htT
    exact wholeLineFrozenSignal_K_control p (by norm_num) H.Cexcess_nonneg
      (H.U_nonneg t) (H.U_le_one t)
      (wholeLineClassicalSolution_u_slice_continuous H.solution t ht0 htT)
      (H.U_nonneg t) (H.U_le_one t)
      (H.lower_excess_indicator_integrable t ht0 htT)
      (H.lower_excess_indicator_energy_control t ht0 htT)

theorem wholeLine_constantBarrier_trapping_unconditional
    {p : CMParams} {T : ℝ} {u0 : ℝ → ℝ} {U : ℝ → ℝ → ℝ} {lo hi Cexcess : ℝ}
    (hχ : p.χ ≤ 0) (hlo0 : 0 ≤ lo) (hlo1 : lo ≤ 1) (hhi1 : 1 ≤ hi)
    (hu0lo : ∀ x, lo ≤ u0 x) (hu0hi : ∀ x, u0 x ≤ hi)
    (H : WholeLineConstantBarrierTrappingRegularityData p T U lo hi Cexcess) :
    ∀ t, 0 < t → t < T → ∀ x, lo ≤ U t x ∧ U t x ≤ hi := by
  let Cgrad := wholeLineFrozenSignalRestrictedCgrad p 1 Cexcess
  let K := wholeLineFrozenSignalCrossK p 1 Cexcess Cgrad
  have hK_nonneg : 0 ≤ K := by
    simpa [K, Cgrad] using wholeLineFrozenSignalCrossK_one_nonneg p H.Cexcess_nonneg
  let HupperChem := wholeLineUpperFrozenChemotaxisCrossData H
  let HlowerChem := wholeLineLowerFrozenChemotaxisCrossData H
  have Hupper :
      WholeLineBarrierEnergyFrontier (wholeLineUpperExcessEnergy U hi) T :=
    wholeLineUpperBarrierEnergyFrontier_of_solution H.solution K Cgrad hK_nonneg hhi1
      H.upper_cont H.upper_initial H.upper_time H.upper_pde H.upper_diffusion
      (by
        simpa [HupperChem, K, Cgrad] using HupperChem)
  have Hlower :
      WholeLineBarrierEnergyFrontier (wholeLineLowerDeficitEnergy U lo) T :=
    wholeLineLowerBarrierEnergyFrontier_of_solution H.solution K Cgrad hK_nonneg
      H.U_nonneg hlo1 H.lower_cont H.lower_initial H.lower_time H.lower_pde
      H.lower_diffusion
      (by
        simpa [HlowerChem, K, Cgrad] using HlowerChem)
  let Hmethod :
      WholeLineConstantBarrierEnergyMethod p T u0 U (wholeLineFrozenSignalTime p U)
        lo hi := {
    solution := H.solution
    upper := Hupper
    lower := Hlower
    upper_zero_controls := by
      intro t ht0 htT hE
      exact wholeLineUpperExcessEnergy_zero_controls_of_integrable
        (wholeLineClassicalSolution_u_slice_continuous H.solution t ht0 htT)
        (wholeLineUpperExcess_square_integrable_of_timeData H.upper_time ht0 htT)
        hE
    lower_zero_controls := by
      intro t ht0 htT hE
      exact wholeLineLowerDeficitEnergy_zero_controls_of_integrable
        (wholeLineClassicalSolution_u_slice_continuous H.solution t ht0 htT)
        (wholeLineLowerDeficit_square_integrable_of_timeData H.lower_time ht0 htT)
        hE }
  exact wholeLine_constantBarrier_trapping_via_energy hχ hlo0 hlo1 hhi1
    hu0lo hu0hi Hmethod

#print axioms wholeLine_constantBarrier_trapping_unconditional

end ShenWork.PaperOne
