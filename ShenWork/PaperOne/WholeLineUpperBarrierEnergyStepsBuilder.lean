import ShenWork.PaperOne.WholeLineBarrierEnergyFrontierLower
import ShenWork.PaperOne.WholeLineChemotaxisCrossControl
import ShenWork.PaperOne.WholeLineDiffusionIBPDecay
import ShenWork.PaperOne.WholeLineEnergyTimeLeibnizPDE

open Filter MeasureTheory
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

def wholeLineTimeDeriv (U : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  deriv (fun τ : ℝ => U τ x) t

def wholeLineNegTimeDeriv (U : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  -wholeLineTimeDeriv U t x

theorem wholeLineUpperExcessEnergy_eq_two_half
    (U : ℝ → ℝ → ℝ) (hi t : ℝ) :
    wholeLineUpperExcessEnergy U hi t =
      2 * wholeLineUpperHalfExcessEnergy U hi t := by
  calc
    wholeLineUpperExcessEnergy U hi t
        = ∫ x : ℝ, 2 * ((1 / 2 : ℝ) * (max (U t x - hi) 0) ^ 2) := by
          unfold wholeLineUpperExcessEnergy
          congr
          ext x
          ring
    _ = 2 * wholeLineUpperHalfExcessEnergy U hi t := by
          rw [integral_const_mul]
          rfl

theorem wholeLineLowerDeficitEnergy_eq_two_half
    (U : ℝ → ℝ → ℝ) (lo t : ℝ) :
    wholeLineLowerDeficitEnergy U lo t =
      2 * wholeLineLowerHalfDeficitEnergy U lo t := by
  calc
    wholeLineLowerDeficitEnergy U lo t
        = ∫ x : ℝ, 2 * ((1 / 2 : ℝ) * (max (lo - U t x) 0) ^ 2) := by
          unfold wholeLineLowerDeficitEnergy
          congr
          ext x
          ring
    _ = 2 * wholeLineLowerHalfDeficitEnergy U lo t := by
          rw [integral_const_mul]
          rfl

structure WholeLineUpperTimeLeibnizData
    (T : ℝ) (U : ℝ → ℝ → ℝ) (hi : ℝ) where
  δ : ℝ → ℝ
  bound : ℝ → ℝ → ℝ
  δ_pos : ∀ t, 0 < t → t < T → 0 < δ t
  F_meas : ∀ t, 0 < t → t < T →
    ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable
        (wholeLineHalfEnergyIntegrand (wholeLineUpperExcessProfile U hi) s)
        volume
  F_int : ∀ t, 0 < t → t < T →
    Integrable
      (wholeLineHalfEnergyIntegrand (wholeLineUpperExcessProfile U hi) t)
      volume
  F_deriv_meas : ∀ t, 0 < t → t < T →
    AEStronglyMeasurable
      (wholeLineHalfEnergyIntegrandDeriv
        (wholeLineUpperExcessProfile U hi) (wholeLineTimeDeriv U) t)
      volume
  deriv_bound : ∀ t, 0 < t → t < T →
    ∀ᵐ x ∂volume,
      ∀ s ∈ Metric.ball t (δ t),
        ‖wholeLineHalfEnergyIntegrandDeriv
          (wholeLineUpperExcessProfile U hi) (wholeLineTimeDeriv U) s x‖ ≤
          bound t x
  bound_int : ∀ t, 0 < t → t < T → Integrable (bound t) volume
  profile_hasDeriv : ∀ t, 0 < t → t < T →
    ∀ᵐ x ∂volume,
      ∀ s ∈ Metric.ball t (δ t),
        HasDerivAt
          (fun r : ℝ => wholeLineUpperExcessProfile U hi r x)
          (wholeLineTimeDeriv U s x) s

structure WholeLineLowerTimeLeibnizData
    (T : ℝ) (U : ℝ → ℝ → ℝ) (lo : ℝ) where
  δ : ℝ → ℝ
  bound : ℝ → ℝ → ℝ
  δ_pos : ∀ t, 0 < t → t < T → 0 < δ t
  F_meas : ∀ t, 0 < t → t < T →
    ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable
        (wholeLineHalfEnergyIntegrand (wholeLineLowerDeficitProfile U lo) s)
        volume
  F_int : ∀ t, 0 < t → t < T →
    Integrable
      (wholeLineHalfEnergyIntegrand (wholeLineLowerDeficitProfile U lo) t)
      volume
  F_deriv_meas : ∀ t, 0 < t → t < T →
    AEStronglyMeasurable
      (wholeLineHalfEnergyIntegrandDeriv
        (wholeLineLowerDeficitProfile U lo) (wholeLineNegTimeDeriv U) t)
      volume
  deriv_bound : ∀ t, 0 < t → t < T →
    ∀ᵐ x ∂volume,
      ∀ s ∈ Metric.ball t (δ t),
        ‖wholeLineHalfEnergyIntegrandDeriv
          (wholeLineLowerDeficitProfile U lo) (wholeLineNegTimeDeriv U) s x‖ ≤
          bound t x
  bound_int : ∀ t, 0 < t → t < T → Integrable (bound t) volume
  profile_hasDeriv : ∀ t, 0 < t → t < T →
    ∀ᵐ x ∂volume,
      ∀ s ∈ Metric.ball t (δ t),
        HasDerivAt
          (fun r : ℝ => wholeLineLowerDeficitProfile U lo r x)
          (wholeLineNegTimeDeriv U s x) s

structure WholeLineUpperPDESubstitutionData
    (p : CMParams) (T : ℝ) (U V : ℝ → ℝ → ℝ) (hi : ℝ) where
  diffusion_int : ∀ t, 0 < t → t < T →
    Integrable
      (fun x : ℝ =>
        wholeLineUpperExcessProfile U hi t x * wholeLineDiffusionDensity U t x)
      volume
  chemotaxis_int : ∀ t, 0 < t → t < T →
    Integrable
      (fun x : ℝ =>
        wholeLineUpperExcessProfile U hi t x *
          wholeLineChemotaxisDensity p U V t x)
      volume
  reaction_int : ∀ t, 0 < t → t < T →
    Integrable
      (fun x : ℝ =>
        wholeLineUpperExcessProfile U hi t x *
          wholeLineLogisticDensity p U t x)
      volume

structure WholeLineLowerPDESubstitutionData
    (p : CMParams) (T : ℝ) (U V : ℝ → ℝ → ℝ) (lo : ℝ) where
  diffusion_int : ∀ t, 0 < t → t < T →
    Integrable
      (fun x : ℝ =>
        wholeLineLowerDeficitProfile U lo t x * wholeLineDiffusionDensity U t x)
      volume
  chemotaxis_int : ∀ t, 0 < t → t < T →
    Integrable
      (fun x : ℝ =>
        wholeLineLowerDeficitProfile U lo t x *
          wholeLineChemotaxisDensity p U V t x)
      volume
  reaction_int : ∀ t, 0 < t → t < T →
    Integrable
      (fun x : ℝ =>
        wholeLineLowerDeficitProfile U lo t x *
          wholeLineLogisticDensity p U t x)
      volume

structure WholeLineUpperDiffusionIBPData
    (T : ℝ) (U : ℝ → ℝ → ℝ) (hi : ℝ) where
  flux : ℝ → ℝ → ℝ
  profile_deriv : ∀ t, 0 < t → t < T →
    ∀ x ∈ tsupport (flux t),
      HasDerivAt (wholeLineUpperBarrierTest U hi t) (flux t x) x
  flux_deriv : ∀ t, 0 < t → t < T →
    ∀ x ∈ tsupport (wholeLineUpperBarrierTest U hi t),
      HasDerivAt (flux t) (iteratedDeriv 2 (U t) x) x
  lhs_int : ∀ t, 0 < t → t < T →
    Integrable
      (fun x : ℝ =>
        wholeLineUpperBarrierTest U hi t x * iteratedDeriv 2 (U t) x)
      volume
  energy_int : ∀ t, 0 < t → t < T →
    Integrable (fun x : ℝ => flux t x * flux t x) volume
  decay_bot : ∀ t, 0 < t → t < T →
    Tendsto (fun x : ℝ => wholeLineUpperBarrierTest U hi t x * flux t x)
      atBot (𝓝 0)
  decay_top : ∀ t, 0 < t → t < T →
    Tendsto (fun x : ℝ => wholeLineUpperBarrierTest U hi t x * flux t x)
      atTop (𝓝 0)

structure WholeLineLowerDiffusionIBPData
    (T : ℝ) (U : ℝ → ℝ → ℝ) (lo : ℝ) where
  flux : ℝ → ℝ → ℝ
  profile_deriv : ∀ t, 0 < t → t < T →
    ∀ x ∈ tsupport (flux t),
      HasDerivAt (wholeLineLowerBarrierTest U lo t) (flux t x) x
  flux_deriv : ∀ t, 0 < t → t < T →
    ∀ x ∈ tsupport (wholeLineLowerBarrierTest U lo t),
      HasDerivAt (flux t) (-iteratedDeriv 2 (U t) x) x
  lhs_int : ∀ t, 0 < t → t < T →
    Integrable
      (fun x : ℝ =>
        wholeLineLowerBarrierTest U lo t x * (-iteratedDeriv 2 (U t) x))
      volume
  energy_int : ∀ t, 0 < t → t < T →
    Integrable (fun x : ℝ => flux t x * flux t x) volume
  decay_bot : ∀ t, 0 < t → t < T →
    Tendsto (fun x : ℝ => wholeLineLowerBarrierTest U lo t x * flux t x)
      atBot (𝓝 0)
  decay_top : ∀ t, 0 < t → t < T →
    Tendsto (fun x : ℝ => wholeLineLowerBarrierTest U lo t x * flux t x)
      atTop (𝓝 0)

structure WholeLineUpperChemotaxisCrossData
    (p : CMParams) (T : ℝ) (U V : ℝ → ℝ → ℝ) (hi K Cgrad : ℝ) where
  flux : ℝ → ℝ → ℝ
  bounds : ∀ t, 0 < t → t < T →
    WholeLineChemotaxisCrossBounds p
      (wholeLineUpperBarrierTest U hi t) (U t) (fun x : ℝ => deriv (V t) x)
      (wholeLineUpperExcessEnergy U hi t)
  postIBP : ∀ t, 0 < t → t < T →
    wholeLineUpperBarrierChemotaxisTerm p U V hi t =
      ∫ x : ℝ,
        flux t x *
          wholeLineChemotaxisWeight p (U t) (fun y : ℝ => deriv (V t) y) x
  zero_off_excess : ∀ t, 0 < t → t < T →
    ∀ x, ¬ 0 < wholeLineUpperBarrierTest U hi t x → flux t x = 0
  flux_sq_int : ∀ t, 0 < t → t < T →
    Integrable (fun x : ℝ => flux t x * flux t x) volume
  cross_int : ∀ t, 0 < t → t < T →
    Integrable
      (fun x : ℝ =>
        flux t x *
          wholeLineChemotaxisWeight p (U t) (fun y : ℝ => deriv (V t) y) x)
      volume
  restricted_sq_int : ∀ t, 0 < t → t < T →
    Integrable
      (fun x : ℝ =>
        wholeLineRestrictedChemotaxisWeight p
          (wholeLineUpperBarrierTest U hi t) (U t)
          (fun y : ℝ => deriv (V t) y) x *
        wholeLineRestrictedChemotaxisWeight p
          (wholeLineUpperBarrierTest U hi t) (U t)
          (fun y : ℝ => deriv (V t) y) x)
      volume
  gradient_control : ∀ t, 0 < t → t < T →
    wholeLineGradientDissipation (flux t) ≤
      Cgrad * wholeLineUpperExcessEnergy U hi t
  K_control : ∀ t (ht0 : 0 < t) (htT : t < T),
    Cgrad + 2 * (bounds t ht0 htT).K ≤ K

structure WholeLineLowerChemotaxisCrossData
    (p : CMParams) (T : ℝ) (U V : ℝ → ℝ → ℝ) (lo K Cgrad : ℝ) where
  flux : ℝ → ℝ → ℝ
  bounds : ∀ t, 0 < t → t < T →
    WholeLineChemotaxisCrossBounds p
      (wholeLineLowerBarrierTest U lo t) (U t) (fun x : ℝ => deriv (V t) x)
      (wholeLineLowerDeficitEnergy U lo t)
  postIBP : ∀ t, 0 < t → t < T →
    -wholeLineLowerBarrierChemotaxisTerm p U V lo t =
      ∫ x : ℝ,
        flux t x *
          wholeLineChemotaxisWeight p (U t) (fun y : ℝ => deriv (V t) y) x
  zero_off_excess : ∀ t, 0 < t → t < T →
    ∀ x, ¬ 0 < wholeLineLowerBarrierTest U lo t x → flux t x = 0
  flux_sq_int : ∀ t, 0 < t → t < T →
    Integrable (fun x : ℝ => flux t x * flux t x) volume
  cross_int : ∀ t, 0 < t → t < T →
    Integrable
      (fun x : ℝ =>
        flux t x *
          wholeLineChemotaxisWeight p (U t) (fun y : ℝ => deriv (V t) y) x)
      volume
  restricted_sq_int : ∀ t, 0 < t → t < T →
    Integrable
      (fun x : ℝ =>
        wholeLineRestrictedChemotaxisWeight p
          (wholeLineLowerBarrierTest U lo t) (U t)
          (fun y : ℝ => deriv (V t) y) x *
        wholeLineRestrictedChemotaxisWeight p
          (wholeLineLowerBarrierTest U lo t) (U t)
          (fun y : ℝ => deriv (V t) y) x)
      volume
  gradient_control : ∀ t, 0 < t → t < T →
    wholeLineGradientDissipation (flux t) ≤
      Cgrad * wholeLineLowerDeficitEnergy U lo t
  K_control : ∀ t (ht0 : 0 < t) (htT : t < T),
    Cgrad + 2 * (bounds t ht0 htT).K ≤ K

theorem wholeLineUpper_weightedTimeTerm_eq_barrierTimeTerm
    (U : ℝ → ℝ → ℝ) (hi t : ℝ) :
    wholeLineWeightedTimeTerm (wholeLineUpperExcessProfile U hi)
        (wholeLineTimeDeriv U) t =
      wholeLineUpperBarrierTimeTerm U hi t := by
  rfl

theorem wholeLineLower_weightedNegTimeTerm_eq_neg_barrierTimeTerm
    (U : ℝ → ℝ → ℝ) (lo t : ℝ) :
    wholeLineWeightedTimeTerm (wholeLineLowerDeficitProfile U lo)
        (wholeLineNegTimeDeriv U) t =
      -wholeLineLowerBarrierTimeTerm U lo t := by
  unfold wholeLineWeightedTimeTerm wholeLineHalfEnergyIntegrandDeriv
    wholeLineNegTimeDeriv wholeLineTimeDeriv wholeLineLowerBarrierTimeTerm
    wholeLineLowerDeficitProfile wholeLineLowerBarrierTest
  rw [← integral_neg]
  congr
  ext x
  ring

theorem wholeLineUpper_timeLeibniz_field_of_data
    {T : ℝ} {U : ℝ → ℝ → ℝ} {hi : ℝ}
    (H : WholeLineUpperTimeLeibnizData T U hi) :
    ∀ t, 0 < t → t < T →
      HasDerivWithinAt (wholeLineUpperExcessEnergy U hi)
        (2 * wholeLineUpperBarrierTimeTerm U hi t) (Set.Ici t) t := by
  intro t ht0 htT
  have hhalf :
      HasDerivAt
        (fun s : ℝ =>
          wholeLineHalfEnergy (wholeLineUpperExcessProfile U hi) s)
        (wholeLineWeightedTimeTerm (wholeLineUpperExcessProfile U hi)
          (wholeLineTimeDeriv U) t) t :=
    wholeLine_halfEnergy_hasDerivAt_of_dominated
      (phi := wholeLineUpperExcessProfile U hi)
      (phi_t := wholeLineTimeDeriv U)
      (t := t) (δ := H.δ t) (bound := H.bound t)
      (H.δ_pos t ht0 htT) (H.F_meas t ht0 htT)
      (H.F_int t ht0 htT) (H.F_deriv_meas t ht0 htT)
      (H.deriv_bound t ht0 htT) (H.bound_int t ht0 htT)
      (H.profile_hasDeriv t ht0 htT)
  have hscaled :
      HasDerivWithinAt
        (fun s : ℝ => 2 * wholeLineUpperHalfExcessEnergy U hi s)
        (2 * wholeLineWeightedTimeTerm (wholeLineUpperExcessProfile U hi)
          (wholeLineTimeDeriv U) t) (Set.Ici t) t :=
    (HasDerivAt.const_mul (2 : ℝ) (by
      simpa [wholeLineUpperHalfExcessEnergy] using hhalf)).hasDerivWithinAt
  have hfun :
      (fun s : ℝ => 2 * wholeLineUpperHalfExcessEnergy U hi s) =
        wholeLineUpperExcessEnergy U hi := by
    funext s
    rw [wholeLineUpperExcessEnergy_eq_two_half]
  simpa [wholeLineUpper_weightedTimeTerm_eq_barrierTimeTerm] using hfun ▸ hscaled

theorem wholeLineLower_timeLeibniz_field_of_data
    {T : ℝ} {U : ℝ → ℝ → ℝ} {lo : ℝ}
    (H : WholeLineLowerTimeLeibnizData T U lo) :
    ∀ t, 0 < t → t < T →
      HasDerivWithinAt (wholeLineLowerDeficitEnergy U lo)
        (-2 * wholeLineLowerBarrierTimeTerm U lo t) (Set.Ici t) t := by
  intro t ht0 htT
  have hhalf :
      HasDerivAt
        (fun s : ℝ =>
          wholeLineHalfEnergy (wholeLineLowerDeficitProfile U lo) s)
        (wholeLineWeightedTimeTerm (wholeLineLowerDeficitProfile U lo)
          (wholeLineNegTimeDeriv U) t) t :=
    wholeLine_halfEnergy_hasDerivAt_of_dominated
      (phi := wholeLineLowerDeficitProfile U lo)
      (phi_t := wholeLineNegTimeDeriv U)
      (t := t) (δ := H.δ t) (bound := H.bound t)
      (H.δ_pos t ht0 htT) (H.F_meas t ht0 htT)
      (H.F_int t ht0 htT) (H.F_deriv_meas t ht0 htT)
      (H.deriv_bound t ht0 htT) (H.bound_int t ht0 htT)
      (H.profile_hasDeriv t ht0 htT)
  have hscaled :
      HasDerivWithinAt
        (fun s : ℝ => 2 * wholeLineLowerHalfDeficitEnergy U lo s)
        (2 * wholeLineWeightedTimeTerm (wholeLineLowerDeficitProfile U lo)
          (wholeLineNegTimeDeriv U) t) (Set.Ici t) t :=
    (HasDerivAt.const_mul (2 : ℝ) (by
      simpa [wholeLineLowerHalfDeficitEnergy] using hhalf)).hasDerivWithinAt
  rw [wholeLineLower_weightedNegTimeTerm_eq_neg_barrierTimeTerm] at hscaled
  have hscaled' :
      HasDerivWithinAt
        (fun s : ℝ => 2 * wholeLineLowerHalfDeficitEnergy U lo s)
        (-(2 * wholeLineLowerBarrierTimeTerm U lo t)) (Set.Ici t) t := by
    simpa [mul_neg] using hscaled
  have hfun :
      (fun s : ℝ => 2 * wholeLineLowerHalfDeficitEnergy U lo s) =
        wholeLineLowerDeficitEnergy U lo := by
    funext s
    rw [wholeLineLowerDeficitEnergy_eq_two_half]
  simpa using hfun ▸ hscaled'

theorem wholeLineUpper_pdeSubstitution_field_of_solution
    {p : CMParams} {T : ℝ} {U V : ℝ → ℝ → ℝ} {hi : ℝ}
    (hsol : IsClassicalSolution p T U V)
    (H : WholeLineUpperPDESubstitutionData p T U V hi) :
    ∀ t, 0 < t → t < T →
      wholeLineUpperBarrierTimeTerm U hi t =
        wholeLineUpperBarrierDiffusionTerm U hi t -
          p.χ * wholeLineUpperBarrierChemotaxisTerm p U V hi t +
        wholeLineUpperBarrierReactionTerm p U hi t := by
  intro t ht0 htT
  have hweightedPDE :
      ∀ᵐ x ∂volume,
        wholeLineUpperExcessProfile U hi t x * wholeLineTimeDeriv U t x =
          wholeLineUpperExcessProfile U hi t x * wholeLineDiffusionDensity U t x
            - p.χ *
                (wholeLineUpperExcessProfile U hi t x *
                  wholeLineChemotaxisDensity p U V t x)
            + wholeLineUpperExcessProfile U hi t x *
                wholeLineLogisticDensity p U t x := by
    exact Eventually.of_forall fun x => by
      have hpde := hsol.pde_u t x ht0 htT
      unfold wholeLineTimeDeriv wholeLineDiffusionDensity
        wholeLineChemotaxisDensity wholeLineLogisticDensity
      rw [hpde]
      ring
  have hAtom :=
    wholeLineUpper_pdeSubstitution_of_integrable
      (p := p) (U := U) (V := V) (phi_t := wholeLineTimeDeriv U)
      (hi := hi) (t := t)
      (H.diffusion_int t ht0 htT) (H.chemotaxis_int t ht0 htT)
      (H.reaction_int t ht0 htT) hweightedPDE
  simpa [wholeLineUpper_weightedTimeTerm_eq_barrierTimeTerm,
    wholeLineUpperBarrierDiffusionTerm, wholeLineUpperBarrierChemotaxisTerm,
    wholeLineUpperBarrierReactionTerm, wholeLineUpperBarrierTest,
    wholeLineUpperExcessProfile, wholeLineDiffusionIntegral,
    wholeLineChemotaxisIntegral, wholeLineLogisticIntegral,
    wholeLineDiffusionDensity, wholeLineChemotaxisDensity,
    wholeLineLogisticDensity] using hAtom

theorem wholeLineLower_pdeSubstitution_field_of_solution
    {p : CMParams} {T : ℝ} {U V : ℝ → ℝ → ℝ} {lo : ℝ}
    (hsol : IsClassicalSolution p T U V)
    (H : WholeLineLowerPDESubstitutionData p T U V lo) :
    ∀ t, 0 < t → t < T →
      wholeLineLowerBarrierTimeTerm U lo t =
        wholeLineLowerBarrierDiffusionTerm U lo t -
          p.χ * wholeLineLowerBarrierChemotaxisTerm p U V lo t +
        wholeLineLowerBarrierReactionTerm p U lo t := by
  intro t ht0 htT
  have hweightedPDE :
      ∀ᵐ x ∂volume,
        wholeLineLowerDeficitProfile U lo t x * wholeLineNegTimeDeriv U t x =
          - (wholeLineLowerDeficitProfile U lo t x *
                wholeLineDiffusionDensity U t x
              - p.χ *
                  (wholeLineLowerDeficitProfile U lo t x *
                    wholeLineChemotaxisDensity p U V t x)
              + wholeLineLowerDeficitProfile U lo t x *
                  wholeLineLogisticDensity p U t x) := by
    exact Eventually.of_forall fun x => by
      have hpde := hsol.pde_u t x ht0 htT
      unfold wholeLineNegTimeDeriv wholeLineTimeDeriv wholeLineDiffusionDensity
        wholeLineChemotaxisDensity wholeLineLogisticDensity
      rw [hpde]
      ring
  have hAtom :=
    wholeLineLower_pdeSubstitution_of_integrable
      (p := p) (U := U) (V := V) (phi_t := wholeLineNegTimeDeriv U)
      (lo := lo) (t := t)
      (H.diffusion_int t ht0 htT) (H.chemotaxis_int t ht0 htT)
      (H.reaction_int t ht0 htT) hweightedPDE
  have hneg :
      -wholeLineWeightedTimeTerm (wholeLineLowerDeficitProfile U lo)
          (wholeLineNegTimeDeriv U) t =
        wholeLineDiffusionIntegral (wholeLineLowerDeficitProfile U lo) U t
          - p.χ * wholeLineChemotaxisIntegral p
              (wholeLineLowerDeficitProfile U lo) U V t
          + wholeLineLogisticIntegral p (wholeLineLowerDeficitProfile U lo) U t := by
    linarith
  calc
    wholeLineLowerBarrierTimeTerm U lo t
        = -wholeLineWeightedTimeTerm (wholeLineLowerDeficitProfile U lo)
            (wholeLineNegTimeDeriv U) t := by
          rw [wholeLineLower_weightedNegTimeTerm_eq_neg_barrierTimeTerm]
          ring
    _ = wholeLineDiffusionIntegral (wholeLineLowerDeficitProfile U lo) U t
          - p.χ * wholeLineChemotaxisIntegral p
              (wholeLineLowerDeficitProfile U lo) U V t
          + wholeLineLogisticIntegral p (wholeLineLowerDeficitProfile U lo) U t :=
          hneg
    _ = wholeLineLowerBarrierDiffusionTerm U lo t -
          p.χ * wholeLineLowerBarrierChemotaxisTerm p U V lo t +
        wholeLineLowerBarrierReactionTerm p U lo t := by
          simp [wholeLineLowerBarrierDiffusionTerm,
            wholeLineLowerBarrierChemotaxisTerm,
            wholeLineLowerBarrierReactionTerm, wholeLineLowerBarrierTest,
            wholeLineLowerDeficitProfile, wholeLineDiffusionIntegral,
            wholeLineChemotaxisIntegral, wholeLineLogisticIntegral,
            wholeLineDiffusionDensity, wholeLineChemotaxisDensity,
            wholeLineLogisticDensity, wholeLineReaction]

theorem wholeLineUpper_diffusionIBP_decay_field_of_data
    {T : ℝ} {U : ℝ → ℝ → ℝ} {hi : ℝ}
    (H : WholeLineUpperDiffusionIBPData T U hi) :
    ∀ t, 0 < t → t < T →
      wholeLineUpperBarrierDiffusionTerm U hi t ≤ 0 := by
  intro t ht0 htT
  have hIBP :=
    wholeLine_diffusion_ibp_decay_with_derivatives
      (wholeLineUpperBarrierTest U hi t) (H.flux t)
      (fun x : ℝ => iteratedDeriv 2 (U t) x)
      (H.profile_deriv t ht0 htT) (H.flux_deriv t ht0 htT)
      (H.lhs_int t ht0 htT) (H.energy_int t ht0 htT)
      (H.decay_bot t ht0 htT) (H.decay_top t ht0 htT)
  have hEq :
      wholeLineUpperBarrierDiffusionTerm U hi t =
        -∫ x : ℝ, H.flux t x * H.flux t x := by
    simpa [wholeLineUpperBarrierDiffusionTerm] using hIBP
  rw [hEq]
  exact neg_nonpos.mpr (integral_nonneg fun x => mul_self_nonneg (H.flux t x))

theorem wholeLineLower_diffusionIBP_decay_field_of_data
    {T : ℝ} {U : ℝ → ℝ → ℝ} {lo : ℝ}
    (H : WholeLineLowerDiffusionIBPData T U lo) :
    ∀ t, 0 < t → t < T →
      0 ≤ wholeLineLowerBarrierDiffusionTerm U lo t := by
  intro t ht0 htT
  have hIBP :=
    wholeLine_diffusion_ibp_decay_with_derivatives
      (wholeLineLowerBarrierTest U lo t) (H.flux t)
      (fun x : ℝ => -iteratedDeriv 2 (U t) x)
      (H.profile_deriv t ht0 htT) (H.flux_deriv t ht0 htT)
      (H.lhs_int t ht0 htT) (H.energy_int t ht0 htT)
      (H.decay_bot t ht0 htT) (H.decay_top t ht0 htT)
  have hNegTerm :
      (∫ x : ℝ,
        wholeLineLowerBarrierTest U lo t x * (-iteratedDeriv 2 (U t) x)) =
        -wholeLineLowerBarrierDiffusionTerm U lo t := by
    unfold wholeLineLowerBarrierDiffusionTerm
    rw [← integral_neg]
    congr
    ext x
    ring
  have hEq :
      wholeLineLowerBarrierDiffusionTerm U lo t =
        ∫ x : ℝ, H.flux t x * H.flux t x := by
    linarith
  rw [hEq]
  exact integral_nonneg fun x => mul_self_nonneg (H.flux t x)

theorem wholeLineUpper_chemotaxisCrossControl_field_of_data
    {p : CMParams} {T : ℝ} {U V : ℝ → ℝ → ℝ} {hi K Cgrad : ℝ}
    (hE_nonneg : ∀ t, 0 < t → t < T →
      0 ≤ wholeLineUpperExcessEnergy U hi t)
    (H : WholeLineUpperChemotaxisCrossData p T U V hi K Cgrad) :
    ∀ t, 0 < t → t < T →
      2 * (-p.χ * wholeLineUpperBarrierChemotaxisTerm p U V hi t) ≤
        K * wholeLineUpperExcessEnergy U hi t := by
  intro t ht0 htT
  let B := H.bounds t ht0 htT
  let E := wholeLineUpperExcessEnergy U hi t
  let D := wholeLineGradientDissipation (H.flux t)
  have hAtom :=
    wholeLine_chemotaxisCrossControl_postIBP p B
      (H.zero_off_excess t ht0 htT) (H.flux_sq_int t ht0 htT)
      (H.cross_int t ht0 htT) (H.restricted_sq_int t ht0 htT)
  have hpost :
      -p.χ * wholeLineUpperBarrierChemotaxisTerm p U V hi t ≤
        (1 / 2) * D + B.K * E := by
    rw [H.postIBP t ht0 htT]
    simpa [B, E, D] using hAtom
  calc
    2 * (-p.χ * wholeLineUpperBarrierChemotaxisTerm p U V hi t)
        ≤ 2 * ((1 / 2) * D + B.K * E) :=
          mul_le_mul_of_nonneg_left hpost (by norm_num)
    _ = D + 2 * B.K * E := by ring
    _ ≤ Cgrad * E + 2 * B.K * E := by
          have h :=
            add_le_add_right
              (by simpa [E, D] using H.gradient_control t ht0 htT)
              (2 * B.K * E)
          simpa [add_comm, add_left_comm, add_assoc] using h
    _ = (Cgrad + 2 * B.K) * E := by ring
    _ ≤ K * E :=
          mul_le_mul_of_nonneg_right
            (by simpa [B] using H.K_control t ht0 htT)
            (by simpa [E] using hE_nonneg t ht0 htT)

theorem wholeLineLower_chemotaxisCrossControl_field_of_data
    {p : CMParams} {T : ℝ} {U V : ℝ → ℝ → ℝ} {lo K Cgrad : ℝ}
    (hE_nonneg : ∀ t, 0 < t → t < T →
      0 ≤ wholeLineLowerDeficitEnergy U lo t)
    (H : WholeLineLowerChemotaxisCrossData p T U V lo K Cgrad) :
    ∀ t, 0 < t → t < T →
      2 * (p.χ * wholeLineLowerBarrierChemotaxisTerm p U V lo t) ≤
        K * wholeLineLowerDeficitEnergy U lo t := by
  intro t ht0 htT
  let B := H.bounds t ht0 htT
  let E := wholeLineLowerDeficitEnergy U lo t
  let D := wholeLineGradientDissipation (H.flux t)
  have hAtom :=
    wholeLine_chemotaxisCrossControl_postIBP p B
      (H.zero_off_excess t ht0 htT) (H.flux_sq_int t ht0 htT)
      (H.cross_int t ht0 htT) (H.restricted_sq_int t ht0 htT)
  have hpost :
      p.χ * wholeLineLowerBarrierChemotaxisTerm p U V lo t ≤
        (1 / 2) * D + B.K * E := by
    rw [← H.postIBP t ht0 htT] at hAtom
    simpa [B, E, D] using hAtom
  calc
    2 * (p.χ * wholeLineLowerBarrierChemotaxisTerm p U V lo t)
        ≤ 2 * ((1 / 2) * D + B.K * E) :=
          mul_le_mul_of_nonneg_left hpost (by norm_num)
    _ = D + 2 * B.K * E := by ring
    _ ≤ Cgrad * E + 2 * B.K * E := by
          have h :=
            add_le_add_right
              (by simpa [E, D] using H.gradient_control t ht0 htT)
              (2 * B.K * E)
          simpa [add_comm, add_left_comm, add_assoc] using h
    _ = (Cgrad + 2 * B.K) * E := by ring
    _ ≤ K * E :=
          mul_le_mul_of_nonneg_right
            (by simpa [B] using H.K_control t ht0 htT)
            (by simpa [E] using hE_nonneg t ht0 htT)

theorem wholeLineUpperExcessEnergy_nonneg
    (U : ℝ → ℝ → ℝ) (hi t : ℝ) :
    0 ≤ wholeLineUpperExcessEnergy U hi t := by
  unfold wholeLineUpperExcessEnergy
  exact integral_nonneg fun x => sq_nonneg (max (U t x - hi) 0)

theorem wholeLineLowerDeficitEnergy_nonneg
    (U : ℝ → ℝ → ℝ) (lo t : ℝ) :
    0 ≤ wholeLineLowerDeficitEnergy U lo t := by
  unfold wholeLineLowerDeficitEnergy
  exact integral_nonneg fun x => sq_nonneg (max (lo - U t x) 0)

def wholeLineUpperBarrierEnergySteps_of_solution
    {p : CMParams} {T : ℝ} {U V : ℝ → ℝ → ℝ} {hi : ℝ}
    (hsol : IsClassicalSolution p T U V)
    (K Cgrad : ℝ)
    (hK_nonneg : 0 ≤ K)
    (hhi : 1 ≤ hi)
    (hcont : ∀ s t, 0 < s → s ≤ t → t < T →
      ContinuousOn (wholeLineUpperExcessEnergy U hi) (Set.Icc s t))
    (hinitial : ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → s < T →
      wholeLineUpperExcessEnergy U hi s < ε)
    (htime : WholeLineUpperTimeLeibnizData T U hi)
    (hpde : WholeLineUpperPDESubstitutionData p T U V hi)
    (hdiff : WholeLineUpperDiffusionIBPData T U hi)
    (hchem : WholeLineUpperChemotaxisCrossData p T U V hi K Cgrad) :
    WholeLineUpperBarrierEnergySteps p T U V hi where
  K := K
  K_nonneg := hK_nonneg
  hi_one_le := hhi
  nonneg := fun t _ _ => wholeLineUpperExcessEnergy_nonneg U hi t
  cont := hcont
  initial_vanishes := hinitial
  timeLeibniz := wholeLineUpper_timeLeibniz_field_of_data htime
  pdeSubstitution := wholeLineUpper_pdeSubstitution_field_of_solution hsol hpde
  diffusionIBP_decay := wholeLineUpper_diffusionIBP_decay_field_of_data hdiff
  chemotaxisCrossControl :=
    wholeLineUpper_chemotaxisCrossControl_field_of_data
      (fun t _ _ => wholeLineUpperExcessEnergy_nonneg U hi t) hchem

def wholeLineLowerBarrierEnergySteps_of_solution
    {p : CMParams} {T : ℝ} {U V : ℝ → ℝ → ℝ} {lo : ℝ}
    (hsol : IsClassicalSolution p T U V)
    (K Cgrad : ℝ)
    (hK_nonneg : 0 ≤ K)
    (hU_nonneg : ∀ t x, 0 ≤ U t x)
    (hlo : lo ≤ 1)
    (hcont : ∀ s t, 0 < s → s ≤ t → t < T →
      ContinuousOn (wholeLineLowerDeficitEnergy U lo) (Set.Icc s t))
    (hinitial : ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → s < T →
      wholeLineLowerDeficitEnergy U lo s < ε)
    (htime : WholeLineLowerTimeLeibnizData T U lo)
    (hpde : WholeLineLowerPDESubstitutionData p T U V lo)
    (hdiff : WholeLineLowerDiffusionIBPData T U lo)
    (hchem : WholeLineLowerChemotaxisCrossData p T U V lo K Cgrad) :
    WholeLineLowerBarrierEnergySteps p T U V lo where
  K := K
  K_nonneg := hK_nonneg
  U_nonneg := hU_nonneg
  lo_le_one := hlo
  nonneg := fun t _ _ => wholeLineLowerDeficitEnergy_nonneg U lo t
  cont := hcont
  initial_vanishes := hinitial
  timeLeibniz := wholeLineLower_timeLeibniz_field_of_data htime
  pdeSubstitution := wholeLineLower_pdeSubstitution_field_of_solution hsol hpde
  diffusionIBP_decay := wholeLineLower_diffusionIBP_decay_field_of_data hdiff
  chemotaxisCrossControl :=
    wholeLineLower_chemotaxisCrossControl_field_of_data
      (fun t _ _ => wholeLineLowerDeficitEnergy_nonneg U lo t) hchem

def wholeLineUpperBarrierEnergyFrontier_of_solution
    {p : CMParams} {T : ℝ} {U V : ℝ → ℝ → ℝ} {hi : ℝ}
    (hsol : IsClassicalSolution p T U V)
    (K Cgrad : ℝ)
    (hK_nonneg : 0 ≤ K)
    (hhi : 1 ≤ hi)
    (hcont : ∀ s t, 0 < s → s ≤ t → t < T →
      ContinuousOn (wholeLineUpperExcessEnergy U hi) (Set.Icc s t))
    (hinitial : ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → s < T →
      wholeLineUpperExcessEnergy U hi s < ε)
    (htime : WholeLineUpperTimeLeibnizData T U hi)
    (hpde : WholeLineUpperPDESubstitutionData p T U V hi)
    (hdiff : WholeLineUpperDiffusionIBPData T U hi)
    (hchem : WholeLineUpperChemotaxisCrossData p T U V hi K Cgrad) :
    WholeLineBarrierEnergyFrontier (wholeLineUpperExcessEnergy U hi) T :=
  wholeLine_upperBarrierEnergyFrontierOfSteps
    (wholeLineUpperBarrierEnergySteps_of_solution hsol K Cgrad hK_nonneg hhi
      hcont hinitial htime hpde hdiff hchem)

def wholeLineLowerBarrierEnergyFrontier_of_solution
    {p : CMParams} {T : ℝ} {U V : ℝ → ℝ → ℝ} {lo : ℝ}
    (hsol : IsClassicalSolution p T U V)
    (K Cgrad : ℝ)
    (hK_nonneg : 0 ≤ K)
    (hU_nonneg : ∀ t x, 0 ≤ U t x)
    (hlo : lo ≤ 1)
    (hcont : ∀ s t, 0 < s → s ≤ t → t < T →
      ContinuousOn (wholeLineLowerDeficitEnergy U lo) (Set.Icc s t))
    (hinitial : ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → s < T →
      wholeLineLowerDeficitEnergy U lo s < ε)
    (htime : WholeLineLowerTimeLeibnizData T U lo)
    (hpde : WholeLineLowerPDESubstitutionData p T U V lo)
    (hdiff : WholeLineLowerDiffusionIBPData T U lo)
    (hchem : WholeLineLowerChemotaxisCrossData p T U V lo K Cgrad) :
    WholeLineBarrierEnergyFrontier (wholeLineLowerDeficitEnergy U lo) T :=
  wholeLine_lowerBarrierEnergyFrontierOfSteps
    (wholeLineLowerBarrierEnergySteps_of_solution hsol K Cgrad hK_nonneg
      hU_nonneg hlo hcont hinitial htime hpde hdiff hchem)

theorem wholeLineUpperBarrierEnergyFrontier_nonempty_of_solution
    {p : CMParams} {T : ℝ} {U V : ℝ → ℝ → ℝ} {hi : ℝ}
    (hsol : IsClassicalSolution p T U V)
    (K Cgrad : ℝ)
    (hK_nonneg : 0 ≤ K)
    (hhi : 1 ≤ hi)
    (hcont : ∀ s t, 0 < s → s ≤ t → t < T →
      ContinuousOn (wholeLineUpperExcessEnergy U hi) (Set.Icc s t))
    (hinitial : ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → s < T →
      wholeLineUpperExcessEnergy U hi s < ε)
    (htime : WholeLineUpperTimeLeibnizData T U hi)
    (hpde : WholeLineUpperPDESubstitutionData p T U V hi)
    (hdiff : WholeLineUpperDiffusionIBPData T U hi)
    (hchem : WholeLineUpperChemotaxisCrossData p T U V hi K Cgrad) :
    Nonempty (WholeLineBarrierEnergyFrontier (wholeLineUpperExcessEnergy U hi) T) :=
  ⟨wholeLineUpperBarrierEnergyFrontier_of_solution hsol K Cgrad hK_nonneg hhi
    hcont hinitial htime hpde hdiff hchem⟩

theorem wholeLineLowerBarrierEnergyFrontier_nonempty_of_solution
    {p : CMParams} {T : ℝ} {U V : ℝ → ℝ → ℝ} {lo : ℝ}
    (hsol : IsClassicalSolution p T U V)
    (K Cgrad : ℝ)
    (hK_nonneg : 0 ≤ K)
    (hU_nonneg : ∀ t x, 0 ≤ U t x)
    (hlo : lo ≤ 1)
    (hcont : ∀ s t, 0 < s → s ≤ t → t < T →
      ContinuousOn (wholeLineLowerDeficitEnergy U lo) (Set.Icc s t))
    (hinitial : ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → s < T →
      wholeLineLowerDeficitEnergy U lo s < ε)
    (htime : WholeLineLowerTimeLeibnizData T U lo)
    (hpde : WholeLineLowerPDESubstitutionData p T U V lo)
    (hdiff : WholeLineLowerDiffusionIBPData T U lo)
    (hchem : WholeLineLowerChemotaxisCrossData p T U V lo K Cgrad) :
    Nonempty (WholeLineBarrierEnergyFrontier (wholeLineLowerDeficitEnergy U lo) T) :=
  ⟨wholeLineLowerBarrierEnergyFrontier_of_solution hsol K Cgrad hK_nonneg
    hU_nonneg hlo hcont hinitial htime hpde hdiff hchem⟩

#print axioms wholeLineUpperBarrierEnergySteps_of_solution
#print axioms wholeLineLowerBarrierEnergySteps_of_solution
#print axioms wholeLineUpperBarrierEnergyFrontier_of_solution
#print axioms wholeLineLowerBarrierEnergyFrontier_of_solution
#print axioms wholeLineUpperBarrierEnergyFrontier_nonempty_of_solution
#print axioms wholeLineLowerBarrierEnergyFrontier_nonempty_of_solution

end ShenWork.PaperOne
