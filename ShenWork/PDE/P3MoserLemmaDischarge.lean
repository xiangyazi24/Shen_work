import ShenWork.Paper2.IntervalDomainMCL

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.Paper2.IntervalDomainMCL
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainLpMonotonicity
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserLemmaDischarge

/-! ### Dissipation/drop packaging -/

theorem moserDissipationDropBefore_of_raw_drop
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T rho p0 : ℝ}
    (hdrop :
      ∀ p, p0 ≤ p → ∀ B t, 0 < t → t < T →
        0 ≤
          (1 / p) * deriv (fun τ => D.integral (fun x => (u τ x) ^ p)) t +
            B * D.integral (fun x => (u t x) ^ p)) :
    MoserDissipationDropBefore D u T rho p0 := by
  intro p hp _A B _K _L_const _hfull t ht0 htT
  exact hdrop p hp B t ht0 htT

/-! ### Closed-time L² seed from the integrated identity -/

theorem intervalDomainLpAbsEnergy_two_zero_eq_of_pointwise_trace
    {u₀ : intervalDomain.Point → ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (h0 : ∀ x : intervalDomain.Point, u 0 x = u₀ x) :
    intervalDomainLpAbsEnergy 2 u 0 =
      intervalDomain.integral (fun x : intervalDomain.Point => |u₀ x| ^ (2 : ℝ)) := by
  unfold intervalDomainLpAbsEnergy
  congr
  ext x
  rw [h0 x]

structure ClosedEnergyIdentityTraceData
    (T : ℝ) (u₀ : intervalDomain.Point → ℝ)
    (u : ℝ → intervalDomain.Point → ℝ) where
  nonnegT : 0 ≤ T
  g : ℝ → ℝ
  g_integrable : IntegrableOn g (Set.uIcc (0 : ℝ) T) volume
  energy_eq :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      intervalDomainLpAbsEnergy 2 u t =
        intervalDomainLpAbsEnergy 2 u 0 + ∫ s in (0 : ℝ)..t, g s
  initial_trace_energy :
    intervalDomainLpAbsEnergy 2 u 0 =
      intervalDomain.integral (fun x : intervalDomain.Point => |u₀ x| ^ (2 : ℝ))
  energyHasDerivWithin :
    ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt
        (fun τ => intervalDomainLpAbsEnergy 2 u τ)
        (deriv (fun τ => intervalDomainLpAbsEnergy 2 u τ) t)
        (Set.Ici t) t
  derivativeAlignment :
    ∀ t ∈ Set.Ico (0 : ℝ) T,
      deriv (fun τ => intervalDomainLpAbsEnergy 2 u τ) t =
        2 * deriv (fun τ => intervalDomainL2HalfEnergy u τ) t

theorem ClosedEnergyIdentityTraceData.energyContinuous
    {T : ℝ} {u₀ : intervalDomain.Point → ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (h : ClosedEnergyIdentityTraceData T u₀ u) :
    ContinuousOn (fun t => intervalDomainLpAbsEnergy 2 u t)
      (Set.Icc (0 : ℝ) T) := by
  have hprim_u :
      ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, h.g s)
        (Set.uIcc (0 : ℝ) T) :=
    intervalIntegral.continuousOn_primitive_interval
      (μ := volume) (a := (0 : ℝ)) (b := T) h.g_integrable
  have hprim :
      ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, h.g s)
        (Set.Icc (0 : ℝ) T) := by
    simpa [Set.uIcc_of_le h.nonnegT] using hprim_u
  have hmodel :
      ContinuousOn
        (fun t => intervalDomainLpAbsEnergy 2 u 0 + ∫ s in (0 : ℝ)..t, h.g s)
        (Set.Icc (0 : ℝ) T) :=
    continuousOn_const.add hprim
  exact hmodel.congr (fun t ht => h.energy_eq t ht)

theorem ClosedEnergyIdentityTraceData.initialBound
    {T : ℝ} {u₀ : intervalDomain.Point → ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (h : ClosedEnergyIdentityTraceData T u₀ u) :
    ∃ δ0, 0 ≤ δ0 ∧ intervalDomainLpAbsEnergy 2 u 0 ≤ δ0 := by
  let E0 : ℝ :=
    intervalDomain.integral (fun x : intervalDomain.Point => |u₀ x| ^ (2 : ℝ))
  refine ⟨max E0 (0 : ℝ), le_max_right E0 (0 : ℝ), ?_⟩
  rw [h.initial_trace_energy]
  exact le_max_left E0 0

theorem l2SeedRegularity_of_closedEnergyIdentityTraceData
    {T : ℝ} {u₀ : intervalDomain.Point → ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (h : ClosedEnergyIdentityTraceData T u₀ u) :
    IntervalDomainL2SeedRegularityFrontier T u where
  energyContinuous := h.energyContinuous
  energyHasDerivWithin := h.energyHasDerivWithin
  initialBound := h.initialBound
  derivativeAlignment := h.derivativeAlignment

/-! ### The proved regular slice GN/Agmon package -/

theorem unitInterval_regular_power_GNYoung :
    UnitIntervalPowerGNYoungForMoser :=
  unitIntervalPowerGNYoungForMoser_proved

theorem relativeMoserInterpolationBefore_of_massGradient
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T rho p0 : ℝ}
    (cGrad : ℝ → ℝ)
    (hcGrad : ∀ p, p0 ≤ p → 0 < cGrad p)
    (hMG : ∀ p, p0 ≤ p → ∀ eta > 0, ∃ Ceta,
      LpMassGradientInterpolationEstimate D (p + rho) eta Ceta T u)
    (hgrad : ∀ p, p0 ≤ p → ∀ t, 0 < t → t < T →
      D.integral (fun x =>
          (u t x) ^ (p + rho - 2) * (D.gradNorm (u t) x) ^ 2) ≤
        cGrad p * D.integral (fun x =>
          (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
    (hmassToLp : MoserMassPowerToCurrentLpLowerOrder D u T rho p0) :
    RelativeMoserInterpolationBefore D u T rho p0 :=
  moserClosure_relativeInterpolationBefore_of_mass_gradient_estimate
    cGrad hcGrad hMG hgrad hmassToLp

/-! ### What the current dissipation predicate cannot express -/

def unitMoserCounterDomain : BoundedDomainData where
  Point := Unit
  inside := Set.univ
  boundary := ∅
  volume := 1
  supNorm := fun f => |f ()|
  infValue := fun f => f ()
  integral := fun f => f ()
  gradNorm := fun _ _ => 0
  timeDeriv := fun _ _ _ => 0
  laplacian := fun _ _ => 0
  chemotaxisDiv := fun _ _ _ _ => 0
  crossDiffusionEnergyTerm := fun _ _ _ _ => 0
  normalDeriv := fun _ _ => 0
  initialAdmissible := fun _ => True
  classicalRegularity := fun _ _ _ => True

def unitMoserCounterU (_t : ℝ) (_x : Unit) : ℝ := 1

theorem unitMoserCounter_has_LpBootstrapEnergyInequality :
    LpBootstrapEnergyInequality
      unitMoserCounterDomain unitMoserCounterU 1 1 1 := by
  intro p hp
  refine ⟨1, by norm_num, 1, by norm_num, 1, by norm_num, 0, ?_⟩
  intro t ht0 htT
  simp [unitMoserCounterDomain, unitMoserCounterU]

theorem unitMoserCounter_not_MoserDissipationDropBefore :
    ¬ MoserDissipationDropBefore
      unitMoserCounterDomain unitMoserCounterU 1 1 1 := by
  intro h
  have hfull :
      ∀ t, 0 < t → t < (1 : ℝ) →
        (1 / (1 : ℝ)) *
            deriv
              (fun τ =>
                unitMoserCounterDomain.integral
                  (fun x => (unitMoserCounterU τ x) ^ (1 : ℝ))) t +
          0 *
            unitMoserCounterDomain.integral
              (fun x =>
                (unitMoserCounterDomain.gradNorm
                  (fun y => (unitMoserCounterU t y) ^ ((1 : ℝ) / 2)) x) ^ 2) +
          (-1) *
            unitMoserCounterDomain.integral
              (fun x => (unitMoserCounterU t x) ^ (1 : ℝ)) ≤
        0 *
            unitMoserCounterDomain.integral
              (fun x => (unitMoserCounterU t x) ^ ((1 : ℝ) + 1)) +
          0 := by
    intro t ht0 htT
    simp [unitMoserCounterDomain, unitMoserCounterU]
  have hbad :=
    h (1 : ℝ) (le_rfl : (1 : ℝ) ≤ 1)
      0 (-1) 0 0 hfull (1 / 2) (by norm_num) (by norm_num)
  simp [unitMoserCounterDomain, unitMoserCounterU] at hbad
  norm_num at hbad

theorem LpBootstrapEnergyInequality_does_not_imply_MoserDissipationDropBefore :
    ∃ D : BoundedDomainData, ∃ u : ℝ → D.Point → ℝ,
      LpBootstrapEnergyInequality D u 1 1 1 ∧
        ¬ MoserDissipationDropBefore D u 1 1 1 := by
  exact
    ⟨unitMoserCounterDomain, unitMoserCounterU,
      unitMoserCounter_has_LpBootstrapEnergyInequality,
      unitMoserCounter_not_MoserDissipationDropBefore⟩

#print axioms l2SeedRegularity_of_closedEnergyIdentityTraceData
#print axioms intervalDomainLpAbsEnergy_two_zero_eq_of_pointwise_trace
#print axioms unitInterval_regular_power_GNYoung
#print axioms moserDissipationDropBefore_of_raw_drop
#print axioms relativeMoserInterpolationBefore_of_massGradient
#print axioms LpBootstrapEnergyInequality_does_not_imply_MoserDissipationDropBefore

end ShenWork.IntervalDomainExistence.P3MoserLemmaDischarge

end
