import ShenWork.Paper2.IntervalChiNegH1ScalarRegularityProducer
import ShenWork.PDE.IntervalDomainExistence

/-!
# H¹ initial endpoint continuity

This file reduces the H¹ right-continuity-at-zero input to the same two-part
endpoint data used elsewhere in the project: deleted-right energy convergence
to the prescribed initial datum, plus compatibility of the stored zero slice.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1ScalarDIProducer
open ShenWork.Paper2.IntervalChiNegH1ScalarRegularityProducer

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1InitialContinuity

/-- The H¹ seminorm energy of the prescribed initial datum. -/
def H1InitialEnergy (u₀ : intervalDomainPoint → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..1,
    (deriv (intervalDomainLift u₀) x) ^ 2

/-- Deleted-right convergence of positive-time H¹ energy to the prescribed
initial H¹ energy.  This is not a statement about the stored slice `u 0`. -/
def H1InitialTraceEnergyTendsto
    (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (T : ℝ) : Prop :=
  Tendsto (H1energy u) (𝓝[Set.Ioc (0 : ℝ) T] (0 : ℝ))
    (𝓝 (H1InitialEnergy u₀))

/-- Compatibility of the stored zero slice with the prescribed initial datum at
the H¹ energy level.  Positive-time trace convergence alone does not imply this.
-/
def H1InitialEnergyCompatibleAtZero
    (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  H1energy u 0 = H1InitialEnergy u₀

/-- Bundled H¹ endpoint data: deleted-right convergence to the prescribed
initial H¹ energy plus compatibility of the stored zero slice. -/
structure H1InitialEndpointData
    (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (T : ℝ) : Prop where
  tendsto : H1InitialTraceEnergyTendsto u₀ u T
  compatible : H1InitialEnergyCompatibleAtZero u₀ u

private theorem intervalIntegral_constLift_deriv_sq_zero (c : ℝ) :
    (∫ x in (0 : ℝ)..1,
      (deriv (intervalDomainLift (fun _ : intervalDomainPoint => c)) x) ^ 2) = 0 := by
  calc
    (∫ x in (0 : ℝ)..1,
      (deriv (intervalDomainLift (fun _ : intervalDomainPoint => c)) x) ^ 2)
        = ∫ _x in (0 : ℝ)..1, (0 : ℝ) := by
          refine intervalIntegral.integral_congr (fun x hx => ?_)
          rw [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] at hx
          have hderiv :
              deriv (intervalDomainLift (fun _ : intervalDomainPoint => c)) x = 0 := by
            by_cases hx0 : x = 0
            · subst x
              exact (intervalDomainLift_const_deriv_endpoint_zero c).1
            · by_cases hx1 : x = 1
              · subst x
                exact (intervalDomainLift_const_deriv_endpoint_zero c).2
              · exact intervalDomainLift_const_deriv_zero c
                  ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hx1⟩
          simp [hderiv]
    _ = 0 := by simp

/-- The H¹ energy of a spatially constant trajectory is zero. -/
theorem H1energy_const (c τ : ℝ) :
    H1energy (fun _ (_ : intervalDomainPoint) => c) τ = 0 := by
  simp [H1energy, intervalIntegral_constLift_deriv_sq_zero c]

/-- The prescribed initial H¹ energy of a spatially constant datum is zero. -/
theorem H1InitialEnergy_const (c : ℝ) :
    H1InitialEnergy (fun _ : intervalDomainPoint => c) = 0 := by
  simp [H1InitialEnergy, intervalIntegral_constLift_deriv_sq_zero c]

/-- A constant trajectory has deleted-right H¹ energy trace equal to its
constant initial datum. -/
theorem H1InitialTraceEnergyTendsto_const {T c : ℝ} :
    H1InitialTraceEnergyTendsto
      (fun _ : intervalDomainPoint => c)
      (fun _ (_ : intervalDomainPoint) => c)
      T := by
  have hfun :
      (fun τ : ℝ => H1energy (fun _ (_ : intervalDomainPoint) => c) τ) =
        fun _ : ℝ => (0 : ℝ) := by
    funext τ
    exact H1energy_const c τ
  unfold H1InitialTraceEnergyTendsto
  change Tendsto (fun τ : ℝ => H1energy (fun _ (_ : intervalDomainPoint) => c) τ)
    (𝓝[Set.Ioc (0 : ℝ) T] (0 : ℝ))
    (𝓝 (H1InitialEnergy (fun _ : intervalDomainPoint => c)))
  rw [hfun, H1InitialEnergy_const c]
  exact tendsto_const_nhds

/-- A constant trajectory is compatible with its constant initial datum at the
stored zero slice. -/
theorem H1InitialEnergyCompatibleAtZero_const (c : ℝ) :
    H1InitialEnergyCompatibleAtZero
      (fun _ : intervalDomainPoint => c)
      (fun _ (_ : intervalDomainPoint) => c) := by
  unfold H1InitialEnergyCompatibleAtZero
  rw [H1energy_const c 0, H1InitialEnergy_const c]

/-- Bundled H¹ endpoint data for a spatially constant trajectory. -/
theorem H1InitialEndpointData_const {T c : ℝ} :
    H1InitialEndpointData
      (fun _ : intervalDomainPoint => c)
      (fun _ (_ : intervalDomainPoint) => c)
      T :=
  ⟨H1InitialTraceEnergyTendsto_const, H1InitialEnergyCompatibleAtZero_const c⟩

/-- Bundled H¹ endpoint data for the interval-domain constant datum API. -/
theorem H1InitialEndpointData_constOnInterval {T c : ℝ} :
    H1InitialEndpointData
      (constOnInterval c)
      (fun _ (_ : intervalDomainPoint) => c)
      T := by
  simpa [constOnInterval] using H1InitialEndpointData_const (T := T) (c := c)

/-- Exact equality of the stored zero slice gives the H¹ energy compatibility
field.  This does not imply deleted-right H¹ energy convergence. -/
theorem H1InitialEnergyCompatibleAtZero_of_zeroSlice
    {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (hzero : u 0 = u₀) :
    H1InitialEnergyCompatibleAtZero u₀ u := by
  simp [H1InitialEnergyCompatibleAtZero, H1InitialEnergy, H1energy, hzero]

/-- Pointwise equality of the stored zero slice gives the H¹ energy
compatibility field. -/
theorem H1InitialEnergyCompatibleAtZero_of_zeroSlice_pointwise
    {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (hzero : ∀ x : intervalDomainPoint, u 0 x = u₀ x) :
    H1InitialEnergyCompatibleAtZero u₀ u :=
  H1InitialEnergyCompatibleAtZero_of_zeroSlice (funext hzero)

/-- Deleted-right convergence on `(0, T]` plus the stored value at zero gives
right-continuity on `Ici 0`. -/
theorem tendsto_nhdsWithin_Ici_zero_of_tendsto_nhdsWithin_Ioc_zero
    {f : ℝ → ℝ} {T y₀ : ℝ} (hT : 0 < T)
    (htend : Tendsto f (𝓝[Set.Ioc (0 : ℝ) T] (0 : ℝ)) (𝓝 y₀))
    (h0 : f 0 = y₀) :
    Tendsto f (𝓝[Set.Ici (0 : ℝ)] (0 : ℝ)) (𝓝 y₀) := by
  rw [Metric.tendsto_nhdsWithin_nhds] at htend ⊢
  intro ε hε
  rcases htend ε hε with ⟨δ, hδ, hδ_spec⟩
  refine ⟨min δ T, lt_min hδ hT, ?_⟩
  intro x hxIci hxnear
  by_cases hx0 : x = 0
  · subst x
    simpa [h0] using hε
  · have hx_nonneg : 0 ≤ x := hxIci
    have hx_pos : 0 < x := lt_of_le_of_ne hx_nonneg (Ne.symm hx0)
    have hxnearδ : dist x (0 : ℝ) < δ :=
      lt_of_lt_of_le hxnear (min_le_left _ _)
    have hxnearT : dist x (0 : ℝ) < T :=
      lt_of_lt_of_le hxnear (min_le_right _ _)
    have hxT : x ≤ T := by
      have hxT_lt : x < T := by
        simpa [Real.dist_eq, abs_of_nonneg hx_nonneg] using hxnearT
      exact le_of_lt hxT_lt
    exact hδ_spec ⟨hx_pos, hxT⟩ hxnearδ

/-- Deleted-right H¹ energy convergence plus zero-slice compatibility gives the
`hcont0` input used by the scalar H¹ regularity producer. -/
theorem H1energy_continuousWithinAt_zero_of_initialTraceEnergy
    {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hT : 0 < T)
    (htend : H1InitialTraceEnergyTendsto u₀ u T)
    (hcompat : H1InitialEnergyCompatibleAtZero u₀ u) :
    ContinuousWithinAt (H1energy u) (Set.Ici (0 : ℝ)) (0 : ℝ) := by
  unfold H1InitialTraceEnergyTendsto at htend
  unfold H1InitialEnergyCompatibleAtZero at hcompat
  have hright :
      Tendsto (H1energy u) (𝓝[Set.Ici (0 : ℝ)] (0 : ℝ))
        (𝓝 (H1InitialEnergy u₀)) :=
    tendsto_nhdsWithin_Ici_zero_of_tendsto_nhdsWithin_Ioc_zero
      (f := H1energy u) (T := T) hT htend hcompat
  change Tendsto (H1energy u) (𝓝[Set.Ici (0 : ℝ)] (0 : ℝ))
    (𝓝 (H1energy u 0))
  rw [hcompat]
  exact hright

/-- Bundled endpoint-data version of
`H1energy_continuousWithinAt_zero_of_initialTraceEnergy`. -/
theorem H1energy_continuousWithinAt_zero_of_initialEndpointData
    {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hT : 0 < T)
    (hinit : H1InitialEndpointData u₀ u T) :
    ContinuousWithinAt (H1energy u) (Set.Ici (0 : ℝ)) (0 : ℝ) :=
  H1energy_continuousWithinAt_zero_of_initialTraceEnergy
    hT hinit.tendsto hinit.compatible

/-- Closed-window H¹ energy continuity from `u_xx` L¹ time-continuity plus the
split initial endpoint data. -/
theorem H1energy_continuousOn_before_of_uxxL1Cont_initialTraceEnergy
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hUxxL1 : H1UxxL1ContBefore u T)
    (htend : H1InitialTraceEnergyTendsto u₀ u T)
    (hcompat : H1InitialEnergyCompatibleAtZero u₀ u) :
    ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn (H1energy u) (Set.Icc a b) := by
  have hcont0 : ContinuousWithinAt (H1energy u) (Set.Ici (0 : ℝ)) (0 : ℝ) :=
    H1energy_continuousWithinAt_zero_of_initialTraceEnergy
      (u₀ := u₀) (u := u) (T := T) hsol.1 htend hcompat
  intro a b ha hab hbT
  exact H1energy_continuousOn_before_of_uxxL1Cont hsol hUxxL1 hcont0 ha hab hbT

/-- Bundled endpoint-data version of
`H1energy_continuousOn_before_of_uxxL1Cont_initialTraceEnergy`. -/
theorem H1energy_continuousOn_before_of_uxxL1Cont_initialEndpointData
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hUxxL1 : H1UxxL1ContBefore u T)
    (hinit : H1InitialEndpointData u₀ u T) :
    ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn (H1energy u) (Set.Icc a b) :=
  H1energy_continuousOn_before_of_uxxL1Cont_initialTraceEnergy
    hsol hUxxL1 hinit.tendsto hinit.compatible

#print axioms tendsto_nhdsWithin_Ici_zero_of_tendsto_nhdsWithin_Ioc_zero
#print axioms H1energy_const
#print axioms H1InitialEnergy_const
#print axioms H1InitialTraceEnergyTendsto_const
#print axioms H1InitialEnergyCompatibleAtZero_const
#print axioms H1InitialEndpointData_const
#print axioms H1InitialEndpointData_constOnInterval
#print axioms H1InitialEnergyCompatibleAtZero_of_zeroSlice
#print axioms H1InitialEnergyCompatibleAtZero_of_zeroSlice_pointwise
#print axioms H1energy_continuousWithinAt_zero_of_initialTraceEnergy
#print axioms H1energy_continuousWithinAt_zero_of_initialEndpointData
#print axioms H1energy_continuousOn_before_of_uxxL1Cont_initialTraceEnergy
#print axioms H1energy_continuousOn_before_of_uxxL1Cont_initialEndpointData

end ShenWork.Paper2.IntervalChiNegH1InitialContinuity
