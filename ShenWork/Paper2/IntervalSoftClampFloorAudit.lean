import ShenWork.Paper2.IntervalChiNegConcreteConnectors
import ShenWork.PDE.IntervalTimeSoftClamp

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalTimeSoftClamp (φ φ_mem_range)
open ShenWork.Paper2.ParabolicGainInduction
open ShenWork.Paper2.ChiNegConcreteConnectors

noncomputable section

namespace ShenWork.Paper2.SoftClampFloorAudit

theorem clamped_time_mem_window
    {c' c d d' τ ρ : ℝ} (hc' : c' < c) (hcd : c ≤ d)
    (hd' : d < d') :
    φ c' c d d' (τ + ρ) ∈ Set.Icc c' d' :=
  φ_mem_range hc' hcd hd' (τ + ρ)

theorem exists_uniform_profile_floor_on_time_window
    {w : ℝ → intervalDomainPoint → ℝ} {lo hi : ℝ} (hlohi : lo ≤ hi)
    (hjoint : ContinuousOn
      (Function.uncurry (fun s x => intervalDomainLift (w s) x))
      (Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1))
    (hpos : ∀ s ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (w s) x) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ s ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
        δ ≤ intervalDomainLift (w s) x := by
  classical
  set K : Set (ℝ × ℝ) := Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1 with hK
  have hKcompact : IsCompact K := by
    rw [hK]
    exact isCompact_Icc.prod isCompact_Icc
  have hKne : K.Nonempty := by
    refine ⟨(lo, 0), ?_⟩
    rw [hK]
    exact Set.mem_prod.mpr
      ⟨Set.left_mem_Icc.mpr hlohi, by constructor <;> norm_num⟩
  obtain ⟨q₀, hq₀_mem, hq₀_min⟩ :=
    hKcompact.exists_isMinOn hKne (by simpa [hK] using hjoint)
  obtain ⟨s₀, x₀⟩ := q₀
  have hqprod :
      (s₀, x₀) ∈ Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1 := by
    simpa [hK] using hq₀_mem
  obtain ⟨hs₀, hx₀⟩ := Set.mem_prod.mp hqprod
  refine ⟨intervalDomainLift (w s₀) x₀, hpos s₀ hs₀ x₀ hx₀, ?_⟩
  intro s hs x hx
  have hmem : (s, x) ∈ K := by
    rw [hK]
    exact Set.mem_prod.mpr ⟨hs, hx⟩
  exact isMinOn_iff.mp hq₀_min (s, x) hmem

theorem intervalLogisticSource_spatialSlice_lower_of_positive
    {p : CM2Params} {u : intervalDomainPoint → ℝ} {k : ℕ}
    (hu : SpatialSlice k u)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift u x) :
    SpatialSlice (k - 1)
      (ShenWork.IntervalDomainExistence.intervalLogisticSource p u) :=
  intervalLogisticSource_spatialSlice_lower_of_nonzero
    (p := p) (u := u) (k := k) hu
    (fun x hx => ne_of_gt (hpos x hx))

theorem concreteChemDivLosesOneAtom_of_component_atoms_positive
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hchem : ∀ k, 2 ≤ k → k < 6 →
      CoupledSlice k ((concreteU u) k) ((concreteV p u) k) →
        SpatialSlice (k - 1)
          (ShenWork.IntervalDomain.intervalDomainChemotaxisDiv p
            ((concreteU u) k) ((concreteV p u) k)))
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift u x) :
    ConcreteChemDivLosesOneAtom p u := by
  intro k hk2 hk6 hcoupled
  exact intervalCoupledSource_spatialSlice_of_components
    (hchem k hk2 hk6 hcoupled)
    (intervalLogisticSource_spatialSlice_lower_of_positive
      (p := p) (u := (concreteU u) k) (k := k) hcoupled.1
      (by intro x hx; simpa [concreteU] using hpos x hx))

theorem concreteChemDivLosesOneAtomC7_of_component_atoms_positive
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hchem : ∀ k, 2 ≤ k → k < 7 →
      CoupledSlice k ((concreteU u) k) ((concreteV p u) k) →
        SpatialSlice (k - 1)
          (ShenWork.IntervalDomain.intervalDomainChemotaxisDiv p
            ((concreteU u) k) ((concreteV p u) k)))
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift u x) :
    ConcreteChemDivLosesOneAtomC7 p u := by
  intro k hk2 hk7 hcoupled
  exact intervalCoupledSource_spatialSlice_of_components
    (hchem k hk2 hk7 hcoupled)
    (intervalLogisticSource_spatialSlice_lower_of_positive
      (p := p) (u := (concreteU u) k) (k := k) hcoupled.1
      (by intro x hx; simpa [concreteU] using hpos x hx))

#print axioms clamped_time_mem_window
#print axioms exists_uniform_profile_floor_on_time_window
#print axioms intervalLogisticSource_spatialSlice_lower_of_positive
#print axioms concreteChemDivLosesOneAtom_of_component_atoms_positive
#print axioms concreteChemDivLosesOneAtomC7_of_component_atoms_positive
end ShenWork.Paper2.SoftClampFloorAudit
