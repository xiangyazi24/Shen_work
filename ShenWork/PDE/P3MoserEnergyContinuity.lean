import ShenWork.PDE.P3MoserIntegratedClosure
import ShenWork.Paper2.IntervalDomainLpTimeLeibniz

/-!
# Energy continuity from classical solution joint continuity

This file proves `ContinuousOn (fun t => intervalDomain.integral (fun x => (u t x) ^ p)) S`
for `S ⊆ Ioo 0 T` from:
- Conjunct (9) of `intervalDomainClassicalRegularity`: joint continuity of
  `(t,x) ↦ intervalDomainLift (u t) x` on `Ioo 0 T ×ˢ Icc 0 1`
- Positivity: `u t x > 0` for interior times

The key Mathlib tool is `intervalIntegral.continuousWithinAt_of_dominated_interval`.
-/

open MeasureTheory Set Filter
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

/-- Extract conjunct (9) from the classical solution: joint continuity of the
solution field on `Ioo 0 T ×ˢ Icc 0 1`. -/
theorem intervalDomain_solution_jointContinuousOn
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    ContinuousOn
      (Function.uncurry (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
  hsol.2.1.2.2.2.2.2.2.1

/-- Joint continuity of `(t,x) ↦ (intervalDomainLift (u t) x) ^ p` on
`Ioo 0 T ×ˢ Icc 0 1` for a positive classical solution. -/
theorem intervalDomain_power_jointContinuousOn
    {params : CM2Params} {T p : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    ContinuousOn
      (fun tx : ℝ × ℝ => (intervalDomainLift (u tx.1) tx.2) ^ p)
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) := by
  have hj := intervalDomain_solution_jointContinuousOn hsol
  have hj' : ContinuousOn
      (fun tx : ℝ × ℝ => intervalDomainLift (u tx.1) tx.2)
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) := hj
  exact ContinuousOn.rpow hj' continuousOn_const
    (fun ⟨t, x⟩ ⟨ht, hx⟩ =>
      Or.inl (ne_of_gt (intervalDomain_solution_lift_u_pos hsol ht.1 ht.2 hx)))

/-- On a compact sub-slab `[a,b] × [0,1] ⊆ (0,T) × [0,1]`, the integrand
`(intervalDomainLift (u t) x) ^ p` is bounded. -/
theorem intervalDomain_power_bounded_on_slab
    {params : CM2Params} {T p a b : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ha : 0 < a) (hb : b < T) (hab : a ≤ b) :
    ∃ C, ∀ t ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖(intervalDomainLift (u t) x) ^ p‖ ≤ C := by
  have hcompact : IsCompact (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hsub : Icc a b ×ˢ Icc (0 : ℝ) 1 ⊆ Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1 :=
    prod_mono (Icc_subset_Ioo ha hb) Subset.rfl
  have hcont := (intervalDomain_power_jointContinuousOn hsol (p := p)).mono hsub
  have hcont_norm : ContinuousOn
      (fun tx : ℝ × ℝ => ‖(intervalDomainLift (u tx.1) tx.2) ^ p‖)
      (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    continuous_norm.comp_continuousOn hcont
  have hne : (Icc a b ×ˢ Icc (0 : ℝ) 1).Nonempty :=
    ⟨⟨a, 0⟩, ⟨le_refl a, hab⟩, ⟨le_refl 0, zero_le_one⟩⟩
  rcases hcompact.exists_isMaxOn hne hcont_norm with ⟨⟨t₀, x₀⟩, _, hmax⟩
  exact ⟨‖(intervalDomainLift (u t₀) x₀) ^ p‖,
    fun t ht x hx => hmax (show (t, x) ∈ Icc a b ×ˢ Icc (0 : ℝ) 1 from ⟨ht, hx⟩)⟩

/-- Energy continuity on the open interior `(0,T)`: the map
`t ↦ ∫₀¹ u(t,x)^p dx` is continuous on `Ioo 0 T` for a positive classical
interval-domain solution.

Uses `intervalIntegral.continuousWithinAt_of_dominated_interval` with the
compact-slab bound from `intervalDomain_power_bounded_on_slab`. -/
theorem intervalDomain_energyContinuousOn_Ioo
    {params : CM2Params} {T p : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    ContinuousOn
      (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
      (Ioo (0 : ℝ) T) := by
  rw [ContinuousOn]
  intro t₀ ht₀
  have hderiv :
      HasDerivAt (fun s => intervalDomainPowerEnergy p u s)
        (∫ y in (0 : ℝ)..1, intervalDomainPowerDeriv p u t₀ y) t₀ :=
    intervalDomainPowerEnergy_hasDerivAt (q := p) hsol ht₀
  have henergy :
      (fun t => intervalDomain.integral (fun x => (u t x) ^ p)) =
        fun t => intervalDomainPowerEnergy p u t := by
    funext t
    unfold intervalDomainPowerEnergy
    change intervalDomainIntegral (fun x => (u t x) ^ p) = _
    unfold intervalDomainIntegral
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    rw [Set.uIcc_of_le (zero_le_one)] at hy
    simp [intervalDomainLift, hy]
  rw [henergy]
  exact hderiv.continuousAt.continuousWithinAt

/-- Endpoint continuity data needed to upgrade the already-proved interior
energy continuity to the closed interval `[0,T]`.

This is honest: `IsPaper2ClassicalSolution` currently controls interior times,
while the closed regularity field also asks about the values at `0` and `T`. -/
structure IntervalDomainPowerEnergyEndpointContinuity
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop where
  atZero :
    ∀ p, p0 ≤ p →
      ContinuousWithinAt
        (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
        (Set.Icc (0 : ℝ) T) 0
  atRight :
    ∀ p, p0 ≤ p →
      ContinuousWithinAt
        (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
        (Set.Icc (0 : ℝ) T) T

/-- Closed-interval energy continuity from the interior classical-solution
continuity theorem plus explicit endpoint continuity data. -/
theorem intervalDomain_energyContinuousOn_Icc_of_classical_endpointContinuity
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hend : IntervalDomainPowerEnergyEndpointContinuity u T p0) :
    ∀ p, p0 ≤ p →
      ContinuousOn
        (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
        (Set.Icc (0 : ℝ) T) := by
  intro p hp
  rw [ContinuousOn]
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    exact hend.atZero p hp
  by_cases htT : t = T
  · subst t
    exact hend.atRight p hp
  have htIoo : t ∈ Set.Ioo (0 : ℝ) T := by
    exact
      ⟨lt_of_le_of_ne ht.1 (fun h => ht0 h.symm),
       lt_of_le_of_ne ht.2 htT⟩
  have hcontWithin :
      ContinuousWithinAt
        (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
        (Set.Ioo (0 : ℝ) T) t :=
    intervalDomain_energyContinuousOn_Ioo (p := p) hsol t htIoo
  exact
    (hcontWithin.continuousAt (isOpen_Ioo.mem_nhds htIoo)).continuousWithinAt

/-- Endpoint power-energy continuity from a left-endpoint residual and a global
classical solution.

The right endpoint `T` is an interior time for the longer horizon `T + 1`, so
its continuity follows from `intervalDomain_energyContinuousOn_Ioo`.  The left
endpoint remains an explicit residual because the current classical-solution
record is an interior-time regularity statement. -/
theorem intervalDomain_powerEnergyEndpointContinuity_of_atZero_and_global_classical
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (hzero :
      ∀ p, p0 ≤ p →
        ContinuousWithinAt
          (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
          (Set.Icc (0 : ℝ) T) 0) :
    IntervalDomainPowerEnergyEndpointContinuity u T p0 := by
  refine ⟨hzero, ?_⟩
  intro p hp
  have hTplus : 0 < T + 1 := by
    linarith
  have hsolLong :
      IsPaper2ClassicalSolution intervalDomain params (T + 1) u v :=
    hglobal.classical hTplus
  have hIoo :
      ContinuousOn
        (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
        (Set.Ioo (0 : ℝ) (T + 1)) :=
    intervalDomain_energyContinuousOn_Ioo (p := p) hsolLong
  have hTmem : T ∈ Set.Ioo (0 : ℝ) (T + 1) := by
    exact ⟨hT, by linarith⟩
  have hcontAt :
      ContinuousAt
        (fun t => intervalDomain.integral (fun x => (u t x) ^ p)) T :=
    hIoo.continuousAt (isOpen_Ioo.mem_nhds hTmem)
  exact hcontAt.continuousWithinAt

#print axioms intervalDomain_solution_jointContinuousOn
#print axioms intervalDomain_power_jointContinuousOn
#print axioms intervalDomain_power_bounded_on_slab
#print axioms intervalDomain_energyContinuousOn_Ioo
#print axioms intervalDomain_energyContinuousOn_Icc_of_classical_endpointContinuity
#print axioms
  intervalDomain_powerEnergyEndpointContinuity_of_atZero_and_global_classical

end ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

end
