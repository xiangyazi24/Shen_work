import ShenWork.PDE.P3MoserRegularityProducer
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
open ShenWork.IntervalDomainExistence.P3MoserRegularityProducer
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

#print axioms intervalDomain_solution_jointContinuousOn
#print axioms intervalDomain_power_jointContinuousOn
#print axioms intervalDomain_power_bounded_on_slab
#print axioms intervalDomain_energyContinuousOn_Ioo

end ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

end
