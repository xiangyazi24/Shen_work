import ShenWork.PDE.P3MoserBoundedBeforeProducer
import ShenWork.PDE.P3MoserContinuityExtension

/-!
# Subinterval assembly bridge from the integrated Moser ladder

This file wires the subinterval assembly residual to the existing integrated
Moser first-crossing step and quantitative endpoint suppliers.

The existing Moser endpoint closes `IsPaper2BoundedBefore`, hence controls the
strict positive-time interval `0 < t < τ`.  The closed subinterval residual also
asks for the right endpoint `t = τ`; that endpoint is therefore carried as an
explicit supplier below.
-/

open Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDomainExistence.P3MoserBoundedBeforeProducer
open ShenWork.IntervalDomainExistence.P3MoserFirstCrossingContinuation
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open ShenWork.IntervalDomainExistence.P3MoserIntegratedDissipationPDEv2

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserSubintervalAssemblyBridge

/-- For the concrete interval domain, bounded absolute-value range makes the
concrete `supNorm` control pointwise absolute values. -/
theorem intervalDomain_abs_le_supNorm_of_bddAbove_abs
    {f : intervalDomain.Point → ℝ}
    (hbdd : BddAbove (Set.range (fun x : intervalDomain.Point => |f x|)))
    (x : intervalDomain.Point) :
    |f x| ≤ intervalDomain.supNorm f := by
  change |f x| ≤ intervalDomainSupNorm f
  unfold intervalDomainSupNorm
  exact le_csSup hbdd ⟨x, rfl⟩

/-- The Moser ladder suppliers give a uniform pointwise bound on the strict
positive-time subinterval `0 < t < τ`. -/
theorem intervalDomain_subinterval_strict_pointwise_bound_of_step_and_endpoint
    {p : CM2Params}
    (hstep :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
        LpBootstrapEnergyInequalityWithGap intervalDomain u T rho p0 →
          IntegratedMoserFirstCrossingStep intervalDomain u T rho p0)
    (hEndpoint :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
          ∃ pSeq rootBound : ℕ → ℝ,
            (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
              IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound)
    {T τ rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hsub : BoundedBeforeOnSubinterval intervalDomain u τ T)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain p τ rho u v)
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) τ rho p0)
    (hgap : LpBootstrapEnergyInequalityWithGap intervalDomain u τ rho p0) :
    ∃ M, ∀ t, 0 < t → t < τ → ∀ x : intervalDomain.Point, |u t x| ≤ M := by
  have hτ_pos : 0 < τ := AbstractLpBootstrapHypothesis.T_pos hboot
  have hsolτ : IsPaper2ClassicalSolution intervalDomain p τ u v :=
    isPaper2ClassicalSolution_intervalDomain_mono
      (p := p) (Tshort := τ) (Tlong := T) (u := u) (v := v)
      hτ_pos hsub.1 hsol
  have hstepτ : IntegratedMoserFirstCrossingStep intervalDomain u τ rho p0 :=
    hstep hsolτ hcross hboot hgap
  rcases hEndpoint hsolτ hcross hboot with
    ⟨pSeq, rootBound, hQuantEndpoint⟩
  have hbounded : IsPaper2BoundedBefore intervalDomain τ u :=
    intervalDomain_hBoundedBefore_of_integrated_step_and_endpoint
      hsolτ hcross hboot hstepτ hQuantEndpoint
  rcases hbounded with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro t ht0 htτ x
  have hbdd :
      BddAbove (Set.range (fun x : intervalDomain.Point => |u t x|)) :=
    intervalDomain_solution_slice_abs_bddAbove hsolτ
      (show t ∈ Set.Ioo (0 : ℝ) τ from ⟨ht0, htτ⟩)
  exact (intervalDomain_abs_le_supNorm_of_bddAbove_abs hbdd x).trans
    (hM t ht0 htτ)

/-- Closed-subinterval assembly from the Moser ladder suppliers, initial
boundedness, and an explicit right-endpoint boundedness supplier.

The extra endpoint supplier is the current minimal residual: the existing
`IsPaper2BoundedBefore`/Moser endpoint APIs only cover `0 < t < τ`, while
`SubintervalAssemblyResidual` asks for `t = τ` as well. -/
theorem intervalDomain_subintervalAssemblyResidual_of_step_endpoint_initial_and_terminal
    {p : CM2Params}
    (hstep :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
        LpBootstrapEnergyInequalityWithGap intervalDomain u T rho p0 →
          IntegratedMoserFirstCrossingStep intervalDomain u T rho p0)
    (hEndpoint :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
          ∃ pSeq rootBound : ℕ → ℝ,
            (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
              IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound)
    (hInitial :
      ∀ {T : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
          ∃ M₀, ∀ x, |u 0 x| ≤ M₀)
    (hTerminal :
      ∀ {T τ : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        BoundedBeforeOnSubinterval intervalDomain u τ T →
        0 < τ →
          ∃ Mτ, ∀ x, |u τ x| ≤ Mτ) :
    SubintervalAssemblyResidual intervalDomain p := by
  intro T τ rho p0 u v hsol hsub hcross hboot hgap
  have hτ_pos : 0 < τ := AbstractLpBootstrapHypothesis.T_pos hboot
  rcases intervalDomain_subinterval_strict_pointwise_bound_of_step_and_endpoint
      (p := p) hstep hEndpoint hsol hsub hcross hboot hgap with
    ⟨Mopen, hMopen⟩
  rcases hInitial hsol with ⟨M₀, hM₀⟩
  rcases hTerminal hsol hsub hτ_pos with ⟨Mτ, hMτ⟩
  refine ⟨max (max Mopen M₀) Mτ, ?_⟩
  intro t ht x
  by_cases ht_zero : t = 0
  · subst t
    exact (hM₀ x).trans
      (le_trans (le_max_right Mopen M₀) (le_max_left (max Mopen M₀) Mτ))
  · have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht_zero)
    by_cases ht_terminal : t = τ
    · subst t
      exact (hMτ x).trans (le_max_right (max Mopen M₀) Mτ)
    · have ht_lt : t < τ := lt_of_le_of_ne ht.2 ht_terminal
      exact (hMopen t ht_pos ht_lt x).trans
        (le_trans (le_max_left Mopen M₀) (le_max_left (max Mopen M₀) Mτ))

#print axioms intervalDomain_abs_le_supNorm_of_bddAbove_abs
#print axioms intervalDomain_subinterval_strict_pointwise_bound_of_step_and_endpoint
#print axioms intervalDomain_subintervalAssemblyResidual_of_step_endpoint_initial_and_terminal

end ShenWork.IntervalDomainExistence.P3MoserSubintervalAssemblyBridge

end
