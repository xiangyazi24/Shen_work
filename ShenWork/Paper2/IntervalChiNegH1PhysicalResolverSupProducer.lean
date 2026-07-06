import ShenWork.Paper2.IntervalChiNegH1PhysicalChemSqrtBounds
import ShenWork.Paper2.IntervalDomainResolverSupQuantitative
import ShenWork.PDE.IntervalResolverSpatialC2

/-!
# Source producers for physical H¹ chem resolver sup data

This file lowers a smaller source-facing residual to the resolver/core package
used by the physical H¹ sqrt route.  It does not produce uniform before-`T`
constants from classical regularity alone.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.PDE
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1PhysicalRHSScalars
open ShenWork.Paper2.IntervalChiNegH1PhysicalChemSqrtBounds

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1PhysicalResolverSupProducer

/-- Quantitative resolver-gradient cap obtained from a fixed pointwise upper
bound on `u`. -/
abbrev H1PhysicalChemResolverGradCap (p : CM2Params) (M : ℝ) : ℝ :=
  Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
    (2 * (p.ν * M ^ p.γ))

private theorem H1PhysicalChemResolverGradCap_nonneg
    (p : CM2Params) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ H1PhysicalChemResolverGradCap p M := by
  unfold H1PhysicalChemResolverGradCap
  exact
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (mul_nonneg p.hν.le (Real.rpow_nonneg hM p.γ)))

/-- Quantitative resolver-value cap obtained from a fixed pointwise upper bound
on `u`. -/
abbrev H1PhysicalChemResolverValueCap (p : CM2Params) (M : ℝ) : ℝ :=
  Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) *
    (2 * (p.ν * M ^ p.γ))

private theorem H1PhysicalChemResolverValueCap_nonneg
    (p : CM2Params) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ H1PhysicalChemResolverValueCap p M := by
  unfold H1PhysicalChemResolverValueCap
  exact
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (mul_nonneg p.hν.le (Real.rpow_nonneg hM p.γ)))

/-- Smaller source-facing residual for the physical H¹ chem route: a fixed
before-`T` pointwise upper bound on `u`, plus the remaining exact uvxx-core
bound.  The resolver-gradient bound is produced quantitatively from the `u`
upper bound. -/
structure H1PhysicalChemUpperCoreBoundsBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ)
    (T M V₂ : ℝ) : Prop where
  hM : 0 ≤ M
  hV2 : 0 ≤ V₂
  u_le : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    ∀ x, x ∈ Set.Icc (0 : ℝ) 1 →
      intervalDomainLift (u τ) x ≤ M
  uvxx_core_le : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    ∀ x, x ∈ Set.Icc (0 : ℝ) 1 →
      |(p.μ * intervalDomainLift (v τ) x -
          p.ν * (intervalDomainLift (u τ) x) ^ p.γ) /
          (1 + intervalDomainLift (v τ) x) ^ p.β -
        p.β * (deriv (intervalDomainLift (v τ)) x) ^ 2 /
          (1 + intervalDomainLift (v τ) x) ^ (p.β + 1)| ≤ V₂

/-- For a classical interval solution, the concrete sup norm controls the
closed-interval lift pointwise. -/
theorem intervalDomainLift_le_supNorm_of_classical
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ x : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalDomainLift (u τ) x ≤ intervalDomain.supNorm (u τ) := by
  have hbdd :
      BddAbove (Set.range (fun y : intervalDomainPoint => |u τ y|)) :=
    ShenWork.Paper2.classicalSolution_u_range_bddAbove hsol hτ
  have habs :
      |u τ (⟨x, hx⟩ : intervalDomainPoint)| ≤ intervalDomain.supNorm (u τ) := by
    change
      |u τ (⟨x, hx⟩ : intervalDomainPoint)| ≤
        intervalDomainSupNorm (u τ)
    unfold intervalDomainSupNorm
    exact le_csSup hbdd ⟨(⟨x, hx⟩ : intervalDomainPoint), rfl⟩
  have hlift :
      intervalDomainLift (u τ) x = u τ (⟨x, hx⟩ : intervalDomainPoint) := by
    simp [intervalDomainLift, hx]
  rw [hlift]
  exact (le_abs_self _).trans habs

/-- The unconditional interior elliptic characterization extends to the closed
interval by continuity of the resolver series and of the clamped lift
representative of `v`. -/
theorem solution_v_eq_resolver_pointwise_Icc
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ x : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalNeumannResolverR p (u τ) (⟨x, hx⟩ : intervalDomainPoint) =
      intervalDomainLift (v τ) x := by
  classical
  set R : ℝ → ℝ := fun y : ℝ =>
    ∑' k : ℕ, (intervalNeumannResolverCoeff p (u τ) k).re *
      ShenWork.CosineSpectrum.cosineMode k y
    with hRdef
  set V : ℝ → ℝ := liftRepr (v τ) with hVdef
  have hRcont : Continuous R := by
    have hdecay := sourceCoeffQuadraticDecay_of_solution hsol hτ
    simpa [R] using
      (ShenWork.IntervalResolverSpatialC2.resolverR_contDiff_two
        (p := p) (u := u τ) hdecay).continuous
  have hVcont : Continuous V := by
    have hcontV : ContinuousOn (intervalDomainLift (v τ)) (Set.Icc (0 : ℝ) 1) :=
      ((hsol.regularity.2.2.2.2.1 τ hτ).2.1).continuousOn
    simpa [V] using liftRepr_continuous hcontV
  have heq : Set.EqOn R V (Set.Ioo (0 : ℝ) 1) := by
    intro y hy
    have hrv :=
      solution_v_eq_resolver_pointwise_unconditional
        (p := p) (T := T) (u := u) (v := v) hsol hτ hy
    have hR_apply :
        intervalNeumannResolverR p (u τ)
            (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint) = R y := by
      simpa [R] using
        (ShenWork.IntervalResolverSpatialC2.resolverR_eq_cosineSeries
          (p := p) (u := u τ)
          (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint))
    have hV_apply : V y = intervalDomainLift (v τ) y := by
      simpa [V] using liftRepr_eq_on_Icc (Set.Ioo_subset_Icc_self hy)
    exact hR_apply.symm.trans (hrv.trans hV_apply.symm)
  have hclos := heq.closure hRcont hVcont
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at hclos
  have hR_apply :
      intervalNeumannResolverR p (u τ) (⟨x, hx⟩ : intervalDomainPoint) = R x := by
    simpa [R] using
      (ShenWork.IntervalResolverSpatialC2.resolverR_eq_cosineSeries
        (p := p) (u := u τ) (⟨x, hx⟩ : intervalDomainPoint))
  have hV_apply : V x = intervalDomainLift (v τ) x := by
    simpa [V] using liftRepr_eq_on_Icc hx
  exact hR_apply.symm.trans ((hclos hx).trans hV_apply)

/-- A finite-horizon sup-norm bound, together with the exact uvxx-core source
bound, produces the smaller upper/core source package.  The sup-norm constant
is replaced by `max M 0` so the downstream quantitative resolver theorem has a
nonnegative upper constant. -/
theorem H1PhysicalChemUpperCoreBoundsBefore_of_boundedBefore_core
    {p : CM2Params} {T V₂ : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hbounded : IsPaper2BoundedBefore intervalDomain T u)
    (hV2 : 0 ≤ V₂)
    (hcore : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      ∀ x, x ∈ Set.Icc (0 : ℝ) 1 →
        |(p.μ * intervalDomainLift (v τ) x -
            p.ν * (intervalDomainLift (u τ) x) ^ p.γ) /
            (1 + intervalDomainLift (v τ) x) ^ p.β -
          p.β * (deriv (intervalDomainLift (v τ)) x) ^ 2 /
            (1 + intervalDomainLift (v τ) x) ^ (p.β + 1)| ≤ V₂) :
    ∃ M, H1PhysicalChemUpperCoreBoundsBefore p u v T M V₂ := by
  rcases hbounded with ⟨M₀, hM₀⟩
  refine ⟨max M₀ 0, ?_⟩
  refine
    { hM := le_max_right M₀ 0
      hV2 := hV2
      u_le := ?_
      uvxx_core_le := hcore }
  intro τ hτ x hx
  have hpoint :
      intervalDomainLift (u τ) x ≤ intervalDomain.supNorm (u τ) :=
    intervalDomainLift_le_supNorm_of_classical
      (p := p) (T := T) (u := u) (v := v) hsol hτ hx
  have hsup : intervalDomain.supNorm (u τ) ≤ M₀ :=
    hM₀ τ hτ.1 hτ.2
  exact (hpoint.trans hsup).trans (le_max_left M₀ 0)

/-- A finite-horizon sup-norm bound for a classical solution gives uniform
before-`T` bounds on `u`, `v = R(u)`, and the resolver gradient. -/
theorem H1PhysicalChemValueGradSupBefore_of_boundedBefore
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hbounded : IsPaper2BoundedBefore intervalDomain T u) :
    ∃ M, H1PhysicalChemValueGradSupBefore p u v T M
      (H1PhysicalChemResolverValueCap p M)
      (H1PhysicalChemResolverGradCap p M) := by
  rcases hbounded with ⟨M₀, hM₀⟩
  let M : ℝ := max M₀ 0
  refine ⟨M, ?_⟩
  have hM_nonneg : 0 ≤ M := le_max_right M₀ 0
  refine
    { hM := hM_nonneg
      hV := H1PhysicalChemResolverValueCap_nonneg p hM_nonneg
      hG := H1PhysicalChemResolverGradCap_nonneg p hM_nonneg
      u_nonneg_le := ?_
      v_abs_le := ?_
      resolver_grad_le := ?_ }
  · intro τ hτ x hx
    have hnonneg : 0 ≤ intervalDomainLift (u τ) x :=
      (solution_lift_pos
        (p := p) (T := T) (u := u) (v := v) hsol hτ x hx).le
    have hpoint :
        intervalDomainLift (u τ) x ≤ intervalDomain.supNorm (u τ) :=
      intervalDomainLift_le_supNorm_of_classical
        (p := p) (T := T) (u := u) (v := v) hsol hτ hx
    have hsup : intervalDomain.supNorm (u τ) ≤ M₀ :=
      hM₀ τ hτ.1 hτ.2
    exact ⟨hnonneg, (hpoint.trans hsup).trans (le_max_left M₀ 0)⟩
  · intro τ hτ x hx
    have hub : ∀ y, y ∈ Set.Icc (0 : ℝ) 1 →
        intervalDomainLift (u τ) y ≤ M := by
      intro y hy
      have hpoint :
          intervalDomainLift (u τ) y ≤ intervalDomain.supNorm (u τ) :=
        intervalDomainLift_le_supNorm_of_classical
          (p := p) (T := T) (u := u) (v := v) hsol hτ hy
      have hsup : intervalDomain.supNorm (u τ) ≤ M₀ :=
        hM₀ τ hτ.1 hτ.2
      exact (hpoint.trans hsup).trans (le_max_left M₀ 0)
    have hv_eq :=
      solution_v_eq_resolver_pointwise_Icc
        (p := p) (T := T) (u := u) (v := v) hsol hτ hx
    rw [← hv_eq]
    simpa [H1PhysicalChemResolverValueCap] using
      resolverValue_sup_le_of_ub
        (p := p) (T := T) (u := u) (v := v)
        hsol (τ := τ) (M := M) hτ hub
        (⟨x, hx⟩ : intervalDomainPoint)
  · intro τ hτ x hx
    have hub : ∀ y, y ∈ Set.Icc (0 : ℝ) 1 →
        intervalDomainLift (u τ) y ≤ M := by
      intro y hy
      have hpoint :
          intervalDomainLift (u τ) y ≤ intervalDomain.supNorm (u τ) :=
        intervalDomainLift_le_supNorm_of_classical
          (p := p) (T := T) (u := u) (v := v) hsol hτ hy
      have hsup : intervalDomain.supNorm (u τ) ≤ M₀ :=
        hM₀ τ hτ.1 hτ.2
      exact (hpoint.trans hsup).trans (le_max_left M₀ 0)
    simpa [H1PhysicalChemResolverGradCap] using
      resolverGrad_sup_le_of_ub
        (p := p) (T := T) (u := u) (v := v)
        hsol (τ := τ) (M := M) hτ hub (x := x) hx

/-- Uniform pointwise upper control of `u` plus the exact uvxx-core source bound
produces the resolver/core package used by the physical H¹ sqrt route. -/
theorem H1PhysicalChemResolverSupBefore_of_upperCore
    {p : CM2Params} {T M V₂ : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (h : H1PhysicalChemUpperCoreBoundsBefore p u v T M V₂) :
    H1PhysicalChemResolverSupBefore p u v T
      (H1PhysicalChemResolverGradCap p M) V₂ M := by
  refine
    { hV1 := H1PhysicalChemResolverGradCap_nonneg p h.hM
      hV2 := h.hV2
      hM := h.hM
      u_abs_le := ?_
      resolver_grad_le := ?_
      uvxx_core_le := h.uvxx_core_le }
  · intro τ hτ x hx
    have hpos : 0 < intervalDomainLift (u τ) x :=
      solution_lift_pos
        (p := p) (T := T) (u := u) (v := v) hsol hτ x hx
    rw [abs_of_pos hpos]
    exact h.u_le τ hτ x hx
  · intro τ hτ x hx
    simpa [H1PhysicalChemResolverGradCap] using
      resolverGrad_sup_le_of_ub
        (p := p) (T := T) (u := u) (v := v)
        hsol (τ := τ) (M := M) hτ (h.u_le τ hτ) (x := x) hx

/-- Direct full physical H¹ sqrt wrapper from the smaller source-facing
upper/core package. -/
theorem H1PhysicalRHSSqrtBoundsBefore_of_classical_upperCore
    {p : CM2Params} {T M V₂ L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hchi : 0 ≤ -p.χ₀)
    (hL : p.a ≤ L)
    (h : H1PhysicalChemUpperCoreBoundsBefore p u v T M V₂) :
    H1PhysicalRHSSqrtBoundsBefore p u v T
      (H1PhysicalChemResolverGradCap p M) V₂ M L :=
  H1PhysicalRHSSqrtBoundsBefore_of_classical_resolverSup
    (p := p) (T := T)
    (V₁ := H1PhysicalChemResolverGradCap p M) (V₂ := V₂)
    (M := M) (L := L) (u := u) (v := v) hsol hchi hL
    (H1PhysicalChemResolverSupBefore_of_upperCore
      (p := p) (T := T) (M := M) (V₂ := V₂)
      (u := u) (v := v) hsol h)

/-- Direct resolver/core producer from a finite-horizon sup-norm bound and the
remaining exact uvxx-core source bound. -/
theorem H1PhysicalChemResolverSupBefore_of_boundedBefore_core
    {p : CM2Params} {T V₂ : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hbounded : IsPaper2BoundedBefore intervalDomain T u)
    (hV2 : 0 ≤ V₂)
    (hcore : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      ∀ x, x ∈ Set.Icc (0 : ℝ) 1 →
        |(p.μ * intervalDomainLift (v τ) x -
            p.ν * (intervalDomainLift (u τ) x) ^ p.γ) /
            (1 + intervalDomainLift (v τ) x) ^ p.β -
          p.β * (deriv (intervalDomainLift (v τ)) x) ^ 2 /
            (1 + intervalDomainLift (v τ) x) ^ (p.β + 1)| ≤ V₂) :
    ∃ M, H1PhysicalChemResolverSupBefore p u v T
      (H1PhysicalChemResolverGradCap p M) V₂ M := by
  rcases
    H1PhysicalChemUpperCoreBoundsBefore_of_boundedBefore_core
      (p := p) (T := T) (V₂ := V₂) (u := u) (v := v)
      hsol hbounded hV2 hcore with
    ⟨M, hupper⟩
  exact ⟨M, H1PhysicalChemResolverSupBefore_of_upperCore
    (p := p) (T := T) (M := M) (V₂ := V₂)
    (u := u) (v := v) hsol hupper⟩

/-- Direct full physical H¹ sqrt wrapper from a finite-horizon sup-norm bound
and the remaining exact uvxx-core source bound. -/
theorem H1PhysicalRHSSqrtBoundsBefore_of_classical_boundedBefore_core
    {p : CM2Params} {T V₂ L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hchi : 0 ≤ -p.χ₀)
    (hL : p.a ≤ L)
    (hbounded : IsPaper2BoundedBefore intervalDomain T u)
    (hV2 : 0 ≤ V₂)
    (hcore : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      ∀ x, x ∈ Set.Icc (0 : ℝ) 1 →
        |(p.μ * intervalDomainLift (v τ) x -
            p.ν * (intervalDomainLift (u τ) x) ^ p.γ) /
            (1 + intervalDomainLift (v τ) x) ^ p.β -
          p.β * (deriv (intervalDomainLift (v τ)) x) ^ 2 /
            (1 + intervalDomainLift (v τ) x) ^ (p.β + 1)| ≤ V₂) :
    ∃ M, H1PhysicalRHSSqrtBoundsBefore p u v T
      (H1PhysicalChemResolverGradCap p M) V₂ M L := by
  rcases
    H1PhysicalChemUpperCoreBoundsBefore_of_boundedBefore_core
      (p := p) (T := T) (V₂ := V₂) (u := u) (v := v)
      hsol hbounded hV2 hcore with
    ⟨M, hupper⟩
  exact ⟨M, H1PhysicalRHSSqrtBoundsBefore_of_classical_upperCore
    (p := p) (T := T) (M := M) (V₂ := V₂) (L := L)
    (u := u) (v := v) hsol hchi hL hupper⟩

/-- Direct resolver/core producer from a finite-horizon sup-norm bound.  The
uvxx-core constant is generated from the value and gradient caps, so this no
longer carries the exact-core source residual. -/
theorem H1PhysicalChemResolverSupBefore_of_boundedBefore_valueGrad
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hbounded : IsPaper2BoundedBefore intervalDomain T u) :
    ∃ M, H1PhysicalChemResolverSupBefore p u v T
      (H1PhysicalChemResolverGradCap p M)
      (H1PhysicalChemUvxxCoreSupConstant p M
        (H1PhysicalChemResolverValueCap p M)
        (H1PhysicalChemResolverGradCap p M))
      M := by
  rcases
    H1PhysicalChemValueGradSupBefore_of_boundedBefore
      (p := p) (T := T) (u := u) (v := v) hsol hbounded with
    ⟨M, hVG⟩
  exact
    ⟨M,
      H1PhysicalChemResolverSupBefore_of_valueGradSup
        (p := p) (T := T) (M := M)
        (V := H1PhysicalChemResolverValueCap p M)
        (G := H1PhysicalChemResolverGradCap p M)
        (u := u) (v := v) hsol hVG⟩

/-- Direct full physical H¹ sqrt wrapper from a finite-horizon sup-norm bound.
The chem core constant is the algebraic value/gradient cap. -/
theorem H1PhysicalRHSSqrtBoundsBefore_of_classical_boundedBefore_valueGrad
    {p : CM2Params} {T L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hchi : 0 ≤ -p.χ₀)
    (hL : p.a ≤ L)
    (hbounded : IsPaper2BoundedBefore intervalDomain T u) :
    ∃ M, H1PhysicalRHSSqrtBoundsBefore p u v T
      (H1PhysicalChemResolverGradCap p M)
      (H1PhysicalChemUvxxCoreSupConstant p M
        (H1PhysicalChemResolverValueCap p M)
        (H1PhysicalChemResolverGradCap p M))
      M L := by
  rcases
    H1PhysicalChemResolverSupBefore_of_boundedBefore_valueGrad
      (p := p) (T := T) (u := u) (v := v) hsol hbounded with
    ⟨M, hres⟩
  exact
    ⟨M,
      H1PhysicalRHSSqrtBoundsBefore_of_classical_resolverSup
        (p := p) (T := T)
        (V₁ := H1PhysicalChemResolverGradCap p M)
        (V₂ := H1PhysicalChemUvxxCoreSupConstant p M
          (H1PhysicalChemResolverValueCap p M)
          (H1PhysicalChemResolverGradCap p M))
        (M := M) (L := L) (u := u) (v := v)
        hsol hchi hL hres⟩

#print axioms H1PhysicalChemResolverSupBefore_of_upperCore
#print axioms H1PhysicalRHSSqrtBoundsBefore_of_classical_upperCore
#print axioms intervalDomainLift_le_supNorm_of_classical
#print axioms solution_v_eq_resolver_pointwise_Icc
#print axioms H1PhysicalChemValueGradSupBefore_of_boundedBefore
#print axioms H1PhysicalChemUpperCoreBoundsBefore_of_boundedBefore_core
#print axioms H1PhysicalChemResolverSupBefore_of_boundedBefore_core
#print axioms H1PhysicalRHSSqrtBoundsBefore_of_classical_boundedBefore_core
#print axioms H1PhysicalChemResolverSupBefore_of_boundedBefore_valueGrad
#print axioms H1PhysicalRHSSqrtBoundsBefore_of_classical_boundedBefore_valueGrad

end ShenWork.Paper2.IntervalChiNegH1PhysicalResolverSupProducer
