import ShenWork.PDE.IntervalDomain
import ShenWork.Paper2.Statements
import ShenWork.PDE.P3MoserIntegratedClosure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.TietzeExtension

open ShenWork.IntervalDomain
open ShenWork.Paper2
open MeasureTheory
open scoped Topology

noncomputable section

/-!
# Spatial derivative continuity inputs for the interval-domain P3 Moser route

This file records the PDE reductions needed for proving joint continuity of
`∂ₓ v` and `∂ₓ u` on `(0,T) × [0,1]`.

The remaining analytic frontier is the closed-slab variable-upper-limit
primitive theorem for a function known only as `ContinuousOn` on
`Ioo 0 T ×ˢ Icc 0 1`, together with the endpoint transfer from the interior
PDE identity.  No theorem below assumes that frontier.
-/

/-- A Tietze-extension wrapper for real-valued functions that are continuous on
a closed rectangle. -/
lemma exists_continuous_extension_of_continuousOn_Icc_prod
    {f : ℝ × ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)) :
    ∃ g : C(ℝ × ℝ, ℝ),
      ∀ z ∈ (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1), g z = f z := by
  let K : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1
  have hKclosed : IsClosed K := isClosed_Icc.prod isClosed_Icc
  let fK : C(K, ℝ) := ⟨fun z : K => f z, by
    exact hf.comp_continuous continuous_subtype_val (fun z => z.2)⟩
  rcases ContinuousMap.exists_restrict_eq (s := K) hKclosed fK with ⟨g, hg⟩
  refine ⟨g, ?_⟩
  intro z hz
  exact congrArg (fun H : C(K, ℝ) => H ⟨z, hz⟩) hg

/-- Closed-spatial-slab parametric primitive continuity from slab
`ContinuousOn`.

This is the local replacement for Mathlib's global
`intervalIntegral.continuous_parametric_primitive_of_continuous`: around each
`(t₀,x₀) ∈ (0,T) × [0,1]`, extend the integrand from a closed time rectangle
`[a,b] × [0,1]` to a globally continuous function by Tietze, then use the
global primitive theorem. -/
lemma continuousOn_parametric_primitive_of_continuousOn_Ioo_Icc
    {T : ℝ} {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn
      (fun z : ℝ × ℝ => ∫ s in (0 : ℝ)..z.2, f (z.1, s))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
  intro z hz
  rcases z with ⟨t0, x0⟩
  rcases hz with ⟨ht0, hx0⟩
  rcases exists_between ht0.1 with ⟨a, h0a, hat0⟩
  rcases exists_between ht0.2 with ⟨b, ht0b, hbT⟩
  let K : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1
  have hKsub : K ⊆ Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1 := by
    intro y hy
    exact ⟨⟨lt_of_lt_of_le h0a hy.1.1, lt_of_le_of_lt hy.1.2 hbT⟩, hy.2⟩
  have hfK : ContinuousOn f K := hf.mono hKsub
  rcases exists_continuous_extension_of_continuousOn_Icc_prod
      (a := a) (b := b) hfK with ⟨g, hg⟩
  let F : ℝ → ℝ → ℝ := fun t x => g (t, x)
  have hFcont : Continuous (Function.uncurry F) := by
    simpa [F, Function.uncurry] using g.continuous
  have hprim :
      Continuous fun z : ℝ × ℝ => ∫ s in (0 : ℝ)..z.2, F z.1 s :=
    intervalIntegral.continuous_parametric_primitive_of_continuous
      (μ := volume) (f := F) (a₀ := (0 : ℝ)) hFcont
  refine hprim.continuousWithinAt.congr_of_eventuallyEq ?_ ?_
  · have hN : (Set.Ioo a b ×ˢ (Set.univ : Set ℝ)) ∈ 𝓝 (t0, x0) :=
      (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨⟨hat0, ht0b⟩, trivial⟩
    have hN' : (Set.Ioo a b ×ˢ (Set.univ : Set ℝ)) ∈
        𝓝[Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1] (t0, x0) :=
      mem_nhdsWithin_of_mem_nhds hN
    filter_upwards [hN', self_mem_nhdsWithin] with y hyN hyslab
    apply intervalIntegral.integral_congr
    intro s hs
    have hs01 : s ∈ Set.Icc (0 : ℝ) 1 :=
      Set.uIcc_subset_Icc (a₁ := (0 : ℝ)) (b₁ := y.2)
        (by norm_num) hyslab.2 hs
    have hmemK : (y.1, s) ∈ K :=
      ⟨⟨hyN.1.1.le, hyN.1.2.le⟩, hs01⟩
    exact (hg (y.1, s) hmemK).symm
  · apply intervalIntegral.integral_congr
    intro s hs
    have hs01 : s ∈ Set.Icc (0 : ℝ) 1 :=
      Set.uIcc_subset_Icc (a₁ := (0 : ℝ)) (b₁ := x0)
        (by norm_num) hx0 hs
    have hmemK : (t0, s) ∈ K :=
      ⟨⟨hat0.le, ht0b.le⟩, hs01⟩
    exact (hg (t0, s) hmemK).symm

/-- The elliptic `v` equation, solved pointwise for the interval-domain
Laplian. -/
theorem intervalDomain_laplacian_v_eq_reaction
    {params : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ} {x : intervalDomain.Point}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) (hx : x ∈ intervalDomain.inside) :
    intervalDomain.laplacian (v t) x =
      params.μ * v t x - params.ν * (u t x) ^ params.γ := by
  have hpde := hsol.pde_v ht0 htT hx
  linarith

/-- The same `v`-equation written for the real lift on interior spatial
points. -/
theorem intervalDomain_v_xx_eq_reaction_lift
    {params : CM2Params} {T t x : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) (hx0 : 0 < x) (hx1 : x < 1) :
    deriv (fun y : ℝ => deriv (intervalDomainLift (v t)) y) x =
      params.μ * intervalDomainLift (v t) x -
        params.ν * (intervalDomainLift (u t) x) ^ params.γ := by
  let X : intervalDomain.Point := ⟨x, ⟨hx0.le, hx1.le⟩⟩
  have hXin : X ∈ intervalDomain.inside := by
    change (X.1 : ℝ) ∈ Set.Ioo (0 : ℝ) 1
    exact ⟨hx0, hx1⟩
  have hL :
      intervalDomain.laplacian (v t) X =
        params.μ * v t X - params.ν * (u t X) ^ params.γ :=
    intervalDomain_laplacian_v_eq_reaction hsol ht0 htT hXin
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx0.le, hx1.le⟩
  simpa [intervalDomain, intervalDomainLaplacian, intervalDomainLift, hxIcc, X]
    using hL

/-- The parabolic `u` equation, solved pointwise for the interval-domain
Laplacian. -/
theorem intervalDomain_laplacian_u_eq_time_chem_logistic
    {params : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ} {x : intervalDomain.Point}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) (hx : x ∈ intervalDomain.inside) :
    intervalDomain.laplacian (u t) x =
      intervalDomain.timeDeriv u t x
        + params.χ₀ * intervalDomain.chemotaxisDiv params (u t) (v t) x
        - u t x * (params.a - params.b * (u t x) ^ params.α) := by
  have hpde := hsol.pde_u ht0 htT hx
  linarith

/-- Left Neumann value for the lifted `u` derivative, as stored in
`intervalDomainClassicalRegularity`. -/
theorem intervalDomain_dx_u_left_neumann
    {params : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    deriv (intervalDomainLift (u t)) 0 = 0 := by
  have hreg := hsol.regularity
  change intervalDomainClassicalRegularity T u v at hreg
  exact (hreg.2.2.2.2.1 t ht).1.2.1

/-- Left Neumann value for the lifted `v` derivative, as stored in
`intervalDomainClassicalRegularity`. -/
theorem intervalDomain_dx_v_left_neumann
    {params : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    deriv (intervalDomainLift (v t)) 0 = 0 := by
  have hreg := hsol.regularity
  change intervalDomainClassicalRegularity T u v at hreg
  exact (hreg.2.2.2.2.1 t ht).2.2.1

/-- Closed-slab joint continuity of the elliptic source obtained from the
`v`-equation.  This is the continuous integrand whose primitive should give
joint continuity of `∂ₓ v`. -/
theorem intervalDomain_v_xx_reaction_jointContinuous
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          params.μ * intervalDomainLift (v t) x -
            params.ν * (intervalDomainLift (u t) x) ^ params.γ))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hreg := hsol.regularity
  change intervalDomainClassicalRegularity T u v at hreg
  have hu_cont :
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    hreg.2.2.2.2.2.2.1
  have hv_cont :
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    hreg.2.2.2.2.2.2.2
  have hu_pos :
      ∀ z ∈ (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1),
        0 <
          Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x) z := by
    intro z hz
    rcases z with ⟨t, x⟩
    rcases hz with ⟨ht, hx⟩
    simp only [Function.uncurry_apply_pair]
    rw [intervalDomainLift, dif_pos hx]
    exact hsol.u_pos' ht.1 ht.2
  have hupow :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          (Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x) z) ^ params.γ)
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
    exact hu_cont.rpow_const
      (fun z hz => Or.inl (ne_of_gt (hu_pos z hz)))
  simpa [Function.uncurry] using
    (hv_cont.const_mul params.μ).sub (hupow.const_mul params.ν)

/-- Closed-slab joint continuity of the logistic source in the integrated
`u_x` identity. -/
theorem intervalDomain_u_logistic_jointContinuous
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          intervalDomainLift (u t) x *
            (params.a - params.b * (intervalDomainLift (u t) x) ^ params.α)))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hreg := hsol.regularity
  change intervalDomainClassicalRegularity T u v at hreg
  have hu_cont :
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    hreg.2.2.2.2.2.2.1
  have hu_pos :
      ∀ z ∈ (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1),
        0 <
          Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x) z := by
    intro z hz
    rcases z with ⟨t, x⟩
    rcases hz with ⟨ht, hx⟩
    simp only [Function.uncurry_apply_pair]
    rw [intervalDomainLift, dif_pos hx]
    exact hsol.u_pos' ht.1 ht.2
  have hupow :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          (Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x) z) ^ params.α)
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
    exact hu_cont.rpow_const
      (fun z hz => Or.inl (ne_of_gt (hu_pos z hz)))
  simpa [Function.uncurry] using
    hu_cont.mul (continuousOn_const.sub (hupow.const_mul params.b))

/-- Joint continuity of the variable-upper-limit primitive of the elliptic
`v`-source.  This is the continuous expression expected to equal `∂ₓv` after
the FTC + Neumann step. -/
theorem intervalDomain_v_x_reactionPrimitive_jointContinuous
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    ContinuousOn
      (fun z : ℝ × ℝ =>
        ∫ s in (0 : ℝ)..z.2,
          params.μ * intervalDomainLift (v z.1) s -
            params.ν * (intervalDomainLift (u z.1) s) ^ params.γ)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
  exact continuousOn_parametric_primitive_of_continuousOn_Ioo_Icc
    (intervalDomain_v_xx_reaction_jointContinuous hsol)

/-- Joint continuity of the variable-upper-limit primitive of the logistic
source in the integrated `u_x` identity. -/
theorem intervalDomain_u_logisticPrimitive_jointContinuous
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    ContinuousOn
      (fun z : ℝ × ℝ =>
        ∫ s in (0 : ℝ)..z.2,
          intervalDomainLift (u z.1) s *
            (params.a - params.b * (intervalDomainLift (u z.1) s) ^ params.α))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
  exact continuousOn_parametric_primitive_of_continuousOn_Ioo_Icc
    (intervalDomain_u_logistic_jointContinuous hsol)

#print axioms exists_continuous_extension_of_continuousOn_Icc_prod
#print axioms continuousOn_parametric_primitive_of_continuousOn_Ioo_Icc
#print axioms intervalDomain_laplacian_v_eq_reaction
#print axioms intervalDomain_v_xx_eq_reaction_lift
#print axioms intervalDomain_laplacian_u_eq_time_chem_logistic
#print axioms intervalDomain_dx_u_left_neumann
#print axioms intervalDomain_dx_v_left_neumann
#print axioms intervalDomain_v_xx_reaction_jointContinuous
#print axioms intervalDomain_u_logistic_jointContinuous
#print axioms intervalDomain_v_x_reactionPrimitive_jointContinuous
#print axioms intervalDomain_u_logisticPrimitive_jointContinuous
