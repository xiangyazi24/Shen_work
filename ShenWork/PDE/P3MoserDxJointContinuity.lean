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

/-- Pointwise FTC bridge from the elliptic `v` equation and the left Neumann
condition: on the closed spatial interval, `v_x` is the primitive of the
reaction source. -/
theorem intervalDomain_dx_v_eq_reactionPrimitive
    {params : CM2Params} {T t x : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    deriv (intervalDomainLift (v t)) x =
      ∫ s in (0 : ℝ)..x,
        params.μ * intervalDomainLift (v t) s -
          params.ν * (intervalDomainLift (u t) s) ^ params.γ := by
  classical
  rcases hx with ⟨hx0, hx1⟩
  by_cases hx_eq0 : x = 0
  · subst x
    simp [intervalDomain_dx_v_left_neumann hsol ht]
  have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx_eq0)
  let R : ℝ → ℝ := fun s =>
    params.μ * intervalDomainLift (v t) s -
      params.ν * (intervalDomainLift (u t) s) ^ params.γ
  have hreg := hsol.regularity
  change intervalDomainClassicalRegularity T u v at hreg
  have hC2v : ContDiffOn ℝ 2 (intervalDomainLift (v t)) (Set.Ioo (0 : ℝ) 1) :=
    (hreg.1 t ht).2
  have hDvC1 : ContDiffOn ℝ 1 (deriv (intervalDomainLift (v t))) (Set.Ioo (0 : ℝ) 1) :=
    hC2v.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hderiv :
      ∀ y ∈ Set.Ioo (0 : ℝ) x,
        HasDerivAt (fun z : ℝ => deriv (intervalDomainLift (v t)) z) (R y) y := by
    intro y hy
    have hy01 : y ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨hy.1, lt_of_lt_of_le hy.2 hx1⟩
    have hdiff :
        DifferentiableAt ℝ (deriv (intervalDomainLift (v t))) y :=
      (hDvC1.differentiableOn (by norm_num)).differentiableAt
        (IsOpen.mem_nhds isOpen_Ioo hy01)
    have hxx :
        deriv (fun z : ℝ => deriv (intervalDomainLift (v t)) z) y = R y := by
      simpa [R] using
        intervalDomain_v_xx_eq_reaction_lift hsol ht.1 ht.2 hy.1
          (lt_of_lt_of_le hy.2 hx1)
    simpa [hxx] using hdiff.hasDerivAt
  have hRint : IntervalIntegrable R volume (0 : ℝ) x := by
    have hsrc := intervalDomain_v_xx_reaction_jointContinuous (params := params)
      (T := T) (u := u) (v := v) hsol
    have hmap : ContinuousOn (fun s : ℝ => (t, s)) (Set.Icc (0 : ℝ) x) :=
      (continuous_const.prodMk continuous_id).continuousOn
    have hslice : ContinuousOn R (Set.Icc (0 : ℝ) x) := by
      refine (hsrc.comp hmap ?_)
      intro s hs
      exact ⟨ht, ⟨hs.1, le_trans hs.2 hx1⟩⟩
    exact hslice.intervalIntegrable_of_Icc hxpos.le
  have hleft_tendsto :
      Filter.Tendsto (fun z : ℝ => deriv (intervalDomainLift (v t)) z)
        (𝓝[>] (0 : ℝ)) (𝓝 (deriv (intervalDomainLift (v t)) 0)) := by
    have hleft := (hreg.2.2.2.1 t ht).2.1
    have h0 := intervalDomain_dx_v_left_neumann hsol ht
    simpa [h0] using hleft
  have hright_tendsto :
      Filter.Tendsto (fun z : ℝ => deriv (intervalDomainLift (v t)) z)
        (𝓝[<] x) (𝓝 (deriv (intervalDomainLift (v t)) x)) := by
    by_cases hxlt : x < 1
    · have hx01 : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hxpos, hxlt⟩
      have hdiff :
          DifferentiableAt ℝ (deriv (intervalDomainLift (v t))) x :=
        (hDvC1.differentiableOn (by norm_num)).differentiableAt
          (IsOpen.mem_nhds isOpen_Ioo hx01)
      exact hdiff.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · have hx_eq1 : x = 1 := le_antisymm hx1 (le_of_not_gt hxlt)
      subst x
      have hright := (hreg.2.2.2.1 t ht).2.2
      have h1 : deriv (intervalDomainLift (v t)) 1 = 0 :=
        (hreg.2.2.2.2.1 t ht).2.2.2
      simpa [h1] using hright
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
      (f := fun z : ℝ => deriv (intervalDomainLift (v t)) z)
      (f' := R) hxpos hderiv hRint hleft_tendsto hright_tendsto
  have h0 := intervalDomain_dx_v_left_neumann hsol ht
  rw [h0, sub_zero] at hFTC
  exact hFTC.symm

/-- Joint continuity of the lifted spatial derivative `v_x` on
`(0,T) × [0,1]`, obtained by transferring continuity from the already-proved
reaction primitive. -/
theorem intervalDomain_dx_v_jointlyContinuous
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => deriv (intervalDomainLift (v t)) x))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
  refine ContinuousOn.congr
    (intervalDomain_v_x_reactionPrimitive_jointContinuous (params := params)
      (T := T) (u := u) (v := v) hsol) ?_
  intro z hz
  rcases z with ⟨t, x⟩
  exact intervalDomain_dx_v_eq_reactionPrimitive (params := params)
    (T := T) (u := u) (v := v) hsol hz.1 hz.2

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
#print axioms intervalDomain_dx_v_eq_reactionPrimitive
#print axioms intervalDomain_dx_v_jointlyContinuous

/-- Joint continuity of the variable-upper-limit primitive of the closed-slab
time derivative field in the integrated `u_x` identity. -/
theorem intervalDomain_u_timeDeriv_primitive_jointContinuous
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    ContinuousOn
      (fun z : ℝ × ℝ =>
        ∫ s in (0 : ℝ)..z.2,
          deriv (fun r : ℝ => intervalDomainLift (u r) s) z.1)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hreg := hsol.regularity
  change intervalDomainClassicalRegularity T u v at hreg
  exact continuousOn_parametric_primitive_of_continuousOn_Ioo_Icc
    (by
      simpa [Function.uncurry] using hreg.2.2.2.2.2.1.1)

/-- Closed-slab joint continuity of the chemotactic flux
`u v_x / (1 + v)^β`. -/
theorem intervalDomain_chemotaxis_flux_jointContinuous
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    ContinuousOn
      (fun z : ℝ × ℝ =>
        intervalDomainLift (u z.1) z.2 *
          deriv (intervalDomainLift (v z.1)) z.2 /
            (1 + intervalDomainLift (v z.1) z.2) ^ params.β)
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
  have hvx_cont :
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => deriv (intervalDomainLift (v t)) x))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    intervalDomain_dx_v_jointlyContinuous (params := params)
      (T := T) (u := u) (v := v) hsol
  have hbase_cont :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          1 +
            Function.uncurry
              (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z)
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.add hv_cont
  have hbase_pos :
      ∀ z ∈ (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1),
        0 <
          1 +
            Function.uncurry
              (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z := by
    intro z hz
    rcases z with ⟨t, x⟩
    rcases hz with ⟨ht, hx⟩
    simp only [Function.uncurry_apply_pair]
    rw [intervalDomainLift, dif_pos hx]
    have hv_nonneg : 0 ≤ v t ⟨x, hx⟩ :=
      hsol.v_nonneg ht.1 ht.2
    linarith
  have hden_cont :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          (1 +
            Function.uncurry
              (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) ^
            params.β)
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    hbase_cont.rpow_const
      (fun z hz => Or.inl (ne_of_gt (hbase_pos z hz)))
  have hden_ne :
      ∀ z ∈ (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1),
        (1 +
          Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) ^
            params.β ≠ 0 := by
    intro z hz
    exact ne_of_gt (Real.rpow_pos_of_pos (hbase_pos z hz) _)
  simpa [Function.uncurry] using
    (hu_cont.mul hvx_cont).div hden_cont hden_ne

#print axioms intervalDomain_u_timeDeriv_primitive_jointContinuous
#print axioms intervalDomain_chemotaxis_flux_jointContinuous

/-- The closed-interval representative of `u_x` has zero left endpoint value. -/
theorem intervalDomain_dxWithin_u_left_neumann
    {params : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    derivWithin (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) 0 = 0 := by
  let X0 : intervalDomain.Point := ⟨0, ⟨le_rfl, by norm_num⟩⟩
  have hbd : X0 ∈ intervalDomain.boundary := by
    change (X0.1 : ℝ) = 0 ∨ (X0.1 : ℝ) = 1
    left
    rfl
  have hN := (hsol.neumann ht.1 ht.2 hbd).1
  have hnormal :
      derivWithin (intervalDomainLift (u t)) (Set.Ici (0 : ℝ)) 0 = 0 := by
    simpa [intervalDomain, intervalDomainNormalDeriv, X0] using hN
  have hsets :
      (Set.Icc (0 : ℝ) 1 : Set ℝ) =ᶠ[𝓝 (0 : ℝ)] Set.Ici (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with y hy
    apply propext
    constructor
    · intro h
      exact h.1
    · intro h
      exact ⟨h, le_of_lt hy⟩
  rwa [derivWithin_congr_set hsets]

/-- The closed-interval representative of `u_x` has zero right endpoint value. -/
theorem intervalDomain_dxWithin_u_right_neumann
    {params : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    derivWithin (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) 1 = 0 := by
  let X1 : intervalDomain.Point := ⟨1, ⟨by norm_num, le_rfl⟩⟩
  have hbd : X1 ∈ intervalDomain.boundary := by
    change (X1.1 : ℝ) = 0 ∨ (X1.1 : ℝ) = 1
    right
    rfl
  have hN := (hsol.neumann ht.1 ht.2 hbd).1
  have hnormal :
      derivWithin (intervalDomainLift (u t)) (Set.Iic (1 : ℝ)) 1 = 0 := by
    simpa [intervalDomain, intervalDomainNormalDeriv, X1] using hN
  have hsets :
      (Set.Icc (0 : ℝ) 1 : Set ℝ) =ᶠ[𝓝 (1 : ℝ)] Set.Iic (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with y hy
    apply propext
    constructor
    · intro h
      exact h.2
    · intro h
      exact ⟨le_of_lt hy, h⟩
  rwa [derivWithin_congr_set hsets]

/-- Pointwise FTC bridge: on the closed spatial interval, `u_x` is the
primitive of the lifted second spatial derivative. -/
theorem intervalDomain_dx_u_eq_laplacianPrimitive
    {params : CM2Params} {T t x : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    deriv (intervalDomainLift (u t)) x =
      ∫ s in (0 : ℝ)..x,
        deriv (fun y : ℝ => deriv (intervalDomainLift (u t)) y) s := by
  classical
  rcases hx with ⟨hx0, hx1⟩
  by_cases hx_eq0 : x = 0
  · subst x
    simp [intervalDomain_dx_u_left_neumann hsol ht]
  have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx_eq0)
  let W : ℝ → ℝ :=
    fun y => derivWithin (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) y
  have hreg := hsol.regularity
  change intervalDomainClassicalRegularity T u v at hreg
  have hC2u : ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    (hreg.2.2.2.2.1 t ht).1.1
  have hWc1 : ContDiffOn ℝ 1 W (Set.Icc (0 : ℝ) 1) := by
    simpa [W] using
      hC2u.derivWithin (uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num))
        (by norm_num)
  have hWc1_x : ContDiffOn ℝ 1 W (Set.Icc (0 : ℝ) x) :=
    hWc1.mono (by
      intro y hy
      exact ⟨hy.1, le_trans hy.2 hx1⟩)
  have hW_cont : ContinuousOn W (Set.Icc (0 : ℝ) x) :=
    hWc1_x.continuousOn
  have hW_deriv :
      ∀ y ∈ Set.Ioo (0 : ℝ) x, HasDerivAt W (deriv W y) y := by
    intro y hy
    have hyIcc : y ∈ Set.Icc (0 : ℝ) x := ⟨hy.1.le, hy.2.le⟩
    have hdiff : DifferentiableAt ℝ W y :=
      ((hWc1_x y hyIcc).contDiffAt (Icc_mem_nhds hy.1 hy.2)).differentiableAt
        one_ne_zero
    exact hdiff.hasDerivAt
  have hW_derivWithin_cont :
      ContinuousOn (derivWithin W (Set.Icc (0 : ℝ) x)) (Set.Icc (0 : ℝ) x) :=
    (hWc1_x.derivWithin (m := 0) (uniqueDiffOn_Icc hxpos) (by norm_num)).continuousOn
  have hW_derivWithin_int :
      IntervalIntegrable (derivWithin W (Set.Icc (0 : ℝ) x)) volume (0 : ℝ) x :=
    hW_derivWithin_cont.intervalIntegrable_of_Icc hxpos.le
  have hW_deriv_int : IntervalIntegrable (deriv W) volume (0 : ℝ) x := by
    refine hW_derivWithin_int.congr_ae ?_
    simp only [Set.uIoc_of_le hxpos.le]
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with y hy
    exact derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)
  have hFTC :
      ∫ s in (0 : ℝ)..x, deriv W s = W x - W 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hxpos.le hW_cont
      hW_deriv hW_deriv_int
  have hcongr :
      (∫ s in (0 : ℝ)..x,
          deriv (fun y : ℝ => deriv (intervalDomainLift (u t)) y) s)
        = ∫ s in (0 : ℝ)..x, deriv W s := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [ae_uIoc_iff]
    constructor
    · filter_upwards [(Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := x) :
          Set.Ioo (0 : ℝ) x =ᶠ[ae volume] Set.Ioc (0 : ℝ) x)]
        with y hyEq hyIoc
      have hy : y ∈ Set.Ioo (0 : ℝ) x := by
        exact Eq.mpr hyEq hyIoc
      have hy01 : y ∈ Set.Ioo (0 : ℝ) 1 := ⟨hy.1, lt_of_lt_of_le hy.2 hx1⟩
      have hWev :
          W =ᶠ[𝓝 y] fun z : ℝ => deriv (intervalDomainLift (u t)) z := by
        filter_upwards [IsOpen.mem_nhds isOpen_Ioo hy01] with z hz
        have hzsets : Set.Icc (0 : ℝ) 1 ∈ 𝓝 z := Icc_mem_nhds hz.1 hz.2
        simp [W, derivWithin_of_mem_nhds hzsets]
      exact (hWev.deriv_eq).symm
    · filter_upwards with y hy
      have hyfalse : False := by
        rcases hy with ⟨hyx, hy0⟩
        linarith
      exact False.elim hyfalse
  have hW0 : W 0 = 0 := by
    simpa [W] using intervalDomain_dxWithin_u_left_neumann
      (params := params) (T := T) (u := u) (v := v) hsol ht
  have hWx : W x = deriv (intervalDomainLift (u t)) x := by
    by_cases hx_eq1 : x = 1
    · subst x
      have hW1 : W 1 = 0 := by
        simpa [W] using intervalDomain_dxWithin_u_right_neumann
          (params := params) (T := T) (u := u) (v := v) hsol ht
      have hD1 : deriv (intervalDomainLift (u t)) 1 = 0 :=
        (hreg.2.2.2.2.1 t ht).1.2.2
      simp [hW1, hD1]
    · have hxlt : x < 1 := lt_of_le_of_ne hx1 hx_eq1
      have hsets : Set.Icc (0 : ℝ) 1 ∈ 𝓝 x := Icc_mem_nhds hxpos hxlt
      simp [W, derivWithin_of_mem_nhds hsets]
  rw [hcongr, hFTC, hWx, hW0, sub_zero]

#print axioms intervalDomain_dxWithin_u_left_neumann
#print axioms intervalDomain_dxWithin_u_right_neumann
#print axioms intervalDomain_dx_u_eq_laplacianPrimitive
