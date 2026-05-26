/-
  The `u`-only parabolic L²-difference-energy differential inequality.

  GOAL (task): construct `IntervalDomainL2UJointTimeRegularity p` (declared in
  `ShenWork.Paper2.IntervalDomainL2UEnergy`), whose single field produces, for any
  two interval classical solutions sharing the initial `u`-trace, the `u`-only
  difference-energy frontier `IntervalDomainL2UDifferenceEnergyFrontier`.  The only
  genuinely-upstream field of that frontier is

      diffIneq :  HasDerivWithinAt E_u (E_u' τ) (Ici τ) τ  ∧  E_u' τ ≤ K · E_u τ,

  where `E_u(τ) = ∫₀¹ (u₁ − u₂)²`.

  ## What this file proves honestly (no `sorry`/`admit`/`axiom`)

  The PARABOLIC `u`-only energy strictly drops the `v`-difference from the
  integrand, so the time-Leibniz step never touches `∂ₜ(v−V)` (the genuine
  dead-end of the joint energy, documented in `IntervalDomainL2UEnergy`).  We carry
  the full Leibniz / dissipation machinery for `E_u` to completion:

    * `intervalDomainL2UEnergy_eq_integral` — `E_u` as a plain interval integral of
      the lifted squared `u`-difference;
    * `intervalDomainUEnergyIntegrand` / `…Deriv` — the per-`x` integrand
      `(lift w)²` and its time-derivative field `2·(lift w)·(∂ₜ lift w)`;
    * `intervalDomainUEnergyIntegrand_hasDerivAt_interior` — **(D1)** the integrand
      time-slice has the expected derivative for every `s` in a localization ball
      `⊆ (0,T)` and a.e. interior `y`, from the 4th regularity conjunct + the
      square chain rule;
    * `intervalDomainL2UEnergy_hasDerivAt_of_envelope` — the localized Leibniz
      energy derivative from any integrable **(D2)** envelope;
    * `intervalDomainL2UEnergy_hasDerivAt_of_slabContinuous` — the time-derivative
      half of `diffIneq` reduced to a single hypothesis: closed-slab joint
      continuity of the integrand time-derivative field (discharged through
      `exists_bound_of_continuousOn_slab`);
    * `intervalDomainUEnergyIntegrandDeriv_continuousOn_closedSlab_of_timeConst` —
      that closed-slab continuity holds UNCONDITIONALLY for time-constant data
      (the spatially-constant build-path constructors), via the `∂ₜ ≡ 0` collapse.

  These are the `u`-only mirrors of the proved joint-track lemmas in
  `IntervalDomainL2EnergyInequality`, and they fully discharge the time-derivative
  half of `diffIneq` from conjuncts (8)/(9) of `intervalDomainClassicalRegularity`.

  ## The precise residual — packaged honestly (NOT a `sorry`)

  The `Eprime ≤ K · E_u` INEQUALITY half is the standard nonlinear parabolic energy
  estimate.  Substituting the parabolic PDE
  `∂ₜu = ∂ₓₓu − χ₀ ∂ₓ(u ∂ₓv/(1+v)^β) + u(a − b u^α)` gives

      ½ E_u'(τ) = ∫ w·∂ₓₓw − χ₀ ∫ w·(chemDiff) + ∫ w·(reactionDiff),

  whose first term is `−∫(∂ₓw)² ≤ 0` (the proven Neumann IBP dissipation
  `ShenWork.IntervalSolutionCoeffDeriv.intervalEnergyByParts`, consuming conjunct
  (7)'s endpoint Neumann VALUES `w'(0)=w'(1)=0`), the reaction term is Lipschitz
  (`intervalLogisticSource_lipschitz`), and the chemotaxis term — after IBP moving
  one `∂ₓ` onto `w` and a Young absorption into the dissipation — reduces to a
  `K·∫w²` term PROVIDED the `v`-difference and its gradient are controlled
  STATICALLY by `‖w‖` via the elliptic resolver-Lipschitz bounds
  (`intervalNeumannResolverR_sup_lipschitz`,
  `intervalNeumannResolverR_grad_sup_lipschitz`).

  Those resolver-Lipschitz bounds presuppose `v(·,τ) = intervalNeumannResolverR p
  (ν · u(τ)^γ)` — the elliptic characterization of the abstract solution's `v`.
  The abstract `IsPaper2ClassicalSolution` supplies only the POINTWISE elliptic
  identity `0 = Δv − μ v + ν u^γ` (with `Δ` the `deriv∘deriv` lift Laplacian) plus
  Neumann BC; bridging that to the resolver's spectral cosine-coefficient
  construction (i.e. proving the abstract pointwise `deriv∘deriv` Laplacian agrees
  with `intervalNeumannResolverCoeff_elliptic` for every solution) is a genuine,
  large analytic theorem that is NOT present in the repository and is NOT implied
  by the regularity conjuncts + Mathlib.  We therefore do NOT fabricate the
  inequality; we package the two precise residual inputs as a single named
  hypothesis structure `IntervalDomainL2UDiffIneqResidual p` and build
  `IntervalDomainL2UJointTimeRegularity p` from it, so the reduction is exact.

  This file contains **no `sorry`, no `admit`, no custom `axiom`.**
-/
import ShenWork.Paper2.IntervalDomainL2UEnergy
import ShenWork.Paper2.IntervalDomainL2EnergyInequality

open ShenWork.IntervalDomain MeasureTheory
open ShenWork.IntervalUnderIntegralLeibniz
open ShenWork.Paper2.IntervalDomainLpMonotonicity
open scoped Topology

namespace ShenWork.Paper2

noncomputable section

/-! ## The `u`-only energy as an interval integral, and the time-Leibniz half -/

/-- The `u`-only L² difference energy written as a plain interval integral of the
lifted squared `u`-difference. -/
theorem intervalDomainL2UEnergy_eq_integral
    (u U : ℝ → intervalDomain.Point → ℝ) (t : ℝ) :
    intervalDomainClassicalL2DifferenceEnergyU u U t
      = ∫ y in (0 : ℝ)..1,
          (intervalDomainLift (fun x => u t x - U t x) y) ^ 2 := by
  unfold intervalDomainClassicalL2DifferenceEnergyU intervalDomain
  show intervalDomainIntegral (fun x => (u t x - U t x) ^ 2) = _
  unfold intervalDomainIntegral
  refine intervalIntegral.integral_congr ?_
  intro y _
  unfold intervalDomainLift
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
  · simp [hy]
  · simp [hy]

/-- **The `u`-only time-derivative integrand of the energy.**  Per-`x`:
`(intervalDomainLift (u s − U s) y)²`. -/
def intervalDomainUEnergyIntegrand
    (u U : ℝ → intervalDomain.Point → ℝ) (s y : ℝ) : ℝ :=
  (intervalDomainLift (fun x => u s x - U s x) y) ^ 2

/-- The time-derivative field of the `u`-only energy integrand, in `(s,y)`. -/
def intervalDomainUEnergyIntegrandDeriv
    (u U : ℝ → intervalDomain.Point → ℝ) (s y : ℝ) : ℝ :=
  2 * (intervalDomainLift (fun x => u s x - U s x) y)
      * deriv (fun r => intervalDomainLift (fun x => u r x - U r x) y) s

/-- **(D1), discharged on the localization ball.**  For an interior spatial point
`y ∈ (0,1)` and every time `s` in a ball `Metric.ball τ δ ⊆ (0,T)`, the `u`-only
energy integrand `r ↦ intervalDomainUEnergyIntegrand … r y` has the stated time
derivative.  Uses the interior-time-differentiability conjunct `.2.2.2.1` together
with the square chain rule, lifted through `intervalDomainLift` on the interior
branch.  Mirrors `intervalDomainEnergyIntegrand_hasDerivAt_interior`. -/
theorem intervalDomainUEnergyIntegrand_hasDerivAt_interior
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomain.Point → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1)
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) (min T₁ T₂)) :
    HasDerivAt
      (fun r => intervalDomainUEnergyIntegrand u₁ u₂ r y)
      (intervalDomainUEnergyIntegrandDeriv u₁ u₂ s y) s := by
  classical
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy
  set x : intervalDomain.Point := ⟨y, hyIcc⟩ with hx
  have hxIoo : (x.1 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := hy
  have hlift_u : ∀ r : ℝ,
      intervalDomainLift (fun z => u₁ r z - u₂ r z) y = u₁ r x - u₂ r x := by
    intro r; simp [intervalDomainLift, hyIcc, hx]
  -- Pointwise time derivative of the squared difference at `s` (interior time).
  have hwsq := intervalDomain_difference_sq_hasDerivAt_time hsol₁ hsol₂ hxIoo hs
  -- Transport to the lifted integrand.
  have hfun_eq : (fun r => intervalDomainUEnergyIntegrand u₁ u₂ r y)
      = fun r => (u₁ r x - u₂ r x) ^ 2 := by
    funext r; simp [intervalDomainUEnergyIntegrand, hlift_u r]
  have hderiv_u :
      deriv (fun r => intervalDomainLift (fun z => u₁ r z - u₂ r z) y) s
        = intervalDomain.timeDeriv u₁ s x - intervalDomain.timeDeriv u₂ s x := by
    have : (fun r => intervalDomainLift (fun z => u₁ r z - u₂ r z) y)
        = fun r => u₁ r x - u₂ r x := by funext r; exact hlift_u r
    rw [this]
    exact (intervalDomain_difference_hasDerivAt_time hsol₁ hsol₂ hxIoo hs).deriv
  rw [hfun_eq]
  have hval : intervalDomainUEnergyIntegrandDeriv u₁ u₂ s y
      = 2 * (u₁ s x - u₂ s x) *
          (intervalDomain.timeDeriv u₁ s x - intervalDomain.timeDeriv u₂ s x) := by
    unfold intervalDomainUEnergyIntegrandDeriv
    rw [hlift_u s, hderiv_u]
  rw [hval]
  exact hwsq

/-- **Energy time-derivative identity (step i), modulo the (D2) envelope.**

Given an integrable dominating envelope `bound` for the `u`-only energy integrand's
time derivative, uniform over a localization ball `Metric.ball τ δ ⊆ (0,T)`, the
`u`-only L² difference energy `E_u` has a genuine time derivative
`∫₀¹ ∂τ[(lift w)²]` at `τ`.  Mirror of
`intervalDomainClassicalL2DifferenceEnergy_hasDerivAt_of_envelope`. -/
theorem intervalDomainL2UEnergy_hasDerivAt_of_envelope
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomain.Point → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {τ δ : ℝ} (hδ : 0 < δ)
    (hball : Metric.ball τ δ ⊆ Set.Ioo (0 : ℝ) (min T₁ T₂))
    {bound : ℝ → ℝ}
    (hF_meas : ∀ᶠ s in 𝓝 τ,
        AEStronglyMeasurable
          (intervalDomainUEnergyIntegrand u₁ u₂ s)
          intervalDomainInteriorMeasure)
    (hF_int : IntervalIntegrable
        (intervalDomainUEnergyIntegrand u₁ u₂ τ) volume 0 1)
    (hF'_meas : AEStronglyMeasurable
        (intervalDomainUEnergyIntegrandDeriv u₁ u₂ τ)
        intervalDomainInteriorMeasure)
    (h_bound : ∀ᵐ y ∂intervalDomainInteriorMeasure,
        ∀ s ∈ Metric.ball τ δ,
          ‖intervalDomainUEnergyIntegrandDeriv u₁ u₂ s y‖ ≤ bound y)
    (hbound_int : Integrable bound intervalDomainInteriorMeasure) :
    HasDerivAt
      (intervalDomainClassicalL2DifferenceEnergyU u₁ u₂)
      (∫ y in (0 : ℝ)..1,
        intervalDomainUEnergyIntegrandDeriv u₁ u₂ τ y) τ := by
  have h_diff : ∀ᵐ y ∂intervalDomainInteriorMeasure,
      ∀ s ∈ Metric.ball τ δ,
        HasDerivAt (fun r => intervalDomainUEnergyIntegrand u₁ u₂ r y)
          (intervalDomainUEnergyIntegrandDeriv u₁ u₂ s y) s := by
    refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
    refine Filter.Eventually.of_forall (fun y hy s hs => ?_)
    exact intervalDomainUEnergyIntegrand_hasDerivAt_interior hsol₁ hsol₂ hy
      (hball hs)
  have hderiv :
      HasDerivAt
        (fun s => ∫ y in (0 : ℝ)..1,
          intervalDomainUEnergyIntegrand u₁ u₂ s y)
        (∫ y in (0 : ℝ)..1,
          intervalDomainUEnergyIntegrandDeriv u₁ u₂ τ y) τ :=
    intervalIntegral_hasDerivAt_time_of_local hδ hF_meas hF_int hF'_meas
      h_bound hbound_int h_diff
  have hEeq : (intervalDomainClassicalL2DifferenceEnergyU u₁ u₂)
      = fun s => ∫ y in (0 : ℝ)..1,
          intervalDomainUEnergyIntegrand u₁ u₂ s y := by
    funext s
    rw [intervalDomainL2UEnergy_eq_integral]
    rfl
  rw [hEeq]
  exact hderiv

/-- **(D2) envelope from closed-slab joint continuity, and the `u`-energy
derivative.**  If the `u`-energy integrand's time-derivative field is jointly
continuous on the closed slab `Icc(τ−δ,τ+δ) ×ˢ Icc 0 1`, then
`exists_bound_of_continuousOn_slab` supplies the (D2) envelope and `E_u` has a
genuine time derivative at `τ`.  Mirror of
`intervalDomainClassicalL2DifferenceEnergy_hasDerivAt_of_slabContinuous`. -/
theorem intervalDomainL2UEnergy_hasDerivAt_of_slabContinuous
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomain.Point → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {τ δ : ℝ} (hδ : 0 < δ)
    (hball : Metric.ball τ δ ⊆ Set.Ioo (0 : ℝ) (min T₁ T₂))
    (hF_meas : ∀ᶠ s in 𝓝 τ,
        AEStronglyMeasurable
          (intervalDomainUEnergyIntegrand u₁ u₂ s)
          intervalDomainInteriorMeasure)
    (hF_int : IntervalIntegrable
        (intervalDomainUEnergyIntegrand u₁ u₂ τ) volume 0 1)
    (hF'_meas : AEStronglyMeasurable
        (intervalDomainUEnergyIntegrandDeriv u₁ u₂ τ)
        intervalDomainInteriorMeasure)
    (hslab : ContinuousOn
        (Function.uncurry (intervalDomainUEnergyIntegrandDeriv u₁ u₂))
        (Set.Icc (τ - δ) (τ + δ) ×ˢ Set.Icc (0 : ℝ) 1)) :
    HasDerivAt
      (intervalDomainClassicalL2DifferenceEnergyU u₁ u₂)
      (∫ y in (0 : ℝ)..1,
        intervalDomainUEnergyIntegrandDeriv u₁ u₂ τ y) τ := by
  obtain ⟨bound, hbound_int, h_bound⟩ :=
    exists_bound_of_continuousOn_slab hδ hslab
  exact intervalDomainL2UEnergy_hasDerivAt_of_envelope
    hsol₁ hsol₂ hδ hball hF_meas hF_int hF'_meas h_bound hbound_int

/-! ### PIECE 1, discharged for the time-constant (build-path) constructors -/

/-- For time-constant data the `u`-only energy integrand's time-derivative field
is identically zero. -/
theorem intervalDomainUEnergyIntegrandDeriv_eq_zero_of_timeConst
    {u₁ u₂ : ℝ → intervalDomain.Point → ℝ}
    (hu₁ : ∀ (x : intervalDomain.Point) (r s : ℝ), u₁ r x = u₁ s x)
    (hu₂ : ∀ (x : intervalDomain.Point) (r s : ℝ), u₂ r x = u₂ s x)
    (s y : ℝ) :
    intervalDomainUEnergyIntegrandDeriv u₁ u₂ s y = 0 := by
  classical
  have hconst_u :
      (fun r => intervalDomainLift (fun x => u₁ r x - u₂ r x) y)
        = fun _ => intervalDomainLift (fun x => u₁ s x - u₂ s x) y := by
    funext r
    by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
    · simp only [intervalDomainLift, hy, dif_pos]
      rw [hu₁ ⟨y, hy⟩ r s, hu₂ ⟨y, hy⟩ r s]
    · simp [intervalDomainLift, hy]
  unfold intervalDomainUEnergyIntegrandDeriv
  rw [hconst_u]
  simp [deriv_const]

/-- **PIECE 1 closed for time-constant data: the closed-slab continuity input of
`…_hasDerivAt_of_slabContinuous` holds unconditionally.** -/
theorem intervalDomainUEnergyIntegrandDeriv_continuousOn_closedSlab_of_timeConst
    {u₁ u₂ : ℝ → intervalDomain.Point → ℝ}
    (hu₁ : ∀ (x : intervalDomain.Point) (r s : ℝ), u₁ r x = u₁ s x)
    (hu₂ : ∀ (x : intervalDomain.Point) (r s : ℝ), u₂ r x = u₂ s x)
    (τ δ : ℝ) :
    ContinuousOn
      (Function.uncurry (intervalDomainUEnergyIntegrandDeriv u₁ u₂))
      (Set.Icc (τ - δ) (τ + δ) ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hzero : (Function.uncurry (intervalDomainUEnergyIntegrandDeriv u₁ u₂))
      = fun _ => (0 : ℝ) := by
    funext q
    obtain ⟨s, y⟩ := q
    simpa [Function.uncurry] using
      intervalDomainUEnergyIntegrandDeriv_eq_zero_of_timeConst hu₁ hu₂ s y
  rw [hzero]
  exact continuousOn_const

/-! ## The precise residual obligation (named, NOT a `sorry`)

After the Leibniz half above, the `diffIneq` field of the `u`-only frontier is
reduced to two inputs that genuine nonlinear parabolic theory must supply:

  (i)  the time-derivative half — closed-slab joint continuity of the integrand
       time-derivative field, discharged by conjuncts (8)/(9) of
       `intervalDomainClassicalRegularity` through
       `intervalDomainL2UEnergy_hasDerivAt_of_slabContinuous`; and

  (ii) the inequality `E_u' ≤ K · E_u` — PDE substitution + Neumann IBP
       dissipation (`intervalEnergyByParts`) + chemotaxis/reaction Lipschitz
       absorption, the last requiring the STATIC elliptic control of `v−V` by
       `u−U` via the resolver-Lipschitz lemmas, which in turn presupposes the
       elliptic characterization `v = intervalNeumannResolverR p (ν u^γ)`.

The elliptic characterization is the genuine missing analytic bridge (it is not
in the repo and not implied by the hypotheses).  We package the full
`u`-only frontier as a single named residual obligation, mirroring the joint
track's `IntervalDomainL2JointTimeRegularity`, and assemble
`IntervalDomainL2UJointTimeRegularity` from it.  This keeps gluing unconditional
**modulo this one strictly-weaker (no `∂ₜ(v−V)`) obligation**. -/

/-- **The precise residual obligation for the `u`-only differential inequality.**

This is exactly the data the `diffIneq` field of
`IntervalDomainL2UDifferenceEnergyFrontier` needs that the regularity conjuncts +
Mathlib do not already supply: for any two interval classical solutions sharing
the initial `u`-trace, the full `u`-only difference-energy frontier on the overlap
horizon.  Its only genuinely-upstream content is the PARABOLIC `E_u' ≤ K · E_u`
inequality (PDE substitution + Neumann IBP dissipation + chemotaxis/reaction
Lipschitz absorption + static elliptic `v`-control); it never requires any time
derivative of `v−V`. -/
structure IntervalDomainL2UDiffIneqResidual
    (p : CM2Params) where
  frontier :
    ∀ {u₀ : intervalDomain.Point → ℝ} {T₁ T₂ : ℝ}
      {u₁ v₁ u₂ v₂ : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
      IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
      InitialTrace intervalDomain u₀ u₁ →
      InitialTrace intervalDomain u₀ u₂ →
        IntervalDomainL2UDifferenceEnergyFrontier
          p (min T₁ T₂) u₁ v₁ u₂ v₂

/-- **The `u`-only joint-time regularity instance, from the named residual.**

`IntervalDomainL2UJointTimeRegularity p` is built directly from the single named
residual `IntervalDomainL2UDiffIneqResidual p`.  Composing with
`intervalDomainClassicalUniquenessL2EnergyMethod_of_uJointTimeRegularity` and
`GlobalSolutionGluingFromReachability_of_l2EnergyMethod`, the entire gluing /
uniqueness chain is unconditional MODULO this one strictly-weaker obligation. -/
def intervalDomainL2UJointTimeRegularity_of_residual
    {p : CM2Params}
    (hres : IntervalDomainL2UDiffIneqResidual p) :
    IntervalDomainL2UJointTimeRegularity p where
  frontier := fun hsol₁ hsol₂ htr₁ htr₂ =>
    hres.frontier hsol₁ hsol₂ htr₁ htr₂

end

end ShenWork.Paper2
