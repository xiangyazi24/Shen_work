/-
  Concrete L² energy-method overlap-uniqueness certificate for the coupled
  interval-domain Paper2 PDE.

  This file closes the *Grönwall* half of the L² energy method honestly and in
  full, and assembles the remaining analytic inputs into a single named
  "frontier" interface.  Concretely:

  Let `w = u₁ - u₂`, `z = v₁ - v₂`, and
  `E t = ∫ (w t)² + (z t)²  (= intervalDomainClassicalL2DifferenceEnergy)`.
  The textbook energy identity gives, after integrating `w · ∂ₜw` by parts with
  the Neumann conditions and using the boundedness of the classical solutions on
  the overlap plus `intervalLogisticSource_lipschitz` / chemotaxis Lipschitz,
  a differential inequality `dE/dt ≤ K · E` on the open overlap interval.

  What this file proves *from scratch*:
    * `intervalDomainL2_gronwall_exp_of_diffIneq` — from a right-derivative
      differential inequality `E' τ ≤ K · E τ` (with `0 ≤ K`, `E` continuous,
      `E ≥ 0`) on `(s,t)` one gets `E t ≤ E s · exp (K (t - s))`.  This is the
      genuine Grönwall step, via Mathlib's
      `le_gronwallBound_of_liminf_deriv_right_le`.
    * `intervalDomainClassicalL2DifferenceEnergy_nonneg` — the L² difference
      energy is `≥ 0` (integral of a sum of squares), proved directly.
    * `intervalDomainClassicalOverlapL2EnergyCertificate_of_diffIneqFrontier` —
      assembles all four certificate fields from the named analytic frontiers.
    * `intervalDomainClassicalUniquenessL2EnergyMethod_of_frontier` and
      `intervalDomainClassicalUniquenessL2EnergyMethod_concrete` — produce the
      full method instance, given the per-pair analytic frontier.

  What remains genuinely upstream (documented, NOT faked): the PDE-level
  derivation of the differential-inequality frontier itself
  (`IntervalDomainL2DifferenceEnergyFrontier` below) from
  `IsPaper2ClassicalSolution`.  This is the same regularity gap the whole
  `IntervalDomainEnergyStep` family leaves open: the abstract
  `intervalDomainClassicalRegularity` controls only the *time trace of the sup
  norm*, not the spatial `C²` regularity / differentiation-under-the-integral
  needed to differentiate `E` and integrate `w · Δw` by parts.  See the
  detailed status note at the end of this file.
-/
import ShenWork.Paper2.IntervalDomainClassicalUniqueness
import Mathlib.Analysis.ODE.Gronwall

open ShenWork.IntervalDomain
open scoped Topology

namespace ShenWork.Paper2

noncomputable section

/-- The L² difference energy is nonnegative: it is the interval integral of a
sum of squares.  Proved directly from `intervalIntegral.integral_nonneg`. -/
theorem intervalDomainClassicalL2DifferenceEnergy_nonneg
    (u v U V : ℝ → intervalDomain.Point → ℝ) (t : ℝ) :
    0 ≤ intervalDomainClassicalL2DifferenceEnergy u v U V t := by
  unfold intervalDomainClassicalL2DifferenceEnergy
  -- `intervalDomain.integral f = ∫ x in 0..1, intervalDomainLift f x`.
  show 0 ≤ intervalDomainIntegral
    (fun x => (u t x - U t x) ^ 2 + (v t x - V t x) ^ 2)
  unfold intervalDomainIntegral
  apply intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1)
  intro x _hx
  -- `intervalDomainLift` of a nonneg function is nonneg everywhere.
  unfold intervalDomainLift
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · simp only [hx, dif_pos]
    positivity
  · simp only [hx, dif_neg, not_false_iff, le_refl]

/-- **Grönwall step (proved in full).**  If `E` is continuous on `[s, t]`,
nonnegative, has a right derivative `E' τ` at every `τ ∈ [s, t)` bounded by
`E' τ ≤ K · E τ` with `0 ≤ K`, then `E t ≤ E s · exp (K (t - s))`.

This is the analytic heart of the L² energy uniqueness method; it is derived
honestly from Mathlib's `le_gronwallBound_of_liminf_deriv_right_le` with `ε = 0`,
for which `gronwallBound δ K 0 x = δ * exp (K * x)`. -/
theorem intervalDomainL2_gronwall_exp_of_diffIneq
    {E E' : ℝ → ℝ} {K s t : ℝ}
    (hst : s ≤ t)
    (hcont : ContinuousOn E (Set.Icc s t))
    (hderiv : ∀ τ ∈ Set.Ico s t, HasDerivWithinAt E (E' τ) (Set.Ici τ) τ)
    (hbound : ∀ τ ∈ Set.Ico s t, E' τ ≤ K * E τ) :
    E t ≤ E s * Real.exp (K * (t - s)) := by
  -- Apply Grönwall with δ = E s, ε = 0.
  have hgr :=
    le_gronwallBound_of_liminf_deriv_right_le (f := E) (f' := E')
      (δ := E s) (K := K) (ε := 0) (a := s) (b := t)
      hcont
      (fun τ hτ r hr => (hderiv τ hτ).liminf_right_slope_le hr)
      (le_refl (E s))
      (fun τ hτ => by simpa using hbound τ hτ)
      t ⟨hst, le_refl t⟩
  -- `gronwallBound (E s) K 0 (t - s) = E s * exp (K * (t - s))`.
  rwa [gronwallBound_ε0] at hgr

/-- `IntervalDomainSupNormDerivativeNonposOn` is antitone in its set argument:
shrinking the domain weakens the predicate. -/
theorem intervalDomainSupNormDerivativeNonposOn_mono
    {u : ℝ → intervalDomain.Point → ℝ} {I J : Set ℝ}
    (hsub : J ⊆ I)
    (h : IntervalDomainSupNormDerivativeNonposOn u I) :
    IntervalDomainSupNormDerivativeNonposOn u J where
  continuousOn := h.continuousOn.mono hsub
  differentiableOn :=
    h.differentiableOn.mono (interior_mono hsub)
  deriv_nonpos := fun t ht => h.deriv_nonpos t (interior_mono hsub ht)

/-- The interval-domain classical regularity predicate is monotone in the
horizon: regularity up to `T` implies regularity up to any `T' ≤ T`. -/
theorem intervalDomainClassicalRegularity_mono_horizon
    {T T' : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hTT' : T' ≤ T)
    (hreg : intervalDomain.classicalRegularity T u v) :
    intervalDomain.classicalRegularity T' u v := by
  have hreg' : intervalDomainClassicalRegularity T u v := hreg
  refine ⟨?_, ?_, ?_⟩
  · intro p hχ ha hb t₀ ht₀0 ht₀T' hsup
    exact hreg'.1 p hχ ha hb t₀ ht₀0 (lt_of_lt_of_le ht₀T' hTT') hsup
  · intro p hχ ha hb
    exact intervalDomainSupNormDerivativeNonposOn_mono
      (Set.Ioo_subset_Ioo_right hTT') (hreg'.2.1 p hχ ha hb)
  · intro t ht
    exact hreg'.2.2 t ⟨ht.1, lt_of_lt_of_le ht.2 hTT'⟩

/-- The named analytic frontier for the L² difference energy of two interval
classical solutions on a common horizon `T`.

This bundles exactly the PDE/regularity inputs that are NOT available from the
abstract `BoundedDomainData` interface, kept explicit instead of faked:

* `cont` — the L² energy is continuous on every `[s,t] ⊂ (0,T)`;
* `diffIneq` — the energy admits a right-derivative `Eprime` on `(0,T)` with the
  differential inequality `Eprime τ ≤ K · E τ` (this is the integrated energy
  identity + Neumann IBP + Lipschitz/boundedness bounds, the textbook step);
* `K_nonneg` — the Grönwall constant is nonnegative;
* `initial_vanishes` — the positive-time initial L² error tends to `0`
  (consequence of the common initial trace plus regularity);
* `zero_pointwise` — vanishing L² energy forces pointwise equality (the
  zero-`L²`-to-pointwise step under spatial regularity). -/
structure IntervalDomainL2DifferenceEnergyFrontier
    (p : CM2Params) (T : ℝ)
    (u v U V : ℝ → intervalDomain.Point → ℝ) where
  Eprime : ℝ → ℝ
  K : ℝ
  K_nonneg : 0 ≤ K
  cont :
    ∀ s t, 0 < s → s ≤ t → t < T →
      ContinuousOn
        (intervalDomainClassicalL2DifferenceEnergy u v U V) (Set.Icc s t)
  diffIneq :
    ∀ τ, 0 < τ → τ < T →
      HasDerivWithinAt
        (intervalDomainClassicalL2DifferenceEnergy u v U V) (Eprime τ)
        (Set.Ici τ) τ ∧
      Eprime τ ≤ K * intervalDomainClassicalL2DifferenceEnergy u v U V τ
  initial_vanishes :
    ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → s < T →
      intervalDomainClassicalL2DifferenceEnergy u v U V s < ε
  zero_pointwise :
    ∀ t, 0 < t → t < T →
      intervalDomainClassicalL2DifferenceEnergy u v U V t = 0 →
        ∀ x : intervalDomain.Point, u t x = U t x ∧ v t x = V t x

/-- Assemble the concrete overlap L² certificate from the analytic frontier.
The Grönwall (`l2_gronwall_from_positive_times`) and nonnegativity
(`l2_energy_nonneg`) fields are discharged here by genuine proofs. -/
def intervalDomainClassicalOverlapL2EnergyCertificate_of_diffIneqFrontier
    {p : CM2Params} {T : ℝ}
    {u v U V : ℝ → intervalDomain.Point → ℝ}
    (hsol_left : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hsol_right : IsPaper2ClassicalSolution intervalDomain p T U V)
    (hfront : IntervalDomainL2DifferenceEnergyFrontier p T u v U V) :
    IntervalDomainClassicalOverlapL2EnergyCertificate p T u v U V where
  left_solution := hsol_left
  right_solution := hsol_right
  l2_energy_nonneg := fun t _ _ =>
    intervalDomainClassicalL2DifferenceEnergy_nonneg u v U V t
  l2_gronwall_from_positive_times := by
    refine ⟨hfront.K, hfront.K_nonneg, ?_⟩
    intro s t hs0 hst htT
    -- Genuine Grönwall on [s, t], with E' := hfront.Eprime.
    refine intervalDomainL2_gronwall_exp_of_diffIneq (E' := hfront.Eprime) hst
      (hfront.cont s t hs0 hst htT) ?_ ?_
    · intro τ hτ
      have hτ0 : 0 < τ := lt_of_lt_of_le hs0 hτ.1
      have hτT : τ < T := lt_trans hτ.2 htT
      exact (hfront.diffIneq τ hτ0 hτT).1
    · intro τ hτ
      have hτ0 : 0 < τ := lt_of_lt_of_le hs0 hτ.1
      have hτT : τ < T := lt_trans hτ.2 htT
      exact (hfront.diffIneq τ hτ0 hτT).2
  l2_initial_error_vanishes := hfront.initial_vanishes
  l2_zero_controls_pointwise := hfront.zero_pointwise

/-- A per-pair frontier builder: for any two interval classical solutions with
the same initial `u`-trace, produce the L² difference energy frontier.  This is
the single remaining genuinely-upstream PDE obligation (see the file note). -/
structure IntervalDomainL2DifferenceEnergyFrontierBuilder
    (p : CM2Params) where
  frontier :
    ∀ {u₀ : intervalDomain.Point → ℝ} {T₁ T₂ : ℝ}
      {u₁ v₁ u₂ v₂ : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
      IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
      InitialTrace intervalDomain u₀ u₁ →
      InitialTrace intervalDomain u₀ u₂ →
        IntervalDomainL2DifferenceEnergyFrontier
          p (min T₁ T₂) u₁ v₁ u₂ v₂

/-- The L² energy-method uniqueness instance, built from the frontier builder.
Everything except the frontier itself is discharged by the proofs above. -/
def intervalDomainClassicalUniquenessL2EnergyMethod_of_frontier
    {p : CM2Params}
    (hbuilder : IntervalDomainL2DifferenceEnergyFrontierBuilder p) :
    IntervalDomainClassicalUniquenessL2EnergyMethod p where
  certificate := by
    intro u₀ T₁ T₂ u₁ v₁ u₂ v₂ hsol₁ hsol₂ htr₁ htr₂
    -- Restrict each solution to the overlap horizon `min T₁ T₂`.
    have hsol₁' :
        IsPaper2ClassicalSolution intervalDomain p (min T₁ T₂) u₁ v₁ := by
      refine ⟨lt_min hsol₁.T_pos hsol₂.T_pos, ?_, ?_, ?_, ?_, ?_⟩
      · exact intervalDomainClassicalRegularity_mono_horizon
          (min_le_left _ _) hsol₁.regularity
      · exact fun t x ht0 htT hx =>
          hsol₁.u_pos ht0 (lt_of_lt_of_le htT (min_le_left _ _)) hx
      · exact fun t x ht0 htT hx =>
          hsol₁.pde_u ht0 (lt_of_lt_of_le htT (min_le_left _ _)) hx
      · exact fun t x ht0 htT hx =>
          hsol₁.pde_v ht0 (lt_of_lt_of_le htT (min_le_left _ _)) hx
      · exact fun t x ht0 htT hx =>
          hsol₁.neumann ht0 (lt_of_lt_of_le htT (min_le_left _ _)) hx
    have hsol₂' :
        IsPaper2ClassicalSolution intervalDomain p (min T₁ T₂) u₂ v₂ := by
      refine ⟨lt_min hsol₁.T_pos hsol₂.T_pos, ?_, ?_, ?_, ?_, ?_⟩
      · exact intervalDomainClassicalRegularity_mono_horizon
          (min_le_right _ _) hsol₂.regularity
      · exact fun t x ht0 htT hx =>
          hsol₂.u_pos ht0 (lt_of_lt_of_le htT (min_le_right _ _)) hx
      · exact fun t x ht0 htT hx =>
          hsol₂.pde_u ht0 (lt_of_lt_of_le htT (min_le_right _ _)) hx
      · exact fun t x ht0 htT hx =>
          hsol₂.pde_v ht0 (lt_of_lt_of_le htT (min_le_right _ _)) hx
      · exact fun t x ht0 htT hx =>
          hsol₂.neumann ht0 (lt_of_lt_of_le htT (min_le_right _ _)) hx
    exact
      intervalDomainClassicalOverlapL2EnergyCertificate_of_diffIneqFrontier
        hsol₁' hsol₂'
        (hbuilder.frontier hsol₁ hsol₂ htr₁ htr₂)

/-- **Concrete instance, modulo the single named PDE frontier.**

`intervalDomainClassicalUniquenessL2EnergyMethod_concrete` produces the full
`IntervalDomainClassicalUniquenessL2EnergyMethod p` instance from a
`IntervalDomainL2DifferenceEnergyFrontierBuilder p`.  The Grönwall, energy
nonnegativity, and assembly steps are fully proved; the frontier builder is the
exact remaining upstream analytic input (PDE energy identity + Neumann IBP +
Lipschitz bounds), documented honestly rather than admitted as a `sorry`. -/
theorem intervalDomainClassicalUniquenessL2EnergyMethod_concrete
    (p : CM2Params)
    (hbuilder : IntervalDomainL2DifferenceEnergyFrontierBuilder p) :
    IntervalDomainClassicalUniquenessL2EnergyMethod p :=
  intervalDomainClassicalUniquenessL2EnergyMethod_of_frontier hbuilder

/-!
## Status note (honest gap report)

* **Fully proved here (no `sorry`/`axiom`):**
  - `intervalDomainClassicalL2DifferenceEnergy_nonneg`: the L² difference energy
    is `≥ 0`.
  - `intervalDomainL2_gronwall_exp_of_diffIneq`: the Grönwall exponential bound
    `E t ≤ E s · exp (K (t-s))` from the differential inequality `E' ≤ K·E`,
    via Mathlib `le_gronwallBound_of_liminf_deriv_right_le`.
  - The assembly of all four certificate fields and the overlap-horizon
    restriction of the two solutions.

* **Single remaining genuinely-upstream obligation:** constructing a
  `IntervalDomainL2DifferenceEnergyFrontierBuilder p`, i.e. deriving the
  `diffIneq`/`cont`/`initial_vanishes`/`zero_pointwise` fields directly from
  `IsPaper2ClassicalSolution`.  This is blocked by the *same* regularity gap as
  the whole `IntervalDomainEnergyStep` `_of_frontiers` family: the abstract
  `intervalDomainClassicalRegularity` constrains only the time monotonicity of
  the sup norm, providing neither the spatial `C²` regularity needed for the
  Neumann integration-by-parts `∫ w·Δw = -∫|∂ₓw|²` nor the joint regularity
  needed to differentiate `E(t) = ∫ w² + z²` under the integral (Leibniz).
  Supplying that regularity strengthening is a separate analytic task; once it
  exists, `intervalDomainClassicalUniquenessL2EnergyMethod_concrete` closes the
  gluing step with no further changes.
-/

end

end ShenWork.Paper2
