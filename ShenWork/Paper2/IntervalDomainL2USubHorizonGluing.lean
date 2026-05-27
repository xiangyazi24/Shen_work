/-
  Sub-horizon gluing closure: discharging the explicit `hlower` in the general
  γ>0 case from `IntervalDomainPosDatumLowerBound` via a PER-SUB-HORIZON
  uniform two-sided lift bound.

  ## Why this file exists

  `GlobalSolutionGluingFromReachability_of_regimeAndLowerBound`
  (`IntervalDomainL2UEnergyUniform`) closes the general γ>0 gluing modulo an
  explicit hypothesis `hlower`: a SINGLE positive δ > 0 uniform on the entire
  open overlap interior `(0, min T₁ T₂)`.  The textbook positive-datum input
  `IntervalDomainPosDatumLowerBound u₀` (`IntervalDomainL2StaticVDifference`)
  produces, via the half-horizon lemma `lift_u_uniformPositive_on_halfHorizon`,
  uniform δ_t > 0 on every closed sub-horizon `(0, t]` with `t < min T₁ T₂`,
  but a single δ uniform on the full open `(0, min T₁ T₂)` would require
  ruling out solutions decaying to 0 at the temporal frontier — a stronger
  maximum-principle output than what we have available without further
  hypotheses.

  ## What this file does

  Adds a PARALLEL sub-horizon variant of the existing chain that consumes the
  half-horizon-style per-sub-horizon `(δ_t, M_t)` and produces
  `IntervalDomainClassicalUniquenessL2EnergyMethod p` directly.  For each
  fixed target time `t < min T₁ T₂`, we pick a strict sub-horizon threshold
  `T' = (t + min T₁ T₂)/2 ∈ (t, min T₁ T₂)`, restrict each original solution
  to horizon `T'` via `IsPaper2ClassicalSolution.restrict_horizon`, and read
  off the uniform two-sided lift bound on `(0, T']` for this specific pair.
  Per-pair application of the EXISTING `u`-only chain — specifically
  `gronwall_const_of_uniformLiftBound` + the unconditional frontier
  `intervalDomainL2UDifferenceEnergyFrontier_of_solution` + the certificate
  `intervalDomainClassicalOverlapL2UEnergyCertificate_of_diffIneqFrontier` —
  yields overlap equality on `(0, min T' T') = (0, T')`, in particular at the
  original `t`.  Collecting over `t` produces overlap equality on the FULL
  `(0, min T₁ T₂)`, which is exactly the content of a joint L²-energy method
  certificate (the joint energy is identically zero, so its Grönwall /
  initial-vanishing fields are discharged trivially).

  The existing single-K certificate / frontier / boundedness chain is left
  untouched; this file is purely additive.

  No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainL2UEnergyUniform
import ShenWork.Paper2.IntervalDomainL2StaticVDifference

open MeasureTheory intervalIntegral
open ShenWork.IntervalDomain
open scoped Topology BigOperators

namespace ShenWork.Paper2

noncomputable section

/-- **Truncation of an `IsPaper2ClassicalSolution` to a smaller horizon.**
Each conjunct is monotone in the horizon: regularity via
`intervalDomainClassicalRegularity_mono_horizon`, the pointwise positivity /
nonnegativity / PDE / Neumann conditions by horizon monotonicity in the time
quantifier. -/
theorem IsPaper2ClassicalSolution.restrict_horizon
    {p : CM2Params} {T T' : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hT'_pos : 0 < T') (hT'_le : T' ≤ T) :
    IsPaper2ClassicalSolution intervalDomain p T' u v := by
  refine ⟨hT'_pos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact intervalDomainClassicalRegularity_mono_horizon hT'_le hsol.regularity
  · exact fun t x ht0 htT' => hsol.u_pos' ht0 (lt_of_lt_of_le htT' hT'_le)
  · exact fun t x ht0 htT' => hsol.v_nonneg ht0 (lt_of_lt_of_le htT' hT'_le)
  · exact fun t x ht0 htT' hx => hsol.pde_u ht0 (lt_of_lt_of_le htT' hT'_le) hx
  · exact fun t x ht0 htT' hx => hsol.pde_v ht0 (lt_of_lt_of_le htT' hT'_le) hx
  · exact fun t x ht0 htT' hx => hsol.neumann ht0 (lt_of_lt_of_le htT' hT'_le) hx

/-! ## The per-sub-horizon uniform lift bound -/

/-- **Per-sub-horizon uniform two-sided lift bound datum.**

For every solution pair sharing an initial trace AND every sub-horizon
threshold `T' < min T₁ T₂`, the lifts stay in a fixed `[δ_{T'}, M_{T'}]`
(δ_{T'}>0) on `[0,1]` over the closed sub-horizon `(0, T']`.  The bounds
are allowed to depend on `T'`: this is precisely the relaxation that lets
the half-horizon lemma supply them from
`IntervalDomainPosDatumLowerBound` without needing a strong-maximum-principle
endpoint argument at the temporal frontier `min T₁ T₂`. -/
structure IntervalDomainSubHorizonUniformLiftBound (p : CM2Params) : Prop where
  bound :
    ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
      {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
      IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
      InitialTrace intervalDomain u₀ u₁ →
      InitialTrace intervalDomain u₀ u₂ →
        ∀ T', 0 < T' → T' < min T₁ T₂ →
          ∃ δ M : ℝ, 0 < δ ∧ ∀ τ, 0 < τ → τ ≤ T' →
            (∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₁ τ) x ∈ Set.Icc δ M) ∧
            (∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₂ τ) x ∈ Set.Icc δ M)

/-! ## Per-pair sub-horizon overlap equality

For each specific solution pair and each fixed target time `t` in the overlap
interior, we directly invoke the proven `u`-only chain on a truncated horizon
`T'` that strictly contains `t`.  All ingredients are already proven:

* `gronwall_const_of_uniformLiftBound` (`IntervalDomainL2UEnergyUniform`) —
  per-pair uniform Grönwall constant from a per-pair uniform two-sided lift
  bound;
* `intervalDomainL2UDifferenceEnergyFrontier_of_solution`
  (`IntervalDomainL2UFrontierAssembly`) — unconditional frontier assembly
  from a per-pair Kunif (and a bounded shared initial datum);
* `intervalDomainClassicalOverlapL2UEnergyCertificate_of_diffIneqFrontier`
  (`IntervalDomainL2UEnergy`) — certificate from frontier;
* `intervalDomain_classicalSolution_overlap_unique_of_l2UEnergyCertificate`
  (`IntervalDomainL2UEnergy`) — overlap uniqueness from the certificate.

No structural hypothesis (`IntervalDomainL2UBoundednessHypothesis`,
`IntervalDomainUniformLiftBound`) is needed; the per-pair chain is invoked
directly. -/

/-- **Per-pair overlap equality on the open `(0, min T₁ T₂)` from
per-sub-horizon datum + bounded datum.**

For a specific solution pair sharing an initial trace, with the
per-sub-horizon uniform two-sided lift bound and the shared initial datum
bounded, overlap equality `u₁ t x = u₂ t x ∧ v₁ t x = v₂ t x` holds for every
`t ∈ (0, min T₁ T₂)` and every `x : intervalDomainPoint`. -/
theorem intervalDomain_classicalSolution_overlap_unique_of_subHorizonBound
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    (htr₁ : InitialTrace intervalDomain u₀ u₁)
    (htr₂ : InitialTrace intervalDomain u₀ u₂)
    (hbdd₀ : BddAbove (Set.range (fun x : intervalDomainPoint => |u₀ x|)))
    (hbnd :
      ∀ T', 0 < T' → T' < min T₁ T₂ →
        ∃ δ M : ℝ, 0 < δ ∧ ∀ τ, 0 < τ → τ ≤ T' →
          (∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₁ τ) x ∈ Set.Icc δ M) ∧
          (∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₂ τ) x ∈ Set.Icc δ M)) :
    ∀ t, 0 < t → t < min T₁ T₂ →
      ∀ x : intervalDomainPoint, u₁ t x = u₂ t x ∧ v₁ t x = v₂ t x := by
  classical
  intro t ht0 htTm
  -- Strict sub-horizon threshold `T' := (t + min T₁ T₂) / 2`.
  set Tm : ℝ := min T₁ T₂ with hTm
  set T' : ℝ := (t + Tm) / 2 with hT'def
  have hT'_pos : 0 < T' := by rw [hT'def]; linarith
  have ht_lt_T' : t < T' := by rw [hT'def]; linarith
  have hT'_lt_Tm : T' < Tm := by rw [hT'def]; linarith
  have hT'_le_T₁ : T' ≤ T₁ := le_of_lt (lt_of_lt_of_le hT'_lt_Tm (min_le_left _ _))
  have hT'_le_T₂ : T' ≤ T₂ := le_of_lt (lt_of_lt_of_le hT'_lt_Tm (min_le_right _ _))
  -- Restrict each original solution to horizon `T'`.
  have hsol₁_T' : IsPaper2ClassicalSolution intervalDomain p T' u₁ v₁ :=
    hsol₁.restrict_horizon hT'_pos hT'_le_T₁
  have hsol₂_T' : IsPaper2ClassicalSolution intervalDomain p T' u₂ v₂ :=
    hsol₂.restrict_horizon hT'_pos hT'_le_T₂
  -- The per-sub-horizon datum at `T'`.
  obtain ⟨δ_T', M_T', hδ_T'_pos, hbnd_T'⟩ := hbnd T' hT'_pos hT'_lt_Tm
  -- Translate the per-sub-horizon datum on `(0, T']` to the open interval
  -- `(0, min T' T') = (0, T')` needed by `gronwall_const_of_uniformLiftBound`.
  have hbnd_open :
      ∀ τ, 0 < τ → τ < min T' T' →
        (∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₁ τ) x ∈ Set.Icc δ_T' M_T') ∧
        (∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₂ τ) x ∈ Set.Icc δ_T' M_T') := by
    intro τ hτ0 hτmin
    have hτ_lt_T' : τ < T' := by rw [min_self] at hτmin; exact hτmin
    have hτ_le_T' : τ ≤ T' := le_of_lt hτ_lt_T'
    exact hbnd_T' τ hτ0 hτ_le_T'
  -- Per-pair uniform Grönwall constant `K` on `(0, T')`.
  have hKunif :
      ∃ K : ℝ, 0 ≤ K ∧ ∀ τ, 0 < τ → τ < min T' T' →
        (∫ y in (0:ℝ)..1, intervalDomainUEnergyIntegrandDeriv u₁ u₂ τ y)
          ≤ K * intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ :=
    gronwall_const_of_uniformLiftBound hsol₁_T' hsol₂_T' hδ_T'_pos hbnd_open
  -- Unconditional `u`-only frontier on `min T' T' = T'`.
  have hfront :=
    intervalDomainL2UDifferenceEnergyFrontier_of_solution
      hsol₁_T' hsol₂_T' htr₁ htr₂ hbdd₀ hKunif
  -- The corresponding overlap certificate.  The frontier is indexed by
  -- `min T' T'`; restrict each `T'`-solution to that same `min T' T'` horizon
  -- (which equals `T'`) so the certificate-builder's solution-horizon constraints
  -- type-match.
  have hminT'T' : min T' T' = T' := min_self T'
  have hsol₁_minT' :
      IsPaper2ClassicalSolution intervalDomain p (min T' T') u₁ v₁ := by
    rw [hminT'T']; exact hsol₁_T'
  have hsol₂_minT' :
      IsPaper2ClassicalSolution intervalDomain p (min T' T') u₂ v₂ := by
    rw [hminT'T']; exact hsol₂_T'
  have hcert :
      IntervalDomainClassicalOverlapL2UEnergyCertificate
        p (min T' T') u₁ v₁ u₂ v₂ :=
    intervalDomainClassicalOverlapL2UEnergyCertificate_of_diffIneqFrontier
      hsol₁_minT' hsol₂_minT' hfront
  -- Apply `intervalDomain_classicalSolution_overlap_unique_of_l2UEnergyCertificate`
  -- at our target time `t`.  We need `0 < t` and `t < min T' T' = T'`.
  have hcert_unique :
      ∀ s, 0 < s → s < min T' T' →
        ∀ x : intervalDomainPoint, u₁ s x = u₂ s x ∧ v₁ s x = v₂ s x :=
    intervalDomain_classicalSolution_overlap_unique_of_l2UEnergyCertificate hcert
  intro x
  have ht_lt_minT' : t < min T' T' := by rw [min_self]; exact ht_lt_T'
  exact hcert_unique t ht0 ht_lt_minT' x

/-- **L²-energy method from the per-sub-horizon uniform lift bound + bounded
shared initial datum.**

For each pair sharing an initial trace, we build a JOINT L²-energy overlap
certificate on horizon `min T₁ T₂` whose `l2_zero_controls_pointwise` is
supplied by the per-target-time reduction.  The Grönwall and
initial-vanishing fields are trivially discharged: under the established
pointwise equality the joint energy is identically zero on positive times. -/
def intervalDomainClassicalUniquenessL2EnergyMethod_of_subHorizonUniformBound
    {p : CM2Params}
    (hbnd : IntervalDomainSubHorizonUniformLiftBound p)
    (hdatum :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          BddAbove (Set.range (fun x : intervalDomainPoint => |u₀ x|))) :
    IntervalDomainClassicalUniquenessL2EnergyMethod p where
  certificate := by
    classical
    intro u₀ T₁ T₂ u₁ v₁ u₂ v₂ hsol₁ hsol₂ htr₁ htr₂
    set Tm : ℝ := min T₁ T₂ with hTm
    have hTm_pos : 0 < Tm := lt_min hsol₁.T_pos hsol₂.T_pos
    have hsol₁' : IsPaper2ClassicalSolution intervalDomain p Tm u₁ v₁ :=
      hsol₁.restrict_horizon hTm_pos (min_le_left _ _)
    have hsol₂' : IsPaper2ClassicalSolution intervalDomain p Tm u₂ v₂ :=
      hsol₂.restrict_horizon hTm_pos (min_le_right _ _)
    have hbdd₀ : BddAbove (Set.range (fun x : intervalDomainPoint => |u₀ x|)) :=
      hdatum hsol₁ hsol₂ htr₁ htr₂
    have hoverlap :
        ∀ t, 0 < t → t < Tm →
          ∀ x : intervalDomainPoint, u₁ t x = u₂ t x ∧ v₁ t x = v₂ t x :=
      intervalDomain_classicalSolution_overlap_unique_of_subHorizonBound
        hsol₁ hsol₂ htr₁ htr₂ hbdd₀
        (hbnd.bound hsol₁ hsol₂ htr₁ htr₂)
    refine
      { left_solution := hsol₁'
        right_solution := hsol₂'
        l2_energy_nonneg := fun t _ _ =>
          intervalDomainClassicalL2DifferenceEnergy_nonneg u₁ v₁ u₂ v₂ t
        l2_gronwall_from_positive_times := ?_
        l2_initial_error_vanishes := ?_
        l2_zero_controls_pointwise := fun t ht0 htT _ x =>
          hoverlap t ht0 htT x }
    · refine ⟨0, le_refl 0, ?_⟩
      intro s t hs0 hst htT
      have hEt0 :
          intervalDomainClassicalL2DifferenceEnergy u₁ v₁ u₂ v₂ t = 0 := by
        unfold intervalDomainClassicalL2DifferenceEnergy
        have : (fun x => (u₁ t x - u₂ t x) ^ 2 + (v₁ t x - v₂ t x) ^ 2)
            = fun _ => (0 : ℝ) := by
          funext x
          obtain ⟨hu, hv⟩ :=
            hoverlap t (lt_of_lt_of_le hs0 hst) htT x
          rw [hu, hv]; ring
        rw [this]
        show intervalDomainIntegral (fun _ => (0 : ℝ)) = 0
        unfold intervalDomainIntegral intervalDomainLift
        simp
      have hEs_nn :
          0 ≤ intervalDomainClassicalL2DifferenceEnergy u₁ v₁ u₂ v₂ s :=
        intervalDomainClassicalL2DifferenceEnergy_nonneg u₁ v₁ u₂ v₂ s
      rw [hEt0]
      positivity
    · intro ε hε
      refine ⟨1, by norm_num, ?_⟩
      intro s hs0 _ hsT
      have hEs0 :
          intervalDomainClassicalL2DifferenceEnergy u₁ v₁ u₂ v₂ s = 0 := by
        unfold intervalDomainClassicalL2DifferenceEnergy
        have : (fun x => (u₁ s x - u₂ s x) ^ 2 + (v₁ s x - v₂ s x) ^ 2)
            = fun _ => (0 : ℝ) := by
          funext x
          obtain ⟨hu, hv⟩ := hoverlap s hs0 hsT x
          rw [hu, hv]; ring
        rw [this]
        show intervalDomainIntegral (fun _ => (0 : ℝ)) = 0
        unfold intervalDomainIntegral intervalDomainLift
        simp
      rw [hEs0]; exact hε

/-- **Global-solution gluing from reachability, reduced to the per-sub-horizon
uniform lift bound + bounded shared initial datum.**

The full gluing theorem holds given `IntervalDomainSubHorizonUniformLiftBound p`
(a per-sub-horizon uniform two-sided lift bound, allowing the bounds to depend
on the sub-horizon threshold) plus the bounded shared initial datum.  This is
the structural API into which the regime + positive-datum-lower-bound chain
plugs (next theorem). -/
theorem GlobalSolutionGluingFromReachability_of_subHorizonUniformBound
    (p : CM2Params)
    (hbnd : IntervalDomainSubHorizonUniformLiftBound p)
    (hdatum :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          BddAbove (Set.range (fun x : intervalDomainPoint => |u₀ x|))) :
    ShenWork.IntervalDomainExistence.GlobalSolutionGluingFromReachability p :=
  ShenWork.IntervalDomainExistence.GlobalSolutionGluingFromReachability_of_l2EnergyMethod
    (intervalDomainClassicalUniquenessL2EnergyMethod_of_subHorizonUniformBound
      hbnd hdatum)

/-! ## Discharge of the per-sub-horizon datum from regime + positive-datum
lower bound

Combining `lift_u_uniformPositive_on_halfHorizon`
(`IntervalDomainL2StaticVDifference`) for the per-sub-horizon δ_t > 0 with
`uniform_lift_upper_bound_of_regime` (`IntervalDomainL2UEnergyUniform`) for
the τ-independent upper bound `M = max(supNorm u₀, (a/b)^{1/α})`, the
per-sub-horizon datum reduces to the SHARED `IntervalDomainPosDatumLowerBound`
(plus regime + positive initial datum). -/

/-- **Per-sub-horizon uniform two-sided lift bound from the Theorem-1.1
regime + positive bounded datum + uniform datum lower bound.**

Under the regime (`χ₀ ≤ 0`, `0 < a`, `0 < b`), for each pair of solutions
sharing an initial trace with a positive bounded datum `u₀` admitting a
uniform positive lower bound (`IntervalDomainPosDatumLowerBound`), the
per-sub-horizon uniform two-sided lift bound holds:

* the δ_{T'} > 0 lower bound is supplied by
  `lift_u_uniformPositive_on_halfHorizon` (which delivers a uniform δ on
  `(0, T']` from the positive-datum lower bound + initial trace +
  admissibility);
* the M upper bound is the τ-INDEPENDENT
  `M = max (supNorm u₀, (a/b)^{1/α})` from
  `uniform_lift_upper_bound_of_regime` (regime-conditional, but valid on the
  full open horizon, not just on `(0, T']`).

The two are combined to produce the closed-sub-horizon `Set.Icc δ_{T'} M`
membership. -/
theorem subHorizonUniformLiftBound_of_regimeAndPosDatumLowerBound
    (p : CM2Params)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hpos :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          PositiveInitialDatum intervalDomain u₀)
    (hposLower :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          IntervalDomainPosDatumLowerBound u₀) :
    IntervalDomainSubHorizonUniformLiftBound p where
  bound := by
    intro u₀ T₁ T₂ u₁ v₁ u₂ v₂ hsol₁ hsol₂ htr₁ htr₂ T' hT'_pos hT'_lt_Tm
    have hT'_lt_T₁ : T' < T₁ := lt_of_lt_of_le hT'_lt_Tm (min_le_left _ _)
    have hT'_lt_T₂ : T' < T₂ := lt_of_lt_of_le hT'_lt_Tm (min_le_right _ _)
    have hu₀ : PositiveInitialDatum intervalDomain u₀ := hpos hsol₁ hsol₂ htr₁ htr₂
    have hu₀_adm : intervalDomain.initialAdmissible u₀ := hu₀.admissible
    have hbddu₀ : BddAbove (Set.range (fun x : intervalDomainPoint => |u₀ x|)) :=
      hu₀_adm
    have hPosLow : IntervalDomainPosDatumLowerBound u₀ :=
      hposLower hsol₁ hsol₂ htr₁ htr₂
    -- Half-horizon uniform lower bound for `u₁` on `(0, T']`.
    obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ :=
      lift_u_uniformPositive_on_halfHorizon
        hsol₁ htr₁ hPosLow hu₀_adm hT'_pos hT'_lt_T₁
    -- Half-horizon uniform lower bound for `u₂` on `(0, T']`.
    obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ :=
      lift_u_uniformPositive_on_halfHorizon
        hsol₂ htr₂ hPosLow hu₀_adm hT'_pos hT'_lt_T₂
    -- Uniform UPPER bound `M` from the regime (τ-independent).
    set M : ℝ := max (intervalDomainSupNorm u₀) ((p.a / p.b) ^ (1 / p.α)) with hMdef
    have hub₁ :=
      uniform_lift_upper_bound_of_regime p hχ ha hb hu₀ hbddu₀ hsol₁.T_pos hsol₁ htr₁
    have hub₂ :=
      uniform_lift_upper_bound_of_regime p hχ ha hb hu₀ hbddu₀ hsol₂.T_pos hsol₂ htr₂
    -- Combine: take δ := min δ₁ δ₂ > 0 and the shared `M`.
    refine ⟨min δ₁ δ₂, M, lt_min hδ₁_pos hδ₂_pos, ?_⟩
    intro τ hτ_pos hτ_le_T'
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · -- `u₁` membership.
      have hτ_lt_T₁ : τ < T₁ :=
        lt_of_le_of_lt hτ_le_T' hT'_lt_T₁
      have hlo : min δ₁ δ₂ ≤ intervalDomainLift (u₁ τ) x :=
        le_trans (min_le_left _ _) (hδ₁ τ hτ_pos hτ_le_T' x hx)
      have hup : intervalDomainLift (u₁ τ) x ≤ M :=
        (hub₁ τ hτ_pos hτ_lt_T₁ x hx).2
      exact ⟨hlo, hup⟩
    · -- `u₂` membership.
      have hτ_lt_T₂ : τ < T₂ :=
        lt_of_le_of_lt hτ_le_T' hT'_lt_T₂
      have hlo : min δ₁ δ₂ ≤ intervalDomainLift (u₂ τ) x :=
        le_trans (min_le_right _ _) (hδ₂ τ hτ_pos hτ_le_T' x hx)
      have hup : intervalDomainLift (u₂ τ) x ≤ M :=
        (hub₂ τ hτ_pos hτ_lt_T₂ x hx).2
      exact ⟨hlo, hup⟩

/-- **Global-solution gluing from reachability, fully closed for general
γ>0 from the regime + positive datum + positive-datum uniform lower bound.**

Under the Theorem-1.1 negative-sensitivity regime (`χ₀ ≤ 0`, `0 < a`, `0 < b`)
and the textbook positive-datum strengthening
`IntervalDomainPosDatumLowerBound` (a *uniform* positive lower bound on `u₀`
itself, not merely pointwise positivity), the full gluing theorem holds for
GENERAL `γ > 0` — no `γ ≥ 1` collapse and no ad-hoc per-pair `hlower`
assumption.

Datum-boundedness is folded into the strengthened `initialAdmissible`
(`BddAbove (range |·|)`), so `hpos.admissible` directly supplies it.  The
uniform δ on the *open* `(0, min T₁ T₂)` is NEVER required: the proof
splits each fixed target time into a strict sub-horizon `T'` and uses the
half-horizon δ_{T'} > 0, which the `IntervalDomainPosDatumLowerBound` input
genuinely supplies. -/
theorem GlobalSolutionGluingFromReachability_of_regimeAndPosDatumLowerBound
    (p : CM2Params)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hpos :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          PositiveInitialDatum intervalDomain u₀)
    (hposLower :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          IntervalDomainPosDatumLowerBound u₀) :
    ShenWork.IntervalDomainExistence.GlobalSolutionGluingFromReachability p :=
  GlobalSolutionGluingFromReachability_of_subHorizonUniformBound p
    (subHorizonUniformLiftBound_of_regimeAndPosDatumLowerBound
      p hχ ha hb hpos hposLower)
    (fun hsol₁ hsol₂ htr₁ htr₂ => (hpos hsol₁ hsol₂ htr₁ htr₂).admissible)

end

end ShenWork.Paper2
