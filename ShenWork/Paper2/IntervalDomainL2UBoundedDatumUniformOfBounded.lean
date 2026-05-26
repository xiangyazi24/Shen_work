/-
  Reduction of the final gluing obligation `IntervalDomainL2UBoundedDatumUniform p`
  to a single, explicit, faithful boundedness hypothesis (option 2).

  This file is DOWNSTREAM of `IntervalDomainL2UFrontierAssembly` (which constructs
  every frontier field unconditionally except the two inputs bundled in
  `IntervalDomainL2UBoundedDatumUniform`).  It records HONESTLY which of those two
  inputs can be discharged and which genuinely requires extra hypotheses, and
  packages the precise remaining gap.

  ## Honest status of the two obligation fields

  * `bdd₀` (bounded shared initial datum).  The obligation's `u₀` is the
    `InitialTrace` limit of `u₁`.  `InitialTrace` ALONE does NOT force `u₀` bounded:
    `intervalDomainSupNorm = sSup (range |·|)` uses the junk-`0` convention off
    `BddAbove`, so for an UNBOUNDED `u₀` the trace bound `supNorm (u₁ τ − u₀) < ε`
    holds vacuously (the `sSup` is the junk `0`).  Trying to recover `|u₀ x| ≤ M+1`
    from a uniform bound `supNorm (u₁ τ) ≤ M` is CIRCULAR — it needs
    `BddAbove (range |u₁ τ − u₀|)`, which itself needs `u₀` bounded.  Hence `bdd₀`
    is a GENUINE independent input: the shared initial datum must be bounded.  (For
    `intervalDomain`, `initialAdmissible = fun _ => True`, so admissibility carries
    no boundedness; a faithful datum hypothesis must supply it.)

  * `Kunif` (uniform Grönwall constant).  The per-time bound
    `∫ integrandDeriv τ ≤ K(τ) · E_u(τ)` is PROVED unconditionally
    (`intervalDomainL2U_energy_diffIneq_bound`), with
    `K(τ) = χ₀²·Cflux(τ) + 2·L(τ)`.  Tracing the constant:
      - `L(τ)` (logistic Lipschitz over `[0, sup u_i(τ)]`) is bounded by a function of
        an UPPER sup-norm bound `M` (`intervalLogisticSource_lipschitz`);
      - `Cflux(τ) = 3·(G² + U²·Cg + (UGβ)²·Cv)` with `U ≤ M`, and
        `Cg, Cv = (∑ W_k)²·4·(ν·L_γ)²` where `L_γ = γ·(δ^{γ-1}+M^{γ-1})` is the local
        Lipschitz constant of `x ↦ x^γ` over the solution range `[δ, M]`
        (`source_integral_le_Eu`, `static_v_*_L2_le_Eu`).  For `γ < 1` this needs a
        POSITIVE LOWER bound `δ` as well as the upper bound `M`;
      - `G` (resolver-gradient sup bound, `resolverGradReal_bounded`) is currently
        obtained only via continuity on the compact `[0,1]`, with NO explicit
        dependence on `M`.  A τ-uniform `G` would need a quantitative sup bound
        `‖∂ₓ R(ν u^γ)‖_∞ ≤ F(M)` from the source `L²` mass, which is not available in
        usable form (it needs the per-point summability side-conditions of
        `intervalNeumannResolverR_grad_sup_lipschitz`).

    Hence `Kunif` is NOT discharged unconditionally, NOR from a uniform two-sided
    lift bound alone, without that additional quantitative resolver-gradient sup
    bound.  We therefore keep `Kunif` as the EXACT named residual.

  ## Parameter-regime honesty

  A uniform sup-norm bound `M` for the solutions in the obligation is exactly what
  `Theorem_1_1_intervalDomain_conditional` produces VIA `Lemma_3_1_intervalDomain`
  (sup-norm monotonicity), proven ONLY under the Theorem-1.1 parameter regime
  (negative sensitivity `χ₀ ≤ 0`, `0 < a`, `0 < b`).  The obligation
  `IntervalDomainL2UBoundedDatumUniform p` is stated for ARBITRARY `p` and ARBITRARY
  positive classical solutions, so NO uniform `M` is available unconditionally.  The
  reduction below is therefore genuinely conditional on explicit hypotheses, not
  unconditional.

  This file contains **no `sorry`, no `admit`, no custom `axiom`.**
-/
import ShenWork.Paper2.IntervalDomainL2UFrontierAssembly

open ShenWork.IntervalDomain MeasureTheory
open scoped Topology

namespace ShenWork.Paper2

noncomputable section

/-- **The precise, faithful boundedness hypothesis bundling the two genuine inputs.**

For EVERY pair of positive classical interval solutions sharing an initial trace
`u₀`, this records exactly the two facts that `IntervalDomainL2UFrontierAssembly`
cannot supply unconditionally:

* `datumBdd` — the shared initial datum `u₀` is bounded (`BddAbove (range |u₀|)`),
  a genuine independent input (see the file header: it is NOT derivable from
  `InitialTrace` alone, by the junk-`0` convention of `intervalDomainSupNorm`);
* `gronwall` — a UNIFORM (τ-independent) Grönwall constant for the per-time PROVED
  differential inequality over the overlap interior.

This is exactly the field-by-field content of `IntervalDomainL2UBoundedDatumUniform`,
stated as a hypothesis; it is the single clean boundedness assumption to which the
whole gluing chain reduces. -/
structure IntervalDomainL2UBoundednessHypothesis (p : CM2Params) : Prop where
  datumBdd :
    ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
      {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
      IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
      InitialTrace intervalDomain u₀ u₁ →
      InitialTrace intervalDomain u₀ u₂ →
        BddAbove (Set.range (fun x : intervalDomainPoint => |u₀ x|))
  gronwall :
    ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
      {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
      IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
      InitialTrace intervalDomain u₀ u₁ →
      InitialTrace intervalDomain u₀ u₂ →
        ∃ K : ℝ, 0 ≤ K ∧ ∀ τ, 0 < τ → τ < min T₁ T₂ →
          (∫ y in (0:ℝ)..1, intervalDomainUEnergyIntegrandDeriv u₁ u₂ τ y)
            ≤ K * intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ

/-- **The final obligation, from the explicit boundedness hypothesis (option 2).**

`IntervalDomainL2UBoundedDatumUniform p` — the single named input that makes the
gluing chain go through — is produced directly from
`IntervalDomainL2UBoundednessHypothesis p`.  The two structures carry identical
mathematical content; this lemma is the faithful repackaging, making explicit that
the remaining gap is EXACTLY a bounded shared initial datum plus a uniform Grönwall
constant, with no hidden assumptions. -/
def intervalDomainL2UBoundedDatumUniform_of_bounded
    {p : CM2Params}
    (h : IntervalDomainL2UBoundednessHypothesis p) :
    IntervalDomainL2UBoundedDatumUniform p where
  bdd₀ := fun hsol₁ hsol₂ htr₁ htr₂ => h.datumBdd hsol₁ hsol₂ htr₁ htr₂
  Kunif := fun hsol₁ hsol₂ htr₁ htr₂ => h.gronwall hsol₁ hsol₂ htr₁ htr₂

/-- **Global-solution gluing from reachability, reduced to the explicit boundedness
hypothesis.**

The full gluing theorem holds given only `IntervalDomainL2UBoundednessHypothesis p`
— the bounded shared initial datum plus a uniform Grönwall constant for the
(per-time PROVED) `u`-only energy differential inequality.  Every other ingredient
is constructed unconditionally in `IntervalDomainL2UFrontierAssembly`.  See the file
header for the precise reasons neither field is unconditional and the parameter
regime under which a uniform sup-norm bound (and hence the Grönwall uniformity)
becomes available. -/
theorem GlobalSolutionGluingFromReachability_of_bounded
    (p : CM2Params)
    (h : IntervalDomainL2UBoundednessHypothesis p) :
    ShenWork.IntervalDomainExistence.GlobalSolutionGluingFromReachability p :=
  GlobalSolutionGluingFromReachability_of_boundedDatumUniform p
    (intervalDomainL2UBoundedDatumUniform_of_bounded h)

/-! ## Concrete uniformization of the τ-dependent constant (the `x↦x^γ` Lipschitz)

The only τ-dependence in the static `v`-control constants `Cv,Cg = (∑W_k)²·4·(ν·L_γ)²`
is the local Lipschitz constant `L_γ(τ) = γ·(δ_τ^{γ-1}+M_τ^{γ-1})` of `x↦x^γ` over the
per-time solution range `[δ_τ,M_τ]`.  Under a UNIFORM two-sided lift bound `[δ,M]`
(`δ>0`), this constant becomes the τ-independent `L_γ = γ·(δ^{γ-1}+M^{γ-1})`.  The
lemma below is the uniform analogue of `source_integral_le_Eu`, proven directly from
`rpow_lipschitz_on_pos_Icc` with the uniform `[δ,M]`; it is the concrete witness that
the Grönwall constant's reaction/source part uniformizes from `(δ,M)` alone. -/
theorem source_integral_le_Eu_uniform
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {δ M τ : ℝ} (hδ : 0 < δ)
    (hmem₁ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₁ τ) x ∈ Set.Icc δ M)
    (hmem₂ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₂ τ) x ∈ Set.Icc δ M)
    (hτ₁ : τ ∈ Set.Ioo (0 : ℝ) T₁) (hτ₂ : τ ∈ Set.Ioo (0 : ℝ) T₂) :
    (∫ x in (0:ℝ)..1, (p.ν * intervalDomainLift (u₁ τ) x ^ p.γ
        - p.ν * intervalDomainLift (u₂ τ) x ^ p.γ) ^ 2)
      ≤ (p.ν * (p.γ * (δ ^ (p.γ - 1) + M ^ (p.γ - 1)))) ^ 2 *
          intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ := by
  classical
  set L : ℝ := p.γ * (δ ^ (p.γ - 1) + M ^ (p.γ - 1)) with hLdef
  -- pointwise bound on `[0,1]`: `(νu₁^γ − νu₂^γ)² ≤ (νL)²·(u₁−u₂)²` (uniform L).
  have hptwise : ∀ x ∈ Set.Icc (0:ℝ) 1,
      (p.ν * intervalDomainLift (u₁ τ) x ^ p.γ
        - p.ν * intervalDomainLift (u₂ τ) x ^ p.γ) ^ 2
      ≤ (p.ν * L) ^ 2 *
        (intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x) ^ 2 := by
    intro x hxIcc
    have hlip := rpow_lipschitz_on_pos_Icc p.hγ hδ (hmem₁ x hxIcc) (hmem₂ x hxIcc)
    have habs : |intervalDomainLift (u₁ τ) x ^ p.γ - intervalDomainLift (u₂ τ) x ^ p.γ|
        ≤ L * |intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x| := hlip
    have hsq := mul_self_le_mul_self (abs_nonneg _) habs
    have hsq2 : (intervalDomainLift (u₁ τ) x ^ p.γ - intervalDomainLift (u₂ τ) x ^ p.γ) ^ 2
        ≤ L ^ 2 * (intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x) ^ 2 := by
      rw [← sq_abs (intervalDomainLift (u₁ τ) x ^ p.γ - intervalDomainLift (u₂ τ) x ^ p.γ),
          ← sq_abs (intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x)]
      calc |intervalDomainLift (u₁ τ) x ^ p.γ - intervalDomainLift (u₂ τ) x ^ p.γ| ^ 2
          = |intervalDomainLift (u₁ τ) x ^ p.γ - intervalDomainLift (u₂ τ) x ^ p.γ| *
            |intervalDomainLift (u₁ τ) x ^ p.γ - intervalDomainLift (u₂ τ) x ^ p.γ| := by ring
        _ ≤ (L * |intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x|) *
            (L * |intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x|) := hsq
        _ = L ^ 2 * |intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x| ^ 2 := by ring
    have hνsq : (0:ℝ) ≤ p.ν ^ 2 := by positivity
    calc (p.ν * intervalDomainLift (u₁ τ) x ^ p.γ
            - p.ν * intervalDomainLift (u₂ τ) x ^ p.γ) ^ 2
        = p.ν ^ 2 *
            (intervalDomainLift (u₁ τ) x ^ p.γ - intervalDomainLift (u₂ τ) x ^ p.γ) ^ 2 := by
          ring
      _ ≤ p.ν ^ 2 *
            (L ^ 2 * (intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq2 hνsq
      _ = (p.ν * L) ^ 2 *
            (intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x) ^ 2 := by ring
  have hEu : intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ
      = ∫ x in (0:ℝ)..1,
        (intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x) ^ 2 := by
    unfold intervalDomainClassicalL2DifferenceEnergyU
    show intervalDomainIntegral (fun x => (u₁ τ x - u₂ τ x) ^ 2)
      = ∫ x in (0:ℝ)..1, (intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x) ^ 2
    unfold intervalDomainIntegral
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    simp only [intervalDomainLift, hx, dif_pos]
  rw [hEu, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ hptwise
  · have hc1 := source_continuousOn_Icc hsol₁ hτ₁
    have hc2 := source_continuousOn_Icc hsol₂ hτ₂
    have : ContinuousOn (fun x => (p.ν * intervalDomainLift (u₁ τ) x ^ p.γ
        - p.ν * intervalDomainLift (u₂ τ) x ^ p.γ) ^ 2) (Set.uIcc (0:ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact ((hc1.sub hc2).pow 2)
    exact this.intervalIntegrable
  · have hcu1 : ContinuousOn (intervalDomainLift (u₁ τ)) (Set.Icc (0:ℝ) 1) :=
      ((hsol₁.regularity.2.2.2.2.2.2.1 τ hτ₁).1.1).continuousOn
    have hcu2 : ContinuousOn (intervalDomainLift (u₂ τ)) (Set.Icc (0:ℝ) 1) :=
      ((hsol₂.regularity.2.2.2.2.2.2.1 τ hτ₂).1.1).continuousOn
    have : ContinuousOn (fun x => (p.ν * L) ^ 2 *
        (intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x) ^ 2)
        (Set.uIcc (0:ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact continuousOn_const.mul ((hcu1.sub hcu2).pow 2)
    exact this.intervalIntegrable

end

end ShenWork.Paper2
