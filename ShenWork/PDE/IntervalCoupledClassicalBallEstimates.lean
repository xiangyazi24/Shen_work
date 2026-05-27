/-
  ShenWork/PDE/IntervalCoupledClassicalBallEstimates.lean

  PARALLEL classical-solution-strength ball framework for the coupled
  chemotaxis-logistic Duhamel scaffold, complementing
  `ShenWork/PDE/IntervalCoupledBallEstimates.lean`.

  Motivation.  The existing `IntervalCoupledResolverBallEstimates`
  (in `IntervalDomainExistence.lean`) is parametrized over
  `intervalTrajectoryBoundedOn T M u`, a SUP-norm-only ball hypothesis.  That
  hypothesis cannot wire into the already-proven C¹/C²-strength constituents
  (`sourceValue_eq_source`, `sourceValue_sup_lipschitz_of_uBoundedDiff`,
  `intervalNeumannResolverRLap_diff_abs_le`, `intervalNeumannResolverR_sup_lipschitz`,
  `resolverGradReal_*` Lipschitz, `chemQuotient_lipschitz`) because each of those
  requires `IsPaper2ClassicalSolution`-strength regularity of the snapshot
  trajectories.

  This file introduces a STRONGER ball predicate
  `IntervalDomainClassicalSnapshot p T M u v` that records exactly the
  classical-solution-strength regularity each `u τ`, `v τ` carries (it asks for
  an `IsPaper2ClassicalSolution` witness up to time `T` with the standard sup
  bound `M` on `lift (u τ)`), and proves the **pointwise sup-Lipschitz bound on
  the chemotactic FLUX** (not yet on its spatial derivative, the chemotaxis
  divergence — see "scope" comment below) on the trajectory ball.  The flux
  bound combines the existing proved constituents exactly per the task spec:

    `|flux(u₁,R u₁,y) − flux(u₂,R u₂,y)|
        ≤ G · |lift u₁ y − lift u₂ y|
          + U · |resolverGradReal u₁ y − resolverGradReal u₂ y|
          + U·G·β · |lift v₁ y − lift v₂ y|`

  with `U`, `G` the L∞ bounds on `lift u_i` and `resolverGradReal p (u_i τ)`
  produced by `lift_u_bounded`/`resolverGradReal_bounded` from the classical
  snapshot.  This pointwise bound is the genuine C¹-strength conclusion the
  task asked for; everything in it is a value-level Lipschitz of an already-
  proven constituent.

  Scope (honest).
  * STRUCTURE / PREDICATE — proved (`IntervalDomainClassicalSnapshot`).
  * FLUX value sup-Lipschitz on the snapshot ball — PROVED
    (`intervalFlux_classical_diff_abs_le`), reducing to
    `flux_diff_pointwise_bound` + closed-domain `v ≥ 0` (free for paper sols).
  * Conversion to the `(K · D)` ball form demanded by the existing
    `IntervalCoupledResolverBallEstimates.hflux_lip` slot — PROVED for the
    flux value (`intervalFlux_classical_K_D_form`) under an explicit Lipschitz
    constant abstracting `G + U·G·β + U` (each piece factors through
    `|lift u₁ y − lift u₂ y|` once the resolver's value/gradient sup-Lipschitz
    in `u` is supplied).
  * Conversion to the chemotaxis DIVERGENCE form
    `intervalDomainChemotaxisDiv p u (R u)` — left as a precisely-named gap.
    The chemDiv is `deriv flux`, so its pointwise sup-Lipschitz requires a
    pointwise sup-Lipschitz of the PRODUCT-RULE EXPANSION at the SECOND-
    derivative level: each summand (∂ₓlift u)·g·q, lift u·(∂²ₓlift v)·q,
    lift u·g·∂ₓq needs a value-Lipschitz on its factors.  The Lipschitz of
    `∂ₓ(lift u)` in `u` is NOT among the already-proven sup-Lipschitz
    constituents: it requires either an additional resolver-style smoothing
    estimate for `u` (which `u` does not satisfy in general) or the classical
    `C²,α` parabolic Schauder bound on `u`.  Documented gap below.
-/
import ShenWork.PDE.IntervalDomainExistence
import ShenWork.PDE.IntervalResolverLaplacianBridge
import ShenWork.PDE.IntervalNeumannEllipticResolverR
import ShenWork.Paper2.IntervalDomainL2UEnergyCombine

open ShenWork.Paper2 ShenWork.IntervalDomain ShenWork.PDE MeasureTheory
open ShenWork.IntervalResolverLaplacianBridge

noncomputable section

namespace ShenWork.IntervalCoupledClassicalBallEstimates

open ShenWork.IntervalDomainExistence

/-! ## Classical-solution-strength snapshot predicate

A `IntervalDomainClassicalSnapshot p T M u v` packages the precise regularity
that the existing proved sup-Lipschitz constituents consume: each time slice
`u τ`, `v τ` is part of a classical paper solution on `[0,T]`, plus the sup
bound `|lift (u τ) y| ≤ M` for every `y ∈ [0,1]` and every `τ ∈ (0,T)`.

This predicate is the "classical-strength" analog of
`intervalTrajectoryBoundedOn T M u`, with the extra regularity needed to fire
`flux_diff_pointwise_bound`, `chemQuotient_lipschitz`,
`sourceValue_eq_source`, `resolverGradReal_bounded`, etc. -/
def IntervalDomainClassicalSnapshot
    (p : CM2Params) (T M : ℝ)
    (u v : ℝ → intervalDomainPoint → ℝ) : Prop :=
  IsPaper2ClassicalSolution intervalDomain p T u v ∧
    ∀ τ : ℝ, τ ∈ Set.Ioo (0 : ℝ) T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |intervalDomainLift (u τ) x| ≤ M

namespace IntervalDomainClassicalSnapshot

variable {p : CM2Params} {T M : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}

theorem isSolution (h : IntervalDomainClassicalSnapshot p T M u v) :
    IsPaper2ClassicalSolution intervalDomain p T u v := h.1

theorem sup_bound (h : IntervalDomainClassicalSnapshot p T M u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |intervalDomainLift (u τ) x| ≤ M :=
  h.2 τ hτ x hx

end IntervalDomainClassicalSnapshot

/-! ## Flux value sup-Lipschitz on the classical-strength ball

Combining `flux_diff_pointwise_bound` with the L∞ resolver/lift bounds
(`lift_u_bounded`, `resolverGradReal_bounded`) and the closed-domain
nonnegativity of the chemical concentration (`solution_lift_v_nonneg_Icc`), we
get a pointwise sup-Lipschitz bound on the flux difference inside the OPEN
interior `(0,1)`, in terms of:

  * `|lift (u₁ τ) y − lift (u₂ τ) y|`,
  * `|resolverGradReal p (u₁ τ) y − resolverGradReal p (u₂ τ) y|`,
  * `|lift (v₁ τ) y − lift (v₂ τ) y|`.

The bound holds on the entire closed `[0,1]` for `intervalFluxRepr` (the C¹
representative); on the open interior it agrees with `intervalFlux`
(`intervalFlux_eq_repr_interior`). -/

/-- **Pointwise flux-value sup-Lipschitz bound on the classical-strength ball.**

For two classical-snapshot trajectories `(u_i, v_i)` of sup norm `≤ M`, the
chemotactic flux representative difference at every `y ∈ [0,1]` is bounded by
the value-level differences of `lift u`, `resolverGradReal p u`, and `lift v`,
with explicit constants in terms of:

  * `U = M` (sup on `|lift u|` from the snapshot bound),
  * `G = max G₁ G₂` (sup on `|resolverGradReal p (u_i τ)|` from `resolverGradReal_bounded`),
  * `p.β` (the chemotactic exponent).
-/
theorem intervalFluxRepr_classical_diff_abs_le
    {p : CM2Params} {T M : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsnap₁ : IntervalDomainClassicalSnapshot p T M u₁ v₁)
    (hsnap₂ : IntervalDomainClassicalSnapshot p T M u₂ v₂)
    (hMnn : 0 ≤ M)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    ∃ G : ℝ, 0 ≤ G ∧
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
        |intervalFluxRepr p (u₁ τ) (v₁ τ) y - intervalFluxRepr p (u₂ τ) (v₂ τ) y|
          ≤ G * |intervalDomainLift (u₁ τ) y - intervalDomainLift (u₂ τ) y|
            + M * |resolverGradReal p (u₁ τ) y - resolverGradReal p (u₂ τ) y|
            + M * G * p.β
                * |intervalDomainLift (v₁ τ) y - intervalDomainLift (v₂ τ) y|
          ∧ |resolverGradReal p (u₁ τ) y| ≤ G
          ∧ |resolverGradReal p (u₂ τ) y| ≤ G := by
  classical
  -- Unpack classical-solution snapshots.
  have hsol₁ := hsnap₁.isSolution
  have hsol₂ := hsnap₂.isSolution
  -- Closed-domain v ≥ 0 (free from positive classical solution).
  have hv₁nn := solution_lift_v_nonneg_Icc hsol₁ hτ
  have hv₂nn := solution_lift_v_nonneg_Icc hsol₂ hτ
  -- Uniform L∞ bound on the resolver gradient (continuity on compact `[0,1]`).
  obtain ⟨G₁, hG₁nn, hG₁⟩ := resolverGradReal_bounded hsol₁ hτ
  obtain ⟨G₂, hG₂nn, hG₂⟩ := resolverGradReal_bounded hsol₂ hτ
  set G : ℝ := max G₁ G₂ with hGdef
  have hGnn : 0 ≤ G := le_trans hG₁nn (le_max_left _ _)
  have hβnn : 0 ≤ p.β := p.hβ
  refine ⟨G, hGnn, ?_⟩
  intro y hyIcc
  -- Lift sup bounds from the snapshot.
  have ha₁ : |intervalDomainLift (u₁ τ) y| ≤ M := hsnap₁.sup_bound hτ hyIcc
  have ha₂ : |intervalDomainLift (u₂ τ) y| ≤ M := hsnap₂.sup_bound hτ hyIcc
  -- Resolver-gradient sup bounds.
  have hg₁ : |resolverGradReal p (u₁ τ) y| ≤ G :=
    le_trans (hG₁ y hyIcc) (le_max_left _ _)
  have hg₂ : |resolverGradReal p (u₂ τ) y| ≤ G :=
    le_trans (hG₂ y hyIcc) (le_max_right _ _)
  -- chemQuotient pieces.
  have hq₁ := chemQuotient_mem_Ioc hβnn (hv₁nn y hyIcc)
  have hq₂ := chemQuotient_mem_Ioc hβnn (hv₂nn y hyIcc)
  have hqLip := chemQuotient_lipschitz hβnn (hv₁nn y hyIcc) (hv₂nn y hyIcc)
  -- Apply the algebraic flux-difference bound.
  have hbound := flux_diff_pointwise_bound
    (a₁ := intervalDomainLift (u₁ τ) y) (a₂ := intervalDomainLift (u₂ τ) y)
    (g₁ := resolverGradReal p (u₁ τ) y) (g₂ := resolverGradReal p (u₂ τ) y)
    (q₁ := (1 + intervalDomainLift (v₁ τ) y) ^ (-p.β))
    (q₂ := (1 + intervalDomainLift (v₂ τ) y) ^ (-p.β))
    (v₁ := intervalDomainLift (v₁ τ) y) (v₂ := intervalDomainLift (v₂ τ) y)
    (U := M) (G := G) (Lq := p.β)
    ha₁ ha₂ hg₁ hg₂ hq₁.1.le hq₁.2 hq₂.1.le hq₂.2 hMnn hGnn hqLip
  refine ⟨?_, hg₁, hg₂⟩
  simpa only [intervalFluxRepr] using hbound

/-- **Flux value sup-Lipschitz on the OPEN interior** (where `intervalFlux`
agrees with `intervalFluxRepr`).  Same bound as `intervalFluxRepr_classical_diff_abs_le`
but stated for the genuine `intervalFlux`. -/
theorem intervalFlux_classical_diff_abs_le
    {p : CM2Params} {T M : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsnap₁ : IntervalDomainClassicalSnapshot p T M u₁ v₁)
    (hsnap₂ : IntervalDomainClassicalSnapshot p T M u₂ v₂)
    (hMnn : 0 ≤ M)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    ∃ G : ℝ, 0 ≤ G ∧
      ∀ y ∈ Set.Ioo (0 : ℝ) 1,
        |intervalFlux p (u₁ τ) (v₁ τ) y - intervalFlux p (u₂ τ) (v₂ τ) y|
          ≤ G * |intervalDomainLift (u₁ τ) y - intervalDomainLift (u₂ τ) y|
            + M * |resolverGradReal p (u₁ τ) y - resolverGradReal p (u₂ τ) y|
            + M * G * p.β
                * |intervalDomainLift (v₁ τ) y - intervalDomainLift (v₂ τ) y| := by
  classical
  obtain ⟨G, hGnn, hRepr⟩ :=
    intervalFluxRepr_classical_diff_abs_le hsnap₁ hsnap₂ hMnn hτ
  refine ⟨G, hGnn, ?_⟩
  intro y hyIoo
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hyIoo
  have hv₁nn := solution_lift_v_nonneg_Icc hsnap₁.isSolution hτ
  have hv₂nn := solution_lift_v_nonneg_Icc hsnap₂.isSolution hτ
  -- On the open interior, `intervalFlux` = `intervalFluxRepr`.
  have h1 := intervalFlux_eq_repr_interior hsnap₁.isSolution hτ hv₁nn hyIoo
  have h2 := intervalFlux_eq_repr_interior hsnap₂.isSolution hτ hv₂nn hyIoo
  rw [h1, h2]
  exact (hRepr y hyIcc).1

/-! ## Packaging into the `(K · D)` ball form

`IntervalCoupledResolverBallEstimates` demands a pointwise Lipschitz bound of
the shape `|flux₁ − flux₂| ≤ K · D` where `D` is a SINGLE scalar majorizing the
sup-norm of the trajectory difference.  Our three-term bound above factors
through:

  * `|lift u₁ y − lift u₂ y| ≤ D`  (trajectory ball-difference sup bound),
  * `|resolverGradReal p (u₁ τ) y − resolverGradReal p (u₂ τ) y|`
    `≤ L_R · D`  (resolver-gradient sup-Lipschitz constant `L_R`),
  * `|lift v₁ y − lift v₂ y| ≤ L_V · D`  (resolver-value sup-Lipschitz),

producing the consolidated constant `K = G + M · L_R + M · G · p.β · L_V`.

Both `L_R` and `L_V` are produced from
`intervalNeumannResolverR_grad_sup_lipschitz` and
`intervalNeumannResolverR_sup_lipschitz` respectively, contracted via the
source-coefficient `ℓ²` Lipschitz pipeline (`solution_resolver_sineSeries_summable`,
`solution_resolver_cosSeries_summable`).  We expose them as explicit named
hypotheses in the K-form theorem so the snapshot framework remains agnostic to
the specific path that bridges the trajectory ball difference to the resolver
coefficient L²-norm difference. -/

/-- **Packaged `K · D` form of the flux value sup-Lipschitz bound.**

Given the value/gradient sup-Lipschitz constants `L_V`, `L_R` of the resolver
on the trajectory ball (supplied as explicit named hypotheses, exactly the
content of `intervalNeumannResolverR_sup_lipschitz` and `…_grad_sup_lipschitz`
contracted into trajectory-ball form), the flux value difference at every
interior `y` is bounded by `K · D` with the explicit constant
`K = G + M · L_R + M · G · p.β · L_V`. -/
theorem intervalFlux_classical_K_D_form
    {p : CM2Params} {T M : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsnap₁ : IntervalDomainClassicalSnapshot p T M u₁ v₁)
    (hsnap₂ : IntervalDomainClassicalSnapshot p T M u₂ v₂)
    (hMnn : 0 ≤ M)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    {D L_V L_R : ℝ} (_hD : 0 ≤ D) (hLVnn : 0 ≤ L_V) (hLRnn : 0 ≤ L_R)
    (hu_diff :
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
        |intervalDomainLift (u₁ τ) y - intervalDomainLift (u₂ τ) y| ≤ D)
    (hv_diff :
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
        |intervalDomainLift (v₁ τ) y - intervalDomainLift (v₂ τ) y| ≤ L_V * D)
    (hg_diff :
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
        |resolverGradReal p (u₁ τ) y - resolverGradReal p (u₂ τ) y| ≤ L_R * D) :
    ∃ G K : ℝ, 0 ≤ G ∧ 0 ≤ K ∧
      ∀ y ∈ Set.Ioo (0 : ℝ) 1,
        |intervalFlux p (u₁ τ) (v₁ τ) y - intervalFlux p (u₂ τ) (v₂ τ) y|
          ≤ K * D := by
  classical
  obtain ⟨G, hGnn, hbnd⟩ := intervalFlux_classical_diff_abs_le hsnap₁ hsnap₂ hMnn hτ
  set K : ℝ := G + M * L_R + M * G * p.β * L_V with hKdef
  have hKnn : 0 ≤ K := by
    have h1 : 0 ≤ M * L_R := mul_nonneg hMnn hLRnn
    have h2 : 0 ≤ M * G * p.β * L_V := by
      have hMG : 0 ≤ M * G := mul_nonneg hMnn hGnn
      have hMGβ : 0 ≤ M * G * p.β := mul_nonneg hMG p.hβ
      exact mul_nonneg hMGβ hLVnn
    have : 0 ≤ G + M * L_R + M * G * p.β * L_V := by linarith
    simpa [hKdef] using this
  refine ⟨G, K, hGnn, hKnn, ?_⟩
  intro y hyIoo
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hyIoo
  have hMG : 0 ≤ M * G := mul_nonneg hMnn hGnn
  have hMGβ : 0 ≤ M * G * p.β := mul_nonneg hMG p.hβ
  -- Plug bounded differences into the three-term flux bound.
  have hu := hu_diff y hyIcc
  have hg := hg_diff y hyIcc
  have hv := hv_diff y hyIcc
  have hraw := hbnd y hyIoo
  have h1 :
      G * |intervalDomainLift (u₁ τ) y - intervalDomainLift (u₂ τ) y| ≤ G * D :=
    mul_le_mul_of_nonneg_left hu hGnn
  have h2 :
      M * |resolverGradReal p (u₁ τ) y - resolverGradReal p (u₂ τ) y|
        ≤ M * (L_R * D) :=
    mul_le_mul_of_nonneg_left hg hMnn
  have h3 :
      M * G * p.β
          * |intervalDomainLift (v₁ τ) y - intervalDomainLift (v₂ τ) y|
        ≤ M * G * p.β * (L_V * D) :=
    mul_le_mul_of_nonneg_left hv hMGβ
  calc |intervalFlux p (u₁ τ) (v₁ τ) y - intervalFlux p (u₂ τ) (v₂ τ) y|
      ≤ G * |intervalDomainLift (u₁ τ) y - intervalDomainLift (u₂ τ) y|
          + M * |resolverGradReal p (u₁ τ) y - resolverGradReal p (u₂ τ) y|
          + M * G * p.β
              * |intervalDomainLift (v₁ τ) y - intervalDomainLift (v₂ τ) y| := hraw
    _ ≤ G * D + M * (L_R * D) + M * G * p.β * (L_V * D) := by
        gcongr
    _ = K * D := by rw [hKdef]; ring

/-! ## Documented gap: chemotaxis DIVERGENCE Lipschitz

The chemotaxis divergence is `chemDiv p u v y := deriv (intervalFlux p u v) y.1`,
the SPATIAL DERIVATIVE of the flux.  Its pointwise sup-Lipschitz at fixed `y`
between two snapshots is therefore a bound on the difference of two derivative
values, not of two function values.  Even when both fluxes are `C¹` on `[0,1]`
(which `flux_contDiffOn_Icc` gives us under the classical snapshot), the
derivative difference does NOT follow from the value difference; one needs an
additional `C²` (one-derivative-stronger) regularity bound on the flux, which
in turn factors through:

  * `lift u` Lipschitz of `deriv (lift u)` in `u` — NOT a sup-Lipschitz of any
    proven constituent; the snapshot guarantees `lift u` is `C²` on `Icc 0 1`
    (regularity conjunct 7) but does NOT give a value-Lipschitz of its
    spatial derivative.  The cleanest analytic source for this is the parabolic
    Schauder bound on `u` (a `C^{2,α}` parabolic regularity estimate up to the
    closed Neumann boundary), which the current `IsPaper2ClassicalSolution`
    skeleton does NOT carry.

  * `resolverGradReal` Lipschitz of `resolverGrad2Real` in `u`.  The
    corresponding `…_grad2_sup_lipschitz` lemma is NOT in the library; only the
    value and first-derivative sup-Lipschitz pair is proved
    (`intervalNeumannResolverR_sup_lipschitz` / `_grad_sup_lipschitz`).  The
    coefficient-form derivation goes through the cube-mode weight `(kπ)³`
    summability rather than the quadratic-mode weight `(kπ)²` covered by
    `intervalNeumannResolverGradWeight_sq_summable`.

The honest path to the chemDiv pointwise sup-Lipschitz on the classical-strength
ball is therefore a TWO-pronged extension:

  (a) Add parabolic Schauder `C^{2,α}` regularity to
      `IsPaper2ClassicalSolution`, including a sup-Lipschitz of `deriv (lift u)`
      in `u` over the trajectory ball, OR equivalently strengthen the snapshot
      predicate by an explicit "C¹ trajectory" hypothesis on `u` and a
      Lipschitz constant on `deriv (lift u)`;
  (b) Prove an `intervalNeumannResolverR_grad2_sup_lipschitz`-style lemma in
      `IntervalNeumannEllipticResolverR.lean`, with the cube-mode weight
      `∑ₖ (kπ)³ / (μ+λ_k))²` finite (from `1/k³` summability) — directly
      analogous to the existing value and gradient bounds.

Once (a) and (b) are in place, the chemDiv pointwise Lipschitz follows from
the PRODUCT-RULE expansion of `deriv (flux)`:

  `deriv (flux) = (∂ₓlift u)·g·q + lift u · g' · q + lift u · g · ∂ₓq`

with `g = resolverGradReal`, `g' = resolverGrad2Real`, `q = (1+v)^{-β}`, by
the same three-factor algebraic identity (`flux_diff_pointwise_bound` applied
to the second derivative shape).  We DO NOT attempt to close this here; it is
a multi-day refactor of the resolver-coefficient theory that should land in a
dedicated PR after pieces (a),(b) are in.

The flux *value* sup-Lipschitz (above) is the C¹-ball-strength conclusion the
already-proven constituents (sourceValue, RLap, R, resolverGradReal, chemQuotient)
can support TODAY.  It is the natural intermediate output that any subsequent
chemDiv attack will consume. -/

/-! ## C¹_x-strength snapshot predicate and `chemDivRepr` Lipschitz

We now extend the framework with a STRONGER ball predicate
`IntervalDomainClassicalC1Snapshot p T M G_u u v` that additionally records a
uniform sup bound `G_u` on `deriv (intervalDomainLift (u τ))`.  This is exactly
the C¹_x-level regularity needed to bound the
`(∂ₓ(lift u))·g·q` term in the product-rule expansion of the chemotaxis
divergence.

Existence of such `G_u` is automatic from the classical-solution snapshot
(via `solution_deriv_lift_continuousOn_Icc` and compactness of `[0,1]`); the
predicate fixes a *named* constant so the resulting Lipschitz bound has an
explicit shape.

The chemotactic divergence is *defined* as
`chemDiv p u v y = deriv (fun z => lift u z · deriv (lift v) z / (1+lift v z)^β) y`.

On the open interior `(0,1)`, since `lift v` is `C²` with
`deriv (lift v) = resolverGradReal p u` (interior bridge) and `deriv² (lift v)
= RLap p u` (`deriv_resolverGradReal_eq_RLap`), the product/quotient rule
gives the closed-form expansion:

```
chemDiv = ∂ₓ(lift u) · g · q
        + lift u · RLap · q
        − p.β · lift u · g² · q′
```

where `g = resolverGradReal p u`, `q = (1+lift v)^{-p.β}`, and
`q′ = (1+lift v)^{-p.β-1}` (so `∂ₓq = −p.β · g · q′`).

We isolate this closed-form expansion as `intervalChemDivRepr` and prove its
pointwise sup-Lipschitz on the C¹_x snapshot ball, in the shape
`|chemDivRepr₁ − chemDivRepr₂| ≤ K_u · D + K_g · D_g`, where `D` is the
sup-norm trajectory diff and `D_g` is the sup-norm diff of `deriv (lift u)`.
The conversion `chemDiv = chemDivRepr` on the open interior is a separate
`HasDerivAt`-of-a-product-of-quotients computation, deliberately left as a
documented gap (see "scope" comment at the end). -/

/-! ### `chemQuotient2` — Lipschitz of `(1+v)^{-β-1}` -/

/-- **`(1+v)^{-β-1} ∈ (0,1]`** for `v ≥ 0`, `β ≥ 0` (so `-β-1 ≤ 0`).  Identical
proof to `chemQuotient_mem_Ioc` with exponent `β+1`. -/
theorem chemQuotient2_mem_Ioc
    {β v : ℝ} (hβ : 0 ≤ β) (hv : 0 ≤ v) :
    0 < (1 + v) ^ (-β - 1) ∧ (1 + v) ^ (-β - 1) ≤ 1 := by
  have hbase : (1 : ℝ) ≤ 1 + v := by linarith
  have hbase_pos : (0 : ℝ) < 1 + v := by linarith
  refine ⟨Real.rpow_pos_of_pos hbase_pos _, ?_⟩
  have := Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ) < 1) hbase
    (by linarith : -β - 1 ≤ 0)
  simpa using this

/-- **`(β+1)`-Lipschitz of `s ↦ (1+s)^{-β-1}` on `s ≥ 0`.**  Identical MVT
proof to `chemQuotient_lipschitz` with exponent `β+1`. -/
theorem chemQuotient2_lipschitz
    {β : ℝ} (hβ : 0 ≤ β) {v₁ v₂ : ℝ} (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂) :
    |(1 + v₁) ^ (-β - 1) - (1 + v₂) ^ (-β - 1)| ≤ (β + 1) * |v₁ - v₂| := by
  set M : ℝ := max v₁ v₂ with hM
  have hv₁M : v₁ ∈ Set.Icc (0:ℝ) M := ⟨hv₁, le_max_left _ _⟩
  have hv₂M : v₂ ∈ Set.Icc (0:ℝ) M := ⟨hv₂, le_max_right _ _⟩
  have hconv : Convex ℝ (Set.Icc (0:ℝ) M) := convex_Icc 0 M
  have hβ1 : 0 ≤ β + 1 := by linarith
  have hderiv : ∀ s ∈ Set.Icc (0:ℝ) M,
      HasDerivWithinAt (fun y : ℝ => (1 + y) ^ (-β - 1))
        ((-β - 1) * (1 + s) ^ (-β - 1 - 1)) (Set.Icc (0:ℝ) M) s := by
    intro s hs
    have hbase_pos : (0:ℝ) < 1 + s := by have := hs.1; linarith
    have hb : HasDerivAt (fun y : ℝ => (1 + y)) (1 : ℝ) s := by
      simpa using (hasDerivAt_id s).const_add (1 : ℝ)
    have hrp : HasDerivAt (fun y : ℝ => (1 + y) ^ (-β - 1))
        ((-β - 1) * (1 + s) ^ (-β - 1 - 1) * 1) s :=
      (Real.hasDerivAt_rpow_const (p := -β - 1) (Or.inl (ne_of_gt hbase_pos))).comp s hb
    have : (-β - 1) * (1 + s) ^ (-β - 1 - 1) * 1 = (-β - 1) * (1 + s) ^ (-β - 1 - 1) :=
      by ring
    rw [this] at hrp
    exact hrp.hasDerivWithinAt
  have hbound : ∀ s ∈ Set.Icc (0:ℝ) M,
      ‖(-β - 1) * (1 + s) ^ (-β - 1 - 1)‖ ≤ β + 1 := by
    intro s hs
    have hbase : (1:ℝ) ≤ 1 + s := by have := hs.1; linarith
    have hbase_pos : (0:ℝ) < 1 + s := by linarith
    have hle1 : (1 + s) ^ (-β - 1 - 1) ≤ 1 := by
      have := Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ) < 1) hbase
        (by linarith : -β - 1 - 1 ≤ 0)
      simpa using this
    have hpos : (0:ℝ) ≤ (1 + s) ^ (-β - 1 - 1) := (Real.rpow_pos_of_pos hbase_pos _).le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpos]
    have habs : |(-β - 1)| = β + 1 := by
      rw [show (-β - 1) = -(β + 1) by ring, abs_neg, abs_of_nonneg hβ1]
    rw [habs]
    calc (β + 1) * (1 + s) ^ (-β - 1 - 1) ≤ (β + 1) * 1 :=
          mul_le_mul_of_nonneg_left hle1 hβ1
      _ = β + 1 := by ring
  have hmvt := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hv₂M hv₁M
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  exact hmvt

/-! ### C¹_x-strength snapshot predicate -/

/-- **Classical C¹_x snapshot predicate.**  Extends
`IntervalDomainClassicalSnapshot` by a uniform sup bound `G_u` on the spatial
derivative `deriv (intervalDomainLift (u τ))` over `[0,1]` for each interior
time `τ ∈ (0,T)`.  This is exactly the regularity needed to bound the
`(∂ₓ lift u)·g·q` term in the product-rule expansion of the chemDiv. -/
def IntervalDomainClassicalC1Snapshot
    (p : CM2Params) (T M G_u : ℝ)
    (u v : ℝ → intervalDomainPoint → ℝ) : Prop :=
  IsPaper2ClassicalSolution intervalDomain p T u v ∧
    (∀ τ : ℝ, τ ∈ Set.Ioo (0 : ℝ) T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |intervalDomainLift (u τ) x| ≤ M) ∧
    (∀ τ : ℝ, τ ∈ Set.Ioo (0 : ℝ) T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (intervalDomainLift (u τ)) x| ≤ G_u)

namespace IntervalDomainClassicalC1Snapshot

variable {p : CM2Params} {T M G_u : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}

theorem isSolution (h : IntervalDomainClassicalC1Snapshot p T M G_u u v) :
    IsPaper2ClassicalSolution intervalDomain p T u v := h.1

theorem sup_bound (h : IntervalDomainClassicalC1Snapshot p T M G_u u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |intervalDomainLift (u τ) x| ≤ M :=
  h.2.1 τ hτ x hx

theorem grad_sup_bound (h : IntervalDomainClassicalC1Snapshot p T M G_u u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |deriv (intervalDomainLift (u τ)) x| ≤ G_u :=
  h.2.2 τ hτ x hx

/-- A C¹_x snapshot specializes to a sup-norm-only classical snapshot by
forgetting the gradient bound. -/
theorem toClassicalSnapshot (h : IntervalDomainClassicalC1Snapshot p T M G_u u v) :
    IntervalDomainClassicalSnapshot p T M u v :=
  ⟨h.1, h.2.1⟩

end IntervalDomainClassicalC1Snapshot

/-! ### `intervalChemDivRepr` — closed-form product-rule expansion -/

/-- **Closed-form representative for the chemotaxis divergence.**

On the open interior `(0,1)`, `intervalDomainChemotaxisDiv p u v` equals the
product-rule expansion using `resolverGradReal` for `∂ₓ(lift v)` and `RLap` for
`∂ₓ²(lift v)`:

```
chemDivRepr(u,v,y) := ∂ₓ(lift u)(y) · g(y) · q(y)
                    + lift u(y) · RLap(y) · q(y)
                    − p.β · lift u(y) · g(y)² · q′(y)
```

with `g = resolverGradReal p u`, `q = (1+lift v)^{-p.β}`,
`q′ = (1+lift v)^{-p.β-1}`.  This is the genuine C²-strength differential
identity; the equality `chemDiv = chemDivRepr` on `(0,1)` follows from
`solution_lift_v_deriv_eq_resolverGrad` + `deriv_resolverGradReal_eq_RLap` +
the quotient/product rule and is left as a documented gap. -/
def intervalChemDivRepr (p : CM2Params)
    (u v : intervalDomainPoint → ℝ) (y : intervalDomainPoint) : ℝ :=
  deriv (intervalDomainLift u) y.1 * resolverGradReal p u y.1
      * (1 + intervalDomainLift v y.1) ^ (-p.β)
    + intervalDomainLift u y.1 * intervalNeumannResolverRLap p u y
        * (1 + intervalDomainLift v y.1) ^ (-p.β)
    - p.β * intervalDomainLift u y.1
        * (resolverGradReal p u y.1)^2
        * (1 + intervalDomainLift v y.1) ^ (-p.β - 1)

/-! ### Pure-algebraic five-factor product-difference bound

The chemDivRepr difference telescopes through five factor differences:
`Δ(∂ₓ lift u)`, `Δ(lift u)`, `Δg`, `ΔRLap`, `Δq`, `Δq′`, weighted by the
appropriate L∞ bounds of the other factors.  We do the algebra in one
all-purpose lemma `chemDivRepr_diff_pointwise_bound` (analog of
`flux_diff_pointwise_bound`) and then plug in the snapshot L∞ bounds. -/

/-- **Algebraic chemDivRepr-difference bound** at one point, all factors
treated as abstract bounded reals.  Telescopes via the standard difference of
products `a·b·c` and `a·b²·d`.

With L∞ bounds (`|a_i| ≤ A`, `|du_i| ≤ Du`, `|g_i| ≤ G`, `|gp_i| ≤ Gp`,
`0 ≤ q_i ≤ 1`, `0 ≤ q'_i ≤ 1`) and Lipschitz of `q`,`q'` in `v` (constants
`Lq`, `Lq'`):

```
| (du₁·g₁·q₁ + a₁·gp₁·q₁ − β·a₁·g₁²·q'₁)
  −(du₂·g₂·q₂ + a₂·gp₂·q₂ − β·a₂·g₂²·q'₂) |
  ≤ G·|du₁−du₂|
  + (Du+Gp+β·G²)·|a₁−a₂|
  + (A + 2·β·A·G)·|g₁−g₂|
  + A·|gp₁−gp₂|
  + (Du·G + A·Gp)·Lq·|v₁−v₂|
  + β·A·G²·Lq'·|v₁−v₂|
```

The exact constants are recorded below; the proof is a long but mechanical
telescoping using `abs_add_three`/`abs_sub` and product-of-bounded-factors
estimates. -/
theorem chemDivRepr_diff_pointwise_bound
    {du₁ du₂ a₁ a₂ g₁ g₂ gp₁ gp₂ q₁ q₂ qp₁ qp₂ v₁ v₂
     A Du G Gp Lq Lqp β : ℝ}
    (hdu₁ : |du₁| ≤ Du) (hdu₂ : |du₂| ≤ Du)
    (ha₁ : |a₁| ≤ A) (ha₂ : |a₂| ≤ A)
    (hg₁ : |g₁| ≤ G) (hg₂ : |g₂| ≤ G)
    (hgp₁ : |gp₁| ≤ Gp) (hgp₂ : |gp₂| ≤ Gp)
    (hq₁0 : 0 ≤ q₁) (hq₁1 : q₁ ≤ 1) (hq₂0 : 0 ≤ q₂) (hq₂1 : q₂ ≤ 1)
    (hqp₁0 : 0 ≤ qp₁) (hqp₁1 : qp₁ ≤ 1)
    (_hqp₂0 : 0 ≤ qp₂) (_hqp₂1 : qp₂ ≤ 1)
    (hAnn : 0 ≤ A) (hDunn : 0 ≤ Du) (hGnn : 0 ≤ G) (hGpnn : 0 ≤ Gp)
    (hβnn : 0 ≤ β)
    (hqLip : |q₁ - q₂| ≤ Lq * |v₁ - v₂|)
    (hqpLip : |qp₁ - qp₂| ≤ Lqp * |v₁ - v₂|) :
    |(du₁ * g₁ * q₁ + a₁ * gp₁ * q₁ - β * a₁ * g₁^2 * qp₁)
      - (du₂ * g₂ * q₂ + a₂ * gp₂ * q₂ - β * a₂ * g₂^2 * qp₂)|
    ≤ G * |du₁ - du₂|
      + Gp * |a₁ - a₂|
      + A * |gp₁ - gp₂|
      + Du * |g₁ - g₂|
      + (Du * G + A * Gp) * Lq * |v₁ - v₂|
      + β * (A * G^2) * Lqp * |v₁ - v₂|
      + β * G^2 * |a₁ - a₂|
      + β * A * (G + G) * |g₁ - g₂| := by
  -- Telescope T1, T2, T3 individually using flux_diff_pointwise_bound.
  -- T1 = du · g · q : direct application.
  have hT1 :=
    flux_diff_pointwise_bound (a₁ := du₁) (a₂ := du₂)
      (g₁ := g₁) (g₂ := g₂) (q₁ := q₁) (q₂ := q₂) (v₁ := v₁) (v₂ := v₂)
      (U := Du) (G := G) (Lq := Lq)
      hdu₁ hdu₂ hg₁ hg₂ hq₁0 hq₁1 hq₂0 hq₂1 hDunn hGnn hqLip
  -- T2 = a · gp · q : same shape with (a,gp,q) playing (a,g,q).
  have hT2 :=
    flux_diff_pointwise_bound (a₁ := a₁) (a₂ := a₂)
      (g₁ := gp₁) (g₂ := gp₂) (q₁ := q₁) (q₂ := q₂) (v₁ := v₁) (v₂ := v₂)
      (U := A) (G := Gp) (Lq := Lq)
      ha₁ ha₂ hgp₁ hgp₂ hq₁0 hq₁1 hq₂0 hq₂1 hAnn hGpnn hqLip
  -- T3 = β · a · g² · qp.  Bound it by telescoping
  --   a₁ g₁² qp₁ − a₂ g₂² qp₂
  --   = (a₁−a₂) g₁² qp₁ + a₂ (g₁²−g₂²) qp₁ + a₂ g₂² (qp₁−qp₂)
  -- and using g₁²−g₂² = (g₁−g₂)(g₁+g₂), |g₁+g₂| ≤ 2G.
  have hT3raw : |a₁ * g₁^2 * qp₁ - a₂ * g₂^2 * qp₂|
      ≤ G^2 * |a₁ - a₂| + A * (G + G) * |g₁ - g₂|
          + A * G^2 * Lqp * |v₁ - v₂| := by
    have htel : a₁ * g₁^2 * qp₁ - a₂ * g₂^2 * qp₂
        = (a₁ - a₂) * g₁^2 * qp₁
          + a₂ * (g₁^2 - g₂^2) * qp₁
          + a₂ * g₂^2 * (qp₁ - qp₂) := by ring
    rw [htel]
    refine (abs_add_three _ _ _).trans ?_
    refine add_le_add (add_le_add ?_ ?_) ?_
    · -- |(a₁−a₂) g₁² qp₁| ≤ G² · |a₁−a₂|
      rw [abs_mul, abs_mul]
      have hg1sq : |g₁^2| ≤ G^2 := by
        have h : |g₁^2| = |g₁| * |g₁| := by rw [sq, abs_mul]
        rw [h, sq]
        exact mul_le_mul hg₁ hg₁ (abs_nonneg _) hGnn
      have hqp1abs : |qp₁| ≤ 1 := by rw [abs_of_nonneg hqp₁0]; exact hqp₁1
      calc |a₁ - a₂| * |g₁^2| * |qp₁|
          ≤ |a₁ - a₂| * G^2 * 1 := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left hg1sq (abs_nonneg _)
            · exact hqp1abs
            · exact abs_nonneg _
            · positivity
        _ = G^2 * |a₁ - a₂| := by ring
    · -- |a₂ (g₁²−g₂²) qp₁| ≤ A · 2G · |g₁−g₂|
      have hdiff : g₁^2 - g₂^2 = (g₁ - g₂) * (g₁ + g₂) := by ring
      rw [show a₂ * (g₁^2 - g₂^2) * qp₁
          = a₂ * ((g₁ - g₂) * (g₁ + g₂)) * qp₁ from by rw [hdiff]]
      rw [abs_mul, abs_mul, abs_mul]
      have hg12 : |g₁ + g₂| ≤ G + G := by
        calc |g₁ + g₂| ≤ |g₁| + |g₂| := abs_add_le _ _
          _ ≤ G + G := add_le_add hg₁ hg₂
      have hqp1abs : |qp₁| ≤ 1 := by rw [abs_of_nonneg hqp₁0]; exact hqp₁1
      calc |a₂| * (|g₁ - g₂| * |g₁ + g₂|) * |qp₁|
          ≤ A * (|g₁ - g₂| * (G + G)) * 1 := by
            apply mul_le_mul
            · apply mul_le_mul ha₂ _ (by positivity) hAnn
              exact mul_le_mul_of_nonneg_left hg12 (abs_nonneg _)
            · exact hqp1abs
            · exact abs_nonneg _
            · positivity
        _ = A * (G + G) * |g₁ - g₂| := by ring
    · -- |a₂ g₂² (qp₁−qp₂)| ≤ A · G² · Lqp · |v₁−v₂|
      rw [abs_mul, abs_mul]
      have hg2sq : |g₂^2| ≤ G^2 := by
        have h : |g₂^2| = |g₂| * |g₂| := by rw [sq, abs_mul]
        rw [h, sq]
        exact mul_le_mul hg₂ hg₂ (abs_nonneg _) hGnn
      calc |a₂| * |g₂^2| * |qp₁ - qp₂|
          ≤ A * G^2 * (Lqp * |v₁ - v₂|) := by
            apply mul_le_mul
            · exact mul_le_mul ha₂ hg2sq (abs_nonneg _) hAnn
            · exact hqpLip
            · exact abs_nonneg _
            · positivity
        _ = A * G^2 * Lqp * |v₁ - v₂| := by ring
  -- Assemble.  Combine via triangle inequality on T1 + T2 - T3.
  have hsplit : (du₁ * g₁ * q₁ + a₁ * gp₁ * q₁ - β * a₁ * g₁^2 * qp₁)
      - (du₂ * g₂ * q₂ + a₂ * gp₂ * q₂ - β * a₂ * g₂^2 * qp₂)
      = (du₁ * g₁ * q₁ - du₂ * g₂ * q₂)
        + (a₁ * gp₁ * q₁ - a₂ * gp₂ * q₂)
        - β * (a₁ * g₁^2 * qp₁ - a₂ * g₂^2 * qp₂) := by ring
  rw [hsplit]
  have habs_sub : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := fun x y => by
    calc |x - y| ≤ |x| + |(-y)| := by rw [sub_eq_add_neg]; exact abs_add_le _ _
      _ = |x| + |y| := by rw [abs_neg]
  have hβT3 : |β * (a₁ * g₁^2 * qp₁ - a₂ * g₂^2 * qp₂)|
      ≤ β * (G^2 * |a₁ - a₂| + A * (G + G) * |g₁ - g₂|
              + A * G^2 * Lqp * |v₁ - v₂|) := by
    rw [abs_mul, abs_of_nonneg hβnn]
    exact mul_le_mul_of_nonneg_left hT3raw hβnn
  have hsum := habs_sub ((du₁ * g₁ * q₁ - du₂ * g₂ * q₂)
        + (a₁ * gp₁ * q₁ - a₂ * gp₂ * q₂))
        (β * (a₁ * g₁^2 * qp₁ - a₂ * g₂^2 * qp₂))
  have hAB : |(du₁ * g₁ * q₁ - du₂ * g₂ * q₂)
        + (a₁ * gp₁ * q₁ - a₂ * gp₂ * q₂)|
      ≤ |du₁ * g₁ * q₁ - du₂ * g₂ * q₂|
        + |a₁ * gp₁ * q₁ - a₂ * gp₂ * q₂| := abs_add_le _ _
  calc |(du₁ * g₁ * q₁ - du₂ * g₂ * q₂) + (a₁ * gp₁ * q₁ - a₂ * gp₂ * q₂)
          - β * (a₁ * g₁^2 * qp₁ - a₂ * g₂^2 * qp₂)|
      ≤ |(du₁ * g₁ * q₁ - du₂ * g₂ * q₂) + (a₁ * gp₁ * q₁ - a₂ * gp₂ * q₂)|
        + |β * (a₁ * g₁^2 * qp₁ - a₂ * g₂^2 * qp₂)| := hsum
    _ ≤ (|du₁ * g₁ * q₁ - du₂ * g₂ * q₂|
        + |a₁ * gp₁ * q₁ - a₂ * gp₂ * q₂|)
        + β * (G^2 * |a₁ - a₂| + A * (G + G) * |g₁ - g₂|
                + A * G^2 * Lqp * |v₁ - v₂|) := add_le_add hAB hβT3
    _ ≤ (G * |du₁ - du₂| + Du * |g₁ - g₂| + Du * G * Lq * |v₁ - v₂|)
        + (Gp * |a₁ - a₂| + A * |gp₁ - gp₂| + A * Gp * Lq * |v₁ - v₂|)
        + β * (G^2 * |a₁ - a₂| + A * (G + G) * |g₁ - g₂|
                + A * G^2 * Lqp * |v₁ - v₂|) := by
          have := add_le_add hT1 hT2
          linarith
    _ = G * |du₁ - du₂|
        + Gp * |a₁ - a₂|
        + A * |gp₁ - gp₂|
        + Du * |g₁ - g₂|
        + (Du * G + A * Gp) * Lq * |v₁ - v₂|
        + β * (A * G^2) * Lqp * |v₁ - v₂|
        + β * G^2 * |a₁ - a₂|
        + β * A * (G + G) * |g₁ - g₂| := by ring

/-! ### chemDivRepr Lipschitz on the C¹_x snapshot ball -/

/-- **Pointwise chemDivRepr difference bound on the C¹_x snapshot ball.**

For two C¹_x snapshots `(u_i, v_i, M, G_u)` (sharing the sup-norm bound `M` on
`lift u` and the gradient-sup bound `G_u` on `deriv (lift u)`), the
chemDivRepr difference at every `y ∈ [0,1]` is bounded by:

* `|deriv (lift u₁) y − deriv (lift u₂) y|` (the gradient-trajectory diff),
* `|lift u₁ y − lift u₂ y|`,
* `|resolverGradReal p u₁ y − resolverGradReal p u₂ y|`,
* `|RLap p u₁ y − RLap p u₂ y|`,
* `|lift v₁ y − lift v₂ y|`,

with explicit constants depending only on `M`, `G_u`, an L∞ bound `G` on
`resolverGradReal` (from `resolverGradReal_bounded`), an L∞ bound `H` on
`RLap` (from `RLap_bounded` — recorded as an explicit hypothesis here),
and `p.β`. -/
theorem intervalChemDivRepr_classical_diff_abs_le
    {p : CM2Params} {T M G_u : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsnap₁ : IntervalDomainClassicalC1Snapshot p T M G_u u₁ v₁)
    (hsnap₂ : IntervalDomainClassicalC1Snapshot p T M G_u u₂ v₂)
    (hMnn : 0 ≤ M) (hGunn : 0 ≤ G_u)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    {H : ℝ} (hHnn : 0 ≤ H)
    (hH₁ : ∀ y : intervalDomainPoint, y.1 ∈ Set.Icc (0:ℝ) 1 →
      |intervalNeumannResolverRLap p (u₁ τ) y| ≤ H)
    (hH₂ : ∀ y : intervalDomainPoint, y.1 ∈ Set.Icc (0:ℝ) 1 →
      |intervalNeumannResolverRLap p (u₂ τ) y| ≤ H) :
    ∃ G : ℝ, 0 ≤ G ∧
      ∀ y : intervalDomainPoint, y.1 ∈ Set.Icc (0:ℝ) 1 →
        |intervalChemDivRepr p (u₁ τ) (v₁ τ) y
          - intervalChemDivRepr p (u₂ τ) (v₂ τ) y|
        ≤ G * |deriv (intervalDomainLift (u₁ τ)) y.1
                - deriv (intervalDomainLift (u₂ τ)) y.1|
          + (H + p.β * G^2) * |intervalDomainLift (u₁ τ) y.1
                                - intervalDomainLift (u₂ τ) y.1|
          + (G_u + 2 * p.β * M * G) * |resolverGradReal p (u₁ τ) y.1
                                        - resolverGradReal p (u₂ τ) y.1|
          + M * |intervalNeumannResolverRLap p (u₁ τ) y
                  - intervalNeumannResolverRLap p (u₂ τ) y|
          + (G_u * G + M * H) * p.β * |intervalDomainLift (v₁ τ) y.1
                                        - intervalDomainLift (v₂ τ) y.1|
          + p.β * (M * G^2) * (p.β + 1) * |intervalDomainLift (v₁ τ) y.1
                                            - intervalDomainLift (v₂ τ) y.1| := by
  classical
  have hsol₁ := hsnap₁.isSolution
  have hsol₂ := hsnap₂.isSolution
  have hv₁nn := solution_lift_v_nonneg_Icc hsol₁ hτ
  have hv₂nn := solution_lift_v_nonneg_Icc hsol₂ hτ
  obtain ⟨G₁, hG₁nn, hG₁⟩ := resolverGradReal_bounded hsol₁ hτ
  obtain ⟨G₂, hG₂nn, hG₂⟩ := resolverGradReal_bounded hsol₂ hτ
  set G : ℝ := max G₁ G₂ with hGdef
  have hGnn : 0 ≤ G := le_trans hG₁nn (le_max_left _ _)
  have hβnn : 0 ≤ p.β := p.hβ
  refine ⟨G, hGnn, ?_⟩
  intro y hyIcc
  -- Bounds on individual factors.
  have ha₁ : |intervalDomainLift (u₁ τ) y.1| ≤ M := hsnap₁.sup_bound hτ hyIcc
  have ha₂ : |intervalDomainLift (u₂ τ) y.1| ≤ M := hsnap₂.sup_bound hτ hyIcc
  have hdu₁ : |deriv (intervalDomainLift (u₁ τ)) y.1| ≤ G_u :=
    hsnap₁.grad_sup_bound hτ hyIcc
  have hdu₂ : |deriv (intervalDomainLift (u₂ τ)) y.1| ≤ G_u :=
    hsnap₂.grad_sup_bound hτ hyIcc
  have hg₁ : |resolverGradReal p (u₁ τ) y.1| ≤ G :=
    le_trans (hG₁ y.1 hyIcc) (le_max_left _ _)
  have hg₂ : |resolverGradReal p (u₂ τ) y.1| ≤ G :=
    le_trans (hG₂ y.1 hyIcc) (le_max_right _ _)
  have hgp₁ : |intervalNeumannResolverRLap p (u₁ τ) y| ≤ H := hH₁ y hyIcc
  have hgp₂ : |intervalNeumannResolverRLap p (u₂ τ) y| ≤ H := hH₂ y hyIcc
  -- chemQuotient.
  have hq₁ := chemQuotient_mem_Ioc hβnn (hv₁nn y.1 hyIcc)
  have hq₂ := chemQuotient_mem_Ioc hβnn (hv₂nn y.1 hyIcc)
  have hqLip := chemQuotient_lipschitz hβnn (hv₁nn y.1 hyIcc) (hv₂nn y.1 hyIcc)
  -- chemQuotient2.
  have hqp₁ := chemQuotient2_mem_Ioc hβnn (hv₁nn y.1 hyIcc)
  have hqp₂ := chemQuotient2_mem_Ioc hβnn (hv₂nn y.1 hyIcc)
  have hqpLip := chemQuotient2_lipschitz hβnn (hv₁nn y.1 hyIcc) (hv₂nn y.1 hyIcc)
  -- Apply the algebraic chemDivRepr-difference bound.
  have hbound := chemDivRepr_diff_pointwise_bound
    (du₁ := deriv (intervalDomainLift (u₁ τ)) y.1)
    (du₂ := deriv (intervalDomainLift (u₂ τ)) y.1)
    (a₁ := intervalDomainLift (u₁ τ) y.1)
    (a₂ := intervalDomainLift (u₂ τ) y.1)
    (g₁ := resolverGradReal p (u₁ τ) y.1)
    (g₂ := resolverGradReal p (u₂ τ) y.1)
    (gp₁ := intervalNeumannResolverRLap p (u₁ τ) y)
    (gp₂ := intervalNeumannResolverRLap p (u₂ τ) y)
    (q₁ := (1 + intervalDomainLift (v₁ τ) y.1) ^ (-p.β))
    (q₂ := (1 + intervalDomainLift (v₂ τ) y.1) ^ (-p.β))
    (qp₁ := (1 + intervalDomainLift (v₁ τ) y.1) ^ (-p.β - 1))
    (qp₂ := (1 + intervalDomainLift (v₂ τ) y.1) ^ (-p.β - 1))
    (v₁ := intervalDomainLift (v₁ τ) y.1)
    (v₂ := intervalDomainLift (v₂ τ) y.1)
    (A := M) (Du := G_u) (G := G) (Gp := H)
    (Lq := p.β) (Lqp := p.β + 1) (β := p.β)
    hdu₁ hdu₂ ha₁ ha₂ hg₁ hg₂ hgp₁ hgp₂
    hq₁.1.le hq₁.2 hq₂.1.le hq₂.2
    hqp₁.1.le hqp₁.2 hqp₂.1.le hqp₂.2
    hMnn hGunn hGnn hHnn hβnn hqLip hqpLip
  -- Convert `intervalChemDivRepr` definitional unfolding.
  have hrepr_unfold₁ :
      intervalChemDivRepr p (u₁ τ) (v₁ τ) y
        = deriv (intervalDomainLift (u₁ τ)) y.1 * resolverGradReal p (u₁ τ) y.1
              * (1 + intervalDomainLift (v₁ τ) y.1) ^ (-p.β)
          + intervalDomainLift (u₁ τ) y.1 * intervalNeumannResolverRLap p (u₁ τ) y
              * (1 + intervalDomainLift (v₁ τ) y.1) ^ (-p.β)
          - p.β * intervalDomainLift (u₁ τ) y.1
              * (resolverGradReal p (u₁ τ) y.1)^2
              * (1 + intervalDomainLift (v₁ τ) y.1) ^ (-p.β - 1) := rfl
  have hrepr_unfold₂ :
      intervalChemDivRepr p (u₂ τ) (v₂ τ) y
        = deriv (intervalDomainLift (u₂ τ)) y.1 * resolverGradReal p (u₂ τ) y.1
              * (1 + intervalDomainLift (v₂ τ) y.1) ^ (-p.β)
          + intervalDomainLift (u₂ τ) y.1 * intervalNeumannResolverRLap p (u₂ τ) y
              * (1 + intervalDomainLift (v₂ τ) y.1) ^ (-p.β)
          - p.β * intervalDomainLift (u₂ τ) y.1
              * (resolverGradReal p (u₂ τ) y.1)^2
              * (1 + intervalDomainLift (v₂ τ) y.1) ^ (-p.β - 1) := rfl
  rw [hrepr_unfold₁, hrepr_unfold₂]
  linarith [hbound]

/-! ### Packaged `K_u · D + K_g · D_g` form

Given trajectory-ball sup bounds on each component difference (`Δ(lift u)`,
`Δ(deriv lift u)`, `Δg`, `ΔRLap`, `Δ(lift v)`) factoring through `D` and
`D_g`, the chemDivRepr difference reduces to the `K_u · D + K_g · D_g` shape
demanded by the C¹_x ball framework. -/

/-- **Packaged `K_u · D + K_g · D_g` form of the chemDivRepr Lipschitz bound.**

Given the trajectory-ball sup bounds on each factor difference (parametrized
by `D = sup |Δ(lift u)|` and `D_g = sup |Δ(deriv lift u)|`, with the
auxiliary differences `Δg`, `ΔRLap`, `Δ(lift v)` factoring linearly through
`D` with constants `L_R`, `L_H`, `L_V`), the chemDivRepr difference is
bounded by `K_u · D + K_g · D_g` with explicit nonnegative `K_u`, `K_g`. -/
theorem intervalChemDivRepr_classical_K_D_form
    {p : CM2Params} {T M G_u : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsnap₁ : IntervalDomainClassicalC1Snapshot p T M G_u u₁ v₁)
    (hsnap₂ : IntervalDomainClassicalC1Snapshot p T M G_u u₂ v₂)
    (hMnn : 0 ≤ M) (hGunn : 0 ≤ G_u)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    {H : ℝ} (hHnn : 0 ≤ H)
    (hH₁ : ∀ y : intervalDomainPoint, y.1 ∈ Set.Icc (0:ℝ) 1 →
      |intervalNeumannResolverRLap p (u₁ τ) y| ≤ H)
    (hH₂ : ∀ y : intervalDomainPoint, y.1 ∈ Set.Icc (0:ℝ) 1 →
      |intervalNeumannResolverRLap p (u₂ τ) y| ≤ H)
    {D D_g L_V L_R L_H : ℝ}
    (_hDnn : 0 ≤ D) (_hDgnn : 0 ≤ D_g)
    (hLVnn : 0 ≤ L_V) (hLRnn : 0 ≤ L_R) (hLHnn : 0 ≤ L_H)
    (hu_diff :
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x| ≤ D)
    (hdu_diff :
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (intervalDomainLift (u₁ τ)) x
          - deriv (intervalDomainLift (u₂ τ)) x| ≤ D_g)
    (hv_diff :
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |intervalDomainLift (v₁ τ) x - intervalDomainLift (v₂ τ) x| ≤ L_V * D)
    (hg_diff :
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |resolverGradReal p (u₁ τ) x - resolverGradReal p (u₂ τ) x| ≤ L_R * D)
    (hH_diff :
      ∀ y : intervalDomainPoint, y.1 ∈ Set.Icc (0 : ℝ) 1 →
        |intervalNeumannResolverRLap p (u₁ τ) y
          - intervalNeumannResolverRLap p (u₂ τ) y| ≤ L_H * D) :
    ∃ G K_u K_g : ℝ, 0 ≤ G ∧ 0 ≤ K_u ∧ 0 ≤ K_g ∧
      ∀ y : intervalDomainPoint, y.1 ∈ Set.Icc (0 : ℝ) 1 →
        |intervalChemDivRepr p (u₁ τ) (v₁ τ) y
          - intervalChemDivRepr p (u₂ τ) (v₂ τ) y|
        ≤ K_u * D + K_g * D_g := by
  classical
  obtain ⟨G, hGnn, hraw⟩ :=
    intervalChemDivRepr_classical_diff_abs_le hsnap₁ hsnap₂ hMnn hGunn hτ hHnn hH₁ hH₂
  have hβnn : 0 ≤ p.β := p.hβ
  have hMG : 0 ≤ M * G := mul_nonneg hMnn hGnn
  have hMG2 : 0 ≤ M * G^2 := mul_nonneg hMnn (sq_nonneg _)
  have hHβG2 : 0 ≤ H + p.β * G^2 :=
    add_nonneg hHnn (mul_nonneg hβnn (sq_nonneg _))
  have h2pβMG : 0 ≤ 2 * p.β * M * G := by
    have : 0 ≤ 2 * p.β := by positivity
    exact mul_nonneg (mul_nonneg this hMnn) hGnn
  have hGu2pβMG : 0 ≤ G_u + 2 * p.β * M * G := add_nonneg hGunn h2pβMG
  set K_u : ℝ := (H + p.β * G^2)
        + (G_u + 2 * p.β * M * G) * L_R
        + M * L_H
        + (G_u * G + M * H) * p.β * L_V
        + p.β * (M * G^2) * (p.β + 1) * L_V with hKudef
  set K_g : ℝ := G with hKgdef
  have hKunn : 0 ≤ K_u := by
    have hh : 0 ≤ p.β * (M * G^2) * (p.β + 1) * L_V := by positivity
    have h1 : 0 ≤ (G_u + 2 * p.β * M * G) * L_R := mul_nonneg hGu2pβMG hLRnn
    have h2 : 0 ≤ M * L_H := mul_nonneg hMnn hLHnn
    have h3 : 0 ≤ (G_u * G + M * H) * p.β * L_V :=
      mul_nonneg (mul_nonneg
        (add_nonneg (mul_nonneg hGunn hGnn) (mul_nonneg hMnn hHnn)) hβnn) hLVnn
    change 0 ≤ K_u
    have : 0 ≤ (H + p.β * G^2)
        + (G_u + 2 * p.β * M * G) * L_R
        + M * L_H
        + (G_u * G + M * H) * p.β * L_V
        + p.β * (M * G^2) * (p.β + 1) * L_V := by linarith
    simpa [hKudef] using this
  have hKgnn : 0 ≤ K_g := hGnn
  refine ⟨G, K_u, K_g, hGnn, hKunn, hKgnn, ?_⟩
  intro y hyIcc
  -- We will need ≤ versions of every term.
  have hraw_y := hraw y hyIcc
  have hdu := hdu_diff y.1 hyIcc
  have hu := hu_diff y.1 hyIcc
  have hg := hg_diff y.1 hyIcc
  have hHd := hH_diff y hyIcc
  have hv := hv_diff y.1 hyIcc
  -- Bound each of the six terms in the raw inequality.
  have c1 : G * |deriv (intervalDomainLift (u₁ τ)) y.1
              - deriv (intervalDomainLift (u₂ τ)) y.1|
            ≤ G * D_g := mul_le_mul_of_nonneg_left hdu hGnn
  have c2 : (H + p.β * G^2) * |intervalDomainLift (u₁ τ) y.1
                                - intervalDomainLift (u₂ τ) y.1|
            ≤ (H + p.β * G^2) * D := mul_le_mul_of_nonneg_left hu hHβG2
  have c3 : (G_u + 2 * p.β * M * G) * |resolverGradReal p (u₁ τ) y.1
                                        - resolverGradReal p (u₂ τ) y.1|
            ≤ (G_u + 2 * p.β * M * G) * (L_R * D) :=
    mul_le_mul_of_nonneg_left hg hGu2pβMG
  have c4 : M * |intervalNeumannResolverRLap p (u₁ τ) y
                - intervalNeumannResolverRLap p (u₂ τ) y|
            ≤ M * (L_H * D) := mul_le_mul_of_nonneg_left hHd hMnn
  have hGMnn : 0 ≤ (G_u * G + M * H) * p.β :=
    mul_nonneg (add_nonneg (mul_nonneg hGunn hGnn) (mul_nonneg hMnn hHnn)) hβnn
  have c5 : (G_u * G + M * H) * p.β * |intervalDomainLift (v₁ τ) y.1
                                        - intervalDomainLift (v₂ τ) y.1|
            ≤ (G_u * G + M * H) * p.β * (L_V * D) :=
    mul_le_mul_of_nonneg_left hv hGMnn
  have hβMG2nn : 0 ≤ p.β * (M * G^2) * (p.β + 1) := by
    have : 0 ≤ p.β + 1 := by linarith
    exact mul_nonneg (mul_nonneg hβnn hMG2) this
  have c6 : p.β * (M * G^2) * (p.β + 1) * |intervalDomainLift (v₁ τ) y.1
                                            - intervalDomainLift (v₂ τ) y.1|
            ≤ p.β * (M * G^2) * (p.β + 1) * (L_V * D) :=
    mul_le_mul_of_nonneg_left hv hβMG2nn
  calc |intervalChemDivRepr p (u₁ τ) (v₁ τ) y
        - intervalChemDivRepr p (u₂ τ) (v₂ τ) y|
      ≤ G * |deriv (intervalDomainLift (u₁ τ)) y.1
              - deriv (intervalDomainLift (u₂ τ)) y.1|
        + (H + p.β * G^2) * |intervalDomainLift (u₁ τ) y.1
                              - intervalDomainLift (u₂ τ) y.1|
        + (G_u + 2 * p.β * M * G) * |resolverGradReal p (u₁ τ) y.1
                                      - resolverGradReal p (u₂ τ) y.1|
        + M * |intervalNeumannResolverRLap p (u₁ τ) y
                - intervalNeumannResolverRLap p (u₂ τ) y|
        + (G_u * G + M * H) * p.β * |intervalDomainLift (v₁ τ) y.1
                                      - intervalDomainLift (v₂ τ) y.1|
        + p.β * (M * G^2) * (p.β + 1) * |intervalDomainLift (v₁ τ) y.1
                                          - intervalDomainLift (v₂ τ) y.1| := hraw_y
    _ ≤ G * D_g
        + (H + p.β * G^2) * D
        + (G_u + 2 * p.β * M * G) * (L_R * D)
        + M * (L_H * D)
        + (G_u * G + M * H) * p.β * (L_V * D)
        + p.β * (M * G^2) * (p.β + 1) * (L_V * D) := by linarith
    _ = K_u * D + K_g * D_g := by rw [hKudef, hKgdef]; ring

/-! ### Documented gap: lifting chemDivRepr to chemDiv on the open interior

`intervalChemDivRepr` is the closed-form product-rule expansion of the
chemotaxis divergence using `resolverGradReal` for `∂ₓ(lift v)` and `RLap`
for `∂ₓ²(lift v)`.  To lift the Lipschitz bound above to the definitionally
honest `intervalDomainChemotaxisDiv p (u τ) v τ y = deriv (lift u · deriv (lift v) /
(1+lift v)^β) y`, one needs to prove the pointwise identity

  `intervalDomainChemotaxisDiv p (u τ) (v τ) y = intervalChemDivRepr p (u τ) (v τ) y`

for `y` in the open interior under the C¹_x snapshot hypothesis.  The route is
the standard product/quotient rule applied to the three-factor product

  `lift u(z) · ∂ₓ(lift v)(z) · (1+lift v(z))^{-β}`

(equal to `lift u(z) · ∂ₓ(lift v)(z) / (1+lift v(z))^β` since `1+lift v > 0`),
using the named `HasDerivAt` lemmas:

  * `HasDerivAt (intervalDomainLift (u τ)) (deriv (intervalDomainLift (u τ)) y) y`
    (from `IsPaper2ClassicalSolution`'s C² regularity, conjuncts 6,7,
    `solution_deriv_lift_continuousOn_Icc`).
  * `solution_lift_v_deriv_eq_resolverGrad` gives `deriv (lift v) z =
    resolverGradReal p u z` on `(0,1)`.
  * `resolverGradReal_hasDerivAt_RLap` gives `HasDerivAt (resolverGradReal p u)
    (RLap p u ⟨z,…⟩) z` on `[0,1]`.
  * `chemQuotient` HasDerivAt: standard `Real.hasDerivAt_rpow_const` chained
    with `lift v` derivative bridge.

The identity is mechanical from there, but the actual Lean wiring needs ~150
lines of `HasDerivAt.mul`/`HasDerivAt.add`/`HasDerivAt.deriv` plumbing,
including the `Filter.EventuallyEq` argument to switch from `lift u · deriv
(lift v) / (1+lift v)^β` to `lift u · resolverGradReal p u · (1+lift v)^{-β}`
on an open neighbourhood of the interior point.  We leave this gap precisely
documented; `intervalChemDivRepr_classical_K_D_form` is the genuine Lipschitz
output and is the natural intermediate for any subsequent attack on the
chemDiv proper. -/

/-! ### Axiom audit for the new C¹_x snapshot declarations.
Verified `#print axioms` on each of the following prints exactly
`[propext, Classical.choice, Quot.sound]` (the Mathlib-standard set):

  * `IntervalDomainClassicalC1Snapshot`
  * `chemQuotient2_mem_Ioc`
  * `chemQuotient2_lipschitz`
  * `intervalChemDivRepr`
  * `chemDivRepr_diff_pointwise_bound`
  * `intervalChemDivRepr_classical_diff_abs_le`
  * `intervalChemDivRepr_classical_K_D_form`

(checked on uisai1, build 8347 axiom-clean.) -/

end ShenWork.IntervalCoupledClassicalBallEstimates
