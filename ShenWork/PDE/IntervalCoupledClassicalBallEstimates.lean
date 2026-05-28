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
import ShenWork.PDE.IntervalCoupledBallEstimates
import ShenWork.PDE.IntervalResolverLaplacianBridge
import ShenWork.PDE.IntervalNeumannEllipticResolverR
import ShenWork.PDE.RegularityBootstrap
import ShenWork.Paper2.IntervalDomainL2UEnergyCombine
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

open ShenWork.Paper2 ShenWork.IntervalDomain ShenWork.PDE MeasureTheory
open ShenWork.IntervalResolverLaplacianBridge
open ShenWork.IntervalCoupledBallEstimates
open scoped Topology

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

/-! ### Pointwise identity `chemDiv = chemDivRepr` on the open interior

`intervalChemDivRepr` is the closed-form product-rule expansion of the
chemotaxis divergence using `resolverGradReal` for `∂ₓ(lift v)` and `RLap`
for `∂ₓ²(lift v)`.  At every interior `y ∈ (0,1)`, the definitionally honest
`intervalDomainChemotaxisDiv p (u τ) (v τ) y = deriv (lift u·deriv(lift v) /
(1+lift v)^β) y` agrees with the closed-form representative. -/

/-- **Pointwise identity `chemDiv = chemDivRepr` at every interior `y`.**

At every interior point `y` of a paper-2 classical solution, the chemotaxis
divergence (the spatial derivative of `lift u · deriv(lift v) / (1+lift v)^β`)
equals the closed-form product-rule expansion `intervalChemDivRepr`:

  `deriv(lift u)·g·(1+lift v)^{-β} + lift u·RLap·(1+lift v)^{-β}
   − β · lift u · g² · (1+lift v)^{-β-1}`

where `g = resolverGradReal p (u τ)` (the `∂ₓ(lift v)` identification on
`(0,1)` from `solution_lift_v_deriv_eq_resolverGrad`) and `RLap` is
`∂ₓ(resolverGradReal)` (from `deriv_resolverGradReal_eq_RLap`).

Route: `HasDerivAt.div` on `(lift u · deriv(lift v))/(1+lift v)^β`, with
`HasDerivAt` for the numerator (product rule, with `deriv(lift v)` having
derivative `RLap` via `EventuallyEq` swap with `resolverGradReal` and
`resolverGradReal_hasDerivAt_RLap`) and `HasDerivAt` for the denominator
(chain rule for `^β` at base `1+lift v > 0`). -/
theorem intervalDomainChemotaxisDiv_eq_chemDivRepr_interior
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    {y : intervalDomainPoint} (hy_int : y.1 ∈ Set.Ioo (0 : ℝ) 1) :
    intervalDomainChemotaxisDiv p (u τ) (v τ) y =
      intervalChemDivRepr p (u τ) (v τ) y := by
  classical
  -- Notation.
  set y₀ : ℝ := y.1 with hy₀
  have hy_Icc : y₀ ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy_int
  -- C² interior regularity of `lift u` and `lift v` (conjunct 3).
  have hC2u : ContDiffOn ℝ 2 (intervalDomainLift (u τ)) (Set.Ioo (0:ℝ) 1) :=
    (hsol.regularity.2.2.1 τ hτ).1
  have hC2v : ContDiffOn ℝ 2 (intervalDomainLift (v τ)) (Set.Ioo (0:ℝ) 1) :=
    (hsol.regularity.2.2.1 τ hτ).2
  -- HasDerivAt for `lift u` at `y₀`.
  have hU_diff : DifferentiableAt ℝ (intervalDomainLift (u τ)) y₀ :=
    (hC2u.differentiableOn (by norm_num)).differentiableAt
      (IsOpen.mem_nhds isOpen_Ioo hy_int)
  have hU_has : HasDerivAt (intervalDomainLift (u τ))
      (deriv (intervalDomainLift (u τ)) y₀) y₀ := hU_diff.hasDerivAt
  -- HasDerivAt for `lift v` at `y₀`.
  have hV_diff : DifferentiableAt ℝ (intervalDomainLift (v τ)) y₀ :=
    (hC2v.differentiableOn (by norm_num)).differentiableAt
      (IsOpen.mem_nhds isOpen_Ioo hy_int)
  -- deriv (lift v) y₀ = resolverGradReal p (u τ) y₀ on the interior.
  have hdv_eq : deriv (intervalDomainLift (v τ)) y₀
      = resolverGradReal p (u τ) y₀ :=
    solution_lift_v_deriv_eq_resolverGrad hsol hτ hy_int
  set g₀ : ℝ := resolverGradReal p (u τ) y₀ with hg₀_def
  have hV_has : HasDerivAt (intervalDomainLift (v τ)) g₀ y₀ := by
    have h := hV_diff.hasDerivAt
    rw [hdv_eq] at h; exact h
  -- HasDerivAt for `deriv (lift v)` at `y₀`.  This requires switching from
  -- `deriv (lift v)` to `resolverGradReal p (u τ)` via `EventuallyEq` on a
  -- neighborhood of `y₀`, then applying `resolverGradReal_hasDerivAt_RLap`.
  have hdecay : SourceCoeffQuadraticDecay p (u τ) :=
    sourceCoeffQuadraticDecay_of_solution hsol hτ
  -- `deriv (lift v) =ᶠ resolverGradReal p (u τ)` on `Ioo (0,1)` (a nbhd of `y₀`).
  have hdv_eqOn : ∀ x ∈ Set.Ioo (0:ℝ) 1,
      deriv (intervalDomainLift (v τ)) x = resolverGradReal p (u τ) x := by
    intro x hx
    exact solution_lift_v_deriv_eq_resolverGrad hsol hτ hx
  have hdv_eventuallyEq :
      deriv (intervalDomainLift (v τ)) =ᶠ[𝓝 y₀] resolverGradReal p (u τ) := by
    refine Filter.eventuallyEq_of_mem
      (IsOpen.mem_nhds isOpen_Ioo hy_int) ?_
    intro x hx
    exact hdv_eqOn x hx
  -- `HasDerivAt (resolverGradReal p (u τ)) (RLap …) y₀`.
  have hRgrad_has : HasDerivAt (fun z : ℝ => resolverGradReal p (u τ) z)
      (intervalNeumannResolverRLap p (u τ) ⟨y₀, hy_Icc⟩) y₀ :=
    resolverGradReal_hasDerivAt_RLap hdecay hy_Icc
  set H₀ : ℝ := intervalNeumannResolverRLap p (u τ) ⟨y₀, hy_Icc⟩ with hH₀_def
  have hW_has : HasDerivAt (deriv (intervalDomainLift (v τ))) H₀ y₀ :=
    hRgrad_has.congr_of_eventuallyEq hdv_eventuallyEq
  -- Positivity `1 + lift v y₀ > 0`.
  have hv_nn : 0 ≤ intervalDomainLift (v τ) y₀ :=
    solution_lift_v_nonneg_Icc hsol hτ y₀ hy_Icc
  set V₀ : ℝ := intervalDomainLift (v τ) y₀ with hV₀_def
  have hV₀_pos : 0 < 1 + V₀ := by linarith
  have hV₀_ne : (1 + V₀) ≠ 0 := ne_of_gt hV₀_pos
  -- HasDerivAt for `1 + lift v`.
  have hOnePlusV_has : HasDerivAt (fun z : ℝ => 1 + intervalDomainLift (v τ) z)
      g₀ y₀ := by
    have h := (hasDerivAt_const y₀ (1 : ℝ)).add hV_has
    have : (fun z : ℝ => (1 : ℝ) + intervalDomainLift (v τ) z)
        = (fun _ : ℝ => (1 : ℝ)) + intervalDomainLift (v τ) := by
      funext z; simp [Pi.add_apply]
    rw [this]
    have hzero : (0 : ℝ) + g₀ = g₀ := zero_add _
    simpa [hzero] using h
  -- HasDerivAt for `(1+V)^β` via chain rule.
  have hpow_at : HasDerivAt (fun x : ℝ => x ^ p.β)
      (p.β * (1 + V₀) ^ (p.β - 1)) (1 + V₀) :=
    Real.hasDerivAt_rpow_const (Or.inl hV₀_ne)
  have hD_has : HasDerivAt (fun z : ℝ => (1 + intervalDomainLift (v τ) z) ^ p.β)
      (p.β * (1 + V₀) ^ (p.β - 1) * g₀) y₀ := by
    have hcomp := hpow_at.comp y₀ hOnePlusV_has
    -- `hcomp : HasDerivAt ((fun x => x^β) ∘ (1 + lift v)) (β·(1+V₀)^(β-1) · g₀) y₀`
    simpa [Function.comp] using hcomp
  set D₀ : ℝ := (1 + V₀) ^ p.β with hD₀_def
  have hD₀_pos : 0 < D₀ := Real.rpow_pos_of_pos hV₀_pos _
  have hD₀_ne : D₀ ≠ 0 := ne_of_gt hD₀_pos
  -- HasDerivAt for the numerator `lift u · deriv (lift v)`.
  have hN_has : HasDerivAt
      (fun z : ℝ => intervalDomainLift (u τ) z * deriv (intervalDomainLift (v τ)) z)
      (deriv (intervalDomainLift (u τ)) y₀ * deriv (intervalDomainLift (v τ)) y₀
        + intervalDomainLift (u τ) y₀ * H₀) y₀ := by
    have := hU_has.mul hW_has
    simpa using this
  -- HasDerivAt for the chemotactic-flux quotient.
  have hQ_has : HasDerivAt
      (fun z : ℝ => intervalDomainLift (u τ) z * deriv (intervalDomainLift (v τ)) z
        / (1 + intervalDomainLift (v τ) z) ^ p.β)
      (((deriv (intervalDomainLift (u τ)) y₀ * deriv (intervalDomainLift (v τ)) y₀
            + intervalDomainLift (u τ) y₀ * H₀) * D₀
          - intervalDomainLift (u τ) y₀ * deriv (intervalDomainLift (v τ)) y₀
              * (p.β * (1 + V₀) ^ (p.β - 1) * g₀))
          / D₀ ^ 2) y₀ := by
    have := hN_has.div hD_has hD₀_ne
    -- Reshape the explicit `(1 + lift v _)^β` denominator to `D₀`.
    simpa using this
  -- `.deriv` of `hQ_has` gives the LHS in the divider form.  Unfold chemotaxisDiv.
  have hLHS : intervalDomainChemotaxisDiv p (u τ) (v τ) y
      = ((deriv (intervalDomainLift (u τ)) y₀ * deriv (intervalDomainLift (v τ)) y₀
            + intervalDomainLift (u τ) y₀ * H₀) * D₀
          - intervalDomainLift (u τ) y₀ * deriv (intervalDomainLift (v τ)) y₀
              * (p.β * (1 + V₀) ^ (p.β - 1) * g₀)) / D₀ ^ 2 := by
    unfold intervalDomainChemotaxisDiv
    exact hQ_has.deriv
  -- Now algebraically simplify the RHS of `hLHS` to `intervalChemDivRepr p (u τ) (v τ) y`.
  -- Use:  `D₀ = (1+V₀)^β`, hence
  --       `1/D₀ = (1+V₀)^(-β)`, and
  --       `(1+V₀)^(β-1) / D₀^2 = (1+V₀)^(β-1) * (1+V₀)^(-2β) = (1+V₀)^(-β-1)`.
  have hD₀_eq : D₀ = (1 + V₀) ^ p.β := hD₀_def
  -- Key rpow identities (using `1+V₀ > 0`).
  have hrpow_neg_β : (1 + V₀) ^ (-p.β) = ((1 + V₀) ^ p.β)⁻¹ :=
    Real.rpow_neg hV₀_pos.le p.β
  have hrpow_neg_β_minus1 : (1 + V₀) ^ (-p.β - 1) = ((1 + V₀) ^ (p.β + 1))⁻¹ := by
    have h := Real.rpow_neg hV₀_pos.le (p.β + 1)
    have : -(p.β + 1) = -p.β - 1 := by ring
    rw [this] at h; exact h
  -- `D₀^2 = (1+V₀)^(2β)` and `(1+V₀)^(β-1) / (1+V₀)^(2β) = (1+V₀)^(-β-1)`.
  have hD₀_sq : D₀ ^ 2 = (1 + V₀) ^ (2 * p.β) := by
    have h1 : D₀ ^ 2 = ((1 + V₀) ^ p.β) ^ (2 : ℕ) := by rw [hD₀_eq]
    rw [h1, ← Real.rpow_natCast ((1 + V₀) ^ p.β) 2,
        ← Real.rpow_mul hV₀_pos.le]
    congr 1; push_cast; ring
  -- `(1+V₀)^(β-1) / (1+V₀)^(2β) = (1+V₀)^(β-1 - 2β) = (1+V₀)^(-β-1)`.
  have hrpow_combine : (1 + V₀) ^ (p.β - 1) / (1 + V₀) ^ (2 * p.β)
      = (1 + V₀) ^ (-p.β - 1) := by
    rw [← Real.rpow_sub hV₀_pos]
    congr 1; ring
  -- Plug everything in.  Use `deriv(lift v) y₀ = g₀`.
  have hRHS_simplify :
      ((deriv (intervalDomainLift (u τ)) y₀ * deriv (intervalDomainLift (v τ)) y₀
          + intervalDomainLift (u τ) y₀ * H₀) * D₀
        - intervalDomainLift (u τ) y₀ * deriv (intervalDomainLift (v τ)) y₀
            * (p.β * (1 + V₀) ^ (p.β - 1) * g₀)) / D₀ ^ 2
      = intervalChemDivRepr p (u τ) (v τ) y := by
    -- Substitute `deriv (lift v) y₀ = g₀`.
    rw [hdv_eq]
    -- Now everything is in `g₀, H₀, V₀, U(y₀), D₀ = (1+V₀)^β`.
    -- Split the division.
    have hsplit :
        ((deriv (intervalDomainLift (u τ)) y₀ * g₀
            + intervalDomainLift (u τ) y₀ * H₀) * D₀
          - intervalDomainLift (u τ) y₀ * g₀
              * (p.β * (1 + V₀) ^ (p.β - 1) * g₀)) / D₀ ^ 2
        = (deriv (intervalDomainLift (u τ)) y₀ * g₀ * (1 / D₀)
          + intervalDomainLift (u τ) y₀ * H₀ * (1 / D₀))
            - p.β * intervalDomainLift (u τ) y₀ * g₀ ^ 2
                * ((1 + V₀) ^ (p.β - 1) / D₀ ^ 2) := by
      have hD₀_sq_ne : D₀ ^ 2 ≠ 0 := pow_ne_zero 2 hD₀_ne
      field_simp
    rw [hsplit]
    -- `1 / D₀ = (1+V₀)^(-β)`.
    have h1D₀ : (1 : ℝ) / D₀ = (1 + V₀) ^ (-p.β) := by
      rw [hrpow_neg_β, hD₀_eq, one_div]
    rw [h1D₀]
    -- `(1+V₀)^(β-1) / D₀^2 = (1+V₀)^(-β-1)`.
    rw [hD₀_sq, hrpow_combine]
    -- Identify `H₀` with `intervalNeumannResolverRLap p (u τ) y` (same fun on `.1`).
    have hH₀_eq : H₀ = intervalNeumannResolverRLap p (u τ) y := by
      rw [hH₀_def]; rfl
    -- Unfold `intervalChemDivRepr` and `set`s so the polynomial identity can be
    -- closed by `ring`.
    unfold intervalChemDivRepr
    -- After unfolding RHS, the `set` abbreviations on the LHS are `g₀, V₀, H₀, y₀`.
    -- Substitute each in terms of the actual expressions, then match via `ring`.
    rw [hg₀_def, hV₀_def, hH₀_eq, hy₀]
  rw [hLHS, hRHS_simplify]

/-- **Corollary: chemDiv `K_u · D + K_g · D_g` Lipschitz on the C¹_x snapshot
ball at interior `y`.**  Combines the pointwise identity
`intervalDomainChemotaxisDiv_eq_chemDivRepr_interior` with
`intervalChemDivRepr_classical_K_D_form`. -/
theorem intervalDomainChemotaxisDiv_classical_K_D_form_interior
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
    (hDnn : 0 ≤ D) (hDgnn : 0 ≤ D_g)
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
      ∀ y : intervalDomainPoint, y.1 ∈ Set.Ioo (0 : ℝ) 1 →
        |intervalDomainChemotaxisDiv p (u₁ τ) (v₁ τ) y
          - intervalDomainChemotaxisDiv p (u₂ τ) (v₂ τ) y|
        ≤ K_u * D + K_g * D_g := by
  classical
  obtain ⟨G, K_u, K_g, hGnn, hKunn, hKgnn, hbound⟩ :=
    intervalChemDivRepr_classical_K_D_form
      hsnap₁ hsnap₂ hMnn hGunn hτ hHnn hH₁ hH₂
      hDnn hDgnn hLVnn hLRnn hLHnn
      hu_diff hdu_diff hv_diff hg_diff hH_diff
  refine ⟨G, K_u, K_g, hGnn, hKunn, hKgnn, ?_⟩
  intro y hy_int
  have hy_Icc : y.1 ∈ Set.Icc (0:ℝ) 1 := Set.Ioo_subset_Icc_self hy_int
  have h₁ := intervalDomainChemotaxisDiv_eq_chemDivRepr_interior
    hsnap₁.isSolution hτ (y := y) hy_int
  have h₂ := intervalDomainChemotaxisDiv_eq_chemDivRepr_interior
    hsnap₂.isSolution hτ (y := y) hy_int
  rw [h₁, h₂]
  exact hbound y hy_Icc

/-! ## Classical-strength C¹_x parallel ball estimates predicate

The existing `IntervalCoupledResolverBallEstimates` (in
`IntervalDomainExistence.lean`, line 1959) is the four-conjunct interface that
discharges the coupled Duhamel contraction on a sup-norm trajectory ball.  Its
chemotaxis-divergence conjunct (`hchem`) is parameterized over
`intervalTrajectoryBoundedOn T M u`, a sup-norm-only ball hypothesis whose
hypotheses cannot fire `intervalDomainChemotaxisDiv_classical_K_D_form_interior`
(which needs `IntervalDomainClassicalC1Snapshot` strength).

We now define a STRONGER parallel ball-estimates predicate
`IntervalCoupledClassicalC1BallEstimates` whose chemotaxis conjunct
is parameterized over **C¹_x classical snapshots**, in the
`K_u · D + K_g · D_g` two-dimensional shape of the proven Lipschitz.  This is
the natural target for the chemDiv Lipschitz on the C¹_x ball.

The four conjuncts of the parallel predicate are:

  * (`hmap`) Coupled Duhamel maps the C¹_x ball into itself (the Duhamel
    operator preserves both the sup-norm `M` and the C¹_x gradient-sup `G_u`
    when applied to a C¹_x snapshot trajectory).  This is the genuine
    Schauder/heat-kernel-smoothing step — recorded as an EXPLICIT FIELD,
    not discharged.
  * (`hchem`) chemDiv pointwise Lipschitz on the C¹_x ball:
    `|chemDiv₁ − chemDiv₂| ≤ K_u · D + K_g · D_g` at interior `y`, where
    `D = sup |Δ(lift u)|`, `D_g = sup |Δ(deriv lift u)|`.  ASSEMBLED from
    `intervalDomainChemotaxisDiv_classical_K_D_form_interior` (proved above)
    plus the named resolver Lipschitz constants `L_V, L_R, L_H` and an `H`
    sup bound on `intervalNeumannResolverRLap` on the ball.
  * (`hint`) Time-integrability of the Duhamel integrand:
    `s ↦ S(t-s)(lift(coupledSource(u s, R(u s))))(x)` on `Icc 0 t`.  Assembled
    from `intervalCoupledDuhamelIntegrand_integrableOn` given chemDiv-sup,
    log-sup and a.e.-strong-measurability of the semigroup integrand.
  * (`hlift_int`) Integrability of the lifted coupled source against the
    interval measure.  Assembled from `intervalCoupledSource_lift_integrable`
    given chemDiv-sup, log-sup and a.e.-strong-measurability of the lift.

The structure is a `Prop`-valued predicate so it has no implementation gap of
its own; constructors that supply the four conjuncts compose into it. -/

/-- **C¹_x classical-strength parallel ball-estimates predicate.**

The four conjuncts (hmap, hchem, hint, hlift_int) for the coupled chemotaxis-
logistic Duhamel scaffold, parameterized over **C¹_x classical snapshots**
rather than sup-norm trajectory ball.  The `hchem` conjunct is in the
two-dimensional `K_u · D + K_g · D_g` shape supplied by
`intervalDomainChemotaxisDiv_classical_K_D_form_interior`.

Type parameters:
  * `p : CM2Params` — chemotaxis parameters.
  * `R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ` — the elliptic
    resolver mapping `u ↦ v`.
  * `u₀ : intervalDomainPoint → ℝ` — initial datum.
  * `T M G_u K_u K_g : ℝ` — time horizon, sup bound, C¹_x gradient sup bound,
    and the two-dimensional Lipschitz constants for chemDiv. -/
def IntervalCoupledClassicalC1BallEstimates
    (p : CM2Params)
    (R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ)
    (u₀ : intervalDomainPoint → ℝ)
    (T M G_u K_u K_g : ℝ) : Prop :=
  -- (hmap): Coupled Duhamel preserves the C¹_x ball.  Explicit field — the
  -- genuine Schauder/heat-kernel-smoothing step required for the C¹_x ball.
  (∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
        IntervalDomainClassicalC1Snapshot p T M G_u
          (fun t : ℝ => fun x : intervalDomainPoint =>
            intervalCoupledDuhamelOperator p R u₀ u t x) v) ∧
  -- (hchem): chemDiv K_u · D + K_g · D_g Lipschitz at interior y on the
  -- C¹_x ball.  Discharged by `intervalDomainChemotaxisDiv_classical_K_D_form_interior`.
  (∀ (u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ) (D D_g : ℝ),
      0 ≤ D → 0 ≤ D_g →
      IntervalDomainClassicalC1Snapshot p T M G_u u₁ v₁ →
      IntervalDomainClassicalC1Snapshot p T M G_u u₂ v₂ →
      (∀ τ x, τ ∈ Set.Ioo (0:ℝ) T → x ∈ Set.Icc (0:ℝ) 1 →
        |intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x| ≤ D) →
      (∀ τ x, τ ∈ Set.Ioo (0:ℝ) T → x ∈ Set.Icc (0:ℝ) 1 →
        |deriv (intervalDomainLift (u₁ τ)) x
          - deriv (intervalDomainLift (u₂ τ)) x| ≤ D_g) →
        ∀ (τ : ℝ) (y : intervalDomainPoint),
          τ ∈ Set.Ioo (0:ℝ) T → y.1 ∈ Set.Ioo (0:ℝ) 1 →
          |intervalDomainChemotaxisDiv p (u₁ τ) (v₁ τ) y -
            intervalDomainChemotaxisDiv p (u₂ τ) (v₂ τ) y| ≤ K_u * D + K_g * D_g) ∧
  -- (hint): Time-integrability of Duhamel integrand on the C¹_x ball.
  (∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
        ∀ (t : ℝ) (x : intervalDomainPoint), 0 ≤ t → t ≤ T →
          MeasureTheory.IntegrableOn
            (fun s => intervalSemigroupOperator 1 (t - s)
              (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x.1)
            (Set.Icc 0 t) MeasureTheory.volume) ∧
  -- (hlift_int): Integrability of the lifted coupled source on the C¹_x ball.
  (∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
        ∀ s, 0 ≤ s → s ≤ T →
          MeasureTheory.Integrable
            (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
            (intervalMeasure 1))

namespace IntervalCoupledClassicalC1BallEstimates

variable {p : CM2Params}
  {R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ}
  {u₀ : intervalDomainPoint → ℝ} {T M G_u K_u K_g : ℝ}

theorem hmap (h : IntervalCoupledClassicalC1BallEstimates p R u₀ T M G_u K_u K_g) :
    ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
        IntervalDomainClassicalC1Snapshot p T M G_u
          (fun t : ℝ => fun x : intervalDomainPoint =>
            intervalCoupledDuhamelOperator p R u₀ u t x) v :=
  h.1

theorem hchem (h : IntervalCoupledClassicalC1BallEstimates p R u₀ T M G_u K_u K_g) :
    ∀ (u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ) (D D_g : ℝ),
      0 ≤ D → 0 ≤ D_g →
      IntervalDomainClassicalC1Snapshot p T M G_u u₁ v₁ →
      IntervalDomainClassicalC1Snapshot p T M G_u u₂ v₂ →
      (∀ τ x, τ ∈ Set.Ioo (0:ℝ) T → x ∈ Set.Icc (0:ℝ) 1 →
        |intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x| ≤ D) →
      (∀ τ x, τ ∈ Set.Ioo (0:ℝ) T → x ∈ Set.Icc (0:ℝ) 1 →
        |deriv (intervalDomainLift (u₁ τ)) x
          - deriv (intervalDomainLift (u₂ τ)) x| ≤ D_g) →
        ∀ (τ : ℝ) (y : intervalDomainPoint),
          τ ∈ Set.Ioo (0:ℝ) T → y.1 ∈ Set.Ioo (0:ℝ) 1 →
          |intervalDomainChemotaxisDiv p (u₁ τ) (v₁ τ) y -
            intervalDomainChemotaxisDiv p (u₂ τ) (v₂ τ) y| ≤ K_u * D + K_g * D_g :=
  h.2.1

theorem hint (h : IntervalCoupledClassicalC1BallEstimates p R u₀ T M G_u K_u K_g) :
    ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
        ∀ (t : ℝ) (x : intervalDomainPoint), 0 ≤ t → t ≤ T →
          MeasureTheory.IntegrableOn
            (fun s => intervalSemigroupOperator 1 (t - s)
              (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x.1)
            (Set.Icc 0 t) MeasureTheory.volume :=
  h.2.2.1

theorem hlift_int (h : IntervalCoupledClassicalC1BallEstimates p R u₀ T M G_u K_u K_g) :
    ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
        ∀ s, 0 ≤ s → s ≤ T →
          MeasureTheory.Integrable
            (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
            (intervalMeasure 1) :=
  h.2.2.2

end IntervalCoupledClassicalC1BallEstimates

/-! ### Assembly of `hchem` from the proven chemDiv K-form

The `hchem` conjunct in the structure form has fixed `K_u K_g` (parameters
of the structure).  To assemble it from
`intervalDomainChemotaxisDiv_classical_K_D_form_interior`, we additionally need
a UNIFORM L∞ sup bound `G` on `resolverGradReal` over the trajectory ball
(this absorbs the per-snapshot `G` that the K-form theorem extracts via
`resolverGradReal_bounded` into a uniform constant), plus the L∞ `H` sup
bound on `intervalNeumannResolverRLap` and the three resolver-Lipschitz
factorizations `(L_V, L_R, L_H)`.  Given these, `K_u, K_g` are fixed by:

```
  K_u := (H + p.β · G²) + (G_u + 2 p.β · M · G) · L_R + M · L_H
         + (G_u · G + M · H) · p.β · L_V
         + p.β · (M · G²) · (p.β + 1) · L_V
  K_g := G
```

and the chemDiv `K_u · D + K_g · D_g` bound holds across the entire ball. -/

/-- **Per-pair chemDiv `K_u · D + K_g · D_g` Lipschitz against a uniform `G`.**

Strengthens `intervalDomainChemotaxisDiv_classical_K_D_form_interior` by
threading a UNIFORM `G` sup bound (rather than the snapshot-extracted one) on
`resolverGradReal`, yielding FIXED `K_u, K_g` constants that no longer depend
on the specific snapshot pair.  This is the per-pair piece of `hchem`. -/
theorem intervalDomainChemotaxisDiv_classical_K_D_form_interior_uniformG
    {p : CM2Params} {T M G_u : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsnap₁ : IntervalDomainClassicalC1Snapshot p T M G_u u₁ v₁)
    (hsnap₂ : IntervalDomainClassicalC1Snapshot p T M G_u u₂ v₂)
    (hMnn : 0 ≤ M) (hGunn : 0 ≤ G_u)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    {G H : ℝ} (hGnn : 0 ≤ G) (hHnn : 0 ≤ H)
    (hG₁ : ∀ x ∈ Set.Icc (0:ℝ) 1, |resolverGradReal p (u₁ τ) x| ≤ G)
    (hG₂ : ∀ x ∈ Set.Icc (0:ℝ) 1, |resolverGradReal p (u₂ τ) x| ≤ G)
    (hH₁ : ∀ y : intervalDomainPoint, y.1 ∈ Set.Icc (0:ℝ) 1 →
      |intervalNeumannResolverRLap p (u₁ τ) y| ≤ H)
    (hH₂ : ∀ y : intervalDomainPoint, y.1 ∈ Set.Icc (0:ℝ) 1 →
      |intervalNeumannResolverRLap p (u₂ τ) y| ≤ H)
    {D D_g L_V L_R L_H : ℝ}
    (hDnn : 0 ≤ D) (hDgnn : 0 ≤ D_g)
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
    ∀ y : intervalDomainPoint, y.1 ∈ Set.Ioo (0 : ℝ) 1 →
      |intervalDomainChemotaxisDiv p (u₁ τ) (v₁ τ) y
        - intervalDomainChemotaxisDiv p (u₂ τ) (v₂ τ) y|
        ≤ ((H + p.β * G^2)
              + (G_u + 2 * p.β * M * G) * L_R
              + M * L_H
              + (G_u * G + M * H) * p.β * L_V
              + p.β * (M * G^2) * (p.β + 1) * L_V) * D
          + G * D_g := by
  classical
  -- The K-form theorem extracts its `G` from `resolverGradReal_bounded`.
  -- We reroute via the underlying `intervalChemDivRepr_classical_diff_abs_le`
  -- which factors through any uniform `G` bound on resolverGradReal — except
  -- the file's lemma uses `max G₁ G₂`.  We therefore prove the bound by
  -- directly invoking `chemDivRepr_diff_pointwise_bound` with our supplied
  -- uniform `G`, then composing with the chemDiv = chemDivRepr identity.
  intro y hy_int
  have hy_Icc : y.1 ∈ Set.Icc (0:ℝ) 1 := Set.Ioo_subset_Icc_self hy_int
  have hsol₁ := hsnap₁.isSolution
  have hsol₂ := hsnap₂.isSolution
  have hv₁nn := solution_lift_v_nonneg_Icc hsol₁ hτ
  have hv₂nn := solution_lift_v_nonneg_Icc hsol₂ hτ
  have hβnn : 0 ≤ p.β := p.hβ
  -- Per-factor bounds.
  have ha₁ : |intervalDomainLift (u₁ τ) y.1| ≤ M := hsnap₁.sup_bound hτ hy_Icc
  have ha₂ : |intervalDomainLift (u₂ τ) y.1| ≤ M := hsnap₂.sup_bound hτ hy_Icc
  have hdu₁ : |deriv (intervalDomainLift (u₁ τ)) y.1| ≤ G_u :=
    hsnap₁.grad_sup_bound hτ hy_Icc
  have hdu₂ : |deriv (intervalDomainLift (u₂ τ)) y.1| ≤ G_u :=
    hsnap₂.grad_sup_bound hτ hy_Icc
  have hgv₁ : |resolverGradReal p (u₁ τ) y.1| ≤ G := hG₁ y.1 hy_Icc
  have hgv₂ : |resolverGradReal p (u₂ τ) y.1| ≤ G := hG₂ y.1 hy_Icc
  have hgp₁ : |intervalNeumannResolverRLap p (u₁ τ) y| ≤ H := hH₁ y hy_Icc
  have hgp₂ : |intervalNeumannResolverRLap p (u₂ τ) y| ≤ H := hH₂ y hy_Icc
  have hq₁ := chemQuotient_mem_Ioc hβnn (hv₁nn y.1 hy_Icc)
  have hq₂ := chemQuotient_mem_Ioc hβnn (hv₂nn y.1 hy_Icc)
  have hqLip := chemQuotient_lipschitz hβnn (hv₁nn y.1 hy_Icc) (hv₂nn y.1 hy_Icc)
  have hqp₁ := chemQuotient2_mem_Ioc hβnn (hv₁nn y.1 hy_Icc)
  have hqp₂ := chemQuotient2_mem_Ioc hβnn (hv₂nn y.1 hy_Icc)
  have hqpLip := chemQuotient2_lipschitz hβnn (hv₁nn y.1 hy_Icc) (hv₂nn y.1 hy_Icc)
  -- Algebraic bound on the chemDivRepr difference.
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
    hdu₁ hdu₂ ha₁ ha₂ hgv₁ hgv₂ hgp₁ hgp₂
    hq₁.1.le hq₁.2 hq₂.1.le hq₂.2
    hqp₁.1.le hqp₁.2 hqp₂.1.le hqp₂.2
    hMnn hGunn hGnn hHnn hβnn hqLip hqpLip
  -- chemDiv = chemDivRepr identity on the interior.
  have hch₁ := intervalDomainChemotaxisDiv_eq_chemDivRepr_interior
    hsol₁ hτ (y := y) hy_int
  have hch₂ := intervalDomainChemotaxisDiv_eq_chemDivRepr_interior
    hsol₂ hτ (y := y) hy_int
  have hu := hu_diff y.1 hy_Icc
  have hdu := hdu_diff y.1 hy_Icc
  have hv := hv_diff y.1 hy_Icc
  have hg := hg_diff y.1 hy_Icc
  have hHd := hH_diff y hy_Icc
  have hHβG2 : 0 ≤ H + p.β * G^2 :=
    add_nonneg hHnn (mul_nonneg hβnn (sq_nonneg _))
  have h2pβMG : 0 ≤ 2 * p.β * M * G := by
    have : 0 ≤ 2 * p.β := by positivity
    exact mul_nonneg (mul_nonneg this hMnn) hGnn
  have hGu2pβMG : 0 ≤ G_u + 2 * p.β * M * G := add_nonneg hGunn h2pβMG
  have hMG : 0 ≤ M * G := mul_nonneg hMnn hGnn
  have hGMnn : 0 ≤ (G_u * G + M * H) * p.β :=
    mul_nonneg (add_nonneg (mul_nonneg hGunn hGnn) (mul_nonneg hMnn hHnn)) hβnn
  have hβMG2nn : 0 ≤ p.β * (M * G^2) * (p.β + 1) := by
    have hMG2 : 0 ≤ M * G^2 := mul_nonneg hMnn (sq_nonneg _)
    have : 0 ≤ p.β + 1 := by linarith
    exact mul_nonneg (mul_nonneg hβnn hMG2) this
  -- Bound each factor difference.
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
  have c5 : (G_u * G + M * H) * p.β * |intervalDomainLift (v₁ τ) y.1
                                        - intervalDomainLift (v₂ τ) y.1|
            ≤ (G_u * G + M * H) * p.β * (L_V * D) :=
    mul_le_mul_of_nonneg_left hv hGMnn
  have c6 : p.β * (M * G^2) * (p.β + 1) * |intervalDomainLift (v₁ τ) y.1
                                            - intervalDomainLift (v₂ τ) y.1|
            ≤ p.β * (M * G^2) * (p.β + 1) * (L_V * D) :=
    mul_le_mul_of_nonneg_left hv hβMG2nn
  -- Unfold `intervalChemDivRepr` on both sides and combine.
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
  rw [hch₁, hch₂, hrepr_unfold₁, hrepr_unfold₂]
  -- The algebraic chemDivRepr bound gives 8 terms; we bound them
  -- by the closed-form K_u·D + K_g·D_g expression.
  calc |(deriv (intervalDomainLift (u₁ τ)) y.1 * resolverGradReal p (u₁ τ) y.1
              * (1 + intervalDomainLift (v₁ τ) y.1) ^ (-p.β)
          + intervalDomainLift (u₁ τ) y.1 * intervalNeumannResolverRLap p (u₁ τ) y
              * (1 + intervalDomainLift (v₁ τ) y.1) ^ (-p.β)
          - p.β * intervalDomainLift (u₁ τ) y.1
              * (resolverGradReal p (u₁ τ) y.1)^2
              * (1 + intervalDomainLift (v₁ τ) y.1) ^ (-p.β - 1))
        - (deriv (intervalDomainLift (u₂ τ)) y.1 * resolverGradReal p (u₂ τ) y.1
              * (1 + intervalDomainLift (v₂ τ) y.1) ^ (-p.β)
          + intervalDomainLift (u₂ τ) y.1 * intervalNeumannResolverRLap p (u₂ τ) y
              * (1 + intervalDomainLift (v₂ τ) y.1) ^ (-p.β)
          - p.β * intervalDomainLift (u₂ τ) y.1
              * (resolverGradReal p (u₂ τ) y.1)^2
              * (1 + intervalDomainLift (v₂ τ) y.1) ^ (-p.β - 1))|
      ≤ G * |deriv (intervalDomainLift (u₁ τ)) y.1
              - deriv (intervalDomainLift (u₂ τ)) y.1|
        + H * |intervalDomainLift (u₁ τ) y.1 - intervalDomainLift (u₂ τ) y.1|
        + M * |intervalNeumannResolverRLap p (u₁ τ) y
                - intervalNeumannResolverRLap p (u₂ τ) y|
        + G_u * |resolverGradReal p (u₁ τ) y.1 - resolverGradReal p (u₂ τ) y.1|
        + (G_u * G + M * H) * p.β * |intervalDomainLift (v₁ τ) y.1
                                      - intervalDomainLift (v₂ τ) y.1|
        + p.β * (M * G^2) * (p.β + 1) * |intervalDomainLift (v₁ τ) y.1
                                          - intervalDomainLift (v₂ τ) y.1|
        + p.β * G^2 * |intervalDomainLift (u₁ τ) y.1 - intervalDomainLift (u₂ τ) y.1|
        + p.β * M * (G + G) * |resolverGradReal p (u₁ τ) y.1
                                - resolverGradReal p (u₂ τ) y.1| := hbound
    _ ≤ G * D_g
        + H * D
        + M * (L_H * D)
        + G_u * (L_R * D)
        + (G_u * G + M * H) * p.β * (L_V * D)
        + p.β * (M * G^2) * (p.β + 1) * (L_V * D)
        + p.β * G^2 * D
        + p.β * M * (G + G) * (L_R * D) := by
        have hH_nn := hHnn
        have hM_nn := hMnn
        have hGu_nn := hGunn
        have hG_nn := hGnn
        have hHd_le : H * |intervalDomainLift (u₁ τ) y.1
                            - intervalDomainLift (u₂ τ) y.1| ≤ H * D :=
          mul_le_mul_of_nonneg_left hu hHnn
        have hMLHd : M * |intervalNeumannResolverRLap p (u₁ τ) y
                            - intervalNeumannResolverRLap p (u₂ τ) y|
                      ≤ M * (L_H * D) := mul_le_mul_of_nonneg_left hHd hMnn
        have hGuLR : G_u * |resolverGradReal p (u₁ τ) y.1
                            - resolverGradReal p (u₂ τ) y.1| ≤ G_u * (L_R * D) :=
          mul_le_mul_of_nonneg_left hg hGunn
        have hβG2_nn : 0 ≤ p.β * G^2 := mul_nonneg hβnn (sq_nonneg _)
        have hβG2d : p.β * G^2 * |intervalDomainLift (u₁ τ) y.1
                                  - intervalDomainLift (u₂ τ) y.1| ≤ p.β * G^2 * D :=
          mul_le_mul_of_nonneg_left hu hβG2_nn
        have hβM2G_nn : 0 ≤ p.β * M * (G + G) := by positivity
        have hβM2Gg : p.β * M * (G + G) * |resolverGradReal p (u₁ τ) y.1
                                            - resolverGradReal p (u₂ τ) y.1|
                       ≤ p.β * M * (G + G) * (L_R * D) :=
          mul_le_mul_of_nonneg_left hg hβM2G_nn
        linarith [c1, hHd_le, hMLHd, hGuLR, c5, c6, hβG2d, hβM2Gg]
    _ = ((H + p.β * G^2)
              + (G_u + 2 * p.β * M * G) * L_R
              + M * L_H
              + (G_u * G + M * H) * p.β * L_V
              + p.β * (M * G^2) * (p.β + 1) * L_V) * D
          + G * D_g := by ring

/-- **Assembly of `IntervalCoupledClassicalC1BallEstimates`** from the
constituent inputs: an explicit `hmap` (Schauder / heat-kernel-smoothing
deferred), the proven chemDiv K-form (uniform-`G` version), and integrability
inputs (chemDiv-sup, log-sup, and a.e.-strong-measurability of the integrand
and the lift). -/
theorem intervalCoupledClassicalC1BallEstimates_assemble
    {p : CM2Params}
    {R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {T M G_u : ℝ}
    (hMnn : 0 ≤ M) (hGunn : 0 ≤ G_u)
    -- (hmap): supplied as an explicit input (Schauder).
    (hmap : ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
        IntervalDomainClassicalC1Snapshot p T M G_u
          (fun t : ℝ => fun x : intervalDomainPoint =>
            intervalCoupledDuhamelOperator p R u₀ u t x) v)
    -- chemDiv K-form inputs:
    {G H L_V L_R L_H : ℝ}
    (hGnn : 0 ≤ G) (hHnn : 0 ≤ H)
    (hLVnn : 0 ≤ L_V) (hLRnn : 0 ≤ L_R) (hLHnn : 0 ≤ L_H)
    (hG_sup : ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
        ∀ τ : ℝ, τ ∈ Set.Ioo (0:ℝ) T →
          ∀ x ∈ Set.Icc (0:ℝ) 1,
            |resolverGradReal p (u τ) x| ≤ G)
    (hH_sup : ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
        ∀ τ : ℝ, τ ∈ Set.Ioo (0:ℝ) T →
          ∀ y : intervalDomainPoint, y.1 ∈ Set.Icc (0:ℝ) 1 →
            |intervalNeumannResolverRLap p (u τ) y| ≤ H)
    (hv_lip : ∀ (u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
      0 ≤ D →
      IntervalDomainClassicalC1Snapshot p T M G_u u₁ v₁ →
      IntervalDomainClassicalC1Snapshot p T M G_u u₂ v₂ →
      (∀ τ x, τ ∈ Set.Ioo (0:ℝ) T → x ∈ Set.Icc (0:ℝ) 1 →
        |intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x| ≤ D) →
        ∀ τ : ℝ, τ ∈ Set.Ioo (0:ℝ) T →
          ∀ x ∈ Set.Icc (0:ℝ) 1,
            |intervalDomainLift (v₁ τ) x - intervalDomainLift (v₂ τ) x| ≤ L_V * D)
    (hg_lip : ∀ (u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
      0 ≤ D →
      IntervalDomainClassicalC1Snapshot p T M G_u u₁ v₁ →
      IntervalDomainClassicalC1Snapshot p T M G_u u₂ v₂ →
      (∀ τ x, τ ∈ Set.Ioo (0:ℝ) T → x ∈ Set.Icc (0:ℝ) 1 →
        |intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x| ≤ D) →
        ∀ τ : ℝ, τ ∈ Set.Ioo (0:ℝ) T →
          ∀ x ∈ Set.Icc (0:ℝ) 1,
            |resolverGradReal p (u₁ τ) x - resolverGradReal p (u₂ τ) x| ≤ L_R * D)
    (hH_lip : ∀ (u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
      0 ≤ D →
      IntervalDomainClassicalC1Snapshot p T M G_u u₁ v₁ →
      IntervalDomainClassicalC1Snapshot p T M G_u u₂ v₂ →
      (∀ τ x, τ ∈ Set.Ioo (0:ℝ) T → x ∈ Set.Icc (0:ℝ) 1 →
        |intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x| ≤ D) →
        ∀ τ : ℝ, τ ∈ Set.Ioo (0:ℝ) T →
          ∀ y : intervalDomainPoint, y.1 ∈ Set.Icc (0:ℝ) 1 →
            |intervalNeumannResolverRLap p (u₁ τ) y
              - intervalNeumannResolverRLap p (u₂ τ) y| ≤ L_H * D)
    -- Integrability inputs:
    {Kc Lc : ℝ} (hKc : 0 ≤ Kc) (hLc : 0 ≤ Lc)
    (hchem_sup_ball : ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
        ∀ τ : ℝ, 0 ≤ τ → τ ≤ T →
          ∀ y : intervalDomainPoint,
            |intervalDomainChemotaxisDiv p (u τ) (R (u τ)) y| ≤ Kc)
    (hlog_sup_ball : ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
        ∀ τ : ℝ, 0 ≤ τ → τ ≤ T →
          ∀ y : intervalDomainPoint,
            |intervalLogisticSource p (u τ) y| ≤ Lc)
    (hsemigroup_meas : ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
        ∀ (t : ℝ) (x : intervalDomainPoint), 0 ≤ t → t ≤ T →
          AEStronglyMeasurable
            (fun s => intervalSemigroupOperator 1 (t - s)
              (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x.1)
            (volume.restrict (Set.Icc 0 t)))
    (hlift_meas : ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
        ∀ s, 0 ≤ s → s ≤ T →
          AEStronglyMeasurable
            (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
            (intervalMeasure 1)) :
    let K_u : ℝ := (H + p.β * G^2)
              + (G_u + 2 * p.β * M * G) * L_R
              + M * L_H
              + (G_u * G + M * H) * p.β * L_V
              + p.β * (M * G^2) * (p.β + 1) * L_V
    let K_g : ℝ := G
    IntervalCoupledClassicalC1BallEstimates p R u₀ T M G_u K_u K_g := by
  classical
  intro K_u K_g
  refine ⟨hmap, ?_, ?_, ?_⟩
  · -- hchem
    intro u₁ v₁ u₂ v₂ D D_g hDnn hDgnn hsnap₁ hsnap₂ hu_diff hdu_diff τ y hτ hy_int
    have hG₁ : ∀ x ∈ Set.Icc (0:ℝ) 1, |resolverGradReal p (u₁ τ) x| ≤ G :=
      fun x hx => hG_sup u₁ v₁ hsnap₁ τ hτ x hx
    have hG₂ : ∀ x ∈ Set.Icc (0:ℝ) 1, |resolverGradReal p (u₂ τ) x| ≤ G :=
      fun x hx => hG_sup u₂ v₂ hsnap₂ τ hτ x hx
    have hH₁ : ∀ y : intervalDomainPoint, y.1 ∈ Set.Icc (0:ℝ) 1 →
        |intervalNeumannResolverRLap p (u₁ τ) y| ≤ H :=
      fun y hy => hH_sup u₁ v₁ hsnap₁ τ hτ y hy
    have hH₂ : ∀ y : intervalDomainPoint, y.1 ∈ Set.Icc (0:ℝ) 1 →
        |intervalNeumannResolverRLap p (u₂ τ) y| ≤ H :=
      fun y hy => hH_sup u₂ v₂ hsnap₂ τ hτ y hy
    have hu_τ : ∀ x ∈ Set.Icc (0:ℝ) 1,
        |intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x| ≤ D :=
      fun x hx => hu_diff τ x hτ hx
    have hdu_τ : ∀ x ∈ Set.Icc (0:ℝ) 1,
        |deriv (intervalDomainLift (u₁ τ)) x
          - deriv (intervalDomainLift (u₂ τ)) x| ≤ D_g :=
      fun x hx => hdu_diff τ x hτ hx
    have hv_τ : ∀ x ∈ Set.Icc (0:ℝ) 1,
        |intervalDomainLift (v₁ τ) x - intervalDomainLift (v₂ τ) x| ≤ L_V * D :=
      hv_lip u₁ v₁ u₂ v₂ D hDnn hsnap₁ hsnap₂ hu_diff τ hτ
    have hg_τ : ∀ x ∈ Set.Icc (0:ℝ) 1,
        |resolverGradReal p (u₁ τ) x - resolverGradReal p (u₂ τ) x| ≤ L_R * D :=
      hg_lip u₁ v₁ u₂ v₂ D hDnn hsnap₁ hsnap₂ hu_diff τ hτ
    have hH_τ : ∀ y : intervalDomainPoint, y.1 ∈ Set.Icc (0:ℝ) 1 →
        |intervalNeumannResolverRLap p (u₁ τ) y
          - intervalNeumannResolverRLap p (u₂ τ) y| ≤ L_H * D :=
      hH_lip u₁ v₁ u₂ v₂ D hDnn hsnap₁ hsnap₂ hu_diff τ hτ
    exact intervalDomainChemotaxisDiv_classical_K_D_form_interior_uniformG
      hsnap₁ hsnap₂ hMnn hGunn hτ hGnn hHnn hG₁ hG₂ hH₁ hH₂
      hDnn hDgnn hLVnn hLRnn hLHnn hu_τ hdu_τ hv_τ hg_τ hH_τ y hy_int
  · -- hint
    intro u v hsnap t x ht0 htT
    refine intervalCoupledDuhamelIntegrand_integrableOn p R u (Kc := Kc) (Lc := Lc)
      ht0 hKc hLc x ?_ ?_ ?_
    · exact hsemigroup_meas u v hsnap t x ht0 htT
    · exact fun s y hs0 hst =>
        hchem_sup_ball u v hsnap s hs0 (le_trans hst htT) y
    · exact fun s y hs0 hst =>
        hlog_sup_ball u v hsnap s hs0 (le_trans hst htT) y
  · -- hlift_int
    intro u v hsnap s hs0 hsT
    exact intervalCoupledSource_lift_integrable p (u s) (R (u s))
      (hlift_meas u v hsnap s hs0 hsT)
      (fun y => hchem_sup_ball u v hsnap s hs0 hsT y)
      (fun y => hlog_sup_ball u v hsnap s hs0 hsT y)

/-! ## Toward `hmap`: helper theorems for ball-preservation of Duhamel.

The `hmap` conjunct of `IntervalCoupledClassicalC1BallEstimates` asserts that
the coupled Duhamel operator maps the C¹_x ball into itself, i.e. given
`IntervalDomainClassicalC1Snapshot p T M G_u u v` it returns an analogous
snapshot whose first slice is `Duhamel u`.  This is a **three-part**
obligation, because `IntervalDomainClassicalC1Snapshot` is a conjunction of:

  1. `IsPaper2ClassicalSolution intervalDomain p T (Duhamel u) v`
     — the Duhamel image, paired with the same chemical concentration `v`,
     is itself a paper classical solution.  This is the genuine PDE-theoretic
     content: it requires C²,¹ regularity of the Duhamel image, the parabolic
     equation, homogeneous Neumann BC on the image, positivity of `Duhamel u`,
     and a representation argument tying the helper-operator-based Duhamel
     scaffold to the actual full Neumann heat semigroup.  This is the
     **Schauder / parabolic-regularity** input.

  2. `|intervalDomainLift (Duhamel u τ) x| ≤ M` on `Ioo 0 T × Icc 0 1`.
     This is the sup-norm ball-preservation: discharged below
     (`intervalCoupledDuhamel_lift_abs_le`).

  3. `|deriv (intervalDomainLift (Duhamel u τ)) x| ≤ G_u` on
     `Ioo 0 T × Icc 0 1`.  This is the C¹_x gradient-ball preservation: the
     parabolic-gain Duhamel gradient estimate.  Documented as
     `intervalCoupledDuhamel_grad_estimate_gap` below — the existing
     L¹→L∞ pointwise gradient estimate has a `1/t` time singularity
     (`heatGradientL1LinftyFactor t = (2t√π)⁻¹`), which is **not**
     time-integrable on `[0,t]`.  The needed estimate is an L∞→L∞ heat-kernel
     gradient bound `‖∂ₓ S(t) f‖∞ ≤ Cgrad · t^{-1/2} · ‖f‖∞`, whose
     time-integral against the source is `∫₀ᵗ Cgrad (t-s)^{-1/2} ds =
     2 Cgrad √t`; that bound is **not currently in the file**
     `HeatKernelGradientEstimates.lean` (which only carries L¹→L∞ at `1/t`
     and spectral L²→L∞ at `1/√t`).

The helpers below close (2) outright and isolate (1)+(3) for downstream work. -/

/-- **Sup-norm ball preservation for the coupled Duhamel operator on the
unit interval lift.**

Given:
  * `u₀` bounded by `H` pointwise,
  * the lifted coupled source bounded by `C` pointwise (uniform in `s ∈ [0,T]`),
  * pointwise integrability hypotheses for the Duhamel integrand and the lift,

the lift of `Duhamel(u₀, u)(t)` is bounded by `H + C·T` at every point of `ℝ`,
hence in particular at every `x ∈ [0,1]`.

This is the value-level ball-preservation half of the C¹_x snapshot's first
sup-bound conjunct; it does **not** by itself establish that `Duhamel u` is a
paper classical solution. -/
theorem intervalCoupledDuhamel_lift_abs_le
    {p : CM2Params}
    {R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {H C T : ℝ} (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hu₀ : ∀ y : intervalDomainPoint, |u₀ y| ≤ H)
    (hsource : ∀ s, 0 ≤ s → s ≤ T → ∀ y,
      |intervalDomainLift (intervalCoupledSource p (u s) (R (u s))) y| ≤ C)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hint : ∀ x : intervalDomainPoint,
      MeasureTheory.IntegrableOn
        (fun s => intervalSemigroupOperator 1 (t - s)
          (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x.1)
        (Set.Icc 0 t) MeasureTheory.volume)
    (hlift_int : ∀ s, 0 ≤ s → s ≤ T →
      MeasureTheory.Integrable
        (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
        (intervalMeasure 1)) :
    ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 →
      |intervalDomainLift
          (fun y : intervalDomainPoint =>
            intervalCoupledDuhamelOperator p R u₀ u t y) x| ≤ H + C * T := by
  intro x hx
  -- On `[0,1]`, the lift evaluates to `Duhamel ⟨x, hx⟩`.
  have hpt :
      intervalDomainLift
          (fun y : intervalDomainPoint =>
            intervalCoupledDuhamelOperator p R u₀ u t y) x =
        intervalCoupledDuhamelOperator p R u₀ u t ⟨x, hx⟩ := by
    unfold intervalDomainLift
    simp [hx]
  rw [hpt]
  exact intervalCoupledDuhamelOperator_bound_of_source_bound p R u₀ u
    hH hC hu₀ hsource ht0 htT ⟨x, hx⟩ (hint ⟨x, hx⟩) hlift_int

/-- **Statement of the heat-kernel L∞→L∞ Duhamel gradient gap.**

The C¹_x ball-preservation requires a pointwise gradient estimate on the
Duhamel integral term of the form

```
  |∂ₓ ∫₀ᵗ S(t-s) F(s) ds|_∞  ≤  Cgrad · √T · sup_{s,y} |F(s,y)|
```

This in turn rests on the parabolic-gain heat-kernel L∞→L∞ gradient
inequality

```
  |∂ₓ S(t) f|_∞  ≤  Cgrad · t^{-1/2} · |f|_∞     (★)
```

whose Duhamel time-integral is `∫₀ᵗ Cgrad (t-s)^{-1/2} ds = 2 Cgrad √t`.

**Status of the existing machinery** (in
`ShenWork/PDE/HeatKernelGradientEstimates.lean`):
  * `intervalSemigroupOperator_deriv_L1_Linfty_pointwise` provides an L¹→L∞
    pointwise gradient estimate with factor
    `heatGradientL1LinftyFactor t = (2 t √π)⁻¹`, i.e. a `1/t` time singularity
    (NOT `1/√t`).  This factor is **not** time-integrable on `[0,t]`:
    `∫₀ᵗ (t-s)⁻¹ ds = ∞`, so it cannot directly bound the Duhamel-integral
    gradient.
  * `unitIntervalNeumannHeatSemigroup_grad_Lp_pointwise_bound` is a spectral
    L^p→L∞ pointwise gradient bound but for the SPECTRAL Neumann heat
    semigroup (`unitIntervalNeumannHeatSemigroup`), not for the helper operator
    `intervalSemigroupOperator` that the Duhamel scaffold uses, with factor
    `unitIntervalCosineGradientL1LinftyConstant / t²`.
  * `unitIntervalCosineHeatGradientTsumL2Norm_le_inv_sqrt` provides an L²→L²
    `1/√t` heat-gradient bound but on the spectral side.

**What is missing for the C¹_x hmap.**  An L∞→L∞ heat-gradient inequality (★)
for the **helper operator** `intervalSemigroupOperator`, with the standard
`Cgrad · t^{-1/2}` parabolic-gain rate.  Once (★) is in place, the gradient
ball-preservation follows by Duhamel-style integration plus the
`intervalDomainLift`'s endpoint zero-extension structure.

This declaration is a **statement-only marker**: it records the precise
analytic content needed, with the right rate, signed and ready to plug into
`hmap`.  No proof is provided; the conclusion is `True` by `trivial`. -/
def intervalCoupledDuhamel_grad_estimate_gap : Prop :=
  -- The needed (★) bound, stated in the precise form the C¹_x ball
  -- preservation consumes:
  ∀ {Cgrad : ℝ}, 0 ≤ Cgrad →
    ∀ {t : ℝ}, 0 < t →
      ∀ {f : ℝ → ℝ}, MeasureTheory.Integrable f (intervalMeasure 1) →
        (∀ y : ℝ, |f y| ≤ 1) →
          ∀ x : ℝ,
            |deriv (fun z : ℝ => intervalSemigroupOperator 1 t f z) x| ≤
              Cgrad / Real.sqrt t

theorem intervalCoupledDuhamel_grad_estimate_gap_marker :
    True := trivial

/-- **Fixed-point shortcut for `hmap`.**

If on `Set.Ioo 0 T × Set.Icc 0 1` the Duhamel image coincides with `u`
pointwise (as functions of `(τ, ⟨x, hx⟩)`), then the C¹_x snapshot of
`(Duhamel u, v)` follows from the C¹_x snapshot of `(u, v)` by
extensional rewriting.  This is the route through the Duhamel representation
theorem (`intervalDuhamelRepresentation_of`): for a paper classical solution,
the actual Duhamel formula reconstructs `u` on the interior.

The hypothesis is exactly the equality `Duhamel u τ ⟨x,hx⟩ = u τ ⟨x,hx⟩` for
`(τ, x)` ranging over `Ioo 0 T × Icc 0 1`, plus the closed-domain endpoint
preservation.  Under these, `(Duhamel u, v)` carries the same classical
regularity, the same sup bounds, and the same gradient sup bounds as `(u, v)`.

**Caveat.**  This is a conditional helper.  The pointwise-equality hypothesis
is itself nontrivial: the existing `intervalDuhamelRepresentation_of` uses
`intervalFullSemigroupOperator` (the genuine full Neumann heat semigroup),
whereas `intervalCoupledDuhamelOperator` uses `intervalSemigroupOperator`
(the zeroth-reflection helper operator).  A semigroup-equality bridge between
the two is required to instantiate this hypothesis.  Recording the bridge is
a separate task. -/
theorem intervalCoupledClassicalC1BallEstimates_hmap_of_pointwise_fixed_point
    {p : CM2Params}
    {R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {T M G_u : ℝ}
    (hfix : ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
      (∀ τ x, τ ∈ Set.Ioo (0 : ℝ) T → x ∈ Set.Icc (0 : ℝ) 1 →
          intervalDomainLift
              (fun y : intervalDomainPoint =>
                intervalCoupledDuhamelOperator p R u₀ u τ y) x =
            intervalDomainLift (u τ) x) ∧
        (∀ τ x, τ ∈ Set.Ioo (0 : ℝ) T → x ∈ Set.Icc (0 : ℝ) 1 →
          deriv
              (intervalDomainLift
                (fun y : intervalDomainPoint =>
                  intervalCoupledDuhamelOperator p R u₀ u τ y)) x =
            deriv (intervalDomainLift (u τ)) x) ∧
        IsPaper2ClassicalSolution intervalDomain p T
          (fun τ : ℝ => fun y : intervalDomainPoint =>
            intervalCoupledDuhamelOperator p R u₀ u τ y) v) :
    ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
        IntervalDomainClassicalC1Snapshot p T M G_u
          (fun t : ℝ => fun x : intervalDomainPoint =>
            intervalCoupledDuhamelOperator p R u₀ u t x) v := by
  intro u v hsnap
  obtain ⟨hsupEq, hgradEq, hsol⟩ := hfix u v hsnap
  refine ⟨hsol, ?_, ?_⟩
  · intro τ hτ x hxIcc
    have heq := hsupEq τ x hτ hxIcc
    rw [heq]
    exact hsnap.sup_bound hτ hxIcc
  · intro τ hτ x hxIcc
    have heq := hgradEq τ x hτ hxIcc
    rw [heq]
    exact hsnap.grad_sup_bound hτ hxIcc

/-! ## Wiring the L∞→L∞ gradient estimate into the Duhamel time-integral

With `intervalSemigroupOperator_deriv_Linfty_pointwise_sqrt_t` now proved (in
`ShenWork.HeatKernelGradientEstimates`), the pointwise bound

```
  |∂_z (S(t-s) F(s))(x)|  ≤  Cgrad · (t-s)^{-1/2} · C_source
```

becomes available whenever the lifted source `F(s) = lift (source(u s, R(u s)))`
satisfies the pointwise sup bound `|F(s) y| ≤ C_source`.  Its time integral
against `s ↦ (t-s)^{-1/2}` evaluates to `2 Cgrad · C_source · √t` on `[0,t]`,
hence is uniformly bounded by `2 Cgrad · C_source · √T` on `t ∈ (0,T]`.  This
is the source-integral contribution to the C¹_x ball-preservation argument.

The block below assembles this in three pieces:

1. `intervalCoupledDuhamel_grad_integrand_pointwise_bound` — for any
   `s ∈ [0,t)`, the spatial derivative of the helper-semigroup integrand at
   time-slice `s` is bounded by `Cgrad / √(t-s) · C_source`.  This is direct
   from `intervalSemigroupOperator_deriv_Linfty_pointwise_sqrt_t_unit` after
   normalizing the source sup bound to `1`.

2. `intervalIntegral_inv_sqrt_sub_eq_two_sqrt` — the elementary calculus fact
   `∫₀ᵗ (t-s)^{-1/2} ds = 2√t` for `0 < t`, via `integral_rpow` after the
   change of variable `u = t-s`.

3. `intervalCoupledDuhamel_grad_integral_bound_of_leibniz` — the bridge
   theorem.  Given (a) a differentiation-under-the-integral hypothesis
   linking `deriv (fun x => ∫₀ᵗ S(t-s) F(s) (x) ds) x₀` to
   `∫₀ᵗ deriv (fun z => S(t-s) F(s) z) x₀ ds`, and (b) the pointwise sup bound
   on the lifted source, conclude `|deriv ...| ≤ Cgrad · 2√T · C_source`.

Honest scope. -/

/-- **Pointwise gradient bound on a single time slice of the Duhamel integrand.**

For `0 ≤ s < t` and a pointwise sup bound `|F(s) y| ≤ C_source` on the lifted
source at time `s`, the spatial derivative of the helper semigroup operator
`z ↦ intervalSemigroupOperator 1 (t-s) (F(s)) z` is bounded at every `x` by
`Cgrad · C_source · (t-s)^{-1/2}`, where
`Cgrad = heatGradientLinftyLinftyConstant = 1/√π`.

This is the integrand-level gradient bound; combined with the time-integral
identity `∫₀ᵗ (t-s)^{-1/2} ds = 2√t` and a differentiation-under-the-integral
hypothesis, it discharges the source-integral half of the C¹_x ball-
preservation. -/
theorem intervalCoupledDuhamel_grad_integrand_pointwise_bound
    {t s : ℝ} (hs0 : 0 ≤ s) (hst : s < t)
    {F : ℝ → ℝ}
    (hF_int : MeasureTheory.Integrable F (intervalMeasure 1))
    {C_source : ℝ} (hC_source_nn : 0 ≤ C_source)
    (hF_sup : ∀ y : ℝ, |F y| ≤ C_source) (x : ℝ) :
    |deriv (fun z : ℝ => intervalSemigroupOperator 1 (t - s) F z) x| ≤
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
        / Real.sqrt (t - s) * C_source := by
  have htmS_pos : 0 < t - s := sub_pos.mpr hst
  exact ShenWork.HeatKernelGradientEstimates.intervalSemigroupOperator_deriv_Linfty_pointwise_sqrt_t
    (L := 1) (t := t - s) htmS_pos (f := F) hF_int
    (Cf := C_source) hF_sup x

/-- **Time integral of `(t-s)^{-1/2}` over `[0,t]` is `2√t`.**

A clean Mathlib calculation: change of variables `u = t - s` reduces the
integral to `∫₀ᵗ u^{-1/2} du`, which `integral_rpow` evaluates to
`t^{1/2}/(1/2) = 2√t`.  This is the standard analytic input for the Duhamel
time integral of the parabolic-gain gradient kernel. -/
theorem intervalIntegral_inv_sqrt_sub_eq_two_sqrt
    {t : ℝ} (ht : 0 < t) :
    ∫ s in (0 : ℝ)..t, (t - s) ^ (-(1/2 : ℝ)) = 2 * Real.sqrt t := by
  -- Substitution: `intervalIntegral.integral_comp_sub_left` rewrites
  --   `∫_{0}^{t} (t - s) ^ r ds = ∫_{t - t}^{t - 0} s ^ r ds = ∫_{0}^{t} s ^ r ds`.
  have hcomp : ∫ s in (0 : ℝ)..t, (t - s) ^ (-(1/2 : ℝ)) =
      ∫ s in (t - t)..(t - 0), s ^ (-(1/2 : ℝ)) := by
    rw [intervalIntegral.integral_comp_sub_left (fun s => s ^ (-(1/2 : ℝ))) t]
  have h2 : (t - t : ℝ) = 0 := by ring
  have h3 : (t - 0 : ℝ) = t := by ring
  rw [hcomp, h2, h3]
  -- Evaluate `∫₀ᵗ s^(-1/2) ds = (t^(1/2) - 0^(1/2)) / (1/2) = 2√t`.
  have hrpow := integral_rpow (a := (0 : ℝ)) (b := t) (r := -(1/2 : ℝ))
    (Or.inl (by norm_num))
  rw [hrpow]
  have hexp : (-(1/2 : ℝ) + 1) = (1/2 : ℝ) := by ring
  rw [hexp]
  have hzero : (0 : ℝ) ^ (1/2 : ℝ) = 0 :=
    Real.zero_rpow (by norm_num : (1/2 : ℝ) ≠ 0)
  rw [hzero, sub_zero]
  have ht_half : t ^ (1/2 : ℝ) = Real.sqrt t := (Real.sqrt_eq_rpow t).symm
  rw [ht_half]
  ring

/-- **Bridge: source-integral gradient bound under a Leibniz-interchange
hypothesis.**

Given:
  * `t ∈ (0,T]`,
  * a Leibniz-interchange identity: the spatial derivative of the time
    integral at `x` equals the time integral of the spatial derivatives —
    `deriv (fun x => ∫₀ᵗ S(t-s) F(s) (x) ds) x₀ = ∫₀ᵗ deriv_x S(t-s)(F(s)) x₀ ds`,
  * pointwise sup bound on each lifted source slice: `|F(s) y| ≤ C_source`,
  * pointwise integrability of each slice as required by the unit estimate,
  * integrability over `[0,t]` of the gradient integrand,
  * a closed-form sup bound expression on the dominating integrand
    (delivered cleanly via the time-integral identity
    `intervalIntegral_inv_sqrt_sub_eq_two_sqrt`).

we conclude

```
  |deriv (fun x => ∫₀ᵗ S(t-s) F(s) (x) ds) x₀|  ≤  Cgrad · 2 · √T · C_source.
```

This is the source-integral part of the C¹_x ball-preservation: uniformly
bounded as `t → 0⁺` (the factor `√t ≤ √T`), with `Cgrad = 1/√π`.

The Leibniz identity is a hypothesis here — proving it from the existing
regularity conjuncts requires joint space-time regularity of the integrand
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le` with a uniform integrable
envelope on a neighbourhood of `x₀`), which is an additional analytic input
on the source field, not a Mathlib gap. -/
theorem intervalCoupledDuhamel_grad_integral_bound_of_leibniz
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T)
    {F : ℝ → ℝ → ℝ}
    (hF_int : ∀ s, MeasureTheory.Integrable (F s) (intervalMeasure 1))
    {C_source : ℝ} (hC_source_nn : 0 ≤ C_source)
    (hF_sup : ∀ s, ∀ y : ℝ, |F s y| ≤ C_source)
    (x₀ : ℝ)
    (hLeibniz :
      deriv (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t,
          intervalSemigroupOperator 1 (t - s) (F s) x) x₀ =
      ∫ s in (0 : ℝ)..t,
        deriv (fun z : ℝ =>
          intervalSemigroupOperator 1 (t - s) (F s) z) x₀)
    (hGrad_int :
      IntervalIntegrable
        (fun s : ℝ =>
          deriv (fun z : ℝ =>
            intervalSemigroupOperator 1 (t - s) (F s) z) x₀)
        MeasureTheory.volume (0 : ℝ) t)
    (hDom_int :
      IntervalIntegrable
        (fun s : ℝ =>
          ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            * C_source * (t - s) ^ (-(1/2 : ℝ)))
        MeasureTheory.volume (0 : ℝ) t) :
    |deriv (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t,
          intervalSemigroupOperator 1 (t - s) (F s) x) x₀| ≤
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
        (2 * Real.sqrt T) * C_source := by
  set Cgrad :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant with hCgrad_def
  have hCgrad_nn : 0 ≤ Cgrad :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
  -- Pointwise gradient bound at each interior time slice:
  -- `|deriv (S(t-s) F(s)) x₀| ≤ Cgrad · C_source · (t-s)^(-1/2)`.
  have hpt_bound : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      |deriv (fun z : ℝ =>
        intervalSemigroupOperator 1 (t - s) (F s) z) x₀| ≤
      Cgrad * C_source * (t - s) ^ (-(1/2 : ℝ)) := by
    intro s hs
    have hs0 : 0 ≤ s := hs.1.le
    have hst : s < t := hs.2
    have htms_pos : 0 < t - s := sub_pos.mpr hst
    have h1 := intervalCoupledDuhamel_grad_integrand_pointwise_bound
      (t := t) (s := s) hs0 hst (F := F s) (hF_int s)
      (C_source := C_source) hC_source_nn (hF_sup s) x₀
    -- Convert `Cgrad / √(t-s) · C_source` to `Cgrad · C_source · (t-s)^(-1/2)`.
    have hsqrt_eq : Real.sqrt (t - s) = (t - s) ^ ((1 : ℝ)/2) :=
      Real.sqrt_eq_rpow (t - s)
    have hsqrt_pos : 0 < Real.sqrt (t - s) := Real.sqrt_pos.mpr htms_pos
    have hsqrt_ne : Real.sqrt (t - s) ≠ 0 := ne_of_gt hsqrt_pos
    have hrpow_neg : (t - s) ^ (-(1/2 : ℝ)) = (Real.sqrt (t - s))⁻¹ := by
      rw [Real.rpow_neg htms_pos.le, hsqrt_eq]
    have hrhs_eq :
        Cgrad / Real.sqrt (t - s) * C_source =
          Cgrad * C_source * (t - s) ^ (-(1/2 : ℝ)) := by
      rw [hrpow_neg]
      field_simp
    calc
      |deriv (fun z : ℝ =>
          intervalSemigroupOperator 1 (t - s) (F s) z) x₀|
          ≤ Cgrad / Real.sqrt (t - s) * C_source := h1
      _ = Cgrad * C_source * (t - s) ^ (-(1/2 : ℝ)) := hrhs_eq
  -- Rewrite the derivative using the Leibniz hypothesis.
  rw [hLeibniz]
  -- Bound `|∫ deriv|` by `∫ Cgrad·C·(t-s)^(-1/2)` via abs+integral_mono_on.
  have habs_le :
      |∫ s in (0 : ℝ)..t,
          deriv (fun z : ℝ =>
            intervalSemigroupOperator 1 (t - s) (F s) z) x₀| ≤
        ∫ s in (0 : ℝ)..t,
          |deriv (fun z : ℝ =>
            intervalSemigroupOperator 1 (t - s) (F s) z) x₀| := by
    exact intervalIntegral.abs_integral_le_integral_abs ht.le
  have hmono :
      ∫ s in (0 : ℝ)..t,
        |deriv (fun z : ℝ =>
          intervalSemigroupOperator 1 (t - s) (F s) z) x₀| ≤
      ∫ s in (0 : ℝ)..t, Cgrad * C_source * (t - s) ^ (-(1/2 : ℝ)) := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo ht.le ?_ ?_ ?_
    · exact hGrad_int.abs
    · exact hDom_int
    · intro s hs
      exact hpt_bound s hs
  -- Compute `∫₀ᵗ Cgrad·C·(t-s)^(-1/2) ds = Cgrad·C · 2√t`.
  have hint_eq :
      ∫ s in (0 : ℝ)..t, Cgrad * C_source * (t - s) ^ (-(1/2 : ℝ)) =
        Cgrad * C_source * (2 * Real.sqrt t) := by
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral_inv_sqrt_sub_eq_two_sqrt ht]
  -- Combine and use `√t ≤ √T`.
  have hsqrt_mono : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt htT
  have hC_nn : 0 ≤ Cgrad * C_source := mul_nonneg hCgrad_nn hC_source_nn
  have hsqrt_t_nn : 0 ≤ 2 * Real.sqrt t := by positivity
  have htriple_nn : 0 ≤ Cgrad * C_source := hC_nn
  have hT_bound :
      Cgrad * C_source * (2 * Real.sqrt t) ≤
        Cgrad * C_source * (2 * Real.sqrt T) := by
    have h2 : 2 * Real.sqrt t ≤ 2 * Real.sqrt T :=
      mul_le_mul_of_nonneg_left hsqrt_mono (by norm_num)
    exact mul_le_mul_of_nonneg_left h2 hC_nn
  -- Final algebraic shuffle to `Cgrad * (2√T) * C_source`.
  have hfinal_form :
      Cgrad * C_source * (2 * Real.sqrt T) =
        Cgrad * (2 * Real.sqrt T) * C_source := by ring
  calc
    |∫ s in (0 : ℝ)..t,
        deriv (fun z : ℝ =>
          intervalSemigroupOperator 1 (t - s) (F s) z) x₀|
        ≤ ∫ s in (0 : ℝ)..t,
            |deriv (fun z : ℝ =>
              intervalSemigroupOperator 1 (t - s) (F s) z) x₀| := habs_le
    _ ≤ ∫ s in (0 : ℝ)..t,
            Cgrad * C_source * (t - s) ^ (-(1/2 : ℝ)) := hmono
    _ = Cgrad * C_source * (2 * Real.sqrt t) := hint_eq
    _ ≤ Cgrad * C_source * (2 * Real.sqrt T) := hT_bound
    _ = Cgrad * (2 * Real.sqrt T) * C_source := hfinal_form

/-! ### Discharge of the Leibniz interchange via dominated differentiation

The bridge above (`intervalCoupledDuhamel_grad_integral_bound_of_leibniz`)
takes the differentiation-under-the-integral identity `hLeibniz` as an
opaque hypothesis.  Mathlib provides
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` for
exactly this purpose: given per-slice differentiability of the integrand
in the parameter `x`, joint measurability of the integrand and its
parameter-derivative, and a uniform-in-`x` envelope on the
parameter-derivative that is interval-integrable in `s`, the spatial
derivative of the time integral equals the time integral of the spatial
derivatives.

For the Duhamel integrand `(s, x) ↦ intervalSemigroupOperator 1 (t-s) (F s) x`,
the ingredients are:

* Per-slice differentiability: free from
  `intervalSemigroupOperator_hasDerivAt_deriv` (proved in
  `ShenWork.RegularityBootstrap`), available for every `s < t`.
* Uniform-in-`x` envelope on the parameter-derivative:
  `intervalSemigroupOperator_deriv_Linfty_pointwise_sqrt_t` provides
  `|deriv_z (S(t-s) F(s))(x)| ≤ Cgrad · C_source · (t-s)^(-1/2)`
  with the bound independent of `x`; integrability on `[0,t]` is the
  closed-form `2√t` of `intervalIntegral_inv_sqrt_sub_eq_two_sqrt`.
* Measurability: routine joint-measurability content on the helper-kernel
  integral.  This is named as a hypothesis pair (`hF_meas_s`, `hF'_meas_s`),
  not a `sorry`; it is the standard analytic obligation any caller can
  discharge from the source field's joint regularity.

The Leibniz discharge below is the `_no_leibniz` upgrade of the bridge:
it produces the Leibniz identity from these natural hypotheses, then chains
into the existing source-integral gradient bound. -/

/-- **Discharge of the Leibniz interchange for the Duhamel time integral.**

Given the natural analytic inputs — per-slice spatial differentiability of
the source integrand (free from `intervalSemigroupOperator_hasDerivAt_deriv`),
measurability of the integrand and its `x`-derivative as functions of `s`,
the uniform pointwise envelope from
`intervalCoupledDuhamel_grad_integrand_pointwise_bound`, and the envelope's
interval-integrability — Mathlib's
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` yields
the differentiation-under-the-integral identity

```
deriv (fun x => ∫ s in (0:ℝ)..t, intervalSemigroupOperator 1 (t-s) (F s) x) x₀
  = ∫ s in (0:ℝ)..t, deriv (fun z => intervalSemigroupOperator 1 (t-s) (F s) z) x₀.
```

This is the analytic content that the original `_of_leibniz` bridges
recorded as a hypothesis; here it is proved from atomic ingredients. -/
theorem intervalCoupledDuhamel_grad_leibniz
    {t : ℝ} (ht : 0 < t)
    {F : ℝ → ℝ → ℝ}
    (hF_int : ∀ s, MeasureTheory.Integrable (F s) (intervalMeasure 1))
    {C_source : ℝ} (hC_source_nn : 0 ≤ C_source)
    (hF_sup : ∀ s, ∀ y : ℝ, |F s y| ≤ C_source)
    (x₀ : ℝ)
    (hF_meas :
      ∀ x : ℝ,
        MeasureTheory.AEStronglyMeasurable
          (fun s : ℝ => intervalSemigroupOperator 1 (t - s) (F s) x)
          (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)))
    (hF'_meas :
      MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ =>
          deriv (fun z : ℝ =>
            intervalSemigroupOperator 1 (t - s) (F s) z) x₀)
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)))
    (hDom_int :
      IntervalIntegrable
        (fun s : ℝ =>
          ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            * C_source * (t - s) ^ (-(1/2 : ℝ)))
        MeasureTheory.volume (0 : ℝ) t) :
    deriv (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t,
          intervalSemigroupOperator 1 (t - s) (F s) x) x₀ =
      ∫ s in (0 : ℝ)..t,
        deriv (fun z : ℝ =>
          intervalSemigroupOperator 1 (t - s) (F s) z) x₀ := by
  set Cgrad :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
    with hCgrad_def
  -- Parametric integrand and its `x`-derivative, as functions of `(x, s)`.
  set F_p : ℝ → ℝ → ℝ :=
    fun x s => intervalSemigroupOperator 1 (t - s) (F s) x with hF_p_def
  set F'_p : ℝ → ℝ → ℝ :=
    fun x s => deriv (fun z : ℝ =>
      intervalSemigroupOperator 1 (t - s) (F s) z) x with hF'_p_def
  set bound : ℝ → ℝ :=
    fun s => Cgrad * C_source * (t - s) ^ (-(1/2 : ℝ)) with hbound_def
  -- `Ι 0 t = Ioc 0 t` for `0 < t`.
  have huIoc_eq : Set.uIoc (0 : ℝ) t = Set.Ioc (0 : ℝ) t :=
    Set.uIoc_of_le ht.le
  -- The single point `{t}` has volume zero, so `s < t` holds a.e. on the
  -- restriction to `Ι 0 t = Ioc 0 t`.  We use this to upgrade `s ≤ t` (from
  -- membership in `Ioc 0 t`) to the strict `s < t` needed for `t - s > 0`.
  have hae_ne_t : ∀ᵐ s ∂MeasureTheory.volume, s ≠ t := by
    have heq : {s : ℝ | ¬ s ≠ t} = {t} := by
      ext s; simp [eq_comm]
    rw [MeasureTheory.ae_iff, heq]
    exact Real.volume_singleton
  -- Per-slice spatial differentiability of `x ↦ F_p x s` for `s ∈ Ι 0 t`.
  have hDiff_pt : ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.uIoc (0 : ℝ) t →
      ∀ x ∈ (Set.univ : Set ℝ),
        HasDerivAt (fun x => F_p x s) (F'_p x s) x := by
    filter_upwards [hae_ne_t] with s hsne hs x _
    rw [huIoc_eq] at hs
    have hst : s < t := lt_of_le_of_ne hs.2 hsne
    have htms_pos : 0 < t - s := sub_pos.mpr hst
    exact
      ShenWork.RegularityBootstrap.intervalSemigroupOperator_hasDerivAt_deriv
        (L := 1) (t := t - s) (x := x) htms_pos
        (f := F s) (hF_int s)
  -- Uniform-in-`x` pointwise envelope on the parameter-derivative on `Ι 0 t`.
  have hBound_pt : ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.uIoc (0 : ℝ) t →
      ∀ x ∈ (Set.univ : Set ℝ), ‖F'_p x s‖ ≤ bound s := by
    filter_upwards [hae_ne_t] with s hsne hs x _
    rw [huIoc_eq] at hs
    have hs0 : 0 ≤ s := hs.1.le
    have hst : s < t := lt_of_le_of_ne hs.2 hsne
    have htms_pos : 0 < t - s := sub_pos.mpr hst
    have h := intervalCoupledDuhamel_grad_integrand_pointwise_bound
      (t := t) (s := s) hs0 hst (F := F s) (hF_int s)
      (C_source := C_source) hC_source_nn (hF_sup s) x
    have hsqrt_eq : Real.sqrt (t - s) = (t - s) ^ ((1 : ℝ)/2) :=
      Real.sqrt_eq_rpow (t - s)
    have hrpow_neg : (t - s) ^ (-(1/2 : ℝ)) = (Real.sqrt (t - s))⁻¹ := by
      rw [Real.rpow_neg htms_pos.le, hsqrt_eq]
    have hrhs_eq :
        Cgrad / Real.sqrt (t - s) * C_source =
          Cgrad * C_source * (t - s) ^ (-(1/2 : ℝ)) := by
      rw [hrpow_neg]; field_simp
    have h' :
        |deriv (fun z : ℝ =>
            intervalSemigroupOperator 1 (t - s) (F s) z) x| ≤
          Cgrad * C_source * (t - s) ^ (-(1/2 : ℝ)) := by
      calc
        |deriv (fun z : ℝ =>
            intervalSemigroupOperator 1 (t - s) (F s) z) x|
            ≤ Cgrad / Real.sqrt (t - s) * C_source := h
        _ = Cgrad * C_source * (t - s) ^ (-(1/2 : ℝ)) := hrhs_eq
    simpa [F'_p, bound, Real.norm_eq_abs] using h'
  -- `F_p x₀` is interval-integrable on `[0,t]` via `IntervalIntegrable.mono_fun'`
  -- against the integrable constant `C_source` (volume is locally finite).
  have hF_p_sup_ae :
      (fun s => ‖F_p x₀ s‖) ≤ᵐ[MeasureTheory.volume.restrict (Set.uIoc 0 t)]
        (fun _ => C_source) := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
    filter_upwards [hae_ne_t] with s hsne hs
    rw [huIoc_eq] at hs
    have hst : s < t := lt_of_le_of_ne hs.2 hsne
    have htms_pos : 0 < t - s := sub_pos.mpr hst
    have h := ShenWork.IntervalDomain.intervalSemigroupOperator_Linfty_bound
      (L := 1) (t := t - s) htms_pos (M := C_source) hC_source_nn (hF_sup s) x₀
    simpa [F_p, Real.norm_eq_abs] using h
  have hconst_int : IntervalIntegrable (fun _ : ℝ => C_source)
      MeasureTheory.volume (0 : ℝ) t :=
    intervalIntegrable_const
  have hF_p_int :
      IntervalIntegrable (F_p x₀) MeasureTheory.volume (0 : ℝ) t :=
    IntervalIntegrable.mono_fun' (f := F_p x₀) (g := fun _ => C_source)
      hconst_int (hF_meas x₀) hF_p_sup_ae
  -- Eventually-in-`x` measurability is supplied uniformly by `hF_meas`.
  have hF_meas_evt :
      ∀ᶠ x in 𝓝 x₀,
        MeasureTheory.AEStronglyMeasurable (F_p x)
          (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)) :=
    Filter.Eventually.of_forall (fun x => hF_meas x)
  -- Invoke Mathlib's parametric Leibniz lemma with `s = univ` neighbourhood.
  have hresult :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := t)
      (F := F_p) (F' := F'_p) (x₀ := x₀)
      (s := (Set.univ : Set ℝ))
      (bound := bound)
      (hs := Filter.univ_mem)
      (hF_meas := hF_meas_evt)
      (hF_int := hF_p_int)
      (hF'_meas := hF'_meas)
      (h_bound := hBound_pt)
      (bound_integrable := hDom_int)
      (h_diff := hDiff_pt)
  -- Read off the equality from `HasDerivAt`.
  have hderiv := hresult.2
  exact hderiv.deriv

/-- **`HasDerivAt` for the Duhamel time-integrated source, sibling of
`intervalCoupledDuhamel_grad_leibniz`.**

Same hypotheses as the Leibniz lemma; conclusion is the `HasDerivAt` form
that the underlying Mathlib parametric Leibniz lemma directly produces
(before reading off the derivative equality).  Useful when downstream
code needs to package the integral's spatial differentiability for
`deriv_add` style sum splits. -/
theorem intervalCoupledDuhamel_grad_integral_hasDerivAt
    {t : ℝ} (ht : 0 < t)
    {F : ℝ → ℝ → ℝ}
    (hF_int : ∀ s, MeasureTheory.Integrable (F s) (intervalMeasure 1))
    {C_source : ℝ} (hC_source_nn : 0 ≤ C_source)
    (hF_sup : ∀ s, ∀ y : ℝ, |F s y| ≤ C_source)
    (x₀ : ℝ)
    (hF_meas :
      ∀ x : ℝ,
        MeasureTheory.AEStronglyMeasurable
          (fun s : ℝ => intervalSemigroupOperator 1 (t - s) (F s) x)
          (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)))
    (hF'_meas :
      MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ =>
          deriv (fun z : ℝ =>
            intervalSemigroupOperator 1 (t - s) (F s) z) x₀)
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)))
    (hDom_int :
      IntervalIntegrable
        (fun s : ℝ =>
          ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            * C_source * (t - s) ^ (-(1/2 : ℝ)))
        MeasureTheory.volume (0 : ℝ) t) :
    HasDerivAt
      (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t,
          intervalSemigroupOperator 1 (t - s) (F s) x)
      (∫ s in (0 : ℝ)..t,
        deriv (fun z : ℝ =>
          intervalSemigroupOperator 1 (t - s) (F s) z) x₀)
      x₀ := by
  set Cgrad :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
    with hCgrad_def
  set F_p : ℝ → ℝ → ℝ :=
    fun x s => intervalSemigroupOperator 1 (t - s) (F s) x with hF_p_def
  set F'_p : ℝ → ℝ → ℝ :=
    fun x s => deriv (fun z : ℝ =>
      intervalSemigroupOperator 1 (t - s) (F s) z) x with hF'_p_def
  set bound : ℝ → ℝ :=
    fun s => Cgrad * C_source * (t - s) ^ (-(1/2 : ℝ)) with hbound_def
  have huIoc_eq : Set.uIoc (0 : ℝ) t = Set.Ioc (0 : ℝ) t :=
    Set.uIoc_of_le ht.le
  have hae_ne_t : ∀ᵐ s ∂MeasureTheory.volume, s ≠ t := by
    have heq : {s : ℝ | ¬ s ≠ t} = {t} := by
      ext s; simp [eq_comm]
    rw [MeasureTheory.ae_iff, heq]
    exact Real.volume_singleton
  have hDiff_pt : ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.uIoc (0 : ℝ) t →
      ∀ x ∈ (Set.univ : Set ℝ),
        HasDerivAt (fun x => F_p x s) (F'_p x s) x := by
    filter_upwards [hae_ne_t] with s hsne hs x _
    rw [huIoc_eq] at hs
    have hst : s < t := lt_of_le_of_ne hs.2 hsne
    have htms_pos : 0 < t - s := sub_pos.mpr hst
    exact
      ShenWork.RegularityBootstrap.intervalSemigroupOperator_hasDerivAt_deriv
        (L := 1) (t := t - s) (x := x) htms_pos
        (f := F s) (hF_int s)
  have hBound_pt : ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.uIoc (0 : ℝ) t →
      ∀ x ∈ (Set.univ : Set ℝ), ‖F'_p x s‖ ≤ bound s := by
    filter_upwards [hae_ne_t] with s hsne hs x _
    rw [huIoc_eq] at hs
    have hs0 : 0 ≤ s := hs.1.le
    have hst : s < t := lt_of_le_of_ne hs.2 hsne
    have htms_pos : 0 < t - s := sub_pos.mpr hst
    have h := intervalCoupledDuhamel_grad_integrand_pointwise_bound
      (t := t) (s := s) hs0 hst (F := F s) (hF_int s)
      (C_source := C_source) hC_source_nn (hF_sup s) x
    have hsqrt_eq : Real.sqrt (t - s) = (t - s) ^ ((1 : ℝ)/2) :=
      Real.sqrt_eq_rpow (t - s)
    have hrpow_neg : (t - s) ^ (-(1/2 : ℝ)) = (Real.sqrt (t - s))⁻¹ := by
      rw [Real.rpow_neg htms_pos.le, hsqrt_eq]
    have hrhs_eq :
        Cgrad / Real.sqrt (t - s) * C_source =
          Cgrad * C_source * (t - s) ^ (-(1/2 : ℝ)) := by
      rw [hrpow_neg]; field_simp
    have h' :
        |deriv (fun z : ℝ =>
            intervalSemigroupOperator 1 (t - s) (F s) z) x| ≤
          Cgrad * C_source * (t - s) ^ (-(1/2 : ℝ)) := by
      calc
        |deriv (fun z : ℝ =>
            intervalSemigroupOperator 1 (t - s) (F s) z) x|
            ≤ Cgrad / Real.sqrt (t - s) * C_source := h
        _ = Cgrad * C_source * (t - s) ^ (-(1/2 : ℝ)) := hrhs_eq
    simpa [F'_p, bound, Real.norm_eq_abs] using h'
  have hF_p_sup_ae :
      (fun s => ‖F_p x₀ s‖) ≤ᵐ[MeasureTheory.volume.restrict (Set.uIoc 0 t)]
        (fun _ => C_source) := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
    filter_upwards [hae_ne_t] with s hsne hs
    rw [huIoc_eq] at hs
    have hst : s < t := lt_of_le_of_ne hs.2 hsne
    have htms_pos : 0 < t - s := sub_pos.mpr hst
    have h := ShenWork.IntervalDomain.intervalSemigroupOperator_Linfty_bound
      (L := 1) (t := t - s) htms_pos (M := C_source) hC_source_nn (hF_sup s) x₀
    simpa [F_p, Real.norm_eq_abs] using h
  have hconst_int : IntervalIntegrable (fun _ : ℝ => C_source)
      MeasureTheory.volume (0 : ℝ) t :=
    intervalIntegrable_const
  have hF_p_int :
      IntervalIntegrable (F_p x₀) MeasureTheory.volume (0 : ℝ) t :=
    IntervalIntegrable.mono_fun' (f := F_p x₀) (g := fun _ => C_source)
      hconst_int (hF_meas x₀) hF_p_sup_ae
  have hF_meas_evt :
      ∀ᶠ x in 𝓝 x₀,
        MeasureTheory.AEStronglyMeasurable (F_p x)
          (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)) :=
    Filter.Eventually.of_forall (fun x => hF_meas x)
  have hresult :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := t)
      (F := F_p) (F' := F'_p) (x₀ := x₀)
      (s := (Set.univ : Set ℝ))
      (bound := bound)
      (hs := Filter.univ_mem)
      (hF_meas := hF_meas_evt)
      (hF_int := hF_p_int)
      (hF'_meas := hF'_meas)
      (h_bound := hBound_pt)
      (bound_integrable := hDom_int)
      (h_diff := hDiff_pt)
  exact hresult.2

/-- **Source-integral gradient bound, Leibniz hypothesis discharged.**

The `_no_leibniz` upgrade of `intervalCoupledDuhamel_grad_integral_bound_of_leibniz`:
the `hLeibniz` differentiation-under-the-integral hypothesis is now produced
internally via `intervalCoupledDuhamel_grad_leibniz`, taking only the
natural analytic inputs — joint measurability of the integrand and its
parameter-derivative as functions of `s`, plus the standard per-slice
pointwise integrability of the source.

The conclusion is identical to the `_of_leibniz` variant:

```
|deriv (fun x => ∫₀ᵗ S(t-s) F(s) (x) ds) x₀|  ≤  Cgrad · 2 · √T · C_source.
```

The remaining hypotheses (`hF_meas`, `hF'_meas`) are the routine measurability
obligations any caller can deliver from the source field's joint regularity;
they are not opaque differentiation-interchange identities. -/
theorem intervalCoupledDuhamel_grad_integral_bound_no_leibniz
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T)
    {F : ℝ → ℝ → ℝ}
    (hF_int : ∀ s, MeasureTheory.Integrable (F s) (intervalMeasure 1))
    {C_source : ℝ} (hC_source_nn : 0 ≤ C_source)
    (hF_sup : ∀ s, ∀ y : ℝ, |F s y| ≤ C_source)
    (x₀ : ℝ)
    (hF_meas :
      ∀ x : ℝ,
        MeasureTheory.AEStronglyMeasurable
          (fun s : ℝ => intervalSemigroupOperator 1 (t - s) (F s) x)
          (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)))
    (hF'_meas :
      MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ =>
          deriv (fun z : ℝ =>
            intervalSemigroupOperator 1 (t - s) (F s) z) x₀)
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)))
    (hGrad_int :
      IntervalIntegrable
        (fun s : ℝ =>
          deriv (fun z : ℝ =>
            intervalSemigroupOperator 1 (t - s) (F s) z) x₀)
        MeasureTheory.volume (0 : ℝ) t)
    (hDom_int :
      IntervalIntegrable
        (fun s : ℝ =>
          ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            * C_source * (t - s) ^ (-(1/2 : ℝ)))
        MeasureTheory.volume (0 : ℝ) t) :
    |deriv (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t,
          intervalSemigroupOperator 1 (t - s) (F s) x) x₀| ≤
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
        (2 * Real.sqrt T) * C_source := by
  have hLeibniz :=
    intervalCoupledDuhamel_grad_leibniz
      (t := t) ht (F := F) hF_int (C_source := C_source) hC_source_nn
      hF_sup x₀ hF_meas hF'_meas hDom_int
  exact
    intervalCoupledDuhamel_grad_integral_bound_of_leibniz
      (t := t) (T := T) ht htT (F := F) hF_int (C_source := C_source)
      hC_source_nn hF_sup x₀ hLeibniz hGrad_int hDom_int

/-! ### Joint-continuity discharge of the measurability hypotheses

The two `AEStronglyMeasurable`-in-`s` hypotheses (`hF_meas`, `hF'_meas`) of
`intervalCoupledDuhamel_grad_integral_bound_no_leibniz` are the routine
joint-measurability content that comes for free from any **joint regularity**
of the source field `F : ℝ → ℝ → ℝ`.  Below we discharge both from the
single, precisely-named analytic input

```
hF_joint_meas : Measurable (Function.uncurry F)
```

— i.e. measurability of the source field viewed as a function of
`(s, y) : ℝ × ℝ` — which is exactly what a paper classical-solution snapshot
supplies (any jointly continuous `F` is jointly measurable).

The reasoning is Fubini-Tonelli: the integrand
`(s, y) ↦ K(1, t-s, x, y) · F s y` is jointly measurable in `(s, y)` (the
helper kernel `K` is a Borel function of `(s, y)`, even with its singularity
at `s = t`), and `intervalMeasure 1 = volume.restrict (Icc 0 1)` is
`SFinite`, so the partial integral in `y` is `AEStronglyMeasurable` in `s`
by `MeasureTheory.AEStronglyMeasurable.integral_prod_right'`.  The
derivative case is handled by rewriting through `intervalSemigroupOperator_hasDerivAt`
and applying the same Fubini argument to the kernel-derivative `K'`. -/

/-- The normalized zeroth-reflection helper kernel `(s, y) ↦ K(L, t-s, x, y)`
is jointly `Measurable` as a function of `(s, y) : ℝ × ℝ`. -/
private lemma normalizedZerothReflectionKernel_s_dependent_measurable
    (L t x : ℝ) :
    Measurable
      (fun z : ℝ × ℝ =>
        ShenWork.IntervalDomain.normalizedZerothReflectionKernel L
            (t - z.1) x z.2) := by
  unfold ShenWork.IntervalDomain.normalizedZerothReflectionKernel
    ShenWork.IntervalDomain.neumannHeatKernel_zerothReflection heatKernel
  fun_prop

/-- The derivative of the heat kernel `(s, y) ↦ deriv (fun w => heatKernel (t-s) (w - y)) z`
is jointly `Measurable` as a function of `(s, y) : ℝ × ℝ`, for any fixed `z`. -/
private lemma heatKernel_translated_deriv_s_dependent_measurable
    (t z : ℝ) :
    Measurable
      (fun w : ℝ × ℝ =>
        deriv (fun w' : ℝ => heatKernel (t - w.1) (w' - w.2)) z) := by
  -- For `t - w.1 > 0`, the closed-form derivative is
  --   `K'(t-s)(z, y) = -((z - y) / (2 * (t-s))) * heatKernel (t-s) (z - y)`.
  -- For `t - w.1 ≤ 0`, `heatKernel (t-w.1) _ ≡ 0` (Lean's `Real.sqrt` returns 0
  -- on nonpositive inputs, hence `1 / Real.sqrt 0 = 0`), so the inner function
  -- is constantly zero and its derivative is 0.
  -- Both cases agree with the piecewise closed-form
  --   `if t - w.1 > 0 then -((z-y)/(2(t-s))) * heatKernel(t-s)(z-y) else 0`,
  -- which `fun_prop` proves measurable.
  set M : ℝ × ℝ → ℝ :=
    fun w : ℝ × ℝ =>
      -((z - w.2) / (2 * (t - w.1))) * heatKernel (t - w.1) (z - w.2)
    with hM_def
  have hM_meas : Measurable M := by
    show Measurable
      (fun w : ℝ × ℝ =>
        -((z - w.2) / (2 * (t - w.1))) * heatKernel (t - w.1) (z - w.2))
    unfold heatKernel
    fun_prop
  set f_pw : ℝ × ℝ → ℝ :=
    fun w : ℝ × ℝ => if 0 < t - w.1 then M w else 0
    with hf_pw_def
  have hf_pw_meas : Measurable f_pw := by
    show Measurable (fun w : ℝ × ℝ => if 0 < t - w.1 then M w else 0)
    refine Measurable.ite ?_ hM_meas measurable_const
    have h_open : IsOpen {w : ℝ × ℝ | 0 < t - w.1} := by
      have hset_eq :
          {w : ℝ × ℝ | 0 < t - w.1} = (fun w : ℝ × ℝ => t - w.1) ⁻¹' Set.Ioi 0 :=
        rfl
      rw [hset_eq]
      exact (continuous_const.sub continuous_fst).isOpen_preimage _ isOpen_Ioi
    exact h_open.measurableSet
  -- Pointwise equality: `deriv (...) = f_pw`.
  have h_eq :
      ∀ w : ℝ × ℝ,
        deriv (fun w' : ℝ => heatKernel (t - w.1) (w' - w.2)) z = f_pw w := by
    intro w
    by_cases hpos : 0 < t - w.1
    · simp only [f_pw, hpos, if_true]
      -- `deriv_heatKernel_translated_left` gives the full closed form directly.
      have h := deriv_heatKernel_translated_left (t := t - w.1) hpos z w.2
      simpa [M] using h
    · simp only [f_pw, hpos, if_false]
      -- `t - w.1 ≤ 0` so `Real.sqrt (4π(t-w.1)) = 0`, kernel is 0 everywhere.
      have htle : t - w.1 ≤ 0 := not_lt.mp hpos
      have h4π_nn : (0 : ℝ) ≤ 4 * Real.pi := by positivity
      have hprod_nonpos : 4 * Real.pi * (t - w.1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos h4π_nn htle
      have h_sqrt0 : Real.sqrt (4 * Real.pi * (t - w.1)) = 0 :=
        Real.sqrt_eq_zero'.mpr hprod_nonpos
      have hkernel_zero : ∀ w' : ℝ, heatKernel (t - w.1) (w' - w.2) = 0 := by
        intro w'
        unfold heatKernel
        rw [h_sqrt0]
        ring
      have hconst :
          (fun w' : ℝ => heatKernel (t - w.1) (w' - w.2)) =
            (fun _ : ℝ => (0 : ℝ)) := by
        funext w'
        exact hkernel_zero w'
      rw [hconst]
      exact deriv_const z 0
  -- `Measurable f → f = g pointwise → Measurable g` via congr from below.
  have : Measurable
      (fun w : ℝ × ℝ =>
        deriv (fun w' : ℝ => heatKernel (t - w.1) (w' - w.2)) z) := by
    have h_fn_eq : (fun w : ℝ × ℝ =>
        deriv (fun w' : ℝ => heatKernel (t - w.1) (w' - w.2)) z) = f_pw := by
      funext w
      exact h_eq w
    rw [h_fn_eq]
    exact hf_pw_meas
  exact this

/-- **Lemma 1 (`hF_meas` discharge).** Given joint measurability of the source
field `F` and per-slice integrability against the interval measure, the map
`s ↦ intervalSemigroupOperator 1 (t-s) (F s) x` is `AEStronglyMeasurable` on
`volume.restrict (Set.uIoc 0 t)` for any fixed `x : ℝ`. -/
theorem intervalSemigroupOperator_s_dependent_aestronglyMeasurable_x
    {t : ℝ} (ht : 0 < t) {F : ℝ → ℝ → ℝ}
    (hF_joint_meas : Measurable (Function.uncurry F))
    (x : ℝ) :
    AEStronglyMeasurable
      (fun s : ℝ => intervalSemigroupOperator 1 (t - s) (F s) x)
      (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)) := by
  -- The integrand of `intervalSemigroupOperator` is `K(1, t-s, x, y) * F s y`,
  -- which is jointly measurable.  Apply Fubini's
  -- `AEStronglyMeasurable.integral_prod_right'`.
  set J : ℝ × ℝ → ℝ :=
    fun z : ℝ × ℝ =>
      ShenWork.IntervalDomain.normalizedZerothReflectionKernel 1 (t - z.1) x z.2 *
        F z.1 z.2 with hJ_def
  -- Joint measurability of `J`.
  have hK_meas := normalizedZerothReflectionKernel_s_dependent_measurable 1 t x
  have hF_meas_pair : Measurable (fun z : ℝ × ℝ => F z.1 z.2) := by
    have : (fun z : ℝ × ℝ => F z.1 z.2) = Function.uncurry F := rfl
    rw [this]; exact hF_joint_meas
  have hJ_meas : Measurable J := hK_meas.mul hF_meas_pair
  -- AE-strongly measurable on the product measure.
  have hJ_aestrong :
      AEStronglyMeasurable J
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t) |>.prod
          (ShenWork.IntervalDomain.intervalMeasure 1)) :=
    hJ_meas.aestronglyMeasurable
  -- Apply Fubini: `s ↦ ∫ y, J(s, y) ∂(intervalMeasure 1)` is AE strongly measurable.
  have hfubini :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t))
      (ν := ShenWork.IntervalDomain.intervalMeasure 1)
      (f := J) hJ_aestrong
  -- Unfold `intervalSemigroupOperator` to match.
  simpa [intervalSemigroupOperator, J] using hfubini

/-- **Lemma 2 (`hF'_meas` discharge).** Given joint measurability of the source
field `F` and per-slice integrability against the interval measure, the map
`s ↦ deriv (fun z => intervalSemigroupOperator 1 (t-s) (F s) z) x₀` is
`AEStronglyMeasurable` on `volume.restrict (Set.uIoc 0 t)`.

The proof rewrites the parameter derivative through `intervalSemigroupOperator_hasDerivAt`
into a sum of two explicit parametric integrals against the kernel-derivative
`(s, y) ↦ deriv (fun w => heatKernel (t-s) (w - y)) z`, each jointly measurable
in `(s, y)`. -/
theorem intervalSemigroupOperator_s_dependent_deriv_aestronglyMeasurable_x₀
    {t : ℝ} (ht : 0 < t) {F : ℝ → ℝ → ℝ}
    (hF_joint_meas : Measurable (Function.uncurry F))
    (hF_int : ∀ s, MeasureTheory.Integrable (F s) (intervalMeasure 1))
    (x₀ : ℝ) :
    AEStronglyMeasurable
      (fun s : ℝ =>
        deriv (fun z : ℝ =>
          intervalSemigroupOperator 1 (t - s) (F s) z) x₀)
      (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)) := by
  -- Define the closed-form parametric-integral surrogate `G(s)` that equals the
  -- `deriv` a.e. on `uIoc 0 t` (specifically, on the full-measure subset
  -- `s < t`).
  set Kderiv : ℝ → ℝ → ℝ → ℝ :=
    fun s y z =>
      deriv (fun w : ℝ => heatKernel (t - s) (w - y)) z with hKderiv_def
  -- Joint measurability of `(s, y) ↦ Kderiv s y z` for any `z`.
  have hKderiv_meas : ∀ z : ℝ,
      Measurable (fun w : ℝ × ℝ => Kderiv w.1 w.2 z) := by
    intro z
    exact heatKernel_translated_deriv_s_dependent_measurable t z
  -- Joint integrand: `(s, y) ↦ Kderiv s y z * (indicator (intervalSet 1) (F s)) y`.
  -- For the partial-integral form, we use the unrestricted full-line measure with the
  -- indicator absorbed into `F`-piece via the intervalMeasure restriction.
  -- Explicitly: `D(s, z) := deriv (fun w => heatSemigroup (t-s) (indicator (intervalSet 1) (F s)) w) z
  --              = ∫ y, Kderiv s y z * F s y ∂(intervalMeasure 1)` (a.e.)
  set D₁ : ℝ → ℝ :=
    fun s : ℝ =>
      ∫ y, Kderiv s y x₀ * F s y ∂(ShenWork.IntervalDomain.intervalMeasure 1)
    with hD₁_def
  set D₂ : ℝ → ℝ :=
    fun s : ℝ =>
      ∫ y, Kderiv s y (-x₀) * F s y ∂(ShenWork.IntervalDomain.intervalMeasure 1)
    with hD₂_def
  -- `D₁`, `D₂` are AEStronglyMeasurable on `volume.restrict (uIoc 0 t)` by Fubini.
  have hF_meas_pair : Measurable (fun z : ℝ × ℝ => F z.1 z.2) := by
    have : (fun z : ℝ × ℝ => F z.1 z.2) = Function.uncurry F := rfl
    rw [this]; exact hF_joint_meas
  have hD₁_aestrong : AEStronglyMeasurable D₁
      (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)) := by
    have hint_meas : Measurable
        (fun w : ℝ × ℝ => Kderiv w.1 w.2 x₀ * F w.1 w.2) :=
      (hKderiv_meas x₀).mul hF_meas_pair
    have :=
      MeasureTheory.AEStronglyMeasurable.integral_prod_right'
        (μ := MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t))
        (ν := ShenWork.IntervalDomain.intervalMeasure 1)
        (f := fun w : ℝ × ℝ => Kderiv w.1 w.2 x₀ * F w.1 w.2)
        hint_meas.aestronglyMeasurable
    exact this
  have hD₂_aestrong : AEStronglyMeasurable D₂
      (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)) := by
    have hint_meas : Measurable
        (fun w : ℝ × ℝ => Kderiv w.1 w.2 (-x₀) * F w.1 w.2) :=
      (hKderiv_meas (-x₀)).mul hF_meas_pair
    have :=
      MeasureTheory.AEStronglyMeasurable.integral_prod_right'
        (μ := MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t))
        (ν := ShenWork.IntervalDomain.intervalMeasure 1)
        (f := fun w : ℝ × ℝ => Kderiv w.1 w.2 (-x₀) * F w.1 w.2)
        hint_meas.aestronglyMeasurable
    exact this
  -- The combination `(1/2) * D₁ - (1/2) * D₂` is AEStronglyMeasurable.
  have hG_aestrong : AEStronglyMeasurable
      (fun s : ℝ => (1/2 : ℝ) * D₁ s - (1/2 : ℝ) * D₂ s)
      (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)) := by
    exact (hD₁_aestrong.const_mul (1/2 : ℝ)).sub (hD₂_aestrong.const_mul (1/2 : ℝ))
  -- Now show `deriv (...) x₀ = (1/2) * D₁ s - (1/2) * D₂ s` a.e. on `uIoc 0 t`.
  refine hG_aestrong.congr ?_
  -- The equality holds for all `s` with `t - s > 0`, i.e., `s < t`.
  have huIoc_eq : Set.uIoc (0 : ℝ) t = Set.Ioc (0 : ℝ) t :=
    Set.uIoc_of_le ht.le
  have hae_lt_t : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 t)), s < t := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
    have hae_ne_t : ∀ᵐ s ∂MeasureTheory.volume, s ≠ t := by
      have heq : {s : ℝ | ¬ s ≠ t} = {t} := by
        ext s; simp [eq_comm]
      rw [MeasureTheory.ae_iff, heq]
      exact Real.volume_singleton
    filter_upwards [hae_ne_t] with s hsne hs
    rw [huIoc_eq] at hs
    exact lt_of_le_of_ne hs.2 hsne
  filter_upwards [hae_lt_t] with s hst
  -- For such `s`, use `intervalSemigroupOperator_hasDerivAt` and `deriv_heatSemigroup`.
  have htms_pos : 0 < t - s := sub_pos.mpr hst
  -- Use the closed-form for the operator derivative.
  have hOp_deriv :
      deriv (fun z : ℝ => intervalSemigroupOperator 1 (t - s) (F s) z) x₀ =
        (1 / 2 : ℝ) *
            deriv
              (fun z : ℝ =>
                heatSemigroup (t - s)
                  (Set.indicator (ShenWork.IntervalDomain.intervalSet 1) (F s)) z) x₀ -
          (1 / 2 : ℝ) *
            deriv
              (fun z : ℝ =>
                heatSemigroup (t - s)
                  (Set.indicator (ShenWork.IntervalDomain.intervalSet 1) (F s)) z) (-x₀) :=
    (ShenWork.RegularityBootstrap.intervalSemigroupOperator_hasDerivAt
      (L := 1) (t := t - s) (x := x₀) htms_pos (f := F s) (hF_int s)).deriv
  -- Express each `deriv (heatSemigroup ...) z` as a parametric integral against the
  -- full-line measure, then convert to the interval measure.
  set g_s : ℝ → ℝ :=
    Set.indicator (ShenWork.IntervalDomain.intervalSet 1) (F s) with hg_s_def
  have hg_s_int : MeasureTheory.Integrable g_s MeasureTheory.volume :=
    ShenWork.HeatKernelGradientEstimates.interval_indicator_integrable_of_integrable
      (L := 1) (f := F s) (hF_int s)
  have hh1 :
      deriv (fun z : ℝ => heatSemigroup (t - s) g_s z) x₀ =
        ∫ y, deriv (fun w : ℝ => heatKernel (t - s) (w - y)) x₀ * g_s y :=
    deriv_heatSemigroup htms_pos x₀ hg_s_int
  have hh2 :
      deriv (fun z : ℝ => heatSemigroup (t - s) g_s z) (-x₀) =
        ∫ y, deriv (fun w : ℝ => heatKernel (t - s) (w - y)) (-x₀) * g_s y :=
    deriv_heatSemigroup htms_pos (-x₀) hg_s_int
  -- Convert each full-line integral to an intervalMeasure integral by absorbing
  -- the indicator.  Lemma: `∫ y, k y * indicator(intervalSet 1) f y = ∫ y in intervalSet 1, k y * f y dy
  -- = ∫ y, k y * f y ∂ intervalMeasure 1`.
  have hconv :
      ∀ k : ℝ → ℝ, ∫ y, k y * g_s y =
        ∫ y, k y * F s y ∂(ShenWork.IntervalDomain.intervalMeasure 1) := by
    intro k
    show ∫ y, k y * Set.indicator (ShenWork.IntervalDomain.intervalSet 1) (F s) y =
      ∫ y, k y * F s y ∂(ShenWork.IntervalDomain.intervalMeasure 1)
    have hfun :
        (fun y : ℝ => k y * Set.indicator (ShenWork.IntervalDomain.intervalSet 1) (F s) y) =
          Set.indicator (ShenWork.IntervalDomain.intervalSet 1)
            (fun y => k y * F s y) := by
      funext y
      by_cases hy : y ∈ ShenWork.IntervalDomain.intervalSet 1
      · simp [Set.indicator_of_mem hy]
      · simp [Set.indicator_of_notMem hy]
    rw [hfun]
    rw [MeasureTheory.integral_indicator
      (show MeasurableSet (ShenWork.IntervalDomain.intervalSet 1) by
        simp [ShenWork.IntervalDomain.intervalSet])]
    rfl
  have hh1' :
      deriv (fun z : ℝ => heatSemigroup (t - s) g_s z) x₀ =
        D₁ s := by
    rw [hh1, hconv]
  have hh2' :
      deriv (fun z : ℝ => heatSemigroup (t - s) g_s z) (-x₀) =
        D₂ s := by
    rw [hh2, hconv]
  -- Combine, matching `(1/2)*D₁ - (1/2)*D₂ = deriv (...)`.
  rw [hOp_deriv, hh1', hh2']

/-- **Envelope integrability on `[0,t]`** for the `(t-s)^{-1/2}` gradient
bound.  For `t > 0`, `Cgrad ≥ 0`, `C_source ≥ 0`, the dominating envelope
`s ↦ Cgrad · C_source · (t - s)^{-1/2}` is `IntervalIntegrable` on `[0, t]`.

Route: `intervalIntegral.intervalIntegrable_rpow'` (which needs `-1 < r`,
satisfied by `r = -1/2`) gives `IntervalIntegrable (fun x => x^(-1/2)) volume 0 t`;
`IntervalIntegrable.comp_sub_left` translates to `(t - s)^(-1/2)`; `const_mul`
multiplies by the constant `Cgrad · C_source`.

This discharges the `hDom_int` hypothesis of
`intervalCoupledDuhamel_grad_integral_bound_no_meas` internally.  Closed-form
value `∫₀ᵗ (t - s)^{-1/2} ds = 2√t` is recorded separately in
`intervalIntegral_inv_sqrt_sub_eq_two_sqrt`. -/
theorem intervalCoupledDuhamel_grad_envelope_intervalIntegrable
    {t : ℝ} (ht : 0 < t) (C_source : ℝ) :
    IntervalIntegrable
      (fun s : ℝ =>
        ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
          * C_source * (t - s) ^ (-(1/2 : ℝ)))
      MeasureTheory.volume (0 : ℝ) t := by
  -- Base step: `s ↦ s ^ (-1/2)` is interval integrable on `[0, t]` via the
  -- `intervalIntegrable_rpow'` lemma (`-1 < -1/2`).
  have hbase : IntervalIntegrable (fun x : ℝ => x ^ (-(1/2 : ℝ)))
      MeasureTheory.volume (0 : ℝ) t :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1/2 : ℝ))
  -- Translate by `t`: `(fun x => (t - x) ^ (-1/2))` is IntervalIntegrable on
  -- `[t - 0, t - t] = [t, 0]`, hence on `[0, t]` by symmetry.
  have htrans :
      IntervalIntegrable (fun x : ℝ => (t - x) ^ (-(1/2 : ℝ)))
        MeasureTheory.volume (t - 0) (t - t) :=
    hbase.comp_sub_left t
  have htrans' :
      IntervalIntegrable (fun x : ℝ => (t - x) ^ (-(1/2 : ℝ)))
        MeasureTheory.volume t 0 := by
    have h1 : (t - 0 : ℝ) = t := by ring
    have h2 : (t - t : ℝ) = 0 := by ring
    rw [h1, h2] at htrans
    exact htrans
  have hsub : IntervalIntegrable (fun s : ℝ => (t - s) ^ (-(1/2 : ℝ)))
      MeasureTheory.volume (0 : ℝ) t := htrans'.symm
  -- Multiply by the constant `Cgrad * C_source`.
  exact hsub.const_mul _

/-- **Gradient integrand interval integrability on `[0,t]`** (envelope-dominated).

For `t > 0` and a source field `F : ℝ → ℝ → ℝ` with joint measurability,
per-slice `intervalMeasure`-integrability, and a uniform pointwise sup bound
`|F s y| ≤ C_source`, the parameter-derivative integrand
`s ↦ deriv (fun z => S(t-s)(F s) z) x₀` is `IntervalIntegrable` on `[0, t]`.

Route: dominate by the envelope `Cgrad · C_source · (t - s)^{-1/2}` (proved
integrable in `intervalCoupledDuhamel_grad_envelope_intervalIntegrable`) using
the pointwise bound `intervalCoupledDuhamel_grad_integrand_pointwise_bound`,
then apply `IntervalIntegrable.mono_fun'` with the AE-strong-measurability
of the integrand provided by
`intervalSemigroupOperator_s_dependent_deriv_aestronglyMeasurable_x₀`.

This discharges the `hGrad_int` hypothesis of
`intervalCoupledDuhamel_grad_integral_bound_no_meas` internally. -/
theorem intervalCoupledDuhamel_grad_integrand_intervalIntegrable
    {t : ℝ} (ht : 0 < t)
    {F : ℝ → ℝ → ℝ}
    (hF_joint_meas : Measurable (Function.uncurry F))
    (hF_int : ∀ s, MeasureTheory.Integrable (F s) (intervalMeasure 1))
    {C_source : ℝ} (hC_source_nn : 0 ≤ C_source)
    (hF_sup : ∀ s, ∀ y : ℝ, |F s y| ≤ C_source)
    (x₀ : ℝ) :
    IntervalIntegrable
      (fun s : ℝ =>
        deriv (fun z : ℝ =>
          intervalSemigroupOperator 1 (t - s) (F s) z) x₀)
      MeasureTheory.volume (0 : ℝ) t := by
  set Cgrad :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
    with hCgrad_def
  have hCgrad_nn : 0 ≤ Cgrad :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
  -- AE-strong-measurability of the integrand on `volume.restrict (Ι 0 t)`.
  have hF'_meas :
      MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ =>
          deriv (fun z : ℝ =>
            intervalSemigroupOperator 1 (t - s) (F s) z) x₀)
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)) :=
    intervalSemigroupOperator_s_dependent_deriv_aestronglyMeasurable_x₀
      ht hF_joint_meas hF_int x₀
  -- Envelope `s ↦ Cgrad · C_source · (t - s)^{-1/2}` is IntervalIntegrable.
  have henv :
      IntervalIntegrable
        (fun s : ℝ => Cgrad * C_source * (t - s) ^ (-(1/2 : ℝ)))
        MeasureTheory.volume (0 : ℝ) t :=
    intervalCoupledDuhamel_grad_envelope_intervalIntegrable ht C_source
  -- Pointwise dominance `‖integrand‖ ≤ envelope` on the `Ι 0 t = Ioc 0 t` set.
  have huIoc_eq : Set.uIoc (0 : ℝ) t = Set.Ioc (0 : ℝ) t :=
    Set.uIoc_of_le ht.le
  -- `s ≠ t` a.e. wrt `volume`, so `s < t` a.e. on the `Ι 0 t` restriction.
  have hae_ne_t : ∀ᵐ s ∂MeasureTheory.volume, s ≠ t := by
    have heq : {s : ℝ | ¬ s ≠ t} = {t} := by
      ext s; simp [eq_comm]
    rw [MeasureTheory.ae_iff, heq]
    exact Real.volume_singleton
  have hdom_ae :
      (fun s : ℝ =>
          ‖deriv (fun z : ℝ =>
            intervalSemigroupOperator 1 (t - s) (F s) z) x₀‖) ≤ᵐ[
        MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)]
        (fun s : ℝ => Cgrad * C_source * (t - s) ^ (-(1/2 : ℝ))) := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
    filter_upwards [hae_ne_t] with s hsne hs
    rw [huIoc_eq] at hs
    have hs0 : 0 ≤ s := hs.1.le
    have hst : s < t := lt_of_le_of_ne hs.2 hsne
    have htms_pos : 0 < t - s := sub_pos.mpr hst
    have h := intervalCoupledDuhamel_grad_integrand_pointwise_bound
      (t := t) (s := s) hs0 hst (F := F s) (hF_int s)
      (C_source := C_source) hC_source_nn (hF_sup s) x₀
    -- Convert `Cgrad / √(t-s) * C_source` to `Cgrad * C_source * (t-s)^(-1/2)`.
    have hsqrt_eq : Real.sqrt (t - s) = (t - s) ^ ((1 : ℝ)/2) :=
      Real.sqrt_eq_rpow (t - s)
    have hrpow_neg : (t - s) ^ (-(1/2 : ℝ)) = (Real.sqrt (t - s))⁻¹ := by
      rw [Real.rpow_neg htms_pos.le, hsqrt_eq]
    have hrhs_eq :
        Cgrad / Real.sqrt (t - s) * C_source =
          Cgrad * C_source * (t - s) ^ (-(1/2 : ℝ)) := by
      rw [hrpow_neg]; field_simp
    have h' :
        |deriv (fun z : ℝ =>
            intervalSemigroupOperator 1 (t - s) (F s) z) x₀| ≤
          Cgrad * C_source * (t - s) ^ (-(1/2 : ℝ)) := by
      calc
        |deriv (fun z : ℝ =>
            intervalSemigroupOperator 1 (t - s) (F s) z) x₀|
            ≤ Cgrad / Real.sqrt (t - s) * C_source := h
        _ = Cgrad * C_source * (t - s) ^ (-(1/2 : ℝ)) := hrhs_eq
    simpa [Real.norm_eq_abs] using h'
  -- Apply `IntervalIntegrable.mono_fun'` against the envelope.
  exact IntervalIntegrable.mono_fun' (f := fun s : ℝ =>
      deriv (fun z : ℝ => intervalSemigroupOperator 1 (t - s) (F s) z) x₀)
    (g := fun s : ℝ => Cgrad * C_source * (t - s) ^ (-(1/2 : ℝ)))
    henv hF'_meas hdom_ae

/-- **Source-integral gradient bound, internal measurability discharge.**

The `_no_meas` upgrade of `intervalCoupledDuhamel_grad_integral_bound_no_leibniz`:
both the `hF_meas` (per-`x`) and `hF'_meas` (at `x₀`) `AEStronglyMeasurable`
hypotheses are now produced internally from the single, precisely-named
analytic input `hF_joint_meas : Measurable (Function.uncurry F)` — the source
field's joint measurability in `(s, y) : ℝ × ℝ`.

Any paper classical-solution snapshot supplies `Continuous (Function.uncurry F)`,
which in turn gives `Measurable (Function.uncurry F)` for free.

The conclusion is identical to the `_no_leibniz` variant:

```
|deriv (fun x => ∫₀ᵗ S(t-s) F(s) (x) ds) x₀|  ≤  Cgrad · 2 · √T · C_source.
```
-/
theorem intervalCoupledDuhamel_grad_integral_bound_no_meas
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T)
    {F : ℝ → ℝ → ℝ}
    (hF_joint_meas : Measurable (Function.uncurry F))
    (hF_int : ∀ s, MeasureTheory.Integrable (F s) (intervalMeasure 1))
    {C_source : ℝ} (hC_source_nn : 0 ≤ C_source)
    (hF_sup : ∀ s, ∀ y : ℝ, |F s y| ≤ C_source)
    (x₀ : ℝ)
    (hGrad_int :
      IntervalIntegrable
        (fun s : ℝ =>
          deriv (fun z : ℝ =>
            intervalSemigroupOperator 1 (t - s) (F s) z) x₀)
        MeasureTheory.volume (0 : ℝ) t)
    (hDom_int :
      IntervalIntegrable
        (fun s : ℝ =>
          ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            * C_source * (t - s) ^ (-(1/2 : ℝ)))
        MeasureTheory.volume (0 : ℝ) t) :
    |deriv (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t,
          intervalSemigroupOperator 1 (t - s) (F s) x) x₀| ≤
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
        (2 * Real.sqrt T) * C_source := by
  -- Discharge both measurability hypotheses from the joint-measurability input.
  have hF_meas : ∀ x : ℝ,
      MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ => intervalSemigroupOperator 1 (t - s) (F s) x)
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)) := by
    intro x
    exact intervalSemigroupOperator_s_dependent_aestronglyMeasurable_x ht hF_joint_meas x
  have hF'_meas :
      MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ =>
          deriv (fun z : ℝ =>
            intervalSemigroupOperator 1 (t - s) (F s) z) x₀)
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)) :=
    intervalSemigroupOperator_s_dependent_deriv_aestronglyMeasurable_x₀
      ht hF_joint_meas hF_int x₀
  exact
    intervalCoupledDuhamel_grad_integral_bound_no_leibniz
      (t := t) (T := T) ht htT (F := F) hF_int (C_source := C_source)
      hC_source_nn hF_sup x₀ hF_meas hF'_meas hGrad_int hDom_int

/-- **Source-integral gradient bound, integrability hypotheses discharged.**

The `_no_int` upgrade of `intervalCoupledDuhamel_grad_integral_bound_no_meas`:
both the gradient-integrand `IntervalIntegrable` hypothesis `hGrad_int` and the
envelope `IntervalIntegrable` hypothesis `hDom_int` are now produced internally
from the standard analytic inputs — joint measurability of `F`, per-slice
`intervalMeasure`-integrability of each `F s`, and the uniform pointwise sup
bound on each slice.

The envelope discharge is the closed-form `(t-s)^{-1/2}` integrability proved
in `intervalCoupledDuhamel_grad_envelope_intervalIntegrable`; the gradient
integrand discharge is the envelope-dominated `mono_fun'` argument proved in
`intervalCoupledDuhamel_grad_integrand_intervalIntegrable`.

The remaining hypotheses are exactly the per-slice analytic obligations any
classical-solution snapshot supplies:

* `hF_joint_meas : Measurable (Function.uncurry F)` — free from
  `Continuous (Function.uncurry F)`.
* `hF_int : ∀ s, Integrable (F s) (intervalMeasure 1)` — per-slice integrability
  of the source field against the unit interval measure.
* `hF_sup : ∀ s, ∀ y, |F s y| ≤ C_source` — uniform pointwise sup bound.

The conclusion is identical to the `_no_meas` variant:

```
|deriv (fun x => ∫₀ᵗ S(t-s) F(s) (x) ds) x₀|  ≤  Cgrad · 2 · √T · C_source.
```
-/
theorem intervalCoupledDuhamel_grad_integral_bound_no_int
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T)
    {F : ℝ → ℝ → ℝ}
    (hF_joint_meas : Measurable (Function.uncurry F))
    (hF_int : ∀ s, MeasureTheory.Integrable (F s) (intervalMeasure 1))
    {C_source : ℝ} (hC_source_nn : 0 ≤ C_source)
    (hF_sup : ∀ s, ∀ y : ℝ, |F s y| ≤ C_source)
    (x₀ : ℝ) :
    |deriv (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t,
          intervalSemigroupOperator 1 (t - s) (F s) x) x₀| ≤
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
        (2 * Real.sqrt T) * C_source := by
  -- Discharge `hDom_int` via the closed-form envelope integrability lemma.
  have hDom_int :
      IntervalIntegrable
        (fun s : ℝ =>
          ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            * C_source * (t - s) ^ (-(1/2 : ℝ)))
        MeasureTheory.volume (0 : ℝ) t :=
    intervalCoupledDuhamel_grad_envelope_intervalIntegrable ht C_source
  -- Discharge `hGrad_int` via the envelope-dominated `mono_fun'` argument.
  have hGrad_int :
      IntervalIntegrable
        (fun s : ℝ =>
          deriv (fun z : ℝ =>
            intervalSemigroupOperator 1 (t - s) (F s) z) x₀)
        MeasureTheory.volume (0 : ℝ) t :=
    intervalCoupledDuhamel_grad_integrand_intervalIntegrable
      ht hF_joint_meas hF_int hC_source_nn hF_sup x₀
  exact
    intervalCoupledDuhamel_grad_integral_bound_no_meas
      (t := t) (T := T) ht htT (F := F) hF_joint_meas hF_int
      (C_source := C_source) hC_source_nn hF_sup x₀ hGrad_int hDom_int

/-! ### Initial-data gradient gap (documentation only)

The third conjunct of `IntervalDomainClassicalC1Snapshot` for the Duhamel image
requires a uniform spatial-derivative bound on the **initial-data term**
`x ↦ S(t)·u₀(x)`.  The L∞→L∞ heat-kernel gradient estimate gives only

```
  |deriv (S(t) (lift u₀)) x|  ≤  Cgrad · t^{-1/2} · ‖u₀‖_∞,
```

which **blows up as `t → 0⁺`** unless `u₀` itself carries C¹ regularity.

There are two structurally honest routes to close this gap, neither of which
is a `sorry`-shaped Mathlib hole:

1. **Strengthen the admissibility of `u₀`.** Require `u₀ ∈ C¹` on `[0,1]`
   (or equivalently, a uniform pointwise sup bound on `deriv (lift u₀)`).
   Then `deriv (S(t)(lift u₀)) (x) = S(t) (deriv (lift u₀)) (x)` by the
   semigroup-derivative commutativity (parabolic regularity of the semigroup
   on C¹ data), giving the uniform bound
   `|deriv (S(t)(lift u₀)) x| ≤ ‖deriv (lift u₀)‖_∞`.

2. **Absorb the initial-data term differently.** For a paper classical
   solution `(u, v)` the Duhamel representation theorem
   (`intervalDuhamelRepresentation_of`) gives a pointwise equality
   `S(t)·u₀ = u(t) - ∫₀ᵗ S(t-s)·source(s) ds` on the interior, so the
   gradient of `S(t)·u₀` inherits the gradient of `u(t)` minus the
   already-bounded source-integral gradient.  This route does not require
   strengthening the admissibility but uses the representation theorem to
   trade unstrengthened initial-data regularity for the snapshot's existing
   `grad_sup_bound`.

Both routes are valid; route 1 is the cleaner conceptual fit for the C¹_x
ball framework (the ball is C¹ in `x` to begin with), while route 2 needs
only the existing snapshot data.  The choice is a structural design
decision, not a missing analytic step. -/

/-- **Combined source-integral + initial-data gradient bound under the
Leibniz-interchange hypothesis and an explicit initial-data gradient sup.**

If, in addition to the source-integral hypotheses above, the initial-data
term carries a uniform pointwise gradient sup bound `G_init` —
`|deriv (fun z => intervalSemigroupOperator 1 t (lift u₀) z) x| ≤ G_init` —
and the Duhamel image's spatial derivative splits as the sum of the initial-
data and source-integral gradients (a linearity hypothesis, since both are
present in the Duhamel sum), then the full Duhamel gradient is bounded by
`G_init + Cgrad · 2√T · C_source`.

This is the analog of `intervalCoupledDuhamel_lift_abs_le` for the gradient.
Like its sup-bound sibling, it requires the integrability hypotheses to be
delivered by the snapshot (here in the gradient direction), and like the
fixed-point bridge `..._hmap_of_pointwise_fixed_point`, the Leibniz step is
recorded as a hypothesis rather than reproved.

The gradient-linearity hypothesis is the direct consequence of the
`deriv_add` rule when both summands of the Duhamel operator are
differentiable at `x₀`. -/
theorem intervalCoupledDuhamel_grad_estimate_of_leibniz
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T)
    {u₀ : ℝ → ℝ}
    {F : ℝ → ℝ → ℝ}
    (hF_int : ∀ s, MeasureTheory.Integrable (F s) (intervalMeasure 1))
    {C_source : ℝ} (hC_source_nn : 0 ≤ C_source)
    (hF_sup : ∀ s, ∀ y : ℝ, |F s y| ≤ C_source)
    (x₀ : ℝ)
    {G_init : ℝ} (hG_init_nn : 0 ≤ G_init)
    (hInit_grad :
      |deriv (fun z : ℝ => intervalSemigroupOperator 1 t u₀ z) x₀| ≤ G_init)
    (hSplit :
      deriv (fun x : ℝ =>
        intervalSemigroupOperator 1 t u₀ x +
        ∫ s in (0 : ℝ)..t,
          intervalSemigroupOperator 1 (t - s) (F s) x) x₀ =
      deriv (fun z : ℝ => intervalSemigroupOperator 1 t u₀ z) x₀ +
      deriv (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t,
          intervalSemigroupOperator 1 (t - s) (F s) x) x₀)
    (hLeibniz :
      deriv (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t,
          intervalSemigroupOperator 1 (t - s) (F s) x) x₀ =
      ∫ s in (0 : ℝ)..t,
        deriv (fun z : ℝ =>
          intervalSemigroupOperator 1 (t - s) (F s) z) x₀)
    (hGrad_int :
      IntervalIntegrable
        (fun s : ℝ =>
          deriv (fun z : ℝ =>
            intervalSemigroupOperator 1 (t - s) (F s) z) x₀)
        MeasureTheory.volume (0 : ℝ) t)
    (hDom_int :
      IntervalIntegrable
        (fun s : ℝ =>
          ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            * C_source * (t - s) ^ (-(1/2 : ℝ)))
        MeasureTheory.volume (0 : ℝ) t) :
    |deriv (fun x : ℝ =>
        intervalSemigroupOperator 1 t u₀ x +
        ∫ s in (0 : ℝ)..t,
          intervalSemigroupOperator 1 (t - s) (F s) x) x₀| ≤
      G_init +
        ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
          (2 * Real.sqrt T) * C_source := by
  set Cgrad :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
  rw [hSplit]
  have hint_bound :=
    intervalCoupledDuhamel_grad_integral_bound_of_leibniz
      (t := t) (T := T) ht htT (F := F) hF_int (C_source := C_source)
      hC_source_nn hF_sup x₀ hLeibniz hGrad_int hDom_int
  calc
    |deriv (fun z : ℝ => intervalSemigroupOperator 1 t u₀ z) x₀ +
        deriv (fun x : ℝ =>
          ∫ s in (0 : ℝ)..t,
            intervalSemigroupOperator 1 (t - s) (F s) x) x₀|
        ≤
        |deriv (fun z : ℝ => intervalSemigroupOperator 1 t u₀ z) x₀| +
          |deriv (fun x : ℝ =>
            ∫ s in (0 : ℝ)..t,
              intervalSemigroupOperator 1 (t - s) (F s) x) x₀| := abs_add_le _ _
    _ ≤ G_init + Cgrad * (2 * Real.sqrt T) * C_source :=
        add_le_add hInit_grad hint_bound

/-! ### Initial-data gradient bound from C¹ data + semigroup-derivative commute

For C¹ initial data `u₀` with `|deriv (lift u₀) y| ≤ G_u_init`, IF the
spatial derivative commutes with the helper semigroup operator —
`deriv (z ↦ S(t) u₀ z) x = S(t) (deriv u₀) (x)` (this is the heat-semigroup
analog of `(∂/∂x) e^{t Δ} u₀ = e^{t Δ} (∂/∂x) u₀`, classical PDE content
that follows from kernel-`y`-integration-by-parts plus decay) — THEN the
sup-preservation property of `intervalSemigroupOperator` gives a UNIFORM
gradient bound `|deriv (S(t) u₀) x| ≤ G_u_init`, independent of `t > 0`.

This closes the initial-data piece of the C¹_x ball-preservation under
Route 1 of `intervalCoupledDuhamel_grad_estimate_gap`: strengthening
admissibility of `u₀` to C¹.  The commutation identity is the SINGLE
named analytic input; the rest is mechanical sup-norm preservation
provided by `intervalSemigroupOperator_Linfty_bound`. -/

/-- **Uniform-in-`t` initial-data gradient bound on the helper semigroup,
under the spatial-derivative commutation hypothesis.**

Given:
  * `t > 0`,
  * `u₀ : ℝ → ℝ` with `|deriv u₀ y| ≤ G_u_init` for every `y`,
  * the commutation identity
    `deriv (fun z => intervalSemigroupOperator 1 t u₀ z) x =
     intervalSemigroupOperator 1 t (deriv u₀) x`,

we conclude `|deriv (S(t) u₀) x| ≤ G_u_init`, **uniformly in `t > 0`**.

The commutation identity is the standard "heat semigroup commutes with
spatial derivative" fact (classical PDE content); it is a clean named
hypothesis, NOT a `sorry`, and is the analytic input that Route 1 of the
initial-data gradient gap requires. -/
theorem intervalCoupledDuhamel_grad_initial_bound_of_commute
    {t : ℝ} (ht : 0 < t)
    {u₀ : ℝ → ℝ}
    {G_u_init : ℝ} (hG_init_nn : 0 ≤ G_u_init)
    (hu₀_deriv_sup : ∀ y : ℝ, |deriv u₀ y| ≤ G_u_init)
    (x : ℝ)
    (hCommute :
      deriv (fun z : ℝ => intervalSemigroupOperator 1 t u₀ z) x =
      intervalSemigroupOperator 1 t (deriv u₀) x) :
    |deriv (fun z : ℝ => intervalSemigroupOperator 1 t u₀ z) x| ≤ G_u_init := by
  rw [hCommute]
  exact
    ShenWork.IntervalDomain.intervalSemigroupOperator_Linfty_bound
      (L := 1) (t := t) ht (M := G_u_init) hG_init_nn hu₀_deriv_sup x

/-! ### Full Duhamel-image gradient bound under both bridges

Combining the initial-data bound (Route 1: C¹ `u₀` + commutation) with the
source-integral bound (Leibniz interchange) yields the full Duhamel-image
gradient bound `G_u_init + Cgrad · 2√T · C_source`, uniformly in
`t ∈ (0, T]`.

This is the gradient counterpart of `intervalCoupledDuhamel_lift_abs_le`,
discharging the third conjunct of `IntervalDomainClassicalC1Snapshot` for
the Duhamel image — modulo the two named analytic inputs.  The `_of_leibniz`
variant above kept `G_init` as an opaque hypothesis; here `G_init = G_u_init`
is grounded in the C¹ initial-data sup bound. -/

/-- **Full Duhamel-image gradient bound (initial + source) under named
bridges.**

Discharges the gradient sup conjunct of the C¹_x snapshot for the Duhamel
image, parameterized by:
  * The Leibniz interchange hypothesis on the source integral;
  * The semigroup-derivative commutation hypothesis on the initial datum;
  * Joint analytic data: C¹ `u₀`, pointwise source sup `C_source`,
    integrability and gradient-integrability of the source-integral
    integrand.

The resulting bound `G_u_init + Cgrad · 2√T · C_source` is UNIFORM in
`t ∈ (0, T]` — both the initial-data piece (by sup-preservation) and the
source-integral piece (since `√t ≤ √T`) are independent of `t`. -/
theorem intervalCoupledDuhamel_grad_estimate_full_of_bridges
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T)
    {u₀ : ℝ → ℝ}
    {G_u_init : ℝ} (hG_init_nn : 0 ≤ G_u_init)
    (hu₀_deriv_sup : ∀ y : ℝ, |deriv u₀ y| ≤ G_u_init)
    {F : ℝ → ℝ → ℝ}
    (hF_int : ∀ s, MeasureTheory.Integrable (F s) (intervalMeasure 1))
    {C_source : ℝ} (hC_source_nn : 0 ≤ C_source)
    (hF_sup : ∀ s, ∀ y : ℝ, |F s y| ≤ C_source)
    (x₀ : ℝ)
    (hCommute :
      deriv (fun z : ℝ => intervalSemigroupOperator 1 t u₀ z) x₀ =
      intervalSemigroupOperator 1 t (deriv u₀) x₀)
    (hSplit :
      deriv (fun x : ℝ =>
        intervalSemigroupOperator 1 t u₀ x +
        ∫ s in (0 : ℝ)..t,
          intervalSemigroupOperator 1 (t - s) (F s) x) x₀ =
      deriv (fun z : ℝ => intervalSemigroupOperator 1 t u₀ z) x₀ +
      deriv (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t,
          intervalSemigroupOperator 1 (t - s) (F s) x) x₀)
    (hLeibniz :
      deriv (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t,
          intervalSemigroupOperator 1 (t - s) (F s) x) x₀ =
      ∫ s in (0 : ℝ)..t,
        deriv (fun z : ℝ =>
          intervalSemigroupOperator 1 (t - s) (F s) z) x₀)
    (hGrad_int :
      IntervalIntegrable
        (fun s : ℝ =>
          deriv (fun z : ℝ =>
            intervalSemigroupOperator 1 (t - s) (F s) z) x₀)
        MeasureTheory.volume (0 : ℝ) t)
    (hDom_int :
      IntervalIntegrable
        (fun s : ℝ =>
          ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            * C_source * (t - s) ^ (-(1/2 : ℝ)))
        MeasureTheory.volume (0 : ℝ) t) :
    |deriv (fun x : ℝ =>
        intervalSemigroupOperator 1 t u₀ x +
        ∫ s in (0 : ℝ)..t,
          intervalSemigroupOperator 1 (t - s) (F s) x) x₀| ≤
      G_u_init +
        ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
          (2 * Real.sqrt T) * C_source := by
  -- The C¹ initial-data path supplies a uniform `G_init` for `_of_leibniz`.
  have hInit_grad :
      |deriv (fun z : ℝ => intervalSemigroupOperator 1 t u₀ z) x₀| ≤ G_u_init :=
    intervalCoupledDuhamel_grad_initial_bound_of_commute
      (t := t) ht (u₀ := u₀) (G_u_init := G_u_init) hG_init_nn
      hu₀_deriv_sup x₀ hCommute
  exact
    intervalCoupledDuhamel_grad_estimate_of_leibniz
      (t := t) (T := T) ht htT (u₀ := u₀) (F := F) hF_int
      (C_source := C_source) hC_source_nn hF_sup x₀
      (G_init := G_u_init) hG_init_nn hInit_grad hSplit hLeibniz hGrad_int
      hDom_int

/-! ### Partial hmap discharge under the analytic bridges.

We package the conjunction of the three analytic bridges — Schauder
content (`IsPaper2ClassicalSolution`), Leibniz interchange, and
semigroup-derivative commutation — into a single hypothesis bundle, and
discharge the full `hmap` conjunct of `IntervalCoupledClassicalC1BallEstimates`
from it.

This is a STRUCTURAL refinement of
`intervalCoupledClassicalC1BallEstimates_hmap_of_pointwise_fixed_point`:
where the latter takes a pointwise Duhamel-fixed-point equality (an unusual
shape requiring the helper-vs-full-semigroup bridge), the present discharge
takes the named analytic inputs in their natural shape — the gradient
bound is derived genuinely from the L∞→L∞ heat-kernel gradient estimate
proved in this file, not assumed pointwise.

The discharge unfolds the third conjunct of `IntervalDomainClassicalC1Snapshot`
for the Duhamel image into the bound proved by
`intervalCoupledDuhamel_grad_estimate_full_of_bridges`, threading the
matching `G_u`, and uses `intervalCoupledDuhamel_lift_abs_le` for the
sup-bound conjunct.

For the discharge to instantiate `G_u`, the Duhamel-ball parameter must
match the predicted upper bound `G_u_init + Cgrad · 2√T · C_source`.
This is recorded as an explicit constraint hypothesis `hG_u_eq`. -/

/-- **Partial `hmap` discharge for the C¹_x ball under the analytic bridges.**

Discharges the `hmap` conjunct of `IntervalCoupledClassicalC1BallEstimates`,
parameterized by:
  * `hSol`: the Schauder content (Duhamel image is a paper classical solution);
  * `hH`: pointwise sup bound on `u₀` (delivers the `M` field via
    `intervalCoupledDuhamel_lift_abs_le`);
  * `hC_source`: pointwise sup bound on lifted source (delivers `C` for
    both the sup-bound and the gradient-bound source-integral pieces);
  * `hu₀_deriv_sup`: C¹ initial-data gradient sup `≤ G_u_init`;
  * `hLeibniz`, `hCommute`, `hSplit`: the differentiation-interchange
    identities, packaged here as named hypotheses (genuine PDE Mathlib
    content, deferred);
  * `hint`, `hlift_int`, `hGrad_int`, `hDom_int`: routine integrability
    obligations on the Duhamel integrand and the dominating envelope;
  * `hsupEq`, `hgradEq`: the bridge between `intervalCoupledDuhamelOperator`'s
    Set.Icc-set-integral and the `intervalIntegral 0..t` form used by the
    estimates above (a clean definitional bridge, deferred);
  * `hG_u_eq` and `hM_eq`: the ball parameters `G_u`, `M` must match the
    predicted upper bounds.

Returns the full `IntervalDomainClassicalC1Snapshot` snapshot for the
Duhamel image, including all three conjuncts. -/
theorem intervalCoupledClassicalC1BallEstimates_hmap_of_bridges
    {p : CM2Params}
    {R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {T M G_u G_u_init C_source H : ℝ}
    (hT : 0 < T) (hH_nn : 0 ≤ H) (hC_nn : 0 ≤ C_source)
    (hG_init_nn : 0 ≤ G_u_init)
    (hM_eq : M = H + C_source * T)
    (hG_u_eq : G_u = G_u_init +
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
        (2 * Real.sqrt T) * C_source)
    (hu₀_sup : ∀ y : intervalDomainPoint, |u₀ y| ≤ H)
    (hu₀_deriv_sup :
      ∀ y : ℝ, |deriv (intervalDomainLift u₀) y| ≤ G_u_init)
    (hSol : ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
        IsPaper2ClassicalSolution intervalDomain p T
          (fun τ : ℝ => fun y : intervalDomainPoint =>
            intervalCoupledDuhamelOperator p R u₀ u τ y) v)
    (hSource_sup_local :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s, 0 ≤ s → s ≤ T → ∀ y : ℝ,
            |intervalDomainLift
              (intervalCoupledSource p (u s) (R (u s))) y| ≤ C_source)
    (hSource_sup_global :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s : ℝ, ∀ y : ℝ,
            |intervalDomainLift
              (intervalCoupledSource p (u s) (R (u s))) y| ≤ C_source)
    (hint :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ (t : ℝ) (x : intervalDomainPoint), 0 ≤ t → t ≤ T →
            MeasureTheory.IntegrableOn
              (fun s => intervalSemigroupOperator 1 (t - s)
                (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x.1)
              (Set.Icc 0 t) MeasureTheory.volume)
    (hlift_int :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s, 0 ≤ s → s ≤ T →
            MeasureTheory.Integrable
              (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
              (intervalMeasure 1))
    (hSource_int_global :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s : ℝ,
            MeasureTheory.Integrable
              (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
              (intervalMeasure 1))
    (hSupEq :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ (τ : ℝ) (x : ℝ), τ ∈ Set.Ioo (0 : ℝ) T → x ∈ Set.Icc (0 : ℝ) 1 →
            intervalDomainLift
              (fun y : intervalDomainPoint =>
                intervalCoupledDuhamelOperator p R u₀ u τ y) x =
            intervalSemigroupOperator 1 τ (intervalDomainLift u₀) x +
              ∫ s in (0 : ℝ)..τ,
                intervalSemigroupOperator 1 (τ - s)
                  (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x)
    (hGradEq :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ (τ : ℝ) (x : ℝ), τ ∈ Set.Ioo (0 : ℝ) T → x ∈ Set.Icc (0 : ℝ) 1 →
            deriv
              (intervalDomainLift
                (fun y : intervalDomainPoint =>
                  intervalCoupledDuhamelOperator p R u₀ u τ y)) x =
            deriv (fun z : ℝ =>
              intervalSemigroupOperator 1 τ (intervalDomainLift u₀) z +
              ∫ s in (0 : ℝ)..τ,
                intervalSemigroupOperator 1 (τ - s)
                  (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
                  z) x)
    (hCommute :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ (τ : ℝ) (x : ℝ), τ ∈ Set.Ioo (0 : ℝ) T → x ∈ Set.Icc (0 : ℝ) 1 →
            deriv
              (fun z : ℝ =>
                intervalSemigroupOperator 1 τ (intervalDomainLift u₀) z) x =
            intervalSemigroupOperator 1 τ
              (deriv (intervalDomainLift u₀)) x)
    (hSplit :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ (τ : ℝ) (x : ℝ), τ ∈ Set.Ioo (0 : ℝ) T → x ∈ Set.Icc (0 : ℝ) 1 →
            deriv (fun z : ℝ =>
              intervalSemigroupOperator 1 τ (intervalDomainLift u₀) z +
              ∫ s in (0 : ℝ)..τ,
                intervalSemigroupOperator 1 (τ - s)
                  (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
                  z) x =
            deriv (fun z : ℝ =>
              intervalSemigroupOperator 1 τ (intervalDomainLift u₀) z) x +
            deriv (fun z : ℝ =>
              ∫ s in (0 : ℝ)..τ,
                intervalSemigroupOperator 1 (τ - s)
                  (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
                  z) x)
    (hLeibniz :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ (τ : ℝ) (x : ℝ), τ ∈ Set.Ioo (0 : ℝ) T → x ∈ Set.Icc (0 : ℝ) 1 →
            deriv (fun z : ℝ =>
              ∫ s in (0 : ℝ)..τ,
                intervalSemigroupOperator 1 (τ - s)
                  (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
                  z) x =
            ∫ s in (0 : ℝ)..τ,
              deriv (fun z : ℝ =>
                intervalSemigroupOperator 1 (τ - s)
                  (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
                  z) x)
    (hGrad_int :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ (τ : ℝ) (x : ℝ), τ ∈ Set.Ioo (0 : ℝ) T → x ∈ Set.Icc (0 : ℝ) 1 →
            IntervalIntegrable
              (fun s : ℝ =>
                deriv (fun z : ℝ =>
                  intervalSemigroupOperator 1 (τ - s)
                    (intervalDomainLift
                      (intervalCoupledSource p (u s) (R (u s)))) z) x)
              MeasureTheory.volume (0 : ℝ) τ)
    (hDom_int :
      ∀ (τ : ℝ), τ ∈ Set.Ioo (0 : ℝ) T →
        IntervalIntegrable
          (fun s : ℝ =>
            ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
              * C_source * (τ - s) ^ (-(1/2 : ℝ)))
          MeasureTheory.volume (0 : ℝ) τ) :
    ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
        IntervalDomainClassicalC1Snapshot p T M G_u
          (fun t : ℝ => fun x : intervalDomainPoint =>
            intervalCoupledDuhamelOperator p R u₀ u t x) v := by
  intro u v hsnap
  refine ⟨hSol u v hsnap, ?_, ?_⟩
  · -- Sup-bound conjunct: discharged by `intervalCoupledDuhamel_lift_abs_le`.
    intro τ hτ x hxIcc
    have hτ_le : τ ≤ T := le_of_lt hτ.2
    have hτ_nn : 0 ≤ τ := le_of_lt hτ.1
    -- Repackage local sup from `∀ y : ℝ` to the `lift y` form expected.
    have hsource' :
        ∀ s, 0 ≤ s → s ≤ T → ∀ y : ℝ,
          |intervalDomainLift
            (intervalCoupledSource p (u s) (R (u s))) y| ≤ C_source :=
      fun s hs0 hsT y => hSource_sup_local u v hsnap s hs0 hsT y
    have hint_pt :
        ∀ x' : intervalDomainPoint,
          MeasureTheory.IntegrableOn
            (fun s => intervalSemigroupOperator 1 (τ - s)
              (intervalDomainLift
                (intervalCoupledSource p (u s) (R (u s)))) x'.1)
            (Set.Icc 0 τ) MeasureTheory.volume :=
      fun x' => hint u v hsnap τ x' hτ_nn hτ_le
    have hlift_pt :
        ∀ s, 0 ≤ s → s ≤ T →
          MeasureTheory.Integrable
            (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
            (intervalMeasure 1) :=
      fun s hs0 hsT => hlift_int u v hsnap s hs0 hsT
    have hsup_le :=
      intervalCoupledDuhamel_lift_abs_le
        (p := p) (R := R) (u₀ := u₀) (u := u) (H := H) (C := C_source) (T := T)
        hH_nn hC_nn hu₀_sup hsource' (t := τ) hτ_nn hτ_le hint_pt hlift_pt
        x hxIcc
    -- Rewrite to the predicted M = H + C * T form.
    have hM_form : H + C_source * T = M := hM_eq.symm
    rw [hM_form] at hsup_le
    exact hsup_le
  · -- Gradient-bound conjunct: discharged by
    -- `intervalCoupledDuhamel_grad_estimate_full_of_bridges`.
    intro τ hτ x hxIcc
    have hτ_le : τ ≤ T := le_of_lt hτ.2
    have hτ_pos : 0 < τ := hτ.1
    -- Rewrite the gradient through the Set.Icc-vs-intervalIntegral bridge.
    rw [hGradEq u v hsnap τ x hτ hxIcc]
    -- Apply the full-of-bridges estimate.
    have hF_int_τ :
        ∀ s, MeasureTheory.Integrable
          (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
          (intervalMeasure 1) :=
      fun s => hSource_int_global u v hsnap s
    have hF_sup_τ :
        ∀ s : ℝ, ∀ y : ℝ,
          |intervalDomainLift (intervalCoupledSource p (u s) (R (u s))) y| ≤
            C_source :=
      fun s y => hSource_sup_global u v hsnap s y
    have hbound :=
      intervalCoupledDuhamel_grad_estimate_full_of_bridges
        (t := τ) (T := T) hτ_pos hτ_le
        (u₀ := intervalDomainLift u₀) (G_u_init := G_u_init) hG_init_nn
        hu₀_deriv_sup
        (F := fun s : ℝ => intervalDomainLift
          (intervalCoupledSource p (u s) (R (u s))))
        hF_int_τ (C_source := C_source) hC_nn hF_sup_τ x
        (hCommute u v hsnap τ x hτ hxIcc)
        (hSplit u v hsnap τ x hτ hxIcc)
        (hLeibniz u v hsnap τ x hτ hxIcc)
        (hGrad_int u v hsnap τ x hτ hxIcc)
        (hDom_int τ hτ)
    -- Rewrite the predicted bound to match `G_u`.
    rw [hG_u_eq]
    exact hbound

/-! ### Dirichlet C¹ discharge of the commutation hypothesis

For Dirichlet C¹ initial data the literal heat-semigroup-derivative
commutation identity is structurally invalid for the helper Neumann-style
operator (cf. the `hCommute` discussion in
`HeatKernelGradientEstimates.lean`).  However, the IBP identity

  `∂_x (S_1(t) u₀)(x) = (1/2) · ∫₀¹ K_D(t,x,y) · u₀'(y) dy`

combined with the uniform `L¹` bound `∫₀¹ |K_D(t,x,y)| dy ≤ 2` provides
the same conclusion `|∂_x (S_1(t) u₀)(x)| ≤ ‖u₀'‖_∞` (uniform in `t > 0`)
without invoking the literal commutation identity.

The lemmas below replace the `hCommute` hypothesis of the previous wave
of discharges with explicit Dirichlet C¹ hypotheses on `u₀`. -/

/-- **Initial-data gradient bound, Dirichlet C¹ variant** (replaces
`intervalCoupledDuhamel_grad_initial_bound_of_commute`).

For C¹ initial data `u₀` with sup-bounded derivative `|u₀' y| ≤ G_u_init`
and Dirichlet endpoint trace `u₀ 1 = 0`, we have

  `|∂_x (S_1(t) u₀)(x)| ≤ G_u_init`,

uniformly in `t > 0`.

Internally, this is a direct wrapper around
`ShenWork.HeatKernelGradientEstimates.intervalSemigroupOperator_deriv_Linfty_dirichlet`. -/
theorem intervalCoupledDuhamel_grad_initial_bound_dirichlet
    {t : ℝ} (ht : 0 < t)
    {u₀ u₀' : ℝ → ℝ}
    (hu₀_int : MeasureTheory.Integrable u₀
      (ShenWork.IntervalDomain.intervalMeasure 1))
    (hu₀ : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt u₀ (u₀' y) y)
    (hu₀'_int : IntervalIntegrable u₀' MeasureTheory.volume 0 1)
    (hu₀_one : u₀ 1 = 0)
    {G_u_init : ℝ} (hG_init_nn : 0 ≤ G_u_init)
    (hu₀_deriv_sup : ∀ y : ℝ, |u₀' y| ≤ G_u_init)
    (x : ℝ) :
    |deriv (fun z : ℝ => intervalSemigroupOperator 1 t u₀ z) x| ≤ G_u_init :=
  ShenWork.HeatKernelGradientEstimates.intervalSemigroupOperator_deriv_Linfty_dirichlet
    (t := t) ht (u₀ := u₀) (u₀' := u₀')
    hu₀_int hu₀ hu₀'_int hu₀_one hG_init_nn hu₀_deriv_sup x

/-- **Full Duhamel-image gradient bound, Dirichlet C¹ initial-data variant.**

Same shape and conclusion as
`intervalCoupledDuhamel_grad_estimate_full_of_bridges`, but the
heat-semigroup-derivative commutation hypothesis `hCommute` is replaced
by Dirichlet C¹ hypotheses on `u₀` together with a sup bound on `u₀'`;
the Leibniz interchange + Schauder split bridges are still required.

The resulting bound is
`G_u_init + Cgrad · 2√T · C_source`, uniformly in `t ∈ (0, T]`. -/
theorem intervalCoupledDuhamel_grad_estimate_full_dirichlet
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T)
    {u₀ u₀' : ℝ → ℝ}
    (hu₀_int : MeasureTheory.Integrable u₀
      (ShenWork.IntervalDomain.intervalMeasure 1))
    (hu₀ : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt u₀ (u₀' y) y)
    (hu₀'_int : IntervalIntegrable u₀' MeasureTheory.volume 0 1)
    (hu₀_one : u₀ 1 = 0)
    {G_u_init : ℝ} (hG_init_nn : 0 ≤ G_u_init)
    (hu₀_deriv_sup : ∀ y : ℝ, |u₀' y| ≤ G_u_init)
    {F : ℝ → ℝ → ℝ}
    (hF_int : ∀ s, MeasureTheory.Integrable (F s)
      (ShenWork.IntervalDomain.intervalMeasure 1))
    {C_source : ℝ} (hC_source_nn : 0 ≤ C_source)
    (hF_sup : ∀ s, ∀ y : ℝ, |F s y| ≤ C_source)
    (x₀ : ℝ)
    (hSplit :
      deriv (fun x : ℝ =>
        intervalSemigroupOperator 1 t u₀ x +
        ∫ s in (0 : ℝ)..t,
          intervalSemigroupOperator 1 (t - s) (F s) x) x₀ =
      deriv (fun z : ℝ => intervalSemigroupOperator 1 t u₀ z) x₀ +
      deriv (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t,
          intervalSemigroupOperator 1 (t - s) (F s) x) x₀)
    (hLeibniz :
      deriv (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t,
          intervalSemigroupOperator 1 (t - s) (F s) x) x₀ =
      ∫ s in (0 : ℝ)..t,
        deriv (fun z : ℝ =>
          intervalSemigroupOperator 1 (t - s) (F s) z) x₀)
    (hGrad_int :
      IntervalIntegrable
        (fun s : ℝ =>
          deriv (fun z : ℝ =>
            intervalSemigroupOperator 1 (t - s) (F s) z) x₀)
        MeasureTheory.volume (0 : ℝ) t)
    (hDom_int :
      IntervalIntegrable
        (fun s : ℝ =>
          ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            * C_source * (t - s) ^ (-(1/2 : ℝ)))
        MeasureTheory.volume (0 : ℝ) t) :
    |deriv (fun x : ℝ =>
        intervalSemigroupOperator 1 t u₀ x +
        ∫ s in (0 : ℝ)..t,
          intervalSemigroupOperator 1 (t - s) (F s) x) x₀| ≤
      G_u_init +
        ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
          (2 * Real.sqrt T) * C_source := by
  -- Discharge the initial-data gradient bound via the Dirichlet IBP path.
  have hInit_grad :
      |deriv (fun z : ℝ => intervalSemigroupOperator 1 t u₀ z) x₀| ≤ G_u_init :=
    intervalCoupledDuhamel_grad_initial_bound_dirichlet
      (t := t) ht (u₀ := u₀) (u₀' := u₀')
      hu₀_int hu₀ hu₀'_int hu₀_one hG_init_nn hu₀_deriv_sup x₀
  exact
    intervalCoupledDuhamel_grad_estimate_of_leibniz
      (t := t) (T := T) ht htT (u₀ := u₀) (F := F) hF_int
      (C_source := C_source) hC_source_nn hF_sup x₀
      (G_init := G_u_init) hG_init_nn hInit_grad hSplit hLeibniz hGrad_int
      hDom_int

/-- **Partial `hmap` discharge for the C¹_x ball, Dirichlet C¹ initial-data
variant.**

Companion to `intervalCoupledClassicalC1BallEstimates_hmap_of_bridges`,
where the per-(u, v, τ, x) commutation hypothesis `hCommute` is replaced
by a single Dirichlet C¹ representative `u₀_ext` of the lifted initial
datum, together with sup bounds on its derivative.

Specifically, the caller supplies:
* `u₀_ext : ℝ → ℝ`, `u₀'_ext : ℝ → ℝ`
* `hext_eq : ∀ y ∈ Set.Icc 0 1, intervalDomainLift u₀ y = u₀_ext y`
* C¹ regularity of `u₀_ext` on a neighborhood of `[0,1]`
* `hu₀_ext_one : u₀_ext 1 = 0`
* `hu₀_ext'_sup : ∀ y, |u₀'_ext y| ≤ G_u_init`

The bridge `hext_eq` lets us replace `intervalDomainLift u₀` by `u₀_ext`
inside `intervalSemigroupOperator 1 τ (·) x` (which only sees its
argument on `[0,1]`), so the Dirichlet IBP path applies. -/
theorem intervalCoupledClassicalC1BallEstimates_hmap_dirichlet_initial
    {p : CM2Params}
    {R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u₀_ext u₀'_ext : ℝ → ℝ}
    {T M G_u G_u_init C_source H : ℝ}
    (hT : 0 < T) (hH_nn : 0 ≤ H) (hC_nn : 0 ≤ C_source)
    (hG_init_nn : 0 ≤ G_u_init)
    (hM_eq : M = H + C_source * T)
    (hG_u_eq : G_u = G_u_init +
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
        (2 * Real.sqrt T) * C_source)
    (hu₀_sup : ∀ y : intervalDomainPoint, |u₀ y| ≤ H)
    (hext_eq : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift u₀ y = u₀_ext y)
    (hu₀_ext_int : MeasureTheory.Integrable u₀_ext
      (ShenWork.IntervalDomain.intervalMeasure 1))
    (hu₀_ext_C1 : ∀ y ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt u₀_ext (u₀'_ext y) y)
    (hu₀_ext'_int : IntervalIntegrable u₀'_ext MeasureTheory.volume 0 1)
    (hu₀_ext_one : u₀_ext 1 = 0)
    (hu₀_ext'_sup : ∀ y : ℝ, |u₀'_ext y| ≤ G_u_init)
    (hSol : ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
        IsPaper2ClassicalSolution intervalDomain p T
          (fun τ : ℝ => fun y : intervalDomainPoint =>
            intervalCoupledDuhamelOperator p R u₀ u τ y) v)
    (hSource_sup_local :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s, 0 ≤ s → s ≤ T → ∀ y : ℝ,
            |intervalDomainLift
              (intervalCoupledSource p (u s) (R (u s))) y| ≤ C_source)
    (hSource_sup_global :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s : ℝ, ∀ y : ℝ,
            |intervalDomainLift
              (intervalCoupledSource p (u s) (R (u s))) y| ≤ C_source)
    (hint :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ (t : ℝ) (x : intervalDomainPoint), 0 ≤ t → t ≤ T →
            MeasureTheory.IntegrableOn
              (fun s => intervalSemigroupOperator 1 (t - s)
                (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x.1)
              (Set.Icc 0 t) MeasureTheory.volume)
    (hlift_int :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s, 0 ≤ s → s ≤ T →
            MeasureTheory.Integrable
              (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
              (ShenWork.IntervalDomain.intervalMeasure 1))
    (hSource_int_global :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s : ℝ,
            MeasureTheory.Integrable
              (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
              (ShenWork.IntervalDomain.intervalMeasure 1))
    (hSupEq :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ (τ : ℝ) (x : ℝ), τ ∈ Set.Ioo (0 : ℝ) T → x ∈ Set.Icc (0 : ℝ) 1 →
            intervalDomainLift
              (fun y : intervalDomainPoint =>
                intervalCoupledDuhamelOperator p R u₀ u τ y) x =
            intervalSemigroupOperator 1 τ (intervalDomainLift u₀) x +
              ∫ s in (0 : ℝ)..τ,
                intervalSemigroupOperator 1 (τ - s)
                  (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x)
    (hGradEq :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ (τ : ℝ) (x : ℝ), τ ∈ Set.Ioo (0 : ℝ) T → x ∈ Set.Icc (0 : ℝ) 1 →
            deriv
              (intervalDomainLift
                (fun y : intervalDomainPoint =>
                  intervalCoupledDuhamelOperator p R u₀ u τ y)) x =
            deriv (fun z : ℝ =>
              intervalSemigroupOperator 1 τ (intervalDomainLift u₀) z +
              ∫ s in (0 : ℝ)..τ,
                intervalSemigroupOperator 1 (τ - s)
                  (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
                  z) x)
    (hLiftSemigroupEq :
      ∀ (τ : ℝ) (x : ℝ),
        intervalSemigroupOperator 1 τ (intervalDomainLift u₀) x =
        intervalSemigroupOperator 1 τ u₀_ext x)
    (hLiftSemigroupDerivEq :
      ∀ (τ : ℝ) (x : ℝ),
        deriv (fun z : ℝ =>
          intervalSemigroupOperator 1 τ (intervalDomainLift u₀) z) x =
        deriv (fun z : ℝ =>
          intervalSemigroupOperator 1 τ u₀_ext z) x)
    (hSplit :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ (τ : ℝ) (x : ℝ), τ ∈ Set.Ioo (0 : ℝ) T → x ∈ Set.Icc (0 : ℝ) 1 →
            deriv (fun z : ℝ =>
              intervalSemigroupOperator 1 τ u₀_ext z +
              ∫ s in (0 : ℝ)..τ,
                intervalSemigroupOperator 1 (τ - s)
                  (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
                  z) x =
            deriv (fun z : ℝ =>
              intervalSemigroupOperator 1 τ u₀_ext z) x +
            deriv (fun z : ℝ =>
              ∫ s in (0 : ℝ)..τ,
                intervalSemigroupOperator 1 (τ - s)
                  (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
                  z) x)
    (hLeibniz :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ (τ : ℝ) (x : ℝ), τ ∈ Set.Ioo (0 : ℝ) T → x ∈ Set.Icc (0 : ℝ) 1 →
            deriv (fun z : ℝ =>
              ∫ s in (0 : ℝ)..τ,
                intervalSemigroupOperator 1 (τ - s)
                  (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
                  z) x =
            ∫ s in (0 : ℝ)..τ,
              deriv (fun z : ℝ =>
                intervalSemigroupOperator 1 (τ - s)
                  (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
                  z) x)
    (hGrad_int :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ (τ : ℝ) (x : ℝ), τ ∈ Set.Ioo (0 : ℝ) T → x ∈ Set.Icc (0 : ℝ) 1 →
            IntervalIntegrable
              (fun s : ℝ =>
                deriv (fun z : ℝ =>
                  intervalSemigroupOperator 1 (τ - s)
                    (intervalDomainLift
                      (intervalCoupledSource p (u s) (R (u s)))) z) x)
              MeasureTheory.volume (0 : ℝ) τ)
    (hDom_int :
      ∀ (τ : ℝ), τ ∈ Set.Ioo (0 : ℝ) T →
        IntervalIntegrable
          (fun s : ℝ =>
            ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
              * C_source * (τ - s) ^ (-(1/2 : ℝ)))
          MeasureTheory.volume (0 : ℝ) τ) :
    ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
        IntervalDomainClassicalC1Snapshot p T M G_u
          (fun t : ℝ => fun x : intervalDomainPoint =>
            intervalCoupledDuhamelOperator p R u₀ u t x) v := by
  intro u v hsnap
  refine ⟨hSol u v hsnap, ?_, ?_⟩
  · -- Sup-bound conjunct: discharged by `intervalCoupledDuhamel_lift_abs_le`.
    intro τ hτ x hxIcc
    have hτ_le : τ ≤ T := le_of_lt hτ.2
    have hτ_nn : 0 ≤ τ := le_of_lt hτ.1
    have hsource' :
        ∀ s, 0 ≤ s → s ≤ T → ∀ y : ℝ,
          |intervalDomainLift
            (intervalCoupledSource p (u s) (R (u s))) y| ≤ C_source :=
      fun s hs0 hsT y => hSource_sup_local u v hsnap s hs0 hsT y
    have hint_pt :
        ∀ x' : intervalDomainPoint,
          MeasureTheory.IntegrableOn
            (fun s => intervalSemigroupOperator 1 (τ - s)
              (intervalDomainLift
                (intervalCoupledSource p (u s) (R (u s)))) x'.1)
            (Set.Icc 0 τ) MeasureTheory.volume :=
      fun x' => hint u v hsnap τ x' hτ_nn hτ_le
    have hlift_pt :
        ∀ s, 0 ≤ s → s ≤ T →
          MeasureTheory.Integrable
            (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
            (ShenWork.IntervalDomain.intervalMeasure 1) :=
      fun s hs0 hsT => hlift_int u v hsnap s hs0 hsT
    have hsup_le :=
      intervalCoupledDuhamel_lift_abs_le
        (p := p) (R := R) (u₀ := u₀) (u := u) (H := H) (C := C_source) (T := T)
        hH_nn hC_nn hu₀_sup hsource' (t := τ) hτ_nn hτ_le hint_pt hlift_pt
        x hxIcc
    have hM_form : H + C_source * T = M := hM_eq.symm
    rw [hM_form] at hsup_le
    exact hsup_le
  · -- Gradient-bound conjunct via the Dirichlet IBP path.
    intro τ hτ x hxIcc
    have hτ_le : τ ≤ T := le_of_lt hτ.2
    have hτ_pos : 0 < τ := hτ.1
    -- Rewrite the gradient through the Set.Icc-vs-intervalIntegral bridge.
    rw [hGradEq u v hsnap τ x hτ hxIcc]
    -- Replace the lifted initial datum by the C¹ Dirichlet representative `u₀_ext`
    -- inside the semigroup operator and its derivative.
    have hreplace_value :
        intervalSemigroupOperator 1 τ (intervalDomainLift u₀) x =
        intervalSemigroupOperator 1 τ u₀_ext x := hLiftSemigroupEq τ x
    have hreplace_fun :
        (fun z : ℝ =>
          intervalSemigroupOperator 1 τ (intervalDomainLift u₀) z +
          ∫ s in (0 : ℝ)..τ,
            intervalSemigroupOperator 1 (τ - s)
              (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
              z) =
        (fun z : ℝ =>
          intervalSemigroupOperator 1 τ u₀_ext z +
          ∫ s in (0 : ℝ)..τ,
            intervalSemigroupOperator 1 (τ - s)
              (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
              z) := by
      funext z
      rw [hLiftSemigroupEq τ z]
    rw [hreplace_fun]
    -- Apply the Dirichlet full estimate to the rewritten expression.
    have hF_int_τ :
        ∀ s, MeasureTheory.Integrable
          (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
          (ShenWork.IntervalDomain.intervalMeasure 1) :=
      fun s => hSource_int_global u v hsnap s
    have hF_sup_τ :
        ∀ s : ℝ, ∀ y : ℝ,
          |intervalDomainLift (intervalCoupledSource p (u s) (R (u s))) y| ≤
            C_source :=
      fun s y => hSource_sup_global u v hsnap s y
    have hbound :=
      intervalCoupledDuhamel_grad_estimate_full_dirichlet
        (t := τ) (T := T) hτ_pos hτ_le
        (u₀ := u₀_ext) (u₀' := u₀'_ext)
        hu₀_ext_int hu₀_ext_C1 hu₀_ext'_int hu₀_ext_one
        (G_u_init := G_u_init) hG_init_nn hu₀_ext'_sup
        (F := fun s : ℝ => intervalDomainLift
          (intervalCoupledSource p (u s) (R (u s))))
        hF_int_τ (C_source := C_source) hC_nn hF_sup_τ x
        (hSplit u v hsnap τ x hτ hxIcc)
        (hLeibniz u v hsnap τ x hτ hxIcc)
        (hGrad_int u v hsnap τ x hτ hxIcc)
        (hDom_int τ hτ)
    rw [hG_u_eq]
    exact hbound

/-! ### Path-A consolidation: clean `hmap_dirichlet_initial`.

The `..._hmap_dirichlet_initial` theorem above carries a long list of
bridge hypotheses, several of which are pure bookkeeping discharges given
the natural data we already have in hand (joint measurability of the
source field, the Dirichlet C¹ representative `u₀_ext` of the lifted
initial datum, etc.).

The clean variant below internalizes the routine bookkeeping bridges and
keeps only:

* the Schauder / PDE-solution content (`hSol` — multi-week),
* the boundary-derivative bridge `hGradEq` (the equality
  `deriv (lift ∘ Duhamel) = deriv (semigroup + integral)` at points in
  `Icc 0 1`; this is structurally non-trivial at the endpoints `{0,1}`),
* the gradient-`deriv_add` split `hSplit` (requires a packaged
  `DifferentiableAt` of both summands at `x₀`),
* the natural data hypotheses (sup/integrability/measurability),
* the Dirichlet C¹ representative on the lifted initial datum.

The following are discharged internally:

* `hSupEq` and `hLiftSemigroupDerivEq` — **dead hypotheses** in the
  proof body of `..._hmap_dirichlet_initial`; removed in the clean
  variant.
* `hLiftSemigroupEq` — discharged via integrand congruence on
  `intervalMeasure 1` (the kernel only sees `[0,1]`, on which
  `intervalDomainLift u₀ = u₀_ext` by `hext_eq`).
* `hLeibniz` — discharged via `intervalCoupledDuhamel_grad_leibniz`
  (the standalone Leibniz lemma).
* `hGrad_int` — discharged via
  `intervalCoupledDuhamel_grad_integrand_intervalIntegrable`.
* `hDom_int` — discharged via
  `intervalCoupledDuhamel_grad_envelope_intervalIntegrable`.

Remaining hypotheses are TRULY irreducible from the existing
infrastructure. -/

/-- **Clean `hmap` for the C¹_x ball, Dirichlet initial-data variant.**

Consolidated version of `intervalCoupledClassicalC1BallEstimates_hmap_dirichlet_initial`.
The routine bookkeeping bridges (`hSupEq`, `hLiftSemigroupEq`,
`hLiftSemigroupDerivEq`, `hLeibniz`, `hGrad_int`, `hDom_int`) have been
discharged internally; only the truly load-bearing hypotheses remain.

Specifically, the caller must supply:

1. **PDE content (Schauder, multi-week):** `hSol` — the Duhamel image of
   a snapshot satisfies `IsPaper2ClassicalSolution`.

2. **Boundary-derivative bridge:** `hGradEq` — the spatial derivative of
   the lifted Duhamel image agrees with the spatial derivative of the
   explicit `semigroup + integral` formula at points of `Icc 0 1`.  This
   is bookkeeping in `Ioo 0 1` (definitions agree on a neighborhood) but
   carries genuine content at the endpoints `{0,1}` (the lift is
   zero-extended outside).

3. **`deriv_add` for the sum split:** `hSplit` — both the
   semigroup-evaluated initial-data term and the source-integral term
   are differentiable at the relevant `x₀`, and `deriv` distributes over
   the sum.

4. **Natural data hypotheses:**
   - `hu₀_sup`, `hu₀_ext_int`, `hu₀_ext_C1`, `hu₀_ext'_int`,
     `hu₀_ext_one`, `hu₀_ext'_sup`, `hext_eq` (the Dirichlet C¹
     representative of the lifted initial datum);
   - `hSource_sup_local`, `hSource_sup_global`,
     `hSource_int_global` (pointwise / integrability bounds on the
     source field);
   - `hF_joint_meas` (joint measurability of the lifted source as a
     function `(s, y) ↦ lift(Source p (u s) (R (u s))) y`);
   - `hint`, `hlift_int` (per-`x` and per-`s` integrability).

The conclusion is the same `hmap` form as in
`..._hmap_dirichlet_initial`. -/
theorem intervalCoupledClassicalC1BallEstimates_hmap_dirichlet_initial_clean
    {p : CM2Params}
    {R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u₀_ext u₀'_ext : ℝ → ℝ}
    {T M G_u G_u_init C_source H : ℝ}
    (hT : 0 < T) (hH_nn : 0 ≤ H) (hC_nn : 0 ≤ C_source)
    (hG_init_nn : 0 ≤ G_u_init)
    (hM_eq : M = H + C_source * T)
    (hG_u_eq : G_u = G_u_init +
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
        (2 * Real.sqrt T) * C_source)
    (hu₀_sup : ∀ y : intervalDomainPoint, |u₀ y| ≤ H)
    (hext_eq : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift u₀ y = u₀_ext y)
    (hu₀_ext_int : MeasureTheory.Integrable u₀_ext
      (ShenWork.IntervalDomain.intervalMeasure 1))
    (hu₀_ext_C1 : ∀ y ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt u₀_ext (u₀'_ext y) y)
    (hu₀_ext'_int : IntervalIntegrable u₀'_ext MeasureTheory.volume 0 1)
    (hu₀_ext_one : u₀_ext 1 = 0)
    (hu₀_ext'_sup : ∀ y : ℝ, |u₀'_ext y| ≤ G_u_init)
    (hSol : ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
        IsPaper2ClassicalSolution intervalDomain p T
          (fun τ : ℝ => fun y : intervalDomainPoint =>
            intervalCoupledDuhamelOperator p R u₀ u τ y) v)
    (hSource_sup_local :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s, 0 ≤ s → s ≤ T → ∀ y : ℝ,
            |intervalDomainLift
              (intervalCoupledSource p (u s) (R (u s))) y| ≤ C_source)
    (hSource_sup_global :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s : ℝ, ∀ y : ℝ,
            |intervalDomainLift
              (intervalCoupledSource p (u s) (R (u s))) y| ≤ C_source)
    (hint :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ (t : ℝ) (x : intervalDomainPoint), 0 ≤ t → t ≤ T →
            MeasureTheory.IntegrableOn
              (fun s => intervalSemigroupOperator 1 (t - s)
                (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x.1)
              (Set.Icc 0 t) MeasureTheory.volume)
    (hlift_int :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s, 0 ≤ s → s ≤ T →
            MeasureTheory.Integrable
              (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
              (ShenWork.IntervalDomain.intervalMeasure 1))
    (hSource_int_global :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s : ℝ,
            MeasureTheory.Integrable
              (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
              (ShenWork.IntervalDomain.intervalMeasure 1))
    (hF_joint_meas :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          Measurable
            (Function.uncurry
              (fun (s : ℝ) (y : ℝ) =>
                intervalDomainLift
                  (intervalCoupledSource p (u s) (R (u s))) y)))
    (hGradEq :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ (τ : ℝ) (x : ℝ), τ ∈ Set.Ioo (0 : ℝ) T → x ∈ Set.Icc (0 : ℝ) 1 →
            deriv
              (intervalDomainLift
                (fun y : intervalDomainPoint =>
                  intervalCoupledDuhamelOperator p R u₀ u τ y)) x =
            deriv (fun z : ℝ =>
              intervalSemigroupOperator 1 τ (intervalDomainLift u₀) z +
              ∫ s in (0 : ℝ)..τ,
                intervalSemigroupOperator 1 (τ - s)
                  (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
                  z) x)
    (hSplit :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ (τ : ℝ) (x : ℝ), τ ∈ Set.Ioo (0 : ℝ) T → x ∈ Set.Icc (0 : ℝ) 1 →
            deriv (fun z : ℝ =>
              intervalSemigroupOperator 1 τ u₀_ext z +
              ∫ s in (0 : ℝ)..τ,
                intervalSemigroupOperator 1 (τ - s)
                  (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
                  z) x =
            deriv (fun z : ℝ =>
              intervalSemigroupOperator 1 τ u₀_ext z) x +
            deriv (fun z : ℝ =>
              ∫ s in (0 : ℝ)..τ,
                intervalSemigroupOperator 1 (τ - s)
                  (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
                  z) x) :
    ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
        IntervalDomainClassicalC1Snapshot p T M G_u
          (fun t : ℝ => fun x : intervalDomainPoint =>
            intervalCoupledDuhamelOperator p R u₀ u t x) v := by
  intro u v hsnap
  -- Internally-discharged bookkeeping: `hLiftSemigroupEq` from `hext_eq`.
  have hLiftSemigroupEq :
      ∀ (τ : ℝ) (x : ℝ),
        intervalSemigroupOperator 1 τ (intervalDomainLift u₀) x =
        intervalSemigroupOperator 1 τ u₀_ext x := by
    intro τ x
    unfold intervalSemigroupOperator
    -- The integral is taken w.r.t. `intervalMeasure 1 = volume.restrict (Icc 0 1)`;
    -- on `Icc 0 1` the two integrands agree by `hext_eq`.
    refine MeasureTheory.integral_congr_ae ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy
    show normalizedZerothReflectionKernel 1 τ x y * intervalDomainLift u₀ y =
      normalizedZerothReflectionKernel 1 τ x y * u₀_ext y
    rw [hext_eq y hy]
  -- Internally-discharged bookkeeping: `hLeibniz`, `hGrad_int`, `hDom_int`
  -- (per-snapshot, per-(τ, x)).
  have hDom_int_local :
      ∀ (τ : ℝ), τ ∈ Set.Ioo (0 : ℝ) T →
        IntervalIntegrable
          (fun s : ℝ =>
            ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
              * C_source * (τ - s) ^ (-(1/2 : ℝ)))
          MeasureTheory.volume (0 : ℝ) τ := by
    intro τ hτ
    exact intervalCoupledDuhamel_grad_envelope_intervalIntegrable hτ.1 C_source
  have hGrad_int_local :
      ∀ (τ : ℝ) (x : ℝ), τ ∈ Set.Ioo (0 : ℝ) T → x ∈ Set.Icc (0 : ℝ) 1 →
        IntervalIntegrable
          (fun s : ℝ =>
            deriv (fun z : ℝ =>
              intervalSemigroupOperator 1 (τ - s)
                (intervalDomainLift
                  (intervalCoupledSource p (u s) (R (u s)))) z) x)
          MeasureTheory.volume (0 : ℝ) τ := by
    intro τ x hτ _hx
    exact intervalCoupledDuhamel_grad_integrand_intervalIntegrable
      hτ.1 (hF_joint_meas u v hsnap)
      (fun s => hSource_int_global u v hsnap s)
      hC_nn (fun s y => hSource_sup_global u v hsnap s y) x
  have hLeibniz_local :
      ∀ (τ : ℝ) (x : ℝ), τ ∈ Set.Ioo (0 : ℝ) T → x ∈ Set.Icc (0 : ℝ) 1 →
        deriv (fun z : ℝ =>
          ∫ s in (0 : ℝ)..τ,
            intervalSemigroupOperator 1 (τ - s)
              (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
              z) x =
        ∫ s in (0 : ℝ)..τ,
          deriv (fun z : ℝ =>
            intervalSemigroupOperator 1 (τ - s)
              (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
              z) x := by
    intro τ x hτ _hx
    set F : ℝ → ℝ → ℝ := fun s y =>
      intervalDomainLift (intervalCoupledSource p (u s) (R (u s))) y with hF_def
    have hF_int : ∀ s, MeasureTheory.Integrable (F s)
        (ShenWork.IntervalDomain.intervalMeasure 1) :=
      fun s => hSource_int_global u v hsnap s
    have hF_sup : ∀ s, ∀ y : ℝ, |F s y| ≤ C_source :=
      fun s y => hSource_sup_global u v hsnap s y
    have hF_joint : Measurable (Function.uncurry F) := hF_joint_meas u v hsnap
    -- AE-strong-measurability of `s ↦ S(t-s)(F s) x` on `Ι 0 τ` (for the
    -- `hF_meas` slot of `intervalCoupledDuhamel_grad_leibniz`).
    have hF_meas_pt :
        ∀ x' : ℝ,
          MeasureTheory.AEStronglyMeasurable
            (fun s : ℝ => intervalSemigroupOperator 1 (τ - s) (F s) x')
            (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) τ)) := by
      intro x'
      exact intervalSemigroupOperator_s_dependent_aestronglyMeasurable_x
        hτ.1 hF_joint x'
    -- AE-strong-measurability of the derivative in `s` at `x`.
    have hF'_meas :
        MeasureTheory.AEStronglyMeasurable
          (fun s : ℝ =>
            deriv (fun z : ℝ =>
              intervalSemigroupOperator 1 (τ - s) (F s) z) x)
          (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) τ)) :=
      intervalSemigroupOperator_s_dependent_deriv_aestronglyMeasurable_x₀
        hτ.1 hF_joint hF_int x
    exact intervalCoupledDuhamel_grad_leibniz
      (t := τ) hτ.1 (F := F) hF_int (C_source := C_source) hC_nn hF_sup x
      hF_meas_pt hF'_meas (hDom_int_local τ hτ)
  -- Assemble the conclusion exactly as in `..._hmap_dirichlet_initial`, but
  -- with the discharged bridges built locally above.
  refine ⟨hSol u v hsnap, ?_, ?_⟩
  · -- Sup-bound conjunct (unchanged from `..._hmap_dirichlet_initial`).
    intro τ hτ x hxIcc
    have hτ_le : τ ≤ T := le_of_lt hτ.2
    have hτ_nn : 0 ≤ τ := le_of_lt hτ.1
    have hsource' :
        ∀ s, 0 ≤ s → s ≤ T → ∀ y : ℝ,
          |intervalDomainLift
            (intervalCoupledSource p (u s) (R (u s))) y| ≤ C_source :=
      fun s hs0 hsT y => hSource_sup_local u v hsnap s hs0 hsT y
    have hint_pt :
        ∀ x' : intervalDomainPoint,
          MeasureTheory.IntegrableOn
            (fun s => intervalSemigroupOperator 1 (τ - s)
              (intervalDomainLift
                (intervalCoupledSource p (u s) (R (u s)))) x'.1)
            (Set.Icc 0 τ) MeasureTheory.volume :=
      fun x' => hint u v hsnap τ x' hτ_nn hτ_le
    have hlift_pt :
        ∀ s, 0 ≤ s → s ≤ T →
          MeasureTheory.Integrable
            (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
            (ShenWork.IntervalDomain.intervalMeasure 1) :=
      fun s hs0 hsT => hlift_int u v hsnap s hs0 hsT
    have hsup_le :=
      intervalCoupledDuhamel_lift_abs_le
        (p := p) (R := R) (u₀ := u₀) (u := u) (H := H) (C := C_source) (T := T)
        hH_nn hC_nn hu₀_sup hsource' (t := τ) hτ_nn hτ_le hint_pt hlift_pt
        x hxIcc
    have hM_form : H + C_source * T = M := hM_eq.symm
    rw [hM_form] at hsup_le
    exact hsup_le
  · -- Gradient-bound conjunct, via the Dirichlet IBP path, with bookkeeping
    -- bridges discharged locally.
    intro τ hτ x hxIcc
    have hτ_le : τ ≤ T := le_of_lt hτ.2
    have hτ_pos : 0 < τ := hτ.1
    -- Boundary-derivative bridge `hGradEq` (kept; deep at endpoints).
    rw [hGradEq u v hsnap τ x hτ hxIcc]
    -- Replace `lift u₀` by the C¹ Dirichlet representative `u₀_ext` inside
    -- both the value and the integrand, using `hLiftSemigroupEq` derived
    -- from `hext_eq` above.
    have hreplace_fun :
        (fun z : ℝ =>
          intervalSemigroupOperator 1 τ (intervalDomainLift u₀) z +
          ∫ s in (0 : ℝ)..τ,
            intervalSemigroupOperator 1 (τ - s)
              (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
              z) =
        (fun z : ℝ =>
          intervalSemigroupOperator 1 τ u₀_ext z +
          ∫ s in (0 : ℝ)..τ,
            intervalSemigroupOperator 1 (τ - s)
              (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
              z) := by
      funext z
      rw [hLiftSemigroupEq τ z]
    rw [hreplace_fun]
    -- Apply the Dirichlet full estimate at `x`, with the locally-discharged
    -- `hLeibniz`, `hGrad_int`, `hDom_int` bridges, and the user-supplied
    -- `hSplit` bridge.
    have hF_int_τ :
        ∀ s, MeasureTheory.Integrable
          (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
          (ShenWork.IntervalDomain.intervalMeasure 1) :=
      fun s => hSource_int_global u v hsnap s
    have hF_sup_τ :
        ∀ s : ℝ, ∀ y : ℝ,
          |intervalDomainLift (intervalCoupledSource p (u s) (R (u s))) y| ≤
            C_source :=
      fun s y => hSource_sup_global u v hsnap s y
    have hbound :=
      intervalCoupledDuhamel_grad_estimate_full_dirichlet
        (t := τ) (T := T) hτ_pos hτ_le
        (u₀ := u₀_ext) (u₀' := u₀'_ext)
        hu₀_ext_int hu₀_ext_C1 hu₀_ext'_int hu₀_ext_one
        (G_u_init := G_u_init) hG_init_nn hu₀_ext'_sup
        (F := fun s : ℝ => intervalDomainLift
          (intervalCoupledSource p (u s) (R (u s))))
        hF_int_τ (C_source := C_source) hC_nn hF_sup_τ x
        (hSplit u v hsnap τ x hτ hxIcc)
        (hLeibniz_local τ x hτ hxIcc)
        (hGrad_int_local τ x hτ hxIcc)
        (hDom_int_local τ hτ)
    rw [hG_u_eq]
    exact hbound

/-! ### Path-A `_cleaner`: discharge `hSplit` via `deriv_add`.

`intervalCoupledClassicalC1BallEstimates_hmap_dirichlet_initial_clean` still
carries `hSplit` as a hypothesis — but `hSplit` is purely a real-analysis
`deriv_add` step at a single point `x₀`, requiring nothing more than
`DifferentiableAt` of the two summands.

* The initial-data summand `z ↦ S(τ) u₀_ext z` is `DifferentiableAt x` for
  any `x : ℝ` by `intervalSemigroupOperator_hasDerivAt_deriv`
  (needs only `Integrable u₀_ext (intervalMeasure 1)`, supplied by
  `hu₀_ext_int`).

* The source-integral summand
  `z ↦ ∫ s in (0..τ), S(τ-s) (lift F(s)) z` is `DifferentiableAt x` by
  the freshly-extracted
  `intervalCoupledDuhamel_grad_integral_hasDerivAt` (the `HasDerivAt`
  sibling of `intervalCoupledDuhamel_grad_leibniz`, same hypothesis
  shape).

`hGradEq` is **not** dischargeable from the existing infrastructure: it is
the identity

```
deriv (intervalDomainLift (fun y => Duhamel τ y)) x
  = deriv (fun z => S(τ)(lift u₀) z + ∫ S(τ-s)(lift F(s)) z ds) x
```

at points `x ∈ Icc 0 1`.  On the open interior `x ∈ Ioo 0 1`,
`intervalDomainLift (fun y => Duhamel τ y)` agrees with the explicit
formula on the open neighborhood `Ioo 0 1`, so the two derivatives coincide
by `Filter.EventuallyEq.deriv_eq`.  At the **endpoints** `{0, 1}` the lift
is zero-extended outside `[0,1]`, so the one-sided derivatives of the lift
and of the explicit formula generally disagree — Lean's `deriv` returns
`0` whenever a function is not differentiable, so the identity at the
endpoints carries genuine analytic content (the heat-flow image of a
Dirichlet datum has the same boundary derivative as the explicit
representative, which is a Dirichlet-PDE-level fact, not bookkeeping).

Closing `hGradEq` therefore requires either:
* restricting the gradient conjunct of `IntervalDomainClassicalC1Snapshot`
  to the open interior `Ioo 0 1` (a snapshot-shape change that propagates
  through downstream consumers), or
* a Dirichlet-boundary derivative-matching lemma for the lifted Duhamel
  image (a genuine PDE step, not currently in the Path-A scope).

This `_cleaner` theorem internalizes the `hSplit` discharge but keeps
`hGradEq` as the single remaining non-bookkeeping bridge. -/

/-- **Cleaner `hmap` for the C¹_x ball, Dirichlet initial-data variant.**

Consolidated version of
`intervalCoupledClassicalC1BallEstimates_hmap_dirichlet_initial_clean`.
The `hSplit` (`deriv_add` split for the sum of the initial-data semigroup
term and the source-integral term) is discharged internally from the
existing `HasDerivAt` infrastructure; only `hGradEq` (the boundary
derivative-matching bridge, deep at endpoints) is retained as a non-PDE
hypothesis.

Discharged internally beyond `_clean`:
* `hSplit` — via `deriv_add` on the two `HasDerivAt` summands.

Still retained (with reason):
* `hSol` — Schauder / PDE-solution content (multi-week).
* `hGradEq` — boundary derivative-matching bridge (Dirichlet-PDE content
  at the endpoints `{0,1}`; not bookkeeping).
* Natural data hypotheses on `u₀_ext`, the source field, and the per-`s`
  / per-`x` integrability.

The conclusion is the same `hmap` form as in
`..._hmap_dirichlet_initial_clean`. -/
theorem intervalCoupledClassicalC1BallEstimates_hmap_dirichlet_initial_cleaner
    {p : CM2Params}
    {R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u₀_ext u₀'_ext : ℝ → ℝ}
    {T M G_u G_u_init C_source H : ℝ}
    (hT : 0 < T) (hH_nn : 0 ≤ H) (hC_nn : 0 ≤ C_source)
    (hG_init_nn : 0 ≤ G_u_init)
    (hM_eq : M = H + C_source * T)
    (hG_u_eq : G_u = G_u_init +
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
        (2 * Real.sqrt T) * C_source)
    (hu₀_sup : ∀ y : intervalDomainPoint, |u₀ y| ≤ H)
    (hext_eq : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift u₀ y = u₀_ext y)
    (hu₀_ext_int : MeasureTheory.Integrable u₀_ext
      (ShenWork.IntervalDomain.intervalMeasure 1))
    (hu₀_ext_C1 : ∀ y ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt u₀_ext (u₀'_ext y) y)
    (hu₀_ext'_int : IntervalIntegrable u₀'_ext MeasureTheory.volume 0 1)
    (hu₀_ext_one : u₀_ext 1 = 0)
    (hu₀_ext'_sup : ∀ y : ℝ, |u₀'_ext y| ≤ G_u_init)
    (hSol : ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
        IsPaper2ClassicalSolution intervalDomain p T
          (fun τ : ℝ => fun y : intervalDomainPoint =>
            intervalCoupledDuhamelOperator p R u₀ u τ y) v)
    (hSource_sup_local :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s, 0 ≤ s → s ≤ T → ∀ y : ℝ,
            |intervalDomainLift
              (intervalCoupledSource p (u s) (R (u s))) y| ≤ C_source)
    (hSource_sup_global :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s : ℝ, ∀ y : ℝ,
            |intervalDomainLift
              (intervalCoupledSource p (u s) (R (u s))) y| ≤ C_source)
    (hint :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ (t : ℝ) (x : intervalDomainPoint), 0 ≤ t → t ≤ T →
            MeasureTheory.IntegrableOn
              (fun s => intervalSemigroupOperator 1 (t - s)
                (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x.1)
              (Set.Icc 0 t) MeasureTheory.volume)
    (hlift_int :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s, 0 ≤ s → s ≤ T →
            MeasureTheory.Integrable
              (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
              (ShenWork.IntervalDomain.intervalMeasure 1))
    (hSource_int_global :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s : ℝ,
            MeasureTheory.Integrable
              (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
              (ShenWork.IntervalDomain.intervalMeasure 1))
    (hF_joint_meas :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          Measurable
            (Function.uncurry
              (fun (s : ℝ) (y : ℝ) =>
                intervalDomainLift
                  (intervalCoupledSource p (u s) (R (u s))) y)))
    (hGradEq :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ (τ : ℝ) (x : ℝ), τ ∈ Set.Ioo (0 : ℝ) T → x ∈ Set.Icc (0 : ℝ) 1 →
            deriv
              (intervalDomainLift
                (fun y : intervalDomainPoint =>
                  intervalCoupledDuhamelOperator p R u₀ u τ y)) x =
            deriv (fun z : ℝ =>
              intervalSemigroupOperator 1 τ (intervalDomainLift u₀) z +
              ∫ s in (0 : ℝ)..τ,
                intervalSemigroupOperator 1 (τ - s)
                  (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
                  z) x) :
    ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
        IntervalDomainClassicalC1Snapshot p T M G_u
          (fun t : ℝ => fun x : intervalDomainPoint =>
            intervalCoupledDuhamelOperator p R u₀ u t x) v := by
  -- We discharge `hSplit` internally and forward to the `_clean` variant.
  refine intervalCoupledClassicalC1BallEstimates_hmap_dirichlet_initial_clean
    (p := p) (R := R) (u₀ := u₀) (u₀_ext := u₀_ext) (u₀'_ext := u₀'_ext)
    (T := T) (M := M) (G_u := G_u) (G_u_init := G_u_init)
    (C_source := C_source) (H := H)
    hT hH_nn hC_nn hG_init_nn hM_eq hG_u_eq hu₀_sup hext_eq
    hu₀_ext_int hu₀_ext_C1 hu₀_ext'_int hu₀_ext_one hu₀_ext'_sup
    hSol hSource_sup_local hSource_sup_global hint hlift_int
    hSource_int_global hF_joint_meas hGradEq ?_
  -- `hSplit`: pure `deriv_add` at the point `x` from `DifferentiableAt` of
  -- both summands.
  intro u v hsnap τ x hτ _hxIcc
  -- (1) `DifferentiableAt` of the initial-data semigroup term at `x`.
  have hInit_hasDeriv :
      HasDerivAt (fun z : ℝ => intervalSemigroupOperator 1 τ u₀_ext z)
        (deriv (fun z : ℝ => intervalSemigroupOperator 1 τ u₀_ext z) x) x :=
    ShenWork.RegularityBootstrap.intervalSemigroupOperator_hasDerivAt_deriv
      (L := 1) (t := τ) (x := x) hτ.1 (f := u₀_ext) hu₀_ext_int
  have hInit_diff :
      DifferentiableAt ℝ
        (fun z : ℝ => intervalSemigroupOperator 1 τ u₀_ext z) x :=
    hInit_hasDeriv.differentiableAt
  -- (2) `DifferentiableAt` of the source-integral term at `x`.
  set F : ℝ → ℝ → ℝ := fun s y =>
    intervalDomainLift (intervalCoupledSource p (u s) (R (u s))) y with hF_def
  have hF_int_local : ∀ s, MeasureTheory.Integrable (F s)
      (ShenWork.IntervalDomain.intervalMeasure 1) :=
    fun s => hSource_int_global u v hsnap s
  have hF_sup_local : ∀ s, ∀ y : ℝ, |F s y| ≤ C_source :=
    fun s y => hSource_sup_global u v hsnap s y
  have hF_joint : Measurable (Function.uncurry F) := hF_joint_meas u v hsnap
  have hF_meas_pt :
      ∀ x' : ℝ,
        MeasureTheory.AEStronglyMeasurable
          (fun s : ℝ => intervalSemigroupOperator 1 (τ - s) (F s) x')
          (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) τ)) := by
    intro x'
    exact intervalSemigroupOperator_s_dependent_aestronglyMeasurable_x
      hτ.1 hF_joint x'
  have hF'_meas :
      MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ =>
          deriv (fun z : ℝ =>
            intervalSemigroupOperator 1 (τ - s) (F s) z) x)
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) τ)) :=
    intervalSemigroupOperator_s_dependent_deriv_aestronglyMeasurable_x₀
      hτ.1 hF_joint hF_int_local x
  have hDom_int_local :
      IntervalIntegrable
        (fun s : ℝ =>
          ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            * C_source * (τ - s) ^ (-(1/2 : ℝ)))
        MeasureTheory.volume (0 : ℝ) τ :=
    intervalCoupledDuhamel_grad_envelope_intervalIntegrable hτ.1 C_source
  have hIntegral_hasDeriv :
      HasDerivAt
        (fun y : ℝ =>
          ∫ s in (0 : ℝ)..τ,
            intervalSemigroupOperator 1 (τ - s) (F s) y)
        (∫ s in (0 : ℝ)..τ,
          deriv (fun z : ℝ =>
            intervalSemigroupOperator 1 (τ - s) (F s) z) x)
        x :=
    intervalCoupledDuhamel_grad_integral_hasDerivAt
      (t := τ) hτ.1 (F := F) hF_int_local (C_source := C_source) hC_nn
      hF_sup_local x hF_meas_pt hF'_meas hDom_int_local
  have hIntegral_diff :
      DifferentiableAt ℝ
        (fun y : ℝ =>
          ∫ s in (0 : ℝ)..τ,
            intervalSemigroupOperator 1 (τ - s) (F s) y) x :=
    hIntegral_hasDeriv.differentiableAt
  -- `deriv_add` discharges `hSplit` at `x`.
  exact deriv_add hInit_diff hIntegral_diff

/-! ### Path-A `_cleanest`: decompose `hF_joint_meas` into atomic pieces.

The `_cleaner` form carries a monolithic joint-measurability hypothesis
`hF_joint_meas` on the LIFTED coupled source

```
Measurable (Function.uncurry (fun s y =>
  intervalDomainLift (intervalCoupledSource p (u s) (R (u s))) y))
```

This monolithic hypothesis hides two unrelated analytic ingredients:

1.  **Joint measurability of the lifted trajectory** `(s,y) ↦ lift(u s) y`
    — a low-level statement about the trajectory `u`, with conjunct (9) of
    `intervalDomainClassicalRegularity` (joint continuity on
    `Ioo 0 T ×ˢ Icc 0 1`) as the natural snapshot-derived source.

2.  **Joint measurability of the lifted chemotaxis divergence**
    `(s,y) ↦ lift(intervalDomainChemotaxisDiv p (u s) (R (u s))) y`
    — the genuinely deep PDE/spectral piece: it folds in joint regularity
    of the elliptic resolver `R(u s)` and of `∂ₓ lift (R (u s))`, neither
    of which is provided by the current snapshot.  This is the *honest*
    irreducible content of `hF_joint_meas`.

Below we prove a helper
`intervalCoupledSource_lift_joint_measurable_of_components` which combines
(1) and (2) into `hF_joint_meas` by pure algebraic measurability: the lifted
coupled source decomposes pointwise into a measurable combination of
`lift(u s) y` and `lift(chemDiv ...) y`, namely

```
lift(source p (u s)(R(u s))) y
  = -p.χ₀ · lift(chemDiv p (u s)(R(u s))) y
    + lift(u s) y · (p.a - p.b · (lift(u s) y) ^ p.α)
```

(the equality holds **everywhere** as a function of `y`, including outside
`[0,1]` where both sides are `0` because the lift is zero-extended and
`0^p.α = 0` for `p.α > 0`).

The `_cleanest` variant then replaces `hF_joint_meas` with the two atomic
hypotheses (1) and (2), so downstream consumers see two precisely-named
pieces and can attack them independently — (1) reduces to continuity →
measurability infrastructure, (2) remains the standing PDE gap. -/

/-- **Pointwise lift identity for the coupled source.**  Holds everywhere on
`ℝ` as a function of `y`: inside `[0,1]` both sides equal the value
`−χ₀·chemDiv + logistic`; outside, both sides are zero (the LHS by the lift
zero-extension; the RHS because `lift(u s) y = 0` and
`0 · (a − b · 0^α) = 0`). -/
lemma intervalCoupledSource_lift_pointwise_decomp
    (p : CM2Params) (u v : intervalDomainPoint → ℝ) (y : ℝ) :
    intervalDomainLift (intervalCoupledSource p u v) y =
      -p.χ₀ * intervalDomainLift (intervalDomainChemotaxisDiv p u v) y +
        intervalDomainLift u y *
          (p.a - p.b * (intervalDomainLift u y) ^ p.α) := by
  unfold intervalDomainLift
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
  · simp [hy, intervalCoupledSource, intervalLogisticSource]
  · -- Outside [0,1]: lift is 0 on every piece, RHS reduces to `0 · (...)`.
    have hαpos : (0 : ℝ) < p.α := p.hα
    have hα_ne : (0 : ℝ) ^ p.α = 0 := Real.zero_rpow hαpos.ne'
    simp [hy, hα_ne]

/-- **Algebraic combination step for `hF_joint_meas`.**

Given the two atomic joint-measurability inputs:

* `hU_joint : Measurable (Function.uncurry (fun s y => lift(u s) y))`,
* `hChemDiv_joint : Measurable (Function.uncurry (fun s y =>
      lift(chemDiv p (u s) (R (u s))) y))`,

the lifted coupled source `(s,y) ↦ lift(intervalCoupledSource p (u s)
(R (u s))) y` is jointly measurable.  The proof is the pointwise decomp
identity `intervalCoupledSource_lift_pointwise_decomp` plus standard
algebraic closure of `Measurable` (constants, sum, product, real `rpow`
by a fixed exponent). -/
theorem intervalCoupledSource_lift_joint_measurable_of_components
    {p : CM2Params}
    {R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (hU_joint :
      Measurable
        (Function.uncurry
          (fun (s : ℝ) (y : ℝ) => intervalDomainLift (u s) y)))
    (hChemDiv_joint :
      Measurable
        (Function.uncurry
          (fun (s : ℝ) (y : ℝ) =>
            intervalDomainLift
              (intervalDomainChemotaxisDiv p (u s) (R (u s))) y))) :
    Measurable
      (Function.uncurry
        (fun (s : ℝ) (y : ℝ) =>
          intervalDomainLift (intervalCoupledSource p (u s) (R (u s))) y)) := by
  -- Step 1.  Build the RHS of the pointwise decomposition as a `Measurable`
  -- function of `z : ℝ × ℝ`.
  set Glift : ℝ × ℝ → ℝ :=
    fun z : ℝ × ℝ => intervalDomainLift (u z.1) z.2 with hGlift_def
  set Hchem : ℝ × ℝ → ℝ :=
    fun z : ℝ × ℝ =>
      intervalDomainLift
        (intervalDomainChemotaxisDiv p (u z.1) (R (u z.1))) z.2
    with hHchem_def
  have hGlift_meas : Measurable Glift := hU_joint
  have hHchem_meas : Measurable Hchem := hChemDiv_joint
  -- `(lift u s y)^p.α` is measurable: it factors as `Real.rpow (·) p.α ∘ Glift`,
  -- and `Real.rpow` is continuous at every fixed exponent off the negative
  -- branch — but for our purposes we only need that the composition is
  -- measurable, which follows from `Glift_meas` plus the measurability of
  -- `fun x : ℝ => x ^ p.α` (a `fun_prop` Mathlib fact for `Real.rpow`).
  have h_rpow_meas : Measurable (fun x : ℝ => x ^ p.α) := by
    fun_prop
  have h_pow_meas : Measurable (fun z : ℝ × ℝ => (Glift z) ^ p.α) :=
    h_rpow_meas.comp hGlift_meas
  -- The bracket factor `(p.a - p.b * (Glift z)^p.α)`.
  have h_bracket :
      Measurable (fun z : ℝ × ℝ => p.a - p.b * (Glift z) ^ p.α) := by
    have := (measurable_const (a := p.b)).mul h_pow_meas
    exact (measurable_const (a := p.a)).sub this
  -- The logistic summand `Glift z * (p.a - p.b * (Glift z) ^ p.α)`.
  have h_log :
      Measurable
        (fun z : ℝ × ℝ => Glift z * (p.a - p.b * (Glift z) ^ p.α)) :=
    hGlift_meas.mul h_bracket
  -- The chemotaxis summand `-p.χ₀ * Hchem z`.
  have h_chem :
      Measurable (fun z : ℝ × ℝ => -p.χ₀ * Hchem z) :=
    (measurable_const (a := -p.χ₀)).mul hHchem_meas
  -- Sum of both summands.
  have h_sum :
      Measurable
        (fun z : ℝ × ℝ =>
          -p.χ₀ * Hchem z + Glift z * (p.a - p.b * (Glift z) ^ p.α)) :=
    h_chem.add h_log
  -- Step 2.  Identify the uncurried lifted source with `h_sum`'s function
  -- pointwise.
  have h_eq :
      (Function.uncurry
          (fun (s : ℝ) (y : ℝ) =>
            intervalDomainLift (intervalCoupledSource p (u s) (R (u s))) y)) =
        (fun z : ℝ × ℝ =>
          -p.χ₀ * Hchem z + Glift z * (p.a - p.b * (Glift z) ^ p.α)) := by
    funext z
    -- Destruct `z` to apply the pointwise lemma.
    obtain ⟨s, y⟩ := z
    simpa [Function.uncurry, Glift, Hchem] using
      intervalCoupledSource_lift_pointwise_decomp p (u s) (R (u s)) y
  rw [h_eq]
  exact h_sum

/-- **Cleanest `hmap` for the C¹_x ball, Dirichlet initial-data variant.**

Consolidated version of
`intervalCoupledClassicalC1BallEstimates_hmap_dirichlet_initial_cleaner`,
which replaces the monolithic `hF_joint_meas` hypothesis on the lifted
coupled source with the two atomic joint-measurability hypotheses

* `hU_joint_meas` — joint measurability of the lifted trajectory
  `(s,y) ↦ lift(u s) y`,
* `hChemDiv_joint_meas` — joint measurability of the lifted chemotaxis
  divergence `(s,y) ↦ lift(chemDiv p (u s) (R (u s))) y`.

The combination is discharged by
`intervalCoupledSource_lift_joint_measurable_of_components`.

Honest gap (unchanged from `_cleaner` in PDE content, but decomposed):
* `hU_joint_meas` reduces (under conjunct (9) of
  `intervalDomainClassicalRegularity`) to `ContinuousOn → Measurable`
  bookkeeping plus the `Borel`/`OpensMeasurableSpace` infrastructure on
  `ℝ²`; this is mechanical Lean work but not yet wired here.
* `hChemDiv_joint_meas` is the irreducible PDE content: joint regularity
  of `R (u s)` and `∂ₓ lift (R (u s))` in `(s,y)`, which the current
  snapshot does not provide.

The conclusion is the same `hmap` form as in
`..._hmap_dirichlet_initial_cleaner`. -/
theorem intervalCoupledClassicalC1BallEstimates_hmap_dirichlet_initial_cleanest
    {p : CM2Params}
    {R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u₀_ext u₀'_ext : ℝ → ℝ}
    {T M G_u G_u_init C_source H : ℝ}
    (hT : 0 < T) (hH_nn : 0 ≤ H) (hC_nn : 0 ≤ C_source)
    (hG_init_nn : 0 ≤ G_u_init)
    (hM_eq : M = H + C_source * T)
    (hG_u_eq : G_u = G_u_init +
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
        (2 * Real.sqrt T) * C_source)
    (hu₀_sup : ∀ y : intervalDomainPoint, |u₀ y| ≤ H)
    (hext_eq : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift u₀ y = u₀_ext y)
    (hu₀_ext_int : MeasureTheory.Integrable u₀_ext
      (ShenWork.IntervalDomain.intervalMeasure 1))
    (hu₀_ext_C1 : ∀ y ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt u₀_ext (u₀'_ext y) y)
    (hu₀_ext'_int : IntervalIntegrable u₀'_ext MeasureTheory.volume 0 1)
    (hu₀_ext_one : u₀_ext 1 = 0)
    (hu₀_ext'_sup : ∀ y : ℝ, |u₀'_ext y| ≤ G_u_init)
    (hSol : ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
        IsPaper2ClassicalSolution intervalDomain p T
          (fun τ : ℝ => fun y : intervalDomainPoint =>
            intervalCoupledDuhamelOperator p R u₀ u τ y) v)
    (hSource_sup_local :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s, 0 ≤ s → s ≤ T → ∀ y : ℝ,
            |intervalDomainLift
              (intervalCoupledSource p (u s) (R (u s))) y| ≤ C_source)
    (hSource_sup_global :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s : ℝ, ∀ y : ℝ,
            |intervalDomainLift
              (intervalCoupledSource p (u s) (R (u s))) y| ≤ C_source)
    (hint :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ (t : ℝ) (x : intervalDomainPoint), 0 ≤ t → t ≤ T →
            MeasureTheory.IntegrableOn
              (fun s => intervalSemigroupOperator 1 (t - s)
                (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x.1)
              (Set.Icc 0 t) MeasureTheory.volume)
    (hlift_int :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s, 0 ≤ s → s ≤ T →
            MeasureTheory.Integrable
              (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
              (ShenWork.IntervalDomain.intervalMeasure 1))
    (hSource_int_global :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s : ℝ,
            MeasureTheory.Integrable
              (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
              (ShenWork.IntervalDomain.intervalMeasure 1))
    (hU_joint_meas :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          Measurable
            (Function.uncurry
              (fun (s : ℝ) (y : ℝ) => intervalDomainLift (u s) y)))
    (hChemDiv_joint_meas :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          Measurable
            (Function.uncurry
              (fun (s : ℝ) (y : ℝ) =>
                intervalDomainLift
                  (intervalDomainChemotaxisDiv p (u s) (R (u s))) y)))
    (hGradEq :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ (τ : ℝ) (x : ℝ), τ ∈ Set.Ioo (0 : ℝ) T → x ∈ Set.Icc (0 : ℝ) 1 →
            deriv
              (intervalDomainLift
                (fun y : intervalDomainPoint =>
                  intervalCoupledDuhamelOperator p R u₀ u τ y)) x =
            deriv (fun z : ℝ =>
              intervalSemigroupOperator 1 τ (intervalDomainLift u₀) z +
              ∫ s in (0 : ℝ)..τ,
                intervalSemigroupOperator 1 (τ - s)
                  (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
                  z) x) :
    ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
        IntervalDomainClassicalC1Snapshot p T M G_u
          (fun t : ℝ => fun x : intervalDomainPoint =>
            intervalCoupledDuhamelOperator p R u₀ u t x) v := by
  -- Build `hF_joint_meas` from the two atomic pieces via the algebraic
  -- combination lemma, then forward to `_cleaner`.
  refine intervalCoupledClassicalC1BallEstimates_hmap_dirichlet_initial_cleaner
    (p := p) (R := R) (u₀ := u₀) (u₀_ext := u₀_ext) (u₀'_ext := u₀'_ext)
    (T := T) (M := M) (G_u := G_u) (G_u_init := G_u_init)
    (C_source := C_source) (H := H)
    hT hH_nn hC_nn hG_init_nn hM_eq hG_u_eq hu₀_sup hext_eq
    hu₀_ext_int hu₀_ext_C1 hu₀_ext'_int hu₀_ext_one hu₀_ext'_sup
    hSol hSource_sup_local hSource_sup_global hint hlift_int
    hSource_int_global ?_ hGradEq
  -- Atomic combination: `hF_joint_meas` from `hU_joint_meas` and
  -- `hChemDiv_joint_meas` at the current snapshot.
  intro u v hsnap
  exact intervalCoupledSource_lift_joint_measurable_of_components
    (p := p) (R := R) (u := u)
    (hU_joint_meas u v hsnap)
    (hChemDiv_joint_meas u v hsnap)

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
  * `intervalDomainChemotaxisDiv_eq_chemDivRepr_interior`
  * `intervalDomainChemotaxisDiv_classical_K_D_form_interior`
  * `IntervalCoupledClassicalC1BallEstimates`
  * `intervalDomainChemotaxisDiv_classical_K_D_form_interior_uniformG`
  * `intervalCoupledClassicalC1BallEstimates_assemble`
  * `intervalCoupledDuhamel_lift_abs_le`
  * `intervalCoupledDuhamel_grad_estimate_gap`
  * `intervalCoupledDuhamel_grad_estimate_gap_marker`
  * `intervalCoupledClassicalC1BallEstimates_hmap_of_pointwise_fixed_point`
  * `intervalCoupledDuhamel_grad_integrand_pointwise_bound`
  * `intervalIntegral_inv_sqrt_sub_eq_two_sqrt`
  * `intervalCoupledDuhamel_grad_integral_bound_of_leibniz`
  * `intervalCoupledDuhamel_grad_estimate_of_leibniz`
  * `intervalCoupledDuhamel_grad_initial_bound_of_commute`
  * `intervalCoupledDuhamel_grad_estimate_full_of_bridges`
  * `intervalCoupledClassicalC1BallEstimates_hmap_of_bridges`
  * `intervalCoupledDuhamel_grad_initial_bound_dirichlet`
  * `intervalCoupledDuhamel_grad_estimate_full_dirichlet`
  * `intervalCoupledClassicalC1BallEstimates_hmap_dirichlet_initial`
  * `intervalCoupledClassicalC1BallEstimates_hmap_dirichlet_initial_clean`
  * `intervalCoupledDuhamel_grad_integral_hasDerivAt`
  * `intervalCoupledClassicalC1BallEstimates_hmap_dirichlet_initial_cleaner`
  * `intervalCoupledSource_lift_pointwise_decomp`
  * `intervalCoupledSource_lift_joint_measurable_of_components`
  * `intervalCoupledClassicalC1BallEstimates_hmap_dirichlet_initial_cleanest`

(verify on uisai1, build green.) -/

end ShenWork.IntervalCoupledClassicalBallEstimates
