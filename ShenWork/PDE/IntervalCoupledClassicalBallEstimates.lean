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

end ShenWork.IntervalCoupledClassicalBallEstimates
