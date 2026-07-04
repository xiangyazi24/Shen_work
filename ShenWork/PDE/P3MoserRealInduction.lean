import ShenWork.PDE.P3MoserFirstCrossingContinuation

/-!
# Real-induction closure interface for the interval-domain Moser continuation

This file isolates the part of Residual D that is not present in the current
formal interface.  `SubintervalAssemblyResidual` still requires bootstrap
inputs (`rho`, `p0`, cross-diffusion, bootstrap, and the energy-gap statement)
which are not arguments of `FirstCrossingSupremumClosureResidual`; those inputs
are packaged below as `SubintervalMoserInputResidual`.

The actual supremum/real-induction step is packaged as
`FirstCrossingPointwiseUniformClosureResidual`: it says that short-time
boundedness plus the right-extension step yields a single pointwise bound on
the whole open interval `(0,T)`.  For `intervalDomain`, the remaining conversion
from that uniform pointwise bound to `IsPaper2BoundedBefore` is proved here from
the concrete `sSup (range |f|)` definition of `intervalDomain.supNorm`.
-/

open Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalDomainExistence.P3MoserIntegratedDissipationPDEv2

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserRealInduction

open ShenWork.IntervalDomainExistence.P3MoserFirstCrossingContinuation

/-- The missing local bootstrap data needed to apply
`SubintervalAssemblyResidual` at an arbitrary continued subinterval. -/
def SubintervalMoserInputResidual (p : CM2Params) : Prop :=
  ∀ {T τ : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
    IsPaper2ClassicalSolution intervalDomain p T u v →
      BoundedBeforeOnSubinterval intervalDomain u τ T →
        0 < τ →
          ∃ rho p0,
            CrossDiffusionBootstrapEstimate intervalDomain p τ rho u v ∧
              AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) τ rho p0 ∧
                LpBootstrapEnergyInequalityWithGap intervalDomain u τ rho p0

/-- The closed-time pointwise bound needed by the continuation step, after the
subinterval bootstrap inputs have been supplied. -/
def ClosedTimeSubintervalBoundResidual (p : CM2Params) : Prop :=
  ∀ {T τ : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
    IsPaper2ClassicalSolution intervalDomain p T u v →
      BoundedBeforeOnSubinterval intervalDomain u τ T →
        0 < τ →
          ∃ M, ∀ t, t ∈ Set.Icc (0 : ℝ) τ →
            ∀ x, |u t x| ≤ M

/-- The real-induction/supremum closure step, stated at the pointwise level.

This is the named residual for the topological `sSup` argument and the compact
uniformization of the pointwise subinterval bounds. -/
def FirstCrossingPointwiseUniformClosureResidual
    (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ {T : ℝ} {u v : ℝ → D.Point → ℝ},
    IsPaper2ClassicalSolution D p T u v →
      ShortTimeBoundedBeforeResidual D p →
        (∀ {τ : ℝ},
          0 < τ →
            τ < T →
              BoundedBeforeOnSubinterval D u τ T →
                ∃ δ, 0 < δ ∧ τ + δ ≤ T ∧
                  BoundedBeforeOnSubinterval D u (τ + δ) T) →
          ∃ M, ∀ t, 0 < t → t < T → ∀ x, |u t x| ≤ M

theorem closedTimeSubintervalBound_of_assembly
    {p : CM2Params}
    (hinputs : SubintervalMoserInputResidual p)
    (hassembly : SubintervalAssemblyResidual intervalDomain p) :
    ClosedTimeSubintervalBoundResidual p := by
  intro T τ u v hsol hsub hτ_pos
  rcases hinputs hsol hsub hτ_pos with
    ⟨rho, p0, hcross, hboot, hgap⟩
  exact hassembly hsol hsub hcross hboot hgap

theorem rightExtension_of_closedTimeSubintervalBound
    {p : CM2Params}
    (hclosed : ClosedTimeSubintervalBoundResidual p)
    (hextend : ExtensionByContinuityResidual intervalDomain p)
    {T τ : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hsub : BoundedBeforeOnSubinterval intervalDomain u τ T)
    (hτ_pos : 0 < τ)
    (hτT : τ < T) :
    ∃ δ, 0 < δ ∧ τ + δ ≤ T ∧
      BoundedBeforeOnSubinterval intervalDomain u (τ + δ) T := by
  rcases hclosed hsol hsub hτ_pos with ⟨M, hM⟩
  exact hextend hτT hsol (hM τ ⟨le_of_lt hτ_pos, le_rfl⟩)

/-- For the concrete interval domain, a uniform pointwise absolute-value bound
controls the concrete `supNorm`, because that norm is `sSup (range |f|)`. -/
theorem intervalDomain_supNorm_le_of_pointwise_abs_bound
    {f : intervalDomain.Point → ℝ} {M : ℝ}
    (hM : ∀ x : intervalDomain.Point, |f x| ≤ M) :
    intervalDomain.supNorm f ≤ M := by
  have hM_nonneg : 0 ≤ M := by
    let x0 : intervalDomain.Point := ⟨0, by exact ⟨by norm_num, by norm_num⟩⟩
    exact le_trans (abs_nonneg (f x0)) (hM x0)
  change intervalDomainSupNorm f ≤ M
  unfold intervalDomainSupNorm
  apply Real.sSup_le
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    exact hM x
  · exact hM_nonneg

/-- Uniform pointwise control on `(0,T)` gives the paper's bounded-before
`supNorm` conclusion on `intervalDomain`. -/
theorem intervalDomain_boundedBefore_of_pointwise_uniform_bound
    {T : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hpoint : ∃ M, ∀ t, 0 < t → t < T →
      ∀ x : intervalDomain.Point, |u t x| ≤ M) :
    IsPaper2BoundedBefore intervalDomain T u := by
  rcases hpoint with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro t ht0 htT
  exact intervalDomain_supNorm_le_of_pointwise_abs_bound (hM t ht0 htT)

/-- Conditional discharge of Residual D for `intervalDomain`.

The two remaining named residuals are exactly the pieces not available from the
current `FirstCrossingSupremumClosureResidual` arguments:
* `SubintervalMoserInputResidual`, because `SubintervalAssemblyResidual` needs
  bootstrap inputs not present in Residual D;
* `FirstCrossingPointwiseUniformClosureResidual`, the actual topological
  real-induction/supremum closure and uniformization step.
-/
theorem intervalDomain_FirstCrossingSupremumClosureResidual
    {p : CM2Params}
    (hinputs : SubintervalMoserInputResidual p)
    (hclosure : FirstCrossingPointwiseUniformClosureResidual intervalDomain p) :
    FirstCrossingSupremumClosureResidual intervalDomain p := by
  intro T u v hsol hshort hassembly hextend
  have hclosed : ClosedTimeSubintervalBoundResidual p :=
    closedTimeSubintervalBound_of_assembly hinputs hassembly
  have hright :
      ∀ {τ : ℝ},
        0 < τ →
          τ < T →
            BoundedBeforeOnSubinterval intervalDomain u τ T →
              ∃ δ, 0 < δ ∧ τ + δ ≤ T ∧
                BoundedBeforeOnSubinterval intervalDomain u (τ + δ) T := by
    intro τ hτ_pos hτT hsub
    exact rightExtension_of_closedTimeSubintervalBound
      hclosed hextend hsol hsub hτ_pos hτT
  exact intervalDomain_boundedBefore_of_pointwise_uniform_bound
    (hclosure hsol hshort hright)

#print axioms closedTimeSubintervalBound_of_assembly
#print axioms rightExtension_of_closedTimeSubintervalBound
#print axioms intervalDomain_supNorm_le_of_pointwise_abs_bound
#print axioms intervalDomain_boundedBefore_of_pointwise_uniform_bound
#print axioms intervalDomain_FirstCrossingSupremumClosureResidual

end ShenWork.IntervalDomainExistence.P3MoserRealInduction

end
