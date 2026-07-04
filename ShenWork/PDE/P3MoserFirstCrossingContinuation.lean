import ShenWork.PDE.P3MoserAssemblyFiller

/-!
# First-crossing continuation framework

This file records the non-circular continuation interface for producing
`IsPaper2BoundedBefore` on a finite horizon.  The current abstract
`BoundedDomainData` API does not identify `supNorm` with pointwise bounds, and
the compactness/continuity part of the first-crossing argument is not yet
available as a Mathlib-level theorem here.  Those analytic pieces are therefore
kept as named residual predicates; the formal theorems below wire them without
introducing any new assumptions.
-/

open Set
open ShenWork.Paper2
open ShenWork.IntervalDomainExistence.P3MoserIntegratedDissipationPDEv2

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserFirstCrossingContinuation

/-- Pointwise boundedness on the strict positive-time subinterval `[0, τ)`,
with the endpoint `τ` constrained by the ambient horizon `T`. -/
def BoundedBeforeOnSubinterval
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (τ T : ℝ) : Prop :=
  τ ≤ T ∧ ∀ t, 0 < t → t < τ → ∃ M, ∀ x, |u t x| ≤ M

theorem BoundedBeforeOnSubinterval.mono
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {τ τ' T : ℝ}
    (h : BoundedBeforeOnSubinterval D u τ T)
    (hτ'τ : τ' ≤ τ) :
    BoundedBeforeOnSubinterval D u τ' T := by
  refine ⟨le_trans hτ'τ h.1, ?_⟩
  intro t ht0 htτ'
  exact h.2 t ht0 (lt_of_lt_of_le htτ' hτ'τ)

theorem boundedBeforeOnSubinterval_of_Icc_pointwise_bound
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {τ T : ℝ}
    (hτT : τ ≤ T)
    (hbound : ∃ M, ∀ t, t ∈ Set.Icc (0 : ℝ) τ → ∀ x, |u t x| ≤ M) :
    BoundedBeforeOnSubinterval D u τ T := by
  rcases hbound with ⟨M, hM⟩
  refine ⟨hτT, ?_⟩
  intro t ht0 htτ
  exact ⟨M, hM t ⟨le_of_lt ht0, le_of_lt htτ⟩⟩

theorem boundedBeforeOnSubinterval_extend_right
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {τ δ T : ℝ}
    (hprev : BoundedBeforeOnSubinterval D u τ T)
    (hδT : τ + δ ≤ T)
    (hnew : ∃ M, ∀ t, τ ≤ t → t < τ + δ → ∀ x, |u t x| ≤ M) :
    BoundedBeforeOnSubinterval D u (τ + δ) T := by
  rcases hnew with ⟨Mnew, hMnew⟩
  refine ⟨hδT, ?_⟩
  intro t ht0 htτδ
  by_cases htτ : t < τ
  · exact hprev.2 t ht0 htτ
  · exact ⟨Mnew, hMnew t (le_of_not_gt htτ) htτδ⟩

/-- Residual A: a classical solution is pointwise bounded on some short
positive-time subinterval.  For the concrete interval this should come from
the closed-domain regularity/continuity fields and compactness. -/
def ShortTimeBoundedBeforeResidual
    (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ {T : ℝ} {u v : ℝ → D.Point → ℝ},
    IsPaper2ClassicalSolution D p T u v →
      ∃ τ, 0 < τ ∧ BoundedBeforeOnSubinterval D u τ T

/-- Residual B: the Moser assembly, localized to a subinterval `[0, τ]`, gives a
closed-time pointwise bound.  This is the non-circular replacement for feeding
`IsPaper2BoundedBefore D T u` into the full-horizon assembly. -/
def SubintervalAssemblyResidual
    (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ {T τ rho p0 : ℝ} {u v : ℝ → D.Point → ℝ},
    IsPaper2ClassicalSolution D p T u v →
      BoundedBeforeOnSubinterval D u τ T →
        CrossDiffusionBootstrapEstimate D p τ rho u v →
          AbstractLpBootstrapHypothesis D u (p.N : ℝ) τ rho p0 →
            LpBootstrapEnergyInequalityWithGap D u τ rho p0 →
              ∃ M, ∀ t, t ∈ Set.Icc (0 : ℝ) τ → ∀ x, |u t x| ≤ M

/-- Residual C: a closed-time bound at `τ`, plus classical continuity, extends
bounded-before to a strictly larger subinterval.  The result records `τ + δ ≤ T`
so that the extension stays inside the ambient finite horizon. -/
def ExtensionByContinuityResidual
    (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ {T τ M : ℝ} {u v : ℝ → D.Point → ℝ},
    τ < T →
      IsPaper2ClassicalSolution D p T u v →
        (∀ x, |u τ x| ≤ M) →
          ∃ δ, 0 < δ ∧ τ + δ ≤ T ∧
            BoundedBeforeOnSubinterval D u (τ + δ) T

/-- Residual D: the real first-crossing/supremum closure.  This is the only
place where the topological connectedness argument and the conversion from the
subinterval pointwise continuation statement to the paper's uniform `supNorm`
bounded-before predicate are still bundled. -/
def FirstCrossingSupremumClosureResidual
    (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ {T : ℝ} {u v : ℝ → D.Point → ℝ},
    IsPaper2ClassicalSolution D p T u v →
      ShortTimeBoundedBeforeResidual D p →
        SubintervalAssemblyResidual D p →
          ExtensionByContinuityResidual D p →
            IsPaper2BoundedBefore D T u

theorem short_time_boundedBefore_of_classical
    {D : BoundedDomainData} {p : CM2Params}
    (hshort : ShortTimeBoundedBeforeResidual D p)
    {T : ℝ} {u v : ℝ → D.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution D p T u v) :
    ∃ τ, 0 < τ ∧ BoundedBeforeOnSubinterval D u τ T :=
  hshort hsol

theorem assembly_on_subinterval
    {D : BoundedDomainData} {p : CM2Params}
    (hassembly : SubintervalAssemblyResidual D p)
    {T τ rho p0 : ℝ} {u v : ℝ → D.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution D p T u v)
    (hsub : BoundedBeforeOnSubinterval D u τ T)
    (hcross : CrossDiffusionBootstrapEstimate D p τ rho u v)
    (hboot : AbstractLpBootstrapHypothesis D u (p.N : ℝ) τ rho p0)
    (hgap : LpBootstrapEnergyInequalityWithGap D u τ rho p0) :
    ∃ M, ∀ t, t ∈ Set.Icc (0 : ℝ) τ → ∀ x, |u t x| ≤ M :=
  hassembly hsol hsub hcross hboot hgap

theorem extension_of_assembly_output
    {D : BoundedDomainData} {p : CM2Params}
    (hextend : ExtensionByContinuityResidual D p)
    {T τ M : ℝ} {u v : ℝ → D.Point → ℝ}
    (hτT : τ < T)
    (hsol : IsPaper2ClassicalSolution D p T u v)
    (hbound_at_τ : ∀ x, |u τ x| ≤ M) :
    ∃ δ, 0 < δ ∧ τ + δ ≤ T ∧
      BoundedBeforeOnSubinterval D u (τ + δ) T :=
  hextend hτT hsol hbound_at_τ

/-- Conditional first-crossing continuation theorem.  Once residuals A--D are
discharged for the concrete interval assembly, this produces the desired
full-horizon `IsPaper2BoundedBefore` without feeding that predicate back into
the Moser assembly. -/
theorem boundedBefore_of_classical_and_assembly
    {D : BoundedDomainData} {p : CM2Params}
    (hshort : ShortTimeBoundedBeforeResidual D p)
    (hassembly : SubintervalAssemblyResidual D p)
    (hextend : ExtensionByContinuityResidual D p)
    (hclosure : FirstCrossingSupremumClosureResidual D p)
    {T : ℝ} {u v : ℝ → D.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution D p T u v) :
    IsPaper2BoundedBefore D T u :=
  hclosure hsol hshort hassembly hextend

#print axioms BoundedBeforeOnSubinterval.mono
#print axioms boundedBeforeOnSubinterval_of_Icc_pointwise_bound
#print axioms boundedBeforeOnSubinterval_extend_right
#print axioms short_time_boundedBefore_of_classical
#print axioms assembly_on_subinterval
#print axioms extension_of_assembly_output
#print axioms boundedBefore_of_classical_and_assembly

end ShenWork.IntervalDomainExistence.P3MoserFirstCrossingContinuation

end
