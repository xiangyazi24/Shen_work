import ShenWork.PDE.IntervalSemigroupUniform

/-!
# Conditional C1 approximate identity for the homogeneous initial leg

This module isolates the easy metric part of the homogeneous C1 initial
approach.  The real analytic input, a derivative-commutation/IBP theorem for
the full Neumann semigroup, is kept as an explicit hypothesis.
-/

open MeasureTheory Filter Topology
open scoped Topology

open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel

namespace ShenWork.IntervalSemigroupC1ApproxIdentity

noncomputable section

/-- The full Neumann semigroup only reads the source on `[0,1]`. -/
theorem intervalFullSemigroupOperator_congr_on_Icc
    {f g : ℝ → ℝ}
    (hfg : ∀ y ∈ Set.Icc (0 : ℝ) 1, f y = g y)
    (t x : ℝ) :
    intervalFullSemigroupOperator t f x =
      intervalFullSemigroupOperator t g x := by
  unfold intervalFullSemigroupOperator
  apply MeasureTheory.integral_congr_ae
  have hmem : ∀ᵐ y ∂(intervalMeasure 1), y ∈ Set.Icc (0 : ℝ) 1 := by
    simp only [intervalMeasure, intervalSet]
    exact (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
      (Filter.Eventually.of_forall fun y hy => hy)
  filter_upwards [hmem] with y hy
  rw [hfg y hy]

/-- Uniform value approximate identity on `[0,1]` for a candidate derivative
profile. -/
def InitialLegDerivativeValueApprox (df : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |intervalFullSemigroupOperator t df x - df x| < ε

/-- Explicit derivative-commutation/IBP hypothesis for the homogeneous initial
leg.  This is the analytic theorem still missing from the current source-side
toolbox. -/
def InitialLegDerivativeCommutes (f df : ℝ → ℝ) : Prop :=
  ∀ {t : ℝ}, 0 < t → ∀ x ∈ Set.Icc (0 : ℝ) 1,
    deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) x =
      intervalFullSemigroupOperator t df x

/-- If the derivative field commutes with the homogeneous semigroup leg and the
candidate derivative profile has value approximate identity, then the
homogeneous C1 initial approach follows. -/
theorem initialLegC1Approx_of_valueApprox_of_commute
    {f df : ℝ → ℝ}
    (happrox : InitialLegDerivativeValueApprox df)
    (hcomm : InitialLegDerivativeCommutes f df) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) x - df x| < ε := by
  intro ε hε
  rcases happrox ε hε with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro t ht htδ x hx
  simpa [hcomm (t := t) ht x hx] using hδ t ht htδ x hx

/-- The existing uniform value approximate identity supplies
`InitialLegDerivativeValueApprox` for a globally continuous derivative
representative. -/
theorem derivativeValueApprox_of_continuous
    (df : ℝ → ℝ) (hdf : Continuous df) :
    InitialLegDerivativeValueApprox df := by
  intro ε hε
  have htend :=
    ShenWork.IntervalSemigroupUniform.intervalFullSemigroup_tendstoUniformlyOn df hdf
  rw [Metric.tendstoUniformlyOn_iff] at htend
  have hev := htend ε hε
  rw [Filter.eventually_iff, mem_nhdsGT_iff_exists_Ioo_subset] at hev
  rcases hev with ⟨δ, hδmem, hδsub⟩
  refine ⟨δ, hδmem, ?_⟩
  intro t ht htδ x hx
  have hdist := hδsub ⟨ht, htδ⟩ x hx
  simpa [Real.dist_eq, abs_sub_comm] using hdist

/-- Domain-facing conditional homogeneous C1 initial approach.  This is the
metric wrapper needed by the zero-start derivative route once the genuine
commutation/IBP theorem is supplied. -/
theorem intervalFullSemigroup_initialLegC1Approx_of_global_deriv_continuous_of_commute
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀x_cont : Continuous (fun x : ℝ => deriv (intervalDomainLift u₀) x))
    (hcomm : InitialLegDerivativeCommutes
      (intervalDomainLift u₀)
      (fun x : ℝ => deriv (intervalDomainLift u₀) x)) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (fun z : ℝ =>
            intervalFullSemigroupOperator t (intervalDomainLift u₀) z) x -
          deriv (intervalDomainLift u₀) x| < ε :=
  initialLegC1Approx_of_valueApprox_of_commute
    (derivativeValueApprox_of_continuous
      (fun x : ℝ => deriv (intervalDomainLift u₀) x) hu₀x_cont)
    hcomm

end

end ShenWork.IntervalSemigroupC1ApproxIdentity
