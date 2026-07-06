import ShenWork.PDE.IntervalSemigroupUniform
import ShenWork.PDE.IntervalFullKernelSourceIBP

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

/-- Uniform approximate identity on `[0,1]` for the conjugate-kernel
representation of the homogeneous initial-leg derivative.  This is the
remaining analytic input after applying source-side kernel IBP. -/
def InitialLegConjugateDerivativeApprox (df : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |-(∫ y in (0 : ℝ)..1, df y * intervalNeumannConjugateKernel t x y) - df x| < ε

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

/-- The public source-IBP identity reduces homogeneous C1 initial approach to
the conjugate-kernel approximate identity for the derivative profile. -/
theorem initialLegC1Approx_of_conjugateApprox_of_sourceIBP
    {f df : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    {Cf : ℝ} (hf_bound : ∀ y, |f y| ≤ Cf)
    (hf_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt f (df y) y)
    (hdf_int : IntervalIntegrable df MeasureTheory.volume 0 1)
    (happrox : InitialLegConjugateDerivativeApprox df) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) x - df x| < ε := by
  intro ε hε
  rcases happrox ε hε with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro t ht htδ x hx
  have hderiv :
      deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) x =
        -(∫ y in (0 : ℝ)..1, df y * intervalNeumannConjugateKernel t x y) :=
    deriv_intervalFullSemigroupOperator_eq_neg_conjugateKernel_source_integral
      (t := t) ht (Q := f) (Q' := df) hf_meas hf_bound hf_deriv hdf_int x
  rw [hderiv]
  exact hδ t ht htδ x hx

/-- Source-IBP reducer through a global C1 representative `Q` that agrees with
the desired source `f` on `[0,1]`.  This is the safer form for zero-extended
interval data, whose raw lift need not be globally differentiable at the
endpoints. -/
theorem initialLegC1Approx_of_conjugateApprox_of_Icc_repr
    {f Q dQ : ℝ → ℝ}
    (hfQ : ∀ y ∈ Set.Icc (0 : ℝ) 1, f y = Q y)
    (hQ_meas : AEStronglyMeasurable Q (intervalMeasure 1))
    {CQ : ℝ} (hQ_bound : ∀ y, |Q y| ≤ CQ)
    (hQ_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt Q (dQ y) y)
    (hdQ_int : IntervalIntegrable dQ MeasureTheory.volume 0 1)
    (happrox : InitialLegConjugateDerivativeApprox dQ) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) x - dQ x| < ε := by
  intro ε hε
  rcases happrox ε hε with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro t ht htδ x hx
  have hfun :
      (fun z : ℝ => intervalFullSemigroupOperator t f z) =
        fun z : ℝ => intervalFullSemigroupOperator t Q z := by
    funext z
    exact intervalFullSemigroupOperator_congr_on_Icc hfQ t z
  rw [hfun]
  have hderiv :
      deriv (fun z : ℝ => intervalFullSemigroupOperator t Q z) x =
        -(∫ y in (0 : ℝ)..1, dQ y * intervalNeumannConjugateKernel t x y) :=
    deriv_intervalFullSemigroupOperator_eq_neg_conjugateKernel_source_integral
      (t := t) ht (Q := Q) (Q' := dQ) hQ_meas hQ_bound hQ_deriv hdQ_int x
  rw [hderiv]
  exact hδ t ht htδ x hx

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

/-- Domain-facing source-IBP reducer for the homogeneous C1 initial approach.
The derivative profile `du₀` is explicit, and the only convergence hypothesis is
the conjugate-kernel approximate identity for `du₀`. -/
theorem intervalFullSemigroup_initialLegC1Approx_of_conjugateApprox
    {u₀ : intervalDomainPoint → ℝ} {du₀ : ℝ → ℝ}
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {Cu₀ : ℝ} (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ Cu₀)
    (hu₀_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (intervalDomainLift u₀) (du₀ y) y)
    (hdu₀_int : IntervalIntegrable du₀ MeasureTheory.volume 0 1)
    (happrox : InitialLegConjugateDerivativeApprox du₀) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (fun z : ℝ =>
            intervalFullSemigroupOperator t (intervalDomainLift u₀) z) x -
          du₀ x| < ε :=
  initialLegC1Approx_of_conjugateApprox_of_sourceIBP
    hu₀_meas hu₀_bound hu₀_deriv hdu₀_int happrox

/-- Domain-facing representative form for interval initial data.  The global
representative `Q` supplies the differentiability required by source IBP, while
the semigroup still acts on the original zero-extended interval source. -/
theorem intervalFullSemigroup_initialLegC1Approx_of_Icc_repr_conjugateApprox
    {u₀ : intervalDomainPoint → ℝ} {Q du₀ : ℝ → ℝ}
    (hu₀Q : ∀ y ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift u₀ y = Q y)
    (hQ_meas : AEStronglyMeasurable Q (intervalMeasure 1))
    {CQ : ℝ} (hQ_bound : ∀ y, |Q y| ≤ CQ)
    (hQ_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt Q (du₀ y) y)
    (hdu₀_int : IntervalIntegrable du₀ MeasureTheory.volume 0 1)
    (happrox : InitialLegConjugateDerivativeApprox du₀) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (fun z : ℝ =>
            intervalFullSemigroupOperator t (intervalDomainLift u₀) z) x -
          du₀ x| < ε :=
  initialLegC1Approx_of_conjugateApprox_of_Icc_repr
    hu₀Q hQ_meas hQ_bound hQ_deriv hdu₀_int happrox

end

end ShenWork.IntervalSemigroupC1ApproxIdentity
