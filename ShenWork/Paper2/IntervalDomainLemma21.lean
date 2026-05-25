/-
  ShenWork/Paper2/IntervalDomainLemma21.lean

  Paper 2 Lemma 2.1 on intervalDomain: concrete heat-semigroup bridge.

  This file connects the already proved unit-interval heat estimates to the
  Paper2 interval-domain function interface.  It does not claim the full
  `Lemma_2_1 intervalDomain` package yet: the remaining missing analytic input
  is the fractional-domain graph norm / semigroup-difference estimate

    ‖S(t)u - u‖₂ ≤ C t^σ ‖u‖_{X^σ_2}

  for the actual Neumann heat semigroup on `[0,1]`, with a real-valued total
  `fractionalNorm` compatible with the statement layer.
-/
import ShenWork.Paper2.Statements
import ShenWork.PDE.HeatKernelGradientEstimates

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace ShenWork.Paper2.IntervalDomainLemma21

open ShenWork.IntervalDomain
open ShenWork.HeatKernelGradientEstimates

/-! ### Concrete interval-domain heat-semigroup interface -/

/-- The `LpSeminorm` used for interval-domain functions through the concrete
zero-extension `intervalDomainLift`. -/
def intervalDomainLpNorm (q : ℝ) (u : intervalDomain.Point → ℝ) : ℝ :=
  lpNorm (intervalDomainLift u) (ENNReal.ofReal q) (intervalMeasure 1)

/-- The restricted reflected heat operator as an interval-domain point
function.  This is the H0.1 helper operator on the unit interval. -/
def intervalDomainHeatSemigroup
    (t : ℝ) (u : intervalDomain.Point → ℝ) :
    intervalDomain.Point → ℝ :=
  fun x => intervalSemigroupOperator 1 t (intervalDomainLift u) x.1

/-- Real-valued `lpNorm` respects almost-everywhere equality.  Mathlib has the
corresponding theorem for `eLpNorm`; this is the `toReal` wrapper needed by the
statement-layer real norms. -/
theorem lpNorm_congr_ae_real
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {p : ℝ≥0∞} {μ : Measure α} {f g : α → E}
    (hfg : f =ᵐ[μ] g) :
    lpNorm f p μ = lpNorm g p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · have hg : AEStronglyMeasurable g μ :=
      (aestronglyMeasurable_congr hfg).mp hf
    rw [← toReal_eLpNorm hf, ← toReal_eLpNorm hg, eLpNorm_congr_ae hfg]
  · have hg : ¬ AEStronglyMeasurable g μ := by
      intro hg
      exact hf ((aestronglyMeasurable_congr hfg).mpr hg)
    simp [lpNorm, hf, hg]

/-- On the restricted unit interval measure, lifting the point-function heat
output agrees almost everywhere with the real-line helper operator. -/
theorem intervalDomainHeatSemigroup_lift_ae_eq
    (t : ℝ) (u : intervalDomain.Point → ℝ) :
    intervalDomainLift (intervalDomainHeatSemigroup t u)
      =ᵐ[intervalMeasure 1]
        fun x : ℝ => intervalSemigroupOperator 1 t (intervalDomainLift u) x := by
  unfold intervalMeasure intervalSet
  filter_upwards
    [MeasureTheory.self_mem_ae_restrict
      (show MeasurableSet (Set.Icc (0 : ℝ) 1) by simp)] with x hx
  simp [intervalDomainLift, intervalDomainHeatSemigroup, hx]

/-- The point-function heat output has the same `LpSeminorm` as the concrete
real helper operator on `[0,1]`. -/
theorem intervalDomainHeatSemigroup_lpNorm_eq
    (q t : ℝ) (u : intervalDomain.Point → ℝ) :
    intervalDomainLpNorm q (intervalDomainHeatSemigroup t u) =
      lpNorm
        (fun x : ℝ => intervalSemigroupOperator 1 t (intervalDomainLift u) x)
        (ENNReal.ofReal q) (intervalMeasure 1) := by
  exact lpNorm_congr_ae_real
    (intervalDomainHeatSemigroup_lift_ae_eq t u)

/-! ### H0.1/H0.2 estimates specialized to intervalDomain -/

/-- H0.1 specialized to `intervalDomain`: finite `L^p → L^q` smoothing for
the concrete unit-interval helper heat operator, stated on point functions via
`intervalDomainLift`. -/
theorem intervalDomainHeat_Lp_Lq_bound_from_memLp
    {t p q r : ℝ} (ht : 0 < t) (hrp : r.HolderConjugate p)
    (hpq : p ≤ q)
    {u : intervalDomain.Point → ℝ}
    (hu_mem :
      MemLp (intervalDomainLift u) (ENNReal.ofReal p) (intervalMeasure 1)) :
    intervalDomainLpNorm q (intervalDomainHeatSemigroup t u) ≤
      (1 / Real.sqrt (4 * Real.pi * t)) ^ (1 / p - 1 / q) *
        intervalDomainLpNorm p u := by
  rw [intervalDomainHeatSemigroup_lpNorm_eq]
  exact intervalHeatSemigroup_Lp_Lq_bound
    (L := 1) (t := t) (p := p) (q := q) (r := r)
    ht hrp hpq (f := intervalDomainLift u) hu_mem

/-- H0.2 specialized to `intervalDomain`: finite `L^p → L^q` smoothing for
the spatial derivative of the unit-interval helper heat operator. -/
theorem intervalDomainHeat_grad_Lp_Lq_bound_from_memLp
    {t p q : ℝ} (ht : 0 < t) (hp : 1 ≤ p) (hq : 0 < q)
    {u : intervalDomain.Point → ℝ}
    (hu_mem :
      MemLp (intervalDomainLift u) (ENNReal.ofReal p) (intervalMeasure 1)) :
    lpNorm
        (fun x : ℝ =>
          deriv
            (fun z : ℝ =>
              intervalSemigroupOperator 1 t (intervalDomainLift u) z) x)
        (ENNReal.ofReal q) (intervalMeasure 1) ≤
      heatGradientL1LinftyFactor t * intervalDomainLpNorm p u := by
  exact unitIntervalSemigroupOperator_grad_Lp_Lq_lpNorm_bound
    (t := t) (p := p) (q := q) ht hp hq
    (f := intervalDomainLift u) hu_mem

/-- The corresponding `L^p → L∞` derivative estimate for the unit-interval
helper heat operator. -/
theorem intervalDomainHeat_grad_Lp_Linfty_bound_from_memLp
    {t p : ℝ} (ht : 0 < t) (hp : 1 ≤ p)
    {u : intervalDomain.Point → ℝ}
    (hu_mem :
      MemLp (intervalDomainLift u) (ENNReal.ofReal p) (intervalMeasure 1)) :
    lpNorm
        (fun x : ℝ =>
          deriv
            (fun z : ℝ =>
              intervalSemigroupOperator 1 t (intervalDomainLift u) z) x)
        ∞ (intervalMeasure 1) ≤
      heatGradientL1LinftyFactor t * intervalDomainLpNorm p u := by
  exact unitIntervalSemigroupOperator_grad_Lp_Linfty_lpNorm_bound
    (t := t) (p := p) ht hp
    (f := intervalDomainLift u) hu_mem

end ShenWork.Paper2.IntervalDomainLemma21

end
