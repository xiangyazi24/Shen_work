/-
  ShenWork/PDE/IntervalCosineSliceRegularity.lean

  T7 step [A] — the **conjunct-(7) bridge** turning a slice represented as a
  cosine series into the exact closed-`Icc 0 1` `C²` + endpoint-Neumann shape of
  `intervalDomainClassicalRegularity` conjunct (7).

  This is the precise wiring that makes the T6 atom
  (`intervalDuhamelTerm_closedC2_of_timeC1_source`) and the generic cosine-series
  engine (`cosineCoeffSeries_contDiff_two` etc.) directly consumable as the
  closed-domain spatial regularity conjunct of a paper classical solution.

  A mild-solution slice `u_t = S_t u₀ + D_t` is a single cosine series
  `∑ cₙ cos(nπx)` with `∑ λₙ|cₙ| < ∞` (`T7_DESIGN.md`, Finding 1).  This file
  takes that representation abstractly (an arbitrary coefficient sequence `b`
  with `∑ λₙ|bₙ| < ∞`, agreeing with the slice's lift on `Icc 0 1`) and produces
  conjunct (7).

  The two-sided endpoint `deriv = 0` is discharged by the junk-value convention:
  the zero-extension `intervalDomainLift w` jumps at the endpoint when the slice
  value there is nonzero (`w 0 ≠ 0`, faithful for a *positive* classical
  solution), hence is not differentiable there, hence `deriv = 0`.  The genuine
  one-sided Neumann content is conjunct (6), supplied separately by the atom.

  No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.PDE.IntervalDuhamelClosedC2

open MeasureTheory Filter Topology
open ShenWork.IntervalDomain
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalDuhamelClosedC2

namespace ShenWork.IntervalCosineSliceRegularity

/-- **Junk-value endpoint derivative at the left endpoint.**  If the lift of a
slice is nonzero at `0`, then — since `intervalDomainLift` zero-extends to the
left of `0` — the lift is discontinuous at `0`, hence not differentiable, hence
`deriv = 0` by the Mathlib junk-value convention.  (Generalises
`intervalDomainLift_const_deriv_endpoint_zero`.) -/
theorem intervalDomainLift_deriv_left_endpoint_zero_of_ne
    {w : intervalDomainPoint → ℝ} (hne : intervalDomainLift w 0 ≠ 0) :
    deriv (intervalDomainLift w) 0 = 0 := by
  apply deriv_zero_of_not_differentiableAt
  intro hdiff
  have hcont : ContinuousAt (intervalDomainLift w) 0 := hdiff.continuousAt
  have hlim : Filter.Tendsto (intervalDomainLift w)
      (nhdsWithin (0 : ℝ) (Set.Iio 0)) (nhds (intervalDomainLift w 0)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hzero : Filter.Tendsto (intervalDomainLift w)
      (nhdsWithin (0 : ℝ) (Set.Iio 0)) (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    refine Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨Set.Iio 0, self_mem_nhdsWithin, fun y hy => ?_⟩
    have hmem : y ∉ Set.Icc (0 : ℝ) 1 := fun hmem => absurd hmem.1 (not_le.mpr hy)
    simp [intervalDomainLift, hmem]
  exact hne (tendsto_nhds_unique hlim hzero)

/-- **Junk-value endpoint derivative at the right endpoint.**  Symmetric to
`intervalDomainLift_deriv_left_endpoint_zero_of_ne`: the lift zero-extends to the
right of `1`, so a nonzero value at `1` forces a discontinuity there. -/
theorem intervalDomainLift_deriv_right_endpoint_zero_of_ne
    {w : intervalDomainPoint → ℝ} (hne : intervalDomainLift w 1 ≠ 0) :
    deriv (intervalDomainLift w) 1 = 0 := by
  apply deriv_zero_of_not_differentiableAt
  intro hdiff
  have hcont : ContinuousAt (intervalDomainLift w) 1 := hdiff.continuousAt
  have hlim : Filter.Tendsto (intervalDomainLift w)
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds (intervalDomainLift w 1)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hzero : Filter.Tendsto (intervalDomainLift w)
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    refine Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨Set.Ioi 1, self_mem_nhdsWithin, fun y hy => ?_⟩
    have hmem : y ∉ Set.Icc (0 : ℝ) 1 := fun hmem => absurd hmem.2 (not_le.mpr hy)
    simp [intervalDomainLift, hmem]
  exact hne (tendsto_nhds_unique hlim hzero)

/-- **Conjunct-(7) bridge.**  A slice whose lift agrees on `Icc 0 1` with a
cosine series `∑ bₙ cos(nπx)` of summable eigenvalue-weighted coefficients
(`∑ λₙ|bₙ| < ∞`) satisfies the closed-domain spatial-`C²` + endpoint-Neumann
conjunct (7) of `intervalDomainClassicalRegularity`, provided the slice's
endpoint values are nonzero (faithful for a positive classical solution).

* `ContDiffOn ℝ 2` on `Icc 0 1` — the engine's `ContDiff ℝ 2` restricted and
  transported along the `Icc 0 1` agreement.
* endpoint `deriv = 0` — junk-value non-differentiability of the zero-extension.

Instantiate with `b = (e^{−tλₙ}û₀ₙ + duhamelSpectralCoeff a t n)` for the full
mild-solution slice `S_t u₀ + D_t` (T6 atom + homogeneous semigroup). -/
theorem intervalDomainCosineSlice_conjunct7
    {b : ℕ → ℝ} {w : intervalDomainPoint → ℝ}
    (hb : Summable (fun n => unitIntervalCosineEigenvalue n * |b n|))
    (hagree : Set.EqOn (intervalDomainLift w)
        (fun x => ∑' n, b n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hne0 : intervalDomainLift w 0 ≠ 0)
    (hne1 : intervalDomainLift w 1 ≠ 0) :
    ContDiffOn ℝ 2 (intervalDomainLift w) (Set.Icc (0 : ℝ) 1)
      ∧ deriv (intervalDomainLift w) 0 = 0
      ∧ deriv (intervalDomainLift w) 1 = 0 := by
  refine ⟨?_, intervalDomainLift_deriv_left_endpoint_zero_of_ne hne0,
            intervalDomainLift_deriv_right_endpoint_zero_of_ne hne1⟩
  exact ((cosineCoeffSeries_contDiff_two hb).contDiffOn).congr hagree

end ShenWork.IntervalCosineSliceRegularity
