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

/-- The endpoint `deriv = 0` conclusion does not actually require a nonzero
endpoint value.  If the zero extension is not differentiable, this is the
usual junk-value conclusion.  If it is differentiable, uniqueness of the
one-sided derivative on `[0,1]` identifies it with the derivative of the
cosine-series representative, which vanishes at both endpoints. -/
theorem intervalDomainCosineSlice_conjunct7_unconditional
    {b : ℕ → ℝ} {w : intervalDomainPoint → ℝ}
    (hb : Summable (fun n => unitIntervalCosineEigenvalue n * |b n|))
    (hagree : Set.EqOn (intervalDomainLift w)
        (fun x => ∑' n, b n * cosineMode n x) (Set.Icc (0 : ℝ) 1)) :
    ContDiffOn ℝ 2 (intervalDomainLift w) (Set.Icc (0 : ℝ) 1)
      ∧ deriv (intervalDomainLift w) 0 = 0
      ∧ deriv (intervalDomainLift w) 1 = 0 := by
  let g : ℝ → ℝ := fun x => ∑' n, b n * cosineMode n x
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have h1mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hg0 : HasDerivWithinAt g 0 (Set.Icc (0 : ℝ) 1) 0 := by
    have hder : HasDerivAt g 0 0 := by
      simpa [g] using (cosineCoeffSeries_grad_hasDerivAt hb 0)
    exact hder.hasDerivWithinAt
  have hg1 : HasDerivWithinAt g 0 (Set.Icc (0 : ℝ) 1) 1 := by
    have hder : HasDerivAt g 0 1 := by
      simpa [g] using (cosineCoeffSeries_grad_hasDerivAt hb 1)
    exact hder.hasDerivWithinAt
  have hw0 : HasDerivWithinAt (intervalDomainLift w) 0
      (Set.Icc (0 : ℝ) 1) 0 :=
    hg0.congr_of_mem (fun x hx => by simpa [g] using hagree hx) h0mem
  have hw1 : HasDerivWithinAt (intervalDomainLift w) 0
      (Set.Icc (0 : ℝ) 1) 1 :=
    hg1.congr_of_mem (fun x hx => by simpa [g] using hagree hx) h1mem
  refine ⟨((cosineCoeffSeries_contDiff_two hb).contDiffOn).congr hagree, ?_, ?_⟩
  · by_cases hdiff : DifferentiableAt ℝ (intervalDomainLift w) 0
    · exact (uniqueDiffOn_Icc_zero_one 0 h0mem).eq_deriv
        (Set.Icc (0 : ℝ) 1) hdiff.hasDerivAt.hasDerivWithinAt hw0
    · exact deriv_zero_of_not_differentiableAt hdiff
  · by_cases hdiff : DifferentiableAt ℝ (intervalDomainLift w) 1
    · exact (uniqueDiffOn_Icc_zero_one 1 h1mem).eq_deriv
        (Set.Icc (0 : ℝ) 1) hdiff.hasDerivAt.hasDerivWithinAt hw1
    · exact deriv_zero_of_not_differentiableAt hdiff

/-! ## Subgoal [B] — the remaining spatial conjuncts (3) and (6)

Conjunct (3) is the open-interval `ContDiffOn` (a restriction of conjunct (7));
conjunct (6) is the genuine one-sided Neumann *limit* `deriv(lift w) → 0` at the
endpoints.  Both are supplied by the same cosine-series engine. -/

/-- **Conjunct-(3) bridge.**  Open-interval spatial `C²` for a cosine-series
slice — the restriction of conjunct (7)'s closed `ContDiffOn` to `Ioo 0 1`.
Needs no endpoint hypotheses (the interior never sees the zero-extension jump). -/
theorem intervalDomainCosineSlice_contDiffOn_Ioo
    {b : ℕ → ℝ} {w : intervalDomainPoint → ℝ}
    (hb : Summable (fun n => unitIntervalCosineEigenvalue n * |b n|))
    (hagree : Set.EqOn (intervalDomainLift w)
        (fun x => ∑' n, b n * cosineMode n x) (Set.Icc (0 : ℝ) 1)) :
    ContDiffOn ℝ 2 (intervalDomainLift w) (Set.Ioo (0 : ℝ) 1) :=
  (((cosineCoeffSeries_contDiff_two hb).contDiffOn).congr hagree).mono
    Set.Ioo_subset_Icc_self

/-- **Eventual deriv agreement near an endpoint.**  On the open interior the lift
agrees with the cosine series `g` on an open neighbourhood of each point, so the
derivatives agree on the one-sided neighbourhood filter at the endpoint. -/
private theorem deriv_lift_eventuallyEq_cosineSeries_left
    {b : ℕ → ℝ} {w : intervalDomainPoint → ℝ}
    (hagree : Set.EqOn (intervalDomainLift w)
        (fun x => ∑' n, b n * cosineMode n x) (Set.Icc (0 : ℝ) 1)) :
    deriv (intervalDomainLift w)
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)] deriv (fun x => ∑' n, b n * cosineMode n x) := by
  have hmem : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    mem_nhdsWithin.mpr ⟨Set.Iio 1, isOpen_Iio, by norm_num, by
      intro z hz; exact ⟨hz.2, hz.1⟩⟩
  filter_upwards [hmem] with y hy
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz
  exact hagree (Set.Ioo_subset_Icc_self hz)

private theorem deriv_lift_eventuallyEq_cosineSeries_right
    {b : ℕ → ℝ} {w : intervalDomainPoint → ℝ}
    (hagree : Set.EqOn (intervalDomainLift w)
        (fun x => ∑' n, b n * cosineMode n x) (Set.Icc (0 : ℝ) 1)) :
    deriv (intervalDomainLift w)
      =ᶠ[nhdsWithin (1 : ℝ) (Set.Iio 1)] deriv (fun x => ∑' n, b n * cosineMode n x) := by
  have hmem : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (1 : ℝ) (Set.Iio 1) :=
    mem_nhdsWithin.mpr ⟨Set.Ioi 0, isOpen_Ioi, by norm_num, by
      intro z hz; exact ⟨hz.1, hz.2⟩⟩
  filter_upwards [hmem] with y hy
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz
  exact hagree (Set.Ioo_subset_Icc_self hz)

/-- **Conjunct-(6) bridge, left endpoint.**  The genuine one-sided Neumann limit
`deriv(lift w) → 0` as `x → 0⁺`: on the interior the lift's derivative equals the
cosine series' derivative, which is globally continuous (the series is `C²`) and
vanishes at `0` (`cosineCoeffSeries_deriv_at_zero`). -/
theorem intervalDomainCosineSlice_neumann_limit_left
    {b : ℕ → ℝ} {w : intervalDomainPoint → ℝ}
    (hb : Summable (fun n => unitIntervalCosineEigenvalue n * |b n|))
    (hagree : Set.EqOn (intervalDomainLift w)
        (fun x => ∑' n, b n * cosineMode n x) (Set.Icc (0 : ℝ) 1)) :
    Filter.Tendsto (deriv (intervalDomainLift w))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hcont : Continuous (deriv (fun x => ∑' n, b n * cosineMode n x)) :=
    (cosineCoeffSeries_contDiff_two hb).continuous_deriv (by norm_num)
  have htend : Filter.Tendsto (deriv (fun x => ∑' n, b n * cosineMode n x))
      (nhds 0) (nhds 0) := by
    have := hcont.continuousAt (x := (0 : ℝ)) |>.tendsto
    rwa [cosineCoeffSeries_deriv_at_zero hb] at this
  exact Filter.Tendsto.congr' (deriv_lift_eventuallyEq_cosineSeries_left hagree).symm
    (htend.mono_left nhdsWithin_le_nhds)

/-- **Conjunct-(6) bridge, right endpoint.**  Symmetric: `deriv(lift w) → 0` as
`x → 1⁻` (`cosineCoeffSeries_deriv_at_one`). -/
theorem intervalDomainCosineSlice_neumann_limit_right
    {b : ℕ → ℝ} {w : intervalDomainPoint → ℝ}
    (hb : Summable (fun n => unitIntervalCosineEigenvalue n * |b n|))
    (hagree : Set.EqOn (intervalDomainLift w)
        (fun x => ∑' n, b n * cosineMode n x) (Set.Icc (0 : ℝ) 1)) :
    Filter.Tendsto (deriv (intervalDomainLift w))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by
  have hcont : Continuous (deriv (fun x => ∑' n, b n * cosineMode n x)) :=
    (cosineCoeffSeries_contDiff_two hb).continuous_deriv (by norm_num)
  have htend : Filter.Tendsto (deriv (fun x => ∑' n, b n * cosineMode n x))
      (nhds 1) (nhds 0) := by
    have := hcont.continuousAt (x := (1 : ℝ)) |>.tendsto
    rwa [cosineCoeffSeries_deriv_at_one hb] at this
  exact Filter.Tendsto.congr' (deriv_lift_eventuallyEq_cosineSeries_right hagree).symm
    (htend.mono_left nhdsWithin_le_nhds)

end ShenWork.IntervalCosineSliceRegularity
