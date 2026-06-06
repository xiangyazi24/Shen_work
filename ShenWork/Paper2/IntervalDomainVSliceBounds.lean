/-
  B2/B4 (MinPersistence): the chemical v-slice coefficient bounds.

  Instantiates `elliptic_coeff_bounds` (B4) for the chemical concentration
  slice `v(t)` of a classical solution, with `Src = ν·u^γ`, `B = ν·M'^γ`,
  producing the slab-independent derivative bounds
    `|v_x| ≤ 2νM'^γ`,   `|v_xx| ≤ 2νM'^γ`   on the open interior,
  which are the `hvx_bd`/`hvxx_bd` inputs of `min_point_estimate_interior`.

  The classical-solution conjunct projections (`C²`, elliptic identity from
  `pde_v`, Neumann endpoints, `v ≥ 0`, the `u`-sup bound) are taken as clean
  hypotheses; the 9-tuple / subtype projection from `IsPaper2ClassicalSolution`
  is the capstone wrapper.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainEllipticCoeffBounds
import ShenWork.Paper2.IntervalDomainPowerSourceBound
import ShenWork.Paper2.IntervalDomainC2Extraction
import ShenWork.PDE.IntervalDomain

open ShenWork.IntervalDomain Filter Topology

noncomputable section

namespace ShenWork.MinPersistenceAtoms

/-- **Chemical v-slice coefficient bounds.**  From the `C²` / elliptic-identity
/ Neumann / nonnegativity facts of a classical chemical slice `v` (source
`ν·u^γ`, `0 ≤ u ≤ M'`), the resolver derivative bounds `|v_x|, |v_xx| ≤ 2νM'^γ`
on the open interior. -/
theorem v_slice_coeff_bounds
    {p : CM2Params} {u v : intervalDomainPoint → ℝ} {M' : ℝ}
    (hM' : 0 ≤ M')
    (hv_c2 : ContDiffOn ℝ 2 (intervalDomainLift v) (Set.Ioo (0:ℝ) 1))
    (hv_cont : ContinuousOn (intervalDomainLift v) (Set.Icc (0:ℝ) 1))
    (hv_nonneg : ∀ y, 0 ≤ intervalDomainLift v y)
    (hu_nonneg : ∀ y ∈ Set.Ioo (0:ℝ) 1, 0 ≤ intervalDomainLift u y)
    (hu_le : ∀ y ∈ Set.Ioo (0:ℝ) 1, intervalDomainLift u y ≤ M')
    (hPDE : ∀ y ∈ Set.Ioo (0:ℝ) 1, deriv (deriv (intervalDomainLift v)) y
        = p.μ * intervalDomainLift v y - p.ν * (intervalDomainLift u y) ^ p.γ)
    (hNeu0 : Tendsto (deriv (intervalDomainLift v)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hNeu1 : Tendsto (deriv (intervalDomainLift v)) (nhdsWithin 1 (Set.Iio 1)) (nhds 0)) :
    (∀ y ∈ Set.Ioo (0:ℝ) 1, |deriv (intervalDomainLift v) y| ≤ 2 * (p.ν * M' ^ p.γ)) ∧
      (∀ y ∈ Set.Ioo (0:ℝ) 1,
        |deriv (deriv (intervalDomainLift v)) y| ≤ 2 * (p.ν * M' ^ p.γ)) := by
  set B : ℝ := p.ν * M' ^ p.γ with hB_def
  have hB_nonneg : 0 ≤ B := by
    rw [hB_def]; exact mul_nonneg p.hν.le (Real.rpow_nonneg hM' _)
  -- Differentiability data from `C²`.
  have hd1 : ∀ y ∈ Set.Ioo (0:ℝ) 1, DifferentiableAt ℝ (intervalDomainLift v) y :=
    fun y hy => (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hv_c2 hy).1.differentiableAt
  have hd2 : ∀ y ∈ Set.Ioo (0:ℝ) 1,
      DifferentiableAt ℝ (deriv (intervalDomainLift v)) y :=
    fun y hy => (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hv_c2 hy).2.differentiableAt
  have hdv1 : ContDiffOn ℝ 1 (deriv (intervalDomainLift v)) (Set.Ioo (0:ℝ) 1) :=
    hv_c2.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hdv0 : ContDiffOn ℝ 0 (deriv (deriv (intervalDomainLift v))) (Set.Ioo (0:ℝ) 1) :=
    hdv1.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hd2c : ContinuousOn (deriv (deriv (intervalDomainLift v))) (Set.Ioo (0:ℝ) 1) :=
    hdv0.continuousOn
  -- Source bound `|ν·u^γ| ≤ B`.
  have hSrc : ∀ y ∈ Set.Ioo (0:ℝ) 1,
      |p.ν * (intervalDomainLift u y) ^ p.γ| ≤ B :=
    fun y hy => power_source_abs_le p.hν.le p.hγ.le (hu_nonneg y hy) (hu_le y hy)
  -- Apply the B4 atom.
  have hbounds := elliptic_coeff_bounds (w := intervalDomainLift v)
    (Src := fun y => p.ν * (intervalDomainLift u y) ^ p.γ) (μ := p.μ) (B := B)
    p.hμ hB_nonneg hv_cont hd1 hd2 hd2c hPDE hSrc (fun y _ => hv_nonneg y) hNeu0 hNeu1
  exact ⟨hbounds.2.1, hbounds.2.2⟩

end ShenWork.MinPersistenceAtoms
