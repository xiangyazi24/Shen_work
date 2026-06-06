/-
  B2 (MinPersistence): nonnegative second derivative at an interior argmin.

  Second-derivative test (Phase A) packaged for the classical-solution `C²`
  slice: at an interior spatial argmin `x*` of `u(t,·)`, the lift's second
  derivative is `≥ 0`.  This is the `huxx` input of
  `min_point_estimate_interior`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainInteriorArgmin
import ShenWork.Paper2.IntervalDomainC2Extraction
import ShenWork.Paper2.IntervalDomainMinPersistenceAtoms

open ShenWork.IntervalDomain Topology

noncomputable section

namespace ShenWork.MinPersistenceAtoms

/-- **Nonnegative second derivative at an interior argmin.**  If `x*` is a
spatial argmin of `u` in the open interior and the lift is `C²` there, then
`0 ≤ (lift u)''(x*)`. -/
theorem interior_argmin_deriv2_nonneg
    {u : intervalDomainPoint → ℝ} {x : intervalDomainPoint}
    (hmin : ∀ y, u x ≤ u y) (hint : x.1 ∈ Set.Ioo (0:ℝ) 1)
    (hu_c2 : ContDiffOn ℝ 2 (intervalDomainLift u) (Set.Ioo (0:ℝ) 1)) :
    0 ≤ deriv (deriv (intervalDomainLift u)) x.1 := by
  have hlm := intervalDomainLift_isLocalMin_of_argmin hmin hint
  have hdiff_ev : ∀ᶠ y in nhds x.1, DifferentiableAt ℝ (intervalDomainLift u) y := by
    filter_upwards [isOpen_Ioo.mem_nhds hint] with y hy
    exact (hu_c2.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hy)
  have hf'' := (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hu_c2 hint).2
  exact deriv2_nonneg_of_isLocalMin hlm hdiff_ev hf''

end ShenWork.MinPersistenceAtoms
