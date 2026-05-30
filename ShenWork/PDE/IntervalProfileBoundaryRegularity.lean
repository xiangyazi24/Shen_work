/-
  ShenWork/PDE/IntervalProfileBoundaryRegularity.lean

  **T5 — abstract `C²`-up-to-boundary profile regularity package.**

  The full-Neumann-kernel boundary-regularity arguments depend only on three facts
  about the spatial profile `S : ℝ → ℝ` a solution slice agrees with on `[0,1]`:

  * `S` is `ContDiff ℝ 2` (globally — the cosine spectral heat value is entire);
  * `deriv S 0 = 0` and `deriv S 1 = 0` (the Neumann property of the profile);
  * `lift (slice) = S` on the closed `[0,1]`.

  This file isolates that abstraction: the entire `C^{2,1}`-up-to-boundary
  regularity package (closed `C²`, up-to-boundary `C¹` continuity, interior
  right-`HasDerivWithinAt` data, interval-integrability of the first and second
  derivatives) is proved once for any such profile `S`.  Both the homogeneous
  semigroup (`S = S_t f`) and the Duhamel term (`S = Σ bₙ cos(nπ·)`, a cosine
  heat value) are instances — so this discharges the regularity package for the
  *full* full-kernel solution `u t = S_t u₀ + D_t` once it is represented by a
  bounded-coefficient cosine heat value on `[0,1]`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalFullKernelBoundaryRegularity

open MeasureTheory Set
open scoped Topology

namespace ShenWork.IntervalFullKernelRegularity

open ShenWork.IntervalDomain

/-- **Closed-boundary upgrade of an interior agreement (density bridge).**  Two
functions that agree on the open interior `(0,1)` and are *continuous on the
closed* `[0,1]` agree on all of `[0,1]`, including the endpoints.  The interior
`(0,1)` is dense in `[0,1]` (its closure is `[0,1]`), so the agreement extends to
the closure by `Set.EqOn.of_subset_closure`.  This converts the open-interior
heat-value representation (`DuhamelHeatValueRepresentation`, stated on `Ioo`) into
the closed-`Icc` agreement that the Neumann IBP / energy machinery consumes,
*provided* closed-`[0,1]` continuity is available (which conjunct (7)'s
`ContDiffOn ℝ 2 _ (Icc 0 1)` supplies). -/
theorem eqOn_Icc_of_eqOn_Ioo_of_continuousOn
    {f S : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hS : ContinuousOn S (Set.Icc (0 : ℝ) 1))
    (h : Set.EqOn f S (Set.Ioo (0 : ℝ) 1)) :
    Set.EqOn f S (Set.Icc (0 : ℝ) 1) := by
  refine Set.EqOn.of_subset_closure h hf hS Set.Ioo_subset_Icc_self ?_
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]

variable {S : ℝ → ℝ} {g : intervalDomainPoint → ℝ}

/-- Closed-`[0,1]` `C²` of a profile slice. -/
theorem intervalDomainLift_profile_contDiffOn_two_closed
    (hS : ContDiff ℝ 2 S)
    (hg : Set.EqOn (intervalDomainLift g) S (Set.Icc (0 : ℝ) 1)) :
    ContDiffOn ℝ 2 (intervalDomainLift g) (Set.Icc (0 : ℝ) 1) :=
  (hS.contDiffOn).congr hg

/-- On the open interior the first lift derivative agrees with `deriv S`. -/
theorem deriv_intervalDomainLift_profile_eqOn_Ioo
    (hg : Set.EqOn (intervalDomainLift g) S (Set.Icc (0 : ℝ) 1)) :
    Set.EqOn (deriv (intervalDomainLift g)) (deriv S) (Set.Ioo (0 : ℝ) 1) := by
  intro y hy
  have hev : intervalDomainLift g =ᶠ[𝓝 y] S :=
    Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hy)
      (fun z hz => hg ⟨le_of_lt hz.1, le_of_lt hz.2⟩)
  exact hev.deriv_eq

/-- Up-to-boundary `C¹` continuity of a Neumann profile slice's derivative. -/
theorem deriv_intervalDomainLift_profile_continuousOn_Icc
    (hS : ContDiff ℝ 2 S) (hS_d0 : deriv S 0 = 0) (hS_d1 : deriv S 1 = 0)
    (hg : Set.EqOn (intervalDomainLift g) S (Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (deriv (intervalDomainLift g)) (Set.Icc (0 : ℝ) 1) := by
  have hderiv_cont : Continuous (deriv S) := hS.continuous_deriv (by norm_num)
  have hEqD : Set.EqOn (deriv (intervalDomainLift g)) (deriv S) (Set.Icc (0 : ℝ) 1) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with hx0 | hx0
    · rw [← hx0, deriv_intervalDomainLift_eq_zero_at_zero, hS_d0]
    · rcases eq_or_lt_of_le hx.2 with hx1 | hx1
      · rw [hx1, deriv_intervalDomainLift_eq_zero_at_one, hS_d1]
      · exact deriv_intervalDomainLift_profile_eqOn_Ioo hg ⟨hx0, hx1⟩
  exact (hderiv_cont.continuousOn).congr hEqD

/-- Closed-`[0,1]` continuity of the lift itself. -/
theorem intervalDomainLift_profile_continuousOn_Icc
    (hS : ContDiff ℝ 2 S)
    (hg : Set.EqOn (intervalDomainLift g) S (Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (intervalDomainLift g) (Set.Icc (0 : ℝ) 1) :=
  (intervalDomainLift_profile_contDiffOn_two_closed hS hg).continuousOn

/-- Interior right-`HasDerivWithinAt` of the lift. -/
theorem intervalDomainLift_profile_hasDerivWithinAt_Ioi
    (hS : ContDiff ℝ 2 S)
    (hg : Set.EqOn (intervalDomainLift g) S (Set.Icc (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivWithinAt (intervalDomainLift g)
      (deriv (intervalDomainLift g) x) (Set.Ioi x) x := by
  have hev : intervalDomainLift g =ᶠ[𝓝 x] S :=
    Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hx)
      (fun z hz => hg ⟨le_of_lt hz.1, le_of_lt hz.2⟩)
  have hdiff : DifferentiableAt ℝ (intervalDomainLift g) x :=
    (hS.differentiable (by norm_num)).differentiableAt.congr_of_eventuallyEq hev
  exact hdiff.hasDerivAt.hasDerivWithinAt

/-- Interior right-`HasDerivWithinAt` of the first derivative. -/
theorem deriv_intervalDomainLift_profile_hasDerivWithinAt_Ioi
    (hS : ContDiff ℝ 2 S)
    (hg : Set.EqOn (intervalDomainLift g) S (Set.Icc (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivWithinAt (deriv (intervalDomainLift g))
      (deriv (deriv (intervalDomainLift g)) x) (Set.Ioi x) x := by
  have hevD : deriv (intervalDomainLift g) =ᶠ[𝓝 x] deriv S :=
    Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hx)
      (fun z hz => deriv_intervalDomainLift_profile_eqOn_Ioo hg hz)
  have hdiff : DifferentiableAt ℝ (deriv (intervalDomainLift g)) x :=
    ((hS.deriv' (n := 1)).differentiable (by norm_num)).differentiableAt.congr_of_eventuallyEq hevD
  exact hdiff.hasDerivAt.hasDerivWithinAt

/-- First lift derivative is interval-integrable on `[0,1]`. -/
theorem intervalIntegrable_deriv_intervalDomainLift_profile
    (hS : ContDiff ℝ 2 S) (hS_d0 : deriv S 0 = 0) (hS_d1 : deriv S 1 = 0)
    (hg : Set.EqOn (intervalDomainLift g) S (Set.Icc (0 : ℝ) 1)) :
    IntervalIntegrable (deriv (intervalDomainLift g)) MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (zero_le_one)]
  exact deriv_intervalDomainLift_profile_continuousOn_Icc hS hS_d0 hS_d1 hg

/-- Second lift derivative is interval-integrable on `[0,1]`. -/
theorem intervalIntegrable_deriv2_intervalDomainLift_profile
    (hS : ContDiff ℝ 2 S)
    (hg : Set.EqOn (intervalDomainLift g) S (Set.Icc (0 : ℝ) 1)) :
    IntervalIntegrable (deriv (deriv (intervalDomainLift g))) MeasureTheory.volume 0 1 := by
  have hd2S_cont : Continuous (deriv (deriv S)) :=
    (hS.deriv' (n := 1)).continuous_deriv (by norm_num)
  have hd2S_int : IntervalIntegrable (deriv (deriv S)) MeasureTheory.volume 0 1 :=
    hd2S_cont.intervalIntegrable 0 1
  have hEq2 : Set.EqOn (deriv (deriv (intervalDomainLift g))) (deriv (deriv S))
      (Set.Ioo (0 : ℝ) 1) := by
    intro y hy
    have hevD : deriv (intervalDomainLift g) =ᶠ[𝓝 y] deriv S :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hy)
        (fun z hz => deriv_intervalDomainLift_profile_eqOn_Ioo hg hz)
    exact hevD.deriv_eq
  have hae : deriv (deriv (intervalDomainLift g))
      =ᵐ[MeasureTheory.volume.restrict (Set.uIoc 0 1)] deriv (deriv S) := by
    rw [Set.uIoc_of_le (zero_le_one)]
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_
    have hne1 : ∀ᵐ y ∂MeasureTheory.volume, y ≠ (1 : ℝ) := by
      have heq : {y : ℝ | ¬ y ≠ 1} = {(1 : ℝ)} := by ext y; simp [eq_comm]
      rw [MeasureTheory.ae_iff, heq]; exact Real.volume_singleton
    filter_upwards [hne1] with y hyne hyIoc
    exact hEq2 ⟨hyIoc.1, lt_of_le_of_ne hyIoc.2 hyne⟩
  exact hd2S_int.congr_ae hae.symm

end ShenWork.IntervalFullKernelRegularity
