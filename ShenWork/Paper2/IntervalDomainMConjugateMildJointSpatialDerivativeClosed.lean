/-
  Closed-space joint continuity of the faithful mild spatial derivative.

  The positive-time Holder estimate is initially available only at interior
  spatial points.  Genuine one-sided Neumann limits first glue the ordinary
  derivative continuously to its zero endpoint values.  Continuity then
  extends the common Holder estimate from the open interval to its closure,
  after which the parametric secant-slope bridge gives joint continuity.
-/
import ShenWork.Paper2.IntervalDomainMConjugateMildJointSpatialDerivative
import ShenWork.Paper2.IntervalDomainMConjugateMildClosedSpatial

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace ShenWork.Paper2

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit
  (ConjugateMildSolutionDataM)

/-- A Holder estimate on the open unit interval extends to the closed interval
when the function is continuous up to the boundary. -/
private theorem holderOn_Icc_of_continuousOn_of_holderOn_Ioo
    {g : ℝ → ℝ} {K theta : ℝ}
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) 1))
    (htheta : 0 < theta)
    (hholder : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      |g x - g y| ≤ K * |x - y| ^ theta) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |g x - g y| ≤ K * |x - y| ^ theta := by
  have hclosure : closure (Set.Ioo (0 : ℝ) 1) = Set.Icc (0 : ℝ) 1 :=
    closure_Ioo (by norm_num)
  have hfirst : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |g x - g y| ≤ K * |x - y| ^ theta := by
    intro x hx y hy
    have hlhs : ContinuousOn (fun z : ℝ ↦ |g x - g z|)
        (closure (Set.Ioo (0 : ℝ) 1)) := by
      rw [hclosure]
      exact (continuousOn_const.sub hg).abs
    have habs : Continuous (fun z : ℝ ↦ |x - z|) :=
      (continuous_const.sub continuous_id).abs
    have hrhs : ContinuousOn (fun z : ℝ ↦ K * |x - z| ^ theta)
        (closure (Set.Ioo (0 : ℝ) 1)) :=
      (continuous_const.mul
        (habs.rpow_const (fun _ ↦ Or.inr htheta.le))).continuousOn
    apply le_on_closure (s := Set.Ioo (0 : ℝ) 1)
      (f := fun z : ℝ ↦ |g x - g z|)
      (g := fun z : ℝ ↦ K * |x - z| ^ theta)
      (fun z hz ↦ hholder x hx z hz) hlhs hrhs
    simpa [hclosure] using hy
  intro x hx y hy
  have hlhs : ContinuousOn (fun z : ℝ ↦ |g z - g y|)
      (closure (Set.Ioo (0 : ℝ) 1)) := by
    rw [hclosure]
    exact (hg.sub continuousOn_const).abs
  have habs : Continuous (fun z : ℝ ↦ |z - y|) :=
    (continuous_id.sub continuous_const).abs
  have hrhs : ContinuousOn (fun z : ℝ ↦ K * |z - y| ^ theta)
      (closure (Set.Ioo (0 : ℝ) 1)) :=
    (continuous_const.mul
      (habs.rpow_const (fun _ ↦ Or.inr htheta.le))).continuousOn
  apply le_on_closure (s := Set.Ioo (0 : ℝ) 1)
    (f := fun z : ℝ ↦ |g z - g y|)
    (g := fun z : ℝ ↦ K * |z - y| ^ theta)
    (fun z hz ↦ hfirst z hz y hy) hlhs hrhs
  simpa [hclosure] using hx

/-- At every positive time, the ordinary derivative of the lifted faithful
mild slice is continuous on the closed physical interval.  Interior
continuity comes from spatial C2; the endpoint pieces use the genuine Neumann
limits and the ordinary zero-extension derivative values. -/
theorem conjugateMildM_intervalDomainLift_deriv_continuousOn_Icc
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    ContinuousOn (deriv (intervalDomainLift (D.u t)))
      (Set.Icc (0 : ℝ) 1) := by
  let U : ℝ → ℝ := intervalDomainLift (D.u t)
  have hC2 : ContDiffOn ℝ 2 U (Set.Ioo (0 : ℝ) 1) := by
    exact conjugateMildM_intervalDomainLift_contDiffOn_two_interior
      D hu₀ hu₀_meas ht htT
  obtain ⟨htend0, htend1⟩ :=
    conjugateMildM_intervalDomainLift_neumannLimits
      D hu₀ hu₀_meas ht htT
  have hend := conjugateMildM_intervalDomainLift_closedC2_endpointDerivs
    D hu₀ hu₀_meas ht htT
  have hbc0 : deriv U 0 = 0 := by
    simpa [U] using hend.2.1
  have hbc1 : deriv U 1 = 0 := by
    simpa [U] using hend.2.2
  have hinter : ContinuousOn (deriv U) (Set.Ioo (0 : ℝ) 1) :=
    hC2.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  intro x hx
  rcases eq_or_lt_of_le hx.1 with hx0 | hx0
  · subst x
    rw [ContinuousWithinAt]
    rw [hbc0, nhdsWithin_Icc_eq_nhdsGE (by norm_num : (0 : ℝ) < 1)]
    have hsplit :
        nhdsWithin (0 : ℝ) (Set.Ici 0) =
          nhdsWithin (0 : ℝ) (Set.Ioi 0) ⊔
            nhdsWithin (0 : ℝ) {(0 : ℝ)} := by
      rw [← nhdsWithin_union, Set.Ioi_union_left]
    rw [hsplit, Filter.tendsto_sup]
    refine ⟨htend0, ?_⟩
    rw [nhdsWithin_singleton]
    have hpure := tendsto_pure_nhds (deriv U) (0 : ℝ)
    rwa [hbc0] at hpure
  · rcases eq_or_lt_of_le hx.2 with hx1 | hx1
    · subst x
      rw [ContinuousWithinAt]
      rw [hbc1, nhdsWithin_Icc_eq_nhdsLE (by norm_num : (0 : ℝ) < 1)]
      have hsplit :
          nhdsWithin (1 : ℝ) (Set.Iic 1) =
            nhdsWithin (1 : ℝ) (Set.Iio 1) ⊔
              nhdsWithin (1 : ℝ) {(1 : ℝ)} := by
        rw [← nhdsWithin_union, Set.Iio_union_right]
      rw [hsplit, Filter.tendsto_sup]
      refine ⟨htend1, ?_⟩
      rw [nhdsWithin_singleton]
      have hpure := tendsto_pure_nhds (deriv U) (1 : ℝ)
      rwa [hbc1] at hpure
    · have hwithin : ContinuousWithinAt (deriv U)
          (Set.Ioo (0 : ℝ) 1) x := hinter x ⟨hx0, hx1⟩
      exact hwithin.mono_of_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds
          (IsOpen.mem_nhds isOpen_Ioo ⟨hx0, hx1⟩))

/-- The actual faithful mild spatial derivative has a common Holder modulus
on the closed spatial interval on every closed positive-time strip. -/
theorem conjugateMildM_intervalDomainLift_deriv_positiveTime_holder_uniform_closed
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {τ eta : ℝ} (hτ : 0 < τ) (heta0 : 0 < eta) (heta1 : eta < 1) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ t, τ ≤ t → t ≤ D.T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        |deriv (intervalDomainLift (D.u t)) x -
          deriv (intervalDomainLift (D.u t)) y| ≤ H * |x - y| ^ eta := by
  obtain ⟨H, hH, hholder⟩ :=
    conjugateMildM_intervalDomainLift_deriv_positiveTime_holder_uniform
      D hu₀ hu₀_meas hτ heta0 heta1
  refine ⟨H, hH, ?_⟩
  intro t ht htT
  apply holderOn_Icc_of_continuousOn_of_holderOn_Ioo
    (conjugateMildM_intervalDomainLift_deriv_continuousOn_Icc
      D hu₀ hu₀_meas (hτ.trans_le ht) htT)
    heta0
  exact hholder t ht htT

/-- The ordinary spatial derivative of the lifted faithful mild solution is
jointly continuous at strict positive times on the closed physical interval. -/
theorem conjugateMildM_jointSpatialDeriv_closed
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1)) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) ↦ deriv (intervalDomainLift (D.u t)) x))
      (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1) := by
  apply parametricSpatialDeriv_jointContinuousOn_Ioo_of_positiveStripHolder
    (theta := (1 : ℝ) / 4) (by norm_num)
  · exact conjugateMildM_jointValue_u D hu₀_bound hu₀_meas
  · intro t ht x hx
    exact (conjugateMildM_intervalDomainLift_hasDerivAt_interior
      D hu₀_bound hu₀_meas
        (θ := (1 : ℝ) / 4) (by norm_num) (by norm_num)
        ht.1 ht.2.le hx).differentiableAt.differentiableWithinAt
  · intro tau htau
    obtain ⟨H, hH, hholder⟩ :=
      conjugateMildM_intervalDomainLift_deriv_positiveTime_holder_uniform_closed
        D hu₀_bound hu₀_meas
          (τ := tau) (eta := (1 : ℝ) / 4)
          htau (by norm_num) (by norm_num)
    refine ⟨H, hH, ?_⟩
    intro t ht x hx y hy
    exact hholder t ht.1 ht.2 x hx y hy
  · intro t ht
    exact (conjugateMildM_intervalDomainLift_closedC2_endpointDerivs
      D hu₀_bound hu₀_meas ht.1 ht.2.le).2.1
  · intro t ht
    exact (conjugateMildM_intervalDomainLift_closedC2_endpointDerivs
      D hu₀_bound hu₀_meas ht.1 ht.2.le).2.2

end ShenWork.Paper2

#print axioms ShenWork.Paper2.conjugateMildM_intervalDomainLift_deriv_continuousOn_Icc
#print axioms ShenWork.Paper2.conjugateMildM_intervalDomainLift_deriv_positiveTime_holder_uniform_closed
#print axioms ShenWork.Paper2.conjugateMildM_jointSpatialDeriv_closed
