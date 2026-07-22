import ShenWork.Paper1.WholeLinePhysicalMildAppend

/-!
# Classical regularity of finite physical mild segments

Every positive interior time of a physical mild segment lies in a canonical
restart chart.  Classical regularity and the equations therefore transfer
from the canonical fixed point to the ambient segment.
-/

open Filter MeasureTheory Real Set Topology Function
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section

namespace ShenWork.Paper1
namespace WholeLinePhysicalMildSegment

/-- A positive interior point has a canonical classical chart, expressed in
the ambient time coordinate. -/
theorem exists_eventuallyEq_classical_chart
    {p : CMParams} {u₀ : WholeLineBUC} {T M t : ℝ}
    (d : WholeLinePhysicalMildSegment p u₀ T)
    (hM : 0 ≤ M)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (d.traj z).1 x ∈ Set.Icc (0 : ℝ) M)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ∃ a h q : ℝ, ∃ hh : 0 < h, ∃ Canon : WholeLineBUCTrajectory h,
      0 < q ∧ q < h ∧ t = a + q ∧
      IsClassicalSolution p h
        (fun s x => (wholeLineBUCTrajectoryExtend hh.le Canon s).1 x)
        (fun s => frozenElliptic p
          (fun x => (wholeLineBUCTrajectoryExtend hh.le Canon s).1 x)) ∧
      (fun s => d.extend s) =ᶠ[nhds t]
        (fun s => wholeLineBUCTrajectoryExtend hh.le Canon (s - a)) := by
  have hfixed := d.isFixedPt hM hstrip
  rcases wholeLinePhysicalFixedPoint_exists_canonical_chart
      p hM d.T_pos u₀ d.traj hfixed hstrip t ht with
    ⟨a, h, q, ha, hh, hq, hah, htime, hsmall, hchart⟩
  let za : Set.Icc (0 : ℝ) T :=
    ⟨a, ha.le, (le_add_of_nonneg_right hh.le).trans hah⟩
  let datum : WholeLineBUC := d.traj za
  let Canon : WholeLineBUCTrajectory h :=
    wholeLineCauchyBUCMildFixedPoint p hM hh.le datum hsmall
  have hstripCanon : ∀ z : Set.Icc (0 : ℝ) h, ∀ x,
      (Canon z).1 x ∈ Set.Icc (0 : ℝ) M := by
    intro z x
    have happ := congrArg (fun Q : WholeLineBUCTrajectory h => Q z) hchart
    have hzT : a + z.1 ∈ Set.Icc (0 : ℝ) T :=
      ⟨add_nonneg ha.le z.2.1, by linarith [z.2.2, hah]⟩
    have heq : Canon z = d.traj ⟨a + z.1, hzT⟩ := by
      simpa [Canon, datum, za, wholeLineBUCTrajectoryShift] using happ.symm
    rw [heq]
    exact hstrip ⟨a + z.1, hzT⟩ x
  have hclass : IsClassicalSolution p h
      (fun s x => (wholeLineBUCTrajectoryExtend hh.le Canon s).1 x)
      (fun s => frozenElliptic p
        (fun x => (wholeLineBUCTrajectoryExtend hh.le Canon s).1 x)) := by
    simpa [Canon] using
      (wholeLineCauchyBUCMildFixedPoint_isClassicalSolution
        p (M := M) (T := h) (theta := (1 / 2 : ℝ))
        (eta := (1 / 4 : ℝ)) hM hh datum hsmall
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by simpa [Canon] using hstripCanon))
  have hev : (fun s => d.extend s) =ᶠ[nhds t]
      (fun s => wholeLineBUCTrajectoryExtend hh.le Canon (s - a)) := by
    have htmem : t ∈ Set.Ioo a (a + h) := by
      rw [htime]
      exact ⟨by linarith [hq.1], by linarith [hq.2]⟩
    filter_upwards [isOpen_Ioo.mem_nhds htmem] with s hs
    have hr : s - a ∈ Set.Icc (0 : ℝ) h :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hsT : s ∈ Set.Icc (0 : ℝ) T :=
      ⟨by linarith [ha, hs.1], by linarith [hs.2, hah]⟩
    rw [extend, wholeLineBUCTrajectoryExtend_eq d.T_pos.le d.traj hsT,
      wholeLineBUCTrajectoryExtend_eq hh.le Canon hr]
    have happ := congrArg
      (fun Q : WholeLineBUCTrajectory h => Q ⟨s - a, hr⟩) hchart
    simpa [Canon, datum, za, wholeLineBUCTrajectoryShift] using happ
  exact ⟨a, h, q, hh, Canon, hq.1, hq.2, htime, hclass, hev⟩

/-- Every finite physical mild segment is a classical solution on its open
time slab. -/
theorem isClassicalSolution
    {p : CMParams} {u₀ : WholeLineBUC} {T : ℝ}
    (d : WholeLinePhysicalMildSegment p u₀ T) :
    IsClassicalSolution p T d.population
      (fun t => frozenElliptic p (d.population t)) := by
  obtain ⟨M, hM, hstrip⟩ := d.exists_physical_clamp
  refine
    { hT := d.T_pos
      u_smooth := ?_
      v_smooth := ?_
      pde_u := ?_
      pde_v := ?_ }
  · intro t x ht0 htT
    rcases d.exists_eventuallyEq_classical_chart hM hstrip ⟨ht0, htT⟩ with
      ⟨a, h, q, hh, Canon, hq0, hqh, htime, hclass, hev⟩
    let ul : ℝ → ℝ → ℝ := fun s y =>
      (wholeLineBUCTrajectoryExtend hclass.hT.le Canon s).1 y
    have hevx : (fun s => d.population s x) =ᶠ[nhds t]
        (fun s => ul (s - a) x) := by
      exact hev.fun_comp (fun w : WholeLineBUC => w.1 x)
    constructor
    · apply (hevx.differentiableAt_iff).2
      apply (differentiableAt_comp_sub_const
        (f := fun s => ul s x) (a := t) (b := a)).2
      have htq : t - a = q := by rw [htime]; ring
      simpa [htq, ul] using (hclass.u_smooth q x hq0 hqh).1
    · have hslice : d.population t = ul q := by
        funext y
        have hy := (hev.fun_comp (fun w : WholeLineBUC => w.1 y)).eq_of_nhds
        simpa [population, ul, htime] using hy
      rw [hslice]
      exact (hclass.u_smooth q x hq0 hqh).2
  · intro t x ht0 htT
    rcases d.exists_eventuallyEq_classical_chart hM hstrip ⟨ht0, htT⟩ with
      ⟨a, h, q, hh, Canon, hq0, hqh, htime, hclass, hev⟩
    let ul : ℝ → ℝ → ℝ := fun s y =>
      (wholeLineBUCTrajectoryExtend hclass.hT.le Canon s).1 y
    let vl : ℝ → ℝ → ℝ := fun s => frozenElliptic p (ul s)
    have hslice : d.population t = ul q := by
      funext y
      have hy := (hev.fun_comp (fun w : WholeLineBUC => w.1 y)).eq_of_nhds
      simpa [population, ul, htime] using hy
    change DifferentiableAt ℝ (frozenElliptic p (d.population t)) x
    rw [hslice]
    exact hclass.v_smooth q x hq0 hqh
  · intro t x ht0 htT
    rcases d.exists_eventuallyEq_classical_chart hM hstrip ⟨ht0, htT⟩ with
      ⟨a, h, q, hh, Canon, hq0, hqh, htime, hclass, hev⟩
    let ul : ℝ → ℝ → ℝ := fun s y =>
      (wholeLineBUCTrajectoryExtend hclass.hT.le Canon s).1 y
    let vl : ℝ → ℝ → ℝ := fun s => frozenElliptic p (ul s)
    have hevx : (fun s => d.population s x) =ᶠ[nhds t]
        (fun s => ul (s - a) x) :=
      hev.fun_comp (fun w : WholeLineBUC => w.1 x)
    have htimeDeriv : deriv (fun s => d.population s x) t =
        deriv (fun s => ul s x) q := by
      calc
        deriv (fun s => d.population s x) t =
            deriv (fun s => ul (s - a) x) t := hevx.deriv_eq
        _ = deriv (fun s => ul s x) (t - a) :=
          deriv_comp_sub_const (fun s => ul s x) a t
        _ = deriv (fun s => ul s x) q := by rw [htime]; ring_nf
    have hsliceU : d.population t = ul q := by
      funext y
      have hy := (hev.fun_comp (fun w : WholeLineBUC => w.1 y)).eq_of_nhds
      simpa [population, ul, htime] using hy
    rw [htimeDeriv, hsliceU]
    simpa [ul, vl] using hclass.pde_u q x hq0 hqh
  · intro t x ht0 htT
    rcases d.exists_eventuallyEq_classical_chart hM hstrip ⟨ht0, htT⟩ with
      ⟨a, h, q, hh, Canon, hq0, hqh, htime, hclass, hev⟩
    let ul : ℝ → ℝ → ℝ := fun s y =>
      (wholeLineBUCTrajectoryExtend hclass.hT.le Canon s).1 y
    let vl : ℝ → ℝ → ℝ := fun s => frozenElliptic p (ul s)
    have hsliceU : d.population t = ul q := by
      funext y
      have hy := (hev.fun_comp (fun w : WholeLineBUC => w.1 y)).eq_of_nhds
      simpa [population, ul, htime] using hy
    rw [hsliceU]
    simpa [ul, vl] using hclass.pde_v q x hq0 hqh

section AxiomAudit

#print axioms WholeLinePhysicalMildSegment.exists_eventuallyEq_classical_chart
#print axioms WholeLinePhysicalMildSegment.isClassicalSolution

end AxiomAudit

end WholeLinePhysicalMildSegment
end ShenWork.Paper1
