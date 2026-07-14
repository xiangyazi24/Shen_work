import ShenWork.PDE.IntervalSemigroupHolderFamilyApprox
import ShenWork.Paper2.IntervalDomainMConjugateMildInitialTrace
import ShenWork.Paper3.IntervalDomainGlobalTailHolderM

/-!
# Uniform time modulus on bounded faithful general-power orbit tails

The window-specific positive floor is used only to justify each mild restart.
All quantitative constants depend on the common tail ceiling, so the resulting
time modulus is uniform over every sufficiently late restart time.
-/

namespace ShenWork.Paper3

open Filter Set Topology MeasureTheory
open ShenWork.IntervalDomain ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainMConjugateDuhamelMap
open ShenWork.Paper2.IntervalDomainMConjugateMapBounds
open ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit
open ShenWork.IntervalConjugateDuhamelMap
open ShenWork.IntervalGradientDuhamelMap
open ShenWork.IntervalNeumannFullKernel

noncomputable section

/-- A bounded faithful global orbit has a common right-time modulus on a
positive-time tail.  This is the time component of translated-orbit Ascoli. -/
theorem intervalDomainM_globalBounded_eventual_right_time_equi
    (p : CM2Params)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v) :
    ∃ T > 0, ∀ ε > 0, ∃ δ > 0,
      ∀ a r, T ≤ a → 0 < r → r < δ →
        ∀ x : intervalDomainPoint, |u (a + r) x - u a x| < ε := by
  obtain ⟨T, M, G, hT, hM, hG, hsup, hholder⟩ :=
    intervalDomainM_globalBounded_eventual_holder p huv
  let I : Type := {a : ℝ // T ≤ a}
  let f : I → ℝ → ℝ := fun a => intervalDomainLift (u a.1)
  have hf : ∀ a : I, ContinuousOn (f a) (Icc (0 : ℝ) 1) := by
    intro a
    have ha0 : 0 < a.1 := lt_of_lt_of_le hT a.2
    have hsol := huv.classical (a.1 + 1) (by linarith)
    simpa [f] using
      solution_lift_continuousOn_Icc hsol
        (show a.1 ∈ Ioo (0 : ℝ) (a.1 + 1) by constructor <;> linarith)
  have hfholder : ∀ a : I, ∀ x, x ∈ Icc (0 : ℝ) 1 →
      ∀ y, y ∈ Icc (0 : ℝ) 1 →
        |f a y - f a x| ≤ G * Real.sqrt |y - x| := by
    intro a x hx y hy
    have hxy := hholder a.1 a.2
      (⟨y, hy⟩ : intervalDomainPoint) (⟨x, hx⟩ : intervalDomainPoint)
    simpa [f, intervalDomainLift, hx, hy, Real.sqrt_eq_rpow] using hxy
  refine ⟨T, hT, ?_⟩
  intro ε hε
  have hsem_ev :=
    ShenWork.IntervalSemigroupHolderFamilyApprox.intervalFullSemigroup_eventually_uniform_family_of_holder
      f G hf hfholder (ε / 2) (by linarith)
  have hsem_mem :
      {r : ℝ | ∀ a : I, ∀ x, x ∈ Icc (0 : ℝ) 1 →
        dist (intervalFullSemigroupOperator r (f a) x) (f a x) < ε / 2}
        ∈ 𝓝[>] (0 : ℝ) := by
    exact hsem_ev
  obtain ⟨δS, hδS, hδSsub⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp hsem_mem
  let CQ : ℝ := chemFluxMSupConstant p M
  have hCQ : 0 ≤ CQ := chemFluxMSupConstant_nonneg p hM.le
  let CL : ℝ := M * (p.a + p.b * M ^ p.α)
  have hCL : 0 ≤ CL := by
    dsimp [CL]
    exact mul_nonneg hM.le
      (add_nonneg p.ha (mul_nonneg p.hb (Real.rpow_nonneg hM.le _)))
  let A : ℝ := 2 * |p.χ₀| *
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant * CQ
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (abs_nonneg p.χ₀))
        ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg)
      hCQ
  obtain ⟨δD, hδD, hDsmall⟩ :=
    exists_small_contraction_time_target hA hCL (show 0 < ε / 2 by linarith)
  refine ⟨min δS δD, lt_min hδS hδD, ?_⟩
  intro a r ha hr hrδ x
  have hrS : r < δS := lt_of_lt_of_le hrδ (min_le_left _ _)
  have hrD : r < δD := lt_of_lt_of_le hrδ (min_le_right _ _)
  have hsem := hδSsub ⟨hr, hrS⟩ (⟨a, ha⟩ : I) x.1 x.2
  have hsem_abs :
      |intervalFullSemigroupOperator r (intervalDomainLift (u a)) x.1 -
        u a x| < ε / 2 := by
    simpa [f, Real.dist_eq, intervalDomainLift, x.2] using hsem
  have hub : ∀ t, a ≤ t → intervalDomainM.supNorm (u t) ≤ M := by
    intro t hat
    exact hsup t (ha.trans hat)
  obtain ⟨D, hDT, hDM, hDu⟩ :=
    intervalDomainM_tailRestartMildData_exists p huv.classical
      (lt_of_lt_of_le hT ha) hr hM hub
  have hrT : r ≤ D.T := by rw [hDT]
  have hbound_r : ∀ s, 0 < s → s ≤ r → ∀ y, |D.u s y| ≤ D.M := by
    intro s hs hsr
    exact D.hbound s hs (hsr.trans hrT)
  have hfloor_r : ∀ s, 0 < s → s ≤ r → ∀ y, D.c ≤ D.u s y := by
    intro s hs hsr
    exact D.hfloor s hs (hsr.trans hrT)
  have hcont_r : ShenWork.IntervalMildPicard.HasContinuousSlices r D.u := by
    intro s hs hsr
    exact D.hcont s hs (hsr.trans hrT)
  have hQbound : ∀ s, 0 < s → s ≤ r → ∀ y,
      |chemFluxMLifted p (D.u s) y| ≤ CQ := by
    intro s hs hsr y
    have hraw := chemFluxMLifted_abs_le_of_pos_slice
      p D.hc D.floor_le_bound (hbound_r s hs hsr)
        (hfloor_r s hs hsr) (hcont_r s hs hsr) y
    simpa [CQ, chemFluxMSupConstant, hDM] using hraw
  have hLbound : ∀ s, 0 < s → s ≤ r → ∀ y,
      |logisticLifted p (D.u s) y| ≤ CL := by
    intro s hs hsr y
    have hraw :=
      ShenWork.IntervalDomainExistence.intervalLogisticSource_lift_abs_bound
        p D.hM (hbound_r s hs hsr) y
    simpa [CL, hDM] using hraw
  have hchem :
      |∫ s in (0 : ℝ)..r,
        intervalConjugateKernelOperator (r - s)
          (chemFluxMLifted p (D.u s)) x.1| ≤
        ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
          (2 * Real.sqrt r) * CQ :=
    conjugateMDuhamel_sup_bound_of_positive_cone_univ
      p D.hc D.floor_le_bound hCQ hbound_r hfloor_r hcont_r hQbound
        hr le_rfl x
  have hval :
      |∫ s in (0 : ℝ)..r,
        intervalFullSemigroupOperator (r - s)
          (logisticLifted p (D.u s)) x.1| ≤ r * CL :=
    ShenWork.IntervalConjugateBallSupBound.valueDuhamel_sup_bound_of_ball
      p D.hM hCL hbound_r hLbound hr le_rfl x
  have hcorr :
      |(-p.χ₀) * (∫ s in (0 : ℝ)..r,
          intervalConjugateKernelOperator (r - s)
            (chemFluxMLifted p (D.u s)) x.1) +
        ∫ s in (0 : ℝ)..r,
          intervalFullSemigroupOperator (r - s)
            (logisticLifted p (D.u s)) x.1| ≤
        A * Real.sqrt r + CL * r := by
    calc
      _ ≤ |(-p.χ₀) * (∫ s in (0 : ℝ)..r,
            intervalConjugateKernelOperator (r - s)
              (chemFluxMLifted p (D.u s)) x.1)| +
          |∫ s in (0 : ℝ)..r,
            intervalFullSemigroupOperator (r - s)
              (logisticLifted p (D.u s)) x.1| := abs_add_le _ _
      _ ≤ |p.χ₀| *
            (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
              (2 * Real.sqrt r) * CQ) + r * CL := by
        simpa [abs_mul, abs_neg] using
          add_le_add (mul_le_mul_of_nonneg_left hchem (abs_nonneg p.χ₀)) hval
      _ = A * Real.sqrt r + CL * r := by
        dsimp [A]
        ring
  have hcorr_small : A * Real.sqrt r + CL * r < ε / 2 := by
    have hsqrt : Real.sqrt r ≤ Real.sqrt δD := Real.sqrt_le_sqrt hrD.le
    have hA' := mul_le_mul_of_nonneg_left hsqrt hA
    have hL' := mul_le_mul_of_nonneg_left hrD.le hCL
    linarith
  have hslice : D.u r x = u (a + r) x := by
    rw [hDu, classicalRestartTrajectoryM_eq
      (show r ∈ Icc (0 : ℝ) r by exact ⟨hr.le, le_rfl⟩)]
  rw [← hslice, D.hmild r hr hrT x]
  unfold intervalConjugateDuhamelMapM
  calc
    |intervalFullSemigroupOperator r (intervalDomainLift (u a)) x.1 +
          (-p.χ₀) * (∫ s in (0 : ℝ)..r,
            intervalConjugateKernelOperator (r - s)
              (chemFluxMLifted p (D.u s)) x.1) +
          (∫ s in (0 : ℝ)..r,
            intervalFullSemigroupOperator (r - s)
              (logisticLifted p (D.u s)) x.1) - u a x| =
        |(intervalFullSemigroupOperator r (intervalDomainLift (u a)) x.1 -
            u a x) +
          ((-p.χ₀) * (∫ s in (0 : ℝ)..r,
            intervalConjugateKernelOperator (r - s)
              (chemFluxMLifted p (D.u s)) x.1) +
          ∫ s in (0 : ℝ)..r,
            intervalFullSemigroupOperator (r - s)
              (logisticLifted p (D.u s)) x.1)| := by
        congr 1
        ring
    _ ≤ |intervalFullSemigroupOperator r (intervalDomainLift (u a)) x.1 -
          u a x| +
        |(-p.χ₀) * (∫ s in (0 : ℝ)..r,
            intervalConjugateKernelOperator (r - s)
              (chemFluxMLifted p (D.u s)) x.1) +
          ∫ s in (0 : ℝ)..r,
            intervalFullSemigroupOperator (r - s)
              (logisticLifted p (D.u s)) x.1| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hsem_abs (hcorr.trans_lt hcorr_small)
    _ = ε := by ring

/-- Symmetric two-time form of the tail modulus. -/
theorem intervalDomainM_globalBounded_eventual_time_equi
    (p : CM2Params)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v) :
    ∃ T > 0, ∀ ε > 0, ∃ δ > 0,
      ∀ s t, T ≤ s → T ≤ t → |t - s| < δ →
        ∀ x : intervalDomainPoint, |u t x - u s x| < ε := by
  obtain ⟨T, hT, hright⟩ :=
    intervalDomainM_globalBounded_eventual_right_time_equi p huv
  refine ⟨T, hT, ?_⟩
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := hright ε hε
  refine ⟨δ, hδ, ?_⟩
  intro s t hs ht hst x
  rcases lt_trichotomy s t with hlt | heq | hgt
  · have hr : 0 < t - s := sub_pos.mpr hlt
    have hraw := hmod s (t - s) hs hr (by simpa [abs_of_pos hr] using hst) x
    simpa [sub_add_cancel] using hraw
  · subst t
    simpa using hε
  · have hr : 0 < s - t := sub_pos.mpr hgt
    have hraw := hmod t (s - t) ht hr (by
      rw [abs_sub_comm, abs_of_pos hr] at hst
      exact hst) x
    simpa [sub_add_cancel, abs_sub_comm] using hraw

end


end ShenWork.Paper3

#print axioms
  ShenWork.Paper3.intervalDomainM_globalBounded_eventual_right_time_equi
#print axioms
  ShenWork.Paper3.intervalDomainM_globalBounded_eventual_time_equi
