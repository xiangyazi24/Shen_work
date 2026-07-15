import ShenWork.Paper3.IntervalDomainMLinearCoefficientProducer

open Set Filter Topology

noncomputable section

namespace ShenWork.Paper3

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.BFormPositiveDatumNegPart
open ShenWork.Paper2.IntervalDomainMMinPersistence
open ShenWork.PDE.ParabolicMaxPrinciple

/-- Exact matched-coefficient expansion of the physical faithful divergence. -/
theorem intervalDomainM_physicalRep_linearized
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {t x : ℝ}
    (hU : 0 < intervalDomainLift (u t) x) :
    -p.χ₀ * classicalChemDivMPhysicalRep p u v t x +
        intervalDomainLift (u t) x *
          (p.a - p.b * intervalDomainLift (u t) x ^ p.α) =
      intervalDomainMLinearDrift p u v t x *
          deriv (intervalDomainLift (u t)) x +
        intervalDomainMLinearReaction p u v t x *
          intervalDomainLift (u t) x := by
  have hpow : intervalDomainLift (u t) x ^ p.m =
      intervalDomainLift (u t) x ^ (p.m - 1) *
        intervalDomainLift (u t) x := by
    calc
      intervalDomainLift (u t) x ^ p.m =
          intervalDomainLift (u t) x ^ ((p.m - 1) + 1) := by ring_nf
      _ = intervalDomainLift (u t) x ^ (p.m - 1) *
          intervalDomainLift (u t) x ^ (1 : ℝ) :=
        Real.rpow_add hU (p.m - 1) 1
      _ = intervalDomainLift (u t) x ^ (p.m - 1) *
          intervalDomainLift (u t) x := by rw [Real.rpow_one]
  simp only [classicalChemDivMPhysicalRep]
  unfold intervalDomainMLinearDrift
    intervalDomainMLinearReaction intervalDomainMFluxFactor
    intervalDomainMFluxFactorDerivPhysical
  rw [hpow]
  ring

/-- The clamped physical trajectory is an exact supersolution (indeed a
solution) of the matched linear drift-reaction equation on every positive
strip carrying a common `u` ceiling. -/
theorem intervalDomainM_classical_linearSuperSolution
    {p : CM2Params} {T s L M : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hs : 0 < s) (_hL : 0 ≤ L) (hsLT : s + L < T) (hM : 0 ≤ M)
    (hu_le : ∀ r ∈ Set.Icc (0 : ℝ) L,
      ∀ x : intervalDomainPoint, u (s + r) x ≤ M) :
    IsClassicalNeumannLinearDriftSuperSolution L
      (restartTimeShift s (intervalDomainMLinearDrift p u v))
      (restartTimeShift s (intervalDomainMLinearReaction p u v))
      (restartTimeShift s (classicalClampField u)) := by
  obtain ⟨_, hTime, _, _, _, _, _⟩ := hsol.regularity
  have hmap : Set.MapsTo
      (fun q : ℝ × ℝ => (s + q.1, q.2))
      (Set.Icc (0 : ℝ) L ×ˢ Set.Icc (0 : ℝ) 1)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro q hq
    exact ⟨⟨lt_of_lt_of_le hs (le_add_of_nonneg_right hq.1.1),
      by linarith [hq.1.2]⟩, hq.2⟩
  refine
    { continuousOn_rect := ?_
      time_hasDerivAt := ?_
      space_hasDerivAt := ?_
      space_second_hasDerivAt := ?_
      pde_ge := ?_
      neumann := ?_
      bounded := ?_ }
  · have hc := classicalClampField_jointContinuousOn hsol
    have hcomp := hc.comp
      (by fun_prop : Continuous (fun q : ℝ × ℝ => (s + q.1, q.2))).continuousOn
      hmap
    simpa [Function.uncurry, restartTimeShift] using hcomp
  · intro r x hr0 hrL hx
    have ht0 : 0 < s + r := by linarith
    have htT : s + r < T := by linarith
    have hbase := classicalClampField_time_hasDerivAt hsol ht0 htT hx
    have hshift : HasDerivAt (fun q : ℝ => s + q) 1 r := by
      simpa using (hasDerivAt_const (x := r) (c := s)).add (hasDerivAt_id r)
    have h := hbase.comp r hshift
    have hdiff : DifferentiableAt ℝ
        (fun q : ℝ => restartTimeShift s (classicalClampField u) q x) r := by
      simpa [restartTimeShift, Function.comp_def] using h.differentiableAt
    simpa [dt] using hdiff.hasDerivAt
  · intro r x hr0 hrL hx
    have ht0 : 0 < s + r := by linarith
    have htT : s + r < T := by linarith
    have h := classicalClampField_space_hasDerivAt hsol ht0 htT hx
    simpa [restartTimeShift, dx, h.deriv] using h
  · intro r x hr0 hrL hx
    have ht0 : 0 < s + r := by linarith
    have htT : s + r < T := by linarith
    have h := classicalClampField_space_second_hasDerivAt hsol ht0 htT hx
    simpa [restartTimeShift, dx, dxx, h.deriv] using h
  · intro r x hr0 hrL hx
    have ht0 : 0 < s + r := by linarith
    have htT : s + r < T := by linarith
    let X : intervalDomainPoint := ⟨x, Set.Ioo_subset_Icc_self hx⟩
    have htime_base := ((hTime X (s + r) ⟨ht0, htT⟩).1.1).hasDerivAt
    have hshift : HasDerivAt (fun q : ℝ => s + q) 1 r := by
      simpa using (hasDerivAt_const (x := r) (c := s)).add (hasDerivAt_id r)
    have htime_shift := htime_base.comp r hshift
    have htime_fun :
        (fun q : ℝ => restartTimeShift s (classicalClampField u) q x) =
          (fun q : ℝ => u (s + q) X) := by
      funext q
      simpa [restartTimeShift, X] using
        classicalClampField_eq_solution
          (u := u) (t := s + q) (x := x) (Set.Ioo_subset_Icc_self hx)
    have hdt :
        deriv (fun q : ℝ => restartTimeShift s (classicalClampField u) q x) r =
          deriv (fun q : ℝ => u q X) (s + r) := by
      rw [htime_fun]
      simpa [Function.comp_def] using htime_shift.deriv
    have hdx :
        deriv (fun y : ℝ => restartTimeShift s (classicalClampField u) r y) x =
          deriv (intervalDomainLift (u (s + r))) x := by
      simpa [restartTimeShift] using
        classicalClampField_deriv_eq_lift (u := u) (t := s + r) hx
    have hdxx :
        deriv (fun y : ℝ =>
          deriv (fun z : ℝ => restartTimeShift s (classicalClampField u) r z) y) x =
          deriv (fun y : ℝ => deriv (intervalDomainLift (u (s + r))) y) x := by
      simpa [restartTimeShift] using
        classicalClampField_secondDeriv_eq_lift (u := u) (t := s + r) hx
    have hval : restartTimeShift s (classicalClampField u) r x =
        intervalDomainLift (u (s + r)) x := by
      simpa [restartTimeShift] using
        classicalClampField_eq_lift (u := u) (t := s + r)
          (Set.Ioo_subset_Icc_self hx)
    have hpde := hsol.pde_u ht0 htT (x := X) hx
    change deriv (fun q : ℝ => u q X) (s + r) =
      deriv (fun y : ℝ => deriv (intervalDomainLift (u (s + r))) y) x -
        p.χ₀ * intervalDomainChemotaxisDivM p (u (s + r)) (v (s + r)) X +
        u (s + r) X * (p.a - p.b * (u (s + r) X) ^ p.α) at hpde
    have hchem := intervalDomainMChemotaxisDiv_eq_physicalRep_interior
      hsol ht0 htT hx
    have hUpos : 0 < intervalDomainLift (u (s + r)) x := by
      simpa [intervalDomainLift, Set.Ioo_subset_Icc_self hx] using
        hsol.u_pos' (x := X) ht0 htT
    have halg := intervalDomainM_physicalRep_linearized
      (p := p) (u := u) (v := v) (t := s + r) (x := x) hUpos
    have hXU : u (s + r) X = intervalDomainLift (u (s + r)) x := by
      rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hx)]
    rw [hchem, hXU] at hpde
    rw [neumannLinearDriftResidual, hdt, hdxx, hdx, hval]
    simp only [restartTimeShift]
    linarith [hpde, halg]
  · intro r hr0 hrL
    have ht0 : 0 < s + r := by linarith
    have htT : s + r < T := by linarith
    have hneu := classicalClampField_neumann hsol ht0 htT
    simpa [restartTimeShift, dx] using hneu
  · refine ⟨M, hM, ?_⟩
    intro r hr x hx
    have ht0 : 0 < s + r := lt_of_lt_of_le hs (le_add_of_nonneg_right hr.1)
    have htT : s + r < T := by linarith [hr.2]
    have hpos : 0 < restartTimeShift s (classicalClampField u) r x := by
      rw [restartTimeShift, classicalClampField_eq_solution hx]
      exact
        hsol.u_pos' (x := (⟨x, hx⟩ : intervalDomainPoint)) ht0 htT
    rw [abs_of_pos hpos]
    rw [restartTimeShift, classicalClampField_eq_solution hx]
    exact hu_le r hr ⟨x, hx⟩

end ShenWork.Paper3

#print axioms ShenWork.Paper3.intervalDomainM_physicalRep_linearized
#print axioms ShenWork.Paper3.intervalDomainM_classical_linearSuperSolution
