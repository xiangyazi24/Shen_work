import ShenWork.Paper3.IntervalDomainMRectangleInteriorSlopes
import ShenWork.Paper2.IntervalDomainMChemDivBoundaryLimit
import ShenWork.Paper2.IntervalLemma31Closure

/-!
# Closed-interval boundary slopes for the faithful general-`m` rectangle argument

`intervalDomainM` counterpart of `IntervalDomainRectangleBoundarySlopes`.  At a
Neumann endpoint the one-sided derivative of the lifted population vanishes, so the
faithful `u^m` chemotaxis divergence limit factors as `U^m · (elliptic
coefficient)`.  The exact endpoint value is read off the closed-interval physical
representative `classicalChemDivMPhysicalRep` (continuous up to the boundary), whose
value at the endpoint collapses to `U0^m · (1+V0)^(-β)·(μV0 − νU0^γ)` because both
`U_x` and `V_x` vanish there.  The maximum/minimum r-limit second-derivative sign
lemmas are the common `Lemma31Closure` ones.
-/

open Set Filter Topology
open ShenWork.IntervalDomain ShenWork.PDE ShenWork.Paper2
open ShenWork.MinPersistenceAtoms ShenWork.MaxPrincipleAtoms
open ShenWork.Paper2.IntervalDomainMMinPersistence

namespace ShenWork.Paper3

noncomputable section

/-- Left-boundary rectangle balance for the faithful `u^m` flux. -/
theorem intervalDomainM_rectangle_boundary_left_balance
    {p : CM2Params} {T t : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    ((∀ y ∈ Ioo (0 : ℝ) 1,
        intervalDomainLift (u t) y ≤ intervalDomainLift (u t) 0) →
      deriv (fun r => intervalDomainLift (u r) 0) t ≤
        intervalDomainLift (u t) 0 *
            (p.a - p.b * (intervalDomainLift (u t) 0) ^ p.α) -
          p.χ₀ * (intervalDomainLift (u t) 0) ^ p.m *
            ((1 + intervalDomainLift (v t) 0) ^ (-p.β) *
              (p.μ * intervalDomainLift (v t) 0 -
                p.ν * (intervalDomainLift (u t) 0) ^ p.γ))) ∧
    ((∀ y ∈ Ioo (0 : ℝ) 1,
        intervalDomainLift (u t) 0 ≤ intervalDomainLift (u t) y) →
      intervalDomainLift (u t) 0 *
            (p.a - p.b * (intervalDomainLift (u t) 0) ^ p.α) -
          p.χ₀ * (intervalDomainLift (u t) 0) ^ p.m *
            ((1 + intervalDomainLift (v t) 0) ^ (-p.β) *
              (p.μ * intervalDomainLift (v t) 0 -
                p.ν * (intervalDomainLift (u t) 0) ^ p.γ)) ≤
        deriv (fun r => intervalDomainLift (u r) 0) t) := by
  obtain ⟨hC2, _, _, hNeu, hClosed, hJDt, _⟩ := hsol.regularity
  set U : ℝ → ℝ := intervalDomainLift (u t) with hU_def
  set V : ℝ → ℝ := intervalDomainLift (v t) with hV_def
  have huC2 : ContDiffOn ℝ 2 U (Ioo (0 : ℝ) 1) := (hC2 t ht).1
  have huCont : ContinuousOn U (Icc (0 : ℝ) 1) :=
    (hClosed t ht).1.1.continuousOn
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h01 : (0 : ℝ) < 1 := by norm_num
  have hUpos : 0 < U 0 := by
    rw [hU_def, intervalDomainLift, dif_pos h0]
    exact hsol.u_pos' ht.1 ht.2
  have hNeuU : Tendsto (deriv U) (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    (hNeu t ht).1.1
  have hdu0 : deriv U 0 = 0 := (hClosed t ht).1.2.1
  have hdv0 : deriv V 0 = 0 := (hClosed t ht).2.2.1
  set G : ℝ → ℝ := fun x =>
    deriv (fun r => intervalDomainLift (u r) x) t with hG_def
  set R : ℝ → ℝ := fun x => U x * (p.a - p.b * U x ^ p.α) with hR_def
  set Cfun : ℝ → ℝ := fun x => boundaryChemDivMReal p (u t) (v t) x with hCfun_def
  set CL : ℝ := (U 0) ^ p.m * ((1 + V 0) ^ (-p.β) *
    (p.μ * V 0 - p.ν * U 0 ^ p.γ)) with hCL_def
  have hfilter : nhdsWithin (0 : ℝ) (Ioo 0 1) =
      nhdsWithin 0 (Ioi 0) := nhdsWithin_Ioo_eq_nhdsGT h01
  have hGlim : Tendsto G (nhdsWithin 0 (Ioi 0)) (nhds (G 0)) := by
    have hmaps : MapsTo (fun w => (t, w)) (Icc (0 : ℝ) 1)
        (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) := fun w hw => ⟨ht, hw⟩
    have hcomp : ContinuousOn G (Icc (0 : ℝ) 1) :=
      hJDt.1.comp (Continuous.continuousOn
        (by fun_prop : Continuous fun w : ℝ => (t, w))) hmaps
    rw [← hfilter]
    exact (hcomp 0 h0).mono_left
      (nhdsWithin_mono 0 Ioo_subset_Icc_self)
  have hRlim : Tendsto R (nhdsWithin 0 (Ioi 0)) (nhds (R 0)) := by
    have hRcont : ContinuousOn R (Icc (0 : ℝ) 1) :=
      huCont.mul (continuousOn_const.sub
        (continuousOn_const.mul
          (huCont.rpow_const (fun _ _ => Or.inr p.hα.le))))
    rw [← hfilter]
    exact (hRcont 0 h0).mono_left
      (nhdsWithin_mono 0 Ioo_subset_Icc_self)
  have hUxxEq : ∀ x ∈ Ioo (0 : ℝ) 1,
      deriv (deriv U) x = G x - R x + p.χ₀ * Cfun x := by
    intro x hx
    let xp : intervalDomainPoint := ⟨x, Ioo_subset_Icc_self hx⟩
    have hpde := hsol.pde_u ht.1 ht.2 (x := xp) hx
    have etd : intervalDomainM.timeDeriv u t xp = G x := by
      show deriv (fun r => u r xp) t = G x
      simp only [hG_def]
      congr 1
      funext r
      rw [intervalDomainLift, dif_pos (Ioo_subset_Icc_self hx)]
    have elap : intervalDomainM.laplacian (u t) xp = deriv (deriv U) x := rfl
    have echem : intervalDomainM.chemotaxisDiv p (u t) (v t) xp = Cfun x := by
      show intervalDomainChemotaxisDivM p (u t) (v t) xp =
        boundaryChemDivMReal p (u t) (v t) x
      unfold boundaryChemDivMReal
      rw [dif_pos (Ioo_subset_Icc_self hx)]
    have eu : u t xp = U x := by
      rw [hU_def, intervalDomainLift, dif_pos (Ioo_subset_Icc_self hx)]
    rw [etd, elap, echem, eu] at hpde
    rw [hR_def]
    linarith
  -- exact endpoint chemotaxis limit via the continuous physical representative
  have hphys0 : classicalChemDivMPhysicalRep p u v t 0 = CL := by
    simp only [classicalChemDivMPhysicalRep, hCL_def, ← hU_def, ← hV_def, hdu0,
      hdv0]
    ring
  have hphysCont : ContinuousOn (classicalChemDivMPhysicalRep p u v t)
      (Icc (0 : ℝ) 1) :=
    classicalChemDivMPhysicalRep_continuousOn_Icc hsol ht.1 ht.2
  have hClim : Tendsto Cfun (nhdsWithin 0 (Ioi 0)) (nhds CL) := by
    have hlim : Tendsto (classicalChemDivMPhysicalRep p u v t)
        (nhdsWithin 0 (Ioo 0 1)) (nhds CL) := by
      rw [← hphys0]
      exact (hphysCont 0 h0).mono_left
        (nhdsWithin_mono 0 Ioo_subset_Icc_self)
    have heq := boundaryChemDivMReal_eq_physicalRep_eventually hsol ht.1 ht.2
    rw [← hfilter]
    exact (Filter.Tendsto.congr' heq.symm hlim)
  set W : ℝ := G 0 - R 0 + p.χ₀ * CL with hW_def
  have hUxxLim : Tendsto (deriv (deriv U)) (nhdsWithin 0 (Ioi 0))
      (nhds W) := by
    refine ((hGlim.sub hRlim).add (hClim.const_mul p.χ₀)).congr' ?_
    rw [← hfilter]
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hUxxEq x hx).symm
  have hUwithin : ContinuousWithinAt U (Ici 0) 0 := by
    refine (huCont 0 h0).mono_of_mem_nhdsWithin ?_
    have hIcc : Icc (0 : ℝ) 1 = Ici (0 : ℝ) ∩ Iic 1 := by
      ext z; simp [mem_Icc, mem_Ici, mem_Iic]
    rw [hIcc]
    exact inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds h01))
  have hd1 : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt U (deriv U x) x :=
    fun x hx => (contDiffOn_two_hasDerivAt_pair isOpen_Ioo huC2 hx).1
  have hd2 : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (deriv U) (deriv (deriv U) x) x :=
    fun x hx => (contDiffOn_two_hasDerivAt_pair isOpen_Ioo huC2 hx).2
  have hG : G 0 = W + R 0 - p.χ₀ * CL := by rw [hW_def]; ring
  constructor
  · intro hmax
    have hWle : W ≤ 0 :=
      Lemma31Closure.boundary_max_deriv2_rlimit_nonpos h01 hUwithin
        hmax hd1 hd2 hNeuU hUxxLim
    rw [show deriv (fun r => intervalDomainLift (u r) 0) t = G 0 from rfl, hG]
    simp only [hR_def, hCL_def, hU_def, hV_def]
    linarith
  · intro hmin
    have hWge : 0 ≤ W :=
      boundary_min_deriv2_rlimit_nonneg h01 hUwithin
        hmin hd1 hd2 hNeuU hUxxLim
    rw [show deriv (fun r => intervalDomainLift (u r) 0) t = G 0 from rfl, hG]
    simp only [hR_def, hCL_def, hU_def, hV_def]
    linarith

end

end ShenWork.Paper3
