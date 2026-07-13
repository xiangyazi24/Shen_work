/-
  Phase C (MinPersistence): the interior min-point bound in `hbound` shape.

  Bridges `interior_min_point_of_solution` (which concludes
  `−K·(u t x) ≤ timeDeriv u t x`) to the exact `hbound` shape consumed by
  `solution_persist_exists_c`:
    `−K·sInf(lift(u s) '' [0,1]) ≤ deriv (fun r => lift(u r) ys) s`
  at an INTERIOR spatial argmin `ys ∈ (0,1)`.  Uses `u s x = lift(u s) ys = sInf`
  (argmin) and `timeDeriv u s x = deriv(fun r => lift(u r) ys) s` (defeq + the
  interior lift bridge).  Boundary argmins `ys ∈ {0,1}` are the separate
  boundary assembly.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainMinPointSolution

open ShenWork.IntervalDomain ShenWork.Paper2 Set Filter Topology

noncomputable section

namespace ShenWork.MinPersistenceAtoms

/-- **Interior min-point bound (hbound shape).** -/
theorem hbound_interior_allChi
    {p : CM2Params} {T s M' : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hs0 : 0 < s) (hsT : s < T) (hM' : 0 ≤ M')
    (hu_bd : ∀ y, |intervalDomainLift (u s) y| ≤ M')
    {ys : ℝ} (hys_int : ys ∈ Set.Ioo (0:ℝ) 1)
    (hargmin : intervalDomainLift (u s) ys
        = sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1)) :
    -(|p.χ₀| * fluxCoeffConst p.β (p.ν * M' ^ p.γ) + p.b * M' ^ p.α)
        * sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1)
      ≤ deriv (fun r => intervalDomainLift (u r) ys) s := by
  set x : intervalDomainPoint := ⟨ys, Set.Ioo_subset_Icc_self hys_int⟩ with hx_def
  -- `lift (u s) ys = u s x`.
  have hlift_x : intervalDomainLift (u s) ys = u s x := by
    rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hys_int)]
  -- `u s x = sInf` (it is the argmin value).
  have husx_eq : u s x = sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1) := by
    rw [← hlift_x]; exact hargmin
  -- Spatial slice continuous ⇒ image compact ⇒ bdd below.
  have hslice_cont : ContinuousOn (intervalDomainLift (u s)) (Set.Icc (0:ℝ) 1) := by
    obtain ⟨_, _, _, _, h7, _, _⟩ := hsol.regularity
    exact (h7 s ⟨hs0, hsT⟩).1.1.continuousOn
  have hbdd : BddBelow (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1) :=
    (isCompact_Icc.image_of_continuousOn hslice_cont).bddBelow
  -- `x` is a spatial argmin: `u s x ≤ u s z` for all `z`.
  have hmin : ∀ z : intervalDomainPoint, u s x ≤ u s z := by
    intro z
    have hz_lift : intervalDomainLift (u s) z.1 = u s z := by
      simp only [intervalDomainLift, Subtype.coe_eta]
      exact dif_pos z.2
    rw [husx_eq, ← hz_lift]
    exact csInf_le hbdd (Set.mem_image_of_mem _ z.2)
  -- Apply the interior min-point estimate.
  have hmp := interior_min_point_of_solution_allChi hsol hs0 hsT hys_int hmin hM' hu_bd
  -- Bridge `timeDeriv u s x = deriv (fun r => lift (u r) ys) s`.
  have htd_eq : intervalDomain.timeDeriv u s x
      = deriv (fun r => intervalDomainLift (u r) ys) s := by
    have hfun : (fun r => u r x) = (fun r => intervalDomainLift (u r) ys) := by
      funext r
      rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hys_int)]
    show deriv (fun r => u r x) s = _
    rw [hfun]
  rw [htd_eq, husx_eq] at hmp
  exact hmp

/-- Compatibility wrapper for the former nonpositive-sensitivity API. -/
theorem hbound_interior
    {p : CM2Params} {T s M' : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (_hχ : p.χ₀ ≤ 0)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hs0 : 0 < s) (hsT : s < T) (hM' : 0 ≤ M')
    (hu_bd : ∀ y, |intervalDomainLift (u s) y| ≤ M')
    {ys : ℝ} (hys_int : ys ∈ Set.Ioo (0:ℝ) 1)
    (hargmin : intervalDomainLift (u s) ys
        = sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1)) :
    -(|p.χ₀| * fluxCoeffConst p.β (p.ν * M' ^ p.γ) + p.b * M' ^ p.α)
        * sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1)
      ≤ deriv (fun r => intervalDomainLift (u r) ys) s :=
  hbound_interior_allChi hsol hs0 hsT hM' hu_bd hys_int hargmin

end ShenWork.MinPersistenceAtoms
