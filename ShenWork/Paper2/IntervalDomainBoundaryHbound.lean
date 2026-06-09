/-
  Phase C (MinPersistence): the boundary min-point bound for χ₀ = 0.

  At χ₀ = 0 the chemotaxis flux drops out of the PDE, so at a boundary spatial
  argmin (`ys = 0`, Neumann `u'(0⁺) → 0`):
    u_t(s,0) = (lim_{x→0⁺} u_xx(s,x)) + reaction(s,0),
  and `V := u_t(s,0) − reaction(s,0)` IS the `u_xx` right-limit (interior PDE +
  joint-∂ₜ continuity (conjunct 8) + reaction continuity), so
  `boundary_min_deriv2_rlimit_nonneg` gives `V ≥ 0`, whence
    u_t(s,0) = V + reaction(s,0) ≥ reaction(s,0) = m(a−b·m^α) ≥ −b·M'^α·m ≥ −K·m.
  This discharges `hbdry` (left endpoint) for χ₀ = 0 — the last analytic gap of
  general-trace MinPersistence in the flux-free regime.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainBoundaryDeriv2
import ShenWork.Paper2.IntervalDomainC2Extraction
import ShenWork.Paper2.IntervalDomainFluxCoeffBound
import ShenWork.Paper2.Statements

open ShenWork.IntervalDomain ShenWork.Paper2 Set Filter Topology

noncomputable section

namespace ShenWork.MinPersistenceAtoms

set_option maxHeartbeats 1600000 in
/-- **Boundary (left) min-point bound, χ₀ = 0.** -/
theorem hbdry_left_chi0
    {p : CM2Params} {T s M' : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hχ0 : p.χ₀ = 0)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hs0 : 0 < s) (hsT : s < T) (hM' : 0 ≤ M')
    (hu_le : ∀ x : intervalDomainPoint, u s x ≤ M')
    (hargmin : intervalDomainLift (u s) 0
        = sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1)) :
    -(|p.χ₀| * fluxCoeffConst p.β (p.ν * M' ^ p.γ) + p.b * M' ^ p.α)
        * sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1)
      ≤ deriv (fun r => intervalDomainLift (u r) 0) s := by
  have htmem : s ∈ Set.Ioo (0:ℝ) T := ⟨hs0, hsT⟩
  obtain ⟨_, _, _, h6, h7, h8, _⟩ := hsol.regularity
  have hu_c2 : ContDiffOn ℝ 2 (intervalDomainLift (u s)) (Set.Icc (0:ℝ) 1) :=
    (h7 s htmem).1.1
  have hu_c2_Ioo : ContDiffOn ℝ 2 (intervalDomainLift (u s)) (Set.Ioo (0:ℝ) 1) :=
    hu_c2.mono Set.Ioo_subset_Icc_self
  have hliftcont : ContinuousOn (intervalDomainLift (u s)) (Set.Icc (0:ℝ) 1) :=
    hu_c2.continuousOn
  have hNeu0 : Tendsto (deriv (intervalDomainLift (u s)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := (h6 s htmem).1.1
  have h0Icc : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  have h01 : (0:ℝ) < 1 := by norm_num
  set G : ℝ → ℝ := fun x => deriv (fun r => intervalDomainLift (u r) x) s with hG_def
  set R : ℝ → ℝ := fun x => intervalDomainLift (u s) x
    * (p.a - p.b * (intervalDomainLift (u s) x) ^ p.α) with hR_def
  -- Bridge `𝓝[Ioo 0 1] 0 = 𝓝[Ioi 0] 0` for the right-limits.
  have hfilter : nhdsWithin (0:ℝ) (Set.Ioo 0 1) = nhdsWithin 0 (Set.Ioi 0) :=
    nhdsWithin_Ioo_eq_nhdsGT h01
  -- `G` continuous at `0` along `0⁺` (conjunct 8).
  have hG_cont : Tendsto G (nhdsWithin 0 (Set.Ioi 0)) (nhds (G 0)) := by
    have hmaps : Set.MapsTo (fun w => (s, w)) (Set.Icc (0:ℝ) 1)
        (Set.Ioo (0:ℝ) T ×ˢ Set.Icc (0:ℝ) 1) := fun w hw => ⟨htmem, hw⟩
    have hcomp : ContinuousOn G (Set.Icc (0:ℝ) 1) :=
      h8.1.comp (Continuous.continuousOn
        (by fun_prop : Continuous fun w : ℝ => (s, w))) hmaps
    rw [← hfilter]
    exact (hcomp 0 h0Icc).mono_left (nhdsWithin_mono 0 Set.Ioo_subset_Icc_self)
  -- reaction `R` continuous at `0` along `0⁺`.
  have hR_cont : Tendsto R (nhdsWithin 0 (Set.Ioi 0)) (nhds (R 0)) := by
    have hRcontOn : ContinuousOn R (Set.Icc (0:ℝ) 1) :=
      hliftcont.mul (continuousOn_const.sub (continuousOn_const.mul
        (hliftcont.rpow_const (fun x _ => Or.inr p.hα.le))))
    rw [← hfilter]
    exact (hRcontOn 0 h0Icc).mono_left (nhdsWithin_mono 0 Set.Ioo_subset_Icc_self)
  -- PDE on the interior (χ₀ = 0): `deriv² (lift (u s)) = G − R` on `(0,1)`.
  have hpde_eq : ∀ x ∈ Set.Ioo (0:ℝ) 1,
      deriv (deriv (intervalDomainLift (u s))) x = G x - R x := by
    intro x hx
    have hmem : (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint)
        ∈ intervalDomain.inside := hx
    have hpu := hsol.pde_u hs0 hsT hmem
    have e_td : intervalDomain.timeDeriv u s ⟨x, Set.Ioo_subset_Icc_self hx⟩ = G x := by
      show deriv (fun r => u r ⟨x, Set.Ioo_subset_Icc_self hx⟩) s = G x
      simp only [hG_def]; congr 1; funext r
      rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hx)]
    have e_lap : intervalDomain.laplacian (u s)
        ⟨x, Set.Ioo_subset_Icc_self hx⟩
        = deriv (deriv (intervalDomainLift (u s))) x := rfl
    have e_u : u s (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint)
        = intervalDomainLift (u s) x := by
      rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hx)]
    rw [e_td, e_lap, hχ0] at hpu
    simp only [zero_mul, sub_zero] at hpu
    rw [e_u] at hpu
    rw [hR_def]; linarith [hpu]
  -- `deriv² (lift (u s)) → V := G 0 − R 0` along `0⁺`.
  set V : ℝ := G 0 - R 0 with hV_def
  have hderiv2_lim : Tendsto (deriv (deriv (intervalDomainLift (u s))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds V) := by
    refine (hG_cont.sub hR_cont).congr' ?_
    rw [← hfilter]
    filter_upwards [self_mem_nhdsWithin] with x hx using (hpde_eq x hx).symm
  -- HasDerivAt data on `(0,1)`.
  have hd1 : ∀ x ∈ Set.Ioo (0:ℝ) 1,
      HasDerivAt (intervalDomainLift (u s)) (deriv (intervalDomainLift (u s)) x) x :=
    fun x hx => (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hu_c2_Ioo hx).1
  have hd2 : ∀ x ∈ Set.Ioo (0:ℝ) 1,
      HasDerivAt (deriv (intervalDomainLift (u s)))
        (deriv (deriv (intervalDomainLift (u s))) x) x :=
    fun x hx => (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hu_c2_Ioo hx).2
  -- `lift (u s)` right-continuous at `0`.
  have hwcont : ContinuousWithinAt (intervalDomainLift (u s)) (Set.Ici 0) 0 := by
    refine (hliftcont 0 h0Icc).mono_of_mem_nhdsWithin ?_
    have hIcc_eq : Set.Icc (0:ℝ) 1 = Set.Ici (0:ℝ) ∩ Set.Iic 1 := by
      ext z; simp [Set.mem_Icc, Set.mem_Ici, Set.mem_Iic, and_comm]
    rw [hIcc_eq]
    exact Filter.inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds h01))
  -- `0` is a spatial argmin on `(0,1)`.
  have hbdd : BddBelow (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1) :=
    (isCompact_Icc.image_of_continuousOn hliftcont).bddBelow
  have hmin : ∀ x ∈ Set.Ioo (0:ℝ) 1,
      intervalDomainLift (u s) 0 ≤ intervalDomainLift (u s) x := by
    intro x hx
    rw [hargmin]
    exact csInf_le hbdd (Set.mem_image_of_mem _ (Set.Ioo_subset_Icc_self hx))
  -- Boundary 2nd-derivative test ⇒ `0 ≤ V`.
  have hV_nonneg : 0 ≤ V :=
    boundary_min_deriv2_rlimit_nonneg h01 hwcont hmin hd1 hd2 hNeu0 hderiv2_lim
  -- Reaction lower bound at `0`.
  set m : ℝ := intervalDomainLift (u s) 0 with hm_def
  have hm_eq_sInf : m = sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1) := hargmin
  have hm_nonneg : 0 ≤ m := by
    rw [hm_def, intervalDomainLift, dif_pos h0Icc]
    exact (hsol.u_pos' hs0 hsT).le
  have hm_le : m ≤ M' := by
    rw [hm_def, intervalDomainLift, dif_pos h0Icc]; exact hu_le _
  have hpow_le : m ^ p.α ≤ M' ^ p.α := Real.rpow_le_rpow hm_nonneg hm_le p.hα.le
  have hmpow_nn : 0 ≤ m ^ p.α := Real.rpow_nonneg hm_nonneg _
  have hflux_nn : 0 ≤ fluxCoeffConst p.β (p.ν * M' ^ p.γ) :=
    fluxCoeffConst_nonneg p.hβ (mul_nonneg p.hν.le (Real.rpow_nonneg hM' _))
  -- `R 0 = m·(a − b·m^α) ≥ −(b·M'^α)·m ≥ −K·m`, and `G 0 = V + R 0 ≥ R 0`.
  have hR0 : R 0 = m * (p.a - p.b * m ^ p.α) := by rw [hR_def, hm_def]
  have hgoal_G : deriv (fun r => intervalDomainLift (u r) 0) s = G 0 := rfl
  rw [hgoal_G, ← hm_eq_sInf]
  have hG0_ge : R 0 ≤ G 0 := by rw [hV_def] at hV_nonneg; linarith
  have hkey : -(|p.χ₀| * fluxCoeffConst p.β (p.ν * M' ^ p.γ) + p.b * M' ^ p.α) * m
      ≤ R 0 := by
    rw [hR0]
    have h1 : 0 ≤ p.b * (m * M' ^ p.α - m * m ^ p.α) :=
      mul_nonneg p.hb (sub_nonneg.mpr (mul_le_mul_of_nonneg_left hpow_le hm_nonneg))
    have h2 : 0 ≤ |p.χ₀| * fluxCoeffConst p.β (p.ν * M' ^ p.γ) * m :=
      mul_nonneg (mul_nonneg (abs_nonneg _) hflux_nn) hm_nonneg
    have h3 : 0 ≤ m * p.a := mul_nonneg hm_nonneg p.ha
    nlinarith [h1, h2, h3]
  linarith [hG0_ge, hkey]

end ShenWork.MinPersistenceAtoms
