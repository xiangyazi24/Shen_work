/-
  Boundary Hamilton inequalities for the faithful general-m interval problem.
-/
import ShenWork.Paper2.IntervalDomainMChemDivBoundaryLimit
import ShenWork.Paper2.IntervalDomainBoundaryHboundChiNonpos

open ShenWork.IntervalDomain ShenWork.Paper2 Set Filter Topology

noncomputable section

namespace ShenWork.Paper2.IntervalDomainMMinPersistence

set_option maxHeartbeats 2400000 in
/-- Left endpoint Hamilton inequality from a one-sided faithful divergence
factorization. -/
theorem hbdry_left_M_of_chemDiv_limit
    {p : CM2Params} {T s M gchem : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hm : 1 ≤ p.m)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hs0 : 0 < s) (hsT : s < T) (hM : 0 ≤ M)
    (hu_le : ∀ x : intervalDomainPoint, u s x ≤ M)
    (hargmin : intervalDomainLift (u s) 0 =
      sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1))
    (hchem_lim : Tendsto (boundaryChemDivMReal p (u s) (v s))
      (nhdsWithin 0 (Set.Ioo (0 : ℝ) 1))
      (nhds (intervalDomainLift (u s) 0 * gchem)))
    (hgchem : |gchem| ≤ M ^ (p.m - 1) *
      ShenWork.MinPersistenceAtoms.fluxCoeffConst p.β (p.ν * M ^ p.γ)) :
    generalMMinGrowthRate p M *
        sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) ≤
      deriv (fun r => intervalDomainLift (u r) 0) s := by
  have htmem : s ∈ Set.Ioo (0 : ℝ) T := ⟨hs0, hsT⟩
  obtain ⟨_, _, _, h6, h7, h8, _⟩ := hsol.regularity
  have hu_c2 : ContDiffOn ℝ 2 (intervalDomainLift (u s))
      (Set.Icc (0 : ℝ) 1) := (h7 s htmem).1.1
  have hu_c2_Ioo := hu_c2.mono Set.Ioo_subset_Icc_self
  have hliftcont := hu_c2.continuousOn
  have hNeu0 : Tendsto (deriv (intervalDomainLift (u s)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := (h6 s htmem).1.1
  have h0Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h01 : (0 : ℝ) < 1 := by norm_num
  let Gt : ℝ → ℝ := fun x =>
    deriv (fun r => intervalDomainLift (u r) x) s
  let R : ℝ → ℝ := fun x => intervalDomainLift (u s) x *
    (p.a - p.b * intervalDomainLift (u s) x ^ p.α)
  let CD : ℝ → ℝ := boundaryChemDivMReal p (u s) (v s)
  let minv : ℝ := intervalDomainLift (u s) 0
  have hfilter : nhdsWithin (0 : ℝ) (Set.Ioo 0 1) =
      nhdsWithin 0 (Set.Ioi 0) :=
    nhdsWithin_Ioo_eq_nhdsGT h01
  have hCD_lim : Tendsto CD (nhdsWithin 0 (Set.Ioi 0))
      (nhds (minv * gchem)) := by
    rw [← hfilter]
    simpa [CD, minv] using hchem_lim
  have hGt_cont : Tendsto Gt (nhdsWithin 0 (Set.Ioi 0)) (nhds (Gt 0)) := by
    have hmaps : Set.MapsTo (fun w => (s, w)) (Set.Icc (0 : ℝ) 1)
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
      fun w hw => ⟨htmem, hw⟩
    have hcomp : ContinuousOn Gt (Set.Icc (0 : ℝ) 1) :=
      h8.1.comp (Continuous.continuousOn
        (by fun_prop : Continuous fun w : ℝ => (s, w))) hmaps
    rw [← hfilter]
    exact (hcomp 0 h0Icc).mono_left
      (nhdsWithin_mono 0 Set.Ioo_subset_Icc_self)
  have hR_cont : Tendsto R (nhdsWithin 0 (Set.Ioi 0)) (nhds (R 0)) := by
    have hRcontOn : ContinuousOn R (Set.Icc (0 : ℝ) 1) :=
      hliftcont.mul (continuousOn_const.sub (continuousOn_const.mul
        (hliftcont.rpow_const (fun _ _ => Or.inr p.hα.le))))
    rw [← hfilter]
    exact (hRcontOn 0 h0Icc).mono_left
      (nhdsWithin_mono 0 Set.Ioo_subset_Icc_self)
  have hpde_eq : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      deriv (deriv (intervalDomainLift (u s))) x =
        Gt x + p.χ₀ * CD x - R x := by
    intro x hx
    have hmem : (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint)
        ∈ intervalDomainM.inside := by
      change x ∈ Set.Ioo (0 : ℝ) 1
      exact hx
    have hpu := hsol.pde_u htmem.1 htmem.2
      hmem
    have etd : intervalDomainM.timeDeriv u s
        (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint) = Gt x := by
      change deriv (fun r =>
        u r (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint)) s = Gt x
      simp only [Gt]
      congr 1
      funext r
      rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hx)]
    have elap : intervalDomainM.laplacian (u s)
        (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint) =
        deriv (deriv (intervalDomainLift (u s))) x := rfl
    have ecd : intervalDomainM.chemotaxisDiv p (u s) (v s)
        (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint) = CD x := by
      change intervalDomainChemotaxisDivM p (u s) (v s)
          (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint) = CD x
      simp [CD, boundaryChemDivMReal, Set.Ioo_subset_Icc_self hx]
    have eu : u s (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint) =
        intervalDomainLift (u s) x := by
      rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hx)]
    rw [etd, elap, ecd, eu] at hpu
    simp only [R]
    linarith [hpu]
  let Vlim : ℝ := Gt 0 + p.χ₀ * (minv * gchem) - R 0
  have hCD_term : Tendsto (fun x => p.χ₀ * CD x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (p.χ₀ * (minv * gchem))) := hCD_lim.const_mul p.χ₀
  have hderiv2_lim : Tendsto (deriv (deriv (intervalDomainLift (u s))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds Vlim) := by
    refine ((hGt_cont.add hCD_term).sub hR_cont).congr' ?_
    rw [← hfilter]
    filter_upwards [self_mem_nhdsWithin] with x hx using (hpde_eq x hx).symm
  have hd1 : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (intervalDomainLift (u s))
        (deriv (intervalDomainLift (u s)) x) x :=
    fun x hx => (ShenWork.MinPersistenceAtoms.contDiffOn_two_hasDerivAt_pair
      isOpen_Ioo hu_c2_Ioo hx).1
  have hd2 : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (deriv (intervalDomainLift (u s)))
        (deriv (deriv (intervalDomainLift (u s))) x) x :=
    fun x hx => (ShenWork.MinPersistenceAtoms.contDiffOn_two_hasDerivAt_pair
      isOpen_Ioo hu_c2_Ioo hx).2
  have hwcont : ContinuousWithinAt (intervalDomainLift (u s))
      (Set.Ici 0) 0 := by
    refine (hliftcont 0 h0Icc).mono_of_mem_nhdsWithin ?_
    have hIcc_eq : Set.Icc (0 : ℝ) 1 = Set.Ici (0 : ℝ) ∩ Set.Iic 1 := by
      ext z
      simp [Set.mem_Icc, Set.mem_Ici, Set.mem_Iic]
    rw [hIcc_eq]
    exact Filter.inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds h01))
  have hbdd : BddBelow
      (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) :=
    (isCompact_Icc.image_of_continuousOn hliftcont).bddBelow
  have hmin : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      intervalDomainLift (u s) 0 ≤ intervalDomainLift (u s) x := by
    intro x hx
    rw [hargmin]
    exact csInf_le hbdd (Set.mem_image_of_mem _ (Set.Ioo_subset_Icc_self hx))
  have hVlim : 0 ≤ Vlim :=
    ShenWork.MinPersistenceAtoms.boundary_min_deriv2_rlimit_nonneg
      h01 hwcont hmin hd1 hd2 hNeu0 hderiv2_lim
  have hminv : minv =
      sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) := by
    exact hargmin
  have hminv_nonneg : 0 ≤ minv := by
    dsimp [minv]
    simpa [intervalDomainLift] using
      (hsol.u_pos' (x := (⟨0, h0Icc⟩ : intervalDomainPoint)) hs0 hsT).le
  have hminv_le : minv ≤ M := by
    dsimp [minv]
    simpa [intervalDomainLift] using
      hu_le (⟨0, h0Icc⟩ : intervalDomainPoint)
  have hpow_le : minv ^ p.α ≤ M ^ p.α :=
    Real.rpow_le_rpow hminv_nonneg hminv_le p.hα.le
  have hR0 : R 0 = minv * (p.a - p.b * minv ^ p.α) := rfl
  have hGt0 : deriv (fun r => intervalDomainLift (u r) 0) s = Gt 0 := rfl
  rw [hGt0, ← hminv]
  have hGt_ge : R 0 - p.χ₀ * (minv * gchem) ≤ Gt 0 := by
    dsimp [Vlim] at hVlim
    linarith
  have hR_lb : (p.a - p.b * M ^ p.α) * minv ≤ R 0 := by
    rw [hR0]
    have h1 : 0 ≤ p.b * (minv * M ^ p.α - minv * minv ^ p.α) :=
      mul_nonneg p.hb (sub_nonneg.mpr
        (mul_le_mul_of_nonneg_left hpow_le hminv_nonneg))
    nlinarith
  let Kchem := M ^ (p.m - 1) *
    ShenWork.MinPersistenceAtoms.fluxCoeffConst p.β (p.ν * M ^ p.γ)
  have hchem_lb : -(|p.χ₀| * Kchem) * minv ≤
      -p.χ₀ * (minv * gchem) := by
    have habs : |-p.χ₀ * (minv * gchem)| ≤ |p.χ₀| * Kchem * minv := by
      rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg hminv_nonneg]
      dsimp [Kchem]
      nlinarith [mul_nonneg (abs_nonneg p.χ₀) hminv_nonneg,
        mul_nonneg (abs_nonneg p.χ₀) (abs_nonneg gchem)]
    nlinarith [(abs_le.mp habs).1]
  have hkey : (p.a - (|p.χ₀| * Kchem + p.b * M ^ p.α)) * minv ≤
      R 0 - p.χ₀ * (minv * gchem) := by
    nlinarith [hR_lb, hchem_lb]
  simpa [generalMMinGrowthRate, generalMMinSlopeConst, Kchem] using
    (show (p.a - (|p.χ₀| * Kchem + p.b * M ^ p.α)) * minv ≤ Gt 0 by
      linarith [hkey, hGt_ge])

/-- Historical left-endpoint Hamilton inequality, obtained by discarding the
nonnegative linear reaction from the sharper growth estimate. -/
theorem hbdry_left_M_of_chemDiv_limit_legacy
    {p : CM2Params} {T s M gchem : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hm : 1 ≤ p.m)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hs0 : 0 < s) (hsT : s < T) (hM : 0 ≤ M)
    (hu_le : ∀ x : intervalDomainPoint, u s x ≤ M)
    (hargmin : intervalDomainLift (u s) 0 =
      sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1))
    (hchem_lim : Tendsto (boundaryChemDivMReal p (u s) (v s))
      (nhdsWithin 0 (Set.Ioo (0 : ℝ) 1))
      (nhds (intervalDomainLift (u s) 0 * gchem)))
    (hgchem : |gchem| ≤ M ^ (p.m - 1) *
      ShenWork.MinPersistenceAtoms.fluxCoeffConst p.β (p.ν * M ^ p.γ)) :
    -generalMMinSlopeConst p M *
        sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) ≤
      deriv (fun r => intervalDomainLift (u r) 0) s := by
  have hgrowth := hbdry_left_M_of_chemDiv_limit hm hsol hs0 hsT hM
    hu_le hargmin hchem_lim hgchem
  have h0Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hmin_nonneg : 0 ≤
      sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) := by
    rw [← hargmin]
    simpa [intervalDomainLift] using
      (hsol.u_pos' (x := (⟨0, h0Icc⟩ : intervalDomainPoint)) hs0 hsT).le
  unfold generalMMinGrowthRate at hgrowth
  nlinarith [mul_nonneg p.ha hmin_nonneg]

/-- The left endpoint bound with its faithful limit producer discharged. -/
theorem hbdry_left_M_of_classicalSolution
    {p : CM2Params} {T s M : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hm : 1 ≤ p.m)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hs0 : 0 < s) (hsT : s < T) (hM : 0 ≤ M)
    (hu_le : ∀ x : intervalDomainPoint, u s x ≤ M)
    (hargmin : intervalDomainLift (u s) 0 =
      sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1)) :
    -generalMMinSlopeConst p M *
        sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) ≤
      deriv (fun r => intervalDomainLift (u r) 0) s := by
  obtain ⟨g, hg, hlim⟩ :=
    boundaryChemDivM_left_limit_factor hm hsol hs0 hsT hM hu_le
  exact hbdry_left_M_of_chemDiv_limit_legacy
    hm hsol hs0 hsT hM hu_le hargmin hlim hg

/-- The left endpoint growth bound with its faithful limit producer
discharged. -/
theorem hbdry_left_M_of_classicalSolution_with_growth
    {p : CM2Params} {T s M : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hm : 1 ≤ p.m)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hs0 : 0 < s) (hsT : s < T) (hM : 0 ≤ M)
    (hu_le : ∀ x : intervalDomainPoint, u s x ≤ M)
    (hargmin : intervalDomainLift (u s) 0 =
      sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1)) :
    generalMMinGrowthRate p M *
        sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) ≤
      deriv (fun r => intervalDomainLift (u r) 0) s := by
  obtain ⟨g, hg, hlim⟩ :=
    boundaryChemDivM_left_limit_factor hm hsol hs0 hsT hM hu_le
  exact hbdry_left_M_of_chemDiv_limit
    hm hsol hs0 hsT hM hu_le hargmin hlim hg

set_option maxHeartbeats 2400000 in
/-- Right endpoint Hamilton inequality from a one-sided faithful divergence
factorization. -/
theorem hbdry_right_M_of_chemDiv_limit
    {p : CM2Params} {T s M gchem : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hm : 1 ≤ p.m)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hs0 : 0 < s) (hsT : s < T) (hM : 0 ≤ M)
    (hu_le : ∀ x : intervalDomainPoint, u s x ≤ M)
    (hargmin : intervalDomainLift (u s) 1 =
      sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1))
    (hchem_lim : Tendsto (boundaryChemDivMReal p (u s) (v s))
      (nhdsWithin 1 (Set.Ioo (0 : ℝ) 1))
      (nhds (intervalDomainLift (u s) 1 * gchem)))
    (hgchem : |gchem| ≤ M ^ (p.m - 1) *
      ShenWork.MinPersistenceAtoms.fluxCoeffConst p.β (p.ν * M ^ p.γ)) :
    generalMMinGrowthRate p M *
        sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) ≤
      deriv (fun r => intervalDomainLift (u r) 1) s := by
  have htmem : s ∈ Set.Ioo (0 : ℝ) T := ⟨hs0, hsT⟩
  obtain ⟨_, _, _, h6, h7, h8, _⟩ := hsol.regularity
  have hu_c2 : ContDiffOn ℝ 2 (intervalDomainLift (u s))
      (Set.Icc (0 : ℝ) 1) := (h7 s htmem).1.1
  have hu_c2_Ioo := hu_c2.mono Set.Ioo_subset_Icc_self
  have hliftcont := hu_c2.continuousOn
  have hNeu1 : Tendsto (deriv (intervalDomainLift (u s)))
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := (h6 s htmem).1.2
  have h1Icc : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have h01 : (0 : ℝ) < 1 := by norm_num
  let Gt : ℝ → ℝ := fun x =>
    deriv (fun r => intervalDomainLift (u r) x) s
  let R : ℝ → ℝ := fun x => intervalDomainLift (u s) x *
    (p.a - p.b * intervalDomainLift (u s) x ^ p.α)
  let CD : ℝ → ℝ := boundaryChemDivMReal p (u s) (v s)
  let minv : ℝ := intervalDomainLift (u s) 1
  have hfilter : nhdsWithin (1 : ℝ) (Set.Ioo 0 1) =
      nhdsWithin 1 (Set.Iio 1) :=
    nhdsWithin_Ioo_eq_nhdsLT h01
  have hCD_lim : Tendsto CD (nhdsWithin 1 (Set.Iio 1))
      (nhds (minv * gchem)) := by
    rw [← hfilter]
    simpa [CD, minv] using hchem_lim
  have hGt_cont : Tendsto Gt (nhdsWithin 1 (Set.Iio 1)) (nhds (Gt 1)) := by
    have hmaps : Set.MapsTo (fun w => (s, w)) (Set.Icc (0 : ℝ) 1)
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
      fun w hw => ⟨htmem, hw⟩
    have hcomp : ContinuousOn Gt (Set.Icc (0 : ℝ) 1) :=
      h8.1.comp (Continuous.continuousOn
        (by fun_prop : Continuous fun w : ℝ => (s, w))) hmaps
    rw [← hfilter]
    exact (hcomp 1 h1Icc).mono_left
      (nhdsWithin_mono 1 Set.Ioo_subset_Icc_self)
  have hR_cont : Tendsto R (nhdsWithin 1 (Set.Iio 1)) (nhds (R 1)) := by
    have hRcontOn : ContinuousOn R (Set.Icc (0 : ℝ) 1) :=
      hliftcont.mul (continuousOn_const.sub (continuousOn_const.mul
        (hliftcont.rpow_const (fun _ _ => Or.inr p.hα.le))))
    rw [← hfilter]
    exact (hRcontOn 1 h1Icc).mono_left
      (nhdsWithin_mono 1 Set.Ioo_subset_Icc_self)
  have hpde_eq : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      deriv (deriv (intervalDomainLift (u s))) x =
        Gt x + p.χ₀ * CD x - R x := by
    intro x hx
    have hmem : (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint)
        ∈ intervalDomainM.inside := by
      change x ∈ Set.Ioo (0 : ℝ) 1
      exact hx
    have hpu := hsol.pde_u htmem.1 htmem.2 hmem
    have etd : intervalDomainM.timeDeriv u s
        (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint) = Gt x := by
      change deriv (fun r =>
        u r (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint)) s = Gt x
      simp only [Gt]
      congr 1
      funext r
      rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hx)]
    have elap : intervalDomainM.laplacian (u s)
        (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint) =
        deriv (deriv (intervalDomainLift (u s))) x := rfl
    have ecd : intervalDomainM.chemotaxisDiv p (u s) (v s)
        (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint) = CD x := by
      change intervalDomainChemotaxisDivM p (u s) (v s)
          (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint) = CD x
      simp [CD, boundaryChemDivMReal, Set.Ioo_subset_Icc_self hx]
    have eu : u s (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint) =
        intervalDomainLift (u s) x := by
      rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hx)]
    rw [etd, elap, ecd, eu] at hpu
    simp only [R]
    linarith [hpu]
  let Vlim : ℝ := Gt 1 + p.χ₀ * (minv * gchem) - R 1
  have hCD_term : Tendsto (fun x => p.χ₀ * CD x)
      (nhdsWithin 1 (Set.Iio 1))
      (nhds (p.χ₀ * (minv * gchem))) := hCD_lim.const_mul p.χ₀
  have hderiv2_lim : Tendsto (deriv (deriv (intervalDomainLift (u s))))
      (nhdsWithin 1 (Set.Iio 1)) (nhds Vlim) := by
    refine ((hGt_cont.add hCD_term).sub hR_cont).congr' ?_
    rw [← hfilter]
    filter_upwards [self_mem_nhdsWithin] with x hx using (hpde_eq x hx).symm
  have hd1 : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (intervalDomainLift (u s))
        (deriv (intervalDomainLift (u s)) x) x :=
    fun x hx => (ShenWork.MinPersistenceAtoms.contDiffOn_two_hasDerivAt_pair
      isOpen_Ioo hu_c2_Ioo hx).1
  have hd2 : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (deriv (intervalDomainLift (u s)))
        (deriv (deriv (intervalDomainLift (u s))) x) x :=
    fun x hx => (ShenWork.MinPersistenceAtoms.contDiffOn_two_hasDerivAt_pair
      isOpen_Ioo hu_c2_Ioo hx).2
  have hwcont : ContinuousWithinAt (intervalDomainLift (u s))
      (Set.Iic 1) 1 := by
    refine (hliftcont 1 h1Icc).mono_of_mem_nhdsWithin ?_
    have hIcc_eq : Set.Icc (0 : ℝ) 1 = Set.Ici (0 : ℝ) ∩ Set.Iic 1 := by
      ext z
      simp [Set.mem_Icc, Set.mem_Ici, Set.mem_Iic]
    rw [hIcc_eq]
    exact Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds h01))
      self_mem_nhdsWithin
  have hbdd : BddBelow
      (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) :=
    (isCompact_Icc.image_of_continuousOn hliftcont).bddBelow
  have hmin : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      intervalDomainLift (u s) 1 ≤ intervalDomainLift (u s) x := by
    intro x hx
    rw [hargmin]
    exact csInf_le hbdd (Set.mem_image_of_mem _ (Set.Ioo_subset_Icc_self hx))
  have hVlim : 0 ≤ Vlim :=
    ShenWork.MinPersistenceAtoms.boundary_min_deriv2_llimit_nonneg
      (η := 1) h01 hwcont
      (fun x hx => hmin x (by simpa using hx))
      (fun x hx => hd1 x (by simpa using hx))
      (fun x hx => hd2 x (by simpa using hx))
      hNeu1 hderiv2_lim
  have hminv : minv =
      sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) := by
    exact hargmin
  have hminv_nonneg : 0 ≤ minv := by
    dsimp [minv]
    simpa [intervalDomainLift] using
      (hsol.u_pos' (x := (⟨1, h1Icc⟩ : intervalDomainPoint)) hs0 hsT).le
  have hminv_le : minv ≤ M := by
    dsimp [minv]
    simpa [intervalDomainLift] using
      hu_le (⟨1, h1Icc⟩ : intervalDomainPoint)
  have hpow_le : minv ^ p.α ≤ M ^ p.α :=
    Real.rpow_le_rpow hminv_nonneg hminv_le p.hα.le
  have hR1 : R 1 = minv * (p.a - p.b * minv ^ p.α) := rfl
  have hGt1 : deriv (fun r => intervalDomainLift (u r) 1) s = Gt 1 := rfl
  rw [hGt1, ← hminv]
  have hGt_ge : R 1 - p.χ₀ * (minv * gchem) ≤ Gt 1 := by
    dsimp [Vlim] at hVlim
    linarith
  have hR_lb : (p.a - p.b * M ^ p.α) * minv ≤ R 1 := by
    rw [hR1]
    have h1 : 0 ≤ p.b * (minv * M ^ p.α - minv * minv ^ p.α) :=
      mul_nonneg p.hb (sub_nonneg.mpr
        (mul_le_mul_of_nonneg_left hpow_le hminv_nonneg))
    nlinarith
  let Kchem := M ^ (p.m - 1) *
    ShenWork.MinPersistenceAtoms.fluxCoeffConst p.β (p.ν * M ^ p.γ)
  have hchem_lb : -(|p.χ₀| * Kchem) * minv ≤
      -p.χ₀ * (minv * gchem) := by
    have habs : |-p.χ₀ * (minv * gchem)| ≤ |p.χ₀| * Kchem * minv := by
      rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg hminv_nonneg]
      dsimp [Kchem]
      nlinarith [mul_nonneg (abs_nonneg p.χ₀) hminv_nonneg,
        mul_nonneg (abs_nonneg p.χ₀) (abs_nonneg gchem)]
    nlinarith [(abs_le.mp habs).1]
  have hkey : (p.a - (|p.χ₀| * Kchem + p.b * M ^ p.α)) * minv ≤
      R 1 - p.χ₀ * (minv * gchem) := by
    nlinarith [hR_lb, hchem_lb]
  simpa [generalMMinGrowthRate, generalMMinSlopeConst, Kchem] using
    (show (p.a - (|p.χ₀| * Kchem + p.b * M ^ p.α)) * minv ≤ Gt 1 by
      linarith [hkey, hGt_ge])

/-- Historical right-endpoint Hamilton inequality, obtained by discarding the
nonnegative linear reaction from the sharper growth estimate. -/
theorem hbdry_right_M_of_chemDiv_limit_legacy
    {p : CM2Params} {T s M gchem : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hm : 1 ≤ p.m)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hs0 : 0 < s) (hsT : s < T) (hM : 0 ≤ M)
    (hu_le : ∀ x : intervalDomainPoint, u s x ≤ M)
    (hargmin : intervalDomainLift (u s) 1 =
      sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1))
    (hchem_lim : Tendsto (boundaryChemDivMReal p (u s) (v s))
      (nhdsWithin 1 (Set.Ioo (0 : ℝ) 1))
      (nhds (intervalDomainLift (u s) 1 * gchem)))
    (hgchem : |gchem| ≤ M ^ (p.m - 1) *
      ShenWork.MinPersistenceAtoms.fluxCoeffConst p.β (p.ν * M ^ p.γ)) :
    -generalMMinSlopeConst p M *
        sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) ≤
      deriv (fun r => intervalDomainLift (u r) 1) s := by
  have hgrowth := hbdry_right_M_of_chemDiv_limit hm hsol hs0 hsT hM
    hu_le hargmin hchem_lim hgchem
  have h1Icc : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hmin_nonneg : 0 ≤
      sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) := by
    rw [← hargmin]
    simpa [intervalDomainLift] using
      (hsol.u_pos' (x := (⟨1, h1Icc⟩ : intervalDomainPoint)) hs0 hsT).le
  unfold generalMMinGrowthRate at hgrowth
  nlinarith [mul_nonneg p.ha hmin_nonneg]

/-- The right endpoint bound with its faithful limit producer discharged. -/
theorem hbdry_right_M_of_classicalSolution
    {p : CM2Params} {T s M : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hm : 1 ≤ p.m)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hs0 : 0 < s) (hsT : s < T) (hM : 0 ≤ M)
    (hu_le : ∀ x : intervalDomainPoint, u s x ≤ M)
    (hargmin : intervalDomainLift (u s) 1 =
      sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1)) :
    -generalMMinSlopeConst p M *
        sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) ≤
      deriv (fun r => intervalDomainLift (u r) 1) s := by
  obtain ⟨g, hg, hlim⟩ :=
    boundaryChemDivM_right_limit_factor hm hsol hs0 hsT hM hu_le
  exact hbdry_right_M_of_chemDiv_limit_legacy
    hm hsol hs0 hsT hM hu_le hargmin hlim hg

/-- The right endpoint growth bound with its faithful limit producer
discharged. -/
theorem hbdry_right_M_of_classicalSolution_with_growth
    {p : CM2Params} {T s M : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hm : 1 ≤ p.m)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hs0 : 0 < s) (hsT : s < T) (hM : 0 ≤ M)
    (hu_le : ∀ x : intervalDomainPoint, u s x ≤ M)
    (hargmin : intervalDomainLift (u s) 1 =
      sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1)) :
    generalMMinGrowthRate p M *
        sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) ≤
      deriv (fun r => intervalDomainLift (u r) 1) s := by
  obtain ⟨g, hg, hlim⟩ :=
    boundaryChemDivM_right_limit_factor hm hsol hs0 hsT hM hu_le
  exact hbdry_right_M_of_chemDiv_limit
    hm hsol hs0 hsT hM hu_le hargmin hlim hg

section AxiomAudit

#print axioms hbdry_left_M_of_chemDiv_limit
#print axioms hbdry_left_M_of_classicalSolution_with_growth
#print axioms hbdry_left_M_of_classicalSolution
#print axioms hbdry_right_M_of_chemDiv_limit
#print axioms hbdry_right_M_of_classicalSolution_with_growth
#print axioms hbdry_right_M_of_classicalSolution

end AxiomAudit

end ShenWork.Paper2.IntervalDomainMMinPersistence
