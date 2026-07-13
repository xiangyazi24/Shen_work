/-
  Phase C (MinPersistence): boundary min-point reducers for general χ₀ ≤ 0.

  The χ₀ = 0 endpoint lemmas avoid the chemotaxis term.  For χ₀ ≤ 0 the
  remaining analytic input is exactly a one-sided endpoint factorization/bound
  for the interior chemotaxis divergence:

    chemDiv(x) → m * g,       |g| ≤ K₁,

  where `m` is the endpoint value of `u` and
  `K₁ = fluxCoeffConst β (ν M'^γ)`.  These lemmas prove that this input is
  sufficient for the left/right boundary min-point residuals.  They do not
  assert the endpoint chemDiv limit itself.
-/
import ShenWork.Paper2.IntervalDomainBoundaryHbound
import ShenWork.Paper2.IntervalDomainBoundaryHboundRight
import ShenWork.Paper2.IntervalBFormPositiveDatumQuantWiring

open ShenWork.IntervalDomain ShenWork.Paper2 Set Filter Topology

noncomputable section

namespace ShenWork.MinPersistenceAtoms

/-- Real-line representative of the interval chemotaxis divergence.

This is meant to be used under one-sided interior filters such as
`𝓝[Set.Ioo 0 1] 0` and `𝓝[Set.Ioo 0 1] 1`; outside `[0,1]` the value is
irrelevant. -/
def boundaryChemDivReal
    (p : CM2Params) (u v : intervalDomainPoint → ℝ) (y : ℝ) : ℝ :=
  if hy : y ∈ Set.Icc (0 : ℝ) 1 then
    intervalDomain.chemotaxisDiv p u v ⟨y, hy⟩
  else 0

/-- Left endpoint one-sided chemotaxis-divergence factor/bound residual. -/
def BoundaryChemDivLeftLimitBound (p : CM2Params) : Prop :=
  ∀ {T s M' : ℝ} {u v : ℝ → intervalDomainPoint → ℝ},
    IsPaper2ClassicalSolution intervalDomain p T u v →
    0 < s → s < T → 0 ≤ M' →
    (∀ x : intervalDomainPoint, u s x ≤ M') →
    ∃ gchem : ℝ,
      |gchem| ≤ fluxCoeffConst p.β (p.ν * M' ^ p.γ) ∧
      Tendsto (boundaryChemDivReal p (u s) (v s))
        (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1))
        (nhds (intervalDomainLift (u s) 0 * gchem))

/-- Right endpoint one-sided chemotaxis-divergence factor/bound residual. -/
def BoundaryChemDivRightLimitBound (p : CM2Params) : Prop :=
  ∀ {T s M' : ℝ} {u v : ℝ → intervalDomainPoint → ℝ},
    IsPaper2ClassicalSolution intervalDomain p T u v →
    0 < s → s < T → 0 ≤ M' →
    (∀ x : intervalDomainPoint, u s x ≤ M') →
    ∃ gchem : ℝ,
      |gchem| ≤ fluxCoeffConst p.β (p.ν * M' ^ p.γ) ∧
      Tendsto (boundaryChemDivReal p (u s) (v s))
        (nhdsWithin (1 : ℝ) (Set.Ioo (0 : ℝ) 1))
        (nhds (intervalDomainLift (u s) 1 * gchem))

/-- Bundled one-sided chemotaxis-divergence endpoint residuals. -/
structure BoundaryChemDivEndpointLimitBounds (p : CM2Params) : Prop where
  left : BoundaryChemDivLeftLimitBound p
  right : BoundaryChemDivRightLimitBound p

set_option maxHeartbeats 1600000 in
-- The endpoint reducer replays the boundary second-derivative test and PDE
-- transfer algebra in one theorem, which is near the default heartbeat budget.
/-- **Left endpoint min-point bound from a one-sided chemDiv factor bound.** -/
theorem hbdry_left_of_chemDiv_limit
    {p : CM2Params} {T s M' gchem : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hs0 : 0 < s) (hsT : s < T) (hM' : 0 ≤ M')
    (hu_le : ∀ x : intervalDomainPoint, u s x ≤ M')
    (hargmin : intervalDomainLift (u s) 0
        = sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1))
    (hchem_lim : Tendsto (boundaryChemDivReal p (u s) (v s))
      (nhdsWithin 0 (Set.Ioo (0 : ℝ) 1))
      (nhds (intervalDomainLift (u s) 0 * gchem)))
    (hgchem : |gchem| ≤ fluxCoeffConst p.β (p.ν * M' ^ p.γ)) :
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
  set CD : ℝ → ℝ := boundaryChemDivReal p (u s) (v s) with hCD_def
  set m : ℝ := intervalDomainLift (u s) 0 with hm_def
  -- Bridge `𝓝[Ioo 0 1] 0 = 𝓝[Ioi 0] 0` for the right-limits.
  have hfilter : nhdsWithin (0:ℝ) (Set.Ioo 0 1) = nhdsWithin 0 (Set.Ioi 0) :=
    nhdsWithin_Ioo_eq_nhdsGT h01
  have hCD_lim : Tendsto CD (nhdsWithin 0 (Set.Ioi 0)) (nhds (m * gchem)) := by
    rw [← hfilter]
    simpa [hCD_def, hm_def] using hchem_lim
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
  -- PDE on the interior:
  -- `deriv² (lift (u s)) = G + χ₀ * chemDiv - R` on `(0,1)`.
  have hpde_eq : ∀ x ∈ Set.Ioo (0:ℝ) 1,
      deriv (deriv (intervalDomainLift (u s))) x = G x + p.χ₀ * CD x - R x := by
    intro x hx
    have hmem : (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint)
        ∈ intervalDomain.inside := hx
    have hpu := hsol.pde_u hs0 hsT hmem
    have e_td : intervalDomain.timeDeriv u s ⟨x, Set.Ioo_subset_Icc_self hx⟩ = G x := by
      change deriv (fun r => u r ⟨x, Set.Ioo_subset_Icc_self hx⟩) s = G x
      simp only [hG_def]; congr 1; funext r
      rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hx)]
    have e_lap : intervalDomain.laplacian (u s)
        ⟨x, Set.Ioo_subset_Icc_self hx⟩
        = deriv (deriv (intervalDomainLift (u s))) x := rfl
    have e_cd : intervalDomain.chemotaxisDiv p (u s) (v s)
        ⟨x, Set.Ioo_subset_Icc_self hx⟩ = CD x := by
      rw [hCD_def, boundaryChemDivReal, dif_pos (Set.Ioo_subset_Icc_self hx)]
    have e_u : u s (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint)
        = intervalDomainLift (u s) x := by
      rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hx)]
    rw [e_td, e_lap, e_cd, e_u] at hpu
    rw [hR_def]
    linarith [hpu]
  -- `deriv² (lift (u s)) → V := G 0 + χ₀·m·gchem − R 0` along `0⁺`.
  set V : ℝ := G 0 + p.χ₀ * (m * gchem) - R 0 with hV_def
  have hCD_term : Tendsto (fun x => p.χ₀ * CD x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (p.χ₀ * (m * gchem))) :=
    hCD_lim.const_mul p.χ₀
  have hderiv2_lim : Tendsto (deriv (deriv (intervalDomainLift (u s))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds V) := by
    refine ((hG_cont.add hCD_term).sub hR_cont).congr' ?_
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
      ext z; simp [Set.mem_Icc, Set.mem_Ici, Set.mem_Iic]
    rw [hIcc_eq]
    exact Filter.inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds h01))
  -- `0` is a spatial argmin on `(0,1)`.
  have hbdd : BddBelow (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1) :=
    (isCompact_Icc.image_of_continuousOn hliftcont).bddBelow
  have hmin : ∀ x ∈ Set.Ioo (0:ℝ) 1,
      intervalDomainLift (u s) 0 ≤ intervalDomainLift (u s) x := by
    intro x hx
    rw [← hm_def]
    rw [hargmin]
    exact csInf_le hbdd (Set.mem_image_of_mem _ (Set.Ioo_subset_Icc_self hx))
  -- Boundary 2nd-derivative test ⇒ `0 ≤ V`.
  have hV_nonneg : 0 ≤ V :=
    boundary_min_deriv2_rlimit_nonneg h01 hwcont hmin hd1 hd2 hNeu0 hderiv2_lim
  -- Algebra at the endpoint.
  have hm_eq_sInf : m = sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1) := by
    rw [hm_def]
    exact hargmin
  have hm_nonneg : 0 ≤ m := by
    rw [hm_def, intervalDomainLift, dif_pos h0Icc]
    exact (hsol.u_pos' hs0 hsT).le
  have hm_le : m ≤ M' := by
    rw [hm_def, intervalDomainLift, dif_pos h0Icc]; exact hu_le _
  have hpow_le : m ^ p.α ≤ M' ^ p.α := Real.rpow_le_rpow hm_nonneg hm_le p.hα.le
  have hmpow_nn : 0 ≤ m ^ p.α := Real.rpow_nonneg hm_nonneg _
  have hflux_nn : 0 ≤ fluxCoeffConst p.β (p.ν * M' ^ p.γ) :=
    fluxCoeffConst_nonneg p.hβ (mul_nonneg p.hν.le (Real.rpow_nonneg hM' _))
  have hR0 : R 0 = m * (p.a - p.b * m ^ p.α) := by rw [hR_def, hm_def]
  have hgoal_G : deriv (fun r => intervalDomainLift (u r) 0) s = G 0 := rfl
  rw [hgoal_G, ← hm_eq_sInf]
  have hG0_ge : R 0 - p.χ₀ * (m * gchem) ≤ G 0 := by
    rw [hV_def] at hV_nonneg
    linarith
  have hR_lb : -(p.b * M' ^ p.α) * m ≤ R 0 := by
    rw [hR0]
    have h1 : 0 ≤ p.b * (m * M' ^ p.α - m * m ^ p.α) :=
      mul_nonneg p.hb (sub_nonneg.mpr (mul_le_mul_of_nonneg_left hpow_le hm_nonneg))
    have h3 : 0 ≤ m * p.a := mul_nonneg hm_nonneg p.ha
    nlinarith [h1, h3]
  have hchem_lb :
      -(|p.χ₀| * fluxCoeffConst p.β (p.ν * M' ^ p.γ)) * m
        ≤ -p.χ₀ * (m * gchem) := by
    have hterm_abs : |-p.χ₀ * (m * gchem)| ≤
        |p.χ₀| * fluxCoeffConst p.β (p.ν * M' ^ p.γ) * m := by
      rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg hm_nonneg]
      nlinarith [mul_nonneg (abs_nonneg p.χ₀) hm_nonneg,
        mul_nonneg (abs_nonneg p.χ₀) (abs_nonneg gchem)]
    have := (abs_le.mp hterm_abs).1
    nlinarith
  have hkey :
      -(|p.χ₀| * fluxCoeffConst p.β (p.ν * M' ^ p.γ) + p.b * M' ^ p.α) * m
        ≤ R 0 - p.χ₀ * (m * gchem) := by
    nlinarith [hR_lb, hchem_lb]
  linarith [hkey, hG0_ge]

/-- Compatibility wrapper retaining the former nonpositive-sensitivity
interface. -/
theorem hbdry_left_chi_nonpos_of_chemDiv_limit
    {p : CM2Params} {T s M' gchem : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (_hχ : p.χ₀ ≤ 0)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hs0 : 0 < s) (hsT : s < T) (hM' : 0 ≤ M')
    (hu_le : ∀ x : intervalDomainPoint, u s x ≤ M')
    (hargmin : intervalDomainLift (u s) 0
        = sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1))
    (hchem_lim : Tendsto (boundaryChemDivReal p (u s) (v s))
      (nhdsWithin 0 (Set.Ioo (0 : ℝ) 1))
      (nhds (intervalDomainLift (u s) 0 * gchem)))
    (hgchem : |gchem| ≤ fluxCoeffConst p.β (p.ν * M' ^ p.γ)) :
    -(|p.χ₀| * fluxCoeffConst p.β (p.ν * M' ^ p.γ) + p.b * M' ^ p.α)
        * sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1)
      ≤ deriv (fun r => intervalDomainLift (u r) 0) s :=
  hbdry_left_of_chemDiv_limit hsol hs0 hsT hM' hu_le hargmin hchem_lim hgchem

set_option maxHeartbeats 1600000 in
-- The right endpoint proof mirrors the left endpoint reducer, with the same
-- boundary limit and endpoint algebra budget.
/-- **Right endpoint min-point bound from a one-sided chemDiv factor bound.** -/
theorem hbdry_right_of_chemDiv_limit
    {p : CM2Params} {T s M' gchem : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hs0 : 0 < s) (hsT : s < T) (hM' : 0 ≤ M')
    (hu_le : ∀ x : intervalDomainPoint, u s x ≤ M')
    (hargmin : intervalDomainLift (u s) 1
        = sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1))
    (hchem_lim : Tendsto (boundaryChemDivReal p (u s) (v s))
      (nhdsWithin 1 (Set.Ioo (0 : ℝ) 1))
      (nhds (intervalDomainLift (u s) 1 * gchem)))
    (hgchem : |gchem| ≤ fluxCoeffConst p.β (p.ν * M' ^ p.γ)) :
    -(|p.χ₀| * fluxCoeffConst p.β (p.ν * M' ^ p.γ) + p.b * M' ^ p.α)
        * sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1)
      ≤ deriv (fun r => intervalDomainLift (u r) 1) s := by
  have htmem : s ∈ Set.Ioo (0:ℝ) T := ⟨hs0, hsT⟩
  obtain ⟨_, _, _, h6, h7, h8, _⟩ := hsol.regularity
  have hu_c2 : ContDiffOn ℝ 2 (intervalDomainLift (u s)) (Set.Icc (0:ℝ) 1) :=
    (h7 s htmem).1.1
  have hu_c2_Ioo : ContDiffOn ℝ 2 (intervalDomainLift (u s)) (Set.Ioo (0:ℝ) 1) :=
    hu_c2.mono Set.Ioo_subset_Icc_self
  have hliftcont : ContinuousOn (intervalDomainLift (u s)) (Set.Icc (0:ℝ) 1) :=
    hu_c2.continuousOn
  have hNeu1 : Tendsto (deriv (intervalDomainLift (u s)))
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := (h6 s htmem).1.2
  have h1Icc : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_refl _⟩
  have h01 : (0:ℝ) < 1 := by norm_num
  set G : ℝ → ℝ := fun x => deriv (fun r => intervalDomainLift (u r) x) s with hG_def
  set R : ℝ → ℝ := fun x => intervalDomainLift (u s) x
    * (p.a - p.b * (intervalDomainLift (u s) x) ^ p.α) with hR_def
  set CD : ℝ → ℝ := boundaryChemDivReal p (u s) (v s) with hCD_def
  set m : ℝ := intervalDomainLift (u s) 1 with hm_def
  -- Bridge `𝓝[Ioo 0 1] 1 = 𝓝[Iio 1] 1` for the left-limits.
  have hfilter : nhdsWithin (1:ℝ) (Set.Ioo 0 1) = nhdsWithin 1 (Set.Iio 1) :=
    nhdsWithin_Ioo_eq_nhdsLT h01
  have hCD_lim : Tendsto CD (nhdsWithin 1 (Set.Iio 1)) (nhds (m * gchem)) := by
    rw [← hfilter]
    simpa [hCD_def, hm_def] using hchem_lim
  -- `G` continuous at `1` along `1⁻` (conjunct 8).
  have hG_cont : Tendsto G (nhdsWithin 1 (Set.Iio 1)) (nhds (G 1)) := by
    have hmaps : Set.MapsTo (fun w => (s, w)) (Set.Icc (0:ℝ) 1)
        (Set.Ioo (0:ℝ) T ×ˢ Set.Icc (0:ℝ) 1) := fun w hw => ⟨htmem, hw⟩
    have hcomp : ContinuousOn G (Set.Icc (0:ℝ) 1) :=
      h8.1.comp (Continuous.continuousOn
        (by fun_prop : Continuous fun w : ℝ => (s, w))) hmaps
    rw [← hfilter]
    exact (hcomp 1 h1Icc).mono_left (nhdsWithin_mono 1 Set.Ioo_subset_Icc_self)
  -- reaction `R` continuous at `1` along `1⁻`.
  have hR_cont : Tendsto R (nhdsWithin 1 (Set.Iio 1)) (nhds (R 1)) := by
    have hRcontOn : ContinuousOn R (Set.Icc (0:ℝ) 1) :=
      hliftcont.mul (continuousOn_const.sub (continuousOn_const.mul
        (hliftcont.rpow_const (fun x _ => Or.inr p.hα.le))))
    rw [← hfilter]
    exact (hRcontOn 1 h1Icc).mono_left (nhdsWithin_mono 1 Set.Ioo_subset_Icc_self)
  have hpde_eq : ∀ x ∈ Set.Ioo (0:ℝ) 1,
      deriv (deriv (intervalDomainLift (u s))) x = G x + p.χ₀ * CD x - R x := by
    intro x hx
    have hmem : (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint)
        ∈ intervalDomain.inside := hx
    have hpu := hsol.pde_u hs0 hsT hmem
    have e_td : intervalDomain.timeDeriv u s ⟨x, Set.Ioo_subset_Icc_self hx⟩ = G x := by
      change deriv (fun r => u r ⟨x, Set.Ioo_subset_Icc_self hx⟩) s = G x
      simp only [hG_def]; congr 1; funext r
      rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hx)]
    have e_lap : intervalDomain.laplacian (u s)
        ⟨x, Set.Ioo_subset_Icc_self hx⟩
        = deriv (deriv (intervalDomainLift (u s))) x := rfl
    have e_cd : intervalDomain.chemotaxisDiv p (u s) (v s)
        ⟨x, Set.Ioo_subset_Icc_self hx⟩ = CD x := by
      rw [hCD_def, boundaryChemDivReal, dif_pos (Set.Ioo_subset_Icc_self hx)]
    have e_u : u s (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint)
        = intervalDomainLift (u s) x := by
      rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hx)]
    rw [e_td, e_lap, e_cd, e_u] at hpu
    rw [hR_def]
    linarith [hpu]
  -- `deriv² (lift (u s)) → V := G 1 + χ₀·m·gchem − R 1` along `1⁻`.
  set V : ℝ := G 1 + p.χ₀ * (m * gchem) - R 1 with hV_def
  have hCD_term : Tendsto (fun x => p.χ₀ * CD x)
      (nhdsWithin 1 (Set.Iio 1)) (nhds (p.χ₀ * (m * gchem))) :=
    hCD_lim.const_mul p.χ₀
  have hderiv2_lim : Tendsto (deriv (deriv (intervalDomainLift (u s))))
      (nhdsWithin 1 (Set.Iio 1)) (nhds V) := by
    refine ((hG_cont.add hCD_term).sub hR_cont).congr' ?_
    rw [← hfilter]
    filter_upwards [self_mem_nhdsWithin] with x hx using (hpde_eq x hx).symm
  have hd1 : ∀ x ∈ Set.Ioo (0:ℝ) 1,
      HasDerivAt (intervalDomainLift (u s)) (deriv (intervalDomainLift (u s)) x) x :=
    fun x hx => (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hu_c2_Ioo hx).1
  have hd2 : ∀ x ∈ Set.Ioo (0:ℝ) 1,
      HasDerivAt (deriv (intervalDomainLift (u s)))
        (deriv (deriv (intervalDomainLift (u s))) x) x :=
    fun x hx => (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hu_c2_Ioo hx).2
  have hwcont : ContinuousWithinAt (intervalDomainLift (u s)) (Set.Iic 1) 1 := by
    refine (hliftcont 1 h1Icc).mono_of_mem_nhdsWithin ?_
    have hIcc_eq : Set.Icc (0:ℝ) 1 = Set.Ici (0:ℝ) ∩ Set.Iic 1 := by
      ext z; simp [Set.mem_Icc, Set.mem_Ici, Set.mem_Iic]
    rw [hIcc_eq]
    exact Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds h01))
      self_mem_nhdsWithin
  have hbdd : BddBelow (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1) :=
    (isCompact_Icc.image_of_continuousOn hliftcont).bddBelow
  have hmin : ∀ x ∈ Set.Ioo (0:ℝ) 1,
      intervalDomainLift (u s) 1 ≤ intervalDomainLift (u s) x := by
    intro x hx
    rw [← hm_def]
    rw [hargmin]
    exact csInf_le hbdd (Set.mem_image_of_mem _ (Set.Ioo_subset_Icc_self hx))
  have hV_nonneg : 0 ≤ V :=
    boundary_min_deriv2_llimit_nonneg (η := 1) h01 hwcont
      (fun x hx => hmin x (by simpa using hx))
      (fun x hx => hd1 x (by simpa using hx))
      (fun x hx => hd2 x (by simpa using hx))
      hNeu1 hderiv2_lim
  have hm_eq_sInf : m = sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1) := by
    rw [hm_def]
    exact hargmin
  have hm_nonneg : 0 ≤ m := by
    rw [hm_def, intervalDomainLift, dif_pos h1Icc]
    exact (hsol.u_pos' hs0 hsT).le
  have hm_le : m ≤ M' := by
    rw [hm_def, intervalDomainLift, dif_pos h1Icc]; exact hu_le _
  have hpow_le : m ^ p.α ≤ M' ^ p.α := Real.rpow_le_rpow hm_nonneg hm_le p.hα.le
  have hmpow_nn : 0 ≤ m ^ p.α := Real.rpow_nonneg hm_nonneg _
  have hflux_nn : 0 ≤ fluxCoeffConst p.β (p.ν * M' ^ p.γ) :=
    fluxCoeffConst_nonneg p.hβ (mul_nonneg p.hν.le (Real.rpow_nonneg hM' _))
  have hR1 : R 1 = m * (p.a - p.b * m ^ p.α) := by rw [hR_def, hm_def]
  have hgoal_G : deriv (fun r => intervalDomainLift (u r) 1) s = G 1 := rfl
  rw [hgoal_G, ← hm_eq_sInf]
  have hG1_ge : R 1 - p.χ₀ * (m * gchem) ≤ G 1 := by
    rw [hV_def] at hV_nonneg
    linarith
  have hR_lb : -(p.b * M' ^ p.α) * m ≤ R 1 := by
    rw [hR1]
    have h1 : 0 ≤ p.b * (m * M' ^ p.α - m * m ^ p.α) :=
      mul_nonneg p.hb (sub_nonneg.mpr (mul_le_mul_of_nonneg_left hpow_le hm_nonneg))
    have h3 : 0 ≤ m * p.a := mul_nonneg hm_nonneg p.ha
    nlinarith [h1, h3]
  have hchem_lb :
      -(|p.χ₀| * fluxCoeffConst p.β (p.ν * M' ^ p.γ)) * m
        ≤ -p.χ₀ * (m * gchem) := by
    have hterm_abs : |-p.χ₀ * (m * gchem)| ≤
        |p.χ₀| * fluxCoeffConst p.β (p.ν * M' ^ p.γ) * m := by
      rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg hm_nonneg]
      nlinarith [mul_nonneg (abs_nonneg p.χ₀) hm_nonneg,
        mul_nonneg (abs_nonneg p.χ₀) (abs_nonneg gchem)]
    have := (abs_le.mp hterm_abs).1
    nlinarith
  have hkey :
      -(|p.χ₀| * fluxCoeffConst p.β (p.ν * M' ^ p.γ) + p.b * M' ^ p.α) * m
        ≤ R 1 - p.χ₀ * (m * gchem) := by
    nlinarith [hR_lb, hchem_lb]
  linarith [hkey, hG1_ge]

/-- Compatibility wrapper retaining the former nonpositive-sensitivity
interface. -/
theorem hbdry_right_chi_nonpos_of_chemDiv_limit
    {p : CM2Params} {T s M' gchem : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (_hχ : p.χ₀ ≤ 0)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hs0 : 0 < s) (hsT : s < T) (hM' : 0 ≤ M')
    (hu_le : ∀ x : intervalDomainPoint, u s x ≤ M')
    (hargmin : intervalDomainLift (u s) 1
        = sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1))
    (hchem_lim : Tendsto (boundaryChemDivReal p (u s) (v s))
      (nhdsWithin 1 (Set.Ioo (0 : ℝ) 1))
      (nhds (intervalDomainLift (u s) 1 * gchem)))
    (hgchem : |gchem| ≤ fluxCoeffConst p.β (p.ν * M' ^ p.γ)) :
    -(|p.χ₀| * fluxCoeffConst p.β (p.ν * M' ^ p.γ) + p.b * M' ^ p.α)
        * sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1)
      ≤ deriv (fun r => intervalDomainLift (u r) 1) s :=
  hbdry_right_of_chemDiv_limit hsol hs0 hsT hM' hu_le hargmin hchem_lim hgchem

end ShenWork.MinPersistenceAtoms

namespace ShenWork.MinPersistenceAtoms

/-- Left endpoint min-point bound, for arbitrary sensitivity sign, from the
packaged one-sided chemDiv residual. -/
theorem hbdry_left_of_chemDivLimit
    {p : CM2Params} {T s M' : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hChem : BoundaryChemDivLeftLimitBound p)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hs0 : 0 < s) (hsT : s < T) (hM' : 0 ≤ M')
    (hu_le : ∀ x : intervalDomainPoint, u s x ≤ M')
    (hargmin : intervalDomainLift (u s) 0 =
        sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1)) :
    -(|p.χ₀| * fluxCoeffConst p.β (p.ν * M' ^ p.γ) + p.b * M' ^ p.α)
        * sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1)
      ≤ deriv (fun r => intervalDomainLift (u r) 0) s := by
  rcases hChem hsol hs0 hsT hM' hu_le with ⟨gchem, hgchem, hlim⟩
  exact hbdry_left_of_chemDiv_limit
    hsol hs0 hsT hM' hu_le hargmin hlim hgchem

/-- Right endpoint analogue of `hbdry_left_of_chemDivLimit`. -/
theorem hbdry_right_of_chemDivLimit
    {p : CM2Params} {T s M' : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hChem : BoundaryChemDivRightLimitBound p)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hs0 : 0 < s) (hsT : s < T) (hM' : 0 ≤ M')
    (hu_le : ∀ x : intervalDomainPoint, u s x ≤ M')
    (hargmin : intervalDomainLift (u s) 1 =
        sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1)) :
    -(|p.χ₀| * fluxCoeffConst p.β (p.ν * M' ^ p.γ) + p.b * M' ^ p.α)
        * sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1)
      ≤ deriv (fun r => intervalDomainLift (u r) 1) s := by
  rcases hChem hsol hs0 hsT hM' hu_le with ⟨gchem, hgchem, hlim⟩
  exact hbdry_right_of_chemDiv_limit
    hsol hs0 hsT hM' hu_le hargmin hlim hgchem

/-- Left endpoint min-point bound from the packaged one-sided chemDiv residual. -/
theorem hbdry_left_chi_nonpos_of_chemDivLimit
    {p : CM2Params} {T s M' : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hχ : p.χ₀ ≤ 0)
    (hChem : BoundaryChemDivLeftLimitBound p)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hs0 : 0 < s) (hsT : s < T) (hM' : 0 ≤ M')
    (hu_le : ∀ x : intervalDomainPoint, u s x ≤ M')
    (hargmin : intervalDomainLift (u s) 0 =
        sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1)) :
    -(|p.χ₀| * fluxCoeffConst p.β (p.ν * M' ^ p.γ) + p.b * M' ^ p.α)
        * sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1)
      ≤ deriv (fun r => intervalDomainLift (u r) 0) s := by
  rcases hChem hsol hs0 hsT hM' hu_le with ⟨gchem, hgchem, hlim⟩
  exact hbdry_left_chi_nonpos_of_chemDiv_limit
    hχ hsol hs0 hsT hM' hu_le hargmin hlim hgchem

/-- Right endpoint min-point bound from the packaged one-sided chemDiv residual. -/
theorem hbdry_right_chi_nonpos_of_chemDivLimit
    {p : CM2Params} {T s M' : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hχ : p.χ₀ ≤ 0)
    (hChem : BoundaryChemDivRightLimitBound p)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hs0 : 0 < s) (hsT : s < T) (hM' : 0 ≤ M')
    (hu_le : ∀ x : intervalDomainPoint, u s x ≤ M')
    (hargmin : intervalDomainLift (u s) 1 =
        sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1)) :
    -(|p.χ₀| * fluxCoeffConst p.β (p.ν * M' ^ p.γ) + p.b * M' ^ p.α)
        * sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1)
      ≤ deriv (fun r => intervalDomainLift (u r) 1) s := by
  rcases hChem hsol hs0 hsT hM' hu_le with ⟨gchem, hgchem, hlim⟩
  exact hbdry_right_chi_nonpos_of_chemDiv_limit
    hχ hsol hs0 hsT hM' hu_le hargmin hlim hgchem

end ShenWork.MinPersistenceAtoms

namespace ShenWork.Paper2.BFormPositiveDatumLocal

/-- Packaged left endpoint chemDiv limit residual implies the windowed left
boundary min-persistence residual. -/
theorem boundaryMinPersistenceWindowLeftBound_of_chemDivLimit
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hChem : ShenWork.MinPersistenceAtoms.BoundaryChemDivLeftLimitBound p) :
    BoundaryMinPersistenceWindowLeftBound p := by
  intro u₀ hu₀ M hM hbnd t₁ T u v ht₁ hsol htr s hs harg
  have hs0 : 0 < s := lt_of_lt_of_le (by linarith : (0 : ℝ) < t₁ / 2) hs.1
  have hsT : s < T := hs.2
  have hMpos : (0 : ℝ) ≤ SupNormBridge.regimeBound p M :=
    (SupNormBridge.regimeBound_pos p hM).le
  have hsup :=
    ShenWork.MinPersistenceAtoms.hSupNorm_of_regime
      p hχ ha hb hu₀ hM hbnd ht₁ hsol.T_pos hsol htr
  have hu_le : ∀ x : intervalDomainPoint, u s x ≤ SupNormBridge.regimeBound p M := by
    intro x
    have hb_abs := hsup s hs x.1
    have hlift : intervalDomainLift (u s) x.1 = u s x := by
      simp only [intervalDomainLift]
      exact dif_pos x.2
    rw [hlift] at hb_abs
    exact (abs_le.mp hb_abs).2
  exact ShenWork.MinPersistenceAtoms.hbdry_left_chi_nonpos_of_chemDivLimit
    hχ hChem hsol hs0 hsT hMpos hu_le harg

/-- Packaged right endpoint chemDiv limit residual implies the windowed right
boundary min-persistence residual. -/
theorem boundaryMinPersistenceWindowRightBound_of_chemDivLimit
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hChem : ShenWork.MinPersistenceAtoms.BoundaryChemDivRightLimitBound p) :
    BoundaryMinPersistenceWindowRightBound p := by
  intro u₀ hu₀ M hM hbnd t₁ T u v ht₁ hsol htr s hs harg
  have hs0 : 0 < s := lt_of_lt_of_le (by linarith : (0 : ℝ) < t₁ / 2) hs.1
  have hsT : s < T := hs.2
  have hMpos : (0 : ℝ) ≤ SupNormBridge.regimeBound p M :=
    (SupNormBridge.regimeBound_pos p hM).le
  have hsup :=
    ShenWork.MinPersistenceAtoms.hSupNorm_of_regime
      p hχ ha hb hu₀ hM hbnd ht₁ hsol.T_pos hsol htr
  have hu_le : ∀ x : intervalDomainPoint, u s x ≤ SupNormBridge.regimeBound p M := by
    intro x
    have hb_abs := hsup s hs x.1
    have hlift : intervalDomainLift (u s) x.1 = u s x := by
      simp only [intervalDomainLift]
      exact dif_pos x.2
    rw [hlift] at hb_abs
    exact (abs_le.mp hb_abs).2
  exact ShenWork.MinPersistenceAtoms.hbdry_right_chi_nonpos_of_chemDivLimit
    hχ hChem hsol hs0 hsT hMpos hu_le harg

/-- Packaged endpoint chemDiv limit residuals imply the split windowed boundary
min-persistence residuals. -/
theorem boundaryMinPersistenceWindowEndpointBounds_of_chemDivEndpointLimits
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hChem : ShenWork.MinPersistenceAtoms.BoundaryChemDivEndpointLimitBounds p) :
    BoundaryMinPersistenceWindowEndpointBounds p where
  left := boundaryMinPersistenceWindowLeftBound_of_chemDivLimit p hχ ha hb hChem.left
  right := boundaryMinPersistenceWindowRightBound_of_chemDivLimit p hχ ha hb hChem.right

/-- Packaged endpoint chemDiv limit residuals imply the combined windowed
boundary min-persistence residual. -/
theorem boundaryMinPersistenceWindowBound_of_chemDivEndpointLimits
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hChem : ShenWork.MinPersistenceAtoms.BoundaryChemDivEndpointLimitBounds p) :
    BoundaryMinPersistenceWindowBound p :=
  boundaryMinPersistenceWindowBound_of_endpointBounds
    (boundaryMinPersistenceWindowEndpointBounds_of_chemDivEndpointLimits
      p hχ ha hb hChem)

end ShenWork.Paper2.BFormPositiveDatumLocal
