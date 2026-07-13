/-
  One-sided endpoint limits of the faithful general-m chemotaxis divergence.

  The literal divergence differentiates a zero extension, so endpoint values
  are not the physical boundary values.  We identify it on the open interval
  with a continuous closed-interval product-rule representative and take the
  one-sided limits of that representative.
-/
import ShenWork.Paper2.IntervalDomainMMinPointSolution
import ShenWork.Paper2.IntervalDomainMFlux

open ShenWork.IntervalDomain ShenWork.Paper2 Set Filter Topology

noncomputable section

namespace ShenWork.Paper2.IntervalDomainMMinPersistence

/-- Real-line representative of the faithful general-`m` divergence, used
only under one-sided interior filters. -/
def boundaryChemDivMReal
    (p : CM2Params) (u v : intervalDomainPoint → ℝ) (y : ℝ) : ℝ :=
  if hy : y ∈ Set.Icc (0 : ℝ) 1 then
    intervalDomainChemotaxisDivM p u v ⟨y, hy⟩
  else 0

/-- Closed-interval physical product-rule representative of `Q_x` for
`Q = u^m v_x (1+v)^(-beta)`. -/
def classicalChemDivMPhysicalRep (p : CM2Params)
    (u v : ℝ → intervalDomainPoint → ℝ) (t x : ℝ) : ℝ :=
  let U := intervalDomainLift (u t)
  let V := intervalDomainLift (v t)
  (p.m * U x ^ (p.m - 1) * deriv U x) * deriv V x *
      (1 + V x) ^ (-p.β) +
    U x ^ p.m * (p.μ * V x - p.ν * U x ^ p.γ) *
      (1 + V x) ^ (-p.β) -
    p.β * U x ^ p.m * deriv V x ^ 2 *
      (1 + V x) ^ (-p.β - 1)

private theorem lift_eq_interior (f : intervalDomainPoint → ℝ)
    {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    intervalDomainLift f y = f ⟨y, Set.Ioo_subset_Icc_self hy⟩ := by
  rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hy)]

/-- On the open interval the literal faithful divergence equals the physical
closed-interval representative. -/
theorem intervalDomainMChemotaxisDiv_eq_physicalRep_interior
    {p : CM2Params} {T t x : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    intervalDomainChemotaxisDivM p (u t) (v t)
        ⟨x, Set.Ioo_subset_Icc_self hx⟩ =
      classicalChemDivMPhysicalRep p u v t x := by
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let V : ℝ → ℝ := intervalDomainLift (v t)
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hU2 : ContDiffOn ℝ 2 U (Set.Ioo (0 : ℝ) 1) :=
    (hsol.regularity.1 t ht).1
  have hV2 : ContDiffOn ℝ 2 V (Set.Ioo (0 : ℝ) 1) :=
    (hsol.regularity.1 t ht).2
  have hU := (ShenWork.MinPersistenceAtoms.contDiffOn_two_hasDerivAt_pair
    isOpen_Ioo hU2 hx).1
  have hVpair := ShenWork.MinPersistenceAtoms.contDiffOn_two_hasDerivAt_pair
    isOpen_Ioo hV2 hx
  have hUpos : 0 < U x := by
    dsimp [U]
    rw [lift_eq_interior (u t) hx]
    exact hsol.u_pos' ht0 htT
  have hVnn : 0 ≤ V x := by
    dsimp [V]
    rw [lift_eq_interior (v t) hx]
    exact hsol.v_nonneg ht0 htT
  have hbase : 0 < 1 + V x := by linarith
  have hUpow := hU.rpow_const (p := p.m) (Or.inl hUpos.ne')
  have hPeq : (fun y => deriv V y / (1 + V y) ^ p.β) =
      (fun y => deriv V y * (1 + V y) ^ (-p.β)) := by
    funext y
    have hypos : 0 < 1 + V y := by
      have hvnn : 0 ≤ V y := by
        dsimp [V]
        unfold intervalDomainLift
        split_ifs
        · exact hsol.v_nonneg ht0 htT
        · exact le_rfl
      linarith
    rw [Real.rpow_neg hypos.le, div_eq_mul_inv]
  have hP : HasDerivAt
      (fun y => deriv V y / (1 + V y) ^ p.β)
      (-p.β * (1 + V x) ^ (-p.β - 1) * deriv V x ^ 2 +
        (1 + V x) ^ (-p.β) * deriv (deriv V) x) x := by
    rw [hPeq]
    exact ShenWork.MinPersistenceAtoms.flux_integrand_hasDerivAt
      hVpair.1 hVpair.2 hbase
  have hmul : HasDerivAt
      (fun y => U y ^ p.m * (deriv V y / (1 + V y) ^ p.β))
      ((deriv U x * p.m * U x ^ (p.m - 1)) *
          (deriv V x / (1 + V x) ^ p.β) +
        U x ^ p.m *
          (-p.β * (1 + V x) ^ (-p.β - 1) * deriv V x ^ 2 +
            (1 + V x) ^ (-p.β) * deriv (deriv V) x)) x := by
    simpa only [Pi.mul_apply] using hUpow.mul hP
  have hpv := hsol.pde_v ht0 htT
    (show (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint) ∈
      intervalDomainM.inside from hx)
  have hvxx : deriv (deriv V) x = p.μ * V x - p.ν * U x ^ p.γ := by
    dsimp [U, V]
    rw [lift_eq_interior (v t) hx, lift_eq_interior (u t) hx]
    have hlap : intervalDomainM.laplacian (v t)
        (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint) =
          deriv (deriv (intervalDomainLift (v t))) x := rfl
    rw [hlap] at hpv
    linarith [hpv]
  have hden : deriv V x / (1 + V x) ^ p.β =
      deriv V x * (1 + V x) ^ (-p.β) := by
    rw [Real.rpow_neg hbase.le, div_eq_mul_inv]
  unfold intervalDomainChemotaxisDivM
  have hfun :
      (fun y => intervalDomainLift (u t) y ^ p.m *
          deriv (intervalDomainLift (v t)) y /
            (1 + intervalDomainLift (v t) y) ^ p.β) =
        (fun y => U y ^ p.m *
          (deriv V y / (1 + V y) ^ p.β)) := by
    funext y
    dsimp [U, V]
    rw [mul_div_assoc]
  rw [hfun, hmul.deriv, hvxx, hden]
  simp only [classicalChemDivMPhysicalRep]
  dsimp [U, V]
  ring

/-- The physical representative is continuous on the closed spatial
interval at every positive classical time. -/
theorem classicalChemDivMPhysicalRep_continuousOn_Icc
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    ContinuousOn (classicalChemDivMPhysicalRep p u v t)
      (Set.Icc (0 : ℝ) 1) := by
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let V : ℝ → ℝ := intervalDomainLift (v t)
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hclosed := hsol.regularity.2.2.2.2.1 t ht
  have hU2 : ContDiffOn ℝ 2 U (Set.Icc (0 : ℝ) 1) := hclosed.1.1
  have hV2 : ContDiffOn ℝ 2 V (Set.Icc (0 : ℝ) 1) := hclosed.2.1
  have hU : ContinuousOn U (Set.Icc (0 : ℝ) 1) := hU2.continuousOn
  have hV : ContinuousOn V (Set.Icc (0 : ℝ) 1) := hV2.continuousOn
  have hdU : ContDiffOn ℝ 1 (deriv U) (Set.Icc (0 : ℝ) 1) := by
    exact ShenWork.Paper2.IntervalDomainM.deriv_lift_contDiffOn_one_Icc
      hU2
      (ShenWork.Paper2.IntervalDomainM.derivWithin_left_zero
        hsol ht0 htT u (Or.inl rfl))
      (ShenWork.Paper2.IntervalDomainM.derivWithin_right_zero
        hsol ht0 htT u (Or.inl rfl))
  have hdV : ContDiffOn ℝ 1 (deriv V) (Set.Icc (0 : ℝ) 1) := by
    exact ShenWork.Paper2.IntervalDomainM.deriv_lift_contDiffOn_one_Icc
      hV2
      (ShenWork.Paper2.IntervalDomainM.derivWithin_left_zero
        hsol ht0 htT v (Or.inr rfl))
      (ShenWork.Paper2.IntervalDomainM.derivWithin_right_zero
        hsol ht0 htT v (Or.inr rfl))
  have hUpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < U x := by
    intro x hx
    dsimp [U]
    simpa [intervalDomainLift, hx] using
      hsol.u_pos' (x := (⟨x, hx⟩ : intervalDomainPoint)) ht0 htT
  have hVnn : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ V x := by
    intro x hx
    dsimp [V]
    simpa [intervalDomainLift, hx] using
      hsol.v_nonneg (x := (⟨x, hx⟩ : intervalDomainPoint)) ht0 htT
  have hUm : ContinuousOn (fun x => U x ^ p.m) (Set.Icc (0 : ℝ) 1) :=
    hU.rpow_const (fun x hx => Or.inl (hUpos x hx).ne')
  have hUm1 : ContinuousOn (fun x => U x ^ (p.m - 1))
      (Set.Icc (0 : ℝ) 1) :=
    hU.rpow_const (fun x hx => Or.inl (hUpos x hx).ne')
  have hUg : ContinuousOn (fun x => U x ^ p.γ) (Set.Icc (0 : ℝ) 1) :=
    hU.rpow_const (fun _ _ => Or.inr p.hγ.le)
  have hbase : ContinuousOn (fun x => 1 + V x) (Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.add hV
  have hden : ContinuousOn (fun x => (1 + V x) ^ (-p.β))
      (Set.Icc (0 : ℝ) 1) :=
    hbase.rpow_const (fun x hx => Or.inl (by
      have := hVnn x hx
      linarith))
  have hden1 : ContinuousOn (fun x => (1 + V x) ^ (-p.β - 1))
      (Set.Icc (0 : ℝ) 1) :=
    hbase.rpow_const (fun x hx => Or.inl (by
      have := hVnn x hx
      linarith))
  have hphysical : ContinuousOn
      (fun x => p.μ * V x - p.ν * U x ^ p.γ) (Set.Icc (0 : ℝ) 1) :=
    (continuousOn_const.mul hV).sub (continuousOn_const.mul hUg)
  have hterm1 : ContinuousOn
      (fun x => (p.m * U x ^ (p.m - 1) * deriv U x) * deriv V x *
        (1 + V x) ^ (-p.β)) (Set.Icc (0 : ℝ) 1) :=
    (((continuousOn_const.mul hUm1).mul hdU.continuousOn).mul
      hdV.continuousOn).mul hden
  have hterm2 : ContinuousOn
      (fun x => U x ^ p.m * (p.μ * V x - p.ν * U x ^ p.γ) *
        (1 + V x) ^ (-p.β)) (Set.Icc (0 : ℝ) 1) :=
    (hUm.mul hphysical).mul hden
  have hterm3 : ContinuousOn
      (fun x => p.β * U x ^ p.m * deriv V x ^ 2 *
        (1 + V x) ^ (-p.β - 1)) (Set.Icc (0 : ℝ) 1) :=
    (((continuousOn_const.mul hUm).mul (hdV.continuousOn.pow 2)).mul hden1)
  simpa [classicalChemDivMPhysicalRep, U, V] using
    (hterm1.add hterm2).sub hterm3

/-- Closed-interval bound for the elliptic reaction coefficient. -/
theorem vReactionM_abs_le_Icc
    {p : CM2Params} {T t M : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) (hM : 0 ≤ M)
    (hu_le : ∀ x : intervalDomainPoint, u t x ≤ M) :
    ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |p.μ * intervalDomainLift (v t) y -
        p.ν * intervalDomainLift (u t) y ^ p.γ| ≤
          2 * (p.ν * M ^ p.γ) := by
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  obtain ⟨h3, _, _, h6, h7, _, _⟩ := hsol.regularity
  have hU2c := (h7 t ht).1.1
  have hV2c := (h7 t ht).2.1
  have hUcont := hU2c.continuousOn
  have hVcont := hV2c.continuousOn
  have hVnn : ∀ y, 0 ≤ intervalDomainLift (v t) y := by
    intro y
    unfold intervalDomainLift
    split_ifs
    · exact hsol.v_nonneg ht0 htT
    · exact le_rfl
  have hUnn : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      0 ≤ intervalDomainLift (u t) y := by
    intro y hy
    rw [lift_eq_interior (u t) hy]
    exact (hsol.u_pos' ht0 htT).le
  have hUle : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      intervalDomainLift (u t) y ≤ M := by
    intro y hy
    rw [lift_eq_interior (u t) hy]
    exact hu_le _
  have hPDE : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      deriv (deriv (intervalDomainLift (v t))) y =
        p.μ * intervalDomainLift (v t) y -
          p.ν * intervalDomainLift (u t) y ^ p.γ := by
    intro y hy
    have hpv := hsol.pde_v ht0 htT
      (show (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint) ∈
        intervalDomainM.inside from hy)
    rw [lift_eq_interior (v t) hy, lift_eq_interior (u t) hy]
    have hlap : intervalDomainM.laplacian (v t)
        (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint) =
          deriv (deriv (intervalDomainLift (v t))) y := rfl
    rw [hlap] at hpv
    linarith [hpv]
  have hvb := ShenWork.MinPersistenceAtoms.v_slice_coeff_bounds
    (p := p) (u := u t) (v := v t) (M' := M)
    hM (h3 t ht).2 hVcont hVnn hUnn hUle hPDE
      (h6 t ht).2.1 (h6 t ht).2.2
  let F : ℝ → ℝ := fun y =>
    p.μ * intervalDomainLift (v t) y -
      p.ν * intervalDomainLift (u t) y ^ p.γ
  have hUpos : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (u t) y := by
    intro y hy
    simpa [intervalDomainLift, hy] using
      hsol.u_pos' (x := (⟨y, hy⟩ : intervalDomainPoint)) ht0 htT
  have hFcont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
    exact (continuousOn_const.mul hVcont).sub
      (continuousOn_const.mul
        (hUcont.rpow_const (fun y hy => Or.inl (hUpos y hy).ne')))
  have hclosure : closure (Set.Ioo (0 : ℝ) 1) = Set.Icc (0 : ℝ) 1 :=
    closure_Ioo (by norm_num)
  intro y hy
  apply le_on_closure (s := Set.Ioo (0 : ℝ) 1)
    (f := fun z => |F z|)
    (g := fun _ => 2 * (p.ν * M ^ p.γ))
  · intro z hz
    simpa [F, hPDE z hz] using hvb.2 z hz
  · simpa [hclosure] using hFcont.abs
  · exact continuousOn_const
  · simpa [hclosure] using hy

private theorem boundaryChemDivMReal_eq_physicalRep_eventually
    {p : CM2Params} {T t e : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    (fun y => boundaryChemDivMReal p (u t) (v t) y) =ᶠ[
      nhdsWithin e (Set.Ioo (0 : ℝ) 1)]
        (classicalChemDivMPhysicalRep p u v t) := by
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp only [boundaryChemDivMReal, dif_pos (Set.Ioo_subset_Icc_self hy)]
  exact intervalDomainMChemotaxisDiv_eq_physicalRep_interior
    hsol ht0 htT hy

/-- Left endpoint factor/bound and one-sided physical divergence limit. -/
theorem boundaryChemDivM_left_limit_factor
    {p : CM2Params} {T t M : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hm : 1 ≤ p.m)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) (hM : 0 ≤ M)
    (hu_le : ∀ x : intervalDomainPoint, u t x ≤ M) :
    ∃ g : ℝ,
      |g| ≤ M ^ (p.m - 1) *
        ShenWork.MinPersistenceAtoms.fluxCoeffConst p.β (p.ν * M ^ p.γ) ∧
      Tendsto (boundaryChemDivMReal p (u t) (v t))
        (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1))
        (nhds (intervalDomainLift (u t) 0 * g)) := by
  let U0 := intervalDomainLift (u t) 0
  let V0 := intervalDomainLift (v t) 0
  let r := p.μ * V0 - p.ν * U0 ^ p.γ
  let G := -p.β * (1 + V0) ^ (-p.β - 1) * (0 : ℝ) ^ 2 +
    (1 + V0) ^ (-p.β) * r
  let g := U0 ^ (p.m - 1) * G
  refine ⟨g, ?_, ?_⟩
  · have hU0 : 0 < U0 := by
      dsimp [U0]
      simpa [intervalDomainLift] using
        hsol.u_pos' (x := (⟨0, ⟨le_rfl, zero_le_one⟩⟩ :
          intervalDomainPoint)) ht0 htT
    have hU0le : U0 ≤ M := by
      dsimp [U0]
      simpa [intervalDomainLift] using
        hu_le (⟨0, ⟨le_rfl, zero_le_one⟩⟩ : intervalDomainPoint)
    have hV0 : 0 ≤ V0 := by
      dsimp [V0]
      simpa [intervalDomainLift] using
        hsol.v_nonneg (x := (⟨0, ⟨le_rfl, zero_le_one⟩⟩ :
          intervalDomainPoint)) ht0 htT
    have hr := vReactionM_abs_le_Icc hsol ht0 htT hM hu_le 0
      ⟨le_rfl, zero_le_one⟩
    have hB : 0 ≤ p.ν * M ^ p.γ :=
      mul_nonneg p.hν.le (Real.rpow_nonneg hM _)
    have hG : |G| ≤ ShenWork.MinPersistenceAtoms.fluxCoeffConst p.β
        (p.ν * M ^ p.γ) := by
      exact ShenWork.MinPersistenceAtoms.flux_coeff_bound
        p.hβ hB hV0 (by simp [hB]) (by simpa [r] using hr)
    have hpow : U0 ^ (p.m - 1) ≤ M ^ (p.m - 1) :=
      Real.rpow_le_rpow hU0.le hU0le (by linarith)
    rw [show |g| = U0 ^ (p.m - 1) * |G| by
      simp [g, abs_of_nonneg (Real.rpow_nonneg hU0.le _)]]
    exact mul_le_mul hpow hG (abs_nonneg G) (Real.rpow_nonneg hM _)
  · have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
    have hclosed := hsol.regularity.2.2.2.2.1 t ht
    have hdu : deriv (intervalDomainLift (u t)) 0 = 0 := hclosed.1.2.1
    have hdv : deriv (intervalDomainLift (v t)) 0 = 0 := hclosed.2.2.1
    have hU0 : 0 < U0 := by
      dsimp [U0]
      simpa [intervalDomainLift] using
        hsol.u_pos' (x := (⟨0, ⟨le_rfl, zero_le_one⟩⟩ :
          intervalDomainPoint)) ht0 htT
    have hfac : classicalChemDivMPhysicalRep p u v t 0 = U0 * g := by
      simp only [classicalChemDivMPhysicalRep]
      dsimp [U0, V0, r, G, g]
      have hpow : intervalDomainLift (u t) 0 ^ p.m =
          intervalDomainLift (u t) 0 ^ (p.m - 1) *
            intervalDomainLift (u t) 0 :=
        rpow_eq_rpow_sub_one_mul hU0
      rw [hdu, hdv, hpow]
      ring
    have hcont := classicalChemDivMPhysicalRep_continuousOn_Icc
      hsol ht0 htT
    have hlim : Tendsto (classicalChemDivMPhysicalRep p u v t)
        (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1))
        (nhds (classicalChemDivMPhysicalRep p u v t 0)) :=
      (hcont 0 ⟨le_rfl, zero_le_one⟩).mono_left
        (nhdsWithin_mono 0 Set.Ioo_subset_Icc_self)
    rw [hfac] at hlim
    simpa [U0, g] using Filter.Tendsto.congr'
      (boundaryChemDivMReal_eq_physicalRep_eventually hsol ht0 htT).symm hlim

/-- Right endpoint analogue of `boundaryChemDivM_left_limit_factor`. -/
theorem boundaryChemDivM_right_limit_factor
    {p : CM2Params} {T t M : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hm : 1 ≤ p.m)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) (hM : 0 ≤ M)
    (hu_le : ∀ x : intervalDomainPoint, u t x ≤ M) :
    ∃ g : ℝ,
      |g| ≤ M ^ (p.m - 1) *
        ShenWork.MinPersistenceAtoms.fluxCoeffConst p.β (p.ν * M ^ p.γ) ∧
      Tendsto (boundaryChemDivMReal p (u t) (v t))
        (nhdsWithin (1 : ℝ) (Set.Ioo (0 : ℝ) 1))
        (nhds (intervalDomainLift (u t) 1 * g)) := by
  let U1 := intervalDomainLift (u t) 1
  let V1 := intervalDomainLift (v t) 1
  let r := p.μ * V1 - p.ν * U1 ^ p.γ
  let G := -p.β * (1 + V1) ^ (-p.β - 1) * (0 : ℝ) ^ 2 +
    (1 + V1) ^ (-p.β) * r
  let g := U1 ^ (p.m - 1) * G
  refine ⟨g, ?_, ?_⟩
  · have hU1 : 0 < U1 := by
      dsimp [U1]
      simpa [intervalDomainLift] using
        hsol.u_pos' (x := (⟨1, ⟨zero_le_one, le_rfl⟩⟩ :
          intervalDomainPoint)) ht0 htT
    have hU1le : U1 ≤ M := by
      dsimp [U1]
      simpa [intervalDomainLift] using
        hu_le (⟨1, ⟨zero_le_one, le_rfl⟩⟩ : intervalDomainPoint)
    have hV1 : 0 ≤ V1 := by
      dsimp [V1]
      simpa [intervalDomainLift] using
        hsol.v_nonneg (x := (⟨1, ⟨zero_le_one, le_rfl⟩⟩ :
          intervalDomainPoint)) ht0 htT
    have hr := vReactionM_abs_le_Icc hsol ht0 htT hM hu_le 1
      ⟨zero_le_one, le_rfl⟩
    have hB : 0 ≤ p.ν * M ^ p.γ :=
      mul_nonneg p.hν.le (Real.rpow_nonneg hM _)
    have hG : |G| ≤ ShenWork.MinPersistenceAtoms.fluxCoeffConst p.β
        (p.ν * M ^ p.γ) := by
      exact ShenWork.MinPersistenceAtoms.flux_coeff_bound
        p.hβ hB hV1 (by simp [hB]) (by simpa [r] using hr)
    have hpow : U1 ^ (p.m - 1) ≤ M ^ (p.m - 1) :=
      Real.rpow_le_rpow hU1.le hU1le (by linarith)
    rw [show |g| = U1 ^ (p.m - 1) * |G| by
      simp [g, abs_of_nonneg (Real.rpow_nonneg hU1.le _)]]
    exact mul_le_mul hpow hG (abs_nonneg G) (Real.rpow_nonneg hM _)
  · have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
    have hclosed := hsol.regularity.2.2.2.2.1 t ht
    have hdu : deriv (intervalDomainLift (u t)) 1 = 0 := hclosed.1.2.2
    have hdv : deriv (intervalDomainLift (v t)) 1 = 0 := hclosed.2.2.2
    have hU1 : 0 < U1 := by
      dsimp [U1]
      simpa [intervalDomainLift] using
        hsol.u_pos' (x := (⟨1, ⟨zero_le_one, le_rfl⟩⟩ :
          intervalDomainPoint)) ht0 htT
    have hfac : classicalChemDivMPhysicalRep p u v t 1 = U1 * g := by
      simp only [classicalChemDivMPhysicalRep]
      dsimp [U1, V1, r, G, g]
      have hpow : intervalDomainLift (u t) 1 ^ p.m =
          intervalDomainLift (u t) 1 ^ (p.m - 1) *
            intervalDomainLift (u t) 1 :=
        rpow_eq_rpow_sub_one_mul hU1
      rw [hdu, hdv, hpow]
      ring
    have hcont := classicalChemDivMPhysicalRep_continuousOn_Icc
      hsol ht0 htT
    have hlim : Tendsto (classicalChemDivMPhysicalRep p u v t)
        (nhdsWithin (1 : ℝ) (Set.Ioo (0 : ℝ) 1))
        (nhds (classicalChemDivMPhysicalRep p u v t 1)) :=
      (hcont 1 ⟨zero_le_one, le_rfl⟩).mono_left
        (nhdsWithin_mono 1 Set.Ioo_subset_Icc_self)
    rw [hfac] at hlim
    simpa [U1, g] using Filter.Tendsto.congr'
      (boundaryChemDivMReal_eq_physicalRep_eventually hsol ht0 htT).symm hlim

section AxiomAudit

#print axioms intervalDomainMChemotaxisDiv_eq_physicalRep_interior
#print axioms classicalChemDivMPhysicalRep_continuousOn_Icc
#print axioms vReactionM_abs_le_Icc
#print axioms boundaryChemDivM_left_limit_factor
#print axioms boundaryChemDivM_right_limit_factor

end AxiomAudit

end ShenWork.Paper2.IntervalDomainMMinPersistence
