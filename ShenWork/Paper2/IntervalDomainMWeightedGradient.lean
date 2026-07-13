import ShenWork.Paper2.IntervalDomainMMass
import ShenWork.Paper2.IntervalDomainWeightedGradientEstimate
import ShenWork.Paper3.IntervalDomainPersistenceElliptic

/-!
# Weighted elliptic gradient estimate for the faithful interval model

Only the elliptic equation for `v`, positivity, and classical spatial
regularity enter Proposition 2.2.  This file proves the required weighted
gradient half directly for `intervalDomainM`; it does not transport the
parabolic equation through the legacy linear-flux model.
-/

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain
open ShenWork.IntervalEllipticCharacterization

noncomputable section

namespace ShenWork.Paper2.IntervalDomainM

theorem v_xx_eq_reaction_lift
    {p : CM2Params} {T t x : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) (hx0 : 0 < x) (hx1 : x < 1) :
    deriv (deriv (intervalDomainLift (v t))) x =
      p.μ * intervalDomainLift (v t) x -
        p.ν * (intervalDomainLift (u t) x) ^ p.γ := by
  let X : intervalDomain.Point := ⟨x, ⟨hx0.le, hx1.le⟩⟩
  have hXin : X ∈ intervalDomainM.inside := ⟨hx0, hx1⟩
  have hpde := hsol.pde_v ht0 htT hXin
  have hL : intervalDomainM.laplacian (v t) X =
      p.μ * v t X - p.ν * (u t X) ^ p.γ := by linarith
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx0.le, hx1.le⟩
  simpa [intervalDomainM, intervalDomainLaplacian, intervalDomainLift, hxIcc, X]
    using hL

theorem exists_uniform_u_lower_at_time
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    ∃ δ > 0, ∀ x : intervalDomain.Point, δ ≤ u t x := by
  let U : ℝ → ℝ := intervalDomainLift (u t)
  have hcont : ContinuousOn U (Set.Icc (0 : ℝ) 1) := by
    simpa [U] using solution_lift_continuousOn_Icc hsol ⟨ht0, htT⟩
  obtain ⟨x0, hx0, hmin⟩ :=
    isCompact_Icc.exists_isMinOn ⟨0, Set.left_mem_Icc.mpr zero_le_one⟩ hcont
  let δ := U x0
  have hδ : 0 < δ := by
    dsimp [δ]
    exact solution_lift_pos_Icc hsol ⟨ht0, htT⟩ x0 hx0
  refine ⟨δ, hδ, ?_⟩
  intro x
  have hx := hmin x.2
  change U x0 ≤ U x.1 at hx
  simpa [δ, U, intervalDomainLift, x.2] using hx

theorem classical_v_lower_of_u_lower_at_time
    {p : CM2Params} {T t δ : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hδ : 0 < δ) (hu : ∀ x : intervalDomain.Point, δ ≤ u t x) :
    ∀ x : intervalDomain.Point, p.ν / p.μ * δ ^ p.γ ≤ v t x := by
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let V : ℝ → ℝ := intervalDomainLift (v t)
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hV2 : ContDiffOn ℝ 2 V (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.1
  have hVcont : ContinuousOn V (Set.Icc (0 : ℝ) 1) := hV2.continuousOn
  have hd2 : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (deriv V) y := by
    intro y hy
    exact ((ShenWork.MinPersistenceAtoms.contDiffOn_two_hasDerivAt_pair
      isOpen_Ioo (hV2.mono Set.Ioo_subset_Icc_self) hy).2).differentiableAt
  have hPDE : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      deriv (deriv V) y = p.μ * V y - p.ν * (U y) ^ p.γ := by
    intro y hy
    simpa [U, V] using v_xx_eq_reaction_lift hsol ht0 htT hy.1 hy.2
  have hSrc : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      p.ν * δ ^ p.γ ≤ p.ν * (U y) ^ p.γ := by
    intro y hy
    have hyu : δ ≤ U y := by
      simpa [U, intervalDomainLift, Set.Ioo_subset_Icc_self hy] using
        hu (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomain.Point)
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hδ.le hyu p.hγ.le) p.hν.le
  have hneu := hsol.regularity.2.2.2.1 t ht
  have hlower := ShenWork.Paper3.interval_elliptic_lower_bound_of_source_ge
    (V := V) (Src := fun y => p.ν * (U y) ^ p.γ)
    (mu := p.μ) (c0 := p.ν * δ ^ p.γ)
    p.hμ hVcont hd2 hPDE hSrc hneu.2.1 hneu.2.2
  intro x
  have hx := hlower x.1 x.2
  have hconst : (p.ν * δ ^ p.γ) / p.μ = p.ν / p.μ * δ ^ p.γ := by ring
  rw [hconst] at hx
  simpa [V, intervalDomainLift, x.2] using hx

theorem solution_lift_v_pos_Icc
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (v t) x := by
  obtain ⟨δ, hδ, hu⟩ := exists_uniform_u_lower_at_time hsol ht0 htT
  have hv := classical_v_lower_of_u_lower_at_time hsol ht0 htT hδ hu
  have hc : 0 < p.ν / p.μ * δ ^ p.γ :=
    mul_pos (div_pos p.hν p.hμ) (Real.rpow_pos_of_pos hδ _)
  intro x hx
  have h := hv (⟨x, hx⟩ : intervalDomain.Point)
  simpa [intervalDomainLift, hx] using hc.trans_le h

theorem deriv_v_continuousOn_Icc
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    ContinuousOn (deriv (intervalDomainLift (v t))) (Set.Icc (0 : ℝ) 1) := by
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hV := (hsol.regularity.2.2.2.2.1 t ht).2
  have hdw0 : derivWithin (intervalDomainLift (v t)) (Set.Icc (0 : ℝ) 1) 0 = 0 := by
    let X0 : intervalDomain.Point := ⟨0, ⟨le_rfl, zero_le_one⟩⟩
    have hbd : X0 ∈ intervalDomainM.boundary := Or.inl rfl
    have hN := (hsol.neumann ht.1 ht.2 hbd).2
    have hnormal : derivWithin (intervalDomainLift (v t)) (Set.Ici (0 : ℝ)) 0 = 0 := by
      simpa [intervalDomainM, intervalDomainNormalDeriv, X0] using hN
    have hsets : (Set.Icc (0 : ℝ) 1 : Set ℝ) =ᶠ[𝓝 (0 : ℝ)] Set.Ici 0 := by
      filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with y hy
      apply propext
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, le_of_lt hy⟩
    rwa [derivWithin_congr_set hsets]
  have hdw1 : derivWithin (intervalDomainLift (v t)) (Set.Icc (0 : ℝ) 1) 1 = 0 := by
    let X1 : intervalDomain.Point := ⟨1, ⟨zero_le_one, le_rfl⟩⟩
    have hbd : X1 ∈ intervalDomainM.boundary := Or.inr rfl
    have hN := (hsol.neumann ht.1 ht.2 hbd).2
    have hnormal : derivWithin (intervalDomainLift (v t)) (Set.Iic (1 : ℝ)) 1 = 0 := by
      simpa [intervalDomainM, intervalDomainNormalDeriv, X1] using hN
    have hsets : (Set.Icc (0 : ℝ) 1 : Set ℝ) =ᶠ[𝓝 (1 : ℝ)] Set.Iic 1 := by
      filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with y hy
      apply propext
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨le_of_lt hy, h⟩
    rwa [derivWithin_congr_set hsets]
  exact deriv_intervalDomainLift_continuousOn_Icc_of_regularity
    hV.1 hdw0 hdw1

theorem elliptic_log_gradient_bound
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (v t)) x| ≤
        Real.sqrt p.μ * intervalDomainLift (v t) x := by
  let V : ℝ → ℝ := intervalDomainLift (v t)
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let k : ℝ := Real.sqrt p.μ
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hk : 0 < k := by simpa [k] using Real.sqrt_pos_of_pos p.hμ
  have hk2 : k ^ 2 = p.μ := by simpa [k] using Real.sq_sqrt p.hμ.le
  have hV2 : ContDiffOn ℝ 2 V (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.1
  have hdVcont : ContinuousOn (deriv V) (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using deriv_v_continuousOn_Icc hsol ht0 htT
  have hVnonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ V x := by
    intro x hx
    simpa [V, intervalDomainLift, hx] using
      hsol.v_nonneg (x := (⟨x, hx⟩ : intervalDomain.Point)) ht0 htT
  have hUpos : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 < U x := by
    intro x hx
    simpa [U, intervalDomainLift, Set.Ioo_subset_Icc_self hx] using
      u_pos hsol ht0 htT (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomain.Point)
  have hVxx : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      deriv (deriv V) x = p.μ * V x - p.ν * U x ^ p.γ := by
    intro x hx
    simpa [V, U] using v_xx_eq_reaction_lift hsol ht0 htT hx.1 hx.2
  have hNeu0 : deriv V 0 = 0 := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.2.1
  have hNeu1 : deriv V 1 = 0 := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.2.2
  let F : ℝ → ℝ := fun x => Real.exp (k * x) * (deriv V x - k * V x)
  let G : ℝ → ℝ := fun x => Real.exp (-k * x) * (deriv V x + k * V x)
  have hExpF : Continuous (fun x : ℝ => Real.exp (k*x)) := by
    simpa [Function.comp_def] using
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hExpG : Continuous (fun x : ℝ => Real.exp (-k*x)) := by
    simpa [Function.comp_def] using
      Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)
  have hFcont : ContinuousOn F (Set.Icc (0 : ℝ) 1) :=
    hExpF.continuousOn.mul
      (hdVcont.sub (continuousOn_const.mul hV2.continuousOn))
  have hGcont : ContinuousOn G (Set.Icc (0 : ℝ) 1) :=
    hExpG.continuousOn.mul
      (hdVcont.add (continuousOn_const.mul hV2.continuousOn))
  have hFderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt F (Real.exp (k*x) * (deriv (deriv V) x - k^2*V x)) x := by
    intro x hx
    have hp := ShenWork.MinPersistenceAtoms.contDiffOn_two_hasDerivAt_pair
      isOpen_Ioo (hV2.mono Set.Ioo_subset_Icc_self) hx
    have he : HasDerivAt (fun z : ℝ => Real.exp (k*z))
        (k * Real.exp (k*x)) x := by
      convert Real.hasDerivAt_exp (k*x) |>.comp x ((hasDerivAt_id x).const_mul k)
        using 1 <;> simp <;> ring
    convert he.mul (hp.2.sub (hp.1.const_mul k)) using 1 <;>
      simp only [F, Pi.sub_apply] <;> ring
  have hGderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt G (Real.exp (-k*x) * (deriv (deriv V) x - k^2*V x)) x := by
    intro x hx
    have hp := ShenWork.MinPersistenceAtoms.contDiffOn_two_hasDerivAt_pair
      isOpen_Ioo (hV2.mono Set.Ioo_subset_Icc_self) hx
    have he : HasDerivAt (fun z : ℝ => Real.exp (-k*z))
        ((-k) * Real.exp (-k*x)) x := by
      convert Real.hasDerivAt_exp (-k*x) |>.comp x
        ((hasDerivAt_id x).const_mul (-k)) using 1 <;> simp <;> ring
    convert he.mul (hp.2.add (hp.1.const_mul k)) using 1 <;>
      simp only [G, Pi.add_apply] <;> ring
  have hFanti : AntitoneOn F (Set.Icc (0 : ℝ) 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) hFcont ?_ ?_
    · intro x hx
      rw [interior_Icc] at hx
      exact (hFderiv x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hFderiv x hx).deriv, hVxx x hx, hk2]
      have hs : 0 ≤ p.ν * U x ^ p.γ :=
        mul_nonneg p.hν.le (Real.rpow_nonneg (hUpos x hx).le _)
      calc
        Real.exp (k*x) * (p.μ * V x - p.ν * U x ^ p.γ - p.μ * V x) =
            -(Real.exp (k*x) * (p.ν * U x ^ p.γ)) := by ring
        _ ≤ 0 := neg_nonpos.mpr (mul_nonneg (Real.exp_pos (k*x)).le hs)
  have hGanti : AntitoneOn G (Set.Icc (0 : ℝ) 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) hGcont ?_ ?_
    · intro x hx
      rw [interior_Icc] at hx
      exact (hGderiv x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hGderiv x hx).deriv, hVxx x hx, hk2]
      have hs : 0 ≤ p.ν * U x ^ p.γ :=
        mul_nonneg p.hν.le (Real.rpow_nonneg (hUpos x hx).le _)
      calc
        Real.exp (-k*x) * (p.μ * V x - p.ν * U x ^ p.γ - p.μ * V x) =
            -(Real.exp (-k*x) * (p.ν * U x ^ p.γ)) := by ring
        _ ≤ 0 := neg_nonpos.mpr (mul_nonneg (Real.exp_pos (-k*x)).le hs)
  intro x hx
  have hFle := hFanti (by norm_num) hx hx.1
  have hupper : deriv V x ≤ k * V x := by
    have hV0 := hVnonneg 0 (by norm_num)
    simp [F, hNeu0] at hFle
    nlinarith [Real.exp_pos (k*x)]
  have hGle := hGanti hx (by norm_num) hx.2
  have hlower : -k * V x ≤ deriv V x := by
    have hV1 := hVnonneg 1 (by norm_num)
    have hnonneg : 0 ≤ Real.exp (-k) * (k * V 1) := by positivity
    have hG1 : G 1 = Real.exp (-k) * (k * V 1) := by simp [G, hNeu1]
    rw [hG1] at hGle
    have hprod : 0 ≤ Real.exp (-k*x) * (deriv V x + k*V x) := by
      simpa [G] using hnonneg.trans hGle
    have := (mul_nonneg_iff_of_pos_left (Real.exp_pos (-k*x))).mp hprod
    linarith
  rw [abs_le]
  exact ⟨by linarith, hupper⟩

theorem elliptic_power_preestimate
    {p : CM2Params} {T t q : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) (hq : 1 < q) :
    p.μ * (∫ x in (0 : ℝ)..1, intervalDomainLift (v t) x ^ q) ≤
      p.ν * (∫ x in (0 : ℝ)..1,
        intervalDomainLift (u t) x ^ p.γ *
          intervalDomainLift (v t) x ^ (q - 1)) := by
  let V : ℝ → ℝ := intervalDomainLift (v t)
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let W : ℝ → ℝ := fun x => V x ^ (q - 1)
  let W' : ℝ → ℝ := fun x => (q - 1) * V x ^ (q - 2) * deriv V x
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hV2 : ContDiffOn ℝ 2 V (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.1
  have hdVcont : ContinuousOn (deriv V) (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using deriv_v_continuousOn_Icc hsol ht0 htT
  have hVpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < V x := by
    simpa [V] using solution_lift_v_pos_Icc hsol ht0 htT
  have hUpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < U x := by
    intro x hx
    simpa [U] using solution_lift_pos_Icc hsol ht x hx
  have hWcont : ContinuousOn W (Set.Icc (0 : ℝ) 1) :=
    hV2.continuousOn.rpow_const (fun x hx => Or.inl (ne_of_gt (hVpos x hx)))
  have hW'cont : ContinuousOn W' (Set.Icc (0 : ℝ) 1) :=
    (continuousOn_const.mul
      (hV2.continuousOn.rpow_const
        (fun x hx => Or.inl (ne_of_gt (hVpos x hx))))).mul hdVcont
  have hWderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt W (W' x) x := by
    intro x hx
    have hVderiv := (ShenWork.MinPersistenceAtoms.contDiffOn_two_hasDerivAt_pair
      isOpen_Ioo (hV2.mono Set.Ioo_subset_Icc_self) hx).1
    convert hVderiv.rpow_const (p := q - 1)
      (Or.inl (ne_of_gt (hVpos x (Set.Ioo_subset_Icc_self hx)))) using 1 <;>
      dsimp [W, W'] <;> ring
  have hV2deriv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (deriv V) (deriv (deriv V) x) x := by
    intro x hx
    exact (ShenWork.MinPersistenceAtoms.contDiffOn_two_hasDerivAt_pair
      isOpen_Ioo (hV2.mono Set.Ioo_subset_Icc_self) hx).2
  have hW'int : IntervalIntegrable W' volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le zero_le_one] using hW'cont
  have hV2int : IntervalIntegrable (deriv (deriv V)) volume 0 1 :=
    intervalIntegrable_deriv_deriv_of_contDiffOn_two hV2
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (u := W) (v := deriv V)
    (u' := W') (v' := deriv (deriv V))
    (by simpa [Set.uIcc_of_le zero_le_one] using hWcont)
    (by simpa [Set.uIcc_of_le zero_le_one] using hdVcont)
    (by simpa using hWderiv) (by simpa using hV2deriv) hW'int hV2int
  have hNeu0 : deriv V 0 = 0 := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.2.1
  have hNeu1 : deriv V 1 = 0 := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.2.2
  have hgradnn : 0 ≤ ∫ x in (0 : ℝ)..1, W' x * deriv V x := by
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx => by
      have hq1 : 0 ≤ q - 1 := by linarith
      have hvpow : 0 ≤ V x ^ (q - 2) := Real.rpow_nonneg (hVpos x hx).le _
      dsimp [W']
      nlinarith [sq_nonneg (deriv V x), mul_nonneg hq1 hvpow])
  have hlapnonpos : ∫ x in (0 : ℝ)..1, W x * deriv (deriv V) x ≤ 0 := by
    rw [hIBP, hNeu0, hNeu1]
    linarith
  have hVxx : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      W x * deriv (deriv V) x =
        p.μ * V x ^ q - p.ν * (U x ^ p.γ * V x ^ (q - 1)) := by
    intro x hx
    have hpde : deriv (deriv V) x = p.μ * V x - p.ν * U x ^ p.γ := by
      simpa [V, U] using v_xx_eq_reaction_lift hsol ht0 htT hx.1 hx.2
    have hpow : V x ^ (q - 1) * V x = V x ^ q := by
      calc
        V x ^ (q - 1) * V x = V x ^ (q - 1) * V x ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = V x ^ ((q - 1) + 1) := by
          rw [Real.rpow_add (hVpos x (Set.Ioo_subset_Icc_self hx))]
        _ = V x ^ q := by congr 1 <;> ring
    dsimp [W]
    rw [hpde]
    rw [show V x ^ (q - 1) * (p.μ * V x - p.ν * U x ^ p.γ) =
      p.μ * (V x ^ (q - 1) * V x) -
        p.ν * (U x ^ p.γ * V x ^ (q - 1)) by ring, hpow]
  have hleftInt : IntervalIntegrable (fun x => W x * deriv (deriv V) x)
      volume 0 1 := hV2int.continuousOn_mul (by
        simpa [Set.uIcc_of_le zero_le_one] using hWcont)
  have hmuInt : IntervalIntegrable (fun x => p.μ * V x ^ q) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact continuousOn_const.mul
      (hV2.continuousOn.rpow_const
        (fun x hx => Or.inl (ne_of_gt (hVpos x hx))))
  have hsrcInt : IntervalIntegrable
      (fun x => p.ν * (U x ^ p.γ * V x ^ (q - 1))) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact continuousOn_const.mul
      (((solution_lift_continuousOn_Icc hsol ht).rpow_const
          (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))).mul
        (hV2.continuousOn.rpow_const
          (fun x hx => Or.inl (ne_of_gt (hVpos x hx)))))
  have heq :
      (∫ x in (0 : ℝ)..1, W x * deriv (deriv V) x) =
        p.μ * (∫ x in (0 : ℝ)..1, V x ^ q) -
          p.ν * (∫ x in (0 : ℝ)..1, U x ^ p.γ * V x ^ (q - 1)) := by
    calc
      _ = ∫ x in (0 : ℝ)..1,
          p.μ * V x ^ q - p.ν * (U x ^ p.γ * V x ^ (q - 1)) := by
        apply intervalIntegral.integral_congr_ae
        have hne1 : ∀ᵐ x ∂volume, x ≠ (1 : ℝ) := by
          have heq : {x : ℝ | ¬ x ≠ 1} = ({1} : Set ℝ) := by ext x; simp
          rw [MeasureTheory.ae_iff, heq]
          exact Real.volume_singleton
        filter_upwards [hne1] with x hxne hxmem
        rw [Set.uIoc_of_le zero_le_one] at hxmem
        exact hVxx x ⟨hxmem.1, lt_of_le_of_ne hxmem.2 hxne⟩
      _ = _ := by
        rw [intervalIntegral.integral_sub hmuInt hsrcInt,
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  rw [heq] at hlapnonpos
  simpa [V, U] using (show
    p.μ * (∫ x in (0 : ℝ)..1, V x ^ q) ≤
      p.ν * (∫ x in (0 : ℝ)..1, U x ^ p.γ * V x ^ (q - 1)) by linarith)

theorem elliptic_power_estimate_of_young
    {p : CM2Params} {T t q C0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) (hq : 1 < q)
    (hY : ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      p.ν * A * B ^ (q - 1) ≤ p.μ / 2 * B ^ q + C0 * A ^ q) :
    (∫ x in (0 : ℝ)..1, intervalDomainLift (v t) x ^ q) ≤
      (2 * C0 / p.μ) * (∫ x in (0 : ℝ)..1,
        intervalDomainLift (u t) x ^ (p.γ * q)) := by
  let V : ℝ → ℝ := intervalDomainLift (v t)
  let U : ℝ → ℝ := intervalDomainLift (u t)
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hVpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < V x := by
    simpa [V] using solution_lift_v_pos_Icc hsol ht0 htT
  have hUpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < U x := by
    intro x hx
    simpa [U] using solution_lift_pos_Icc hsol ht x hx
  have hVcont : ContinuousOn V (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.1.continuousOn
  have hUcont : ContinuousOn U (Set.Icc (0 : ℝ) 1) := by
    simpa [U] using solution_lift_continuousOn_Icc hsol ht
  have hVqint : IntervalIntegrable (fun x => V x ^ q) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact hVcont.rpow_const (fun x hx => Or.inl (ne_of_gt (hVpos x hx)))
  have hUqint : IntervalIntegrable (fun x => U x ^ (p.γ * q)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact hUcont.rpow_const (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))
  have hsourceInt : IntervalIntegrable
      (fun x => p.ν * (U x ^ p.γ * V x ^ (q - 1))) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact continuousOn_const.mul
      ((hUcont.rpow_const (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))).mul
        (hVcont.rpow_const (fun x hx => Or.inl (ne_of_gt (hVpos x hx)))))
  have hrightInt : IntervalIntegrable
      (fun x => p.μ / 2 * V x ^ q + C0 * U x ^ (p.γ * q)) volume 0 1 :=
    (hVqint.const_mul (p.μ / 2)).add (hUqint.const_mul C0)
  have hpoint : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      p.ν * (U x ^ p.γ * V x ^ (q - 1)) ≤
        p.μ / 2 * V x ^ q + C0 * U x ^ (p.γ * q) := by
    intro x hx
    have hy := hY (U x ^ p.γ) (V x)
      (Real.rpow_nonneg (hUpos x hx).le _) (hVpos x hx).le
    have hpow : (U x ^ p.γ) ^ q = U x ^ (p.γ * q) := by
      rw [← Real.rpow_mul (hUpos x hx).le]
    simpa [mul_assoc, hpow] using hy
  have hint_le :
      (∫ x in (0 : ℝ)..1, p.ν * (U x ^ p.γ * V x ^ (q - 1))) ≤
        ∫ x in (0 : ℝ)..1, p.μ / 2 * V x ^ q + C0 * U x ^ (p.γ * q) :=
    intervalIntegral.integral_mono_on (by norm_num) hsourceInt hrightInt hpoint
  have hpre := elliptic_power_preestimate hsol ht0 htT hq
  have hcombined :
      p.μ * (∫ x in (0 : ℝ)..1, V x ^ q) ≤
        p.μ / 2 * (∫ x in (0 : ℝ)..1, V x ^ q) +
          C0 * (∫ x in (0 : ℝ)..1, U x ^ (p.γ * q)) := by
    calc
      _ ≤ p.ν * (∫ x in (0 : ℝ)..1, U x ^ p.γ * V x ^ (q - 1)) := by
        simpa [V, U] using hpre
      _ = ∫ x in (0 : ℝ)..1, p.ν * (U x ^ p.γ * V x ^ (q - 1)) := by
        rw [intervalIntegral.integral_const_mul]
      _ ≤ _ := hint_le
      _ = _ := by
        rw [intervalIntegral.integral_add
            (hVqint.const_mul (p.μ / 2)) (hUqint.const_mul C0),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  have hhalf : p.μ / 2 * (∫ x in (0 : ℝ)..1, V x ^ q) ≤
      C0 * (∫ x in (0 : ℝ)..1, U x ^ (p.γ * q)) := by linarith
  change (∫ x in (0 : ℝ)..1, V x ^ q) ≤
    (2 * C0 / p.μ) * (∫ x in (0 : ℝ)..1, U x ^ (p.γ * q))
  rw [show (2 * C0 / p.μ) * (∫ x in (0 : ℝ)..1, U x ^ (p.γ * q)) =
      (2 * C0 * (∫ x in (0 : ℝ)..1, U x ^ (p.γ * q))) / p.μ by ring]
  apply (le_div_iff₀ p.hμ).2
  nlinarith

/-- The weighted-gradient half of Proposition 2.2, in the exact form used by
the finite descent and the critical `rho = gamma` bootstrap. -/
theorem weighted_one_add_v_gradient_estimate
    {p : CM2Params} {T q beta : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hq : 1 < q) (hbeta : 0 ≤ beta) :
    ∀ t, 0 < t → t < T →
      (∫ x in (0 : ℝ)..1,
        |deriv (intervalDomainLift (v t)) x| ^ (2 * q) /
          (1 + intervalDomainLift (v t) x) ^ ((1 + beta) * q)) ≤
        (Theta_beta beta) ^ q * intervalDomainWeightedGradientConstant p q *
          (∫ x in (0 : ℝ)..1,
            intervalDomainLift (u t) x ^ (p.γ * q)) := by
  let C0 : ℝ := ellipticSourceYoungConstant p q
  have hC0 : 0 < C0 := ellipticSourceYoungConstant_pos p hq
  have hY := ellipticSourceYoungConstant_bound p hq
  let Mstar : ℝ := intervalDomainWeightedGradientConstant p q
  intro t ht0 htT
  let V : ℝ → ℝ := intervalDomainLift (v t)
  let U : ℝ → ℝ := intervalDomainLift (u t)
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hVpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < V x := by
    simpa [V] using solution_lift_v_pos_Icc hsol ht0 htT
  have hVcont : ContinuousOn V (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.1.continuousOn
  have hdVcont : ContinuousOn (deriv V) (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using deriv_v_continuousOn_Icc hsol ht0 htT
  have hlog : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv V x| ≤ Real.sqrt p.μ * V x := by
    simpa [V] using elliptic_log_gradient_bound hsol ht0 htT
  have hnumcont : ContinuousOn (fun x => |deriv V x| ^ (2 * q))
      (Set.Icc (0 : ℝ) 1) :=
    hdVcont.abs.rpow_const (fun _ _ => Or.inr (by linarith))
  have hbasecont : ContinuousOn (fun x => 1 + V x) (Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.add hVcont
  have hdencont : ContinuousOn
      (fun x => (1 + V x) ^ ((1 + beta) * q)) (Set.Icc (0 : ℝ) 1) :=
    hbasecont.rpow_const (fun x hx => Or.inl
      (ne_of_gt (show 0 < 1 + V x by linarith [hVpos x hx])))
  have hint : IntervalIntegrable
      (fun x => |deriv V x| ^ (2 * q) /
        (1 + V x) ^ ((1 + beta) * q)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact hnumcont.div hdencont (fun x hx => ne_of_gt
      (Real.rpow_pos_of_pos (by have := hVpos x hx; linarith) _))
  have hVqint : IntervalIntegrable (fun x => V x ^ q) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact hVcont.rpow_const (fun x hx => Or.inl (ne_of_gt (hVpos x hx)))
  have hraw :
      (∫ x in (0 : ℝ)..1,
        |deriv V x| ^ (2 * q) / (1 + V x) ^ ((1 + beta) * q)) ≤
        (Theta_beta beta) ^ q *
          (p.μ ^ q * (∫ x in (0 : ℝ)..1, V x ^ q)) := by
    calc
      _ ≤ ∫ x in (0 : ℝ)..1,
          (Theta_beta beta) ^ q * (p.μ ^ q * V x ^ q) :=
        intervalIntegral.integral_mono_on (by norm_num) hint
          (by simpa [mul_assoc] using
            hVqint.const_mul ((Theta_beta beta) ^ q * p.μ ^ q))
          (fun x hx => by
            simpa [mul_assoc] using
              ShenWork.Paper2.elliptic_denominator_weight_pointwise
                p.hμ hbeta hq (hVpos x hx) (hlog x hx))
      _ = _ := by
        rw [show (fun x => (Theta_beta beta) ^ q * (p.μ ^ q * V x ^ q)) =
            fun x => ((Theta_beta beta) ^ q * p.μ ^ q) * V x ^ q by
              funext x; ring,
          intervalIntegral.integral_const_mul]
        ring
  have hpower := elliptic_power_estimate_of_young
    hsol ht0 htT hq hY
  calc
    _ ≤ (Theta_beta beta) ^ q *
        (p.μ ^ q * (∫ x in (0 : ℝ)..1, V x ^ q)) := hraw
    _ ≤ (Theta_beta beta) ^ q *
        (p.μ ^ q * ((2 * C0 / p.μ) *
          (∫ x in (0 : ℝ)..1, U x ^ (p.γ * q)))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (by simpa [V, U] using hpower)
          (Real.rpow_nonneg p.hμ.le q))
        (Real.rpow_nonneg (Theta_beta_pos_of_nonneg hbeta).le q)
    _ = (Theta_beta beta) ^ q * Mstar *
        (∫ x in (0 : ℝ)..1, U x ^ (p.γ * q)) := by
      dsimp [Mstar, intervalDomainWeightedGradientConstant, C0]
      ring

end ShenWork.Paper2.IntervalDomainM
