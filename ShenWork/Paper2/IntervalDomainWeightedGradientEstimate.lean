import ShenWork.Paper2.IntervalDomainL2UEnergyCombine
import ShenWork.Paper2.IntervalDomainL2StaticVDifference
import ShenWork.PDE.P3MoserDxJointContinuity
import ShenWork.Paper3.IntervalDomainPersistenceElliptic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Concrete weighted elliptic gradient estimate on the unit interval

This file realizes Paper 2, Proposition 2.2 for the concrete interval domain.
The proof is the elementary one-dimensional elliptic route: a maximum-principle
factorization gives `|v_x| ≤ sqrt μ · v`, and a Neumann multiplier estimate
controls the `L^q` norm of `v` by the `L^(γq)` norm of `u`.
-/

open MeasureTheory Set
open scoped Topology Interval
open ShenWork.IntervalDomain
open ShenWork.IntervalEllipticCharacterization

noncomputable section

namespace ShenWork.Paper2

theorem intervalDomain_elliptic_log_gradient_bound
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (v t)) x| ≤
        Real.sqrt p.μ * intervalDomainLift (v t) x := by
  let V : ℝ → ℝ := intervalDomainLift (v t)
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let k : ℝ := Real.sqrt p.μ
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hk : 0 < k := by
    simpa [k] using Real.sqrt_pos_of_pos p.hμ
  have hk_sq : k ^ 2 = p.μ := by
    simpa [k] using Real.sq_sqrt p.hμ.le
  have hV2 : ContDiffOn ℝ 2 V (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.1
  have hV1 : ContDiffOn ℝ 1 V (Set.Icc (0 : ℝ) 1) :=
    hV2.of_le (by norm_num)
  have hdV1 : ContDiffOn ℝ 1 (deriv V) (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using
      (resolverGradReal_contDiffOn_Icc hsol ht).congr
        (fun x hx => solution_lift_v_deriv_eq_resolverGrad_Icc hsol ht hx)
  have hV_nonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ V x := by
    simpa [V] using solution_lift_v_nonneg_Icc hsol ht
  have hU_pos : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 < U x := by
    intro x hx
    simpa [U, intervalDomainLift, Set.Ioo_subset_Icc_self hx] using
      (hsol.u_pos' (x :=
        (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomain.Point)) ht0 htT)
  have hVxx : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      deriv (deriv V) x = p.μ * V x - p.ν * (U x) ^ p.γ := by
    intro x hx
    simpa [V, U] using
      intervalDomain_v_xx_eq_reaction_lift hsol ht0 htT hx.1 hx.2
  have hNeu0 : deriv V 0 = 0 := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.2.1
  have hNeu1 : deriv V 1 = 0 := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.2.2
  let F : ℝ → ℝ := fun x => Real.exp (k * x) * (deriv V x - k * V x)
  let G : ℝ → ℝ := fun x => Real.exp (-k * x) * (deriv V x + k * V x)
  have hExpF_cont : Continuous (fun x : ℝ => Real.exp (k * x)) := by
    simpa [Function.comp_def] using
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hExpG_cont : Continuous (fun x : ℝ => Real.exp (-k * x)) := by
    simpa [Function.comp_def] using
      Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)
  have hF_cont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
    exact hExpF_cont.continuousOn.mul
      (hdV1.continuousOn.sub (continuousOn_const.mul hV1.continuousOn))
  have hG_cont : ContinuousOn G (Set.Icc (0 : ℝ) 1) := by
    exact hExpG_cont.continuousOn.mul
      (hdV1.continuousOn.add (continuousOn_const.mul hV1.continuousOn))
  have hF_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt F
        (Real.exp (k * x) * (deriv (deriv V) x - k ^ 2 * V x)) x := by
    intro x hx
    have hpair := ShenWork.MinPersistenceAtoms.contDiffOn_two_hasDerivAt_pair
      isOpen_Ioo (hV2.mono Set.Ioo_subset_Icc_self) hx
    have hexp : HasDerivAt (fun z : ℝ => Real.exp (k * z))
        (k * Real.exp (k * x)) x := by
      convert Real.hasDerivAt_exp (k * x) |>.comp x
        ((hasDerivAt_id x).const_mul k) using 1 <;> simp <;> ring
    convert hexp.mul (hpair.2.sub (hpair.1.const_mul k)) using 1 <;>
      simp only [F, Pi.sub_apply] <;> ring
  have hG_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt G
        (Real.exp (-k * x) * (deriv (deriv V) x - k ^ 2 * V x)) x := by
    intro x hx
    have hpair := ShenWork.MinPersistenceAtoms.contDiffOn_two_hasDerivAt_pair
      isOpen_Ioo (hV2.mono Set.Ioo_subset_Icc_self) hx
    have hexp : HasDerivAt (fun z : ℝ => Real.exp (-k * z))
        ((-k) * Real.exp (-k * x)) x := by
      convert Real.hasDerivAt_exp (-k * x) |>.comp x
        ((hasDerivAt_id x).const_mul (-k)) using 1 <;> simp <;> ring
    convert hexp.mul (hpair.2.add (hpair.1.const_mul k)) using 1 <;>
      simp only [G, Pi.add_apply] <;> ring
  have hF_anti : AntitoneOn F (Set.Icc (0 : ℝ) 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) hF_cont ?_ ?_
    · intro x hx
      rw [interior_Icc] at hx
      exact (hF_deriv x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hF_deriv x hx).deriv, hVxx x hx, hk_sq]
      have hsrc : 0 ≤ p.ν * (U x) ^ p.γ :=
        mul_nonneg p.hν.le (Real.rpow_nonneg (hU_pos x hx).le _)
      calc
        Real.exp (k * x) *
              (p.μ * V x - p.ν * U x ^ p.γ - p.μ * V x) =
            -(Real.exp (k * x) * (p.ν * U x ^ p.γ)) := by ring
        _ ≤ 0 := neg_nonpos.mpr (mul_nonneg (Real.exp_pos _).le hsrc)
  have hG_anti : AntitoneOn G (Set.Icc (0 : ℝ) 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) hG_cont ?_ ?_
    · intro x hx
      rw [interior_Icc] at hx
      exact (hG_deriv x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hG_deriv x hx).deriv, hVxx x hx, hk_sq]
      have hsrc : 0 ≤ p.ν * (U x) ^ p.γ :=
        mul_nonneg p.hν.le (Real.rpow_nonneg (hU_pos x hx).le _)
      calc
        Real.exp (-k * x) *
              (p.μ * V x - p.ν * U x ^ p.γ - p.μ * V x) =
            -(Real.exp (-k * x) * (p.ν * U x ^ p.γ)) := by ring
        _ ≤ 0 := neg_nonpos.mpr (mul_nonneg (Real.exp_pos _).le hsrc)
  intro x hx
  have hFle : F x ≤ F 0 := hF_anti (by norm_num) hx hx.1
  have hF0 : F 0 = -k * V 0 := by simp [F, hNeu0]
  have hdV_upper : deriv V x ≤ k * V x := by
    rw [hF0] at hFle
    have hexp : 0 < Real.exp (k * x) := Real.exp_pos _
    have hV0 := hV_nonneg 0 (by norm_num)
    dsimp [F] at hFle
    nlinarith
  have hGge : G 1 ≤ G x := hG_anti hx (by norm_num) hx.2
  have hG1 : G 1 = Real.exp (-k) * (k * V 1) := by
    simp [G, hNeu1]
  have hdV_lower : -k * V x ≤ deriv V x := by
    rw [hG1] at hGge
    have hexp : 0 < Real.exp (-k * x) := Real.exp_pos _
    have hV1nn := hV_nonneg 1 (by norm_num)
    dsimp [G] at hGge
    have hG1nn : 0 ≤ Real.exp (-k) * (k * V 1) := by positivity
    have hprod : 0 ≤ Real.exp (-k * x) * (deriv V x + k * V x) :=
      hG1nn.trans hGge
    have hsum : 0 ≤ deriv V x + k * V x :=
      (mul_nonneg_iff_of_pos_left hexp).mp hprod
    linarith
  rw [abs_le]
  exact ⟨by linarith, hdV_upper⟩

theorem intervalDomain_solution_lift_v_pos_Icc
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (v t) x := by
  obtain ⟨δ, hδ, hδu⟩ :=
    lift_u_uniformPositive_on_compact hsol ht0 (le_refl t) htT
  have hvlow := ShenWork.Paper3.intervalDomain_classical_v_lower_of_u_lower_at_time
      (p := p) (T := T) (t := t) (u := u) (v := v) hsol ⟨ht0, htT⟩ hδ
      (fun X => by
        have heq : intervalDomainLift (u t) X.1 = u t X := by
          by_cases hxmem : X.1 ∈ Set.Icc (0 : ℝ) 1
          · simp [intervalDomainLift, hxmem]
          · exact (hxmem X.2).elim
        rw [← heq]
        exact hδu t ⟨le_rfl, le_rfl⟩ X.1 X.2)
  intro x hx
  have hconst : 0 < p.ν / p.μ * δ ^ p.γ :=
    mul_pos (div_pos p.hν p.hμ) (Real.rpow_pos_of_pos hδ _)
  have hxlow := hvlow (⟨x, hx⟩ : intervalDomain.Point)
  have hlift : intervalDomainLift (v t) x = v t (⟨x, hx⟩ : intervalDomain.Point) := by
    simp [intervalDomainLift, hx]
  rw [hlift]
  exact hconst.trans_le hxlow

theorem intervalDomain_elliptic_power_preestimate
    {p : CM2Params} {T t q : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
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
    simpa [V] using
      (resolverGradReal_contDiffOn_Icc hsol ht).continuousOn.congr
        (fun x hx => solution_lift_v_deriv_eq_resolverGrad_Icc hsol ht hx)
  have hVpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < V x := by
    simpa [V] using intervalDomain_solution_lift_v_pos_Icc hsol ht0 htT
  have hUpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < U x := by
    intro x hx
    simpa [U] using solution_lift_pos hsol ht x hx
  have hWcont : ContinuousOn W (Set.Icc (0 : ℝ) 1) := by
    exact hV2.continuousOn.rpow_const (fun x hx => Or.inl (ne_of_gt (hVpos x hx)))
  have hW'cont : ContinuousOn W' (Set.Icc (0 : ℝ) 1) := by
    exact (continuousOn_const.mul
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
    have hc : ContinuousOn W' (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hW'cont
    exact hc.intervalIntegrable
  have hV2int : IntervalIntegrable (deriv (deriv V)) volume 0 1 :=
    intervalIntegrable_deriv_deriv_of_contDiffOn_two hV2
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (u := W) (v := deriv V)
    (u' := W') (v' := deriv (deriv V))
    (by simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hWcont)
    (by simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hdVcont)
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
  have hlap_nonpos : ∫ x in (0 : ℝ)..1, W x * deriv (deriv V) x ≤ 0 := by
    rw [hIBP, hNeu0, hNeu1]
    linarith
  have hVxx : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      W x * deriv (deriv V) x =
        p.μ * V x ^ q - p.ν * (U x ^ p.γ * V x ^ (q - 1)) := by
    intro x hx
    have hpde : deriv (deriv V) x = p.μ * V x - p.ν * U x ^ p.γ := by
      simpa [V, U] using
        intervalDomain_v_xx_eq_reaction_lift hsol ht0 htT hx.1 hx.2
    have hpow : V x ^ (q - 1) * V x = V x ^ q := by
      calc
        V x ^ (q - 1) * V x = V x ^ (q - 1) * V x ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = V x ^ ((q - 1) + 1) :=
          (Real.rpow_add (hVpos x (Set.Ioo_subset_Icc_self hx)) (q - 1) 1).symm
        _ = V x ^ q := by ring_nf
    rw [hpde]
    dsimp [W]
    calc
      V x ^ (q - 1) * (p.μ * V x - p.ν * U x ^ p.γ) =
          p.μ * (V x ^ (q - 1) * V x) -
            p.ν * (U x ^ p.γ * V x ^ (q - 1)) := by ring
      _ = p.μ * V x ^ q -
            p.ν * (U x ^ p.γ * V x ^ (q - 1)) := by rw [hpow]
  have hLapEq :
      (∫ x in (0 : ℝ)..1, W x * deriv (deriv V) x) =
        ∫ x in (0 : ℝ)..1,
          p.μ * V x ^ q - p.ν * (U x ^ p.γ * V x ^ (q - 1)) := by
    apply intervalIntegral.integral_congr_ae
    rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    have hnull : volume ({(1 : ℝ)} : Set ℝ) = 0 := by simp
    refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    push Not at hx
    obtain ⟨hxIoc, hne⟩ := hx
    simp only [Set.mem_singleton_iff]
    by_contra hx1
    have hxoo : x ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨hxIoc.1, lt_of_le_of_ne hxIoc.2 hx1⟩
    exact hne (hVxx x hxoo)
  have hVqcont : ContinuousOn (fun x => V x ^ q) (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    exact hV2.continuousOn.rpow_const
      (fun x hx => Or.inl (ne_of_gt (hVpos x hx)))
  have hProdcont : ContinuousOn
      (fun x => U x ^ p.γ * V x ^ (q - 1)) (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    have hUcont : ContinuousOn U (Set.Icc (0 : ℝ) 1) := by
      simpa [U] using (hsol.regularity.2.2.2.2.1 t ht).1.1.continuousOn
    exact (hUcont.rpow_const (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))).mul
      (hV2.continuousOn.rpow_const (fun x hx => Or.inl (ne_of_gt (hVpos x hx))))
  have hVqint : IntervalIntegrable (fun x => V x ^ q) volume 0 1 :=
    hVqcont.intervalIntegrable
  have hProdint : IntervalIntegrable
      (fun x => U x ^ p.γ * V x ^ (q - 1)) volume 0 1 :=
    hProdcont.intervalIntegrable
  have hmain :
      p.μ * (∫ x in (0 : ℝ)..1, V x ^ q) -
          p.ν * (∫ x in (0 : ℝ)..1, U x ^ p.γ * V x ^ (q - 1)) ≤ 0 := by
    calc
      p.μ * (∫ x in (0 : ℝ)..1, V x ^ q) -
            p.ν * (∫ x in (0 : ℝ)..1, U x ^ p.γ * V x ^ (q - 1)) =
          ∫ x in (0 : ℝ)..1,
            p.μ * V x ^ q - p.ν * (U x ^ p.γ * V x ^ (q - 1)) := by
          rw [intervalIntegral.integral_sub
              (hVqint.const_mul p.μ) (hProdint.const_mul p.ν),
            intervalIntegral.integral_const_mul,
            intervalIntegral.integral_const_mul]
      _ = ∫ x in (0 : ℝ)..1, W x * deriv (deriv V) x := hLapEq.symm
      _ ≤ 0 := hlap_nonpos
  simpa [V, U] using (sub_nonpos.mp hmain)

theorem elliptic_source_young_exists
    {mu nu q : ℝ} (hmu : 0 < mu) (hnu : 0 < nu) (hq : 1 < q) :
    ∃ C > 0, ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      nu * A * B ^ (q - 1) ≤ mu / 2 * B ^ q + C * A ^ q := by
  let pH : ℝ := q / (q - 1)
  have hq1 : 0 < q - 1 := sub_pos.mpr hq
  have hpH : 1 < pH := by
    dsimp [pH]
    rw [one_lt_div hq1]
    linarith
  have hpHpos : 0 < pH := zero_lt_one.trans hpH
  have hpHne : pH ≠ 0 := ne_of_gt hpHpos
  have hconj : pH.HolderConjugate q := by
    rw [Real.holderConjugate_iff]
    refine ⟨hpH, ?_⟩
    dsimp [pH]
    field_simp [ne_of_gt hq1, ne_of_gt (zero_lt_one.trans hq)]
    ring
  let scale : ℝ := ((mu / 2) * pH) ^ (1 / pH)
  have hscale : 0 < scale := by
    dsimp [scale]
    exact Real.rpow_pos_of_pos (mul_pos (by positivity) hpHpos) _
  let C : ℝ := (nu / scale) ^ q / q
  have hC : 0 < C := by
    dsimp [C]
    exact div_pos (Real.rpow_pos_of_pos (div_pos hnu hscale) _) (zero_lt_one.trans hq)
  refine ⟨C, hC, ?_⟩
  intro A B hA hB
  have hleft : 0 ≤ scale * B ^ (q - 1) :=
    mul_nonneg hscale.le (Real.rpow_nonneg hB _)
  have hright : 0 ≤ nu * A / scale :=
    div_nonneg (mul_nonneg hnu.le hA) hscale.le
  have hY := Real.young_inequality_of_nonneg
    (a := scale * B ^ (q - 1)) (b := nu * A / scale) hleft hright hconj
  have hprod :
      (scale * B ^ (q - 1)) * (nu * A / scale) = nu * A * B ^ (q - 1) := by
    field_simp [ne_of_gt hscale]
  have hscalePow : scale ^ pH = (mu / 2) * pH := by
    dsimp [scale]
    rw [← Real.rpow_mul (mul_pos (by positivity) hpHpos).le]
    have hone : (1 / pH) * pH = 1 := by field_simp [hpHne]
    rw [hone, Real.rpow_one]
  have hBpow : (B ^ (q - 1)) ^ pH = B ^ q := by
    rw [← Real.rpow_mul hB]
    dsimp [pH]
    have : (q - 1) * (q / (q - 1)) = q := by field_simp [ne_of_gt hq1]
    rw [this]
  have hterm1 : (scale * B ^ (q - 1)) ^ pH / pH = mu / 2 * B ^ q := by
    rw [Real.mul_rpow hscale.le (Real.rpow_nonneg hB _), hscalePow, hBpow]
    field_simp [hpHne]
  have hterm2 : (nu * A / scale) ^ q / q = C * A ^ q := by
    have hbase : nu * A / scale = (nu / scale) * A := by ring
    rw [hbase, Real.mul_rpow (div_nonneg hnu.le hscale.le) hA]
    dsimp [C]
    ring
  calc
    nu * A * B ^ (q - 1) =
        (scale * B ^ (q - 1)) * (nu * A / scale) := hprod.symm
    _ ≤ (scale * B ^ (q - 1)) ^ pH / pH + (nu * A / scale) ^ q / q := hY
    _ = mu / 2 * B ^ q + C * A ^ q := by rw [hterm1, hterm2]

theorem intervalDomain_elliptic_power_estimate_of_young
    {p : CM2Params} {T t q C0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T) (hq : 1 < q)
    (hC0 : 0 < C0)
    (hY : ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      p.ν * A * B ^ (q - 1) ≤ p.μ / 2 * B ^ q + C0 * A ^ q) :
    (∫ x in (0 : ℝ)..1, intervalDomainLift (v t) x ^ q) ≤
      (2 * C0 / p.μ) * (∫ x in (0 : ℝ)..1,
        intervalDomainLift (u t) x ^ (p.γ * q)) := by
  let V : ℝ → ℝ := intervalDomainLift (v t)
  let U : ℝ → ℝ := intervalDomainLift (u t)
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hVpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < V x := by
    simpa [V] using intervalDomain_solution_lift_v_pos_Icc hsol ht0 htT
  have hUpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < U x := by
    intro x hx
    simpa [U] using solution_lift_pos hsol ht x hx
  have hVcont : ContinuousOn V (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.1.continuousOn
  have hUcont : ContinuousOn U (Set.Icc (0 : ℝ) 1) := by
    simpa [U] using (hsol.regularity.2.2.2.2.1 t ht).1.1.continuousOn
  have hVqint : IntervalIntegrable (fun x => V x ^ q) volume 0 1 := by
    have hc : ContinuousOn (fun x => V x ^ q) (Set.Icc (0 : ℝ) 1) :=
      hVcont.rpow_const (fun x hx => Or.inl (ne_of_gt (hVpos x hx)))
    have hcu : ContinuousOn (fun x => V x ^ q) (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hc
    exact hcu.intervalIntegrable
  have hUqint : IntervalIntegrable (fun x => U x ^ (p.γ * q)) volume 0 1 := by
    have hc : ContinuousOn (fun x => U x ^ (p.γ * q)) (Set.Icc (0 : ℝ) 1) :=
      hUcont.rpow_const (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))
    have hcu : ContinuousOn (fun x => U x ^ (p.γ * q)) (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hc
    exact hcu.intervalIntegrable
  have hsourceInt : IntervalIntegrable
      (fun x => p.ν * (U x ^ p.γ * V x ^ (q - 1))) volume 0 1 := by
    have hc : ContinuousOn (fun x => p.ν * (U x ^ p.γ * V x ^ (q - 1)))
        (Set.uIcc (0 : ℝ) 1) := by
      rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
      exact continuousOn_const.mul
        ((hUcont.rpow_const (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))).mul
          (hVcont.rpow_const (fun x hx => Or.inl (ne_of_gt (hVpos x hx)))))
    exact hc.intervalIntegrable
  have hrightInt : IntervalIntegrable
      (fun x => p.μ / 2 * V x ^ q + C0 * U x ^ (p.γ * q)) volume 0 1 :=
    (hVqint.const_mul (p.μ / 2)).add (hUqint.const_mul C0)
  have hpt : ∀ x ∈ Set.Icc (0 : ℝ) 1,
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
    intervalIntegral.integral_mono_on (by norm_num) hsourceInt hrightInt hpt
  have hpre := intervalDomain_elliptic_power_preestimate hsol ht0 htT hq
  have hcombined :
      p.μ * (∫ x in (0 : ℝ)..1, V x ^ q) ≤
        p.μ / 2 * (∫ x in (0 : ℝ)..1, V x ^ q) +
          C0 * (∫ x in (0 : ℝ)..1, U x ^ (p.γ * q)) := by
    calc
      p.μ * (∫ x in (0 : ℝ)..1, V x ^ q) ≤
          p.ν * (∫ x in (0 : ℝ)..1, U x ^ p.γ * V x ^ (q - 1)) := by
        simpa [V, U] using hpre
      _ = ∫ x in (0 : ℝ)..1, p.ν * (U x ^ p.γ * V x ^ (q - 1)) := by
        rw [intervalIntegral.integral_const_mul]
      _ ≤ ∫ x in (0 : ℝ)..1,
          p.μ / 2 * V x ^ q + C0 * U x ^ (p.γ * q) := hint_le
      _ = p.μ / 2 * (∫ x in (0 : ℝ)..1, V x ^ q) +
          C0 * (∫ x in (0 : ℝ)..1, U x ^ (p.γ * q)) := by
        rw [intervalIntegral.integral_add
            (hVqint.const_mul (p.μ / 2)) (hUqint.const_mul C0),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hhalf : p.μ / 2 * (∫ x in (0 : ℝ)..1, V x ^ q) ≤
      C0 * (∫ x in (0 : ℝ)..1, U x ^ (p.γ * q)) := by linarith
  change (∫ x in (0 : ℝ)..1, V x ^ q) ≤
    (2 * C0 / p.μ) * (∫ x in (0 : ℝ)..1, U x ^ (p.γ * q))
  rw [show (2 * C0 / p.μ) * (∫ x in (0 : ℝ)..1, U x ^ (p.γ * q)) =
      (2 * C0 * (∫ x in (0 : ℝ)..1, U x ^ (p.γ * q))) / p.μ by ring]
  apply (le_div_iff₀ p.hμ).2
  nlinarith

theorem intervalDomain_elliptic_power_estimate
    {p : CM2Params} {T t q : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T) (hq : 1 < q) :
    ∃ C > 0,
      (∫ x in (0 : ℝ)..1, intervalDomainLift (v t) x ^ q) ≤
        C * (∫ x in (0 : ℝ)..1,
          intervalDomainLift (u t) x ^ (p.γ * q)) := by
  obtain ⟨C0, hC0, hY⟩ := elliptic_source_young_exists p.hμ p.hν hq
  exact ⟨2 * C0 / p.μ, div_pos (mul_pos (by norm_num) hC0) p.hμ,
    intervalDomain_elliptic_power_estimate_of_young hsol ht0 htT hq hC0 hY⟩

theorem elliptic_log_weight_pointwise
    {mu q V d : ℝ} (hmu : 0 < mu) (hq : 1 < q) (hV : 0 < V)
    (hd : |d| ≤ Real.sqrt mu * V) :
    |d| ^ (2 * q) / V ^ q ≤ mu ^ q * V ^ q := by
  have h2q : 0 ≤ 2 * q := mul_nonneg (by norm_num) (zero_lt_one.trans hq).le
  have hden : 0 < V ^ q := Real.rpow_pos_of_pos hV _
  have hpowle : |d| ^ (2 * q) ≤ (Real.sqrt mu * V) ^ (2 * q) :=
    Real.rpow_le_rpow (abs_nonneg d) hd h2q
  calc
    |d| ^ (2 * q) / V ^ q ≤ (Real.sqrt mu * V) ^ (2 * q) / V ^ q :=
      (div_le_div_iff_of_pos_right hden).2 hpowle
    _ = mu ^ q * V ^ q := by
      have hk : 0 ≤ Real.sqrt mu := Real.sqrt_nonneg _
      have hkpow : (Real.sqrt mu) ^ (2 * q) = mu ^ q := by
        calc
          (Real.sqrt mu) ^ (2 * q) =
              ((Real.sqrt mu) ^ (2 : ℝ)) ^ q := Real.rpow_mul hk 2 q
          _ = mu ^ q := by
            have hs : (Real.sqrt mu) ^ (2 : ℝ) = mu := by
              simpa using Real.sq_sqrt hmu.le
            rw [hs]
      have hVpow : V ^ (2 * q) / V ^ q = V ^ q := by
        rw [← Real.rpow_sub hV]
        congr 1
        ring
      rw [Real.mul_rpow hk hV.le, hkpow]
      calc
        mu ^ q * V ^ (2 * q) / V ^ q = mu ^ q * (V ^ (2 * q) / V ^ q) := by ring
        _ = mu ^ q * V ^ q := by rw [hVpow]

theorem elliptic_denominator_weight_pointwise
    {mu beta q V d : ℝ} (hmu : 0 < mu) (hbeta : 0 ≤ beta)
    (hq : 1 < q) (hV : 0 < V)
    (hd : |d| ≤ Real.sqrt mu * V) :
    |d| ^ (2 * q) / (1 + V) ^ ((1 + beta) * q) ≤
      (Theta_beta beta) ^ q * (mu ^ q * V ^ q) := by
  have hbase : 0 < 1 + V := by linarith
  have hratio_nonneg : 0 ≤ V / (1 + V) ^ (1 + beta) :=
    div_nonneg hV.le (Real.rpow_nonneg hbase.le _)
  have htheta : V / (1 + V) ^ (1 + beta) ≤ Theta_beta beta := by
    by_cases hb0 : beta = 0
    · subst beta
      rw [Theta_beta_zero]
      norm_num [Real.rpow_one]
      exact (div_le_one hbase).2 (by linarith)
    · exact Lemma_2_5_normalized_Theta_bound
        (lt_of_le_of_ne hbeta (Ne.symm hb0)) hV
  have hratioPow :
      (V / (1 + V) ^ (1 + beta)) ^ q ≤ (Theta_beta beta) ^ q :=
    Real.rpow_le_rpow hratio_nonneg htheta (zero_lt_one.trans hq).le
  have hfactor :
      |d| ^ (2 * q) / (1 + V) ^ ((1 + beta) * q) =
        (|d| ^ (2 * q) / V ^ q) *
          (V / (1 + V) ^ (1 + beta)) ^ q := by
    rw [Real.div_rpow hV.le (Real.rpow_nonneg hbase.le _),
      ← Real.rpow_mul hbase.le]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hV q),
      ne_of_gt (Real.rpow_pos_of_pos hbase ((1 + beta) * q))]
  rw [hfactor]
  have hfirst := elliptic_log_weight_pointwise hmu hq hV hd
  have hmul := mul_le_mul hfirst hratioPow (Real.rpow_nonneg hratio_nonneg q)
    (mul_nonneg (Real.rpow_nonneg hmu.le q) (Real.rpow_nonneg hV.le q))
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

theorem intervalDomain_weighted_v_integral_lift
    {f : intervalDomain.Point → ℝ} {q : ℝ} :
    intervalDomain.integral
        (fun x => (intervalDomain.gradNorm f x) ^ (2 * q) / f x ^ q) =
      ∫ y in (0 : ℝ)..1,
        |deriv (intervalDomainLift f) y| ^ (2 * q) /
          intervalDomainLift f y ^ q := by
  change intervalDomainIntegral
      (fun x => (intervalDomainGradNorm f x) ^ (2 * q) / f x ^ q) = _
  rw [intervalDomainIntegral]
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hy
  simp [intervalDomainLift, intervalDomainGradNorm, hy]

theorem intervalDomain_weighted_one_add_v_integral_lift
    {f : intervalDomain.Point → ℝ} {q beta : ℝ} :
    intervalDomain.integral
        (fun x => (intervalDomain.gradNorm f x) ^ (2 * q) /
          (1 + f x) ^ ((1 + beta) * q)) =
      ∫ y in (0 : ℝ)..1,
        |deriv (intervalDomainLift f) y| ^ (2 * q) /
          (1 + intervalDomainLift f y) ^ ((1 + beta) * q) := by
  change intervalDomainIntegral
      (fun x => (intervalDomainGradNorm f x) ^ (2 * q) /
        (1 + f x) ^ ((1 + beta) * q)) = _
  rw [intervalDomainIntegral]
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hy
  simp [intervalDomainLift, intervalDomainGradNorm, hy]

theorem intervalDomain_power_integral_lift'
    {f : intervalDomain.Point → ℝ} {q : ℝ} :
    intervalDomain.integral (fun x => f x ^ q) =
      ∫ y in (0 : ℝ)..1, intervalDomainLift f y ^ q := by
  change intervalDomainIntegral (fun x => f x ^ q) = _
  rw [intervalDomainIntegral]
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hy
  simp [intervalDomainLift, hy]

/-- A fixed Young coefficient for the elliptic source estimate.  The
definition depends only on the equation parameters and the exponent, not on
the solution or its time horizon. -/
def ellipticSourceYoungConstant (p : CM2Params) (q : ℝ) : ℝ :=
  if hq : 1 < q then
    Classical.choose (elliptic_source_young_exists p.hμ p.hν hq)
  else 1

theorem ellipticSourceYoungConstant_pos
    (p : CM2Params) {q : ℝ} (hq : 1 < q) :
    0 < ellipticSourceYoungConstant p q := by
  simp only [ellipticSourceYoungConstant, dif_pos hq]
  exact (Classical.choose_spec
    (elliptic_source_young_exists p.hμ p.hν hq)).1

theorem ellipticSourceYoungConstant_bound
    (p : CM2Params) {q : ℝ} (hq : 1 < q) :
    ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      p.ν * A * B ^ (q - 1) ≤
        p.μ / 2 * B ^ q + ellipticSourceYoungConstant p q * A ^ q := by
  simp only [ellipticSourceYoungConstant, dif_pos hq]
  exact (Classical.choose_spec
    (elliptic_source_young_exists p.hμ p.hν hq)).2

/-- Explicit horizon-independent coefficient in the weighted elliptic
gradient estimate. -/
def intervalDomainWeightedGradientConstant (p : CM2Params) (q : ℝ) : ℝ :=
  p.μ ^ q * (2 * ellipticSourceYoungConstant p q / p.μ)

theorem intervalDomainWeightedGradientConstant_pos
    (p : CM2Params) {q : ℝ} (hq : 1 < q) :
    0 < intervalDomainWeightedGradientConstant p q := by
  unfold intervalDomainWeightedGradientConstant
  exact mul_pos (Real.rpow_pos_of_pos p.hμ _)
    (div_pos (mul_pos (by norm_num) (ellipticSourceYoungConstant_pos p hq)) p.hμ)

/-- Explicit-coefficient version of the weighted gradient estimate. -/
theorem intervalDomain_weightedGradientEstimate_of_classical_beta_explicit
    {p : CM2Params} {T q beta : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hq : 1 < q) (hbeta : 0 ≤ beta) :
    WeightedGradientEstimate intervalDomain q beta p.γ
      (intervalDomainWeightedGradientConstant p q) T u v := by
  let C0 : ℝ := ellipticSourceYoungConstant p q
  have hC0 : 0 < C0 := ellipticSourceYoungConstant_pos p hq
  have hY := ellipticSourceYoungConstant_bound p hq
  let Mstar : ℝ := intervalDomainWeightedGradientConstant p q
  intro t ht0 htT
  let V : ℝ → ℝ := intervalDomainLift (v t)
  let U : ℝ → ℝ := intervalDomainLift (u t)
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hVpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < V x := by
    simpa [V] using intervalDomain_solution_lift_v_pos_Icc hsol ht0 htT
  have hVcont : ContinuousOn V (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.1.continuousOn
  have hdVcont : ContinuousOn (deriv V) (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using
      (resolverGradReal_contDiffOn_Icc hsol ht).continuousOn.congr
        (fun x hx => solution_lift_v_deriv_eq_resolverGrad_Icc hsol ht hx)
  have hlog : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv V x| ≤ Real.sqrt p.μ * V x := by
    simpa [V] using intervalDomain_elliptic_log_gradient_bound hsol ht0 htT
  have hVqcont : ContinuousOn (fun x => V x ^ q) (Set.Icc (0 : ℝ) 1) :=
    hVcont.rpow_const (fun x hx => Or.inl (ne_of_gt (hVpos x hx)))
  have hVqint : IntervalIntegrable (fun x => V x ^ q) volume 0 1 := by
    have hc : ContinuousOn (fun x => V x ^ q) (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hVqcont
    exact hc.intervalIntegrable
  have hnumcont : ContinuousOn (fun x => |deriv V x| ^ (2 * q))
      (Set.Icc (0 : ℝ) 1) := by
    exact hdVcont.abs.rpow_const (fun _ _ => Or.inr (by linarith))
  have hfirstCont : ContinuousOn
      (fun x => |deriv V x| ^ (2 * q) / V x ^ q) (Set.Icc (0 : ℝ) 1) :=
    hnumcont.div hVqcont
      (fun x hx => ne_of_gt (Real.rpow_pos_of_pos (hVpos x hx) q))
  have hfirstInt : IntervalIntegrable
      (fun x => |deriv V x| ^ (2 * q) / V x ^ q) volume 0 1 := by
    have hc : ContinuousOn (fun x => |deriv V x| ^ (2 * q) / V x ^ q)
        (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hfirstCont
    exact hc.intervalIntegrable
  have hfirstRaw :
      (∫ x in (0 : ℝ)..1, |deriv V x| ^ (2 * q) / V x ^ q) ≤
        p.μ ^ q * (∫ x in (0 : ℝ)..1, V x ^ q) := by
    calc
      (∫ x in (0 : ℝ)..1, |deriv V x| ^ (2 * q) / V x ^ q) ≤
          ∫ x in (0 : ℝ)..1, p.μ ^ q * V x ^ q :=
        intervalIntegral.integral_mono_on (by norm_num) hfirstInt
          (hVqint.const_mul (p.μ ^ q))
          (fun x hx => elliptic_log_weight_pointwise p.hμ hq (hVpos x hx) (hlog x hx))
      _ = p.μ ^ q * (∫ x in (0 : ℝ)..1, V x ^ q) := by
        rw [intervalIntegral.integral_const_mul]
  have hpower := intervalDomain_elliptic_power_estimate_of_young
    hsol ht0 htT hq hC0 hY
  have hfirstFinal :
      (∫ x in (0 : ℝ)..1, |deriv V x| ^ (2 * q) / V x ^ q) ≤
        Mstar * (∫ x in (0 : ℝ)..1, U x ^ (p.γ * q)) := by
    calc
      _ ≤ p.μ ^ q * (∫ x in (0 : ℝ)..1, V x ^ q) := hfirstRaw
      _ ≤ p.μ ^ q * ((2 * C0 / p.μ) *
          (∫ x in (0 : ℝ)..1, U x ^ (p.γ * q))) :=
        mul_le_mul_of_nonneg_left (by simpa [V, U] using hpower)
          (Real.rpow_nonneg p.hμ.le q)
      _ = Mstar * (∫ x in (0 : ℝ)..1, U x ^ (p.γ * q)) := by
        dsimp [Mstar, intervalDomainWeightedGradientConstant, C0]
        ring
  have hbaseCont : ContinuousOn (fun x => 1 + V x) (Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.add hVcont
  have hdenCont : ContinuousOn
      (fun x => (1 + V x) ^ ((1 + beta) * q)) (Set.Icc (0 : ℝ) 1) :=
    hbaseCont.rpow_const (fun x hx => Or.inl (by
      have := hVpos x hx
      positivity))
  have hsecondCont : ContinuousOn
      (fun x => |deriv V x| ^ (2 * q) / (1 + V x) ^ ((1 + beta) * q))
      (Set.Icc (0 : ℝ) 1) :=
    hnumcont.div hdenCont (fun x hx => ne_of_gt
      (Real.rpow_pos_of_pos (by have := hVpos x hx; linarith) _))
  have hsecondInt : IntervalIntegrable
      (fun x => |deriv V x| ^ (2 * q) / (1 + V x) ^ ((1 + beta) * q))
      volume 0 1 := by
    have hc : ContinuousOn
        (fun x => |deriv V x| ^ (2 * q) / (1 + V x) ^ ((1 + beta) * q))
        (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hsecondCont
    exact hc.intervalIntegrable
  have htheta_nonneg : 0 ≤ Theta_beta beta ^ q :=
    Real.rpow_nonneg (Theta_beta_pos_of_nonneg hbeta).le _
  have hsecondRaw :
      (∫ x in (0 : ℝ)..1,
        |deriv V x| ^ (2 * q) / (1 + V x) ^ ((1 + beta) * q)) ≤
      (Theta_beta beta) ^ q *
        (p.μ ^ q * (∫ x in (0 : ℝ)..1, V x ^ q)) := by
    calc
      _ ≤ ∫ x in (0 : ℝ)..1,
          (Theta_beta beta) ^ q * (p.μ ^ q * V x ^ q) :=
        intervalIntegral.integral_mono_on (by norm_num) hsecondInt
          (by simpa [mul_assoc] using
            hVqint.const_mul ((Theta_beta beta) ^ q * p.μ ^ q))
          (fun x hx => by
            simpa [mul_assoc] using elliptic_denominator_weight_pointwise
              p.hμ hbeta hq (hVpos x hx) (hlog x hx))
      _ = (Theta_beta beta) ^ q *
          (p.μ ^ q * (∫ x in (0 : ℝ)..1, V x ^ q)) := by
        rw [show (fun x => (Theta_beta beta) ^ q * (p.μ ^ q * V x ^ q)) =
            fun x => ((Theta_beta beta) ^ q * p.μ ^ q) * V x ^ q by
              funext x; ring,
          intervalIntegral.integral_const_mul]
        ring
  have hsecondFinal :
      (∫ x in (0 : ℝ)..1,
        |deriv V x| ^ (2 * q) / (1 + V x) ^ ((1 + beta) * q)) ≤
      (Theta_beta beta) ^ q * Mstar *
        (∫ x in (0 : ℝ)..1, U x ^ (p.γ * q)) := by
    calc
      _ ≤ (Theta_beta beta) ^ q *
          (p.μ ^ q * (∫ x in (0 : ℝ)..1, V x ^ q)) := hsecondRaw
      _ ≤ (Theta_beta beta) ^ q *
          (p.μ ^ q * ((2 * C0 / p.μ) *
            (∫ x in (0 : ℝ)..1, U x ^ (p.γ * q)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (by simpa [V, U] using hpower)
            (Real.rpow_nonneg p.hμ.le q)) htheta_nonneg
      _ = (Theta_beta beta) ^ q * Mstar *
          (∫ x in (0 : ℝ)..1, U x ^ (p.γ * q)) := by
        dsimp [Mstar, intervalDomainWeightedGradientConstant, C0]
        ring
  constructor
  · rw [intervalDomain_weighted_v_integral_lift,
      intervalDomain_power_integral_lift']
    simpa [V, U] using hfirstFinal
  · rw [intervalDomain_weighted_one_add_v_integral_lift,
      intervalDomain_power_integral_lift']
    simpa [V, U] using hsecondFinal

theorem intervalDomain_weightedGradientEstimate_of_classical_beta
    {p : CM2Params} {T q beta : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hq : 1 < q) (hbeta : 0 ≤ beta) :
    ∃ Mstar > 0, WeightedGradientEstimate intervalDomain q beta p.γ Mstar T u v := by
  exact ⟨intervalDomainWeightedGradientConstant p q,
    intervalDomainWeightedGradientConstant_pos p hq,
    intervalDomain_weightedGradientEstimate_of_classical_beta_explicit
      hsol hq hbeta⟩

/-- Explicit-constant form of Paper 2, Proposition 2.2 with the signal-weight
parameter named `eta`.  The hypotheses deliberately impose no relation
between `q` and `eta`: the estimate holds for every `q > 1` and every
`eta ≥ 0`. -/
theorem intervalDomain_signalWeightedGradientEstimate_of_classical_explicit
    {p : CM2Params} {T q eta : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hq : 1 < q) (heta : 0 ≤ eta) :
    WeightedGradientEstimate intervalDomain q eta p.γ
      (intervalDomainWeightedGradientConstant p q) T u v := by
  exact intervalDomain_weightedGradientEstimate_of_classical_beta_explicit
    hsol hq heta

/-- Existential-constant form of the general signal-weight estimate.  The
later critical specialization `eta = 2 * beta - 1` is a separate use of this
theorem, not an admissibility condition here. -/
theorem intervalDomain_signalWeightedGradientEstimate_of_classical
    {p : CM2Params} {T q eta : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hq : 1 < q) (heta : 0 ≤ eta) :
    ∃ Mstar > 0,
      WeightedGradientEstimate intervalDomain q eta p.γ Mstar T u v := by
  exact ⟨intervalDomainWeightedGradientConstant p q,
    intervalDomainWeightedGradientConstant_pos p hq,
    intervalDomain_signalWeightedGradientEstimate_of_classical_explicit
      hsol hq heta⟩

theorem intervalDomain_weightedGradientEstimate_of_classical
    {p : CM2Params} {T q : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hq : 1 < q) :
    ∃ Mstar > 0, WeightedGradientEstimate intervalDomain q p.β p.γ Mstar T u v :=
  intervalDomain_weightedGradientEstimate_of_classical_beta hsol hq p.hβ

/-- Concrete interval-domain realization of Paper 2, Proposition 2.2. -/
theorem intervalDomain_Proposition_2_2 (p : CM2Params) :
    Proposition_2_2 intervalDomain p := by
  intro T _hT u v hsol q hq
  exact intervalDomain_weightedGradientEstimate_of_classical hsol hq

#print axioms intervalDomain_elliptic_log_gradient_bound
#print axioms intervalDomain_elliptic_power_preestimate
#print axioms intervalDomain_signalWeightedGradientEstimate_of_classical_explicit
#print axioms intervalDomain_signalWeightedGradientEstimate_of_classical
#print axioms intervalDomain_weightedGradientEstimate_of_classical
#print axioms intervalDomain_Proposition_2_2

end ShenWork.Paper2
