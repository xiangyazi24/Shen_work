import ShenWork.Paper2.IntervalDomainMPhysicalRestart

/-!
# Elliptic resolver agreement for the faithful general-`m` equation

The elliptic equation is independent of the chemotactic power `m`.  This file
repeats only the domain-sensitive coefficient extraction needed to identify the
chemical slice of an `intervalDomainM` classical solution with the Neumann
resolver.  The reconstruction and resolver estimates are the shared, proved
unit-interval infrastructure.
-/

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainM

open ShenWork.IntervalEllipticCharacterization
open ShenWork.PDE
open ShenWork.Paper3
open ShenWork.IntervalCosineInversion
open ShenWork.IntervalResolverWeakBounds
open ShenWork.IntervalResolverGradientBridge
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

/-- The cosine coefficients of a faithful classical chemical slice satisfy
the diagonal elliptic equation.  The parabolic flux field is not used. -/
theorem solution_v_rawCoeff_ellipticM
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (k : ℕ) :
    (p.μ + ((k : ℝ) * Real.pi) ^ 2) *
        (∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) *
          intervalDomainLift (v t) x) =
      ∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) *
        (p.ν * intervalDomainLift (u t) x ^ p.γ) := by
  classical
  have hreg : intervalDomainClassicalRegularity T u v := hsol.regularity
  have h7 := (hreg.2.2.2.2.1 t ht).2
  obtain ⟨hC2, hbc0, hbc1⟩ := h7
  have h6 := (hreg.2.2.2.1 t ht).2
  obtain ⟨htend0, htend1⟩ := h6
  set V : ℝ → ℝ := intervalDomainLift (v t) with hV
  have hIBP := intervalCosineLaplacianCoeff_eq_of_contDiffOn
    k hC2 htend0 htend1 hbc0 hbc1
  have hpde : ∀ x : ℝ, x ∈ Ioo (0 : ℝ) 1 →
      deriv (deriv V) x = p.μ * V x - p.ν * intervalDomainLift (u t) x ^ p.γ := by
    intro x hx
    have hxIcc : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx
    set xp : intervalDomainPoint := ⟨x, hxIcc⟩ with hxp
    have hxIn : xp ∈ intervalDomainM.inside := hx
    have hpv := hsol.pde_v ht.1 ht.2 hxIn
    have hlap : intervalDomainM.laplacian (v t) xp = deriv (deriv V) x := by
      show intervalDomainLaplacian (v t) xp = deriv (deriv V) x
      simp only [intervalDomainLaplacian, hV, hxp]
    have hvval : v t xp = V x := by
      simp only [hV, intervalDomainLift, hxIcc, dif_pos, hxp]
    have huval : (u t xp) ^ p.γ = intervalDomainLift (u t) x ^ p.γ := by
      simp only [intervalDomainLift, hxIcc, dif_pos, hxp]
    rw [hlap, hvval, huval] at hpv
    linarith [hpv]
  have hint_eq :
      (∫ x in (0 : ℝ)..1,
          Real.cos ((k : ℝ) * Real.pi * x) * deriv (deriv V) x) =
        ∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) *
          (p.μ * V x - p.ν * intervalDomainLift (u t) x ^ p.γ) := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hnull : volume ({(1 : ℝ)} : Set ℝ) = 0 := by simp
    refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    push_neg at hx
    obtain ⟨hxIoc, hne⟩ := hx
    simp only [Set.mem_singleton_iff]
    by_contra hx1
    have hxIoo : x ∈ Ioo (0 : ℝ) 1 :=
      ⟨hxIoc.1, lt_of_le_of_ne hxIoc.2 hx1⟩
    exact hne (by rw [hpde x hxIoo])
  rw [hint_eq] at hIBP
  have hsplit :
      (∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) *
          (p.μ * V x - p.ν * intervalDomainLift (u t) x ^ p.γ)) =
        p.μ * (∫ x in (0 : ℝ)..1,
          Real.cos ((k : ℝ) * Real.pi * x) * V x) -
          (∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) *
            (p.ν * intervalDomainLift (u t) x ^ p.γ)) := by
    have hVcont : ContinuousOn V (Set.uIcc (0 : ℝ) 1) :=
      continuousOn_of_contDiffOn_two hC2
    have hUcont : ContinuousOn (intervalDomainLift (u t))
        (Set.uIcc (0 : ℝ) 1) := by
      have hC2u := (hreg.2.2.2.2.1 t ht).1.1
      exact continuousOn_of_contDiffOn_two hC2u
    have hcos_cont : ContinuousOn
        (fun x : ℝ => Real.cos ((k : ℝ) * Real.pi * x))
        (Set.uIcc (0 : ℝ) 1) :=
      (Real.continuous_cos.comp (by fun_prop)).continuousOn
    have hUpow : ContinuousOn
        (fun x : ℝ => intervalDomainLift (u t) x ^ p.γ)
        (Set.uIcc (0 : ℝ) 1) :=
      hUcont.rpow_const (fun _ _ => Or.inr p.hγ.le)
    have hII1 : IntervalIntegrable
        (fun x => p.μ * (Real.cos ((k : ℝ) * Real.pi * x) * V x))
        volume 0 1 := by
      exact (continuousOn_const.mul (hcos_cont.mul hVcont)).intervalIntegrable
    have hII2 : IntervalIntegrable
        (fun x => Real.cos ((k : ℝ) * Real.pi * x) *
          (p.ν * intervalDomainLift (u t) x ^ p.γ)) volume 0 1 := by
      exact (hcos_cont.mul (continuousOn_const.mul hUpow)).intervalIntegrable
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub hII1 hII2]
    refine intervalIntegral.integral_congr ?_
    intro x _
    ring
  rw [hsplit] at hIBP
  have hexpand : (p.μ + ((k : ℝ) * Real.pi) ^ 2) *
      (∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) * V x) =
        p.μ * (∫ x in (0 : ℝ)..1,
          Real.cos ((k : ℝ) * Real.pi * x) * V x) +
        ((k : ℝ) * Real.pi) ^ 2 *
          (∫ x in (0 : ℝ)..1,
            Real.cos ((k : ℝ) * Real.pi * x) * V x) := by ring
  rw [hexpand]
  linarith [hIBP]

/-- The resolver coefficient equals the cosine coefficient of the actual
chemical slice for the faithful domain. -/
theorem solution_v_resolverCoeff_eqM
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (k : ℕ) :
    (intervalNeumannResolverCoeff p (u t) k).re =
      cosineCoeffs (intervalDomainLift (v t)) k := by
  classical
  set Iv : ℝ := ∫ x in (0 : ℝ)..1,
    Real.cos ((k : ℝ) * Real.pi * x) * intervalDomainLift (v t) x with hIv
  set Is : ℝ := ∫ x in (0 : ℝ)..1,
    Real.cos ((k : ℝ) * Real.pi * x) *
      (p.ν * intervalDomainLift (u t) x ^ p.γ) with hIs
  set fac : ℝ := if k = 0 then (1 : ℝ) else 2 with hfac
  have hden_pos : 0 < p.μ + ((k : ℝ) * Real.pi) ^ 2 :=
    add_pos_of_pos_of_nonneg p.hμ (sq_nonneg _)
  have hB : (p.μ + ((k : ℝ) * Real.pi) ^ 2) * Iv = Is :=
    solution_v_rawCoeff_ellipticM hsol ht k
  have hres := intervalNeumannResolverCoeff_elliptic p (u t) k
  have hresRe :
      (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) *
          (intervalNeumannResolverCoeff p (u t) k).re =
        (intervalNeumannResolverSourceCoeff p (u t) k).re := by
    have hcast :
        ((p.μ : ℂ) + (unitIntervalNeumannSpectrum.eigenvalue k : ℂ)) =
          (((p.μ + unitIntervalNeumannSpectrum.eigenvalue k : ℝ)) : ℂ) := by
      push_cast
      ring
    have hk := congrArg Complex.re hres
    rw [hcast, Complex.re_ofReal_mul] at hk
    exact hk
  have hlam : unitIntervalNeumannSpectrum.eigenvalue k =
      ((k : ℝ) * Real.pi) ^ 2 := by
    change (k : ℝ) ^ 2 * Real.pi ^ 2 = _
    ring
  rw [hlam] at hresRe
  rw [sourceCoeff_re_eq] at hresRe
  rw [cosineCoeffs_lift_eq]
  have hIvfac : (p.μ + ((k : ℝ) * Real.pi) ^ 2) * (fac * Iv) = fac * Is := by
    rw [show (p.μ + ((k : ℝ) * Real.pi) ^ 2) * (fac * Iv) =
      fac * ((p.μ + ((k : ℝ) * Real.pi) ^ 2) * Iv) by ring, hB]
  have hcancel : (p.μ + ((k : ℝ) * Real.pi) ^ 2) *
      (intervalNeumannResolverCoeff p (u t) k).re =
      (p.μ + ((k : ℝ) * Real.pi) ^ 2) * (fac * Iv) := by
    rw [hIvfac]
    rw [← hfac, ← hIs] at hresRe
    exact hresRe
  exact mul_left_cancel₀ (ne_of_gt hden_pos) hcancel

/-- Pointwise resolver identification on the open spatial interval. -/
theorem solution_v_eq_resolver_pointwiseM
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    intervalNeumannResolverR p (u t) ⟨x, Ioo_subset_Icc_self hx⟩ =
      intervalDomainLift (v t) x := by
  classical
  have hreg : intervalDomainClassicalRegularity T u v := hsol.regularity
  obtain ⟨hC2v, hbc0, hbc1⟩ := (hreg.2.2.2.2.1 t ht).2
  obtain ⟨htend0, htend1⟩ := (hreg.2.2.2.1 t ht).2
  let F : ℝ → ℝ := liftRepr (v t)
  have hVcontOn : ContinuousOn (intervalDomainLift (v t)) (Icc (0 : ℝ) 1) :=
    hC2v.continuousOn
  have hFcont : Continuous F := liftRepr_continuous hVcontOn
  have hFeqOn : ∀ y ∈ Icc (0 : ℝ) 1,
      F y = intervalDomainLift (v t) y := fun y hy => liftRepr_eq_on_Icc hy
  have hFcoeff : ∀ k,
      cosineCoeffs F k = cosineCoeffs (intervalDomainLift (v t)) k :=
    fun k => cosineCoeffs_liftRepr k
  have hFsum : Summable (fun n : ℤ => fourierCoeff (reflCircle F) n) :=
    fourierCoeff_reflCircle_summable_of_repr
      hFcont hC2v hFeqOn htend0 htend1 hbc0 hbc1
  have hUcont : ContinuousOn (intervalDomainLift (u t)) (Icc (0 : ℝ) 1) :=
    (hreg.2.2.2.2.1 t ht).1.1.continuousOn
  have hsrcL2 : Summable fun k : ℕ =>
      ((intervalNeumannResolverSourceCoeff p (u t) k).re) ^ 2 := by
    simpa [intervalNeumannResolverSourceCoeff_zero, sub_zero] using
      resolverSourceCoeff_re_sq_summable_of_continuousOn p hUcont
  have hRsum := resolver_cosineSeries_summable_of_sourceL2 p hsrcL2 x
  have hinv : HasSum
      (fun k => unitIntervalCosineMode k x * cosineCoeffs F k) (F x) :=
    intervalCosine_hasSum_pointwise F hFcont hx hFsum
  have hterm : ∀ k : ℕ,
      unitIntervalCosineMode k x * cosineCoeffs F k =
        (intervalNeumannResolverCoeff p (u t) k).re *
          unitIntervalCosineMode k x := by
    intro k
    rw [hFcoeff k, ← solution_v_resolverCoeff_eqM hsol ht k]
    ring
  have hinv' : HasSum
      (fun k => (intervalNeumannResolverCoeff p (u t) k).re *
        unitIntervalCosineMode k x) (F x) := by
    refine hinv.congr_fun ?_
    intro k
    exact (hterm k).symm
  rw [show intervalNeumannResolverR p (u t) ⟨x, Ioo_subset_Icc_self hx⟩ =
      ∑' k : ℕ, (intervalNeumannResolverCoeff p (u t) k).re *
        unitIntervalCosineMode k x by simp only [intervalNeumannResolverR],
    hinv'.tsum_eq, hFeqOn x (Ioo_subset_Icc_self hx)]

/-- The chemical derivative agrees with the resolver gradient on the closed
unit interval; endpoint equality is the common Neumann value zero. -/
theorem solution_lift_v_deriv_eq_resolverGrad_IccM
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    deriv (intervalDomainLift (v t)) x = resolverGradReal p (u t) x := by
  rcases eq_or_lt_of_le hx.1 with rfl | hx0
  · rw [(hsol.regularity.2.2.2.2.1 t ht).2.2.1]
    exact (ShenWork.Paper2.resolverGradReal_zero p (u t)).symm
  · rcases eq_or_lt_of_le hx.2 with rfl | hx1
    · rw [(hsol.regularity.2.2.2.2.1 t ht).2.2.2]
      exact (ShenWork.Paper2.resolverGradReal_one p (u t)).symm
    · have hxIoo : x ∈ Ioo (0 : ℝ) 1 := ⟨hx0, hx1⟩
      have hUcont : ContinuousOn (intervalDomainLift (u t)) (Icc (0 : ℝ) 1) :=
        (hsol.regularity.2.2.2.2.1 t ht).1.1.continuousOn
      have hRderiv :=
        intervalNeumannResolverR_lift_hasDerivAt_resolverGradReal_of_continuousOn
          p hUcont hxIoo
      have hEq : intervalDomainLift (v t) =ᶠ[nhds x]
          fun z => intervalDomainLift (intervalNeumannResolverR p (u t)) z := by
        refine eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hxIoo) ?_
        intro z hz
        have hzIcc := Ioo_subset_Icc_self hz
        simpa [intervalDomainLift, hzIcc] using
          (solution_v_eq_resolver_pointwiseM hsol ht hz).symm
      rw [hEq.deriv_eq, hRderiv.deriv]

#print axioms solution_v_rawCoeff_ellipticM
#print axioms solution_v_eq_resolver_pointwiseM
#print axioms solution_lift_v_deriv_eq_resolverGrad_IccM

end ShenWork.Paper2.IntervalDomainM
