/-
  ShenWork/Paper2/ChemMildHolderBootstrap.lean

  **Paper2 Theorem 1.1 (χ₀ < 0) — P2-T11 hregularize pass-1 CAPSTONE:
  the mild fixed point is Hölder for positive time.**

  GOAL (`mild_orderBox_positiveTime_holder`): the divergence-form mild fixed point
  `u` (an `IntervalGradientDuhamelMap.IntervalMildSolution`, packaged as
  `IntervalMildPicard.GradientMildSolutionData`) satisfies, at every time `t ∈ [τ,T]`
  with `τ > 0`, a fractional Hölder modulus

    `|u(t,x) − u(t,y)| ≤ K · |x − y|^θ`   (`0 < θ < 1`),

  with `K` depending only on `τ, T, M, χ₀, p`.  This is pure PLUMBING: it applies
  the now-committed heat-semigroup Hölder-smoothing of `ShenWork/Paper2/ChemMildHolder`
  leg-by-leg to the three terms of the mild representation
    `u(t) = S(t)u₀  −  χ₀ ∫₀ᵗ ∂ₓS(t−s)Q(u(s)) ds  +  ∫₀ᵗ S(t−s)L(u(s)) ds`.

  ROUTE
  * Generic core `holder_of_duhamel_integral` — integral-Minkowski: if the per-slice
    Hölder bounds `|G s x − G s y| ≤ φ s · |x−y|^θ` hold a.e. on `[0,t]` and both
    `s↦G s x`, `s↦G s y`, `s↦φ s |x−y|^θ` are interval-integrable, then
    `|∫G s x − ∫G s y| ≤ (∫φ) · |x−y|^θ`.
  * Leg `S(t)u₀`:  `neumannHeat_Linf_to_Ctheta` with `Cf = M`.
  * Reaction leg `∫S(t−s)L(u(s))`:  per-slice `neumannHeat_Linf_to_Ctheta`
    (`Cf = C_L = M(a+bMᵅ)`), integrand `(t−s)^{−θ/2}` integrable
    (`duhamel_holder_time_integrand_integrable`).
  * Chemotaxis leg `∫∂ₓS(t−s)Q(u(s))`:  per-slice GRADIENT Hölder
    `neumannHeatGradient_Linf_to_Ctheta` (`Cf = C_Q`), integrand `(t−s)^{−(1+θ)/2}`
    integrable iff `θ < 1` (`duhamel_holder_gradTime_integrand_integrable`).

  The order-box uniform source bounds and joint measurability are re-derived from the
  `GradientMildSolutionData` side conditions (`hbound`, `hnonneg`, `hcont`, `hmeas`)
  via the committed source lemmas.  The statement is over `intervalDomainPoint`
  (the genuine domain of `u`); the zero-extension `intervalDomainLift (u t)` is NOT
  globally Hölder on `ℝ` since `u` is strictly positive at the endpoints (`hpos`).

  This file is intended to stay free of proof-gap placeholders and custom trust hooks.
-/
import ShenWork.Paper2.ChemMildHolder
import ShenWork.Paper2.IntervalDuhamelIntegrability
import ShenWork.Paper2.IntervalMildPicard

open MeasureTheory Filter
open ShenWork.IntervalDomain (intervalMeasure intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalGradientDuhamelMap
  (chemFluxLifted logisticLifted intervalGradientDuhamelMap IntervalMildSolution)
open ShenWork.IntervalMildPicard
  (HasJointMeasurability HasContinuousSlices GradientMildSolutionData)
open ShenWork.IntervalDuhamelIntegrability
  (intervalDomainLift_aestronglyMeasurable_of_continuous)

namespace ShenWork.Paper2

noncomputable section

/-! ## Generic integral-Minkowski Hölder core -/

/-- **Integral-Minkowski Hölder core.**  If `s ↦ G s a` and `s ↦ G s b` are
interval-integrable on `[0,t]`, the per-slice difference is a.e. dominated by
`φ s · |a−b|^θ`, and `s ↦ φ s` is interval-integrable, then the *integrals* obey
the same Hölder bound with constant `∫₀ᵗ φ`:

  `|∫₀ᵗ G s a ds − ∫₀ᵗ G s b ds| ≤ (∫₀ᵗ φ s ds) · |a − b|^θ`.

This is the only mild-representation algebra the Duhamel legs need: it turns the
committed per-slice heat Hölder bounds into a Hölder bound on the Duhamel integral. -/
theorem holder_of_duhamel_integral {t : ℝ} (ht : 0 ≤ t)
    {G : ℝ → ℝ} {H : ℝ → ℝ} {φ : ℝ → ℝ} {dxy : ℝ}
    (hG : IntervalIntegrable G volume 0 t)
    (hH : IntervalIntegrable H volume 0 t)
    (hφ : IntervalIntegrable φ volume 0 t)
    (hbound : ∀ᵐ s ∂(volume.restrict (Set.Icc 0 t)), |G s - H s| ≤ φ s * dxy) :
    |(∫ s in (0:ℝ)..t, G s) - (∫ s in (0:ℝ)..t, H s)|
      ≤ (∫ s in (0:ℝ)..t, φ s) * dxy := by
  rw [← intervalIntegral.integral_sub hG hH]
  calc |∫ s in (0:ℝ)..t, (G s - H s)|
      ≤ ∫ s in (0:ℝ)..t, |G s - H s| :=
        intervalIntegral.abs_integral_le_integral_abs ht
    _ ≤ ∫ s in (0:ℝ)..t, φ s * dxy :=
        intervalIntegral.integral_mono_ae_restrict ht (hG.sub hH).abs (hφ.mul_const dxy) hbound
    _ = (∫ s in (0:ℝ)..t, φ s) * dxy := by
        rw [intervalIntegral.integral_mul_const]

/-! ## The gradient Duhamel time integrand is integrable for `θ < 1` -/

/-- **Gradient-Duhamel Hölder time integrand integrability.**  The chemotaxis leg,
after applying the GRADIENT Hölder lemma slice-by-slice, produces the time integrand
`(t − s)^{−(1+θ)/2}`, integrable on `[0,t]` iff `(1+θ)/2 < 1`, i.e. `θ < 1`. -/
theorem duhamel_holder_gradTime_integrand_integrable {t θ : ℝ} (_ht : 0 < t)
    (_hθ0 : 0 < θ) (hθ1 : θ < 1) :
    IntervalIntegrable (fun s : ℝ => (t - s) ^ (-((1 + θ) / 2) : ℝ)) volume 0 t := by
  have hr : (-1 : ℝ) < -((1 + θ) / 2) := by linarith
  have hcomp : IntervalIntegrable (fun s : ℝ => s ^ (-((1 + θ) / 2) : ℝ)) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t) hr
  have hshift := hcomp.comp_sub_left t
  simp only [sub_zero, sub_self] at hshift
  exact hshift.symm

/-! ## Per-slice source data on the order box -/

/-- Joint measurability of the reaction source family `(s,y) ↦ L(u(s))(y)` from the
order-box trajectory's joint measurability.  Re-derived (the codebase version is
`private`) directly from `hmeas` — `L` is a polynomial in `u`, no resolver. -/
theorem logisticLifted_uncurry_measurable {p : CM2Params}
    {u : ℝ → intervalDomainPoint → ℝ} (hmeas : HasJointMeasurability u) :
    Measurable (Function.uncurry (fun s => logisticLifted p (u s))) := by
  have h_rpow : Measurable (fun x : ℝ => x ^ p.α) := by fun_prop
  have hpow : Measurable (fun q : ℝ × ℝ => (intervalDomainLift (u q.1) q.2) ^ p.α) :=
    h_rpow.comp hmeas
  have hpoly : Measurable (fun q : ℝ × ℝ =>
      intervalDomainLift (u q.1) q.2 *
        (p.a - p.b * (intervalDomainLift (u q.1) q.2) ^ p.α)) :=
    hmeas.mul (measurable_const.sub (measurable_const.mul hpow))
  rw [show Function.uncurry (fun s => logisticLifted p (u s)) =
      fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2 *
        (p.a - p.b * (intervalDomainLift (u q.1) q.2) ^ p.α) by
    funext q
    by_cases hy : q.2 ∈ Set.Icc (0 : ℝ) 1
    · simp [Function.uncurry, logisticLifted,
        ShenWork.IntervalDomainExistence.intervalLogisticSource, intervalDomainLift, hy]
    · simp [Function.uncurry, logisticLifted, intervalDomainLift, hy]]
  exact hpoly

/-- Uniform order-box bound on the reaction source: `|L(u(s))(y)| ≤ M(a+bMᵅ)`. -/
theorem logisticLifted_orderBox_bound {p : CM2Params} {M : ℝ} (hM : 0 < M)
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hbound : ∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M)
    (s : ℝ) (hs0 : 0 < s) (hsT : s ≤ T) (y : ℝ) :
    |logisticLifted p (u s) y| ≤ M * (p.a + p.b * M ^ p.α) :=
  ShenWork.IntervalDomainExistence.intervalLogisticSource_lift_abs_bound
    p hM (fun x => hbound s hs0 hsT x) y

/-! ## Leg lemmas (Hölder seminorm of each mild term) -/

/-- **Leg 1 — the `S(t)u₀` term is Hölder.**  Direct application of the committed
value Hölder bound with `Cf = M` (the order-box bound on `u₀`). -/
theorem holderLeg_initial {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {t θ : ℝ} (ht : 0 < t) (hθ0 : 0 < θ) (hθ1 : θ < 1) (x y : intervalDomainPoint) :
    |intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
        - intervalFullSemigroupOperator t (intervalDomainLift u₀) y.1|
      ≤ (2 : ℝ) ^ (1 - θ) * gradSmoothingConst ^ θ
          * t ^ (-(θ / 2) : ℝ) * M * |x.1 - y.1| ^ θ :=
  neumannHeat_Linf_to_Ctheta ht hθ0 hθ1 hu₀_meas hu₀ x.1 y.1

/-- Per-slice continuity of the reaction source (subtype function). -/
theorem intervalLogisticSource_continuous {p : CM2Params} {w : intervalDomainPoint → ℝ}
    (hw : Continuous w) :
    Continuous (ShenWork.IntervalDomainExistence.intervalLogisticSource p w) := by
  unfold ShenWork.IntervalDomainExistence.intervalLogisticSource
  exact hw.mul (continuous_const.sub
    (continuous_const.mul (hw.rpow_const (fun _ => Or.inr p.hα.le))))

/-- **Leg 3 — the reaction Duhamel term `∫₀ᵗ S(t−s)L(u(s)) ds` is Hölder.**
Per-slice value Hölder (`Cf = C_L = M(a+bMᵅ)`) integrated against the integrable
time integrand `(t−s)^{−θ/2}` via `holder_of_duhamel_integral`. -/
theorem holderLeg_reaction {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {T M : ℝ} (hM : 0 < M)
    (hbound : ∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M)
    (hcont : HasContinuousSlices T u) (hmeas : HasJointMeasurability u)
    {t θ : ℝ} (ht : 0 < t) (htT : t ≤ T) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (x y : intervalDomainPoint) :
    |(∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x.1)
        - (∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) y.1)|
      ≤ (∫ s in (0:ℝ)..t,
            (2 : ℝ) ^ (1 - θ) * gradSmoothingConst ^ θ
              * (t - s) ^ (-(θ / 2) : ℝ) * (M * (p.a + p.b * M ^ p.α)))
        * |x.1 - y.1| ^ θ := by
  set CL : ℝ := M * (p.a + p.b * M ^ p.α) with hCL
  have hCL_nn : 0 ≤ CL := by
    rw [hCL]; exact mul_nonneg hM.le (by have := p.ha; have := p.hb; positivity)
  -- the time-cutoff source, globally bounded by CL, measurable, agreeing on (0,t]
  set f : ℝ → ℝ → ℝ :=
    fun s y => if 0 < s ∧ s ≤ T then logisticLifted p (u s) y else 0 with hf
  have hf_bdd : ∀ s yy, |f s yy| ≤ CL := by
    intro s yy; simp only [hf]; split_ifs with h
    · exact logisticLifted_orderBox_bound hM hbound s h.1 h.2 yy
    · simpa using hCL_nn
  have hf_meas : Measurable (Function.uncurry f) := by
    have hbase := logisticLifted_uncurry_measurable (p := p) (u := u) hmeas
    simp only [Function.uncurry] at hbase ⊢
    simp only [hf]
    refine Measurable.ite ?_ hbase measurable_const
    exact ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
      ((isClosed_Iic.preimage continuous_fst).measurableSet)
  -- raw source = cutoff source on (0,t]; the two interval integrals agree
  have hcongr : ∀ z : ℝ,
      (∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) z)
        = ∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s) (f s) z := by
    intro z
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun s hs => ?_))
    rw [Set.uIoc_of_le ht.le] at hs
    have hmem : (0 < s ∧ s ≤ T) := ⟨hs.1, le_trans hs.2 htT⟩
    simp only [hf, if_pos hmem]
  rw [hcongr x.1, hcongr y.1]
  -- φ s = 2^{1−θ} C∇^θ (t−s)^{−θ/2} CL, interval-integrable on [0,t]
  have hφ_int : IntervalIntegrable
      (fun s : ℝ => (2 : ℝ) ^ (1 - θ) * gradSmoothingConst ^ θ
        * (t - s) ^ (-(θ / 2) : ℝ) * CL) volume 0 t := by
    have h0 := duhamel_holder_time_integrand_integrable ht hθ0 (show θ < 2 by linarith)
    have h1 := h0.const_mul ((2 : ℝ) ^ (1 - θ) * gradSmoothingConst ^ θ)
    have h2 := h1.mul_const CL
    exact h2.congr (fun s _ => by ring)
  -- generic integral-Minkowski with per-slice value Hölder bound
  refine holder_of_duhamel_integral ht.le
    (ShenWork.IntervalDuhamelIntegrability.valueDuhamel_intervalIntegrable_of_joint_measurable
      ht hf_meas hCL_nn hf_bdd x.1)
    (ShenWork.IntervalDuhamelIntegrability.valueDuhamel_intervalIntegrable_of_joint_measurable
      ht hf_meas hCL_nn hf_bdd y.1)
    hφ_int ?_
  -- a.e. on [0,t]: the per-slice value Hölder bound
  have hne : ∀ᵐ s ∂volume, s ≠ t := by
    rw [ae_iff]; simp only [not_not, Set.setOf_eq_eq_singleton]; exact Real.volume_singleton
  refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
  filter_upwards [hne] with s hs_ne hs_mem
  have hts : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs_mem.2 hs_ne)
  have hfs_meas : AEStronglyMeasurable (f s) (intervalMeasure 1) := by
    simp only [hf]; by_cases h : 0 < s ∧ s ≤ T
    · simp only [if_pos h]
      exact intervalDomainLift_aestronglyMeasurable_of_continuous
        (intervalLogisticSource_continuous (hcont s h.1 h.2))
    · simp only [if_neg h]; exact aestronglyMeasurable_const
  exact neumannHeat_Linf_to_Ctheta hts hθ0 hθ1 hfs_meas (hf_bdd s) x.1 y.1

/-! ## Chemotaxis source: joint measurability (re-derived from the private chain) -/

private theorem measurable_tsum_nat' {α : Type*} [MeasurableSpace α]
    {f : ℕ → α → ℝ} (hf : ∀ n, Measurable (f n)) :
    Measurable (fun a : α => ∑' n : ℕ, f n a) := by
  classical
  let L := SummationFilter.unconditional ℕ
  set S : Finset ℕ → α → ℝ := fun s a => ∑ n ∈ s, f n a with hSdef
  have hS_meas : ∀ s, StronglyMeasurable (S s) := fun s =>
    (Finset.measurable_sum _ (fun n _ => hf n)).stronglyMeasurable
  set C : Set α := {a | ∃ c : ℝ, Tendsto (fun s : Finset ℕ => S s a) L.filter (nhds c)}
    with hCdef
  have hC_meas : MeasurableSet C := by
    simpa [C] using MeasureTheory.StronglyMeasurable.measurableSet_exists_tendsto
      (l := L.filter) (f := S) hS_meas
  have hlim_meas : Measurable (fun a : α =>
      L.filter.limUnder (fun s : Finset ℕ => S s a)) :=
    (MeasureTheory.StronglyMeasurable.limUnder (l := L.filter) hS_meas).measurable
  have h_eq : (fun a : α => ∑' n : ℕ, f n a) =
      fun a : α => if a ∈ C then L.filter.limUnder (fun s : Finset ℕ => S s a) else 0 := by
    funext a
    by_cases ha : a ∈ C
    · simp only [ha, if_true]
      rcases ha with ⟨c, hc⟩
      exact (Summable.hasSum ⟨c, hc⟩).limUnder_eq.symm
    · simp only [ha, if_false]
      exact tsum_eq_zero_of_not_summable (fun hs => ha ⟨∑' n : ℕ, f n a, hs.hasSum⟩)
  rw [h_eq]
  exact Measurable.ite hC_meas hlim_meas measurable_const

private theorem resolverSourceCoeff_time_measurable
    {p : CM2Params} {w : ℝ → intervalDomainPoint → ℝ}
    (hum : HasJointMeasurability w) (k : ℕ) :
    Measurable (fun s : ℝ => ShenWork.PDE.intervalNeumannResolverSourceCoeff p (w s) k) := by
  set src : ℝ → ℝ → ℂ :=
    fun s x => ((p.ν * intervalDomainLift (w s) x ^ p.γ : ℝ) : ℂ) with hsrc_def
  have hsrc_meas : Measurable (fun q : ℝ × ℝ => src q.1 q.2) := by
    have h_rpow : Measurable (fun x : ℝ => x ^ p.γ) := by fun_prop
    have hpow : Measurable (fun q : ℝ × ℝ =>
        intervalDomainLift (w q.1) q.2 ^ p.γ) := h_rpow.comp hum
    have hreal : Measurable (fun q : ℝ × ℝ =>
        p.ν * intervalDomainLift (w q.1) q.2 ^ p.γ) := measurable_const.mul hpow
    exact Complex.continuous_ofReal.measurable.comp hreal
  have hraw : ∀ n : ℕ, Measurable (fun s : ℝ =>
      ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff
        (fun x : ℝ => src s x) n) := by
    intro n
    set F : ℝ × ℝ → ℂ :=
      fun q => (Real.cos ((n : ℝ) * Real.pi * q.2) : ℂ) * src q.1 q.2 with hF_def
    have hF : Measurable F := by
      have hcos : Measurable (fun q : ℝ × ℝ =>
          (Real.cos ((n : ℝ) * Real.pi * q.2) : ℂ)) := by fun_prop
      exact hcos.mul hsrc_meas
    have hI : StronglyMeasurable (fun s : ℝ =>
        ∫ x : ℝ, F (s, x) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
      MeasureTheory.StronglyMeasurable.integral_prod_right'
        (ν := volume.restrict (Set.Ioc (0 : ℝ) 1)) hF.stronglyMeasurable
    have hfun : (fun s : ℝ =>
        ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff
          (fun x : ℝ => src s x) n) =
        fun s : ℝ => ∫ x : ℝ, F (s, x) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      funext s
      rw [ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff,
        intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    rw [hfun]; exact hI.measurable
  have hcoeff_real : Measurable (fun s : ℝ =>
      ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff
        (fun x : ℝ => src s x) k) := by
    by_cases hk : k = 0
    · subst k
      have hre : Measurable (fun s : ℝ =>
          (ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff
            (fun x : ℝ => src s x) 0).re) :=
        Complex.continuous_re.measurable.comp (hraw 0)
      simpa [ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff] using hre
    · have hre : Measurable (fun s : ℝ =>
          (ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff
            (fun x : ℝ => src s x) k).re) :=
        Complex.continuous_re.measurable.comp (hraw k)
      simpa [ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff, hk] using
        (measurable_const.mul hre)
  have hcomplex : Measurable (fun s : ℝ =>
      ((ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff
        (fun x : ℝ => src s x) k : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp hcoeff_real
  simpa [ShenWork.PDE.intervalNeumannResolverSourceCoeff, hsrc_def] using hcomplex

private theorem resolverCoeff_re_time_measurable
    {p : CM2Params} {w : ℝ → intervalDomainPoint → ℝ}
    (hum : HasJointMeasurability w) (k : ℕ) :
    Measurable (fun s : ℝ => (ShenWork.PDE.intervalNeumannResolverCoeff p (w s) k).re) := by
  have hsource := resolverSourceCoeff_time_measurable (p := p) (w := w) hum k
  have hcoeff : Measurable (fun s : ℝ =>
      ShenWork.PDE.intervalNeumannResolverCoeff p (w s) k) := by
    unfold ShenWork.PDE.intervalNeumannResolverCoeff
    unfold ShenWork.PDE.ResolventEstimate.shiftedNeumannResolventCoeff
    exact measurable_const.mul hsource
  exact Complex.continuous_re.measurable.comp hcoeff

private theorem resolverR_lift_uncurry_measurable
    {p : CM2Params} {w : ℝ → intervalDomainPoint → ℝ}
    (hum : HasJointMeasurability w) :
    Measurable (fun q : ℝ × ℝ =>
      intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p (w q.1)) q.2) := by
  have hseries : Measurable (fun q : ℝ × ℝ =>
      ∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverCoeff p (w q.1) k).re *
          unitIntervalCosineMode k q.2) := by
    refine measurable_tsum_nat' ?_
    intro k
    have hcoeff : Measurable (fun q : ℝ × ℝ =>
        (ShenWork.PDE.intervalNeumannResolverCoeff p (w q.1) k).re) :=
      (resolverCoeff_re_time_measurable (p := p) (w := w) hum k).comp measurable_fst
    have hmode : Measurable (fun q : ℝ × ℝ => unitIntervalCosineMode k q.2) := by
      unfold unitIntervalCosineMode; fun_prop
    exact hcoeff.mul hmode
  have hfun : (fun q : ℝ × ℝ =>
      intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p (w q.1)) q.2) =
      fun q : ℝ × ℝ =>
        if q.2 ∈ Set.Icc (0 : ℝ) 1 then
          ∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverCoeff p (w q.1) k).re *
              unitIntervalCosineMode k q.2
        else 0 := by
    funext q
    by_cases hy : q.2 ∈ Set.Icc (0 : ℝ) 1
    · simp [intervalDomainLift, ShenWork.PDE.intervalNeumannResolverR, hy]
    · simp [intervalDomainLift, hy]
  rw [hfun]
  exact Measurable.ite (measurableSet_Icc.preimage measurable_snd) hseries measurable_const

private theorem resolverGradReal_uncurry_measurable
    {p : CM2Params} {w : ℝ → intervalDomainPoint → ℝ}
    (hum : HasJointMeasurability w) :
    Measurable (fun q : ℝ × ℝ => ShenWork.Paper2.resolverGradReal p (w q.1) q.2) := by
  unfold ShenWork.Paper2.resolverGradReal
  refine measurable_tsum_nat' ?_
  intro k
  have hcoeff : Measurable (fun q : ℝ × ℝ =>
      (ShenWork.PDE.intervalNeumannResolverCoeff p (w q.1) k).re) :=
    (resolverCoeff_re_time_measurable (p := p) (w := w) hum k).comp measurable_fst
  have hmode : Measurable (fun q : ℝ × ℝ =>
      -((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * q.2)) := by fun_prop
  exact hcoeff.mul hmode

/-- Joint measurability of the chemotaxis source family `(s,y) ↦ Q(u(s))(y)`. -/
theorem chemFluxLifted_uncurry_measurable {p : CM2Params}
    {u : ℝ → intervalDomainPoint → ℝ} (hmeas : HasJointMeasurability u) :
    Measurable (Function.uncurry (fun s => chemFluxLifted p (u s))) := by
  have hR := resolverR_lift_uncurry_measurable (p := p) (w := u) hmeas
  have hG := resolverGradReal_uncurry_measurable (p := p) (w := u) hmeas
  have hden_base : Measurable (fun q : ℝ × ℝ =>
      1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p (u q.1)) q.2) :=
    measurable_const.add hR
  have h_rpow : Measurable (fun x : ℝ => x ^ p.β) := by fun_prop
  have hden : Measurable (fun q : ℝ × ℝ =>
      (1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p (u q.1)) q.2) ^ p.β) :=
    h_rpow.comp hden_base
  have hnum : Measurable (fun q : ℝ × ℝ =>
      intervalDomainLift (u q.1) q.2 * ShenWork.Paper2.resolverGradReal p (u q.1) q.2) :=
    hmeas.mul hG
  simpa [Function.uncurry, chemFluxLifted] using hnum.div hden

/-- Uniform order-box bound on the chemotaxis source (re-derived from the private
`chemFluxLifted_bound_of_ball`): `|Q(w)(y)| ≤ M·√(∑ gradWeightₖ²)·2νMᵞ`, using the
resolver positivity `(1+R)^β ≥ 1` and the L² gradient bound `|∂ₓR| ≤ C_RG`. -/
theorem chemFluxLifted_bound_of_ball'
    (p : CM2Params) {M : ℝ} (hM_nonneg : 0 ≤ M)
    {w : intervalDomainPoint → ℝ}
    (hw_bound : ∀ x, |w x| ≤ M)
    (hw_nonneg : ∀ x, 0 ≤ w x)
    (hw_cont : Continuous w) :
    ∀ y : ℝ,
      |chemFluxLifted p w y| ≤
        M * (Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * (p.ν * M ^ p.γ))) := by
  intro y
  set C_RG := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
    (2 * (p.ν * M ^ p.γ))
  have hC_RG_nn : 0 ≤ C_RG :=
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (mul_nonneg p.hν.le (Real.rpow_nonneg hM_nonneg _)))
  unfold chemFluxLifted
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
  · have hcont_on : ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) := by
      rw [continuousOn_iff_continuous_restrict]
      have : Set.restrict (Set.Icc (0 : ℝ) 1) (intervalDomainLift w) = w := by
        ext ⟨x, hx⟩
        simp [Set.restrict, intervalDomainLift, hx]
        rfl
      rw [this]
      exact hw_cont
    have hlb : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift w x := by
      intro x hx
      simp [intervalDomainLift, hx]
      exact hw_nonneg ⟨x, hx⟩
    have hub : ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift w x ≤ M := by
      intro x hx
      simp [intervalDomainLift, hx]
      exact (abs_le.mp (hw_bound ⟨x, hx⟩)).2
    have hgrad : |ShenWork.Paper2.resolverGradReal p w y| ≤ C_RG := by
      simpa [C_RG] using
        ShenWork.IntervalResolverWeakBounds.resolverGrad_sup_le_of_bounded
          p hcont_on hlb hub hy
    have hlift : |intervalDomainLift w y| ≤ M := by
      simp [intervalDomainLift, hy]
      exact hw_bound ⟨y, hy⟩
    open ShenWork.PDE ShenWork.IntervalResolverGradientBridge
        ShenWork.IntervalResolverWeakBounds ShenWork.Paper2
        ShenWork.IntervalNeumannFullKernel ShenWork.IntervalResolverPositivity in
    have hR_nonneg_pt : 0 ≤ intervalNeumannResolverR p w ⟨y, hy⟩ := by
      have hcont_src : Continuous
          (fun x : intervalDomainPoint ↦ p.ν * (w x) ^ p.γ) :=
        continuous_const.mul (hw_cont.rpow_const (fun x ↦ Or.inr p.hγ.le))
      set clip : ℝ → intervalDomainPoint := fun x ↦
        ⟨max 0 (min x 1), le_max_left 0 _,
          max_le (by norm_num) (min_le_right x 1)⟩
      have hclip_cont : Continuous clip :=
        Continuous.subtype_mk
          (continuous_const.max (continuous_id.min continuous_const)) _
      set f : ℝ → ℝ :=
        (fun x : intervalDomainPoint ↦ p.ν * (w x) ^ p.γ) ∘ clip
      have hf_cont : Continuous f := hcont_src.comp hclip_cont
      have hf_nonneg : ∀ z, 0 ≤ f z := fun z ↦
        mul_nonneg p.hν.le (Real.rpow_nonneg (hw_nonneg _) _)
      have hf_coeff : ∀ k, cosineCoeffs f k =
          (intervalNeumannResolverSourceCoeff p w k).re := by
        intro k
        have hsrc_eq :
            (intervalNeumannResolverSourceCoeff p w k).re =
            cosineCoeffs (fun x ↦ p.ν * intervalDomainLift w x ^ p.γ) k := by
          simp [cosineCoeffs, intervalNeumannResolverSourceCoeff,
            Complex.ofReal_re]
        rw [hsrc_eq]
        exact cosineCoeffs_congr_on_Icc (fun x hx ↦ by
          simp only [f, Function.comp, clip]
          have hclip_eq : max 0 (min x 1) = x := by
            rw [min_eq_left hx.2, max_eq_right hx.1]
          simp only [hclip_eq, intervalDomainLift,
            dif_pos (Set.mem_Icc.mpr hx)]) k
      have hâ : Summable (fun k ↦ (cosineCoeffs f k) ^ 2) := by
        have h := resolverSourceCoeff_re_sq_summable_of_continuousOn p hcont_on
        simp only [intervalNeumannResolverSourceCoeff_zero, sub_zero] at h
        exact h.congr (fun k ↦ by rw [hf_coeff])
      exact intervalNeumannResolverR_nonneg_of_nonneg_source
        hf_cont hf_nonneg hf_coeff hâ ⟨y, hy⟩
    have hR_lift_eq :
        intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y =
          ShenWork.PDE.intervalNeumannResolverR p w ⟨y, hy⟩ := by
      simp [intervalDomainLift, hy]
    have hden_ge_one :
        1 ≤ (1 + intervalDomainLift
          (ShenWork.PDE.intervalNeumannResolverR p w) y) ^ p.β := by
      rw [hR_lift_eq]
      exact Real.one_le_rpow (by linarith [hR_nonneg_pt]) p.hβ
    calc
      |intervalDomainLift w y * ShenWork.Paper2.resolverGradReal p w y /
          (1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y) ^ p.β|
          = |intervalDomainLift w y * ShenWork.Paper2.resolverGradReal p w y| /
            |(1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y) ^ p.β| :=
            abs_div _ _
      _ ≤ |intervalDomainLift w y * ShenWork.Paper2.resolverGradReal p w y| / 1 := by
          apply div_le_div_of_nonneg_left (abs_nonneg _) one_pos
          rwa [abs_of_nonneg (le_of_lt (Real.rpow_pos_of_pos
            (by rw [hR_lift_eq]; linarith [hR_nonneg_pt]) p.β))]
      _ = |intervalDomainLift w y * ShenWork.Paper2.resolverGradReal p w y| := by
          rw [div_one]
      _ ≤ |intervalDomainLift w y| * |ShenWork.Paper2.resolverGradReal p w y| :=
          le_of_eq (abs_mul _ _)
      _ ≤ M * C_RG := by
          exact mul_le_mul hlift hgrad (abs_nonneg _) hM_nonneg
      _ = M * (Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
              (2 * (p.ν * M ^ p.γ))) := by
          rfl
  · simp [intervalDomainLift, hy, zero_mul, abs_zero]
    exact mul_nonneg hM_nonneg hC_RG_nn

/-- Per-slice continuity of the chemotaxis source (subtype function), needed for the
per-slice gradient Hölder smoothing.  Reuses `chemFluxLifted_bounded_of_continuous`'s
continuity argument via the restricted lift. -/
private theorem chemFluxLifted_aestronglyMeasurable {p : CM2Params}
    {w : intervalDomainPoint → ℝ} {M : ℝ} (hw : ∀ x, |w x| ≤ M) (hM : 0 ≤ M)
    (hcont : Continuous w) (hw_nonneg : ∀ x, 0 ≤ w x) :
    AEStronglyMeasurable (chemFluxLifted p w) (intervalMeasure 1) :=
  (ShenWork.IntervalDuhamelIntegrability.chemFluxLifted_integrable_of_continuous
    p hw hM hcont hw_nonneg).aestronglyMeasurable

/-- **Leg 2 — the chemotaxis Duhamel term `∫₀ᵗ ∂ₓS(t−s)Q(u(s)) ds` is Hölder.**
Per-slice GRADIENT Hölder (`Cf = C_Q = M·C_RG`) integrated against the integrable
time integrand `(t−s)^{−(1+θ)/2}` (integrable for `θ < 1`) via
`holder_of_duhamel_integral`. -/
theorem holderLeg_chemotaxis {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {T M : ℝ} (hM : 0 < M)
    (hbound : ∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M)
    (hnonneg : ∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ u t x)
    (hcont : HasContinuousSlices T u) (hmeas : HasJointMeasurability u)
    {t θ : ℝ} (ht : 0 < t) (htT : t ≤ T) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (x y : intervalDomainPoint) :
    |(∫ s in (0:ℝ)..t,
        deriv (fun z => intervalFullSemigroupOperator (t - s) (chemFluxLifted p (u s)) z) x.1)
        - (∫ s in (0:ℝ)..t,
        deriv (fun z => intervalFullSemigroupOperator (t - s) (chemFluxLifted p (u s)) z) y.1)|
      ≤ (∫ s in (0:ℝ)..t,
            (2 : ℝ) ^ (1 - θ)
              * (secondDerivSmoothingConst ^ θ * gradSmoothingConst ^ (1 - θ))
              * (t - s) ^ (-((1 + θ) / 2) : ℝ)
              * (M * (Real.sqrt (∑' k : ℕ,
                  (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2)
                  * (2 * (p.ν * M ^ p.γ)))))
        * |x.1 - y.1| ^ θ := by
  set CQ : ℝ := M * (Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) * (2 * (p.ν * M ^ p.γ)))
    with hCQ
  have hCQ_nn : 0 ≤ CQ := by
    rw [hCQ]; exact mul_nonneg hM.le (mul_nonneg (Real.sqrt_nonneg _)
      (by have := p.hν; positivity))
  set f : ℝ → ℝ → ℝ :=
    fun s yy => if 0 < s ∧ s ≤ T then chemFluxLifted p (u s) yy else 0 with hf
  have hf_bdd : ∀ s yy, |f s yy| ≤ CQ := by
    intro s yy; simp only [hf]; split_ifs with h
    · exact chemFluxLifted_bound_of_ball' p hM.le (fun z => hbound s h.1 h.2 z)
        (fun z => hnonneg s h.1 h.2 z) (hcont s h.1 h.2) yy
    · simpa using hCQ_nn
  have hf_meas : Measurable (Function.uncurry f) := by
    have hbase := chemFluxLifted_uncurry_measurable (p := p) (u := u) hmeas
    simp only [Function.uncurry] at hbase ⊢
    simp only [hf]
    refine Measurable.ite ?_ hbase measurable_const
    exact ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
      ((isClosed_Iic.preimage continuous_fst).measurableSet)
  -- raw source = cutoff source on (0,t]; the two interval integrals agree
  have hcongr : ∀ z : ℝ,
      (∫ s in (0:ℝ)..t,
          deriv (fun zz => intervalFullSemigroupOperator (t - s) (chemFluxLifted p (u s)) zz) z)
        = ∫ s in (0:ℝ)..t,
          deriv (fun zz => intervalFullSemigroupOperator (t - s) (f s) zz) z := by
    intro z
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun s hs => ?_))
    rw [Set.uIoc_of_le ht.le] at hs
    have hmem : (0 < s ∧ s ≤ T) := ⟨hs.1, le_trans hs.2 htT⟩
    simp only [hf, if_pos hmem]
  rw [hcongr x.1, hcongr y.1]
  -- φ s = 2^{1−θ}·(C∇∇^θ C∇^{1−θ})·(t−s)^{−(1+θ)/2}·CQ
  have hφ_int : IntervalIntegrable
      (fun s : ℝ => (2 : ℝ) ^ (1 - θ)
        * (secondDerivSmoothingConst ^ θ * gradSmoothingConst ^ (1 - θ))
        * (t - s) ^ (-((1 + θ) / 2) : ℝ) * CQ) volume 0 t := by
    have h0 := duhamel_holder_gradTime_integrand_integrable ht hθ0 hθ1
    have h1 := h0.const_mul ((2 : ℝ) ^ (1 - θ)
      * (secondDerivSmoothingConst ^ θ * gradSmoothingConst ^ (1 - θ)))
    have h2 := h1.mul_const CQ
    exact h2.congr (fun s _ => by ring)
  refine holder_of_duhamel_integral ht.le
    (ShenWork.IntervalDuhamelIntegrability.gradDuhamel_intervalIntegrable_of_joint_measurable
      ht hf_meas hCQ_nn hf_bdd x.1)
    (ShenWork.IntervalDuhamelIntegrability.gradDuhamel_intervalIntegrable_of_joint_measurable
      ht hf_meas hCQ_nn hf_bdd y.1)
    hφ_int ?_
  have hne : ∀ᵐ s ∂volume, s ≠ t := by
    rw [ae_iff]; simp only [not_not, Set.setOf_eq_eq_singleton]; exact Real.volume_singleton
  refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
  filter_upwards [hne] with s hs_ne hs_mem
  have hts : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs_mem.2 hs_ne)
  have hfs_meas : AEStronglyMeasurable (f s) (intervalMeasure 1) := by
    simp only [hf]; by_cases h : 0 < s ∧ s ≤ T
    · simp only [if_pos h]
      exact chemFluxLifted_aestronglyMeasurable (M := M) (fun z => hbound s h.1 h.2 z)
        hM.le (hcont s h.1 h.2) (fun z => hnonneg s h.1 h.2 z)
    · simp only [if_neg h]; exact aestronglyMeasurable_const
  exact neumannHeatGradient_Linf_to_Ctheta hts hθ0 hθ1 hfs_meas (hf_bdd s) x.1 y.1

/-! ## Uniform-in-`t` Duhamel time-integral bounds -/

/-- Closed form + `T`-uniform bound for the reaction time integral:
`∫₀ᵗ (t−s)^{−θ/2} ds = t^{(2−θ)/2}/((2−θ)/2) ≤ T^{(2−θ)/2}/((2−θ)/2)` for `0≤t≤T`. -/
theorem duhamel_time_integral_le {t T θ : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (hθ2 : θ < 2) :
    (∫ s in (0:ℝ)..t, (t - s) ^ (-(θ / 2) : ℝ))
      ≤ T ^ (-(θ / 2) + 1) / (-(θ / 2) + 1) := by
  have hr : (-1 : ℝ) < -(θ / 2) := by linarith
  have hcomp : (∫ s in (0:ℝ)..t, (t - s) ^ (-(θ / 2) : ℝ))
      = ∫ x in (t - t)..(t - 0), x ^ (-(θ / 2) : ℝ) :=
    intervalIntegral.integral_comp_sub_left (fun x => x ^ (-(θ / 2) : ℝ)) t
  rw [hcomp, sub_self, sub_zero, integral_rpow (Or.inl hr)]
  have hexp : 0 < -(θ / 2) + 1 := by linarith
  have h0 : (0 : ℝ) ^ (-(θ / 2) + 1) = 0 := Real.zero_rpow (ne_of_gt hexp)
  rw [h0, sub_zero]
  gcongr

/-- Closed form + `T`-uniform bound for the chemotaxis (gradient) time integral:
`∫₀ᵗ (t−s)^{−(1+θ)/2} ds ≤ T^{(1−θ)/2}/((1−θ)/2)` for `0≤t≤T`, `θ<1`. -/
theorem duhamel_gradTime_integral_le {t T θ : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (hθ1 : θ < 1) :
    (∫ s in (0:ℝ)..t, (t - s) ^ (-((1 + θ) / 2) : ℝ))
      ≤ T ^ (-((1 + θ) / 2) + 1) / (-((1 + θ) / 2) + 1) := by
  have hr : (-1 : ℝ) < -((1 + θ) / 2) := by linarith
  have hcomp : (∫ s in (0:ℝ)..t, (t - s) ^ (-((1 + θ) / 2) : ℝ))
      = ∫ x in (t - t)..(t - 0), x ^ (-((1 + θ) / 2) : ℝ) :=
    intervalIntegral.integral_comp_sub_left (fun x => x ^ (-((1 + θ) / 2) : ℝ)) t
  rw [hcomp, sub_self, sub_zero, integral_rpow (Or.inl hr)]
  have hexp : 0 < -((1 + θ) / 2) + 1 := by linarith
  have h0 : (0 : ℝ) ^ (-((1 + θ) / 2) + 1) = 0 := Real.zero_rpow (ne_of_gt hexp)
  rw [h0, sub_zero]
  gcongr

end

/-! ## Capstone -/

/-- **`mild_orderBox_positiveTime_holder` — the pass-1 capstone.**

For the divergence-form mild fixed point `u` (packaged as `GradientMildSolutionData`,
order box `0 ≤ u ≤ M`) and any `τ > 0`, the solution at times `t ∈ [τ,T]` is `C^θ`
Hölder (`0 < θ < 1`) in space, with a single Hölder constant `K = K(τ,T,M,χ₀,p)`:

  `∀ t ∈ [τ,T], ∀ x y, |u(t,x) − u(t,y)| ≤ K · |x − y|^θ`.

PROOF = triangle inequality on the mild equation `u(t) = S(t)u₀ − χ₀·chemo + react`,
applying the three leg lemmas (`holderLeg_initial`, `holderLeg_chemotaxis`,
`holderLeg_reaction`), each per-slice constant bounded uniformly in `t ∈ [τ,T]`
(`t^{−θ/2} ≤ τ^{−θ/2}` for the value leg; the closed-form integral bounds
`duhamel_time_integral_le` / `duhamel_gradTime_integral_le` for the Duhamel legs). -/
theorem mild_orderBox_positiveTime_holder {p : CM2Params}
    {u₀ : intervalDomainPoint → ℝ} (D : GradientMildSolutionData p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {θ τ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hτ : 0 < τ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Icc τ D.T, ∀ x y : intervalDomainPoint,
      |D.u t x - D.u t y| ≤ K * |x.1 - y.1| ^ θ := by
  classical
  set M := D.M with hMdef
  have hMpos : 0 < M := D.hM
  -- leg coefficients (all `· |x−y|^θ`)
  set base : ℝ := (2 : ℝ) ^ (1 - θ) * gradSmoothingConst ^ θ with hbase
  have hbase_nn : 0 ≤ base := by
    rw [hbase]; have := gradSmoothingConst_nonneg; positivity
  set CL : ℝ := M * (p.a + p.b * M ^ p.α) with hCL
  have hCL_nn : 0 ≤ CL := by
    rw [hCL]; exact mul_nonneg hMpos.le (by have := p.ha; have := p.hb; positivity)
  set CQ : ℝ := M * (Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) * (2 * (p.ν * M ^ p.γ)))
    with hCQ
  have hCQ_nn : 0 ≤ CQ := by
    rw [hCQ]; exact mul_nonneg hMpos.le (mul_nonneg (Real.sqrt_nonneg _)
      (by have := p.hν; positivity))
  set gbase : ℝ :=
    (2 : ℝ) ^ (1 - θ) * (secondDerivSmoothingConst ^ θ * gradSmoothingConst ^ (1 - θ))
    with hgbase
  have hgbase_nn : 0 ≤ gbase := by
    rw [hgbase]; have := secondDerivSmoothingConst_nonneg
    have := gradSmoothingConst_nonneg; positivity
  -- uniform integral upper bounds (independent of `t`, valid on [τ,T])
  set UB_L : ℝ := D.T ^ (-(θ / 2) + 1) / (-(θ / 2) + 1) with hUBL
  set UB_Q : ℝ := D.T ^ (-((1 + θ) / 2) + 1) / (-((1 + θ) / 2) + 1) with hUBQ
  have hexpL : 0 < -(θ / 2) + 1 := by linarith
  have hexpQ : 0 < -((1 + θ) / 2) + 1 := by linarith
  have hTnn : 0 ≤ D.T := D.hT.le
  have hUBL_nn : 0 ≤ UB_L := by
    rw [hUBL]; exact div_nonneg (Real.rpow_nonneg hTnn _) hexpL.le
  have hUBQ_nn : 0 ≤ UB_Q := by
    rw [hUBQ]; exact div_nonneg (Real.rpow_nonneg hTnn _) hexpQ.le
  -- the assembled Hölder constant
  set K : ℝ := base * M * τ ^ (-(θ / 2) : ℝ)
      + |p.χ₀| * (gbase * CQ * UB_Q) + base * CL * UB_L with hK
  have hτrpow_nn : 0 ≤ τ ^ (-(θ / 2) : ℝ) := (Real.rpow_pos_of_pos hτ _).le
  have hK_nn : 0 ≤ K := by
    rw [hK]
    have h1 : 0 ≤ base * M * τ ^ (-(θ / 2) : ℝ) :=
      mul_nonneg (mul_nonneg hbase_nn hMpos.le) hτrpow_nn
    have h2 : 0 ≤ |p.χ₀| * (gbase * CQ * UB_Q) :=
      mul_nonneg (abs_nonneg _) (mul_nonneg (mul_nonneg hgbase_nn hCQ_nn) hUBQ_nn)
    have h3 : 0 ≤ base * CL * UB_L := mul_nonneg (mul_nonneg hbase_nn hCL_nn) hUBL_nn
    linarith
  refine ⟨K, hK_nn, fun t ht x y => ?_⟩
  obtain ⟨hτt, htT⟩ := ht
  have htpos : 0 < t := lt_of_lt_of_le hτ hτt
  have hdxy_nn : 0 ≤ |x.1 - y.1| ^ θ := Real.rpow_nonneg (abs_nonneg _) _
  -- short names for the three leg-difference quantities
  set I1 : ℝ := intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1 -
      intervalFullSemigroupOperator t (intervalDomainLift u₀) y.1 with hI1
  set I2 : ℝ := (∫ s in (0:ℝ)..t,
      deriv (fun z => intervalFullSemigroupOperator (t - s) (chemFluxLifted p (D.u s)) z) x.1) -
      (∫ s in (0:ℝ)..t,
      deriv (fun z => intervalFullSemigroupOperator (t - s) (chemFluxLifted p (D.u s)) z) y.1)
    with hI2
  set I3 : ℝ := (∫ s in (0:ℝ)..t,
      intervalFullSemigroupOperator (t - s) (logisticLifted p (D.u s)) x.1) -
      (∫ s in (0:ℝ)..t,
      intervalFullSemigroupOperator (t - s) (logisticLifted p (D.u s)) y.1)
    with hI3
  -- expand the mild equation at x and y
  have hmildx := D.hmild t htpos htT x
  have hmildy := D.hmild t htpos htT y
  have hdiff : D.u t x - D.u t y = I1 + (-p.χ₀) * I2 + I3 := by
    rw [hmildx, hmildy, hI1, hI2, hI3]
    unfold intervalGradientDuhamelMap; ring
  -- the three leg Hölder bounds
  have hleg1 := holderLeg_initial (p := p) (u₀ := u₀) (M := M) hMpos.le hu₀ hu₀_meas
    htpos hθ0 hθ1 x y
  have hleg2 := holderLeg_chemotaxis (p := p) (u := D.u) (M := M) hMpos
    D.hbound D.hnonneg D.hcont D.hmeas htpos htT hθ0 hθ1 x y
  have hleg3 := holderLeg_reaction (p := p) (u := D.u) (M := M) hMpos
    D.hbound D.hcont D.hmeas htpos htT hθ0 hθ1 x y
  -- bound each leg coefficient by the uniform constant times |x−y|^θ
  -- leg1: t^{−θ/2} ≤ τ^{−θ/2}
  have htmono : t ^ (-(θ / 2) : ℝ) ≤ τ ^ (-(θ / 2) : ℝ) := by
    rw [Real.rpow_neg hτ.le, Real.rpow_neg (lt_of_lt_of_le hτ hτt).le]
    have hτpow : 0 < τ ^ (θ / 2 : ℝ) := Real.rpow_pos_of_pos hτ _
    gcongr
  have hL1 : |I1| ≤ (base * M * τ ^ (-(θ / 2) : ℝ)) * |x.1 - y.1| ^ θ := by
    rw [hI1]
    refine hleg1.trans ?_
    have hcoef : base * t ^ (-(θ / 2) : ℝ) * M ≤ base * M * τ ^ (-(θ / 2) : ℝ) := by
      have hbm : 0 ≤ base * M := mul_nonneg hbase_nn hMpos.le
      nlinarith [mul_le_mul_of_nonneg_left htmono hbm]
    exact mul_le_mul_of_nonneg_right hcoef hdxy_nn
  -- leg3 (reaction): pull constants, bound the time integral
  have hintL : (∫ s in (0:ℝ)..t, base * (t - s) ^ (-(θ / 2) : ℝ) * CL)
      ≤ base * CL * UB_L := by
    have hfun_eq : (fun s : ℝ => base * (t - s) ^ (-(θ / 2) : ℝ) * CL)
        = (fun s : ℝ => (base * CL) * (t - s) ^ (-(θ / 2) : ℝ)) := by funext s; ring
    have heq : (∫ s in (0:ℝ)..t, base * (t - s) ^ (-(θ / 2) : ℝ) * CL)
        = base * CL * (∫ s in (0:ℝ)..t, (t - s) ^ (-(θ / 2) : ℝ)) := by
      rw [hfun_eq, intervalIntegral.integral_const_mul]
    rw [heq]
    have hbcl : 0 ≤ base * CL := mul_nonneg hbase_nn hCL_nn
    have hint_le : (∫ s in (0:ℝ)..t, (t - s) ^ (-(θ / 2) : ℝ)) ≤ UB_L :=
      duhamel_time_integral_le htpos.le htT (by linarith)
    exact mul_le_mul_of_nonneg_left hint_le hbcl
  have hL3 : |I3| ≤ (base * CL * UB_L) * |x.1 - y.1| ^ θ := by
    rw [hI3]
    refine hleg3.trans ?_
    exact mul_le_mul_of_nonneg_right hintL hdxy_nn
  -- leg2 (chemotaxis): same with gradient integrand
  have hintQ : (∫ s in (0:ℝ)..t, gbase * (t - s) ^ (-((1 + θ) / 2) : ℝ) * CQ)
      ≤ gbase * CQ * UB_Q := by
    have hfun_eq : (fun s : ℝ => gbase * (t - s) ^ (-((1 + θ) / 2) : ℝ) * CQ)
        = (fun s : ℝ => (gbase * CQ) * (t - s) ^ (-((1 + θ) / 2) : ℝ)) := by funext s; ring
    have heq : (∫ s in (0:ℝ)..t, gbase * (t - s) ^ (-((1 + θ) / 2) : ℝ) * CQ)
        = gbase * CQ * (∫ s in (0:ℝ)..t, (t - s) ^ (-((1 + θ) / 2) : ℝ)) := by
      rw [hfun_eq, intervalIntegral.integral_const_mul]
    rw [heq]
    have hgcq : 0 ≤ gbase * CQ := mul_nonneg hgbase_nn hCQ_nn
    have hint_le : (∫ s in (0:ℝ)..t, (t - s) ^ (-((1 + θ) / 2) : ℝ)) ≤ UB_Q :=
      duhamel_gradTime_integral_le htpos.le htT hθ1
    exact mul_le_mul_of_nonneg_left hint_le hgcq
  have hL2 : |I2| ≤ (gbase * CQ * UB_Q) * |x.1 - y.1| ^ θ := by
    rw [hI2]
    refine hleg2.trans ?_
    exact mul_le_mul_of_nonneg_right hintQ hdxy_nn
  -- assemble via triangle inequality
  rw [hdiff]
  have hχL2 : |(-p.χ₀) * I2| ≤ |p.χ₀| * ((gbase * CQ * UB_Q) * |x.1 - y.1| ^ θ) := by
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left hL2 (abs_nonneg _)
  have htri : |I1 + (-p.χ₀) * I2 + I3| ≤ |I1| + |(-p.χ₀) * I2| + |I3| := by
    refine (abs_add_le (I1 + (-p.χ₀) * I2) I3).trans ?_
    gcongr
    exact abs_add_le I1 ((-p.χ₀) * I2)
  refine le_trans htri ?_
  rw [hK, add_mul, add_mul]
  have hsum := add_le_add (add_le_add hL1 hχL2) hL3
  have hassoc : (base * M * τ ^ (-(θ / 2) : ℝ)) * |x.1 - y.1| ^ θ
      + |p.χ₀| * ((gbase * CQ * UB_Q) * |x.1 - y.1| ^ θ)
      + (base * CL * UB_L) * |x.1 - y.1| ^ θ
      = base * M * τ ^ (-(θ / 2) : ℝ) * |x.1 - y.1| ^ θ
        + |p.χ₀| * (gbase * CQ * UB_Q) * |x.1 - y.1| ^ θ
        + base * CL * UB_L * |x.1 - y.1| ^ θ := by ring
  rw [hassoc] at hsum
  exact hsum

end ShenWork.Paper2
