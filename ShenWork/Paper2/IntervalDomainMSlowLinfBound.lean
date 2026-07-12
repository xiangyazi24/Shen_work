import ShenWork.Paper2.IntervalDomainMPhysicalRestart
import ShenWork.Paper2.IntervalDomainMSlowLpBound
import ShenWork.PDE.IntervalFullKernelSpectralClean

/-!
# Uniform sup bound for the faithful slow-diffusion interval equation

This file converts the uniform high finite-power estimate into the uniform
sup bound needed by the amended slow branch of Theorem 1.2.  The proof uses a
fixed positive restart lag.  The homogeneous heat leg is controlled from the
finite-power bound, the elliptic equation controls the chemical gradient, and
the remaining chemotactic term has the sublinear power `m < 1`.
-/

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainM

open ShenWork.IntervalNeumannFullKernel
  (intervalNeumannFullKernel intervalFullSemigroupOperator)

/-- A finite pointwise bound for the Neumann heat kernel at a fixed positive
time. -/
def fixedHeatKernelBound (r : ℝ) : ℝ :=
  ∑' k : ℤ, Real.exp (-r * ((k : ℝ) * Real.pi) ^ 2)

theorem fixedHeatKernelBound_nonneg (r : ℝ) :
    0 ≤ fixedHeatKernelBound r := by
  exact tsum_nonneg fun _ => Real.exp_nonneg _

theorem fixedHeatKernelBound_anti
    {δ r : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r) :
    fixedHeatKernelBound r ≤ fixedHeatKernelBound δ := by
  have hr : 0 < r := hδ.trans_le hδr
  have hsδ := ShenWork.IntervalFullKernelSpectralClean.expWeightSummable δ hδ
  have hsr := ShenWork.IntervalFullKernelSpectralClean.expWeightSummable r hr
  unfold fixedHeatKernelBound
  exact Summable.tsum_le_tsum (fun k => by
    apply Real.exp_le_exp.mpr
    have hq : 0 ≤ ((k : ℝ) * Real.pi) ^ 2 := sq_nonneg _
    nlinarith) hsr hsδ

/-- A continuous function which is bounded above almost everywhere on the
physical interval is bounded above at both endpoints as well. -/
theorem continuousOn_le_of_ae_le_Ioc
    {f : ℝ → ℝ} {R : ℝ} (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hae : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), f x ≤ R) :
    ∀ x ∈ Icc (0 : ℝ) 1, f x ≤ R := by
  let g : ℝ → ℝ := fun x => max (f x - R) 0
  have hgzero_Ioc : g =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] 0 := by
    filter_upwards [hae] with x hx
    simp [g, max_eq_right (sub_nonpos.mpr hx)]
  have hgzero_Icc : g =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] 0 := by
    rw [← MeasureTheory.restrict_Ioc_eq_restrict_Icc]
    exact hgzero_Ioc
  have hgcont : ContinuousOn g (Icc (0 : ℝ) 1) := by
    exact continuous_max.comp_continuousOn
      ((hf.sub continuousOn_const).prodMk continuousOn_const)
  have hevery : EqOn g (fun _ : ℝ => 0) (Icc (0 : ℝ) 1) :=
    MeasureTheory.Measure.eqOn_Icc_of_ae_eq volume (by norm_num)
      hgzero_Icc hgcont continuousOn_const
  intro x hx
  have := hevery hx
  simp only [g] at this
  exact sub_nonpos.mp (max_eq_right_iff.mp this)

/-- Scalar closure of the sublinear maximum inequality. -/
theorem exists_uniform_bound_of_sublinear_inequality
    {m A B : ℝ} (hm : 0 < m) (hm1 : m < 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ R ≥ 0, ∀ M ≥ 0, M ≤ A + B * M ^ m → M ≤ R := by
  let K : ℝ :=
    ((B / (((1 : ℝ) / 2) * (1 / m)) ^ (m / 1)) ^ (1 / (1 - m))) /
      (1 / (1 - m))
  have hK : 0 ≤ K := by
    dsimp [K]
    have hden : 0 < (1 : ℝ) / (1 - m) := one_div_pos.mpr (sub_pos.mpr hm1)
    exact div_nonneg (Real.rpow_nonneg (div_nonneg hB (Real.rpow_nonneg
      (mul_nonneg (by norm_num) (one_div_nonneg.mpr hm.le)) _)) _) hden.le
  let R : ℝ := 2 * (A + K)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  refine ⟨R, hR, ?_⟩
  intro M hM hineq
  have hy :=
    ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation.scalar_rpow_young_absorb
      (r := m) (s := (1 : ℝ)) (A := B) (eps := (1 : ℝ) / 2) (x := M)
      hm hm1 hB (by norm_num) hM
  dsimp [K, R]
  norm_num at hy ⊢
  linarith

/-- Initial trace supplies a uniform pointwise cap on a short interval. -/
theorem exists_initial_trace_pointwise_upper
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u) :
    ∃ δ > 0, ∃ E ≥ 0, ∀ t, 0 < t → t < δ →
      ∀ x : intervalDomainPoint, u t x ≤ E := by
  obtain ⟨δ, hδ, htraceδ⟩ := htrace 1 (by norm_num)
  let δ₀ : ℝ := min δ (T / 2)
  have hδ₀ : 0 < δ₀ := lt_min hδ (half_pos hsol.1)
  have hu0bdd : BddAbove (range (fun x : intervalDomainPoint => |u₀ x|)) := by
    simpa [intervalDomainM] using hu₀.admissible.1
  obtain ⟨M₀, hM₀⟩ := hu0bdd
  have hM₀nonneg : 0 ≤ M₀ := by
    let x₀ : intervalDomainPoint := ⟨0, ⟨le_rfl, zero_le_one⟩⟩
    exact (abs_nonneg (u₀ x₀)).trans (hM₀ ⟨x₀, rfl⟩)
  let E : ℝ := M₀ + 1
  have hE : 0 ≤ E := by dsimp [E]; linarith
  refine ⟨δ₀, hδ₀, E, hE, ?_⟩
  intro t ht0 htδ₀ x
  have htδ : t < δ := htδ₀.trans_le (min_le_left _ _)
  have htT : t < T :=
    lt_of_lt_of_le htδ₀ (by dsimp [δ₀]; linarith [min_le_right δ (T / 2), hsol.1])
  have hdiffBdd := bddAbove_range_abs_diff_of_bddAbove
    (solution_slice_abs_bddAbove hsol ⟨ht0, htT⟩)
    (by simpa [intervalDomainM] using hu₀.admissible.1)
  have hsup : intervalDomain.supNorm (fun y => u t y - u₀ y) < 1 := by
    simpa [intervalDomainM, intervalDomain] using htraceδ t ht0 htδ
  have hdiff : |u t x - u₀ x| ≤
      intervalDomain.supNorm (fun y => u t y - u₀ y) := by
    change |u t x - u₀ x| ≤ intervalDomainSupNorm (fun y => u t y - u₀ y)
    unfold intervalDomainSupNorm
    exact le_csSup hdiffBdd ⟨x, rfl⟩
  have hu₀x : |u₀ x| ≤ M₀ := hM₀ ⟨x, rfl⟩
  have htri : u t x ≤ |u t x - u₀ x| + |u₀ x| := by
    calc
      u t x = (u t x - u₀ x) + u₀ x := by ring
      _ ≤ |u t x - u₀ x| + |u₀ x| :=
        add_le_add (le_abs_self _) (le_abs_self _)
  dsimp [E]
  linarith [lt_of_le_of_lt hdiff hsup]

theorem intervalNeumannFullKernel_abs_le_fixed
    {r : ℝ} (hr : 0 < r) (x y : ℝ) :
    |intervalNeumannFullKernel r x y| ≤ fixedHeatKernelBound r := by
  rw [ShenWork.IntervalFullKernelSpectralClean.intervalNeumannFullKernel_eq_cosineKernel_clean
    r hr x y]
  let w : ℤ → ℝ := fun k => Real.exp (-r * ((k : ℝ) * Real.pi) ^ 2)
  let f : ℤ → ℝ := fun k => w k *
    (Real.cos ((k : ℝ) * Real.pi * x) * Real.cos ((k : ℝ) * Real.pi * y))
  have hw : Summable w := by
    simpa [w] using ShenWork.IntervalFullKernelSpectralClean.expWeightSummable r hr
  have hnorm : ∀ k, ‖f k‖ ≤ w k := by
    intro k
    dsimp [f, w]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hcos : |Real.cos ((k : ℝ) * Real.pi * x) *
        Real.cos ((k : ℝ) * Real.pi * y)| ≤ 1 := by
      calc
        |Real.cos ((k : ℝ) * Real.pi * x) *
            Real.cos ((k : ℝ) * Real.pi * y)| =
            |Real.cos ((k : ℝ) * Real.pi * x)| *
              |Real.cos ((k : ℝ) * Real.pi * y)| := abs_mul _ _
        _ ≤ 1 * 1 := mul_le_mul (Real.abs_cos_le_one _)
          (Real.abs_cos_le_one _) (abs_nonneg _) (by norm_num)
        _ = 1 := one_mul 1
    exact mul_le_of_le_one_right (Real.exp_pos _).le hcos
  have hfnorm : Summable (fun k => ‖f k‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg (f k)) hnorm hw
  have hf : Summable f := Summable.of_norm hfnorm
  calc
    |∑' k : ℤ, Real.exp (-r * ((k : ℝ) * Real.pi) ^ 2) *
        (Real.cos ((k : ℝ) * Real.pi * x) *
          Real.cos ((k : ℝ) * Real.pi * y))| = ‖∑' k, f k‖ := by
            simp only [f, w, Real.norm_eq_abs]
    _ ≤ ∑' k, ‖f k‖ := norm_tsum_le_tsum_norm hfnorm
    _ ≤ ∑' k, w k := Summable.tsum_le_tsum hnorm hfnorm hw
    _ = fixedHeatKernelBound r := by simp [fixedHeatKernelBound, w]

/-- One-sided maximum preservation for the full Neumann semigroup. -/
theorem intervalFullSemigroupOperator_le_const
    {r B C : ℝ} (hr : 0 < r)
    {f : ℝ → ℝ} (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    (hf_abs : ∀ y, |f y| ≤ C)
    (hf_le : ∀ y, f y ≤ B) (x : ℝ) :
    intervalFullSemigroupOperator r f x ≤ B := by
  have hf_int : Integrable f (intervalMeasure 1) :=
    intervalMeasure_integrable_of_abs_bound hf_meas hf_abs
  have hK_int :=
    ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_integrable hr x
  have hKf_int : Integrable
      (fun y => intervalNeumannFullKernel r x y * f y) (intervalMeasure 1) := by
    refine hK_int.mul_bdd hf_meas (c := C) ?_
    exact Filter.Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using hf_abs y
  have hKB_int : Integrable
      (fun y => intervalNeumannFullKernel r x y * B) (intervalMeasure 1) :=
    hK_int.mul_const B
  unfold intervalFullSemigroupOperator
  calc
    (∫ y, intervalNeumannFullKernel r x y * f y ∂intervalMeasure 1) ≤
        ∫ y, intervalNeumannFullKernel r x y * B ∂intervalMeasure 1 := by
      apply integral_mono hKf_int hKB_int
      exact fun y => mul_le_mul_of_nonneg_left (hf_le y)
        (ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_nonneg hr x y)
    _ = B * (∫ y, intervalNeumannFullKernel r x y ∂intervalMeasure 1) := by
      rw [integral_mul_const]
      ring
    _ = B := by
      rw [ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_intervalMeasure_integral_eq_one
        hr x, mul_one]

/-- At a fixed positive lag, the homogeneous heat leg is bounded by one
finite-power integral of the restart slice. -/
theorem restartHomM_abs_le_of_lp
    {p : CM2Params} {T a r pExp C : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha0 : 0 < a) (haT : a < T) (hr : 0 < r)
    (hp : 1 < pExp)
    (hpower : intervalDomainM.integral (fun z => (u a z) ^ pExp) ≤ C)
    (x : ℝ) :
    |intervalFullSemigroupOperator r (intervalDomainLift (u a)) x| ≤
      fixedHeatKernelBound r * (C + 1) := by
  let f : ℝ → ℝ := intervalDomainLift (u a)
  let K : ℝ := fixedHeatKernelBound r
  have hK : 0 ≤ K := fixedHeatKernelBound_nonneg r
  have hf_nonneg : ∀ y, 0 ≤ f y := by
    intro y
    by_cases hy : y ∈ Icc (0 : ℝ) 1
    · simpa [f, intervalDomainLift, hy] using
        (u_pos hsol ha0 haT (⟨y, hy⟩ : intervalDomainPoint)).le
    · simp [f, intervalDomainLift, hy]
  have hfp_cont : ContinuousOn (fun y => f y ^ pExp) (Icc (0 : ℝ) 1) := by
    simpa [f] using
      power_continuousOn_timeSlice (q := pExp) hsol ⟨ha0, haT⟩
  have hfp_int : Integrable (fun y => f y ^ pExp) (intervalMeasure 1) := by
    unfold intervalMeasure intervalSet
    exact hfp_cont.integrableOn_compact isCompact_Icc
  have hone_int : Integrable (fun _ : ℝ => (1 : ℝ)) (intervalMeasure 1) := by
    simp [intervalMeasure, intervalSet]
  have hupp_int : Integrable (fun y => K * (f y ^ pExp + 1))
      (intervalMeasure 1) :=
    (hfp_int.add hone_int).const_mul K
  have hpoint : ∀ y,
      ‖intervalNeumannFullKernel r x y * f y‖ ≤ K * (f y ^ pExp + 1) := by
    intro y
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hf_nonneg y)]
    have hkernel := intervalNeumannFullKernel_abs_le_fixed hr x y
    have hpow : f y ≤ f y ^ pExp + 1 := by
      simpa [Real.rpow_one] using
        ShenWork.Paper2.IntervalDomainLpMonotonicity.rpow_le_one_add_rpow_of_nonneg_of_le
          (hf_nonneg y) (by norm_num : (0 : ℝ) ≤ 1) hp.le
    calc
      |intervalNeumannFullKernel r x y| * f y ≤ K * f y :=
        mul_le_mul_of_nonneg_right hkernel (hf_nonneg y)
      _ ≤ K * (f y ^ pExp + 1) := mul_le_mul_of_nonneg_left hpow hK
  unfold intervalFullSemigroupOperator
  calc
    |∫ y, intervalNeumannFullKernel r x y * f y ∂intervalMeasure 1| =
        ‖∫ y, intervalNeumannFullKernel r x y * f y ∂intervalMeasure 1‖ := by
          rw [Real.norm_eq_abs]
    _ ≤ ∫ y, ‖intervalNeumannFullKernel r x y * f y‖ ∂intervalMeasure 1 :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y, K * (f y ^ pExp + 1) ∂intervalMeasure 1 := by
      exact integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun y => norm_nonneg _)
        hupp_int (Filter.Eventually.of_forall hpoint)
    _ = K * ((∫ y, f y ^ pExp ∂intervalMeasure 1) + 1) := by
      rw [integral_const_mul, integral_add hfp_int hone_int]
      simp [intervalMeasure, intervalSet]
    _ = K * (intervalDomainM.integral (fun z => (u a z) ^ pExp) + 1) := by
      congr 2
      rw [ShenWork.Paper2.IntervalConjugateKernelIBP.intervalMeasure_one_integral_eq_intervalIntegral]
      change (∫ y in (0 : ℝ)..1, intervalDomainLift (u a) y ^ pExp) =
        intervalDomainM.integral (fun z => (u a z) ^ pExp)
      change (∫ y in (0 : ℝ)..1, intervalDomainLift (u a) y ^ pExp) =
        intervalDomain.integral (fun z => (u a z) ^ pExp)
      exact (ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation.intervalDomain_integral_rpow_eq_lift_integral).symm
    _ ≤ K * (C + 1) := mul_le_mul_of_nonneg_left (by linarith) hK

/-- A higher finite-power bound controls the chemical source power on the
unit interval. -/
theorem solution_gamma_integral_le_of_lp
    {p : CM2Params} {T t pExp C : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hγp : p.γ ≤ pExp)
    (hpower : intervalDomainM.integral (fun z => (u t z) ^ pExp) ≤ C) :
    (∫ y in (0 : ℝ)..1, intervalDomainLift (u t) y ^ p.γ) ≤ C + 1 := by
  have hγ_int : IntervalIntegrable
      (fun y => intervalDomainLift (u t) y ^ p.γ) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact power_continuousOn_timeSlice (q := p.γ) hsol ⟨ht0, htT⟩
  have hp_int : IntervalIntegrable
      (fun y => intervalDomainLift (u t) y ^ pExp) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact power_continuousOn_timeSlice (q := pExp) hsol ⟨ht0, htT⟩
  have hpoint : ∀ y ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u t) y ^ p.γ ≤
        intervalDomainLift (u t) y ^ pExp + 1 := by
    intro y hy
    exact ShenWork.Paper2.IntervalDomainLpMonotonicity.rpow_le_one_add_rpow_of_nonneg_of_le
      (solution_lift_pos_Icc hsol ⟨ht0, htT⟩ y hy).le p.hγ.le hγp
  have hmono := intervalIntegral.integral_mono_on
    (by norm_num : (0 : ℝ) ≤ 1) hγ_int
    (hp_int.add intervalIntegrable_const) hpoint
  have hsplit :
      (∫ y in (0 : ℝ)..1, intervalDomainLift (u t) y ^ pExp + 1) =
        (∫ y in (0 : ℝ)..1, intervalDomainLift (u t) y ^ pExp) + 1 := by
    rw [intervalIntegral.integral_add hp_int intervalIntegrable_const,
      intervalIntegral.integral_const]
    norm_num [smul_eq_mul]
  rw [hsplit] at hmono
  have hp_eq :
      (∫ y in (0 : ℝ)..1, intervalDomainLift (u t) y ^ pExp) =
        intervalDomainM.integral (fun z => (u t z) ^ pExp) := by
    change (∫ y in (0 : ℝ)..1, intervalDomainLift (u t) y ^ pExp) =
      intervalDomain.integral (fun z => (u t z) ^ pExp)
    exact (ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation.intervalDomain_integral_rpow_eq_lift_integral).symm
  rw [hp_eq] at hmono
  linarith

/-- Integrating the elliptic equation and using the two Neumann endpoints
identifies the chemical mass with the source mass. -/
theorem chemical_mass_identity
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    p.μ * (∫ y in (0 : ℝ)..1, intervalDomainLift (v t) y) =
      p.ν * (∫ y in (0 : ℝ)..1,
        intervalDomainLift (u t) y ^ p.γ) := by
  have hgrad := restartChemGrad_eq_deriv
    (p := p) (T := T) (a := t) (h := (0 : ℝ)) (r := 0) (x := 1)
    hsol ht0 (by norm_num) (by simpa) (by norm_num) (by norm_num)
  have hneu : deriv (intervalDomainLift (v t)) 1 = 0 := by
    simpa using
      (hsol.regularity.2.2.2.2.1 t ⟨ht0, htT⟩).2.2.2
  have hgrad' : restartChemGrad p t 0 u v 0 1 =
      deriv (intervalDomainLift (v t)) 1 := by
    simpa using hgrad
  have hrawClamp :
      (∫ y in (0 : ℝ)..1,
        (p.μ * intervalDomainLift (v t) (clamp01 y) -
          p.ν * intervalDomainLift (u t) (clamp01 y) ^ p.γ)) = 0 := by
    rw [hneu] at hgrad'
    simpa [restartChemGrad, restartChemRhs, restartField,
      restartTimeClamp, clamp01] using hgrad'
  have hraw :
      (∫ y in (0 : ℝ)..1,
        (p.μ * intervalDomainLift (v t) y -
          p.ν * intervalDomainLift (u t) y ^ p.γ)) = 0 := by
    have heq : (∫ y in (0 : ℝ)..1,
        (p.μ * intervalDomainLift (v t) y -
          p.ν * intervalDomainLift (u t) y ^ p.γ)) =
      ∫ y in (0 : ℝ)..1,
        (p.μ * intervalDomainLift (v t) (clamp01 y) -
          p.ν * intervalDomainLift (u t) (clamp01 y) ^ p.γ) := by
      refine intervalIntegral.integral_congr (fun y hy => ?_)
      have hyIcc : y ∈ Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le zero_le_one] using hy
      rw [clamp01_eq_self hyIcc]
    rw [heq]
    exact hrawClamp
  have hv_int : IntervalIntegrable (intervalDomainLift (v t)) volume 0 1 :=
    by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le zero_le_one]
      exact (hsol.regularity.2.2.2.2.1 t ⟨ht0, htT⟩).2.1.continuousOn
  have huγ_int : IntervalIntegrable
      (fun y => intervalDomainLift (u t) y ^ p.γ) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact power_continuousOn_timeSlice (q := p.γ) hsol ⟨ht0, htT⟩
  rw [intervalIntegral.integral_sub (hv_int.const_mul p.μ)
      (huγ_int.const_mul p.ν),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hraw
  linarith

/-- The elliptic primitive and the finite-power source bound give a uniform
pointwise bound for the physical chemical gradient. -/
theorem chemical_gradient_abs_le_of_lp
    {p : CM2Params} {T t pExp C x : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) (hx : x ∈ Icc (0 : ℝ) 1)
    (hγp : p.γ ≤ pExp)
    (hpower : intervalDomainM.integral (fun z => (u t z) ^ pExp) ≤ C) :
    |deriv (intervalDomainLift (v t)) x| ≤ 2 * p.ν * (C + 1) := by
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let V : ℝ → ℝ := intervalDomainLift (v t)
  have hgrad := restartChemGrad_eq_deriv
    (p := p) (T := T) (a := t) (h := (0 : ℝ)) (r := 0) (x := x)
    hsol ht0 (by norm_num) (by simpa) (by norm_num) hx
  have hreprClamp :
      (∫ y in (0 : ℝ)..x,
        (p.μ * V (clamp01 y) - p.ν * U (clamp01 y) ^ p.γ)) =
        deriv V x := by
    simpa [restartChemGrad, restartChemRhs, restartField,
      restartTimeClamp, clamp01_eq_self hx, U, V] using hgrad
  have hrepr :
      (∫ y in (0 : ℝ)..x, (p.μ * V y - p.ν * U y ^ p.γ)) =
        deriv V x := by
    have heq : (∫ y in (0 : ℝ)..x,
        (p.μ * V y - p.ν * U y ^ p.γ)) =
      ∫ y in (0 : ℝ)..x,
        (p.μ * V (clamp01 y) - p.ν * U (clamp01 y) ^ p.γ) := by
      refine intervalIntegral.integral_congr (fun y hy => ?_)
      have hyIcc : y ∈ Icc (0 : ℝ) 1 := by
        rw [Set.uIcc_of_le hx.1] at hy
        exact ⟨hy.1, hy.2.trans hx.2⟩
      rw [clamp01_eq_self hyIcc]
    rw [heq]
    exact hreprClamp
  have hVnonneg : ∀ y ∈ Icc (0 : ℝ) 1, 0 ≤ V y := by
    intro y hy
    simpa [V, intervalDomainLift, hy] using
      hsol.v_nonneg ht0 htT (x := (⟨y, hy⟩ : intervalDomainPoint))
  have hUnonneg : ∀ y ∈ Icc (0 : ℝ) 1, 0 ≤ U y := by
    intro y hy
    exact (by simpa [U, intervalDomainLift, hy] using
      (u_pos hsol ht0 htT (⟨y, hy⟩ : intervalDomainPoint)).le)
  have hVcont : ContinuousOn V (Icc (0 : ℝ) 1) := by
    simpa [V] using
      (hsol.regularity.2.2.2.2.1 t ⟨ht0, htT⟩).2.1.continuousOn
  have hUγcont : ContinuousOn (fun y => U y ^ p.γ) (Icc (0 : ℝ) 1) := by
    simpa [U] using power_continuousOn_timeSlice (q := p.γ) hsol ⟨ht0, htT⟩
  have hV_int : IntervalIntegrable V volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact hVcont
  have hUγ_int : IntervalIntegrable (fun y => U y ^ p.γ) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact hUγcont
  have hsum_int : IntervalIntegrable
      (fun y => p.μ * V y + p.ν * U y ^ p.γ) volume 0 1 :=
    (hV_int.const_mul p.μ).add (hUγ_int.const_mul p.ν)
  have hsum_nonneg : ∀ᵐ y ∂volume.restrict (Ioc (0 : ℝ) 1),
      0 ≤ p.μ * V y + p.ν * U y ^ p.γ := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards with y hy
    have hyIcc : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2⟩
    exact add_nonneg (mul_nonneg p.hμ.le (hVnonneg y hyIcc))
      (mul_nonneg p.hν.le (Real.rpow_nonneg (hUnonneg y hyIcc) _))
  have habsPoint : ∀ y ∈ Icc (0 : ℝ) x,
      |p.μ * V y - p.ν * U y ^ p.γ| ≤
        p.μ * V y + p.ν * U y ^ p.γ := by
    intro y hy
    have hyIcc : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1, hy.2.trans hx.2⟩
    have ha : 0 ≤ p.μ * V y := mul_nonneg p.hμ.le (hVnonneg y hyIcc)
    have hb : 0 ≤ p.ν * U y ^ p.γ :=
      mul_nonneg p.hν.le (Real.rpow_nonneg (hUnonneg y hyIcc) p.γ)
    simpa [abs_of_nonneg ha, abs_of_nonneg hb] using
      (abs_sub (p.μ * V y) (p.ν * U y ^ p.γ))
  have habs_int_x : IntervalIntegrable
      (fun y => |p.μ * V y - p.ν * U y ^ p.γ|) volume 0 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx.1]
    exact (((continuousOn_const.mul hVcont).sub
      (continuousOn_const.mul hUγcont)).abs).mono
        (Icc_subset_Icc le_rfl hx.2)
  have hsum_int_x : IntervalIntegrable
      (fun y => p.μ * V y + p.ν * U y ^ p.γ) volume 0 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx.1]
    exact ((continuousOn_const.mul hVcont).add
      (continuousOn_const.mul hUγcont)).mono
        (Icc_subset_Icc le_rfl hx.2)
  rw [← hrepr]
  calc
    |∫ y in (0 : ℝ)..x, (p.μ * V y - p.ν * U y ^ p.γ)| ≤
        ∫ y in (0 : ℝ)..x, |p.μ * V y - p.ν * U y ^ p.γ| :=
      intervalIntegral.abs_integral_le_integral_abs hx.1
    _ ≤ ∫ y in (0 : ℝ)..x, (p.μ * V y + p.ν * U y ^ p.γ) := by
      exact intervalIntegral.integral_mono_on hx.1
        habs_int_x hsum_int_x habsPoint
    _ ≤ ∫ y in (0 : ℝ)..1, (p.μ * V y + p.ν * U y ^ p.γ) :=
      intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2 hsum_nonneg hsum_int
    _ = 2 * p.ν * (∫ y in (0 : ℝ)..1, U y ^ p.γ) := by
      rw [intervalIntegral.integral_add (hV_int.const_mul p.μ)
          (hUγ_int.const_mul p.ν),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      have hmass := chemical_mass_identity hsol ht0 htT
      simp only [U, V] at hmass ⊢
      linarith
    _ ≤ 2 * p.ν * (C + 1) := by
      have hγ := solution_gamma_integral_le_of_lp hsol ht0 htT hγp hpower
      simpa [U] using mul_le_mul_of_nonneg_left hγ (mul_nonneg (by norm_num) p.hν.le)

/-- On a restart slab, the faithful flux has the sublinear sup bound supplied
by the slab maximum and the uniform finite-power estimate. -/
theorem restartFluxM_abs_le_of_lp_and_slab
    {p : CM2Params} {T a h pExp C M : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T)
    (hγp : p.γ ≤ pExp)
    (hpower : ∀ τ, 0 < τ → τ < T →
      intervalDomainM.integral (fun z => (u τ z) ^ pExp) ≤ C)
    (hM : 0 ≤ M)
    (hslab : ∀ τ ∈ Icc a (a + h), ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u τ) x ≤ M) :
    ∀ r y, |restartFluxM p a h u v r y| ≤
      M ^ p.m * (2 * p.ν * (C + 1)) := by
  intro r y
  let r₀ : ℝ := restartTimeClamp h r
  let x₀ : ℝ := clamp01 y
  let τ : ℝ := a + r₀
  have hr₀ : r₀ ∈ Icc (0 : ℝ) h := restartTimeClamp_mem hh r
  have hx₀ : x₀ ∈ Icc (0 : ℝ) 1 := clamp01_mem y
  have hτ0 : 0 < τ := by dsimp [τ]; exact add_pos_of_pos_of_nonneg ha hr₀.1
  have hτT : τ < T := by
    dsimp [τ]
    exact lt_of_le_of_lt
      (by simpa [add_comm] using add_le_add_left hr₀.2 a) hahT
  have hτslab : τ ∈ Icc a (a + h) := by
    dsimp [τ]
    constructor <;> linarith [hr₀.1, hr₀.2]
  have hu_pos : 0 < restartField a h u r y :=
    restartField_u_pos hsol ha hh hahT r y
  have hu_le : restartField a h u r y ≤ M := by
    rw [restartField_clamp hh u r y]
    simpa [r₀, x₀, τ, restartField, restartTimeClamp_idem hh,
      clamp01_idem, intervalDomainLift, hx₀] using hslab τ hτslab x₀ hx₀
  have hupow : (restartField a h u r y) ^ p.m ≤ M ^ p.m :=
    Real.rpow_le_rpow hu_pos.le hu_le p.hm.le
  have hv_nonneg : 0 ≤ restartField a h v r y :=
    restartField_v_nonneg hsol ha hh hahT r y
  have hden : 1 ≤ (1 + restartField a h v r y) ^ p.β := by
    exact Real.one_le_rpow (by linarith) p.hβ
  have hgrad : |restartChemGrad p a h u v r y| ≤
      2 * p.ν * (C + 1) := by
    rw [restartChemGrad_clamp p hh u v r y]
    have hphys := restartChemGrad_eq_deriv hsol ha hh hahT hr₀ hx₀
    rw [hphys]
    exact chemical_gradient_abs_le_of_lp hsol hτ0 hτT hx₀ hγp
      (hpower τ hτ0 hτT)
  have hG : 0 ≤ 2 * p.ν * (C + 1) :=
    (abs_nonneg (restartChemGrad p a h u v r y)).trans hgrad
  unfold restartFluxM
  rw [abs_div, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hu_pos.le p.m), abs_of_nonneg
    (Real.rpow_nonneg (by linarith : 0 ≤ 1 + restartField a h v r y) p.β)]
  have hnum : (restartField a h u r y) ^ p.m *
      |restartChemGrad p a h u v r y| ≤
        M ^ p.m * (2 * p.ν * (C + 1)) :=
    mul_le_mul hupow hgrad (abs_nonneg _) (Real.rpow_nonneg hM p.m)
  exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hden)).2 <|
    hnum.trans (le_mul_of_one_le_right
      (mul_nonneg (Real.rpow_nonneg hM p.m) hG) hden)

/-- The logistic restart leg is bounded from above by its positive linear
part; the damping term is retained by the order estimate instead of being
placed inside an absolute value. -/
theorem restartLogisticDuhamelM_le_of_slab
    {p : CM2Params} {T a h r M : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T)
    (hr : 0 < r)
    (hslab : ∀ τ ∈ Icc a (a + h), ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u τ) x ≤ M) (x : ℝ) :
    restartLogisticDuhamelM p a h u r x ≤ r * (p.a * M) := by
  have hsource_le : ∀ s y, restartLogisticM p a h u s y ≤ p.a * M := by
    intro s y
    let s₀ : ℝ := restartTimeClamp h s
    let y₀ : ℝ := clamp01 y
    let τ : ℝ := a + s₀
    have hs₀ : s₀ ∈ Icc (0 : ℝ) h := restartTimeClamp_mem hh s
    have hy₀ : y₀ ∈ Icc (0 : ℝ) 1 := clamp01_mem y
    have hτslab : τ ∈ Icc a (a + h) := by
      dsimp [τ]
      constructor <;> linarith [hs₀.1, hs₀.2]
    have hu_pos : 0 < restartField a h u s y :=
      restartField_u_pos hsol ha hh hahT s y
    have hu_le : restartField a h u s y ≤ M := by
      rw [restartField_clamp hh u s y]
      simpa [s₀, y₀, τ, restartField, restartTimeClamp_idem hh,
        clamp01_idem, intervalDomainLift, hy₀] using hslab τ hτslab y₀ hy₀
    have hdamp : 0 ≤ p.b * (restartField a h u s y) ^ p.α :=
      mul_nonneg p.hb (Real.rpow_nonneg hu_pos.le p.α)
    unfold restartLogisticM
    calc
      restartField a h u s y *
          (p.a - p.b * restartField a h u s y ^ p.α) ≤
          restartField a h u s y * p.a := by nlinarith
      _ ≤ M * p.a := mul_le_mul_of_nonneg_right hu_le p.ha
      _ = p.a * M := by ring
  obtain ⟨Cell, hCell, hsource_abs⟩ :=
    exists_restartLogisticM_bound hsol ha hh hahT
  have hsource_cont := restartLogisticM_continuous hsol ha hh hahT
  have hint : IntervalIntegrable
      (fun s => intervalFullSemigroupOperator (r - s)
        (restartLogisticM p a h u s) x) volume 0 r :=
    ShenWork.IntervalDuhamelIntegrability.valueDuhamel_intervalIntegrable_of_joint_measurable
      hr hsource_cont.measurable hCell hsource_abs x
  have hconst_int : IntervalIntegrable (fun _ : ℝ => p.a * M) volume 0 r :=
    intervalIntegrable_const
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ r := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  have hae : (fun s => intervalFullSemigroupOperator (r - s)
      (restartLogisticM p a h u s) x) ≤ᵐ[volume.restrict (Icc (0 : ℝ) r)]
      (fun _ => p.a * M) := by
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [hne] with s hsr hs
    have hrs : 0 < r - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hsr)
    exact intervalFullSemigroupOperator_le_const hrs
      (hsource_cont.uncurry_left s).measurable.aestronglyMeasurable
      (hsource_abs s) (hsource_le s) x
  unfold restartLogisticDuhamelM
  calc
    (∫ s in (0 : ℝ)..r,
        intervalFullSemigroupOperator (r - s) (restartLogisticM p a h u s) x) ≤
        ∫ _s in (0 : ℝ)..r, p.a * M :=
      intervalIntegral.integral_mono_ae_restrict hr.le hint hconst_int hae
    _ = r * (p.a * M) := by
      rw [intervalIntegral.integral_const]
      norm_num [smul_eq_mul]

/-- The amended parameter guard is exactly what makes the positive part of
the logistic reaction globally bounded. -/
theorem exists_logistic_source_upper_of_guard
    (p : CM2Params) (hguard : p.a = 0 ∨ 0 < p.b) :
    ∃ L ≥ 0, ∀ z ≥ 0, z * (p.a - p.b * z ^ p.α) ≤ L := by
  rcases hguard with ha | hb
  · refine ⟨0, le_rfl, ?_⟩
    intro z hz
    rw [ha, zero_sub]
    exact mul_nonpos_of_nonneg_of_nonpos hz
      (neg_nonpos.mpr (mul_nonneg p.hb (Real.rpow_nonneg hz p.α)))
  · let L : ℝ :=
      ((p.a / (p.b * (p.α + 1)) ^ (1 / (p.α + 1))) ^
          ((p.α + 1) / p.α)) / ((p.α + 1) / p.α)
    have hL : 0 ≤ L := by
      dsimp [L]
      have hq : 0 < (p.α + 1) / p.α := div_pos (by linarith [p.hα]) p.hα
      have hbase : 0 ≤ p.a / (p.b * (p.α + 1)) ^ (1 / (p.α + 1)) :=
        div_nonneg p.ha (Real.rpow_nonneg (mul_nonneg hb.le (by linarith [p.hα])) _)
      exact div_nonneg (Real.rpow_nonneg hbase _) hq.le
    refine ⟨L, hL, ?_⟩
    intro z hz
    have hy :=
      ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation.scalar_rpow_young_absorb
        (r := (1 : ℝ)) (s := p.α + 1) (A := p.a) (eps := p.b) (x := z)
        (by norm_num) (by linarith [p.hα]) p.ha hb hz
    have hpow : z ^ (1 : ℝ) = z := Real.rpow_one z
    have hmul : z * z ^ p.α = z ^ (p.α + 1) := by
      by_cases hz0 : z = 0
      · subst z
        simp [ne_of_gt p.hα, ne_of_gt (by linarith [p.hα] : 0 < p.α + 1)]
      · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
        calc
          z * z ^ p.α = z ^ (1 : ℝ) * z ^ p.α := by rw [hpow]
          _ = z ^ ((1 : ℝ) + p.α) := (Real.rpow_add hzpos 1 p.α).symm
          _ = z ^ (p.α + 1) := by ring_nf
    dsimp [L]
    norm_num at hy
    rw [show z * (p.a - p.b * z ^ p.α) =
        p.a * z - p.b * z ^ (p.α + 1) by rw [← hmul]; ring]
    simp only [one_div]
    linarith

/-- Guarded one-sided logistic Duhamel bound, independent of the solution
maximum. -/
theorem restartLogisticDuhamelM_le_of_guard
    {p : CM2Params} {T a h r L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T)
    (hr : 0 < r)
    (hsource : ∀ z ≥ 0, z * (p.a - p.b * z ^ p.α) ≤ L)
    (x : ℝ) : restartLogisticDuhamelM p a h u r x ≤ r * L := by
  have hsource_le : ∀ s y, restartLogisticM p a h u s y ≤ L := by
    intro s y
    exact hsource _ (restartField_u_pos hsol ha hh hahT s y).le
  obtain ⟨Cell, hCell, hsource_abs⟩ :=
    exists_restartLogisticM_bound hsol ha hh hahT
  have hsource_cont := restartLogisticM_continuous hsol ha hh hahT
  have hint : IntervalIntegrable
      (fun s => intervalFullSemigroupOperator (r - s)
        (restartLogisticM p a h u s) x) volume 0 r :=
    ShenWork.IntervalDuhamelIntegrability.valueDuhamel_intervalIntegrable_of_joint_measurable
      hr hsource_cont.measurable hCell hsource_abs x
  have hconst_int : IntervalIntegrable (fun _ : ℝ => L) volume 0 r :=
    intervalIntegrable_const
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ r := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  have hae : (fun s => intervalFullSemigroupOperator (r - s)
      (restartLogisticM p a h u s) x) ≤ᵐ[volume.restrict (Icc (0 : ℝ) r)]
      (fun _ => L) := by
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [hne] with s hsr hs
    have hrs : 0 < r - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hsr)
    exact intervalFullSemigroupOperator_le_const hrs
      (hsource_cont.uncurry_left s).measurable.aestronglyMeasurable
      (hsource_abs s) (hsource_le s) x
  unfold restartLogisticDuhamelM
  calc
    (∫ s in (0 : ℝ)..r,
        intervalFullSemigroupOperator (r - s) (restartLogisticM p a h u s) x) ≤
        ∫ _s in (0 : ℝ)..r, L :=
      intervalIntegral.integral_mono_ae_restrict hr.le hint hconst_int hae
    _ = r * L := by
      rw [intervalIntegral.integral_const]
      norm_num [smul_eq_mul]

/-- Quantitative upper bound for every physical slice at a restart lag bounded
away from zero.  The only occurrence of the slab maximum is the sublinear
factor `M^m`. -/
theorem solutionSlice_le_of_restart_lp_slab_guard
    {p : CM2Params} {T a h δ r pExp C M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T)
    (hδ : 0 < δ) (hδr : δ ≤ r) (hrh : r ≤ h)
    (hp : 1 < pExp) (hγp : p.γ ≤ pExp)
    (hpower : ∀ τ, 0 < τ → τ < T →
      intervalDomainM.integral (fun z => (u τ z) ^ pExp) ≤ C)
    (hM : 0 ≤ M)
    (hslab : ∀ τ ∈ Icc a (a + h), ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u τ) x ≤ M)
    (hL : 0 ≤ L)
    (hsource : ∀ z ≥ 0, z * (p.a - p.b * z ^ p.α) ≤ L) :
    ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u (a + r)) x ≤
        fixedHeatKernelBound δ * (C + 1) +
          |p.χ₀| *
            (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
              (2 * Real.sqrt h) *
                (M ^ p.m * (2 * p.ν * (C + 1)))) + h * L := by
  have hr : 0 < r := hδ.trans_le hδr
  have haT : a < T := lt_of_lt_of_le (by linarith : a < a + r)
    (lt_of_le_of_lt (by linarith) hahT).le
  have hC1 : 0 ≤ C + 1 := by
    have hγ := solution_gamma_integral_le_of_lp hsol ha haT hγp
      (hpower a ha haT)
    have hγnonneg : 0 ≤ ∫ y in (0 : ℝ)..1,
        intervalDomainLift (u a) y ^ p.γ :=
      intervalIntegral.integral_nonneg (by norm_num) (fun y hy =>
        Real.rpow_nonneg
          (solution_lift_pos_Icc hsol ⟨ha, haT⟩ y (by
            simpa [Set.uIcc_of_le zero_le_one] using hy)).le _)
    linarith
  have hqbound := restartFluxM_abs_le_of_lp_and_slab
    hsol ha hh hahT hγp hpower hM hslab
  have hCq : 0 ≤ M ^ p.m * (2 * p.ν * (C + 1)) :=
    mul_nonneg (Real.rpow_nonneg hM p.m)
      (mul_nonneg (mul_nonneg (by norm_num) p.hν.le) hC1)
  have hqcont := restartFluxM_continuous hsol ha hh hahT
  have hhom : ∀ x,
      |intervalFullSemigroupOperator r (intervalDomainLift (u a)) x| ≤
        fixedHeatKernelBound δ * (C + 1) := by
    intro x
    have hb := restartHomM_abs_le_of_lp hsol ha haT hr hp
      (hpower a ha haT) x
    exact hb.trans <| mul_le_mul_of_nonneg_right
      (fixedHeatKernelBound_anti hδ hδr) hC1
  have hchem : ∀ x, |restartChemDuhamelM p a h u v r x| ≤
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
        (2 * Real.sqrt h) * (M ^ p.m * (2 * p.ν * (C + 1))) := by
    intro x
    have hb := restartChemDuhamelM_abs_le hr hCq hqcont.measurable hqbound x
    have hsqrt : Real.sqrt r ≤ Real.sqrt h := Real.sqrt_le_sqrt hrh
    have hCg :=
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
    nlinarith [Real.sqrt_nonneg r, Real.sqrt_nonneg h,
      mul_nonneg hCg hCq, hsqrt]
  have hlog : ∀ x, restartLogisticDuhamelM p a h u r x ≤ h * L := by
    intro x
    have hb := restartLogisticDuhamelM_le_of_guard hsol ha hh hahT hr hsource x
    exact hb.trans (mul_le_mul_of_nonneg_right hrh hL)
  let R : ℝ := fixedHeatKernelBound δ * (C + 1) +
    |p.χ₀| *
      (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
        (2 * Real.sqrt h) * (M ^ p.m * (2 * p.ν * (C + 1)))) + h * L
  have hcand : ∀ x, faithfulRestartDuhamelM p a h u v r x ≤ R := by
    intro x
    unfold faithfulRestartDuhamelM
    dsimp [R]
    have hh₀ := hhom x
    have hc₀ := hchem x
    have hl₀ := hlog x
    have hχ : 0 ≤ |p.χ₀| := abs_nonneg _
    have hchemMul :
        -p.χ₀ * restartChemDuhamelM p a h u v r x ≤
          |p.χ₀| * |restartChemDuhamelM p a h u v r x| := by
      calc
        -p.χ₀ * restartChemDuhamelM p a h u v r x ≤
            |-p.χ₀ * restartChemDuhamelM p a h u v r x| := le_abs_self _
        _ = |p.χ₀| * |restartChemDuhamelM p a h u v r x| := by
          rw [abs_mul, abs_neg]
    nlinarith [le_abs_self
      (intervalFullSemigroupOperator r (intervalDomainLift (u a)) x),
      mul_le_mul_of_nonneg_left hc₀ hχ]
  have haeEq := faithfulRestartDuhamelM_ae_eq_solution
    hsol ha hh hahT hr hrh
  have haeLe : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      intervalDomainLift (u (a + r)) x ≤ R := by
    filter_upwards [haeEq] with x hx
    rw [← hx]
    exact hcand x
  have har0 : 0 < a + r := by linarith
  have harT : a + r < T :=
    lt_of_le_of_lt (by simpa [add_comm] using add_le_add_left hrh a) hahT
  have hcont := solution_lift_continuousOn_Icc hsol ⟨har0, harT⟩
  simpa [R] using continuousOn_le_of_ae_le_Ioc hcont haeLe

/-- Complete finite-horizon boundedness for every faithful slow-diffusion
classical solution with positive initial trace. -/
theorem slow_bounded_before
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hbeta : 1 ≤ p.β) (hm1 : p.m < 1) :
    IsPaper2BoundedBefore intervalDomainM T u := by
  obtain ⟨pExp, hpExp, hLp⟩ :=
    exists_high_slow_lp_power_bounded_before
      hguard hu₀ hsol htrace hbeta hm1
  have hp : 1 < pExp :=
    lt_of_le_of_lt (le_max_left _ _) hpExp
  have hγp : p.γ ≤ pExp :=
    le_trans (le_max_right p.m p.γ)
      (lt_of_le_of_lt (le_max_right 1 (max p.m p.γ)) hpExp).le
  obtain ⟨C, hpower⟩ := hLp
  obtain ⟨δ, hδ, E, hE, hearly⟩ :=
    exists_initial_trace_pointwise_upper hu₀ hsol htrace
  obtain ⟨L, hL, hsource⟩ := exists_logistic_source_upper_of_guard p hguard
  let a : ℝ := min (δ / 4) (T / 4)
  have ha : 0 < a := lt_min
    (div_pos hδ (by norm_num)) (div_pos hsol.1 (by norm_num))
  have h2aδ : 2 * a < δ := by
    have haδ : a ≤ δ / 4 := min_le_left _ _
    linarith
  have h2aT : 2 * a < T := by
    have haT : a ≤ T / 4 := min_le_right _ _
    linarith [hsol.1]
  have haT : a < T := lt_trans (by linarith : a < 2 * a) h2aT
  have hC1 : 0 ≤ C + 1 := by
    have hγ := solution_gamma_integral_le_of_lp hsol ha haT hγp
      (hpower a ha haT)
    have hγnonneg : 0 ≤ ∫ y in (0 : ℝ)..1,
        intervalDomainLift (u a) y ^ p.γ :=
      intervalIntegral.integral_nonneg (by norm_num) (fun y hy =>
        Real.rpow_nonneg
          (solution_lift_pos_Icc hsol ⟨ha, haT⟩ y (by
            simpa [Set.uIcc_of_le zero_le_one] using hy)).le _)
    linarith
  let G : ℝ := 2 * p.ν * (C + 1)
  have hG : 0 ≤ G := by
    dsimp [G]
    exact mul_nonneg (mul_nonneg (by norm_num) p.hν.le) hC1
  let A : ℝ := fixedHeatKernelBound a * (C + 1) + T * L
  let B : ℝ := |p.χ₀| *
    (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
      (2 * Real.sqrt T) * G)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg
      (mul_nonneg (fixedHeatKernelBound_nonneg a) hC1)
      (mul_nonneg hsol.1.le hL)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (abs_nonneg _)
      (mul_nonneg
        (mul_nonneg
          ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
          (mul_nonneg (by norm_num) (Real.sqrt_nonneg T))) hG)
  obtain ⟨R, hR, hscalar⟩ :=
    exists_uniform_bound_of_sublinear_inequality p.hm hm1 hA hB
  refine ⟨max E R, ?_⟩
  intro t ht0 htT
  change intervalDomainSupNorm (u t) ≤ max E R
  unfold intervalDomainSupNorm
  apply csSup_le
  · let x₀ : intervalDomainPoint := ⟨0, ⟨le_rfl, zero_le_one⟩⟩
    exact ⟨|u t x₀|, ⟨x₀, rfl⟩⟩
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  change |u t x| ≤ max E R
  rw [abs_of_pos (u_pos hsol ht0 htT x)]
  by_cases htEarly : t < 2 * a
  · exact (hearly t ht0 (htEarly.trans h2aδ) x).trans (le_max_left _ _)
  · have h2at : 2 * a ≤ t := le_of_not_gt htEarly
    let h : ℝ := t - a
    have hh : 0 ≤ h := by dsimp [h]; linarith
    have hha : a ≤ h := by dsimp [h]; linarith
    have haht : a + h = t := by dsimp [h]; ring
    have hahT : a + h < T := by simpa [haht] using htT
    let Kset : Set (ℝ × ℝ) := Icc (0 : ℝ) h ×ˢ Icc (0 : ℝ) 1
    let F : ℝ × ℝ → ℝ := fun z => restartField a h u z.1 z.2
    have hKcompact : IsCompact Kset := isCompact_Icc.prod isCompact_Icc
    have hKne : Kset.Nonempty := by
      exact ⟨(0, 0), ⟨⟨le_rfl, hh⟩, ⟨le_rfl, zero_le_one⟩⟩⟩
    have hFcont : ContinuousOn F Kset :=
      (restartField_continuous hsol ha hh hahT u (Or.inl rfl)).continuousOn
    obtain ⟨z, hz, hzmax⟩ := hKcompact.exists_isMaxOn hKne hFcont
    let M : ℝ := F z
    have hztime0 : 0 < a + z.1 := by linarith [hz.1.1]
    have hztimeT : a + z.1 < T := by
      have hzle : a + z.1 ≤ a + h := by
        simpa [add_comm] using add_le_add_left hz.1.2 a
      exact hzle.trans_lt hahT
    have hM : 0 ≤ M := by
      have hpos := u_pos hsol hztime0 hztimeT
        (⟨z.2, hz.2⟩ : intervalDomainPoint)
      have heq := restartField_eq_physical
        (a := a) (h := h) (w := u) hz.1 hz.2
      dsimp [M, F]
      rw [heq]
      simpa [intervalDomainLift, hz.2] using hpos.le
    have hslab : ∀ τ ∈ Icc a (a + h), ∀ q ∈ Icc (0 : ℝ) 1,
        intervalDomainLift (u τ) q ≤ M := by
      intro τ hτ q hq
      have hrange : τ - a ∈ Icc (0 : ℝ) h := by
        constructor <;> linarith [hτ.1, hτ.2]
      have hm := hzmax (show (τ - a, q) ∈ Kset from ⟨hrange, hq⟩)
      have heq := restartField_eq_physical (a := a) (h := h) (w := u) hrange hq
      dsimp [M, F] at hm
      rw [heq, show a + (τ - a) = τ by ring] at hm
      exact hm
    have hutM : u t x ≤ M := by
      have hm := hzmax (show (h, x.1) ∈ Kset from
        ⟨Set.right_mem_Icc.mpr hh, x.property⟩)
      have heq := restartField_eq_physical
        (a := a) (h := h) (w := u) (Set.right_mem_Icc.mpr hh) x.property
      dsimp [M, F] at hm
      rw [heq, haht] at hm
      simpa [intervalDomainLift, x.property] using hm
    have hMbound : M ≤ max E R := by
      by_cases hzEarly : z.1 < a
      · have htimeEarly : a + z.1 < 2 * a := by linarith
        have hME := hearly (a + z.1) hztime0
          (htimeEarly.trans h2aδ) (⟨z.2, hz.2⟩ : intervalDomainPoint)
        have heq := restartField_eq_physical (a := a) (h := h) (w := u) hz.1 hz.2
        have hME' : M ≤ E := by
          dsimp [M, F]
          rw [heq]
          simpa [intervalDomainLift, hz.2] using hME
        exact hME'.trans (le_max_left _ _)
      · have haz : a ≤ z.1 := le_of_not_gt hzEarly
        have hslice := solutionSlice_le_of_restart_lp_slab_guard
          hsol ha hh hahT ha haz hz.1.2 hp hγp hpower hM hslab hL hsource
          z.2 hz.2
        have heq := restartField_eq_physical (a := a) (h := h) (w := u) hz.1 hz.2
        have hraw : M ≤ fixedHeatKernelBound a * (C + 1) +
            |p.χ₀| *
              (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
                (2 * Real.sqrt h) * (M ^ p.m * G)) + h * L := by
          have hMeq : M = intervalDomainLift (u (a + z.1)) z.2 := by
            dsimp [M, F]
            exact heq
          calc
            M = intervalDomainLift (u (a + z.1)) z.2 := hMeq
            _ ≤ fixedHeatKernelBound a * (C + 1) +
                |p.χ₀| *
                  (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
                    (2 * Real.sqrt h) * (M ^ p.m * G)) + h * L := by
              simpa [G] using hslice
        let Bh : ℝ := |p.χ₀| *
          (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
            (2 * Real.sqrt h) * G)
        have hhT : h ≤ T := by dsimp [h]; linarith
        have hsqrt : Real.sqrt h ≤ Real.sqrt T := Real.sqrt_le_sqrt hhT
        have hBhB : Bh ≤ B := by
          dsimp [Bh, B]
          have hCg :=
            ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
          have hχ := abs_nonneg p.χ₀
          have htwo : (0 : ℝ) ≤ 2 := by norm_num
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hsqrt htwo) hCg) hG) hχ
        have hchemRewrite : |p.χ₀| *
              (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
                (2 * Real.sqrt h) * (M ^ p.m * G)) = Bh * M ^ p.m := by
          dsimp [Bh]
          ring
        rw [hchemRewrite] at hraw
        have hchemLe : Bh * M ^ p.m ≤ B * M ^ p.m :=
          mul_le_mul_of_nonneg_right hBhB (Real.rpow_nonneg hM p.m)
        have hlogLe : h * L ≤ T * L := mul_le_mul_of_nonneg_right hhT hL
        have hineq : M ≤ A + B * M ^ p.m := by
          dsimp [A]
          linarith
        have hMR : M ≤ R := hscalar M hM hineq
        exact hMR.trans (le_max_right _ _)
    exact hutM.trans hMbound

#print axioms slow_bounded_before

end ShenWork.Paper2.IntervalDomainM
