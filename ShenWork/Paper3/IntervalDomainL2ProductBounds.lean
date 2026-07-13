/- Elementary physical `L²` calculus used by the route-(a) Nemytskii bound. -/
import ShenWork.Paper3.IntervalDomainNonlinearStrongEstimate

namespace ShenWork.Paper3

open MeasureTheory Set Real
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel

noncomputable section

def intervalL2Size (f : ℝ → ℝ) : ℝ :=
  Real.sqrt (∫ x in (0 : ℝ)..1, (f x) ^ 2)

theorem intervalL2Size_nonneg (f : ℝ → ℝ) :
    0 ≤ intervalL2Size f := Real.sqrt_nonneg _

private theorem memLp_sq_intervalIntegrable
    {f : ℝ → ℝ} (hf : MemLp f 2 (intervalMeasure 1)) :
    IntervalIntegrable (fun x => (f x) ^ 2) volume 0 1 := by
  have hsq := hf.integrable_sq
  change IntegrableOn (fun x => (f x) ^ 2) (Set.Icc (0 : ℝ) 1) volume at hsq
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by norm_num : (0 : ℝ) ≤ 1)]
  exact hsq.mono_set Set.Ioc_subset_Icc_self

theorem intervalL2Size_sq_integral_nonneg (f : ℝ → ℝ) :
    0 ≤ ∫ x in (0 : ℝ)..1, (f x) ^ 2 :=
  intervalIntegral.integral_nonneg (by norm_num) (fun x _ => sq_nonneg _)

/-- Multiplication by a bounded physical factor is bounded on interval `L²`. -/
theorem intervalL2Size_le_of_pointwise_mul
    {f g : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : MemLp f 2 (intervalMeasure 1))
    (hg : MemLp g 2 (intervalMeasure 1))
    (hfg : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ B * |g x|) :
    intervalL2Size f ≤ B * intervalL2Size g := by
  have hfsq := memLp_sq_intervalIntegrable hf
  have hgsq := memLp_sq_intervalIntegrable hg
  have hmajor : IntervalIntegrable
      (fun x => B ^ 2 * (g x) ^ 2) volume 0 1 :=
    hgsq.const_mul (B ^ 2)
  have hpoint : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (f x) ^ 2 ≤ B ^ 2 * (g x) ^ 2 := by
    intro x hx
    have h := hfg x hx
    have hsquared := mul_self_le_mul_self (abs_nonneg (f x)) h
    calc
      (f x) ^ 2 = |f x| ^ 2 := by rw [sq_abs]
      _ ≤ (B * |g x|) ^ 2 := by simpa [pow_two] using hsquared
      _ = B ^ 2 * (g x) ^ 2 := by rw [mul_pow, sq_abs]
  have hint : (∫ x in (0 : ℝ)..1, (f x) ^ 2) ≤
      B ^ 2 * (∫ x in (0 : ℝ)..1, (g x) ^ 2) := by
    calc
      _ ≤ ∫ x in (0 : ℝ)..1, B ^ 2 * (g x) ^ 2 :=
        intervalIntegral.integral_mono_on (by norm_num) hfsq hmajor hpoint
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  unfold intervalL2Size
  calc
    Real.sqrt (∫ x in (0 : ℝ)..1, (f x) ^ 2) ≤
        Real.sqrt (B ^ 2 * (∫ x in (0 : ℝ)..1, (g x) ^ 2)) :=
      Real.sqrt_le_sqrt hint
    _ = B * Real.sqrt (∫ x in (0 : ℝ)..1, (g x) ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hB]

/-- Coarse Minkowski bound sufficient for the finite seven-term flux
expansion.  The harmless `sqrt 2` avoids importing a separate `Lp`-norm
identification theorem. -/
theorem intervalL2Size_add_le
    {f g : ℝ → ℝ}
    (hf : MemLp f 2 (intervalMeasure 1))
    (hg : MemLp g 2 (intervalMeasure 1)) :
    intervalL2Size (fun x => f x + g x) ≤
      Real.sqrt 2 * (intervalL2Size f + intervalL2Size g) := by
  have hsum : MemLp (fun x => f x + g x) 2 (intervalMeasure 1) := hf.add hg
  have hsumsq := memLp_sq_intervalIntegrable hsum
  have hfsq := memLp_sq_intervalIntegrable hf
  have hgsq := memLp_sq_intervalIntegrable hg
  have hmajor : IntervalIntegrable
      (fun x => 2 * (f x) ^ 2 + 2 * (g x) ^ 2) volume 0 1 :=
    (hfsq.const_mul 2).add (hgsq.const_mul 2)
  have hpoint : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (f x + g x) ^ 2 ≤ 2 * (f x) ^ 2 + 2 * (g x) ^ 2 := by
    intro x _
    nlinarith [sq_nonneg (f x - g x)]
  have hint : (∫ x in (0 : ℝ)..1, (f x + g x) ^ 2) ≤
      2 * (∫ x in (0 : ℝ)..1, (f x) ^ 2) +
        2 * (∫ x in (0 : ℝ)..1, (g x) ^ 2) := by
    calc
      _ ≤ ∫ x in (0 : ℝ)..1,
          (2 * (f x) ^ 2 + 2 * (g x) ^ 2) :=
        intervalIntegral.integral_mono_on (by norm_num) hsumsq hmajor hpoint
      _ = (∫ x in (0 : ℝ)..1, 2 * (f x) ^ 2) +
          ∫ x in (0 : ℝ)..1, 2 * (g x) ^ 2 := by
        rw [intervalIntegral.integral_add
          (hfsq.const_mul 2) (hgsq.const_mul 2)]
      _ = _ := by simp only [intervalIntegral.integral_const_mul]
  let If : ℝ := ∫ x in (0 : ℝ)..1, (f x) ^ 2
  let Ig : ℝ := ∫ x in (0 : ℝ)..1, (g x) ^ 2
  have hIf : 0 ≤ If := intervalL2Size_sq_integral_nonneg f
  have hIg : 0 ≤ Ig := intervalL2Size_sq_integral_nonneg g
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hIfRoot : Real.sqrt If ^ 2 = If := Real.sq_sqrt hIf
  have hIgRoot : Real.sqrt Ig ^ 2 = Ig := Real.sq_sqrt hIg
  have hcross : 0 ≤ Real.sqrt If * Real.sqrt Ig :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hroot : Real.sqrt (2 * If + 2 * Ig) ≤
      Real.sqrt 2 * (Real.sqrt If + Real.sqrt Ig) := by
    have hleft : 0 ≤ Real.sqrt (2 * If + 2 * Ig) := Real.sqrt_nonneg _
    have hright : 0 ≤ Real.sqrt 2 * (Real.sqrt If + Real.sqrt Ig) := by
      positivity
    apply (sq_le_sq₀ hleft hright).1
    rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * If + 2 * Ig)]
    nlinarith
  unfold intervalL2Size
  calc
    Real.sqrt (∫ x in (0 : ℝ)..1, (f x + g x) ^ 2) ≤
        Real.sqrt (2 * If + 2 * Ig) := by
      apply Real.sqrt_le_sqrt
      simpa [If, Ig] using hint
    _ ≤ Real.sqrt 2 * (Real.sqrt If + Real.sqrt Ig) := hroot
    _ = _ := by rfl

/-- A pointwise bounded measurable profile belongs to interval `L²`. -/
theorem memLp_two_of_pointwise_abs_bound
    {f : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : AEStronglyMeasurable f (intervalMeasure 1))
    (hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ B) :
    MemLp f 2 (intervalMeasure 1) := by
  have hone : MemLp (fun _x : ℝ => (1 : ℝ)) 2 (intervalMeasure 1) :=
    memLp_const 1
  have hdom : ∀ᵐ x ∂ intervalMeasure 1, ‖f x‖ ≤ ‖B * (1 : ℝ)‖ := by
    have hmem : ∀ᵐ x ∂ intervalMeasure 1, x ∈ Set.Icc (0 : ℝ) 1 :=
      ae_restrict_mem measurableSet_Icc
    filter_upwards [hmem] with x hx
    simpa [Real.norm_eq_abs, abs_of_nonneg hB] using hbound x hx
  exact (hone.const_mul B).mono hf hdom

#print axioms intervalL2Size_le_of_pointwise_mul
#print axioms intervalL2Size_add_le
#print axioms memLp_two_of_pointwise_abs_bound

end

end ShenWork.Paper3
