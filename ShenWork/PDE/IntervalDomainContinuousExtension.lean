/-
  Continuous extension of subtype functions to ℝ (Tietze-style).

  The paper works on Ω̄ = [0,1]. Functions are in C(Ω̄) = Continuous on the
  subtype. The semigroup S(t) only sees f|_{[0,1]} (the kernel integral is
  over [0,1]). But the spectral chain (`intervalFullSemigroupOperator_eq_cosineHeatValue_Icc`)
  takes `Continuous f` (globally on ℝ).

  Bridge: extend f ∈ C(Ω̄) to ℝ by constants (f(0) for x ≤ 0, f(1) for x ≥ 1).
  This is globally continuous and agrees with `intervalDomainLift f` on (0,1).
  The semigroup congr lemma then transfers the spectral identity.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalNeumannFullKernel

open Set Filter Topology MeasureTheory

noncomputable section

namespace ShenWork.IntervalDomain

instance : TopologicalSpace intervalDomainPoint := instTopologicalSpaceSubtype

/-- Constant extension of a subtype function to ℝ: f(0) for x ≤ 0,
f(1) for x ≥ 1, f(x) for x ∈ [0,1]. Globally continuous when f is
continuous on the subtype. -/
def intervalDomainConstExtend (f : intervalDomainPoint → ℝ) : ℝ → ℝ :=
  fun x =>
    if h0 : x ≤ 0 then f ⟨0, ⟨le_refl _, zero_le_one⟩⟩
    else if h1 : 1 ≤ x then f ⟨1, ⟨zero_le_one, le_refl _⟩⟩
    else f ⟨x, ⟨(not_le.mp h0).le, (not_le.mp h1).le⟩⟩

/-- The constant extension agrees with the lift on (0,1). -/
theorem constExtend_eq_lift_on_Ioo {f : intervalDomainPoint → ℝ}
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    intervalDomainConstExtend f x = intervalDomainLift f x := by
  simp only [intervalDomainConstExtend, intervalDomainLift,
    dif_pos (Ioo_subset_Icc_self hx)]
  have h0 : ¬ x ≤ 0 := not_le.mpr hx.1
  have h1 : ¬ 1 ≤ x := not_le.mpr hx.2
  simp only [dif_neg h0, dif_neg h1]

/-- The constant extension agrees with the lift on [0,1]. -/
theorem constExtend_eq_lift_on_Icc {f : intervalDomainPoint → ℝ}
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    intervalDomainConstExtend f x = intervalDomainLift f x := by
  simp only [intervalDomainConstExtend, intervalDomainLift, dif_pos hx]
  by_cases hle : x ≤ 0
  · have hx0 : x = 0 := le_antisymm hle hx.1
    subst hx0; simp
  · simp only [dif_neg hle]
    by_cases hle1 : 1 ≤ x
    · have hx1 : x = 1 := le_antisymm hx.2 hle1
      subst hx1; simp
    · simp only [dif_neg hle1]

/-- The constant extension is globally continuous when f is continuous
on the subtype. This is the paper-faithful replacement for the false
`Continuous (intervalDomainLift f)`. -/
theorem constExtend_continuous {f : intervalDomainPoint → ℝ}
    (hf : Continuous f) : Continuous (intervalDomainConstExtend f) := by
  suffices h : intervalDomainConstExtend f = Set.IccExtend (zero_le_one (α := ℝ)) f by
    rw [h]; exact hf.Icc_extend'
  funext x
  simp only [intervalDomainConstExtend, Set.IccExtend, Set.projIcc, Function.comp]
  split_ifs with h0 h1
  · congr 1; exact Subtype.ext (by
      simp [min_eq_right (h0.trans zero_le_one), max_eq_left h0])
  · congr 1; exact Subtype.ext (by
      simp [min_eq_left h1])
  · have h0' : 0 ≤ x := (not_le.mp h0).le
    have h1' : x ≤ 1 := (not_le.mp h1).le
    congr 1; exact Subtype.ext (by simp [min_eq_right h1', max_eq_right h0'])

/-- The cosine coefficients of the constant extension equal those of the lift.
Both integrate f against cos(nπy) over [0,1], where they agree. -/
theorem cosineCoeffs_constExtend_eq_lift (f : intervalDomainPoint → ℝ) (n : ℕ) :
    ShenWork.IntervalNeumannFullKernel.cosineCoeffs (intervalDomainConstExtend f) n =
    ShenWork.IntervalNeumannFullKernel.cosineCoeffs (intervalDomainLift f) n := by
  simp only [ShenWork.IntervalNeumannFullKernel.cosineCoeffs,
    ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff]
  congr 1
  simp only [ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
  rw [constExtend_eq_lift_on_Icc hx]

/-- The semigroup operator of the constant extension equals that of the lift.
S(t) integrates against the kernel over [0,1], where both agree. -/
theorem semigroupOperator_constExtend_eq_lift
    {f : intervalDomainPoint → ℝ} {t x : ℝ} :
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t
      (intervalDomainConstExtend f) x =
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t
      (intervalDomainLift f) x := by
  simp only [ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator,
    intervalMeasure, intervalSet]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  rw [constExtend_eq_lift_on_Icc hy]

end ShenWork.IntervalDomain
