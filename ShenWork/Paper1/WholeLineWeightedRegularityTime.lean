/-
  ShenWork/Paper1/WholeLineWeightedRegularityTime.lean

  Dominated-convergence-free time differentiation of whole-line quadratic
  energies.  The analytic input is differentiability in the Hilbert space
  `L²(ℝ)`; the scalar energy identity is then the norm-square chain rule.
-/
import ShenWork.Paper1.Theorem12WeightedEnergy
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.L2Space

open Filter MeasureTheory Topology
open scoped RealInnerProductSpace Topology

noncomputable section

namespace ShenWork.Paper1

/-- The Hilbert-space quadratic chain rule, stated in the native
difference-quotient form needed by weighted mild-solution arguments. -/
theorem halfNormSq_hasDerivAt_of_differenceQuotient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {Z : ℝ → E} {Zt : E} {t : ℝ}
    (hquot :
      Tendsto (fun h : ℝ => h⁻¹ • (Z (t + h) - Z t)) (𝓝[≠] 0) (𝓝 Zt)) :
    HasDerivAt (fun s => (1 / 2 : ℝ) * ‖Z s‖ ^ 2) (⟪Z t, Zt⟫) t := by
  have hZ : HasDerivAt Z Zt t :=
    hasDerivAt_iff_tendsto_slope_zero.mpr hquot
  convert hZ.norm_sq.const_mul (1 / 2 : ℝ) using 1
  · ring

/-- The concrete real `L²` space on the whole line. -/
abbrev WholeLineRealL2 := MeasureTheory.Lp ℝ 2 (volume : Measure ℝ)

/-- A pointwise representative realizes the whole-line half energy as half
the squared norm of its `L²` class. -/
theorem wholeLineHalfEnergy_eq_halfNormSq_of_aeEq
    {phi : ℝ → ℝ → ℝ} {t : ℝ} (Z : WholeLineRealL2)
    (hrep : (Z : ℝ → ℝ) =ᵐ[volume] phi t) :
    ShenWork.PaperOne.wholeLineHalfEnergy phi t =
      (1 / 2 : ℝ) * ‖Z‖ ^ 2 := by
  rw [ShenWork.PaperOne.wholeLineHalfEnergy,
    MeasureTheory.integral_const_mul]
  rw [← real_inner_self_eq_norm_sq Z, MeasureTheory.L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [hrep] with x hx
  simp [hx, pow_two]

/-- The real `L²` inner product is the integral of the product of any two
chosen pointwise representatives. -/
theorem wholeLineIntegral_mul_eq_inner_of_aeEq
    {phi psi : ℝ → ℝ} (Z Zt : WholeLineRealL2)
    (hrep : (Z : ℝ → ℝ) =ᵐ[volume] phi)
    (htrep : (Zt : ℝ → ℝ) =ᵐ[volume] psi) :
    (∫ x : ℝ, phi x * psi x) = ⟪Z, Zt⟫ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hrep, htrep] with x hx htx
  rw [hx, htx]
  symm
  calc
    ⟪phi x, psi x⟫ =
        ⟪phi x • (1 : ℝ), psi x • (1 : ℝ)⟫ := by simp
    _ = phi x * psi x * ⟪(1 : ℝ), (1 : ℝ)⟫ := by
      rw [real_inner_smul_left, real_inner_smul_right]
      ring
    _ = phi x * psi x := by
      rw [real_inner_self_eq_norm_sq]
      norm_num

/-- Dominated-convergence-free differentiation of a concrete whole-line
quadratic energy.  The family `Z` is an `L²` lifting of the pointwise field
near `t`; `Zt` is an `L²` lifting of its proposed time derivative. -/
theorem wholeLineHalfEnergy_hasDerivAt_of_L2_differenceQuotient
    {phi phi_t : ℝ → ℝ → ℝ}
    {Z : ℝ → WholeLineRealL2} {Zt : WholeLineRealL2} {t : ℝ}
    (hquot :
      Tendsto (fun h : ℝ => h⁻¹ • (Z (t + h) - Z t)) (𝓝[≠] 0) (𝓝 Zt))
    (hrep : ∀ᶠ s in 𝓝 t, (Z s : ℝ → ℝ) =ᵐ[volume] phi s)
    (htrep : (Zt : ℝ → ℝ) =ᵐ[volume] phi_t t) :
    HasDerivAt (ShenWork.PaperOne.wholeLineHalfEnergy phi)
      (∫ x : ℝ, phi t x * phi_t t x) t := by
  have hnorm := halfNormSq_hasDerivAt_of_differenceQuotient hquot
  have heq :
      ShenWork.PaperOne.wholeLineHalfEnergy phi =ᶠ[𝓝 t]
        fun s => (1 / 2 : ℝ) * ‖Z s‖ ^ 2 := by
    filter_upwards [hrep] with s hs
    exact wholeLineHalfEnergy_eq_halfNormSq_of_aeEq (Z s) hs
  have henergy :
      HasDerivAt (ShenWork.PaperOne.wholeLineHalfEnergy phi) ⟪Z t, Zt⟫ t :=
    heq.hasDerivAt_iff.mpr hnorm
  rw [wholeLineIntegral_mul_eq_inner_of_aeEq (Z t) Zt
    (hrep.self_of_nhds) htrep]
  exact henergy

/-- `L²` time differentiation for the weighted co-moving population energy
in the exact shape consumed by `paper5WeightedEnergy_deriv_le_common_of_coreIntegrability`.

The remaining solution-specific analytic task is precisely to construct the
lift `Z`, prove the displayed `L²` difference-quotient limit, and identify
`Zt` with the weighted material derivative.  No pointwise-in-space common
dominator is required. -/
theorem paper5WeightedHalfEnergy_hasDerivAt_of_L2_differenceQuotient
    {eta c t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {Z : ℝ → WholeLineRealL2} {Zt : WholeLineRealL2}
    (hquot :
      Tendsto (fun h : ℝ => h⁻¹ • (Z (t + h) - Z t)) (𝓝[≠] 0) (𝓝 Zt))
    (hrep : ∀ᶠ s in 𝓝 t,
      (Z s : ℝ → ℝ) =ᵐ[volume]
        paper5WeightedPopulation eta (coMovingPath c u) U s)
    (htrep : (Zt : ℝ → ℝ) =ᵐ[volume]
      paper5WeightedPopulationT eta (paper5CoMovingMaterialTime c u) t) :
    HasDerivAt (paper5WeightedHalfEnergy eta c u U)
      (∫ x : ℝ,
        paper5WeightedPopulation eta (coMovingPath c u) U t x *
          paper5WeightedPopulationT eta
            (paper5CoMovingMaterialTime c u) t x) t := by
  simpa [paper5WeightedHalfEnergy] using
    (wholeLineHalfEnergy_hasDerivAt_of_L2_differenceQuotient
      (phi := paper5WeightedPopulation eta (coMovingPath c u) U)
      (phi_t := paper5WeightedPopulationT eta
        (paper5CoMovingMaterialTime c u))
      hquot hrep htrep)

section AxiomAudit

#print axioms halfNormSq_hasDerivAt_of_differenceQuotient
#print axioms wholeLineHalfEnergy_hasDerivAt_of_L2_differenceQuotient
#print axioms paper5WeightedHalfEnergy_hasDerivAt_of_L2_differenceQuotient

end AxiomAudit

end ShenWork.Paper1
