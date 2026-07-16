import ShenWork.Paper1.WholeLineWeightedRegularityRawDQProfile
import ShenWork.Paper1.WholeLineWeightedRegularityHomogeneousRawDQ

open Filter MeasureTheory Set
open scoped Interval RealInnerProductSpace

noncomputable section

namespace ShenWork.Paper1

/-!
# One-step `L²` assembly for the raw spatial quotient

This is the coefficient-aware version of the three-leg Duhamel triangle
estimate.  It is stated on an arbitrary restart interval and therefore
matches the positive-time perturbation restart without translating time.
-/

theorem exists_wholeLineRealL2_threeLeg_interval_with_coeff
    {a b A k : ℝ} (hab : a ≤ b)
    (Z₀ : WholeLineRealL2) (ZG ZR : ℝ → WholeLineRealL2)
    (f₀ fG fR gG gR : ℝ → ℝ)
    (hZG_int : IntervalIntegrable ZG volume a b)
    (hZR_int : IntervalIntegrable ZR volume a b)
    (hgG_int : IntervalIntegrable gG volume a b)
    (hgR_int : IntervalIntegrable gR volume a b)
    (hZ₀ : ‖Z₀‖ ≤ A)
    (hZG : ∀ s ∈ Set.Icc a b, ‖ZG s‖ ≤ gG s)
    (hZR : ∀ s ∈ Set.Icc a b, ‖ZR s‖ ≤ gR s)
    (hZ₀_rep : ((Z₀ : ℝ → ℝ) =ᵐ[volume] f₀))
    (hZG_rep : (((∫ s in a..b, ZG s) : WholeLineRealL2) : ℝ → ℝ)
      =ᵐ[volume] fG)
    (hZR_rep : (((∫ s in a..b, ZR s) : WholeLineRealL2) : ℝ → ℝ)
      =ᵐ[volume] fR) :
    ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x => f₀ x + k * fG x + fR x) ∧
      ‖Z‖ ≤ A + |k| * (∫ s in a..b, gG s) + ∫ s in a..b, gR s := by
  let G : WholeLineRealL2 := ∫ s in a..b, ZG s
  let R : WholeLineRealL2 := ∫ s in a..b, ZR s
  let Z : WholeLineRealL2 := (Z₀ + k • G) + R
  have hGnorm : ‖G‖ ≤ ∫ s in a..b, gG s := by
    dsimp only [G]
    exact wholeLineRealL2_intervalIntegral_norm_le_of_majorant
      hab hZG_int hgG_int hZG
  have hRnorm : ‖R‖ ≤ ∫ s in a..b, gR s := by
    dsimp only [R]
    exact wholeLineRealL2_intervalIntegral_norm_le_of_majorant
      hab hZR_int hgR_int hZR
  refine ⟨Z, ?_, ?_⟩
  · have hadd₀ : (((Z₀ + k • G : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        fun x => Z₀ x + (k • G) x) := Lp.coeFn_add Z₀ (k • G)
    have hadd₁ : ((Z : ℝ → ℝ) =ᵐ[volume]
        fun x => (Z₀ + k • G) x + R x) := by
      simpa only [Z] using Lp.coeFn_add (Z₀ + k • G) R
    have hsmul : (((k • G : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        fun x => k * G x) := by
      simpa only [Pi.smul_apply, smul_eq_mul] using Lp.coeFn_smul k G
    filter_upwards [hadd₀, hadd₁, hsmul, hZ₀_rep, hZG_rep, hZR_rep]
      with x ha₀ ha₁ hk h₀ hG hR
    calc
      Z x = (Z₀ + k • G) x + R x := ha₁
      _ = (Z₀ x + (k • G) x) + R x := by rw [ha₀]
      _ = (Z₀ x + k * G x) + R x := by rw [hk]
      _ = f₀ x + k * fG x + fR x := by
        dsimp only [G, R] at hG hR ⊢
        rw [h₀, hG, hR]
  · calc
      ‖Z‖ ≤ ‖Z₀‖ + ‖k • G‖ + ‖R‖ := by
        dsimp only [Z]
        exact (norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)
      _ = ‖Z₀‖ + |k| * ‖G‖ + ‖R‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ A + |k| * (∫ s in a..b, gG s) + ∫ s in a..b, gR s := by
        gcongr

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.exists_wholeLineRealL2_threeLeg_interval_with_coeff
