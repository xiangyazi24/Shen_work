import ShenWork.Paper1.WholeLineWeightedRegularityRawDQOneStep
import ShenWork.Paper1.WholeLineWeightedRegularityRawDQIccProfile
import ShenWork.Paper1.WholeLineWeightedRegularityRawDQLocalFubini
import ShenWork.Paper1.WholeLineWeightedRegularityWeightedRawDQRestart

open Filter MeasureTheory Real Set
open scoped Interval RealInnerProductSpace

noncomputable section

namespace ShenWork.Paper1

/-!
# Raw-DQ restart inequality in the canonical `L²` profile
-/

/-- Identify the three-leg `L²` assembly with a prescribed canonical target
representative.  This is the last abstract Hilbert-space step before inserting
the concrete heat/source estimates. -/
theorem wholeLineRealL2_norm_le_of_threeLeg_interval_with_coeff
    {a b A k : ℝ} (hab : a ≤ b)
    (P Z₀ : WholeLineRealL2) (ZG ZR : ℝ → WholeLineRealL2)
    (target f₀ fG fR gG gR : ℝ → ℝ)
    (hZG_int : IntervalIntegrable ZG volume a b)
    (hZR_int : IntervalIntegrable ZR volume a b)
    (hgG_int : IntervalIntegrable gG volume a b)
    (hgR_int : IntervalIntegrable gR volume a b)
    (hZ₀ : ‖Z₀‖ ≤ A)
    (hZG : ∀ s ∈ Set.Icc a b, ‖ZG s‖ ≤ gG s)
    (hZR : ∀ s ∈ Set.Icc a b, ‖ZR s‖ ≤ gR s)
    (hP_rep : ((P : ℝ → ℝ) =ᵐ[volume] target))
    (hZ₀_rep : ((Z₀ : ℝ → ℝ) =ᵐ[volume] f₀))
    (hZG_rep : (((∫ s in a..b, ZG s) : WholeLineRealL2) : ℝ → ℝ)
      =ᵐ[volume] fG)
    (hZR_rep : (((∫ s in a..b, ZR s) : WholeLineRealL2) : ℝ → ℝ)
      =ᵐ[volume] fR)
    (hidentity : ∀ x, target x = f₀ x + k * fG x + fR x) :
    ‖P‖ ≤ A + |k| * (∫ s in a..b, gG s) + ∫ s in a..b, gR s := by
  rcases exists_wholeLineRealL2_threeLeg_interval_with_coeff
      hab Z₀ ZG ZR f₀ fG fR gG gR hZG_int hZR_int hgG_int hgR_int
      hZ₀ hZG hZR hZ₀_rep hZG_rep hZR_rep with ⟨Z, hZrep, hZnorm⟩
  have hPZ : P = Z := by
    apply Lp.ext
    filter_upwards [hP_rep, hZrep] with x hP hZ
    rw [hP, hZ, hidentity x]
  rw [hPZ]
  exact hZnorm

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.wholeLineRealL2_norm_le_of_threeLeg_interval_with_coeff
