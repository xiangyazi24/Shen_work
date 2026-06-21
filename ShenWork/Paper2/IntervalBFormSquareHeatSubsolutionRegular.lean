import ShenWork.Paper2.IntervalBFormLinearDriftComparisonRegular

open Filter Topology Set

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData conjugatePicardLimit)
open ShenWork.IntervalMildPicardThreshold
  (unitClip_of_mem)
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-- Corrected squared heat lower barrier using the regular Neumann comparison
interface. -/
theorem square_heat_hbarrier_of_neumann_linear_drift_square_heat_subsolution_regular
    {T A D M : ℝ} {u₀ f : ℝ → ℝ} {B C u : ℝ → ℝ → ℝ}
    (hT : 0 < T)
    (hcoeff : NeumannLinearDriftCoefficientsRegular T B C)
    (hsuper : IsClassicalNeumannLinearDriftSuperSolution T B C u)
    (hu_initial : ∀ x ∈ Set.Icc (0 : ℝ) 1, u 0 x = u₀ x)
    (hcompare : NeumannLinearDriftComparisonRegular T B C u₀ u)
    (hbarrier_reg :
      NeumannLinearDriftSubSolutionRegularity T B C (squareHeatBarrier M f))
    (hcalc : SquareHeatSubsolutionCalculus T M f B C)
    (hM : A ^ 2 / 2 + D ≤ M)
    (hB_bound :
      ∀ t x, 0 < t → t < T → x ∈ Set.Ioo (0 : ℝ) 1 → |B t x| ≤ A)
    (hC_neg_bound :
      ∀ t x, 0 < t → t < T → x ∈ Set.Ioo (0 : ℝ) 1 → -C t x ≤ D)
    (hseed : SquareHeatSeed u₀ f) :
    ∀ t x, 0 < t → t < T → x ∈ Set.Icc (0 : ℝ) 1 →
      squareHeatBarrier M f t x ≤ u t x := by
  have hinit :
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        squareHeatBarrier M f 0 x ≤ u₀ x := by
    intro x hx
    rw [hcalc.initial_eq x hx]
    exact hseed.square_le_initial x hx
  have hpde :
      ∀ ⦃t x : ℝ⦄,
        0 < t → t < T → x ∈ Set.Ioo (0 : ℝ) 1 →
          neumannLinearDriftResidual B C (squareHeatBarrier M f) t x ≤ 0 := by
    intro t x ht htT hx
    exact
      squareHeatBarrier_subsolution_residual_nonpos
        hcalc hM hB_bound hC_neg_bound t x ht htT hx
  have hsub :
      IsClassicalNeumannLinearDriftSubSolution T B C (squareHeatBarrier M f) :=
    NeumannLinearDriftSubSolutionRegularity.toSubSolution hbarrier_reg hpde
  exact hcompare (squareHeatBarrier M f) hT hcoeff hsuper hu_initial hsub hinit

/-- Corrected strict positivity reduction through the regular comparison
interface. -/
theorem strict_pos_of_neumann_linear_drift_square_heat_subsolution_regular
    {T A D M : ℝ} {u₀ f : ℝ → ℝ} {B C u : ℝ → ℝ → ℝ}
    (hT : 0 < T)
    (hcoeff : NeumannLinearDriftCoefficientsRegular T B C)
    (hsuper : IsClassicalNeumannLinearDriftSuperSolution T B C u)
    (hu_initial : ∀ x ∈ Set.Icc (0 : ℝ) 1, u 0 x = u₀ x)
    (hcompare : NeumannLinearDriftComparisonRegular T B C u₀ u)
    (hbarrier_reg :
      NeumannLinearDriftSubSolutionRegularity T B C (squareHeatBarrier M f))
    (hcalc : SquareHeatSubsolutionCalculus T M f B C)
    (hM : A ^ 2 / 2 + D ≤ M)
    (hB_bound :
      ∀ t x, 0 < t → t < T → x ∈ Set.Ioo (0 : ℝ) 1 → |B t x| ≤ A)
    (hC_neg_bound :
      ∀ t x, 0 < t → t < T → x ∈ Set.Ioo (0 : ℝ) 1 → -C t x ≤ D)
    (hseed : SquareHeatSeed u₀ f) :
    ∀ t x, 0 < t → t < T → x ∈ Set.Icc (0 : ℝ) 1 →
      0 < u t x := by
  intro t x ht htT hx
  exact lt_of_lt_of_le
    (squareHeatBarrier_pos (M := M) ht
      hseed.continuousOn hseed.nonneg hseed.pos_somewhere x)
    (square_heat_hbarrier_of_neumann_linear_drift_square_heat_subsolution_regular
      hT hcoeff hsuper hu_initial hcompare hbarrier_reg hcalc hM
      hB_bound hC_neg_bound hseed t x ht htT hx)

/-- B-form lower barrier produced by the corrected regular comparison route. -/
theorem bform_square_heat_hbarrier_of_neumann_linear_drift_square_heat_subsolution_regular
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    {A D M : ℝ} {f : ℝ → ℝ} {drift react : ℝ → ℝ → ℝ}
    (hcoeff : NeumannLinearDriftCoefficientsRegular DB.T drift react)
    (hsuper :
      IsClassicalNeumannLinearDriftSuperSolution DB.T drift react
        (bformConjugatePicardLift p DB))
    (hu_initial :
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        bformConjugatePicardLift p DB 0 x = intervalDomainLift u₀ x)
    (hcompare :
      NeumannLinearDriftComparisonRegular DB.T drift react (intervalDomainLift u₀)
        (bformConjugatePicardLift p DB))
    (hbarrier_reg :
      NeumannLinearDriftSubSolutionRegularity DB.T drift react
        (squareHeatBarrier M f))
    (hcalc : SquareHeatSubsolutionCalculus DB.T M f drift react)
    (hM : A ^ 2 / 2 + D ≤ M)
    (hB_bound :
      ∀ t x, 0 < t → t < DB.T → x ∈ Set.Ioo (0 : ℝ) 1 →
        |drift t x| ≤ A)
    (hC_neg_bound :
      ∀ t x, 0 < t → t < DB.T → x ∈ Set.Ioo (0 : ℝ) 1 →
        -react t x ≤ D)
    (hseed : SquareHeatSeed (intervalDomainLift u₀) f) :
    ∀ t x, 0 < t → t < DB.T →
      squareHeatBarrier M f t x.1 ≤
        conjugatePicardLimit p u₀ DB.T t x := by
  intro t x ht htT
  have hx : x.1 ∈ Set.Icc (0 : ℝ) 1 := x.2
  have hreal :=
    square_heat_hbarrier_of_neumann_linear_drift_square_heat_subsolution_regular
      (T := DB.T) (A := A) (D := D) (M := M)
      (u₀ := intervalDomainLift u₀) (f := f)
      (B := drift) (C := react)
      (u := bformConjugatePicardLift p DB)
      DB.hT hcoeff hsuper hu_initial hcompare hbarrier_reg hcalc hM
      hB_bound hC_neg_bound hseed t x.1 ht htT hx
  simpa [bformConjugatePicardLift, unitClip_of_mem hx] using hreal

/-- B-form strict positivity through the corrected regular comparison route. -/
theorem bform_strictPos_of_square_heat_subsolution_regular
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    {A D M : ℝ} {f : ℝ → ℝ} {drift react : ℝ → ℝ → ℝ}
    (hcoeff : NeumannLinearDriftCoefficientsRegular DB.T drift react)
    (hsuper :
      IsClassicalNeumannLinearDriftSuperSolution DB.T drift react
        (bformConjugatePicardLift p DB))
    (hu_initial :
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        bformConjugatePicardLift p DB 0 x = intervalDomainLift u₀ x)
    (hcompare :
      NeumannLinearDriftComparisonRegular DB.T drift react (intervalDomainLift u₀)
        (bformConjugatePicardLift p DB))
    (hbarrier_reg :
      NeumannLinearDriftSubSolutionRegularity DB.T drift react
        (squareHeatBarrier M f))
    (hcalc : SquareHeatSubsolutionCalculus DB.T M f drift react)
    (hM : A ^ 2 / 2 + D ≤ M)
    (hB_bound :
      ∀ t x, 0 < t → t < DB.T → x ∈ Set.Ioo (0 : ℝ) 1 →
        |drift t x| ≤ A)
    (hC_neg_bound :
      ∀ t x, 0 < t → t < DB.T → x ∈ Set.Ioo (0 : ℝ) 1 →
        -react t x ≤ D)
    (hseed : SquareHeatSeed (intervalDomainLift u₀) f) :
    ∀ t x, 0 < t → t < DB.T →
      0 < conjugatePicardLimit p u₀ DB.T t x := by
  exact
    bform_strictPos_of_square_heat_subsolution hseed
      (bform_square_heat_hbarrier_of_neumann_linear_drift_square_heat_subsolution_regular
        hcoeff hsuper hu_initial hcompare hbarrier_reg hcalc hM
        hB_bound hC_neg_bound hseed)

/-- Route constructor superseding the banked squared-subsolution constructor:
the comparison input is the regular, satisfiable interface. -/
def bform_negpart_route_of_square_heat_subsolution_regular
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    {A D M : ℝ} {f : ℝ → ℝ} {drift react : ℝ → ℝ → ℝ}
    (datum : PositiveInitialDatum intervalDomain u₀)
    (Bbank : ShenWork.Paper2.BFormDirectClassical.BFormBankedInputs p DB)
    (hnegativePart_zero :
      ∀ t, 0 < t → t ≤ DB.T → ∀ x : intervalDomainPoint,
        negativePart (conjugatePicardLimit p u₀ DB.T t x) = 0)
    (hcoeff : NeumannLinearDriftCoefficientsRegular DB.T drift react)
    (hsuper :
      IsClassicalNeumannLinearDriftSuperSolution DB.T drift react
        (bformConjugatePicardLift p DB))
    (hu_initial :
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        bformConjugatePicardLift p DB 0 x = intervalDomainLift u₀ x)
    (hcompare :
      NeumannLinearDriftComparisonRegular DB.T drift react (intervalDomainLift u₀)
        (bformConjugatePicardLift p DB))
    (hbarrier_reg :
      NeumannLinearDriftSubSolutionRegularity DB.T drift react
        (squareHeatBarrier M f))
    (hcalc : SquareHeatSubsolutionCalculus DB.T M f drift react)
    (hM : A ^ 2 / 2 + D ≤ M)
    (hB_bound :
      ∀ t x, 0 < t → t < DB.T → x ∈ Set.Ioo (0 : ℝ) 1 →
        |drift t x| ≤ A)
    (hC_neg_bound :
      ∀ t x, 0 < t → t < DB.T → x ∈ Set.Ioo (0 : ℝ) 1 →
        -react t x ≤ D)
    (hseed : SquareHeatSeed (intervalDomainLift u₀) f) :
    BFormNegativePartPositivityRoute p DB :=
  bform_negpart_route_of_square_heat_lower_barrier datum Bbank
    hnegativePart_zero hseed
    (bform_square_heat_hbarrier_of_neumann_linear_drift_square_heat_subsolution_regular
      hcoeff hsuper hu_initial hcompare hbarrier_reg hcalc hM
      hB_bound hC_neg_bound hseed)

end ShenWork.Paper2.BFormPositiveDatumNegPart