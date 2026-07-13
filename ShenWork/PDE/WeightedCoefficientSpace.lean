/- Weighted cosine coefficients realized in Mathlib's complete `ell^2` space. -/
import ShenWork.PDE.FractionalPowerSpace
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace ShenWork.PDE

open FractionalPower
open MeasureTheory
open Filter
open scoped ENNReal

noncomputable section

/-- The ambient complete Hilbert sequence space used for Bochner-Duhamel
integration. -/
abbrev CoeffL2 := lp (fun _ : ℕ => ℂ) 2

/-- Multiplication by the square root of the fractional-power energy weight. -/
def weightedCoeffSequence (L sigma : ℝ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  ((1 + neumannEigenvalue L n) ^ sigma : ℝ) * a n

theorem weightedCoeffSequence_norm_sq
    (L sigma : ℝ) (a : ℕ → ℂ) (n : ℕ) :
    ‖weightedCoeffSequence L sigma a n‖ ^ 2 =
      fractionalPowerEnergyTerm L sigma a n := by
  have hbase : 0 < 1 + neumannEigenvalue L n :=
    one_add_neumannEigenvalue_pos L n
  simp only [weightedCoeffSequence, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hbase sigma)]
  unfold fractionalPowerEnergyTerm fractionalPowerWeight
  rw [mul_pow]
  congr 1
  rw [show 2 * sigma = sigma * 2 by ring, Real.rpow_mul hbase.le]
  simp [pow_two]

/-- A weighted-energy coefficient family as an element of complete `ell^2`. -/
def weightedCoeffToLp
    (L sigma : ℝ) (a : ℕ → ℂ)
    (ha : Summable fun n : ℕ => fractionalPowerEnergyTerm L sigma a n) :
    CoeffL2 :=
  ⟨weightedCoeffSequence L sigma a, by
    apply memℓp_gen
    simpa [weightedCoeffSequence_norm_sq] using ha⟩

@[simp] theorem weightedCoeffToLp_apply
    (L sigma : ℝ) (a : ℕ → ℂ)
    (ha : Summable fun n : ℕ => fractionalPowerEnergyTerm L sigma a n)
    (n : ℕ) :
    weightedCoeffToLp L sigma a ha n = weightedCoeffSequence L sigma a n :=
  rfl

/-- Its sequence norm is exactly the square root of the weighted energy. -/
theorem norm_weightedCoeffToLp
    (L sigma : ℝ) (a : ℕ → ℂ)
    (ha : Summable fun n : ℕ => fractionalPowerEnergyTerm L sigma a n) :
    ‖weightedCoeffToLp L sigma a ha‖ =
      Real.sqrt (∑' n : ℕ, fractionalPowerEnergyTerm L sigma a n) := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp only [show (2 : ℝ≥0∞).toReal = 2 by norm_num, Real.rpow_two]
  rw [show (∑' n : ℕ, ‖weightedCoeffToLp L sigma a ha n‖ ^ 2) =
      ∑' n : ℕ, fractionalPowerEnergyTerm L sigma a n by
    apply tsum_congr
    intro n
    exact weightedCoeffSequence_norm_sq L sigma a n]
  exact (Real.sqrt_eq_rpow _).symm

/-- Coordinate evaluation on `ell^2`, as a real continuous linear map for
Bochner integration over real time. -/
def coeffL2EvalCLM (n : ℕ) : CoeffL2 →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun a => a n
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun a => by
      simpa using lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) a n)

@[simp] theorem coeffL2EvalCLM_apply (n : ℕ) (a : CoeffL2) :
    coeffL2EvalCLM n a = a n := rfl

/-- A coefficient family with measurable coordinates is strongly measurable
as an `ell^2`-valued map.  The proof uses the canonical finite-support
approximations, avoiding any hidden product-Borel assertion. -/
theorem stronglyMeasurable_weightedCoeffToLp
    {X : Type*} [MeasurableSpace X]
    (L sigma : ℝ) (a : X → ℕ → ℂ)
    (ha : ∀ x, Summable fun n : ℕ =>
      fractionalPowerEnergyTerm L sigma (a x) n)
    (hmeas : ∀ n, StronglyMeasurable
      (fun x => weightedCoeffSequence L sigma (a x) n)) :
    StronglyMeasurable (fun x => weightedCoeffToLp L sigma (a x) (ha x)) := by
  let target : X → CoeffL2 := fun x =>
    weightedCoeffToLp L sigma (a x) (ha x)
  let approx : ℕ → X → CoeffL2 := fun N x =>
    Finset.sum (Finset.range N) (fun n =>
      lp.single (E := fun _ : ℕ => ℂ) 2 n
        (weightedCoeffSequence L sigma (a x) n))
  have happ : ∀ N, StronglyMeasurable (approx N) := by
    intro N
    let term : ℕ → X → CoeffL2 := fun n x =>
      lp.single (E := fun _ : ℕ => ℂ) 2 n
        (weightedCoeffSequence L sigma (a x) n)
    have hterm : ∀ n, StronglyMeasurable (term n) := by
      intro n
      exact (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 2 n).continuous.comp_stronglyMeasurable
        (hmeas n)
    have hsum := Finset.stronglyMeasurable_fun_sum
      (f := term) (Finset.range N) (fun n _hn => hterm n)
    simpa [approx, term] using hsum
  apply stronglyMeasurable_of_tendsto atTop happ
  apply tendsto_pi_nhds.2
  intro x
  have hsum := lp.hasSum_single (E := fun _ : ℕ => ℂ)
    (p := (2 : ℝ≥0∞)) (by norm_num) (target x)
  simpa [approx, target] using hsum.tendsto_sum_nat

theorem aestronglyMeasurable_weightedCoeffToLp
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (L sigma : ℝ) (a : X → ℕ → ℂ)
    (ha : ∀ x, Summable fun n : ℕ =>
      fractionalPowerEnergyTerm L sigma (a x) n)
    (hmeas : ∀ n, StronglyMeasurable
      (fun x => weightedCoeffSequence L sigma (a x) n)) :
    AEStronglyMeasurable
      (fun x => weightedCoeffToLp L sigma (a x) (ha x)) μ :=
  (stronglyMeasurable_weightedCoeffToLp L sigma a ha hmeas).aestronglyMeasurable

/-- Coordinate extraction commutes with an `ell^2`-valued interval integral. -/
theorem coeffL2_intervalIntegral_apply
    {f : ℝ → CoeffL2} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) (n : ℕ) :
    (∫ s in a..b, f s ∂volume) n = ∫ s in a..b, f s n ∂volume := by
  have hcomm := (coeffL2EvalCLM n).intervalIntegral_comp_comm hf
  simpa using hcomm.symm

#print axioms weightedCoeffSequence_norm_sq
#print axioms norm_weightedCoeffToLp
#print axioms stronglyMeasurable_weightedCoeffToLp
#print axioms coeffL2_intervalIntegral_apply

end

end ShenWork.PDE
