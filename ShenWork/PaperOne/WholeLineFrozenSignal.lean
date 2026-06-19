import ShenWork.PaperOne.WholeLineResolvent
open MeasureTheory Filter Topology
noncomputable section
namespace ShenWork.PaperOne
def frozenSignal (γ : ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  wholeLineResolvent (fun y => (u y) ^ γ)
private theorem frozenSignal_source_cont {γ : ℝ} (hγ : 1 ≤ γ) {u : ℝ → ℝ}
    (hu_cont : Continuous u) : Continuous (fun y => (u y) ^ γ) :=
  (Real.continuous_rpow_const (by linarith [hγ])).comp hu_cont
private theorem frozenSignal_source_abs_le_one {γ : ℝ} (hγ : 1 ≤ γ) {u : ℝ → ℝ}
    (hu_nonneg : ∀ x, 0 ≤ u x) (hu_le_one : ∀ x, u x ≤ 1) :
    ∀ y, |(u y) ^ γ| ≤ 1 := by
  intro y
  rw [abs_of_nonneg (Real.rpow_nonneg (hu_nonneg y) γ)]
  exact Real.rpow_le_one (hu_nonneg y) (hu_le_one y) (by linarith [hγ] : 0 ≤ γ)
theorem frozenSignal_nonneg {γ : ℝ} {u : ℝ → ℝ}
    (hu_nonneg : ∀ x, 0 ≤ u x) (x : ℝ) : 0 ≤ frozenSignal γ u x := by
  exact wholeLineResolvent_nonneg (fun y => Real.rpow_nonneg (hu_nonneg y) γ) x
theorem frozenSignal_le_one {γ : ℝ} (hγ : 1 ≤ γ) {u : ℝ → ℝ}
    (hu_cont : Continuous u) (hu_nonneg : ∀ x, 0 ≤ u x)
    (hu_le_one : ∀ x, u x ≤ 1) (x : ℝ) : frozenSignal γ u x ≤ 1 := by
  exact (le_abs_self (frozenSignal γ u x)).trans (by
    simpa [frozenSignal] using
      (wholeLineResolvent_sup_le (f := fun y => (u y) ^ γ) (M := 1) (by norm_num)
        (frozenSignal_source_cont hγ hu_cont)
        (frozenSignal_source_abs_le_one hγ hu_nonneg hu_le_one) x))
theorem frozenSignal_grad_bound {γ : ℝ} (hγ : 1 ≤ γ) {u : ℝ → ℝ}
    (hu_cont : Continuous u) (hu_nonneg : ∀ x, 0 ≤ u x)
    (hu_le_one : ∀ x, u x ≤ 1) (x : ℝ) :
    |deriv (frozenSignal γ u) x| ≤ 1 := by
  simpa [frozenSignal] using
    (wholeLineResolventDeriv_sup_le (f := fun y => (u y) ^ γ) (M := 1) (by norm_num)
      (frozenSignal_source_cont hγ hu_cont)
      (frozenSignal_source_abs_le_one hγ hu_nonneg hu_le_one) x)
private theorem frozenSignal_source_antitone {γ : ℝ} (hγ : 1 ≤ γ) {u : ℝ → ℝ}
    (hu_nonneg : ∀ x, 0 ≤ u x) (hu_anti : Antitone u) :
    Antitone (fun y => (u y) ^ γ) := by
  intro a b hab
  exact Real.rpow_le_rpow (hu_nonneg b) (hu_anti hab) (by linarith [hγ] : 0 ≤ γ)
private theorem frozenSignal_eq_translated_integral (γ : ℝ) (u : ℝ → ℝ) (x : ℝ) :
    frozenSignal γ u x =
      (1 / 2 : ℝ) * ∫ t : ℝ, Real.exp (-|t|) * (u (x + t)) ^ γ := by
  calc
    frozenSignal γ u x =
        (1 / 2 : ℝ) * ∫ y : ℝ, Real.exp (-|x - y|) * (u y) ^ γ := by
      rw [frozenSignal, wholeLineResolvent_eq_Psi]
      simp [Psi, Real.sqrt_one]
    _ = (1 / 2 : ℝ) * ∫ t : ℝ, Real.exp (-|t|) * (u (x + t)) ^ γ := by
      congr 1
      have htrans := integral_add_left_eq_self (μ := (volume : Measure ℝ))
        (fun y : ℝ => Real.exp (-|x - y|) * (u y) ^ γ) x
      rw [← htrans]
      exact integral_congr_ae (Eventually.of_forall fun t => by simp)
private theorem frozenSignal_translated_integrand_integrable {γ : ℝ} (hγ : 1 ≤ γ)
    {u : ℝ → ℝ} (hu_cont : Continuous u) (hu_nonneg : ∀ x, 0 ≤ u x)
    (hu_le_one : ∀ x, u x ≤ 1) (x : ℝ) :
    Integrable (fun t : ℝ => Real.exp (-|t|) * (u (x + t)) ^ γ) := by
  have hbase : Integrable (fun y : ℝ => Real.exp (-|x - y|) * (u y) ^ γ) := by
    simpa [Real.sqrt_one] using
      (psi_kernel_mul_bounded_integrable one_pos (by norm_num : (0 : ℝ) ≤ 1)
        (frozenSignal_source_abs_le_one hγ hu_nonneg hu_le_one) x
        (frozenSignal_source_cont hγ hu_cont).aestronglyMeasurable)
  have hshift : Integrable (fun t : ℝ => Real.exp (-|x - (x + t)|) * (u (x + t)) ^ γ) :=
    (measurePreserving_add_left (μ := (volume : Measure ℝ)) x).integrable_comp_emb
      (MeasurableEquiv.addLeft x).measurableEmbedding |>.mpr hbase
  exact hshift.congr (Eventually.of_forall fun t => by simp)
theorem frozenSignal_antitone_of_monotone {γ : ℝ} (hγ : 1 ≤ γ) {u : ℝ → ℝ}
    (hu_cont : Continuous u) (hu_nonneg : ∀ x, 0 ≤ u x)
    (hu_le_one : ∀ x, u x ≤ 1) (hu_anti : Antitone u) :
    Antitone (frozenSignal γ u) := by
  have hsource := frozenSignal_source_antitone hγ hu_nonneg hu_anti
  intro x₁ x₂ hx
  rw [frozenSignal_eq_translated_integral, frozenSignal_eq_translated_integral]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  apply integral_mono
  · exact frozenSignal_translated_integrand_integrable hγ hu_cont hu_nonneg hu_le_one x₂
  · exact frozenSignal_translated_integrand_integrable hγ hu_cont hu_nonneg hu_le_one x₁
  intro t
  exact mul_le_mul_of_nonneg_left
    (hsource (by linarith : x₁ + t ≤ x₂ + t)) (Real.exp_nonneg _)
theorem frozenSignal_grad_nonpos_of_monotone {γ : ℝ} (hγ : 1 ≤ γ) {u : ℝ → ℝ}
    (hu_cont : Continuous u) (hu_nonneg : ∀ x, 0 ≤ u x)
    (hu_le_one : ∀ x, u x ≤ 1) (hu_anti : Antitone u) (x : ℝ) :
    deriv (frozenSignal γ u) x ≤ 0 :=
  (frozenSignal_antitone_of_monotone hγ hu_cont hu_nonneg hu_le_one hu_anti).deriv_nonpos
#print axioms frozenSignal_nonneg
#print axioms frozenSignal_le_one
#print axioms frozenSignal_grad_bound
#print axioms frozenSignal_antitone_of_monotone
#print axioms frozenSignal_grad_nonpos_of_monotone
end ShenWork.PaperOne
