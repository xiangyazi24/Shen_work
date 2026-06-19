import ShenWork.PaperOne.WholeLineChemotaxisCrossControl
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

theorem wholeLine_chemotaxis_postIBP_with_derivatives
    (φ φx g gx : ℝ → ℝ)
    (hφ_deriv : ∀ x ∈ tsupport g, HasDerivAt φ (φx x) x)
    (hg_deriv : ∀ x ∈ tsupport φ, HasDerivAt g (gx x) x)
    (hlhs_int : Integrable (fun x : ℝ => φ x * gx x))
    (hrhs_int : Integrable (fun x : ℝ => φx x * g x))
    (hdecay_bot : Tendsto (fun x : ℝ => φ x * g x) atBot (𝓝 0))
    (hdecay_top : Tendsto (fun x : ℝ => φ x * g x) atTop (𝓝 0)) :
    (∫ x : ℝ, φ x * gx x) = -∫ x : ℝ, φx x * g x := by
  have hIBP := MeasureTheory.integral_mul_deriv_eq_deriv_mul
    (A := ℝ) (u := φ) (v := g) (u' := φx) (v' := gx)
    (a' := (0 : ℝ)) (b' := (0 : ℝ))
    hφ_deriv hg_deriv
    (by simpa [Pi.mul_def] using hlhs_int)
    (by simpa [Pi.mul_def] using hrhs_int)
    (by simpa [Pi.mul_def] using hdecay_bot)
    (by simpa [Pi.mul_def] using hdecay_top)
  simpa [Pi.mul_def] using hIBP

theorem wholeLine_chemotaxis_postIBP
    (φ g : ℝ → ℝ)
    (hφ_deriv : ∀ x ∈ tsupport g, HasDerivAt φ (deriv φ x) x)
    (hg_deriv : ∀ x ∈ tsupport φ, HasDerivAt g (deriv g x) x)
    (hlhs_int : Integrable (fun x : ℝ => φ x * deriv g x))
    (hrhs_int : Integrable (fun x : ℝ => deriv φ x * g x))
    (hdecay_bot : Tendsto (fun x : ℝ => φ x * g x) atBot (𝓝 0))
    (hdecay_top : Tendsto (fun x : ℝ => φ x * g x) atTop (𝓝 0)) :
    (∫ x : ℝ, φ x * deriv g x) = -∫ x : ℝ, deriv φ x * g x := by
  exact wholeLine_chemotaxis_postIBP_with_derivatives φ (deriv φ) g (deriv g)
    hφ_deriv hg_deriv hlhs_int hrhs_int hdecay_bot hdecay_top

theorem wholeLineUpperBarrier_chemotaxis_postIBP_field
    (p : CMParams) {T : ℝ} {U V : ℝ → ℝ → ℝ} {hi : ℝ} (flux : ℝ → ℝ → ℝ)
    (hφ_deriv : ∀ t, 0 < t → t < T → ∀ x ∈ tsupport
        (wholeLineChemotaxisWeight p (U t) (fun y : ℝ => deriv (V t) y)),
        HasDerivAt (wholeLineUpperBarrierTest U hi t) (-(flux t x)) x)
    (hweight_deriv : ∀ t, 0 < t → t < T → ∀ x ∈ tsupport
        (wholeLineUpperBarrierTest U hi t),
        HasDerivAt
          (wholeLineChemotaxisWeight p (U t) (fun y : ℝ => deriv (V t) y))
          (deriv (wholeLineChemotaxisWeight p (U t) (fun y : ℝ => deriv (V t) y)) x) x)
    (hlhs_int : ∀ t, 0 < t → t < T → Integrable (fun x : ℝ =>
      wholeLineUpperBarrierTest U hi t x *
        deriv (wholeLineChemotaxisWeight p (U t) (fun y : ℝ => deriv (V t) y)) x))
    (hflux_int : ∀ t, 0 < t → t < T → Integrable (fun x : ℝ =>
      flux t x * wholeLineChemotaxisWeight p (U t) (fun y : ℝ => deriv (V t) y) x))
    (hdecay_bot : ∀ t, 0 < t → t < T → Tendsto (fun x : ℝ =>
      wholeLineUpperBarrierTest U hi t x *
        wholeLineChemotaxisWeight p (U t) (fun y : ℝ => deriv (V t) y) x) atBot (𝓝 0))
    (hdecay_top : ∀ t, 0 < t → t < T → Tendsto (fun x : ℝ =>
      wholeLineUpperBarrierTest U hi t x *
        wholeLineChemotaxisWeight p (U t) (fun y : ℝ => deriv (V t) y) x) atTop (𝓝 0)) :
    ∀ t, 0 < t → t < T →
      wholeLineUpperBarrierChemotaxisTerm p U V hi t =
        ∫ x : ℝ, flux t x *
          wholeLineChemotaxisWeight p (U t) (fun y : ℝ => deriv (V t) y) x := by
  intro t ht0 htT
  let φ := wholeLineUpperBarrierTest U hi t
  let g := wholeLineChemotaxisWeight p (U t) (fun y : ℝ => deriv (V t) y)
  have hneg_int : Integrable (fun x : ℝ => (-(flux t x)) * g x) := by
    simpa [g, neg_mul] using (hflux_int t ht0 htT).neg
  have hIBP := wholeLine_chemotaxis_postIBP_with_derivatives φ (fun x : ℝ => -(flux t x)) g
    (fun x : ℝ => deriv g x) (hφ_deriv t ht0 htT) (hweight_deriv t ht0 htT)
    (hlhs_int t ht0 htT) hneg_int (hdecay_bot t ht0 htT) (hdecay_top t ht0 htT)
  calc
    wholeLineUpperBarrierChemotaxisTerm p U V hi t
        = ∫ x : ℝ, φ x * deriv g x := by
          rfl
    _ = -∫ x : ℝ, (-(flux t x)) * g x := hIBP
    _ = ∫ x : ℝ, flux t x *
        wholeLineChemotaxisWeight p (U t) (fun y : ℝ => deriv (V t) y) x := by
          rw [← integral_neg]
          simp [g, neg_mul]

#print axioms wholeLine_chemotaxis_postIBP_with_derivatives
#print axioms wholeLine_chemotaxis_postIBP
#print axioms wholeLineUpperBarrier_chemotaxis_postIBP_field

end ShenWork.PaperOne
