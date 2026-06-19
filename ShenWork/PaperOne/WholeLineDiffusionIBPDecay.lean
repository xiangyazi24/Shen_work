/-
  ShenWork/PaperOne/WholeLineDiffusionIBPDecay.lean

  Whole-line diffusion integration by parts with decay:

    ∫ φ · φ_xx = - ∫ (φ_x)^2.

  The minimal boundary hypothesis used here is the one actually needed by the
  improper whole-line IBP: the product `φ * φ_x` tends to zero at both ends.
  Compact support, or separate decay assumptions strong enough to imply
  `φ * φ_x → 0`, are sufficient but not part of the theorem statement.

  No `sorry`/`admit`/custom `axiom`.
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

/-- Generic whole-line IBP with explicitly supplied first and second derivative
fields.  The derivative assumptions are only required on the topological support
needed by Mathlib's improper IBP theorem. -/
theorem wholeLine_diffusion_ibp_decay_with_derivatives
    (φ φx φxx : ℝ → ℝ)
    (hφ_deriv : ∀ x ∈ tsupport φx, HasDerivAt φ (φx x) x)
    (hφx_deriv : ∀ x ∈ tsupport φ, HasDerivAt φx (φxx x) x)
    (h_lhs_int : Integrable (fun x : ℝ => φ x * φxx x))
    (h_energy_int : Integrable (fun x : ℝ => φx x * φx x))
    (h_decay_bot : Tendsto (fun x : ℝ => φ x * φx x) atBot (𝓝 0))
    (h_decay_top : Tendsto (fun x : ℝ => φ x * φx x) atTop (𝓝 0)) :
    (∫ x : ℝ, φ x * φxx x) = -∫ x : ℝ, φx x * φx x := by
  have hIBP := MeasureTheory.integral_mul_deriv_eq_deriv_mul
    (A := ℝ) (u := φ) (v := φx) (u' := φx) (v' := φxx)
    (a' := (0 : ℝ)) (b' := (0 : ℝ))
    hφ_deriv hφx_deriv
    (by simpa [Pi.mul_def] using h_lhs_int)
    (by simpa [Pi.mul_def] using h_energy_int)
    (by simpa [Pi.mul_def] using h_decay_bot)
    (by simpa [Pi.mul_def] using h_decay_top)
  simpa [Pi.mul_def] using hIBP

/-- Whole-line diffusion IBP in the usual `deriv`/`iteratedDeriv 2` notation:
`∫ φ · φ_xx = -∫ (φ_x)^2`, with boundary killed by
`φ * φ_x → 0` at `±∞`. -/
theorem wholeLine_diffusion_ibp_decay
    (φ : ℝ → ℝ)
    (hφ_deriv : ∀ x ∈ tsupport (deriv φ), HasDerivAt φ (deriv φ x) x)
    (hφx_deriv :
      ∀ x ∈ tsupport φ, HasDerivAt (deriv φ) (iteratedDeriv 2 φ x) x)
    (h_lhs_int : Integrable (fun x : ℝ => φ x * iteratedDeriv 2 φ x))
    (h_energy_int : Integrable (fun x : ℝ => deriv φ x * deriv φ x))
    (h_decay_bot : Tendsto (fun x : ℝ => φ x * deriv φ x) atBot (𝓝 0))
    (h_decay_top : Tendsto (fun x : ℝ => φ x * deriv φ x) atTop (𝓝 0)) :
    (∫ x : ℝ, φ x * iteratedDeriv 2 φ x) =
      -∫ x : ℝ, deriv φ x * deriv φ x := by
  exact wholeLine_diffusion_ibp_decay_with_derivatives
    φ (deriv φ) (iteratedDeriv 2 φ)
    hφ_deriv hφx_deriv h_lhs_int h_energy_int h_decay_bot h_decay_top

/-- The diffusion term is nonpositive once the whole-line IBP hypotheses hold. -/
theorem wholeLine_diffusion_ibp_decay_nonpos
    (φ : ℝ → ℝ)
    (hφ_deriv : ∀ x ∈ tsupport (deriv φ), HasDerivAt φ (deriv φ x) x)
    (hφx_deriv :
      ∀ x ∈ tsupport φ, HasDerivAt (deriv φ) (iteratedDeriv 2 φ x) x)
    (h_lhs_int : Integrable (fun x : ℝ => φ x * iteratedDeriv 2 φ x))
    (h_energy_int : Integrable (fun x : ℝ => deriv φ x * deriv φ x))
    (h_decay_bot : Tendsto (fun x : ℝ => φ x * deriv φ x) atBot (𝓝 0))
    (h_decay_top : Tendsto (fun x : ℝ => φ x * deriv φ x) atTop (𝓝 0)) :
    (∫ x : ℝ, φ x * iteratedDeriv 2 φ x) ≤ 0 := by
  rw [wholeLine_diffusion_ibp_decay φ hφ_deriv hφx_deriv h_lhs_int
    h_energy_int h_decay_bot h_decay_top]
  exact neg_nonpos.mpr (integral_nonneg fun x => mul_self_nonneg (deriv φ x))

#print axioms wholeLine_diffusion_ibp_decay
#print axioms wholeLine_diffusion_ibp_decay_nonpos

end ShenWork.PaperOne
