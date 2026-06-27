noncomputable def localRestartCoeff
    (a₀ : ℕ → ℝ) (a : ℝ → ℕ → ℝ) (τ : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n +
    duhamelSpectralCoeff a τ n
```
```lean
noncomputable def duhamelSpectralCoeff (a : ℝ → ℕ → ℝ) (t : ℝ) (n : ℕ) : ℝ :=
  ∫ s in (0:ℝ)..t, Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * a s n
```
```lean
import ShenWork.PDE.IntervalSourceCoefficientTimeC1
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic

open MeasureTheory intervalIntegral

noncomputable section

namespace ShenWork.Paper2.RestartVariationOfConstants

open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)

/-- Variation of constants for one local restart coefficient.

For a fixed mode `n`, let `λ = unitIntervalCosineEigenvalue n`.  If
`c` is `C¹` in the concrete Lean-friendly sense that every derivative
`deriv c t` is realised by `HasDerivAt` and `deriv c` is continuous, then
restarting from `c η` and forcing with

`ρ ↦ deriv c (η + ρ) + λ * c (η + ρ)`

recovers the shifted coefficient `ρ ↦ c (η + ρ)`.

The proof applies the interval FTC to
`F s = exp (-(ρ - s) * λ) * c (η + s)`.  This avoids division by `λ`, so
it includes the zero mode. -/
theorem localRestartCoeff_variation_of_constants
    {c : ℝ → ℝ}
    (hc_deriv : ∀ t : ℝ, HasDerivAt c (deriv c t) t)
    (hc_deriv_cont : Continuous (fun t : ℝ => deriv c t))
    (η ρ : ℝ) (hρ : 0 ≤ ρ) (n : ℕ) :
    localRestartCoeff
      (fun _ : ℕ => c η)
      (fun s _ : ℕ =>
        deriv c (η + s) + unitIntervalCosineEigenvalue n * c (η + s))
      ρ n = c (η + ρ) := by
  set lam : ℝ := unitIntervalCosineEigenvalue n
  set F : ℝ → ℝ := fun s => Real.exp (-(ρ - s) * lam) * c (η + s)

  have hc_cont : Continuous c :=
    continuous_iff_continuousAt.2 (fun t => (hc_deriv t).continuousAt)

  have hF_cont : ContinuousOn F (Set.Icc (0 : ℝ) ρ) := by
    have hF_cont_global : Continuous F := by
      dsimp [F]
      exact (Real.continuous_exp.comp (by fun_prop)).mul
        (hc_cont.comp (continuous_const.add continuous_id))
    exact hF_cont_global.continuousOn

  have hintegrand_cont : Continuous (fun s : ℝ =>
      Real.exp (-(ρ - s) * lam) *
        (deriv c (η + s) + lam * c (η + s))) := by
    have hk : Continuous (fun s : ℝ => Real.exp (-(ρ - s) * lam)) := by
      fun_prop
    have hdc : Continuous (fun s : ℝ => deriv c (η + s)) :=
      hc_deriv_cont.comp (continuous_const.add continuous_id)
    have hcs : Continuous (fun s : ℝ => c (η + s)) :=
      hc_cont.comp (continuous_const.add continuous_id)
    exact hk.mul (hdc.add (continuous_const.mul hcs))

  have hintegrand_int : IntervalIntegrable (fun s : ℝ =>
      Real.exp (-(ρ - s) * lam) *
        (deriv c (η + s) + lam * c (η + s))) volume (0 : ℝ) ρ :=
    hintegrand_cont.intervalIntegrable 0 ρ

  have hF_deriv : ∀ s ∈ Set.Ioo (0 : ℝ) ρ,
      HasDerivAt F
        (Real.exp (-(ρ - s) * lam) *
          (deriv c (η + s) + lam * c (η + s))) s := by
    intro s _hs
    have hkernel_arg : HasDerivAt (fun u : ℝ => -(ρ - u) * lam) lam s := by
      have hsub : HasDerivAt (fun u : ℝ => ρ - u) (-1 : ℝ) s := by
        simpa using (hasDerivAt_const s ρ).sub (hasDerivAt_id s)
      have hneg : HasDerivAt (fun u : ℝ => -(ρ - u)) (1 : ℝ) s := by
        simpa using hsub.neg
      simpa using hneg.mul_const lam
    have hkernel : HasDerivAt (fun u : ℝ => Real.exp (-(ρ - u) * lam))
        (Real.exp (-(ρ - s) * lam) * lam) s :=
      hkernel_arg.exp
    have hshift : HasDerivAt (fun u : ℝ => η + u) (1 : ℝ) s := by
      simpa using (hasDerivAt_const s η).add (hasDerivAt_id s)
    have hc_shift : HasDerivAt (fun u : ℝ => c (η + u))
        (deriv c (η + s)) s := by
      simpa using (hc_deriv (η + s)).comp s hshift
    have hprod := hkernel.mul hc_shift
    convert hprod using 1 <;> ring

  have hFTC :
      (∫ s in (0 : ℝ)..ρ,
        Real.exp (-(ρ - s) * lam) *
          (deriv c (η + s) + lam * c (η + s))) =
        F ρ - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (a := (0 : ℝ)) (b := ρ)
      (f := F)
      (f' := fun s : ℝ =>
        Real.exp (-(ρ - s) * lam) *
          (deriv c (η + s) + lam * c (η + s)))
      hρ hF_cont hF_deriv hintegrand_int

  have hIntegral :
      (∫ s in (0 : ℝ)..ρ,
        Real.exp (-(ρ - s) * lam) *
          (deriv c (η + s) + lam * c (η + s))) =
        c (η + ρ) - Real.exp (-ρ * lam) * c η := by
    rw [hFTC]
    simp [F]
    ring

  unfold localRestartCoeff duhamelSpectralCoeff
  change Real.exp (-ρ * lam) * c η +
      (∫ s in (0 : ℝ)..ρ,
        Real.exp (-(ρ - s) * lam) *
          (deriv c (η + s) + lam * c (η + s))) =
      c (η + ρ)
  rw [hIntegral]
  ring

end ShenWork.Paper2.RestartVariationOfConstants
```
```lean
(hc_deriv : ∀ t : ℝ, HasDerivAt c (deriv c t) t)
(hc_deriv_cont : Continuous (fun t : ℝ => deriv c t))
```
```lean
fun s _ : ℕ => deriv c (η + s) + unitIntervalCosineEigenvalue n * c (η + s)
