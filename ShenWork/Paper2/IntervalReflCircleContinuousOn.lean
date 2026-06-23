/-
# `reflCircle` continuity and Fourier ℓ¹ from `ContinuousOn f [0,1]` (NOT `Continuous f` on ℝ)

FAITHFULNESS FIX (§3.3 vacuity).  The χ₀<0 CarrySeam currently demands
`hu_cont : Continuous (intervalDomainLift (u τ))` on ALL of ℝ.  But
`intervalDomainLift` is the ZERO-extension, and for a strictly-positive conj-mild
slice it is DISCONTINUOUS at the boundary (`IntervalDomainConstantEquilibriumWitness`).
So that hypothesis is UNSATISFIABLE for the actual solution, making the headline
vacuously conditional.

`reflCircle f = AddCircle.liftIoc 2 (-1) (reflC f)` with `reflC f = fun x => (f |x| : ℂ)`,
so it reads `f` ONLY through `|x|`, i.e. only on `[0,1]`.  Hence its continuity, and
the whole Fourier-ℓ¹ chain it feeds, need only `ContinuousOn f (Set.Icc 0 1)`, which
the conj-mild slice GENUINELY satisfies (`HasContinuousSlices`).

This file provides the `ContinuousOn`-based building blocks:
* `reflCircle_continuous_of_continuousOn`,
* `reflCircle_eq_of_eqOn_Icc`,
* the cosine-coefficient chain (`fco`/`cosineCoeffs`/realness) in `ContinuousOn` form,
* `fourierCoeff_reflCircle_summable_of_cosineCoeff_abs_continuousOn`.

No `sorry`/`admit`/`native_decide`/custom axiom.
-/
import ShenWork.PDE.IntervalCosineInversion

open MeasureTheory Complex
open ShenWork.CosineParsevalBridge
open ShenWork.HeatKernelGradientEstimates
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalCosineInversion
open scoped Real

namespace ShenWork.Paper2.IntervalReflCircleContinuousOn

noncomputable section

local notation "fco" => fourierCoeffOn (show (-1 : ℝ) < 1 by norm_num)

/-! ## 0. The integrability that the cosine chain actually needs. -/

/-- `ContinuousOn f [0,1]` gives the interval-integrability the cosine coefficients use. -/
theorem ofReal_intervalIntegrable_of_continuousOn
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1)) :
    IntervalIntegrable (fun x => (f x : ℂ)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact Complex.continuous_ofReal.comp_continuousOn hf

/-! ## 1. `reflCircle` continuity from `ContinuousOn f [0,1]`. -/

/-- The even-reflection circle map is continuous from `ContinuousOn f [0,1]` alone:
the reflection folds `[-1,1] → [0,1]` via `|·|`, needing no continuity off `[0,1]`. -/
theorem reflCircle_continuous_of_continuousOn
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1)) :
    Continuous (reflCircle f) := by
  apply AddCircle.liftIoc_continuous
  · show reflC f (-1) = reflC f (-1 + 2)
    simp only [reflC, unitIntervalEvenReflection]; norm_num
  · have hmaps : Set.MapsTo (fun x : ℝ => |x|) (Set.Icc (-1 : ℝ) (-1 + 2))
        (Set.Icc 0 1) := by
      intro x hx
      simp only [Set.mem_Icc] at hx ⊢
      refine ⟨abs_nonneg x, ?_⟩
      rw [abs_le]; constructor <;> [linarith [hx.1]; linarith [hx.2]]
    have habs : ContinuousOn (fun x : ℝ => |x|) (Set.Icc (-1 : ℝ) (-1 + 2)) :=
      continuous_abs.continuousOn
    show ContinuousOn (unitIntervalEvenReflection (fun x => (f x : ℂ)))
      (Set.Icc (-1 : ℝ) (-1 + 2))
    exact (Complex.continuous_ofReal.comp_continuousOn hf).comp habs hmaps

/-! ## 2. `reflCircle` reads only `[0,1]`: agreement transfer. -/

/-- If `f = g` on `[0,1]` then `reflCircle f = reflCircle g` — the lift evaluates the
even reflection only on the fundamental domain `Ioc (-1) 1`, where `|·| ∈ [0,1]`. -/
theorem reflCircle_eq_of_eqOn_Icc {f g : ℝ → ℝ}
    (h : Set.EqOn f g (Set.Icc 0 1)) : reflCircle f = reflCircle g := by
  funext z
  simp only [reflCircle, AddCircle.liftIoc, Function.comp_apply, Set.restrict_apply]
  set y : ℝ := ((AddCircle.equivIoc (2 : ℝ) (-1) z : Set.Ioc (-1 : ℝ) (-1 + 2)) : ℝ)
    with hy
  have hmem : y ∈ Set.Ioc (-1 : ℝ) (-1 + 2) := (AddCircle.equivIoc (2 : ℝ) (-1) z).2
  have hyabs : |y| ∈ Set.Icc (0 : ℝ) 1 := by
    simp only [Set.mem_Ioc] at hmem
    refine Set.mem_Icc.mpr ⟨abs_nonneg y, ?_⟩
    rw [abs_le]; constructor <;> [linarith [hmem.1]; linarith [hmem.2]]
  simp only [reflC, unitIntervalEvenReflection]
  rw [h hyabs]

/-! ## 3. The cosine-coefficient chain in `ContinuousOn` form. -/

/-- `fco (reflC f) n = ∫₀¹ cos(nπx) f(x) dx` from `ContinuousOn f [0,1]`. -/
theorem fco_eq_raw_continuousOn {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    (n : ℤ) :
    fco (reflC f) n =
      ∫ x in (0 : ℝ)..1, (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * (f x : ℂ) :=
  unitIntervalEvenReflection_fourierCoeffOn_eq_cosineCoeff
    (ofReal_intervalIntegrable_of_continuousOn hf) n

/-- The cosine integral is real-valued (cast form). -/
theorem fco_eq_ofReal_continuousOn {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 1)) (n : ℤ) :
    fco (reflC f) n =
      ((∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * f x : ℝ) : ℂ) := by
  rw [fco_eq_raw_continuousOn hf n, ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro x _hx; push_cast; ring

/-- `cosineCoeffs f n` as the real part of the circle coefficient. -/
theorem cosineCoeffs_eq_continuousOn {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 1)) (n : ℕ) :
    cosineCoeffs f n =
      (if n = 0 then (1 : ℝ) else 2) * (fco (reflC f) (n : ℤ)).re := by
  rw [cosineCoeffs, unitIntervalNeumannCosineCoeff]
  have hre : (fco (reflC f) (n : ℤ)).re =
      (unitIntervalCosineRawCoeff (fun x => (f x : ℂ)) n).re := by
    rw [fco_eq_raw_continuousOn hf, unitIntervalCosineRawCoeff]; norm_cast
  rcases eq_or_ne n 0 with h | h
  · subst h; rw [hre]; simp
  · simp only [if_neg h]; rw [hre]

/-- Evenness of the circle coefficient in the frequency, `ContinuousOn` form. -/
theorem fco_neg_continuousOn {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    (n : ℤ) : fco (reflC f) (-n) = fco (reflC f) n := by
  rw [fco_eq_raw_continuousOn hf, fco_eq_raw_continuousOn hf]
  apply intervalIntegral.integral_congr
  intro x _hx
  have hcos : ((-n : ℤ) : ℝ) * Real.pi * x = -((n : ℝ) * Real.pi * x) := by
    push_cast; ring
  simp only []; rw [hcos, Real.cos_neg]

/-- Realness of the Fourier coefficient, `ContinuousOn` form. -/
theorem fourierCoeff_ofReal_re_continuousOn {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 1)) (n : ℤ) :
    (((fourierCoeff (reflCircle f) n).re : ℝ) : ℂ) = fourierCoeff (reflCircle f) n := by
  rw [fourierCoeff_reflCircle, fco_eq_ofReal_continuousOn hf]; simp

/-! ## 4. Fourier ℓ¹ summability from `ContinuousOn f [0,1]`. -/

/-- **`hu_sum`/`hwfac_sum` from a SATISFIABLE hypothesis.**  ℓ¹-summability of the
`reflCircle` Fourier coefficients follows from `ContinuousOn f [0,1]` (genuine for
the conj-mild slice) plus absolute summability of the cosine coefficients — no
continuity of the discontinuous lift is required. -/
theorem fourierCoeff_reflCircle_summable_of_cosineCoeff_abs_continuousOn
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    (hcos : Summable (fun n : ℕ => |cosineCoeffs f n|)) :
    Summable (fun n : ℤ => fourierCoeff (reflCircle f) n) := by
  classical
  have hbnd : ∀ n : ℕ,
      ‖fourierCoeff (reflCircle f) (n : ℤ)‖ ≤ |cosineCoeffs f n| := by
    intro n
    have hre : ‖fourierCoeff (reflCircle f) (n : ℤ)‖
        = |(fourierCoeff (reflCircle f) (n : ℤ)).re| := by
      rw [← fourierCoeff_ofReal_re_continuousOn hf (n : ℤ), Complex.norm_real,
        Real.norm_eq_abs, Complex.ofReal_re]
    have hcoeff : cosineCoeffs f n
        = (if n = 0 then (1 : ℝ) else 2)
            * (fourierCoeff (reflCircle f) (n : ℤ)).re := by
      rw [cosineCoeffs_eq_continuousOn hf n, fourierCoeff_reflCircle]
    rw [hre, hcoeff, abs_mul]
    have hfac : (1 : ℝ) ≤ |(if n = 0 then (1 : ℝ) else 2)| := by
      rcases eq_or_ne n 0 with h | h <;> simp [h]
    nlinarith [hfac, abs_nonneg ((fourierCoeff (reflCircle f) (n : ℤ)).re)]
  have heven : ∀ n : ℤ,
      fourierCoeff (reflCircle f) (-n) = fourierCoeff (reflCircle f) n := by
    intro n
    rw [fourierCoeff_reflCircle, fourierCoeff_reflCircle, fco_neg_continuousOn hf]
  rw [← summable_norm_iff]
  apply Summable.of_nat_of_neg_add_one
  · exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbnd hcos
  · refine Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => ?_) (hcos.comp_injective (add_left_injective 1))
    rw [show (-((n : ℤ) + 1)) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, heven]
    simpa using hbnd (n + 1)

end

end ShenWork.Paper2.IntervalReflCircleContinuousOn

namespace ShenWork.Paper2.IntervalReflCircleContinuousOn
section AxiomAudit
#print axioms reflCircle_continuous_of_continuousOn
#print axioms reflCircle_eq_of_eqOn_Icc
#print axioms fourierCoeff_reflCircle_summable_of_cosineCoeff_abs_continuousOn
end AxiomAudit
end ShenWork.Paper2.IntervalReflCircleContinuousOn
