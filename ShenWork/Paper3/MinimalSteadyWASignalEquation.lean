import ShenWork.Paper3.MinimalSteadyWAClassicalProfiles

/-!
# The classical signal equation on the minimal steady branch

The diagonal multiplier defining `R = (-∂ₓₓ + 1)⁻¹` satisfies its elliptic
equation coefficientwise.  Applying this identity to

`v = 1 + a R h`,  `u = 1 + a h`

and then using Wiener differentiation/evaluation proves

`vₓₓ - v + u = 0`

for every point of the local branch.
-/

noncomputable section

namespace ShenWork.M3Counterexample

open ShenWork.Wiener

/-! ## Elementary differentiation rules -/

@[simp]
theorem wD_zero (r : ℕ) :
    WA.wD (0 : WA (r + 1)) = 0 := by
  apply WA.ext
  funext n
  simp [WA.wD, wDeriv]

@[simp]
theorem wD_one (r : ℕ) :
    WA.wD (1 : WA (r + 1)) = 0 := by
  apply WA.ext
  funext n
  simp [WA.wD, wDeriv, wOne]

theorem wD_add {r : ℕ} (a b : WA (r + 1)) :
    WA.wD (a + b) = WA.wD a + WA.wD b := by
  apply WA.ext
  funext n
  change
    (Complex.I * Real.pi * (n : ℂ)) *
        (a.toFun n + b.toFun n) =
      (Complex.I * Real.pi * (n : ℂ)) * a.toFun n +
        (Complex.I * Real.pi * (n : ℂ)) * b.toFun n
  ring

theorem wD_sub {r : ℕ} (a b : WA (r + 1)) :
    WA.wD (a - b) = WA.wD a - WA.wD b := by
  apply WA.ext
  funext n
  change
    (Complex.I * Real.pi * (n : ℂ)) *
        (a.toFun n - b.toFun n) =
      (Complex.I * Real.pi * (n : ℂ)) * a.toFun n -
        (Complex.I * Real.pi * (n : ℂ)) * b.toFun n
  ring

theorem wD_real_smul {r : ℕ} (c : ℝ) (a : WA (r + 1)) :
    WA.wD (c • a) = c • WA.wD a := by
  apply WA.ext
  funext n
  change
    (Complex.I * Real.pi * (n : ℂ)) *
        ((c : ℂ) * a.toFun n) =
      (c : ℂ) *
        ((Complex.I * Real.pi * (n : ℂ)) * a.toFun n)
  ring

@[simp]
theorem toZero_toZero {r : ℕ} (a : WA r) :
    WA.toZero (WA.toZero a) = WA.toZero a := by
  apply WA.ext
  rfl

theorem staticEval_toZero {r : ℕ} (a : WA r) :
    staticEval (WA.toZero a) = staticEval a := by
  funext x
  unfold staticEval
  rw [toZero_toZero]

/-! ## Coefficient-space elliptic equation -/

theorem signalResolverAmbient_equation (h : BranchSpace) :
    WA.wD (WA.wD (signalResolverAmbientCLM h)) -
        WA.toZero (signalResolverAmbientCLM h) +
      WA.toZero (branchSpaceAmbientCLM h) = 0 := by
  apply WA.ext
  funext n
  change
    (Complex.I * Real.pi * (n : ℂ)) *
          ((Complex.I * Real.pi * (n : ℂ)) *
            (((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) *
              h.1.1.toFun n)) -
        (((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) *
          h.1.1.toFun n) +
      h.1.1.toFun n = 0
  have hden :
      (1 + ((n : ℝ) * Real.pi) ^ 2 : ℝ) ≠ 0 := by
    positivity
  have hreal :
      (1 : ℝ) -
          ((n : ℝ) * Real.pi) ^ 2 *
            (1 / (1 + ((n : ℝ) * Real.pi) ^ 2)) -
        (1 / (1 + ((n : ℝ) * Real.pi) ^ 2)) = 0 := by
    field_simp [hden]
    ring
  have hcomplex :
      (1 : ℂ) -
          ((((n : ℝ) * Real.pi) ^ 2 : ℝ) : ℂ) *
            (((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ)) -
        (((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ)) = 0 := by
    exact_mod_cast hreal
  calc
    (Complex.I * Real.pi * (n : ℂ)) *
            ((Complex.I * Real.pi * (n : ℂ)) *
              (((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) *
                h.1.1.toFun n)) -
          (((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) *
            h.1.1.toFun n) +
        h.1.1.toFun n =
        ((1 : ℂ) -
            ((((n : ℝ) * Real.pi) ^ 2 : ℝ) : ℂ) *
              (((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ)) -
          (((1 / (1 + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ))) *
            h.1.1.toFun n := by
          ring_nf
          rw [Complex.I_sq]
          push_cast
          ring
    _ = 0 := by rw [hcomplex, zero_mul]

theorem minimalSteadySignalCoeff_equation (a : ℝ) :
    WA.wD (WA.wD (minimalSteadySignalCoeff a)) -
        WA.toZero (minimalSteadySignalCoeff a) +
      WA.toZero (minimalSteadyPopulationCoeff a) = 0 := by
  rw [minimalSteadySignalCoeff_formula,
    minimalSteadyPopulationCoeff_formula,
    wD_add, wD_one, zero_add, wD_real_smul,
    wD_real_smul, toZero_add, toZero_add,
    toZero_one, toZero_real_smul, toZero_real_smul]
  have hresolver :=
    signalResolverAmbient_equation (minimalSteadyProfile a)
  change
    (a : ℂ) •
          WA.wD (WA.wD
            (signalResolverAmbientCLM (minimalSteadyProfile a))) -
        (1 + (a : ℂ) •
          WA.toZero
            (signalResolverAmbientCLM (minimalSteadyProfile a))) +
      (1 + (a : ℂ) •
        WA.toZero
          (branchSpaceAmbientCLM (minimalSteadyProfile a))) = 0
  calc
    (a : ℂ) •
            WA.wD (WA.wD
              (signalResolverAmbientCLM (minimalSteadyProfile a))) -
          (1 + (a : ℂ) •
            WA.toZero
              (signalResolverAmbientCLM (minimalSteadyProfile a))) +
        (1 + (a : ℂ) •
          WA.toZero
            (branchSpaceAmbientCLM (minimalSteadyProfile a))) =
        (a : ℂ) •
          (WA.wD (WA.wD
              (signalResolverAmbientCLM (minimalSteadyProfile a))) -
            WA.toZero
              (signalResolverAmbientCLM (minimalSteadyProfile a)) +
            WA.toZero
              (branchSpaceAmbientCLM (minimalSteadyProfile a))) := by
          module
    _ = 0 := by rw [hresolver, smul_zero]

/-! ## Classical signal equation -/

theorem minimalSteadySignal_equation (a x : ℝ) :
    deriv (deriv (minimalSteadySignal a)) x -
        minimalSteadySignal a x +
      minimalSteadyPopulation a x = 0 := by
  have hcoeff := minimalSteadySignalCoeff_equation a
  have heval :=
    congrArg (fun q : WA 0 => staticEval q x) hcoeff
  change
    staticEval
        (WA.wD (WA.wD (minimalSteadySignalCoeff a)) -
          WA.toZero (minimalSteadySignalCoeff a) +
          WA.toZero (minimalSteadyPopulationCoeff a)) x =
      staticEval 0 x at heval
  rw [congrFun (staticEval_add
      (WA.wD (WA.wD (minimalSteadySignalCoeff a)) -
        WA.toZero (minimalSteadySignalCoeff a))
      (WA.toZero (minimalSteadyPopulationCoeff a))) x,
    Pi.add_apply,
    congrFun (staticEval_sub
      (WA.wD (WA.wD (minimalSteadySignalCoeff a)))
      (WA.toZero (minimalSteadySignalCoeff a))) x,
    congrFun (staticEval_zero 0) x,
    Pi.sub_apply,
    congrFun (staticEval_toZero
      (minimalSteadySignalCoeff a)) x,
    congrFun (staticEval_toZero
      (minimalSteadyPopulationCoeff a)) x] at heval
  simpa only [minimalSteadySignal, minimalSteadyPopulation,
    secondDeriv_staticEval_eq_wD_wD] using heval

end ShenWork.M3Counterexample
