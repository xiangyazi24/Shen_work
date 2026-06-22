/-
  ShenWork/Paper2/IntervalChiNegCloseBaseSeed.lean

  TASK 1 (the χ₀<0 closer) — the BASE SEED `h0 : MemHSigma 0 (cosineCoeffs ut)`.

  This is the elementary, fully unconditional input the uniform bootstrap ladder
  `gradientSolution_contDiffOn_two_FINAL` starts from: the running regularity at
  level `σ₀ = 0`.  It is pure cosine–Bessel: a function continuous on `[0,1]`
  lies in `L²[0,1]`, hence its Neumann cosine coefficients are `ℓ²`, i.e.
  `MemHSigma 0 (cosineCoeffs f)`.

  We derive it for an ARBITRARY function continuous on `[0,1]`
  (`memHSigma_zero_of_continuousOn`) — a clean mirror of the source-side
  `resolverSourceCoeff_re_sq_summable_of_continuousOn`, with the bare lift in
  place of `ν·u^γ` — and then specialize to the χ₀<0 gradient mild solution slice
  `D.u t` for `t > 0` via the keystone's `HasContinuousSlices`
  (`gradientSolution_memHSigma_zero`).

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New names only.
-/
import ShenWork.Paper2.IntervalResolverWeakBounds
import ShenWork.Paper2.IntervalHSigmaScale
import ShenWork.Paper2.IntervalMildPicard

noncomputable section

open MeasureTheory intervalIntegral
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.HeatKernelGradientEstimates
  (unitIntervalNeumannCosineCoeff unitIntervalNeumannCosineCoeff_l2_bound)
open ShenWork.Paper2.HSigmaScale (MemHSigma memHSigma_zero)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalMildPicard (GradientMildSolutionData HasContinuousSlices)
open ShenWork.Paper2 (evenReflection_memLp_two_of_continuousOn)
open scoped Topology

namespace ShenWork.Paper2.ChiNegCloseBaseSeed

/-- `intervalDomainLift f` is continuous on `[0,1]` whenever `f` is continuous on
the (subtype) domain.  A local copy of the (private) bridge in `IntervalDomainMass`. -/
theorem intervalDomainLift_continuousOn_Icc_of_continuous
    {f : intervalDomainPoint → ℝ} (hf : Continuous f) :
    ContinuousOn (intervalDomainLift f) (Set.Icc (0 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_restrict]
  have heq : (Set.Icc (0 : ℝ) 1).restrict (intervalDomainLift f) = f := by
    funext ⟨y, hy⟩
    simp only [Set.restrict_apply, intervalDomainLift]
    split_ifs
    exact congr_arg f (Subtype.ext rfl)
  rw [heq]; exact hf

/-- **TASK 1 (generic) — cosine–Bessel base seed.**  Any function continuous on
`[0,1]` has `ℓ²` Neumann cosine coefficients, i.e. `MemHSigma 0 (cosineCoeffs g)`.

The integrability discharge mirrors `resolverSourceCoeff_re_sq_summable_of_
continuousOn` (with the bare `g` in place of `ν·u^γ`): `g ∈ C[0,1] ⟹ ↑g ∈ L²`,
so `unitIntervalNeumannCosineCoeff_l2_bound` gives `Summable (cosineCoeffs g)²`,
which is exactly `MemHSigma 0` by `memHSigma_zero`. -/
theorem memHSigma_zero_of_continuousOn {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) 1)) :
    MemHSigma 0 (cosineCoeffs g) := by
  set f : ℝ → ℂ := fun x => ((g x : ℝ) : ℂ) with hf
  have hfcontOn : ContinuousOn f (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Complex.continuous_ofReal.comp_continuousOn hg
  have hfint : IntervalIntegrable f volume 0 1 := hfcontOn.intervalIntegrable
  have hfsq : IntervalIntegrable (fun x : ℝ => ‖f x‖ ^ 2) volume 0 1 :=
    ((hfcontOn.norm).pow 2).intervalIntegrable
  have hL2 : MemLp (ShenWork.CosineParsevalBridge.unitIntervalEvenReflection f) 2
      (volume.restrict (Set.Ioc (-1 : ℝ) 1)) :=
    evenReflection_memLp_two_of_continuousOn hg
  have hsum := (unitIntervalNeumannCosineCoeff_l2_bound hfint hL2 hfsq).1
  rw [memHSigma_zero]
  -- `cosineCoeffs g k = unitIntervalNeumannCosineCoeff (↑∘g) k` definitionally.
  exact hsum.congr (fun k => by rw [cosineCoeffs])

/-- **TASK 1 — the χ₀<0 gradient mild solution base seed.**  For every interior
time `t ∈ (0, D.T]`, the solution slice lift `D.u t` is continuous on `[0,1]`
(keystone `HasContinuousSlices`), hence `MemHSigma 0 (cosineCoeffs (lift (D.u t)))`.

This is the `h0` consumed at base regularity `σ₀ = 0` by
`gradientSolution_contDiffOn_two_FINAL` (with `n·α > 5/2`).  Unconditional in the
sign of `χ₀` — it uses only the slice continuity carried by every
`GradientMildSolutionData`. -/
theorem gradientSolution_memHSigma_zero
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    MemHSigma 0 (cosineCoeffs (intervalDomainLift (D.u t))) :=
  memHSigma_zero_of_continuousOn
    (intervalDomainLift_continuousOn_Icc_of_continuous (D.hcont t ht htT))

end ShenWork.Paper2.ChiNegCloseBaseSeed

namespace ShenWork.Paper2.ChiNegCloseBaseSeed
#print axioms memHSigma_zero_of_continuousOn
#print axioms gradientSolution_memHSigma_zero
end ShenWork.Paper2.ChiNegCloseBaseSeed
