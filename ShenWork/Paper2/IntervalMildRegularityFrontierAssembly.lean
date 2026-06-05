/-
  Assembly of regularity frontier fields from G4 infrastructure.

  Maps the 9 fields of `GradientMildClassicalRegularityFrontierData`
  to proved G4 theorems. The u-side time regularity (timeSlices,
  jointTimeDerivInterior) flows from `HasTimeNeighborhoodSpectralAgreement`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalMildToClassical
import ShenWork.PDE.IntervalMildTimeDerivContinuity
import ShenWork.PDE.IntervalMildFrontierFromSpectral

open ShenWork.IntervalDomain
open ShenWork.IntervalMildTimeDerivContinuity
  (HasTimeNeighborhoodSpectralAgreement
   mildSolution_hasDerivAt_time
   mildSolution_timeDeriv_continuousOn_fixed_x
   mildSolution_timeDeriv_jointContinuousOn)
open ShenWork.IntervalMildFrontierFromSpectral
  (mildSolution_timeDeriv_jointContinuousOn_closed
   mildSolution_jointContinuousOn_closed)
open ShenWork.Paper2
open ShenWork.IntervalMildPicard
open Set Filter Topology

noncomputable section

namespace ShenWork.Paper2.RegularityFrontierAssembly

/-- **timeSlices (u-side)**: DifferentiableAt + continuous time derivative
for each fixed x, from `HasTimeNeighborhoodSpectralAgreement`. -/
theorem timeSlices_u_of_spectralAgreement
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (H : HasTimeNeighborhoodSpectralAgreement T u)
    (x : intervalDomainPoint) :
    (∀ t ∈ Ioo (0 : ℝ) T,
      DifferentiableAt ℝ (fun s => u s x) t) ∧
    ContinuousOn (fun s => deriv (fun r => u r x) s) (Ioo (0 : ℝ) T) := by
  constructor
  · intro t ht
    obtain ⟨a₀, M, hM, ha₀, a, src, offset, hτ₀, hagree⟩ :=
      H.exists_data t ht.1 ht.2
    exact (mildSolution_hasDerivAt_time hM ha₀ src hτ₀ hagree x).differentiableAt
  · exact mildSolution_timeDeriv_continuousOn_fixed_x H x

/-- **jointTimeDerivInterior (u-side)**: joint (t,x) continuity of the time
derivative on the open slab (0,T) × (0,1). -/
theorem jointTimeDerivInterior_u_of_spectralAgreement
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (H : HasTimeNeighborhoodSpectralAgreement T u) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          deriv (fun s => intervalDomainLift (u s) x) t))
      (Ioo (0 : ℝ) T ×ˢ Ioo (0 : ℝ) 1) :=
  mildSolution_timeDeriv_jointContinuousOn H

/-- **jointTimeDerivClosed (u-side)**: joint (t,x) continuity of ∂ₜ(lift(u t))(x)
on `Ioo 0 T ×ˢ Icc 0 1` (closed in x).

Extends `jointTimeDerivInterior_u_of_spectralAgreement` from `Ioo 0 1` to `Icc 0 1`
using uniform convergence of the cosine derivative series on all of `[0,1]`
(|cos(nπx)| ≤ 1 for all x), via `mildSolution_timeDeriv_jointContinuousOn_closed`. -/
theorem jointTimeDerivClosed_u_of_spectralAgreement
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (H : HasTimeNeighborhoodSpectralAgreement T u) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          deriv (fun s => intervalDomainLift (u s) x) t))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
  mildSolution_timeDeriv_jointContinuousOn_closed H

/-- **jointSolutionClosed (u-side)**: joint (t,x) continuity of `lift(u t)(x)`
on `Ioo 0 T ×ˢ Icc 0 1` (closed in x).

The restart cosine series is jointly continuous on all of `Ioi 0 × ℝ`; this
restricts to `Ioo 0 T × Icc 0 1` via `mildSolution_jointContinuousOn_closed`. -/
theorem jointSolutionClosed_u_of_spectralAgreement
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (H : HasTimeNeighborhoodSpectralAgreement T u) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
  mildSolution_jointContinuousOn_closed H

end ShenWork.Paper2.RegularityFrontierAssembly
