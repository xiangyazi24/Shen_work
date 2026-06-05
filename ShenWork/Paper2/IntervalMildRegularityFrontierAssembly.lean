/-
  Assembly of regularity frontier fields from G4 + F2 infrastructure.

  Maps the time-regularity fields of `GradientMildClassicalRegularityFrontierData`
  to proved theorems:
  - u-side: from `HasTimeNeighborhoodSpectralAgreement` (G4)
  - v-side: from `HasResolverDirectSpectralData` (F2)

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalMildToClassical
import ShenWork.PDE.IntervalMildTimeDerivContinuity
import ShenWork.PDE.IntervalMildFrontierFromSpectral
import ShenWork.Paper2.IntervalResolverDirectTimeRegularity

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
open ShenWork.IntervalResolverDirectTimeRegularity
  (HasResolverDirectSpectralData
   resolver_direct_differentiableAt_time
   resolver_direct_timeDeriv_continuousOn
   resolver_direct_jointTimeDerivInterior
   resolver_direct_jointTimeDerivClosed
   resolver_direct_jointSolutionClosed)
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

/-! ## V-side time regularity fields (from F2: resolver spectral data) -/

/-- **timeSlices (v-side)**: DifferentiableAt + continuous time derivative
for the resolver v at each fixed x, from `HasResolverDirectSpectralData`. -/
theorem timeSlices_v_of_resolverSpectral
    {T : ℝ} {v : ℝ → intervalDomainPoint → ℝ} {p : CM2Params}
    (H : HasResolverDirectSpectralData T v p)
    (x : intervalDomainPoint) :
    (∀ t ∈ Ioo (0 : ℝ) T,
      DifferentiableAt ℝ (fun s => v s x) t) ∧
    ContinuousOn (fun s => deriv (fun r => v r x) s) (Ioo (0 : ℝ) T) := by
  constructor
  · intro t ht
    exact resolver_direct_differentiableAt_time H ht.1 ht.2 x
  · exact resolver_direct_timeDeriv_continuousOn H x

/-- **jointTimeDerivInterior (v-side)**: joint (t,x) continuity of the
resolver time derivative on the open slab (0,T) × (0,1). -/
theorem jointTimeDerivInterior_v_of_resolverSpectral
    {T : ℝ} {v : ℝ → intervalDomainPoint → ℝ} {p : CM2Params}
    (H : HasResolverDirectSpectralData T v p) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          deriv (fun s => intervalDomainLift (v s) x) t))
      (Ioo (0 : ℝ) T ×ˢ Ioo (0 : ℝ) 1) :=
  resolver_direct_jointTimeDerivInterior H

/-- **jointTimeDerivClosed (v-side)**: joint (t,x) continuity of ∂ₜv on
the closed spatial slab Ioo 0 T ×ˢ Icc 0 1. -/
theorem jointTimeDerivClosed_v_of_resolverSpectral
    {T : ℝ} {v : ℝ → intervalDomainPoint → ℝ} {p : CM2Params}
    (H : HasResolverDirectSpectralData T v p) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          deriv (fun s => intervalDomainLift (v s) x) t))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
  resolver_direct_jointTimeDerivClosed H

/-- **jointSolutionClosed (v-side)**: joint (t,x) continuity of the resolver
v(t,x) on the closed spatial slab Ioo 0 T ×ˢ Icc 0 1. -/
theorem jointSolutionClosed_v_of_resolverSpectral
    {T : ℝ} {v : ℝ → intervalDomainPoint → ℝ} {p : CM2Params}
    (H : HasResolverDirectSpectralData T v p) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
  resolver_direct_jointSolutionClosed H

end ShenWork.Paper2.RegularityFrontierAssembly
