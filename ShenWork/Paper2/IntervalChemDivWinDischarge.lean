import ShenWork.PDE.IntervalFlooredSourceTimeDataIterate
import ShenWork.PDE.IntervalChemDivTimeDerivative
import ShenWork.PDE.IntervalDuhamelSourceTimeC1On
import ShenWork.Paper2.IntervalMildPicard

/-!
# `win` discharge — chem-div `DuhamelSourceTimeC1On` from a gradient mild solution

This file closes the `win` field of `ChemDivHalfStepSourceData`
(`Brick4ChemDivHalfStep.lean`), i.e. the windowed chemotaxis-divergence source
package

  `DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p D.u) c' d'`,

to its precise true bottom, starting from a `GradientMildSolutionData`.

## What the target needs (recursion check, verified against the repo)

The window-local package is the forgetful image (`DuhamelSourceTimeC1.toOn`) of the
GLOBAL `DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p D.u)`, which the committed
chain `coupledChemDivSource_timeC1_of_fields` / `…_of_fluxJointC2` produces from a
`CoupledChemDivTimeC1Fields p D.u`.  That structure's load-bearing field is the
chain-rule/joint-`C²` leg `hchain : CoupledChemDivLocalChainRule p D.u`, which —
threaded through the committed FAC producers — bottoms out at

  `IterateSourceTimeData p D.u du d2u`

(the source `srcSlice = ν·u^γ` time-`C²` chain `∂ₜ(ν u^γ)=s₁`, `∂ₜ s₁=s₂`,
plus per-slice space-`C²`-Neumann data and `(kπ)⁻²` envelopes) together with the
bounded-weight `ℓ¹` source summability and the FAC slab `other`.

**Recursion-check verdict.**  `GradientMildSolutionData` carries only
`HasContinuousSlices` (per-slice spatial *continuity*) and `HasJointMeasurability`
of `D.u`, plus the pointwise bound/nonneg/positivity facts.  It does **not** carry
the time-`C²`/space-`C²` parabolic regularity that `IterateSourceTimeData` demands
(`time1`/`time2`: the solution is twice differentiable in time with explicit
derivative fields; `sliceC2`/`sliceNeumann`: each slice is space-`C²` with Neumann
endpoint data).  The positivity floor `IterateSourceTimeData.floor` IS available
(from `D.hpos`), but the time/space `C²` legs are the genuine solution-regularity
residual.  This residual is exactly the "G4 regularity bootstrap / restart cosine
representation" frontier of the Thm 1.1 ledger; in that ledger it is supplied by
`ResolverHasSpectralAgreement`, whose `exists_data` field literally *carries a
`DuhamelSourceTimeC1`* — so the regularity is a sibling-of/downstream-of a source
time-`C¹` package, not a free consequence of the bare mild fixed point.

**No `s=0` obstruction.**  The genuine consumer (`ChemDivHalfStepSourceData.win`)
uses a positive window `0 < c' t`; the global package is stated on all of `ℝ` and
`.toOn` restricts to any `[lo,hi]` with `0 ≤ lo`, so the value- and
derivative-envelope legs never touch `s → 0+`.

This file therefore lands the maximal *unconditional-modulo-the-residual* producer:
the residual is named `IterateSourceTimeData` (+ decay/`ℓ¹`/adot inputs), and the
windowed `DuhamelSourceTimeC1On` is produced from it through the committed chain.

No `sorry`, no `axiom`, no `native_decide`, no `admit`.
-/

open Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.PDE.IntervalMildSourceDecayHelper (IntervalWeakH2Neumann)
open ShenWork.IntervalCoupledRegularityBootstrap

noncomputable section

namespace ShenWork.IntervalChemDivWinDischarge

variable {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}

/-- **The genuine residual bundle.**  Everything `CoupledChemDivTimeC1Fields p u`
needs that is NOT carried by a bare `GradientMildSolutionData`: the iterate
time-`C²`/space-`C²` source datum `IterateSourceTimeData`, the bounded-weight
`ℓ¹` source summability (value + gradient), the FAC slab `other`, the chem-div
source weak-`H²ₙ`/decay/zeroth-coefficient envelopes, and the time-derivative
coefficient continuity/uniform-bound. -/
structure ChemDivSolutionRegularityResidual
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) where
  du : ℝ → ℝ → ℝ
  d2u : ℝ → ℝ → ℝ
  hiter : ShenWork.IntervalFlooredSourceTimeDataIterate.IterateSourceTimeData p u du d2u
  hsrcContDiff : ∀ k, ContDiff ℝ (2 : ℕ∞)
    (ShenWork.IntervalPhysicalResolverDataConcrete.srcTimeCoeff p u k)
  hsrcBound : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
    ‖iteratedFDeriv ℝ i
      (ShenWork.IntervalPhysicalResolverDataConcrete.srcTimeCoeff p u k) t‖ ≤
      ShenWork.IntervalPhysicalSourceTimeC2Concrete.builtEs
        (ShenWork.IntervalFlooredSourceTimeDataIterate.flooredSourceTimeData_of_iterate
          hiter) i k
  hval : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (ShenWork.IntervalResolverJointC2Physical.boundedWeightJointMajorant
      (fun i k => ShenWork.PDE.intervalNeumannResolverWeight p k *
        ShenWork.IntervalPhysicalSourceTimeC2Concrete.builtEs
          (ShenWork.IntervalFlooredSourceTimeDataIterate.flooredSourceTimeData_of_iterate
            hiter) i k) m)
  hgrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (ShenWork.IntervalResolverJointC2Physical.boundedWeightJointGradMajorant
      (fun i k => ShenWork.PDE.intervalNeumannResolverWeight p k *
        ShenWork.IntervalPhysicalSourceTimeC2Concrete.builtEs
          (ShenWork.IntervalFlooredSourceTimeDataIterate.flooredSourceTimeData_of_iterate
            hiter) i k) m)
  other : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in nhds τ,
      ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      ContDiffAt ℝ 2 (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x)) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      0 < 1 + intervalDomainLift (coupledChemicalConcentration p u s) x) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      (fun y : ℝ => coupledChemDivFluxTimeDerivativeLift p u s y) =ᶠ[nhds x]
        (fun y : ℝ => fderiv ℝ
          (Function.uncurry (coupledChemDivFluxLift p u)) (s, y) (1, 0))) ∧
    ContinuousOn (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
  Cchem : ℝ
  hCchem : 0 ≤ Cchem
  hH2 : ∀ s, 0 ≤ s → IntervalWeakH2Neumann (coupledChemDivSourceLift p u s)
  hdecay : ∀ s, 0 ≤ s → ∀ k : ℕ, 1 ≤ k →
    |cosineCoeffs (coupledChemDivSourceLift p u s) k| ≤ Cchem / ((k : ℝ) * Real.pi) ^ 2
  hzero : ∀ s, 0 ≤ s →
    |cosineCoeffs (coupledChemDivSourceLift p u s) 0| ≤ Cchem
  hadotcont : ∀ n, Continuous (fun s => coupledChemDivAdot p u s n)
  MchemDot : ℝ
  hMdot : ∀ s, 0 ≤ s → ∀ n, |coupledChemDivAdot p u s n| ≤ MchemDot

/-- The chem-div primitive joint-`C²` flux package built from the iterate residual,
through the committed FAC chain. -/
theorem fluxJointC2Hyp_of_residual {u : ℝ → intervalDomainPoint → ℝ}
    (R : ChemDivSolutionRegularityResidual p u) :
    CoupledChemDivFluxJointC2Hyp p u :=
  coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs
    (ShenWork.IntervalFlooredSourceTimeDataIterate.coupledChemDivFluxFactorJointC2Inputs_of_iterate
      R.hiter R.hsrcContDiff R.hsrcBound R.hval R.hgrad R.other)

/-- **Global chem-div source time-`C¹` package from the residual.**  Wires the
residual's chain-rule/decay/adot data through `coupledChemDivSource_timeC1_of_fluxJointC2`. -/
noncomputable def coupledChemDivSource_duhamelSourceTimeC1_of_residual
    {u : ℝ → intervalDomainPoint → ℝ}
    (R : ChemDivSolutionRegularityResidual p u) :
    DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u) :=
  coupledChemDivSource_timeC1_of_fluxJointC2
    R.Cchem R.hCchem R.hH2 R.hdecay R.hzero
    (fluxJointC2Hyp_of_residual R)
    R.hadotcont R.MchemDot R.hMdot

/-- **`win` discharge on `[0, T]`.**  From a gradient mild solution together with
the chem-div solution-regularity residual, produce the window-local chem-div
source package on the full closed window `[0, D.T]`. -/
noncomputable def coupledChemDivSource_timeC1On_of_gradientSolution
    (D : GradientMildSolutionData p u₀)
    (R : ChemDivSolutionRegularityResidual p D.u) :
    DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p D.u) 0 D.T :=
  ShenWork.IntervalDuhamelSourceTimeC1On.DuhamelSourceTimeC1.toOn
    (coupledChemDivSource_duhamelSourceTimeC1_of_residual R) 0 D.T le_rfl

/-- **`win` discharge on a positive window `[c', d']`.**  The genuine consumer
(`ChemDivHalfStepSourceData.win`) needs the package off the `t=0` wall, on
`0 ≤ c' ≤ d' ≤ D.T`; obtained by `toOn` + `restrict_hi`.  No `s = 0` demand: the
value- and derivative-envelope legs hold uniformly on the whole nonnegative axis. -/
noncomputable def coupledChemDivSource_timeC1On_window_of_gradientSolution
    (D : GradientMildSolutionData p u₀)
    (R : ChemDivSolutionRegularityResidual p D.u)
    {c' d' : ℝ} (hc' : 0 ≤ c') (hd' : d' ≤ D.T) :
    DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p D.u) c' d' := by
  have hglob : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p D.u) :=
    coupledChemDivSource_duhamelSourceTimeC1_of_residual R
  exact ShenWork.IntervalDuhamelSourceTimeC1On.DuhamelSourceTimeC1On.restrict_hi
    (ShenWork.IntervalDuhamelSourceTimeC1On.DuhamelSourceTimeC1.toOn hglob c' D.T hc') hd'

end ShenWork.IntervalChemDivWinDischarge

open ShenWork.IntervalChemDivWinDischarge in
#print axioms coupledChemDivSource_timeC1On_of_gradientSolution
open ShenWork.IntervalChemDivWinDischarge in
#print axioms coupledChemDivSource_timeC1On_window_of_gradientSolution
