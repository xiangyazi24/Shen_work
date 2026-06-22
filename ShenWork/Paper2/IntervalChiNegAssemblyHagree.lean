/-
  ShenWork/Paper2/IntervalChiNegAssemblyHagree.lean

  ASSEMBLY (χ₀<0) — TASK 1: deriving the `hagree` restart-cosine agreement from
  cosine Fourier inversion plus the restart-coefficient identity.

  `ChemDivHalfStepSourceData.hagree` / `RestartCosineRepresentation.hagree` is the
  slice equality
      `intervalDomainLift (D.u t) = ∑'ₙ restartDuhamelCoeff a₀ a (t/2) n · cosineMode n x`
  on `[0,1]`.

  This file lands `gradientSolution_hagree_of_restartCoeff`: the equality is
  DERIVABLE from
  * a CONTINUOUS surrogate `g` agreeing with the lift on `[0,1]` (the lift itself
    is NOT globally continuous — it is `0` off `[0,1]`; the honest inversion route
    therefore goes through a surrogate, matching the repo's existing
    `source_inversion_eq_reaction_surrogate` pattern);
  * absolute summability of `g`'s even-reflection Fourier coefficients (the
    H²-Neumann / ℓ¹ tail regularity produced by the landed bootstrap);
  * the half-step restart data `(τ>0, |a₀|≤M, src)` giving `ContDiff` of the
    restart series (`restartDuhamelCoeffSeries_contDiff_two`);
  * the **restart-coefficient identity**
      `restartDuhamelCoeff a₀ a (t/2) n = cosineCoeffs g n`   (∀ n),
    i.e. the diagonalized restart/Duhamel form of the slice's cosine coefficients.

  Bridge: `intervalCosine_hasSum_pointwise` (continuous surrogate ⇒ pointwise
  cosine inversion on `(0,1)`) + `eqOn_Icc_of_eqOn_Ioo_of_continuousOn`.

  CRITICAL HONEST ACCOUNTING.  The restart-coefficient identity itself
  (`restartDuhamelCoeff = cosineCoeffs g`) is NOT discharged here and is NOT a
  consequence of a bare `GradientMildSolutionData`: it is the restart/Duhamel
  semigroup content of the mild solution.  This file lands the inversion bridge;
  the residual is reported precisely in the assembly report.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file, new names only.
-/
import ShenWork.PDE.IntervalCosineInversion
import ShenWork.Paper2.IntervalMildRegularityBootstrap
import ShenWork.PDE.IntervalProfileBoundaryRegularity

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegAssemblyHagree

open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalCosineInversion
  (intervalCosine_hasSum_pointwise reflCircle)
open ShenWork.IntervalFullKernelRegularity (eqOn_Icc_of_eqOn_Ioo_of_continuousOn)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalMildRegularityBootstrap
  (restartDuhamelCoeff restartDuhamelCoeffSeries_contDiff_two)

/-- The lift of a continuous-on-`[0,1]` surrogate is continuous on `[0,1]`. -/
theorem lift_continuousOn_of_surrogate
    {w : intervalDomainPoint → ℝ} {g : ℝ → ℝ}
    (hg : Continuous g) (hgeq : Set.EqOn g (intervalDomainLift w) (Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) :=
  hg.continuousOn.congr hgeq.symm

/-- **The pointwise cosine-inversion agreement on the open interior (surrogate).**

For a continuous surrogate `g` agreeing on `[0,1]` with the slice lift, under
summability of `g`'s even-reflection Fourier coefficients, the lift agrees on
`(0,1)` with the cosine series of `g`'s coefficients. -/
theorem lift_eqOn_cosineSeries_Ioo
    {w : intervalDomainPoint → ℝ} {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgeq : Set.EqOn g (intervalDomainLift w) (Set.Icc (0 : ℝ) 1))
    (hsum : Summable (fun n : ℤ => fourierCoeff (reflCircle g) n)) :
    ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      intervalDomainLift w x
        = ∑' n : ℕ, cosineCoeffs g n * cosineMode n x := by
  intro x hx
  have hinv := intervalCosine_hasSum_pointwise g hg hx hsum
  have hgx : g x = intervalDomainLift w x := hgeq (Set.Ioo_subset_Icc_self hx)
  have hsum_eq : (∑' n, cosineCoeffs g n * cosineMode n x) = g x := by
    rw [← hinv.tsum_eq]
    exact tsum_congr (fun n => by
      show cosineCoeffs g n * cosineMode n x
        = unitIntervalCosineMode n x * cosineCoeffs g n
      rw [show unitIntervalCosineMode n x = cosineMode n x from rfl]; ring)
  rw [hsum_eq, hgx]

/-- **TASK 1 — `gradientSolution_hagree_of_restartCoeff`.**

The restart-cosine agreement `hagree` on `[0,1]`, derived from
* the continuous surrogate `g` (agreeing with the lift on `[0,1]`),
* its even-reflection Fourier summability `hsum`,
* the half-step restart data `(hτ, ha₀, src)` (⇒ `ContDiff` of the restart series),
* the restart-coefficient identity `hrestart : restartDuhamelCoeff a₀ a τ n = cosineCoeffs g n`.

`intervalCosine_hasSum_pointwise` gives the interior agreement; both sides are
continuous on `[0,1]` (the lift via the surrogate's continuity; the restart
series via `restartDuhamelCoeffSeries_contDiff_two`), so
`eqOn_Icc_of_eqOn_Ioo_of_continuousOn` closes the endpoints. -/
theorem gradientSolution_hagree_of_restartCoeff
    {w : intervalDomainPoint → ℝ} {g : ℝ → ℝ}
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {τ M : ℝ}
    (hτ : 0 < τ) (ha₀ : ∀ n, |a₀ n| ≤ M) (src : DuhamelSourceTimeC1 a)
    (hg : Continuous g)
    (hgeq : Set.EqOn g (intervalDomainLift w) (Set.Icc (0 : ℝ) 1))
    (hsum : Summable (fun n : ℤ => fourierCoeff (reflCircle g) n))
    (hrestart : ∀ n, restartDuhamelCoeff a₀ a τ n = cosineCoeffs g n) :
    Set.EqOn (intervalDomainLift w)
      (fun x : ℝ => ∑' n : ℕ, restartDuhamelCoeff a₀ a τ n * cosineMode n x)
      (Set.Icc (0 : ℝ) 1) := by
  -- the restart series is `ContDiff ℝ 2`, hence continuous
  have hScont : Continuous (fun x : ℝ =>
      ∑' n : ℕ, restartDuhamelCoeff a₀ a τ n * cosineMode n x) :=
    (restartDuhamelCoeffSeries_contDiff_two hτ ha₀ src).continuous
  -- lift continuous on [0,1]
  have hliftcont : ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) :=
    lift_continuousOn_of_surrogate hg hgeq
  -- interior agreement: lift = restart series on (0,1)
  have hIoo : Set.EqOn (intervalDomainLift w)
      (fun x : ℝ => ∑' n : ℕ, restartDuhamelCoeff a₀ a τ n * cosineMode n x)
      (Set.Ioo (0 : ℝ) 1) := by
    intro x hx
    rw [lift_eqOn_cosineSeries_Ioo hg hgeq hsum x hx]
    exact tsum_congr (fun n => by rw [hrestart n])
  exact eqOn_Icc_of_eqOn_Ioo_of_continuousOn hliftcont hScont.continuousOn hIoo

end ShenWork.Paper2.IntervalChiNegAssemblyHagree

#print axioms ShenWork.Paper2.IntervalChiNegAssemblyHagree.gradientSolution_hagree_of_restartCoeff
