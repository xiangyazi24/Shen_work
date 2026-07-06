/-
  ShenWork/Paper2/IntervalHuRestartCoeffFiniteCover.lean

  Consumer side of the later finite-cover producer for Hu restart coefficients.

  This file does not prove the topological finite subcover.  It proves that once
  such a finite family of restart charts is supplied, it fills the compact
  coefficient envelope field required by the HuCoeff resolver-source surfaces.
-/
import ShenWork.Paper2.IntervalHuRestartCoeffEnvelope
import ShenWork.Paper2.IntervalResolverSourceWindowHuCoeffNoK1Inputs

open MeasureTheory Filter Topology Set
open scoped BigOperators
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalMildTimeDerivContinuity (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalPicardLimitRestartBdd (DuhamelSourceBddOn)
open ShenWork.IntervalPicardLimitBddProducer (patchedSource)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)

noncomputable section

namespace ShenWork.Paper2.ResolverSourceWindowInput

/-- A finite family of restart charts that covers one compact time window.
Each covered time is represented by one chart whose restart time is bounded
away from zero by the chart's `eps`. -/
structure HuRestartFiniteCover
    (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    (Hu : HasTimeNeighborhoodSpectralAgreement T u)
    (a b : ℝ) (ι : Type) [Fintype ι] where
  M : ι → ℝ
  hM : ∀ i, 0 ≤ M i
  a0 : ι → ℕ → ℝ
  ha0 : ∀ i n, |a0 i n| ≤ M i
  coeff : ι → ℝ → ℕ → ℝ
  src : ∀ i, DuhamelSourceTimeC1 (coeff i)
  offset : ι → ℝ
  eps : ι → ℝ
  heps : ∀ i, 0 < eps i
  exists_chart : ∀ σ ∈ Set.Icc a b,
    ∃ i : ι,
      eps i ≤ σ - offset i ∧
      Set.EqOn (intervalDomainLift (u σ))
        (fun x => ∑' n,
          localRestartCoeff (a0 i) (coeff i) (σ - offset i) n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1)

/-- A finite restart-chart cover gives the Hu coefficient envelope on the
covered compact window. -/
theorem huRestartCoeff_henv_of_finiteCover
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (Hu : HasTimeNeighborhoodSpectralAgreement T u)
    {a b : ℝ} (ha : 0 < a) (hb : b < T)
    {ι : Type} [Fintype ι]
    (C : HuRestartFiniteCover T u Hu a b ι) :
    ∃ E : ℕ → ℝ,
      Summable E ∧
      (∀ n, 0 ≤ E n) ∧
      (∀ σ ∈ Set.Icc a b, ∀ n,
        unitIntervalCosineEigenvalue n * |huRestartCoeff Hu σ n| ≤ E n) := by
  let E : ℕ → ℝ := fun n =>
    ∑ i : ι, restartCoeffWindowEigEnv (C.M i) (C.src i) (C.eps i) n
  refine ⟨E, ?_, ?_, ?_⟩
  · have hsum :
        Summable (fun n =>
          ∑ i ∈ (Finset.univ : Finset ι),
            restartCoeffWindowEigEnv (C.M i) (C.src i) (C.eps i) n) := by
      exact summable_sum (s := (Finset.univ : Finset ι))
        (f := fun i n => restartCoeffWindowEigEnv (C.M i) (C.src i) (C.eps i) n)
        (fun i _hi => restartCoeffWindowEigEnv_summable (C.src i) (C.heps i))
    simpa [E] using hsum
  · intro n
    dsimp [E]
    exact Finset.sum_nonneg (fun i _hi =>
      restartCoeffWindowEigEnv_nonneg (C.src i) (C.hM i) n)
  · intro σ hσ n
    obtain ⟨i, hετ, hagree⟩ := C.exists_chart σ hσ
    have hσ0 : 0 < σ := lt_of_lt_of_le ha hσ.1
    have hσT : σ < T := lt_of_le_of_lt hσ.2 hb
    have hlocal :
        unitIntervalCosineEigenvalue n * |huRestartCoeff Hu σ n|
          ≤ restartCoeffWindowEigEnv (C.M i) (C.src i) (C.eps i) n :=
      huRestartCoeff_eigen_abs_le_chart_window Hu hσ0 hσT
        (C.ha0 i) (C.src i) (C.heps i) hετ hagree n
    dsimp [E]
    exact hlocal.trans
      (Finset.single_le_sum
        (fun j _hj => restartCoeffWindowEigEnv_nonneg (C.src j) (C.hM j) n)
        (Finset.mem_univ i))

/-- HuCoeff inputs where the compact coefficient envelope is supplied by
explicit finite restart-chart covers. -/
structure ResolverSourceWindowHuFiniteCoverInputs
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u) where
  hcover : ∀ a b, 0 < a → b < D.T → a ≤ b →
    Σ (ι : Type), Σ (_ : Fintype ι), HuRestartFiniteCover D.T D.u Hu a b ι
  adotPow : ℝ → ℕ → ℝ
  hderivPow : ∀ σ, 0 < σ → σ < D.T → ∀ n,
    HasDerivAt
      (fun r => ShenWork.IntervalNeumannFullKernel.cosineCoeffs
        (fun x => p.ν * intervalDomainLift (D.u r) x ^ p.γ) n)
      (adotPow σ n) σ
  hadotPowCont : ∀ n, ContinuousOn (fun σ => adotPow σ n) (Set.Ioo 0 D.T)
  hMdotPow : ∀ a b, 0 < a → b < D.T →
    ∃ Mdot, ∀ σ ∈ Set.Icc a b, ∀ n, |adotPow σ n| ≤ Mdot

/-- Explicit finite covers fill the existing HuCoeff resolver-source input
surface. -/
def resolverSourceWindowHuCoeffInputs_of_finiteCoverInputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    {Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u}
    (H : ResolverSourceWindowHuFiniteCoverInputs p D Hu) :
    ResolverSourceWindowHuCoeffInputs p D Hu where
  henv := by
    intro a b ha hb hab
    obtain ⟨ι, hι, C⟩ := H.hcover a b ha hb hab
    letI : Fintype ι := hι
    exact huRestartCoeff_henv_of_finiteCover Hu ha hb C
  adotPow := H.adotPow
  hderivPow := H.hderivPow
  hadotPowCont := H.hadotPowCont
  hMdotPow := H.hMdotPow

/-- No-K1 HuCoeff inputs where the compact coefficient envelope is supplied by
explicit finite restart-chart covers. -/
structure ResolverSourceWindowHuFiniteCoverNoK1Inputs
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u) where
  hcover : ∀ a b, 0 < a → b < D.T → a ≤ b →
    Σ (ι : Type), Σ (_ : Fintype ι), HuRestartFiniteCover D.T D.u Hu a b ι
  hsrc0 : DuhamelSourceBddOn (patchedSource p u₀ D.u) D.T

/-- Explicit finite covers fill the no-K1 HuCoeff resolver-source input
surface. -/
def resolverSourceWindowHuCoeffNoK1Inputs_of_finiteCoverNoK1Inputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    {Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u}
    (H : ResolverSourceWindowHuFiniteCoverNoK1Inputs p D Hu) :
    ResolverSourceWindowHuCoeffNoK1Inputs p D Hu where
  henv := by
    intro a b ha hb hab
    obtain ⟨ι, hι, C⟩ := H.hcover a b ha hb hab
    letI : Fintype ι := hι
    exact huRestartCoeff_henv_of_finiteCover Hu ha hb C
  hsrc0 := H.hsrc0

end ShenWork.Paper2.ResolverSourceWindowInput
