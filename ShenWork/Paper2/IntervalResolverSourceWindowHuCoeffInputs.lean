/-
  ShenWork/Paper2/IntervalResolverSourceWindowHuCoeffInputs.lean

  Resolver-source inputs whose representation coefficients are chosen directly
  from the already-carried u-side time-neighborhood spectral agreement.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalResolverSourceWindowEnvelopeOnlyNoJointInputs
import ShenWork.PDE.IntervalResolverSpectralJointC2Producer

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalMildTimeDerivContinuity (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.ResolverSourceWindowInput

/-- A single restart chart extracted from `HasTimeNeighborhoodSpectralAgreement`
at one interior time. -/
structure HuRestartData
    (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ) (σ : ℝ) where
  a0 : ℕ → ℝ
  M : ℝ
  hM : 0 ≤ M
  ha0 : ∀ n, |a0 n| ≤ M
  a : ℝ → ℕ → ℝ
  src : DuhamelSourceTimeC1 a
  offset : ℝ
  hτ : 0 < σ - offset
  hagree_nhd : ∀ᶠ s in 𝓝 σ, ∀ x : intervalDomainPoint,
    u s x = ∑' n, localRestartCoeff a0 a (s - offset) n * cosineMode n x.1

/-- Existence of a restart chart from `Hu.exists_data` at an interior time.
This proposition-level wrapper lets the later noncomputable definition use
`Classical.choose` without eliminating a `Prop` proof directly into `Type`. -/
theorem huRestartData_exists
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (Hu : HasTimeNeighborhoodSpectralAgreement T u)
    (σ : ℝ) (hσ : 0 < σ ∧ σ < T) :
    ∃ _R : HuRestartData T u σ, True := by
  classical
  obtain ⟨a0, M, hM, ha0, a, src, offset, hτ, hagree_nhd⟩ :=
    Hu.exists_data σ hσ.1 hσ.2
  refine ⟨?_, trivial⟩
  exact
    { a0 := a0
      M := M
      hM := hM
      ha0 := ha0
      a := a
      src := src
      offset := offset
      hτ := hτ
      hagree_nhd := hagree_nhd }

/-- Choose a restart chart from `Hu.exists_data` at an interior time. -/
noncomputable def huRestartData
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (Hu : HasTimeNeighborhoodSpectralAgreement T u)
    (σ : ℝ) (hσ : 0 < σ ∧ σ < T) :
    HuRestartData T u σ :=
  Classical.choose (huRestartData_exists Hu σ hσ)

/-- Canonical coefficients chosen from the u-side spectral agreement at each
interior time; outside `(0,T)` the value is harmlessly set to zero. -/
noncomputable def huRestartCoeff
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (Hu : HasTimeNeighborhoodSpectralAgreement T u)
    (σ : ℝ) (n : ℕ) : ℝ :=
  if hσ : 0 < σ ∧ σ < T then
    let R := huRestartData Hu σ hσ
    localRestartCoeff R.a0 R.a (σ - R.offset) n
  else 0

/-- The coefficients selected from `Hu` represent the lifted solution on
`[0,1]` at every interior time. -/
theorem huRestartCoeff_agree
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (Hu : HasTimeNeighborhoodSpectralAgreement T u) :
    ∀ σ, 0 < σ → σ < T →
      Set.EqOn (intervalDomainLift (u σ))
        (fun x => ∑' n, huRestartCoeff Hu σ n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1) := by
  intro σ hσ0 hσT x hx
  let hσ : 0 < σ ∧ σ < T := ⟨hσ0, hσT⟩
  let R := huRestartData Hu σ hσ
  have hpoint :
      u σ ⟨x, hx⟩ =
        ∑' n, localRestartCoeff R.a0 R.a (σ - R.offset) n * cosineMode n x := by
    simpa [R] using R.hagree_nhd.self_of_nhds ⟨x, hx⟩
  calc
    intervalDomainLift (u σ) x = u σ ⟨x, hx⟩ := by
      simp [intervalDomainLift, hx]
    _ = ∑' n, localRestartCoeff R.a0 R.a (σ - R.offset) n * cosineMode n x :=
      hpoint
    _ = ∑' n, huRestartCoeff Hu σ n * cosineMode n x := by
      refine tsum_congr (fun n => ?_)
      simp [huRestartCoeff, hσ, R]

/-- The `Hu`-chosen coefficients have the eigenvalue-weighted summability needed
by the cosine derivative-transfer lemmas at each interior time. -/
theorem huRestartCoeff_hbsum
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (Hu : HasTimeNeighborhoodSpectralAgreement T u) :
    ∀ σ, 0 < σ → σ < T →
      Summable (fun n => unitIntervalCosineEigenvalue n * |huRestartCoeff Hu σ n|) := by
  intro σ hσ0 hσT
  let hσ : 0 < σ ∧ σ < T := ⟨hσ0, hσT⟩
  let R := huRestartData Hu σ hσ
  have hsum :=
    ShenWork.IntervalResolverSpectralJointC2Producer.localRestartCoeff_eigenvalue_summable
      (τ := σ - R.offset) (M := R.M) (a₀ := R.a0) (a := R.a)
      R.hτ R.ha0 R.src
  simpa [huRestartCoeff, hσ, R] using hsum

/-- Resolver-source primitive inputs after deleting the `bc/hagree` fields:
they are supplied canonically by `HasTimeNeighborhoodSpectralAgreement`.  The
remaining coefficient envelope and power-source K1 data are still honest inputs. -/
structure ResolverSourceWindowHuCoeffInputs
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u) where
  henv : ∀ a b, 0 < a → b < D.T → a ≤ b →
    ∃ E : ℕ → ℝ,
      Summable E ∧
      (∀ n, 0 ≤ E n) ∧
      (∀ σ ∈ Set.Icc a b, ∀ n,
        unitIntervalCosineEigenvalue n * |huRestartCoeff Hu σ n| ≤ E n)
  adotPow : ℝ → ℕ → ℝ
  hderivPow : ∀ σ, 0 < σ → σ < D.T → ∀ n,
    HasDerivAt
      (fun r => cosineCoeffs
        (fun x => p.ν * intervalDomainLift (D.u r) x ^ p.γ) n)
      (adotPow σ n) σ
  hadotPowCont : ∀ n, ContinuousOn (fun σ => adotPow σ n) (Set.Ioo 0 D.T)
  hMdotPow : ∀ a b, 0 < a → b < D.T →
    ∃ Mdot, ∀ σ ∈ Set.Icc a b, ∀ n, |adotPow σ n| ≤ Mdot

/-- Fill the Task268 envelope/no-joint resolver-source package from the thinner
Hu-coefficient input surface. -/
def resolverSourceWindowEnvelopeOnlyNoJointInputs_of_huCoeffInputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    {Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u}
    (H : ResolverSourceWindowHuCoeffInputs p D Hu) :
    ResolverSourceWindowEnvelopeOnlyNoJointInputs p D where
  bc := huRestartCoeff Hu
  hagree := huRestartCoeff_agree Hu
  henv := H.henv
  adotPow := H.adotPow
  hderivPow := H.hderivPow
  hadotPowCont := H.hadotPowCont
  hMdotPow := H.hMdotPow

/-- Hu-coefficient inputs produce the Task246 resolver-source window data via
the Task268 envelope/no-joint surface. -/
theorem resolverSourceWindowData_of_huCoeffInputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    {Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u}
    (H : ResolverSourceWindowHuCoeffInputs p D Hu) :
    ShenWork.Paper2.ResolverSourceWitnessFrontier.ResolverSourceWindowData p D :=
  resolverSourceWindowData_of_envelopeOnlyNoJointInputs Hu
    (resolverSourceWindowEnvelopeOnlyNoJointInputs_of_huCoeffInputs H)

/-- Hu-coefficient inputs also produce the raw clamped resolver-source witness. -/
theorem resolverSourceWitness_of_huCoeffInputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    {Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u}
    (H : ResolverSourceWindowHuCoeffInputs p D Hu) :
    ShenWork.Paper2.ResolverSourceWitnessFrontier.ResolverSourceWitness p D :=
  resolverSourceWitness_of_envelopeOnlyNoJointInputs Hu
    (resolverSourceWindowEnvelopeOnlyNoJointInputs_of_huCoeffInputs H)

end ShenWork.Paper2.ResolverSourceWindowInput
