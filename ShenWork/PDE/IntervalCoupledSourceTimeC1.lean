import ShenWork.PDE.IntervalCoupledRegularityBootstrap
import ShenWork.PDE.IntervalSourceCoefficientTimeC1
import ShenWork.PDE.IntervalSemigroupNeumann

open ShenWork.IntervalDomain
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalSemigroupNeumann
open ShenWork.IntervalSourceCoefficientTimeC1
open ShenWork.PDE.IntervalMildSourceDecayHelper

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

/-- Lifted chemotaxis-divergence source with the elliptic resolver substituted. -/
def coupledChemDivSourceLift (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (s : ℝ) : ℝ → ℝ :=
  intervalDomainLift
    (fun x => intervalDomainChemotaxisDiv p (u s)
      (coupledChemicalConcentration p u s) x)

/-- Cosine coefficients of the chemotaxis-divergence source. -/
def coupledChemDivSourceCoeffs (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) : ℝ → ℕ → ℝ :=
  fun s n => cosineCoeffs (coupledChemDivSourceLift p u s) n

/-- Lifted logistic source. -/
def coupledLogisticSourceLift (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (s : ℝ) : ℝ → ℝ :=
  intervalDomainLift
    (ShenWork.IntervalDomainExistence.intervalLogisticSource p (u s))

/-- Cosine coefficients of the logistic source. -/
def coupledLogisticSourceCoeffs (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) : ℝ → ℕ → ℝ :=
  fun s n => cosineCoeffs (coupledLogisticSourceLift p u s) n

/-- Lifted full chemotaxis-logistic source with the elliptic resolver substituted. -/
def coupledChemicalSourceLift (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (s : ℝ) : ℝ → ℝ :=
  intervalDomainLift
    (ShenWork.IntervalDomainExistence.intervalCoupledSource p (u s)
      (coupledChemicalConcentration p u s))

/-- Cosine coefficients of the coupled chemotaxis-logistic source. -/
def coupledChemicalSourceCoeffs (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) : ℝ → ℕ → ℝ :=
  fun s n => cosineCoeffs (coupledChemicalSourceLift p u s) n

/-- Chemotaxis-divergence source `DuhamelSourceTimeC1` from raw H²/time-C¹ data. -/
noncomputable def coupledChemDivSource_duhamelSourceTimeC1
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hH2 : ∀ s, 0 ≤ s →
      IntervalWeakH2Neumann (coupledChemDivSourceLift p u s))
    {C : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ s, 0 ≤ s → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (coupledChemDivSourceLift p u s) k|
        ≤ C / ((k : ℝ) * Real.pi) ^ 2)
    (ha0 : ∀ s, 0 ≤ s →
      |cosineCoeffs (coupledChemDivSourceLift p u s) 0| ≤ C)
    {adot : ℝ → ℕ → ℝ}
    (hderiv : ∀ s n,
      HasDerivAt
        (fun r => cosineCoeffs (coupledChemDivSourceLift p u r) n)
        (adot s n) s)
    (hadotcont : ∀ n, Continuous (fun s => adot s n))
    {Mdot : ℝ}
    (hMdot : ∀ s, 0 ≤ s → ∀ n, |adot s n| ≤ Mdot) :
    DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u) := by
  simpa [coupledChemDivSourceCoeffs] using
    duhamelSourceTimeC1_of_H2Neumann_timeC1 hH2 hC hdecay hderiv
      hadotcont hMdot ha0

/-- Coupled source `DuhamelSourceTimeC1` by scaling chem-div and adding logistic. -/
noncomputable def coupledChemicalSource_duhamelSourceTimeC1
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u))
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u))
    (hsplit : coupledChemicalSourceCoeffs p u =
      fun s n => -(p.χ₀ * coupledChemDivSourceCoeffs p u s n)
        + coupledLogisticSourceCoeffs p u s n) :
    DuhamelSourceTimeC1 (coupledChemicalSourceCoeffs p u) := by
  have hchemScaled :
      DuhamelSourceTimeC1
        (fun s n => (-p.χ₀) * coupledChemDivSourceCoeffs p u s n) :=
    duhamelSourceTimeC1_const_mul hchem (-p.χ₀)
  have hsum :
      DuhamelSourceTimeC1
        (fun s n => -(p.χ₀ * coupledChemDivSourceCoeffs p u s n)
          + coupledLogisticSourceCoeffs p u s n) := by
    simpa using
      duhamelSourceTimeC1_add hchemScaled hlog
  rw [hsplit]
  exact hsum

end ShenWork.IntervalCoupledRegularityBootstrap
