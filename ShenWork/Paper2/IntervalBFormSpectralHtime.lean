/-
  B-form spectral PDE: time-derivative spectral identity.

  The analytic time-differentiation is the committed restart cosine theorem.
  This file specializes it to the B-form source split
  `reaction coefficients - χ₀ * chemDiv coefficients`, keeping the chemotaxis
  term explicitly.

  Proof-only file; no extra assumptions are introduced.
-/
import ShenWork.Paper2.IntervalBFormSpectralHchem
import ShenWork.Paper2.IntervalConjugateDuhamelMap
import ShenWork.PDE.IntervalDuhamelSourceTimeC1On

open Filter Topology

noncomputable section

namespace ShenWork.IntervalBFormSpectral

open ShenWork.IntervalDomain (intervalDomainPoint intervalDomain)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalSourceCoefficientTimeC1
  (localRestartCoeff duhamelSourceTimeC1_const_mul duhamelSourceTimeC1_add)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)

/-- The B-form total source coefficient family:
reaction coefficients minus `χ₀` times chem-div coefficients. -/
def bFormSourceCoeffs (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) : ℝ → ℕ → ℝ :=
  fun s n => coupledLogisticSourceCoeffs p u s n
    - p.χ₀ * coupledChemDivSourceCoeffs p u s n

/-- `DuhamelSourceTimeC1` for the B-form total source, obtained by the committed
addition/scalar-closure of coefficient time-regularity. -/
noncomputable def bFormSource_duhamelSourceTimeC1
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u))
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u)) :
    DuhamelSourceTimeC1 (bFormSourceCoeffs p u) := by
  have hchemScaled :
      DuhamelSourceTimeC1
        (fun s n => (-p.χ₀) * coupledChemDivSourceCoeffs p u s n) :=
    duhamelSourceTimeC1_const_mul hchem (-p.χ₀)
  have hsum :
      DuhamelSourceTimeC1
        (fun s n => coupledLogisticSourceCoeffs p u s n
          + (-p.χ₀) * coupledChemDivSourceCoeffs p u s n) :=
    duhamelSourceTimeC1_add hlog hchemScaled
  convert hsum using 1
  ext s n
  simp [bFormSourceCoeffs]
  ring

/-- `DuhamelSourceTimeC1On` for the B-form total source, obtained by the committed
addition/scalar-closure of coefficient time-regularity on a window `[lo, hi]`. -/
noncomputable def bFormSource_duhamelSourceTimeC1On
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {lo hi : ℝ}
    (hlog : DuhamelSourceTimeC1On (coupledLogisticSourceCoeffs p u) lo hi)
    (hchem : DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p u) lo hi) :
    DuhamelSourceTimeC1On (bFormSourceCoeffs p u) lo hi := by
  have hchemScaled :
      DuhamelSourceTimeC1On
        (fun s n => (-p.χ₀) * coupledChemDivSourceCoeffs p u s n) lo hi :=
    hchem.const_mul (-p.χ₀)
  have hsum :
      DuhamelSourceTimeC1On
        (fun s n => coupledLogisticSourceCoeffs p u s n
          + (-p.χ₀) * coupledChemDivSourceCoeffs p u s n) lo hi :=
    hlog.add hchemScaled
  convert hsum using 1
  ext s n
  simp [bFormSourceCoeffs]
  ring

/-- Time derivative of a B-form restart representation.  The local source family
`a` is allowed to be shifted/clamped; the only required identification is the
slice split at `t₀ - offset`, where it equals the physical B-form source
`reaction - χ₀ * chemDiv` at time `t₀`. -/
theorem bForm_timeDeriv_eq_of_local_restart
    (p : CM2Params)
    {u : ℝ → intervalDomainPoint → ℝ} {t₀ : ℝ}
    {a₀ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M) (ha₀ : ∀ n, |a₀ n| ≤ M)
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {offset : ℝ} (hoff : 0 < t₀ - offset)
    (hrep : ∀ᶠ s in 𝓝 t₀, ∀ y : intervalDomainPoint,
      u s y = ∑' n, localRestartCoeff a₀ a (s - offset) n * cosineMode n y.1)
    (hsource_split : ∀ n, a (t₀ - offset) n
      = coupledLogisticSourceCoeffs p u t₀ n
        - p.χ₀ * coupledChemDivSourceCoeffs p u t₀ n)
    (x : intervalDomainPoint) :
    intervalDomain.timeDeriv u t₀ x
      = ∑' n,
          (coupledLogisticSourceCoeffs p u t₀ n
            - p.χ₀ * coupledChemDivSourceCoeffs p u t₀ n
            - unitIntervalCosineEigenvalue n
              * localRestartCoeff a₀ a (t₀ - offset) n)
            * cosineMode n x.1 := by
  have htime :=
    ShenWork.IntervalDomainPdeUChiZero.timeDeriv_eq_of_rep
      hM ha₀ src hoff hrep x
  rw [htime]
  refine tsum_congr (fun n => ?_)
  rw [hsource_split n]

/-- Same spectral time-derivative identity, stated with the B-form fixed-point
predicate in the hypotheses.  The fixed-point equation supplies the restart
representation upstream; this theorem consumes that representation and performs
the spectral time differentiation. -/
theorem intervalConjugateMildSolution_timeDeriv_spectral_form
    (p : CM2Params) {T : ℝ} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (_hB : ShenWork.IntervalConjugateDuhamelMap.IntervalConjugateMildSolution
      p T u₀ u)
    {t₀ : ℝ}
    {a₀ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M) (ha₀ : ∀ n, |a₀ n| ≤ M)
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {offset : ℝ} (hoff : 0 < t₀ - offset)
    (hrep : ∀ᶠ s in 𝓝 t₀, ∀ y : intervalDomainPoint,
      u s y = ∑' n, localRestartCoeff a₀ a (s - offset) n * cosineMode n y.1)
    (hsource_split : ∀ n, a (t₀ - offset) n
      = coupledLogisticSourceCoeffs p u t₀ n
        - p.χ₀ * coupledChemDivSourceCoeffs p u t₀ n)
    (x : intervalDomainPoint) :
    intervalDomain.timeDeriv u t₀ x
      = ∑' n,
          (coupledLogisticSourceCoeffs p u t₀ n
            - p.χ₀ * coupledChemDivSourceCoeffs p u t₀ n
            - unitIntervalCosineEigenvalue n
              * localRestartCoeff a₀ a (t₀ - offset) n)
            * cosineMode n x.1 :=
  bForm_timeDeriv_eq_of_local_restart p hM ha₀ src hoff hrep hsource_split x

#print axioms bForm_timeDeriv_eq_of_local_restart
#print axioms intervalConjugateMildSolution_timeDeriv_spectral_form

end ShenWork.IntervalBFormSpectral
