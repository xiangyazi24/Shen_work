/-
  B-form spectral PDE: cosine inversion for the chemotaxis divergence source.

  This file discharges the pointwise Fourier-convergence input for the B-form
  interior PDE.  The analytic regularity is carried as named, satisfiable data:
  a continuous representative that agrees with the physical interval source on
  `[0,1]`, plus summability of its even-reflection Fourier coefficients.

  Proof-only file; no extra assumptions are introduced.
-/
import ShenWork.PDE.IntervalDomainContinuousExtension
import ShenWork.PDE.IntervalCosineInversion
import ShenWork.PDE.IntervalCoupledSourceTimeC1

open Set

noncomputable section

namespace ShenWork.IntervalBFormSpectral

open ShenWork.IntervalDomain
  (intervalDomainPoint intervalDomainLift intervalDomainConstExtend
   intervalDomainChemotaxisDiv)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalCosineInversion
  (intervalCosine_hasSum_pointwise reflCircle)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceLift coupledChemDivSourceCoeffs
   coupledLogisticSourceLift coupledLogisticSourceCoeffs)

/-- The lifted physical chemotaxis-divergence slice on `[0,1]`, extended by zero
outside through `intervalDomainLift`. -/
def chemDivLift (p : CM2Params) (u v : intervalDomainPoint → ℝ) : ℝ → ℝ :=
  intervalDomainLift (fun x => intervalDomainChemotaxisDiv p u v x)

/-- Cosine coefficients of the lifted physical chemotaxis-divergence slice. -/
def chemDivCoeffs (p : CM2Params) (u v : intervalDomainPoint → ℝ) : ℕ → ℝ :=
  fun n => cosineCoeffs (chemDivLift p u v) n

/-- Named regularity package sufficient for pointwise cosine inversion of a
chemotaxis-divergence slice.  A typical witness is the constant extension of the
physical interval source, with the Fourier summability obtained from the usual
closed-interval `C²`/Neumann or weak-H² data. -/
structure ChemDivCosineFourierData
    (p : CM2Params) (u v : intervalDomainPoint → ℝ) where
  representative : ℝ → ℝ
  continuous_representative : Continuous representative
  representative_eq_chemDiv :
    Set.EqOn representative (chemDivLift p u v) (Set.Icc (0 : ℝ) 1)
  fourier_summable :
    Summable (fun n : ℤ => fourierCoeff (reflCircle representative) n)

/-- The constant-extension form of the chem-div regularity package. -/
def chemDivCosineFourierData_constExtend
    (p : CM2Params) (u v : intervalDomainPoint → ℝ)
    (hcont : Continuous
      (intervalDomainConstExtend (fun x => intervalDomainChemotaxisDiv p u v x)))
    (hsum : Summable (fun n : ℤ =>
      fourierCoeff
        (reflCircle
          (intervalDomainConstExtend
            (fun x => intervalDomainChemotaxisDiv p u v x))) n)) :
    ChemDivCosineFourierData p u v where
  representative :=
    intervalDomainConstExtend (fun x => intervalDomainChemotaxisDiv p u v x)
  continuous_representative := hcont
  representative_eq_chemDiv := by
    intro y hy
    exact ShenWork.IntervalDomain.constExtend_eq_lift_on_Icc hy
  fourier_summable := hsum

private theorem chemDiv_coeff_eq_representative
    {p : CM2Params} {u v : intervalDomainPoint → ℝ}
    (H : ChemDivCosineFourierData p u v) (n : ℕ) :
    chemDivCoeffs p u v n = cosineCoeffs H.representative n := by
  exact ShenWork.Paper2.cosineCoeffs_congr_on_Icc
    (fun y hy => (H.representative_eq_chemDiv hy).symm) n

/-- Summability of the chem-div cosine series at an interior point, from the
named regularity package. -/
theorem chemDiv_cosineSeries_summable
    {p : CM2Params} {u v : intervalDomainPoint → ℝ}
    (H : ChemDivCosineFourierData p u v)
    {x : intervalDomainPoint} (hx : x.1 ∈ Set.Ioo (0 : ℝ) 1) :
    Summable (fun n => chemDivCoeffs p u v n * cosineMode n x.1) := by
  have hinv := intervalCosine_hasSum_pointwise H.representative
    H.continuous_representative hx H.fourier_summable
  have hterm :
      (fun n => chemDivCoeffs p u v n * cosineMode n x.1)
        =
      (fun n => unitIntervalCosineMode n x.1
        * cosineCoeffs H.representative n) := by
    funext n
    rw [chemDiv_coeff_eq_representative H n]
    simp only [cosineMode,
      unitIntervalCosineMode]
    ring
  rw [hterm]
  exact hinv.summable

/-- Chemotaxis-divergence cosine Fourier convergence on the open interval. -/
theorem chemDiv_cosineFourier_convergence
    {p : CM2Params} {u v : intervalDomainPoint → ℝ}
    (H : ChemDivCosineFourierData p u v)
    {x : intervalDomainPoint} (hx : x.1 ∈ Set.Ioo (0 : ℝ) 1) :
    (∑' n, chemDivCoeffs p u v n * cosineMode n x.1)
      = intervalDomainChemotaxisDiv p u v x := by
  have hinv := intervalCosine_hasSum_pointwise H.representative
    H.continuous_representative hx H.fourier_summable
  have hsum_eq :
      (∑' n, chemDivCoeffs p u v n * cosineMode n x.1)
        = H.representative x.1 := by
    rw [← hinv.tsum_eq]
    refine tsum_congr (fun n => ?_)
    rw [chemDiv_coeff_eq_representative H n]
    simp only [cosineMode,
      unitIntervalCosineMode]
    ring
  have hxIcc : x.1 ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
  have hrep_x : H.representative x.1 = chemDivLift p u v x.1 :=
    H.representative_eq_chemDiv hxIcc
  have hlift :
      chemDivLift p u v x.1 = intervalDomainChemotaxisDiv p u v x := by
    simp [chemDivLift, intervalDomainLift]
  rw [hsum_eq, hrep_x, hlift]

/-- Coupled B-form chem-div summability, with the elliptic resolver substituted. -/
theorem coupledChemDiv_cosineSeries_summable
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ)
    (H : ChemDivCosineFourierData p (u t) (coupledChemicalConcentration p u t))
    {x : intervalDomainPoint} (hx : x.1 ∈ Set.Ioo (0 : ℝ) 1) :
    Summable (fun n => coupledChemDivSourceCoeffs p u t n * cosineMode n x.1) := by
  simpa [coupledChemDivSourceCoeffs, coupledChemDivSourceLift,
    chemDivCoeffs, chemDivLift] using
    chemDiv_cosineSeries_summable (p := p) (u := u t)
      (v := coupledChemicalConcentration p u t) H hx

/-- Coupled B-form chem-div cosine Fourier convergence, with the resolver written
as the `mildChemicalConcentration` used by the PDE core. -/
theorem coupledChemDiv_cosineFourier_convergence
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ)
    (H : ChemDivCosineFourierData p (u t) (coupledChemicalConcentration p u t))
    {x : intervalDomainPoint} (hx : x.1 ∈ Set.Ioo (0 : ℝ) 1) :
    (∑' n, coupledChemDivSourceCoeffs p u t n * cosineMode n x.1)
      = ShenWork.IntervalDomain.intervalDomain.chemotaxisDiv p (u t)
          (ShenWork.IntervalMildToClassical.mildChemicalConcentration p u t) x := by
  have h := chemDiv_cosineFourier_convergence (p := p) (u := u t)
    (v := coupledChemicalConcentration p u t) H hx
  change
    (∑' n, coupledChemDivSourceCoeffs p u t n * cosineMode n x.1)
      = intervalDomainChemotaxisDiv p (u t)
          (ShenWork.IntervalMildToClassical.mildChemicalConcentration p u t) x
  simpa [coupledChemDivSourceCoeffs, coupledChemDivSourceLift,
    chemDivCoeffs, chemDivLift,
    coupledChemicalConcentration,
    ShenWork.IntervalMildToClassical.mildChemicalConcentration] using h

/-- Named regularity package sufficient for pointwise cosine inversion of the
logistic source coefficients.  This is the reaction-source analogue needed by
the B-form producer. -/
structure LogisticCosineFourierData
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) where
  representative : ℝ → ℝ
  continuous_representative : Continuous representative
  representative_eq_logistic :
    Set.EqOn representative (coupledLogisticSourceLift p u t) (Set.Icc (0 : ℝ) 1)
  fourier_summable :
    Summable (fun n : ℤ => fourierCoeff (reflCircle representative) n)

private theorem logistic_coeff_eq_representative
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {t : ℝ}
    (H : LogisticCosineFourierData p u t) (n : ℕ) :
    coupledLogisticSourceCoeffs p u t n = cosineCoeffs H.representative n := by
  rw [coupledLogisticSourceCoeffs]
  exact ShenWork.Paper2.cosineCoeffs_congr_on_Icc
    (fun y hy => (H.representative_eq_logistic hy).symm) n

/-- Summability of the logistic cosine series at an interior point. -/
theorem coupledLogistic_cosineSeries_summable
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {t : ℝ}
    (H : LogisticCosineFourierData p u t)
    {x : intervalDomainPoint} (hx : x.1 ∈ Set.Ioo (0 : ℝ) 1) :
    Summable (fun n => coupledLogisticSourceCoeffs p u t n * cosineMode n x.1) := by
  have hinv := intervalCosine_hasSum_pointwise H.representative
    H.continuous_representative hx H.fourier_summable
  have hterm :
      (fun n => coupledLogisticSourceCoeffs p u t n * cosineMode n x.1)
        =
      (fun n => unitIntervalCosineMode n x.1
        * cosineCoeffs H.representative n) := by
    funext n
    rw [logistic_coeff_eq_representative H n]
    simp only [cosineMode,
      unitIntervalCosineMode]
    ring
  rw [hterm]
  exact hinv.summable

/-- Logistic source cosine Fourier convergence to the pointwise reaction. -/
theorem coupledLogistic_cosineFourier_convergence
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {t : ℝ}
    (H : LogisticCosineFourierData p u t)
    {x : intervalDomainPoint} (hx : x.1 ∈ Set.Ioo (0 : ℝ) 1) :
    (∑' n, coupledLogisticSourceCoeffs p u t n * cosineMode n x.1)
      = u t x * (p.a - p.b * (u t x) ^ p.α) := by
  have hinv := intervalCosine_hasSum_pointwise H.representative
    H.continuous_representative hx H.fourier_summable
  have hsum_eq :
      (∑' n, coupledLogisticSourceCoeffs p u t n * cosineMode n x.1)
        = H.representative x.1 := by
    rw [← hinv.tsum_eq]
    refine tsum_congr (fun n => ?_)
    rw [logistic_coeff_eq_representative H n]
    simp only [cosineMode,
      unitIntervalCosineMode]
    ring
  have hxIcc : x.1 ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
  have hrep_x : H.representative x.1 = coupledLogisticSourceLift p u t x.1 :=
    H.representative_eq_logistic hxIcc
  have hlift :
      coupledLogisticSourceLift p u t x.1
        = ShenWork.IntervalDomainExistence.intervalLogisticSource p (u t) x := by
    simp [coupledLogisticSourceLift, intervalDomainLift]
  rw [hsum_eq, hrep_x, hlift,
    ShenWork.IntervalDomainExistence.intervalLogisticSource]

#print axioms chemDiv_cosineFourier_convergence
#print axioms coupledChemDiv_cosineFourier_convergence

end ShenWork.IntervalBFormSpectral
