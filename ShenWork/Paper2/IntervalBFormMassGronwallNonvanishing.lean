import ShenWork.PDE.IntervalDuhamelCoeffFTC
import ShenWork.Paper2.IntervalBFormSpectralHtime
import ShenWork.Paper2.IntervalDomainL2UniquenessCertificate

open Set
open scoped Topology

noncomputable section

namespace ShenWork.Paper2

open ShenWork.IntervalDomain (intervalDomain intervalDomainPoint)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalBFormSpectral (bFormSourceCoeffs)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs)

/-- Scalar lower-Gronwall nonvanishing.  If `A' ≥ -C A` on `(0,T)` in
right-derivative form and `A 0 > 0`, then `A` cannot vanish on `[0,T]`. -/
theorem positive_of_hasDerivWithinAt_ge_neg_mul
    {A A' : ℝ → ℝ} {T C : ℝ}
    (hcont : ContinuousOn A (Icc (0 : ℝ) T))
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt A (A' t) (Ici t) t)
    (hlower : ∀ t ∈ Ico (0 : ℝ) T, -C * A t ≤ A' t)
    (hA0 : 0 < A 0) :
    ∀ t, 0 ≤ t → t ≤ T → 0 < A t := by
  intro t ht0 htT
  rcases eq_or_lt_of_le ht0 with rfl | htpos
  · exact hA0
  have hcont_neg : ContinuousOn (fun r => -A r) (Icc (0 : ℝ) t) :=
    hcont.neg.mono (fun r hr => ⟨hr.1, le_trans hr.2 htT⟩)
  have hderiv_neg :
      ∀ r ∈ Ico (0 : ℝ) t,
        HasDerivWithinAt (fun q => -A q) (-A' r) (Ici r) r := by
    intro r hr
    exact (hderiv r ⟨hr.1, lt_of_lt_of_le hr.2 htT⟩).neg
  have hbound_neg :
      ∀ r ∈ Ico (0 : ℝ) t, -A' r ≤ (-C) * (-A r) := by
    intro r hr
    calc
      -A' r ≤ C * A r := by
        linarith [hlower r ⟨hr.1, lt_of_lt_of_le hr.2 htT⟩]
      _ = (-C) * (-A r) := by ring
  have hgr :=
    intervalDomainL2_gronwall_exp_of_diffIneq
      (E := fun r => -A r) (E' := fun r => -A' r) (K := -C)
      (s := 0) (t := t) ht0 hcont_neg hderiv_neg hbound_neg
  have hright_neg : (-A 0) * Real.exp ((-C) * (t - 0)) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) (Real.exp_pos _)
  have hneg : -A t < 0 := lt_of_le_of_lt hgr hright_neg
  linarith

/-- Zeroth restart coefficient stays positive under the B-form mass lower
bound.  The interior coefficient ODE is supplied by
`IntervalDuhamelCoeffFTC.localRestartCoeff_hasDerivAt_of_contSource_relative`;
the endpoint right derivative is kept as a separate input. -/
theorem restartCoeff_zeroMode_positive_of_source_lower
    {aInit : ℕ → ℝ} {src : ℝ → ℕ → ℝ} {T C : ℝ}
    (hAcont : ContinuousOn
      (fun t => localRestartCoeff aInit src t 0) (Icc (0 : ℝ) T))
    (hsrcCont : ContinuousOn (fun t => src t 0) (Icc (0 : ℝ) T))
    (hderiv0 : HasDerivWithinAt
      (fun t => localRestartCoeff aInit src t 0) (src 0 0) (Ici 0) 0)
    (hsrcLower : ∀ t ∈ Ico (0 : ℝ) T,
      -C * localRestartCoeff aInit src t 0 ≤ src t 0)
    (hinit : 0 < aInit 0) :
    ∀ t, 0 ≤ t → t ≤ T → 0 < localRestartCoeff aInit src t 0 := by
  let A : ℝ → ℝ := fun t => localRestartCoeff aInit src t 0
  have hA0 : 0 < A 0 := by
    simpa [A, localRestartCoeff,
      ShenWork.IntervalDuhamelClosedC2.duhamelSpectralCoeff,
      unitIntervalCosineEigenvalue] using hinit
  have hderiv : ∀ t ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt A (src t 0) (Ici t) t := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | htpos
    · simpa [A] using hderiv0
    · have hd :=
        ShenWork.IntervalDuhamelCoeffFTC.localRestartCoeff_hasDerivAt_of_contSource_relative
          (a₀ := aInit) (a := src) (T := T) htpos ht.2 0 hsrcCont
      simpa [A, unitIntervalCosineEigenvalue] using hd.hasDerivWithinAt
  exact positive_of_hasDerivWithinAt_ge_neg_mul
    (A := A) (A' := fun t => src t 0) (T := T) (C := C)
    (by simpa [A] using hAcont) hderiv
    (by simpa [A] using hsrcLower) hA0

/-- A5 mass Gronwall nonvanishing for a truncated B-form mild profile once its
mass is identified with the zeroth restart coefficient.  The `hchem0` input is
the Neumann-flux cancellation of the chemotaxis divergence zero mode; `hlogLower`
is the logistic bound, typically with `C = |p.a| + p.b * R ^ p.α`
(`p.α` is the paper exponent minus one in this formalization). -/
theorem truncatedBForm_mass_nonvanishing
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ} {aInit : ℕ → ℝ} {T C : ℝ}
    (hmassCoeff : ∀ t, 0 ≤ t → t ≤ T →
      intervalDomain.integral (u t) =
        localRestartCoeff aInit (bFormSourceCoeffs p u) t 0)
    (hAcont : ContinuousOn
      (fun t => localRestartCoeff aInit (bFormSourceCoeffs p u) t 0)
      (Icc (0 : ℝ) T))
    (hsrcCont : ContinuousOn
      (fun t => bFormSourceCoeffs p u t 0) (Icc (0 : ℝ) T))
    (hderiv0 : HasDerivWithinAt
      (fun t => localRestartCoeff aInit (bFormSourceCoeffs p u) t 0)
      (bFormSourceCoeffs p u 0 0) (Ici 0) 0)
    (hinitCoeff : aInit 0 = intervalDomain.integral u₀)
    (hinitMass : 0 < intervalDomain.integral u₀)
    (hchem0 : ∀ t ∈ Ico (0 : ℝ) T,
      coupledChemDivSourceCoeffs p u t 0 = 0)
    (hlogLower : ∀ t ∈ Ico (0 : ℝ) T,
      -C * localRestartCoeff aInit (bFormSourceCoeffs p u) t 0 ≤
        coupledLogisticSourceCoeffs p u t 0) :
    ∀ t, 0 < t → t ≤ T → 0 < intervalDomain.integral (u t) := by
  have hsrcLower : ∀ t ∈ Ico (0 : ℝ) T,
      -C * localRestartCoeff aInit (bFormSourceCoeffs p u) t 0 ≤
        bFormSourceCoeffs p u t 0 := by
    intro t ht
    simpa [bFormSourceCoeffs, hchem0 t ht] using hlogLower t ht
  have hposCoeff :=
    restartCoeff_zeroMode_positive_of_source_lower
      (aInit := aInit) (src := bFormSourceCoeffs p u) (T := T) (C := C)
      hAcont hsrcCont hderiv0 hsrcLower (by
        rw [hinitCoeff]
        exact hinitMass)
  intro t ht htT
  rw [hmassCoeff t ht.le htT]
  exact hposCoeff t ht.le htT

end ShenWork.Paper2
