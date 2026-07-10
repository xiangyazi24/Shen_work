import ShenWork.Paper2.IntervalBFormCron2CoefficientWeakTest
import ShenWork.Paper2.IntervalBFormCron2RegularNegativePartEnergyA3
import ShenWork.Paper2.IntervalChiNegFinalAssemblyV4
import ShenWork.Paper2.IntervalChiNegTruncatedRestartStrictPosProducer

open MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section

namespace ShenWork.Paper2.Batch2RemainingSubfields

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalMeasure
   intervalMeasure_integrable_of_abs_bound)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalMildPicardThreshold (unitClip)
open ShenWork.Paper2.BFormPositiveDatumNegPart
open ShenWork.Paper2.IntervalChiNegFinalAssemblyV4

/-! ## A1: remaining tested-series fields. -/

/-- Time `tsum` Leibniz for the tested scalar spectral series.  This is the
field-level alias used by the coefficient weak-test record. -/
theorem time_leibniz_tsum
    {t : ℝ} (ht : 0 < t) {a : ℕ → ℝ} {φ : ℝ → ℝ} {M : ℝ}
    (hM : ∀ n, |a n * cosineTestCoeff φ n| ≤ M) :
    HasDerivAt (fun s : ℝ => spectralTestPairing a φ s)
      (spectralTestLaplacianPairing a φ t) t :=
  spectralTestPairing_hasDerivAt ht hM

/-- Convert a differentiated tested pairing into the exact field
`time_leibniz_tsum` of `NegativePartCoefficientWeakTestData`. -/
theorem time_leibniz_tsum_field
    {u : ℝ → intervalDomainPoint → ℝ} {t : ℝ}
    {coeffTimeDeriv : ℕ → ℝ}
    (h :
      (∫ x,
          intervalDomainLift
              (fun z : intervalDomainPoint =>
                ShenWork.IntervalDomain.intervalDomain.timeDeriv u t z) x *
            negativePartTest u t x
          ∂ intervalMeasure 1)
        =
      ∑' k : ℕ,
        coeffTimeDeriv k * cosineTestCoeff (negativePartTest u t) k) :
    (∫ x,
        intervalDomainLift
            (fun z : intervalDomainPoint =>
              ShenWork.IntervalDomain.intervalDomain.timeDeriv u t z) x *
          negativePartTest u t x
        ∂ intervalMeasure 1)
      =
    ∑' k : ℕ,
      coeffTimeDeriv k * cosineTestCoeff (negativePartTest u t) k :=
  h

/-- Full-series gradient IBP after the spatial derivative has already been
interchanged with the cosine series.  The remaining step is the single-mode
Neumann IBP `∫ e'_k φ' = λ_k ∫ e_k φ`. -/
theorem gradient_ibp_tsum
    {G : ℝ} {a : ℕ → ℝ} {φ φ' : ℝ → ℝ}
    (hseries :
      G =
        ∑' k : ℕ,
          a k * (∫ x in (0 : ℝ)..1, deriv (cosineMode k) x * φ' x))
    (hφ : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt φ (φ' x) x)
    (hφ'_int : IntervalIntegrable φ' volume (0 : ℝ) 1) :
    G =
      ∑' k : ℕ,
        unitIntervalCosineEigenvalue k * a k * cosineTestCoeff φ k := by
  calc
    G =
        ∑' k : ℕ,
          a k * (∫ x in (0 : ℝ)..1, deriv (cosineMode k) x * φ' x) :=
      hseries
    _ =
      ∑' k : ℕ,
        unitIntervalCosineEigenvalue k * a k * cosineTestCoeff φ k := by
      refine tsum_congr fun k => ?_
      rw [cosineMode_gradient_testCoeff_eq k hφ hφ'_int]
      ring

/-- Source pairing assembly from separate weighted Parseval identities for the
chemotaxis and logistic source parts. -/
theorem source_pairing
    {p : CM2Params} {sourceCoeff chemCoeff logCoeff φhat : ℕ → ℝ}
    {chemIntegral logIntegral : ℝ}
    (hsource :
      ∀ k,
        sourceCoeff k * φhat k =
          p.χ₀ * chemCoeff k * φhat k + logCoeff k * φhat k)
    (hchem_sum : Summable (fun k : ℕ => p.χ₀ * chemCoeff k * φhat k))
    (hlog_sum : Summable (fun k : ℕ => logCoeff k * φhat k))
    (hchem :
      (∑' k : ℕ, p.χ₀ * chemCoeff k * φhat k) =
        p.χ₀ * chemIntegral)
    (hlog : (∑' k : ℕ, logCoeff k * φhat k) = logIntegral) :
    (∑' k : ℕ, sourceCoeff k * φhat k)
      = p.χ₀ * chemIntegral + logIntegral := by
  calc
    (∑' k : ℕ, sourceCoeff k * φhat k)
        =
      ∑' k : ℕ,
        (p.χ₀ * chemCoeff k * φhat k + logCoeff k * φhat k) := by
        exact tsum_congr hsource
    _ =
      (∑' k : ℕ, p.χ₀ * chemCoeff k * φhat k)
        + (∑' k : ℕ, logCoeff k * φhat k) := by
        exact Summable.tsum_add hchem_sum hlog_sum
    _ = p.χ₀ * chemIntegral + logIntegral := by
        rw [hchem, hlog]

/-- Constructor for the A1 coefficient weak-test record once Batch 1 supplies
the ODE and summability fields and this file supplies the three tested-pairing
fields. -/
def coefficientWeakTestData_of_remaining_subfields
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {t : ℝ}
    (coeff coeffTimeDeriv sourceCoeff : ℕ → ℝ)
    (coeff_ode :
      ∀ k, coeffTimeDeriv k =
        -unitIntervalCosineEigenvalue k * coeff k + sourceCoeff k)
    (lap_summable :
      Summable (fun k : ℕ =>
        unitIntervalCosineEigenvalue k * coeff k *
          cosineTestCoeff (negativePartTest u t) k))
    (source_summable :
      Summable (fun k : ℕ =>
        sourceCoeff k * cosineTestCoeff (negativePartTest u t) k))
    (time_leibniz_tsum :
      (∫ x,
          intervalDomainLift
              (fun z : intervalDomainPoint =>
                ShenWork.IntervalDomain.intervalDomain.timeDeriv u t z) x *
            negativePartTest u t x
          ∂ intervalMeasure 1)
        =
      ∑' k : ℕ,
        coeffTimeDeriv k * cosineTestCoeff (negativePartTest u t) k)
    (gradient_ibp_tsum :
      (∫ x,
          deriv (intervalDomainLift (u t)) x * deriv (negativePartTest u t) x
          ∂ intervalMeasure 1)
        =
      ∑' k : ℕ, unitIntervalCosineEigenvalue k * coeff k *
        cosineTestCoeff (negativePartTest u t) k)
    (source_pairing :
      (∑' k : ℕ, sourceCoeff k * cosineTestCoeff (negativePartTest u t) k)
        =
      p.χ₀ *
        (∫ x,
          truncatedChemFluxLifted p (u t) x *
            deriv (negativePartTest u t) x
          ∂ intervalMeasure 1)
        + (∫ x,
            truncatedLogisticLifted p (u t) x * negativePartTest u t x
            ∂ intervalMeasure 1)) :
    NegativePartCoefficientWeakTestData p u t where
  coeff := coeff
  coeffTimeDeriv := coeffTimeDeriv
  sourceCoeff := sourceCoeff
  coeff_ode := coeff_ode
  lap_summable := lap_summable
  source_summable := source_summable
  time_leibniz_tsum := time_leibniz_tsum
  gradient_ibp_tsum := gradient_ibp_tsum
  source_pairing := source_pairing

/-! ## A2: negative-part chain and integrability fields. -/

/-- Derivative of `r ↦ r_-` vanishes at points where the underlying function is
strictly positive. -/
theorem neg_deriv_zero_on_pos
    {μ : Measure ℝ} {w : ℝ → ℝ}
    (hw_cont : ∀ᵐ x ∂ μ, ContinuousAt w x) :
    ∀ᵐ x ∂ μ, 0 < w x →
      deriv (fun y : ℝ => negativePart (w y)) x = 0 := by
  filter_upwards [hw_cont] with x hx hpos
  exact deriv_negativePartLift_eq_zero_of_pos hx hpos

/-- Lifted interval version of `neg_deriv_zero_on_pos`. -/
theorem neg_deriv_zero_on_pos_lift
    {w : intervalDomainPoint → ℝ}
    (hw_cont :
      ∀ᵐ x ∂ intervalMeasure 1, ContinuousAt (intervalDomainLift w) x) :
    ∀ᵐ x ∂ intervalMeasure 1,
      0 < intervalDomainLift w x → deriv (negativePartLift w) x = 0 := by
  simpa [negativePartLift] using
    neg_deriv_zero_on_pos (μ := intervalMeasure 1)
      (w := intervalDomainLift w) hw_cont

/-- Algebraic form of the time chain rule:
`E' = 2 I` is equivalent to the A2 field `I = (1/2) E'`. -/
theorem time_chain {I E' : ℝ} (hE : E' = 2 * I) :
    I = (1 / 2 : ℝ) * E' := by
  nlinarith

/-- A2 time-chain field specialized to the negative-part test. -/
theorem time_chain_field
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T t E't : ℝ}
    (hE :
      E't =
        2 *
          (∫ x,
            intervalDomainLift
                (fun z : intervalDomainPoint =>
                  ShenWork.IntervalDomain.intervalDomain.timeDeriv
                    (truncatedConjugatePicardLimit p u₀ T) t z) x *
              negativePartTest (truncatedConjugatePicardLimit p u₀ T) t x
            ∂ intervalMeasure 1)) :
    (∫ x,
        intervalDomainLift
            (fun z : intervalDomainPoint =>
              ShenWork.IntervalDomain.intervalDomain.timeDeriv
                (truncatedConjugatePicardLimit p u₀ T) t z) x *
          negativePartTest (truncatedConjugatePicardLimit p u₀ T) t x
        ∂ intervalMeasure 1)
      = (1 / 2 : ℝ) * E't :=
  time_chain hE

/-- Diffusion-chain field from the a.e. pointwise identity of the two
integrands. -/
theorem diffusion_chain
    {u : ℝ → intervalDomainPoint → ℝ} {t : ℝ}
    (h :
      (fun x =>
        deriv (intervalDomainLift (u t)) x * deriv (negativePartTest u t) x)
        =ᵐ[intervalMeasure 1]
      fun x => (deriv (negativePartLift (u t)) x) ^ 2) :
    (∫ x,
        deriv (intervalDomainLift (u t)) x * deriv (negativePartTest u t) x
        ∂ intervalMeasure 1)
      = negativePartDissipation u t := by
  unfold negativePartDissipation
  exact MeasureTheory.integral_congr_ae h

/-- Nonnegativity of the squared-gradient dissipation. -/
theorem diffusion_nonneg
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) :
    0 ≤ negativePartDissipation u t := by
  unfold negativePartDissipation
  exact MeasureTheory.integral_nonneg_of_ae
    (Eventually.of_forall fun x => sq_nonneg (deriv (negativePartLift (u t)) x))

/-- Bounded measurable logistic-tested source is integrable on `[0,1]`. -/
theorem logistic_integrable
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {t M : ℝ}
    (hmeas :
      AEStronglyMeasurable
        (fun x =>
          truncatedLogisticLifted p (u t) x * negativePartTest u t x)
        (intervalMeasure 1))
    (hbound :
      ∀ x,
        |truncatedLogisticLifted p (u t) x * negativePartTest u t x| ≤ M) :
    Integrable
      (fun x =>
        truncatedLogisticLifted p (u t) x * negativePartTest u t x)
      (intervalMeasure 1) :=
  intervalMeasure_integrable_of_abs_bound hmeas hbound

/-- Energy integrability from the existing continuous bounded-slice lemma. -/
theorem energy_integrable_of_continuous_bound
    {w : intervalDomainPoint → ℝ} {R : ℝ}
    (hwcont : Continuous w) (hR : 0 ≤ R)
    (hwbound : ∀ x, |w x| ≤ R) :
    Integrable (fun x => (negativePartLift w x) ^ 2) (intervalMeasure 1) :=
  negativePart_sq_integrable_of_continuous_bound hwcont hR hwbound

/-- Constructor for the A2 estimate record from the five chain/integrability
sub-fields plus the squared negative-part integrability field. -/
def A2Data_of_remaining_subfields
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T : ℝ}
    {E' : ℝ → ℝ}
    (neg_deriv_zero_on_pos :
      ∀ t, 0 < t → t ≤ T →
        ∀ᵐ x ∂ intervalMeasure 1,
          0 < intervalDomainLift
              (truncatedConjugatePicardLimit p u₀ T t) x →
            deriv (negativePartLift
              (truncatedConjugatePicardLimit p u₀ T t)) x = 0)
    (time_chain :
      ∀ t, 0 < t → t ≤ T →
        (∫ x,
            intervalDomainLift
                (fun z : intervalDomainPoint =>
                  ShenWork.IntervalDomain.intervalDomain.timeDeriv
                    (truncatedConjugatePicardLimit p u₀ T) t z) x *
              negativePartTest (truncatedConjugatePicardLimit p u₀ T) t x
            ∂ intervalMeasure 1)
          = (1 / 2 : ℝ) * E' t)
    (diffusion_chain :
      ∀ t, 0 < t → t ≤ T →
        (∫ x,
            deriv (intervalDomainLift
              (truncatedConjugatePicardLimit p u₀ T t)) x *
              deriv (negativePartTest
                (truncatedConjugatePicardLimit p u₀ T) t) x
            ∂ intervalMeasure 1)
          =
        negativePartDissipation (truncatedConjugatePicardLimit p u₀ T) t)
    (logistic_integrable :
      ∀ t, 0 < t → t ≤ T →
        Integrable
          (fun x =>
            truncatedLogisticLifted p
                (truncatedConjugatePicardLimit p u₀ T t) x *
              negativePartTest (truncatedConjugatePicardLimit p u₀ T) t x)
          (intervalMeasure 1))
    (energy_integrable :
      ∀ t, 0 < t → t ≤ T →
        Integrable
          (fun x =>
            (negativePartLift
              (truncatedConjugatePicardLimit p u₀ T t) x) ^ 2)
          (intervalMeasure 1)) :
    TruncatedPicardNegativePartEnergyEstimateA2Data
      p (u₀ := u₀) T E' where
  neg_deriv_zero_on_pos := neg_deriv_zero_on_pos
  time_chain := time_chain
  diffusion_chain := diffusion_chain
  diffusion_nonneg := fun t _ _ => diffusion_nonneg
    (truncatedConjugatePicardLimit p u₀ T) t
  logistic_integrable := logistic_integrable
  energy_integrable := energy_integrable

/-! ## A3 and Jensen witness packaging. -/

theorem energy_cont
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (h : ContinuousOn (negativePartEnergy u) (Set.Icc (0 : ℝ) T)) :
    ContinuousOn (negativePartEnergy u) (Set.Icc (0 : ℝ) T) :=
  h

theorem energy_has_deriv
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ} {E' : ℝ → ℝ}
    (h :
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (negativePartEnergy u) (E' t) (Set.Ici t) t) :
    ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (negativePartEnergy u) (E' t) (Set.Ici t) t :=
  h

/-- Jensen witness assembly with a fixed discount constant and per-target
restart seed data. -/
def jensen_witness_assembly
    {T D : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (hmild :
      ReactionDiscountedMildLower D
        (fun r y => u r (unitClip y)))
    (Hseed :
      ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
        ∃ s σ : ℝ, ∃ f : ℝ → ℝ,
          0 < σ ∧
          s + σ = t ∧
          FullKernelJensenInequality f ∧
          intervalFullSemigroupOperator σ (fun y => (f y) ^ 2) x.1 ≤
            intervalFullSemigroupOperator σ
              (fun y => u s (unitClip y)) x.1 ∧
          0 < intervalFullSemigroupOperator σ f x.1) :
    JensenBypassStrictPosDataFor T u where
  witness := by
    intro t ht htT x
    rcases Hseed t ht htT x with
      ⟨s, σ, f, hσ, htime, hjensen, hseed, hpos⟩
    exact ⟨D, s, σ, f, hσ, htime, hmild, hjensen, hseed, hpos⟩

end ShenWork.Paper2.Batch2RemainingSubfields
