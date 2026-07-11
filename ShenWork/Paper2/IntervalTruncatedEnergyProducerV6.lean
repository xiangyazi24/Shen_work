/-
  Direct weak-form energy producer for the faithful truncated Picard limit.

  This file deliberately avoids the positive-time coefficient bootstrap.  The
  weak PDE is obtained from the Neumann heat/Duhamel decomposition in
  `IntervalBFormCron2SemigroupWeakDuhamel`; energy regularity is then assembled
  at the variational level.
-/

import ShenWork.Paper2.IntervalChiNegUniformCoreComplete
import ShenWork.Paper2.IntervalBFormTruncatedBridgeProducerData
import ShenWork.Paper2.IntervalBFormCron2SemigroupWeakDuhamel
import ShenWork.Paper2.IntervalNeumannHeatGradientL2
import ShenWork.Paper2.IntervalBFormCron2RegularNegativePartEnergyA2
import ShenWork.Paper2.IntervalBFormCron2RegularNegativePartEnergyA3
import ShenWork.Paper2.IntervalBFormCron2EnergyRegularityConcrete
import ShenWork.Paper2.IntervalTruncatedPicardIterJointContinuity
import ShenWork.Paper2.IntervalTruncatedPicardLimitJointContinuity

open Filter Topology Set MeasureTheory
open scoped BigOperators Topology

noncomputable section

namespace ShenWork.Paper2.IntervalTruncatedEnergyProducerV6

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalConjugatePicard
  (UniformConjugateMildExistenceCore)
open ShenWork.Paper2.BFormPositiveDatumNegPart

/-- The exact expansion of
`IntervalChiNegV6Assembly.UniformTruncatedEnergyDataV6`.  Keeping the producer
on this expansion avoids importing the unrelated Jensen assembly chain. -/
abbrev UniformTruncatedEnergyDataV6Direct (p : CM2Params) : Type :=
  ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
    PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) →
    ∀ C : UniformConjugateMildExistenceCore p u₀,
      ∀ A : UniformTruncatedConjugateMapCertificate p C,
      TruncatedNegativePartEnergyCoreRegularData p
        (uniformTruncatedConjugateMildExistenceCore_of_uniformCore C A).toData

/-- The L² Neumann heat-gradient estimate used by the direct weak-Duhamel
route is already available with constant one. -/
theorem neumannHeatGradientTMinusHalfBound :
    NeumannHeatGradientTMinusHalfBound :=
  ShenWork.IntervalNeumannHeatGradientL2.neumannHeatGradientTMinusHalfBound_proof

/-! ## Algebraic adapter from the direct weak identity

The legacy energy record stores a coefficient certificate even though its
consumer uses only the resulting weak identity.  A single nonzero positive
cosine test mode is enough to encode the three scalar pairings in a
finite-support coefficient certificate. -/

private def singleSeq (k : ℕ) (a : ℝ) : ℕ → ℝ :=
  Pi.single (M := fun _ => ℝ) k a

private theorem singleSeq_hasSum (k : ℕ) (a : ℝ) :
    HasSum (singleSeq k a) a := by
  change HasSum (fun n : ℕ => Pi.single (M := fun _ => ℝ) k a n) a
  convert hasSum_single
      (f := fun n : ℕ => Pi.single (M := fun _ => ℝ) k a n) k
      (fun b hb => by simp [Pi.single, Function.update, hb]) using 1 <;> simp

/-- A direct weak identity can be packaged in the coefficient-shaped legacy
interface whenever the negative-part test has a nonzero positive cosine mode.
The sequences are supported at that one mode; no coefficient regularity or
summability of the solution is used. -/
def coefficientWeakTestData_of_weakIdentity_of_nonzeroMode
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {t : ℝ}
    (hweak : NegativePartWeakTestIdentityAt p u t)
    {k : ℕ} (hk : k ≠ 0)
    (hmode : cosineTestCoeff (negativePartTest u t) k ≠ 0) :
    NegativePartCoefficientWeakTestData p u t := by
  classical
  let φhat : ℕ → ℝ := fun n => cosineTestCoeff (negativePartTest u t) n
  let A : ℝ :=
    ∫ x,
      intervalDomainLift
          (fun z : intervalDomainPoint => intervalDomain.timeDeriv u t z) x *
        negativePartTest u t x
      ∂ intervalMeasure 1
  let B : ℝ :=
    ∫ x,
      deriv (intervalDomainLift (u t)) x * deriv (negativePartTest u t) x
      ∂ intervalMeasure 1
  let C : ℝ :=
    p.χ₀ *
        (∫ x,
          truncatedChemFluxLifted p (u t) x *
            deriv (negativePartTest u t) x
          ∂ intervalMeasure 1) +
      ∫ x, truncatedLogisticLifted p (u t) x * negativePartTest u t x
        ∂ intervalMeasure 1
  have hABC : A + B = C := by
    simpa [A, B, C, NegativePartWeakTestIdentityAt] using hweak
  have hlam : unitIntervalCosineEigenvalue k ≠ 0 := by
    have : 0 < unitIntervalCosineEigenvalue k := by
      unfold unitIntervalCosineEigenvalue
      have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
      positivity
    exact ne_of_gt this
  have hphi : φhat k ≠ 0 := by simpa [φhat] using hmode
  let coeff : ℕ → ℝ := singleSeq k (B / (unitIntervalCosineEigenvalue k * φhat k))
  let coeffTimeDeriv : ℕ → ℝ := singleSeq k (A / φhat k)
  let sourceCoeff : ℕ → ℝ := singleSeq k (C / φhat k)
  have hlap_eq :
      (fun n : ℕ => unitIntervalCosineEigenvalue n * coeff n * φhat n) =
        singleSeq k B := by
    funext n
    by_cases hnk : n = k
    · subst n
      simp only [coeff, singleSeq, Pi.single_eq_same]
      field_simp
    · simp [coeff, singleSeq, Pi.single_eq_of_ne hnk]
  have htime_eq :
      (fun n : ℕ => coeffTimeDeriv n * φhat n) = singleSeq k A := by
    funext n
    by_cases hnk : n = k
    · subst n
      simp only [coeffTimeDeriv, singleSeq, Pi.single_eq_same]
      field_simp
    · simp [coeffTimeDeriv, singleSeq, Pi.single_eq_of_ne hnk]
  have hsource_eq :
      (fun n : ℕ => sourceCoeff n * φhat n) = singleSeq k C := by
    funext n
    by_cases hnk : n = k
    · subst n
      simp only [sourceCoeff, singleSeq, Pi.single_eq_same]
      field_simp
    · simp [sourceCoeff, singleSeq, Pi.single_eq_of_ne hnk]
  refine
    { coeff := coeff
      coeffTimeDeriv := coeffTimeDeriv
      sourceCoeff := sourceCoeff
      coeff_ode := ?_
      lap_summable := ?_
      source_summable := ?_
      time_leibniz_tsum := ?_
      gradient_ibp_tsum := ?_
      source_pairing := ?_ }
  · intro n
    by_cases hnk : n = k
    · subst n
      simp only [coeffTimeDeriv, coeff, sourceCoeff, singleSeq,
        Pi.single_eq_same]
      field_simp
      linarith
    · simp [coeffTimeDeriv, coeff, sourceCoeff, singleSeq,
        Pi.single_eq_of_ne hnk]
  · change Summable (fun n : ℕ => unitIntervalCosineEigenvalue n * coeff n * φhat n)
    rw [hlap_eq]
    exact (singleSeq_hasSum k B).summable
  · change Summable (fun n : ℕ => sourceCoeff n * φhat n)
    rw [hsource_eq]
    exact (singleSeq_hasSum k C).summable
  · change A = ∑' n : ℕ, coeffTimeDeriv n * φhat n
    rw [htime_eq, (singleSeq_hasSum k A).tsum_eq]
  · change B = ∑' n : ℕ, unitIntervalCosineEigenvalue n * coeff n * φhat n
    rw [hlap_eq, (singleSeq_hasSum k B).tsum_eq]
  · change (∑' n : ℕ, sourceCoeff n * φhat n) = C
    rw [hsource_eq, (singleSeq_hasSum k C).tsum_eq]

end ShenWork.Paper2.IntervalTruncatedEnergyProducerV6
