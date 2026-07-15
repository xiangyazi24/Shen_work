import ShenWork.Paper2.IntervalDomainLemma21
import ShenWork.PDE.AnalyticSemigroupDecay

/-!
# Corrected interval-domain semigroup lemmas

The literal `Lemma_2_1`--`Lemma_2_4` records attach exponential decay to an
undamped Neumann semigroup and therefore cannot hold on its constant mode.
The concrete interval implementation also currently proves the divergence
endpoint with `heatGradientL1LinftyFactor`, rather than silently replacing it
by the sharper paper factor.

These corrected headlines separate the two mathematically different cases:

* on the full undamped space, the available estimates carry no exponential
  factor and use the concrete heat-gradient factor;
* a positive spectral shift, or removal of the Neumann zero mode, gives the
  genuine exponential factor through the proved coefficient semigroup.

No abstract `SemigroupEstimateData` field or zero-output impostor is used by
the closers below.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace ShenWork.Paper2.IntervalDomainCorrectedSemigroupLemmas

open ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalDomainLemma21
open ShenWork.HeatKernelGradientEstimates
open ShenWork.PDE.AnalyticSemigroupGen
open ShenWork.PDE.AnalyticSemigroupDecay
open ShenWork.PDE.ResolventEstimate
open ShenWork.Paper3

/-! ## Lemma 2.1 -/

/-- The attainable full-space part of Lemma 2.1.  The undamped Neumann
semigroup is an `L^q` contraction; no false exponential decay is asserted for
the constant mode. -/
def CorrectedLemma_2_1_NoSpectralGap : Prop :=
  ∀ sigma q r : ℝ, 0 ≤ sigma → 1 ≤ q → r.HolderConjugate q →
    ∃ C > 0, ∀ t > 0, ∀ u : intervalDomain.Point → ℝ,
      MemLp (intervalDomainLift u) (ENNReal.ofReal q) (intervalMeasure 1) →
        intervalDomainSemigroupEstimateData.fractionalNorm sigma q
            (intervalDomainSemigroupEstimateData.semigroup t u) ≤
          C * intervalDomainSemigroupEstimateData.lpNorm q u

/-- The attainable fractional `S(t)-I` part of Lemma 2.1 in the concrete
Neumann cosine `L²` model. -/
def CorrectedLemma_2_1_FractionalDifference : Prop :=
  ∀ {t sigma : ℝ} (a : ℕ → ℂ)
      (ht : 0 < t) (hsigma_pos : 0 < sigma) (hsigma_le : sigma ≤ 1)
      (henergy :
        Summable fun n : ℕ =>
          (unitIntervalCosineEigenvalue n ^ sigma) ^ 2 * ‖a n‖ ^ 2),
    ‖unitIntervalCosineHeatDifferenceLpFromCoeffs
        a ht hsigma_pos hsigma_le henergy‖ ≤
      t ^ sigma * spectralCoeffFractionalNorm sigma a

/-- The genuine spectral-gap version of the exponential factor.  The first
conjunct is the positively shifted operator, including its zero mode.  The
second is the unshifted Neumann operator restricted to zero-mode-free data. -/
def CorrectedLemma_2_1_WithSpectralGap : Prop :=
  (∀ {omega t : ℝ}, 0 < omega → 0 ≤ t →
      ∀ {a : ℕ → ℂ},
        Summable (fun n : ℕ => ‖a n‖ ^ 2) →
          coeffL2Norm (shiftedNeumannHeatCoeff omega t a) ≤
            Real.exp (-(omega * t)) * coeffL2Norm a) ∧
    (∀ {t : ℝ}, 0 ≤ t →
      ∀ {a : ℕ → ℂ},
        Summable (fun n : ℕ => ‖a n‖ ^ 2) → a 0 = 0 →
          coeffL2Norm (shiftedNeumannHeatCoeff 0 t a) ≤
            Real.exp
                (-(unitIntervalNeumannSpectrum.firstNonzero * t)) *
              coeffL2Norm a)

/-- Corrected Lemma 2.1: full-space nonsharp control, the fractional
difference estimate, and exponential decay exactly on the spectral-gap
subspaces where it is valid. -/
def CorrectedLemma_2_1 : Prop :=
  CorrectedLemma_2_1_NoSpectralGap ∧
    CorrectedLemma_2_1_FractionalDifference ∧
      CorrectedLemma_2_1_WithSpectralGap

theorem intervalDomain_CorrectedLemma_2_1 : CorrectedLemma_2_1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact intervalDomainSemigroupEstimateData_Lemma_2_1_nonsharp_semigroup_branch
  · intro t sigma a ht hsigma_pos hsigma_le henergy
    exact unitIntervalCosineHeatDifferenceLpFromCoeffs_norm_le
      a ht hsigma_pos hsigma_le henergy
  · constructor
    · intro omega t _homega ht a ha
      exact
        ShenWork.PDE.AnalyticSemigroupDecay.shiftedNeumannHeatCoeff_l2_norm_decay
          ht ha
    · intro t ht a ha ha0
      exact
        ShenWork.PDE.AnalyticSemigroupDecay.unshiftedNeumannHeatCoeff_l2_norm_firstNonzero_of_zeroMode
          ht ha ha0

/-! ## Lemma 2.2 -/

/-- Corrected Lemma 2.2 for the concrete norm model.  Both branches are the
proved same-exponent embeddings; the unavailable general `q -> r` Sobolev
gain is not hidden in a package field. -/
def CorrectedLemma_2_2 : Prop :=
  (∀ sigma q k, 0 ≤ sigma → 1 ≤ q →
      k - intervalDomain.volume / q <
          2 * sigma - intervalDomain.volume / q →
        ∃ C > 0, ∀ u : intervalDomain.Point → ℝ,
          intervalDomainSemigroupEstimateData.embeddingNorm k q sigma u ≤
            C * intervalDomainSemigroupEstimateData.fractionalNorm sigma q u) ∧
    (∀ sigma q theta, 0 ≤ theta →
      theta < 2 * sigma - intervalDomain.volume / q →
        ∃ C > 0, ∀ u : intervalDomain.Point → ℝ,
          intervalDomainSemigroupEstimateData.embeddingNorm theta q sigma u ≤
            C * intervalDomainSemigroupEstimateData.fractionalNorm sigma q u)

theorem intervalDomain_CorrectedLemma_2_2 : CorrectedLemma_2_2 :=
  ⟨intervalDomainSemigroupEstimateData_Lemma_2_2_nonsharp_diagonal_branch,
    intervalDomainSemigroupEstimateData_Lemma_2_2_nonsharp_same_branch⟩

/-! ## Lemma 2.3 -/

/-- Corrected Lemma 2.3 with the concrete no-gap heat-gradient factor. -/
def CorrectedLemma_2_3 : Prop :=
  ∃ C > 0, ∀ q > 1, ∀ t > 0,
    ∀ phi : intervalDomain.Point → ℝ,
      MemLp (intervalDomainLift phi) (ENNReal.ofReal q) (intervalMeasure 1) →
        intervalDomainSemigroupEstimateData.lpNorm q
            (intervalDomainSemigroupEstimateData.divergenceSemigroup t phi) ≤
          C * heatGradientL1LinftyFactor t *
            intervalDomainSemigroupEstimateData.vectorLpNorm q phi

theorem intervalDomain_CorrectedLemma_2_3 : CorrectedLemma_2_3 :=
  intervalDomainSemigroupEstimateData_Lemma_2_3_nonsharp

/-! ## Lemma 2.4 -/

/-- Corrected Lemma 2.4 with the concrete no-gap heat-gradient factor.  In
the current concrete data the fractional norm is the underlying `L^q` norm,
so this is the proved divergence estimate in that field. -/
def CorrectedLemma_2_4 : Prop :=
  ∀ sigma q, 0 < sigma → 1 < q →
    ∃ C > 0, ∀ t > 0, ∀ phi : intervalDomain.Point → ℝ,
      MemLp (intervalDomainLift phi) (ENNReal.ofReal q) (intervalMeasure 1) →
        intervalDomainSemigroupEstimateData.fractionalNorm sigma q
            (intervalDomainSemigroupEstimateData.divergenceSemigroup t phi) ≤
          C * heatGradientL1LinftyFactor t *
            intervalDomainSemigroupEstimateData.vectorLpNorm q phi

theorem intervalDomain_CorrectedLemma_2_4 : CorrectedLemma_2_4 :=
  intervalDomainSemigroupEstimateData_Lemma_2_4_nonsharp

/-! ## Appendix A.2--A.4 corrected closers

Paper 3's raw appendix declarations are aliases of the unreachable literal
Paper 2 declarations.  These corrected aliases use the concrete, proved
interval statements above instead.
-/

end ShenWork.Paper2.IntervalDomainCorrectedSemigroupLemmas

namespace ShenWork.Paper3.IntervalDomainCorrectedAppendixSemigroupLemmas

open ShenWork.Paper2.IntervalDomainCorrectedSemigroupLemmas

def CorrectedLemma_A_2 : Prop := CorrectedLemma_2_1
def CorrectedLemma_A_3 : Prop := CorrectedLemma_2_2
def CorrectedLemma_A_4 : Prop := CorrectedLemma_2_3

theorem intervalDomain_CorrectedLemma_A_2 : CorrectedLemma_A_2 :=
  intervalDomain_CorrectedLemma_2_1

theorem intervalDomain_CorrectedLemma_A_3 : CorrectedLemma_A_3 :=
  intervalDomain_CorrectedLemma_2_2

theorem intervalDomain_CorrectedLemma_A_4 : CorrectedLemma_A_4 :=
  intervalDomain_CorrectedLemma_2_3

end ShenWork.Paper3.IntervalDomainCorrectedAppendixSemigroupLemmas

#print axioms
  ShenWork.Paper2.IntervalDomainCorrectedSemigroupLemmas.intervalDomain_CorrectedLemma_2_1
#print axioms
  ShenWork.Paper2.IntervalDomainCorrectedSemigroupLemmas.intervalDomain_CorrectedLemma_2_2
#print axioms
  ShenWork.Paper2.IntervalDomainCorrectedSemigroupLemmas.intervalDomain_CorrectedLemma_2_3
#print axioms
  ShenWork.Paper2.IntervalDomainCorrectedSemigroupLemmas.intervalDomain_CorrectedLemma_2_4
#print axioms
  ShenWork.Paper3.IntervalDomainCorrectedAppendixSemigroupLemmas.intervalDomain_CorrectedLemma_A_2
#print axioms
  ShenWork.Paper3.IntervalDomainCorrectedAppendixSemigroupLemmas.intervalDomain_CorrectedLemma_A_3
#print axioms
  ShenWork.Paper3.IntervalDomainCorrectedAppendixSemigroupLemmas.intervalDomain_CorrectedLemma_A_4

end
