import ShenWork.Paper2.IntervalBFormJensenBarrierBypass
import ShenWork.Paper2.IntervalCoeffLadderFull
import ShenWork.Paper2.IntervalPicardLimitK1
import ShenWork.PDE.IntervalDuhamelCoeffFTC
import Mathlib.Analysis.Convex.Integral

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace ShenWork.Paper2.Batch1FoundationalLemmas

open ShenWork.IntervalDomain (intervalMeasure intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator intervalNeumannFullKernel)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalDuhamelCoeffFTC
  (localRestartCoeff_hasDerivAt_of_contSource_relative)
open ShenWork.Paper2.PicardLimitK1 (LocalRestart)
open ShenWork.Paper2.IntervalCoeffLadderFull
  (WindowCoefficientEnvelope eigenvalue_weighted_summable_of_pass4)
open ShenWork.Paper2.BFormPositiveDatumNegPart
  (FullKernelJensenInequality ReactionDiscountedMildLower)

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-! ## 1. Restart coefficient ODE for the Picard-limit local restart. -/

/-- The local-restart coefficients of the Picard-limit restart bundle satisfy
the scalar heat-mode ODE.  The only analytic input is source-coefficient
continuity, read from the `DuhamelSourceTimeC1` package carried by `L.srcC`. -/
theorem coeff_ode
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {T σ t : ℝ}
    (L : LocalRestart p u T σ) (htτ : L.τ < t) (htd : t < L.d) (k : ℕ) :
    HasDerivAt
      (fun r : ℝ => localRestartCoeff L.a₀ L.aC (r - L.τ) k)
      (L.aC (t - L.τ) k -
        (λ_ k) * localRestartCoeff L.a₀ L.aC (t - L.τ) k) t := by
  have hρ0 : 0 < t - L.τ := by linarith
  have hρT : t - L.τ < L.d - L.τ := by linarith
  have hcont : ContinuousOn (fun s : ℝ => L.aC s k)
      (Set.Icc (0 : ℝ) (L.d - L.τ)) := by
    intro s _hs
    exact (L.srcC.hderiv s k).continuousAt.continuousWithinAt
  have hrel :=
    localRestartCoeff_hasDerivAt_of_contSource_relative
      (a₀ := L.a₀) (a := L.aC) (T := L.d - L.τ)
      hρ0 hρT k hcont
  have hshift : HasDerivAt (fun r : ℝ => r - L.τ) (1 : ℝ) t := by
    simpa using (hasDerivAt_id t).sub_const L.τ
  simpa [one_mul] using hrel.comp t hshift

/-! ## 2. Full-kernel Jensen inequality. -/

/-- Jensen for the positive-time full Neumann heat kernel, under the standard
measurable bounded-input hypotheses needed by the Bochner integral API. -/
theorem fullKernelJensenInequality_of_aestronglyMeasurable_bounded
    {f : ℝ → ℝ} {M : ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    (hf_bdd : ∀ y, |f y| ≤ M) :
    FullKernelJensenInequality f := by
  intro σ x hσ
  let K : ℝ → ℝ := fun y => intervalNeumannFullKernel σ x y
  let Kd : ℝ → ENNReal := fun y => ENNReal.ofReal (K y)
  let μK := (intervalMeasure 1).withDensity Kd
  have hK_nn : ∀ y, 0 ≤ K y := fun y =>
    ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_nonneg hσ x y
  have hK_int : Integrable K (intervalMeasure 1) := by
    simpa [K] using
      ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_integrable hσ x
  have hKd_aem : AEMeasurable Kd (intervalMeasure 1) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      hK_int.aestronglyMeasurable.aemeasurable
  have hKd_ae_lt : ∀ᵐ y ∂(intervalMeasure 1), Kd y < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hKd_toReal : ∀ y, (Kd y).toReal = K y := by
    intro y
    simp [Kd, ENNReal.toReal_ofReal (hK_nn y)]
  have hmassK : ∫ y, K y ∂(intervalMeasure 1) = 1 := by
    simpa [K] using
      ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_intervalMeasure_integral_eq_one
        hσ x
  have hμK_mass : μK Set.univ = 1 := by
    rw [show μK = (intervalMeasure 1).withDensity Kd from rfl,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hK_int
        (Filter.Eventually.of_forall hK_nn)]
    simp [hmassK]
  haveI : IsProbabilityMeasure μK := ⟨hμK_mass⟩
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg (f 0)) (hf_bdd 0)
  have hf2_meas : AEStronglyMeasurable (fun y => f y ^ (2 : ℕ))
      (intervalMeasure 1) := by
    simpa [pow_two] using hf_meas.mul hf_meas
  have hf2_bdd : ∀ y, |f y ^ (2 : ℕ)| ≤ M ^ (2 : ℕ) := by
    intro y
    have hsq : (f y) ^ (2 : ℕ) ≤ M ^ (2 : ℕ) := by
      rw [sq_le_sq]
      simpa [abs_of_nonneg hM_nonneg] using hf_bdd y
    simpa [abs_of_nonneg (sq_nonneg (f y))] using hsq
  have hKf_int : Integrable (fun y => K y * f y) (intervalMeasure 1) := by
    have hmul : Integrable (fun y => f y * K y) (intervalMeasure 1) :=
      hK_int.bdd_mul hf_meas
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs]
          exact hf_bdd y)
    exact hmul.congr (Eventually.of_forall fun y => by ring)
  have hKf2_int : Integrable (fun y => K y * f y ^ (2 : ℕ))
      (intervalMeasure 1) := by
    have hmul : Integrable (fun y => (f y ^ (2 : ℕ)) * K y)
        (intervalMeasure 1) :=
      hK_int.bdd_mul hf2_meas
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs]
          exact hf2_bdd y)
    exact hmul.congr (Eventually.of_forall fun y => by ring)
  have hf_int_μK : Integrable f μK := by
    rw [show μK = (intervalMeasure 1).withDensity Kd from rfl,
      integrable_withDensity_iff_integrable_smul₀' hKd_aem hKd_ae_lt,
      show (fun y => (Kd y).toReal • f y) = fun y => K y * f y by
        ext y; simp [hKd_toReal, smul_eq_mul]]
    exact hKf_int
  have hf2_int_μK : Integrable (fun y => f y ^ (2 : ℕ)) μK := by
    rw [show μK = (intervalMeasure 1).withDensity Kd from rfl,
      integrable_withDensity_iff_integrable_smul₀' hKd_aem hKd_ae_lt,
      show (fun y => (Kd y).toReal • f y ^ (2 : ℕ)) =
          fun y => K y * f y ^ (2 : ℕ) by
        ext y; simp [hKd_toReal, smul_eq_mul]]
    exact hKf2_int
  have hint_rel : ∀ g : ℝ → ℝ,
      ∫ y, g y ∂μK = ∫ y, K y * g y ∂(intervalMeasure 1) := by
    intro g
    rw [show μK = (intervalMeasure 1).withDensity Kd from rfl,
      integral_withDensity_eq_integral_toReal_smul₀ hKd_aem hKd_ae_lt]
    congr 1
    ext y
    simp [hKd_toReal, smul_eq_mul]
  have hconv : ConvexOn ℝ (Set.univ : Set ℝ) (fun z : ℝ => z ^ (2 : ℕ)) := by
    simpa using (show Even (2 : ℕ) by norm_num).convexOn_pow (𝕜 := ℝ)
  have hJ := hconv.map_integral_le
    ((continuous_id.pow 2).continuousOn) isClosed_univ
    (Filter.Eventually.of_forall fun y => Set.mem_univ (f y))
    hf_int_μK hf2_int_μK
  rw [hint_rel f, hint_rel (fun y => f y ^ (2 : ℕ))] at hJ
  simpa [intervalFullSemigroupOperator, K] using hJ

/-! ## 3. Discounted mild lower bound from the exact Duhamel lower remainder. -/

/-- Algebraic assembly of the reaction-discounted lower bound.  The hypothesis
`hduh_lower` is the precise lower estimate on the Duhamel remainder that the
source comparison argument must supply. -/
theorem reactionDiscountedMildLower_of_duhamel_lower
    {D : ℝ} {u : ℝ → ℝ → ℝ}
    (hmild :
      ∀ ⦃s σ x : ℝ⦄, 0 < σ →
        ∃ I : ℝ,
          u (s + σ) x =
            intervalFullSemigroupOperator σ (fun y => u s y) x + I ∧
          (Real.exp (-D * σ) - 1) *
              intervalFullSemigroupOperator σ (fun y => u s y) x ≤ I) :
    ReactionDiscountedMildLower D u := by
  intro s σ x hσ
  rcases hmild hσ with ⟨I, hrepr, hI⟩
  calc
    Real.exp (-D * σ) * intervalFullSemigroupOperator σ (fun y => u s y) x
        = intervalFullSemigroupOperator σ (fun y => u s y) x +
            (Real.exp (-D * σ) - 1) *
              intervalFullSemigroupOperator σ (fun y => u s y) x := by ring
    _ ≤ intervalFullSemigroupOperator σ (fun y => u s y) x + I :=
        add_le_add (le_refl _) hI
    _ = u (s + σ) x := hrepr.symm

/-! ## 4. Summability wrappers. -/

/-- The pass-4 coefficient ladder gives `Σ λₖ |aₖ(s)| < ∞`. -/
theorem lap_summable
    {c T' : ℝ} {û : ℝ → ℕ → ℝ}
    (env4 : WindowCoefficientEnvelope 4 c T' û)
    {s : ℝ} (hs : s ∈ Set.Icc c T') :
    Summable (fun k : ℕ => (λ_ k) * |û s k|) :=
  eigenvalue_weighted_summable_of_pass4 env4 hs

/-- A `DuhamelSourceTimeC1` source package gives absolute summability of the
source coefficients at every nonnegative time. -/
theorem source_summable
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {s : ℝ} (hs : 0 ≤ s) :
    Summable (fun k : ℕ => |a s k|) := by
  refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
    src.henv_summable
  exact src.henv_bound s hs k

/-- Source summability specialized to the Picard-limit local restart bundle. -/
theorem localRestart_source_summable
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {T σ s : ℝ}
    (L : LocalRestart p u T σ) (hs : 0 ≤ s) :
    Summable (fun k : ℕ => |L.aC s k|) :=
  source_summable L.srcC hs

end ShenWork.Paper2.Batch1FoundationalLemmas
