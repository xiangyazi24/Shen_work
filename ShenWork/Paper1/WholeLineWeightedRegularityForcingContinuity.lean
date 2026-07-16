import ShenWork.Paper1.WholeLineWeightedRegularityL2CoefficientContinuity
import ShenWork.Paper1.WholeLineWeightedRegularityFluxDerivative

open Filter MeasureTheory Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Exact-weight continuity of the expanded generator forcing

The weighted chemotactic flux derivative is a sum of four bounded
coefficient fields multiplying the exact-weight trajectories `Wx`, `W`,
`Zx`, and `Z`.  This file turns strong scalar `L²` continuity of those
trajectories and uniform continuity of the two dynamic coefficients into
strong `L²` continuity of the expanded forcing.  No stronger exponential
weight and no weighted time derivative are used.
-/

/-- The dynamic coefficient multiplying the weighted population field in
the expanded chemotactic flux derivative. -/
def paper5WeightedFluxPopulationCoefficient
    (p : CMParams) (eta : ℝ) (u v : ℝ → ℝ → ℝ)
    (U : ℝ → ℝ) (t x : ℝ) : ℝ :=
  paper5B2 p u v U t x +
    paper5CorrectedChemZeroCoefficient p u v U t x -
      eta * paper5B1 p u v t x

/-- The static coefficient multiplying the weighted signal field in the
expanded chemotactic flux derivative. -/
def paper5WeightedFluxSignalCoefficient
    (p : CMParams) (eta : ℝ) (U : ℝ → ℝ) (x : ℝ) : ℝ :=
  paper5B4 p U x - eta * paper5B3 p U x

/-- The expanded chemotactic flux derivative, viewed as a time trajectory
of scalar fields. -/
def paper5WeightedFluxDerivativeExpandedTrajectory
    (p : CMParams) (eta : ℝ)
    (u v : ℝ → ℝ → ℝ) (U : ℝ → ℝ)
    (W Wx Z Zx : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  paper5WeightedFluxDerivativeExpanded p eta u v U
    (W t) (Wx t) (Z t) (Zx t) t x

/-- The reaction part of the exact weighted generator forcing, expressed
as its mean coefficient multiplying the weighted population field. -/
def paper5WeightedReactionExpandedTrajectory
    (p : CMParams) (u : ℝ → ℝ → ℝ) (U : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  (1 - paper5A (1 + p.α) u U t x) * W t x

/-- The source-faithful expanded generator forcing: the corrected
chemotactic flux derivative plus the reaction mean-coefficient term. -/
def paper5WeightedGeneratorForcingExpandedTrajectory
    (p : CMParams) (eta : ℝ)
    (u v : ℝ → ℝ → ℝ) (U : ℝ → ℝ)
    (W Wx Z Zx : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  -p.χ * paper5WeightedFluxDerivativeExpandedTrajectory
      p eta u v U W Wx Z Zx t x +
    paper5WeightedReactionExpandedTrajectory p u U W t x

/-- Measurability of the expanded flux trajectory follows termwise from
the four coefficient and four field representatives. -/
theorem paper5WeightedFluxDerivativeExpandedTrajectory_aestronglyMeasurable
    (p : CMParams) (eta : ℝ)
    {u v : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {W Wx Z Zx : ℝ → ℝ → ℝ} (t : ℝ)
    (hB1 : AEStronglyMeasurable (paper5B1 p u v t) volume)
    (hB2 : AEStronglyMeasurable
      (paper5WeightedFluxPopulationCoefficient p eta u v U t) volume)
    (hB3 : AEStronglyMeasurable (paper5B3 p U) volume)
    (hB4 : AEStronglyMeasurable
      (paper5WeightedFluxSignalCoefficient p eta U) volume)
    (hW : AEStronglyMeasurable (W t) volume)
    (hWx : AEStronglyMeasurable (Wx t) volume)
    (hZ : AEStronglyMeasurable (Z t) volume)
    (hZx : AEStronglyMeasurable (Zx t) volume) :
    AEStronglyMeasurable
      (paper5WeightedFluxDerivativeExpandedTrajectory
        p eta u v U W Wx Z Zx t) volume := by
  simpa [paper5WeightedFluxDerivativeExpandedTrajectory,
    paper5WeightedFluxDerivativeExpanded,
    paper5WeightedFluxPopulationCoefficient,
    paper5WeightedFluxSignalCoefficient] using
    (((hB1.mul hWx).add (hB2.mul hW)).add (hB3.mul hZx)).add
      (hB4.mul hZ)

/-- Measurability of the expanded reaction trajectory follows from its
coefficient and weighted population representatives. -/
theorem paper5WeightedReactionExpandedTrajectory_aestronglyMeasurable
    (p : CMParams) {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {W : ℝ → ℝ → ℝ} (t : ℝ)
    (hcoef : AEStronglyMeasurable
      (fun x => 1 - paper5A (1 + p.α) u U t x) volume)
    (hW : AEStronglyMeasurable (W t) volume) :
    AEStronglyMeasurable
      (paper5WeightedReactionExpandedTrajectory p u U W t) volume := by
  simpa [paper5WeightedReactionExpandedTrajectory] using hcoef.mul hW

/-- Algebraic identification of the expanded generator forcing with the
already named lower-order source after removal of the zero-order term of
the conjugated heat generator. -/
theorem paper5WeightedGeneratorForcingExpandedTrajectory_eq
    (p : CMParams) (eta c : ℝ)
    (u v : ℝ → ℝ → ℝ) (U : ℝ → ℝ)
    (W Wx Z Zx : ℝ → ℝ → ℝ) (t x : ℝ) :
    paper5WeightedGeneratorForcingExpandedTrajectory
        p eta u v U W Wx Z Zx t x =
      paper5WeightedLowerOrderSource p eta c u v U
          (W t) (Wx t) (Z t) (Zx t) t x -
        (eta ^ 2 - c * eta) * W t x := by
  unfold paper5WeightedGeneratorForcingExpandedTrajectory
    paper5WeightedFluxDerivativeExpandedTrajectory
    paper5WeightedReactionExpandedTrajectory
    paper5WeightedFluxDerivativeExpanded
    paper5WeightedLowerOrderSource
    paper5CorrectedJ2Coefficient
  ring

/-- The product-continuity theorem together with the integrability data
needed by a subsequent finite-sum closure. -/
theorem eventually_integrable_and_tendsto_integral_mul_sub_mul_sq_zero
    {a u : ℝ → ℝ → ℝ} {t B : ℝ} {D : ℝ → ℝ}
    (hB : 0 ≤ B)
    (hD_nonneg : ∀ᶠ s in 𝓝 t, 0 ≤ D s)
    (hD : Tendsto D (𝓝 t) (𝓝 0))
    (ha : ∀ᶠ s in 𝓝 t, ∀ x, |a s x| ≤ B)
    (hadiff : ∀ᶠ s in 𝓝 t, ∀ x,
      |a s x - a t x| ≤ D s)
    (hout_meas : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable
        (fun x => a s x * u s x - a t x * u t x) volume)
    (hut : Integrable (fun x => u t x ^ 2) volume)
    (hudiff : ∀ᶠ s in 𝓝 t,
      Integrable (fun x => (u s x - u t x) ^ 2) volume)
    (hudiff_zero : Tendsto
      (fun s => ∫ x : ℝ, (u s x - u t x) ^ 2)
      (𝓝 t) (𝓝 0)) :
    (∀ᶠ s in 𝓝 t,
      Integrable
        (fun x => (a s x * u s x - a t x * u t x) ^ 2) volume) ∧
      Tendsto
        (fun s => ∫ x : ℝ,
          (a s x * u s x - a t x * u t x) ^ 2)
        (𝓝 t) (𝓝 0) := by
  constructor
  · filter_upwards [hD_nonneg, ha, hadiff, hout_meas, hudiff]
      with s hsD hsa hsad hsmeas hsint
    exact (integral_mul_sub_mul_sq_data hB hsD hsa hsad
      hsmeas hsint hut).1
  · exact tendsto_integral_mul_sub_mul_sq_zero hB hD_nonneg hD ha
      hadiff hout_meas hut hudiff hudiff_zero

/-- Exact-weight strong `L²` continuity of the corrected expanded
chemotactic flux derivative.  The only time-dependent coefficient inputs
are uniform bounds and explicit sup-norm moduli for `B1` and the combined
population coefficient `B2 + B0 - eta * B1`. -/
theorem paper5WeightedFluxDerivativeExpandedTrajectory_strongL2At
    (p : CMParams) (eta : ℝ)
    {u v : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {W Wx Z Zx : ℝ → ℝ → ℝ}
    {t K1 K2 K3 K4 : ℝ} {D1 D2 : ℝ → ℝ}
    (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hK3 : 0 ≤ K3) (hK4 : 0 ≤ K4)
    (hD1_nonneg : ∀ᶠ s in 𝓝 t, 0 ≤ D1 s)
    (hD2_nonneg : ∀ᶠ s in 𝓝 t, 0 ≤ D2 s)
    (hD1 : Tendsto D1 (𝓝 t) (𝓝 0))
    (hD2 : Tendsto D2 (𝓝 t) (𝓝 0))
    (hB1_bound : ∀ᶠ s in 𝓝 t, ∀ x,
      |paper5B1 p u v s x| ≤ K1)
    (hB1_diff : ∀ᶠ s in 𝓝 t, ∀ x,
      |paper5B1 p u v s x - paper5B1 p u v t x| ≤ D1 s)
    (hB2_bound : ∀ᶠ s in 𝓝 t, ∀ x,
      |paper5WeightedFluxPopulationCoefficient p eta u v U s x| ≤ K2)
    (hB2_diff : ∀ᶠ s in 𝓝 t, ∀ x,
      |paper5WeightedFluxPopulationCoefficient p eta u v U s x -
          paper5WeightedFluxPopulationCoefficient p eta u v U t x| ≤ D2 s)
    (hB3_bound : ∀ x, |paper5B3 p U x| ≤ K3)
    (hB4_bound : ∀ x,
      |paper5WeightedFluxSignalCoefficient p eta U x| ≤ K4)
    (hB1_meas : ∀ s,
      AEStronglyMeasurable (paper5B1 p u v s) volume)
    (hB2_meas : ∀ s, AEStronglyMeasurable
      (paper5WeightedFluxPopulationCoefficient p eta u v U s) volume)
    (hB3_meas : AEStronglyMeasurable (paper5B3 p U) volume)
    (hB4_meas : AEStronglyMeasurable
      (paper5WeightedFluxSignalCoefficient p eta U) volume)
    (hW_meas : ∀ s, AEStronglyMeasurable (W s) volume)
    (hWx_meas : ∀ s, AEStronglyMeasurable (Wx s) volume)
    (hZ_meas : ∀ s, AEStronglyMeasurable (Z s) volume)
    (hZx_meas : ∀ s, AEStronglyMeasurable (Zx s) volume)
    (hW_t : Integrable (fun x => W t x ^ 2) volume)
    (hWx_t : Integrable (fun x => Wx t x ^ 2) volume)
    (hZ_t : Integrable (fun x => Z t x ^ 2) volume)
    (hZx_t : Integrable (fun x => Zx t x ^ 2) volume)
    (hW_diff : ∀ᶠ s in 𝓝 t,
      Integrable (fun x => (W s x - W t x) ^ 2) volume)
    (hWx_diff : ∀ᶠ s in 𝓝 t,
      Integrable (fun x => (Wx s x - Wx t x) ^ 2) volume)
    (hZ_diff : ∀ᶠ s in 𝓝 t,
      Integrable (fun x => (Z s x - Z t x) ^ 2) volume)
    (hZx_diff : ∀ᶠ s in 𝓝 t,
      Integrable (fun x => (Zx s x - Zx t x) ^ 2) volume)
    (hW_zero : Tendsto
      (fun s => ∫ x : ℝ, (W s x - W t x) ^ 2) (𝓝 t) (𝓝 0))
    (hWx_zero : Tendsto
      (fun s => ∫ x : ℝ, (Wx s x - Wx t x) ^ 2) (𝓝 t) (𝓝 0))
    (hZ_zero : Tendsto
      (fun s => ∫ x : ℝ, (Z s x - Z t x) ^ 2) (𝓝 t) (𝓝 0))
    (hZx_zero : Tendsto
      (fun s => ∫ x : ℝ, (Zx s x - Zx t x) ^ 2) (𝓝 t) (𝓝 0)) :
    (∀ᶠ s in 𝓝 t, Integrable (fun x =>
      (paper5WeightedFluxDerivativeExpandedTrajectory
          p eta u v U W Wx Z Zx s x -
        paper5WeightedFluxDerivativeExpandedTrajectory
          p eta u v U W Wx Z Zx t x) ^ 2) volume) ∧
      Tendsto (fun s => ∫ x : ℝ,
        (paper5WeightedFluxDerivativeExpandedTrajectory
            p eta u v U W Wx Z Zx s x -
          paper5WeightedFluxDerivativeExpandedTrajectory
            p eta u v U W Wx Z Zx t x) ^ 2)
        (𝓝 t) (𝓝 0) := by
  let a1 : ℝ → ℝ → ℝ := fun s => paper5B1 p u v s
  let a2 : ℝ → ℝ → ℝ := fun s =>
    paper5WeightedFluxPopulationCoefficient p eta u v U s
  let a3 : ℝ → ℝ → ℝ := fun _ => paper5B3 p U
  let a4 : ℝ → ℝ → ℝ := fun _ =>
    paper5WeightedFluxSignalCoefficient p eta U
  let f1 : ℝ → ℝ → ℝ := fun s x => a1 s x * Wx s x
  let f2 : ℝ → ℝ → ℝ := fun s x => a2 s x * W s x
  let f3 : ℝ → ℝ → ℝ := fun s x => a3 s x * Zx s x
  let f4 : ℝ → ℝ → ℝ := fun s x => a4 s x * Z s x
  have hf1_meas : ∀ s, AEStronglyMeasurable (f1 s) volume := by
    intro s
    exact (hB1_meas s).mul (hWx_meas s)
  have hf2_meas : ∀ s, AEStronglyMeasurable (f2 s) volume := by
    intro s
    exact (hB2_meas s).mul (hW_meas s)
  have hf3_meas : ∀ s, AEStronglyMeasurable (f3 s) volume := by
    intro s
    exact hB3_meas.mul (hZx_meas s)
  have hf4_meas : ∀ s, AEStronglyMeasurable (f4 s) volume := by
    intro s
    exact hB4_meas.mul (hZ_meas s)
  have hf1_diff_meas : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (fun x => f1 s x - f1 t x) volume :=
    Eventually.of_forall fun s => (hf1_meas s).sub (hf1_meas t)
  have hf2_diff_meas : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (fun x => f2 s x - f2 t x) volume :=
    Eventually.of_forall fun s => (hf2_meas s).sub (hf2_meas t)
  have hf3_diff_meas : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (fun x => f3 s x - f3 t x) volume :=
    Eventually.of_forall fun s => (hf3_meas s).sub (hf3_meas t)
  have hf4_diff_meas : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (fun x => f4 s x - f4 t x) volume :=
    Eventually.of_forall fun s => (hf4_meas s).sub (hf4_meas t)
  have h1 := eventually_integrable_and_tendsto_integral_mul_sub_mul_sq_zero
    (a := a1) (u := Wx) (B := K1) (D := D1)
    hK1 hD1_nonneg hD1 hB1_bound hB1_diff hf1_diff_meas
    hWx_t hWx_diff hWx_zero
  have h2 := eventually_integrable_and_tendsto_integral_mul_sub_mul_sq_zero
    (a := a2) (u := W) (B := K2) (D := D2)
    hK2 hD2_nonneg hD2 hB2_bound hB2_diff hf2_diff_meas
    hW_t hW_diff hW_zero
  have h3 := eventually_integrable_and_tendsto_integral_mul_sub_mul_sq_zero
    (a := a3) (u := Zx) (B := K3) (D := fun _ => 0)
    hK3 (Eventually.of_forall fun _ => le_rfl) tendsto_const_nhds
    (Eventually.of_forall fun _ => hB3_bound)
    (Eventually.of_forall fun _ _ => by simp [a3]) hf3_diff_meas
    hZx_t hZx_diff hZx_zero
  have h4 := eventually_integrable_and_tendsto_integral_mul_sub_mul_sq_zero
    (a := a4) (u := Z) (B := K4) (D := fun _ => 0)
    hK4 (Eventually.of_forall fun _ => le_rfl) tendsto_const_nhds
    (Eventually.of_forall fun _ => hB4_bound)
    (Eventually.of_forall fun _ _ => by simp [a4]) hf4_diff_meas
    hZ_t hZ_diff hZ_zero
  have hsum_meas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (fun x =>
      (f1 s x + f2 s x + f3 s x + f4 s x) -
        (f1 t x + f2 t x + f3 t x + f4 t x)) volume :=
    Eventually.of_forall fun s =>
      ((((hf1_meas s).add (hf2_meas s)).add (hf3_meas s)).add
        (hf4_meas s)).sub
      ((((hf1_meas t).add (hf2_meas t)).add (hf3_meas t)).add
        (hf4_meas t))
  have hsum_int : ∀ᶠ s in 𝓝 t, Integrable (fun x =>
      ((f1 s x + f2 s x + f3 s x + f4 s x) -
        (f1 t x + f2 t x + f3 t x + f4 t x)) ^ 2) volume := by
    filter_upwards [hsum_meas, h1.1, h2.1, h3.1, h4.1]
      with s hsmeas hs1 hs2 hs3 hs4
    exact (integral_four_sum_sub_sq_data hsmeas hs1 hs2 hs3 hs4).1
  have hsum_zero := tendsto_integral_four_sum_sub_sq_zero
    hsum_meas h1.1 h2.1 h3.1 h4.1 h1.2 h2.2 h3.2 h4.2
  constructor
  · simpa [paper5WeightedFluxDerivativeExpandedTrajectory,
      paper5WeightedFluxDerivativeExpanded,
      paper5WeightedFluxPopulationCoefficient,
      paper5WeightedFluxSignalCoefficient, a1, a2, a3, a4,
      f1, f2, f3, f4] using hsum_int
  · simpa [paper5WeightedFluxDerivativeExpandedTrajectory,
      paper5WeightedFluxDerivativeExpanded,
      paper5WeightedFluxPopulationCoefficient,
      paper5WeightedFluxSignalCoefficient, a1, a2, a3, a4,
      f1, f2, f3, f4] using hsum_zero

/-- Strong `L²` continuity of the reaction mean-coefficient product at the
exact weight. -/
theorem paper5WeightedReactionExpandedTrajectory_strongL2At
    (p : CMParams) {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {W : ℝ → ℝ → ℝ} {t K : ℝ} {D : ℝ → ℝ}
    (hK : 0 ≤ K)
    (hD_nonneg : ∀ᶠ s in 𝓝 t, 0 ≤ D s)
    (hD : Tendsto D (𝓝 t) (𝓝 0))
    (hcoef_bound : ∀ᶠ s in 𝓝 t, ∀ x,
      |1 - paper5A (1 + p.α) u U s x| ≤ K)
    (hcoef_diff : ∀ᶠ s in 𝓝 t, ∀ x,
      |(1 - paper5A (1 + p.α) u U s x) -
          (1 - paper5A (1 + p.α) u U t x)| ≤ D s)
    (hcoef_meas : ∀ s, AEStronglyMeasurable
      (fun x => 1 - paper5A (1 + p.α) u U s x) volume)
    (hW_meas : ∀ s, AEStronglyMeasurable (W s) volume)
    (hW_t : Integrable (fun x => W t x ^ 2) volume)
    (hW_diff : ∀ᶠ s in 𝓝 t,
      Integrable (fun x => (W s x - W t x) ^ 2) volume)
    (hW_zero : Tendsto
      (fun s => ∫ x : ℝ, (W s x - W t x) ^ 2) (𝓝 t) (𝓝 0)) :
    (∀ᶠ s in 𝓝 t, Integrable (fun x =>
      (paper5WeightedReactionExpandedTrajectory p u U W s x -
        paper5WeightedReactionExpandedTrajectory p u U W t x) ^ 2)
      volume) ∧
      Tendsto (fun s => ∫ x : ℝ,
        (paper5WeightedReactionExpandedTrajectory p u U W s x -
          paper5WeightedReactionExpandedTrajectory p u U W t x) ^ 2)
        (𝓝 t) (𝓝 0) := by
  let a : ℝ → ℝ → ℝ := fun s x =>
    1 - paper5A (1 + p.α) u U s x
  have hout_meas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable
      (fun x => a s x * W s x - a t x * W t x) volume :=
    Eventually.of_forall fun s =>
      ((hcoef_meas s).mul (hW_meas s)).sub
        ((hcoef_meas t).mul (hW_meas t))
  simpa [paper5WeightedReactionExpandedTrajectory, a] using
    (eventually_integrable_and_tendsto_integral_mul_sub_mul_sq_zero
      (a := a) (u := W) (B := K) (D := D)
      hK hD_nonneg hD hcoef_bound hcoef_diff hout_meas
      hW_t hW_diff hW_zero)

/-- Two strongly `L²` convergent scalar trajectories may be added after a
fixed scalar rescaling of the first.  The conclusion retains the
integrability needed by later Duhamel arguments. -/
theorem eventually_integrable_and_tendsto_integral_const_mul_add_sub_sq_zero
    {F R : ℝ → ℝ → ℝ} {t q : ℝ}
    (hout_meas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (fun x =>
      (q * F s x + R s x) - (q * F t x + R t x)) volume)
    (hFint : ∀ᶠ s in 𝓝 t,
      Integrable (fun x => (F s x - F t x) ^ 2) volume)
    (hRint : ∀ᶠ s in 𝓝 t,
      Integrable (fun x => (R s x - R t x) ^ 2) volume)
    (hFzero : Tendsto
      (fun s => ∫ x : ℝ, (F s x - F t x) ^ 2) (𝓝 t) (𝓝 0))
    (hRzero : Tendsto
      (fun s => ∫ x : ℝ, (R s x - R t x) ^ 2) (𝓝 t) (𝓝 0)) :
    (∀ᶠ s in 𝓝 t, Integrable (fun x =>
      ((q * F s x + R s x) - (q * F t x + R t x)) ^ 2) volume) ∧
      Tendsto (fun s => ∫ x : ℝ,
        ((q * F s x + R s x) - (q * F t x + R t x)) ^ 2)
        (𝓝 t) (𝓝 0) := by
  let upper : ℝ → ℝ := fun s =>
    2 * q ^ 2 * (∫ x : ℝ, (F s x - F t x) ^ 2) +
      2 * (∫ x : ℝ, (R s x - R t x) ^ 2)
  have hupper_zero : Tendsto upper (𝓝 t) (𝓝 0) := by
    have hfirst := hFzero.const_mul (2 * q ^ 2)
    have hsecond := hRzero.const_mul 2
    simpa only [upper, mul_zero, zero_add] using hfirst.add hsecond
  have hdata : ∀ᶠ s in 𝓝 t,
      Integrable (fun x =>
        ((q * F s x + R s x) - (q * F t x + R t x)) ^ 2) volume ∧
      (∫ x : ℝ,
        ((q * F s x + R s x) - (q * F t x + R t x)) ^ 2) ≤
          upper s := by
    filter_upwards [hout_meas, hFint, hRint]
      with s hsmeas hsF hsR
    let major : ℝ → ℝ := fun x =>
      2 * q ^ 2 * (F s x - F t x) ^ 2 +
        2 * (R s x - R t x) ^ 2
    have hmajor : Integrable major volume :=
      (hsF.const_mul (2 * q ^ 2)).add (hsR.const_mul 2)
    have hpoint : ∀ x,
        ((q * F s x + R s x) - (q * F t x + R t x)) ^ 2 ≤
          major x := by
      intro x
      have hsquare :
          (q * (F s x - F t x) + (R s x - R t x)) ^ 2 ≤
            2 * (q * (F s x - F t x)) ^ 2 +
              2 * (R s x - R t x) ^ 2 := by
        nlinarith [sq_nonneg
          (q * (F s x - F t x) - (R s x - R t x))]
      dsimp only [major]
      convert hsquare using 1 <;> ring
    have hout : Integrable (fun x =>
        ((q * F s x + R s x) - (q * F t x + R t x)) ^ 2) volume := by
      refine hmajor.mono' (hsmeas.pow 2) ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpoint x
    refine ⟨hout, ?_⟩
    calc
      (∫ x : ℝ,
          ((q * F s x + R s x) - (q * F t x + R t x)) ^ 2) ≤
          ∫ x : ℝ, major x := integral_mono hout hmajor hpoint
      _ = upper s := by
        dsimp only [major, upper]
        rw [integral_add, integral_const_mul, integral_const_mul]
        · exact hsF.const_mul _
        · exact hsR.const_mul _
  constructor
  · exact hdata.mono fun _ hs => hs.1
  · exact squeeze_zero'
      (Eventually.of_forall fun s => integral_nonneg fun x => sq_nonneg _)
      (hdata.mono fun _ hs => hs.2) hupper_zero

/-- Exact-weight strong `L²` continuity of the expanded generator forcing,
assembled from the independently proved flux and reaction trajectories. -/
theorem paper5WeightedGeneratorForcingExpandedTrajectory_strongL2At_of_flux_reaction
    (p : CMParams) (eta : ℝ)
    {u v : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {W Wx Z Zx : ℝ → ℝ → ℝ} {t : ℝ}
    (hflux_meas : ∀ s, AEStronglyMeasurable
      (paper5WeightedFluxDerivativeExpandedTrajectory
        p eta u v U W Wx Z Zx s) volume)
    (hreact_meas : ∀ s, AEStronglyMeasurable
      (paper5WeightedReactionExpandedTrajectory p u U W s) volume)
    (hflux_int : ∀ᶠ s in 𝓝 t, Integrable (fun x =>
      (paper5WeightedFluxDerivativeExpandedTrajectory
          p eta u v U W Wx Z Zx s x -
        paper5WeightedFluxDerivativeExpandedTrajectory
          p eta u v U W Wx Z Zx t x) ^ 2) volume)
    (hreact_int : ∀ᶠ s in 𝓝 t, Integrable (fun x =>
      (paper5WeightedReactionExpandedTrajectory p u U W s x -
        paper5WeightedReactionExpandedTrajectory p u U W t x) ^ 2) volume)
    (hflux_zero : Tendsto (fun s => ∫ x : ℝ,
      (paper5WeightedFluxDerivativeExpandedTrajectory
          p eta u v U W Wx Z Zx s x -
        paper5WeightedFluxDerivativeExpandedTrajectory
          p eta u v U W Wx Z Zx t x) ^ 2) (𝓝 t) (𝓝 0))
    (hreact_zero : Tendsto (fun s => ∫ x : ℝ,
      (paper5WeightedReactionExpandedTrajectory p u U W s x -
        paper5WeightedReactionExpandedTrajectory p u U W t x) ^ 2)
      (𝓝 t) (𝓝 0)) :
    (∀ᶠ s in 𝓝 t, Integrable (fun x =>
      (paper5WeightedGeneratorForcingExpandedTrajectory
          p eta u v U W Wx Z Zx s x -
        paper5WeightedGeneratorForcingExpandedTrajectory
          p eta u v U W Wx Z Zx t x) ^ 2) volume) ∧
      Tendsto (fun s => ∫ x : ℝ,
        (paper5WeightedGeneratorForcingExpandedTrajectory
            p eta u v U W Wx Z Zx s x -
          paper5WeightedGeneratorForcingExpandedTrajectory
            p eta u v U W Wx Z Zx t x) ^ 2)
        (𝓝 t) (𝓝 0) := by
  have hout_meas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (fun x =>
      (-p.χ *
          paper5WeightedFluxDerivativeExpandedTrajectory
            p eta u v U W Wx Z Zx s x +
        paper5WeightedReactionExpandedTrajectory p u U W s x) -
      (-p.χ *
          paper5WeightedFluxDerivativeExpandedTrajectory
            p eta u v U W Wx Z Zx t x +
        paper5WeightedReactionExpandedTrajectory p u U W t x)) volume :=
    Eventually.of_forall fun s =>
      (((hflux_meas s).const_mul (-p.χ)).add (hreact_meas s)).sub
        (((hflux_meas t).const_mul (-p.χ)).add (hreact_meas t))
  simpa [paper5WeightedGeneratorForcingExpandedTrajectory] using
    (eventually_integrable_and_tendsto_integral_const_mul_add_sub_sq_zero
      (F := paper5WeightedFluxDerivativeExpandedTrajectory
        p eta u v U W Wx Z Zx)
      (R := paper5WeightedReactionExpandedTrajectory p u U W)
      (q := -p.χ) hout_meas hflux_int hreact_int hflux_zero hreact_zero)

section AxiomAudit

#print axioms paper5WeightedGeneratorForcingExpandedTrajectory_eq
#print axioms
  paper5WeightedFluxDerivativeExpandedTrajectory_aestronglyMeasurable
#print axioms
  paper5WeightedReactionExpandedTrajectory_aestronglyMeasurable
#print axioms eventually_integrable_and_tendsto_integral_mul_sub_mul_sq_zero
#print axioms paper5WeightedFluxDerivativeExpandedTrajectory_strongL2At
#print axioms paper5WeightedReactionExpandedTrajectory_strongL2At
#print axioms eventually_integrable_and_tendsto_integral_const_mul_add_sub_sq_zero
#print axioms
  paper5WeightedGeneratorForcingExpandedTrajectory_strongL2At_of_flux_reaction

end AxiomAudit

end ShenWork.Paper1
