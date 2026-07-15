import ShenWork.Paper1.WholeLineWeightedRegularityLinearSource
import ShenWork.Paper1.Theorem12EnergyProducer

open Filter MeasureTheory Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Weighted chemotactic-flux derivative in `L2`

The corrected flux expansion contains only the four canonical weighted
fields `W`, `Wx`, `Z`, and `Zx`.  This file records the exact conjugated
identity and the static `L2` estimate needed before applying the strict
weight-gap interpolation in time.
-/

/-- The corrected conjugated derivative of the chemotactic flux difference,
written as four bounded coefficients multiplying `Wx`, `W`, `Zx`, and `Z`.
-/
def paper5WeightedFluxDerivativeExpanded
    (p : CMParams) (eta : ℝ)
    (u v : ℝ → ℝ → ℝ) (U : ℝ → ℝ)
    (W Wx Z Zx : ℝ → ℝ) (t x : ℝ) : ℝ :=
  paper5B1 p u v t x * Wx x +
    (paper5B2 p u v U t x +
        paper5CorrectedChemZeroCoefficient p u v U t x -
          eta * paper5B1 p u v t x) * W x +
    paper5B3 p U x * Zx x +
    (paper5B4 p U x - eta * paper5B3 p U x) * Z x

/-- Exact exponential conjugation of the corrected flux-derivative identity.
The two derivative realizations are supplied by the classical PDE and the
traveling-wave elliptic equation. -/
theorem paper5WeightedFluxDerivativeExpanded_eq
    (p : CMParams) {T eta c t x : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hsol : IsClassicalSolution p T u v) (ht0 : 0 < t) (htT : t < T)
    (hTW : IsTravelingWave p c U V)
    (hu : 0 ≤ coMovingPath c u t x) (hU : 0 ≤ U x)
    (hu1 : ContDiff ℝ 1 (coMovingPath c u t))
    (hv2 : ContDiff ℝ 2 (coMovingPath c v t))
    (hU1 : ContDiff ℝ 1 U) (hV2 : ContDiff ℝ 2 V) :
    Real.exp (eta * x) *
        (deriv
            (fun y => (coMovingPath c u t y) ^ p.m *
              deriv (coMovingPath c v t) y) x -
          deriv (fun y => (U y) ^ p.m * deriv V y) x) =
      paper5WeightedFluxDerivativeExpanded p eta
        (coMovingPath c u) (coMovingPath c v) U
        (paper5WeightedPopulation eta (coMovingPath c u) U t)
        (paper5WeightedPopulationX eta (coMovingPath c u) U t)
        (paper5WeightedSignal eta (coMovingPath c v) V t)
        (paper5WeightedSignalX eta (coMovingPath c v) V t) t x := by
  rw [paper5CoMovingFluxDerivative_realization_of_classical
      p hsol ht0 htT hu1 hv2,
    paper5WaveFluxDerivative_realization p hTW hU1 hV2,
    paper5ChemFluxDifference_expansion_corrected p
      (coMovingPath c u) (coMovingPath c v) U V t x hu hU]
  unfold paper5WeightedFluxDerivativeExpanded
  unfold paper5WeightedPopulationX paper5WeightedPopulation
  unfold paper5WeightedSignalX paper5WeightedSignal
  unfold paper5CorrectedChemZeroCoefficient
  ring

/-- Pointwise four-square estimate for the expanded weighted flux derivative.
-/
theorem paper5WeightedFluxDerivativeExpanded_sq_le
    (p : CMParams) {eta t x B1 B2 B0 B3 B4 : ℝ}
    {u v : ℝ → ℝ → ℝ} {U W Wx Z Zx : ℝ → ℝ}
    (hb1 : |paper5B1 p u v t x| ≤ B1)
    (hb2 : |paper5B2 p u v U t x| ≤ B2)
    (hb0 : |paper5CorrectedChemZeroCoefficient p u v U t x| ≤ B0)
    (hb3 : |paper5B3 p U x| ≤ B3)
    (hb4 : |paper5B4 p U x| ≤ B4) :
    paper5WeightedFluxDerivativeExpanded p eta u v U W Wx Z Zx t x ^ 2 ≤
      4 *
        (B1 ^ 2 * Wx x ^ 2 +
          (B2 + B0 + |eta| * B1) ^ 2 * W x ^ 2 +
          B3 ^ 2 * Zx x ^ 2 +
          (B4 + |eta| * B3) ^ 2 * Z x ^ 2) := by
  have hB1 : 0 ≤ B1 := (abs_nonneg _).trans hb1
  have hB2 : 0 ≤ B2 := (abs_nonneg _).trans hb2
  have hB0 : 0 ≤ B0 := (abs_nonneg _).trans hb0
  have hB3 : 0 ≤ B3 := (abs_nonneg _).trans hb3
  have hB4 : 0 ≤ B4 := (abs_nonneg _).trans hb4
  let q1 := paper5B1 p u v t x * Wx x
  let q2 := (paper5B2 p u v U t x +
      paper5CorrectedChemZeroCoefficient p u v U t x -
        eta * paper5B1 p u v t x) * W x
  let q3 := paper5B3 p U x * Zx x
  let q4 := (paper5B4 p U x - eta * paper5B3 p U x) * Z x
  have hq1 : q1 ^ 2 ≤ B1 ^ 2 * Wx x ^ 2 := by
    have hab : |q1| ≤ B1 * |Wx x| := by
      dsimp only [q1]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hb1 (abs_nonneg _)
    have hs := (sq_le_sq₀ (abs_nonneg q1)
      (mul_nonneg hB1 (abs_nonneg (Wx x)))).2 hab
    simpa only [sq_abs, mul_pow] using hs
  have hq2 : q2 ^ 2 ≤
      (B2 + B0 + |eta| * B1) ^ 2 * W x ^ 2 := by
    have hcoef :
        |paper5B2 p u v U t x +
            paper5CorrectedChemZeroCoefficient p u v U t x -
              eta * paper5B1 p u v t x| ≤
          B2 + B0 + |eta| * B1 := by
      calc
        |paper5B2 p u v U t x +
            paper5CorrectedChemZeroCoefficient p u v U t x -
              eta * paper5B1 p u v t x| ≤
            |paper5B2 p u v U t x| +
              |paper5CorrectedChemZeroCoefficient p u v U t x| +
                |eta| * |paper5B1 p u v t x| := by
          calc
            |paper5B2 p u v U t x +
                paper5CorrectedChemZeroCoefficient p u v U t x -
                  eta * paper5B1 p u v t x| ≤
                |paper5B2 p u v U t x +
                  paper5CorrectedChemZeroCoefficient p u v U t x| +
                  |eta * paper5B1 p u v t x| := abs_sub _ _
            _ ≤ (|paper5B2 p u v U t x| +
                  |paper5CorrectedChemZeroCoefficient p u v U t x|) +
                  |eta| * |paper5B1 p u v t x| := by
              rw [abs_mul]
              exact add_le_add (abs_add_le _ _) le_rfl
        _ ≤ B2 + B0 + |eta| * B1 := by
          exact add_le_add (add_le_add hb2 hb0)
            (mul_le_mul_of_nonneg_left hb1 (abs_nonneg _))
    have hcoeff0 : 0 ≤ B2 + B0 + |eta| * B1 := by positivity
    have hab : |q2| ≤
        (B2 + B0 + |eta| * B1) * |W x| := by
      dsimp only [q2]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
    have hs := (sq_le_sq₀ (abs_nonneg q2)
      (mul_nonneg hcoeff0 (abs_nonneg (W x)))).2 hab
    simpa only [sq_abs, mul_pow] using hs
  have hq3 : q3 ^ 2 ≤ B3 ^ 2 * Zx x ^ 2 := by
    have hab : |q3| ≤ B3 * |Zx x| := by
      dsimp only [q3]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hb3 (abs_nonneg _)
    have hs := (sq_le_sq₀ (abs_nonneg q3)
      (mul_nonneg hB3 (abs_nonneg (Zx x)))).2 hab
    simpa only [sq_abs, mul_pow] using hs
  have hq4 : q4 ^ 2 ≤ (B4 + |eta| * B3) ^ 2 * Z x ^ 2 := by
    have hcoef : |paper5B4 p U x - eta * paper5B3 p U x| ≤
        B4 + |eta| * B3 := by
      calc
        |paper5B4 p U x - eta * paper5B3 p U x| ≤
            |paper5B4 p U x| + |eta| * |paper5B3 p U x| := by
          simpa only [abs_mul] using
            (abs_sub (paper5B4 p U x) (eta * paper5B3 p U x))
        _ ≤ B4 + |eta| * B3 :=
          add_le_add hb4
            (mul_le_mul_of_nonneg_left hb3 (abs_nonneg _))
    have hcoeff0 : 0 ≤ B4 + |eta| * B3 := by positivity
    have hab : |q4| ≤ (B4 + |eta| * B3) * |Z x| := by
      dsimp only [q4]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
    have hs := (sq_le_sq₀ (abs_nonneg q4)
      (mul_nonneg hcoeff0 (abs_nonneg (Z x)))).2 hab
    simpa only [sq_abs, mul_pow] using hs
  calc
    paper5WeightedFluxDerivativeExpanded p eta u v U W Wx Z Zx t x ^ 2 =
        (q1 + q2 + q3 + q4) ^ 2 := by
      dsimp only [paper5WeightedFluxDerivativeExpanded, q1, q2, q3, q4]
    _ ≤ 4 * (q1 ^ 2 + q2 ^ 2 + q3 ^ 2 + q4 ^ 2) :=
      paper5_four_term_sq_le_four_sum_sq q1 q2 q3 q4
    _ ≤ 4 *
        (B1 ^ 2 * Wx x ^ 2 +
          (B2 + B0 + |eta| * B1) ^ 2 * W x ^ 2 +
          B3 ^ 2 * Zx x ^ 2 +
          (B4 + |eta| * B3) ^ 2 * Z x ^ 2) := by
      nlinarith

/-- Static `L2` closure for the corrected weighted flux derivative.  The
measurability premise is explicit; canonical positive-time trajectories
supply it from their BUC flux-derivative representative. -/
theorem paper5WeightedFluxDerivativeExpanded_sq_integrable
    (p : CMParams) {eta t B1 B2 B0 B3 B4 : ℝ}
    {u v : ℝ → ℝ → ℝ} {U W Wx Z Zx : ℝ → ℝ}
    (hsource_meas : AEStronglyMeasurable
      (paper5WeightedFluxDerivativeExpanded p eta u v U W Wx Z Zx t))
    (hb1 : ∀ x, |paper5B1 p u v t x| ≤ B1)
    (hb2 : ∀ x, |paper5B2 p u v U t x| ≤ B2)
    (hb0 : ∀ x,
      |paper5CorrectedChemZeroCoefficient p u v U t x| ≤ B0)
    (hb3 : ∀ x, |paper5B3 p U x| ≤ B3)
    (hb4 : ∀ x, |paper5B4 p U x| ≤ B4)
    (hW2 : Integrable (fun x => W x ^ 2))
    (hWx2 : Integrable (fun x => Wx x ^ 2))
    (hZ2 : Integrable (fun x => Z x ^ 2))
    (hZx2 : Integrable (fun x => Zx x ^ 2)) :
    Integrable (fun x =>
      paper5WeightedFluxDerivativeExpanded p eta
        u v U W Wx Z Zx t x ^ 2) := by
  let major : ℝ → ℝ := fun x => 4 *
    (B1 ^ 2 * Wx x ^ 2 +
      (B2 + B0 + |eta| * B1) ^ 2 * W x ^ 2 +
      B3 ^ 2 * Zx x ^ 2 +
      (B4 + |eta| * B3) ^ 2 * Z x ^ 2)
  have hmajor : Integrable major := by
    have h1 := hWx2.const_mul (B1 ^ 2)
    have h2 := hW2.const_mul ((B2 + B0 + |eta| * B1) ^ 2)
    have h3 := hZx2.const_mul (B3 ^ 2)
    have h4 := hZ2.const_mul ((B4 + |eta| * B3) ^ 2)
    exact (((h1.add h2).add h3).add h4).const_mul 4
  refine hmajor.mono' (hsource_meas.pow 2) ?_
  filter_upwards with x
  have hsq := paper5WeightedFluxDerivativeExpanded_sq_le
    (p := p) (eta := eta) (t := t) (x := x)
    (u := u) (v := v) (U := U) (W := W) (Wx := Wx) (Z := Z) (Zx := Zx)
    (hb1 x) (hb2 x) (hb0 x) (hb3 x) (hb4 x)
  have hnonneg : 0 ≤
      paper5WeightedFluxDerivativeExpanded p eta u v U W Wx Z Zx t x ^ 2 :=
    sq_nonneg _
  simpa only [major, Real.norm_eq_abs, abs_of_nonneg hnonneg] using hsq

/-- Integral-bound form of
`paper5WeightedFluxDerivativeExpanded_sq_integrable`.  This is the static
estimate used uniformly on a stronger-weight positive-time window. -/
theorem paper5WeightedFluxDerivativeExpanded_sq_integrable_and_integral_le
    (p : CMParams) {eta t B1 B2 B0 B3 B4 : ℝ}
    {u v : ℝ → ℝ → ℝ} {U W Wx Z Zx : ℝ → ℝ}
    (hsource_meas : AEStronglyMeasurable
      (paper5WeightedFluxDerivativeExpanded p eta u v U W Wx Z Zx t))
    (hb1 : ∀ x, |paper5B1 p u v t x| ≤ B1)
    (hb2 : ∀ x, |paper5B2 p u v U t x| ≤ B2)
    (hb0 : ∀ x,
      |paper5CorrectedChemZeroCoefficient p u v U t x| ≤ B0)
    (hb3 : ∀ x, |paper5B3 p U x| ≤ B3)
    (hb4 : ∀ x, |paper5B4 p U x| ≤ B4)
    (hW2 : Integrable (fun x => W x ^ 2))
    (hWx2 : Integrable (fun x => Wx x ^ 2))
    (hZ2 : Integrable (fun x => Z x ^ 2))
    (hZx2 : Integrable (fun x => Zx x ^ 2)) :
    Integrable (fun x =>
        paper5WeightedFluxDerivativeExpanded p eta
          u v U W Wx Z Zx t x ^ 2) ∧
      (∫ x : ℝ,
        paper5WeightedFluxDerivativeExpanded p eta
          u v U W Wx Z Zx t x ^ 2) ≤
        4 *
          (B1 ^ 2 * (∫ x : ℝ, Wx x ^ 2) +
            (B2 + B0 + |eta| * B1) ^ 2 * (∫ x : ℝ, W x ^ 2) +
            B3 ^ 2 * (∫ x : ℝ, Zx x ^ 2) +
            (B4 + |eta| * B3) ^ 2 * (∫ x : ℝ, Z x ^ 2)) := by
  have hsource := paper5WeightedFluxDerivativeExpanded_sq_integrable p
    hsource_meas hb1 hb2 hb0 hb3 hb4 hW2 hWx2 hZ2 hZx2
  refine ⟨hsource, ?_⟩
  let f1 : ℝ → ℝ := fun x => B1 ^ 2 * Wx x ^ 2
  let f2 : ℝ → ℝ := fun x =>
    (B2 + B0 + |eta| * B1) ^ 2 * W x ^ 2
  let f3 : ℝ → ℝ := fun x => B3 ^ 2 * Zx x ^ 2
  let f4 : ℝ → ℝ := fun x =>
    (B4 + |eta| * B3) ^ 2 * Z x ^ 2
  let major : ℝ → ℝ := fun x =>
    4 * (f1 x + f2 x + f3 x + f4 x)
  have hf1 : Integrable f1 := hWx2.const_mul (B1 ^ 2)
  have hf2 : Integrable f2 :=
    hW2.const_mul ((B2 + B0 + |eta| * B1) ^ 2)
  have hf3 : Integrable f3 := hZx2.const_mul (B3 ^ 2)
  have hf4 : Integrable f4 :=
    hZ2.const_mul ((B4 + |eta| * B3) ^ 2)
  have hf12 : Integrable (fun x => f1 x + f2 x) := hf1.add hf2
  have hf123 : Integrable (fun x => f1 x + f2 x + f3 x) :=
    hf12.add hf3
  have hsum : Integrable (fun x => f1 x + f2 x + f3 x + f4 x) :=
    hf123.add hf4
  have hmajor : Integrable major := hsum.const_mul 4
  have hpoint : ∀ x,
      paper5WeightedFluxDerivativeExpanded p eta
          u v U W Wx Z Zx t x ^ 2 ≤ major x := by
    intro x
    simpa only [major, f1, f2, f3, f4] using
      (paper5WeightedFluxDerivativeExpanded_sq_le p
        (hb1 x) (hb2 x) (hb0 x) (hb3 x) (hb4 x))
  calc
    (∫ x : ℝ,
        paper5WeightedFluxDerivativeExpanded p eta
          u v U W Wx Z Zx t x ^ 2) ≤ ∫ x : ℝ, major x :=
      integral_mono hsource hmajor hpoint
    _ = 4 *
          (B1 ^ 2 * (∫ x : ℝ, Wx x ^ 2) +
            (B2 + B0 + |eta| * B1) ^ 2 * (∫ x : ℝ, W x ^ 2) +
            B3 ^ 2 * (∫ x : ℝ, Zx x ^ 2) +
            (B4 + |eta| * B3) ^ 2 * (∫ x : ℝ, Z x ^ 2)) := by
      rw [show major = fun x => 4 * (f1 x + f2 x + f3 x + f4 x) by rfl,
        integral_const_mul, integral_add hf123 hf4,
        integral_add hf12 hf3, integral_add hf1 hf2]
      simp only [f1, f2, f3, f4, integral_const_mul]

/-- Explicit static square budget for the genuine weighted flux derivative
in terms of the population weighted `H1` energies. -/
def paper5WeightedFluxDerivativeH1SquareBound
    (p : CMParams) (M eta EW EWx : ℝ) : ℝ :=
  4 *
    (paper5CommonB1 p M ^ 2 * EWx +
      (paper5CommonB2 p M +
          (2 * p.m + p.γ) * M ^ (p.m + p.γ - 1) +
          |eta| * paper5CommonB1 p M) ^ 2 * EW +
      paper5CommonB3 p M ^ 2 *
        (paper5WeightedResolverVxFactor p M eta * EW) +
      (paper5CommonB4 p M + |eta| * paper5CommonB3 p M) ^ 2 *
        (paper5WeightedResolverVFactor p M eta * EW))

/-- The genuine exponentially weighted chemotactic-flux derivative is in
`L2` at every positive classical time once the population perturbation is in
weighted `H1`.  All signal terms are produced internally by the frozen
elliptic resolver.  Measurability of the genuine derivative representative
is derived internally from the classical `C2` slices and the two exact flux
realization identities. -/
theorem paper5WeightedFluxDerivative_data_of_population_H1
    (p : CMParams) {M T eta c t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hchi : p.χ ≠ 0)
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (heta : 0 < eta) (hetaCap : eta < stabilityWeightCap p)
    (hsol : IsClassicalSolution p T u v) (ht0 : 0 < t) (htT : t < T)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hMChiM : MChi p ≤ M)
    (hu2 : ContDiff ℝ 2 (coMovingPath c u t))
    (hv2 : ContDiff ℝ 2 (coMovingPath c v t))
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V)
    (huM : ∀ x, coMovingPath c u t x ∈ Set.Icc (0 : ℝ) M)
    (hvEq : coMovingPath c v t =
      frozenElliptic p (coMovingPath c u t))
    (hclose : Integrable (fun x =>
      Real.exp (2 * eta * x) * |coMovingPath c u t x - U x| ^ 2))
    (hWx2 : Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U t x ^ 2)) :
    Integrable (fun x : ℝ =>
        (Real.exp (eta * x) *
          (deriv
              (fun y => (coMovingPath c u t y) ^ p.m *
                deriv (coMovingPath c v t) y) x -
            deriv (fun y => (U y) ^ p.m * deriv V y) x)) ^ 2) ∧
      (∫ x : ℝ,
        (Real.exp (eta * x) *
          (deriv
              (fun y => (coMovingPath c u t y) ^ p.m *
                deriv (coMovingPath c v t) y) x -
            deriv (fun y => (U y) ^ p.m * deriv V y) x)) ^ 2) ≤
        paper5WeightedFluxDerivativeH1SquareBound p M eta
          (∫ x : ℝ,
            Real.exp (2 * eta * x) *
              |coMovingPath c u t x - U x| ^ 2)
          (∫ x : ℝ,
            paper5WeightedPopulationX eta
              (coMovingPath c u) U t x ^ 2) := by
  have hMChi1 : 1 ≤ MChi p := MChi_ge_one_of_travelingWave hTW hbound
  have hM1 : 1 ≤ M := hMChi1.trans hMChiM
  have hM0 : 0 ≤ M := zero_le_one.trans hM1
  have huC : IsCUnifBdd (coMovingPath c u t) := by
    refine ⟨hu2.continuous, ⟨M, fun x => ?_⟩⟩
    rw [abs_of_nonneg (huM x).1]
    exact (huM x).2
  have hUC : IsCUnifBdd U :=
    U_isCUnifBdd_of_continuous hbound hreg.U_cont
  have hUM : ∀ x, U x ∈ Set.Icc (0 : ℝ) M :=
    fun x => ⟨(hTW.U_pos x).le, (hbound.le_MChi x).trans hMChiM⟩
  have hVEq : V = frozenElliptic p U :=
    IsTravelingWave.V_eq_frozenElliptic_full hTW hbound hreg
  have hgamma0 : 0 ≤ p.γ := zero_le_one.trans p.hγ
  have hugamma : ∀ x, (coMovingPath c u t x) ^ p.γ ≤ M ^ p.γ :=
    fun x => Real.rpow_le_rpow (huM x).1 (huM x).2 hgamma0
  have hvUpper : ∀ x, coMovingPath c v t x ≤ M ^ p.γ := by
    intro x
    rw [hvEq]
    exact frozenElliptic_le_of_rpow_le p (Real.rpow_nonneg hM0 _)
      hu2.continuous (fun y => (huM y).1) hugamma x
  have hvM : ∀ x,
      coMovingPath c v t x ∈ Set.Icc (0 : ℝ) (M ^ p.γ) := by
    intro x
    constructor
    · rw [hvEq]
      exact frozenElliptic_nonneg p (fun y => (huM y).1) x
    · exact hvUpper x
  have hvDeriv : ∀ x,
      |deriv (coMovingPath c v t) x| ≤ M ^ p.γ := by
    intro x
    have hx := hvUpper x
    rw [hvEq] at hx ⊢
    exact (frozenElliptic_deriv_abs_le p huC
      (fun y => (huM y).1) x).trans hx
  have hspeed := remark5SpeedCondition_of_correctedCStarStar_lt p hc
  have hbarrier := barrierSpeed_lt_of_correctedCStarStar_lt p hc
  have hcoeff : ∀ x,
      |paper5B1 p (coMovingPath c u) (coMovingPath c v) t x| ≤
          paper5CommonB1 p M ∧
        |paper5B2 p (coMovingPath c u) (coMovingPath c v) U t x| ≤
          paper5CommonB2 p M ∧
        |paper5B3 p U x| ≤ paper5CommonB3 p M ∧
        |paper5B4 p U x| ≤ paper5CommonB4 p M := by
    intro x
    have hx := paper5CoefficientBounds_of_barrier_speed_common_bound p
      (sigma := paper5Sigma) (t := t) (x := x)
      (by norm_num [paper5Sigma]) hchi hspeed hbarrier hTW hreg hbound
      hMChiM (huM x) (hvDeriv x)
    simpa only [paper5CommonB1, paper5CommonB2, paper5CommonB3,
      paper5CommonB4, paper5ConcreteLu] using hx
  have heta1 : eta < 1 := by
    have hcap1 : stabilityWeightCap p ≤ 1 := by
      unfold stabilityWeightCap
      rw [div_le_one (by positivity)]
      exact le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _)
    exact hetaCap.trans_le hcap1
  have hsignal := paper5WeightedSignal_resolver_data p hM1 heta heta1
    huC hUC huM hUM hvEq hVEq
    (hv2.differentiable (by norm_num))
    (hV2.differentiable (by norm_num)) hclose
  have hW2 : Integrable (fun x =>
      paper5WeightedPopulation eta (coMovingPath c u) U t x ^ 2) := by
    refine hclose.congr (Eventually.of_forall fun x => ?_)
    change Real.exp (2 * eta * x) *
        |coMovingPath c u t x - U x| ^ 2 =
      (Real.exp (eta * x) * (coMovingPath c u t x - U x)) ^ 2
    rw [mul_pow, sq_abs]
    congr 1
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  let actual : ℝ → ℝ := fun x =>
    Real.exp (eta * x) *
      (deriv
          (fun y => (coMovingPath c u t y) ^ p.m *
            deriv (coMovingPath c v t) y) x -
        deriv (fun y => (U y) ^ p.m * deriv V y) x)
  let physical : ℝ → ℝ := fun x => Real.exp (eta * x) *
    ((p.m * (coMovingPath c u t x) ^ (p.m - 1) *
          deriv (coMovingPath c u t) x * deriv (coMovingPath c v t) x +
        (coMovingPath c u t x) ^ p.m *
          (coMovingPath c v t x - (coMovingPath c u t x) ^ p.γ)) -
      (p.m * (U x) ^ (p.m - 1) * deriv U x * deriv V x +
        (U x) ^ p.m * (V x - (U x) ^ p.γ)))
  have hphysical_cont : Continuous physical := by
    have hexp : Continuous (fun x : ℝ => Real.exp (eta * x)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have hu : Continuous (coMovingPath c u t) := hu2.continuous
    have hv : Continuous (coMovingPath c v t) := hv2.continuous
    have hU : Continuous U := hU2.continuous
    have hV : Continuous V := hV2.continuous
    have hux : Continuous (deriv (coMovingPath c u t)) :=
      hu2.continuous_deriv (by norm_num)
    have hvx : Continuous (deriv (coMovingPath c v t)) :=
      hv2.continuous_deriv (by norm_num)
    have hUx : Continuous (deriv U) := hU2.continuous_deriv (by norm_num)
    have hVx : Continuous (deriv V) := hV2.continuous_deriv (by norm_num)
    have hm0 : 0 ≤ p.m := zero_le_one.trans p.hm
    have hm10 : 0 ≤ p.m - 1 := sub_nonneg.mpr p.hm
    have hgamma0' : 0 ≤ p.γ := zero_le_one.trans p.hγ
    have hupowm : Continuous (fun x => (coMovingPath c u t x) ^ p.m) :=
      (Real.continuous_rpow_const hm0).comp hu
    have hupowm1 : Continuous
        (fun x => (coMovingPath c u t x) ^ (p.m - 1)) :=
      (Real.continuous_rpow_const hm10).comp hu
    have hupowgamma : Continuous
        (fun x => (coMovingPath c u t x) ^ p.γ) :=
      (Real.continuous_rpow_const hgamma0').comp hu
    have hUpowm : Continuous (fun x => (U x) ^ p.m) :=
      (Real.continuous_rpow_const hm0).comp hU
    have hUpowm1 : Continuous (fun x => (U x) ^ (p.m - 1)) :=
      (Real.continuous_rpow_const hm10).comp hU
    have hUpowgamma : Continuous (fun x => (U x) ^ p.γ) :=
      (Real.continuous_rpow_const hgamma0').comp hU
    have hdynamic : Continuous (fun x =>
        p.m * (coMovingPath c u t x) ^ (p.m - 1) *
            deriv (coMovingPath c u t) x * deriv (coMovingPath c v t) x +
          (coMovingPath c u t x) ^ p.m *
            (coMovingPath c v t x - (coMovingPath c u t x) ^ p.γ)) :=
      (((continuous_const.mul hupowm1).mul hux).mul hvx).add
        (hupowm.mul (hv.sub hupowgamma))
    have hwave : Continuous (fun x =>
        p.m * (U x) ^ (p.m - 1) * deriv U x * deriv V x +
          (U x) ^ p.m * (V x - (U x) ^ p.γ)) :=
      (((continuous_const.mul hUpowm1).mul hUx).mul hVx).add
        (hUpowm.mul (hV.sub hUpowgamma))
    dsimp only [physical]
    exact hexp.mul (hdynamic.sub hwave)
  have hactual_physical : ∀ x, actual x = physical x := by
    intro x
    dsimp only [actual, physical]
    rw [paper5CoMovingFluxDerivative_realization_of_classical
        p hsol ht0 htT (hu2.of_le (by norm_num)) hv2,
      paper5WaveFluxDerivative_realization p hTW
        (hU2.of_le (by norm_num)) hV2]
  have hactual_meas : AEStronglyMeasurable actual volume := by
    exact hphysical_cont.aestronglyMeasurable.congr
      (Eventually.of_forall fun x => (hactual_physical x).symm)
  let expanded : ℝ → ℝ :=
    paper5WeightedFluxDerivativeExpanded p eta
      (coMovingPath c u) (coMovingPath c v) U
      (paper5WeightedPopulation eta (coMovingPath c u) U t)
      (paper5WeightedPopulationX eta (coMovingPath c u) U t)
      (paper5WeightedSignal eta (coMovingPath c v) V t)
      (paper5WeightedSignalX eta (coMovingPath c v) V t) t
  have heq : ∀ x, actual x = expanded x := by
    intro x
    exact paper5WeightedFluxDerivativeExpanded_eq p hsol ht0 htT hTW
      (huM x).1 (hTW.U_pos x).le
      (hu2.of_le (by norm_num)) hv2 (hU2.of_le (by norm_num)) hV2
  have hexpanded_meas : AEStronglyMeasurable expanded volume := by
    exact hactual_meas.congr (Eventually.of_forall heq)
  have hb0 : ∀ x,
      |paper5CorrectedChemZeroCoefficient p
        (coMovingPath c u) (coMovingPath c v) U t x| ≤
        (2 * p.m + p.γ) * M ^ (p.m + p.γ - 1) := by
    intro x
    exact paper5CorrectedChemZeroCoefficient_abs_le p
      hM0 (huM x) (hUM x) (hvM x)
  have hexpanded_data :=
    paper5WeightedFluxDerivativeExpanded_sq_integrable_and_integral_le p
      hexpanded_meas (fun x => (hcoeff x).1)
      (fun x => (hcoeff x).2.1) hb0
      (fun x => (hcoeff x).2.2.1) (fun x => (hcoeff x).2.2.2)
      hW2 hWx2 hsignal.1 hsignal.2.1
  have hactual_int : Integrable (fun x => actual x ^ 2) := by
    refine hexpanded_data.1.congr (Eventually.of_forall fun x => ?_)
    change expanded x ^ 2 = actual x ^ 2
    rw [heq x]
  refine ⟨by simpa only [actual] using hactual_int, ?_⟩
  have hintegral_eq : (∫ x : ℝ, actual x ^ 2) =
      ∫ x : ℝ, expanded x ^ 2 := by
    apply integral_congr_ae
    filter_upwards with x
    rw [heq x]
  have hWIntegral :
      (∫ x : ℝ,
          paper5WeightedPopulation eta (coMovingPath c u) U t x ^ 2) =
        ∫ x : ℝ,
          Real.exp (2 * eta * x) *
            |coMovingPath c u t x - U x| ^ 2 := by
    apply integral_congr_ae
    filter_upwards with x
    change (Real.exp (eta * x) *
        (coMovingPath c u t x - U x)) ^ 2 =
      Real.exp (2 * eta * x) *
        |coMovingPath c u t x - U x| ^ 2
    rw [mul_pow, sq_abs]
    congr 1
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hZxTerm :
      paper5CommonB3 p M ^ 2 *
          (∫ x : ℝ,
            paper5WeightedSignalX eta (coMovingPath c v) V t x ^ 2) ≤
        paper5CommonB3 p M ^ 2 *
          (paper5WeightedResolverVxFactor p M eta *
            ∫ x : ℝ,
              paper5WeightedPopulation eta
                (coMovingPath c u) U t x ^ 2) :=
    mul_le_mul_of_nonneg_left hsignal.2.2.2 (sq_nonneg _)
  have hZTerm :
      (paper5CommonB4 p M + |eta| * paper5CommonB3 p M) ^ 2 *
          (∫ x : ℝ,
            paper5WeightedSignal eta (coMovingPath c v) V t x ^ 2) ≤
        (paper5CommonB4 p M + |eta| * paper5CommonB3 p M) ^ 2 *
          (paper5WeightedResolverVFactor p M eta *
            ∫ x : ℝ,
              paper5WeightedPopulation eta
                (coMovingPath c u) U t x ^ 2) :=
    mul_le_mul_of_nonneg_left hsignal.2.2.1 (sq_nonneg _)
  calc
    (∫ x : ℝ,
        (Real.exp (eta * x) *
          (deriv
              (fun y => (coMovingPath c u t y) ^ p.m *
                deriv (coMovingPath c v t) y) x -
            deriv (fun y => (U y) ^ p.m * deriv V y) x)) ^ 2) =
        ∫ x : ℝ, expanded x ^ 2 := by
      simpa only [actual] using hintegral_eq
    _ ≤ 4 *
        (paper5CommonB1 p M ^ 2 *
            (∫ x : ℝ,
              paper5WeightedPopulationX eta
                (coMovingPath c u) U t x ^ 2) +
          (paper5CommonB2 p M +
              (2 * p.m + p.γ) * M ^ (p.m + p.γ - 1) +
              |eta| * paper5CommonB1 p M) ^ 2 *
            (∫ x : ℝ,
              paper5WeightedPopulation eta
                (coMovingPath c u) U t x ^ 2) +
          paper5CommonB3 p M ^ 2 *
            (∫ x : ℝ,
              paper5WeightedSignalX eta
                (coMovingPath c v) V t x ^ 2) +
          (paper5CommonB4 p M + |eta| * paper5CommonB3 p M) ^ 2 *
            (∫ x : ℝ,
              paper5WeightedSignal eta
                (coMovingPath c v) V t x ^ 2)) :=
      hexpanded_data.2
    _ ≤ 4 *
        (paper5CommonB1 p M ^ 2 *
            (∫ x : ℝ,
              paper5WeightedPopulationX eta
                (coMovingPath c u) U t x ^ 2) +
          (paper5CommonB2 p M +
              (2 * p.m + p.γ) * M ^ (p.m + p.γ - 1) +
              |eta| * paper5CommonB1 p M) ^ 2 *
            (∫ x : ℝ,
              paper5WeightedPopulation eta
                (coMovingPath c u) U t x ^ 2) +
          paper5CommonB3 p M ^ 2 *
            (paper5WeightedResolverVxFactor p M eta *
              ∫ x : ℝ,
                paper5WeightedPopulation eta
                  (coMovingPath c u) U t x ^ 2) +
          (paper5CommonB4 p M + |eta| * paper5CommonB3 p M) ^ 2 *
            (paper5WeightedResolverVFactor p M eta *
              ∫ x : ℝ,
                paper5WeightedPopulation eta
                  (coMovingPath c u) U t x ^ 2)) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add le_rfl hZxTerm) hZTerm) (by norm_num)
    _ = paper5WeightedFluxDerivativeH1SquareBound p M eta
          (∫ x : ℝ,
            Real.exp (2 * eta * x) *
              |coMovingPath c u t x - U x| ^ 2)
          (∫ x : ℝ,
            paper5WeightedPopulationX eta
              (coMovingPath c u) U t x ^ 2) := by
      unfold paper5WeightedFluxDerivativeH1SquareBound
      rw [hWIntegral]

/-- Integrability projection of
`paper5WeightedFluxDerivative_data_of_population_H1`. -/
theorem paper5WeightedFluxDerivative_sq_integrable_of_population_H1
    (p : CMParams) {M T eta c t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hchi : p.χ ≠ 0)
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (heta : 0 < eta) (hetaCap : eta < stabilityWeightCap p)
    (hsol : IsClassicalSolution p T u v) (ht0 : 0 < t) (htT : t < T)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hMChiM : MChi p ≤ M)
    (hu2 : ContDiff ℝ 2 (coMovingPath c u t))
    (hv2 : ContDiff ℝ 2 (coMovingPath c v t))
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V)
    (huM : ∀ x, coMovingPath c u t x ∈ Set.Icc (0 : ℝ) M)
    (hvEq : coMovingPath c v t =
      frozenElliptic p (coMovingPath c u t))
    (hclose : Integrable (fun x =>
      Real.exp (2 * eta * x) * |coMovingPath c u t x - U x| ^ 2))
    (hWx2 : Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U t x ^ 2)) :
    Integrable (fun x : ℝ =>
      (Real.exp (eta * x) *
        (deriv
            (fun y => (coMovingPath c u t y) ^ p.m *
              deriv (coMovingPath c v t) y) x -
          deriv (fun y => (U y) ^ p.m * deriv V y) x)) ^ 2) :=
  (paper5WeightedFluxDerivative_data_of_population_H1 p hchi hc
    heta hetaCap hsol ht0 htT hTW hreg hbound hMChiM
    hu2 hv2 hU2 hV2 huM hvEq hclose hWx2).1

section AxiomAudit

#print axioms paper5WeightedFluxDerivativeExpanded_eq
#print axioms paper5WeightedFluxDerivativeExpanded_sq_le
#print axioms paper5WeightedFluxDerivativeExpanded_sq_integrable
#print axioms paper5WeightedFluxDerivativeExpanded_sq_integrable_and_integral_le
#print axioms paper5WeightedFluxDerivative_data_of_population_H1
#print axioms paper5WeightedFluxDerivative_sq_integrable_of_population_H1

end AxiomAudit

end ShenWork.Paper1
