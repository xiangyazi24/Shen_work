import ShenWork.Paper1.WholeLineWeightedRegularityFluxDerivative
import ShenWork.Paper1.WholeLineWeightedRegularityCap
import ShenWork.Paper1.WholeLineWeightedRegularityCapResolverValue

open Filter MeasureTheory

noncomputable section

namespace ShenWork.Paper1

/-!
# Cap-conjugated chemotactic-flux derivative

The corrected flux-derivative expansion is linear in its four weighted
fields.  Consequently any scalar exhaustion multiplier can be distributed
through the expansion.  This file records the resulting static `L²` estimate
without assuming exponential integrability of the population derivative.
-/

/-- A scalar multiplier distributes through the corrected four-field flux
derivative expansion. -/
theorem paper5WeightedFluxDerivativeExpanded_mul_fields
    (p : CMParams) (eta : ℝ)
    (u v : ℝ → ℝ → ℝ) (U W Wx Z Zx a : ℝ → ℝ)
    (t x : ℝ) :
    paper5WeightedFluxDerivativeExpanded p eta u v U
        (fun y => a y * W y) (fun y => a y * Wx y)
        (fun y => a y * Z y) (fun y => a y * Zx y) t x =
      a x * paper5WeightedFluxDerivativeExpanded p eta u v U
        W Wx Z Zx t x := by
  unfold paper5WeightedFluxDerivativeExpanded
  ring

/-- Static cap/exhaustion version of the corrected flux-derivative estimate.
Only the four multiplier-conjugated fields need to lie in `L²`; the theorem
does not presuppose the exact exponential derivative budget. -/
theorem multipliedFluxDerivativeExpanded_sq_integrable_and_integral_le
    (p : CMParams) {eta t B1 B2 B0 B3 B4 : ℝ}
    {u v : ℝ → ℝ → ℝ} {U W Wx Z Zx a : ℝ → ℝ}
    (hsource_meas : AEStronglyMeasurable (fun x =>
      a x * paper5WeightedFluxDerivativeExpanded p eta
        u v U W Wx Z Zx t x))
    (hb1 : ∀ x, |paper5B1 p u v t x| ≤ B1)
    (hb2 : ∀ x, |paper5B2 p u v U t x| ≤ B2)
    (hb0 : ∀ x,
      |paper5CorrectedChemZeroCoefficient p u v U t x| ≤ B0)
    (hb3 : ∀ x, |paper5B3 p U x| ≤ B3)
    (hb4 : ∀ x, |paper5B4 p U x| ≤ B4)
    (hW2 : Integrable (fun x => (a x * W x) ^ 2))
    (hWx2 : Integrable (fun x => (a x * Wx x) ^ 2))
    (hZ2 : Integrable (fun x => (a x * Z x) ^ 2))
    (hZx2 : Integrable (fun x => (a x * Zx x) ^ 2)) :
    Integrable (fun x =>
        (a x * paper5WeightedFluxDerivativeExpanded p eta
          u v U W Wx Z Zx t x) ^ 2) ∧
      (∫ x : ℝ,
        (a x * paper5WeightedFluxDerivativeExpanded p eta
          u v U W Wx Z Zx t x) ^ 2) ≤
        4 *
          (B1 ^ 2 * (∫ x : ℝ, (a x * Wx x) ^ 2) +
            (B2 + B0 + |eta| * B1) ^ 2 *
              (∫ x : ℝ, (a x * W x) ^ 2) +
            B3 ^ 2 * (∫ x : ℝ, (a x * Zx x) ^ 2) +
            (B4 + |eta| * B3) ^ 2 *
              (∫ x : ℝ, (a x * Z x) ^ 2)) := by
  let Wc : ℝ → ℝ := fun x => a x * W x
  let Wxc : ℝ → ℝ := fun x => a x * Wx x
  let Zc : ℝ → ℝ := fun x => a x * Z x
  let Zxc : ℝ → ℝ := fun x => a x * Zx x
  have hpoint : ∀ x,
      paper5WeightedFluxDerivativeExpanded p eta u v U
          Wc Wxc Zc Zxc t x =
        a x * paper5WeightedFluxDerivativeExpanded p eta
          u v U W Wx Z Zx t x := by
    intro x
    exact paper5WeightedFluxDerivativeExpanded_mul_fields
      p eta u v U W Wx Z Zx a t x
  have hmeas : AEStronglyMeasurable
      (paper5WeightedFluxDerivativeExpanded p eta
        u v U Wc Wxc Zc Zxc t) := by
    refine hsource_meas.congr ?_
    exact Eventually.of_forall fun x => (hpoint x).symm
  have hbase :=
    paper5WeightedFluxDerivativeExpanded_sq_integrable_and_integral_le
      p hmeas hb1 hb2 hb0 hb3 hb4
        (by simpa only [Wc] using hW2)
        (by simpa only [Wxc] using hWx2)
        (by simpa only [Zc] using hZ2)
        (by simpa only [Zxc] using hZx2)
  simpa only [hpoint, Wc, Wxc, Zc, Zxc] using hbase

/-- Cap-uniform square factor for the frozen-resolver value difference. -/
def capResolverValueSquareFactor (p : CMParams) (M eta : ℝ) : ℝ :=
  ((1 / (1 - eta)) * (p.γ * M ^ (p.γ - 1))) ^ 2

/-- Cap-uniform square factor for the raw first-derivative bracket of the
frozen-resolver difference. -/
def capResolverRawXSquareFactor (p : CMParams) (M eta : ℝ) : ℝ :=
  2 * (eta ^ 2 + 1) * capResolverValueSquareFactor p M eta

/-- Static budget for the cap-conjugated corrected flux derivative. -/
def capFluxDerivativeRawH1SquareBound
    (p : CMParams) (M eta B1 B2 B0 B3 B4 EW EWx : ℝ) : ℝ :=
  4 *
    (B1 ^ 2 * EWx +
      (B2 + B0 + |eta| * B1) ^ 2 * EW +
      B3 ^ 2 * (capResolverRawXSquareFactor p M eta * EW) +
      (B4 + |eta| * B3) ^ 2 *
        (capResolverValueSquareFactor p M eta * EW))

/-- The corrected flux-derivative expansion at one spatial slice is
cap-weighted `L²` once the population value and raw first-derivative brackets
are.  Both resolver fields are discharged internally, and every constant is
uniform in the cap radius.  This is a successor estimate for the forthcoming
singular Volterra closure; it does not assert or assume an exact exponential
derivative budget. -/
theorem capFluxDerivativeExpanded_data_of_raw_population_H1
    (p : CMParams) {M eta R t B1 B2 B0 B3 B4 : ℝ}
    {u v : ℝ → ℝ → ℝ} {uRef : ℝ → ℝ}
    (hM : 0 ≤ M) (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (hu : IsCUnifBdd (u t)) (hRef : IsCUnifBdd uRef)
    (hu_mem : ∀ x, u t x ∈ Set.Icc (0 : ℝ) M)
    (hRef_mem : ∀ x, uRef x ∈ Set.Icc (0 : ℝ) M)
    (hclose : Integrable (fun x =>
      capWeight eta R x * |u t x - uRef x| ^ 2))
    (hrawX : Integrable (fun x => capWeight eta R x *
      |eta * (u t x - uRef x) +
        (deriv (u t) x - deriv uRef x)| ^ 2))
    (hsource_meas : AEStronglyMeasurable (fun x =>
      capWeightSqrt eta R x *
        paper5WeightedFluxDerivativeExpanded p eta u v uRef
          (fun y => u t y - uRef y)
          (fun y => eta * (u t y - uRef y) +
            (deriv (u t) y - deriv uRef y))
          (fun y => frozenElliptic p (u t) y -
            frozenElliptic p uRef y)
          (fun y => eta *
              (frozenElliptic p (u t) y - frozenElliptic p uRef y) +
            (deriv (frozenElliptic p (u t)) y -
              deriv (frozenElliptic p uRef) y)) t x))
    (hb1 : ∀ x, |paper5B1 p u v t x| ≤ B1)
    (hb2 : ∀ x, |paper5B2 p u v uRef t x| ≤ B2)
    (hb0 : ∀ x,
      |paper5CorrectedChemZeroCoefficient p u v uRef t x| ≤ B0)
    (hb3 : ∀ x, |paper5B3 p uRef x| ≤ B3)
    (hb4 : ∀ x, |paper5B4 p uRef x| ≤ B4) :
    let rawW : ℝ → ℝ := fun x => u t x - uRef x
    let rawWx : ℝ → ℝ := fun x =>
      eta * rawW x + (deriv (u t) x - deriv uRef x)
    let rawZ : ℝ → ℝ := fun x =>
      frozenElliptic p (u t) x - frozenElliptic p uRef x
    let rawZx : ℝ → ℝ := fun x =>
      eta * rawZ x +
        (deriv (frozenElliptic p (u t)) x -
          deriv (frozenElliptic p uRef) x)
    Integrable (fun x =>
        (capWeightSqrt eta R x *
          paper5WeightedFluxDerivativeExpanded p eta u v uRef
            rawW rawWx rawZ rawZx t x) ^ 2) ∧
      (∫ x : ℝ,
        (capWeightSqrt eta R x *
          paper5WeightedFluxDerivativeExpanded p eta u v uRef
            rawW rawWx rawZ rawZx t x) ^ 2) ≤
        capFluxDerivativeRawH1SquareBound p M eta
          B1 B2 B0 B3 B4
          (∫ x : ℝ, capWeight eta R x * |rawW x| ^ 2)
          (∫ x : ℝ, capWeight eta R x * |rawWx x| ^ 2) := by
  dsimp only
  let rawW : ℝ → ℝ := fun x => u t x - uRef x
  let rawWx : ℝ → ℝ := fun x =>
    eta * rawW x + (deriv (u t) x - deriv uRef x)
  let rawZ : ℝ → ℝ := fun x =>
    frozenElliptic p (u t) x - frozenElliptic p uRef x
  let rawZx : ℝ → ℝ := fun x =>
    eta * rawZ x +
      (deriv (frozenElliptic p (u t)) x -
        deriv (frozenElliptic p uRef) x)
  have hW2 : Integrable (fun x =>
      (capWeightSqrt eta R x * rawW x) ^ 2) := by
    refine hclose.congr (Eventually.of_forall fun x => ?_)
    exact (capWeightSqrt_mul_sq_eq eta R x (rawW x)).symm
  have hWx2 : Integrable (fun x =>
      (capWeightSqrt eta R x * rawWx x) ^ 2) := by
    refine hrawX.congr (Eventually.of_forall fun x => ?_)
    exact (capWeightSqrt_mul_sq_eq eta R x (rawWx x)).symm
  have hZcap := capWeight_frozenElliptic_value_difference_l2_bounded
    p hM heta0 heta1 hRef hu hRef_mem hu_mem hclose
  have hZxcap := capWeight_frozenElliptic_rawSignalX_difference_l2_bounded
    p hM heta0 heta1 hRef hu hRef_mem hu_mem hclose
  have hZ2 : Integrable (fun x =>
      (capWeightSqrt eta R x * rawZ x) ^ 2) := by
    refine hZcap.1.congr (Eventually.of_forall fun x => ?_)
    exact (capWeightSqrt_mul_sq_eq eta R x (rawZ x)).symm
  have hZx2 : Integrable (fun x =>
      (capWeightSqrt eta R x * rawZx x) ^ 2) := by
    refine hZxcap.1.congr (Eventually.of_forall fun x => ?_)
    exact (capWeightSqrt_mul_sq_eq eta R x (rawZx x)).symm
  have hmeas : AEStronglyMeasurable (fun x =>
      capWeightSqrt eta R x *
        paper5WeightedFluxDerivativeExpanded p eta u v uRef
          rawW rawWx rawZ rawZx t x) := by
    simpa only [rawW, rawWx, rawZ, rawZx] using hsource_meas
  have hbase := multipliedFluxDerivativeExpanded_sq_integrable_and_integral_le
    p hmeas hb1 hb2 hb0 hb3 hb4 hW2 hWx2 hZ2 hZx2
  refine ⟨hbase.1, hbase.2.trans ?_⟩
  have hZeq :
      (∫ x : ℝ, (capWeightSqrt eta R x * rawZ x) ^ 2) =
        ∫ x : ℝ, capWeight eta R x * |rawZ x| ^ 2 := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x =>
      capWeightSqrt_mul_sq_eq eta R x (rawZ x)
  have hZxeq :
      (∫ x : ℝ, (capWeightSqrt eta R x * rawZx x) ^ 2) =
        ∫ x : ℝ, capWeight eta R x * |rawZx x| ^ 2 := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x =>
      capWeightSqrt_mul_sq_eq eta R x (rawZx x)
  have hWeq :
      (∫ x : ℝ, (capWeightSqrt eta R x * rawW x) ^ 2) =
        ∫ x : ℝ, capWeight eta R x * |rawW x| ^ 2 := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x =>
      capWeightSqrt_mul_sq_eq eta R x (rawW x)
  have hWxeq :
      (∫ x : ℝ, (capWeightSqrt eta R x * rawWx x) ^ 2) =
        ∫ x : ℝ, capWeight eta R x * |rawWx x| ^ 2 := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x =>
      capWeightSqrt_mul_sq_eq eta R x (rawWx x)
  rw [hWeq, hWxeq, hZeq, hZxeq]
  have hZterm := mul_le_mul_of_nonneg_left hZcap.2
    (sq_nonneg (B4 + |eta| * B3))
  have hZxterm := mul_le_mul_of_nonneg_left hZxcap.2 (sq_nonneg B3)
  unfold capFluxDerivativeRawH1SquareBound
    capResolverRawXSquareFactor capResolverValueSquareFactor
  exact mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add le_rfl hZxterm) hZterm) (by norm_num)

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.paper5WeightedFluxDerivativeExpanded_mul_fields
#print axioms
  ShenWork.Paper1.multipliedFluxDerivativeExpanded_sq_integrable_and_integral_le
#print axioms
  ShenWork.Paper1.capFluxDerivativeExpanded_data_of_raw_population_H1
