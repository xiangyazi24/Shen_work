import ShenWork.Paper2.IntervalBFormSpectralHtime
import ShenWork.Paper2.IntervalCoeffLadderFull
import ShenWork.PDE.IntervalSourceDecayQuantitative
import ShenWork.PDE.IntervalTimeSoftClamp

/-!
# Quadratic window envelope for the total B-form source

This file performs the coefficient-level wiring needed by the positive-time
spectral bootstrap.  A weak-Neumann `H²` witness and a uniform `L¹` bound for
the weak second derivative give quadratic cosine decay.  Applying this to the
logistic and chemotaxis-divergence parts separately, then using the soft time
clamp, gives `WindowSourceEnvelope 2` for the total B-form source

`logistic - χ₀ * chemDiv`.

No spatial or time regularity is manufactured here: the two per-slice
witnesses and their compact-window bounds are explicit inputs.
-/

open Set
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.PDE.IntervalMildSourceDecayHelper (IntervalWeakH2Neumann)

noncomputable section

namespace ShenWork.Paper2.IntervalBFormSourceWeakH2Envelope

open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.IntervalBFormSpectral (bFormSourceCoeffs)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledChemDivSourceLift
   coupledLogisticSourceCoeffs coupledLogisticSourceLift)
open ShenWork.IntervalSourceDecayQuantitative
  (intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound)
open ShenWork.IntervalTimeSoftClamp (φ φ_mem_range)
open ShenWork.Paper2.IntervalCoeffLadderFull (WindowSourceEnvelope)

/-- Remove the harmless factor `π²` from the quantitative weak-`H²` decay
bound.  This is the normalization expected by `WindowSourceEnvelope 2`. -/
theorem cosineCoeff_quadratic_decay_nat_of_weakH2_bound
    {f : ℝ → ℝ} (hf : IntervalWeakH2Neumann f) {B : ℝ}
    (hB_nonneg : 0 ≤ B)
    (hB : (∫ x in (0 : ℝ)..1, |hf.secondDeriv x|) ≤ B)
    (k : ℕ) (hk : k ≠ 0) :
    |cosineCoeffs f k| ≤ 2 * B / (k : ℝ) ^ 2 := by
  have hk_one : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
  have hk_pos : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  have hk_sq_pos : 0 < (k : ℝ) ^ 2 := sq_pos_of_pos hk_pos
  have hpi_sq : (1 : ℝ) ≤ Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have hden : (k : ℝ) ^ 2 ≤ ((k : ℝ) * Real.pi) ^ 2 := by
    calc
      (k : ℝ) ^ 2 = (k : ℝ) ^ 2 * 1 := by ring
      _ ≤ (k : ℝ) ^ 2 * Real.pi ^ 2 :=
        mul_le_mul_of_nonneg_left hpi_sq (sq_nonneg _)
      _ = ((k : ℝ) * Real.pi) ^ 2 := by ring
  exact
    (intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound hf hB k hk_one).trans
      (div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hB_nonneg) hk_sq_pos hden)

/-- The soft-clamped total B-form source has a quadratic window envelope once
the logistic and chem-div source slices have uniform weak-`H²` bounds on the
physical compact window `[cLow,dHigh]`.

The restart-window variables do not enter the analytic estimate: every
soft-clamped physical time lies in `[cLow,dHigh]` by `φ_mem_range`. -/
noncomputable def clampedBFormSource_windowSourceEnvelope_two_of_weakH2
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (offset cLow c d dHigh cRestart T' Blog Bchem : ℝ)
    (hcLow : cLow < c) (hcd : c ≤ d) (hdHigh : d < dHigh)
    (hBlog_nonneg : 0 ≤ Blog) (hBchem_nonneg : 0 ≤ Bchem)
    (hlogH2 : ∀ r ∈ Icc cLow dHigh,
      IntervalWeakH2Neumann (coupledLogisticSourceLift p u r))
    (hchemH2 : ∀ r ∈ Icc cLow dHigh,
      IntervalWeakH2Neumann (coupledChemDivSourceLift p u r))
    (hBlog : ∀ r (hr : r ∈ Icc cLow dHigh),
      (∫ x in (0 : ℝ)..1, |(hlogH2 r hr).secondDeriv x|) ≤ Blog)
    (hBchem : ∀ r (hr : r ∈ Icc cLow dHigh),
      (∫ x in (0 : ℝ)..1, |(hchemH2 r hr).secondDeriv x|) ≤ Bchem) :
    WindowSourceEnvelope 2 cRestart T'
      (fun σ n => bFormSourceCoeffs p u (φ cLow c d dHigh (offset + σ)) n) := by
  let C : ℝ := 2 * Blog + |p.χ₀| * (2 * Bchem)
  refine
    { C := C
      hC := by
        dsimp [C]
        positivity
      hbound := ?_ }
  intro τ _hτ σ _hσ0 _hστ k hk
  let r : ℝ := φ cLow c d dHigh (offset + σ)
  have hr : r ∈ Icc cLow dHigh := by
    exact φ_mem_range hcLow hcd hdHigh (offset + σ)
  have hlog :
      |coupledLogisticSourceCoeffs p u r k| ≤ 2 * Blog / (k : ℝ) ^ 2 := by
    exact cosineCoeff_quadratic_decay_nat_of_weakH2_bound
      (hlogH2 r hr) hBlog_nonneg (hBlog r hr) k hk
  have hchem :
      |coupledChemDivSourceCoeffs p u r k| ≤ 2 * Bchem / (k : ℝ) ^ 2 := by
    exact cosineCoeff_quadratic_decay_nat_of_weakH2_bound
      (hchemH2 r hr) hBchem_nonneg (hBchem r hr) k hk
  change
    |coupledLogisticSourceCoeffs p u r k
        - p.χ₀ * coupledChemDivSourceCoeffs p u r k|
      ≤ C / (k : ℝ) ^ 2
  calc
    |coupledLogisticSourceCoeffs p u r k
        - p.χ₀ * coupledChemDivSourceCoeffs p u r k|
        ≤ |coupledLogisticSourceCoeffs p u r k|
            + |p.χ₀ * coupledChemDivSourceCoeffs p u r k| := abs_sub _ _
    _ = |coupledLogisticSourceCoeffs p u r k|
          + |p.χ₀| * |coupledChemDivSourceCoeffs p u r k| := by
        rw [abs_mul]
    _ ≤ 2 * Blog / (k : ℝ) ^ 2
          + |p.χ₀| * (2 * Bchem / (k : ℝ) ^ 2) :=
        add_le_add hlog (mul_le_mul_of_nonneg_left hchem (abs_nonneg _))
    _ = C / (k : ℝ) ^ 2 := by
        dsimp [C]
        ring

end ShenWork.Paper2.IntervalBFormSourceWeakH2Envelope
