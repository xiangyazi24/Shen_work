/- Quantitative one-dimensional `X_2^sigma -> C1` realization bounds. -/
import ShenWork.Paper3.StrongExponentialStability

namespace ShenWork.Paper3

open ShenWork.PDE.FractionalPower
open ShenWork.IntervalDomain
open ShenWork.PDE

noncomputable section

/-- Value-trace constant in the coefficient Cauchy-Schwarz estimate. -/
def intervalDomainX2SigmaValueTrace (sigma : ℝ) : ℝ :=
  Real.sqrt (∑' n : ℕ, reciprocalFractionalPowerWeight 1 sigma n)

/-- One-derivative trace constant.  It is finite for `sigma > 3/4`. -/
def intervalDomainX2SigmaDerivativeTrace (sigma : ℝ) : ℝ :=
  Real.sqrt
    (∑' n : ℕ, derivativeReciprocalFractionalPowerWeight 1 sigma n)

theorem intervalDomainX2SigmaValueTrace_nonneg (sigma : ℝ) :
    0 ≤ intervalDomainX2SigmaValueTrace sigma := Real.sqrt_nonneg _

theorem intervalDomainX2SigmaDerivativeTrace_nonneg (sigma : ℝ) :
    0 ≤ intervalDomainX2SigmaDerivativeTrace sigma := Real.sqrt_nonneg _

/-- Uniform radius on which every segment from the positive equilibrium stays
away from the singular power-law boundary.  The added `1` avoids a spurious
case split if the trace constant vanishes. -/
def intervalDomainX2SigmaPositivityRadius (sigma uStar : ℝ) : ℝ :=
  uStar / (2 * (1 + intervalDomainX2SigmaValueTrace sigma))

theorem intervalDomainX2SigmaPositivityRadius_pos
    {sigma uStar : ℝ} (huStar : 0 < uStar) :
    0 < intervalDomainX2SigmaPositivityRadius sigma uStar := by
  unfold intervalDomainX2SigmaPositivityRadius
  exact div_pos huStar (mul_pos (by norm_num)
    (by linarith [intervalDomainX2SigmaValueTrace_nonneg sigma]))

/-- Weighted energy times the derivative reciprocal trace recovers the
frequency-weighted coefficient norm. -/
theorem sqrt_energy_mul_sqrt_derivativeReciprocal_eq
    (sigma : ℝ) (a : ℕ → ℂ) (n : ℕ) :
    Real.sqrt (fractionalPowerEnergyTerm 1 sigma a n) *
        Real.sqrt (derivativeReciprocalFractionalPowerWeight 1 sigma n) =
      Real.sqrt (neumannEigenvalue 1 n) * ‖a n‖ := by
  have hwpos := fractionalPowerWeight_pos 1 sigma n
  have hlambda := neumannEigenvalue_nonneg 1 n
  have henergy := fractionalPowerEnergyTerm_nonneg 1 sigma a n
  rw [← Real.sqrt_mul henergy]
  have hprod :
      fractionalPowerEnergyTerm 1 sigma a n *
          derivativeReciprocalFractionalPowerWeight 1 sigma n =
        neumannEigenvalue 1 n * ‖a n‖ ^ 2 := by
    dsimp [fractionalPowerEnergyTerm,
      derivativeReciprocalFractionalPowerWeight,
      reciprocalFractionalPowerWeight]
    field_simp [hwpos.ne']
  rw [hprod, Real.sqrt_mul hlambda, Real.sqrt_sq (norm_nonneg (a n))]

/-- The differentiated coefficient amplitudes are summable whenever both the
fractional energy and the derivative trace are summable. -/
theorem sqrt_eigen_mul_coeff_norm_summable
    {sigma : ℝ} (a : ℕ → ℂ)
    (henergy : Summable fun n : ℕ => fractionalPowerEnergyTerm 1 sigma a n)
    (htrace : Summable fun n : ℕ =>
      derivativeReciprocalFractionalPowerWeight 1 sigma n) :
    Summable fun n : ℕ => Real.sqrt (neumannEigenvalue 1 n) * ‖a n‖ := by
  let majorant : ℕ → ℝ := fun n =>
    (1 / 2 : ℝ) *
      (fractionalPowerEnergyTerm 1 sigma a n +
        derivativeReciprocalFractionalPowerWeight 1 sigma n)
  have hmajorant : Summable majorant :=
    (henergy.add htrace).mul_left (1 / 2 : ℝ)
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) ?_ hmajorant
  intro n
  have hyoung := two_mul_le_add_sq
    (Real.sqrt (fractionalPowerEnergyTerm 1 sigma a n))
    (Real.sqrt (derivativeReciprocalFractionalPowerWeight 1 sigma n))
  have hleft := sqrt_energy_mul_sqrt_derivativeReciprocal_eq sigma a n
  have he := Real.sq_sqrt (fractionalPowerEnergyTerm_nonneg 1 sigma a n)
  have ht := Real.sq_sqrt
    (derivativeReciprocalFractionalPowerWeight_nonneg 1 sigma n)
  dsimp [majorant]
  have htwo : 2 *
      (Real.sqrt (fractionalPowerEnergyTerm 1 sigma a n) *
        Real.sqrt (derivativeReciprocalFractionalPowerWeight 1 sigma n)) ≤
      Real.sqrt (fractionalPowerEnergyTerm 1 sigma a n) ^ 2 +
        Real.sqrt (derivativeReciprocalFractionalPowerWeight 1 sigma n) ^ 2 := by
    nlinarith [hyoung]
  rw [hleft] at htwo
  nlinarith

/-- Quantitative derivative-trace Cauchy-Schwarz estimate. -/
theorem tsum_sqrt_eigen_mul_coeff_norm_le
    {sigma : ℝ} (a : ℕ → ℂ)
    (henergy : Summable fun n : ℕ => fractionalPowerEnergyTerm 1 sigma a n)
    (htrace : Summable fun n : ℕ =>
      derivativeReciprocalFractionalPowerWeight 1 sigma n) :
    (∑' n : ℕ, Real.sqrt (neumannEigenvalue 1 n) * ‖a n‖) ≤
      Real.sqrt (∑' n : ℕ, fractionalPowerEnergyTerm 1 sigma a n) *
        Real.sqrt
          (∑' n : ℕ,
            derivativeReciprocalFractionalPowerWeight 1 sigma n) := by
  let f : ℕ → ℝ := fun n =>
    Real.sqrt (fractionalPowerEnergyTerm 1 sigma a n)
  let g : ℕ → ℝ := fun n =>
    Real.sqrt (derivativeReciprocalFractionalPowerWeight 1 sigma n)
  have hf : Summable fun n : ℕ => f n ^ (2 : ℝ) := by
    dsimp [f]
    convert henergy using 1
    ext n
    rw [Real.rpow_two,
      Real.sq_sqrt (fractionalPowerEnergyTerm_nonneg 1 sigma a n)]
  have hg : Summable fun n : ℕ => g n ^ (2 : ℝ) := by
    dsimp [g]
    convert htrace using 1
    ext n
    rw [Real.rpow_two,
      Real.sq_sqrt
        (derivativeReciprocalFractionalPowerWeight_nonneg 1 sigma n)]
  have hholder := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg
    (p := (2 : ℝ)) (q := (2 : ℝ))
    Real.HolderConjugate.two_two
    (fun n => Real.sqrt_nonneg _) (fun n => Real.sqrt_nonneg _) hf hg
  have hleftEq : (∑' n : ℕ, f n * g n) =
      ∑' n : ℕ, Real.sqrt (neumannEigenvalue 1 n) * ‖a n‖ := by
    apply tsum_congr
    intro n
    exact sqrt_energy_mul_sqrt_derivativeReciprocal_eq sigma a n
  have hfEq : (∑' n : ℕ, f n ^ (2 : ℝ)) =
      ∑' n : ℕ, fractionalPowerEnergyTerm 1 sigma a n := by
    apply tsum_congr
    intro n
    dsimp [f]
    rw [Real.rpow_two,
      Real.sq_sqrt (fractionalPowerEnergyTerm_nonneg 1 sigma a n)]
  have hgEq : (∑' n : ℕ, g n ^ (2 : ℝ)) =
      ∑' n : ℕ, derivativeReciprocalFractionalPowerWeight 1 sigma n := by
    apply tsum_congr
    intro n
    dsimp [g]
    rw [Real.rpow_two,
      Real.sq_sqrt
        (derivativeReciprocalFractionalPowerWeight_nonneg 1 sigma n)]
  rw [hleftEq, hfEq, hgEq] at hholder
  simpa [Real.sqrt_eq_rpow] using hholder

/-- A physical profile realizes its coefficient `X_2^sigma` element with the
standard value and derivative trace bounds.  This representation condition is
part of the concrete realization of the abstract fractional domain; it is not
an additional smallness norm. -/
structure IntervalDomainX2SigmaRealizationBounds
    (sigma uStar : ℝ) (w : intervalDomainPoint → ℝ) : Prop where
  value_bound : ∀ x : intervalDomainPoint,
    |w x - uStar| ≤
      intervalDomainX2SigmaValueTrace sigma *
        intervalDomainX2SigmaDistance sigma uStar w
  gradient_bound : ∀ x : intervalDomainPoint,
    intervalDomain.gradNorm (fun y => w y - uStar) x ≤
      intervalDomainX2SigmaDerivativeTrace sigma *
      intervalDomainX2SigmaDistance sigma uStar w

/-- The positivity radius is load-bearing for fractional powers: every point
on the Taylor segment `uStar + s (w-uStar)`, `0 ≤ s ≤ 1`, is at least
`uStar/2`. -/
theorem IntervalDomainX2SigmaRealizationBounds.segment_lower_bound
    {sigma uStar : ℝ} {w : intervalDomainPoint → ℝ}
    (H : IntervalDomainX2SigmaRealizationBounds sigma uStar w)
    (huStar : 0 < uStar)
    (hsmall : intervalDomainX2SigmaDistance sigma uStar w ≤
      intervalDomainX2SigmaPositivityRadius sigma uStar)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : intervalDomainPoint) :
    uStar / 2 ≤ uStar + s * (w x - uStar) := by
  let Cinf := intervalDomainX2SigmaValueTrace sigma
  have hCinf : 0 ≤ Cinf := intervalDomainX2SigmaValueTrace_nonneg sigma
  have hdist0 : 0 ≤ intervalDomainX2SigmaDistance sigma uStar w :=
    Real.sqrt_nonneg _
  have hvalue := H.value_bound x
  have hCradius : Cinf * intervalDomainX2SigmaPositivityRadius sigma uStar ≤
      uStar / 2 := by
    unfold intervalDomainX2SigmaPositivityRadius
    have hden : 0 < 1 + Cinf := by linarith
    have hfrac : Cinf / (1 + Cinf) ≤ 1 := by
      rw [div_le_one hden]
      linarith
    calc
      Cinf * (uStar / (2 * (1 + Cinf))) =
          (uStar / 2) * (Cinf / (1 + Cinf)) := by
        field_simp [ne_of_gt hden]
        <;> ring
      _ ≤ (uStar / 2) * 1 :=
        mul_le_mul_of_nonneg_left hfrac (by linarith)
      _ = uStar / 2 := mul_one _
  have habs : |w x - uStar| ≤ uStar / 2 := by
    calc
      |w x - uStar| ≤ Cinf * intervalDomainX2SigmaDistance sigma uStar w :=
        H.value_bound x
      _ ≤ Cinf * intervalDomainX2SigmaPositivityRadius sigma uStar :=
        mul_le_mul_of_nonneg_left hsmall hCinf
      _ ≤ uStar / 2 := hCradius
  have hlower : -(uStar / 2) ≤ w x - uStar :=
    neg_le_of_abs_le habs
  have hscaled : -(uStar / 2) ≤ s * (w x - uStar) := by
    by_cases hw : 0 ≤ w x - uStar
    · have : 0 ≤ s * (w x - uStar) := mul_nonneg hs.1 hw
      linarith
    · have hsle : s * (w x - uStar) ≥ 1 * (w x - uStar) := by
        exact mul_le_mul_of_nonpos_right hs.2 (le_of_not_ge hw)
      linarith
  linarith

private theorem intervalSupNorm_le_of_pointwise_abs
    {f : intervalDomainPoint → ℝ} {M : ℝ}
    (hM : ∀ x, |f x| ≤ M) : intervalDomain.supNorm f ≤ M := by
  have hM0 : 0 ≤ M := by
    let x0 : intervalDomainPoint := ⟨0, by constructor <;> norm_num⟩
    exact (abs_nonneg (f x0)).trans (hM x0)
  change intervalDomainSupNorm f ≤ M
  unfold intervalDomainSupNorm
  exact Real.sSup_le (by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact hM x) hM0

/-- Concrete `C1` distance of one realized profile is controlled by its strong
coefficient norm. -/
theorem IntervalDomainX2SigmaRealizationBounds.c1Distance_le
    {sigma uStar : ℝ} {w : intervalDomainPoint → ℝ}
    (H : IntervalDomainX2SigmaRealizationBounds sigma uStar w) :
    intervalDomainSectorialC1Distance w (fun _ => uStar) ≤
      (intervalDomainX2SigmaValueTrace sigma +
        intervalDomainX2SigmaDerivativeTrace sigma) *
          intervalDomainX2SigmaDistance sigma uStar w := by
  have hvalue : intervalDomain.supNorm (fun x => w x - uStar) ≤
      intervalDomainX2SigmaValueTrace sigma *
        intervalDomainX2SigmaDistance sigma uStar w :=
    intervalSupNorm_le_of_pointwise_abs H.value_bound
  have hgrad : intervalDomain.supNorm
      (fun x => intervalDomain.gradNorm (fun y => w y - uStar) x) ≤
      intervalDomainX2SigmaDerivativeTrace sigma *
        intervalDomainX2SigmaDistance sigma uStar w := by
    apply intervalSupNorm_le_of_pointwise_abs
    intro x
    have hnonneg : 0 ≤
        intervalDomain.gradNorm (fun y => w y - uStar) x := by
      change 0 ≤ |deriv (intervalDomainLift (fun y => w y - uStar)) x.1|
      exact abs_nonneg _
    simpa [abs_of_nonneg hnonneg] using H.gradient_bound x
  unfold intervalDomainSectorialC1Distance
  calc
    intervalDomain.supNorm (fun x => w x - uStar) +
        intervalDomain.supNorm
          (fun x => intervalDomain.gradNorm (fun y => w y - uStar) x) ≤
      intervalDomainX2SigmaValueTrace sigma *
          intervalDomainX2SigmaDistance sigma uStar w +
        intervalDomainX2SigmaDerivativeTrace sigma *
          intervalDomainX2SigmaDistance sigma uStar w := add_le_add hvalue hgrad
    _ = _ := by ring

#print axioms sqrt_eigen_mul_coeff_norm_summable
#print axioms tsum_sqrt_eigen_mul_coeff_norm_le
#print axioms IntervalDomainX2SigmaRealizationBounds.segment_lower_bound
#print axioms IntervalDomainX2SigmaRealizationBounds.c1Distance_le

end

end ShenWork.Paper3
