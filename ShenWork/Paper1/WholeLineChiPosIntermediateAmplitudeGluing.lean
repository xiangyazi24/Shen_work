import ShenWork.Paper1.WholeLineChiPosWeightedEntropyDissipation
import ShenWork.Paper1.WholeLineChiPosDispersionSharp

/-!
# Intermediate-amplitude entropy coercivity

Let `0 < rho ≤ 1` be a spatially constant logistic background and write the
population as `q = rho * u`.  The normalized relative field satisfies

`u_t = u_xx + c u_x - (chi*rho) (u r_x)_x + rho*u*(1-u)`,
`-r_xx + r = u-1`.

The full logarithmic entropy, rather than its small-amplitude Taylor
approximation, closes at every positive amplitude.  Applying the landed
weighted entropy identity to the artificial velocity

`u_t + (1-rho)u(1-u)`

restores unit logistic reaction.  Removing that artificial reaction changes
the leading displacement-square coefficient from
`1-(chi*rho)^2/16` to

`rho-(chi*rho)^2/16 = rho*(1-chi^2*rho/16)`,

which is strictly positive for `0 ≤ chi < 4` and `0 < rho ≤ 1`.  All weight,
resolver, and endpoint errors remain explicit.

This is the compact nonlinear coefficient check in the intermediate-amplitude
regime.  It does not assert that the displayed localization errors vanish on a
canonical orbit.
-/

open MeasureTheory intervalIntegral Set Real
open scoped Topology Interval

noncomputable section

namespace ShenWork.Paper1

/-- The nonlinear entropy margin about a positive logistic background. -/
def intermediateAmplitudeEntropyMargin (chi rho : ℝ) : ℝ :=
  rho - (chi * rho) ^ 2 / 16

/-- The intermediate-amplitude margin is positive on the full strict
sub-Turing range, uniformly for every positive background `rho ≤ 1`. -/
theorem intermediateAmplitudeEntropyMargin_pos
    {chi rho : ℝ} (hchi : 0 ≤ chi) (hchi4 : chi < 4)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    0 < intermediateAmplitudeEntropyMargin chi rho := by
  have hchiSq : chi ^ 2 < 16 := by
    nlinarith
  have hscaled : chi ^ 2 * rho < 16 := by
    calc
      chi ^ 2 * rho ≤ chi ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hrho1 (sq_nonneg chi)
      _ < 16 := by simpa only [mul_one] using hchiSq
  have hfactor : 0 < 1 - chi ^ 2 * rho / 16 := by
    nlinarith
  rw [show intermediateAmplitudeEntropyMargin chi rho =
      rho * (1 - chi ^ 2 * rho / 16) by
    unfold intermediateAmplitudeEntropyMargin
    ring]
  exact mul_pos hrho hfactor

/-- The linearized relative equation about any `0 < rho ≤ 1` remains below
its exact Turing threshold when `chi < 4`. -/
theorem intermediateAmplitude_lt_turing
    {chi rho : ℝ} (hchi4 : chi < 4)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    chi * rho < (1 + Real.sqrt rho) ^ 2 := by
  have hsqrt0 : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg rho
  have hsqrtSq : (Real.sqrt rho) ^ 2 = rho :=
    Real.sq_sqrt hrho.le
  have hsqrt1 : Real.sqrt rho ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hrho1
  have hfour : chi * rho < 4 * rho :=
    mul_lt_mul_of_pos_right hchi4 hrho
  have hturing : 4 * rho ≤ (1 + Real.sqrt rho) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsqrt1)
      (by nlinarith : 0 ≤ 1 + 3 * Real.sqrt rho)]
  exact hfour.trans_le hturing

/-- Direct reuse of the landed sharp dispersion theorem for the relative
equation about the background `rho`. -/
theorem intermediateAmplitude_dispersion_lt_zero
    {chi rho s : ℝ} (hchi : 0 ≤ chi) (hchi4 : chi < 4)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (hs : 0 ≤ s) :
    dispersion rho (chi * rho) s < 0 := by
  exact ShenWork.Paper1.dispersion_le_of_lt_turing
    rho (chi * rho) hrho (mul_nonneg hchi hrho.le)
      (ShenWork.Paper1.intermediateAmplitude_lt_turing hchi4 hrho hrho1)
      s hs

/-- One positive weighted time slice of the relative equation about a
spatially constant logistic background `rho`. -/
structure IntermediateAmplitudeWeightedEntropySlice
    (a b c chi rho ell : ℝ) (w w' : ℝ → ℝ)
    (u ux uxx r rx rxx ut : ℝ → ℝ) : Prop where
  hab : a ≤ b
  hrho : 0 < rho
  hrho_one : rho ≤ 1
  hell : 0 < ell
  u_pos : ∀ x, 0 < u x
  w_pos : ∀ x, 0 < w x
  w_deriv : ∀ x, HasDerivAt w (w' x) x
  w'_cont : Continuous w'
  w_slow : ∀ x, |w' x| ≤ (1 / ell) * w x
  u_deriv : ∀ x, HasDerivAt u (ux x) x
  ux_deriv : ∀ x, HasDerivAt ux (uxx x) x
  r_deriv : ∀ x, HasDerivAt r (rx x) x
  rx_deriv : ∀ x, HasDerivAt rx (rxx x) x
  uxx_continuous : Continuous uxx
  rxx_continuous : Continuous rxx
  ut_continuous : Continuous ut
  population_pde : ∀ x,
    ut x = uxx x + c * ux x -
      (chi * rho) * (ux x * rx x + u x * rxx x) +
        rho * (u x * (1 - u x))
  resolver_pde : ∀ x, -rxx x + r x = u x - 1

namespace IntermediateAmplitudeWeightedEntropySlice

variable {a b c chi rho ell : ℝ} {w w' : ℝ → ℝ}
    {u ux uxx r rx rxx ut : ℝ → ℝ}
    (d : IntermediateAmplitudeWeightedEntropySlice
      a b c chi rho ell w w' u ux uxx r rx rxx ut)

include d

/-- Velocity obtained by restoring unit logistic reaction. -/
def unitReactionVelocity
    (_d : IntermediateAmplitudeWeightedEntropySlice
      a b c chi rho ell w w' u ux uxx r rx rxx ut) : ℝ → ℝ :=
  fun x => ut x + (1 - rho) * (u x * (1 - u x))

/-- The restored velocity is continuous. -/
theorem unitReactionVelocity_continuous :
    Continuous (d.unitReactionVelocity : ℝ → ℝ) := by
  have hu_cont : Continuous u := by
    rw [continuous_iff_continuousAt]
    exact fun x => (d.u_deriv x).continuousAt
  exact d.ut_continuous.add <|
    continuous_const.mul <|
      hu_cont.mul (continuous_const.sub hu_cont)

/-- Restoring the missing reaction produces exactly the landed unit-reaction
weighted entropy slice, with sensitivity `chi*rho`. -/
theorem toUnitReactionSlice :
    ShenWork.Paper1.ChiOneWeightedEntropySlice
      a b c (chi * rho) ell w w'
        u ux uxx r rx rxx d.unitReactionVelocity := by
  refine
    { hab := d.hab
      hell := d.hell
      u_pos := d.u_pos
      w_pos := d.w_pos
      w_deriv := d.w_deriv
      w'_cont := d.w'_cont
      w_slow := d.w_slow
      u_deriv := d.u_deriv
      ux_deriv := d.ux_deriv
      r_deriv := d.r_deriv
      rx_deriv := d.rx_deriv
      uxx_continuous := d.uxx_continuous
      rxx_continuous := d.rxx_continuous
      ut_continuous := d.unitReactionVelocity_continuous
      population_pde := ?_
      resolver_pde := d.resolver_pde }
  intro x
  unfold unitReactionVelocity
  rw [d.population_pde x]
  ring

/-- Every localization term in the landed weighted entropy inequality,
collected without altering its coefficients. -/
def localizationError
    (_d : IntermediateAmplitudeWeightedEntropySlice
      a b c chi rho ell w w' u ux uxx r rx rxx ut) : ℝ :=
  ((|c| + chi * rho + 2) / ell) *
      ((∫ x in a..b, w x * chiOneRelativeEntropy (u x)) +
        (∫ x in a..b,
          w x * ((ux x / u x) ^ 2 + (u x - 1) ^ 2))) +
    ((chi * rho) ^ 2 / 4 + (chi * rho) / (2 * ell)) *
      ((1 / (2 * ell)) *
          ((∫ x in a..b, w x * (r x) ^ 2) +
            ∫ x in a..b, w x * (rx x) ^ 2) +
        |w b * r b * rx b - w a * r a * rx a|) +
    ((w b * chiOneEntropyMultiplier (u b) * ux b -
        w a * chiOneEntropyMultiplier (u a) * ux a) +
      c * (w b * chiOneRelativeEntropy (u b) -
        w a * chiOneRelativeEntropy (u a)) -
      (chi * rho) * (w b * (u b - 1) * rx b -
        w a * (u a - 1) * rx a))

/-- Restoring unit reaction subtracts exactly `(1-rho)` times the weighted
displacement square from the actual entropy production. -/
theorem unitReaction_production_eq :
    (∫ x in a..b,
        w x * chiOneEntropyMultiplier (u x) *
          d.unitReactionVelocity x) =
      (∫ x in a..b,
        w x * chiOneEntropyMultiplier (u x) * ut x) -
        (1 - rho) * (∫ x in a..b, w x * (u x - 1) ^ 2) := by
  let base := d.toUnitReactionSlice
  have hw_cont : Continuous w := by
    rw [continuous_iff_continuousAt]
    exact fun x => (d.w_deriv x).continuousAt
  have hu_cont : Continuous u := by
    rw [continuous_iff_continuousAt]
    exact fun x => (d.u_deriv x).continuousAt
  have hmult_cont :
      Continuous (fun x => chiOneEntropyMultiplier (u x)) := by
    rw [continuous_iff_continuousAt]
    exact fun x => (base.multiplier_hasDerivAt x).continuousAt
  have hactual_cont : Continuous (fun x =>
      w x * chiOneEntropyMultiplier (u x) * ut x) :=
    (hw_cont.mul hmult_cont).mul d.ut_continuous
  have hreaction_cont : Continuous (fun x =>
      w x * chiOneEntropyMultiplier (u x) *
        ((1 - rho) * (u x * (1 - u x)))) :=
    (hw_cont.mul hmult_cont).mul <|
      continuous_const.mul <|
        hu_cont.mul (continuous_const.sub hu_cont)
  have hsplit :
      (∫ x in a..b,
          w x * chiOneEntropyMultiplier (u x) *
            d.unitReactionVelocity x) =
        (∫ x in a..b,
          w x * chiOneEntropyMultiplier (u x) * ut x) +
          (1 - rho) *
            (∫ x in a..b,
              w x * chiOneEntropyMultiplier (u x) *
                (u x * (1 - u x))) := by
    rw [show (fun x =>
        w x * chiOneEntropyMultiplier (u x) *
          d.unitReactionVelocity x) =
      (fun x =>
        w x * chiOneEntropyMultiplier (u x) * ut x +
          w x * chiOneEntropyMultiplier (u x) *
            ((1 - rho) * (u x * (1 - u x)))) by
      funext x
      unfold unitReactionVelocity
      ring]
    rw [intervalIntegral.integral_add
      (hactual_cont.intervalIntegrable a b)
      (hreaction_cont.intervalIntegrable a b)]
    rw [show (fun x =>
        w x * chiOneEntropyMultiplier (u x) *
          ((1 - rho) * (u x * (1 - u x)))) =
      (fun x => (1 - rho) *
        (w x * chiOneEntropyMultiplier (u x) *
          (u x * (1 - u x)))) by
      funext x
      ring]
    rw [intervalIntegral.integral_const_mul]
  rw [hsplit]
  have hreaction := base.weighted_reaction_integral
  rw [hreaction]
  ring

/-- **Intermediate-amplitude gluing inequality.**  The logarithmic entropy
has a positive leading displacement-square coefficient at every positive
amplitude.  The only remaining terms are the explicit localization and
endpoint errors inherited from the landed weighted entropy calculation. -/
theorem weighted_entropy_production_le
    (hchi : 0 ≤ chi) (hchi4 : chi < 4) :
    0 < intermediateAmplitudeEntropyMargin chi rho ∧
      (∫ x in a..b,
          w x * chiOneEntropyMultiplier (u x) * ut x) ≤
        -intermediateAmplitudeEntropyMargin chi rho *
            (∫ x in a..b, w x * (u x - 1) ^ 2) +
          d.localizationError := by
  constructor
  · exact ShenWork.Paper1.intermediateAmplitudeEntropyMargin_pos
      hchi hchi4 d.hrho d.hrho_one
  let base := d.toUnitReactionSlice
  have hsharp :=
    base.weighted_sharp_entropy_production_le
      (mul_nonneg hchi d.hrho.le)
  have hproduction := d.unitReaction_production_eq
  have hsharp' :
    (∫ x in a..b,
        w x * chiOneEntropyMultiplier (u x) *
          d.unitReactionVelocity x) ≤
      -(1 - (chi * rho) ^ 2 / 16) *
          (∫ x in a..b, w x * (u x - 1) ^ 2) +
        d.localizationError := by
    unfold localizationError
    linarith
  rw [hproduction] at hsharp'
  unfold intermediateAmplitudeEntropyMargin
  linarith

end IntermediateAmplitudeWeightedEntropySlice

section AxiomAudit

#print axioms intermediateAmplitudeEntropyMargin_pos
#print axioms intermediateAmplitude_lt_turing
#print axioms intermediateAmplitude_dispersion_lt_zero
#print axioms
  IntermediateAmplitudeWeightedEntropySlice.toUnitReactionSlice
#print axioms
  IntermediateAmplitudeWeightedEntropySlice.unitReaction_production_eq
#print axioms
  IntermediateAmplitudeWeightedEntropySlice.weighted_entropy_production_le

end AxiomAudit

end ShenWork.Paper1
