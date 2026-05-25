/-
  ShenWork/Paper3/LyapunovFunction.lean

  Lyapunov and entropy estimates for Paper3.
-/
import ShenWork.Paper3.Statements
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Filter Topology
open Set
open scoped Interval

namespace ShenWork.Paper3

noncomputable section

/-- Paper3's entropy density for the nonminimal Lyapunov functional:
`h_m(s) = ∫_{u*}^{s} (1 - (u*/tau)^(2m-1)) d tau`.

The paper uses this on positive solution values.  The definition is total
because Lean functions are total, but the mathematically intended region is
`0 < uStar` and `0 < s`. -/
def chemotaxisEntropyDensity (m uStar s : ℝ) : ℝ :=
  ∫ tau in uStar..s, 1 - (uStar / tau) ^ (2 * m - 1)

/-- The Paper3 entropy functional `F(t)=∫ h_m(u(t,x)) dx`, expressed through
the bounded-domain integral interface already used in Paper2/Paper3. -/
def chemotaxisEntropyFunctional
    (D : BoundedDomainData) (m uStar : ℝ)
    (u : ℝ → D.Point → ℝ) (t : ℝ) : ℝ :=
  D.integral fun x => chemotaxisEntropyDensity m uStar (u t x)

/-- The theta/entropy-production moment appearing in Paper3's stabilization
arguments.  With `theta = p.alpha`, this is the paper's
`∫ (u-u*) (u^alpha-(u*)^alpha)`. -/
def chemotaxisThetaDissipation
    (D : BoundedDomainData) (uStar theta : ℝ)
    (uSlice : D.Point → ℝ) : ℝ :=
  D.integral fun x => (uSlice x - uStar) * (uSlice x ^ theta - uStar ^ theta)

/-- Signal energy for the `w = v-v*` Lyapunov functional from the minimal-model
argument:
`∫ (mu w^2 + |∇w|^2)`.

The abstract domain API only exposes a gradient norm, not a vector gradient or
integration-by-parts theorem, so the actual PDE identity is kept as an explicit
hypothesis in the theorems below. -/
def chemotaxisSignalEnergy
    (D : BoundedDomainData) (mu vStar : ℝ)
    (v : ℝ → D.Point → ℝ) (t : ℝ) : ℝ :=
  D.integral fun x =>
    mu * (v t x - vStar) ^ 2 +
      (D.gradNorm (fun y => v t y - vStar) x) ^ 2

/-- The gradient part of the signal-energy dissipation. -/
def chemotaxisSignalGradientDissipation
    (D : BoundedDomainData) (vStar : ℝ)
    (v : ℝ → D.Point → ℝ) (t : ℝ) : ℝ :=
  D.integral fun x => (D.gradNorm (fun y => v t y - vStar) x) ^ 2

/-- If a differentiable energy has nonpositive time derivative on `(0,∞)`,
then it is antitone there. -/
theorem energy_antitoneOn_Ioi_of_hasDerivAt_nonpos
    {E E' : ℝ → ℝ}
    (hderiv : ∀ t, 0 < t → HasDerivAt E (E' t) t)
    (hnonpos : ∀ t, 0 < t → E' t ≤ 0) :
    AntitoneOn E (Ioi (0 : ℝ)) := by
  have hdiff : DifferentiableOn ℝ E (Ioi (0 : ℝ)) := by
    intro t ht
    exact (hderiv t ht).differentiableAt.differentiableWithinAt
  have hcont : ContinuousOn E (Ioi (0 : ℝ)) := hdiff.continuousOn
  refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) hcont ?_ ?_
  · simpa using hdiff
  · intro t ht
    have ht' : 0 < t := by simpa using ht
    rw [(hderiv t ht').deriv]
    exact hnonpos t ht'

/-- If `E'(t) ≤ -rate E(t)` on `(0,∞)`, then
`exp(rate t) E(t)` is antitone on `(0,∞)`. -/
theorem weighted_energy_antitoneOn_Ioi_of_hasDerivAt_le_neg_mul
    {E E' : ℝ → ℝ} {rate : ℝ}
    (hderiv : ∀ t, 0 < t → HasDerivAt E (E' t) t)
    (hle : ∀ t, 0 < t → E' t ≤ -rate * E t) :
    AntitoneOn (fun t => Real.exp (rate * t) * E t) (Ioi (0 : ℝ)) := by
  apply energy_antitoneOn_Ioi_of_hasDerivAt_nonpos
      (E := fun t => Real.exp (rate * t) * E t)
      (E' := fun t => Real.exp (rate * t) * (rate * E t + E' t))
  · intro t ht
    have hlin : HasDerivAt (fun tau : ℝ => rate * tau) rate t := by
      simpa using (hasDerivAt_id t).const_mul rate
    have hexp : HasDerivAt (fun tau : ℝ => Real.exp (rate * tau))
        (Real.exp (rate * t) * rate) t := hlin.exp
    convert hexp.mul (hderiv t ht) using 1
    ring_nf
  · intro t ht
    have hsum : rate * E t + E' t ≤ 0 := by
      linarith [hle t ht]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hsum

/-- Exponential decay estimate obtained from the differential inequality
`E'(t) ≤ -rate E(t)`. -/
theorem energy_decay_estimate_of_hasDerivAt_le_neg_mul
    {E E' : ℝ → ℝ} {rate : ℝ}
    (hderiv : ∀ t, 0 < t → HasDerivAt E (E' t) t)
    (hle : ∀ t, 0 < t → E' t ≤ -rate * E t) :
    ∀ s t, 0 < s → s ≤ t →
      E t ≤ E s * Real.exp (-rate * (t - s)) := by
  intro s t hs hst
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hweighted :=
    weighted_energy_antitoneOn_Ioi_of_hasDerivAt_le_neg_mul hderiv hle
  have hW :
      Real.exp (rate * t) * E t ≤ Real.exp (rate * s) * E s :=
    hweighted hs ht hst
  have hpos : 0 < Real.exp (rate * t) := Real.exp_pos _
  calc
    E t = (Real.exp (rate * t) * E t) / Real.exp (rate * t) := by
      field_simp [ne_of_gt hpos]
    _ ≤ (Real.exp (rate * s) * E s) / Real.exp (rate * t) :=
      div_le_div_of_nonneg_right hW hpos.le
    _ = E s * Real.exp (-rate * (t - s)) := by
      rw [mul_div_assoc, div_eq_mul_inv, ← Real.exp_neg]
      calc
        Real.exp (rate * s) * (E s * Real.exp (-(rate * t)))
            = E s * (Real.exp (rate * s) * Real.exp (-(rate * t))) := by
              ring_nf
        _ = E s * Real.exp (rate * s + -(rate * t)) := by
              rw [← Real.exp_add]
        _ = E s * Real.exp (-rate * (t - s)) := by
              congr 1
              ring_nf

/-- If a nonnegative energy satisfies `E'(t) ≤ -rate E(t)` with `rate > 0`,
then it tends to zero.  The start time `s` is explicit so this lemma can be used
after a solution becomes regular or persistent only eventually. -/
theorem energy_tendsto_zero_of_hasDerivAt_le_neg_mul
    {E E' : ℝ → ℝ} {rate s : ℝ}
    (hrate : 0 < rate) (hs : 0 < s)
    (hderiv : ∀ t, 0 < t → HasDerivAt E (E' t) t)
    (hle : ∀ t, 0 < t → E' t ≤ -rate * E t)
    (hnonneg : ∀ t, s ≤ t → 0 ≤ E t) :
    Tendsto E atTop (𝓝 0) := by
  have hdecay := energy_decay_estimate_of_hasDerivAt_le_neg_mul hderiv hle
  have hexp0 :
      Tendsto (fun t : ℝ => Real.exp (-rate * (t - s))) atTop (𝓝 0) := by
    have hlinear :
        Tendsto (fun t : ℝ => (-rate) * t + rate * s) atTop atBot := by
      exact tendsto_atBot_add_const_right _ (rate * s)
        (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hrate))
    refine (Real.tendsto_exp_atBot.comp hlinear).congr' ?_
    filter_upwards with t
    apply congrArg Real.exp
    ring
  have hupper0 :
      Tendsto (fun t : ℝ => E s * Real.exp (-rate * (t - s))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hexp0)
  refine squeeze_zero' ?_ ?_ hupper0
  · exact eventually_atTop.mpr ⟨s, fun t ht => hnonneg t ht⟩
  · exact eventually_atTop.mpr
      ⟨s, fun t ht => hdecay s t hs ht⟩

/-- Differential dissipation plus a Poincare-type control implies the weighted
energy is decreasing.

Point 17 status: conditional theorem, state ③.  The unproved analytic inputs are
exactly the hypotheses `hderiv`, `hdiss`, and `hcontrol`: they package the
chain rule, Neumann integration by parts, the chemotaxis term estimate, and the
Poincare control for the particular PDE/domain.  `BoundedDomainData` does not
yet expose enough structure to derive those facts.  Given them, the Lyapunov
decay conclusion is proved here without new axioms or proof holes. -/
theorem energy_weighted_antitoneOn_Ioi_of_dissipation_control
    {E E' G : ℝ → ℝ} {c K : ℝ}
    (hc : 0 < c) (hK : 0 < K)
    (hderiv : ∀ t, 0 < t → HasDerivAt E (E' t) t)
    (hdiss : ∀ t, 0 < t → (1 / 2 : ℝ) * E' t + c * G t ≤ 0)
    (hcontrol : ∀ t, 0 < t → E t ≤ K * G t) :
    AntitoneOn (fun t => Real.exp ((2 * c / K) * t) * E t) (Ioi (0 : ℝ)) := by
  refine weighted_energy_antitoneOn_Ioi_of_hasDerivAt_le_neg_mul hderiv ?_
  intro t ht
  have hd : E' t + 2 * c * G t ≤ 0 := by
    linarith [hdiss t ht]
  have hcoef_nonneg : 0 ≤ 2 * c / K := by positivity
  have hcontrol' :
      (2 * c / K) * E t ≤ (2 * c / K) * (K * G t) :=
    mul_le_mul_of_nonneg_left (hcontrol t ht) hcoef_nonneg
  have hright : (2 * c / K) * (K * G t) = 2 * c * G t := by
    field_simp [ne_of_gt hK]
  have hrateE : (2 * c / K) * E t ≤ 2 * c * G t := by
    simpa [hright] using hcontrol'
  linarith

/-- Exponential energy decay from a differential dissipation inequality and a
Poincare-type control.  This is the abstract core of the Paper3 estimate
`(8.14) -> (8.15)`.

Point 17 status: conditional theorem, state ③, for the same reason as
`energy_weighted_antitoneOn_Ioi_of_dissipation_control`. -/
theorem energy_exponential_decay_of_dissipation_control
    {E E' G : ℝ → ℝ} {c K : ℝ}
    (hc : 0 < c) (hK : 0 < K)
    (hderiv : ∀ t, 0 < t → HasDerivAt E (E' t) t)
    (hdiss : ∀ t, 0 < t → (1 / 2 : ℝ) * E' t + c * G t ≤ 0)
    (hcontrol : ∀ t, 0 < t → E t ≤ K * G t) :
    ∀ s t, 0 < s → s ≤ t →
      E t ≤ E s * Real.exp (-(2 * c / K) * (t - s)) := by
  refine energy_decay_estimate_of_hasDerivAt_le_neg_mul hderiv ?_
  intro t ht
  have hd : E' t + 2 * c * G t ≤ 0 := by
    linarith [hdiss t ht]
  have hcoef_nonneg : 0 ≤ 2 * c / K := by positivity
  have hcontrol' :
      (2 * c / K) * E t ≤ (2 * c / K) * (K * G t) :=
    mul_le_mul_of_nonneg_left (hcontrol t ht) hcoef_nonneg
  have hright : (2 * c / K) * (K * G t) = 2 * c * G t := by
    field_simp [ne_of_gt hK]
  have hrateE : (2 * c / K) * E t ≤ 2 * c * G t := by
    simpa [hright] using hcontrol'
  linarith

/-- The dissipation-control form of the Paper3 Lyapunov estimate implies
decay to zero for nonnegative energies. -/
theorem energy_tendsto_zero_of_dissipation_control
    {E E' G : ℝ → ℝ} {c K s : ℝ}
    (hc : 0 < c) (hK : 0 < K) (hs : 0 < s)
    (hderiv : ∀ t, 0 < t → HasDerivAt E (E' t) t)
    (hdiss : ∀ t, 0 < t → (1 / 2 : ℝ) * E' t + c * G t ≤ 0)
    (hcontrol : ∀ t, 0 < t → E t ≤ K * G t)
    (hnonneg : ∀ t, s ≤ t → 0 ≤ E t) :
    Tendsto E atTop (𝓝 0) := by
  refine energy_tendsto_zero_of_hasDerivAt_le_neg_mul
    (rate := 2 * c / K) (s := s) ?_ hs hderiv ?_ hnonneg
  · positivity
  · intro t ht
    have hd : E' t + 2 * c * G t ≤ 0 := by
      linarith [hdiss t ht]
    have hcoef_nonneg : 0 ≤ 2 * c / K := by positivity
    have hcontrol' :
        (2 * c / K) * E t ≤ (2 * c / K) * (K * G t) :=
      mul_le_mul_of_nonneg_left (hcontrol t ht) hcoef_nonneg
    have hright : (2 * c / K) * (K * G t) = 2 * c * G t := by
      field_simp [ne_of_gt hK]
    have hrateE : (2 * c / K) * E t ≤ 2 * c * G t := by
      simpa [hright] using hcontrol'
    linarith

/-- Entropy dissipation makes the Paper3 entropy functional decrease.

Point 17 status: conditional theorem, state ③.  The missing upstream analytic
input is the PDE derivation of `hderiv` and `hdiss` from the chemotaxis-logistic
system.  The theorem does not assume the conclusion; it turns the genuine
differential entropy-production estimate into Lyapunov monotonicity. -/
theorem chemotaxisEntropyFunctional_antitoneOn_of_dissipation
    {D : BoundedDomainData} {m uStar theta c : ℝ}
    {u : ℝ → D.Point → ℝ} {entropySlope : ℝ → ℝ}
    (hc : 0 ≤ c)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau => chemotaxisEntropyFunctional D m uStar u tau)
          (entropySlope t) t)
    (hdiss :
      ∀ t, 0 < t →
        entropySlope t ≤
          -c * chemotaxisThetaDissipation D uStar theta (u t))
    (hprod_nonneg :
      ∀ t, 0 < t →
        0 ≤ chemotaxisThetaDissipation D uStar theta (u t)) :
    AntitoneOn
      (fun t => chemotaxisEntropyFunctional D m uStar u t)
      (Ioi (0 : ℝ)) := by
  refine energy_antitoneOn_Ioi_of_hasDerivAt_nonpos hderiv ?_
  intro t ht
  have hnonpos :
      -c * chemotaxisThetaDissipation D uStar theta (u t) ≤ 0 := by
    simpa [neg_mul] using
      neg_nonpos.mpr (mul_nonneg hc (hprod_nonneg t ht))
  exact le_trans (hdiss t ht) hnonpos

/-- Signal-energy exponential decay for the Paper3 minimal-model Lyapunov
functional `∫ (mu (v-v*)^2 + |∇(v-v*)|^2)`.

Point 17 status: conditional theorem, state ③.  The theorem is conditional on
the named assumptions in its signature:
* `hderiv`: differentiability of the signal energy;
* `hdiss`: the integrated PDE identity/estimate corresponding to Paper3 (8.14);
* `hcontrol`: the Poincare control corresponding to the step after (8.14).
These are not derivable yet from `BoundedDomainData`. -/
theorem chemotaxisSignalEnergy_exponential_decay
    {D : BoundedDomainData} {mu vStar c K : ℝ}
    {v : ℝ → D.Point → ℝ} {energySlope : ℝ → ℝ}
    (hc : 0 < c) (hK : 0 < K)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau => chemotaxisSignalEnergy D mu vStar v tau)
          (energySlope t) t)
    (hdiss :
      ∀ t, 0 < t →
        (1 / 2 : ℝ) * energySlope t +
          c * chemotaxisSignalGradientDissipation D vStar v t ≤ 0)
    (hcontrol :
      ∀ t, 0 < t →
        chemotaxisSignalEnergy D mu vStar v t ≤
          K * chemotaxisSignalGradientDissipation D vStar v t) :
    ∀ s t, 0 < s → s ≤ t →
      chemotaxisSignalEnergy D mu vStar v t ≤
        chemotaxisSignalEnergy D mu vStar v s *
          Real.exp (-(2 * c / K) * (t - s)) :=
  energy_exponential_decay_of_dissipation_control hc hK hderiv hdiss hcontrol

end

end ShenWork.Paper3
