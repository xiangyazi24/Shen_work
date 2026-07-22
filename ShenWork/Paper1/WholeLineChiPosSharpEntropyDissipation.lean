import ShenWork.Paper1.WholeLineResolverSharpGradient
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Sharp nonlinear entropy dissipation at `m = gamma = alpha = 1`

For the scalar population equation

`u_t = u_xx + c u_x - chi (u r_x)_x + u (1-u)`

coupled to `-r_xx + r = u - 1`, the relative entropy

`H(u) = u - 1 - log u`

has the exact production density

`- (u_x/u)^2 + chi (u_x/u) r_x - (u-1)^2`.

On a periodic interval all fluxes vanish.  Completing the square and using
the sharp resolver estimate `integral r_x^2 <= (1/4) integral (u-1)^2` gives

`Edot <= -(1 - chi^2/16) integral (u-1)^2`.

Thus this is a genuinely nonlinear dissipation law on the full sharp range
`|chi| < 4`; no small-plateau hypothesis is used.  The periodic slice is the
clean flux-free model needed by the whole-line localization/Liouville route.
The remaining whole-line step is to reproduce the same estimate with an
integrable slowly varying weight and control the resulting weight fluxes.
-/

open MeasureTheory intervalIntegral Set Real
open scoped Topology Interval

noncomputable section

namespace ShenWork.Paper1

/-- Relative entropy for the normalized equilibrium `u = 1`. -/
def chiOneRelativeEntropy (u : ℝ) : ℝ := u - 1 - Real.log u

/-- Derivative of `chiOneRelativeEntropy` on the positive axis. -/
def chiOneEntropyMultiplier (u : ℝ) : ℝ := 1 - u⁻¹

theorem chiOneRelativeEntropy_hasDerivAt {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt chiOneRelativeEntropy (chiOneEntropyMultiplier u) u := by
  simpa [chiOneRelativeEntropy, chiOneEntropyMultiplier] using
    (((hasDerivAt_id u).sub (hasDerivAt_const u (1 : ℝ))).sub
      (Real.hasDerivAt_log hu))

theorem chiOneEntropyMultiplier_comp_hasDerivAt
    {u ux : ℝ → ℝ} {x : ℝ}
    (hu : HasDerivAt u (ux x) x) (hux : u x ≠ 0) :
    HasDerivAt (fun y ↦ chiOneEntropyMultiplier (u y))
      (ux x / (u x) ^ 2) x := by
  have hscalar : HasDerivAt chiOneEntropyMultiplier ((u x) ^ 2)⁻¹ (u x) := by
    simpa [chiOneEntropyMultiplier] using
      ((hasDerivAt_const (u x) (1 : ℝ)).sub (hasDerivAt_inv hux))
  convert hscalar.comp x hu using 1 <;> simp [div_eq_mul_inv, mul_comm]

/-- One smooth positive periodic time slice of the normalized
`m = gamma = alpha = 1` system.  The fields are named explicitly so the
interface can be instantiated either from a classical solution or from a
compactness limit. -/
structure ChiOnePeriodicEntropySlice
    (a b c chi : ℝ) (u ux uxx r rx rxx ut : ℝ → ℝ) : Prop where
  hab : a ≤ b
  u_pos : ∀ x, 0 < u x
  u_deriv : ∀ x, HasDerivAt u (ux x) x
  ux_deriv : ∀ x, HasDerivAt ux (uxx x) x
  r_deriv : ∀ x, HasDerivAt r (rx x) x
  rx_deriv : ∀ x, HasDerivAt rx (rxx x) x
  uxx_continuous : Continuous uxx
  rxx_continuous : Continuous rxx
  ut_continuous : Continuous ut
  population_pde : ∀ x,
    ut x = uxx x + c * ux x -
      chi * (ux x * rx x + u x * rxx x) + u x * (1 - u x)
  resolver_pde : ∀ x, -rxx x + r x = u x - 1
  periodic_u : u b = u a
  periodic_ux : ux b = ux a
  periodic_r : r b = r a
  periodic_rx : rx b = rx a

namespace ChiOnePeriodicEntropySlice

variable {a b c chi : ℝ} {u ux uxx r rx rxx ut : ℝ → ℝ}
    (d : ChiOnePeriodicEntropySlice a b c chi u ux uxx r rx rxx ut)

include d

theorem u_continuous : Continuous u := by
  rw [continuous_iff_continuousAt]
  exact fun x ↦ (d.u_deriv x).continuousAt

theorem ux_continuous : Continuous ux := by
  rw [continuous_iff_continuousAt]
  exact fun x ↦ (d.ux_deriv x).continuousAt

theorem r_continuous : Continuous r := by
  rw [continuous_iff_continuousAt]
  exact fun x ↦ (d.r_deriv x).continuousAt

theorem rx_continuous : Continuous rx := by
  rw [continuous_iff_continuousAt]
  exact fun x ↦ (d.rx_deriv x).continuousAt

theorem multiplier_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y ↦ chiOneEntropyMultiplier (u y))
      (ux x / (u x) ^ 2) x :=
  chiOneEntropyMultiplier_comp_hasDerivAt (d.u_deriv x) (d.u_pos x).ne'

theorem entropy_comp_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y ↦ chiOneRelativeEntropy (u y))
      (chiOneEntropyMultiplier (u x) * ux x) x :=
  (chiOneRelativeEntropy_hasDerivAt (d.u_pos x).ne').comp x (d.u_deriv x)

/-- Periodicity removes the diffusion flux in the entropy identity. -/
theorem diffusion_integral :
    (∫ x in a..b, chiOneEntropyMultiplier (u x) * uxx x) =
      -∫ x in a..b, (ux x / u x) ^ 2 := by
  have hmult_cont : Continuous (fun x ↦ chiOneEntropyMultiplier (u x)) := by
    rw [continuous_iff_continuousAt]
    exact fun x ↦ (d.multiplier_hasDerivAt x).continuousAt
  have hmult_deriv_cont : Continuous (fun x ↦ ux x / (u x) ^ 2) := by
    apply Continuous.div (d.ux_continuous)
      ((d.u_continuous).pow 2)
    exact fun x ↦ pow_ne_zero 2 (d.u_pos x).ne'
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := a) (b := b)
    (u := fun x ↦ chiOneEntropyMultiplier (u x)) (v := ux)
    (u' := fun x ↦ ux x / (u x) ^ 2) (v' := uxx)
    (fun x _ ↦ d.multiplier_hasDerivAt x)
    (fun x _ ↦ d.ux_deriv x)
    (hmult_deriv_cont.intervalIntegrable a b)
    (d.uxx_continuous.intervalIntegrable a b)
  have hboundary :
      chiOneEntropyMultiplier (u b) * ux b -
        chiOneEntropyMultiplier (u a) * ux a = 0 := by
    rw [d.periodic_u, d.periodic_ux]
    ring
  rw [hboundary, zero_sub] at hibp
  calc
    (∫ x in a..b, chiOneEntropyMultiplier (u x) * uxx x) =
        -∫ x in a..b, (ux x / (u x) ^ 2) * ux x := hibp
    _ = -∫ x in a..b, (ux x / u x) ^ 2 := by
      congr 1
      apply intervalIntegral.integral_congr
      intro x _
      field_simp [(d.u_pos x).ne']

/-- The constant co-moving drift is an exact periodic entropy flux. -/
theorem drift_integral :
    (∫ x in a..b,
        chiOneEntropyMultiplier (u x) * (c * ux x)) = 0 := by
  have hent_cont : Continuous (fun x ↦ chiOneRelativeEntropy (u x)) := by
    rw [continuous_iff_continuousAt]
    exact fun x ↦ (d.entropy_comp_hasDerivAt x).continuousAt
  have hmult_cont : Continuous (fun x ↦ chiOneEntropyMultiplier (u x)) := by
    rw [continuous_iff_continuousAt]
    exact fun x ↦ (d.multiplier_hasDerivAt x).continuousAt
  have hderiv_cont : Continuous
      (fun x ↦ chiOneEntropyMultiplier (u x) * ux x) := by
    exact hmult_cont.mul d.ux_continuous
  have hftc :
      (∫ x in a..b, chiOneEntropyMultiplier (u x) * ux x) =
        chiOneRelativeEntropy (u b) - chiOneRelativeEntropy (u a) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ ↦ d.entropy_comp_hasDerivAt x)
      (hderiv_cont.intervalIntegrable a b)
  have hzero :
      (∫ x in a..b, chiOneEntropyMultiplier (u x) * ux x) = 0 := by
    rw [hftc, d.periodic_u, sub_self]
  calc
    (∫ x in a..b,
        chiOneEntropyMultiplier (u x) * (c * ux x)) =
        c * ∫ x in a..b,
          chiOneEntropyMultiplier (u x) * ux x := by
      rw [show (fun x ↦ chiOneEntropyMultiplier (u x) * (c * ux x)) =
          (fun x ↦ c * (chiOneEntropyMultiplier (u x) * ux x)) by
        funext x
        ring]
      rw [intervalIntegral.integral_const_mul]
    _ = 0 := by rw [hzero, mul_zero]

/-- The nonlinear chemotaxis term has one exact flux and one entropy cross
term.  Periodicity kills the flux. -/
theorem chemotaxis_integral :
    (∫ x in a..b, chiOneEntropyMultiplier (u x) *
        (-chi * (ux x * rx x + u x * rxx x))) =
      chi * ∫ x in a..b, (ux x / u x) * rx x := by
  have hux_div_cont : Continuous (fun x ↦ ux x / u x) := by
    apply Continuous.div d.ux_continuous d.u_continuous
    exact fun x ↦ (d.u_pos x).ne'
  have hflux_deriv_cont : Continuous
      (fun x ↦ ux x * rx x + (u x - 1) * rxx x) :=
    (d.ux_continuous.mul d.rx_continuous).add
      ((d.u_continuous.sub continuous_const).mul d.rxx_continuous)
  have hcross_cont : Continuous (fun x ↦ (ux x / u x) * rx x) :=
    hux_div_cont.mul d.rx_continuous
  have hflux_hasDerivAt : ∀ x,
      HasDerivAt (fun y ↦ (u y - 1) * rx y)
        (ux x * rx x + (u x - 1) * rxx x) x := by
    intro x
    convert ((d.u_deriv x).sub_const 1).mul (d.rx_deriv x) using 1 <;> ring
  have hflux_zero :
      (∫ x in a..b, ux x * rx x + (u x - 1) * rxx x) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ ↦ hflux_hasDerivAt x)
      (hflux_deriv_cont.intervalIntegrable a b)]
    rw [d.periodic_u, d.periodic_rx, sub_self]
  have hcore :
      (∫ x in a..b, chiOneEntropyMultiplier (u x) *
          (ux x * rx x + u x * rxx x)) =
        -∫ x in a..b, (ux x / u x) * rx x := by
    calc
      (∫ x in a..b, chiOneEntropyMultiplier (u x) *
          (ux x * rx x + u x * rxx x)) =
          ∫ x in a..b,
            (ux x * rx x + (u x - 1) * rxx x) -
              (ux x / u x) * rx x := by
        apply intervalIntegral.integral_congr
        intro x _
        unfold chiOneEntropyMultiplier
        field_simp [(d.u_pos x).ne']
        <;> ring
      _ = (∫ x in a..b, ux x * rx x + (u x - 1) * rxx x) -
          ∫ x in a..b, (ux x / u x) * rx x := by
        rw [intervalIntegral.integral_sub
          (hflux_deriv_cont.intervalIntegrable a b)
          (hcross_cont.intervalIntegrable a b)]
      _ = -∫ x in a..b, (ux x / u x) * rx x := by
        rw [hflux_zero, zero_sub]
  rw [show (fun x ↦ chiOneEntropyMultiplier (u x) *
      (-chi * (ux x * rx x + u x * rxx x))) =
      (fun x ↦ -chi * (chiOneEntropyMultiplier (u x) *
        (ux x * rx x + u x * rxx x))) by
    funext x
    ring]
  rw [intervalIntegral.integral_const_mul, hcore]
  ring

/-- The logistic term is exactly the squared displacement in entropy
variables, without a Taylor remainder. -/
theorem reaction_integral :
    (∫ x in a..b, chiOneEntropyMultiplier (u x) *
        (u x * (1 - u x))) =
      -∫ x in a..b, (u x - 1) ^ 2 := by
  calc
    (∫ x in a..b, chiOneEntropyMultiplier (u x) *
        (u x * (1 - u x))) =
        ∫ x in a..b, -((u x - 1) ^ 2) := by
      apply intervalIntegral.integral_congr
      intro x _
      unfold chiOneEntropyMultiplier
      field_simp [(d.u_pos x).ne']
      <;> ring
    _ = -∫ x in a..b, (u x - 1) ^ 2 := by
      rw [intervalIntegral.integral_neg]

/-- Exact nonlinear entropy production identity on a periodic slice. -/
theorem entropy_production_identity :
    (∫ x in a..b, chiOneEntropyMultiplier (u x) * ut x) =
      -(∫ x in a..b, (ux x / u x) ^ 2) +
        chi * (∫ x in a..b, (ux x / u x) * rx x) -
          ∫ x in a..b, (u x - 1) ^ 2 := by
  let diffusion : ℝ → ℝ := fun x ↦
    chiOneEntropyMultiplier (u x) * uxx x
  let drift : ℝ → ℝ := fun x ↦
    chiOneEntropyMultiplier (u x) * (c * ux x)
  let chemotaxis : ℝ → ℝ := fun x ↦
    chiOneEntropyMultiplier (u x) *
      (-chi * (ux x * rx x + u x * rxx x))
  let reaction : ℝ → ℝ := fun x ↦
    chiOneEntropyMultiplier (u x) * (u x * (1 - u x))
  have hmult_cont : Continuous (fun x ↦ chiOneEntropyMultiplier (u x)) := by
    rw [continuous_iff_continuousAt]
    exact fun x ↦ (d.multiplier_hasDerivAt x).continuousAt
  have hdiff_cont : Continuous diffusion :=
    hmult_cont.mul d.uxx_continuous
  have hdrift_cont : Continuous drift :=
    hmult_cont.mul (continuous_const.mul d.ux_continuous)
  have hchem_cont : Continuous chemotaxis := by
    exact hmult_cont.mul <|
      continuous_const.mul <|
        (d.ux_continuous.mul d.rx_continuous).add
          (d.u_continuous.mul d.rxx_continuous)
  have hreact_cont : Continuous reaction :=
    hmult_cont.mul <|
      d.u_continuous.mul (continuous_const.sub d.u_continuous)
  have hintegrand : (fun x ↦ chiOneEntropyMultiplier (u x) * ut x) =
      diffusion + drift + chemotaxis + reaction := by
    funext x
    rw [d.population_pde x]
    dsimp [diffusion, drift, chemotaxis, reaction]
    ring
  rw [hintegrand]
  calc
    intervalIntegral (diffusion + drift + chemotaxis + reaction) a b volume =
        intervalIntegral (diffusion + drift + chemotaxis) a b volume +
          intervalIntegral reaction a b volume := by
      simpa only [Pi.add_apply] using intervalIntegral.integral_add
        (((hdiff_cont.add hdrift_cont).add hchem_cont).intervalIntegrable a b)
        (hreact_cont.intervalIntegrable a b)
    _ = (intervalIntegral (diffusion + drift) a b volume +
          intervalIntegral chemotaxis a b volume) +
        intervalIntegral reaction a b volume := by
      rw [show intervalIntegral (diffusion + drift + chemotaxis) a b volume =
          intervalIntegral (diffusion + drift) a b volume +
            intervalIntegral chemotaxis a b volume by
        simpa only [Pi.add_apply] using intervalIntegral.integral_add
          ((hdiff_cont.add hdrift_cont).intervalIntegrable a b)
          (hchem_cont.intervalIntegrable a b)]
    _ = ((intervalIntegral diffusion a b volume +
            intervalIntegral drift a b volume) +
          intervalIntegral chemotaxis a b volume) +
        intervalIntegral reaction a b volume := by
      rw [show intervalIntegral (diffusion + drift) a b volume =
          intervalIntegral diffusion a b volume +
            intervalIntegral drift a b volume by
        simpa only [Pi.add_apply] using intervalIntegral.integral_add
          (hdiff_cont.intervalIntegrable a b)
          (hdrift_cont.intervalIntegrable a b)]
    _ = _ := by
      dsimp [diffusion, drift, chemotaxis, reaction]
      rw [d.diffusion_integral, d.drift_integral,
        d.chemotaxis_integral, d.reaction_integral]
      ring

/-- **Sharp nonlinear entropy dissipation.**  The coefficient is positive
exactly below `|chi| = 4`. -/
theorem sharp_entropy_production_le :
    (∫ x in a..b, chiOneEntropyMultiplier (u x) * ut x) ≤
      -(1 - chi ^ 2 / 16) * ∫ x in a..b, (u x - 1) ^ 2 := by
  let A : ℝ → ℝ := fun x ↦ ux x / u x
  let W : ℝ → ℝ := fun x ↦ u x - 1
  have hA_cont : Continuous A := by
    apply Continuous.div d.ux_continuous d.u_continuous
    exact fun x ↦ (d.u_pos x).ne'
  have hW_cont : Continuous W := d.u_continuous.sub continuous_const
  have hcross_point : ∀ x,
      chi * (A x * rx x) ≤ A x ^ 2 + (chi ^ 2 / 4) * rx x ^ 2 := by
    intro x
    nlinarith [sq_nonneg (A x - (chi / 2) * rx x)]
  have hcross :
      chi * (∫ x in a..b, A x * rx x) ≤
        (∫ x in a..b, A x ^ 2) +
          (chi ^ 2 / 4) * ∫ x in a..b, rx x ^ 2 := by
    calc
      chi * (∫ x in a..b, A x * rx x) =
          ∫ x in a..b, chi * (A x * rx x) := by
        rw [intervalIntegral.integral_const_mul]
      _ ≤ ∫ x in a..b,
          A x ^ 2 + (chi ^ 2 / 4) * rx x ^ 2 := by
        apply intervalIntegral.integral_mono_on d.hab
          ((hA_cont.mul d.rx_continuous).const_mul chi |>.intervalIntegrable a b)
          (((hA_cont.pow 2).add
            ((d.rx_continuous.pow 2).const_mul (chi ^ 2 / 4))) |>.intervalIntegrable a b)
        intro x _
        exact hcross_point x
      _ = (∫ x in a..b, A x ^ 2) +
          (chi ^ 2 / 4) * ∫ x in a..b, rx x ^ 2 := by
        rw [intervalIntegral.integral_add
          ((hA_cont.pow 2).intervalIntegrable a b)
          (((d.rx_continuous.pow 2).const_mul (chi ^ 2 / 4)).intervalIntegrable a b),
          intervalIntegral.integral_const_mul]
  have hresolver :
      (∫ x in a..b, rx x ^ 2) ≤
        (1 / 4 : ℝ) * ∫ x in a..b, W x ^ 2 := by
    apply resolver_deriv_sq_le_quarter_source_sq
      (a := a) (b := b) (v := r) (v₁ := rx) (v₂ := rxx) (g := W)
      d.hab
      (fun x _ ↦ d.r_deriv x)
      (fun x _ ↦ d.rx_deriv x)
      (d.rxx_continuous.intervalIntegrable a b)
      ((hW_cont.pow 2).intervalIntegrable a b)
      (fun x _ ↦ d.resolver_pde x)
    rw [d.periodic_rx, d.periodic_r]
    linarith
  have hcoef : 0 ≤ chi ^ 2 / 4 := by positivity
  have hresolver_scaled := mul_le_mul_of_nonneg_left hresolver hcoef
  have hid := d.entropy_production_identity
  dsimp [A, W] at hcross hresolver_scaled ⊢
  nlinarith

omit d in
theorem sharp_entropy_margin_pos_iff (hchi : 0 ≤ chi) :
    0 < 1 - chi ^ 2 / 16 ↔ chi < 4 := by
  constructor <;> intro h <;> nlinarith

theorem sharp_entropy_production_lt
    (hchi : 0 ≤ chi) (hchi4 : chi < 4)
    (hnontrivial : 0 < ∫ x in a..b, (u x - 1) ^ 2) :
    (∫ x in a..b, chiOneEntropyMultiplier (u x) * ut x) < 0 := by
  have hmargin : 0 < 1 - chi ^ 2 / 16 :=
    (sharp_entropy_margin_pos_iff hchi).2 hchi4
  have hprod : 0 < (1 - chi ^ 2 / 16) *
      (∫ x in a..b, (u x - 1) ^ 2) := mul_pos hmargin hnontrivial
  exact lt_of_le_of_lt d.sharp_entropy_production_le
    (by nlinarith)

end ChiOnePeriodicEntropySlice

section AxiomAudit

#print axioms chiOneRelativeEntropy_hasDerivAt
#print axioms chiOneEntropyMultiplier_comp_hasDerivAt
#print axioms ChiOnePeriodicEntropySlice.diffusion_integral
#print axioms ChiOnePeriodicEntropySlice.drift_integral
#print axioms ChiOnePeriodicEntropySlice.chemotaxis_integral
#print axioms ChiOnePeriodicEntropySlice.reaction_integral
#print axioms ChiOnePeriodicEntropySlice.entropy_production_identity
#print axioms ChiOnePeriodicEntropySlice.sharp_entropy_production_le
#print axioms ChiOnePeriodicEntropySlice.sharp_entropy_margin_pos_iff
#print axioms ChiOnePeriodicEntropySlice.sharp_entropy_production_lt

end AxiomAudit

end ShenWork.Paper1
