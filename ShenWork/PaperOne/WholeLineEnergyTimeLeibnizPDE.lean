/-
  ShenWork/PaperOne/WholeLineEnergyTimeLeibnizPDE.lean

  Whole-line barrier-energy atoms for Paper 1:

  * `wholeLine_timeLeibniz_of_dominated`:
      d/dt (1/2 * ∫ phi^2) = ∫ phi * phi_t,
    from Mathlib dominated differentiation under the whole-line integral.

  * `wholeLine_pdeSubstitution_of_integrable`:
      ∫ phi * phi_t =
        ∫ phi * U_xx - chi * ∫ phi * ∂x(U^m V_x)
          + ∫ phi * U(1-U^alpha),
    from the weighted pointwise PDE identity and integral linearity.

  These mirror Paper-2
  `intervalDomain_l2_half_energy_hL2Time` and
  `intervalDomain_l2_half_energy_hPDEIntegral`, but keep the whole-line
  domination/integrability hypotheses explicit.
-/
import ShenWork.Defs
import Mathlib.Analysis.Calculus.ParametricIntegral

open Filter MeasureTheory Topology
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

/-! ## Barrier profiles and energy terms -/

/-- Upper-barrier excess profile `(U-hi)_+`. -/
def wholeLineUpperExcessProfile (U : ℝ → ℝ → ℝ) (hi : ℝ) (t x : ℝ) : ℝ :=
  max (U t x - hi) 0

/-- Lower-barrier deficit profile `(lo-U)_+`. -/
def wholeLineLowerDeficitProfile (U : ℝ → ℝ → ℝ) (lo : ℝ) (t x : ℝ) : ℝ :=
  max (lo - U t x) 0

/-- Whole-line half-energy `1/2 ∫ phi(t,x)^2 dx`. -/
def wholeLineHalfEnergy (phi : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℝ, (1 / 2 : ℝ) * (phi t x) ^ 2

/-- Upper-barrier half-energy. -/
def wholeLineUpperHalfExcessEnergy (U : ℝ → ℝ → ℝ) (hi t : ℝ) : ℝ :=
  wholeLineHalfEnergy (wholeLineUpperExcessProfile U hi) t

/-- Lower-barrier half-energy. -/
def wholeLineLowerHalfDeficitEnergy (U : ℝ → ℝ → ℝ) (lo t : ℝ) : ℝ :=
  wholeLineHalfEnergy (wholeLineLowerDeficitProfile U lo) t

/-- The half-energy integrand. -/
def wholeLineHalfEnergyIntegrand (phi : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (phi t x) ^ 2

/-- The formal time derivative of the half-energy integrand. -/
def wholeLineHalfEnergyIntegrandDeriv
    (phi phi_t : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  phi t x * phi_t t x

/-- Weighted time-derivative term `∫ phi phi_t`. -/
def wholeLineWeightedTimeTerm
    (phi phi_t : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℝ, wholeLineHalfEnergyIntegrandDeriv phi phi_t t x

/-! ## PDE densities and weighted integrals -/

/-- Diffusion density `U_xx`. -/
def wholeLineDiffusionDensity (U : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  iteratedDeriv 2 (U t) x

/-- Chemotaxis divergence density `∂x(U^m V_x)`. -/
def wholeLineChemotaxisDensity
    (p : CMParams) (U V : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  deriv (fun y : ℝ => (U t y) ^ p.m * deriv (V t) y) x

/-- Logistic density `U(1-U^alpha)`. -/
def wholeLineLogisticDensity (p : CMParams) (U : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  U t x * (1 - (U t x) ^ p.α)

/-- Full pointwise PDE right-hand side. -/
def wholeLinePDERHS
    (p : CMParams) (U V : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  wholeLineDiffusionDensity U t x
    - p.χ * wholeLineChemotaxisDensity p U V t x
    + wholeLineLogisticDensity p U t x

/-- Weighted diffusion integral `∫ phi U_xx`. -/
def wholeLineDiffusionIntegral
    (phi U : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℝ, phi t x * wholeLineDiffusionDensity U t x

/-- Weighted chemotaxis integral `∫ phi ∂x(U^m V_x)`. -/
def wholeLineChemotaxisIntegral
    (p : CMParams) (phi U V : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℝ, phi t x * wholeLineChemotaxisDensity p U V t x

/-- Weighted logistic integral `∫ phi U(1-U^alpha)`. -/
def wholeLineLogisticIntegral
    (p : CMParams) (phi U : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℝ, phi t x * wholeLineLogisticDensity p U t x

/-! ## timeLeibniz: dominated differentiation under the whole-line integral -/

/-- Whole-line half-energy time derivative from an explicit local dominated
differentiation package.

This is the whole-line mirror of Paper-2
`intervalDomain_l2_half_energy_hL2Time_of_slabContinuous`, with the compact-slab
boundedness already expressed as the explicit integrable envelope `bound`. -/
theorem wholeLine_halfEnergy_hasDerivAt_of_dominated
    {phi phi_t : ℝ → ℝ → ℝ} {t δ : ℝ} {bound : ℝ → ℝ}
    (hδ : 0 < δ)
    (hF_meas :
      ∀ᶠ s in 𝓝 t,
        AEStronglyMeasurable (wholeLineHalfEnergyIntegrand phi s) volume)
    (hF_int :
      Integrable (wholeLineHalfEnergyIntegrand phi t) volume)
    (hF'_meas :
      AEStronglyMeasurable
        (wholeLineHalfEnergyIntegrandDeriv phi phi_t t) volume)
    (h_bound :
      ∀ᵐ x ∂volume,
        ∀ s ∈ Metric.ball t δ,
          ‖wholeLineHalfEnergyIntegrandDeriv phi phi_t s x‖ ≤ bound x)
    (hbound_int : Integrable bound volume)
    (hphi_hasDeriv :
      ∀ᵐ x ∂volume,
        ∀ s ∈ Metric.ball t δ,
          HasDerivAt (fun r : ℝ => phi r x) (phi_t s x) s) :
    HasDerivAt
      (fun s : ℝ => wholeLineHalfEnergy phi s)
      (wholeLineWeightedTimeTerm phi phi_t t) t := by
  have h_diff :
      ∀ᵐ x ∂volume,
        ∀ s ∈ Metric.ball t δ,
          HasDerivAt
            (fun r : ℝ => wholeLineHalfEnergyIntegrand phi r x)
            (wholeLineHalfEnergyIntegrandDeriv phi phi_t s x) s := by
    filter_upwards [hphi_hasDeriv] with x hx s hs
    have hsq := ((hx s hs).pow 2).const_mul (1 / 2 : ℝ)
    simpa [wholeLineHalfEnergyIntegrand, wholeLineHalfEnergyIntegrandDeriv, pow_one,
      mul_assoc, mul_left_comm, mul_comm] using hsq
  have hmain :
      HasDerivAt
        (fun s : ℝ => ∫ x : ℝ, wholeLineHalfEnergyIntegrand phi s x)
        (∫ x : ℝ, wholeLineHalfEnergyIntegrandDeriv phi phi_t t x) t :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume)
      (bound := bound)
      (F := wholeLineHalfEnergyIntegrand phi)
      (F' := wholeLineHalfEnergyIntegrandDeriv phi phi_t)
      (x₀ := t)
      (s := Metric.ball t δ)
      (Metric.ball_mem_nhds t hδ)
      hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2
  simpa [wholeLineHalfEnergy, wholeLineHalfEnergyIntegrand,
    wholeLineWeightedTimeTerm] using hmain

/-- The derivative form of `wholeLine_halfEnergy_hasDerivAt_of_dominated`.

This is the direct whole-line `timeLeibniz` atom:
`deriv (1/2 ∫ phi^2) = ∫ phi phi_t`. -/
theorem wholeLine_timeLeibniz_of_dominated
    {phi phi_t : ℝ → ℝ → ℝ} {t δ : ℝ} {bound : ℝ → ℝ}
    (hδ : 0 < δ)
    (hF_meas :
      ∀ᶠ s in 𝓝 t,
        AEStronglyMeasurable (wholeLineHalfEnergyIntegrand phi s) volume)
    (hF_int :
      Integrable (wholeLineHalfEnergyIntegrand phi t) volume)
    (hF'_meas :
      AEStronglyMeasurable
        (wholeLineHalfEnergyIntegrandDeriv phi phi_t t) volume)
    (h_bound :
      ∀ᵐ x ∂volume,
        ∀ s ∈ Metric.ball t δ,
          ‖wholeLineHalfEnergyIntegrandDeriv phi phi_t s x‖ ≤ bound x)
    (hbound_int : Integrable bound volume)
    (hphi_hasDeriv :
      ∀ᵐ x ∂volume,
        ∀ s ∈ Metric.ball t δ,
          HasDerivAt (fun r : ℝ => phi r x) (phi_t s x) s) :
    deriv (fun s : ℝ => wholeLineHalfEnergy phi s) t =
      wholeLineWeightedTimeTerm phi phi_t t :=
  (wholeLine_halfEnergy_hasDerivAt_of_dominated hδ hF_meas hF_int
    hF'_meas h_bound hbound_int hphi_hasDeriv).deriv

/-- Upper-excess specialization of the whole-line `timeLeibniz` atom. -/
theorem wholeLineUpper_timeLeibniz_of_dominated
    {U phi_t : ℝ → ℝ → ℝ} {hi t δ : ℝ} {bound : ℝ → ℝ}
    (hδ : 0 < δ)
    (hF_meas :
      ∀ᶠ s in 𝓝 t,
        AEStronglyMeasurable
          (wholeLineHalfEnergyIntegrand (wholeLineUpperExcessProfile U hi) s)
          volume)
    (hF_int :
      Integrable
        (wholeLineHalfEnergyIntegrand (wholeLineUpperExcessProfile U hi) t)
        volume)
    (hF'_meas :
      AEStronglyMeasurable
        (wholeLineHalfEnergyIntegrandDeriv
          (wholeLineUpperExcessProfile U hi) phi_t t)
        volume)
    (h_bound :
      ∀ᵐ x ∂volume,
        ∀ s ∈ Metric.ball t δ,
          ‖wholeLineHalfEnergyIntegrandDeriv
            (wholeLineUpperExcessProfile U hi) phi_t s x‖ ≤ bound x)
    (hbound_int : Integrable bound volume)
    (hphi_hasDeriv :
      ∀ᵐ x ∂volume,
        ∀ s ∈ Metric.ball t δ,
          HasDerivAt
            (fun r : ℝ => wholeLineUpperExcessProfile U hi r x)
            (phi_t s x) s) :
    deriv (fun s : ℝ => wholeLineUpperHalfExcessEnergy U hi s) t =
      wholeLineWeightedTimeTerm (wholeLineUpperExcessProfile U hi) phi_t t :=
  wholeLine_timeLeibniz_of_dominated hδ hF_meas hF_int hF'_meas
    h_bound hbound_int hphi_hasDeriv

/-- Lower-deficit specialization of the whole-line `timeLeibniz` atom. -/
theorem wholeLineLower_timeLeibniz_of_dominated
    {U phi_t : ℝ → ℝ → ℝ} {lo t δ : ℝ} {bound : ℝ → ℝ}
    (hδ : 0 < δ)
    (hF_meas :
      ∀ᶠ s in 𝓝 t,
        AEStronglyMeasurable
          (wholeLineHalfEnergyIntegrand (wholeLineLowerDeficitProfile U lo) s)
          volume)
    (hF_int :
      Integrable
        (wholeLineHalfEnergyIntegrand (wholeLineLowerDeficitProfile U lo) t)
        volume)
    (hF'_meas :
      AEStronglyMeasurable
        (wholeLineHalfEnergyIntegrandDeriv
          (wholeLineLowerDeficitProfile U lo) phi_t t)
        volume)
    (h_bound :
      ∀ᵐ x ∂volume,
        ∀ s ∈ Metric.ball t δ,
          ‖wholeLineHalfEnergyIntegrandDeriv
            (wholeLineLowerDeficitProfile U lo) phi_t s x‖ ≤ bound x)
    (hbound_int : Integrable bound volume)
    (hphi_hasDeriv :
      ∀ᵐ x ∂volume,
        ∀ s ∈ Metric.ball t δ,
          HasDerivAt
            (fun r : ℝ => wholeLineLowerDeficitProfile U lo r x)
            (phi_t s x) s) :
    deriv (fun s : ℝ => wholeLineLowerHalfDeficitEnergy U lo s) t =
      wholeLineWeightedTimeTerm (wholeLineLowerDeficitProfile U lo) phi_t t :=
  wholeLine_timeLeibniz_of_dominated hδ hF_meas hF_int hF'_meas
    h_bound hbound_int hphi_hasDeriv

/-! ## pdeSubstitution: pointwise PDE identity plus integral linearity -/

/-- Signed whole-line PDE-substitution identity.

`sigma = 1` is the upper-excess case (`phi_t = U_t` on the support of `phi`);
`sigma = -1` is the lower-deficit case (`phi_t = -U_t` on the support of `phi`).
The hypothesis is intentionally the weighted a.e. identity, which is the form
used by barrier energies after restricting to the positivity set of `phi`. -/
theorem wholeLine_pdeSubstitution_signed_of_integrable
    {p : CMParams} {phi phi_t U V : ℝ → ℝ → ℝ} {t sigma : ℝ}
    (hA :
      Integrable
        (fun x : ℝ => phi t x * wholeLineDiffusionDensity U t x) volume)
    (hB :
      Integrable
        (fun x : ℝ => phi t x * wholeLineChemotaxisDensity p U V t x) volume)
    (hC :
      Integrable
        (fun x : ℝ => phi t x * wholeLineLogisticDensity p U t x) volume)
    (hweightedPDE :
      ∀ᵐ x ∂volume,
        phi t x * phi_t t x =
          sigma *
            (phi t x * wholeLineDiffusionDensity U t x
              - p.χ * (phi t x * wholeLineChemotaxisDensity p U V t x)
              + phi t x * wholeLineLogisticDensity p U t x)) :
    wholeLineWeightedTimeTerm phi phi_t t =
      sigma *
        (wholeLineDiffusionIntegral phi U t
          - p.χ * wholeLineChemotaxisIntegral p phi U V t
          + wholeLineLogisticIntegral p phi U t) := by
  classical
  let A : ℝ → ℝ := fun x => phi t x * wholeLineDiffusionDensity U t x
  let B : ℝ → ℝ := fun x => phi t x * wholeLineChemotaxisDensity p U V t x
  let C : ℝ → ℝ := fun x => phi t x * wholeLineLogisticDensity p U t x
  have hAB : Integrable (fun x : ℝ => A x - p.χ * B x) volume :=
    hA.sub (hB.const_mul p.χ)
  have hABC : Integrable (fun x : ℝ => A x - p.χ * B x + C x) volume :=
    hAB.add hC
  have hcomb :
      (∫ x : ℝ, sigma * (A x - p.χ * B x + C x)) =
        sigma *
          ((∫ x : ℝ, A x) - p.χ * (∫ x : ℝ, B x) + ∫ x : ℝ, C x) := by
    rw [integral_const_mul, integral_add hAB hC, integral_sub hA (hB.const_mul p.χ),
      integral_const_mul]
  change wholeLineWeightedTimeTerm phi phi_t t =
    sigma * ((∫ x : ℝ, A x) - p.χ * (∫ x : ℝ, B x) + ∫ x : ℝ, C x)
  rw [← hcomb]
  unfold wholeLineWeightedTimeTerm
  refine integral_congr_ae ?_
  filter_upwards [hweightedPDE] with x hx
  simpa [A, B, C, wholeLineHalfEnergyIntegrandDeriv] using hx

/-- Upper-excess whole-line PDE substitution:
`∫ phi phi_t = ∫ phi U_xx - chi∫phi ∂x(U^m V_x) + ∫phi U(1-U^alpha)`. -/
theorem wholeLine_pdeSubstitution_of_integrable
    {p : CMParams} {phi phi_t U V : ℝ → ℝ → ℝ} {t : ℝ}
    (hA :
      Integrable
        (fun x : ℝ => phi t x * wholeLineDiffusionDensity U t x) volume)
    (hB :
      Integrable
        (fun x : ℝ => phi t x * wholeLineChemotaxisDensity p U V t x) volume)
    (hC :
      Integrable
        (fun x : ℝ => phi t x * wholeLineLogisticDensity p U t x) volume)
    (hweightedPDE :
      ∀ᵐ x ∂volume,
        phi t x * phi_t t x =
          phi t x * wholeLineDiffusionDensity U t x
            - p.χ * (phi t x * wholeLineChemotaxisDensity p U V t x)
            + phi t x * wholeLineLogisticDensity p U t x) :
    wholeLineWeightedTimeTerm phi phi_t t =
      wholeLineDiffusionIntegral phi U t
        - p.χ * wholeLineChemotaxisIntegral p phi U V t
        + wholeLineLogisticIntegral p phi U t := by
  simpa using
    (wholeLine_pdeSubstitution_signed_of_integrable
      (p := p) (phi := phi) (phi_t := phi_t) (U := U) (V := V)
      (t := t) (sigma := 1) hA hB hC (by
        filter_upwards [hweightedPDE] with x hx
        simpa using hx))

/-- Lower-deficit whole-line PDE substitution:
`phi_t = -U_t` on the support gives the opposite signed split. -/
theorem wholeLine_pdeSubstitution_lower_of_integrable
    {p : CMParams} {phi phi_t U V : ℝ → ℝ → ℝ} {t : ℝ}
    (hA :
      Integrable
        (fun x : ℝ => phi t x * wholeLineDiffusionDensity U t x) volume)
    (hB :
      Integrable
        (fun x : ℝ => phi t x * wholeLineChemotaxisDensity p U V t x) volume)
    (hC :
      Integrable
        (fun x : ℝ => phi t x * wholeLineLogisticDensity p U t x) volume)
    (hweightedPDE :
      ∀ᵐ x ∂volume,
        phi t x * phi_t t x =
          - (phi t x * wholeLineDiffusionDensity U t x
              - p.χ * (phi t x * wholeLineChemotaxisDensity p U V t x)
              + phi t x * wholeLineLogisticDensity p U t x)) :
    wholeLineWeightedTimeTerm phi phi_t t =
      -wholeLineDiffusionIntegral phi U t
        + p.χ * wholeLineChemotaxisIntegral p phi U V t
        - wholeLineLogisticIntegral p phi U t := by
  have h :=
    wholeLine_pdeSubstitution_signed_of_integrable
      (p := p) (phi := phi) (phi_t := phi_t) (U := U) (V := V)
      (t := t) (sigma := -1) hA hB hC (by
        filter_upwards [hweightedPDE] with x hx
        simpa using hx)
  simpa [neg_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

/-- Upper-excess specialization of `wholeLine_pdeSubstitution_of_integrable`. -/
theorem wholeLineUpper_pdeSubstitution_of_integrable
    {p : CMParams} {U V phi_t : ℝ → ℝ → ℝ} {hi t : ℝ}
    (hA :
      Integrable
        (fun x : ℝ =>
          wholeLineUpperExcessProfile U hi t x * wholeLineDiffusionDensity U t x)
        volume)
    (hB :
      Integrable
        (fun x : ℝ =>
          wholeLineUpperExcessProfile U hi t x *
            wholeLineChemotaxisDensity p U V t x)
        volume)
    (hC :
      Integrable
        (fun x : ℝ =>
          wholeLineUpperExcessProfile U hi t x *
            wholeLineLogisticDensity p U t x)
        volume)
    (hweightedPDE :
      ∀ᵐ x ∂volume,
        wholeLineUpperExcessProfile U hi t x * phi_t t x =
          wholeLineUpperExcessProfile U hi t x * wholeLineDiffusionDensity U t x
            - p.χ *
                (wholeLineUpperExcessProfile U hi t x *
                  wholeLineChemotaxisDensity p U V t x)
            + wholeLineUpperExcessProfile U hi t x *
                wholeLineLogisticDensity p U t x) :
    wholeLineWeightedTimeTerm (wholeLineUpperExcessProfile U hi) phi_t t =
      wholeLineDiffusionIntegral (wholeLineUpperExcessProfile U hi) U t
        - p.χ * wholeLineChemotaxisIntegral p
            (wholeLineUpperExcessProfile U hi) U V t
        + wholeLineLogisticIntegral p (wholeLineUpperExcessProfile U hi) U t :=
  wholeLine_pdeSubstitution_of_integrable hA hB hC hweightedPDE

/-- Lower-deficit specialization of `wholeLine_pdeSubstitution_lower_of_integrable`. -/
theorem wholeLineLower_pdeSubstitution_of_integrable
    {p : CMParams} {U V phi_t : ℝ → ℝ → ℝ} {lo t : ℝ}
    (hA :
      Integrable
        (fun x : ℝ =>
          wholeLineLowerDeficitProfile U lo t x * wholeLineDiffusionDensity U t x)
        volume)
    (hB :
      Integrable
        (fun x : ℝ =>
          wholeLineLowerDeficitProfile U lo t x *
            wholeLineChemotaxisDensity p U V t x)
        volume)
    (hC :
      Integrable
        (fun x : ℝ =>
          wholeLineLowerDeficitProfile U lo t x *
            wholeLineLogisticDensity p U t x)
        volume)
    (hweightedPDE :
      ∀ᵐ x ∂volume,
        wholeLineLowerDeficitProfile U lo t x * phi_t t x =
          - (wholeLineLowerDeficitProfile U lo t x *
                wholeLineDiffusionDensity U t x
              - p.χ *
                  (wholeLineLowerDeficitProfile U lo t x *
                    wholeLineChemotaxisDensity p U V t x)
              + wholeLineLowerDeficitProfile U lo t x *
                  wholeLineLogisticDensity p U t x)) :
    wholeLineWeightedTimeTerm (wholeLineLowerDeficitProfile U lo) phi_t t =
      -wholeLineDiffusionIntegral (wholeLineLowerDeficitProfile U lo) U t
        + p.χ * wholeLineChemotaxisIntegral p
            (wholeLineLowerDeficitProfile U lo) U V t
        - wholeLineLogisticIntegral p (wholeLineLowerDeficitProfile U lo) U t :=
  wholeLine_pdeSubstitution_lower_of_integrable hA hB hC hweightedPDE

#print axioms wholeLine_timeLeibniz_of_dominated
#print axioms wholeLine_pdeSubstitution_of_integrable
#print axioms wholeLine_pdeSubstitution_lower_of_integrable

end ShenWork.PaperOne
