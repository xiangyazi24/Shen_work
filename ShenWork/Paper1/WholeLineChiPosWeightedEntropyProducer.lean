import ShenWork.Paper1.WholeLineChiPosWeightedResolverProducer

/-!
# Whole-line sharp relative-entropy producer

This file turns the localized entropy algebra into an actual fixed-time
whole-line PDE estimate for the normalized case `m = gamma = alpha = 1`.
The only analytic inputs are the repository's `WholeLineIBPData` packages and
integrability of the displayed densities.

For `phi = localizingWeightAt k x₀`, the exact identity is

`Q = -D + chi X - W + F`,

where `D = integral phi (u_x/u)^2`, `W = integral phi (u-1)^2`, and
`X = integral phi (u_x/u) r_x`.  The three components of `F` satisfy

`F <= k D + (k/4 + chi*k/2 + |c|*k/ell) W + chi*k/2 I`.

Combining this with the near-sharp whole-line resolver producer yields a
strict weighted entropy margin for every `0 <= chi < 4`, provided the slice
has a positive floor `u >= ell`.  No smallness of `u-1` is used.
-/

open Filter MeasureTheory Real Set Topology

noncomputable section

namespace ShenWork.Paper1

def chiOneWeightedLogGradientSquare
    (k x₀ : ℝ) (u ux : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ, localizingWeightAt k x₀ x * (ux x / u x) ^ 2

def chiOneWeightedEntropyMainCross
    (k x₀ : ℝ) (u ux rx : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ,
    localizingWeightAt k x₀ x * (ux x / u x) * rx x

def chiOneWeightedEntropyProduction
    (k x₀ : ℝ) (u ut : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ,
    localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) * ut x

def chiOneWeightedDiffusionFlux
    (k x₀ : ℝ) (u ux : ℝ → ℝ) : ℝ :=
  -(∫ x : ℝ,
    deriv (localizingWeightAt k x₀) x *
      chiOneEntropyMultiplier (u x) * ux x)

def chiOneWeightedDriftFlux
    (c k x₀ : ℝ) (u : ℝ → ℝ) : ℝ :=
  -c * (∫ x : ℝ,
    deriv (localizingWeightAt k x₀) x * chiOneRelativeEntropy (u x))

def chiOneWeightedChemotaxisFlux
    (chi k x₀ : ℝ) (u rx : ℝ → ℝ) : ℝ :=
  chi * (∫ x : ℝ,
    deriv (localizingWeightAt k x₀) x * (u x - 1) * rx x)

def chiOneWeightedEntropyFlux
    (chi c k x₀ : ℝ) (u ux rx : ℝ → ℝ) : ℝ :=
  chiOneWeightedDiffusionFlux k x₀ u ux +
    chiOneWeightedDriftFlux c k x₀ u +
    chiOneWeightedChemotaxisFlux chi k x₀ u rx

/-- Analytic data for one positive whole-line entropy slice.  It extends the
resolver producer with the three raw integration-by-parts packages needed by
diffusion, drift, and chemotaxis. -/
structure ChiOneWeightedEntropyData
    (chi c ell k x₀ : ℝ)
    (u ux uxx ut r rx rxx : ℝ → ℝ) : Prop
    extends ChiOneWeightedResolverData k x₀ (fun x => u x - 1) r rx rxx where
  hchi : 0 ≤ chi
  hk1 : k < 1
  hell : 0 < ell
  u_floor : ∀ x : ℝ, ell ≤ u x
  population_pde : ∀ x : ℝ,
    ut x = uxx x + c * ux x -
      chi * (ux x * rx x + u x * rxx x) + u x * (1 - u x)
  diffusion_ibp : WholeLineIBPData
    (fun x : ℝ =>
      localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x))
    (fun x : ℝ =>
      deriv (localizingWeightAt k x₀) x * chiOneEntropyMultiplier (u x) +
        localizingWeightAt k x₀ x * (ux x / (u x) ^ 2))
    ux uxx
  drift_ibp : WholeLineIBPData
    (localizingWeightAt k x₀)
    (fun x : ℝ => deriv (localizingWeightAt k x₀) x)
    (fun x : ℝ => chiOneRelativeEntropy (u x))
    (fun x : ℝ => chiOneEntropyMultiplier (u x) * ux x)
  chemotaxis_ibp : WholeLineIBPData
    (fun x : ℝ =>
      localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x))
    (fun x : ℝ =>
      deriv (localizingWeightAt k x₀) x * chiOneEntropyMultiplier (u x) +
        localizingWeightAt k x₀ x * (ux x / (u x) ^ 2))
    (fun x : ℝ => u x * rx x)
    (fun x : ℝ => ux x * rx x + u x * rxx x)
  production_integrable : Integrable
    (fun x : ℝ =>
      localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) * ut x)
  logGradient_integrable : Integrable
    (fun x : ℝ => localizingWeightAt k x₀ x * (ux x / u x) ^ 2)
  mainCross_integrable : Integrable
    (fun x : ℝ =>
      localizingWeightAt k x₀ x * (ux x / u x) * rx x)
  diffusionFlux_integrable : Integrable
    (fun x : ℝ =>
      deriv (localizingWeightAt k x₀) x *
        chiOneEntropyMultiplier (u x) * ux x)
  driftFlux_integrable : Integrable
    (fun x : ℝ =>
      deriv (localizingWeightAt k x₀) x * chiOneRelativeEntropy (u x))
  chemotaxisFlux_integrable : Integrable
    (fun x : ℝ =>
      deriv (localizingWeightAt k x₀) x * (u x - 1) * rx x)
  reaction_integrable : Integrable
    (fun x : ℝ =>
      localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) *
        (u x * (1 - u x)))

namespace ChiOneWeightedEntropyData

variable {chi c ell k x₀ : ℝ}
    {u ux uxx ut r rx rxx : ℝ → ℝ}
    (H : ChiOneWeightedEntropyData chi c ell k x₀ u ux uxx ut r rx rxx)

include H

theorem u_pos (x : ℝ) : 0 < u x := H.hell.trans_le (H.u_floor x)

theorem logGradientSquare_nonneg :
    0 ≤ chiOneWeightedLogGradientSquare k x₀ u ux := by
  unfold chiOneWeightedLogGradientSquare
  exact integral_nonneg fun x =>
    mul_nonneg (localizingWeightAt_pos k x₀ x).le (sq_nonneg _)

theorem diffusion_integral :
    (∫ x : ℝ,
        localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) * uxx x) =
      -chiOneWeightedLogGradientSquare k x₀ u ux +
        chiOneWeightedDiffusionFlux k x₀ u ux := by
  have hibp := H.diffusion_ibp.integral_mul_deriv
  have hright :
      (∫ x : ℝ,
        (deriv (localizingWeightAt k x₀) x *
              chiOneEntropyMultiplier (u x) +
            localizingWeightAt k x₀ x * (ux x / (u x) ^ 2)) * ux x) =
        (∫ x : ℝ,
          deriv (localizingWeightAt k x₀) x *
            chiOneEntropyMultiplier (u x) * ux x) +
          chiOneWeightedLogGradientSquare k x₀ u ux := by
    rw [show (fun x : ℝ =>
        (deriv (localizingWeightAt k x₀) x *
              chiOneEntropyMultiplier (u x) +
            localizingWeightAt k x₀ x * (ux x / (u x) ^ 2)) * ux x) =
        (fun x : ℝ =>
          deriv (localizingWeightAt k x₀) x *
            chiOneEntropyMultiplier (u x) * ux x) +
        (fun x : ℝ =>
          localizingWeightAt k x₀ x * (ux x / u x) ^ 2) by
      funext x
      simp only [Pi.add_apply]
      field_simp [(H.u_pos x).ne']
      <;> ring]
    change (∫ x : ℝ,
      deriv (localizingWeightAt k x₀) x *
          chiOneEntropyMultiplier (u x) * ux x +
        localizingWeightAt k x₀ x * (ux x / u x) ^ 2) = _
    rw [integral_add H.diffusionFlux_integrable H.logGradient_integrable]
    rfl
  rw [hright] at hibp
  unfold chiOneWeightedDiffusionFlux
  linarith

theorem drift_integral :
    (∫ x : ℝ,
        localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) *
          (c * ux x)) =
      chiOneWeightedDriftFlux c k x₀ u := by
  have hibp := H.drift_ibp.integral_mul_deriv
  unfold chiOneWeightedDriftFlux
  calc
    (∫ x : ℝ,
        localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) *
          (c * ux x)) =
        c * (∫ x : ℝ,
          localizingWeightAt k x₀ x *
            (chiOneEntropyMultiplier (u x) * ux x)) := by
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    _ = -c * (∫ x : ℝ,
          deriv (localizingWeightAt k x₀) x *
            chiOneRelativeEntropy (u x)) := by rw [hibp]; ring

theorem chemotaxis_core_integral :
    (∫ x : ℝ,
        localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) *
          (ux x * rx x + u x * rxx x)) =
      -(∫ x : ℝ,
          deriv (localizingWeightAt k x₀) x * (u x - 1) * rx x) -
        chiOneWeightedEntropyMainCross k x₀ u ux rx := by
  have hibp := H.chemotaxis_ibp.integral_mul_deriv
  have hright :
      (∫ x : ℝ,
        (deriv (localizingWeightAt k x₀) x *
              chiOneEntropyMultiplier (u x) +
            localizingWeightAt k x₀ x * (ux x / (u x) ^ 2)) *
          (u x * rx x)) =
        (∫ x : ℝ,
          deriv (localizingWeightAt k x₀) x * (u x - 1) * rx x) +
          chiOneWeightedEntropyMainCross k x₀ u ux rx := by
    rw [show (fun x : ℝ =>
        (deriv (localizingWeightAt k x₀) x *
              chiOneEntropyMultiplier (u x) +
            localizingWeightAt k x₀ x * (ux x / (u x) ^ 2)) *
          (u x * rx x)) =
        (fun x : ℝ =>
          deriv (localizingWeightAt k x₀) x * (u x - 1) * rx x) +
        (fun x : ℝ =>
          localizingWeightAt k x₀ x * (ux x / u x) * rx x) by
      funext x
      simp only [Pi.add_apply]
      unfold chiOneEntropyMultiplier
      field_simp [(H.u_pos x).ne']
      <;> ring]
    change (∫ x : ℝ,
      deriv (localizingWeightAt k x₀) x * (u x - 1) * rx x +
        localizingWeightAt k x₀ x * (ux x / u x) * rx x) = _
    rw [integral_add H.chemotaxisFlux_integrable H.mainCross_integrable]
    rfl
  rw [hright] at hibp
  linarith

theorem chemotaxis_integral :
    (∫ x : ℝ,
        localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) *
          (-chi * (ux x * rx x + u x * rxx x))) =
      chi * chiOneWeightedEntropyMainCross k x₀ u ux rx +
        chiOneWeightedChemotaxisFlux chi k x₀ u rx := by
  have hcore := H.chemotaxis_core_integral
  unfold chiOneWeightedChemotaxisFlux
  calc
    (∫ x : ℝ,
        localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) *
          (-chi * (ux x * rx x + u x * rxx x))) =
        -chi * (∫ x : ℝ,
          localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) *
            (ux x * rx x + u x * rxx x)) := by
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    _ = chi * chiOneWeightedEntropyMainCross k x₀ u ux rx +
        chi * (∫ x : ℝ,
          deriv (localizingWeightAt k x₀) x * (u x - 1) * rx x) := by
      rw [hcore]
      ring

theorem reaction_integral :
    (∫ x : ℝ,
        localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) *
          (u x * (1 - u x))) =
      -chiOneWeightedSourceSquare k x₀ (fun x => u x - 1) := by
  unfold chiOneWeightedSourceSquare
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with x
  unfold chiOneEntropyMultiplier
  field_simp [(H.u_pos x).ne']
  <;> ring

theorem production_identity :
    chiOneWeightedEntropyProduction k x₀ u ut =
      -chiOneWeightedLogGradientSquare k x₀ u ux +
        chi * chiOneWeightedEntropyMainCross k x₀ u ux rx -
        chiOneWeightedSourceSquare k x₀ (fun x => u x - 1) +
        chiOneWeightedEntropyFlux chi c k x₀ u ux rx := by
  have hdiff := H.diffusion_integral
  have hdrift := H.drift_integral
  have hchem := H.chemotaxis_integral
  have hreact := H.reaction_integral
  unfold chiOneWeightedEntropyProduction
  calc
    (∫ x : ℝ,
        localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) * ut x) =
        ∫ x : ℝ,
          localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) * uxx x +
          localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) *
            (c * ux x) +
          localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) *
            (-chi * (ux x * rx x + u x * rxx x)) +
          localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) *
            (u x * (1 - u x)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [H.population_pde x]
      ring
    _ = (∫ x : ℝ,
          localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) * uxx x) +
        (∫ x : ℝ,
          localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) *
            (c * ux x)) +
        (∫ x : ℝ,
          localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) *
            (-chi * (ux x * rx x + u x * rxx x))) +
        (∫ x : ℝ,
          localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) *
            (u x * (1 - u x))) := by
      have hdriftInt : Integrable (fun x : ℝ =>
          localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) *
            (c * ux x)) := by
        convert H.drift_ibp.left_integrable.const_mul c using 1
        funext x
        ring
      have hchemInt : Integrable (fun x : ℝ =>
          localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) *
            (-chi * (ux x * rx x + u x * rxx x))) := by
        convert H.chemotaxis_ibp.left_integrable.const_mul (-chi) using 1
        funext x
        ring
      calc
        (∫ x : ℝ,
            localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) * uxx x +
              localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) *
                (c * ux x) +
              localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) *
                (-chi * (ux x * rx x + u x * rxx x)) +
              localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) *
                (u x * (1 - u x))) =
            (∫ x : ℝ,
              localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) * uxx x +
                localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) *
                  (c * ux x) +
                localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) *
                  (-chi * (ux x * rx x + u x * rxx x))) +
              ∫ x : ℝ,
                localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) *
                  (u x * (1 - u x)) :=
          integral_add
            ((H.diffusion_ibp.left_integrable.add hdriftInt).add hchemInt)
            H.reaction_integrable
        _ = ((∫ x : ℝ,
                localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) * uxx x +
                  localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) *
                    (c * ux x)) +
              ∫ x : ℝ,
                localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) *
                  (-chi * (ux x * rx x + u x * rxx x))) +
              ∫ x : ℝ,
                localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) *
                  (u x * (1 - u x)) := by
          congr 1
          exact integral_add
            (H.diffusion_ibp.left_integrable.add hdriftInt) hchemInt
        _ = (∫ x : ℝ,
                localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) * uxx x) +
              (∫ x : ℝ,
                localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) *
                  (c * ux x)) +
              (∫ x : ℝ,
                localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) *
                  (-chi * (ux x * rx x + u x * rxx x))) +
              (∫ x : ℝ,
                localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) *
                  (u x * (1 - u x))) := by
          have hab :
              (∫ x : ℝ,
                localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) * uxx x +
                  localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) *
                    (c * ux x)) =
                (∫ x : ℝ,
                  localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) * uxx x) +
                  ∫ x : ℝ,
                    localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u x) *
                      (c * ux x) :=
            integral_add H.diffusion_ibp.left_integrable hdriftInt
          rw [hab]
    _ = -chiOneWeightedLogGradientSquare k x₀ u ux +
        chi * chiOneWeightedEntropyMainCross k x₀ u ux rx -
        chiOneWeightedSourceSquare k x₀ (fun x => u x - 1) +
        chiOneWeightedEntropyFlux chi c k x₀ u ux rx := by
      rw [hdiff, hdrift, hchem, hreact]
      unfold chiOneWeightedEntropyFlux
      ring

/-! ## Pointwise flux inequalities -/

omit H in
private theorem diffusion_flux_pointwise
    {k phi phix w a : ℝ}
    (hk : 0 ≤ k) (hphi : 0 ≤ phi) (hslope : |phix| ≤ k * phi) :
    -phix * w * a ≤ k * phi * a ^ 2 + (k / 4) * phi * w ^ 2 := by
  have hwa : |w * a| ≤ a ^ 2 + w ^ 2 / 4 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|a| - |w| / 2), sq_abs a, sq_abs w]
  calc
    -phix * w * a = -(phix * w * a) := by ring
    _ ≤ |phix * w * a| := neg_le_abs _
    _ = |phix| * |w * a| := by simp only [abs_mul]; ring
    _ ≤ (k * phi) * |w * a| :=
      mul_le_mul_of_nonneg_right hslope (abs_nonneg _)
    _ ≤ (k * phi) * (a ^ 2 + w ^ 2 / 4) :=
      mul_le_mul_of_nonneg_left hwa (mul_nonneg hk hphi)
    _ = k * phi * a ^ 2 + (k / 4) * phi * w ^ 2 := by ring

omit H in
private theorem chemotaxis_flux_pointwise
    {chi k phi phix w b : ℝ}
    (hchi : 0 ≤ chi) (hk : 0 ≤ k) (hphi : 0 ≤ phi)
    (hslope : |phix| ≤ k * phi) :
    chi * phix * w * b ≤
      (chi * k / 2) * (phi * w ^ 2 + phi * b ^ 2) := by
  have hwb : |w * b| ≤ (w ^ 2 + b ^ 2) / 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|w| - |b|), sq_abs w, sq_abs b]
  calc
    chi * phix * w * b ≤ |chi * phix * w * b| := le_abs_self _
    _ = chi * |phix| * |w * b| := by
      simp only [abs_mul, abs_of_nonneg hchi]
      ring
    _ ≤ chi * (k * phi) * |w * b| := by
      have hs : chi * |phix| ≤ chi * (k * phi) :=
        mul_le_mul_of_nonneg_left hslope hchi
      exact mul_le_mul_of_nonneg_right hs (abs_nonneg _)
    _ ≤ chi * (k * phi) * ((w ^ 2 + b ^ 2) / 2) := by
      exact mul_le_mul_of_nonneg_left hwb
        (mul_nonneg hchi (mul_nonneg hk hphi))
    _ = (chi * k / 2) * (phi * w ^ 2 + phi * b ^ 2) := by ring

omit H in
private theorem main_cross_pointwise
    {chi k phi a b : ℝ}
    (hk : k < 1) (hphi : 0 ≤ phi) :
    chi * (phi * a * b) ≤
      (1 - k) * (phi * a ^ 2) +
        chi ^ 2 / (4 * (1 - k)) * (phi * b ^ 2) := by
  have hkpos : 0 < 1 - k := sub_pos.mpr hk
  have hsq :
      0 ≤ phi * (2 * (1 - k) * a - chi * b) ^ 2 :=
    mul_nonneg hphi (sq_nonneg _)
  have hden : 0 < 4 * (1 - k) := by positivity
  rw [show
    (1 - k) * (phi * a ^ 2) +
        chi ^ 2 / (4 * (1 - k)) * (phi * b ^ 2) =
      ((4 * (1 - k) ^ 2 * phi * a ^ 2) +
        chi ^ 2 * phi * b ^ 2) / (4 * (1 - k)) by
      field_simp [hkpos.ne']]
  apply (le_div_iff₀ hden).2
  nlinarith

theorem mainCross_le :
    chi * chiOneWeightedEntropyMainCross k x₀ u ux rx ≤
      (1 - k) * chiOneWeightedLogGradientSquare k x₀ u ux +
        chi ^ 2 / (4 * (1 - k)) *
          chiOneWeightedSignalGradientSquare k x₀ rx := by
  unfold chiOneWeightedEntropyMainCross chiOneWeightedLogGradientSquare
    chiOneWeightedSignalGradientSquare
  let f : ℝ → ℝ := fun x =>
    localizingWeightAt k x₀ x * (ux x / u x) * rx x
  let g : ℝ → ℝ := fun x =>
    (1 - k) * (localizingWeightAt k x₀ x * (ux x / u x) ^ 2)
  let j : ℝ → ℝ := fun x =>
    chi ^ 2 / (4 * (1 - k)) *
      (localizingWeightAt k x₀ x * (rx x) ^ 2)
  have hf : Integrable f := H.mainCross_integrable
  have hg : Integrable g := H.logGradient_integrable.const_mul (1 - k)
  have hj : Integrable j :=
    H.toChiOneWeightedResolverData.gradientSquare_integrable.const_mul
      (chi ^ 2 / (4 * (1 - k)))
  have hmono : (∫ x : ℝ, chi * f x) ≤ ∫ x : ℝ, g x + j x := by
    apply integral_mono (hf.const_mul chi) (hg.add hj)
    intro x
    dsimp [f, g, j]
    exact main_cross_pointwise H.hk1 (localizingWeightAt_pos k x₀ x).le
  calc
    chi * (∫ x : ℝ,
        localizingWeightAt k x₀ x * (ux x / u x) * rx x) =
        ∫ x : ℝ, chi * f x := by
      rw [integral_const_mul]
    _ ≤ ∫ x : ℝ, g x + j x := hmono
    _ = (∫ x : ℝ, g x) + ∫ x : ℝ, j x := integral_add hg hj
    _ = (1 - k) *
          (∫ x : ℝ, localizingWeightAt k x₀ x * (ux x / u x) ^ 2) +
        chi ^ 2 / (4 * (1 - k)) *
          (∫ x : ℝ, localizingWeightAt k x₀ x * (rx x) ^ 2) := by
      dsimp [g, j]
      rw [integral_const_mul, integral_const_mul]

theorem diffusionFlux_le :
    chiOneWeightedDiffusionFlux k x₀ u ux ≤
      k * chiOneWeightedLogGradientSquare k x₀ u ux +
        (k / 4) * chiOneWeightedSourceSquare k x₀ (fun x => u x - 1) := by
  unfold chiOneWeightedDiffusionFlux chiOneWeightedLogGradientSquare
    chiOneWeightedSourceSquare
  let f : ℝ → ℝ := fun x =>
    deriv (localizingWeightAt k x₀) x *
      chiOneEntropyMultiplier (u x) * ux x
  let g : ℝ → ℝ := fun x =>
    k * (localizingWeightAt k x₀ x * (ux x / u x) ^ 2)
  let j : ℝ → ℝ := fun x =>
    (k / 4) * (localizingWeightAt k x₀ x * (u x - 1) ^ 2)
  have hf : Integrable f := H.diffusionFlux_integrable
  have hg : Integrable g := H.logGradient_integrable.const_mul k
  have hj : Integrable j :=
    H.toChiOneWeightedResolverData.sourceSquare_integrable.const_mul (k / 4)
  have hmono : (∫ x : ℝ, -f x) ≤ ∫ x : ℝ, g x + j x := by
    apply integral_mono hf.neg (hg.add hj)
    intro x
    dsimp [f, g, j]
    calc
      -(deriv (localizingWeightAt k x₀) x *
          chiOneEntropyMultiplier (u x) * ux x) =
          -deriv (localizingWeightAt k x₀) x *
            (u x - 1) * (ux x / u x) := by
        unfold chiOneEntropyMultiplier
        field_simp [(H.u_pos x).ne']
        <;> ring
      _ ≤ k * (localizingWeightAt k x₀ x * (ux x / u x) ^ 2) +
          (k / 4) * (localizingWeightAt k x₀ x * (u x - 1) ^ 2) :=
        by
          simpa only [mul_assoc] using
            (diffusion_flux_pointwise
              (k := k) (phi := localizingWeightAt k x₀ x)
              (phix := deriv (localizingWeightAt k x₀) x)
              (w := u x - 1) (a := ux x / u x)
              H.toChiOneWeightedResolverData.hk0
              (localizingWeightAt_pos k x₀ x).le
              (abs_deriv_localizingWeightAt_le
                H.toChiOneWeightedResolverData.hk0 x₀ x))
  calc
    -(∫ x : ℝ,
        deriv (localizingWeightAt k x₀) x *
          chiOneEntropyMultiplier (u x) * ux x) =
        ∫ x : ℝ, -f x := by
      rw [integral_neg]
    _ ≤ ∫ x : ℝ, g x + j x := hmono
    _ = (∫ x : ℝ, g x) + ∫ x : ℝ, j x := integral_add hg hj
    _ = k * (∫ x : ℝ,
          localizingWeightAt k x₀ x * (ux x / u x) ^ 2) +
        (k / 4) * (∫ x : ℝ,
          localizingWeightAt k x₀ x * (u x - 1) ^ 2) := by
      dsimp [g, j]
      rw [integral_const_mul, integral_const_mul]

theorem driftFlux_le :
    chiOneWeightedDriftFlux c k x₀ u ≤
      (|c| * k / ell) *
        chiOneWeightedSourceSquare k x₀ (fun x => u x - 1) := by
  unfold chiOneWeightedDriftFlux chiOneWeightedSourceSquare
  let f : ℝ → ℝ := fun x =>
    deriv (localizingWeightAt k x₀) x * chiOneRelativeEntropy (u x)
  let g : ℝ → ℝ := fun x =>
    (|c| * k / ell) *
      (localizingWeightAt k x₀ x * (u x - 1) ^ 2)
  have hf : Integrable f := H.driftFlux_integrable
  have hg : Integrable g :=
    H.toChiOneWeightedResolverData.sourceSquare_integrable.const_mul
      (|c| * k / ell)
  have hmono : (∫ x : ℝ, -c * f x) ≤ ∫ x : ℝ, g x := by
    apply integral_mono (hf.const_mul (-c)) hg
    intro x
    dsimp [f, g]
    have hent0 := chiOneRelativeEntropy_nonneg (H.u_pos x)
    have hent := chiOneRelativeEntropy_le_sq_div H.hell (H.u_floor x)
    have hslope := abs_deriv_localizingWeightAt_le
      H.toChiOneWeightedResolverData.hk0 x₀ x
    have hphi : 0 ≤ localizingWeightAt k x₀ x :=
      (localizingWeightAt_pos k x₀ x).le
    calc
      -c * (deriv (localizingWeightAt k x₀) x *
          chiOneRelativeEntropy (u x)) =
          -(c * (deriv (localizingWeightAt k x₀) x *
            chiOneRelativeEntropy (u x))) := by ring
      _ ≤ |c * (deriv (localizingWeightAt k x₀) x *
            chiOneRelativeEntropy (u x))| := neg_le_abs _
      _ = |c| * |deriv (localizingWeightAt k x₀) x| *
          chiOneRelativeEntropy (u x) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hent0]
        ring
      _ ≤ |c| * (k * localizingWeightAt k x₀ x) *
          chiOneRelativeEntropy (u x) := by
        have hs : |c| * |deriv (localizingWeightAt k x₀) x| ≤
            |c| * (k * localizingWeightAt k x₀ x) :=
          mul_le_mul_of_nonneg_left hslope (abs_nonneg c)
        exact mul_le_mul_of_nonneg_right hs hent0
      _ ≤ |c| * (k * localizingWeightAt k x₀ x) *
          ((u x - 1) ^ 2 / ell) := by
        exact mul_le_mul_of_nonneg_left hent
          (mul_nonneg (abs_nonneg c)
            (mul_nonneg H.toChiOneWeightedResolverData.hk0 hphi))
      _ = (|c| * k / ell) *
          (localizingWeightAt k x₀ x * (u x - 1) ^ 2) := by ring
  calc
    -c * (∫ x : ℝ,
        deriv (localizingWeightAt k x₀) x * chiOneRelativeEntropy (u x)) =
        ∫ x : ℝ, -c * f x := by
      rw [integral_const_mul]
    _ ≤ ∫ x : ℝ, g x := hmono
    _ = (|c| * k / ell) *
        (∫ x : ℝ, localizingWeightAt k x₀ x * (u x - 1) ^ 2) := by
      dsimp [g]
      rw [integral_const_mul]

theorem chemotaxisFlux_le :
    chiOneWeightedChemotaxisFlux chi k x₀ u rx ≤
      (chi * k / 2) *
        (chiOneWeightedSourceSquare k x₀ (fun x => u x - 1) +
          chiOneWeightedSignalGradientSquare k x₀ rx) := by
  unfold chiOneWeightedChemotaxisFlux chiOneWeightedSourceSquare
    chiOneWeightedSignalGradientSquare
  let f : ℝ → ℝ := fun x =>
    deriv (localizingWeightAt k x₀) x * (u x - 1) * rx x
  let g : ℝ → ℝ := fun x =>
    localizingWeightAt k x₀ x * (u x - 1) ^ 2
  let j : ℝ → ℝ := fun x =>
    localizingWeightAt k x₀ x * (rx x) ^ 2
  have hf : Integrable f := H.chemotaxisFlux_integrable
  have hg : Integrable g :=
    H.toChiOneWeightedResolverData.sourceSquare_integrable
  have hj : Integrable j :=
    H.toChiOneWeightedResolverData.gradientSquare_integrable
  have hmono : (∫ x : ℝ, chi * f x) ≤
      ∫ x : ℝ, (chi * k / 2) * (g x + j x) := by
    apply integral_mono (hf.const_mul chi) ((hg.add hj).const_mul (chi * k / 2))
    intro x
    dsimp [f, g, j]
    simpa only [mul_assoc] using
      (chemotaxis_flux_pointwise
        (chi := chi) (k := k) (phi := localizingWeightAt k x₀ x)
        (phix := deriv (localizingWeightAt k x₀) x)
        (w := u x - 1) (b := rx x) H.hchi
        H.toChiOneWeightedResolverData.hk0
        (localizingWeightAt_pos k x₀ x).le
        (abs_deriv_localizingWeightAt_le
          H.toChiOneWeightedResolverData.hk0 x₀ x))
  calc
    chi * (∫ x : ℝ,
        deriv (localizingWeightAt k x₀) x * (u x - 1) * rx x) =
        ∫ x : ℝ, chi * f x := by
      rw [integral_const_mul]
    _ ≤ ∫ x : ℝ, (chi * k / 2) * (g x + j x) := hmono
    _ = (chi * k / 2) * (∫ x : ℝ, g x + j x) := by
      rw [integral_const_mul]
    _ = (chi * k / 2) *
        ((∫ x : ℝ, g x) + ∫ x : ℝ, j x) := by rw [integral_add hg hj]
    _ = (chi * k / 2) *
        ((∫ x : ℝ, localizingWeightAt k x₀ x * (u x - 1) ^ 2) +
          ∫ x : ℝ, localizingWeightAt k x₀ x * (rx x) ^ 2) := by rfl

theorem flux_budget :
    chiOneWeightedEntropyFlux chi c k x₀ u ux rx ≤
      k * chiOneWeightedLogGradientSquare k x₀ u ux +
        (k / 4 + chi * k / 2 + |c| * k / ell) *
          chiOneWeightedSourceSquare k x₀ (fun x => u x - 1) +
        (chi * k / 2) * chiOneWeightedSignalGradientSquare k x₀ rx := by
  have hd := H.diffusionFlux_le
  have hc := H.chemotaxisFlux_le
  have hv := H.driftFlux_le
  unfold chiOneWeightedEntropyFlux
  nlinarith

/-- The concrete whole-line sharp entropy estimate for one slice. -/
theorem entropy_decay :
    chiOneWeightedEntropyProduction k x₀ u ut ≤
      -(1 - chiOneWeightedEntropyLoss chi c ell k) *
        chiOneWeightedSourceSquare k x₀ (fun x => u x - 1) := by
  apply weighted_entropy_decay_of_flux_budget H.hchi H.hell
    H.toChiOneWeightedResolverData.hk0 H.hk1
    H.logGradientSquare_nonneg
    H.toChiOneWeightedResolverData.sourceSquare_nonneg
    (H.toChiOneWeightedResolverData.gradient_estimate H.hk1)
  · exact H.production_identity.le
  · exact H.mainCross_le
  · exact H.flux_budget

end ChiOneWeightedEntropyData

/-- A single localization slope works for every admissible whole-line slice
on the full sub-Turing range. -/
theorem exists_chiOne_wholeLineEntropySlope_full_sharp_range
    {chi c ell : ℝ} (hchi : 0 ≤ chi) (hchi4 : chi < 4) (hell : 0 < ell) :
    ∃ k : ℝ, 0 < k ∧ k < 1 ∧
      0 < 1 - chiOneWeightedEntropyLoss chi c ell k ∧
      ∀ (x₀ : ℝ) (u ux uxx ut r rx rxx : ℝ → ℝ),
        ChiOneWeightedEntropyData chi c ell k x₀ u ux uxx ut r rx rxx →
        chiOneWeightedEntropyProduction k x₀ u ut ≤
          -(1 - chiOneWeightedEntropyLoss chi c ell k) *
            chiOneWeightedSourceSquare k x₀ (fun x => u x - 1) := by
  obtain ⟨k, hk0, hk1, hloss⟩ :=
    exists_chiOne_localizationSlope_full_sharp_range hchi hchi4 hell
  refine ⟨k, hk0, hk1, sub_pos.mpr hloss, ?_⟩
  intro x₀ u ux uxx ut r rx rxx H
  exact H.entropy_decay

section AxiomAudit

#print axioms ChiOneWeightedEntropyData.production_identity
#print axioms ChiOneWeightedEntropyData.mainCross_le
#print axioms ChiOneWeightedEntropyData.flux_budget
#print axioms ChiOneWeightedEntropyData.entropy_decay
#print axioms exists_chiOne_wholeLineEntropySlope_full_sharp_range

end AxiomAudit

end ShenWork.Paper1
