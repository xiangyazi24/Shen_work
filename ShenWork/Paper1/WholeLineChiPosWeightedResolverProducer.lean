import ShenWork.Paper1.WholeLineChiPosWeightedEntropyRoute
import ShenWork.Paper1.WholeLineLocalMomentEnergy

/-!
# Whole-line producer for the near-sharp weighted resolver gain

This file discharges the scalar resolver hypotheses isolated in
`WholeLineChiPosWeightedEntropyRoute` from one genuine whole-line integration
by parts.  For `phi = localizingWeightAt k x₀` and

`-r_xx + r = w`,

the two exact identities are

`A + I + J = R`,  `S = A + 2 I + 2 J + C`,

where `J = integral phi_x r r_x`.  The logarithmic-slope estimate on `phi`
then gives `|J| <= k/2 (A+I)`.  Thus the near-sharp gain

`integral phi r_x^2 <= (1+k)/(4(1-k)) integral phi w^2`

is not merely an algebraic placeholder: it follows from the repository's
whole-line IBP interface under the listed, standard integrability and decay
hypotheses.
-/

open Filter MeasureTheory Real Set Topology

noncomputable section

namespace ShenWork.Paper1

def chiOneWeightedSourceSquare
    (k x₀ : ℝ) (w : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ, localizingWeightAt k x₀ x * (w x) ^ 2

def chiOneWeightedSignalSquare
    (k x₀ : ℝ) (r : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ, localizingWeightAt k x₀ x * (r x) ^ 2

def chiOneWeightedSignalGradientSquare
    (k x₀ : ℝ) (rx : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ, localizingWeightAt k x₀ x * (rx x) ^ 2

def chiOneWeightedSignalSecondSquare
    (k x₀ : ℝ) (rxx : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ, localizingWeightAt k x₀ x * (rxx x) ^ 2

def chiOneWeightedResolverCross
    (k x₀ : ℝ) (r rx : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ,
    deriv (localizingWeightAt k x₀) x * r x * rx x

def chiOneWeightedSourceSignalPair
    (k x₀ : ℝ) (w r : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ, localizingWeightAt k x₀ x * w x * r x

/-- Fixed-slice analytic data for weighted testing of the whole-line
Helmholtz resolver.  No conclusion of integration by parts is stored. -/
structure ChiOneWeightedResolverData
    (k x₀ : ℝ) (w r rx rxx : ℝ → ℝ) : Prop where
  hk0 : 0 ≤ k
  resolver : ∀ x : ℝ, -rxx x + r x = w x
  ibp : WholeLineIBPData
    (fun x : ℝ => localizingWeightAt k x₀ x * r x)
    (fun x : ℝ =>
      deriv (localizingWeightAt k x₀) x * r x +
        localizingWeightAt k x₀ x * rx x)
    rx rxx
  sourceSquare_integrable : Integrable
    (fun x : ℝ => localizingWeightAt k x₀ x * (w x) ^ 2)
  signalSquare_integrable : Integrable
    (fun x : ℝ => localizingWeightAt k x₀ x * (r x) ^ 2)
  gradientSquare_integrable : Integrable
    (fun x : ℝ => localizingWeightAt k x₀ x * (rx x) ^ 2)
  secondSquare_integrable : Integrable
    (fun x : ℝ => localizingWeightAt k x₀ x * (rxx x) ^ 2)
  weightCross_integrable : Integrable
    (fun x : ℝ =>
      deriv (localizingWeightAt k x₀) x * r x * rx x)
  sourceSignal_integrable : Integrable
    (fun x : ℝ => localizingWeightAt k x₀ x * w x * r x)

theorem ChiOneWeightedResolverData.signalSecond_ibp
    {k x₀ : ℝ} {w r rx rxx : ℝ → ℝ}
    (H : ChiOneWeightedResolverData k x₀ w r rx rxx) :
    (∫ x : ℝ,
        (localizingWeightAt k x₀ x * r x) * rxx x) =
      -(chiOneWeightedResolverCross k x₀ r rx +
        chiOneWeightedSignalGradientSquare k x₀ rx) := by
  have hibp := H.ibp.integral_mul_deriv
  calc
    (∫ x : ℝ,
        (localizingWeightAt k x₀ x * r x) * rxx x) =
        -∫ x : ℝ,
          (deriv (localizingWeightAt k x₀) x * r x +
              localizingWeightAt k x₀ x * rx x) * rx x := hibp
    _ = -(chiOneWeightedResolverCross k x₀ r rx +
          chiOneWeightedSignalGradientSquare k x₀ rx) := by
      unfold chiOneWeightedResolverCross chiOneWeightedSignalGradientSquare
      rw [show (fun x : ℝ =>
          (deriv (localizingWeightAt k x₀) x * r x +
              localizingWeightAt k x₀ x * rx x) * rx x) =
          (fun x : ℝ =>
            deriv (localizingWeightAt k x₀) x * r x * rx x) +
          (fun x : ℝ =>
            localizingWeightAt k x₀ x * (rx x) ^ 2) by
        funext x
        simp only [Pi.add_apply]
        ring]
      change -(∫ x : ℝ,
        deriv (localizingWeightAt k x₀) x * r x * rx x +
          localizingWeightAt k x₀ x * (rx x) ^ 2) = _
      rw [integral_add H.weightCross_integrable H.gradientSquare_integrable]

theorem ChiOneWeightedResolverData.testing_identity
    {k x₀ : ℝ} {w r rx rxx : ℝ → ℝ}
    (H : ChiOneWeightedResolverData k x₀ w r rx rxx) :
    chiOneWeightedSignalSquare k x₀ r +
        chiOneWeightedSignalGradientSquare k x₀ rx +
        chiOneWeightedResolverCross k x₀ r rx =
      chiOneWeightedSourceSignalPair k x₀ w r := by
  have hibp := H.signalSecond_ibp
  have hsource :
      chiOneWeightedSourceSignalPair k x₀ w r =
        chiOneWeightedSignalSquare k x₀ r -
          ∫ x : ℝ, (localizingWeightAt k x₀ x * r x) * rxx x := by
    unfold chiOneWeightedSourceSignalPair chiOneWeightedSignalSquare
    calc
      (∫ x : ℝ, localizingWeightAt k x₀ x * w x * r x) =
          ∫ x : ℝ,
            localizingWeightAt k x₀ x * (r x) ^ 2 -
              (localizingWeightAt k x₀ x * r x) * rxx x := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [← H.resolver x]
        ring
      _ = (∫ x : ℝ, localizingWeightAt k x₀ x * (r x) ^ 2) -
          ∫ x : ℝ,
            (localizingWeightAt k x₀ x * r x) * rxx x := by
        rw [integral_sub H.signalSquare_integrable H.ibp.left_integrable]
  rw [hsource, hibp]
  ring

theorem ChiOneWeightedResolverData.source_square_identity
    {k x₀ : ℝ} {w r rx rxx : ℝ → ℝ}
    (H : ChiOneWeightedResolverData k x₀ w r rx rxx) :
    chiOneWeightedSourceSquare k x₀ w =
      chiOneWeightedSignalSquare k x₀ r +
        2 * chiOneWeightedSignalGradientSquare k x₀ rx +
        2 * chiOneWeightedResolverCross k x₀ r rx +
        chiOneWeightedSignalSecondSquare k x₀ rxx := by
  have hibp := H.signalSecond_ibp
  unfold chiOneWeightedResolverCross
    chiOneWeightedSignalGradientSquare at hibp
  unfold chiOneWeightedSourceSquare chiOneWeightedSignalSquare
    chiOneWeightedSignalGradientSquare chiOneWeightedResolverCross
    chiOneWeightedSignalSecondSquare
  calc
    (∫ x : ℝ, localizingWeightAt k x₀ x * (w x) ^ 2) =
        ∫ x : ℝ,
          localizingWeightAt k x₀ x * (r x) ^ 2 +
            (-2) * ((localizingWeightAt k x₀ x * r x) * rxx x) +
            localizingWeightAt k x₀ x * (rxx x) ^ 2 := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← H.resolver x]
      ring
    _ = (∫ x : ℝ, localizingWeightAt k x₀ x * (r x) ^ 2) +
          (-2) * (∫ x : ℝ,
            (localizingWeightAt k x₀ x * r x) * rxx x) +
          (∫ x : ℝ, localizingWeightAt k x₀ x * (rxx x) ^ 2) := by
      calc
        (∫ x : ℝ,
            localizingWeightAt k x₀ x * (r x) ^ 2 +
              (-2) * ((localizingWeightAt k x₀ x * r x) * rxx x) +
              localizingWeightAt k x₀ x * (rxx x) ^ 2) =
            (∫ x : ℝ,
              localizingWeightAt k x₀ x * (r x) ^ 2 +
                (-2) * ((localizingWeightAt k x₀ x * r x) * rxx x)) +
              ∫ x : ℝ, localizingWeightAt k x₀ x * (rxx x) ^ 2 :=
          integral_add
            (H.signalSquare_integrable.add
              (H.ibp.left_integrable.const_mul (-2)))
            H.secondSquare_integrable
        _ = ((∫ x : ℝ, localizingWeightAt k x₀ x * (r x) ^ 2) +
              ∫ x : ℝ,
                (-2) * ((localizingWeightAt k x₀ x * r x) * rxx x)) +
              ∫ x : ℝ, localizingWeightAt k x₀ x * (rxx x) ^ 2 := by
          rw [integral_add H.signalSquare_integrable
            (H.ibp.left_integrable.const_mul (-2))]
        _ = (∫ x : ℝ, localizingWeightAt k x₀ x * (r x) ^ 2) +
              (-2) * (∫ x : ℝ,
                (localizingWeightAt k x₀ x * r x) * rxx x) +
              (∫ x : ℝ, localizingWeightAt k x₀ x * (rxx x) ^ 2) := by
          rw [integral_const_mul]
    _ = (∫ x : ℝ, localizingWeightAt k x₀ x * (r x) ^ 2) +
          2 * (∫ x : ℝ, localizingWeightAt k x₀ x * (rx x) ^ 2) +
          2 * (∫ x : ℝ,
            deriv (localizingWeightAt k x₀) x * r x * rx x) +
          (∫ x : ℝ, localizingWeightAt k x₀ x * (rxx x) ^ 2) := by
      rw [hibp]
      ring

theorem ChiOneWeightedResolverData.source_signal_young
    {k x₀ : ℝ} {w r rx rxx : ℝ → ℝ}
    (H : ChiOneWeightedResolverData k x₀ w r rx rxx) :
    2 * chiOneWeightedSourceSignalPair k x₀ w r ≤
      chiOneWeightedSourceSquare k x₀ w +
        chiOneWeightedSignalSquare k x₀ r := by
  unfold chiOneWeightedSourceSignalPair chiOneWeightedSourceSquare
    chiOneWeightedSignalSquare
  rw [← integral_const_mul]
  rw [← integral_add H.sourceSquare_integrable H.signalSquare_integrable]
  apply integral_mono
    (H.sourceSignal_integrable.const_mul 2)
    (H.sourceSquare_integrable.add H.signalSquare_integrable)
  intro x
  have hphi : 0 ≤ localizingWeightAt k x₀ x :=
    (localizingWeightAt_pos k x₀ x).le
  change 2 * (localizingWeightAt k x₀ x * w x * r x) ≤
    localizingWeightAt k x₀ x * (w x) ^ 2 +
      localizingWeightAt k x₀ x * (r x) ^ 2
  nlinarith [mul_nonneg hphi (sq_nonneg (w x - r x))]

theorem ChiOneWeightedResolverData.second_young
    {k x₀ : ℝ} {w r rx rxx : ℝ → ℝ}
    (H : ChiOneWeightedResolverData k x₀ w r rx rxx) :
    2 * chiOneWeightedSignalGradientSquare k x₀ rx +
        2 * chiOneWeightedResolverCross k x₀ r rx ≤
      chiOneWeightedSignalSquare k x₀ r +
        chiOneWeightedSignalSecondSquare k x₀ rxx := by
  have hibp := H.signalSecond_ibp
  have hyoung :
      (-2) * (∫ x : ℝ,
          (localizingWeightAt k x₀ x * r x) * rxx x) ≤
        (∫ x : ℝ, localizingWeightAt k x₀ x * (r x) ^ 2) +
          ∫ x : ℝ, localizingWeightAt k x₀ x * (rxx x) ^ 2 := by
    rw [← integral_const_mul]
    rw [← integral_add H.signalSquare_integrable H.secondSquare_integrable]
    apply integral_mono
      (H.ibp.left_integrable.const_mul (-2))
      (H.signalSquare_integrable.add H.secondSquare_integrable)
    intro x
    have hphi : 0 ≤ localizingWeightAt k x₀ x :=
      (localizingWeightAt_pos k x₀ x).le
    change (-2) * ((localizingWeightAt k x₀ x * r x) * rxx x) ≤
      localizingWeightAt k x₀ x * (r x) ^ 2 +
        localizingWeightAt k x₀ x * (rxx x) ^ 2
    nlinarith [mul_nonneg hphi (sq_nonneg (r x + rxx x))]
  unfold chiOneWeightedResolverCross
    chiOneWeightedSignalGradientSquare at hibp
  unfold chiOneWeightedSignalGradientSquare chiOneWeightedResolverCross
    chiOneWeightedSignalSquare chiOneWeightedSignalSecondSquare
  rw [hibp] at hyoung
  linarith

theorem ChiOneWeightedResolverData.weight_cross_bound
    {k x₀ : ℝ} {w r rx rxx : ℝ → ℝ}
    (H : ChiOneWeightedResolverData k x₀ w r rx rxx) :
    |chiOneWeightedResolverCross k x₀ r rx| ≤
      (k / 2) *
        (chiOneWeightedSignalSquare k x₀ r +
          chiOneWeightedSignalGradientSquare k x₀ rx) := by
  let j : ℝ → ℝ := fun x =>
    deriv (localizingWeightAt k x₀) x * r x * rx x
  let d : ℝ → ℝ := fun x =>
    (k / 2) *
      (localizingWeightAt k x₀ x * (r x) ^ 2 +
        localizingWeightAt k x₀ x * (rx x) ^ 2)
  have hjnorm : |∫ x : ℝ, j x| ≤ ∫ x : ℝ, |j x| := by
    simpa [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm (μ := volume) j)
  have hdint : Integrable d := by
    dsimp [d]
    exact (H.signalSquare_integrable.add H.gradientSquare_integrable).const_mul _
  have hpoint : ∀ x : ℝ, |j x| ≤ d x := by
    intro x
    dsimp [j, d]
    have hphi : 0 ≤ localizingWeightAt k x₀ x :=
      (localizingWeightAt_pos k x₀ x).le
    have hphix := abs_deriv_localizingWeightAt_le H.hk0 x₀ x
    have hry : |r x * rx x| ≤ ((r x) ^ 2 + (rx x) ^ 2) / 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|r x| - |rx x|), sq_abs (r x), sq_abs (rx x)]
    calc
      |deriv (localizingWeightAt k x₀) x * r x * rx x| =
          |deriv (localizingWeightAt k x₀) x| * |r x * rx x| := by
        simp only [abs_mul]
        ring
      _ ≤ (k * localizingWeightAt k x₀ x) * |r x * rx x| :=
        mul_le_mul_of_nonneg_right hphix (abs_nonneg _)
      _ ≤ (k * localizingWeightAt k x₀ x) *
          (((r x) ^ 2 + (rx x) ^ 2) / 2) := by
        exact mul_le_mul_of_nonneg_left hry (mul_nonneg H.hk0 hphi)
      _ = (k / 2) *
          (localizingWeightAt k x₀ x * (r x) ^ 2 +
            localizingWeightAt k x₀ x * (rx x) ^ 2) := by ring
  have hmono : (∫ x : ℝ, |j x|) ≤ ∫ x : ℝ, d x :=
    integral_mono H.weightCross_integrable.abs hdint hpoint
  unfold chiOneWeightedResolverCross chiOneWeightedSignalSquare
    chiOneWeightedSignalGradientSquare
  change |∫ x : ℝ, j x| ≤ _
  calc
    |∫ x : ℝ, j x| ≤ ∫ x : ℝ, |j x| := hjnorm
    _ ≤ ∫ x : ℝ, d x := hmono
    _ = (k / 2) *
        ((∫ x : ℝ, localizingWeightAt k x₀ x * (r x) ^ 2) +
          ∫ x : ℝ, localizingWeightAt k x₀ x * (rx x) ^ 2) := by
      dsimp [d]
      rw [integral_const_mul]
      rw [integral_add H.signalSquare_integrable H.gradientSquare_integrable]

theorem ChiOneWeightedResolverData.sourceSquare_nonneg
    {k x₀ : ℝ} {w r rx rxx : ℝ → ℝ}
    (H : ChiOneWeightedResolverData k x₀ w r rx rxx) :
    0 ≤ chiOneWeightedSourceSquare k x₀ w := by
  unfold chiOneWeightedSourceSquare
  exact integral_nonneg fun x =>
    mul_nonneg (localizingWeightAt_pos k x₀ x).le (sq_nonneg _)

theorem ChiOneWeightedResolverData.signalSquare_nonneg
    {k x₀ : ℝ} {w r rx rxx : ℝ → ℝ}
    (H : ChiOneWeightedResolverData k x₀ w r rx rxx) :
    0 ≤ chiOneWeightedSignalSquare k x₀ r := by
  unfold chiOneWeightedSignalSquare
  exact integral_nonneg fun x =>
    mul_nonneg (localizingWeightAt_pos k x₀ x).le (sq_nonneg _)

theorem ChiOneWeightedResolverData.gradientSquare_nonneg
    {k x₀ : ℝ} {w r rx rxx : ℝ → ℝ}
    (H : ChiOneWeightedResolverData k x₀ w r rx rxx) :
    0 ≤ chiOneWeightedSignalGradientSquare k x₀ rx := by
  unfold chiOneWeightedSignalGradientSquare
  exact integral_nonneg fun x =>
    mul_nonneg (localizingWeightAt_pos k x₀ x).le (sq_nonneg _)

theorem ChiOneWeightedResolverData.secondSquare_nonneg
    {k x₀ : ℝ} {w r rx rxx : ℝ → ℝ}
    (H : ChiOneWeightedResolverData k x₀ w r rx rxx) :
    0 ≤ chiOneWeightedSignalSecondSquare k x₀ rxx := by
  unfold chiOneWeightedSignalSecondSquare
  exact integral_nonneg fun x =>
    mul_nonneg (localizingWeightAt_pos k x₀ x).le (sq_nonneg _)

/-- Concrete whole-line near-sharp weighted resolver estimate. -/
theorem ChiOneWeightedResolverData.gradient_estimate
    {k x₀ : ℝ} {w r rx rxx : ℝ → ℝ}
    (H : ChiOneWeightedResolverData k x₀ w r rx rxx)
    (hk1 : k < 1) :
    chiOneWeightedSignalGradientSquare k x₀ rx ≤
      weightedResolverNearSharpGain k *
        chiOneWeightedSourceSquare k x₀ w := by
  exact weighted_resolver_near_sharp_of_testing H.hk0 hk1
    H.sourceSquare_nonneg H.signalSquare_nonneg H.gradientSquare_nonneg
    H.secondSquare_nonneg H.testing_identity H.source_signal_young
    H.weight_cross_bound H.source_square_identity H.second_young

section AxiomAudit

#print axioms ChiOneWeightedResolverData.signalSecond_ibp
#print axioms ChiOneWeightedResolverData.testing_identity
#print axioms ChiOneWeightedResolverData.source_square_identity
#print axioms ChiOneWeightedResolverData.weight_cross_bound
#print axioms ChiOneWeightedResolverData.gradient_estimate

end AxiomAudit

end ShenWork.Paper1
