import ShenWork.PaperOne.WholeLineChemotaxisCrossControl
import ShenWork.PaperOne.WholeLineDiffusionIBPDecay
import ShenWork.PaperOne.WholeLineEnergyTimeLeibnizPDE

open Filter MeasureTheory
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

/-!
This file isolates the whole-line weak parabolic comparison energy core.

The new analytic wrinkle is the positive-part profile `q_+`.  The spatial
chain-rule/weak-derivative input for `q_+` is not hidden: it appears in
`WholeLineWeakParabolicDiffusionIBPData.profile_deriv`,
`WholeLineWeakParabolicDiffusionIBPData.flux_deriv`, and
`WholeLineWeakParabolicComparisonData.qx_eq_flux_on_pos`.
-/

/-- Positive part of a whole-line time slice. -/
def wholeLineQPositivePart (q : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  max (q t x) 0

/-- Half-energy of the positive part: `1/2 ∫ (q_+)^2`. -/
def wholeLineWeakParabolicEnergy (q : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  wholeLineHalfEnergy (wholeLineQPositivePart q) t

/-- Weighted time term `∫ q_+ q_t`. -/
def wholeLineWeakParabolicTimeTerm
    (q qt : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  wholeLineWeightedTimeTerm (wholeLineQPositivePart q) qt t

/-- Diffusion term `∫ q_+ q_xx`. -/
def wholeLineWeakParabolicDiffusionTerm
    (q qxx : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℝ, wholeLineQPositivePart q t x * qxx t x

/-- First-order drift term, still written with the supplied `q_x`. -/
def wholeLineWeakParabolicDriftTerm
    (q a qx : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℝ, wholeLineQPositivePart q t x * (a t x * qx t x)

/-- First-order drift term after replacing `q_x` by `(q_+)_x`. -/
def wholeLineWeakParabolicFluxDriftTerm
    (q a flux : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℝ, wholeLineQPositivePart q t x * (a t x * flux t x)

/-- Zeroth-order term `∫ b (q_+)^2`. -/
def wholeLineWeakParabolicReactionTerm
    (q b : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℝ, b t x * (wholeLineQPositivePart q t x) ^ 2

/-- Pointwise nonnegativity of `q_+`. -/
theorem wholeLineQPositivePart_nonneg
    (q : ℝ → ℝ → ℝ) (t x : ℝ) :
    0 ≤ wholeLineQPositivePart q t x := by
  exact le_max_right _ _

/-- The positive-part half-energy is nonnegative. -/
theorem wholeLineWeakParabolicEnergy_nonneg
    (q : ℝ → ℝ → ℝ) (t : ℝ) :
    0 ≤ wholeLineWeakParabolicEnergy q t := by
  unfold wholeLineWeakParabolicEnergy wholeLineHalfEnergy
  exact integral_nonneg fun x =>
    mul_nonneg (by norm_num) (sq_nonneg (wholeLineQPositivePart q t x))

/-- Integrating a pointwise weighted weak parabolic inequality. -/
structure WholeLineWeakParabolicPDEIntegralData
    (q qt qx qxx a b : ℝ → ℝ → ℝ) (T : ℝ) where
  time_int : ∀ t, 0 < t → t < T →
    Integrable (fun x : ℝ => wholeLineQPositivePart q t x * qt t x) volume
  diffusion_int : ∀ t, 0 < t → t < T →
    Integrable (fun x : ℝ => wholeLineQPositivePart q t x * qxx t x) volume
  drift_int : ∀ t, 0 < t → t < T →
    Integrable
      (fun x : ℝ => wholeLineQPositivePart q t x * (a t x * qx t x))
      volume
  reaction_int : ∀ t, 0 < t → t < T →
    Integrable
      (fun x : ℝ => b t x * (wholeLineQPositivePart q t x) ^ 2)
      volume
  weighted_ineq : ∀ t, 0 < t → t < T →
    ∀ᵐ x ∂volume,
      wholeLineQPositivePart q t x * qt t x ≤
        wholeLineQPositivePart q t x * qxx t x
          + wholeLineQPositivePart q t x * (a t x * qx t x)
          + b t x * (wholeLineQPositivePart q t x) ^ 2

/-- The integrated form of the weighted PDE inequality. -/
theorem wholeLineWeakParabolic_weightedPDEIneq_of_data
    {q qt qx qxx a b : ℝ → ℝ → ℝ} {T : ℝ}
    (H : WholeLineWeakParabolicPDEIntegralData q qt qx qxx a b T) :
    ∀ t, 0 < t → t < T →
      wholeLineWeakParabolicTimeTerm q qt t ≤
        wholeLineWeakParabolicDiffusionTerm q qxx t
          + wholeLineWeakParabolicDriftTerm q a qx t
          + wholeLineWeakParabolicReactionTerm q b t := by
  intro t ht0 htT
  let A : ℝ → ℝ := fun x => wholeLineQPositivePart q t x * qxx t x
  let B : ℝ → ℝ := fun x => wholeLineQPositivePart q t x * (a t x * qx t x)
  let C : ℝ → ℝ := fun x => b t x * (wholeLineQPositivePart q t x) ^ 2
  have hABC : Integrable (fun x : ℝ => A x + B x + C x) volume :=
    ((H.diffusion_int t ht0 htT).add (H.drift_int t ht0 htT)).add
      (H.reaction_int t ht0 htT)
  have hmono :
      (∫ x : ℝ, wholeLineQPositivePart q t x * qt t x) ≤
        ∫ x : ℝ, A x + B x + C x :=
    integral_mono_ae (H.time_int t ht0 htT) hABC
      (by simpa [A, B, C] using H.weighted_ineq t ht0 htT)
  calc
    wholeLineWeakParabolicTimeTerm q qt t
        = ∫ x : ℝ, wholeLineQPositivePart q t x * qt t x := by
          rfl
    _ ≤ ∫ x : ℝ, A x + B x + C x := hmono
    _ = wholeLineWeakParabolicDiffusionTerm q qxx t
          + wholeLineWeakParabolicDriftTerm q a qx t
          + wholeLineWeakParabolicReactionTerm q b t := by
          have hA_int : Integrable A volume := by
            simpa [A] using H.diffusion_int t ht0 htT
          have hB_int : Integrable B volume := by
            simpa [B] using H.drift_int t ht0 htT
          have hC_int : Integrable C volume := by
            simpa [C] using H.reaction_int t ht0 htT
          calc
            (∫ x : ℝ, A x + B x + C x)
                = (∫ x : ℝ, A x + B x) + ∫ x : ℝ, C x := by
                  exact integral_add (hA_int.add hB_int) hC_int
            _ = ((∫ x : ℝ, A x) + ∫ x : ℝ, B x) + ∫ x : ℝ, C x := by
                  rw [integral_add hA_int hB_int]
            _ = wholeLineWeakParabolicDiffusionTerm q qxx t
                  + wholeLineWeakParabolicDriftTerm q a qx t
                  + wholeLineWeakParabolicReactionTerm q b t := by
                  rfl

/-- Time-Leibniz data for the positive-part half-energy. -/
structure WholeLineWeakParabolicTimeLeibnizData
    (q qt : ℝ → ℝ → ℝ) (T : ℝ) where
  δ : ℝ → ℝ
  bound : ℝ → ℝ → ℝ
  δ_pos : ∀ t, 0 < t → t < T → 0 < δ t
  F_meas : ∀ t, 0 < t → t < T →
    ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable
        (wholeLineHalfEnergyIntegrand (wholeLineQPositivePart q) s) volume
  F_int : ∀ t, 0 < t → t < T →
    Integrable
      (wholeLineHalfEnergyIntegrand (wholeLineQPositivePart q) t) volume
  F_deriv_meas : ∀ t, 0 < t → t < T →
    AEStronglyMeasurable
      (wholeLineHalfEnergyIntegrandDeriv (wholeLineQPositivePart q) qt t)
      volume
  deriv_bound : ∀ t, 0 < t → t < T →
    ∀ᵐ x ∂volume,
      ∀ s ∈ Metric.ball t (δ t),
        ‖wholeLineHalfEnergyIntegrandDeriv
          (wholeLineQPositivePart q) qt s x‖ ≤ bound t x
  bound_int : ∀ t, 0 < t → t < T → Integrable (bound t) volume
  positivePart_hasDeriv_time : ∀ t, 0 < t → t < T →
    ∀ᵐ x ∂volume,
      ∀ s ∈ Metric.ball t (δ t),
        HasDerivAt
          (fun r : ℝ => wholeLineQPositivePart q r x) (qt s x) s

/-- The positive-part half-energy time derivative, from the banked atom. -/
theorem wholeLineWeakParabolic_timeLeibniz_field_of_data
    {q qt : ℝ → ℝ → ℝ} {T : ℝ}
    (H : WholeLineWeakParabolicTimeLeibnizData q qt T) :
    ∀ t, 0 < t → t < T →
      HasDerivWithinAt (wholeLineWeakParabolicEnergy q)
        (wholeLineWeakParabolicTimeTerm q qt t) (Set.Ici t) t := by
  intro t ht0 htT
  exact
    (wholeLine_halfEnergy_hasDerivAt_of_dominated
      (phi := wholeLineQPositivePart q) (phi_t := qt)
      (t := t) (δ := H.δ t) (bound := H.bound t)
      (H.δ_pos t ht0 htT) (H.F_meas t ht0 htT)
      (H.F_int t ht0 htT) (H.F_deriv_meas t ht0 htT)
      (H.deriv_bound t ht0 htT) (H.bound_int t ht0 htT)
      (H.positivePart_hasDeriv_time t ht0 htT)).hasDerivWithinAt

/-- Spatial IBP data for `q_+`.

`flux t` is the intended weak derivative `(q_+)_x`, i.e.
`q_x · 1_{q>0}` a.e.; this is the positive-part chain-rule input. -/
structure WholeLineWeakParabolicDiffusionIBPData
    (q qxx : ℝ → ℝ → ℝ) (T : ℝ) where
  flux : ℝ → ℝ → ℝ
  profile_deriv : ∀ t, 0 < t → t < T →
    ∀ x ∈ tsupport (flux t),
      HasDerivAt (wholeLineQPositivePart q t) (flux t x) x
  flux_deriv : ∀ t, 0 < t → t < T →
    ∀ x ∈ tsupport (wholeLineQPositivePart q t),
      HasDerivAt (flux t) (qxx t x) x
  lhs_int : ∀ t, 0 < t → t < T →
    Integrable (fun x : ℝ => wholeLineQPositivePart q t x * qxx t x) volume
  energy_int : ∀ t, 0 < t → t < T →
    Integrable (fun x : ℝ => flux t x * flux t x) volume
  decay_bot : ∀ t, 0 < t → t < T →
    Tendsto (fun x : ℝ => wholeLineQPositivePart q t x * flux t x)
      atBot (𝓝 0)
  decay_top : ∀ t, 0 < t → t < T →
    Tendsto (fun x : ℝ => wholeLineQPositivePart q t x * flux t x)
      atTop (𝓝 0)

/-- Banked whole-line IBP, specialized to the positive part. -/
theorem wholeLineWeakParabolic_diffusionIBP_eq_neg_dissipation
    {q qxx : ℝ → ℝ → ℝ} {T : ℝ}
    (H : WholeLineWeakParabolicDiffusionIBPData q qxx T) :
    ∀ t, 0 < t → t < T →
      wholeLineWeakParabolicDiffusionTerm q qxx t =
        -wholeLineGradientDissipation (H.flux t) := by
  intro t ht0 htT
  have hIBP :=
    wholeLine_diffusion_ibp_decay_with_derivatives
      (wholeLineQPositivePart q t) (H.flux t) (qxx t)
      (H.profile_deriv t ht0 htT) (H.flux_deriv t ht0 htT)
      (H.lhs_int t ht0 htT) (H.energy_int t ht0 htT)
      (H.decay_bot t ht0 htT) (H.decay_top t ht0 htT)
  simpa [wholeLineWeakParabolicDiffusionTerm, wholeLineGradientDissipation]
    using hIBP

/-- Replace the drift `q_x` by `(q_+)_x` under the positive-part weight. -/
theorem wholeLineWeakParabolic_driftTerm_eq_fluxDriftTerm
    {q qx a flux : ℝ → ℝ → ℝ} {t : ℝ}
    (hqx_flux : ∀ x, 0 < q t x → qx t x = flux t x) :
    wholeLineWeakParabolicDriftTerm q a qx t =
      wholeLineWeakParabolicFluxDriftTerm q a flux t := by
  unfold wholeLineWeakParabolicDriftTerm wholeLineWeakParabolicFluxDriftTerm
  refine integral_congr_ae (Eventually.of_forall ?_)
  intro x
  by_cases hx : 0 < q t x
  · change wholeLineQPositivePart q t x * (a t x * qx t x) =
      wholeLineQPositivePart q t x * (a t x * flux t x)
    rw [hqx_flux x hx]
  · have hzero : wholeLineQPositivePart q t x = 0 := by
      unfold wholeLineQPositivePart
      exact max_eq_right (not_lt.mp hx)
    simp [hzero]

private theorem wholeLineWeakParabolic_drift_young_pointwise
    {A a φ φx : ℝ}
    (hφ_nonneg : 0 ≤ φ) (ha : |a| ≤ A) :
    φ * (a * φx) ≤
      (1 / 2 : ℝ) * (φx * φx) + (A ^ 2 / 2) * φ ^ 2 := by
  have hleft_abs : φ * (a * φx) ≤ |φ * (a * φx)| := le_abs_self _
  have habs_eval :
      |φ * (a * φx)| = φ * |a| * |φx| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hφ_nonneg]
    ring
  have habs_le : φ * |a| * |φx| ≤ φ * A * |φx| := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left ha hφ_nonneg) (abs_nonneg φx)
  have hyoung :
      φ * A * |φx| ≤
        (1 / 2 : ℝ) * (φx * φx) + (A ^ 2 / 2) * φ ^ 2 := by
    have hs : 0 ≤ (|φx| - A * φ) ^ 2 := sq_nonneg _
    have hφx_sq : |φx| ^ 2 = φx * φx := by
      rw [sq_abs, pow_two]
    nlinarith
  exact le_trans hleft_abs (by
    rw [habs_eval]
    exact le_trans habs_le hyoung)

/-- Young absorption of the first-order drift term. -/
theorem wholeLineWeakParabolic_drift_young
    {q a flux : ℝ → ℝ → ℝ} {A t : ℝ}
    (ha_bound : ∀ x, |a t x| ≤ A)
    (hpos_sq_int :
      Integrable (fun x : ℝ => (wholeLineQPositivePart q t x) ^ 2) volume)
    (hflux_sq_int :
      Integrable (fun x : ℝ => flux t x * flux t x) volume)
    (hcross_int :
      Integrable
        (fun x : ℝ => wholeLineQPositivePart q t x * (a t x * flux t x))
        volume) :
    wholeLineWeakParabolicFluxDriftTerm q a flux t ≤
      (1 / 2 : ℝ) * wholeLineGradientDissipation (flux t)
        + A ^ 2 * wholeLineWeakParabolicEnergy q t := by
  have hright_int : Integrable
      (fun x : ℝ =>
        (1 / 2 : ℝ) * (flux t x * flux t x)
          + (A ^ 2 / 2) * (wholeLineQPositivePart q t x) ^ 2) volume :=
    (hflux_sq_int.const_mul _).add (hpos_sq_int.const_mul _)
  have hmono :
      (∫ x : ℝ, wholeLineQPositivePart q t x * (a t x * flux t x)) ≤
        ∫ x : ℝ,
          (1 / 2 : ℝ) * (flux t x * flux t x)
            + (A ^ 2 / 2) * (wholeLineQPositivePart q t x) ^ 2 :=
    integral_mono hcross_int hright_int
      (fun x =>
        wholeLineWeakParabolic_drift_young_pointwise
          (A := A) (a := a t x) (φ := wholeLineQPositivePart q t x)
          (φx := flux t x)
          (wholeLineQPositivePart_nonneg q t x) (ha_bound x))
  calc
    wholeLineWeakParabolicFluxDriftTerm q a flux t
        ≤ ∫ x : ℝ,
          (1 / 2 : ℝ) * (flux t x * flux t x)
            + (A ^ 2 / 2) * (wholeLineQPositivePart q t x) ^ 2 := hmono
    _ = (1 / 2 : ℝ) * wholeLineGradientDissipation (flux t)
          + A ^ 2 * wholeLineWeakParabolicEnergy q t := by
          rw [integral_add (hflux_sq_int.const_mul _)
            (hpos_sq_int.const_mul _)]
          rw [integral_const_mul, integral_const_mul]
          unfold wholeLineGradientDissipation wholeLineWeakParabolicEnergy
            wholeLineHalfEnergy
          rw [integral_const_mul]
          ring

/-- The bounded zeroth-order term is controlled by the positive-part energy. -/
theorem wholeLineWeakParabolic_reaction_control
    {q b : ℝ → ℝ → ℝ} {Bb t : ℝ}
    (hb_bound : ∀ x, |b t x| ≤ Bb)
    (hpos_sq_int :
      Integrable (fun x : ℝ => (wholeLineQPositivePart q t x) ^ 2) volume)
    (hreaction_int :
      Integrable
        (fun x : ℝ => b t x * (wholeLineQPositivePart q t x) ^ 2)
        volume) :
    wholeLineWeakParabolicReactionTerm q b t ≤
      2 * Bb * wholeLineWeakParabolicEnergy q t := by
  have hright_int : Integrable
      (fun x : ℝ => Bb * (wholeLineQPositivePart q t x) ^ 2) volume :=
    hpos_sq_int.const_mul _
  have hmono :
      (∫ x : ℝ, b t x * (wholeLineQPositivePart q t x) ^ 2) ≤
        ∫ x : ℝ, Bb * (wholeLineQPositivePart q t x) ^ 2 :=
    integral_mono hreaction_int hright_int
      (fun x => by
        have hb_le : b t x ≤ Bb := le_trans (le_abs_self _) (hb_bound x)
        exact mul_le_mul_of_nonneg_right hb_le
          (sq_nonneg (wholeLineQPositivePart q t x)))
  calc
    wholeLineWeakParabolicReactionTerm q b t
        ≤ ∫ x : ℝ, Bb * (wholeLineQPositivePart q t x) ^ 2 := hmono
    _ = 2 * Bb * wholeLineWeakParabolicEnergy q t := by
          rw [integral_const_mul]
          unfold wholeLineWeakParabolicEnergy wholeLineHalfEnergy
          rw [integral_const_mul]
          ring

/-- All named analytic inputs needed by the weak comparison energy method. -/
structure WholeLineWeakParabolicComparisonData
    (q qt qx qxx a b : ℝ → ℝ → ℝ) (T A Bb : ℝ) where
  A_nonneg : 0 ≤ A
  Bb_nonneg : 0 ≤ Bb
  a_bound : ∀ t, 0 < t → t < T → ∀ x, |a t x| ≤ A
  b_bound : ∀ t, 0 < t → t < T → ∀ x, |b t x| ≤ Bb
  cont : ∀ s t, 0 < s → s ≤ t → t < T →
    ContinuousOn (wholeLineWeakParabolicEnergy q) (Set.Icc s t)
  endpoint_cont : ∀ s, 0 < s → s ≤ T →
    ContinuousOn (wholeLineWeakParabolicEnergy q) (Set.Icc s T)
  initial_vanishes : ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → s < T →
    wholeLineWeakParabolicEnergy q s < ε
  timeLeibniz : WholeLineWeakParabolicTimeLeibnizData q qt T
  pde : WholeLineWeakParabolicPDEIntegralData q qt qx qxx a b T
  diffusion : WholeLineWeakParabolicDiffusionIBPData q qxx T
  positivePart_sq_int : ∀ t, 0 < t → t < T →
    Integrable (fun x : ℝ => (wholeLineQPositivePart q t x) ^ 2) volume
  flux_drift_int : ∀ t, 0 < t → t < T →
    Integrable
      (fun x : ℝ =>
        wholeLineQPositivePart q t x * (a t x * diffusion.flux t x))
      volume
  qx_eq_flux_on_pos : ∀ t, 0 < t → t < T →
    ∀ x, 0 < q t x → qx t x = diffusion.flux t x
  energy_zero_controls : ∀ t, 0 < t → t ≤ T →
    wholeLineWeakParabolicEnergy q t = 0 → ∀ x, q t x ≤ 0

/-- The differential energy inequality
`F' ≤ (A^2 + 2Bb) F` for `F = 1/2 ∫ (q_+)^2`. -/
theorem wholeLineWeakParabolic_energy_differential_ineq
    {q qt qx qxx a b : ℝ → ℝ → ℝ} {T A Bb : ℝ}
    (H : WholeLineWeakParabolicComparisonData q qt qx qxx a b T A Bb) :
    ∀ t, 0 < t → t < T →
      wholeLineWeakParabolicTimeTerm q qt t ≤
        (A ^ 2 + 2 * Bb) * wholeLineWeakParabolicEnergy q t := by
  intro t ht0 htT
  let D : ℝ := wholeLineGradientDissipation (H.diffusion.flux t)
  let E : ℝ := wholeLineWeakParabolicEnergy q t
  have hpde :=
    wholeLineWeakParabolic_weightedPDEIneq_of_data H.pde t ht0 htT
  have hdiff :=
    wholeLineWeakParabolic_diffusionIBP_eq_neg_dissipation
      H.diffusion t ht0 htT
  have hdrift_eq :=
    wholeLineWeakParabolic_driftTerm_eq_fluxDriftTerm
      (q := q) (qx := qx) (a := a) (flux := H.diffusion.flux) (t := t)
      (H.qx_eq_flux_on_pos t ht0 htT)
  have hdrift :=
    wholeLineWeakParabolic_drift_young
      (q := q) (a := a) (flux := H.diffusion.flux) (A := A) (t := t)
      (H.a_bound t ht0 htT)
      (H.positivePart_sq_int t ht0 htT)
      (H.diffusion.energy_int t ht0 htT)
      (H.flux_drift_int t ht0 htT)
  have hreact :=
    wholeLineWeakParabolic_reaction_control
      (q := q) (b := b) (Bb := Bb) (t := t)
      (H.b_bound t ht0 htT)
      (H.positivePart_sq_int t ht0 htT)
      (H.pde.reaction_int t ht0 htT)
  have hrewrite :
      wholeLineWeakParabolicDiffusionTerm q qxx t
          + wholeLineWeakParabolicDriftTerm q a qx t
          + wholeLineWeakParabolicReactionTerm q b t
        =
        -D + wholeLineWeakParabolicFluxDriftTerm q a H.diffusion.flux t
          + wholeLineWeakParabolicReactionTerm q b t := by
    rw [hdiff, hdrift_eq]
  have hstep :
      wholeLineWeakParabolicTimeTerm q qt t ≤
        -D + wholeLineWeakParabolicFluxDriftTerm q a H.diffusion.flux t
          + wholeLineWeakParabolicReactionTerm q b t := by
    exact le_trans hpde (le_of_eq hrewrite)
  have hcontrol :
      -D + wholeLineWeakParabolicFluxDriftTerm q a H.diffusion.flux t
          + wholeLineWeakParabolicReactionTerm q b t
        ≤ -D + ((1 / 2 : ℝ) * D + A ^ 2 * E) + 2 * Bb * E := by
    have hdrift' :
        wholeLineWeakParabolicFluxDriftTerm q a H.diffusion.flux t ≤
          (1 / 2 : ℝ) * D + A ^ 2 * E := by
      simpa [D, E] using hdrift
    have hreact' :
        wholeLineWeakParabolicReactionTerm q b t ≤ 2 * Bb * E := by
      simpa [E, mul_assoc] using hreact
    linarith
  have hD_nonneg : 0 ≤ D := by
    unfold D wholeLineGradientDissipation
    exact integral_nonneg fun x => mul_self_nonneg (H.diffusion.flux t x)
  have htail :
      -D + ((1 / 2 : ℝ) * D + A ^ 2 * E) + 2 * Bb * E
        ≤ (A ^ 2 + 2 * Bb) * E := by
    have hlinear :
        -D + ((1 / 2 : ℝ) * D + A ^ 2 * E) + 2 * Bb * E
          ≤ A ^ 2 * E + 2 * Bb * E := by
      nlinarith [hD_nonneg]
    have hfactor :
        A ^ 2 * E + 2 * Bb * E = (A ^ 2 + 2 * Bb) * E := by
      ring
    exact le_trans hlinear (le_of_eq hfactor)
  exact le_trans hstep (le_trans hcontrol htail)

/-- Build the banked Grönwall frontier for the positive-part energy. -/
def wholeLineWeakParabolicEnergyFrontierOfData
    {q qt qx qxx a b : ℝ → ℝ → ℝ} {T A Bb : ℝ}
    (H : WholeLineWeakParabolicComparisonData q qt qx qxx a b T A Bb) :
    WholeLineBarrierEnergyFrontier (wholeLineWeakParabolicEnergy q) T where
  Eprime := fun t => wholeLineWeakParabolicTimeTerm q qt t
  K := A ^ 2 + 2 * Bb
  K_nonneg := by
    exact add_nonneg (sq_nonneg A) (mul_nonneg (by norm_num) H.Bb_nonneg)
  nonneg := fun t _ _ => wholeLineWeakParabolicEnergy_nonneg q t
  cont := H.cont
  initial_vanishes := H.initial_vanishes
  diffIneq := by
    intro t ht0 htT
    exact
      ⟨wholeLineWeakParabolic_timeLeibniz_field_of_data H.timeLeibniz t ht0 htT,
        wholeLineWeakParabolic_energy_differential_ineq H t ht0 htT⟩

/-- Energy vanishing for the positive part on the open time horizon. -/
theorem wholeLineWeakParabolicEnergy_eq_zero
    {q qt qx qxx a b : ℝ → ℝ → ℝ} {T A Bb t : ℝ}
    (H : WholeLineWeakParabolicComparisonData q qt qx qxx a b T A Bb)
    (ht0 : 0 < t) (htT : t < T) :
    wholeLineWeakParabolicEnergy q t = 0 := by
  exact wholeLineBarrierEnergy_eq_zero
    (wholeLineWeakParabolicEnergyFrontierOfData H) ht0 htT

/-- Energy vanishing at the closed endpoint `T`, using endpoint continuity and
the same Grönwall argument as the banked frontier. -/
theorem wholeLineWeakParabolicEnergy_eq_zero_at_endpoint
    {q qt qx qxx a b : ℝ → ℝ → ℝ} {T A Bb : ℝ}
    (H : WholeLineWeakParabolicComparisonData q qt qx qxx a b T A Bb)
    (hT0 : 0 < T) :
    wholeLineWeakParabolicEnergy q T = 0 := by
  let F : ℝ → ℝ := wholeLineWeakParabolicEnergy q
  let Hfront : WholeLineBarrierEnergyFrontier F T :=
    wholeLineWeakParabolicEnergyFrontierOfData H
  have hET_nonneg : 0 ≤ F T := wholeLineWeakParabolicEnergy_nonneg q T
  by_cases hET_zero : F T = 0
  · exact hET_zero
  have hET_pos : 0 < F T := lt_of_le_of_ne hET_nonneg (Ne.symm hET_zero)
  have hExp_pos : 0 < Real.exp (Hfront.K * T) := Real.exp_pos _
  set ε : ℝ := F T / (2 * Real.exp (Hfront.K * T)) with hε
  have hε_pos : 0 < ε := div_pos hET_pos (mul_pos (by norm_num) hExp_pos)
  obtain ⟨δ, hδ_pos, hδ⟩ := H.initial_vanishes ε hε_pos
  set s : ℝ := min (δ / 2) (T / 2) with hs
  have hs_pos : 0 < s := lt_min (by linarith) (by linarith)
  have hs_lt_δ : s < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hs_lt_T : s < T := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hs_le_T : s ≤ T := le_of_lt hs_lt_T
  have hEs_nonneg : 0 ≤ F s := wholeLineWeakParabolicEnergy_nonneg q s
  have hEs_lt : F s < ε := hδ s hs_pos hs_lt_δ hs_lt_T
  have hET_le : F T ≤ F s * Real.exp (Hfront.K * (T - s)) := by
    refine ShenWork.Paper2.intervalDomainL2_gronwall_exp_of_diffIneq
      (E' := Hfront.Eprime) hs_le_T (H.endpoint_cont s hs_pos hs_le_T) ?_ ?_
    · intro τ hτ
      exact (Hfront.diffIneq τ (lt_of_lt_of_le hs_pos hτ.1) hτ.2).1
    · intro τ hτ
      exact (Hfront.diffIneq τ (lt_of_lt_of_le hs_pos hτ.1) hτ.2).2
  have hExp_le : Real.exp (Hfront.K * (T - s)) ≤ Real.exp (Hfront.K * T) := by
    exact Real.exp_le_exp.mpr (by nlinarith [Hfront.K_nonneg, hs_pos])
  have hET_le' : F T ≤ F s * Real.exp (Hfront.K * T) :=
    le_trans hET_le (mul_le_mul_of_nonneg_left hExp_le hEs_nonneg)
  have hmul_lt : F s * Real.exp (Hfront.K * T) <
      ε * Real.exp (Hfront.K * T) :=
    mul_lt_mul_of_pos_right hEs_lt hExp_pos
  have hε_mul : ε * Real.exp (Hfront.K * T) = F T / 2 := by
    rw [hε]
    field_simp [ne_of_gt hExp_pos]
  linarith

/-- Energy vanishing on the closed time horizon. -/
theorem wholeLineWeakParabolicEnergy_eq_zero_of_le
    {q qt qx qxx a b : ℝ → ℝ → ℝ} {T A Bb t : ℝ}
    (H : WholeLineWeakParabolicComparisonData q qt qx qxx a b T A Bb)
    (ht0 : 0 < t) (htT : t ≤ T) :
    wholeLineWeakParabolicEnergy q t = 0 := by
  by_cases hlt : t < T
  · exact wholeLineWeakParabolicEnergy_eq_zero H ht0 hlt
  · have hT_le_t : T ≤ t := le_of_not_gt hlt
    have ht_eq : t = T := le_antisymm htT hT_le_t
    subst ht_eq
    exact wholeLineWeakParabolicEnergy_eq_zero_at_endpoint H ht0

/-- Differentiated weak parabolic comparison on the whole line.

The endpoint `T` is closed by `endpoint_cont`, with no terminal sign hypothesis. -/
theorem wholeLine_weak_parabolic_comparison
    {q qt qx qxx a b : ℝ → ℝ → ℝ} {T A Bb : ℝ}
    (hinitial : ∀ x, q 0 x ≤ 0)
    (H : WholeLineWeakParabolicComparisonData q qt qx qxx a b T A Bb) :
    ∀ t, 0 ≤ t → t ≤ T → ∀ x, q t x ≤ 0 := by
  intro t ht0 htT x
  by_cases htz : t = 0
  · simpa [htz] using hinitial x
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htz)
    exact H.energy_zero_controls t htpos htT
      (wholeLineWeakParabolicEnergy_eq_zero_of_le H htpos htT) x

#print axioms wholeLineWeakParabolic_drift_young
#print axioms wholeLineWeakParabolic_reaction_control
#print axioms wholeLineWeakParabolic_energy_differential_ineq
#print axioms wholeLineWeakParabolicEnergy_eq_zero
#print axioms wholeLineWeakParabolicEnergy_eq_zero_at_endpoint
#print axioms wholeLineWeakParabolicEnergy_eq_zero_of_le
#print axioms wholeLine_weak_parabolic_comparison

end ShenWork.PaperOne
