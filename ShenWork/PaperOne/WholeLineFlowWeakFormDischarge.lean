import ShenWork.PaperOne.WholeLineWeakStationaryLimit
import ShenWork.PaperOne.WholeLineAuxiliaryClassical
import Mathlib.Tactic

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

/-!
Discharge wrappers for the three named weak-limit inputs in
`WholeLineWeakStationaryLimit`.

The existing weak-test structure only records compact support by radius; it
does not store smoothness, measurability, or integrability.  This file therefore
keeps the missing analytic payloads explicit and proves the named inputs from
those payloads without adding axioms.
-/

/-- Time-window integrand used by the weak-limit DCT package. -/
def wholeLineTimeWindowWeakIntegrand
    (p : CMParams) (c : ℝ) (w : ℝ → ℝ → ℝ) (_τ : ℝ)
    (Φ : WholeLineWeakTestFunction) (n : ℕ) (s : ℝ) : ℝ :=
  ∫ x : ℝ,
    wholeLineDivergenceWeakIntegrand p c
      (fun y => w ((n : ℝ) + s) y) Φ x

/--
The analytic data needed to pass from a classical auxiliary solution to the
weak flow identity.

`time_ftc` is the time fundamental theorem pairing against `Φ`.
`spatial_ibp` is the spatial post-IBP identity: diffusion is integrated by
parts twice, drift once, and the frozen chemotaxis source is put in divergence
weak form.
-/
structure WholeLineClassicalWeakFormData
    (p : CMParams) (c τ : ℝ) (V Vx : ℝ → ℝ)
    (w wx wxx wt : ℝ → ℝ → ℝ) : Prop where
  time_ftc :
    ∀ n Φ,
      wholeLineWeakIncrement w τ Φ n =
        ∫ s in Icc (0 : ℝ) τ,
          ∫ x : ℝ, wt ((n : ℝ) + s) x * Φ.phi x
  spatial_ibp :
    ∀ t Φ, 0 < t →
      (∫ x : ℝ,
          (wxx t x + c * wx t x +
              auxiliaryFrozenNonlinearity p (w t) (wx t) V Vx x) *
            Φ.phi x) =
        ∫ x : ℝ, wholeLineDivergenceWeakIntegrand p c (w t) Φ x

/-- Classical evolution plus the supplied spatial IBP gives the spatial weak
pairing at every positive time. -/
theorem wholeLine_spatialWeakPairing_eq_of_classical
    {p : CMParams} {c τ t : ℝ} {V Vx : ℝ → ℝ}
    {w wx wxx wt : ℝ → ℝ → ℝ}
    (Hclassical :
      ∀ T > 0, IsAuxiliaryClassicalSolutionOn p c V Vx T w wx wxx wt)
    (Hweak : WholeLineClassicalWeakFormData p c τ V Vx w wx wxx wt)
    (Φ : WholeLineWeakTestFunction) (ht : 0 < t) :
    (∫ x : ℝ, wt t x * Φ.phi x) =
      ∫ x : ℝ, wholeLineDivergenceWeakIntegrand p c (w t) Φ x := by
  have hT : 0 < t + 1 := by linarith
  have H := Hclassical (t + 1) hT
  calc
    (∫ x : ℝ, wt t x * Φ.phi x)
        =
          ∫ x : ℝ,
            (wxx t x + c * wx t x +
                auxiliaryFrozenNonlinearity p (w t) (wx t) V Vx x) *
              Φ.phi x := by
            refine integral_congr_ae (Eventually.of_forall ?_)
            intro x
            change wt t x * Φ.phi x =
              (wxx t x + c * wx t x +
                  auxiliaryFrozenNonlinearity p (w t) (wx t) V Vx x) *
                Φ.phi x
            rw [H.evolution_eq ht (by linarith : t < t + 1)]
    _ = ∫ x : ℝ, wholeLineDivergenceWeakIntegrand p c (w t) Φ x :=
          Hweak.spatial_ibp t Φ ht

/-- The positive-time spatial weak pairing holds for a.e. point of every
`[n,n+τ]` window; the only possible zero-time endpoint is null. -/
theorem wholeLine_spatialWeakPairing_eq_ae_nat_window
    {p : CMParams} {c τ : ℝ} {V Vx : ℝ → ℝ}
    {w wx wxx wt : ℝ → ℝ → ℝ}
    (Hclassical :
      ∀ T > 0, IsAuxiliaryClassicalSolutionOn p c V Vx T w wx wxx wt)
    (Hweak : WholeLineClassicalWeakFormData p c τ V Vx w wx wxx wt)
    (n : ℕ) (Φ : WholeLineWeakTestFunction) :
    ∀ᵐ s : ℝ ∂(volume.restrict (Icc (0 : ℝ) τ)),
      (∫ x : ℝ, wt ((n : ℝ) + s) x * Φ.phi x) =
        wholeLineTimeWindowWeakIntegrand p c w τ Φ n s := by
  rw [ae_restrict_iff' measurableSet_Icc]
  have hne_zero : ∀ᵐ s : ℝ ∂volume, s ≠ 0 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne_zero] with s hs_ne hs_mem
  have hs_pos : 0 < s := lt_of_le_of_ne hs_mem.1 (Ne.symm hs_ne)
  have ht_pos : 0 < (n : ℝ) + s := by
    have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    linarith
  simpa [wholeLineTimeWindowWeakIntegrand] using
    wholeLine_spatialWeakPairing_eq_of_classical
      (p := p) (c := c) (τ := τ) (V := V) (Vx := Vx)
      (w := w) (wx := wx) (wxx := wxx) (wt := wt)
      Hclassical Hweak Φ ht_pos

/-- Flow weak form discharged from the classical auxiliary equation, the
time-FTC pairing, and the spatial post-IBP identity. -/
theorem wholeLineFlowWeakForm_of_classical
    {p : CMParams} {c τ : ℝ} {V Vx : ℝ → ℝ}
    {w wx wxx wt : ℝ → ℝ → ℝ}
    (Hclassical :
      ∀ T > 0, IsAuxiliaryClassicalSolutionOn p c V Vx T w wx wxx wt)
    (Hweak : WholeLineClassicalWeakFormData p c τ V Vx w wx wxx wt) :
    WholeLineFlowWeakForm p c w τ := by
  intro n Φ
  calc
    wholeLineWeakIncrement w τ Φ n
        =
          ∫ s in Icc (0 : ℝ) τ,
            ∫ x : ℝ, wt ((n : ℝ) + s) x * Φ.phi x :=
          Hweak.time_ftc n Φ
    _ = ∫ s in Icc (0 : ℝ) τ,
          wholeLineTimeWindowWeakIntegrand p c w τ Φ n s := by
          exact integral_congr_ae
            (wholeLine_spatialWeakPairing_eq_ae_nat_window
              (p := p) (c := c) (τ := τ) (V := V) (Vx := Vx)
              (w := w) (wx := wx) (wxx := wxx) (wt := wt)
              Hclassical Hweak n Φ)
    _ = wholeLineTimeIntegratedWeakRHS p c w τ Φ n := by
          rfl

/-- L¹ estimate for a product whose first factor is uniformly small on the
support of the second factor. -/
theorem integral_mul_abs_le_l1_of_pointwise_on_support
    {d φ : ℝ → ℝ} {η : ℝ}
    (hη : 0 ≤ η) (hφ : Integrable φ)
    (hsmall : ∀ x, φ x ≠ 0 → |d x| ≤ η) :
    |∫ x : ℝ, d x * φ x| ≤ η * ∫ x : ℝ, |φ x| := by
  calc
    |∫ x : ℝ, d x * φ x| = ‖∫ x : ℝ, d x * φ x‖ := by
      simp [Real.norm_eq_abs]
    _ ≤ ∫ x : ℝ, ‖d x * φ x‖ := norm_integral_le_integral_norm _
    _ = ∫ x : ℝ, |d x * φ x| := by
      simp [Real.norm_eq_abs]
    _ ≤ ∫ x : ℝ, η * |φ x| := by
      refine integral_mono_of_nonneg (Eventually.of_forall ?_) ?_
        (Eventually.of_forall ?_)
      · intro x
        exact abs_nonneg _
      · simpa [Real.norm_eq_abs] using hφ.norm.const_mul η
      · intro x
        by_cases hx : φ x = 0
        · simp [hx]
        · simpa [abs_mul] using
            mul_le_mul (hsmall x hx) le_rfl (abs_nonneg (φ x)) hη
    _ = η * ∫ x : ℝ, |φ x| := by
      rw [integral_const_mul]

/-- Pointwise smallness on the support of a weak test datum, obtained from a
local-uniform estimate on a larger compact interval. -/
theorem weakTest_support_small_of_Icc_bound
    {Φ : WholeLineWeakTestFunction} {d : ℝ → ℝ} {R η : ℝ}
    (hR_radius : Φ.supportRadius < R)
    (hsmall : ∀ x, x ∈ Icc (-R) R → |d x| ≤ η) :
    ∀ x, Φ.phi x ≠ 0 → |d x| ≤ η := by
  intro x hx_ne
  by_cases hxR : x ∈ Icc (-R) R
  · exact hsmall x hxR
  · have hcases : ¬ (-R ≤ x) ∨ ¬ (x ≤ R) := not_and_or.mp hxR
    have hR_abs : R < |x| := by
      rcases hcases with hx_left | hx_right
      · rw [lt_abs]
        exact Or.inr (by have hxlt := lt_of_not_ge hx_left; linarith)
      · rw [lt_abs]
        exact Or.inl (lt_of_not_ge hx_right)
    have hphi_zero : Φ.phi x = 0 :=
      Φ.phi_zero_of_radius x (lt_trans hR_radius hR_abs)
    exact False.elim (hx_ne hphi_zero)

/-- Endpoint increment vanishes once both endpoint slices converge locally
uniformly to the same limit and test functions have finite L¹ mass. -/
theorem wholeLineWeakIncrementVanishes_of_endpoint_locUnifLimit
    {w : ℝ → ℝ → ℝ} {U : ℝ → ℝ} {τ : ℝ}
    (horbit :
      ShenWork.Paper1.LocallyUniformConverges
        (fun n x => w (n : ℝ) x) U)
    (hshift :
      ShenWork.Paper1.LocallyUniformConverges
        (fun n x => w ((n : ℝ) + τ) x) U)
    (hΦ_l1 : ∀ Φ : WholeLineWeakTestFunction, Integrable Φ.phi) :
    WholeLineWeakIncrementVanishes w τ := by
  intro Φ
  rw [Metric.tendsto_atTop]
  intro ε hε
  let A : ℝ := ∫ x : ℝ, |Φ.phi x|
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg fun x => abs_nonneg (Φ.phi x)
  let δ : ℝ := ε / (2 * (A + 1))
  have hden_pos : 0 < 2 * (A + 1) := by nlinarith
  have hδ_pos : 0 < δ := div_pos hε hden_pos
  let R : ℝ := Φ.supportRadius + 1
  have hR_pos : 0 < R := by
    dsimp [R]
    nlinarith [Φ.supportRadius_nonneg]
  have hR_radius : Φ.supportRadius < R := by
    dsimp [R]
    linarith
  have hlt : (2 * δ) * A < ε := by
    have hA_lt : A < A + 1 := by linarith
    calc
      (2 * δ) * A < (2 * δ) * (A + 1) := by
        exact mul_lt_mul_of_pos_left hA_lt (by positivity)
      _ = ε := by
        dsimp [δ]
        field_simp [ne_of_gt hden_pos]
  have hevent :
      ∀ᶠ n : ℕ in atTop,
        dist (wholeLineWeakIncrement w τ Φ n) 0 < ε := by
    filter_upwards [horbit R hR_pos δ hδ_pos, hshift R hR_pos δ hδ_pos]
      with n hn hsn
    have hdiff_small :
        ∀ x, Φ.phi x ≠ 0 →
          |w ((n : ℝ) + τ) x - w (n : ℝ) x| ≤ 2 * δ := by
      refine weakTest_support_small_of_Icc_bound
        (Φ := Φ) (R := R) (η := 2 * δ) hR_radius ?_
      intro x hxR
      have hshift_x := hsn x hxR
      have horbit_x := hn x hxR
      calc
        |w ((n : ℝ) + τ) x - w (n : ℝ) x|
            =
              |(w ((n : ℝ) + τ) x - U x) -
                (w (n : ℝ) x - U x)| := by ring_nf
        _ ≤ |w ((n : ℝ) + τ) x - U x| +
              |w (n : ℝ) x - U x| := by
              calc
                |(w ((n : ℝ) + τ) x - U x) -
                    (w (n : ℝ) x - U x)|
                    =
                      |(w ((n : ℝ) + τ) x - U x) +
                        (-(w (n : ℝ) x - U x))| := by ring_nf
                _ ≤ |w ((n : ℝ) + τ) x - U x| +
                      |-(w (n : ℝ) x - U x)| := abs_add_le _ _
                _ = |w ((n : ℝ) + τ) x - U x| +
                      |w (n : ℝ) x - U x| := by rw [abs_neg]
        _ ≤ 2 * δ := by linarith [hshift_x.le, horbit_x.le]
    have hη_nonneg : 0 ≤ 2 * δ := by positivity
    have hbound :
        |wholeLineWeakIncrement w τ Φ n| ≤ (2 * δ) * A := by
      simpa [wholeLineWeakIncrement, A] using
        integral_mul_abs_le_l1_of_pointwise_on_support
          (d := fun x => w ((n : ℝ) + τ) x - w (n : ℝ) x)
          (φ := Φ.phi) hη_nonneg (hΦ_l1 Φ) hdiff_small
    have habs : |wholeLineWeakIncrement w τ Φ n| < ε :=
      lt_of_le_of_lt hbound hlt
    simpa [Real.dist_eq] using habs
  exact eventually_atTop.1 hevent

/-- Increment-vanishing form using the shifted-window convergence already
produced by the weak-stationary-limit assembly. -/
theorem wholeLineWeakIncrementVanishes_of_locUnifLimit
    {w : ℝ → ℝ → ℝ} {U : ℝ → ℝ} {τ : ℝ}
    (hτ_nonneg : 0 ≤ τ)
    (horbit :
      ShenWork.Paper1.LocallyUniformConverges
        (fun n x => w (n : ℝ) x) U)
    (hshift_window :
      ∀ R > 0, ∀ ε > 0,
        ∀ᶠ n : ℕ in atTop,
          ∀ s : ℝ, s ∈ Icc (0 : ℝ) τ →
            ∀ x : ℝ, x ∈ Icc (-R) R →
              |w ((n : ℝ) + s) x - U x| < ε)
    (hΦ_l1 : ∀ Φ : WholeLineWeakTestFunction, Integrable Φ.phi) :
    WholeLineWeakIncrementVanishes w τ := by
  refine wholeLineWeakIncrementVanishes_of_endpoint_locUnifLimit
    (w := w) (U := U) (τ := τ) horbit ?_ hΦ_l1
  intro R hR ε hε
  filter_upwards [hshift_window R hR ε hε] with n hn
  intro x hx
  exact hn τ ⟨hτ_nonneg, le_rfl⟩ x hx

/-- DCT data for one test function on the time window.  The limit integrand is
constant in `s`, hence the average converges to the stationary weak functional. -/
structure WholeLineTimeWindowDCTData
    (p : CMParams) (c : ℝ) (w : ℝ → ℝ → ℝ) (U : ℝ → ℝ)
    (τ : ℝ) (Φ : WholeLineWeakTestFunction) where
  bound : ℝ → ℝ
  bound_integrable :
    Integrable bound (volume.restrict (Icc (0 : ℝ) τ))
  integrand_measurable :
    ∀ᶠ n : ℕ in atTop,
      AEStronglyMeasurable
        (wholeLineTimeWindowWeakIntegrand p c w τ Φ n)
        (volume.restrict (Icc (0 : ℝ) τ))
  dominated :
    ∀ᶠ n : ℕ in atTop,
      ∀ᵐ s : ℝ ∂(volume.restrict (Icc (0 : ℝ) τ)),
        ‖wholeLineTimeWindowWeakIntegrand p c w τ Φ n s‖ ≤ bound s
  pointwise_tendsto :
    ∀ᵐ s : ℝ ∂(volume.restrict (Icc (0 : ℝ) τ)),
      Tendsto
        (fun n : ℕ => wholeLineTimeWindowWeakIntegrand p c w τ Φ n s)
        atTop
        (𝓝 (wholeLineStationaryWeakFunctional p c U Φ))

/-- DCT for the time average against a fixed weak test datum. -/
theorem wholeLineTimeAveragedWeakRHS_tendsto_of_windowDCT
    {p : CMParams} {c : ℝ} {w : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {τ : ℝ} (hτ_pos : 0 < τ) {Φ : WholeLineWeakTestFunction}
    (H : WholeLineTimeWindowDCTData p c w U τ Φ) :
    Tendsto
      (fun n : ℕ => wholeLineTimeAveragedWeakRHS p c w τ Φ n)
      atTop
      (𝓝 (wholeLineStationaryWeakFunctional p c U Φ)) := by
  let F : ℕ → ℝ → ℝ := wholeLineTimeWindowWeakIntegrand p c w τ Φ
  let G : ℝ → ℝ := fun _ =>
    wholeLineStationaryWeakFunctional p c U Φ
  have hInt :
      Tendsto
        (fun n : ℕ => ∫ s, F n s ∂(volume.restrict (Icc (0 : ℝ) τ)))
        atTop
        (𝓝 (∫ s, G s ∂(volume.restrict (Icc (0 : ℝ) τ)))) :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Icc (0 : ℝ) τ)) (l := atTop)
      (F := F) (f := G)
      H.bound
      (by simpa [F] using H.integrand_measurable)
      (by simpa [F] using H.dominated)
      H.bound_integrable
      (by simpa [F, G] using H.pointwise_tendsto)
  have hG_integral :
      (∫ s, G s ∂(volume.restrict (Icc (0 : ℝ) τ))) =
        τ * wholeLineStationaryWeakFunctional p c U Φ := by
    dsimp [G]
    rw [integral_const]
    simp [le_of_lt hτ_pos, smul_eq_mul]
  have hscaled :
      Tendsto
        (fun n : ℕ =>
          (1 / τ) *
            ∫ s, F n s ∂(volume.restrict (Icc (0 : ℝ) τ)))
        atTop
        (𝓝 (wholeLineStationaryWeakFunctional p c U Φ)) := by
    have hmul := hInt.const_mul (1 / τ)
    simpa [hG_integral, ne_of_gt hτ_pos] using hmul
  simpa [wholeLineTimeAveragedWeakRHS, wholeLineTimeIntegratedWeakRHS,
    wholeLineTimeWindowWeakIntegrand, F] using hscaled

/-- The named time-integrated weak DCT input follows from per-test window DCT
data built from the supplied limit and bound information. -/
theorem wholeLineTimeIntegratedWeakDCT_of_bounds
    {p : CMParams} {c : ℝ} {w : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {τ : ℝ} (hτ_pos : 0 < τ)
    (H :
      ∀
        (_orbit_locunif :
          ShenWork.Paper1.LocallyUniformConverges
            (fun n x => w (n : ℝ) x) U)
        (_shift_locunif :
          ∀ R > 0, ∀ ε > 0,
            ∀ᶠ n : ℕ in atTop,
              ∀ s : ℝ, s ∈ Icc (0 : ℝ) τ →
                ∀ x : ℝ, x ∈ Icc (-R) R →
                  |w ((n : ℝ) + s) x - U x| < ε)
        (_flux_locunif :
          ShenWork.Paper1.LocallyUniformConverges
            (fun n x => wholeLineFlux p (fun y => w (n : ℝ) y) x)
            (wholeLineFlux p U))
        (_reaction_locunif :
          ShenWork.Paper1.LocallyUniformConverges
            (fun n x => wholeLineReaction p (fun y => w (n : ℝ) y) x)
            (wholeLineReaction p U))
        (Φ : WholeLineWeakTestFunction),
          WholeLineTimeWindowDCTData p c w U τ Φ) :
    WholeLineTimeIntegratedWeakDCT p c w U τ := by
  intro horbit hshift hflux hreaction Φ
  exact wholeLineTimeAveragedWeakRHS_tendsto_of_windowDCT
    (p := p) (c := c) (w := w) (U := U) (τ := τ)
    hτ_pos (H horbit hshift hflux hreaction Φ)

#print axioms wholeLine_spatialWeakPairing_eq_of_classical
#print axioms wholeLine_spatialWeakPairing_eq_ae_nat_window
#print axioms wholeLineFlowWeakForm_of_classical
#print axioms integral_mul_abs_le_l1_of_pointwise_on_support
#print axioms weakTest_support_small_of_Icc_bound
#print axioms wholeLineWeakIncrementVanishes_of_endpoint_locUnifLimit
#print axioms wholeLineWeakIncrementVanishes_of_locUnifLimit
#print axioms wholeLineTimeAveragedWeakRHS_tendsto_of_windowDCT
#print axioms wholeLineTimeIntegratedWeakDCT_of_bounds

end ShenWork.PaperOne
