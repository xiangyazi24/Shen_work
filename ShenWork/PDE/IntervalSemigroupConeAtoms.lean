/-
  Cone atoms (Q1 groundwork): operator scalar linearity and the
  Duhamel-of-cone evaluation.

  For the χ₀ = 0 cone-invariance route, the mild map's Duhamel term must
  be evaluated EXACTLY on cone elements `c(s)·S(s)f`:

    `∫₀ᵗ S(t−s)(c(s)·S(s)f)(x) ds = (∫₀ᵗ c(s) ds) · S(t)f(x)`,

  which re-absorbs the Grönwall envelope into the same `S(t)f` profile:
  with `c(s) = a·e^{as}` this gives `(e^{at} − 1)·S(t)f`, hence the exact
  invariance of the upper cone `w ≤ e^{at}·S(t)u₀`, and with
  `c(s) = −K·e^{as}` the lower envelope `θ(t)·S(t)u₀`,
  `θ(t) = 1 − K(e^{at}−1)/a`.

  Atoms:
  * `intervalFullSemigroupOperator_const_mul` — `S(t)(c·f) = c·S(t)f`;
  * `intervalFullSemigroupOperator_comp_const_mul` —
    `S(t−s)(c·S(s)f)(x) = c·S(t)f(x)` on `[0,1]` (composition law);
  * `duhamel_cone_eval` — the displayed integral evaluation
    (no integrability hypothesis: `integral_mul_const` is unconditional).

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalSemigroupComposition

open MeasureTheory
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalSemigroupComposition

noncomputable section

namespace ShenWork.IntervalSemigroupConeAtoms

/-- Scalar linearity of the full Neumann propagator. -/
theorem intervalFullSemigroupOperator_const_mul
    (t c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    intervalFullSemigroupOperator t (fun y => c * f y) x
      = c * intervalFullSemigroupOperator t f x := by
  unfold intervalFullSemigroupOperator
  calc (∫ y, intervalNeumannFullKernel t x y * (c * f y)
        ∂(ShenWork.IntervalDomain.intervalMeasure 1))
      = ∫ y, c * (intervalNeumannFullKernel t x y * f y)
          ∂(ShenWork.IntervalDomain.intervalMeasure 1) := by
        congr 1; funext y; ring
    _ = c * ∫ y, intervalNeumannFullKernel t x y * f y
          ∂(ShenWork.IntervalDomain.intervalMeasure 1) :=
        integral_const_mul c _

/-- **Composition + scalar linearity on cone elements**:
`S(t−s)(c·S(s)f)(x) = c·S(t)f(x)` for `0 < s < t`, on `[0,1]`. -/
theorem intervalFullSemigroupOperator_comp_const_mul
    {s t : ℝ} (hs : 0 < s) (hst : s < t)
    {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ n, |cosineCoeffs f n| ≤ M) (c : ℝ)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalFullSemigroupOperator (t - s)
        (fun y => c * intervalFullSemigroupOperator s f y) x
      = c * intervalFullSemigroupOperator t f x := by
  rw [intervalFullSemigroupOperator_const_mul]
  congr 1
  have hcomp := intervalFullSemigroupOperator_comp
    (sub_pos.mpr hst) hs hf hM hx
  have hts : t - s + s = t := by ring
  rw [hcomp, hts]

/-- **Duhamel-of-cone evaluation**: the Duhamel integral of a cone family
`s ↦ c(s)·S(s)f` collapses to `(∫₀ᵗ c)·S(t)f(x)`, for any interval-
integrable scalar profile `c`. -/
theorem duhamel_cone_eval
    {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ n, |cosineCoeffs f n| ≤ M)
    {c : ℝ → ℝ}
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s)
        (fun y => c s * intervalFullSemigroupOperator s f y) x)
      = (∫ s in (0:ℝ)..t, c s) * intervalFullSemigroupOperator t f x := by
  have hcongr : (∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s)
        (fun y => c s * intervalFullSemigroupOperator s f y) x)
      = ∫ s in (0:ℝ)..t, c s * intervalFullSemigroupOperator t f x := by
    apply intervalIntegral.integral_congr_ae
    have hne_t : ∀ᵐ s : ℝ ∂MeasureTheory.volume, s ≠ t := by
      rw [MeasureTheory.ae_iff]
      simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
    filter_upwards [hne_t] with s hsne hsI
    rw [Set.uIoc_of_le ht.le] at hsI
    have hst : s < t := lt_of_le_of_ne hsI.2 hsne
    exact intervalFullSemigroupOperator_comp_const_mul hsI.1 hst hf hM
      (c s) hx
  rw [hcongr, intervalIntegral.integral_mul_const]

/-! ## Monotonicity (bounded measurable inputs) -/

/-- Monotonicity of the full Neumann propagator for bounded measurable
inputs (kernel nonnegativity + integral monotonicity). -/
theorem intervalFullSemigroupOperator_mono_of_le
    {t : ℝ} (ht : 0 < t) {f g : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f
      (ShenWork.IntervalDomain.intervalMeasure 1))
    (hg_meas : AEStronglyMeasurable g
      (ShenWork.IntervalDomain.intervalMeasure 1))
    {Mf Mg : ℝ} (hf_bdd : ∀ y, |f y| ≤ Mf) (hg_bdd : ∀ y, |g y| ≤ Mg)
    (hfg : ∀ y, f y ≤ g y) (x : ℝ) :
    intervalFullSemigroupOperator t f x
      ≤ intervalFullSemigroupOperator t g x := by
  unfold intervalFullSemigroupOperator
  have hK_int := ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_integrable ht x
  have hint : ∀ {h : ℝ → ℝ} {Mh : ℝ},
      AEStronglyMeasurable h (ShenWork.IntervalDomain.intervalMeasure 1) →
      (∀ y, |h y| ≤ Mh) →
      Integrable (fun y => intervalNeumannFullKernel t x y * h y)
        (ShenWork.IntervalDomain.intervalMeasure 1) := by
    intro h Mh hh_meas hh_bdd
    have hmul : Integrable (fun y => h y * intervalNeumannFullKernel t x y)
        (ShenWork.IntervalDomain.intervalMeasure 1) :=
      hK_int.bdd_mul hh_meas
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs]; exact hh_bdd y)
    exact hmul.congr (Filter.Eventually.of_forall fun y => mul_comm _ _)
  apply integral_mono (hint hf_meas hf_bdd) (hint hg_meas hg_bdd)
  intro y
  exact mul_le_mul_of_nonneg_left (hfg y)
    (ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_nonneg ht x y)

/-- Icc-relative monotonicity: the propagator only sees `[0,1]`, so the
comparison hypothesis is only needed there.  This is the form the cone
preservation uses (the cone inequalities hold on `[0,1]` only). -/
theorem intervalFullSemigroupOperator_mono_of_le_on_Icc
    {t : ℝ} (ht : 0 < t) {f g : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f
      (ShenWork.IntervalDomain.intervalMeasure 1))
    (hg_meas : AEStronglyMeasurable g
      (ShenWork.IntervalDomain.intervalMeasure 1))
    {Mf Mg : ℝ} (hf_bdd : ∀ y, |f y| ≤ Mf) (hg_bdd : ∀ y, |g y| ≤ Mg)
    (hfg : ∀ y ∈ Set.Icc (0 : ℝ) 1, f y ≤ g y) (x : ℝ) :
    intervalFullSemigroupOperator t f x
      ≤ intervalFullSemigroupOperator t g x := by
  unfold intervalFullSemigroupOperator
  have hK_int := ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_integrable ht x
  have hint : ∀ {h : ℝ → ℝ} {Mh : ℝ},
      AEStronglyMeasurable h (ShenWork.IntervalDomain.intervalMeasure 1) →
      (∀ y, |h y| ≤ Mh) →
      Integrable (fun y => intervalNeumannFullKernel t x y * h y)
        (ShenWork.IntervalDomain.intervalMeasure 1) := by
    intro h Mh hh_meas hh_bdd
    have hmul : Integrable (fun y => h y * intervalNeumannFullKernel t x y)
        (ShenWork.IntervalDomain.intervalMeasure 1) :=
      hK_int.bdd_mul hh_meas
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs]; exact hh_bdd y)
    exact hmul.congr (Filter.Eventually.of_forall fun y => mul_comm _ _)
  apply integral_mono_ae (hint hf_meas hf_bdd) (hint hg_meas hg_bdd)
  simp only [ShenWork.IntervalDomain.intervalMeasure,
    ShenWork.IntervalDomain.intervalSet]
  refine (ae_restrict_iff' measurableSet_Icc).mpr
    (Filter.Eventually.of_forall fun y hy => ?_)
  exact mul_le_mul_of_nonneg_left (hfg y hy)
    (ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_nonneg ht x y)

/-! ## Strict positivity -/

/-- Strict pointwise positivity of the full Neumann kernel (copy of the
file-private lemma in IntervalDuhamelIntegrability.lean): the `k = 0`
lattice term is a positive Gaussian and all terms are nonnegative. -/
private theorem kernel_pos {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    0 < intervalNeumannFullKernel t x y := by
  rw [ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel]
  have hsumA := ShenWork.IntervalNeumannFullKernel.latticeGaussianSummable ht (x - y)
  have hsumB := ShenWork.IntervalNeumannFullKernel.latticeGaussianSummable ht (x + y)
  have hsum : Summable (fun k : ℤ =>
      heatKernel t (x - y + 2 * (k : ℝ)) + heatKernel t (x + y + 2 * (k : ℝ))) :=
    hsumA.add hsumB
  have hle : heatKernel t (x - y + 2 * ((0 : ℤ) : ℝ)) +
        heatKernel t (x + y + 2 * ((0 : ℤ) : ℝ))
      ≤ (∑' k : ℤ, (heatKernel t (x - y + 2 * (k : ℝ)) +
        heatKernel t (x + y + 2 * (k : ℝ)))) := by
    simpa using hsum.sum_le_tsum ({(0 : ℤ)} : Finset ℤ)
      (fun k _hk => add_nonneg (heatKernel_nonneg ht _) (heatKernel_nonneg ht _))
  have hpos : 0 < heatKernel t (x - y + 2 * ((0 : ℤ) : ℝ)) +
      heatKernel t (x + y + 2 * ((0 : ℤ) : ℝ)) :=
    add_pos (heatKernel_pos ht _) (heatKernel_pos ht _)
  exact lt_of_lt_of_le hpos hle

set_option maxHeartbeats 800000 in
/-- **Strict positivity of the propagator**: for `t > 0` and a continuous
nonnegative input that is positive SOMEWHERE on `[0,1]`, the propagated
value is strictly positive at EVERY point.  This is the instant
positivization that the cone route uses on positive initial data (which
may vanish on the boundary). -/
theorem intervalFullSemigroupOperator_pos
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hf_nonneg : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f y)
    {y₀ : ℝ} (hy₀ : y₀ ∈ Set.Icc (0 : ℝ) 1) (hf_pos : 0 < f y₀)
    (x : ℝ) :
    0 < intervalFullSemigroupOperator t f x := by
  -- Locate a small closed interval J around y₀ inside [0,1] where
  -- f > f y₀ / 2.
  have hcw : ContinuousWithinAt f (Set.Icc (0 : ℝ) 1) y₀ := hf_cont y₀ hy₀
  have hev : ∀ᶠ y in nhdsWithin y₀ (Set.Icc (0 : ℝ) 1), f y₀ / 2 < f y :=
    hcw.eventually (eventually_gt_nhds (by linarith))
  rw [Filter.eventually_iff, mem_nhdsWithin] at hev
  obtain ⟨U, hU_open, hy₀U, hUsub⟩ := hev
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU_open y₀ hy₀U
  set a : ℝ := max 0 (y₀ - r / 2) with ha_def
  set b : ℝ := min 1 (y₀ + r / 2) with hb_def
  have hab : a < b := by
    rcases lt_or_eq_of_le hy₀.2 with hlt | heq
    · -- y₀ < 1
      have hb1 : y₀ < b := lt_min hlt (by linarith)
      have ha1 : a ≤ y₀ := max_le hy₀.1 (by linarith)
      linarith
    · -- y₀ = 1
      have ha1 : a < 1 := max_lt (by norm_num) (by linarith)
      have hb1 : b = 1 := by
        rw [hb_def]
        exact min_eq_left (by linarith)
      rw [hb1]
      exact ha1
  have hJsub01 : Set.Icc a b ⊆ Set.Icc (0 : ℝ) 1 := by
    intro y hy
    constructor
    · exact le_trans (le_max_left 0 _) hy.1
    · exact le_trans hy.2 (min_le_left 1 _)
  have hJball : Set.Icc a b ⊆ Metric.ball y₀ r := by
    intro y hy
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
    have h1 : y₀ - r / 2 ≤ a := le_max_right 0 _
    have h2 : b ≤ y₀ + r / 2 := min_le_right 1 _
    constructor
    · linarith [hy.1, hy.2]
    · linarith [hy.1, hy.2]
  have hJf : ∀ y ∈ Set.Icc a b, f y₀ / 2 < f y := by
    intro y hy
    exact hUsub ⟨hball (hJball hy), hJsub01 hy⟩
  -- Kernel minimum on J is positive.
  have hKcont : ContinuousOn (fun y => intervalNeumannFullKernel t x y)
      (Set.Icc a b) :=
    (ShenWork.IntervalNeumannFullKernel.continuousOn_intervalNeumannFullKernel_snd
      ht x).mono hJsub01
  have hJne : (Set.Icc a b).Nonempty := ⟨a, Set.left_mem_Icc.mpr hab.le⟩
  obtain ⟨y₁, hy₁J, hy₁min⟩ := isCompact_Icc.exists_isMinOn hJne hKcont
  set κ : ℝ := intervalNeumannFullKernel t x y₁ with hκ_def
  have hκ_pos : 0 < κ := kernel_pos ht x y₁
  -- Integrability and a.e. nonnegativity of the integrand.
  have hbound : ∃ C : ℝ, ∀ y ∈ Set.Icc (0 : ℝ) 1, |f y| ≤ C := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf_cont
    exact ⟨C, fun y hy => (Real.norm_eq_abs (f y) ▸ hC y hy)⟩
  obtain ⟨C, hC⟩ := hbound
  have hf_meas : AEStronglyMeasurable f
      (ShenWork.IntervalDomain.intervalMeasure 1) := by
    simp only [ShenWork.IntervalDomain.intervalMeasure,
      ShenWork.IntervalDomain.intervalSet]
    exact hf_cont.aestronglyMeasurable measurableSet_Icc
  have hf_bdd_ae : ∀ᵐ y ∂(ShenWork.IntervalDomain.intervalMeasure 1),
      ‖f y‖ ≤ C := by
    simp only [ShenWork.IntervalDomain.intervalMeasure,
      ShenWork.IntervalDomain.intervalSet]
    exact (ae_restrict_iff' measurableSet_Icc).mpr
      (Filter.Eventually.of_forall fun y hy => by
        rw [Real.norm_eq_abs]; exact hC y hy)
  have hK_int :=
    ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_integrable ht x
  have hint : Integrable (fun y => intervalNeumannFullKernel t x y * f y)
      (ShenWork.IntervalDomain.intervalMeasure 1) :=
    (hK_int.bdd_mul hf_meas hf_bdd_ae).congr
      (Filter.Eventually.of_forall fun y => mul_comm _ _)
  have hnonneg_ae : 0 ≤ᵐ[ShenWork.IntervalDomain.intervalMeasure 1]
      fun y => intervalNeumannFullKernel t x y * f y := by
    simp only [ShenWork.IntervalDomain.intervalMeasure,
      ShenWork.IntervalDomain.intervalSet]
    exact (ae_restrict_iff' measurableSet_Icc).mpr
      (Filter.Eventually.of_forall fun y hy =>
        mul_nonneg
          (ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_nonneg
            ht x y)
          (hf_nonneg y hy))
  -- Restrict the integral to J and bound below by a positive constant.
  have hJ_le : (∫ y in Set.Icc a b, intervalNeumannFullKernel t x y * f y
        ∂(ShenWork.IntervalDomain.intervalMeasure 1))
      ≤ ∫ y, intervalNeumannFullKernel t x y * f y
          ∂(ShenWork.IntervalDomain.intervalMeasure 1) :=
    setIntegral_le_integral hint hnonneg_ae
  have hμJ : (ShenWork.IntervalDomain.intervalMeasure 1) (Set.Icc a b) ≠ ⊤ := by
    simp only [ShenWork.IntervalDomain.intervalMeasure,
      ShenWork.IntervalDomain.intervalSet]
    rw [Measure.restrict_apply measurableSet_Icc]
    exact ne_top_of_le_ne_top (by simp [Real.volume_Icc])
      (measure_mono Set.inter_subset_left)
  have hJ_lb : (κ * (f y₀ / 2)) *
        (ShenWork.IntervalDomain.intervalMeasure 1).real (Set.Icc a b)
      ≤ ∫ y in Set.Icc a b, intervalNeumannFullKernel t x y * f y
          ∂(ShenWork.IntervalDomain.intervalMeasure 1) := by
    apply setIntegral_ge_of_const_le_real measurableSet_Icc hμJ
    · intro y hy
      have hKy : κ ≤ intervalNeumannFullKernel t x y := isMinOn_iff.mp hy₁min y hy
      have hfy : f y₀ / 2 ≤ f y := (hJf y hy).le
      exact mul_le_mul hKy hfy (by linarith) (le_trans hκ_pos.le hKy)
    · exact hint.integrableOn
  have hμJ_real : (ShenWork.IntervalDomain.intervalMeasure 1).real (Set.Icc a b)
      = b - a := by
    simp only [ShenWork.IntervalDomain.intervalMeasure,
      ShenWork.IntervalDomain.intervalSet, MeasureTheory.measureReal_def]
    rw [Measure.restrict_apply measurableSet_Icc,
      Set.inter_eq_self_of_subset_left hJsub01, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith)]
  have hpos : 0 < (κ * (f y₀ / 2)) *
      (ShenWork.IntervalDomain.intervalMeasure 1).real (Set.Icc a b) := by
    rw [hμJ_real]
    have : 0 < b - a := by linarith
    positivity
  unfold intervalFullSemigroupOperator
  linarith

end ShenWork.IntervalSemigroupConeAtoms
