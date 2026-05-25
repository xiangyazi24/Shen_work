/-
  ShenWork/Paper2/IntervalDomainLemma21.lean

  Paper 2 Lemma 2.1 on intervalDomain: concrete heat-semigroup bridge.

  This file connects the already proved unit-interval heat estimates to the
  Paper2 interval-domain function interface.  The concrete
  `intervalDomainSemigroupEstimateData` below uses the real interval `Lp`
  seminorm, the restricted interval heat helper, and its spatial derivative.

  The field-level H0.1/H0.2 estimates are unconditional.  The exact abstract
  `Lemma_2_1`--`Lemma_2_4` statements still contain extra statement-layer
  requirements not supplied by H0.1/H0.2 alone: exponential damping in
  `Lemma_2_1`, a fractional graph norm compatible with `S(t)-I`, and the
  `t^{-1/2}` divergence singularity in `Lemma_2_3`/`Lemma_2_4` whereas the
  current H0.2 endpoint gives a stronger small-time singularity.  The
  comparison obstructions below make those frontiers formal rather than hiding
  them in the structure fields.
-/
import ShenWork.Paper2.Statements
import ShenWork.PDE.HeatKernelGradientEstimates

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace ShenWork.Paper2.IntervalDomainLemma21

open ShenWork.IntervalDomain
open ShenWork.HeatKernelGradientEstimates

/-! ### Concrete interval-domain heat-semigroup interface -/

/-- The `LpSeminorm` used for interval-domain functions through the concrete
zero-extension `intervalDomainLift`. -/
def intervalDomainLpNorm (q : ℝ) (u : intervalDomain.Point → ℝ) : ℝ :=
  lpNorm (intervalDomainLift u) (ENNReal.ofReal q) (intervalMeasure 1)

/-- The restricted reflected heat operator as an interval-domain point
function.  This is the H0.1 helper operator on the unit interval. -/
def intervalDomainHeatSemigroup
    (t : ℝ) (u : intervalDomain.Point → ℝ) :
    intervalDomain.Point → ℝ :=
  fun x => intervalSemigroupOperator 1 t (intervalDomainLift u) x.1

/-- Real-valued `lpNorm` respects almost-everywhere equality.  Mathlib has the
corresponding theorem for `eLpNorm`; this is the `toReal` wrapper needed by the
statement-layer real norms. -/
theorem lpNorm_congr_ae_real
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {p : ℝ≥0∞} {μ : Measure α} {f g : α → E}
    (hfg : f =ᵐ[μ] g) :
    lpNorm f p μ = lpNorm g p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · have hg : AEStronglyMeasurable g μ :=
      (aestronglyMeasurable_congr hfg).mp hf
    rw [← toReal_eLpNorm hf, ← toReal_eLpNorm hg, eLpNorm_congr_ae hfg]
  · have hg : ¬ AEStronglyMeasurable g μ := by
      intro hg
      exact hf ((aestronglyMeasurable_congr hfg).mpr hg)
    simp [lpNorm, hf, hg]

/-- On the restricted unit interval measure, lifting the point-function heat
output agrees almost everywhere with the real-line helper operator. -/
theorem intervalDomainHeatSemigroup_lift_ae_eq
    (t : ℝ) (u : intervalDomain.Point → ℝ) :
    intervalDomainLift (intervalDomainHeatSemigroup t u)
      =ᵐ[intervalMeasure 1]
        fun x : ℝ => intervalSemigroupOperator 1 t (intervalDomainLift u) x := by
  unfold intervalMeasure intervalSet
  filter_upwards
    [MeasureTheory.self_mem_ae_restrict
      (show MeasurableSet (Set.Icc (0 : ℝ) 1) by simp)] with x hx
  simp [intervalDomainLift, intervalDomainHeatSemigroup, hx]

/-- The point-function heat output has the same `LpSeminorm` as the concrete
real helper operator on `[0,1]`. -/
theorem intervalDomainHeatSemigroup_lpNorm_eq
    (q t : ℝ) (u : intervalDomain.Point → ℝ) :
    intervalDomainLpNorm q (intervalDomainHeatSemigroup t u) =
      lpNorm
        (fun x : ℝ => intervalSemigroupOperator 1 t (intervalDomainLift u) x)
        (ENNReal.ofReal q) (intervalMeasure 1) := by
  exact lpNorm_congr_ae_real
    (intervalDomainHeatSemigroup_lift_ae_eq t u)

/-! ### H0.1/H0.2 estimates specialized to intervalDomain -/

/-- H0.1 specialized to `intervalDomain`: finite `L^p → L^q` smoothing for
the concrete unit-interval helper heat operator, stated on point functions via
`intervalDomainLift`. -/
theorem intervalDomainHeat_Lp_Lq_bound_from_memLp
    {t p q r : ℝ} (ht : 0 < t) (hrp : r.HolderConjugate p)
    (hpq : p ≤ q)
    {u : intervalDomain.Point → ℝ}
    (hu_mem :
      MemLp (intervalDomainLift u) (ENNReal.ofReal p) (intervalMeasure 1)) :
    intervalDomainLpNorm q (intervalDomainHeatSemigroup t u) ≤
      (1 / Real.sqrt (4 * Real.pi * t)) ^ (1 / p - 1 / q) *
        intervalDomainLpNorm p u := by
  rw [intervalDomainHeatSemigroup_lpNorm_eq]
  exact intervalHeatSemigroup_Lp_Lq_bound
    (L := 1) (t := t) (p := p) (q := q) (r := r)
    ht hrp hpq (f := intervalDomainLift u) hu_mem

/-- H0.2 specialized to `intervalDomain`: finite `L^p → L^q` smoothing for
the spatial derivative of the unit-interval helper heat operator. -/
theorem intervalDomainHeat_grad_Lp_Lq_bound_from_memLp
    {t p q : ℝ} (ht : 0 < t) (hp : 1 ≤ p) (hq : 0 < q)
    {u : intervalDomain.Point → ℝ}
    (hu_mem :
      MemLp (intervalDomainLift u) (ENNReal.ofReal p) (intervalMeasure 1)) :
    lpNorm
        (fun x : ℝ =>
          deriv
            (fun z : ℝ =>
              intervalSemigroupOperator 1 t (intervalDomainLift u) z) x)
        (ENNReal.ofReal q) (intervalMeasure 1) ≤
      heatGradientL1LinftyFactor t * intervalDomainLpNorm p u := by
  exact unitIntervalSemigroupOperator_grad_Lp_Lq_lpNorm_bound
    (t := t) (p := p) (q := q) ht hp hq
    (f := intervalDomainLift u) hu_mem

/-- The corresponding `L^p → L∞` derivative estimate for the unit-interval
helper heat operator. -/
theorem intervalDomainHeat_grad_Lp_Linfty_bound_from_memLp
    {t p : ℝ} (ht : 0 < t) (hp : 1 ≤ p)
    {u : intervalDomain.Point → ℝ}
    (hu_mem :
      MemLp (intervalDomainLift u) (ENNReal.ofReal p) (intervalMeasure 1)) :
    lpNorm
        (fun x : ℝ =>
          deriv
            (fun z : ℝ =>
              intervalSemigroupOperator 1 t (intervalDomainLift u) z) x)
        ∞ (intervalMeasure 1) ≤
      heatGradientL1LinftyFactor t * intervalDomainLpNorm p u := by
  exact unitIntervalSemigroupOperator_grad_Lp_Linfty_lpNorm_bound
    (t := t) (p := p) ht hp
    (f := intervalDomainLift u) hu_mem

/-! ### Concrete `SemigroupEstimateData` for the interval heat helper -/

/-- The one-dimensional divergence semigroup field represented by the spatial
derivative of the concrete interval heat helper. -/
def intervalDomainHeatDivergenceSemigroup
    (t : ℝ) (u : intervalDomain.Point → ℝ) :
    intervalDomain.Point → ℝ :=
  fun x =>
    deriv
      (fun z : ℝ =>
        intervalSemigroupOperator 1 t (intervalDomainLift u) z) x.1

/-- On the restricted unit interval measure, lifting the point-function
divergence output agrees almost everywhere with the real-line derivative of
the helper heat operator. -/
theorem intervalDomainHeatDivergenceSemigroup_lift_ae_eq
    (t : ℝ) (u : intervalDomain.Point → ℝ) :
    intervalDomainLift (intervalDomainHeatDivergenceSemigroup t u)
      =ᵐ[intervalMeasure 1]
        fun x : ℝ =>
          deriv
            (fun z : ℝ =>
              intervalSemigroupOperator 1 t (intervalDomainLift u) z) x := by
  unfold intervalMeasure intervalSet
  filter_upwards
    [MeasureTheory.self_mem_ae_restrict
      (show MeasurableSet (Set.Icc (0 : ℝ) 1) by simp)] with x hx
  simp [intervalDomainLift, intervalDomainHeatDivergenceSemigroup, hx]

/-- The divergence point-function output has the same `LpSeminorm` as the
real-line derivative of the helper heat operator on `[0,1]`. -/
theorem intervalDomainHeatDivergenceSemigroup_lpNorm_eq
    (q t : ℝ) (u : intervalDomain.Point → ℝ) :
    intervalDomainLpNorm q (intervalDomainHeatDivergenceSemigroup t u) =
      lpNorm
        (fun x : ℝ =>
          deriv
            (fun z : ℝ =>
              intervalSemigroupOperator 1 t (intervalDomainLift u) z) x)
        (ENNReal.ofReal q) (intervalMeasure 1) := by
  exact lpNorm_congr_ae_real
    (intervalDomainHeatDivergenceSemigroup_lift_ae_eq t u)

/-- Concrete interval-domain semigroup estimate data backed by the proved
heat-kernel operators.  The remaining abstract Paper2 lemma fields are not
assumed here; they must be proved from the displayed operators. -/
def intervalDomainSemigroupEstimateData :
    SemigroupEstimateData intervalDomain where
  lpNorm := intervalDomainLpNorm
  vectorLpNorm := intervalDomainLpNorm
  fractionalNorm := fun _ q u => intervalDomainLpNorm q u
  semigroup := intervalDomainHeatSemigroup
  divergenceSemigroup := intervalDomainHeatDivergenceSemigroup
  embeddingNorm := fun _ r _ u => intervalDomainLpNorm r u

/-- H0.1 routed through the concrete `SemigroupEstimateData` object. -/
theorem intervalDomainSemigroupEstimateData_Lp_Lq_bound_from_memLp
    {t p q r : ℝ} (ht : 0 < t) (hrp : r.HolderConjugate p)
    (hpq : p ≤ q)
    {u : intervalDomain.Point → ℝ}
    (hu_mem :
      MemLp (intervalDomainLift u) (ENNReal.ofReal p) (intervalMeasure 1)) :
    intervalDomainSemigroupEstimateData.lpNorm q
        (intervalDomainSemigroupEstimateData.semigroup t u) ≤
      (1 / Real.sqrt (4 * Real.pi * t)) ^ (1 / p - 1 / q) *
        intervalDomainSemigroupEstimateData.lpNorm p u := by
  simpa [intervalDomainSemigroupEstimateData] using
    intervalDomainHeat_Lp_Lq_bound_from_memLp
      (t := t) (p := p) (q := q) (r := r) ht hrp hpq
      (u := u) hu_mem

/-- H0.2 routed through the concrete `SemigroupEstimateData` object, in the
currently proved nonsharp derivative endpoint. -/
theorem intervalDomainSemigroupEstimateData_divergence_Lp_Lq_bound_from_memLp
    {t p q : ℝ} (ht : 0 < t) (hp : 1 ≤ p) (hq : 0 < q)
    {u : intervalDomain.Point → ℝ}
    (hu_mem :
      MemLp (intervalDomainLift u) (ENNReal.ofReal p) (intervalMeasure 1)) :
    intervalDomainSemigroupEstimateData.lpNorm q
        (intervalDomainSemigroupEstimateData.divergenceSemigroup t u) ≤
      heatGradientL1LinftyFactor t *
        intervalDomainSemigroupEstimateData.vectorLpNorm p u := by
  rw [intervalDomainSemigroupEstimateData]
  change intervalDomainLpNorm q
      (intervalDomainHeatDivergenceSemigroup t u) ≤
    heatGradientL1LinftyFactor t * intervalDomainLpNorm p u
  rw [intervalDomainHeatDivergenceSemigroup_lpNorm_eq]
  exact intervalDomainHeat_grad_Lp_Lq_bound_from_memLp
    (t := t) (p := p) (q := q) ht hp hq (u := u) hu_mem

/-! ### Exact Paper2 route obstructions for the current data -/

/-- A semigroup estimate without a real damping factor cannot be upgraded to
an arbitrary positive exponential decay by changing only the constant.  This is
the scalar obstruction behind the `exp (-δ t)` factor in `Lemma_2_1` for the
undamped interval heat-helper data. -/
theorem one_not_bounded_by_exp_decay
    {delta : ℝ} (hdelta : 0 < delta) :
    ¬ ∃ C : ℝ, ∀ t > 0, 1 ≤ C * Real.exp (-(delta * t)) := by
  rintro ⟨C, hC⟩
  let A : ℝ := max C 1
  have hA_ge_one : 1 ≤ A := le_max_right _ _
  have hC_le_A : C ≤ A := le_max_left _ _
  have hA_pos : 0 < A := lt_of_lt_of_le zero_lt_one hA_ge_one
  let t : ℝ := (Real.log A + 1) / delta
  have ht : 0 < t := by
    dsimp [t]
    apply div_pos
    · have hlog_nonneg : 0 ≤ Real.log A := Real.log_nonneg hA_ge_one
      linarith
    · exact hdelta
  have harg : delta * t = Real.log A + 1 := by
    dsimp [t]
    field_simp [ne_of_gt hdelta]
  have hbound := hC t ht
  rw [harg] at hbound
  have hExp :
      Real.exp (-(Real.log A + 1)) = Real.exp (-1) / A := by
    rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_log hA_pos]
    field_simp [ne_of_gt hA_pos]
  rw [hExp] at hbound
  cases le_or_gt C 0 with
  | inl hC_nonpos =>
      have hexp_pos : 0 < Real.exp (-1) / A :=
        div_pos (Real.exp_pos _) hA_pos
      have hright_nonpos : C * (Real.exp (-1) / A) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hC_nonpos hexp_pos.le
      linarith
  | inr _hC_pos =>
      have hC_div_le_one : C / A ≤ 1 :=
        (div_le_one hA_pos).mpr hC_le_A
      have hexp_lt_one : Real.exp (-1) < 1 :=
        Real.exp_lt_one_iff.mpr (by norm_num)
      have hright_lt_one : C * (Real.exp (-1) / A) < 1 := by
        have hrewrite :
            C * (Real.exp (-1) / A) = (C / A) * Real.exp (-1) := by
          ring
        rw [hrewrite]
        calc
          (C / A) * Real.exp (-1) ≤ 1 * Real.exp (-1) := by
            exact mul_le_mul_of_nonneg_right hC_div_le_one
              (Real.exp_pos _).le
          _ < 1 := by simpa only [one_mul] using hexp_lt_one
      linarith

/-- The paper's `1 + t^{-1/2}` gradient factor cannot absorb a `t^{-1}`
small-time endpoint with a uniform constant.  This is the scalar obstruction
behind routing the current nonsharp H0.2 divergence estimate directly into
`Lemma_2_3`/`Lemma_2_4`. -/
theorem inv_not_dominated_by_one_add_inv_sqrt :
    ¬ ∃ C : ℝ, ∀ t > 0,
      1 / t ≤ C * (1 + t ^ (-(1 / 2 : ℝ))) := by
  rintro ⟨C, hC⟩
  let A : ℝ := max (2 * C) 1 + 1
  have hmax1 : (1 : ℝ) ≤ max (2 * C) 1 := le_max_right _ _
  have hmaxC : 2 * C ≤ max (2 * C) 1 := le_max_left _ _
  have hA_gt_one : 1 < A := by
    dsimp [A]
    linarith
  have hA_pos : 0 < A := lt_trans zero_lt_one hA_gt_one
  have hC_le : C ≤ A / 2 := by
    dsimp [A] at hmaxC ⊢
    linarith
  let t : ℝ := (A ^ 2)⁻¹
  have ht : 0 < t := by
    dsimp [t]
    exact inv_pos.mpr (sq_pos_of_pos hA_pos)
  have hinv : 1 / t = A ^ 2 := by
    dsimp [t]
    field_simp [ne_of_gt (sq_pos_of_pos hA_pos)]
  have hrpow : t ^ (-(1 / 2 : ℝ)) = A := by
    dsimp [t]
    have hA2_pos : 0 < A ^ 2 := sq_pos_of_pos hA_pos
    have ht_pos : 0 < (A ^ 2)⁻¹ := inv_pos.mpr hA2_pos
    rw [Real.rpow_neg ht_pos.le]
    have hhalf : ((A ^ 2)⁻¹) ^ (1 / 2 : ℝ) = A⁻¹ := by
      rw [← Real.sqrt_eq_rpow]
      rw [Real.sqrt_inv]
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_pos hA_pos]
    rw [hhalf]
    field_simp [ne_of_gt hA_pos]
  have hbound := hC t ht
  rw [hinv, hrpow] at hbound
  have hright_le : C * (1 + A) ≤ (A / 2) * (1 + A) :=
    mul_le_mul_of_nonneg_right hC_le (by linarith [hA_pos])
  have hhalf_lt : (A / 2) * (1 + A) < A ^ 2 := by
    nlinarith [hA_gt_one]
  have hcontr : A ^ 2 < A ^ 2 :=
    lt_of_le_of_lt hbound (lt_of_le_of_lt hright_le hhalf_lt)
  exact (lt_irrefl _) hcontr

/-! ### Fractional semigroup multiplier estimates -/

/-- Elementary bound used for fractional time regularity:
`1 - exp(-x) ≤ x` on the nonnegative half-line. -/
theorem one_sub_exp_neg_le_self (x : ℝ) :
    1 - Real.exp (-x) ≤ x := by
  have h := Real.add_one_le_exp (-x)
  linarith

/-- For `0 < σ ≤ 1`, the heat multiplier difference is bounded by the
fractional power of the time-frequency product. -/
theorem abs_exp_neg_sub_one_le_rpow
    {x sigma : ℝ} (hx : 0 ≤ x) (hsigma_pos : 0 < sigma)
    (hsigma_le : sigma ≤ 1) :
    |Real.exp (-x) - 1| ≤ x ^ sigma := by
  have hexp_le_one : Real.exp (-x) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  rw [abs_of_nonpos (sub_nonpos.mpr hexp_le_one)]
  by_cases hx_le_one : x ≤ 1
  · have hbasic : 1 - Real.exp (-x) ≤ x :=
      one_sub_exp_neg_le_self x
    have hx_pow : x ≤ x ^ sigma := by
      have hpow : x ^ (1 : ℝ) ≤ x ^ sigma :=
        Real.rpow_le_rpow_of_exponent_ge' hx hx_le_one
          (le_of_lt hsigma_pos) hsigma_le
      simpa [Real.rpow_one] using hpow
    have hneg : -(Real.exp (-x) - 1) = 1 - Real.exp (-x) := by ring
    rw [hneg]
    exact hbasic.trans hx_pow
  · have hone_le_x : 1 ≤ x := le_of_not_ge hx_le_one
    have hone_le_pow : 1 ≤ x ^ sigma :=
      Real.one_le_rpow hone_le_x (le_of_lt hsigma_pos)
    have hdiff_le_one : 1 - Real.exp (-x) ≤ 1 := by
      have hnonneg : 0 ≤ Real.exp (-x) := Real.exp_nonneg _
      linarith
    have hneg : -(Real.exp (-x) - 1) = 1 - Real.exp (-x) := by ring
    rw [hneg]
    exact hdiff_le_one.trans hone_le_pow

/-- Rescaled form of `abs_exp_neg_sub_one_le_rpow`, suitable for spectral
coefficients with eigenvalue `λ`. -/
theorem heat_time_multiplier_difference_le_fractional
    {lambda t sigma : ℝ} (hlambda : 0 ≤ lambda) (ht : 0 < t)
    (hsigma_pos : 0 < sigma) (hsigma_le : sigma ≤ 1) :
    |Real.exp (-(t * lambda)) - 1| ≤ t ^ sigma * lambda ^ sigma := by
  have htl_nonneg : 0 ≤ t * lambda := mul_nonneg (le_of_lt ht) hlambda
  have h :=
    abs_exp_neg_sub_one_le_rpow
      (x := t * lambda) (sigma := sigma) htl_nonneg
      hsigma_pos hsigma_le
  rwa [Real.mul_rpow (le_of_lt ht) hlambda] at h

/-- The endpoint analytic-semigroup multiplier bound on `0 ≤ σ ≤ 1`. -/
theorem rpow_mul_exp_neg_le_one_of_le_one
    {x sigma : ℝ} (hx : 0 < x) (hsigma_nonneg : 0 ≤ sigma)
    (hsigma_le : sigma ≤ 1) :
    x ^ sigma * Real.exp (-x) ≤ 1 := by
  by_cases hx_le_one : x ≤ 1
  · have hpow : x ^ sigma ≤ 1 :=
      Real.rpow_le_one (le_of_lt hx) hx_le_one hsigma_nonneg
    have hexp : Real.exp (-x) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    exact mul_le_one₀ hpow (Real.exp_nonneg _) hexp
  · have hone_le_x : 1 ≤ x := le_of_not_ge hx_le_one
    have hpow : x ^ sigma ≤ x := by
      simpa using
        Real.rpow_le_rpow_of_exponent_le hone_le_x hsigma_le
    have hprod : x ^ sigma * Real.exp (-x) ≤ x * Real.exp (-x) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
    have hte : x * Real.exp (-x) ≤ Real.exp (-1) :=
      Real.mul_exp_neg_le_exp_neg_one x
    have he1 : Real.exp (-1 : ℝ) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by norm_num)
    exact hprod.trans (hte.trans he1)

/-- Equivalent decay form of `rpow_mul_exp_neg_le_one_of_le_one`. -/
theorem exp_neg_le_rpow_neg_of_le_one
    {x sigma : ℝ} (hx : 0 < x) (hsigma_nonneg : 0 ≤ sigma)
    (hsigma_le : sigma ≤ 1) :
    Real.exp (-x) ≤ x ^ (-sigma) := by
  have hmul :=
    rpow_mul_exp_neg_le_one_of_le_one
      (x := x) (sigma := sigma) hx hsigma_nonneg hsigma_le
  have hxpow_pos : 0 < x ^ sigma :=
    Real.rpow_pos_of_pos hx sigma
  rw [Real.rpow_neg (le_of_lt hx)]
  have h' : Real.exp (-x) ≤ (1 : ℝ) * (x ^ sigma)⁻¹ := by
    exact (le_mul_inv_iff₀ hxpow_pos).mpr
      (by simpa [mul_comm] using hmul)
  simpa using h'

/-- Spectral smoothing multiplier:
`λ^σ exp(-tλ) ≤ t^{-σ}` for positive `t, λ` and `0 ≤ σ ≤ 1`. -/
theorem heat_time_multiplier_smoothing_le
    {lambda t sigma : ℝ} (hlambda : 0 < lambda) (ht : 0 < t)
    (hsigma_nonneg : 0 ≤ sigma) (hsigma_le : sigma ≤ 1) :
    lambda ^ sigma * Real.exp (-(t * lambda)) ≤ t ^ (-sigma) := by
  have htl_pos : 0 < t * lambda := mul_pos ht hlambda
  have hmul :=
    rpow_mul_exp_neg_le_one_of_le_one
      (x := t * lambda) (sigma := sigma) htl_pos
      hsigma_nonneg hsigma_le
  rw [Real.mul_rpow (le_of_lt ht) (le_of_lt hlambda)] at hmul
  have htspow_pos : 0 < t ^ sigma :=
    Real.rpow_pos_of_pos ht sigma
  rw [Real.rpow_neg (le_of_lt ht)]
  have h' :
      lambda ^ sigma * Real.exp (-(t * lambda)) ≤
        (1 : ℝ) * (t ^ sigma)⁻¹ := by
    exact (le_mul_inv_iff₀ htspow_pos).mpr
      (by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmul)
  simpa using h'

/-! ### Finite spectral-coefficient consequences -/

/-- Single-coefficient form of the fractional `S(t)-I` multiplier estimate. -/
theorem spectralCoeff_heat_difference_sq_le
    {lambda t sigma : ℝ} {a : ℂ}
    (hlambda : 0 ≤ lambda) (ht : 0 < t)
    (hsigma_pos : 0 < sigma) (hsigma_le : sigma ≤ 1) :
    ‖(((Real.exp (-(t * lambda)) - 1 : ℝ) : ℂ) * a)‖ ^ 2 ≤
      ((t ^ sigma * lambda ^ sigma) ^ 2) * ‖a‖ ^ 2 := by
  have habs :=
    heat_time_multiplier_difference_le_fractional
      (lambda := lambda) (t := t) (sigma := sigma)
      hlambda ht hsigma_pos hsigma_le
  have hscale_nonneg : 0 ≤ t ^ sigma * lambda ^ sigma := by
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _)
      (Real.rpow_nonneg hlambda _)
  have hnorm_nonneg : 0 ≤ ‖a‖ := norm_nonneg a
  have hmul :
      |Real.exp (-(t * lambda)) - 1| * ‖a‖ ≤
        (t ^ sigma * lambda ^ sigma) * ‖a‖ :=
    mul_le_mul_of_nonneg_right habs hnorm_nonneg
  have hlhs_nonneg :
      0 ≤ |Real.exp (-(t * lambda)) - 1| * ‖a‖ :=
    mul_nonneg (abs_nonneg _) hnorm_nonneg
  have hrhs_nonneg :
      0 ≤ (t ^ sigma * lambda ^ sigma) * ‖a‖ :=
    mul_nonneg hscale_nonneg hnorm_nonneg
  calc
    ‖(((Real.exp (-(t * lambda)) - 1 : ℝ) : ℂ) * a)‖ ^ 2
        =
          (|Real.exp (-(t * lambda)) - 1| * ‖a‖) ^ 2 := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ((t ^ sigma * lambda ^ sigma) * ‖a‖) ^ 2 := by
            nlinarith
    _ = ((t ^ sigma * lambda ^ sigma) ^ 2) * ‖a‖ ^ 2 := by
            ring

/-- Finite-mode coefficient-energy form of the fractional `S(t)-I`
estimate for the unit-interval Neumann spectrum. -/
theorem finiteSpectralCoeff_heat_difference_energy_le
    (s : Finset ℕ) {t sigma : ℝ} (a : ℕ → ℂ)
    (ht : 0 < t) (hsigma_pos : 0 < sigma) (hsigma_le : sigma ≤ 1) :
    (∑ n ∈ s,
        ‖(((Real.exp (-(t * unitIntervalCosineEigenvalue n)) - 1 : ℝ) : ℂ) *
          a n)‖ ^ 2) ≤
      (t ^ sigma) ^ 2 *
        ∑ n ∈ s,
          (unitIntervalCosineEigenvalue n ^ sigma) ^ 2 * ‖a n‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro n _hn
  have hlambda : 0 ≤ unitIntervalCosineEigenvalue n := by
    dsimp [unitIntervalCosineEigenvalue]
    positivity
  have hterm :=
    spectralCoeff_heat_difference_sq_le
      (lambda := unitIntervalCosineEigenvalue n) (t := t)
      (sigma := sigma) (a := a n)
      hlambda ht hsigma_pos hsigma_le
  calc
    ‖(((Real.exp (-(t * unitIntervalCosineEigenvalue n)) - 1 : ℝ) : ℂ) *
          a n)‖ ^ 2
        ≤
          ((t ^ sigma * unitIntervalCosineEigenvalue n ^ sigma) ^ 2) *
            ‖a n‖ ^ 2 :=
            hterm
    _ =
          (t ^ sigma) ^ 2 *
            ((unitIntervalCosineEigenvalue n ^ sigma) ^ 2 *
              ‖a n‖ ^ 2) := by
            ring

/-- Single-coefficient form of the spectral smoothing multiplier estimate. -/
theorem spectralCoeff_heat_smoothing_sq_le
    {lambda t sigma : ℝ} {a : ℂ}
    (hlambda : 0 < lambda) (ht : 0 < t)
    (hsigma_nonneg : 0 ≤ sigma) (hsigma_le : sigma ≤ 1) :
    (lambda ^ sigma) ^ 2 *
        ‖(((Real.exp (-(t * lambda)) : ℝ) : ℂ) * a)‖ ^ 2 ≤
      (t ^ (-sigma)) ^ 2 * ‖a‖ ^ 2 := by
  have hmul :=
    heat_time_multiplier_smoothing_le
      (lambda := lambda) (t := t) (sigma := sigma)
      hlambda ht hsigma_nonneg hsigma_le
  have hnorm_nonneg : 0 ≤ ‖a‖ := norm_nonneg a
  have hmul_norm :
      (lambda ^ sigma * Real.exp (-(t * lambda))) * ‖a‖ ≤
        t ^ (-sigma) * ‖a‖ :=
    mul_le_mul_of_nonneg_right hmul hnorm_nonneg
  have hlambda_pow_nonneg : 0 ≤ lambda ^ sigma :=
    Real.rpow_nonneg (le_of_lt hlambda) _
  have hexp_nonneg : 0 ≤ Real.exp (-(t * lambda)) :=
    Real.exp_nonneg _
  have hleft_nonneg :
      0 ≤ (lambda ^ sigma * Real.exp (-(t * lambda))) * ‖a‖ :=
    mul_nonneg (mul_nonneg hlambda_pow_nonneg hexp_nonneg) hnorm_nonneg
  have hright_nonneg : 0 ≤ t ^ (-sigma) * ‖a‖ :=
    mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) hnorm_nonneg
  calc
    (lambda ^ sigma) ^ 2 *
        ‖(((Real.exp (-(t * lambda)) : ℝ) : ℂ) * a)‖ ^ 2
        =
          ((lambda ^ sigma * Real.exp (-(t * lambda))) * ‖a‖) ^ 2 := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hexp_nonneg]
            ring
    _ ≤ (t ^ (-sigma) * ‖a‖) ^ 2 := by
            nlinarith
    _ = (t ^ (-sigma)) ^ 2 * ‖a‖ ^ 2 := by
            ring

/-- Finite-mode coefficient-energy form of `A^σ e^{-tA}` smoothing over
nonzero Neumann modes. -/
theorem finiteSpectralCoeff_heat_smoothing_energy_le
    (s : Finset ℕ) {t sigma : ℝ} (a : ℕ → ℂ)
    (ht : 0 < t) (hsigma_nonneg : 0 ≤ sigma) (hsigma_le : sigma ≤ 1)
    (hs_nonzero : ∀ n ∈ s, n ≠ 0) :
    (∑ n ∈ s,
        (unitIntervalCosineEigenvalue n ^ sigma) ^ 2 *
          ‖(((Real.exp (-(t * unitIntervalCosineEigenvalue n)) : ℝ) : ℂ) *
            a n)‖ ^ 2) ≤
      (t ^ (-sigma)) ^ 2 * ∑ n ∈ s, ‖a n‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro n hn
  have hn0 : n ≠ 0 := hs_nonzero n hn
  have hn_pos_real : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn0
  have hlambda_pos : 0 < unitIntervalCosineEigenvalue n := by
    dsimp [unitIntervalCosineEigenvalue]
    positivity
  exact
    spectralCoeff_heat_smoothing_sq_le
      (lambda := unitIntervalCosineEigenvalue n) (t := t)
      (sigma := sigma) (a := a n)
      hlambda_pos ht hsigma_nonneg hsigma_le

/-! ### Infinite coefficient-energy estimates with explicit domain hypotheses -/

/-- Spectral fractional coefficient energy for the unit-interval Neumann
cosine spectrum.  The value is meaningful when the displayed series is
summable; the theorems below keep that summability hypothesis explicit. -/
def spectralCoeffFractionalEnergy (sigma : ℝ) (a : ℕ → ℂ) : ℝ :=
  ∑' n : ℕ,
    (unitIntervalCosineEigenvalue n ^ sigma) ^ 2 * ‖a n‖ ^ 2

/-- The unweighted coefficient `ℓ²` energy. -/
def spectralCoeffL2Energy (a : ℕ → ℂ) : ℝ :=
  ∑' n : ℕ, ‖a n‖ ^ 2

/-- Square-root form of the spectral fractional coefficient energy. -/
def spectralCoeffFractionalNorm (sigma : ℝ) (a : ℕ → ℂ) : ℝ :=
  Real.sqrt (spectralCoeffFractionalEnergy sigma a)

/-- Square-root form of the unweighted coefficient `ℓ²` energy. -/
def spectralCoeffL2Norm (a : ℕ → ℂ) : ℝ :=
  Real.sqrt (spectralCoeffL2Energy a)

/-- Fractional coefficient energy is nonnegative. -/
theorem spectralCoeffFractionalEnergy_nonneg
    (sigma : ℝ) (a : ℕ → ℂ) :
    0 ≤ spectralCoeffFractionalEnergy sigma a := by
  exact tsum_nonneg fun n => mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- Unweighted coefficient `ℓ²` energy is nonnegative. -/
theorem spectralCoeffL2Energy_nonneg (a : ℕ → ℂ) :
    0 ≤ spectralCoeffL2Energy a := by
  exact tsum_nonneg fun n => sq_nonneg _

/-- Under finite fractional coefficient energy, the coefficient series for
`S(t)-I` is summable. -/
theorem spectralCoeff_heat_difference_sq_summable
    {t sigma : ℝ} (a : ℕ → ℂ)
    (ht : 0 < t) (hsigma_pos : 0 < sigma) (hsigma_le : sigma ≤ 1)
    (henergy :
      Summable fun n : ℕ =>
        (unitIntervalCosineEigenvalue n ^ sigma) ^ 2 * ‖a n‖ ^ 2) :
    Summable fun n : ℕ =>
      ‖(((Real.exp (-(t * unitIntervalCosineEigenvalue n)) - 1 : ℝ) : ℂ) *
        a n)‖ ^ 2 := by
  apply Summable.of_nonneg_of_le
    (fun n => sq_nonneg _)
    ?_
    (henergy.mul_left ((t ^ sigma) ^ 2))
  intro n
  have hlambda : 0 ≤ unitIntervalCosineEigenvalue n := by
    dsimp [unitIntervalCosineEigenvalue]
    positivity
  have hterm :=
    spectralCoeff_heat_difference_sq_le
      (lambda := unitIntervalCosineEigenvalue n) (t := t)
      (sigma := sigma) (a := a n)
      hlambda ht hsigma_pos hsigma_le
  calc
    ‖(((Real.exp (-(t * unitIntervalCosineEigenvalue n)) - 1 : ℝ) : ℂ) *
        a n)‖ ^ 2
        ≤
          ((t ^ sigma * unitIntervalCosineEigenvalue n ^ sigma) ^ 2) *
            ‖a n‖ ^ 2 :=
            hterm
    _ =
          (t ^ sigma) ^ 2 *
            ((unitIntervalCosineEigenvalue n ^ sigma) ^ 2 *
              ‖a n‖ ^ 2) := by
            ring

/-- Infinite-series coefficient-energy form of the fractional `S(t)-I`
estimate. -/
theorem spectralCoeff_heat_difference_tsum_le
    {t sigma : ℝ} (a : ℕ → ℂ)
    (ht : 0 < t) (hsigma_pos : 0 < sigma) (hsigma_le : sigma ≤ 1)
    (henergy :
      Summable fun n : ℕ =>
        (unitIntervalCosineEigenvalue n ^ sigma) ^ 2 * ‖a n‖ ^ 2) :
    (∑' n : ℕ,
      ‖(((Real.exp (-(t * unitIntervalCosineEigenvalue n)) - 1 : ℝ) : ℂ) *
        a n)‖ ^ 2) ≤
      (t ^ sigma) ^ 2 * spectralCoeffFractionalEnergy sigma a := by
  have hdiff :=
    spectralCoeff_heat_difference_sq_summable
      (a := a) ht hsigma_pos hsigma_le henergy
  have hmajor :
      Summable fun n : ℕ =>
        (t ^ sigma) ^ 2 *
          ((unitIntervalCosineEigenvalue n ^ sigma) ^ 2 *
            ‖a n‖ ^ 2) :=
    henergy.mul_left ((t ^ sigma) ^ 2)
  have hle :
      ∀ n : ℕ,
        ‖(((Real.exp (-(t * unitIntervalCosineEigenvalue n)) - 1 : ℝ) : ℂ) *
          a n)‖ ^ 2 ≤
          (t ^ sigma) ^ 2 *
            ((unitIntervalCosineEigenvalue n ^ sigma) ^ 2 *
              ‖a n‖ ^ 2) := by
    intro n
    have hlambda : 0 ≤ unitIntervalCosineEigenvalue n := by
      dsimp [unitIntervalCosineEigenvalue]
      positivity
    have hterm :=
      spectralCoeff_heat_difference_sq_le
        (lambda := unitIntervalCosineEigenvalue n) (t := t)
        (sigma := sigma) (a := a n)
        hlambda ht hsigma_pos hsigma_le
    calc
      ‖(((Real.exp (-(t * unitIntervalCosineEigenvalue n)) - 1 : ℝ) : ℂ) *
          a n)‖ ^ 2
          ≤
            ((t ^ sigma * unitIntervalCosineEigenvalue n ^ sigma) ^ 2) *
              ‖a n‖ ^ 2 :=
              hterm
      _ =
            (t ^ sigma) ^ 2 *
              ((unitIntervalCosineEigenvalue n ^ sigma) ^ 2 *
                ‖a n‖ ^ 2) := by
              ring
  have htsum := hdiff.tsum_le_tsum hle hmajor
  simpa [spectralCoeffFractionalEnergy, henergy.tsum_mul_left] using htsum

/-- Smoothing multiplier estimate with a zero-eigenvalue case split, for
positive fractional exponent. -/
theorem spectralCoeff_heat_smoothing_sq_le_of_nonneg
    {lambda t sigma : ℝ} {a : ℂ}
    (hlambda : 0 ≤ lambda) (ht : 0 < t)
    (hsigma_pos : 0 < sigma) (hsigma_le : sigma ≤ 1) :
    (lambda ^ sigma) ^ 2 *
        ‖(((Real.exp (-(t * lambda)) : ℝ) : ℂ) * a)‖ ^ 2 ≤
      (t ^ (-sigma)) ^ 2 * ‖a‖ ^ 2 := by
  by_cases hzero : lambda = 0
  · subst lambda
    have hz : (0 : ℝ) ^ sigma = 0 :=
      Real.zero_rpow (ne_of_gt hsigma_pos)
    have hright_nonneg :
        0 ≤ (t ^ (-sigma)) ^ 2 * ‖a‖ ^ 2 := by
      exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    simpa [hz] using hright_nonneg
  · have hlambda_pos : 0 < lambda := lt_of_le_of_ne hlambda (Ne.symm hzero)
    exact spectralCoeff_heat_smoothing_sq_le
      (lambda := lambda) (t := t) (sigma := sigma) (a := a)
      hlambda_pos ht (le_of_lt hsigma_pos) hsigma_le

/-- Under finite `ℓ²` coefficient energy, the smoothed fractional coefficient
series is summable. -/
theorem spectralCoeff_heat_smoothing_sq_summable
    {t sigma : ℝ} (a : ℕ → ℂ)
    (ht : 0 < t) (hsigma_pos : 0 < sigma) (hsigma_le : sigma ≤ 1)
    (hcoeff : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    Summable fun n : ℕ =>
      (unitIntervalCosineEigenvalue n ^ sigma) ^ 2 *
        ‖(((Real.exp (-(t * unitIntervalCosineEigenvalue n)) : ℝ) : ℂ) *
          a n)‖ ^ 2 := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    ?_
    (hcoeff.mul_left ((t ^ (-sigma)) ^ 2))
  intro n
  have hlambda : 0 ≤ unitIntervalCosineEigenvalue n := by
    dsimp [unitIntervalCosineEigenvalue]
    positivity
  exact spectralCoeff_heat_smoothing_sq_le_of_nonneg
    (lambda := unitIntervalCosineEigenvalue n) (t := t)
    (sigma := sigma) (a := a n)
    hlambda ht hsigma_pos hsigma_le

/-- Infinite-series coefficient-energy form of `A^σ e^{-tA}` smoothing. -/
theorem spectralCoeff_heat_smoothing_tsum_le
    {t sigma : ℝ} (a : ℕ → ℂ)
    (ht : 0 < t) (hsigma_pos : 0 < sigma) (hsigma_le : sigma ≤ 1)
    (hcoeff : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    (∑' n : ℕ,
      (unitIntervalCosineEigenvalue n ^ sigma) ^ 2 *
        ‖(((Real.exp (-(t * unitIntervalCosineEigenvalue n)) : ℝ) : ℂ) *
          a n)‖ ^ 2) ≤
      (t ^ (-sigma)) ^ 2 * spectralCoeffL2Energy a := by
  have hsmooth :=
    spectralCoeff_heat_smoothing_sq_summable
      (a := a) ht hsigma_pos hsigma_le hcoeff
  have hmajor :
      Summable fun n : ℕ => (t ^ (-sigma)) ^ 2 * ‖a n‖ ^ 2 :=
    hcoeff.mul_left ((t ^ (-sigma)) ^ 2)
  have hle :
      ∀ n : ℕ,
        (unitIntervalCosineEigenvalue n ^ sigma) ^ 2 *
          ‖(((Real.exp (-(t * unitIntervalCosineEigenvalue n)) : ℝ) : ℂ) *
            a n)‖ ^ 2 ≤
          (t ^ (-sigma)) ^ 2 * ‖a n‖ ^ 2 := by
    intro n
    have hlambda : 0 ≤ unitIntervalCosineEigenvalue n := by
      dsimp [unitIntervalCosineEigenvalue]
      positivity
    exact spectralCoeff_heat_smoothing_sq_le_of_nonneg
      (lambda := unitIntervalCosineEigenvalue n) (t := t)
      (sigma := sigma) (a := a n)
      hlambda ht hsigma_pos hsigma_le
  have htsum := hsmooth.tsum_le_tsum hle hmajor
  simpa [spectralCoeffL2Energy, hcoeff.tsum_mul_left] using htsum

/-! ### Hilbert-basis coefficient bridge for finite sums -/

/-- The complex `L²` representative of an interval-domain real function,
through the existing zero-extension to the unit interval. -/
def intervalDomainLiftComplexLp2
    (u : intervalDomain.Point → ℝ)
    (hu : MemLp (intervalDomainLift u) (2 : ℝ≥0∞) (intervalMeasure 1)) :
    Lp ℂ 2 (intervalMeasure 1) :=
  (hu.ofReal).toLp (fun x : ℝ => (intervalDomainLift u x : ℂ))

/-- Finite Bessel inequality for the complete Neumann cosine Hilbert basis. -/
theorem unitIntervalCosineHilbertCoeff_finite_sq_le_norm_sq
    (s : Finset ℕ) (v : Lp ℂ 2 (intervalMeasure 1)) :
    (∑ n ∈ s, ‖unitIntervalCosineHilbertBasis.repr v n‖ ^ 2) ≤
      ‖v‖ ^ 2 := by
  have h :=
    (unitIntervalCosineHilbertBasis.orthonormal).sum_inner_products_le
      (x := v) (s := s)
  simpa [HilbertBasis.repr_apply_apply] using h

/-- The finite cosine-coefficient square sum of an interval-domain input is
controlled by its concrete `L²` seminorm. -/
theorem intervalDomainCosineHilbertCoeff_finite_sq_le_lpNorm_sq
    (s : Finset ℕ) (u : intervalDomain.Point → ℝ)
    (hu : MemLp (intervalDomainLift u) (2 : ℝ≥0∞) (intervalMeasure 1)) :
    (∑ n ∈ s,
        ‖unitIntervalCosineHilbertBasis.repr
          (intervalDomainLiftComplexLp2 u hu) n‖ ^ 2) ≤
      intervalDomainLpNorm 2 u ^ 2 := by
  have hbase :=
    unitIntervalCosineHilbertCoeff_finite_sq_le_norm_sq
      s (intervalDomainLiftComplexLp2 u hu)
  have hnorm :
      ‖intervalDomainLiftComplexLp2 u hu‖ =
        intervalDomainLpNorm 2 u := by
    calc
      ‖intervalDomainLiftComplexLp2 u hu‖
          =
            lpNorm (fun x : ℝ => (intervalDomainLift u x : ℂ))
              (2 : ℝ≥0∞) (intervalMeasure 1) := by
              rw [intervalDomainLiftComplexLp2, Lp.norm_toLp,
                toReal_eLpNorm (hu.ofReal).aestronglyMeasurable]
      _ =
            lpNorm (intervalDomainLift u)
              (2 : ℝ≥0∞) (intervalMeasure 1) :=
              unitInterval_lpNorm_complex_ofReal_eq hu
      _ = intervalDomainLpNorm 2 u := by
              simp [intervalDomainLpNorm]
  rwa [hnorm] at hbase

/-! ### L² coefficient model for the cosine Hilbert basis -/

/-- Package an explicitly square-summable coefficient sequence as an `ℓ²`
sequence. -/
def cosineCoeffLp2 (a : ℕ → ℂ)
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) : ℓ²(ℕ, ℂ) := by
  refine ⟨a, ?_⟩
  change Memℓp (a : PreLp (fun _ : ℕ => ℂ)) (2 : ℝ≥0∞)
  simpa [Memℓp] using ha

/-- The `ℓ²` norm of packaged coefficients is the coefficient energy. -/
theorem cosineCoeffLp2_norm_sq
    (a : ℕ → ℂ) (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    ‖cosineCoeffLp2 a ha‖ ^ 2 = spectralCoeffL2Energy a := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have h :=
    lp.norm_rpow_eq_tsum (E := fun _ : ℕ => ℂ)
      (p := (2 : ℝ≥0∞)) hp (cosineCoeffLp2 a ha)
  simpa [spectralCoeffL2Energy] using h

/-- Reconstruct an interval `L²` vector from square-summable normalized cosine
coefficients. -/
def unitIntervalCosineLpFromCoeffs
    (a : ℕ → ℂ) (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    Lp ℂ 2 (intervalMeasure 1) :=
  unitIntervalCosineHilbertBasis.repr.symm (cosineCoeffLp2 a ha)

/-- The Hilbert-basis reconstruction preserves the coefficient `ℓ²` energy. -/
theorem unitIntervalCosineLpFromCoeffs_norm_sq
    (a : ℕ → ℂ) (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    ‖unitIntervalCosineLpFromCoeffs a ha‖ ^ 2 =
      spectralCoeffL2Energy a := by
  simp [unitIntervalCosineLpFromCoeffs, cosineCoeffLp2_norm_sq]

/-- The cosine Hilbert-basis coefficient sequence of any interval `L²` vector
is square-summable. -/
theorem unitIntervalCosineHilbertBasis_repr_l2_summable
    (v : Lp ℂ 2 (intervalMeasure 1)) :
    Summable fun n : ℕ => ‖unitIntervalCosineHilbertBasis.repr v n‖ ^ 2 := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have h := (unitIntervalCosineHilbertBasis.repr v).2.summable hp
  simpa using h

/-- Reconstructing from the cosine Hilbert-basis coefficients of an interval
`L²` vector returns the original vector. -/
theorem unitIntervalCosineLpFromRepr_eq
    (v : Lp ℂ 2 (intervalMeasure 1)) :
    unitIntervalCosineLpFromCoeffs
      (fun n : ℕ => unitIntervalCosineHilbertBasis.repr v n)
      (unitIntervalCosineHilbertBasis_repr_l2_summable v) = v := by
  simp [unitIntervalCosineLpFromCoeffs, cosineCoeffLp2]

/-- Parseval identity for the complete unit-interval cosine Hilbert basis, in
the coefficient-energy notation used by this file. -/
theorem unitIntervalCosineHilbertBasis_repr_energy_eq_norm_sq
    (v : Lp ℂ 2 (intervalMeasure 1)) :
    spectralCoeffL2Energy
        (fun n : ℕ => unitIntervalCosineHilbertBasis.repr v n) =
      ‖v‖ ^ 2 := by
  have h :=
    unitIntervalCosineLpFromCoeffs_norm_sq
      (fun n : ℕ => unitIntervalCosineHilbertBasis.repr v n)
      (unitIntervalCosineHilbertBasis_repr_l2_summable v)
  rw [unitIntervalCosineLpFromRepr_eq] at h
  exact h.symm

/-- Parseval identity for an interval-domain real input after lifting it into
the complex unit-interval `L²` space. -/
theorem intervalDomainCosineHilbertCoeff_l2_energy_eq_lpNorm_sq
    (u : intervalDomain.Point → ℝ)
    (hu : MemLp (intervalDomainLift u) (2 : ℝ≥0∞) (intervalMeasure 1)) :
    spectralCoeffL2Energy
        (fun n : ℕ => unitIntervalCosineHilbertBasis.repr
          (intervalDomainLiftComplexLp2 u hu) n) =
      intervalDomainLpNorm 2 u ^ 2 := by
  have henergy :=
    unitIntervalCosineHilbertBasis_repr_energy_eq_norm_sq
      (intervalDomainLiftComplexLp2 u hu)
  have hnorm :
      ‖intervalDomainLiftComplexLp2 u hu‖ =
        intervalDomainLpNorm 2 u := by
    calc
      ‖intervalDomainLiftComplexLp2 u hu‖
          =
            lpNorm (fun x : ℝ => (intervalDomainLift u x : ℂ))
              (2 : ℝ≥0∞) (intervalMeasure 1) := by
              rw [intervalDomainLiftComplexLp2, Lp.norm_toLp,
                toReal_eLpNorm (hu.ofReal).aestronglyMeasurable]
      _ =
            lpNorm (intervalDomainLift u)
              (2 : ℝ≥0∞) (intervalMeasure 1) :=
              unitInterval_lpNorm_complex_ofReal_eq hu
      _ = intervalDomainLpNorm 2 u := by
              simp [intervalDomainLpNorm]
  rwa [hnorm] at henergy

/-- The Hilbert-basis reconstruction has the prescribed normalized cosine
coefficients. -/
theorem unitIntervalCosineLpFromCoeffs_repr
    (a : ℕ → ℂ) (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) (n : ℕ) :
    unitIntervalCosineHilbertBasis.repr
        (unitIntervalCosineLpFromCoeffs a ha) n = a n := by
  simp [unitIntervalCosineLpFromCoeffs, cosineCoeffLp2]

/-- Spectral heat multiplier on normalized cosine coefficients. -/
def spectralHeatCoeff (t : ℝ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  (Real.exp (-(t * unitIntervalCosineEigenvalue n)) : ℂ) * a n

/-- Spectral heat multiplier difference on normalized cosine coefficients. -/
def spectralHeatDifferenceCoeff (t : ℝ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  ((Real.exp (-(t * unitIntervalCosineEigenvalue n)) - 1 : ℝ) : ℂ) * a n

/-- Fractional heat multiplier on normalized cosine coefficients. -/
def spectralFractionalHeatCoeff
    (sigma t : ℝ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  (((unitIntervalCosineEigenvalue n ^ sigma) *
      Real.exp (-(t * unitIntervalCosineEigenvalue n)) : ℝ) : ℂ) * a n

/-- The spectral heat multiplier is an `ℓ²` contraction at the coefficient
level. -/
theorem spectralHeatCoeff_l2_summable
    {t : ℝ} (ht : 0 ≤ t) (a : ℕ → ℂ)
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    Summable fun n : ℕ => ‖spectralHeatCoeff t a n‖ ^ 2 := by
  apply Summable.of_nonneg_of_le
    (fun n => sq_nonneg _)
    ?_
    ha
  intro n
  have hlambda : 0 ≤ unitIntervalCosineEigenvalue n := by
    dsimp [unitIntervalCosineEigenvalue]
    positivity
  have htl : 0 ≤ t * unitIntervalCosineEigenvalue n :=
    mul_nonneg ht hlambda
  have hexp_nonneg :
      0 ≤ Real.exp (-(t * unitIntervalCosineEigenvalue n)) :=
    Real.exp_nonneg _
  have hexp_le_one :
      Real.exp (-(t * unitIntervalCosineEigenvalue n)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hnorm_nonneg : 0 ≤ ‖a n‖ := norm_nonneg _
  have hmul :
      Real.exp (-(t * unitIntervalCosineEigenvalue n)) * ‖a n‖ ≤
        1 * ‖a n‖ :=
    mul_le_mul_of_nonneg_right hexp_le_one hnorm_nonneg
  have hleft_nonneg :
      0 ≤ Real.exp (-(t * unitIntervalCosineEigenvalue n)) * ‖a n‖ :=
    mul_nonneg hexp_nonneg hnorm_nonneg
  calc
    ‖spectralHeatCoeff t a n‖ ^ 2
        =
          (Real.exp (-(t * unitIntervalCosineEigenvalue n)) * ‖a n‖) ^ 2 := by
            rw [spectralHeatCoeff, norm_mul, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg hexp_nonneg]
    _ ≤ ‖a n‖ ^ 2 := by
            nlinarith

/-- The interval `L²` spectral heat vector reconstructed from coefficients. -/
def unitIntervalCosineHeatLpFromCoeffs
    {t : ℝ} (ht : 0 ≤ t) (a : ℕ → ℂ)
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    Lp ℂ 2 (intervalMeasure 1) :=
  unitIntervalCosineLpFromCoeffs
    (spectralHeatCoeff t a)
    (spectralHeatCoeff_l2_summable ht a ha)

/-- The reconstructed heat vector has exactly the damped coefficient energy. -/
theorem unitIntervalCosineHeatLpFromCoeffs_norm_sq
    {t : ℝ} (ht : 0 ≤ t) (a : ℕ → ℂ)
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    ‖unitIntervalCosineHeatLpFromCoeffs ht a ha‖ ^ 2 =
      spectralCoeffL2Energy (spectralHeatCoeff t a) := by
  simp [unitIntervalCosineHeatLpFromCoeffs,
    unitIntervalCosineLpFromCoeffs_norm_sq]

/-- Coefficients of the reconstructed interval `L²` spectral heat vector are
exactly the damped coefficients. -/
theorem unitIntervalCosineHeatLpFromCoeffs_repr
    {t : ℝ} (ht : 0 ≤ t) (a : ℕ → ℂ)
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) (n : ℕ) :
    unitIntervalCosineHilbertBasis.repr
        (unitIntervalCosineHeatLpFromCoeffs ht a ha) n =
      spectralHeatCoeff t a n := by
  exact unitIntervalCosineLpFromCoeffs_repr
    (spectralHeatCoeff t a)
    (spectralHeatCoeff_l2_summable ht a ha) n

/-! ### L² spectral fractional estimates as actual interval `Lp` vectors -/

/-- The heat-difference coefficient sequence is square-summable under finite
fractional coefficient energy. -/
theorem spectralHeatDifferenceCoeff_l2_summable
    {t sigma : ℝ} (a : ℕ → ℂ)
    (ht : 0 < t) (hsigma_pos : 0 < sigma) (hsigma_le : sigma ≤ 1)
    (henergy :
      Summable fun n : ℕ =>
        (unitIntervalCosineEigenvalue n ^ sigma) ^ 2 * ‖a n‖ ^ 2) :
    Summable fun n : ℕ => ‖spectralHeatDifferenceCoeff t a n‖ ^ 2 := by
  simpa [spectralHeatDifferenceCoeff] using
    spectralCoeff_heat_difference_sq_summable
      (a := a) ht hsigma_pos hsigma_le henergy

/-- Reconstructed interval `L²` vector for the spectral difference
`S(t) - I`. -/
def unitIntervalCosineHeatDifferenceLpFromCoeffs
    {t sigma : ℝ} (a : ℕ → ℂ)
    (ht : 0 < t) (hsigma_pos : 0 < sigma) (hsigma_le : sigma ≤ 1)
    (henergy :
      Summable fun n : ℕ =>
        (unitIntervalCosineEigenvalue n ^ sigma) ^ 2 * ‖a n‖ ^ 2) :
    Lp ℂ 2 (intervalMeasure 1) :=
  unitIntervalCosineLpFromCoeffs (spectralHeatDifferenceCoeff t a)
    (spectralHeatDifferenceCoeff_l2_summable
      a ht hsigma_pos hsigma_le henergy)

/-- The actual interval `L²` spectral difference satisfies the fractional
`S(t)-I` estimate, in squared norm form. -/
theorem unitIntervalCosineHeatDifferenceLpFromCoeffs_norm_sq_le
    {t sigma : ℝ} (a : ℕ → ℂ)
    (ht : 0 < t) (hsigma_pos : 0 < sigma) (hsigma_le : sigma ≤ 1)
    (henergy :
      Summable fun n : ℕ =>
        (unitIntervalCosineEigenvalue n ^ sigma) ^ 2 * ‖a n‖ ^ 2) :
    ‖unitIntervalCosineHeatDifferenceLpFromCoeffs
        a ht hsigma_pos hsigma_le henergy‖ ^ 2 ≤
      (t ^ sigma) ^ 2 * spectralCoeffFractionalEnergy sigma a := by
  rw [unitIntervalCosineHeatDifferenceLpFromCoeffs,
    unitIntervalCosineLpFromCoeffs_norm_sq]
  simpa [spectralCoeffL2Energy, spectralHeatDifferenceCoeff] using
    spectralCoeff_heat_difference_tsum_le
      (a := a) ht hsigma_pos hsigma_le henergy

/-- Non-squared interval `L²` form of the spectral fractional `S(t)-I`
estimate. -/
theorem unitIntervalCosineHeatDifferenceLpFromCoeffs_norm_le
    {t sigma : ℝ} (a : ℕ → ℂ)
    (ht : 0 < t) (hsigma_pos : 0 < sigma) (hsigma_le : sigma ≤ 1)
    (henergy :
      Summable fun n : ℕ =>
        (unitIntervalCosineEigenvalue n ^ sigma) ^ 2 * ‖a n‖ ^ 2) :
    ‖unitIntervalCosineHeatDifferenceLpFromCoeffs
        a ht hsigma_pos hsigma_le henergy‖ ≤
      t ^ sigma * spectralCoeffFractionalNorm sigma a := by
  have hsq :=
    unitIntervalCosineHeatDifferenceLpFromCoeffs_norm_sq_le
      (a := a) ht hsigma_pos hsigma_le henergy
  have henergy_nonneg := spectralCoeffFractionalEnergy_nonneg sigma a
  have hscale_nonneg : 0 ≤ t ^ sigma := Real.rpow_nonneg ht.le _
  have hright_nonneg :
      0 ≤ t ^ sigma * spectralCoeffFractionalNorm sigma a :=
    mul_nonneg hscale_nonneg (Real.sqrt_nonneg _)
  have hsq_rhs :
      (t ^ sigma) ^ 2 * spectralCoeffFractionalEnergy sigma a =
        (t ^ sigma * spectralCoeffFractionalNorm sigma a) ^ 2 := by
    rw [spectralCoeffFractionalNorm, mul_pow,
      Real.sq_sqrt henergy_nonneg]
  rw [hsq_rhs] at hsq
  exact (sq_le_sq₀ (norm_nonneg _) hright_nonneg).mp hsq

/-- The fractional heat coefficient sequence is square-summable for
square-summable input coefficients. -/
theorem spectralFractionalHeatCoeff_l2_summable
    {t sigma : ℝ} (a : ℕ → ℂ)
    (ht : 0 < t) (hsigma_pos : 0 < sigma) (hsigma_le : sigma ≤ 1)
    (hcoeff : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    Summable fun n : ℕ => ‖spectralFractionalHeatCoeff sigma t a n‖ ^ 2 := by
  have hs :=
    spectralCoeff_heat_smoothing_sq_summable
      (a := a) ht hsigma_pos hsigma_le hcoeff
  convert hs using 1
  ext n
  have hlambda : 0 ≤ unitIntervalCosineEigenvalue n := by
    dsimp [unitIntervalCosineEigenvalue]
    positivity
  have hlambda_pow_nonneg :
      0 ≤ unitIntervalCosineEigenvalue n ^ sigma :=
    Real.rpow_nonneg hlambda _
  simp only [spectralFractionalHeatCoeff, Complex.ofReal_mul,
    Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg hlambda_pow_nonneg]
  ring

/-- The energy of the fractional heat coefficients is the smoothing series
already estimated above. -/
theorem spectralFractionalHeatCoeff_energy_eq
    (sigma t : ℝ) (a : ℕ → ℂ) :
    spectralCoeffL2Energy (spectralFractionalHeatCoeff sigma t a) =
      ∑' n : ℕ,
        (unitIntervalCosineEigenvalue n ^ sigma) ^ 2 *
          ‖(((Real.exp (-(t * unitIntervalCosineEigenvalue n)) : ℝ) : ℂ) *
            a n)‖ ^ 2 := by
  unfold spectralCoeffL2Energy
  apply tsum_congr
  intro n
  have hlambda : 0 ≤ unitIntervalCosineEigenvalue n := by
    dsimp [unitIntervalCosineEigenvalue]
    positivity
  have hlambda_pow_nonneg :
      0 ≤ unitIntervalCosineEigenvalue n ^ sigma :=
    Real.rpow_nonneg hlambda _
  simp [spectralFractionalHeatCoeff, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hlambda_pow_nonneg]
  ring

/-- Reconstructed interval `L²` vector for the fractional heat output
`A^σ S(t)`. -/
def unitIntervalCosineFractionalHeatLpFromCoeffs
    {t sigma : ℝ} (a : ℕ → ℂ)
    (ht : 0 < t) (hsigma_pos : 0 < sigma) (hsigma_le : sigma ≤ 1)
    (hcoeff : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    Lp ℂ 2 (intervalMeasure 1) :=
  unitIntervalCosineLpFromCoeffs (spectralFractionalHeatCoeff sigma t a)
    (spectralFractionalHeatCoeff_l2_summable
      a ht hsigma_pos hsigma_le hcoeff)

/-- The actual interval `L²` fractional heat output satisfies the spectral
smoothing estimate, in squared norm form. -/
theorem unitIntervalCosineFractionalHeatLpFromCoeffs_norm_sq_le
    {t sigma : ℝ} (a : ℕ → ℂ)
    (ht : 0 < t) (hsigma_pos : 0 < sigma) (hsigma_le : sigma ≤ 1)
    (hcoeff : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    ‖unitIntervalCosineFractionalHeatLpFromCoeffs
        a ht hsigma_pos hsigma_le hcoeff‖ ^ 2 ≤
      (t ^ (-sigma)) ^ 2 * spectralCoeffL2Energy a := by
  rw [unitIntervalCosineFractionalHeatLpFromCoeffs,
    unitIntervalCosineLpFromCoeffs_norm_sq,
    spectralFractionalHeatCoeff_energy_eq]
  exact spectralCoeff_heat_smoothing_tsum_le
    (a := a) ht hsigma_pos hsigma_le hcoeff

/-- Non-squared interval `L²` form of the spectral fractional heat smoothing
estimate. -/
theorem unitIntervalCosineFractionalHeatLpFromCoeffs_norm_le
    {t sigma : ℝ} (a : ℕ → ℂ)
    (ht : 0 < t) (hsigma_pos : 0 < sigma) (hsigma_le : sigma ≤ 1)
    (hcoeff : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    ‖unitIntervalCosineFractionalHeatLpFromCoeffs
        a ht hsigma_pos hsigma_le hcoeff‖ ≤
      t ^ (-sigma) * spectralCoeffL2Norm a := by
  have hsq :=
    unitIntervalCosineFractionalHeatLpFromCoeffs_norm_sq_le
      (a := a) ht hsigma_pos hsigma_le hcoeff
  have henergy_nonneg := spectralCoeffL2Energy_nonneg a
  have hscale_nonneg : 0 ≤ t ^ (-sigma) := Real.rpow_nonneg ht.le _
  have hright_nonneg :
      0 ≤ t ^ (-sigma) * spectralCoeffL2Norm a :=
    mul_nonneg hscale_nonneg (Real.sqrt_nonneg _)
  have hsq_rhs :
      (t ^ (-sigma)) ^ 2 * spectralCoeffL2Energy a =
        (t ^ (-sigma) * spectralCoeffL2Norm a) ^ 2 := by
    rw [spectralCoeffL2Norm, mul_pow, Real.sq_sqrt henergy_nonneg]
  rw [hsq_rhs] at hsq
  exact (sq_le_sq₀ (norm_nonneg _) hright_nonneg).mp hsq

end ShenWork.Paper2.IntervalDomainLemma21

end
