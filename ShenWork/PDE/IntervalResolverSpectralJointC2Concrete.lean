import ShenWork.PDE.IntervalResolverSpectralJointC2CutoffBounds

open Filter Topology Set

noncomputable section

namespace ShenWork.IntervalResolverSpectralJointC2Concrete

open ShenWork.IntervalResolverJointC2
open ShenWork.IntervalResolverSpectralJointC2Producer
  (localRestartCoeff_eigenvalue_summable)
open ShenWork.IntervalResolverSpectralTimeC2
  (DuhamelSourceTimeC2Coeff localRestartCoeffAdot localRestartCoeffAddot
    localRestartCoeff_hasDerivAt localRestartCoeffAdot_hasDerivAt_addot
    localRestartCoeff_contDiff_two)
open ShenWork.IntervalResolverSpectralJointC2Cutoff
open ShenWork.IntervalResolverSpectralJointC2CutoffBounds
open ShenWork.IntervalResolverSpectralJointC2Closed
  (one_le_eigenvalue_of_ne_zero frequency_le_eigenvalue)
open ShenWork.IntervalDuhamelClosedC2
  (cosineCoeffSeries_grad_hasDerivAt duhamelSpectralCoeff)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.CosineSpectrum
  (cosineMode cosineMode_deriv cosineMode_second_deriv)

/-- Left support edge for the concrete restart cutoff. -/
def restartCutoffLeftOuter (offset s : ℝ) : ℝ :=
  offset + (s - offset) / 4

/-- Left edge of the plateau for the concrete restart cutoff. -/
def restartCutoffLeft (offset s : ℝ) : ℝ :=
  offset + (s - offset) / 3

/-- Right edge of the plateau for the concrete restart cutoff. -/
def restartCutoffRight (offset s : ℝ) : ℝ :=
  s + (s - offset) / 3

/-- Right support edge for the concrete restart cutoff. -/
def restartCutoffRightOuter (offset s : ℝ) : ℝ :=
  s + (s - offset) / 2

/-- Concrete two-sided smooth cutoff supported in a compact slab around the
target time and equal to one near the target time. -/
def restartSmoothCutoff (offset s : ℝ) : ℝ → ℝ :=
  fun t =>
    smoothRightCutoff (restartCutoffLeftOuter offset s)
        (restartCutoffLeft offset s) t *
      smoothRightCutoff (-(restartCutoffRightOuter offset s))
        (-(restartCutoffRight offset s)) (-t)

theorem restartCutoffLeftOuter_lt_left {offset s : ℝ}
    (hτ : 0 < s - offset) :
    restartCutoffLeftOuter offset s < restartCutoffLeft offset s := by
  unfold restartCutoffLeftOuter restartCutoffLeft
  linarith

theorem restartCutoffLeft_lt_s {offset s : ℝ} (hτ : 0 < s - offset) :
    restartCutoffLeft offset s < s := by
  unfold restartCutoffLeft
  linarith

theorem restartCutoff_s_lt_right {offset s : ℝ} (hτ : 0 < s - offset) :
    s < restartCutoffRight offset s := by
  unfold restartCutoffRight
  linarith

theorem restartCutoffRight_lt_outer {offset s : ℝ} (hτ : 0 < s - offset) :
    restartCutoffRight offset s < restartCutoffRightOuter offset s := by
  unfold restartCutoffRight restartCutoffRightOuter
  linarith

theorem restartCutoffLeft_lt_right {offset s : ℝ} (hτ : 0 < s - offset) :
    restartCutoffLeft offset s < restartCutoffRight offset s := by
  exact (restartCutoffLeft_lt_s hτ).trans (restartCutoff_s_lt_right hτ)

theorem restartCutoffRightOuter_neg_lt_right_neg {offset s : ℝ}
    (hτ : 0 < s - offset) :
    -(restartCutoffRightOuter offset s) < -(restartCutoffRight offset s) := by
  have h := restartCutoffRight_lt_outer (offset := offset) (s := s) hτ
  linarith

theorem restartCutoffLeftOuter_lt_s {offset s : ℝ} (hτ : 0 < s - offset) :
    restartCutoffLeftOuter offset s < s :=
  (restartCutoffLeftOuter_lt_left hτ).trans (restartCutoffLeft_lt_s hτ)

theorem restartCutoff_s_lt_rightOuter {offset s : ℝ} (hτ : 0 < s - offset) :
    s < restartCutoffRightOuter offset s :=
  (restartCutoff_s_lt_right hτ).trans (restartCutoffRight_lt_outer hτ)

theorem restartSmoothCutoff_contDiff {offset s : ℝ} :
    ContDiff ℝ (2 : ℕ∞) (restartSmoothCutoff offset s) :=
  smoothRightCutoff_contDiff.mul
    (smoothRightCutoff_contDiff.comp contDiff_neg)

theorem restartSmoothCutoff_eventually_eq_one {offset s : ℝ}
    (hτ : 0 < s - offset) :
    restartSmoothCutoff offset s =ᶠ[𝓝 s] fun _ : ℝ => 1 := by
  filter_upwards
    [Ioo_mem_nhds (restartCutoffLeft_lt_s hτ)
      (restartCutoff_s_lt_right hτ)] with t ht
  have hleft :
      smoothRightCutoff (restartCutoffLeftOuter offset s)
        (restartCutoffLeft offset s) t = 1 :=
    smoothRightCutoff_eq_one_of_ge
      (restartCutoffLeftOuter_lt_left hτ) (le_of_lt ht.1)
  have hright :
      smoothRightCutoff (-(restartCutoffRightOuter offset s))
        (-(restartCutoffRight offset s)) (-t) = 1 := by
    apply smoothRightCutoff_eq_one_of_ge
      (restartCutoffRightOuter_neg_lt_right_neg hτ)
    linarith [ht.2]
  simp [restartSmoothCutoff, hleft, hright]

theorem restartSmoothCutoff_eq_zero_of_le_left {offset s t : ℝ}
    (hτ : 0 < s - offset) (ht : t ≤ restartCutoffLeftOuter offset s) :
    restartSmoothCutoff offset s t = 0 :=
  by
    rw [restartSmoothCutoff,
      smoothRightCutoff_eq_zero_of_le
        (restartCutoffLeftOuter_lt_left hτ) ht, zero_mul]

theorem restartSmoothCutoff_eq_zero_of_right_le {offset s t : ℝ}
    (hτ : 0 < s - offset) (ht : restartCutoffRightOuter offset s ≤ t) :
    restartSmoothCutoff offset s t = 0 := by
  have hright :
      smoothRightCutoff (-(restartCutoffRightOuter offset s))
        (-(restartCutoffRight offset s)) (-t) = 0 := by
    apply smoothRightCutoff_eq_zero_of_le
      (restartCutoffRightOuter_neg_lt_right_neg hτ)
    linarith
  rw [restartSmoothCutoff, hright, mul_zero]

theorem restartSmoothCutoff_eq_one_of_mem_core {offset s t : ℝ}
    (hτ : 0 < s - offset)
    (ht_left : restartCutoffLeft offset s ≤ t)
    (ht_right : t ≤ restartCutoffRight offset s) :
    restartSmoothCutoff offset s t = 1 := by
  have hleft :
      smoothRightCutoff (restartCutoffLeftOuter offset s)
        (restartCutoffLeft offset s) t = 1 :=
    smoothRightCutoff_eq_one_of_ge
      (restartCutoffLeftOuter_lt_left hτ) ht_left
  have hright :
      smoothRightCutoff (-(restartCutoffRightOuter offset s))
        (-(restartCutoffRight offset s)) (-t) = 1 := by
    apply smoothRightCutoff_eq_one_of_ge
      (restartCutoffRightOuter_neg_lt_right_neg hτ)
    linarith
  simp [restartSmoothCutoff, hleft, hright]

theorem restartSmoothCutoff_hasCompactSupport {offset s : ℝ}
    (hτ : 0 < s - offset) :
    HasCompactSupport (restartSmoothCutoff offset s) := by
  apply HasCompactSupport.intro
    (K := Icc (restartCutoffLeftOuter offset s)
      (restartCutoffRightOuter offset s)) isCompact_Icc
  intro t ht
  by_cases hleft : t ≤ restartCutoffLeftOuter offset s
  · exact restartSmoothCutoff_eq_zero_of_le_left hτ hleft
  · have hL : restartCutoffLeftOuter offset s ≤ t :=
      le_of_lt (lt_of_not_ge hleft)
    have hright : restartCutoffRightOuter offset s ≤ t := by
      by_contra hright
      exact ht ⟨hL, le_of_lt (lt_of_not_ge hright)⟩
    exact restartSmoothCutoff_eq_zero_of_right_le hτ hright

theorem restartSmoothCutoff_iteratedFDeriv_bound_exists
    {offset s : ℝ} (hτ : 0 < s - offset)
    (k : ℕ) (hk : (k : ℕ∞) ≤ (2 : ℕ∞)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, ‖iteratedFDeriv ℝ k (restartSmoothCutoff offset s) t‖ ≤ C := by
  have hcont : Continuous
      (fun t : ℝ => iteratedFDeriv ℝ k (restartSmoothCutoff offset s) t) :=
    restartSmoothCutoff_contDiff.continuous_iteratedFDeriv (by exact_mod_cast hk)
  have hcomp :
      HasCompactSupport
        (fun t : ℝ => iteratedFDeriv ℝ k (restartSmoothCutoff offset s) t) :=
    (restartSmoothCutoff_hasCompactSupport hτ).iteratedFDeriv k
  rcases hcont.bounded_above_of_compact_support hcomp with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right C 0, fun t => ?_⟩
  exact (hC t).trans (le_max_left C 0)

/-- The left edge of the compact coefficient slab, in restart time. -/
def restartSlabMin (offset s : ℝ) : ℝ :=
  restartCutoffLeftOuter offset s - offset

/-- The right edge of the compact coefficient slab, in restart time. -/
def restartSlabMax (offset s : ℝ) : ℝ :=
  restartCutoffRightOuter offset s - offset

theorem restartSlabMin_pos {offset s : ℝ} (hτ : 0 < s - offset) :
    0 < restartSlabMin offset s := by
  unfold restartSlabMin restartCutoffLeftOuter
  linarith

theorem restartSlabMin_le_of_mem_support_slab {offset s t : ℝ}
    (ht : restartCutoffLeftOuter offset s ≤ t) :
    restartSlabMin offset s ≤ t - offset := by
  unfold restartSlabMin
  linarith

theorem restartSlabMax_ge_of_mem_support_slab {offset s t : ℝ}
    (ht : t ≤ restartCutoffRightOuter offset s) :
    t - offset ≤ restartSlabMax offset s := by
  unfold restartSlabMax
  linarith

noncomputable def restartCutoffDerivMajorant
    (offset s : ℝ) (hτ : 0 < s - offset) (k : ℕ) : ℝ :=
  if hk : (k : ℕ∞) ≤ (2 : ℕ∞) then
    Classical.choose
      (restartSmoothCutoff_iteratedFDeriv_bound_exists
        (offset := offset) (s := s) hτ k hk)
  else 0

theorem restartCutoffDerivMajorant_nonneg
    {offset s : ℝ} (hτ : 0 < s - offset) {k : ℕ}
    (hk : (k : ℕ∞) ≤ (2 : ℕ∞)) :
    0 ≤ restartCutoffDerivMajorant offset s hτ k := by
  unfold restartCutoffDerivMajorant
  rw [dif_pos hk]
  exact (Classical.choose_spec
    (restartSmoothCutoff_iteratedFDeriv_bound_exists
      (offset := offset) (s := s) hτ k hk)).1

theorem restartCutoffDerivMajorant_spec
    {offset s : ℝ} (hτ : 0 < s - offset) {k : ℕ}
    (hk : (k : ℕ∞) ≤ (2 : ℕ∞)) (t : ℝ) :
    ‖iteratedFDeriv ℝ k (restartSmoothCutoff offset s) t‖ ≤
      restartCutoffDerivMajorant offset s hτ k := by
  unfold restartCutoffDerivMajorant
  rw [dif_pos hk]
  exact (Classical.choose_spec
    (restartSmoothCutoff_iteratedFDeriv_bound_exists
      (offset := offset) (s := s) hτ k hk)).2 t

/-- A reusable bound for the heat-kernel mass carrying one eigenvalue. -/
theorem heatKernelEigenMass_le_one {τ lam : ℝ}
    (hτ : 0 ≤ τ) (_hlam : 0 ≤ lam) :
    (∫ s in (0 : ℝ)..τ, lam * Real.exp (-(τ - s) * lam)) ≤ 1 := by
  have hcont :
      ContinuousOn (fun s : ℝ => Real.exp (-(τ - s) * lam))
        (Icc (0 : ℝ) τ) := by
    exact (Real.continuous_exp.comp (by fun_prop)).continuousOn
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) τ,
      HasDerivAt (fun u : ℝ => Real.exp (-(τ - u) * lam))
        (lam * Real.exp (-(τ - s) * lam)) s := by
    intro s _hs
    have harg : HasDerivAt (fun u : ℝ => -(τ - u) * lam) lam s := by
      convert ((hasDerivAt_const s τ).sub (hasDerivAt_id s)).neg.mul_const lam
        using 1
      ring
    simpa [mul_comm] using harg.exp
  have hint : IntervalIntegrable
      (fun s : ℝ => lam * Real.exp (-(τ - s) * lam))
      MeasureTheory.volume 0 τ := by
    exact (continuous_const.mul
      (Real.continuous_exp.comp (by fun_prop))).intervalIntegrable 0 τ
  have hEq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (a := (0 : ℝ)) (b := τ)
    (f := fun s : ℝ => Real.exp (-(τ - s) * lam))
    (f' := fun s : ℝ => lam * Real.exp (-(τ - s) * lam))
    hτ hcont hderiv hint
  rw [hEq]
  calc Real.exp (-(τ - τ) * lam) - Real.exp (-(τ - 0) * lam)
      = 1 - Real.exp (-τ * lam) := by simp
    _ ≤ 1 := by
      linarith [Real.exp_nonneg (-τ * lam)]

/-- The Duhamel part gains one eigenvalue from the heat kernel, uniformly for
all nonnegative times. -/
theorem duhamelSpectralCoeff_eigenvalue_cube_bound
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC2Coeff a)
    {τ : ℝ} (hτ : 0 ≤ τ) (n : ℕ) :
    unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          |duhamelSpectralCoeff a τ n|)) ≤
      src.sourceEigenSqEnvelope n := by
  set lam := unitIntervalCosineEigenvalue n
  have hlam : 0 ≤ lam := by
    unfold lam unitIntervalCosineEigenvalue
    positivity
  have henv_nonneg : 0 ≤ src.sourceEigenSqEnvelope n :=
    src.sourceEigenSq_nonneg n
  set f : ℝ → ℝ := fun s => Real.exp (-(τ - s) * lam) * a s n
  have hf_cont : Continuous f := by
    dsimp [f]
    exact (Real.continuous_exp.comp (by fun_prop)).mul
      (continuous_iff_continuousAt.2
        (fun s => (src.toTimeC1.hderiv s n).continuousAt))
  have habs_int :
      |∫ s in (0 : ℝ)..τ, f s| ≤ ∫ s in (0 : ℝ)..τ, |f s| :=
    intervalIntegral.abs_integral_le_integral_abs hτ
  have hleft : lam * (lam * (lam * |∫ s in (0 : ℝ)..τ, f s|)) ≤
      lam * (lam * (lam * ∫ s in (0 : ℝ)..τ, |f s|)) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left habs_int hlam) hlam) hlam
  have hconst : lam * (lam * (lam * ∫ s in (0 : ℝ)..τ, |f s|)) =
      ∫ s in (0 : ℝ)..τ, lam * (lam * (lam * |f s|)) := by
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_const_mul]
  have hmono :
      (∫ s in (0 : ℝ)..τ, lam * (lam * (lam * |f s|))) ≤
        ∫ s in (0 : ℝ)..τ,
          (lam * Real.exp (-(τ - s) * lam)) *
            src.sourceEigenSqEnvelope n := by
    apply intervalIntegral.integral_mono_on hτ
    · exact (continuous_const.mul (continuous_const.mul
        (continuous_const.mul hf_cont.abs))).intervalIntegrable 0 τ
    · exact ((continuous_const.mul
        (Real.continuous_exp.comp (by fun_prop))).mul
          continuous_const).intervalIntegrable 0 τ
    · intro s hs
      rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      have hsrc := src.sourceEigenSq_bound s hs.1 n
      calc lam * (lam *
            (lam * (Real.exp (-(τ - s) * lam) * |a s n|)))
          = (lam * Real.exp (-(τ - s) * lam)) *
              (lam * (lam * |a s n|)) := by ring
        _ ≤ (lam * Real.exp (-(τ - s) * lam)) *
              src.sourceEigenSqEnvelope n := by
            exact mul_le_mul_of_nonneg_left hsrc
              (mul_nonneg hlam (Real.exp_nonneg _))
  have hright :
      (∫ s in (0 : ℝ)..τ,
          (lam * Real.exp (-(τ - s) * lam)) *
            src.sourceEigenSqEnvelope n) ≤
        src.sourceEigenSqEnvelope n := by
    rw [intervalIntegral.integral_mul_const]
    calc (∫ s in (0 : ℝ)..τ, lam * Real.exp (-(τ - s) * lam)) *
          src.sourceEigenSqEnvelope n
        ≤ 1 * src.sourceEigenSqEnvelope n := by
          exact mul_le_mul_of_nonneg_right
            (heatKernelEigenMass_le_one hτ hlam) henv_nonneg
      _ = src.sourceEigenSqEnvelope n := one_mul _
  have hduh : duhamelSpectralCoeff a τ n =
      ∫ s in (0 : ℝ)..τ, f s := by
    simp [duhamelSpectralCoeff, f, lam]
  rw [hduh]
  exact hleft.trans (hconst.le.trans (hmono.trans hright))

/-- Homogeneous restart tail with the compact slab's positive left edge. -/
def restartHomogeneousCubeMajorant
    (a₀ : ℕ → ℝ) (τmin : ℝ) (n : ℕ) : ℝ :=
  unitIntervalCosineEigenvalue n *
    (unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n *
        (Real.exp (-τmin * unitIntervalCosineEigenvalue n) * |a₀ n|)))

/-- Uniform λ³-majorant for the full local restart coefficient. -/
def restartCoeffCubeMajorant
    (a₀ : ℕ → ℝ) {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (τmin : ℝ) (n : ℕ) : ℝ :=
  restartHomogeneousCubeMajorant a₀ τmin n + src.sourceEigenSqEnvelope n

/-- Finite-support zero-mode envelope for the unweighted coefficient and its
first two time derivatives. -/
def restartCoeffZeroModeMajorant
    (a₀ : ℕ → ℝ) {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (τmax : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then
    |a₀ 0| + max τmax 0 * src.toTimeC1.envelope 0 +
      src.toTimeC1.envelope 0 + |src.toTimeC1.derivBound|
  else 0

/-- Summable concrete envelope that controls every coefficient/cosine weight
needed by the value and gradient cutoff series. -/
def restartCoeffCoreMajorant
    (a₀ : ℕ → ℝ) {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (τmin τmax : ℝ) (n : ℕ) : ℝ :=
  restartCoeffZeroModeMajorant a₀ src τmax n +
    4 * restartCoeffCubeMajorant a₀ src τmin n +
      src.sourceEigenEnvelope n + src.sourceEigenSqEnvelope n +
        src.adotEigenEnvelope n

theorem restartHomogeneousCubeMajorant_summable
    {a₀ : ℕ → ℝ} {M τmin : ℝ}
    (hτmin : 0 < τmin) (ha₀ : ∀ n, |a₀ n| ≤ M) :
    Summable (restartHomogeneousCubeMajorant a₀ τmin) := by
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg _) (ha₀ 0)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    ((ShenWork.IntervalResolverSpectralTimeC2.eigenvalue_cube_mul_exp_summable
      hτmin).mul_right M)
  · unfold restartHomogeneousCubeMajorant
    exact mul_nonneg
      (by unfold unitIntervalCosineEigenvalue; positivity)
      (mul_nonneg
        (by unfold unitIntervalCosineEigenvalue; positivity)
        (mul_nonneg
          (by unfold unitIntervalCosineEigenvalue; positivity)
          (mul_nonneg (Real.exp_nonneg _) (abs_nonneg _))))
  · unfold restartHomogeneousCubeMajorant
    have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity
    have hexp : 0 ≤ Real.exp (-τmin * unitIntervalCosineEigenvalue n) :=
      Real.exp_nonneg _
    calc unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              (Real.exp (-τmin * unitIntervalCosineEigenvalue n) *
                |a₀ n|)))
        ≤ unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              (unitIntervalCosineEigenvalue n *
                (Real.exp (-τmin * unitIntervalCosineEigenvalue n) * M))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (ha₀ n) hexp) hlam)
              hlam)
            hlam
      _ = unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              (unitIntervalCosineEigenvalue n *
                Real.exp (-τmin * unitIntervalCosineEigenvalue n))) * M := by
          ring

theorem restartCoeffZeroModeMajorant_summable
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (τmax : ℝ) :
    Summable (restartCoeffZeroModeMajorant a₀ src τmax) := by
  refine summable_of_hasFiniteSupport ?_
  refine (Set.finite_singleton 0).subset ?_
  intro n hn
  simp only [Function.mem_support] at hn
  by_contra hmem
  have hn0 : n ≠ 0 := by
    intro hz
    exact hmem (by simpa [hz])
  simp [restartCoeffZeroModeMajorant, hn0] at hn

theorem restartCoeffCoreMajorant_summable
    {a₀ : ℕ → ℝ} {M τmin τmax : ℝ} {a : ℝ → ℕ → ℝ}
    (hτmin : 0 < τmin) (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC2Coeff a) :
    Summable (restartCoeffCoreMajorant a₀ src τmin τmax) := by
  have hzero : Summable (restartCoeffZeroModeMajorant a₀ src τmax) :=
    restartCoeffZeroModeMajorant_summable src τmax
  have hcube : Summable (restartCoeffCubeMajorant a₀ src τmin) := by
    exact (restartHomogeneousCubeMajorant_summable hτmin ha₀).add
      src.sourceEigenSq_summable
  have hbase : Summable
      (fun n : ℕ =>
        restartCoeffZeroModeMajorant a₀ src τmax n +
          4 * restartCoeffCubeMajorant a₀ src τmin n) :=
    hzero.add (hcube.mul_left 4)
  have hsource : Summable
      (fun n : ℕ =>
        restartCoeffZeroModeMajorant a₀ src τmax n +
          4 * restartCoeffCubeMajorant a₀ src τmin n +
            src.sourceEigenEnvelope n) :=
    hbase.add src.sourceEigen_summable
  have hsourceSq : Summable
      (fun n : ℕ =>
        restartCoeffZeroModeMajorant a₀ src τmax n +
          4 * restartCoeffCubeMajorant a₀ src τmin n +
            src.sourceEigenEnvelope n + src.sourceEigenSqEnvelope n) :=
    hsource.add src.sourceEigenSq_summable
  simpa [restartCoeffCoreMajorant] using
    hsourceSq.add src.adotEigen_summable

theorem restartHomogeneousCubeMajorant_nonneg
    (a₀ : ℕ → ℝ) (τmin : ℝ) (n : ℕ) :
    0 ≤ restartHomogeneousCubeMajorant a₀ τmin n := by
  unfold restartHomogeneousCubeMajorant
  exact mul_nonneg
    (by unfold unitIntervalCosineEigenvalue; positivity)
    (mul_nonneg
      (by unfold unitIntervalCosineEigenvalue; positivity)
      (mul_nonneg
        (by unfold unitIntervalCosineEigenvalue; positivity)
        (mul_nonneg (Real.exp_nonneg _) (abs_nonneg _))))

theorem restartCoeffCubeMajorant_nonneg
    (a₀ : ℕ → ℝ) {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (τmin : ℝ) (n : ℕ) :
    0 ≤ restartCoeffCubeMajorant a₀ src τmin n := by
  exact add_nonneg (restartHomogeneousCubeMajorant_nonneg a₀ τmin n)
    (src.sourceEigenSq_nonneg n)

theorem restartCoeffZeroModeMajorant_nonneg
    (a₀ : ℕ → ℝ) {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (τmax : ℝ) (n : ℕ) :
    0 ≤ restartCoeffZeroModeMajorant a₀ src τmax n := by
  by_cases hn : n = 0
  · have henv0 : 0 ≤ src.toTimeC1.envelope 0 :=
      le_trans (abs_nonneg _) (src.toTimeC1.henv_bound 0 le_rfl 0)
    simp [restartCoeffZeroModeMajorant, hn]
    positivity
  · simp [restartCoeffZeroModeMajorant, hn]

theorem restartCoeffCoreMajorant_nonneg
    (a₀ : ℕ → ℝ) {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (τmin τmax : ℝ) (n : ℕ) :
    0 ≤ restartCoeffCoreMajorant a₀ src τmin τmax n := by
  unfold restartCoeffCoreMajorant
  exact add_nonneg
    (add_nonneg
      (add_nonneg
        (add_nonneg (restartCoeffZeroModeMajorant_nonneg a₀ src τmax n)
          (mul_nonneg (by norm_num)
            (restartCoeffCubeMajorant_nonneg a₀ src τmin n)))
        (src.sourceEigen_nonneg n))
      (src.sourceEigenSq_nonneg n))
    (src.adotEigen_nonneg n)

theorem restartCoeffCubeMajorant_le_core
    (a₀ : ℕ → ℝ) {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (τmin τmax : ℝ) (n : ℕ) :
    restartCoeffCubeMajorant a₀ src τmin n ≤
      restartCoeffCoreMajorant a₀ src τmin τmax n := by
  have hzero := restartCoeffZeroModeMajorant_nonneg a₀ src τmax n
  have hcube := restartCoeffCubeMajorant_nonneg a₀ src τmin n
  have hsource := src.sourceEigen_nonneg n
  have hsourceSq := src.sourceEigenSq_nonneg n
  have hadot := src.adotEigen_nonneg n
  unfold restartCoeffCoreMajorant
  nlinarith

theorem restartCoeffCube_add_sourceEigen_le_core
    (a₀ : ℕ → ℝ) {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (τmin τmax : ℝ) (n : ℕ) :
    restartCoeffCubeMajorant a₀ src τmin n +
        src.sourceEigenEnvelope n ≤
      restartCoeffCoreMajorant a₀ src τmin τmax n := by
  have hzero := restartCoeffZeroModeMajorant_nonneg a₀ src τmax n
  have hcube := restartCoeffCubeMajorant_nonneg a₀ src τmin n
  have hsourceSq := src.sourceEigenSq_nonneg n
  have hadot := src.adotEigen_nonneg n
  unfold restartCoeffCoreMajorant
  nlinarith

theorem restartCoeffCube_add_sourceSq_adot_le_core
    (a₀ : ℕ → ℝ) {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (τmin τmax : ℝ) (n : ℕ) :
    restartCoeffCubeMajorant a₀ src τmin n +
        src.sourceEigenSqEnvelope n + src.adotEigenEnvelope n ≤
      restartCoeffCoreMajorant a₀ src τmin τmax n := by
  have hzero := restartCoeffZeroModeMajorant_nonneg a₀ src τmax n
  have hcube := restartCoeffCubeMajorant_nonneg a₀ src τmin n
  have hsource := src.sourceEigen_nonneg n
  unfold restartCoeffCoreMajorant
  nlinarith

theorem localRestartCoeff_eigenvalue_cube_bound
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) {τ τmin : ℝ}
    (hτ : 0 ≤ τ) (hτmin : τmin ≤ τ) (n : ℕ) :
    unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          |localRestartCoeff a₀ a τ n|)) ≤
      restartCoeffCubeMajorant a₀ src τmin n := by
  set lam := unitIntervalCosineEigenvalue n
  have hlam : 0 ≤ lam := by
    unfold lam unitIntervalCosineEigenvalue
    positivity
  have hhom : lam * (lam *
        (lam * |Real.exp (-τ * lam) * a₀ n|)) ≤
      restartHomogeneousCubeMajorant a₀ τmin n := by
    have hexp_le : Real.exp (-τ * lam) ≤ Real.exp (-τmin * lam) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hτmin hlam]
    have hexp_nonneg : 0 ≤ Real.exp (-τ * lam) := Real.exp_nonneg _
    calc lam * (lam * (lam * |Real.exp (-τ * lam) * a₀ n|))
        = lam * (lam * (lam * (Real.exp (-τ * lam) * |a₀ n|))) := by
          rw [abs_mul, abs_of_nonneg hexp_nonneg]
      _ ≤ lam * (lam *
            (lam * (Real.exp (-τmin * lam) * |a₀ n|))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hexp_le (abs_nonneg _)) hlam)
              hlam) hlam
      _ = restartHomogeneousCubeMajorant a₀ τmin n := by
          simp [restartHomogeneousCubeMajorant, lam]
  have hduh := duhamelSpectralCoeff_eigenvalue_cube_bound src hτ n
  calc lam * (lam * (lam * |localRestartCoeff a₀ a τ n|))
      ≤ lam * (lam * (lam *
          (|Real.exp (-τ * lam) * a₀ n| + |duhamelSpectralCoeff a τ n|))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (by
                simp only [localRestartCoeff]
                exact abs_add_le _ _)
              hlam) hlam) hlam
    _ = lam * (lam * (lam * |Real.exp (-τ * lam) * a₀ n|)) +
          lam * (lam * (lam * |duhamelSpectralCoeff a τ n|)) := by ring
    _ ≤ restartHomogeneousCubeMajorant a₀ τmin n +
          src.sourceEigenSqEnvelope n := add_le_add hhom hduh
    _ = restartCoeffCubeMajorant a₀ src τmin n := rfl

theorem localRestartCoeff_zero_abs_le
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) {τ τmax : ℝ}
    (hτ : 0 ≤ τ) (hτmax : τ ≤ τmax) :
    |localRestartCoeff a₀ a τ 0| ≤
      restartCoeffZeroModeMajorant a₀ src τmax 0 := by
  have henv0 : 0 ≤ src.toTimeC1.envelope 0 :=
    le_trans (abs_nonneg _) (src.toTimeC1.henv_bound 0 le_rfl 0)
  have hduh : |duhamelSpectralCoeff a τ 0| ≤
      τmax * src.toTimeC1.envelope 0 := by
    have hduh_eq : duhamelSpectralCoeff a τ 0 =
        ∫ s in (0 : ℝ)..τ, a s 0 := by
      simp [duhamelSpectralCoeff, unitIntervalCosineEigenvalue]
    rw [hduh_eq]
    have habs : |∫ s in (0 : ℝ)..τ, a s 0| ≤
        ∫ s in (0 : ℝ)..τ, |a s 0| :=
      intervalIntegral.abs_integral_le_integral_abs hτ
    calc |∫ s in (0 : ℝ)..τ, a s 0|
        ≤ ∫ s in (0 : ℝ)..τ, |a s 0| := habs
      _ ≤ ∫ _s in (0 : ℝ)..τ, src.toTimeC1.envelope 0 := by
          apply intervalIntegral.integral_mono_on hτ
          · exact (continuous_iff_continuousAt.2
              (fun s => (src.toTimeC1.hderiv s 0).continuousAt)).abs
                |>.intervalIntegrable 0 τ
          · exact continuous_const.intervalIntegrable 0 τ
          · intro s hs
            exact src.toTimeC1.henv_bound s hs.1 0
      _ = src.toTimeC1.envelope 0 * τ := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
      _ ≤ src.toTimeC1.envelope 0 * τmax :=
          mul_le_mul_of_nonneg_left hτmax henv0
      _ = τmax * src.toTimeC1.envelope 0 := by ring
  calc |localRestartCoeff a₀ a τ 0|
      ≤ |a₀ 0| + |duhamelSpectralCoeff a τ 0| := by
        simp [localRestartCoeff, unitIntervalCosineEigenvalue]
        exact abs_add_le _ _
    _ ≤ |a₀ 0| + τmax * src.toTimeC1.envelope 0 :=
        add_le_add le_rfl hduh
    _ ≤ |a₀ 0| + max τmax 0 * src.toTimeC1.envelope 0 := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_right (le_max_left τmax 0) henv0)
    _ ≤ restartCoeffZeroModeMajorant a₀ src τmax 0 := by
        simp [restartCoeffZeroModeMajorant]
        have htail : 0 ≤ src.toTimeC1.envelope 0 +
            |src.toTimeC1.derivBound| :=
          add_nonneg henv0 (abs_nonneg _)
        linarith

theorem localRestartCoeffAdot_zero_abs_le
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) {τ τmax : ℝ} (hτ : 0 ≤ τ) :
    |localRestartCoeffAdot a₀ a τ 0| ≤
      restartCoeffZeroModeMajorant a₀ src τmax 0 := by
  have henv0 : 0 ≤ src.toTimeC1.envelope 0 :=
    le_trans (abs_nonneg _) (src.toTimeC1.henv_bound 0 le_rfl 0)
  have ha : |a τ 0| ≤ src.toTimeC1.envelope 0 :=
    src.toTimeC1.henv_bound τ hτ 0
  calc |localRestartCoeffAdot a₀ a τ 0|
      ≤ src.toTimeC1.envelope 0 := by
        simpa [localRestartCoeffAdot, unitIntervalCosineEigenvalue] using ha
    _ ≤ restartCoeffZeroModeMajorant a₀ src τmax 0 := by
        simp [restartCoeffZeroModeMajorant]
        have htail : 0 ≤ |a₀ 0| + max τmax 0 * src.toTimeC1.envelope 0 +
            |src.toTimeC1.derivBound| := by positivity
        linarith

theorem localRestartCoeffAddot_zero_abs_le
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) {τ τmax : ℝ} (hτ : 0 ≤ τ) :
    |localRestartCoeffAddot a₀ a src.toTimeC1.adot τ 0| ≤
      restartCoeffZeroModeMajorant a₀ src τmax 0 := by
  have henv0 : 0 ≤ src.toTimeC1.envelope 0 :=
    le_trans (abs_nonneg _) (src.toTimeC1.henv_bound 0 le_rfl 0)
  have hadot :
      |src.toTimeC1.adot τ 0| ≤ |src.toTimeC1.derivBound| :=
    (src.toTimeC1.hderivBound τ hτ 0).trans (le_abs_self _)
  calc |localRestartCoeffAddot a₀ a src.toTimeC1.adot τ 0|
      ≤ |src.toTimeC1.derivBound| := by
        simpa [localRestartCoeffAddot, localRestartCoeffAdot,
          unitIntervalCosineEigenvalue] using hadot
    _ ≤ restartCoeffZeroModeMajorant a₀ src τmax 0 := by
        simp [restartCoeffZeroModeMajorant]
        have htail : 0 ≤ |a₀ 0| + max τmax 0 * src.toTimeC1.envelope 0 +
            src.toTimeC1.envelope 0 := by positivity
        linarith

theorem localRestartCoeff_abs_le_core
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) {τ τmin τmax : ℝ}
    (hτ : 0 ≤ τ) (hτmin : τmin ≤ τ) (hτmax : τ ≤ τmax) (n : ℕ) :
    |localRestartCoeff a₀ a τ n| ≤
      restartCoeffCoreMajorant a₀ src τmin τmax n := by
  by_cases hn : n = 0
  · subst n
    exact (localRestartCoeff_zero_abs_le src hτ hτmax).trans
      (by
        unfold restartCoeffCoreMajorant
        nlinarith [restartCoeffCubeMajorant_nonneg a₀ src τmin 0,
          src.sourceEigen_nonneg 0, src.sourceEigenSq_nonneg 0,
          src.adotEigen_nonneg 0])
  · set lam := unitIntervalCosineEigenvalue n
    have hlam1 : 1 ≤ lam := by
      simpa [lam] using one_le_eigenvalue_of_ne_zero hn
    have hlam0 : 0 ≤ lam := le_trans zero_le_one hlam1
    have hcube :=
      localRestartCoeff_eigenvalue_cube_bound (a₀ := a₀) src hτ hτmin n
    have hpow : |localRestartCoeff a₀ a τ n| ≤
        lam * (lam * (lam * |localRestartCoeff a₀ a τ n|)) := by
      have h0 : 0 ≤ |localRestartCoeff a₀ a τ n| := abs_nonneg _
      calc |localRestartCoeff a₀ a τ n|
          ≤ lam * |localRestartCoeff a₀ a τ n| :=
            le_mul_of_one_le_left h0 hlam1
        _ ≤ lam * (lam * |localRestartCoeff a₀ a τ n|) := by
            exact mul_le_mul_of_nonneg_left
              (le_mul_of_one_le_left h0 hlam1) hlam0
        _ ≤ lam * (lam * (lam * |localRestartCoeff a₀ a τ n|)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (le_mul_of_one_le_left h0 hlam1) hlam0) hlam0
    exact hpow.trans (hcube.trans
      (restartCoeffCubeMajorant_le_core a₀ src τmin τmax n))

theorem localRestartCoeff_eigen_abs_le_core
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) {τ τmin τmax : ℝ}
    (hτ : 0 ≤ τ) (hτmin : τmin ≤ τ) (n : ℕ) :
    unitIntervalCosineEigenvalue n * |localRestartCoeff a₀ a τ n| ≤
      restartCoeffCoreMajorant a₀ src τmin τmax n := by
  by_cases hn : n = 0
  · subst n
    simpa [unitIntervalCosineEigenvalue] using
      restartCoeffCoreMajorant_nonneg a₀ src τmin τmax 0
  · set lam := unitIntervalCosineEigenvalue n
    have hlam1 : 1 ≤ lam := by
      simpa [lam] using one_le_eigenvalue_of_ne_zero hn
    have hlam0 : 0 ≤ lam := le_trans zero_le_one hlam1
    have hcube :=
      localRestartCoeff_eigenvalue_cube_bound (a₀ := a₀) src hτ hτmin n
    have hpow : lam * |localRestartCoeff a₀ a τ n| ≤
        lam * (lam * (lam * |localRestartCoeff a₀ a τ n|)) := by
      have h0 : 0 ≤ |localRestartCoeff a₀ a τ n| := abs_nonneg _
      calc lam * |localRestartCoeff a₀ a τ n|
          ≤ lam * (lam * |localRestartCoeff a₀ a τ n|) := by
            exact mul_le_mul_of_nonneg_left
              (le_mul_of_one_le_left h0 hlam1) hlam0
        _ ≤ lam * (lam * (lam * |localRestartCoeff a₀ a τ n|)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (le_mul_of_one_le_left h0 hlam1) hlam0) hlam0
    exact hpow.trans (hcube.trans
      (restartCoeffCubeMajorant_le_core a₀ src τmin τmax n))

theorem localRestartCoeff_frequency_abs_le_core
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) {τ τmin τmax : ℝ}
    (hτ : 0 ≤ τ) (hτmin : τmin ≤ τ) (n : ℕ) :
    |(n : ℝ) * Real.pi| * |localRestartCoeff a₀ a τ n| ≤
      restartCoeffCoreMajorant a₀ src τmin τmax n := by
  exact (mul_le_mul_of_nonneg_right (frequency_le_eigenvalue n)
    (abs_nonneg _)).trans
      (localRestartCoeff_eigen_abs_le_core src hτ hτmin n)

theorem localRestartCoeff_frequency_eigen_abs_le_core
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) {τ τmin τmax : ℝ}
    (hτ : 0 ≤ τ) (hτmin : τmin ≤ τ) (n : ℕ) :
    |(n : ℝ) * Real.pi| * unitIntervalCosineEigenvalue n *
        |localRestartCoeff a₀ a τ n| ≤
      restartCoeffCoreMajorant a₀ src τmin τmax n := by
  by_cases hn : n = 0
  · subst n
    simpa [unitIntervalCosineEigenvalue] using
      restartCoeffCoreMajorant_nonneg a₀ src τmin τmax 0
  · set lam := unitIntervalCosineEigenvalue n
    have hlam1 : 1 ≤ lam := by
      simpa [lam] using one_le_eigenvalue_of_ne_zero hn
    have hlam0 : 0 ≤ lam := le_trans zero_le_one hlam1
    have hfreq : |(n : ℝ) * Real.pi| ≤ lam := by
      simpa [lam] using frequency_le_eigenvalue n
    have hcube :=
      localRestartCoeff_eigenvalue_cube_bound (a₀ := a₀) src hτ hτmin n
    have hpow : |(n : ℝ) * Real.pi| * lam *
          |localRestartCoeff a₀ a τ n| ≤
        lam * (lam * (lam * |localRestartCoeff a₀ a τ n|)) := by
      have h0 : 0 ≤ |localRestartCoeff a₀ a τ n| := abs_nonneg _
      calc |(n : ℝ) * Real.pi| * lam *
            |localRestartCoeff a₀ a τ n|
          ≤ lam * lam * |localRestartCoeff a₀ a τ n| := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hfreq hlam0) h0
        _ ≤ lam * lam * (lam * |localRestartCoeff a₀ a τ n|) := by
            exact mul_le_mul_of_nonneg_left
              (le_mul_of_one_le_left h0 hlam1) (mul_nonneg hlam0 hlam0)
        _ = lam * (lam * (lam * |localRestartCoeff a₀ a τ n|)) := by ring
    exact hpow.trans (hcube.trans
      (restartCoeffCubeMajorant_le_core a₀ src τmin τmax n))

theorem localRestartCoeffAdot_eigen_abs_le_core
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) {τ τmin τmax : ℝ}
    (hτ : 0 ≤ τ) (hτmin : τmin ≤ τ) (n : ℕ) :
    unitIntervalCosineEigenvalue n *
        |localRestartCoeffAdot a₀ a τ n| ≤
      restartCoeffCoreMajorant a₀ src τmin τmax n := by
  set lam := unitIntervalCosineEigenvalue n
  have hlam : 0 ≤ lam := by
    unfold lam unitIntervalCosineEigenvalue
    positivity
  have hcube :=
    localRestartCoeff_eigenvalue_cube_bound (a₀ := a₀) src hτ hτmin n
  have hsrc := src.sourceEigen_bound τ hτ n
  have hsplit : lam * |localRestartCoeffAdot a₀ a τ n| ≤
      src.sourceEigenEnvelope n + restartCoeffCubeMajorant a₀ src τmin n := by
    calc lam * |localRestartCoeffAdot a₀ a τ n|
        ≤ lam * (|a τ n| +
            |lam * localRestartCoeff a₀ a τ n|) := by
          exact mul_le_mul_of_nonneg_left
            (by
              simpa [localRestartCoeffAdot, lam, sub_eq_add_neg, abs_neg]
                using abs_add_le (a τ n)
                  (-(lam * localRestartCoeff a₀ a τ n)))
            hlam
      _ = lam * |a τ n| + lam * (lam * |localRestartCoeff a₀ a τ n|) := by
          rw [abs_mul, abs_of_nonneg hlam]
          ring
      _ ≤ src.sourceEigenEnvelope n +
            lam * (lam * (lam * |localRestartCoeff a₀ a τ n|)) := by
          exact add_le_add hsrc
            (mul_le_mul_of_nonneg_left
              (by
                by_cases hn : n = 0
                · subst n
                  simp [lam, unitIntervalCosineEigenvalue]
                · have hlam1 : 1 ≤ lam := by
                    simpa [lam] using one_le_eigenvalue_of_ne_zero hn
                  exact le_mul_of_one_le_left
                    (mul_nonneg hlam (abs_nonneg _)) hlam1)
              hlam)
      _ ≤ src.sourceEigenEnvelope n +
            restartCoeffCubeMajorant a₀ src τmin n :=
          add_le_add le_rfl hcube
  exact hsplit.trans
    (by
      rw [add_comm]
      exact restartCoeffCube_add_sourceEigen_le_core a₀ src τmin τmax n)

theorem localRestartCoeffAdot_abs_le_core
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) {τ τmin τmax : ℝ}
    (hτ : 0 ≤ τ) (hτmin : τmin ≤ τ) (n : ℕ) :
    |localRestartCoeffAdot a₀ a τ n| ≤
      restartCoeffCoreMajorant a₀ src τmin τmax n := by
  by_cases hn : n = 0
  · subst n
    exact (localRestartCoeffAdot_zero_abs_le src (τmax := τmax) hτ).trans
      (by
        unfold restartCoeffCoreMajorant
        nlinarith [restartCoeffCubeMajorant_nonneg a₀ src τmin 0,
          src.sourceEigen_nonneg 0, src.sourceEigenSq_nonneg 0,
          src.adotEigen_nonneg 0])
  · set lam := unitIntervalCosineEigenvalue n
    have hlam1 : 1 ≤ lam := by
      simpa [lam] using one_le_eigenvalue_of_ne_zero hn
    have h0 : 0 ≤ |localRestartCoeffAdot a₀ a τ n| := abs_nonneg _
    calc |localRestartCoeffAdot a₀ a τ n|
        ≤ lam * |localRestartCoeffAdot a₀ a τ n| :=
          le_mul_of_one_le_left h0 hlam1
      _ ≤ restartCoeffCoreMajorant a₀ src τmin τmax n :=
          localRestartCoeffAdot_eigen_abs_le_core src hτ hτmin n

theorem localRestartCoeffAdot_frequency_abs_le_core
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) {τ τmin τmax : ℝ}
    (hτ : 0 ≤ τ) (hτmin : τmin ≤ τ) (n : ℕ) :
    |(n : ℝ) * Real.pi| * |localRestartCoeffAdot a₀ a τ n| ≤
      restartCoeffCoreMajorant a₀ src τmin τmax n := by
  exact (mul_le_mul_of_nonneg_right (frequency_le_eigenvalue n)
    (abs_nonneg _)).trans
      (localRestartCoeffAdot_eigen_abs_le_core src hτ hτmin n)

theorem localRestartCoeffAddot_frequency_abs_le_core
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) {τ τmin τmax : ℝ}
    (hτ : 0 ≤ τ) (hτmin : τmin ≤ τ) (n : ℕ) :
    |(n : ℝ) * Real.pi| *
        |localRestartCoeffAddot a₀ a src.toTimeC1.adot τ n| ≤
      restartCoeffCoreMajorant a₀ src τmin τmax n := by
  by_cases hn : n = 0
  · subst n
    simpa using restartCoeffCoreMajorant_nonneg a₀ src τmin τmax 0
  · set lam := unitIntervalCosineEigenvalue n
    have hfreq : |(n : ℝ) * Real.pi| ≤ lam := by
      simpa [lam] using frequency_le_eigenvalue n
    have hlam : 0 ≤ lam := by
      unfold lam unitIntervalCosineEigenvalue
      positivity
    have hcube :=
      localRestartCoeff_eigenvalue_cube_bound (a₀ := a₀) src hτ hτmin n
    have hadot := src.adotEigen_bound τ hτ n
    have hsrcSq := src.sourceEigenSq_bound τ hτ n
    have hsplit : |(n : ℝ) * Real.pi| *
        |localRestartCoeffAddot a₀ a src.toTimeC1.adot τ n| ≤
        restartCoeffCubeMajorant a₀ src τmin n +
          src.sourceEigenSqEnvelope n + src.adotEigenEnvelope n := by
      calc |(n : ℝ) * Real.pi| *
            |localRestartCoeffAddot a₀ a src.toTimeC1.adot τ n|
          ≤ lam * |localRestartCoeffAddot a₀ a src.toTimeC1.adot τ n| := by
            exact mul_le_mul_of_nonneg_right hfreq (abs_nonneg _)
        _ ≤ lam * (|src.toTimeC1.adot τ n| +
              |lam * localRestartCoeffAdot a₀ a τ n|) := by
            exact mul_le_mul_of_nonneg_left
              (by
                simpa [localRestartCoeffAddot, lam, sub_eq_add_neg, abs_neg]
                  using abs_add_le (src.toTimeC1.adot τ n)
                    (-(lam * localRestartCoeffAdot a₀ a τ n)))
              hlam
        _ = lam * |src.toTimeC1.adot τ n| +
              lam * (lam * |localRestartCoeffAdot a₀ a τ n|) := by
            rw [abs_mul, abs_of_nonneg hlam]
            ring
        _ ≤ src.adotEigenEnvelope n +
              (src.sourceEigenSqEnvelope n +
                restartCoeffCubeMajorant a₀ src τmin n) := by
            refine add_le_add hadot ?_
            calc lam * (lam * |localRestartCoeffAdot a₀ a τ n|)
                ≤ lam * (lam * (|a τ n| +
                    |lam * localRestartCoeff a₀ a τ n|)) := by
                  exact mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_left
                      (by
                        simpa [localRestartCoeffAdot, lam, sub_eq_add_neg,
                          abs_neg] using abs_add_le (a τ n)
                            (-(lam * localRestartCoeff a₀ a τ n)))
                      hlam) hlam
              _ = lam * (lam * |a τ n|) +
                    lam * (lam * (lam *
                      |localRestartCoeff a₀ a τ n|)) := by
                  rw [abs_mul, abs_of_nonneg hlam]
                  ring
              _ ≤ src.sourceEigenSqEnvelope n +
                    restartCoeffCubeMajorant a₀ src τmin n :=
                  add_le_add hsrcSq hcube
        _ = restartCoeffCubeMajorant a₀ src τmin n +
              src.sourceEigenSqEnvelope n + src.adotEigenEnvelope n := by
            ring
    exact hsplit.trans
      (restartCoeffCube_add_sourceSq_adot_le_core a₀ src τmin τmax n)

theorem localRestartCoeffAddot_abs_le_core
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) {τ τmin τmax : ℝ}
    (hτ : 0 ≤ τ) (hτmin : τmin ≤ τ) (n : ℕ) :
    |localRestartCoeffAddot a₀ a src.toTimeC1.adot τ n| ≤
      restartCoeffCoreMajorant a₀ src τmin τmax n := by
  by_cases hn : n = 0
  · subst n
    exact (localRestartCoeffAddot_zero_abs_le src (τmax := τmax) hτ).trans
      (by
        unfold restartCoeffCoreMajorant
        nlinarith [restartCoeffCubeMajorant_nonneg a₀ src τmin 0,
          src.sourceEigen_nonneg 0, src.sourceEigenSq_nonneg 0,
          src.adotEigen_nonneg 0])
  · have hfreq_ge_one : 1 ≤ |(n : ℝ) * Real.pi| := by
      have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
      have hnonneg : 0 ≤ (n : ℝ) * Real.pi := by positivity
      rw [abs_of_nonneg hnonneg]
      nlinarith [hn1, Real.pi_gt_three]
    exact (le_mul_of_one_le_left (abs_nonneg _) hfreq_ge_one).trans
      (localRestartCoeffAddot_frequency_abs_le_core src hτ hτmin n)

def valueCosWeight (m n : ℕ) : ℝ :=
  match m with
  | 0 => 1
  | 1 => |(n : ℝ) * Real.pi|
  | _ => unitIntervalCosineEigenvalue n

def gradCosWeight (m n : ℕ) : ℝ :=
  match m with
  | 0 => |(n : ℝ) * Real.pi|
  | 1 => unitIntervalCosineEigenvalue n
  | _ => |(n : ℝ) * Real.pi| * unitIntervalCosineEigenvalue n

theorem valueCosWeight_nonneg (m n : ℕ) :
    0 ≤ valueCosWeight m n := by
  cases m with
  | zero => simp [valueCosWeight]
  | succ m =>
      cases m with
      | zero => simp [valueCosWeight]
      | succ m =>
          simp [valueCosWeight]
          unfold unitIntervalCosineEigenvalue
          positivity

theorem gradCosWeight_nonneg (m n : ℕ) :
    0 ≤ gradCosWeight m n := by
  cases m with
  | zero => simp [gradCosWeight]
  | succ m =>
      cases m with
      | zero =>
          simp [gradCosWeight]
          unfold unitIntervalCosineEigenvalue
          positivity
      | succ m =>
          simp [gradCosWeight]
          exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
            (by unfold unitIntervalCosineEigenvalue; positivity)

theorem cosineMode_iteratedFDeriv_bound
    (n m : ℕ) (y : ℝ) (hm : m ≤ 2) :
    ‖iteratedFDeriv ℝ m (cosineMode n) y‖ ≤ valueCosWeight m n := by
  interval_cases m
  · rw [norm_iteratedFDeriv_zero]
    unfold cosineMode valueCosWeight
    exact Real.abs_cos_le_one _
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    simp [valueCosWeight, cosineMode_deriv]
    calc (n : ℝ) * |Real.pi| * |Real.sin ((n : ℝ) * Real.pi * y)|
        ≤ (n : ℝ) * |Real.pi| * 1 := by
          exact mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _)
            (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
      _ = (n : ℝ) * |Real.pi| := by ring
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hiter : iteratedDeriv 2 (cosineMode n) y =
        deriv (fun z : ℝ => deriv (cosineMode n) z) y := by
      norm_num [iteratedDeriv_succ']
    rw [hiter, cosineMode_second_deriv]
    rw [Real.norm_eq_abs]
    have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity
    calc |-(((n : ℝ) * Real.pi) ^ 2 * cosineMode n y)|
        = unitIntervalCosineEigenvalue n * |cosineMode n y| := by
          rw [abs_neg, abs_mul,
            abs_of_nonneg (sq_nonneg ((n : ℝ) * Real.pi))]
          rfl
      _ ≤ unitIntervalCosineEigenvalue n * 1 := by
          exact mul_le_mul_of_nonneg_left
            (by unfold cosineMode; exact Real.abs_cos_le_one _) hlam
      _ = valueCosWeight 2 n := by
          simp [valueCosWeight]

theorem cosineModeDeriv_iteratedFDeriv_bound
    (n m : ℕ) (y : ℝ) (hm : m ≤ 2) :
    ‖iteratedFDeriv ℝ m (fun z : ℝ => deriv (cosineMode n) z) y‖ ≤
      gradCosWeight m n := by
  interval_cases m
  · rw [norm_iteratedFDeriv_zero]
    simp [gradCosWeight, cosineMode_deriv]
    calc (n : ℝ) * |Real.pi| * |Real.sin ((n : ℝ) * Real.pi * y)|
        ≤ (n : ℝ) * |Real.pi| * 1 := by
          exact mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _)
            (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
      _ = (n : ℝ) * |Real.pi| := by ring
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    simp [gradCosWeight]
    rw [cosineMode_second_deriv]
    have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity
    calc |-(((n : ℝ) * Real.pi) ^ 2 * cosineMode n y)|
        = unitIntervalCosineEigenvalue n * |cosineMode n y| := by
          rw [abs_neg, abs_mul,
            abs_of_nonneg (sq_nonneg ((n : ℝ) * Real.pi))]
          rfl
      _ ≤ unitIntervalCosineEigenvalue n * 1 := by
          exact mul_le_mul_of_nonneg_left
            (by unfold cosineMode; exact Real.abs_cos_le_one _) hlam
      _ = unitIntervalCosineEigenvalue n := by ring
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hiter : iteratedDeriv 2
        (fun z : ℝ => deriv (cosineMode n) z) y =
        deriv (fun z : ℝ =>
          deriv (fun w : ℝ => deriv (cosineMode n) w) z) y := by
      norm_num [iteratedDeriv_succ']
    rw [hiter]
    have hsecond :
        (fun z : ℝ => deriv (fun w : ℝ => deriv (cosineMode n) w) z) =
          fun z : ℝ => -(unitIntervalCosineEigenvalue n * cosineMode n z) := by
      funext z
      rw [cosineMode_second_deriv]
      simp [unitIntervalCosineEigenvalue]
    rw [hsecond]
    have hd : deriv
        (fun z : ℝ => -(unitIntervalCosineEigenvalue n * cosineMode n z)) y =
          -(unitIntervalCosineEigenvalue n * deriv (cosineMode n) y) := by
      simp [deriv_const_mul_field']
    rw [hd, cosineMode_deriv]
    rw [Real.norm_eq_abs]
    have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity
    calc |-(unitIntervalCosineEigenvalue n *
          (-((n : ℝ) * Real.pi) *
            Real.sin ((n : ℝ) * Real.pi * y)))|
        = unitIntervalCosineEigenvalue n *
            (|(n : ℝ) * Real.pi| *
              |Real.sin ((n : ℝ) * Real.pi * y)|) := by
          rw [abs_neg, abs_mul, abs_of_nonneg hlam, abs_mul, abs_neg]
      _ ≤ unitIntervalCosineEigenvalue n *
            (|(n : ℝ) * Real.pi| * 1) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _)
              (abs_nonneg _)) hlam
      _ = gradCosWeight 2 n := by
          simp [gradCosWeight]
          ring

theorem shiftedLocalRestartCoeff_iteratedFDeriv_norm_eq
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (offset t : ℝ) (n r : ℕ)
    (hr : r ≤ 2) :
    ‖iteratedFDeriv ℝ r
      (fun u : ℝ => localRestartCoeff a₀ a (u - offset) n) t‖ =
      match r with
      | 0 => |localRestartCoeff a₀ a (t - offset) n|
      | 1 => |localRestartCoeffAdot a₀ a (t - offset) n|
      | _ => |localRestartCoeffAddot a₀ a src.toTimeC1.adot
          (t - offset) n| := by
  interval_cases r
  · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    simp
    have hderiv :
        deriv (fun u : ℝ => localRestartCoeff a₀ a (u - offset) n) t =
          localRestartCoeffAdot a₀ a (t - offset) n := by
      have h := (localRestartCoeff_hasDerivAt
        (a₀ := a₀) (a := a) src (t - offset) n).comp t
          ((hasDerivAt_id t).sub_const offset)
      simpa [Function.comp_def] using h.deriv
    rw [hderiv]
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hiter : iteratedDeriv 2
        (fun u : ℝ => localRestartCoeff a₀ a (u - offset) n) t =
        deriv (fun u : ℝ =>
          deriv (fun v : ℝ => localRestartCoeff a₀ a (v - offset) n) u)
          t := by
      norm_num [iteratedDeriv_succ']
    rw [hiter]
    have hderiv :
        deriv (fun v : ℝ => localRestartCoeff a₀ a (v - offset) n) =
          fun v : ℝ => localRestartCoeffAdot a₀ a (v - offset) n := by
      funext v
      have h := (localRestartCoeff_hasDerivAt
        (a₀ := a₀) (a := a) src (v - offset) n).comp v
          ((hasDerivAt_id v).sub_const offset)
      simpa [Function.comp_def] using h.deriv
    rw [hderiv]
    have h2deriv :
        deriv (fun u : ℝ => localRestartCoeffAdot a₀ a (u - offset) n) t =
          localRestartCoeffAddot a₀ a src.toTimeC1.adot (t - offset) n := by
      have h2 := (localRestartCoeffAdot_hasDerivAt_addot
        (a₀ := a₀) (a := a) src (t - offset) n).comp t
          ((hasDerivAt_id t).sub_const offset)
      simpa [Function.comp_def] using h2.deriv
    rw [h2deriv, Real.norm_eq_abs]

theorem shiftedLocalRestartCoeff_valueWeight_le_core
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a)
    {offset t τmin τmax : ℝ} {n r m : ℕ}
    (hτ : 0 ≤ t - offset) (hτmin : τmin ≤ t - offset)
    (hτmax : t - offset ≤ τmax) (hrm : r + m ≤ 2) :
    ‖iteratedFDeriv ℝ r
      (fun u : ℝ => localRestartCoeff a₀ a (u - offset) n) t‖ *
        valueCosWeight m n ≤
      restartCoeffCoreMajorant a₀ src τmin τmax n := by
  have hr : r ≤ 2 := by omega
  have hm : m ≤ 2 := by omega
  interval_cases r
  · interval_cases m
    · rw [shiftedLocalRestartCoeff_iteratedFDeriv_norm_eq src offset t n 0
        (by norm_num)]
      simpa [valueCosWeight] using
        localRestartCoeff_abs_le_core src hτ hτmin hτmax n
    · rw [shiftedLocalRestartCoeff_iteratedFDeriv_norm_eq src offset t n 0
        (by norm_num)]
      simpa [valueCosWeight, mul_comm] using
        localRestartCoeff_frequency_abs_le_core src hτ hτmin n
    · rw [shiftedLocalRestartCoeff_iteratedFDeriv_norm_eq src offset t n 0
        (by norm_num)]
      simpa [valueCosWeight, mul_comm] using
        localRestartCoeff_eigen_abs_le_core src hτ hτmin n
  · interval_cases m
    · rw [shiftedLocalRestartCoeff_iteratedFDeriv_norm_eq src offset t n 1
        (by norm_num)]
      simpa [valueCosWeight] using
        localRestartCoeffAdot_abs_le_core src hτ hτmin n
    · rw [shiftedLocalRestartCoeff_iteratedFDeriv_norm_eq src offset t n 1
        (by norm_num)]
      simpa [valueCosWeight, mul_comm] using
        localRestartCoeffAdot_frequency_abs_le_core src hτ hτmin n
    · omega
  · interval_cases m
    · rw [shiftedLocalRestartCoeff_iteratedFDeriv_norm_eq src offset t n 2
        (by norm_num)]
      simpa [valueCosWeight] using
        localRestartCoeffAddot_abs_le_core src hτ hτmin n
    · omega
    · omega

theorem shiftedLocalRestartCoeff_gradWeight_le_core
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a)
    {offset t τmin τmax : ℝ} {n r m : ℕ}
    (hτ : 0 ≤ t - offset) (hτmin : τmin ≤ t - offset)
    (_hτmax : t - offset ≤ τmax) (hrm : r + m ≤ 2) :
    ‖iteratedFDeriv ℝ r
      (fun u : ℝ => localRestartCoeff a₀ a (u - offset) n) t‖ *
        gradCosWeight m n ≤
      restartCoeffCoreMajorant a₀ src τmin τmax n := by
  have hr : r ≤ 2 := by omega
  have hm : m ≤ 2 := by omega
  interval_cases r
  · interval_cases m
    · rw [shiftedLocalRestartCoeff_iteratedFDeriv_norm_eq src offset t n 0
        (by norm_num)]
      simpa [gradCosWeight, mul_comm] using
        localRestartCoeff_frequency_abs_le_core src hτ hτmin n
    · rw [shiftedLocalRestartCoeff_iteratedFDeriv_norm_eq src offset t n 0
        (by norm_num)]
      simpa [gradCosWeight, mul_comm] using
        localRestartCoeff_eigen_abs_le_core src hτ hτmin n
    · rw [shiftedLocalRestartCoeff_iteratedFDeriv_norm_eq src offset t n 0
        (by norm_num)]
      simpa [gradCosWeight, mul_comm, mul_left_comm, mul_assoc] using
        localRestartCoeff_frequency_eigen_abs_le_core src hτ hτmin n
  · interval_cases m
    · rw [shiftedLocalRestartCoeff_iteratedFDeriv_norm_eq src offset t n 1
        (by norm_num)]
      simpa [gradCosWeight, mul_comm] using
        localRestartCoeffAdot_frequency_abs_le_core src hτ hτmin n
    · rw [shiftedLocalRestartCoeff_iteratedFDeriv_norm_eq src offset t n 1
        (by norm_num)]
      simpa [gradCosWeight, mul_comm] using
        localRestartCoeffAdot_eigen_abs_le_core src hτ hτmin n
    · omega
  · interval_cases m
    · rw [shiftedLocalRestartCoeff_iteratedFDeriv_norm_eq src offset t n 2
        (by norm_num)]
      simpa [gradCosWeight, mul_comm] using
        localRestartCoeffAddot_frequency_abs_le_core src hτ hτmin n
    · omega
    · omega

/-- Concrete spatial-gradient summand for the restart resolver series. -/
def resolverSpectralConcreteGradTerm
    (a₀ : ℕ → ℝ) (a : ℝ → ℕ → ℝ) (offset : ℝ)
    (n : ℕ) : ℝ × ℝ → ℝ :=
  fun q =>
    localRestartCoeff a₀ a (q.1 - offset) n *
      deriv (cosineMode n) q.2

theorem cutoffValueTerm_restartSmoothCutoff_contDiff
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {offset s : ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (n : ℕ) :
    ContDiff ℝ (2 : ℕ∞)
      (cutoffValueTerm (restartSmoothCutoff offset s) a₀ a offset n) := by
  have hφ : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => restartSmoothCutoff offset s q.1) :=
    restartSmoothCutoff_contDiff.comp contDiff_fst
  have hcoeff : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => localRestartCoeff a₀ a (q.1 - offset) n) :=
    (localRestartCoeff_contDiff_two (a₀ := a₀) src n).comp
      (contDiff_fst.sub contDiff_const)
  have hcos : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => cosineMode n q.2) := by
    have hcos₀ : ContDiff ℝ (2 : ℕ∞) (cosineMode n) := by
      unfold cosineMode
      fun_prop
    exact hcos₀.comp contDiff_snd
  change ContDiff ℝ (2 : ℕ∞)
    (fun q : ℝ × ℝ =>
      (restartSmoothCutoff offset s q.1 *
        localRestartCoeff a₀ a (q.1 - offset) n) * cosineMode n q.2)
  exact (hφ.mul hcoeff).mul hcos

theorem resolverSpectralConcreteGradTerm_contDiff
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {offset : ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (n : ℕ) :
    ContDiff ℝ (2 : ℕ∞)
      (resolverSpectralConcreteGradTerm a₀ a offset n) := by
  have hcoeff : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => localRestartCoeff a₀ a (q.1 - offset) n) :=
    (localRestartCoeff_contDiff_two (a₀ := a₀) src n).comp
      (contDiff_fst.sub contDiff_const)
  have hderivCos₀ : ContDiff ℝ (2 : ℕ∞)
      (fun y : ℝ => deriv (cosineMode n) y) := by
    have hEq :
        (fun y : ℝ => deriv (cosineMode n) y) =
          fun y : ℝ =>
            -((n : ℝ) * Real.pi) *
              Real.sin ((n : ℝ) * Real.pi * y) := by
      funext y
      rw [cosineMode_deriv]
    rw [hEq]
    fun_prop
  have hderivCos : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => deriv (cosineMode n) q.2) :=
    hderivCos₀.comp contDiff_snd
  simpa [resolverSpectralConcreteGradTerm] using hcoeff.mul hderivCos

theorem cutoffGradTerm_restartSmoothCutoff_contDiff
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {offset s : ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (n : ℕ) :
    ContDiff ℝ (2 : ℕ∞)
      (cutoffGradTerm (restartSmoothCutoff offset s)
        (resolverSpectralConcreteGradTerm a₀ a offset) n) := by
  have hφ : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => restartSmoothCutoff offset s q.1) :=
    restartSmoothCutoff_contDiff.comp contDiff_fst
  simpa [cutoffGradTerm] using
    hφ.mul (resolverSpectralConcreteGradTerm_contDiff
      (a₀ := a₀) (offset := offset) src n)

theorem resolverSpectralGradSeries_eventuallyEq_concreteGradTerm
    {a₀ : ℕ → ℝ} {M : ℝ} {a : ℝ → ℕ → ℝ} {offset s x : ℝ}
    (hτ : 0 < s - offset) (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC2Coeff a) :
    resolverSpectralGradSeries a₀ a offset =ᶠ[𝓝 (s, x)]
      fun q : ℝ × ℝ =>
        ∑' n : ℕ, resolverSpectralConcreteGradTerm a₀ a offset n q := by
  have hpos :
      {q : ℝ × ℝ | 0 < q.1 - offset} ∈ 𝓝 (s, x) := by
    exact (isOpen_lt continuous_const (continuous_fst.sub continuous_const)).mem_nhds hτ
  filter_upwards [hpos] with q hq
  have hsum :
      Summable (fun n : ℕ =>
        unitIntervalCosineEigenvalue n *
          |localRestartCoeff a₀ a (q.1 - offset) n|) :=
    localRestartCoeff_eigenvalue_summable
      (τ := q.1 - offset) (M := M) (a₀ := a₀) (a := a)
      hq ha₀ src.toTimeC1
  unfold resolverSpectralGradSeries
  change
    deriv
        (fun y : ℝ =>
          ∑' n : ℕ,
            localRestartCoeff a₀ a (q.1 - offset) n * cosineMode n y)
        q.2 =
      ∑' n : ℕ, resolverSpectralConcreteGradTerm a₀ a offset n q
  rw [(cosineCoeffSeries_grad_hasDerivAt hsum q.2).deriv]
  apply tsum_congr
  intro n
  simp [resolverSpectralConcreteGradTerm, cosineMode_deriv, mul_assoc]

theorem cutoffValueTerm_restartSmoothCutoff_iteratedFDeriv_eq_zero_of_left
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {offset s : ℝ}
    (hτ : 0 < s - offset) {n k : ℕ} {q : ℝ × ℝ}
    (hleft : q.1 < restartCutoffLeftOuter offset s) :
    iteratedFDeriv ℝ k
      (cutoffValueTerm (restartSmoothCutoff offset s) a₀ a offset n) q =
      0 := by
  have hzero :
      cutoffValueTerm (restartSmoothCutoff offset s) a₀ a offset n
        =ᶠ[𝓝 q] fun _ : ℝ × ℝ => 0 := by
    have hnear :
        {p : ℝ × ℝ | p.1 < restartCutoffLeftOuter offset s} ∈ 𝓝 q :=
      (isOpen_lt continuous_fst continuous_const).mem_nhds hleft
    filter_upwards [hnear] with p hp
    have hcut :=
      restartSmoothCutoff_eq_zero_of_le_left
        (offset := offset) (s := s) hτ (le_of_lt hp)
    simp [cutoffValueTerm, hcut]
  have hderiv := Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hzero k
  have hq : iteratedFDeriv ℝ k
      (cutoffValueTerm (restartSmoothCutoff offset s) a₀ a offset n) q =
      iteratedFDeriv ℝ k (fun _ : ℝ × ℝ => 0) q :=
    hderiv.self_of_nhds
  rw [hq]
  simp

theorem cutoffValueTerm_restartSmoothCutoff_iteratedFDeriv_eq_zero_of_right
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {offset s : ℝ}
    (hτ : 0 < s - offset) {n k : ℕ} {q : ℝ × ℝ}
    (hright : restartCutoffRightOuter offset s < q.1) :
    iteratedFDeriv ℝ k
      (cutoffValueTerm (restartSmoothCutoff offset s) a₀ a offset n) q =
      0 := by
  have hzero :
      cutoffValueTerm (restartSmoothCutoff offset s) a₀ a offset n
        =ᶠ[𝓝 q] fun _ : ℝ × ℝ => 0 := by
    have hnear :
        {p : ℝ × ℝ | restartCutoffRightOuter offset s < p.1} ∈ 𝓝 q :=
      (isOpen_lt continuous_const continuous_fst).mem_nhds hright
    filter_upwards [hnear] with p hp
    have hcut :=
      restartSmoothCutoff_eq_zero_of_right_le
        (offset := offset) (s := s) hτ (le_of_lt hp)
    simp [cutoffValueTerm, hcut]
  have hderiv := Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hzero k
  have hq : iteratedFDeriv ℝ k
      (cutoffValueTerm (restartSmoothCutoff offset s) a₀ a offset n) q =
      iteratedFDeriv ℝ k (fun _ : ℝ × ℝ => 0) q :=
    hderiv.self_of_nhds
  rw [hq]
  simp

theorem cutoffGradTerm_restartSmoothCutoff_iteratedFDeriv_eq_zero_of_left
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {offset s : ℝ}
    (hτ : 0 < s - offset) {n k : ℕ} {q : ℝ × ℝ}
    (hleft : q.1 < restartCutoffLeftOuter offset s) :
    iteratedFDeriv ℝ k
      (cutoffGradTerm (restartSmoothCutoff offset s)
        (resolverSpectralConcreteGradTerm a₀ a offset) n) q =
      0 := by
  have hzero :
      cutoffGradTerm (restartSmoothCutoff offset s)
          (resolverSpectralConcreteGradTerm a₀ a offset) n
        =ᶠ[𝓝 q] fun _ : ℝ × ℝ => 0 := by
    have hnear :
        {p : ℝ × ℝ | p.1 < restartCutoffLeftOuter offset s} ∈ 𝓝 q :=
      (isOpen_lt continuous_fst continuous_const).mem_nhds hleft
    filter_upwards [hnear] with p hp
    have hcut :=
      restartSmoothCutoff_eq_zero_of_le_left
        (offset := offset) (s := s) hτ (le_of_lt hp)
    simp [cutoffGradTerm, hcut]
  have hderiv := Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hzero k
  have hq : iteratedFDeriv ℝ k
      (cutoffGradTerm (restartSmoothCutoff offset s)
        (resolverSpectralConcreteGradTerm a₀ a offset) n) q =
      iteratedFDeriv ℝ k (fun _ : ℝ × ℝ => 0) q :=
    hderiv.self_of_nhds
  rw [hq]
  simp

theorem cutoffGradTerm_restartSmoothCutoff_iteratedFDeriv_eq_zero_of_right
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {offset s : ℝ}
    (hτ : 0 < s - offset) {n k : ℕ} {q : ℝ × ℝ}
    (hright : restartCutoffRightOuter offset s < q.1) :
    iteratedFDeriv ℝ k
      (cutoffGradTerm (restartSmoothCutoff offset s)
        (resolverSpectralConcreteGradTerm a₀ a offset) n) q =
      0 := by
  have hzero :
      cutoffGradTerm (restartSmoothCutoff offset s)
          (resolverSpectralConcreteGradTerm a₀ a offset) n
        =ᶠ[𝓝 q] fun _ : ℝ × ℝ => 0 := by
    have hnear :
        {p : ℝ × ℝ | restartCutoffRightOuter offset s < p.1} ∈ 𝓝 q :=
      (isOpen_lt continuous_const continuous_fst).mem_nhds hright
    filter_upwards [hnear] with p hp
    have hcut :=
      restartSmoothCutoff_eq_zero_of_right_le
        (offset := offset) (s := s) hτ (le_of_lt hp)
    simp [cutoffGradTerm, hcut]
  have hderiv := Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hzero k
  have hq : iteratedFDeriv ℝ k
      (cutoffGradTerm (restartSmoothCutoff offset s)
        (resolverSpectralConcreteGradTerm a₀ a offset) n) q =
      iteratedFDeriv ℝ k (fun _ : ℝ × ℝ => 0) q :=
    hderiv.self_of_nhds
  rw [hq]
  simp

theorem resolverSpectralConcreteGradTerm_iteratedFDeriv_bound_of_mem_slab
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a)
    {offset τmin τmax : ℝ} {n k : ℕ} {q : ℝ × ℝ}
    (hτ : 0 ≤ q.1 - offset) (hτmin : τmin ≤ q.1 - offset)
    (hτmax : q.1 - offset ≤ τmax)
    (hk : (k : ℕ∞) ≤ (2 : ℕ∞)) :
    ‖iteratedFDeriv ℝ k
      (resolverSpectralConcreteGradTerm a₀ a offset n) q‖ ≤
      (∑ r ∈ Finset.range (k + 1), (k.choose r : ℝ)) *
        restartCoeffCoreMajorant a₀ src τmin τmax n := by
  have hkNat : k ≤ 2 := by exact_mod_cast hk
  have hkTop : (k : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast hk
  have hcoeff₀ : ContDiff ℝ (2 : ℕ∞)
      (fun t : ℝ => localRestartCoeff a₀ a (t - offset) n) :=
    (localRestartCoeff_contDiff_two (a₀ := a₀) src n).comp
      (contDiff_id.sub contDiff_const)
  have hcoeff : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => localRestartCoeff a₀ a (q.1 - offset) n) :=
    hcoeff₀.comp contDiff_fst
  have hderivCos₀ : ContDiff ℝ (2 : ℕ∞)
      (fun y : ℝ => deriv (cosineMode n) y) := by
    have hEq :
        (fun y : ℝ => deriv (cosineMode n) y) =
          fun y : ℝ =>
            -((n : ℝ) * Real.pi) *
              Real.sin ((n : ℝ) * Real.pi * y) := by
      funext y
      rw [cosineMode_deriv]
    rw [hEq]
    fun_prop
  have hderivCos : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => deriv (cosineMode n) q.2) :=
    hderivCos₀.comp contDiff_snd
  have hprod := norm_iteratedFDeriv_mul_le hcoeff hderivCos q hkTop
  have hprod' :
      ‖iteratedFDeriv ℝ k
        (resolverSpectralConcreteGradTerm a₀ a offset n) q‖ ≤
        ∑ r ∈ Finset.range (k + 1), (k.choose r : ℝ) *
          ‖iteratedFDeriv ℝ r
            (fun q : ℝ × ℝ =>
              localRestartCoeff a₀ a (q.1 - offset) n) q‖ *
          ‖iteratedFDeriv ℝ (k - r)
            (fun q : ℝ × ℝ => deriv (cosineMode n) q.2) q‖ := by
    simpa [resolverSpectralConcreteGradTerm] using hprod
  refine hprod'.trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro r hr
  have hrk : r ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  have hrTop :
      ((r : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast le_trans hrk hkNat
  have hkrTop :
      (((k - r : ℕ) : ℕ∞) : WithTop ℕ∞) ≤
        ((2 : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast le_trans (Nat.sub_le k r) hkNat
  have hcoeffNorm :
      ‖iteratedFDeriv ℝ r
        (fun q : ℝ × ℝ =>
          localRestartCoeff a₀ a (q.1 - offset) n) q‖ ≤
      ‖iteratedFDeriv ℝ r
        (fun t : ℝ => localRestartCoeff a₀ a (t - offset) n) q.1‖ :=
    norm_iteratedFDeriv_comp_fst_le hcoeff₀ hrTop q
  have hcosNorm :
      ‖iteratedFDeriv ℝ (k - r)
        (fun q : ℝ × ℝ => deriv (cosineMode n) q.2) q‖ ≤
      gradCosWeight (k - r) n := by
    exact (norm_iteratedFDeriv_comp_snd_le hderivCos₀ hkrTop q).trans
      (cosineModeDeriv_iteratedFDeriv_bound n (k - r) q.2
        (by omega))
  have hcore :
      ‖iteratedFDeriv ℝ r
        (fun t : ℝ => localRestartCoeff a₀ a (t - offset) n) q.1‖ *
          gradCosWeight (k - r) n ≤
        restartCoeffCoreMajorant a₀ src τmin τmax n := by
    exact shiftedLocalRestartCoeff_gradWeight_le_core src
      hτ hτmin hτmax (by omega)
  have hpair :
      ‖iteratedFDeriv ℝ r
        (fun q : ℝ × ℝ =>
          localRestartCoeff a₀ a (q.1 - offset) n) q‖ *
        ‖iteratedFDeriv ℝ (k - r)
          (fun q : ℝ × ℝ => deriv (cosineMode n) q.2) q‖ ≤
        restartCoeffCoreMajorant a₀ src τmin τmax n := by
    calc
      ‖iteratedFDeriv ℝ r
        (fun q : ℝ × ℝ =>
          localRestartCoeff a₀ a (q.1 - offset) n) q‖ *
        ‖iteratedFDeriv ℝ (k - r)
          (fun q : ℝ × ℝ => deriv (cosineMode n) q.2) q‖
          ≤ ‖iteratedFDeriv ℝ r
              (fun t : ℝ => localRestartCoeff a₀ a (t - offset) n) q.1‖ *
              gradCosWeight (k - r) n := by
            exact mul_le_mul hcoeffNorm hcosNorm (norm_nonneg _) (norm_nonneg _)
      _ ≤ restartCoeffCoreMajorant a₀ src τmin τmax n := hcore
  calc
    (k.choose r : ℝ) *
        ‖iteratedFDeriv ℝ r
          (fun q : ℝ × ℝ =>
            localRestartCoeff a₀ a (q.1 - offset) n) q‖ *
        ‖iteratedFDeriv ℝ (k - r)
          (fun q : ℝ × ℝ => deriv (cosineMode n) q.2) q‖
        = (k.choose r : ℝ) *
            (‖iteratedFDeriv ℝ r
              (fun q : ℝ × ℝ =>
                localRestartCoeff a₀ a (q.1 - offset) n) q‖ *
              ‖iteratedFDeriv ℝ (k - r)
                (fun q : ℝ × ℝ => deriv (cosineMode n) q.2) q‖) := by
          ring
    _ ≤ (k.choose r : ℝ) *
        restartCoeffCoreMajorant a₀ src τmin τmax n :=
          mul_le_mul_of_nonneg_left hpair (Nat.cast_nonneg _)

/-- Value-side finite Leibniz constant for the compact restart cutoff. -/
def concreteRestartValueLeibnizConstant
    (offset s : ℝ) (hτ : 0 < s - offset) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
    ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
      restartCutoffDerivMajorant offset s hτ j

/-- Gradient-side finite Leibniz constant for the compact restart cutoff. -/
def concreteRestartGradLeibnizConstant
    (offset s : ℝ) (hτ : 0 < s - offset) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
    restartCutoffDerivMajorant offset s hτ i *
      ∑ r ∈ Finset.range (k - i + 1), ((k - i).choose r : ℝ)

theorem concreteRestartValueLeibnizConstant_nonneg
    {offset s : ℝ} (hτ : 0 < s - offset) {k : ℕ}
    (hk : (k : ℕ∞) ≤ (2 : ℕ∞)) :
    0 ≤ concreteRestartValueLeibnizConstant offset s hτ k := by
  have hkNat : k ≤ 2 := by exact_mod_cast hk
  unfold concreteRestartValueLeibnizConstant
  apply Finset.sum_nonneg
  intro i hi
  apply mul_nonneg (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro j hj
  apply mul_nonneg (Nat.cast_nonneg _)
  have hij : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  exact restartCutoffDerivMajorant_nonneg hτ
    (by exact_mod_cast le_trans hij (le_trans hik hkNat))

theorem concreteRestartGradLeibnizConstant_nonneg
    {offset s : ℝ} (hτ : 0 < s - offset) {k : ℕ}
    (hk : (k : ℕ∞) ≤ (2 : ℕ∞)) :
    0 ≤ concreteRestartGradLeibnizConstant offset s hτ k := by
  have hkNat : k ≤ 2 := by exact_mod_cast hk
  unfold concreteRestartGradLeibnizConstant
  apply Finset.sum_nonneg
  intro i hi
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  refine mul_nonneg (mul_nonneg (Nat.cast_nonneg _) ?_) ?_
  · exact restartCutoffDerivMajorant_nonneg hτ
      (by exact_mod_cast le_trans hik hkNat)
  · apply Finset.sum_nonneg
    intro r _hr
    exact Nat.cast_nonneg _

/-- Value-side concrete majorant used by the restart cutoff instantiation. -/
def concreteRestartValueMajorant
    (a₀ : ℕ → ℝ) {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC2Coeff a)
    (offset s : ℝ) (hτ : 0 < s - offset) (k n : ℕ) : ℝ :=
  concreteRestartValueLeibnizConstant offset s hτ k *
    restartCoeffCoreMajorant a₀ src
      (restartSlabMin offset s) (restartSlabMax offset s) n

/-- Gradient-side concrete majorant used by the restart cutoff instantiation. -/
def concreteRestartGradMajorant
    (a₀ : ℕ → ℝ) {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC2Coeff a)
    (offset s : ℝ) (hτ : 0 < s - offset) (k n : ℕ) : ℝ :=
  concreteRestartGradLeibnizConstant offset s hτ k *
    restartCoeffCoreMajorant a₀ src
      (restartSlabMin offset s) (restartSlabMax offset s) n

theorem concreteRestartValueMajorant_nonneg
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {offset s : ℝ}
    (hτ : 0 < s - offset) (src : DuhamelSourceTimeC2Coeff a)
    {k n : ℕ} (hk : (k : ℕ∞) ≤ (2 : ℕ∞)) :
    0 ≤ concreteRestartValueMajorant a₀ src offset s hτ k n := by
  unfold concreteRestartValueMajorant
  exact mul_nonneg (concreteRestartValueLeibnizConstant_nonneg hτ hk)
    (restartCoeffCoreMajorant_nonneg a₀ src
      (restartSlabMin offset s) (restartSlabMax offset s) n)

theorem concreteRestartGradMajorant_nonneg
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {offset s : ℝ}
    (hτ : 0 < s - offset) (src : DuhamelSourceTimeC2Coeff a)
    {k n : ℕ} (hk : (k : ℕ∞) ≤ (2 : ℕ∞)) :
    0 ≤ concreteRestartGradMajorant a₀ src offset s hτ k n := by
  unfold concreteRestartGradMajorant
  exact mul_nonneg (concreteRestartGradLeibnizConstant_nonneg hτ hk)
    (restartCoeffCoreMajorant_nonneg a₀ src
      (restartSlabMin offset s) (restartSlabMax offset s) n)

theorem cutoffGradTerm_restartSmoothCutoff_iteratedFDeriv_bound_of_mem_slab
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {offset s : ℝ}
    (hτ : 0 < s - offset) (src : DuhamelSourceTimeC2Coeff a)
    {n k : ℕ} {q : ℝ × ℝ}
    (hL : restartCutoffLeftOuter offset s ≤ q.1)
    (hR : q.1 ≤ restartCutoffRightOuter offset s)
    (hk : (k : ℕ∞) ≤ (2 : ℕ∞)) :
    ‖iteratedFDeriv ℝ k
      (cutoffGradTerm (restartSmoothCutoff offset s)
        (resolverSpectralConcreteGradTerm a₀ a offset) n) q‖ ≤
      concreteRestartGradMajorant a₀ src offset s hτ k n := by
  have hkNat : k ≤ 2 := by exact_mod_cast hk
  have hτmin : restartSlabMin offset s ≤ q.1 - offset :=
    restartSlabMin_le_of_mem_support_slab hL
  have hτmax : q.1 - offset ≤ restartSlabMax offset s :=
    restartSlabMax_ge_of_mem_support_slab hR
  have hτnonneg : 0 ≤ q.1 - offset :=
    le_trans (restartSlabMin_pos hτ).le hτmin
  have hφ : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => restartSmoothCutoff offset s q.1) :=
    restartSmoothCutoff_contDiff.comp contDiff_fst
  have hterm :=
    cutoffGradTerm_leibniz_bound
      (φ := restartSmoothCutoff offset s)
      (gradTerm := resolverSpectralConcreteGradTerm a₀ a offset)
      (n := n) (k := k) (q := q) hφ
      (resolverSpectralConcreteGradTerm_contDiff
        (a₀ := a₀) (offset := offset) src n) hk
  refine hterm.trans ?_
  unfold concreteRestartGradMajorant concreteRestartGradLeibnizConstant
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hiTop :
      ((i : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast le_trans hik hkNat
  have hki : ((k - i : ℕ) : ℕ∞) ≤ (2 : ℕ∞) := by
    exact_mod_cast le_trans (Nat.sub_le k i) hkNat
  have hcut :
      ‖iteratedFDeriv ℝ i
        (fun q : ℝ × ℝ => restartSmoothCutoff offset s q.1) q‖ ≤
      restartCutoffDerivMajorant offset s hτ i := by
    exact (norm_iteratedFDeriv_comp_fst_le
      (restartSmoothCutoff_contDiff (offset := offset) (s := s)) hiTop q).trans
        (restartCutoffDerivMajorant_spec hτ
          (by exact_mod_cast le_trans hik hkNat) q.1)
  have hgrad :
      ‖iteratedFDeriv ℝ (k - i)
        (resolverSpectralConcreteGradTerm a₀ a offset n) q‖ ≤
      (∑ r ∈ Finset.range (k - i + 1), ((k - i).choose r : ℝ)) *
        restartCoeffCoreMajorant a₀ src
          (restartSlabMin offset s) (restartSlabMax offset s) n := by
    exact resolverSpectralConcreteGradTerm_iteratedFDeriv_bound_of_mem_slab
      (a₀ := a₀) (offset := offset) src hτnonneg hτmin hτmax hki
  have hinner_nonneg :
      0 ≤ (∑ r ∈ Finset.range (k - i + 1),
        ((k - i).choose r : ℝ)) *
          restartCoeffCoreMajorant a₀ src
            (restartSlabMin offset s) (restartSlabMax offset s) n := by
    exact mul_nonneg
      (by
        apply Finset.sum_nonneg
        intro r _hr
        exact Nat.cast_nonneg _)
      (restartCoeffCoreMajorant_nonneg a₀ src
        (restartSlabMin offset s) (restartSlabMax offset s) n)
  have hCnonneg :
      0 ≤ restartCutoffDerivMajorant offset s hτ i :=
    restartCutoffDerivMajorant_nonneg hτ
      (by exact_mod_cast le_trans hik hkNat)
  calc
    (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i
          (fun q : ℝ × ℝ => restartSmoothCutoff offset s q.1) q‖ *
        ‖iteratedFDeriv ℝ (k - i)
          (resolverSpectralConcreteGradTerm a₀ a offset n) q‖
        = (k.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i
              (fun q : ℝ × ℝ => restartSmoothCutoff offset s q.1) q‖ *
            ‖iteratedFDeriv ℝ (k - i)
              (resolverSpectralConcreteGradTerm a₀ a offset n) q‖ := rfl
    _ ≤ (k.choose i : ℝ) *
          restartCutoffDerivMajorant offset s hτ i *
          ((∑ r ∈ Finset.range (k - i + 1), ((k - i).choose r : ℝ)) *
            restartCoeffCoreMajorant a₀ src
              (restartSlabMin offset s) (restartSlabMax offset s) n) := by
        have hleft :
            (k.choose i : ℝ) *
              ‖iteratedFDeriv ℝ i
                (fun q : ℝ × ℝ => restartSmoothCutoff offset s q.1) q‖ ≤
            (k.choose i : ℝ) *
              restartCutoffDerivMajorant offset s hτ i :=
          mul_le_mul_of_nonneg_left hcut (Nat.cast_nonneg _)
        exact mul_le_mul hleft hgrad (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) hCnonneg)
    _ = ((k.choose i : ℝ) *
          restartCutoffDerivMajorant offset s hτ i *
          ∑ r ∈ Finset.range (k - i + 1), ((k - i).choose r : ℝ)) *
          restartCoeffCoreMajorant a₀ src
            (restartSlabMin offset s) (restartSlabMax offset s) n := by
        ring

theorem cutoffValueTerm_restartSmoothCutoff_iteratedFDeriv_bound_of_mem_slab
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {offset s : ℝ}
    (hτ : 0 < s - offset) (src : DuhamelSourceTimeC2Coeff a)
    {n k : ℕ} {q : ℝ × ℝ}
    (hL : restartCutoffLeftOuter offset s ≤ q.1)
    (hR : q.1 ≤ restartCutoffRightOuter offset s)
    (hk : (k : ℕ∞) ≤ (2 : ℕ∞)) :
    ‖iteratedFDeriv ℝ k
      (cutoffValueTerm (restartSmoothCutoff offset s) a₀ a offset n) q‖ ≤
      concreteRestartValueMajorant a₀ src offset s hτ k n := by
  have hkNat : k ≤ 2 := by exact_mod_cast hk
  have hτmin : restartSlabMin offset s ≤ q.1 - offset :=
    restartSlabMin_le_of_mem_support_slab hL
  have hτmax : q.1 - offset ≤ restartSlabMax offset s :=
    restartSlabMax_ge_of_mem_support_slab hR
  have hτnonneg : 0 ≤ q.1 - offset :=
    le_trans (restartSlabMin_pos hτ).le hτmin
  have hφ : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => restartSmoothCutoff offset s q.1) :=
    restartSmoothCutoff_contDiff.comp contDiff_fst
  have hcoeff₀ : ContDiff ℝ (2 : ℕ∞)
      (fun t : ℝ => localRestartCoeff a₀ a (t - offset) n) :=
    (localRestartCoeff_contDiff_two (a₀ := a₀) src n).comp
      (contDiff_id.sub contDiff_const)
  have hcoeff : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => localRestartCoeff a₀ a (q.1 - offset) n) :=
    hcoeff₀.comp contDiff_fst
  have hG : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ =>
        restartSmoothCutoff offset s q.1 *
          localRestartCoeff a₀ a (q.1 - offset) n) :=
    hφ.mul hcoeff
  have hcos₀ : ContDiff ℝ (2 : ℕ∞) (cosineMode n) := by
    unfold cosineMode
    fun_prop
  have hcos : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => cosineMode n q.2) :=
    hcos₀.comp contDiff_snd
  have hterm :=
    cutoffValueTerm_leibniz_bound
      (φ := restartSmoothCutoff offset s) (a₀ := a₀) (a := a)
      (offset := offset) (n := n) (k := k) (q := q) hG hcos hk
  refine hterm.trans ?_
  unfold concreteRestartValueMajorant concreteRestartValueLeibnizConstant
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hiTop :
      ((i : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast le_trans hik hkNat
  have hkiTop :
      (((k - i : ℕ) : ℕ∞) : WithTop ℕ∞) ≤
        ((2 : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast le_trans (Nat.sub_le k i) hkNat
  have hcosNorm :
      ‖iteratedFDeriv ℝ (k - i)
        (fun q : ℝ × ℝ => cosineMode n q.2) q‖ ≤
      valueCosWeight (k - i) n := by
    exact (norm_iteratedFDeriv_comp_snd_le hcos₀ hkiTop q).trans
      (cosineMode_iteratedFDeriv_bound n (k - i) q.2 (by omega))
  have hGprod :
      ‖iteratedFDeriv ℝ i
        (fun q : ℝ × ℝ =>
          restartSmoothCutoff offset s q.1 *
            localRestartCoeff a₀ a (q.1 - offset) n) q‖ ≤
        ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
          ‖iteratedFDeriv ℝ j
            (fun q : ℝ × ℝ => restartSmoothCutoff offset s q.1) q‖ *
          ‖iteratedFDeriv ℝ (i - j)
            (fun q : ℝ × ℝ =>
              localRestartCoeff a₀ a (q.1 - offset) n) q‖ := by
    have hmul := norm_iteratedFDeriv_mul_le hφ hcoeff q hiTop
    simpa using hmul
  have hGsum_nonneg :
      0 ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
        ‖iteratedFDeriv ℝ j
          (fun q : ℝ × ℝ => restartSmoothCutoff offset s q.1) q‖ *
        ‖iteratedFDeriv ℝ (i - j)
          (fun q : ℝ × ℝ =>
            localRestartCoeff a₀ a (q.1 - offset) n) q‖ := by
    apply Finset.sum_nonneg
    intro j _hj
    positivity
  have hGcos :
      ‖iteratedFDeriv ℝ i
        (fun q : ℝ × ℝ =>
          restartSmoothCutoff offset s q.1 *
            localRestartCoeff a₀ a (q.1 - offset) n) q‖ *
        ‖iteratedFDeriv ℝ (k - i)
          (fun q : ℝ × ℝ => cosineMode n q.2) q‖ ≤
      (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
        restartCutoffDerivMajorant offset s hτ j) *
        restartCoeffCoreMajorant a₀ src
          (restartSlabMin offset s) (restartSlabMax offset s) n := by
    calc
      ‖iteratedFDeriv ℝ i
        (fun q : ℝ × ℝ =>
          restartSmoothCutoff offset s q.1 *
            localRestartCoeff a₀ a (q.1 - offset) n) q‖ *
        ‖iteratedFDeriv ℝ (k - i)
          (fun q : ℝ × ℝ => cosineMode n q.2) q‖
          ≤ (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
              ‖iteratedFDeriv ℝ j
                (fun q : ℝ × ℝ => restartSmoothCutoff offset s q.1) q‖ *
              ‖iteratedFDeriv ℝ (i - j)
                (fun q : ℝ × ℝ =>
                  localRestartCoeff a₀ a (q.1 - offset) n) q‖) *
              valueCosWeight (k - i) n := by
            exact mul_le_mul hGprod hcosNorm (norm_nonneg _) hGsum_nonneg
      _ = ∑ j ∈ Finset.range (i + 1), ((i.choose j : ℝ) *
              ‖iteratedFDeriv ℝ j
                (fun q : ℝ × ℝ => restartSmoothCutoff offset s q.1) q‖ *
              ‖iteratedFDeriv ℝ (i - j)
                (fun q : ℝ × ℝ =>
                  localRestartCoeff a₀ a (q.1 - offset) n) q‖) *
              valueCosWeight (k - i) n := by
            rw [Finset.sum_mul]
      _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
            restartCutoffDerivMajorant offset s hτ j *
            restartCoeffCoreMajorant a₀ src
              (restartSlabMin offset s) (restartSlabMax offset s) n := by
            apply Finset.sum_le_sum
            intro j hj
            have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
            have hjTop :
                ((j : ℕ∞) : WithTop ℕ∞) ≤
                  ((2 : ℕ∞) : WithTop ℕ∞) := by
              exact_mod_cast le_trans hji (le_trans hik hkNat)
            have hijTop :
                (((i - j : ℕ) : ℕ∞) : WithTop ℕ∞) ≤
                  ((2 : ℕ∞) : WithTop ℕ∞) := by
              exact_mod_cast le_trans (Nat.sub_le i j)
                (le_trans hik hkNat)
            have hjTopNat : (j : ℕ∞) ≤ (2 : ℕ∞) := by
              exact_mod_cast le_trans hji (le_trans hik hkNat)
            have hcut :
                ‖iteratedFDeriv ℝ j
                  (fun q : ℝ × ℝ =>
                    restartSmoothCutoff offset s q.1) q‖ ≤
                restartCutoffDerivMajorant offset s hτ j := by
              exact (norm_iteratedFDeriv_comp_fst_le
                (restartSmoothCutoff_contDiff
                  (offset := offset) (s := s)) hjTop q).trans
                  (restartCutoffDerivMajorant_spec hτ hjTopNat q.1)
            have hcoeffNorm :
                ‖iteratedFDeriv ℝ (i - j)
                  (fun q : ℝ × ℝ =>
                    localRestartCoeff a₀ a (q.1 - offset) n) q‖ ≤
                ‖iteratedFDeriv ℝ (i - j)
                  (fun t : ℝ =>
                    localRestartCoeff a₀ a (t - offset) n) q.1‖ :=
              norm_iteratedFDeriv_comp_fst_le hcoeff₀ hijTop q
            have hcore :
                ‖iteratedFDeriv ℝ (i - j)
                  (fun t : ℝ =>
                    localRestartCoeff a₀ a (t - offset) n) q.1‖ *
                  valueCosWeight (k - i) n ≤
                restartCoeffCoreMajorant a₀ src
                  (restartSlabMin offset s) (restartSlabMax offset s) n := by
              exact shiftedLocalRestartCoeff_valueWeight_le_core src
                hτnonneg hτmin hτmax (by omega)
            have hcoeffCos :
                ‖iteratedFDeriv ℝ (i - j)
                  (fun q : ℝ × ℝ =>
                    localRestartCoeff a₀ a (q.1 - offset) n) q‖ *
                  valueCosWeight (k - i) n ≤
                restartCoeffCoreMajorant a₀ src
                  (restartSlabMin offset s) (restartSlabMax offset s) n := by
              exact (mul_le_mul_of_nonneg_right hcoeffNorm
                (valueCosWeight_nonneg (k - i) n)).trans hcore
            have hCnonneg :
                0 ≤ restartCutoffDerivMajorant offset s hτ j :=
              restartCutoffDerivMajorant_nonneg hτ hjTopNat
            have hcoeffCos_nonneg :
                0 ≤ ‖iteratedFDeriv ℝ (i - j)
                  (fun q : ℝ × ℝ =>
                    localRestartCoeff a₀ a (q.1 - offset) n) q‖ *
                    valueCosWeight (k - i) n := by
              exact mul_nonneg (norm_nonneg _)
                (valueCosWeight_nonneg (k - i) n)
            calc
              ((i.choose j : ℝ) *
                  ‖iteratedFDeriv ℝ j
                    (fun q : ℝ × ℝ =>
                      restartSmoothCutoff offset s q.1) q‖ *
                  ‖iteratedFDeriv ℝ (i - j)
                    (fun q : ℝ × ℝ =>
                      localRestartCoeff a₀ a (q.1 - offset) n) q‖) *
                  valueCosWeight (k - i) n
                  = ((i.choose j : ℝ) *
                      ‖iteratedFDeriv ℝ j
                        (fun q : ℝ × ℝ =>
                          restartSmoothCutoff offset s q.1) q‖) *
                      (‖iteratedFDeriv ℝ (i - j)
                        (fun q : ℝ × ℝ =>
                          localRestartCoeff a₀ a (q.1 - offset) n) q‖ *
                        valueCosWeight (k - i) n) := by
                    ring
              _ ≤ ((i.choose j : ℝ) *
                    restartCutoffDerivMajorant offset s hτ j) *
                    restartCoeffCoreMajorant a₀ src
                      (restartSlabMin offset s)
                      (restartSlabMax offset s) n := by
                    have hleft :
                        (i.choose j : ℝ) *
                          ‖iteratedFDeriv ℝ j
                            (fun q : ℝ × ℝ =>
                              restartSmoothCutoff offset s q.1) q‖ ≤
                        (i.choose j : ℝ) *
                          restartCutoffDerivMajorant offset s hτ j :=
                      mul_le_mul_of_nonneg_left hcut (Nat.cast_nonneg _)
                    exact mul_le_mul hleft hcoeffCos hcoeffCos_nonneg
                      (mul_nonneg (Nat.cast_nonneg _) hCnonneg)
              _ = (i.choose j : ℝ) *
                    restartCutoffDerivMajorant offset s hτ j *
                    restartCoeffCoreMajorant a₀ src
                      (restartSlabMin offset s)
                      (restartSlabMax offset s) n := by
                    ring
      _ = (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
            restartCutoffDerivMajorant offset s hτ j) *
            restartCoeffCoreMajorant a₀ src
              (restartSlabMin offset s) (restartSlabMax offset s) n := by
            rw [Finset.sum_mul]
  calc
    (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i
          (fun q : ℝ × ℝ =>
            restartSmoothCutoff offset s q.1 *
              localRestartCoeff a₀ a (q.1 - offset) n) q‖ *
        ‖iteratedFDeriv ℝ (k - i)
          (fun q : ℝ × ℝ => cosineMode n q.2) q‖
        = (k.choose i : ℝ) *
          (‖iteratedFDeriv ℝ i
            (fun q : ℝ × ℝ =>
              restartSmoothCutoff offset s q.1 *
                localRestartCoeff a₀ a (q.1 - offset) n) q‖ *
            ‖iteratedFDeriv ℝ (k - i)
              (fun q : ℝ × ℝ => cosineMode n q.2) q‖) := by
          ring
    _ ≤ (k.choose i : ℝ) *
        ((∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
          restartCutoffDerivMajorant offset s hτ j) *
          restartCoeffCoreMajorant a₀ src
            (restartSlabMin offset s) (restartSlabMax offset s) n) :=
          mul_le_mul_of_nonneg_left hGcos (Nat.cast_nonneg _)
    _ = ((k.choose i : ℝ) *
          ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
            restartCutoffDerivMajorant offset s hτ j) *
          restartCoeffCoreMajorant a₀ src
            (restartSlabMin offset s) (restartSlabMax offset s) n := by
        ring

theorem concreteRestartValueMajorant_summable
    {a₀ : ℕ → ℝ} {M : ℝ} {a : ℝ → ℕ → ℝ} {offset s : ℝ}
    (hτ : 0 < s - offset) (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC2Coeff a) :
    ∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (concreteRestartValueMajorant a₀ src offset s hτ k) := by
  intro _k _hk
  exact (restartCoeffCoreMajorant_summable
    (restartSlabMin_pos hτ) ha₀ src).mul_left _

theorem concreteRestartGradMajorant_summable
    {a₀ : ℕ → ℝ} {M : ℝ} {a : ℝ → ℕ → ℝ} {offset s : ℝ}
    (hτ : 0 < s - offset) (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC2Coeff a) :
    ∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (concreteRestartGradMajorant a₀ src offset s hτ k) := by
  intro _k _hk
  exact (restartCoeffCoreMajorant_summable
    (restartSlabMin_pos hτ) ha₀ src).mul_left _

/-- Global value-summand bound from the two-sided compact support. -/
theorem cutoffValueTerm_restartSmoothCutoff_iteratedFDeriv_bound
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {offset s : ℝ}
    (hτ : 0 < s - offset) (src : DuhamelSourceTimeC2Coeff a) :
    ∀ (k n : ℕ) (q : ℝ × ℝ), (k : ℕ∞) ≤ (2 : ℕ∞) →
      ‖iteratedFDeriv ℝ k
        (cutoffValueTerm (restartSmoothCutoff offset s) a₀ a offset n)
          q‖ ≤
        concreteRestartValueMajorant a₀ src offset s hτ k n := by
  intro k n q hk
  by_cases hleft : q.1 < restartCutoffLeftOuter offset s
  · rw [cutoffValueTerm_restartSmoothCutoff_iteratedFDeriv_eq_zero_of_left
      hτ hleft]
    rw [norm_zero]
    exact concreteRestartValueMajorant_nonneg hτ src hk
  · by_cases hright : restartCutoffRightOuter offset s < q.1
    · rw [cutoffValueTerm_restartSmoothCutoff_iteratedFDeriv_eq_zero_of_right
        hτ hright]
      rw [norm_zero]
      exact concreteRestartValueMajorant_nonneg hτ src hk
    · have hL : restartCutoffLeftOuter offset s ≤ q.1 :=
        le_of_not_gt hleft
      have hR : q.1 ≤ restartCutoffRightOuter offset s :=
        le_of_not_gt hright
      exact cutoffValueTerm_restartSmoothCutoff_iteratedFDeriv_bound_of_mem_slab
        hτ src hL hR hk

/-- Global gradient-summand bound from the two-sided compact support. -/
theorem cutoffGradTerm_restartSmoothCutoff_iteratedFDeriv_bound
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {offset s : ℝ}
    (hτ : 0 < s - offset) (src : DuhamelSourceTimeC2Coeff a) :
    ∀ (k n : ℕ) (q : ℝ × ℝ), (k : ℕ∞) ≤ (2 : ℕ∞) →
      ‖iteratedFDeriv ℝ k
        (cutoffGradTerm (restartSmoothCutoff offset s)
          (resolverSpectralConcreteGradTerm a₀ a offset) n) q‖ ≤
        concreteRestartGradMajorant a₀ src offset s hτ k n := by
  intro k n q hk
  by_cases hleft : q.1 < restartCutoffLeftOuter offset s
  · rw [cutoffGradTerm_restartSmoothCutoff_iteratedFDeriv_eq_zero_of_left
      hτ hleft]
    rw [norm_zero]
    exact concreteRestartGradMajorant_nonneg hτ src hk
  · by_cases hright : restartCutoffRightOuter offset s < q.1
    · rw [cutoffGradTerm_restartSmoothCutoff_iteratedFDeriv_eq_zero_of_right
        hτ hright]
      rw [norm_zero]
      exact concreteRestartGradMajorant_nonneg hτ src hk
    · have hL : restartCutoffLeftOuter offset s ≤ q.1 :=
        le_of_not_gt hleft
      have hR : q.1 ≤ restartCutoffRightOuter offset s :=
        le_of_not_gt hright
      exact cutoffGradTerm_restartSmoothCutoff_iteratedFDeriv_bound_of_mem_slab
        hτ src hL hR hk

/-- Concrete cutoff instantiation of the generic producer. -/
theorem resolverSpectralJointC2At_of_restartSmoothCutoff
    {a₀ : ℕ → ℝ} {M : ℝ} {a : ℝ → ℕ → ℝ} {offset s x : ℝ}
    (hτ : 0 < s - offset) (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC2Coeff a) :
    ResolverSpectralJointC2At a₀ a offset s x :=
  resolverSpectralJointC2At_of_smooth_cutoff_contDiff_tsum
    (φ := restartSmoothCutoff offset s)
    (gradTerm := resolverSpectralConcreteGradTerm a₀ a offset)
    (vValue := concreteRestartValueMajorant a₀ src offset s hτ)
    (vGrad := concreteRestartGradMajorant a₀ src offset s hτ)
    (restartSmoothCutoff_eventually_eq_one hτ)
    (cutoffValueTerm_restartSmoothCutoff_contDiff src)
    (concreteRestartValueMajorant_summable hτ ha₀ src)
    (cutoffValueTerm_restartSmoothCutoff_iteratedFDeriv_bound hτ src)
    (cutoffGradTerm_restartSmoothCutoff_contDiff src)
    (concreteRestartGradMajorant_summable hτ ha₀ src)
    (cutoffGradTerm_restartSmoothCutoff_iteratedFDeriv_bound hτ src)
    (resolverSpectralGradSeries_eventuallyEq_concreteGradTerm hτ ha₀ src)

end ShenWork.IntervalResolverSpectralJointC2Concrete
