/-
  ShenWork/PDE/IntervalRestartDerivJointContinuity.lean

  **Joint (τ,x) continuity of the restart time-derivative field.**

  The restart cosine series `u(τ,x) = ∑' n, cₙ(τ) cos(nπx)` has time
  derivative (G4i) `∂_τ u = ∑' n, (a(τ,n) − λₙ cₙ(τ)) cos(nπx)`.

  We prove the derivative field is jointly continuous in `(τ,x)` on
  `Set.Ioi 0 ×ˢ Set.univ`.

  No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.PDE.IntervalSourceCoefficientTimeC1

open MeasureTheory Set
open scoped Topology

namespace ShenWork.IntervalRestartDerivJointContinuity

-- Open all the namespaces we need.
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalSourceCoefficientTimeC1
open ShenWork.IntervalDomainRegularityBootstrap
  (reciprocalSquareTerm reciprocalSquareTerm_summable)
open ShenWork.HeatKernelGradientEstimates
  (unitIntervalCosineHeatTrace_single_exp_summable)

/-! ## Auxiliary: eigenvalue * exp summability -/

/-- `∑ₙ λₙ e^{−τλₙ} < ∞` for `τ > 0`. -/
theorem eigenvalue_mul_exp_summable {τ : ℝ} (hτ : 0 < τ) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        Real.exp (-τ * unitIntervalCosineEigenvalue n)) := by
  have hc : 0 < τ * Real.pi ^ 2 := by positivity
  have hbase := (Real.summable_pow_mul_exp_neg_nat_mul 2 hc).mul_left
    (Real.pi ^ 2)
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity)
      (Real.exp_nonneg _)) (fun n => ?_) hbase
  simp only [unitIntervalCosineEigenvalue]
  calc ((n : ℝ) * Real.pi) ^ 2 *
        Real.exp (-τ * ((n : ℝ) * Real.pi) ^ 2)
      = (n : ℝ) ^ 2 * Real.pi ^ 2 *
          Real.exp (-(τ * Real.pi ^ 2) * (n : ℝ) ^ 2) := by ring_nf
    _ ≤ (n : ℝ) ^ 2 * Real.pi ^ 2 *
          Real.exp (-(τ * Real.pi ^ 2) * (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp_of_le
        have : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
          rcases Nat.eq_zero_or_pos n with h | h
          · simp [h]
          · exact le_self_pow₀ (Nat.one_le_cast.2 h) (by norm_num)
        nlinarith
    _ = Real.pi ^ 2 * ((n : ℝ) ^ 2 *
          Real.exp (-(τ * Real.pi ^ 2) * (n : ℝ))) := by ring

/-! ## Part 1: Duhamel derivative series -/

/-- Each summand `(a(τ,n) − λₙ bₙ(τ)) cos(nπx)` is jointly continuous. -/
private theorem duhamelDerivSummand_continuous
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ =>
      (a p.1 n - unitIntervalCosineEigenvalue n *
        duhamelSpectralCoeff a p.1 n) * cosineMode n p.2) := by
  apply Continuous.mul
  · exact (duhamelSpectralCoeff_deriv_continuous src n).comp continuous_fst
  · change Continuous (fun p : ℝ × ℝ => Real.cos ((n : ℝ) * Real.pi * p.2))
    exact Real.continuous_cos.comp (continuous_const.mul continuous_snd)

/-- **Part 1.** The Duhamel derivative series is ContinuousOn on `Ici 0 ×ˢ univ`. -/
theorem duhamelDerivSeries_continuousOn
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a) :
    ContinuousOn (fun p : ℝ × ℝ =>
      ∑' n, (a p.1 n - unitIntervalCosineEigenvalue n *
        duhamelSpectralCoeff a p.1 n) * cosineMode n p.2)
      (Ici (0 : ℝ) ×ˢ univ) := by
  apply continuousOn_tsum
    (fun n => (duhamelDerivSummand_continuous src n).continuousOn)
    (src.henv_summable.add (reciprocalSquareTerm_summable.mul_left src.derivBound))
  intro n p hp
  rw [Real.norm_eq_abs, abs_mul]
  have hcos : |cosineMode n p.2| ≤ 1 := by
    unfold cosineMode; exact Real.abs_cos_le_one _
  have ht : 0 ≤ p.1 := (mem_prod.1 hp).1
  have hcoeff := duhamelSpectralCoeff_deriv_summable_uniform_bound src ht n
  have hnn : 0 ≤ src.envelope n + src.derivBound * reciprocalSquareTerm n := by
    apply add_nonneg
    · exact le_trans (abs_nonneg _) (src.henv_bound 0 le_rfl n)
    · apply mul_nonneg
      · exact le_trans (abs_nonneg _) (src.hderivBound 0 le_rfl 0)
      · exact div_nonneg zero_le_one (sq_nonneg _)
  calc _ ≤ _ * 1 := mul_le_mul hcoeff hcos (abs_nonneg _) hnn
    _ = _ := mul_one _

/-! ## Part 2: Homogeneous derivative series -/

/-- Each summand `(-λₙ e^{−τλₙ} a₀ₙ) cos(nπx)` is jointly continuous. -/
private theorem homDerivSummand_continuous
    (a₀ : ℕ → ℝ) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ =>
      -(unitIntervalCosineEigenvalue n *
        Real.exp (-p.1 * unitIntervalCosineEigenvalue n)) *
          a₀ n * cosineMode n p.2) := by
  apply Continuous.mul
  · apply Continuous.mul
    · apply Continuous.neg
      exact continuous_const.mul
        (Real.continuous_exp.comp
          (continuous_fst.neg.mul continuous_const))
    · exact continuous_const
  · change Continuous (fun p : ℝ × ℝ => Real.cos ((n : ℝ) * Real.pi * p.2))
    exact Real.continuous_cos.comp (continuous_const.mul continuous_snd)

/-- **Part 2 (local).** The homogeneous derivative series is ContinuousOn on
`Ici ε ×ˢ univ` for each `ε > 0`. -/
theorem homDerivSeries_continuousOn_ici
    {a₀ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M) (ha₀ : ∀ n, |a₀ n| ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (fun p : ℝ × ℝ =>
      ∑' n, -(unitIntervalCosineEigenvalue n *
        Real.exp (-p.1 * unitIntervalCosineEigenvalue n)) *
          a₀ n * cosineMode n p.2)
      (Ici ε ×ˢ univ) := by
  apply continuousOn_tsum
    (fun n => (homDerivSummand_continuous a₀ n).continuousOn)
    ((eigenvalue_mul_exp_summable hε).mul_right M)
  intro n p hp
  have hτ : ε ≤ p.1 := (mem_prod.1 hp).1
  have hlam_nn : (0 : ℝ) ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue; positivity
  rw [Real.norm_eq_abs,
    show -(unitIntervalCosineEigenvalue n *
        Real.exp (-p.1 * unitIntervalCosineEigenvalue n)) *
          a₀ n * cosineMode n p.2 =
      -(unitIntervalCosineEigenvalue n *
        Real.exp (-p.1 * unitIntervalCosineEigenvalue n) *
          a₀ n * cosineMode n p.2) from by ring,
    abs_neg, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg hlam_nn, abs_of_nonneg (Real.exp_nonneg _)]
  have hcos : |cosineMode n p.2| ≤ 1 := by
    unfold cosineMode; exact Real.abs_cos_le_one _
  have hexp_mono : Real.exp (-p.1 * unitIntervalCosineEigenvalue n) ≤
      Real.exp (-ε * unitIntervalCosineEigenvalue n) :=
    Real.exp_le_exp_of_le (by nlinarith)
  calc unitIntervalCosineEigenvalue n *
        Real.exp (-p.1 * unitIntervalCosineEigenvalue n) *
          |a₀ n| * |cosineMode n p.2|
      ≤ unitIntervalCosineEigenvalue n *
          Real.exp (-ε * unitIntervalCosineEigenvalue n) * M * 1 := by
        apply mul_le_mul (mul_le_mul ?_ (ha₀ n) (abs_nonneg _) (by positivity))
          (hcos) (abs_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_left hexp_mono hlam_nn
    _ = unitIntervalCosineEigenvalue n *
          Real.exp (-ε * unitIntervalCosineEigenvalue n) * M := mul_one _

/-- **Part 2.** The homogeneous derivative series is ContinuousOn on
`Ioi 0 ×ˢ univ`. -/
theorem homDerivSeries_continuousOn
    {a₀ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M) (ha₀ : ∀ n, |a₀ n| ≤ M) :
    ContinuousOn (fun p : ℝ × ℝ =>
      ∑' n, -(unitIntervalCosineEigenvalue n *
        Real.exp (-p.1 * unitIntervalCosineEigenvalue n)) *
          a₀ n * cosineMode n p.2)
      (Ioi (0 : ℝ) ×ˢ univ) := by
  rw [(isOpen_Ioi.prod isOpen_univ).continuousOn_iff]
  intro ⟨τ₀, x₀⟩ hp
  have hτ₀ : 0 < τ₀ := (mem_prod.1 hp).1
  have hci := homDerivSeries_continuousOn_ici hM ha₀ (half_pos hτ₀)
  apply hci.continuousAt
  apply mem_nhds_iff.2
  refine ⟨Ioi (τ₀ / 2) ×ˢ univ, ?_, isOpen_Ioi.prod isOpen_univ, ?_⟩
  · exact prod_mono_left Ioi_subset_Ici_self
  · exact mem_prod.2 ⟨mem_Ioi.2 (by linarith), mem_univ _⟩

/-! ## Part 3: Combining the decomposition -/

/-- The restart derivative decomposes as Duhamel part + homogeneous part. -/
private theorem restartDeriv_eq_sum
    {a₀ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M) (ha₀ : ∀ n, |a₀ n| ≤ M)
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {τ : ℝ} (hτ : 0 < τ) (x : ℝ) :
    (∑' n, (a τ n - unitIntervalCosineEigenvalue n *
      localRestartCoeff a₀ a τ n) * cosineMode n x) =
    (∑' n, (a τ n - unitIntervalCosineEigenvalue n *
      duhamelSpectralCoeff a τ n) * cosineMode n x) +
    (∑' n, -(unitIntervalCosineEigenvalue n *
      Real.exp (-τ * unitIntervalCosineEigenvalue n)) *
        a₀ n * cosineMode n x) := by
  have hfun : (fun n => (a τ n - unitIntervalCosineEigenvalue n *
      localRestartCoeff a₀ a τ n) * cosineMode n x) =
    fun n => ((a τ n - unitIntervalCosineEigenvalue n *
        duhamelSpectralCoeff a τ n) * cosineMode n x +
      -(unitIntervalCosineEigenvalue n *
        Real.exp (-τ * unitIntervalCosineEigenvalue n)) *
          a₀ n * cosineMode n x) := by
    ext n; simp only [localRestartCoeff]; ring
  rw [hfun]
  have hcos_le : ∀ n, |cosineMode n x| ≤ 1 := fun n => by
    unfold cosineMode; exact Real.abs_cos_le_one _
  have hs1 : Summable (fun n => (a τ n - unitIntervalCosineEigenvalue n *
      duhamelSpectralCoeff a τ n) * cosineMode n x) := by
    apply Summable.of_norm
    refine (src.henv_summable.add
      (reciprocalSquareTerm_summable.mul_left src.derivBound)).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have hnn : 0 ≤ src.envelope n + src.derivBound * reciprocalSquareTerm n := by
      apply add_nonneg
      · exact le_trans (abs_nonneg _) (src.henv_bound 0 le_rfl n)
      · exact mul_nonneg (le_trans (abs_nonneg _) (src.hderivBound 0 le_rfl 0))
          (div_nonneg zero_le_one (sq_nonneg _))
    calc _ ≤ _ * 1 := mul_le_mul
          (duhamelSpectralCoeff_deriv_summable_uniform_bound src hτ.le n)
          (hcos_le n) (abs_nonneg _) hnn
      _ = _ := mul_one _
  have hs2 : Summable (fun n =>
      -(unitIntervalCosineEigenvalue n *
        Real.exp (-τ * unitIntervalCosineEigenvalue n)) *
          a₀ n * cosineMode n x) := by
    apply Summable.of_norm
    have ht2 : 0 < τ / 2 := by linarith
    refine ((eigenvalue_mul_exp_summable ht2).mul_right M).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun n => ?_)
    have hlam_nn : (0 : ℝ) ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue; positivity
    rw [Real.norm_eq_abs,
      show -(unitIntervalCosineEigenvalue n *
          Real.exp (-τ * unitIntervalCosineEigenvalue n)) *
            a₀ n * cosineMode n x =
        -(unitIntervalCosineEigenvalue n *
          Real.exp (-τ * unitIntervalCosineEigenvalue n) *
            a₀ n * cosineMode n x) from by ring,
      abs_neg, abs_mul, abs_mul, abs_mul, abs_of_nonneg hlam_nn,
      abs_of_nonneg (Real.exp_nonneg _)]
    have hexp_mono : Real.exp (-τ * unitIntervalCosineEigenvalue n) ≤
        Real.exp (-(τ / 2) * unitIntervalCosineEigenvalue n) :=
      Real.exp_le_exp_of_le (by nlinarith)
    calc unitIntervalCosineEigenvalue n *
          Real.exp (-τ * unitIntervalCosineEigenvalue n) *
            |a₀ n| * |cosineMode n x|
        ≤ unitIntervalCosineEigenvalue n *
            Real.exp (-(τ / 2) * unitIntervalCosineEigenvalue n) * M * 1 := by
          apply mul_le_mul (mul_le_mul ?_ (ha₀ n) (abs_nonneg _) (by positivity))
            (hcos_le n) (abs_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hexp_mono hlam_nn
      _ = unitIntervalCosineEigenvalue n *
            Real.exp (-(τ / 2) * unitIntervalCosineEigenvalue n) * M := mul_one _
  exact hs1.tsum_add hs2

/-- **Main theorem: Joint (τ,x) continuity of the restart time-derivative field.**

The time derivative `∂_τ u(τ,x) = ∑' n, (a(τ,n) − λₙ cₙ(τ)) cos(nπx)` is
jointly continuous on `Ioi 0 ×ˢ univ`. -/
theorem restartDerivField_continuousOn_joint
    {a₀ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M) (ha₀ : ∀ n, |a₀ n| ≤ M)
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a) :
    ContinuousOn
      (fun p : ℝ × ℝ =>
        ∑' n, (a p.1 n - unitIntervalCosineEigenvalue n *
          localRestartCoeff a₀ a p.1 n) * cosineMode n p.2)
      (Ioi (0 : ℝ) ×ˢ univ) := by
  intro ⟨τ₀, x₀⟩ hp
  have hτ₀ : 0 < τ₀ := (mem_prod.1 hp).1
  set f1 : ℝ × ℝ → ℝ := fun p =>
    ∑' n, (a p.1 n - unitIntervalCosineEigenvalue n *
      duhamelSpectralCoeff a p.1 n) * cosineMode n p.2
  set f2 : ℝ × ℝ → ℝ := fun p =>
    ∑' n, -(unitIntervalCosineEigenvalue n *
      Real.exp (-p.1 * unitIntervalCosineEigenvalue n)) *
        a₀ n * cosineMode n p.2
  have heq : ∀ p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ),
      (fun p : ℝ × ℝ =>
        ∑' n, (a p.1 n - unitIntervalCosineEigenvalue n *
          localRestartCoeff a₀ a p.1 n) * cosineMode n p.2) p =
      f1 p + f2 p := by
    intro ⟨τ, x⟩ hp'
    exact restartDeriv_eq_sum hM ha₀ src (mem_prod.1 hp').1 x
  apply ContinuousWithinAt.congr _ (fun p hp' => heq p hp')
    (heq ⟨τ₀, x₀⟩ hp)
  have hf1 : ContinuousOn f1 (Ioi (0 : ℝ) ×ˢ univ) :=
    (duhamelDerivSeries_continuousOn src).mono
      (Set.prod_mono_left Ioi_subset_Ici_self)
  have hf2 : ContinuousOn f2 (Ioi (0 : ℝ) ×ˢ univ) :=
    homDerivSeries_continuousOn hM ha₀
  exact (hf1.add hf2).continuousWithinAt hp

end ShenWork.IntervalRestartDerivJointContinuity
