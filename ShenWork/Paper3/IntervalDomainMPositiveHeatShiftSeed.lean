import ShenWork.Paper2.IntervalChiNegTruncatedRestartStrictPos
import ShenWork.Paper2.IntervalTruncatedWeakBarrierComparison
import ShenWork.PDE.IntervalSemigroupUniform

open Filter Topology Set

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalMildPicardThreshold
  (unitClip unitClip_of_mem)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.Paper2.IntervalTruncatedWeakBarrierComparison

noncomputable section

namespace ShenWork.Paper3

open ShenWork.Paper2.BFormPositiveDatumNegPart

/-- A half-sized square-root seed leaves room for replacing the repository's
zero-time semigroup convention by a small strictly positive heat time. -/
def halfRestartSliceSqrtSeed
    (w : intervalDomainPoint → ℝ) : ℝ → ℝ :=
  fun y => restartSliceSqrtSeed w y / 2

theorem halfRestartSliceSqrtSeed_continuous
    {w : intervalDomainPoint → ℝ} (hw : Continuous w) :
    Continuous (halfRestartSliceSqrtSeed w) := by
  exact (restartSliceSqrtSeed_continuous hw).div_const 2

theorem halfRestartSliceSqrtSeed_pos
    {w : intervalDomainPoint → ℝ}
    (hw_pos : ∀ x : intervalDomainPoint, 0 < w x) :
    ∀ y : ℝ, 0 < halfRestartSliceSqrtSeed w y := by
  intro y
  exact div_pos (Real.sqrt_pos.mpr (hw_pos (unitClip y))) (by norm_num)

theorem halfRestartSliceSqrtSeed_squareHeatSeed
    {w : intervalDomainPoint → ℝ}
    (hw_cont : Continuous w)
    (hw_pos : ∀ x : intervalDomainPoint, 0 < w x) :
    SquareHeatSeed (intervalDomainLift w) (halfRestartSliceSqrtSeed w) := by
  refine
    { continuousOn := (halfRestartSliceSqrtSeed_continuous hw_cont).continuousOn
      nonneg := fun y _hy => (halfRestartSliceSqrtSeed_pos hw_pos y).le
      pos_somewhere := ?_
      square_le_initial := ?_ }
  · refine ⟨0, by norm_num, halfRestartSliceSqrtSeed_pos hw_pos 0⟩
  · intro y hy
    have hw_nonneg : 0 ≤ w (unitClip y) := (hw_pos (unitClip y)).le
    have hclip : w (unitClip y) = intervalDomainLift w y := by
      simp [intervalDomainLift, hy, unitClip_of_mem hy]
    have hsqrt : (Real.sqrt (w (unitClip y))) ^ 2 = w (unitClip y) :=
      Real.sq_sqrt hw_nonneg
    change (Real.sqrt (w (unitClip y)) / 2) ^ 2 ≤ intervalDomainLift w y
    rw [hclip] at hsqrt ⊢
    nlinarith [hw_nonneg]

/-- Spectral and positive-heat-time data attached to one strictly positive
continuous interval slice. -/
def PositiveHeatShiftSliceSeedData
    (w : intervalDomainPoint → ℝ) (M : ℝ) (δmax : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ < δmax ∧
    ∃ K : ℝ, ∃ f : ℝ → ℝ,
      f = halfRestartSliceSqrtSeed w ∧
      Continuous f ∧
      SquareHeatSeed (intervalDomainLift w) f ∧
      (∀ n, |cosineCoeffs f n| ≤ K) ∧
      Summable (fun n : ℕ => (cosineCoeffs f n) ^ 2) ∧
      ∀ x ∈ Icc (0 : ℝ) 1,
        squareHeatBarrier M f δ x ≤ intervalDomainLift w x

/-- A continuous strictly positive slice admits a small positive heat shift
at which the discounted squared Neumann heat flow is still below that slice.

The upper bound `δ < δmax` is retained for later uniform-strip arguments. -/
theorem positiveHeatShiftSliceSeedData_of_positive
    {w : intervalDomainPoint → ℝ} {M δmax : ℝ}
    (hw_cont : Continuous w)
    (hw_pos : ∀ x : intervalDomainPoint, 0 < w x)
    (hM : 0 ≤ M) (hδmax : 0 < δmax) :
    PositiveHeatShiftSliceSeedData w M δmax := by
  let f : ℝ → ℝ := halfRestartSliceSqrtSeed w
  have hf_cont : Continuous f := by
    simpa [f] using halfRestartSliceSqrtSeed_continuous hw_cont
  have hf_pos : ∀ y : ℝ, 0 < f y := by
    intro y
    simpa [f] using halfRestartSliceSqrtSeed_pos hw_pos y
  have hIcc_ne : (Icc (0 : ℝ) 1).Nonempty := ⟨0, by norm_num⟩
  obtain ⟨y₀, hy₀, hy₀_min⟩ :=
    isCompact_Icc.exists_isMinOn hIcc_ne hf_cont.continuousOn
  let c : ℝ := f y₀
  have hc_pos : 0 < c := by simpa [c] using hf_pos y₀
  have hc_le : ∀ y ∈ Icc (0 : ℝ) 1, c ≤ f y := by
    intro y hy
    exact hy₀_min hy
  have hsem :=
    ShenWork.IntervalSemigroupUniform.intervalFullSemigroup_tendstoUniformlyOn
      f hf_cont
  rw [Metric.tendstoUniformlyOn_iff] at hsem
  have hev_approx : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ∀ x ∈ Icc (0 : ℝ) 1,
        dist (f x) (intervalFullSemigroupOperator δ f x) < c :=
    hsem c hc_pos
  have hev_small : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < δmax := by
    exact (eventually_lt_nhds hδmax).filter_mono nhdsWithin_le_nhds
  have hev_pos : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ, happrox, hδlt, hδpos⟩ :=
    (hev_approx.and (hev_small.and hev_pos)).exists
  obtain ⟨B, hB⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn hf_cont.continuousOn
  let K₀ : ℝ := max B 0
  let K : ℝ := 2 * K₀
  have hK₀ : 0 ≤ K₀ := le_max_right _ _
  have hf_bound : ∀ y ∈ Icc (0 : ℝ) 1, |f y| ≤ K₀ := by
    intro y hy
    rw [← Real.norm_eq_abs]
    exact (hB y hy).trans (le_max_left _ _)
  have hcoeff : ∀ n, |cosineCoeffs f n| ≤ K := by
    simpa [K] using
      (cosineCoeffs_abs_le_of_continuous_bounded
        hf_cont.continuousOn hK₀ hf_bound)
  have hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2 :=
    cosineCoeffs_sq_summable_of_continuousOn hf_cont.continuousOn
  have hinitial : ∀ x ∈ Icc (0 : ℝ) 1,
      squareHeatBarrier M f δ x ≤ intervalDomainLift w x := by
    intro x hx
    have happ := happrox x hx
    rw [Real.dist_eq] at happ
    have hSf_lower : 0 ≤ intervalFullSemigroupOperator δ f x := by
      have hright : f x - intervalFullSemigroupOperator δ f x < c :=
        (abs_lt.mp happ).2
      nlinarith [hc_le x hx]
    have hSf_upper : intervalFullSemigroupOperator δ f x ≤ 2 * f x := by
      have hleft : -c < f x - intervalFullSemigroupOperator δ f x :=
        (abs_lt.mp happ).1
      nlinarith [hc_le x hx]
    have hsq : (intervalFullSemigroupOperator δ f x) ^ 2 ≤ (2 * f x) ^ 2 := by
      have htwo : 0 ≤ 2 * f x := mul_nonneg (by norm_num) (hf_pos x).le
      exact (sq_le_sq₀ hSf_lower htwo).2 hSf_upper
    have hseed_sq : (2 * f x) ^ 2 = intervalDomainLift w x := by
      have hw_nonneg : 0 ≤ w (unitClip x) := (hw_pos (unitClip x)).le
      have hclip : w (unitClip x) = intervalDomainLift w x := by
        simp [intervalDomainLift, hx, unitClip_of_mem hx]
      change (2 * (Real.sqrt (w (unitClip x)) / 2)) ^ 2 =
        intervalDomainLift w x
      rw [show 2 * (Real.sqrt (w (unitClip x)) / 2) =
          Real.sqrt (w (unitClip x)) by ring,
        Real.sq_sqrt hw_nonneg, hclip]
    have hexp : Real.exp (-M * δ) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hM) hδpos.le
    unfold squareHeatBarrier
    calc
      Real.exp (-M * δ) * (intervalFullSemigroupOperator δ f x) ^ 2
          ≤ 1 * (intervalFullSemigroupOperator δ f x) ^ 2 := by
            exact mul_le_mul_of_nonneg_right hexp (sq_nonneg _)
      _ ≤ (2 * f x) ^ 2 := by simpa using hsq
      _ = intervalDomainLift w x := hseed_sq
  refine ⟨δ, hδpos, hδlt, K, f, rfl, hf_cont, ?_, hcoeff, hl2, hinitial⟩
  simpa [f] using halfRestartSliceSqrtSeed_squareHeatSeed hw_cont hw_pos

end ShenWork.Paper3

#print axioms ShenWork.Paper3.positiveHeatShiftSliceSeedData_of_positive
