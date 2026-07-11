import ShenWork.Paper2.IntervalTruncatedJensenLocalProducer

/-!
# Strict-positivity producer for the V6 Jensen field (χ₀ < 0 branch)

This file reduces the `jensenStrictPos` field of
`UniformTruncatedV6AssemblyInputs` to pointwise strict positivity of the
truncated Picard limit, and then produces that strict positivity.

Reduction step (this section): the witness tuple `(D, s, σ, f)` in
`TruncatedJensenStrictPosDataFor` is existential *per point* `(t, x)`, so the
discount `exp (-D * σ)` may be chosen after `σ`: any constant deficit between
the heat-propagated slice and the solution value is absorbed by taking
`D := max 0 (log (P / u t x)) / σ`.  Consequently a uniform
reaction-discounted comparison is not needed; pointwise strict positivity
plus the existing restart-slice seed machinery supplies every witness field.
-/

open Set MeasureTheory

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalMildPicard
  (HasContinuousSlices)
open ShenWork.IntervalMildPicardThreshold
  (unitClip unitClip_of_mem)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator)
open ShenWork.Paper2.BFormPositiveDatumNegPart
  (FullKernelJensenInequality SquareHeatSeed
   heat_seed_strict_pos_of_squareHeatSeed
   restartSliceSqrtSeed restartSliceSqrtSeed_continuous)

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegV6Assembly

/-- The per-point discount: `exp (-(max 0 (log (P / U)) / σ) * σ) * P ≤ U`
for `σ > 0` and `U > 0`.  This is the elementary fact that lets a pointwise
positivity statement absorb any constant comparison deficit. -/
theorem exp_neg_maxLog_div_mul_le
    {P U σ : ℝ} (hσ : 0 < σ) (hU : 0 < U) :
    Real.exp (-(max 0 (Real.log (P / U)) / σ) * σ) * P ≤ U := by
  have hDσ : max 0 (Real.log (P / U)) / σ * σ = max 0 (Real.log (P / U)) :=
    div_mul_cancel₀ _ hσ.ne'
  rw [neg_mul, hDσ]
  by_cases hP : 0 < P
  · have hlog : Real.log (P / U) ≤ max 0 (Real.log (P / U)) :=
      le_max_right _ _
    have hexp :
        Real.exp (-(max 0 (Real.log (P / U)))) ≤
          Real.exp (-(Real.log (P / U))) :=
      Real.exp_le_exp.mpr (neg_le_neg hlog)
    have hPU : 0 < P / U := div_pos hP hU
    have hexp_log : Real.exp (-(Real.log (P / U))) = U / P := by
      rw [Real.exp_neg, Real.exp_log hPU, one_div_div]
    calc Real.exp (-(max 0 (Real.log (P / U)))) * P
        ≤ Real.exp (-(Real.log (P / U))) * P :=
          mul_le_mul_of_nonneg_right hexp hP.le
      _ = U / P * P := by rw [hexp_log]
      _ = U := div_mul_cancel₀ U hP.ne'
  · have hP0 : P ≤ 0 := le_of_not_gt hP
    have : Real.exp (-(max 0 (Real.log (P / U)))) * P ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hP0
    linarith

/-- Pointwise strict positivity of the trajectory on the positive-time window
supplies all Jensen witnesses.

The restart slice at a small time `s < t` provides the square-root seed `f`
(with `f ^ 2` definitionally the clipped slice), full-kernel Jensen holds for
any bounded measurable seed, kernel strict positivity gives `0 < S σ f x`,
and the discounted comparison field is closed by choosing the per-point
discount `D` after `σ`, using `exp_neg_maxLog_div_mul_le`. -/
theorem truncatedJensenStrictPosDataFor_of_strictPos
    {T R : ℝ} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hcont : HasContinuousSlices T u)
    (hnonneg :
      ∀ s, 0 < s → s ≤ T → ∀ x : intervalDomainPoint, 0 ≤ u s x)
    (hbound :
      ∀ s, 0 < s → s ≤ T → ∀ x : intervalDomainPoint, |u s x| ≤ R)
    (hpos :
      ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint, 0 < u t x) :
    TruncatedJensenStrictPosDataFor T u := by
  constructor
  intro t ht htT x
  rcases
      ShenWork.Paper2.BFormPositiveDatumNegPart.
        exists_restartSliceSqrtSeed_of_initialTrace
        hu₀ htrace hcont hnonneg hbound ht htT with
    ⟨s, hs, hst, hsT, hseed⟩
  let σ : ℝ := t - s
  let f : ℝ → ℝ := restartSliceSqrtSeed (u s)
  have hσ : 0 < σ := by
    dsimp [σ]
    linarith
  have htime : s + σ = t := by
    dsimp [σ]
    ring
  have hf_cont : Continuous f := by
    simpa [f] using restartSliceSqrtSeed_continuous (hcont s hs hsT)
  have hf_meas : AEStronglyMeasurable f (intervalMeasure 1) :=
    hf_cont.aestronglyMeasurable
  have hf_bdd : ∀ y, |f y| ≤ Real.sqrt R := by
    intro y
    have huy_le : u s (unitClip y) ≤ R :=
      (le_abs_self (u s (unitClip y))).trans
        (hbound s hs hsT (unitClip y))
    change |Real.sqrt (u s (unitClip y))| ≤ Real.sqrt R
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt huy_le
  have hjensen : FullKernelJensenInequality f :=
    ShenWork.Paper2.Batch1FoundationalLemmas.
      fullKernelJensenInequality_of_aestronglyMeasurable_bounded
        hf_meas hf_bdd
  have hseed' : SquareHeatSeed (intervalDomainLift (u s)) f := by
    simpa [f] using hseed
  have hsq :
      (fun y : ℝ => (f y) ^ 2) = fun y => u s (unitClip y) := by
    funext y
    change (Real.sqrt (u s (unitClip y))) ^ 2 = u s (unitClip y)
    exact Real.sq_sqrt (hnonneg s hs hsT (unitClip y))
  have hseed_after_heat :
      intervalFullSemigroupOperator σ (fun y => (f y) ^ 2) x.1 ≤
        intervalFullSemigroupOperator σ
          (fun y => u s (unitClip y)) x.1 := by
    rw [hsq]
  have hS_pos : 0 < intervalFullSemigroupOperator σ f x.1 :=
    heat_seed_strict_pos_of_squareHeatSeed hσ hseed'
  have hU : 0 < u t x := hpos t ht htT x
  refine
    ⟨max 0
        (Real.log
          ((intervalFullSemigroupOperator σ
              (fun y => u s (unitClip y)) x.1) / u t x)) / σ,
      s, σ, f, hσ, htime, hjensen, hseed_after_heat, ?_, hS_pos⟩
  exact exp_neg_maxLog_div_mul_le hσ hU

end ShenWork.Paper2.IntervalChiNegV6Assembly
