import ShenWork.Paper2.IntervalTruncatedJensenLocalProducer
import ShenWork.Paper2.IntervalTruncatedWeakBarrierComparisonClosure

/-!
# Strict-positivity producer for the Jensen field (χ₀ < 0 branch)

This file reduces the `jensenStrictPos` field of
`UniformTruncatedAssemblyInputs` to pointwise strict positivity of the
truncated Picard limit, and then produces that strict positivity.

Reduction step (this section): the witness tuple `(D, s, σ, f)` in
`TruncatedJensenStrictPosDataFor` is existential *per point* `(t, x)`, so the
discount `exp (-D * σ)` may be chosen after `σ`: any constant deficit between
the heat-propagated slice and the solution value is absorbed by taking
`D := max 0 (log (P / u t x)) / σ`. Consequently a uniform
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
open ShenWork.IntervalConjugatePicard
 (UniformConjugateMildExistenceCore)
open ShenWork.IntervalNeumannFullKernel
 (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.Paper2.BFormPositiveDatumNegPart
 (FullKernelJensenInequality SquareHeatSeed
 TruncatedConjugateMildExistenceData
 UniformTruncatedConjugateMapCertificateData
 heat_seed_strict_pos_of_squareHeatSeed
 restartSliceSqrtSeed restartSliceSqrtSeed_continuous squareHeatBarrier
 truncatedConjugatePicardLimit
 truncatedConjugatePicardLimit_initialTrace_of_truncated_data
 uniformTruncatedConjugateMildExistenceCore_of_uniformCore)

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegAssembly

/-- The per-point discount: `exp (-(max 0 (log (P / U)) / σ) * σ) * P ≤ U`
for `σ > 0` and `U > 0`. This is the elementary fact that lets a pointwise
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
 rw [Real.exp_neg, Real.exp_log hPU, inv_div]
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
 ShenWork.Paper2.BFormPositiveDatumNegPart.exists_restartSliceSqrtSeed_of_initialTrace
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
 ShenWork.Paper2.Batch1FoundationalLemmas.fullKernelJensenInequality_of_aestronglyMeasurable_bounded
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

/-! ## Strict positivity from the matched-divergence weak barrier -/

/-- The nonnegative truncated Picard limit dominates a strictly positive
squared Neumann heat barrier at every positive time. -/
theorem truncatedConjugatePicardLimit_strictPos
 {p : CM2Params} {M : ℝ} (hM : 0 < M)
 {u₀ : intervalDomainPoint → ℝ}
 (hu₀ : PositiveInitialDatum intervalDomain u₀)
 (hbound₀ : ∀ X, |u₀ X| ≤ M)
 (DT : TruncatedConjugateMildExistenceData p u₀) :
 ∀ t, 0 < t → t ≤ DT.T → ∀ X : intervalDomainPoint,
 0 < truncatedConjugatePicardLimit p u₀ DT.T t X := by
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 let f : ℝ → ℝ := restartSliceSqrtSeed u₀
 let Cf : ℝ := Real.sqrt M
 let K : ℝ := 2 * Cf
 have hu₀_nonneg : ∀ X : intervalDomainPoint, 0 ≤ u₀ X := by
 intro X
 simpa [intervalDomainLift, X.2] using
 ShenWork.Paper2.BFormPositiveDatumNegPart.positiveInitialDatum_intervalDomainLift_nonneg
 hu₀ X.1 X.2
 have hf : Continuous f := by
 simpa [f] using restartSliceSqrtSeed_continuous hu₀.admissible.2
 have hCf : 0 ≤ Cf := Real.sqrt_nonneg _
 have hf_bound : ∀ y, |f y| ≤ Cf := by
 intro y
 have huM : u₀ (unitClip y) ≤ M :=
 (le_abs_self _).trans (hbound₀ (unitClip y))
 change |Real.sqrt (u₀ (unitClip y))| ≤ Real.sqrt M
 rw [abs_of_nonneg (Real.sqrt_nonneg _)]
 exact Real.sqrt_le_sqrt huM
 have hK : ∀ n, |cosineCoeffs f n| ≤ K := by
 simpa [K, Cf] using
 (ShenWork.Paper2.IntervalTruncatedWeakBarrierComparison.cosineCoeffs_abs_le_of_continuous_bounded
 hf.continuousOn (Real.sqrt_nonneg M)
 (fun y _hy => by simpa [Cf] using hf_bound y))
 have hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2 :=
 ShenWork.Paper2.IntervalTruncatedWeakBarrierComparison.cosineCoeffs_sq_summable_of_continuousOn
 hf.continuousOn
 have hfsq : ∀ y ∈ Set.Icc (0 : ℝ) 1,
 f y ^ 2 = intervalDomainLift u₀ y := by
 intro y hy
 have hclip : u₀ (unitClip y) = intervalDomainLift u₀ y := by
 simp [intervalDomainLift, hy, unitClip_of_mem hy]
 have hnonneg : 0 ≤ u₀ (unitClip y) := hu₀_nonneg _
 change Real.sqrt (u₀ (unitClip y)) ^ 2 = intervalDomainLift u₀ y
 rw [Real.sq_sqrt hnonneg, hclip]
 have htrace : InitialTrace intervalDomain u₀ U := by
 simpa [U] using
 truncatedConjugatePicardLimit_initialTrace_of_truncated_data
 p hu₀.admissible.2 DT
 have hnonneg : ∀ r, 0 < r → r ≤ DT.T →
 ∀ X : intervalDomainPoint, 0 ≤ U r X := by
 intro r hr hrT X
 simpa [U] using
 ShenWork.Paper2.IntervalTruncatedEnergyProducer.truncatedConjugatePicardLimit_nonneg
 hu₀ DT r hr hrT X
 have hcompare :=
 ShenWork.Paper2.IntervalTruncatedWeakBarrierComparisonClosure.truncatedSquareHeatBarrier_le_truncatedLimit
 hu₀ DT htrace hnonneg hf hCf hf_bound hK hl2 hfsq
 have hseed : SquareHeatSeed (intervalDomainLift u₀) f := by
 have hpos : ∃ X : intervalDomainPoint, 0 < u₀ X := by
 let X : intervalDomainPoint :=
 ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩
 exact ⟨X, hu₀.pos (by
 change ((1 : ℝ) / 2) ∈ Set.Ioo (0 : ℝ) 1
 constructor <;> norm_num)⟩
 simpa [f] using
 ShenWork.Paper2.BFormPositiveDatumNegPart.restartSliceSqrtSeed_squareHeatSeed
 hu₀.admissible.2 hu₀_nonneg hpos
 intro t ht htT X
 have hS : 0 < intervalFullSemigroupOperator t f X.1 :=
 heat_seed_strict_pos_of_squareHeatSeed ht hseed
 have hbar : 0 < squareHeatBarrier
 (ShenWork.Paper2.IntervalTruncatedWeakBarrierComparisonClosure.truncatedBarrierDiscount
 p DT.M) f t X.1 := by
 exact mul_pos (Real.exp_pos _) (sq_pos_of_pos hS)
 exact hbar.trans_le (by simpa [U] using hcompare t ht htT X)

/-- Exact type of the `jensenStrictPos` field. -/
abbrev UniformTruncatedJensenStrictPosData (p : CM2Params) : Prop :=
 ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
 PositiveInitialDatum intervalDomain u₀ → (∀ X, |u₀ X| ≤ M) →
 ∀ C : UniformConjugateMildExistenceCore p u₀,
 TruncatedJensenStrictPosDataFor C.T
 (truncatedConjugatePicardLimit p u₀ C.T)

/-- Uniform Jensen strict-positivity producer, using the same truncated-map
certificate that supplies the mild existence datum in the assembly. -/
def uniformTruncatedJensenStrictPosData_producer
 (p : CM2Params) (Hmap : UniformTruncatedConjugateMapCertificateData p) :
 UniformTruncatedJensenStrictPosData p := by
 intro M hM u₀ hu₀ hbound₀ C
 let A := Hmap hM hu₀ hbound₀ C
 let HT := uniformTruncatedConjugateMildExistenceCore_of_uniformCore C A
 let DT : TruncatedConjugateMildExistenceData p u₀ := HT.toData
 let U := truncatedConjugatePicardLimit p u₀ C.T
 have htrace : InitialTrace intervalDomain u₀ U := by
 simpa [U, DT, HT] using
 truncatedConjugatePicardLimit_initialTrace_of_truncated_data
 p hu₀.admissible.2 DT
 have hcont : HasContinuousSlices C.T U := by
 simpa [U, DT, HT] using HT.solutionData.hcont
 have hnonneg : ∀ r, 0 < r → r ≤ C.T →
 ∀ X : intervalDomainPoint, 0 ≤ U r X := by
 intro r hr hrT X
 simpa [U, DT, HT] using
 ShenWork.Paper2.IntervalTruncatedEnergyProducer.truncatedConjugatePicardLimit_nonneg
 hu₀ DT r hr hrT X
 have hbound : ∀ r, 0 < r → r ≤ C.T →
 ∀ X : intervalDomainPoint, |U r X| ≤ C.R := by
 intro r hr hrT X
 simpa [U, DT, HT] using HT.solutionData.hbound r hr hrT X
 have hpos : ∀ r, 0 < r → r ≤ C.T →
 ∀ X : intervalDomainPoint, 0 < U r X := by
 intro r hr hrT X
 simpa [U, DT, HT] using
 truncatedConjugatePicardLimit_strictPos hM hu₀ hbound₀ DT
 r hr hrT X
 exact truncatedJensenStrictPosDataFor_of_strictPos
 hu₀ htrace hcont hnonneg hbound hpos

end ShenWork.Paper2.IntervalChiNegAssembly
