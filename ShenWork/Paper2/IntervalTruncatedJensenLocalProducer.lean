import ShenWork.Paper2.IntervalChiNegAssembly
import ShenWork.Paper2.Batch1FoundationalLemmas

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
   restartSliceSqrtSeed restartSliceSqrtSeed_continuous
   )

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegAssembly

/-- Reaction-discounted semigroup lower bound restricted to the active
positive-time window.  Unlike the older global interface, this statement does
not ask a zero-extended local solution to propagate beyond its horizon. -/
def ReactionDiscountedMildLowerOn
    (T D : ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃s σ x : ℝ⦄, 0 < s → 0 < σ → s + σ ≤ T →
    Real.exp (-D * σ) *
        intervalFullSemigroupOperator σ (fun y => u s y) x
      ≤ u (s + σ) x

/-- A localized reaction-discounted lower bound supplies all Jensen witnesses.

Initial trace chooses a nonzero nonnegative restart slice.  Its square-root is
the seed; bounded continuity supplies full-kernel Jensen, and its square is
definitionally the clipped restart slice. -/
theorem truncatedJensenStrictPosDataFor_of_localizedDiscountedLower
    {T R D : ℝ} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hcont : HasContinuousSlices T u)
    (hnonneg :
      ∀ s, 0 < s → s ≤ T → ∀ x : intervalDomainPoint, 0 ≤ u s x)
    (hbound :
      ∀ s, 0 < s → s ≤ T → ∀ x : intervalDomainPoint, |u s x| ≤ R)
    (hlower :
      ReactionDiscountedMildLowerOn T D
        (fun r y => u r (unitClip y))) :
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
    have huy_nonneg : 0 ≤ u s (unitClip y) :=
      hnonneg s hs hsT (unitClip y)
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
  have hdiscount :
      Real.exp (-D * σ) *
          intervalFullSemigroupOperator σ
            (fun y => u s (unitClip y)) x.1
        ≤ u t x := by
    have h := hlower (s := s) (σ := σ) (x := x.1) hs hσ (by
      simpa [htime] using htT)
    simpa [htime, unitClip_of_mem x.2] using h
  have hS_pos : 0 < intervalFullSemigroupOperator σ f x.1 :=
    heat_seed_strict_pos_of_squareHeatSeed hσ hseed'
  exact ⟨D, s, σ, f, hσ, htime, hjensen, hseed_after_heat,
    hdiscount, hS_pos⟩

end ShenWork.Paper2.IntervalChiNegAssembly
