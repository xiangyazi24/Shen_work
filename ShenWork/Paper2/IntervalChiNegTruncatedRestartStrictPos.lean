import ShenWork.Paper2.IntervalChiNegUniformCoreComplete
import ShenWork.PDE.IntervalHeatSemigroupStrictPositivity

open Filter Topology Set MeasureTheory

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalDomainSupNorm)
open ShenWork.IntervalMildPicard
  (HasContinuousSlices)
open ShenWork.IntervalMildPicardThreshold
  (unitClip unitClip_continuous unitClip_of_mem)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildSolutionData UniformConjugateMildExistenceCore
   conjugatePicardLimit)

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-- Continuity of the concrete interval lift on the closed unit interval. -/
theorem intervalDomainLift_continuousOn_Icc_of_continuous_restart
    {f : intervalDomainPoint → ℝ} (hf : Continuous f) :
    ContinuousOn (intervalDomainLift f) (Set.Icc (0 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_restrict]
  have heq : (Set.Icc (0 : ℝ) 1).restrict (intervalDomainLift f) = f := by
    funext ⟨y, hy⟩
    simp only [Set.restrict_apply, intervalDomainLift]
    rw [dif_pos hy]
    exact congrArg f (Subtype.ext rfl)
  rw [heq]
  exact hf

/-- The square-root seed cut from a positive-time slice. -/
def restartSliceSqrtSeed
    (w : intervalDomainPoint → ℝ) : ℝ → ℝ :=
  fun y => Real.sqrt (w (unitClip y))

theorem restartSliceSqrtSeed_continuous
    {w : intervalDomainPoint → ℝ} (hw : Continuous w) :
    Continuous (restartSliceSqrtSeed w) := by
  exact Real.continuous_sqrt.comp (hw.comp unitClip_continuous)

/-- A nonnegative, nonzero positive-time slice supplies a square-heat seed
with initial comparison `f^2 <= w`. -/
theorem restartSliceSqrtSeed_squareHeatSeed
    {w : intervalDomainPoint → ℝ}
    (hw_cont : Continuous w)
    (hw_nonneg : ∀ x : intervalDomainPoint, 0 ≤ w x)
    (hw_pos : ∃ x : intervalDomainPoint, 0 < w x) :
    SquareHeatSeed (intervalDomainLift w) (restartSliceSqrtSeed w) where
  continuousOn := (restartSliceSqrtSeed_continuous hw_cont).continuousOn
  nonneg := by
    intro y _hy
    exact Real.sqrt_nonneg _
  pos_somewhere := by
    rcases hw_pos with ⟨x₀, hx₀_pos⟩
    refine ⟨x₀.1, x₀.2, ?_⟩
    have hclip : w (unitClip x₀.1) = w x₀ := by
      simp [unitClip_of_mem x₀.2]
    exact Real.sqrt_pos.mpr (by
      simpa [restartSliceSqrtSeed, hclip] using hx₀_pos)
  square_le_initial := by
    intro y hy
    have hclip : w (unitClip y) = intervalDomainLift w y := by
      simp [intervalDomainLift, hy, unitClip_of_mem hy]
    have hnonneg : 0 ≤ w (unitClip y) := hw_nonneg _
    calc
      restartSliceSqrtSeed w y ^ 2
          = w (unitClip y) := by
            simp [restartSliceSqrtSeed, Real.sq_sqrt hnonneg]
      _ = intervalDomainLift w y := hclip
      _ ≤ intervalDomainLift w y := le_rfl

/-- For bounded data, the concrete interval sup-norm dominates point values. -/
theorem intervalDomain_abs_le_supNorm_of_bddAbove_restart
    {f : intervalDomainPoint → ℝ}
    (hbdd : BddAbove (Set.range (fun x : intervalDomainPoint => |f x|))) :
    ∀ x : intervalDomainPoint, |f x| ≤ intervalDomain.supNorm f := by
  intro x
  change |f x| ≤ intervalDomainSupNorm f
  unfold intervalDomainSupNorm
  exact le_csSup hbdd ⟨x, rfl⟩

theorem intervalDomain_pointwise_abs_lt_of_supNorm_lt_restart
    {f : intervalDomainPoint → ℝ} {ε : ℝ}
    (hbdd : BddAbove (Set.range (fun x : intervalDomainPoint => |f x|)))
    (hsup : intervalDomain.supNorm f < ε) :
    ∀ x : intervalDomainPoint, |f x| < ε := by
  intro x
  exact lt_of_le_of_lt
    (intervalDomain_abs_le_supNorm_of_bddAbove_restart hbdd x) hsup

/-- If two slices are bounded in absolute value, so is their difference. -/
theorem bddAbove_abs_sub_of_bddAbove_abs_restart
    {X : Type*} {f g : X → ℝ}
    (hf : BddAbove (Set.range (fun x : X => |f x|)))
    (hg : BddAbove (Set.range (fun x : X => |g x|))) :
    BddAbove (Set.range (fun x : X => |f x - g x|)) := by
  obtain ⟨Mf, hMf⟩ := hf
  obtain ⟨Mg, hMg⟩ := hg
  refine ⟨Mf + Mg, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hf_le : |f x| ≤ Mf := hMf ⟨x, rfl⟩
  have hg_le : |g x| ≤ Mg := hMg ⟨x, rfl⟩
  calc
    |f x - g x| ≤ |f x| + |g x| := abs_sub _ _
    _ ≤ Mf + Mg := add_le_add hf_le hg_le

theorem bddAbove_abs_of_uniform_bound_restart
    {X : Type*} {f : X → ℝ} {R : ℝ}
    (hf : ∀ x : X, |f x| ≤ R) :
    BddAbove (Set.range (fun x : X => |f x|)) := by
  exact ⟨R, by
    rintro _ ⟨x, rfl⟩
    exact hf x⟩

/-- Initial trace and nonnegativity give a positive square-root seed at some
restart time `s` with `0 < s < t`. -/
theorem exists_restartSliceSqrtSeed_of_initialTrace
    {T R : ℝ} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hcont : HasContinuousSlices T u)
    (hnonneg :
      ∀ s, 0 < s → s ≤ T → ∀ x : intervalDomainPoint, 0 ≤ u s x)
    (hbound :
      ∀ s, 0 < s → s ≤ T → ∀ x : intervalDomainPoint, |u s x| ≤ R)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    ∃ s, 0 < s ∧ s < t ∧ s ≤ T ∧
      SquareHeatSeed (intervalDomainLift (u s))
        (restartSliceSqrtSeed (u s)) := by
  let xₘ : intervalDomainPoint :=
    ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩
  have hxₘ_inside : xₘ ∈ intervalDomain.inside := by
    change ((1 : ℝ) / 2) ∈ Set.Ioo (0 : ℝ) 1
    constructor <;> norm_num
  have hu₀_pos : 0 < u₀ xₘ := hu₀.pos hxₘ_inside
  have hε : 0 < u₀ xₘ / 2 := by linarith
  obtain ⟨δ, hδ, hsmall⟩ := InitialTrace.eventually_small htrace hε
  let s : ℝ := min (t / 2) (δ / 2)
  have hs_pos : 0 < s := by
    dsimp [s]
    exact lt_min (by linarith) (by linarith)
  have hs_lt_t : s < t := by
    have hle : s ≤ t / 2 := min_le_left _ _
    linarith
  have hs_lt_δ : s < δ := by
    have hle : s ≤ δ / 2 := min_le_right _ _
    linarith
  have hs_le_T : s ≤ T := le_trans (le_of_lt hs_lt_t) htT
  have hsup :
      intervalDomain.supNorm (fun x : intervalDomainPoint => u s x - u₀ x)
        < u₀ xₘ / 2 :=
    hsmall s hs_pos hs_lt_δ
  have hu_bdd :
      BddAbove (Set.range (fun x : intervalDomainPoint => |u s x|)) :=
    bddAbove_abs_of_uniform_bound_restart (hbound s hs_pos hs_le_T)
  have hu₀_bdd :
      BddAbove (Set.range (fun x : intervalDomainPoint => |u₀ x|)) :=
    hu₀.admissible.1
  have hdiff_bdd :
      BddAbove
        (Set.range (fun x : intervalDomainPoint => |u s x - u₀ x|)) :=
    bddAbove_abs_sub_of_bddAbove_abs_restart hu_bdd hu₀_bdd
  have hpoint :
      |u s xₘ - u₀ xₘ| < u₀ xₘ / 2 :=
    intervalDomain_pointwise_abs_lt_of_supNorm_lt_restart hdiff_bdd hsup xₘ
  have hus_pos : 0 < u s xₘ := by
    have hleft := (abs_lt.mp hpoint).1
    linarith
  refine ⟨s, hs_pos, hs_lt_t, hs_le_T, ?_⟩
  exact restartSliceSqrtSeed_squareHeatSeed
    (hcont s hs_pos hs_le_T)
    (hnonneg s hs_pos hs_le_T)
    ⟨xₘ, hus_pos⟩

/-- Restarted strict-positivity input for the truncated limit.

For each target time `t`, the seed is chosen at a positive time `s < t`.  The
comparison inequality is therefore an elapsed-time barrier on the restarted
strip `[s, t]`; the seed field records `f^2 <= u(s)`. -/
structure TruncatedRestartSquareHeatStrictPosInputs
    (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ) where
  Mbar : ℝ
  lowerBarrier :
    ∀ t, 0 < t → t ≤ T →
      ∃ s, 0 < s ∧ s < t ∧ s ≤ T ∧
        ∃ f : ℝ → ℝ,
          SquareHeatSeed (intervalDomainLift (u s)) f ∧
          (∀ x : intervalDomainPoint,
            squareHeatBarrier Mbar f (t - s) x.1 ≤ u t x)

theorem strictPos_of_truncatedRestartSquareHeatStrictPosInputs
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (H : TruncatedRestartSquareHeatStrictPosInputs T u) :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint, 0 < u t x := by
  intro t ht htT x
  rcases H.lowerBarrier t ht htT with
    ⟨s, hs_pos, hs_lt_t, _hs_le_T, f, hseed, hbarrier⟩
  have hts : 0 < t - s := by linarith
  exact lt_of_lt_of_le
    (squareHeatBarrier_pos (M := H.Mbar) (t := t - s) hts
      hseed.continuousOn hseed.nonneg hseed.pos_somewhere x.1)
    (hbarrier x)

/-- Restart comparison supplied by the square-heat subsolution calculation on
the shifted strip.  The seed relation is `f^2 <= u(s)`, not an assertion about
the stalled value of `S_N(0)`. -/
structure TruncatedRestartSquareHeatComparisonData
    (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ) where
  Mbar : ℝ
  compareFromSeed :
    ∀ {s t : ℝ} {f : ℝ → ℝ},
      0 < s → s < t → t ≤ T →
      SquareHeatSeed (intervalDomainLift (u s)) f →
      ∀ x : intervalDomainPoint,
        squareHeatBarrier Mbar f (t - s) x.1 ≤ u t x

/-- The restart comparison plus weak-PID positivity at the initial trace gives
strict positivity at every positive target time. -/
theorem strictPos_of_truncatedRestartSquareHeatComparisonData
    {T R : ℝ} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hcont : HasContinuousSlices T u)
    (hnonneg :
      ∀ s, 0 < s → s ≤ T → ∀ x : intervalDomainPoint, 0 ≤ u s x)
    (hbound :
      ∀ s, 0 < s → s ≤ T → ∀ x : intervalDomainPoint, |u s x| ≤ R)
    (H : TruncatedRestartSquareHeatComparisonData T u) :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint, 0 < u t x := by
  intro t ht htT x
  rcases exists_restartSliceSqrtSeed_of_initialTrace
      hu₀ htrace hcont hnonneg hbound ht htT with
    ⟨s, hs_pos, hs_lt_t, _hs_le_T, hseed⟩
  have hts : 0 < t - s := by linarith
  exact lt_of_lt_of_le
    (squareHeatBarrier_pos (M := H.Mbar) (t := t - s) hts
      hseed.continuousOn hseed.nonneg hseed.pos_somewhere x.1)
    (H.compareFromSeed
      (s := s) (t := t) (f := restartSliceSqrtSeed (u s))
      hs_pos hs_lt_t htT hseed x)

def truncatedRestartStrictPosInputs_of_comparisonData
    {T R : ℝ} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hcont : HasContinuousSlices T u)
    (hnonneg :
      ∀ s, 0 < s → s ≤ T → ∀ x : intervalDomainPoint, 0 ≤ u s x)
    (hbound :
      ∀ s, 0 < s → s ≤ T → ∀ x : intervalDomainPoint, |u s x| ≤ R)
    (H : TruncatedRestartSquareHeatComparisonData T u) :
    TruncatedRestartSquareHeatStrictPosInputs T u where
  Mbar := H.Mbar
  lowerBarrier := by
    intro t ht htT
    rcases exists_restartSliceSqrtSeed_of_initialTrace
        hu₀ htrace hcont hnonneg hbound ht htT with
      ⟨s, hs_pos, hs_lt_t, hs_le_T, hseed⟩
    refine ⟨s, hs_pos, hs_lt_t, hs_le_T, restartSliceSqrtSeed (u s),
      hseed, ?_⟩
    exact H.compareFromSeed
      (s := s) (t := t) (f := restartSliceSqrtSeed (u s))
      hs_pos hs_lt_t htT hseed

end ShenWork.Paper2.BFormPositiveDatumNegPart

namespace ShenWork.Paper2.IntervalChiNegFinalAssemblyV3

open ShenWork.Paper2.BFormPositiveDatumNegPart

/-- Restart-seeded replacement for `UniformTruncatedStampacchiaBarrierInputs`.
It avoids the `t = 0` square-heat convention by asking for a lower barrier
started from a positive slice `u(s)`. -/
structure UniformTruncatedRestartStampacchiaBarrierInputs
    (p : CM2Params) where
  truncCore :
    ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) →
      ∀ C : UniformConjugateMildExistenceCore p u₀,
        UniformTruncatedConjugateMildExistenceCore p C
  energy :
    ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) →
      ∀ C : UniformConjugateMildExistenceCore p u₀,
        NegativePartEnergyCoreRegularDataFor p C.T
          (truncatedConjugatePicardLimit p u₀ C.T)
  restartComparison :
    ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) →
      ∀ C : UniformConjugateMildExistenceCore p u₀,
        TruncatedRestartSquareHeatComparisonData C.T
          (truncatedConjugatePicardLimit p u₀ C.T)
  initialTrace :
    ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) →
      ∀ C : UniformConjugateMildExistenceCore p u₀,
        InitialTrace intervalDomain u₀
          (truncatedConjugatePicardLimit p u₀ C.T)
  agreesWithFullPicard :
    ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) →
      ∀ C : UniformConjugateMildExistenceCore p u₀,
        truncatedConjugatePicardLimit p u₀ C.T =
          conjugatePicardLimit p u₀ C.T

theorem uniformCoreStampacchiaPackage_of_truncatedRestartStrategy
    {p : CM2Params}
    (H : UniformTruncatedRestartStampacchiaBarrierInputs p) :
    UniformCoreStampacchiaPackage p := by
  intro M hM u₀ hu₀ hbound C _hnonneg_old _hpos_old
  let HT := H.truncCore (M := M) hM hu₀ hbound C
  have hnonnegT :
      ∀ t, 0 < t → t ≤ C.T → ∀ x : intervalDomainPoint,
        0 ≤ truncatedConjugatePicardLimit p u₀ C.T t x :=
    nonneg_of_negativePartEnergyCoreRegularDataFor
      (H.energy (M := M) hM hu₀ hbound C)
  have hposT :
      ∀ t, 0 < t → t ≤ C.T → ∀ x : intervalDomainPoint,
        0 < truncatedConjugatePicardLimit p u₀ C.T t x := by
    have hcontT :
        HasContinuousSlices C.T
          (truncatedConjugatePicardLimit p u₀ C.T) := by
      simpa [UniformTruncatedConjugateMildExistenceCore.toData]
        using (HT.solutionData).hcont
    have hboundT :
        ∀ t, 0 < t → t ≤ C.T → ∀ x : intervalDomainPoint,
          |truncatedConjugatePicardLimit p u₀ C.T t x| ≤ C.R := by
      intro t ht htT x
      simpa [UniformTruncatedConjugateMildExistenceCore.toData]
        using (HT.solutionData).hbound t ht htT x
    exact strictPos_of_truncatedRestartSquareHeatComparisonData
      hu₀
      (H.initialTrace (M := M) hM hu₀ hbound C)
      hcontT hnonnegT hboundT
      (H.restartComparison (M := M) hM hu₀ hbound C)
  let S : ConjugateMildSolutionData p u₀ :=
    conjugateMildSolutionData_of_uniformTruncatedCore HT hnonnegT hposT
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · dsimp [S, conjugateMildSolutionData_of_uniformTruncatedCore]
    exact H.agreesWithFullPicard (M := M) hM hu₀ hbound C
  · dsimp [S, conjugateMildSolutionData_of_uniformTruncatedCore]
    exact H.initialTrace (M := M) hM hu₀ hbound C

theorem uniformCoreMildSolutionConditionalInputs_of_truncatedRestartStrategy
    {p : CM2Params}
    (H : UniformTruncatedRestartStampacchiaBarrierInputs p) :
    UniformCoreMildSolutionConditionalInputs p where
  hnonneg := by
    intro M hM u₀ hu₀ hbound C t ht htT x
    have hT :=
      nonneg_of_negativePartEnergyCoreRegularDataFor
        (H.energy (M := M) hM hu₀ hbound C) t ht htT x
    simpa [H.agreesWithFullPicard (M := M) hM hu₀ hbound C] using hT
  hpos := by
    intro M hM u₀ hu₀ hbound C t ht htT x
    let HT := H.truncCore (M := M) hM hu₀ hbound C
    have hnonnegT :
      ∀ t, 0 < t → t ≤ C.T → ∀ x : intervalDomainPoint,
        0 ≤ truncatedConjugatePicardLimit p u₀ C.T t x :=
      nonneg_of_negativePartEnergyCoreRegularDataFor
        (H.energy (M := M) hM hu₀ hbound C)
    have hcontT :
        HasContinuousSlices C.T
          (truncatedConjugatePicardLimit p u₀ C.T) := by
      simpa [UniformTruncatedConjugateMildExistenceCore.toData]
        using (HT.solutionData).hcont
    have hboundT :
        ∀ t, 0 < t → t ≤ C.T → ∀ x : intervalDomainPoint,
          |truncatedConjugatePicardLimit p u₀ C.T t x| ≤ C.R := by
      intro t ht htT x
      simpa [UniformTruncatedConjugateMildExistenceCore.toData]
        using (HT.solutionData).hbound t ht htT x
    have hT :=
      strictPos_of_truncatedRestartSquareHeatComparisonData
        hu₀
        (H.initialTrace (M := M) hM hu₀ hbound C)
        hcontT hnonnegT hboundT
        (H.restartComparison (M := M) hM hu₀ hbound C) t ht htT x
    simpa [H.agreesWithFullPicard (M := M) hM hu₀ hbound C] using hT
  package := uniformCoreStampacchiaPackage_of_truncatedRestartStrategy H

theorem uniformCoreMildSolutionFrontier_of_truncatedRestartStrategy
    {p : CM2Params}
    (H : UniformTruncatedRestartStampacchiaBarrierInputs p) :
    UniformCoreMildSolutionFrontier p :=
  uniformCoreMildSolutionFrontier_of_conditionalInputs
    (uniformCoreMildSolutionConditionalInputs_of_truncatedRestartStrategy H)

end ShenWork.Paper2.IntervalChiNegFinalAssemblyV3
