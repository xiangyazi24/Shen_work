import ShenWork.Paper2.IntervalBFormSquareHeatT0RestartDerivativeData
import ShenWork.Paper2.IntervalConjugatePicardInfThreshold
import ShenWork.Paper2.IntervalDomainResolverStrictPos

open Filter Topology Set

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData ConjugatePicardInfThresholdData
   conjugatePicardLimit paperPositiveFloor)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalMildPicardThreshold
  (unitClip_of_mem)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant)
open ShenWork.Paper2
  (PaperPositiveInitialDatum)

noncomputable section

namespace ShenWork.IntervalConjugatePicard

/-- Quantitative form of `conjugatePicardLimit_pos_of_PID`: the Picard limit
stays above half of the paper-positive initial floor on the inf-threshold
horizon. -/
theorem conjugatePicardLimit_ge_half_floor_of_PID
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T : ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (H : ConjugatePicardInfThresholdData p u₀ T)
    (hsmall :
      |p.χ₀| * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * H.CQ)
        + T * H.CL ≤ paperPositiveFloor hu₀ / 2) :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      paperPositiveFloor hu₀ / 2 ≤ conjugatePicardLimit p u₀ T t x := by
  intro t ht htT x
  have hiter :=
    conjugatePicardIter_ge_half_floor_of_PID hu₀ H hsmall
  unfold conjugatePicardLimit
  simp only [ht, htT, and_self, ite_true]
  set a := fun m => conjugatePicardIter p u₀ m t x
  have hcauchy : CauchySeq a :=
    ShenWork.IntervalMildPicard.real_cauchySeq_of_geometric_bound
      H.hK H.hK_nn H.hC₀
      (fun n => H.hgeom n t ht htT x)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  rw [hL.limUnder_eq]
  exact ge_of_tendsto hL
    (Eventually.of_forall (fun n => hiter n t ht htT x))

end ShenWork.IntervalConjugatePicard

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-- The constant seed value `sqrt(c₀)/2`, where `c₀` is the paper-positive
floor. -/
def paperPositiveSeedValue {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) : ℝ :=
  Real.sqrt (paperPositiveFloor hu₀) / 2

/-- The constant square-heat seed associated to a paper-positive datum. -/
def paperPositiveConstSeed {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) : ℝ → ℝ :=
  fun _ => paperPositiveSeedValue hu₀

theorem paperPositiveSeedValue_nonneg {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    0 ≤ paperPositiveSeedValue hu₀ := by
  unfold paperPositiveSeedValue
  nlinarith [Real.sqrt_nonneg (paperPositiveFloor hu₀)]

theorem paperPositiveSeedValue_pos {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    0 < paperPositiveSeedValue hu₀ := by
  unfold paperPositiveSeedValue
  have hsqrt_pos : 0 < Real.sqrt (paperPositiveFloor hu₀) :=
    Real.sqrt_pos.mpr
      (ShenWork.IntervalConjugatePicard.paperPositiveFloor_pos hu₀)
  nlinarith

theorem paperPositiveSeedValue_sq {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    (paperPositiveSeedValue hu₀) ^ 2 = paperPositiveFloor hu₀ / 4 := by
  unfold paperPositiveSeedValue
  have hfloor_nonneg : 0 ≤ paperPositiveFloor hu₀ :=
    le_of_lt (ShenWork.IntervalConjugatePicard.paperPositiveFloor_pos hu₀)
  have hsqrt_sq : (Real.sqrt (paperPositiveFloor hu₀)) ^ 2 =
      paperPositiveFloor hu₀ :=
    Real.sq_sqrt hfloor_nonneg
  calc
    (Real.sqrt (paperPositiveFloor hu₀) / 2) ^ 2
        = (Real.sqrt (paperPositiveFloor hu₀)) ^ 2 / 4 := by ring
    _ = paperPositiveFloor hu₀ / 4 := by rw [hsqrt_sq]

theorem paperPositiveConstSeed_continuous {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    Continuous (paperPositiveConstSeed hu₀) := by
  simpa [paperPositiveConstSeed] using
    (continuous_const :
      Continuous (fun _ : ℝ => paperPositiveSeedValue hu₀))

theorem paperPositiveConstSeed_squareHeatSeed
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    SquareHeatSeed (intervalDomainLift u₀) (paperPositiveConstSeed hu₀) where
  continuousOn := (paperPositiveConstSeed_continuous hu₀).continuousOn
  nonneg := by
    intro y _hy
    simpa [paperPositiveConstSeed] using paperPositiveSeedValue_nonneg hu₀
  pos_somewhere := by
    refine ⟨0, ?_, ?_⟩
    · exact left_mem_Icc.mpr zero_le_one
    · simpa [paperPositiveConstSeed] using paperPositiveSeedValue_pos hu₀
  square_le_initial := by
    intro y hy
    have hsq := paperPositiveSeedValue_sq hu₀
    have hquarter_le_floor :
        paperPositiveFloor hu₀ / 4 ≤ paperPositiveFloor hu₀ := by
      nlinarith [ShenWork.IntervalConjugatePicard.paperPositiveFloor_pos hu₀]
    have hfloor_le_lift :
        paperPositiveFloor hu₀ ≤ intervalDomainLift u₀ y := by
      have hfloor :=
        ShenWork.IntervalConjugatePicard.paperPositiveFloor_le
          hu₀ ⟨y, hy⟩
      simpa [intervalDomainLift, hy] using hfloor
    calc
      paperPositiveConstSeed hu₀ y ^ 2
          = paperPositiveFloor hu₀ / 4 := by
            simpa [paperPositiveConstSeed] using hsq
      _ ≤ paperPositiveFloor hu₀ := hquarter_le_floor
      _ ≤ intervalDomainLift u₀ y := hfloor_le_lift

theorem constant_cosineCoeff_bound (c : ℝ) :
    ∀ n, |cosineCoeffs (fun _ : ℝ => c) n| ≤ |c| := by
  intro n
  rw [ShenWork.IntervalDomainResolverStrictPos.cosineCoeffs_const c n]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn]

theorem constant_cosineCoeff_sq_summable (c : ℝ) :
    Summable fun n : ℕ => (cosineCoeffs (fun _ : ℝ => c) n) ^ 2 := by
  refine summable_of_hasFiniteSupport ?_
  unfold Function.HasFiniteSupport
  refine (Set.finite_singleton 0).subset ?_
  intro n hn
  by_contra hnmem
  have hn_ne : n ≠ 0 := by
    intro h
    exact hnmem (by simp [h])
  have hcoeff : cosineCoeffs (fun _ : ℝ => c) n = 0 := by
    rw [ShenWork.IntervalDomainResolverStrictPos.cosineCoeffs_const c n,
      if_neg hn_ne]
  have hzero : (cosineCoeffs (fun _ : ℝ => c) n) ^ 2 = 0 := by
    rw [hcoeff]
    norm_num
  exact hn hzero

theorem paperPositiveConstSeed_cosineCoeff_bound
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    ∀ n,
      |cosineCoeffs (paperPositiveConstSeed hu₀) n|
        ≤ |paperPositiveSeedValue hu₀| := by
  simpa [paperPositiveConstSeed] using
    constant_cosineCoeff_bound (paperPositiveSeedValue hu₀)

theorem paperPositiveConstSeed_cosineCoeff_sq_summable
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    Summable fun n : ℕ =>
      (cosineCoeffs (paperPositiveConstSeed hu₀) n) ^ 2 := by
  simpa [paperPositiveConstSeed] using
    constant_cosineCoeff_sq_summable (paperPositiveSeedValue hu₀)

/-- On the closed interval, the full Neumann semigroup preserves constants. -/
theorem intervalFullSemigroupOperator_const_Icc
    {t c x : ℝ} (ht : 0 < t) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalFullSemigroupOperator t (fun _ : ℝ => c) x = c := by
  have hK : ∀ n, |cosineCoeffs (fun _ : ℝ => c) n| ≤ |c| :=
    constant_cosineCoeff_bound c
  rw [ShenWork.IntervalFullKernelSpectralClean.intervalFullSemigroupOperator_eq_cosineHeatValue_Icc
      ht continuous_const hK hx]
  rw [unitIntervalCosineHeatValue, tsum_eq_single 0]
  · rw [ShenWork.IntervalDomainResolverStrictPos.cosineCoeffs_const c 0]
    simp [unitIntervalCosineHeatPointWeight, unitIntervalCosineEigenvalue,
      unitIntervalCosineMode]
  · intro n hn
    rw [ShenWork.IntervalDomainResolverStrictPos.cosineCoeffs_const c n,
      if_neg hn, mul_zero]

theorem squareHeatBarrier_paperPositiveConstSeed_initial_le
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀} {M τ x : ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (Hinf : ConjugatePicardInfThresholdData p u₀ DB.T)
    (hsmall :
      |p.χ₀| * (heatGradientLinftyLinftyConstant *
          (2 * Real.sqrt DB.T) * Hinf.CQ)
        + DB.T * Hinf.CL ≤ paperPositiveFloor hu₀ / 2)
    (hM_nonneg : 0 ≤ M)
    (hτ : 0 < τ) (hτT : τ ≤ DB.T)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    squareHeatBarrier M (paperPositiveConstSeed hu₀) τ x ≤
      bformConjugatePicardLift p DB τ x := by
  have hS :
      intervalFullSemigroupOperator τ (paperPositiveConstSeed hu₀) x =
        paperPositiveSeedValue hu₀ := by
    simpa [paperPositiveConstSeed] using
      intervalFullSemigroupOperator_const_Icc
        (t := τ) (c := paperPositiveSeedValue hu₀) (x := x) hτ hx
  have hbar_eq :
      squareHeatBarrier M (paperPositiveConstSeed hu₀) τ x =
        Real.exp (-M * τ) * (paperPositiveSeedValue hu₀) ^ 2 := by
    simp [squareHeatBarrier, hS]
  have hexp_le_one : Real.exp (-M * τ) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (by nlinarith [hM_nonneg, le_of_lt hτ])
  have hseed_sq := paperPositiveSeedValue_sq hu₀
  have hquarter_nonneg : 0 ≤ paperPositiveFloor hu₀ / 4 := by
    nlinarith [ShenWork.IntervalConjugatePicard.paperPositiveFloor_pos hu₀]
  have hbar_le_quarter :
      squareHeatBarrier M (paperPositiveConstSeed hu₀) τ x ≤
        paperPositiveFloor hu₀ / 4 := by
    rw [hbar_eq, hseed_sq]
    nlinarith [mul_le_mul_of_nonneg_right hexp_le_one hquarter_nonneg]
  have hquarter_le_half :
      paperPositiveFloor hu₀ / 4 ≤ paperPositiveFloor hu₀ / 2 := by
    nlinarith [ShenWork.IntervalConjugatePicard.paperPositiveFloor_pos hu₀]
  have hu_half :
      paperPositiveFloor hu₀ / 2 ≤
        conjugatePicardLimit p u₀ DB.T τ ⟨x, hx⟩ :=
    ShenWork.IntervalConjugatePicard.conjugatePicardLimit_ge_half_floor_of_PID
        hu₀ Hinf hsmall τ hτ hτT ⟨x, hx⟩
  have hlift :
      bformConjugatePicardLift p DB τ x =
        conjugatePicardLimit p u₀ DB.T τ ⟨x, hx⟩ := by
    simp [bformConjugatePicardLift, unitClip_of_mem hx]
  rw [hlift]
  exact hbar_le_quarter.trans (hquarter_le_half.trans hu_half)

/-- Closed B-form strict positivity by the constant `sqrt(c₀)/2` seed and the
proved restarted drift comparison.  The only carried hypotheses are the
genuine linear strip data for the B-form solution and the nonnegative barrier
damping choice. -/
theorem bform_strictPos_closed
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    {A D M : ℝ} {drift react : ℝ → ℝ → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (Hinf : ConjugatePicardInfThresholdData p u₀ DB.T)
    (hsmall :
      |p.χ₀| * (heatGradientLinftyLinftyConstant *
          (2 * Real.sqrt DB.T) * Hinf.CQ)
        + DB.T * Hinf.CL ≤ paperPositiveFloor hu₀ / 2)
    (hM_nonneg : 0 ≤ M)
    (hM : A ^ 2 / 2 + D ≤ M)
    (hstrip :
      ∀ τ, 0 < τ → τ < DB.T →
        NeumannLinearDriftCoefficientsRegular (DB.T - τ)
          (restartTimeShift τ drift) (restartTimeShift τ react) ∧
        IsClassicalNeumannLinearDriftSuperSolution (DB.T - τ)
          (restartTimeShift τ drift) (restartTimeShift τ react)
          (restartTimeShift τ (bformConjugatePicardLift p DB)) ∧
        (∀ s x, 0 < s → s < DB.T - τ →
          x ∈ Set.Ioo (0 : ℝ) 1 → |drift (τ + s) x| ≤ A) ∧
        (∀ s x, 0 < s → s < DB.T - τ →
          x ∈ Set.Ioo (0 : ℝ) 1 → -react (τ + s) x ≤ D)) :
    ∀ t x, 0 < t → t < DB.T →
      0 < conjugatePicardLimit p u₀ DB.T t x := by
  let f : ℝ → ℝ := paperPositiveConstSeed hu₀
  have hseed : SquareHeatSeed (intervalDomainLift u₀) f := by
    simpa [f] using paperPositiveConstSeed_squareHeatSeed hu₀
  have hf : Continuous f := by
    simpa [f] using paperPositiveConstSeed_continuous hu₀
  have hK : ∀ n, |cosineCoeffs f n| ≤ |paperPositiveSeedValue hu₀| := by
    simpa [f] using paperPositiveConstSeed_cosineCoeff_bound hu₀
  have hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2 := by
    simpa [f] using paperPositiveConstSeed_cosineCoeff_sq_summable hu₀
  exact
    bform_strictPos_via_t0_restart_semigroup
      (p := p) (u₀ := u₀) (DB := DB)
      (A := A) (D := D) (M := M) (f := f)
      (drift := drift) (react := react)
      hseed hf (K := |paperPositiveSeedValue hu₀|) hK hl2
      (fun t ht0 htT => by
        let τ : ℝ := t / 2
        have hτ0 : 0 < τ := by
          dsimp [τ]
          linarith
        have hτt : τ < t := by
          dsimp [τ]
          linarith
        have hτT : τ < DB.T := by
          linarith
        have hL : 0 < DB.T - τ := by
          linarith
        rcases hstrip τ hτ0 hτT with
          ⟨hcoeff, hsuper, hB_bound, hC_neg_bound⟩
        refine
          ⟨τ, hτ0, hτt, hL, hcoeff, hsuper, hM,
            hB_bound, hC_neg_bound, ?_⟩
        intro x hx
        simpa [f] using
          squareHeatBarrier_paperPositiveConstSeed_initial_le
            (p := p) (u₀ := u₀) (DB := DB) (M := M)
            (τ := τ) (x := x)
            hu₀ Hinf hsmall hM_nonneg hτ0 (le_of_lt hτT) hx)

end ShenWork.Paper2.BFormPositiveDatumNegPart
