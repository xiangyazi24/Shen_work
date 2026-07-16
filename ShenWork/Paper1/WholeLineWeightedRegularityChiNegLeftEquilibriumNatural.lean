import ShenWork.Paper1.WholeLineWeightedRegularityChiNegBufferedHalfLineComparisonNatural
import ShenWork.Paper1.WholeLineWeightedRegularityChiNegPlateauPersistenceNatural
import ShenWork.Paper1.WholeLineWeightedRegularityCoMovingCompactNatural
import ShenWork.Paper1.WholeLineWeightedRegularityGlobalStrictPositivityNatural
import ShenWork.Paper1.WholeLineWeightedRegularityCoMovingComparisonNatural
import ShenWork.Paper1.Theorem12Step4EnergyProducer
import ShenWork.Paper1.WholeLineCauchyLeftTailBridge
import ShenWork.Paper1.WholeLineCauchySharpBound
import ShenWork.Paper1.WholeLineCauchyLongTimeBound

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-!
# The strictly negative-sensitivity left equilibrium

The persistent plateau supplies a positive restart floor on a fixed left
half-line.  Exact weighted convergence is uniform on each fixed compact
co-moving buffer, so a sufficiently far-left buffer stays close to the wave
value one.  The buffered nonlocal comparison then raises the restart floor to
any prescribed target below one without assuming a whole-line population
floor.
-/

/-- Algebraic fixed-point expansion of the paper wave operator at a positive
population value.  This is the exact nondivergence form consumed by the
buffered half-line comparison. -/
theorem paperWaveOperator_fixedPoint_eq_bufferedForm_of_pos
    (p : CMParams) {c : ℝ} {q : ℝ → ℝ} {x : ℝ}
    (hqx : 0 < q x) :
    paperWaveOperator p c q q x =
      iteratedDeriv 2 q x + c * deriv q x -
        p.χ *
          (p.m * (q x) ^ (p.m - 1) * deriv q x *
              deriv (frozenElliptic p q) x +
            (q x) ^ p.m *
              (frozenElliptic p q x - (q x) ^ p.γ)) +
        reactionFun p.α (q x) := by
  have hpow_m : (q x) ^ p.m = q x * (q x) ^ (p.m - 1) := by
    calc
      (q x) ^ p.m = (q x) ^ (1 + (p.m - 1)) := by congr 1 <;> ring
      _ = (q x) ^ (1 : ℝ) * (q x) ^ (p.m - 1) := by
        rw [Real.rpow_add hqx]
      _ = q x * (q x) ^ (p.m - 1) := by rw [Real.rpow_one]
  have hpow_tail :
      q x * (q x) ^ (p.m + p.γ - 1) =
        (q x) ^ p.m * (q x) ^ p.γ := by
    calc
      q x * (q x) ^ (p.m + p.γ - 1) =
          (q x) ^ (1 : ℝ) * (q x) ^ (p.m + p.γ - 1) := by
            rw [Real.rpow_one]
      _ = (q x) ^ ((1 : ℝ) + (p.m + p.γ - 1)) := by
            rw [← Real.rpow_add hqx]
      _ = (q x) ^ (p.m + p.γ) := by congr 1 <;> ring
      _ = (q x) ^ p.m * (q x) ^ p.γ := by
            rw [Real.rpow_add hqx]
  unfold paperWaveOperator reactionFun
  dsimp only
  linear_combination
    p.χ * frozenElliptic p q x * hpow_m + p.χ * hpow_tail

/-- A persistent positive buffer and an initial left-half-line floor force
eventual convergence from below to every lower target.  This is the
all-positive-time wrapper around the finite-slab buffered comparison. -/
theorem eventually_leftHalfLine_ge_of_buffered_chiNegKPP
    (p : CMParams) (hchi : p.χ ≤ 0)
    {x₀ R c M C L₀ L : ℝ} {q : ℝ → ℝ → ℝ}
    (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hC : 0 < C) (hCL : C < L) (hL1 : L < 1) (hLM : L ≤ M)
    (hL₀L : L₀ < L)
    (hdefectSmall :
      (-p.χ) * M ^ p.m * (Real.exp (-R) / 2 * M ^ p.γ) <
        C * (1 - L ^ p.α))
    (hcontq : Continuous (fun z : ℝ × ℝ => q z.1 z.2))
    (hqrange : ∀ t, 0 ≤ t → ∀ x, q t x ∈ Set.Icc (0 : ℝ) M)
    (hinit : ∀ x ∈ Set.Iic x₀, C ≤ q 0 x)
    (hbuffer : ∀ t, 0 ≤ t →
      ∀ x ∈ Set.Icc x₀ (x₀ + R), L ≤ q t x)
    (htimeq : ∀ ⦃t x : ℝ⦄, 0 < t →
      HasDerivAt (fun s : ℝ => q s x)
        (deriv (fun s : ℝ => q s x) t) t)
    (hspace1q : ∀ ⦃t x : ℝ⦄, 0 < t →
      HasDerivAt (fun y : ℝ => q t y)
        (deriv (fun y : ℝ => q t y) x) x)
    (hspace2q : ∀ ⦃t x : ℝ⦄, 0 < t →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => q t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x) x)
    (hpdeq : ∀ ⦃t x : ℝ⦄, 0 < t → x < x₀ →
      deriv (fun s : ℝ => q s x) t =
        deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x +
          c * deriv (fun y : ℝ => q t y) x -
          p.χ *
            (p.m * (q t x) ^ (p.m - 1) *
                deriv (fun y : ℝ => q t y) x *
                deriv (frozenElliptic p (q t)) x +
              (q t x) ^ p.m *
                (frozenElliptic p (q t) x - (q t x) ^ p.γ)) +
          reactionFun p.α (q t x)) :
    ∃ S : ℝ, 0 ≤ S ∧
      ∀ t, S ≤ t → ∀ x ∈ Set.Iic x₀, L₀ < q t x := by
  let H : ℝ :=
    (-p.χ) * M ^ p.m * (Real.exp (-R) / 2 * M ^ p.γ)
  let lam : ℝ := chiNegKPPFloorRate p.α C L H
  have hlam : 0 < lam := by
    exact chiNegKPPFloorRate_pos hCL (by simpa [H] using hdefectSmall)
  have htend : Tendsto (chiZeroKPPFloor C L lam) atTop (nhds L) :=
    chiZeroKPPFloor_tendsto_target hlam
  have hIoi : Set.Ioi L₀ ∈ nhds L := Ioi_mem_nhds hL₀L
  obtain ⟨S, hfloor⟩ := eventually_atTop.1 (htend.eventually hIoi)
  refine ⟨max S 0, le_max_right _ _, ?_⟩
  intro t ht x hx
  have ht0 : 0 ≤ t := (le_max_right S 0).trans ht
  have hSt : S ≤ t := (le_max_left S 0).trans ht
  have hT : 0 < t + 1 := by linarith
  have hcomp := leftHalfLine_ge_chiNegKPPFloor_of_buffer
    (T := t + 1) (q := q) p hchi hT hR hM hC hCL hL1 hLM
      hdefectSmall hcontq
      (fun s hs y => hqrange s hs.1 y) hinit
      (fun s hs y hy => hbuffer s hs.1 y hy)
      (fun _s _y hs => htimeq hs.1)
      (fun _s _y hs => hspace1q hs.1)
      (fun _s _y hs => hspace2q hs.1)
      (fun _s _y hs hy => hpdeq hs.1 hy)
  exact (hfloor t hSt).trans_le
    (hcomp t ⟨ht0, by linarith⟩ x hx)

/-- For strictly negative sensitivity, the canonical orbit converges
uniformly to the left equilibrium on a sufficiently far-left co-moving
half-line.  The initial datum is only assumed strictly positive at the left
end; no whole-line positive floor is used. -/
theorem
    wholeLineCauchyGlobal_uniformCoMovingLeftEquilibriumConvergence_chi_neg_natural
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (hchi : p.χ < 0)
    {c eta kappaOne : ℝ} {U V : ℝ → ℝ}
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hstrict : HasStrictWaveUpperTailBound p c U)
    (hkappaOne : kappa c < kappaOne)
    (hkappaOne_one : kappaOne < 1)
    (htail : HasWaveRightTailAsymptotic c kappaOne U)
    (hroot : paper531RootMinus c
      (paper531ConcreteStabilityBudget p hregime).A
      (paper531ConcreteStabilityBudget p hregime).B < eta)
    (hetaCap : eta < stabilityWeightCap p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hleft : StrictlyPositiveAtLeft u₀.1)
    (hinitial : WeightedL2InitialCloseness eta u₀.1 U) :
    UniformCoMovingLeftEquilibriumConvergence c
      (wholeLineCauchyGlobalU p u₀) := by
  let hceiling : WholeLineCauchyCeilingRegime p :=
    WholeLineCauchyCeilingRegime.of_nonpositive hchi.le
  have hbaseline : stabilitySpeedBaseline p ≤
      paper5CorrectedCStarStar p p.χ :=
    paper5CorrectedCStarStar_baseline_le p
  have hc_two : 2 < c :=
    two_lt_of_stabilitySpeedBaseline_lt hbaseline hc
  have hkappa : 0 < kappa c := kappa_pos_of_two_lt hc_two
  have heta : 0 < eta :=
    ((paper531ConcreteStabilityBudget p hregime).rootMinus_pos hc).trans hroot
  have hweighted : CoMovingWeightedL2Convergence eta c
      (wholeLineCauchyGlobalU p u₀) U :=
    wholeLineCauchyGlobal_coMovingWeightedL2Convergence_chi_neg_natural
      p hregime hchi hc hTW hstrict.hasWaveUpperTailBound hreg
        hroot hetaCap u₀ hu₀ hinitial
  have hmod : EventuallyUniformMovingFrameSpatialModulus 0
      (coMovingPath c (wholeLineCauchyGlobalU p u₀)) U :=
    wholeLineCauchyGlobal_eventuallyUniformMovingFrameSpatialModulus
      p hceiling u₀ hu₀ c hTW hreg
  obtain ⟨N, kappaTilde, D, Q, hQ, hkappaTilde,
      _hkappaTildeOne, _hkappaTildeEta, _hcond, hD,
      _hDscaled, _hplateau, hpersist⟩ :=
    wholeLineCauchyGlobal_exists_persistent_lowerBarrierPlateau_chi_neg_natural
      p hregime hchi hc hTW hreg hstrict hkappaOne hkappaOne_one htail
        hroot hetaCap u₀ hu₀ hleft hinitial
  obtain ⟨Tleft, Rleft, d, hd, hleftFloor⟩ :=
    wholeLineCauchyGlobal_eventual_coMoving_left_floor_of_persistent_plateau
      p u₀ hkappa hkappaTilde hD hpersist
  intro epsilon hepsilon
  let e : ℝ := min (epsilon / 4) (1 / 4)
  let L₀ : ℝ := 1 - 2 * e
  let L : ℝ := 1 - e
  have he : 0 < e := by
    dsimp [e]
    exact lt_min (by positivity) (by norm_num)
  have he_eps : e ≤ epsilon / 4 := by
    dsimp [e]
    exact min_le_left _ _
  have he_quarter : e ≤ 1 / 4 := by
    dsimp [e]
    exact min_le_right _ _
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hL₀L : L₀ < L := by dsimp [L₀, L]; linarith
  have hL1 : L < 1 := by dsimp [L]; linarith
  let M : ℝ := max 1 ‖u₀‖
  have hM : 0 ≤ M := zero_le_one.trans (le_max_left 1 ‖u₀‖)
  have hLM : L ≤ M :=
    (le_of_lt hL1).trans (le_max_left 1 ‖u₀‖)
  let C : ℝ := min (d / 2) (L / 2)
  have hC : 0 < C := by
    dsimp [C]
    exact lt_min (by positivity) (by positivity)
  have hCL : C < L := by
    have hCle : C ≤ L / 2 := by
      dsimp [C]
      exact min_le_right _ _
    linarith
  have hLpow1 : L ^ p.α < 1 := by
    have halphaPos : 0 < p.α := lt_of_lt_of_le zero_lt_one p.hα
    simpa only [Real.one_rpow] using
      Real.rpow_lt_rpow hLpos.le hL1 halphaPos
  have hbudget : 0 < C * (1 - L ^ p.α) :=
    mul_pos hC (sub_pos.mpr hLpow1)
  obtain ⟨Rbuf, hRbuf, hRsmall⟩ :=
    exists_nonneg_buffer_exp_defect_lt
      (K := (-p.χ) * M ^ p.m * M ^ p.γ) hbudget
  have hdefectSmall :
      (-p.χ) * M ^ p.m *
          (Real.exp (-Rbuf) / 2 * M ^ p.γ) <
        C * (1 - L ^ p.α) := by
    calc
      (-p.χ) * M ^ p.m *
          (Real.exp (-Rbuf) / 2 * M ^ p.γ) =
          ((-p.χ) * M ^ p.m * M ^ p.γ) *
            (Real.exp (-Rbuf) / 2) := by ring
      _ < C * (1 - L ^ p.α) := hRsmall
  have hUevent : ∀ᶠ z in atBot, 1 - e / 2 < U z := by
    have hnhds : Set.Ioi (1 - e / 2) ∈ nhds (1 : ℝ) :=
      Ioi_mem_nhds (by linarith)
    exact hTW.lim_neg_inf.1 hnhds
  rcases eventually_atBot.1 hUevent with ⟨A, hUA⟩
  let x₀ : ℝ := min (A - Rbuf) Rleft
  have hx₀_left : x₀ ≤ Rleft := by
    dsimp [x₀]
    exact min_le_right _ _
  have hx₀_buf : x₀ + Rbuf ≤ A := by
    have hx : x₀ ≤ A - Rbuf := by
      dsimp [x₀]
      exact min_le_left _ _
    linarith
  obtain ⟨Tbuf, hbufferClose⟩ :=
    eventually_coMovingPath_close_on_Icc_of_weightedL2_of_spatialModulus
      heta hweighted hmod (a := x₀) (b := x₀ + Rbuf)
        (e / 2) (by positivity)
  let t₀ : ℝ := max (max Tleft Tbuf) 1
  have ht₀ : 0 < t₀ :=
    lt_of_lt_of_le zero_lt_one (le_max_right (max Tleft Tbuf) 1)
  have hTleft_t₀ : Tleft ≤ t₀ :=
    (le_max_left Tleft Tbuf).trans (le_max_left (max Tleft Tbuf) 1)
  have hTbuf_t₀ : Tbuf ≤ t₀ :=
    (le_max_right Tleft Tbuf).trans (le_max_left (max Tleft Tbuf) 1)
  let q : ℝ → ℝ → ℝ := fun s x =>
    wholeLineCauchyGlobalU p u₀ (t₀ + max s 0)
      (x + c * (t₀ + max s 0))
  have hqcont : Continuous (fun z : ℝ × ℝ => q z.1 z.2) := by
    rw [continuous_iff_continuousAt]
    intro z
    have hphys : 0 < t₀ + max z.1 0 := by
      have : 0 ≤ max z.1 0 := le_max_right _ _
      linarith
    have hbase := wholeLineCauchyGlobalU_joint_hasFDerivAt_positive
      p hceiling u₀ hu₀ hphys
        (x := z.2 + c * (t₀ + max z.1 0))
    have hmap : ContinuousAt
        (fun a : ℝ × ℝ =>
          (t₀ + max a.1 0, a.2 + c * (t₀ + max a.1 0))) z := by
      fun_prop
    simpa [q, Function.comp_def] using
      hbase.continuousAt.comp
        (f := fun a : ℝ × ℝ =>
          (t₀ + max a.1 0, a.2 + c * (t₀ + max a.1 0))) hmap
  have hqrange : ∀ s, 0 ≤ s → ∀ x,
      q s x ∈ Set.Icc (0 : ℝ) M := by
    intro s hs x
    have hphys : 0 ≤ t₀ + s := by linarith
    constructor
    · simpa [q, max_eq_left hs] using
        wholeLineCauchyGlobal_nonnegative
          p hceiling u₀ hu₀ hphys (x + c * (t₀ + s))
    · simpa [q, M, max_eq_left hs] using
        wholeLineCauchyGlobal_le_max_one_of_chi_nonpos
          p hchi.le u₀ hu₀ ‖u₀‖
          (fun y => WholeLineBUC.apply_le_norm u₀ y) hphys
          (x + c * (t₀ + s))
  have hinit : ∀ x ∈ Set.Iic x₀, C ≤ q 0 x := by
    intro x hx
    have hdx := hleftFloor t₀ hTleft_t₀ x (hx.trans hx₀_left)
    have hCd : C ≤ d := by
      have hhalf : C ≤ d / 2 := by
        dsimp [C]
        exact min_le_left _ _
      linarith
    exact hCd.trans (by simpa [q] using hdx)
  have hbuffer : ∀ s, 0 ≤ s →
      ∀ x ∈ Set.Icc x₀ (x₀ + Rbuf), L ≤ q s x := by
    intro s hs x hx
    have htime : Tbuf ≤ t₀ + s := hTbuf_t₀.trans (by linarith)
    have hclose := hbufferClose (t₀ + s) htime x hx
    have hUlower := hUA x (hx.2.trans hx₀_buf)
    have hdiffLower : -(e / 2) <
        coMovingPath c (wholeLineCauchyGlobalU p u₀) (t₀ + s) x - U x :=
      neg_lt_of_abs_lt hclose
    have hraw : L ≤
        wholeLineCauchyGlobalU p u₀ (t₀ + s)
          (x + c * (t₀ + s)) := by
      dsimp [L]
      change -(e / 2) <
        wholeLineCauchyGlobalU p u₀ (t₀ + s)
            (x + c * (t₀ + s)) - U x at hdiffLower
      linarith
    simpa [q, max_eq_left hs] using hraw
  have htimeOp : ∀ ⦃s x : ℝ⦄, 0 < s →
      HasDerivAt (fun r : ℝ => q r x)
        (paperWaveOperator p c (q s) (q s) x) s := by
    intro s x hs
    have hphysical : 0 < t₀ + s := by linarith
    have hraw :=
      wholeLineCauchyGlobal_coMovingRestart_hasDerivAt_paperWaveOperator
        p hceiling u₀ hu₀ c t₀ hphysical x
    have hev : (fun r : ℝ => q r x) =ᶠ[nhds s]
        fun r => wholeLineCauchyGlobalU p u₀ (t₀ + r)
          (x + c * (t₀ + r)) := by
      filter_upwards [Ioi_mem_nhds hs] with r hr
      change 0 < r at hr
      simp [q, max_eq_left hr.le]
    have hcongr := hraw.congr_of_eventuallyEq hev
    simpa [q, max_eq_left hs.le] using hcongr
  have htimeq : ∀ ⦃s x : ℝ⦄, 0 < s →
      HasDerivAt (fun r : ℝ => q r x)
        (deriv (fun r : ℝ => q r x) s) s := by
    intro s x hs
    exact (htimeOp hs).differentiableAt.hasDerivAt
  have hsliceC2 : ∀ ⦃s : ℝ⦄, 0 < s → ContDiff ℝ 2 (q s) := by
    intro s hs
    have hphysical : 0 < t₀ + s := by linarith
    simpa [q, max_eq_left hs.le] using
      wholeLineCauchyGlobal_coMovingRestart_contDiff_two
        p hceiling u₀ hu₀ c t₀ hphysical
  have hspace1q : ∀ ⦃s x : ℝ⦄, 0 < s →
      HasDerivAt (fun y : ℝ => q s y)
        (deriv (fun y : ℝ => q s y) x) x := by
    intro s x hs
    exact ((hsliceC2 hs).differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hspace2q : ∀ ⦃s x : ℝ⦄, 0 < s →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => q s z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => q s z) y) x) x := by
    intro s x hs
    exact (hsliceC2 hs).differentiable_deriv_two.differentiableAt.hasDerivAt
  have hpdeq : ∀ ⦃s x : ℝ⦄, 0 < s → x < x₀ →
      deriv (fun r : ℝ => q r x) s =
        deriv (fun y : ℝ => deriv (fun z : ℝ => q s z) y) x +
          c * deriv (fun y : ℝ => q s y) x -
          p.χ *
            (p.m * (q s x) ^ (p.m - 1) *
                deriv (fun y : ℝ => q s y) x *
                deriv (frozenElliptic p (q s)) x +
              (q s x) ^ p.m *
                (frozenElliptic p (q s) x - (q s x) ^ p.γ)) +
          reactionFun p.α (q s x) := by
    intro s x hs _hx
    have hphysical : 0 < t₀ + s := by linarith
    have hqx : 0 < q s x := by
      simpa [q, max_eq_left hs.le] using
        wholeLineCauchyGlobal_pos_of_posAtBot
          p hceiling u₀ hu₀ hleft hphysical
            (x + c * (t₀ + s))
    have hiter : iteratedDeriv 2 (q s) x =
        deriv (fun y : ℝ => deriv (fun z : ℝ => q s z) y) x := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
        iteratedDeriv_one]
    calc
      deriv (fun r : ℝ => q r x) s =
          paperWaveOperator p c (q s) (q s) x := (htimeOp hs).deriv
      _ = iteratedDeriv 2 (q s) x + c * deriv (q s) x -
            p.χ *
              (p.m * (q s x) ^ (p.m - 1) * deriv (q s) x *
                  deriv (frozenElliptic p (q s)) x +
                (q s x) ^ p.m *
                  (frozenElliptic p (q s) x - (q s x) ^ p.γ)) +
            reactionFun p.α (q s x) :=
          paperWaveOperator_fixedPoint_eq_bufferedForm_of_pos p hqx
      _ = _ := by rw [hiter]
  obtain ⟨S, hS0, hfloor⟩ := eventually_leftHalfLine_ge_of_buffered_chiNegKPP
    p hchi.le hRbuf hM hC hCL hL1 hLM hL₀L hdefectSmall hqcont
      hqrange hinit hbuffer htimeq hspace1q hspace2q hpdeq
  obtain ⟨Tup, hupper⟩ := eventually_atTop.1
    (wholeLineCauchyGlobal_uniformLimsupLe_one_of_chi_nonpos
      p hchi.le u₀ hu₀ e he)
  refine ⟨max 0 (-x₀), max (t₀ + S) Tup, ?_⟩
  intro t z ht hz
  have htKPP : S ≤ t - t₀ := by
    have := (le_max_left (t₀ + S) Tup).trans ht
    linarith
  have hrel0 : 0 ≤ t - t₀ := by
    have := (le_max_left (t₀ + S) Tup).trans ht
    linarith
  have hcut : -max 0 (-x₀) ≤ x₀ := by
    simpa using neg_le_neg (le_max_right (0 : ℝ) (-x₀))
  have hlower := hfloor (t - t₀) htKPP z
    (Set.mem_Iic.mpr (hz.trans hcut))
  have huLower : 1 - 2 * e <
      wholeLineCauchyGlobalU p u₀ t (z + c * t) := by
    simpa [q, L₀, max_eq_left hrel0, coMovingPath] using hlower
  have htUpper : Tup ≤ t := (le_max_right (t₀ + S) Tup).trans ht
  have huUpper := hupper t htUpper (z + c * t)
  have habs :
      |wholeLineCauchyGlobalU p u₀ t (z + c * t) - 1| < epsilon := by
    rw [abs_lt]
    constructor <;> linarith
  simpa [coMovingPath] using habs

section AxiomAudit

#print axioms paperWaveOperator_fixedPoint_eq_bufferedForm_of_pos
#print axioms eventually_leftHalfLine_ge_of_buffered_chiNegKPP
#print axioms
  wholeLineCauchyGlobal_uniformCoMovingLeftEquilibriumConvergence_chi_neg_natural

end AxiomAudit

end ShenWork.Paper1
