import ShenWork.Paper1.WholeLineChiPosHalfLineWeightedComparison
import ShenWork.Paper1.WholeLineChiPosHalfLineTargets
import ShenWork.Paper1.WholeLineChiPosCanonicalRestartNatural
import ShenWork.Paper1.WholeLineWeightedRegularityWeightedConvergenceChiPosNatural
import ShenWork.Paper1.WholeLineWeightedRegularityCoMovingCompactNatural
import ShenWork.Paper1.WholeLineCauchyChiPosRangeBound

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-!
# A buffered half-line successor for positive sensitivity

The comparison is carried out in the co-moving coordinate.  This first
packages the regularity of a positive-time restart in that coordinate; the
successor construction below uses the package twice, first for the floor and
then for the ceiling.
-/

/-- Regularity and range data for the canonical orbit restarted at `t₀` in
the co-moving coordinate.  The clamp by `max s 0` gives a globally continuous
representative while agreeing with the physical restart for `s ≥ 0`. -/
structure WholeLineChiPosCoMovingRestartData
    (p : CMParams) (u₀ : WholeLineBUC) (c t₀ G : ℝ) where
  q : ℝ → ℝ → ℝ
  eq_global : ∀ ⦃s : ℝ⦄, 0 ≤ s → ∀ z,
    q s z = coMovingPath c (wholeLineCauchyGlobalU p u₀) (t₀ + s) z
  continuous : Continuous (fun z : ℝ × ℝ => q z.1 z.2)
  mem_Icc : ∀ ⦃s : ℝ⦄, 0 ≤ s → ∀ z, q s z ∈ Set.Icc (0 : ℝ) G
  positive : ∀ ⦃s z : ℝ⦄, 0 < s → 0 < q s z
  time_operator : ∀ ⦃s z : ℝ⦄, 0 < s →
    HasDerivAt (fun r : ℝ => q r z)
      (paperWaveOperator p c (q s) (q s) z) s
  slice_contDiff_two : ∀ ⦃s : ℝ⦄, 0 < s → ContDiff ℝ 2 (q s)

theorem WholeLineChiPosCoMovingRestartData.time_hasDerivAt
    {p : CMParams} {u₀ : WholeLineBUC} {c t₀ G : ℝ}
    (d : WholeLineChiPosCoMovingRestartData p u₀ c t₀ G)
    {s z : ℝ} (hs : 0 < s) :
    HasDerivAt (fun r : ℝ => d.q r z)
      (deriv (fun r : ℝ => d.q r z) s) s :=
  (d.time_operator hs).differentiableAt.hasDerivAt

theorem WholeLineChiPosCoMovingRestartData.space_hasDerivAt
    {p : CMParams} {u₀ : WholeLineBUC} {c t₀ G : ℝ}
    (d : WholeLineChiPosCoMovingRestartData p u₀ c t₀ G)
    {s z : ℝ} (hs : 0 < s) :
    HasDerivAt (fun y : ℝ => d.q s y)
      (deriv (fun y : ℝ => d.q s y) z) z :=
  ((d.slice_contDiff_two hs).differentiable (by norm_num)).differentiableAt.hasDerivAt

theorem WholeLineChiPosCoMovingRestartData.space_deriv_hasDerivAt
    {p : CMParams} {u₀ : WholeLineBUC} {c t₀ G : ℝ}
    (d : WholeLineChiPosCoMovingRestartData p u₀ c t₀ G)
    {s z : ℝ} (hs : 0 < s) :
    HasDerivAt (fun y : ℝ => deriv (fun x : ℝ => d.q s x) y)
      (deriv (fun y : ℝ => deriv (fun x : ℝ => d.q s x) y) z) z :=
  (d.slice_contDiff_two hs).differentiable_deriv_two.differentiableAt.hasDerivAt

/-- Expanded nondivergence-form PDE for a co-moving restart. -/
theorem WholeLineChiPosCoMovingRestartData.expanded_pde
    {p : CMParams} {u₀ : WholeLineBUC} {c t₀ G : ℝ}
    (d : WholeLineChiPosCoMovingRestartData p u₀ c t₀ G)
    {s z : ℝ} (hs : 0 < s) :
    deriv (fun r : ℝ => d.q r z) s =
      deriv (fun y : ℝ => deriv (fun x : ℝ => d.q s x) y) z +
        c * deriv (fun y : ℝ => d.q s y) z -
        p.χ *
          (p.m * (d.q s z) ^ (p.m - 1) *
              deriv (fun y : ℝ => d.q s y) z *
              deriv (frozenElliptic p (d.q s)) z +
            (d.q s z) ^ p.m *
              (frozenElliptic p (d.q s) z - (d.q s z) ^ p.γ)) +
        reactionFun p.α (d.q s z) := by
  have hiter : iteratedDeriv 2 (d.q s) z =
      deriv (fun y : ℝ => deriv (fun x : ℝ => d.q s x) y) z := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
      iteratedDeriv_one]
  calc
    deriv (fun r : ℝ => d.q r z) s =
        paperWaveOperator p c (d.q s) (d.q s) z :=
      (d.time_operator hs).deriv
    _ = iteratedDeriv 2 (d.q s) z + c * deriv (d.q s) z -
          p.χ *
            (p.m * (d.q s z) ^ (p.m - 1) * deriv (d.q s) z *
                deriv (frozenElliptic p (d.q s)) z +
              (d.q s z) ^ p.m *
                (frozenElliptic p (d.q s) z - (d.q s z) ^ p.γ)) +
          reactionFun p.α (d.q s z) :=
      paperWaveOperator_fixedPoint_eq_bufferedForm_of_pos p (d.positive hs)
    _ = _ := by rw [hiter]

/-- Construct co-moving restart data from the canonical global solution. -/
def wholeLineCauchyGlobal_positiveCoMovingRestartData
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hleft : StrictlyPositiveAtLeft u₀.1) (c : ℝ)
    {t₀ G : ℝ} (ht₀ : 0 < t₀)
    (hupper : ∀ ⦃t : ℝ⦄, 0 ≤ t → ∀ x,
      wholeLineCauchyGlobalU p u₀ t x ≤ G) :
    WholeLineChiPosCoMovingRestartData p u₀ c t₀ G := by
  let q : ℝ → ℝ → ℝ := fun s z =>
    wholeLineCauchyGlobalU p u₀ (t₀ + max s 0)
      (z + c * (t₀ + max s 0))
  refine
    { q := q
      eq_global := ?_
      continuous := ?_
      mem_Icc := ?_
      positive := ?_
      time_operator := ?_
      slice_contDiff_two := ?_ }
  · intro s hs z
    simp [q, max_eq_left hs, coMovingPath]
  · rw [continuous_iff_continuousAt]
    intro z
    have hphys : 0 < t₀ + max z.1 0 := by
      have : 0 ≤ max z.1 0 := le_max_right _ _
      linarith
    have hbase := wholeLineCauchyGlobalU_joint_hasFDerivAt_positive
      p hregime u₀ hu₀ hphys
        (x := z.2 + c * (t₀ + max z.1 0))
    have hmap : ContinuousAt
        (fun a : ℝ × ℝ =>
          (t₀ + max a.1 0, a.2 + c * (t₀ + max a.1 0))) z := by
      fun_prop
    simpa [q, Function.comp_def] using
      hbase.continuousAt.comp
        (f := fun a : ℝ × ℝ =>
          (t₀ + max a.1 0, a.2 + c * (t₀ + max a.1 0))) hmap
  · intro s hs z
    have hphys : 0 ≤ t₀ + s := by linarith
    constructor
    · simpa [q, max_eq_left hs] using
        wholeLineCauchyGlobal_nonnegative p hregime u₀ hu₀ hphys
          (z + c * (t₀ + s))
    · simpa [q, max_eq_left hs] using
        hupper hphys (z + c * (t₀ + s))
  · intro s z hs
    have hphys : 0 < t₀ + s := by linarith
    simpa [q, max_eq_left hs.le] using
      wholeLineCauchyGlobal_pos_of_posAtBot
        p hregime u₀ hu₀ hleft hphys (z + c * (t₀ + s))
  · intro s z hs
    have hphysical : 0 < t₀ + s := by linarith
    have hraw :=
      wholeLineCauchyGlobal_coMovingRestart_hasDerivAt_paperWaveOperator
        p hregime u₀ hu₀ c t₀ hphysical z
    have hev : (fun r : ℝ => q r z) =ᶠ[nhds s]
        fun r => wholeLineCauchyGlobalU p u₀ (t₀ + r)
          (z + c * (t₀ + r)) := by
      filter_upwards [Ioi_mem_nhds hs] with r hr
      change 0 < r at hr
      simp [q, max_eq_left hr.le]
    have hcongr := hraw.congr_of_eventuallyEq hev
    simpa [q, max_eq_left hs.le] using hcongr
  · intro s hs
    have hphysical : 0 < t₀ + s := by linarith
    simpa [q, max_eq_left hs.le] using
      wholeLineCauchyGlobal_coMovingRestart_contDiff_two
        p hregime u₀ hu₀ c t₀ hphysical

/-! ## Forward buffered comparisons -/

/-- Apply the finite-slab weighted floor comparison on an arbitrary forward
time, using the regularity stored in a co-moving restart. -/
theorem WholeLineChiPosCoMovingRestartData.ge_of_weighted_buffered_floor
    {p : CMParams} {u₀ : WholeLineBUC} {c t₀ G : ℝ}
    (d : WholeLineChiPosCoMovingRestartData p u₀ c t₀ G)
    (hchi : 0 < p.χ) {x₀ R ell M : ℝ} {b : ℝ → ℝ}
    (hR : 0 ≤ R) (hell : 0 ≤ ell) (hM : 0 ≤ M)
    (hellM : ell ≤ M) (hMG : M ≤ G)
    (hcontb : Continuous b)
    (hqlocal : ∀ s, 0 ≤ s → ∀ x, x ≤ x₀ + R →
      d.q s x ∈ Set.Icc ell M)
    (hbrange : ∀ s, 0 ≤ s → b s ∈ Set.Icc (0 : ℝ) M)
    (hinit : ∀ x ∈ Set.Iic x₀, b 0 ≤ d.q 0 x)
    (hbuffer : ∀ s, 0 ≤ s →
      ∀ x ∈ Set.Icc x₀ (x₀ + R), b s ≤ d.q s x)
    (htimeb : ∀ ⦃s : ℝ⦄, 0 < s → HasDerivAt b (deriv b s) s)
    (hpdeb : ∀ ⦃s : ℝ⦄, 0 < s →
      deriv b s ≤ b s * (1 - (b s) ^ p.α) -
        p.χ * (b s) ^ p.m * (M ^ p.γ - (b s) ^ p.γ) -
        p.χ * (b s) ^ p.m * (Real.exp (-R) / 2) * G ^ p.γ) :
    ∀ s, 0 ≤ s → ∀ x ∈ Set.Iic x₀, b s ≤ d.q s x := by
  intro s hs x hx
  let T : ℝ := s + 1
  have hT : 0 < T := by dsimp [T]; linarith
  have hcomp := leftHalfLine_ge_of_weighted_buffered_chiPos_floor
    p hchi (T := T) (x₀ := x₀) (R := R) (c := c)
      (ell := ell) (M := M) (G := G) (q := d.q) (b := b)
      hT hR hell hM hellM hMG d.continuous hcontb
      (fun r hr y => d.mem_Icc hr.1 y)
      (fun r hr y hy => hqlocal r hr.1 y hy)
      (fun r hr => hbrange r hr.1) hinit
      (fun r hr y hy => hbuffer r hr.1 y hy)
      (fun _r _y hr => d.time_hasDerivAt hr.1)
      (fun _r _y hr => d.space_hasDerivAt hr.1)
      (fun _r _y hr => d.space_deriv_hasDerivAt hr.1)
      (fun _r hr => htimeb hr.1)
      (fun _r _y hr _hy => d.expanded_pde hr.1)
      (fun _r hr => hpdeb hr.1)
  exact hcomp s ⟨hs, by dsimp [T]; linarith⟩ x hx

/-- Apply the finite-slab weighted ceiling comparison on an arbitrary forward
time, using the regularity stored in a co-moving restart. -/
theorem WholeLineChiPosCoMovingRestartData.le_of_weighted_buffered_ceiling
    {p : CMParams} {u₀ : WholeLineBUC} {c t₀ G : ℝ}
    (d : WholeLineChiPosCoMovingRestartData p u₀ c t₀ G)
    (hchi : 0 < p.χ) {x₀ R Lhat M : ℝ} {a : ℝ → ℝ}
    (hR : 0 ≤ R) (hLhat : 0 ≤ Lhat) (hM : 0 ≤ M)
    (hLhatM : Lhat ≤ M) (hMG : M ≤ G)
    (hconta : Continuous a)
    (hqlocal : ∀ s, 0 ≤ s → ∀ x, x ≤ x₀ + R →
      d.q s x ∈ Set.Icc Lhat M)
    (harange : ∀ s, 0 ≤ s → a s ∈ Set.Icc (0 : ℝ) M)
    (hinit : ∀ x ∈ Set.Iic x₀, d.q 0 x ≤ a 0)
    (hbuffer : ∀ s, 0 ≤ s →
      ∀ x ∈ Set.Icc x₀ (x₀ + R), d.q s x ≤ a s)
    (htimea : ∀ ⦃s : ℝ⦄, 0 < s → HasDerivAt a (deriv a s) s)
    (hpdea : ∀ ⦃s : ℝ⦄, 0 < s →
      a s * (1 - (a s) ^ p.α) +
          p.χ * (a s) ^ p.m * ((a s) ^ p.γ - Lhat ^ p.γ) +
          p.χ * (a s) ^ p.m * (Real.exp (-R) / 2) * Lhat ^ p.γ ≤
        deriv a s) :
    ∀ s, 0 ≤ s → ∀ x ∈ Set.Iic x₀, d.q s x ≤ a s := by
  intro s hs x hx
  let T : ℝ := s + 1
  have hT : 0 < T := by dsimp [T]; linarith
  have hcomp := leftHalfLine_le_of_weighted_buffered_chiPos_ceiling
    p hchi (T := T) (x₀ := x₀) (R := R) (c := c)
      (Lhat := Lhat) (M := M) (G := G) (q := d.q) (a := a)
      hT hR hLhat hM hLhatM hMG d.continuous hconta
      (fun r hr y => d.mem_Icc hr.1 y)
      (fun r hr y hy => hqlocal r hr.1 y hy)
      (fun r hr => harange r hr.1) hinit
      (fun r hr y hy => hbuffer r hr.1 y hy)
      (fun _r _y hr => d.time_hasDerivAt hr.1)
      (fun _r _y hr => d.space_hasDerivAt hr.1)
      (fun _r _y hr => d.space_deriv_hasDerivAt hr.1)
      (fun _r hr => htimea hr.1)
      (fun _r _y hr _hy => d.expanded_pde hr.1)
      (fun _r hr => hpdea hr.1)
  exact hcomp s ⟨hs, by dsimp [T]; linarith⟩ x hx

/-! ## A common buffer width for both weighted contacts -/

/-- Choose one nonnegative buffer width which leaves positive reserve in both
the floor and ceiling scalar gaps.  The two coefficients are different: the
floor is capped at `Lraw`, whereas the ceiling may range up to `M`. -/
theorem exists_chiPos_halfLine_round_buffer_width
    {p : CMParams} {ell M delta G : ℝ}
    (targets : ChiPosHalfLineRoundTargets p ell M delta) :
    ∃ R : ℝ, 0 ≤ R ∧
      p.χ * targets.Lraw ^ (p.m - 1) *
          (Real.exp (-R) / 2) * G ^ p.γ <
        chiPosFloorGap p M targets.Lraw ∧
      p.χ * M ^ (p.m - 1) *
          (Real.exp (-R) / 2) * targets.L ^ p.γ <
        chiPosCeilingGap p targets.L targets.Araw := by
  let Kfloor : ℝ :=
    p.χ * targets.Lraw ^ (p.m - 1) * G ^ p.γ
  let Kceiling : ℝ :=
    p.χ * M ^ (p.m - 1) * targets.L ^ p.γ
  let K : ℝ := max Kfloor Kceiling
  let budget : ℝ := min
    (chiPosFloorGap p M targets.Lraw)
    (chiPosCeilingGap p targets.L targets.Araw)
  have hbudget : 0 < budget := by
    dsimp [budget]
    exact lt_min targets.floor_raw_margin targets.ceiling_raw_margin
  obtain ⟨R, hR, hsmall⟩ :=
    exists_nonneg_buffer_exp_defect_lt (K := K) hbudget
  have htau : 0 ≤ Real.exp (-R) / 2 := by positivity
  refine ⟨R, hR, ?_, ?_⟩
  · have hcoeff : Kfloor ≤ K := by
      dsimp [K]
      exact le_max_left _ _
    have hscaled := mul_le_mul_of_nonneg_right hcoeff htau
    calc
      p.χ * targets.Lraw ^ (p.m - 1) *
            (Real.exp (-R) / 2) * G ^ p.γ =
          Kfloor * (Real.exp (-R) / 2) := by
        dsimp [Kfloor]
        ring
      _ ≤ K * (Real.exp (-R) / 2) := hscaled
      _ < budget := hsmall
      _ ≤ chiPosFloorGap p M targets.Lraw := by
        dsimp [budget]
        exact min_le_left _ _
  · have hcoeff : Kceiling ≤ K := by
      dsimp [K]
      exact le_max_right _ _
    have hscaled := mul_le_mul_of_nonneg_right hcoeff htau
    calc
      p.χ * M ^ (p.m - 1) *
            (Real.exp (-R) / 2) * targets.L ^ p.γ =
          Kceiling * (Real.exp (-R) / 2) := by
        dsimp [Kceiling]
        ring
      _ ≤ K * (Real.exp (-R) / 2) := hscaled
      _ < budget := hsmall
      _ ≤ chiPosCeilingGap p targets.L targets.Araw := by
        dsimp [budget]
        exact min_le_right _ _

/-! ## A strict far-left buffer -/

/-- Weighted compact convergence supplies a fixed far-left buffer which lies
strictly between the two raw barrier targets at every later time.  Its left
endpoint is moved far enough that the whole buffer remains inside the old
rectangle. -/
theorem exists_eventual_chiPos_farLeft_buffer
    {eta c : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (heta : 0 < eta)
    (hweighted : CoMovingWeightedL2Convergence eta c u U)
    (hmod : EventuallyUniformMovingFrameSpatialModulus 0
      (coMovingPath c u) U)
    (hU : Tendsto U atBot (nhds (1 : ℝ)))
    {L A R oldCut : ℝ} (hL : L < 1) (hA : 1 < A) (hR : 0 ≤ R) :
    ∃ cut T : ℝ,
      cut ≤ oldCut ∧ cut + R ≤ oldCut ∧
      ∀ t, T ≤ t → ∀ z ∈ Set.Icc cut (cut + R),
        coMovingPath c u t z ∈ Set.Ioo L A := by
  let e : ℝ := min (1 - L) (A - 1) / 2
  have he : 0 < e := by
    dsimp [e]
    exact div_pos (lt_min (sub_pos.mpr hL) (sub_pos.mpr hA)) (by norm_num)
  have htwoeL : 2 * e ≤ 1 - L := by
    have hmin := min_le_left (1 - L) (A - 1)
    dsimp [e]
    linarith
  have htwoeA : 2 * e ≤ A - 1 := by
    have hmin := min_le_right (1 - L) (A - 1)
    dsimp [e]
    linarith
  have hUevent : ∀ᶠ z in atBot, |U z - 1| < e := by
    have hball : Metric.ball (1 : ℝ) e ∈ nhds (1 : ℝ) :=
      Metric.ball_mem_nhds _ he
    have hev := hU hball
    filter_upwards [hev] with z hz
    simpa [Metric.mem_ball, Real.dist_eq] using hz
  obtain ⟨B, hUB⟩ := eventually_atBot.1 hUevent
  let cut : ℝ := min (oldCut - (R + 1)) (B - R)
  have hcut_old : cut ≤ oldCut := by
    have h := min_le_left (oldCut - (R + 1)) (B - R)
    dsimp [cut]
    linarith
  have hcutR_old : cut + R ≤ oldCut := by
    have h := min_le_left (oldCut - (R + 1)) (B - R)
    dsimp [cut]
    linarith
  have hcutR_B : cut + R ≤ B := by
    have h := min_le_right (oldCut - (R + 1)) (B - R)
    dsimp [cut]
    linarith
  obtain ⟨T, hclose⟩ :=
    eventually_coMovingPath_close_on_Icc_of_weightedL2_of_spatialModulus
      heta hweighted hmod (a := cut) (b := cut + R) e he
  refine ⟨cut, T, hcut_old, hcutR_old, ?_⟩
  intro t ht z hz
  have hpath := abs_lt.mp (hclose t ht z hz)
  have hprofile := abs_lt.mp (hUB z (hz.2.trans hcutR_B))
  constructor <;> linarith

/-! ## The floor half-round -/

/-- Run the weighted buffered floor until it has settled past the finite
target `L`. -/
theorem exists_eventual_chiPos_halfLine_floor
    (p : CMParams) (hchi : 0 < p.χ) (hchi_lt : p.χ < 1)
    (hcritical : p.α = p.m + p.γ - 1)
    (hceiling : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hleft : StrictlyPositiveAtLeft u₀.1) (c : ℝ)
    {G delta R cut Tbuf : ℝ}
    (old : ChiPosHalfLineRectangle p c
      (wholeLineCauchyGlobalU p u₀))
    (hG : 0 ≤ G) (hMG : old.M ≤ G)
    (hglobal : ∀ ⦃t : ℝ⦄, 0 ≤ t → ∀ x,
      wholeLineCauchyGlobalU p u₀ t x ≤ G)
    (hR : 0 ≤ R) (hcutR_old : cut + R ≤ old.cut)
    (targets : ChiPosHalfLineRoundTargets p old.ell old.M delta)
    (hbuffer : ∀ t, Tbuf ≤ t → ∀ z ∈ Set.Icc cut (cut + R),
      coMovingPath c (wholeLineCauchyGlobalU p u₀) t z ∈
        Set.Ioo targets.Lraw targets.Araw)
    (htail : p.χ * targets.Lraw ^ (p.m - 1) *
        (Real.exp (-R) / 2) * G ^ p.γ <
      chiPosFloorGap p old.M targets.Lraw) :
    ∃ t₁ : ℝ, 0 < t₁ ∧ old.start ≤ t₁ ∧ Tbuf ≤ t₁ ∧
      ∀ t, t₁ ≤ t → ∀ z, z ≤ cut →
        targets.L ≤
          coMovingPath c (wholeLineCauchyGlobalU p u₀) t z := by
  let tau : ℝ := Real.exp (-R) / 2
  have htau : 0 ≤ tau := by dsimp [tau]; positivity
  have hM : 0 ≤ old.M := zero_le_one.trans old.one_lt_M.le
  have hreserve :
      0 < chiPosHalfLineFloorReserve p old.M targets.Lraw tau G :=
    chiPosHalfLineFloorReserve_pos_of_tail_lt (by simpa [tau] using htail)
  let t₀ : ℝ := max (max old.start Tbuf) 1
  have ht₀ : 0 < t₀ :=
    zero_lt_one.trans_le (le_max_right (max old.start Tbuf) 1)
  have hold_t₀ : old.start ≤ t₀ :=
    (le_max_left old.start Tbuf).trans
      (le_max_left (max old.start Tbuf) 1)
  have hTbuf_t₀ : Tbuf ≤ t₀ :=
    (le_max_right old.start Tbuf).trans
      (le_max_left (max old.start Tbuf) 1)
  let floorData := wholeLineCauchyGlobal_positiveCoMovingRestartData
    p hceiling u₀ hu₀ hleft c ht₀ hglobal
  have hfloorLocal : ∀ s, 0 ≤ s → ∀ z, z ≤ cut + R →
      floorData.q s z ∈ Set.Icc old.ell old.M := by
    intro s hs z hz
    rw [floorData.eq_global hs z]
    exact old.bounds (t₀ + s)
      (hold_t₀.trans (le_add_of_nonneg_right hs)) z
      (hz.trans hcutR_old)
  have hfloorBuffer : ∀ s, 0 ≤ s →
      ∀ z ∈ Set.Icc cut (cut + R), targets.Lraw < floorData.q s z := by
    intro s hs z hz
    rw [floorData.eq_global hs z]
    exact (hbuffer (t₀ + s)
      (hTbuf_t₀.trans (le_add_of_nonneg_right hs)) z hz).1
  let floorRate : ℝ :=
    chiPosHalfLineFloorRate p old.M old.ell targets.Lraw tau G
  let floorBarrier : ℝ → ℝ :=
    chiZeroKPPFloor old.ell targets.Lraw floorRate
  have hfloorRate : 0 < floorRate := by
    exact chiPosHalfLineFloorRate_pos old.ell_pos
      (targets.ell_lt_L.trans targets.L_lt_Lraw) hreserve
  have hfloorInit : ∀ z ∈ Set.Iic cut,
      floorBarrier 0 ≤ floorData.q 0 z := by
    intro z hz
    rw [show floorBarrier 0 = old.ell by simp [floorBarrier]]
    rw [floorData.eq_global (s := 0) le_rfl z]
    have hcut_old : cut ≤ old.cut := by
      have hcutR : cut ≤ cut + R := by linarith
      exact hcutR.trans hcutR_old
    simpa using (old.bounds t₀ hold_t₀ z (hz.trans hcut_old)).1
  have hfloorRange : ∀ s, 0 ≤ s →
      floorBarrier s ∈ Set.Icc (0 : ℝ) old.M := by
    intro s hs
    have hlo : old.ell ≤ floorBarrier s :=
      chiZeroKPPFloor_ge_start
        (targets.ell_lt_L.trans targets.L_lt_Lraw).le
        hfloorRate.le hs
    have hhi : floorBarrier s ≤ targets.Lraw :=
      chiZeroKPPFloor_le_target
        (targets.ell_lt_L.trans targets.L_lt_Lraw).le
    exact ⟨old.ell_pos.le.trans hlo,
      hhi.trans (targets.Lraw_lt_one.le.trans old.one_lt_M.le)⟩
  have hfloorAll : ∀ s, 0 ≤ s → ∀ z ∈ Set.Iic cut,
      floorBarrier s ≤ floorData.q s z := by
    apply floorData.ge_of_weighted_buffered_floor
        (x₀ := cut) (R := R) (ell := old.ell) (M := old.M)
        (b := floorBarrier) hchi hR old.ell_pos.le hM
        (old.ell_lt_one.trans old.one_lt_M).le hMG
    · rw [continuous_iff_continuousAt]
      intro s
      exact (chiZeroKPPFloor_hasDerivAt
        old.ell targets.Lraw floorRate s).continuousAt
    · exact hfloorLocal
    · exact hfloorRange
    · exact hfloorInit
    · intro s hs z hz
      exact (chiZeroKPPFloor_le_target
        (targets.ell_lt_L.trans targets.L_lt_Lraw).le).trans
          (hfloorBuffer s hs z hz).le
    · intro s hs
      exact (chiZeroKPPFloor_hasDerivAt
        old.ell targets.Lraw floorRate s).differentiableAt.hasDerivAt
    · intro s hs
      have hb := chiZeroKPPFloor_tail_weighted_subsolution
        (p := p) (M := old.M) (C := old.ell) (L := targets.Lraw)
        (tau := tau) (G := G) (t := s) hcritical hchi.le hchi_lt
        old.ell_pos (targets.ell_lt_L.trans targets.L_lt_Lraw)
        targets.Lraw_lt_one.le old.one_lt_M.le htau hG hreserve hs.le
      dsimp [floorBarrier, floorRate, tau] at hb ⊢
      unfold reactionFun at hb
      linarith
  have hfloorTend : Tendsto floorBarrier atTop (nhds targets.Lraw) :=
    chiZeroKPPFloor_tendsto_target hfloorRate
  have hfloorNhd : Set.Ioi targets.L ∈ nhds targets.Lraw :=
    Ioi_mem_nhds targets.L_lt_Lraw
  obtain ⟨Sfloor, hSfloor⟩ := eventually_atTop.1
    (hfloorTend.eventually hfloorNhd)
  let sfloor : ℝ := max Sfloor 0
  have hsfloor : 0 ≤ sfloor := le_max_right Sfloor 0
  have hS_sfloor : Sfloor ≤ sfloor := le_max_left Sfloor 0
  let t₁ : ℝ := t₀ + sfloor
  refine ⟨t₁, by dsimp [t₁]; linarith, ?_, ?_, ?_⟩
  · dsimp [t₁]
    exact hold_t₀.trans (le_add_of_nonneg_right hsfloor)
  · dsimp [t₁]
    exact hTbuf_t₀.trans (le_add_of_nonneg_right hsfloor)
  · intro t ht z hz
    let s : ℝ := t - t₀
    have hs : 0 ≤ s := by dsimp [s, t₁] at ht ⊢; linarith
    have hsettled : Sfloor ≤ s := by
      dsimp [s, t₁] at ht ⊢
      linarith
    have hcomp := hfloorAll s hs z (Set.mem_Iic.mpr hz)
    have hbarrier := (hSfloor s hsettled).le
    rw [floorData.eq_global hs z] at hcomp
    have htime : t₀ + s = t := by dsimp [s]; ring
    rw [htime] at hcomp
    exact hbarrier.trans hcomp

/-! ## The ceiling half-round -/

/-- Restart after the floor has settled, splice that floor with the strict
compact buffer, and run the weighted ceiling until it lies below `A`. -/
theorem exists_eventual_chiPos_halfLine_ceiling
    (p : CMParams) (hchi : 0 < p.χ) (hchi_lt : p.χ < 1)
    (hcritical : p.α = p.m + p.γ - 1)
    (hceiling : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hleft : StrictlyPositiveAtLeft u₀.1) (c : ℝ)
    {G delta R cut Tbuf t₁ : ℝ}
    (old : ChiPosHalfLineRectangle p c
      (wholeLineCauchyGlobalU p u₀))
    (hMG : old.M ≤ G)
    (hglobal : ∀ ⦃t : ℝ⦄, 0 ≤ t → ∀ x,
      wholeLineCauchyGlobalU p u₀ t x ≤ G)
    (hR : 0 ≤ R) (hcutR_old : cut + R ≤ old.cut)
    (targets : ChiPosHalfLineRoundTargets p old.ell old.M delta)
    (hbuffer : ∀ t, Tbuf ≤ t → ∀ z ∈ Set.Icc cut (cut + R),
      coMovingPath c (wholeLineCauchyGlobalU p u₀) t z ∈
        Set.Ioo targets.Lraw targets.Araw)
    (ht₁ : 0 < t₁) (hold_t₁ : old.start ≤ t₁) (hTbuf_t₁ : Tbuf ≤ t₁)
    (hfloor : ∀ t, t₁ ≤ t → ∀ z, z ≤ cut →
      targets.L ≤ coMovingPath c (wholeLineCauchyGlobalU p u₀) t z)
    (htail : p.χ * old.M ^ (p.m - 1) *
        (Real.exp (-R) / 2) * targets.L ^ p.γ <
      chiPosCeilingGap p targets.L targets.Araw) :
    ∃ t₂ : ℝ, t₁ ≤ t₂ ∧
      ∀ t, t₂ ≤ t → ∀ z, z ≤ cut →
        coMovingPath c (wholeLineCauchyGlobalU p u₀) t z ∈
          Set.Icc targets.L targets.A := by
  let tau : ℝ := Real.exp (-R) / 2
  have htau : 0 ≤ tau := by dsimp [tau]; positivity
  have hM : 0 ≤ old.M := zero_le_one.trans old.one_lt_M.le
  have hL : 0 ≤ targets.L :=
    (old.ell_pos.trans targets.ell_lt_L).le
  have hLM : targets.L ≤ old.M :=
    targets.L_lt_one.le.trans old.one_lt_M.le
  have hreserve :
      0 < chiPosHalfLineCeilingReserve p targets.L targets.Araw old.M tau :=
    chiPosHalfLineCeilingReserve_pos_of_tail_lt (by simpa [tau] using htail)
  let ceilingData := wholeLineCauchyGlobal_positiveCoMovingRestartData
    p hceiling u₀ hu₀ hleft c ht₁ hglobal
  have hceilingLocal : ∀ s, 0 ≤ s → ∀ z, z ≤ cut + R →
      ceilingData.q s z ∈ Set.Icc targets.L old.M := by
    intro s hs z hz
    rw [ceilingData.eq_global hs z]
    have htimeStart : old.start ≤ t₁ + s :=
      hold_t₁.trans (le_add_of_nonneg_right hs)
    constructor
    · by_cases hzcut : z ≤ cut
      · exact hfloor (t₁ + s) (le_add_of_nonneg_right hs) z hzcut
      · have hzbuffer : z ∈ Set.Icc cut (cut + R) :=
          ⟨(lt_of_not_ge hzcut).le, hz⟩
        exact targets.L_lt_Lraw.le.trans
          (hbuffer (t₁ + s)
            (hTbuf_t₁.trans (le_add_of_nonneg_right hs)) z hzbuffer).1.le
    · exact (old.bounds (t₁ + s) htimeStart z
        (hz.trans hcutR_old)).2
  let ceilingRate : ℝ :=
    chiPosHalfLineCeilingRate p targets.L targets.Araw old.M tau
  let ceilingBarrier : ℝ → ℝ :=
    chiPosTargetCeiling targets.Araw old.M ceilingRate
  have hceilingRate : 0 < ceilingRate := by
    exact chiPosHalfLineCeilingRate_pos
      (zero_lt_one.trans targets.one_lt_Araw)
      (targets.Araw_lt_A.trans targets.A_lt_M) hreserve
  have hceilingInit : ∀ z ∈ Set.Iic cut,
      ceilingData.q 0 z ≤ ceilingBarrier 0 := by
    intro z hz
    rw [show ceilingBarrier 0 = old.M by simp [ceilingBarrier]]
    exact (hceilingLocal 0 le_rfl z
      (hz.trans (by linarith [hR]))).2
  have hceilingRange : ∀ s, 0 ≤ s →
      ceilingBarrier s ∈ Set.Icc (0 : ℝ) old.M := by
    intro s hs
    have hlo : targets.Araw ≤ ceilingBarrier s :=
      chiPosTargetCeiling_ge_target
        (targets.Araw_lt_A.trans targets.A_lt_M).le
    have hhi : ceilingBarrier s ≤ old.M :=
      chiPosTargetCeiling_le_start
        (targets.Araw_lt_A.trans targets.A_lt_M).le hceilingRate.le hs
    exact ⟨(zero_lt_one.trans targets.one_lt_Araw).le.trans hlo, hhi⟩
  have hceilingAll : ∀ s, 0 ≤ s → ∀ z ∈ Set.Iic cut,
      ceilingData.q s z ≤ ceilingBarrier s := by
    apply ceilingData.le_of_weighted_buffered_ceiling
      (x₀ := cut) (R := R) (Lhat := targets.L) (M := old.M)
        (a := ceilingBarrier) hchi hR hL hM hLM hMG
    · rw [continuous_iff_continuousAt]
      intro s
      exact (chiPosTargetCeiling_hasDerivAt
        targets.Araw old.M ceilingRate s).continuousAt
    · exact hceilingLocal
    · exact hceilingRange
    · exact hceilingInit
    · intro s hs z hz
      rw [ceilingData.eq_global hs z]
      exact (hbuffer (t₁ + s)
        (hTbuf_t₁.trans (le_add_of_nonneg_right hs)) z hz).2.le.trans
          (chiPosTargetCeiling_ge_target
            (targets.Araw_lt_A.trans targets.A_lt_M).le)
    · intro s hs
      exact (chiPosTargetCeiling_hasDerivAt
        targets.Araw old.M ceilingRate s).differentiableAt.hasDerivAt
    · intro s hs
      have hb := chiPosTargetCeiling_tail_weighted_supersolution
        (p := p) (ell := targets.L) (A := targets.Araw) (D := old.M)
        (tau := tau) (t := s) hcritical hchi.le hchi_lt
        (old.ell_pos.trans targets.ell_lt_L) targets.L_lt_one.le
        targets.one_lt_Araw.le
        (targets.Araw_lt_A.trans targets.A_lt_M) htau hreserve hs.le
      simpa [ceilingBarrier, ceilingRate, tau, reactionFun] using hb
  have hceilingTend : Tendsto ceilingBarrier atTop (nhds targets.Araw) :=
    chiPosTargetCeiling_tendsto_target hceilingRate
  have hceilingNhd : Set.Iio targets.A ∈ nhds targets.Araw :=
    Iio_mem_nhds targets.Araw_lt_A
  obtain ⟨Sceiling, hSceiling⟩ := eventually_atTop.1
    (hceilingTend.eventually hceilingNhd)
  let sceiling : ℝ := max Sceiling 0
  have hsceiling : 0 ≤ sceiling := le_max_right Sceiling 0
  have hS_sceiling : Sceiling ≤ sceiling := le_max_left Sceiling 0
  let t₂ : ℝ := t₁ + sceiling
  refine ⟨t₂, by dsimp [t₂]; linarith, ?_⟩
  intro t ht z hz
  let s : ℝ := t - t₁
  have hs : 0 ≤ s := by dsimp [s, t₂] at ht ⊢; linarith
  have hsettled : Sceiling ≤ s := by
    dsimp [s, t₂] at ht ⊢
    linarith
  have hcomp := hceilingAll s hs z (Set.mem_Iic.mpr hz)
  rw [ceilingData.eq_global hs z] at hcomp
  have htime : t₁ + s = t := by dsimp [s]; ring
  rw [htime] at hcomp
  refine ⟨hfloor t (by dsimp [t₂] at ht; linarith) z hz, ?_⟩
  exact hcomp.trans (hSceiling s hsettled).le

/-! ## One complete successor round -/

/-- Every strict positive-sensitivity half-line rectangle admits a buffered
successor.  The buffer width is chosen from both weighted contact reserves;
the floor and ceiling are then advanced in two consecutive restarts. -/
theorem exists_next_chiPosHalfLineRectangle
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (hchi : 0 < p.χ) (hchi_lt : p.χ < 1)
    (hcritical : p.α = p.m + p.γ - 1)
    {c eta : ℝ} {U V : ℝ → ℝ}
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hroot : paper531RootMinus c
      (paper531ConcreteStabilityBudget p hregime).A
      (paper531ConcreteStabilityBudget p hregime).B < eta)
    (hetaCap : eta < stabilityWeightCap p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hleft : StrictlyPositiveAtLeft u₀.1)
    (hinitial : WeightedL2InitialCloseness eta u₀.1 U)
    {delta : ℝ} (hdelta : 0 < delta)
    (old : ChiPosHalfLineRectangle p c
      (wholeLineCauchyGlobalU p u₀)) :
    Nonempty {new : ChiPosHalfLineRectangle p c
        (wholeLineCauchyGlobalU p u₀) //
      ChiPosHalfLineRectangleStep p delta old new} := by
  have hceiling : WholeLineCauchyCeilingRegime p :=
    Or.inr ⟨hchi.le, Or.inr ⟨hchi_lt, hcritical⟩⟩
  have heta : 0 < eta :=
    ((paper531ConcreteStabilityBudget p hregime).rootMinus_pos hc).trans hroot
  have hweighted : CoMovingWeightedL2Convergence eta c
      (wholeLineCauchyGlobalU p u₀) U :=
    wholeLineCauchyGlobal_coMovingWeightedL2Convergence_chi_pos_natural
      p hregime hchi hc hTW hbound hreg hroot hetaCap u₀ hu₀ hinitial
  have hmod : EventuallyUniformMovingFrameSpatialModulus 0
      (coMovingPath c (wholeLineCauchyGlobalU p u₀)) U :=
    wholeLineCauchyGlobal_eventuallyUniformMovingFrameSpatialModulus
      p hceiling u₀ hu₀ c hTW hreg
  obtain ⟨targets⟩ := exists_chiPos_halfLine_round_targets
    hcritical hchi.le hchi_lt hdelta old
  let canonicalG : ℝ := max (MChi p) ‖u₀‖
  let G : ℝ := max canonicalG old.M
  have hMG : old.M ≤ G := by
    dsimp [G]
    exact le_max_right _ _
  have hG : 0 ≤ G :=
    (zero_le_one.trans old.one_lt_M.le).trans hMG
  have hglobal : ∀ ⦃t : ℝ⦄, 0 ≤ t → ∀ x,
      wholeLineCauchyGlobalU p u₀ t x ≤ G := by
    intro t ht x
    have hbase := wholeLineCauchyGlobal_le_max_of_chi_pos
      p hchi hchi_lt hcritical hceiling u₀ hu₀ ht x
    exact hbase.trans (by
      dsimp [G, canonicalG]
      exact le_max_left _ _)
  obtain ⟨R, hR, hfloorTail, hceilingTail⟩ :=
    exists_chiPos_halfLine_round_buffer_width (G := G) targets
  obtain ⟨cut, Tbuf, hcut_old, hcutR_old, hbuffer⟩ :=
    exists_eventual_chiPos_farLeft_buffer
      heta hweighted hmod hTW.lim_neg_inf.1
      (L := targets.Lraw) (A := targets.Araw)
      (R := R) (oldCut := old.cut)
      targets.Lraw_lt_one targets.one_lt_Araw hR
  obtain ⟨t₁, ht₁, hold_t₁, hTbuf_t₁, hfloor⟩ :=
    exists_eventual_chiPos_halfLine_floor
      p hchi hchi_lt hcritical hceiling u₀ hu₀ hleft c
      (G := G) (delta := delta) (R := R) (cut := cut) (Tbuf := Tbuf)
      old hG hMG hglobal hR hcutR_old targets hbuffer hfloorTail
  obtain ⟨t₂, _ht₁_t₂, hfinal⟩ :=
    exists_eventual_chiPos_halfLine_ceiling
      p hchi hchi_lt hcritical hceiling u₀ hu₀ hleft c
      (G := G) (delta := delta) (R := R) (cut := cut)
      (Tbuf := Tbuf) (t₁ := t₁) old hMG hglobal hR hcutR_old
      targets hbuffer ht₁ hold_t₁ hTbuf_t₁ hfloor hceilingTail
  let new : ChiPosHalfLineRectangle p c
      (wholeLineCauchyGlobalU p u₀) :=
    { ell := targets.L
      M := targets.A
      start := t₂
      cut := cut
      ell_pos := old.ell_pos.trans targets.ell_lt_L
      ell_lt_one := targets.L_lt_one
      one_lt_M := targets.one_lt_A
      floor_margin := targets.next_floor_margin
      ceiling_margin := targets.next_ceiling_margin
      bounds := hfinal }
  refine ⟨⟨new, ?_⟩⟩
  exact
    { ell_le := targets.ell_lt_L.le
      M_le := targets.A_lt_M.le
      cut_le := hcut_old
      floor_budget := by
        dsimp [new]
        linarith [targets.floor_delta]
      ceiling_budget := by
        dsimp [new]
        linarith [targets.ceiling_delta] }

section AxiomAudit

#print axioms WholeLineChiPosCoMovingRestartData.expanded_pde
#print axioms wholeLineCauchyGlobal_positiveCoMovingRestartData
#print axioms
  WholeLineChiPosCoMovingRestartData.ge_of_weighted_buffered_floor
#print axioms
  WholeLineChiPosCoMovingRestartData.le_of_weighted_buffered_ceiling
#print axioms exists_chiPos_halfLine_round_buffer_width
#print axioms exists_eventual_chiPos_farLeft_buffer
#print axioms exists_eventual_chiPos_halfLine_floor
#print axioms exists_eventual_chiPos_halfLine_ceiling
#print axioms exists_next_chiPosHalfLineRectangle

end AxiomAudit

end ShenWork.Paper1
