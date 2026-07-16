import ShenWork.Paper1.WholeLineWeightedRegularityChiZeroKPPComparisonNatural
import ShenWork.Paper1.WholeLineWeightedRegularityChiZeroFixedPointNatural
import ShenWork.Paper1.WholeLineWeightedRegularityPlateauComparisonNatural
import ShenWork.Paper1.WholeLineWeightedRegularityGlobalStrictPositivityNatural
import ShenWork.Paper1.WholeLineCauchySharpBound
import ShenWork.Paper1.WholeLineCauchyLongTimeBound
import ShenWork.Paper1.WholeLineCauchyLeftTailBridge

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-!
# The zero-sensitivity left equilibrium

At a fixed co-moving point, weighted convergence and the eventual spatial
modulus give a persistent lateral value near the wave.  A positive restart
slice has a uniform floor on the entire left half-line, by compactness on
the finite part between its one-sided floor and the lateral point.  The
target-capped scalar KPP comparison then raises this floor arbitrarily close
to one.
-/

/-- One-sided uniform positivity, pointwise strict positivity, and
continuity give a positive floor on every prescribed left half-line. -/
theorem exists_pos_floor_Iic_of_continuous_pos_of_strictlyPositiveAtLeft
    {f : ℝ → ℝ} (hcont : Continuous f) (hpos : ∀ x, 0 < f x)
    (hleft : StrictlyPositiveAtLeft f) (z₀ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Set.Iic z₀, C ≤ f x := by
  rcases hleft with ⟨delta, hdelta, hdeltaEv⟩
  rcases eventually_atBot.1 hdeltaEv with ⟨A, hA⟩
  by_cases hzA : z₀ ≤ A
  · exact ⟨delta, hdelta, fun x hx => hA x (hx.trans hzA)⟩
  · have hAz : A ≤ z₀ := le_of_not_ge hzA
    obtain ⟨d, hd, hdle⟩ := isCompact_Icc.exists_forall_le'
      hcont.continuousOn (fun x _hx => hpos x)
    let C : ℝ := min delta d
    refine ⟨C, lt_min hdelta hd, ?_⟩
    intro x hx
    by_cases hxA : x ≤ A
    · exact (min_le_left delta d).trans (hA x hxA)
    · have hAx : A ≤ x := le_of_not_ge hxA
      exact (min_le_right delta d).trans (hdle x ⟨hAx, hx⟩)

/-- The canonical glued orbit preserves `StrictlyPositiveAtLeft` on every
nonnegative physical-time slice. -/
theorem wholeLineCauchyGlobal_strictlyPositiveAtLeft_of_posAtBot
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hleft : StrictlyPositiveAtLeft u₀.1)
    {t : ℝ} (ht : 0 ≤ t) :
    StrictlyPositiveAtLeft (wholeLineCauchyGlobalU p u₀ t) := by
  let n := wholeLineCauchyGlobalIndex p u₀ t
  let q := wholeLineCauchyGlobalLocalTime p u₀ t
  let z : Set.Icc (0 : ℝ) (wholeLineCauchyGlobalSegmentTime p u₀) :=
    ⟨q, wholeLineCauchyGlobalLocalTime_nonneg p u₀ ht,
      (wholeLineCauchyGlobalLocalTime_lt_segmentTime p u₀ ht).le⟩
  have hsegment :=
    (wholeLineCauchyGlobalDatum_segment_pos_and_left_of_posAtBot
      p hregime u₀ hu₀ hleft n).2.2 z
  have heq : wholeLineCauchyGlobalU p u₀ t =
      fun x => (wholeLineCauchyGlobalSegment p u₀ n z).1 x := by
    funext x
    have hx := congrArg (fun w : WholeLineBUC => w.1 x)
      (wholeLineCauchyGlobalBUC_eq_segment p u₀ ht)
    simpa [wholeLineCauchyGlobalU, n, q, z] using hx
  rw [heq]
  exact hsegment

/-- At zero sensitivity, the canonical orbit converges uniformly to the
left equilibrium in every sufficiently far-left co-moving half-line.  The
only asymptotic input is the already constructed co-moving weighted energy
and its canonical eventual spatial modulus. -/
theorem
    wholeLineCauchyGlobal_uniformCoMovingLeftEquilibriumConvergence_chi_zero_natural
    (p : CMParams) (hchi : p.χ = 0)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hleft : StrictlyPositiveAtLeft u₀.1)
    {c eta : ℝ} {U V : ℝ → ℝ}
    (heta : 0 < eta) (hTW : IsTravelingWave p c U V)
    (hweighted : CoMovingWeightedL2Convergence eta c
      (wholeLineCauchyGlobalU p u₀) U)
    (hmod : EventuallyUniformMovingFrameSpatialModulus 0
      (coMovingPath c (wholeLineCauchyGlobalU p u₀)) U) :
    UniformCoMovingLeftEquilibriumConvergence c
      (wholeLineCauchyGlobalU p u₀) := by
  let hregime : WholeLineCauchyCeilingRegime p :=
    WholeLineCauchyCeilingRegime.of_nonpositive hchi.le
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
  have hUevent : ∀ᶠ z in atBot, 1 - e / 2 < U z := by
    have hnhds : Set.Ioi (1 - e / 2) ∈ nhds (1 : ℝ) :=
      Ioi_mem_nhds (by linarith)
    exact hTW.lim_neg_inf.1 hnhds
  rcases eventually_atBot.1 hUevent with ⟨z₀, hUz₀⟩
  obtain ⟨Tb, hboundaryClose⟩ :=
    eventually_coMovingPath_close_at_fixed_of_weightedL2_of_spatialModulus
      heta hweighted hmod z₀ (e / 2) (by positivity)
  let t₀ : ℝ := max Tb 1
  have ht₀ : 0 < t₀ := lt_of_lt_of_le zero_lt_one (le_max_right Tb 1)
  let M : ℝ := max 1 ‖u₀‖
  have hM : 0 ≤ M := zero_le_one.trans (le_max_left 1 ‖u₀‖)
  have hLM : L ≤ M := by
    exact (le_of_lt hL1).trans (le_max_left 1 ‖u₀‖)
  let q : ℝ → ℝ → ℝ := fun s x =>
    wholeLineCauchyGlobalU p u₀ (t₀ + max s 0)
      (x + c * (t₀ + max s 0))
  have hqcont : Continuous (fun r : ℝ × ℝ => q r.1 r.2) := by
    rw [continuous_iff_continuousAt]
    intro r
    have hphys : 0 < t₀ + max r.1 0 := by
      have : 0 ≤ max r.1 0 := le_max_right _ _
      linarith
    have hbase := wholeLineCauchyGlobalU_joint_hasFDerivAt_positive
      p hregime u₀ hu₀ hphys
        (x := r.2 + c * (t₀ + max r.1 0))
    have hmap : ContinuousAt
        (fun a : ℝ × ℝ =>
          (t₀ + max a.1 0, a.2 + c * (t₀ + max a.1 0))) r := by
      fun_prop
    simpa [q, Function.comp_def] using
      hbase.continuousAt.comp
        (f := fun a : ℝ × ℝ =>
          (t₀ + max a.1 0, a.2 + c * (t₀ + max a.1 0))) hmap
  have hqrange : ∀ s, 0 ≤ s → ∀ x ∈ Set.Iic z₀,
      q s x ∈ Set.Icc (0 : ℝ) M := by
    intro s hs x _hx
    have hphys : 0 ≤ t₀ + s := by linarith
    have hphysPos : 0 < t₀ + s := by linarith
    constructor
    · simpa [q, max_eq_left hs] using
        wholeLineCauchyGlobal_nonnegative p hregime u₀ hu₀ hphys
          (x + c * (t₀ + s))
    · simpa [q, M, max_eq_left hs] using
        wholeLineCauchyGlobal_le_max_one_of_chi_nonpos
          p hchi.le u₀ hu₀ ‖u₀‖
          (fun y => WholeLineBUC.apply_le_norm u₀ y) hphys
          (x + c * (t₀ + s))
  have hsliceLeft : StrictlyPositiveAtLeft (q 0) := by
    have hphysical := wholeLineCauchyGlobal_strictlyPositiveAtLeft_of_posAtBot
      p hregime u₀ hu₀ hleft ht₀.le
    simpa [q, max_eq_right (le_refl (0 : ℝ)), coMovingPath] using
      hphysical.shift (c * t₀)
  have hsliceCont : Continuous (q 0) := by
    have hC2 := wholeLineCauchyGlobal_coMovingRestart_contDiff_two
      p hregime u₀ hu₀ c t₀ (t := 0) (by simpa using ht₀)
    simpa [q, max_eq_right (le_refl (0 : ℝ))] using hC2.continuous
  have hslicePos : ∀ x, 0 < q 0 x := by
    intro x
    simpa [q, max_eq_right (le_refl (0 : ℝ))] using
      wholeLineCauchyGlobal_pos_of_posAtBot
        p hregime u₀ hu₀ hleft ht₀ (x + c * t₀)
  obtain ⟨Cbase, hCbase, hCbaseFloor⟩ :=
    exists_pos_floor_Iic_of_continuous_pos_of_strictlyPositiveAtLeft
      hsliceCont hslicePos hsliceLeft z₀
  let C : ℝ := min (Cbase / 2) (L / 2)
  have hC : 0 < C := by
    dsimp [C]
    exact lt_min (by positivity) (by positivity)
  have hCL : C < L := by
    have hCle : C ≤ L / 2 := by dsimp [C]; exact min_le_right _ _
    linarith
  have hinit : ∀ x ∈ Set.Iic z₀, C ≤ q 0 x := by
    intro x hx
    exact (min_le_left (Cbase / 2) (L / 2)).trans
      ((half_le_self hCbase.le).trans (hCbaseFloor x hx))
  have hboundary : ∀ s, 0 ≤ s → L ≤ q s z₀ := by
    intro s hs
    have htime : Tb ≤ t₀ + s := by
      exact (le_max_left Tb 1).trans (by linarith)
    have hclose := hboundaryClose (t₀ + s) htime
    have hUlower := hUz₀ z₀ le_rfl
    have hdiffLower : -(e / 2) <
        coMovingPath c (wholeLineCauchyGlobalU p u₀) (t₀ + s) z₀ - U z₀ :=
      (neg_lt_of_abs_lt hclose)
    change -(e / 2) <
      wholeLineCauchyGlobalU p u₀ (t₀ + s)
          (z₀ + c * (t₀ + s)) - U z₀ at hdiffLower
    have hraw : 1 - e ≤
        wholeLineCauchyGlobalU p u₀ (t₀ + s)
          (z₀ + c * (t₀ + s)) := by
      linarith
    simpa [L, q, max_eq_left hs] using hraw
  have htimeOp : ∀ ⦃s x : ℝ⦄, 0 < s →
      HasDerivAt (fun r : ℝ => q r x)
        (paperWaveOperator p c (q s) (q s) x) s := by
    intro s x hs
    have hphysical : 0 < t₀ + s := by linarith
    have hraw :=
      wholeLineCauchyGlobal_coMovingRestart_hasDerivAt_paperWaveOperator
        p hregime u₀ hu₀ c t₀ hphysical x
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
        p hregime u₀ hu₀ c t₀ hphysical
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
  have hpdeq : ∀ ⦃s x : ℝ⦄, 0 < s → x < z₀ →
      deriv (fun r : ℝ => q r x) s ≥
        deriv (fun y : ℝ => deriv (fun z : ℝ => q s z) y) x +
          c * deriv (fun y : ℝ => q s y) x + reactionFun p.α (q s x) := by
    intro s x hs _hx
    have ht := (htimeOp (s := s) (x := x) hs).deriv
    have hiter : iteratedDeriv 2 (q s) x =
        deriv (fun y : ℝ => deriv (fun z : ℝ => q s z) y) x := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
        iteratedDeriv_one]
    rw [ht]
    unfold paperWaveOperator reactionFun
    rw [hchi, hiter]
    ring_nf
    exact le_rfl
  obtain ⟨S, hfloor⟩ := eventually_leftHalfLine_ge_of_fixed_boundary_kpp
    p.hα hM hC hCL hL1 hLM hL₀L hqcont hqrange hinit hboundary
      htimeq hspace1q hspace2q hpdeq
  let S₀ : ℝ := max S 0
  have hS₀_nonneg : 0 ≤ S₀ := by
    dsimp [S₀]
    exact le_max_right S 0
  have hS_le : S ≤ S₀ := by
    dsimp [S₀]
    exact le_max_left S 0
  obtain ⟨Tup, hupper⟩ := eventually_atTop.1
    (wholeLineCauchyGlobal_uniformLimsupLe_one_of_chi_nonpos
      p hchi.le u₀ hu₀ e he)
  refine ⟨max 0 (-z₀), max (t₀ + S₀) Tup, ?_⟩
  intro t z ht _hz
  have htKPP : S ≤ t - t₀ := by
    have hS₀t : S₀ ≤ t - t₀ := by
      have := (le_max_left (t₀ + S₀) Tup).trans ht
      linarith
    exact hS_le.trans hS₀t
  have hrel0 : 0 ≤ t - t₀ := by
    have := (le_max_left (t₀ + S₀) Tup).trans ht
    linarith
  have hcut : -max 0 (-z₀) ≤ z₀ := by
    simpa using neg_le_neg (le_max_right (0 : ℝ) (-z₀))
  have hlower := hfloor (t - t₀) htKPP z
    (Set.mem_Iic.mpr (_hz.trans hcut))
  have huLower : 1 - 2 * e <
      wholeLineCauchyGlobalU p u₀ t (z + c * t) := by
    simpa [q, L₀, max_eq_left hrel0, coMovingPath] using hlower
  have htUpper : Tup ≤ t := (le_max_right (t₀ + S₀) Tup).trans ht
  have huUpper := hupper t htUpper (z + c * t)
  have habs :
      |wholeLineCauchyGlobalU p u₀ t (z + c * t) - 1| < epsilon := by
    rw [abs_lt]
    constructor <;> linarith
  simpa [coMovingPath] using habs

section AxiomAudit

#print axioms exists_pos_floor_Iic_of_continuous_pos_of_strictlyPositiveAtLeft
#print axioms wholeLineCauchyGlobal_strictlyPositiveAtLeft_of_posAtBot
#print axioms
  wholeLineCauchyGlobal_uniformCoMovingLeftEquilibriumConvergence_chi_zero_natural

end AxiomAudit

end ShenWork.Paper1
