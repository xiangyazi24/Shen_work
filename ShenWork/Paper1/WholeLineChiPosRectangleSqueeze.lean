import ShenWork.Paper1.WholeLineChiPosAffineIteration
import ShenWork.Paper1.WholeLineChiPosCanonicalRestartNatural
import ShenWork.Paper1.WholeLineChiPosDecayFloorNatural
import ShenWork.Paper1.WholeLineChiPosRectangleTargets
import ShenWork.Paper1.WholeLineChiPosWholeLineComparisonNatural
import ShenWork.Paper1.UniformTwoSidedConvergence

open Filter Topology Set Real Function

noncomputable section

namespace ShenWork.Paper1

/-!
# Whole-line rectangle squeeze for positive sensitivity

At the critical exponent `α = m + γ - 1`, an eventual rectangle
`[ell, M]` is improved by a weighted floor barrier followed by a weighted
ceiling barrier.  The resulting `α`-power gap contracts by `2 χ`; hence
`0 < χ < 1/2` forces uniform convergence to one.
-/

/-! ## Abstract rectangle iteration -/

/-- An eventual whole-line rectangle with the strict scalar margins needed
to run another coupled barrier round. -/
structure ChiPosWholeLineRectangle
    (p : CMParams) (u : ℝ → ℝ → ℝ) where
  ell : ℝ
  M : ℝ
  start : ℝ
  ell_pos : 0 < ell
  ell_lt_one : ell < 1
  one_lt_M : 1 < M
  floor_margin : 0 < chiPosFloorGap p M ell
  ceiling_margin : 0 < chiPosCeilingGap p ell M
  bounds : ∀ t, start ≤ t → ∀ x, ell ≤ u t x ∧ u t x ≤ M

/-- The numerical data carried from one rectangle round to the next. -/
structure ChiPosWholeLineRectangleStep
    (p : CMParams) {u : ℝ → ℝ → ℝ} (δ : ℝ)
    (old new : ChiPosWholeLineRectangle p u) : Prop where
  ell_le : old.ell ≤ new.ell
  M_le : new.M ≤ old.M
  floor_budget :
    1 - new.ell ^ p.α ≤
      p.χ *
        (new.ell ^ (p.m - 1) * (old.M ^ p.γ - new.ell ^ p.γ)) + δ
  ceiling_budget :
    new.M ^ p.α - 1 ≤
      p.χ *
        (new.M ^ (p.m - 1) * (new.M ^ p.γ - new.ell ^ p.γ)) + δ

/-- One PDE rectangle round has the affine gap estimate proved in the scalar
squeeze algebra. -/
theorem ChiPosWholeLineRectangleStep.gap_le
    {p : CMParams} {u : ℝ → ℝ → ℝ} {δ : ℝ}
    {old new : ChiPosWholeLineRectangle p u}
    (h : ChiPosWholeLineRectangleStep p δ old new)
    (hcritical : p.α = p.m + p.γ - 1) (hchi : 0 ≤ p.χ) :
    new.M ^ p.α - new.ell ^ p.α ≤
      2 * p.χ * (old.M ^ p.α - old.ell ^ p.α) + 2 * δ := by
  exact chiPos_squeeze_gap_step p.hm p.hγ hcritical hchi
    old.ell_pos h.ell_le new.ell_lt_one.le new.one_lt_M.le h.M_le
    h.floor_budget h.ceiling_budget

/-- Abstract endgame: if every strict-margin rectangle admits another
coupled round, the fixed-defect iteration proves uniform convergence. -/
theorem uniformConvergesToConstant_one_of_rectangle_successors
    (p : CMParams) {u : ℝ → ℝ → ℝ}
    (hchi : 0 ≤ p.χ) (hchi_half : p.χ < 1 / 2)
    (hcritical : p.α = p.m + p.γ - 1)
    (seed : ChiPosWholeLineRectangle p u)
    (hsuccessor : ∀ δ, 0 < δ → ∀ old : ChiPosWholeLineRectangle p u,
      Nonempty {new : ChiPosWholeLineRectangle p u //
        ChiPosWholeLineRectangleStep p δ old new}) :
    UniformConvergesToConstant u 1 := by
  intro epsilon hepsilon
  let r : ℝ := 2 * p.χ
  let δ : ℝ := epsilon * (1 - r) / 4
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by dsimp [r]; linarith
  have h1r : 0 < 1 - r := sub_pos.mpr hr1
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let next : ChiPosWholeLineRectangle p u →
      ChiPosWholeLineRectangle p u := fun old =>
    (Classical.choice (hsuccessor δ hδ old)).1
  have hnext : ∀ old : ChiPosWholeLineRectangle p u,
      ChiPosWholeLineRectangleStep p δ old (next old) := by
    intro old
    exact (Classical.choice (hsuccessor δ hδ old)).2
  let rectangles : ℕ → ChiPosWholeLineRectangle p u := fun n =>
    next^[n] seed
  have hrectangleStep : ∀ n,
      ChiPosWholeLineRectangleStep p δ (rectangles n) (rectangles (n + 1)) := by
    intro n
    simpa [rectangles, Function.iterate_succ_apply'] using hnext (rectangles n)
  let gap : ℕ → ℝ := fun n =>
    (rectangles n).M ^ p.α - (rectangles n).ell ^ p.α
  have hgapStep : ∀ n, gap (n + 1) ≤ r * gap n + 2 * δ := by
    intro n
    simpa [gap, r] using
      (hrectangleStep n).gap_le hcritical hchi
  have hstationary : (2 * δ) / (1 - r) < epsilon := by
    have hne : 1 - r ≠ 0 := ne_of_gt h1r
    have heq : (2 * δ) / (1 - r) = epsilon / 2 := by
      dsimp [δ]
      field_simp
      ring
    rw [heq]
    linarith
  obtain ⟨n, hgap⟩ := exists_index_affine_recurrence_lt
    hr0 hr1 (mul_nonneg (by norm_num) hδ.le) hgapStep hstationary
  refine ⟨(rectangles n).start, ?_⟩
  intro t x ht
  have hrect := (rectangles n).bounds t ht x
  have habs := abs_sub_one_le_rpow_gap p.hα
    (rectangles n).ell_pos (rectangles n).ell_lt_one.le
    (rectangles n).one_lt_M.le hrect.1 hrect.2
  exact habs.trans_lt hgap

section RectangleIterationAxiomAudit

#print axioms ChiPosWholeLineRectangleStep.gap_le
#print axioms uniformConvergesToConstant_one_of_rectangle_successors

end RectangleIterationAxiomAudit

/-! ## Resolver bounds on a canonical restart -/

/-- An eventual population ceiling gives the corresponding frozen resolver
ceiling on every positive restarted slice. -/
theorem WholeLineChiPosCanonicalRestartData.frozenElliptic_le_of_le
    {p : CMParams} {u₀ : WholeLineBUC} {t₀ G M : ℝ}
    (d : WholeLineChiPosCanonicalRestartData p u₀ t₀ G)
    (hM : 0 ≤ M)
    (hqM : ∀ ⦃s : ℝ⦄, 0 ≤ s → ∀ x, d.q s x ≤ M)
    {s x : ℝ} (hs : 0 < s) :
    frozenElliptic p (d.q s) x ≤ M ^ p.γ := by
  apply frozenElliptic_le_of_rpow_le p
    (Real.rpow_nonneg hM p.γ)
    ((d.slice_contDiff_two hs).continuous)
    (fun y => (d.mem_Icc hs.le y).1)
  intro y
  exact Real.rpow_le_rpow (d.mem_Icc hs.le y).1 (hqM hs.le y)
    (zero_le_one.trans p.hγ)

/-- An eventual population floor gives the corresponding frozen resolver
floor on every positive restarted slice. -/
theorem WholeLineChiPosCanonicalRestartData.frozenElliptic_ge_of_ge
    {p : CMParams} {u₀ : WholeLineBUC} {t₀ G ell : ℝ}
    (d : WholeLineChiPosCanonicalRestartData p u₀ t₀ G)
    (hG : 0 ≤ G) (hell : 0 ≤ ell)
    (hqell : ∀ ⦃s : ℝ⦄, 0 ≤ s → ∀ x, ell ≤ d.q s x)
    {s x : ℝ} (hs : 0 < s) :
    ell ^ p.γ ≤ frozenElliptic p (d.q s) x := by
  apply frozenElliptic_ge_of_rpow_ge p
    (M := G ^ p.γ) (c := ell ^ p.γ)
    (Real.rpow_nonneg hG p.γ) (Real.rpow_nonneg hell p.γ)
    ((d.slice_contDiff_two hs).continuous)
    (fun y => (d.mem_Icc hs.le y).1)
  · intro y
    exact Real.rpow_le_rpow (d.mem_Icc hs.le y).1
      (d.mem_Icc hs.le y).2 (zero_le_one.trans p.hγ)
  · intro y
    exact Real.rpow_le_rpow hell (hqell hs.le y)
      (zero_le_one.trans p.hγ)

section ResolverBoundAxiomAudit

#print axioms
  WholeLineChiPosCanonicalRestartData.frozenElliptic_le_of_le
#print axioms
  WholeLineChiPosCanonicalRestartData.frozenElliptic_ge_of_ge

end ResolverBoundAxiomAudit

/-! ## Forward restart comparisons -/

/-- Forward-time wrapper around the coupled whole-line floor comparison. -/
theorem WholeLineChiPosCanonicalRestartData.ge_of_coupled_subsolution
    {p : CMParams} {u₀ : WholeLineBUC} {t₀ G Dup : ℝ}
    (d : WholeLineChiPosCanonicalRestartData p u₀ t₀ G)
    (hchi : 0 < p.χ) (hG : 0 ≤ G) {b : ℝ → ℝ}
    (hcontb : Continuous b)
    (hbrange : ∀ s, 0 ≤ s → b s ∈ Set.Icc (0 : ℝ) G)
    (hinit : ∀ x, b 0 ≤ d.q 0 x)
    (htimeb : ∀ ⦃s : ℝ⦄, 0 < s → HasDerivAt b (deriv b s) s)
    (hresolver : ∀ ⦃s x : ℝ⦄, 0 < s →
      frozenElliptic p (d.q s) x ≤ Dup)
    (hpdeb : ∀ ⦃s : ℝ⦄, 0 < s →
      deriv b s + p.χ * (b s) ^ p.m * (Dup - (b s) ^ p.γ) ≤
        reactionFun p.α (b s)) :
    ∀ s, 0 ≤ s → ∀ x, b s ≤ d.q s x := by
  intro s hs x
  let T : ℝ := s + 1
  have hT : 0 < T := by dsimp [T]; linarith
  have hcomp := wholeLine_ge_of_coupled_resolver_reaction_subsolution
    p hchi hT hG d.continuous hcontb
    (fun t ht y => d.mem_Icc ht.1 y)
    (fun t ht => hbrange t ht.1)
    hinit
    (fun _t _y ht => d.time_hasDerivAt ht.1)
    (fun _t _y ht => d.space_hasDerivAt ht.1)
    (fun _t _y ht => d.space_deriv_hasDerivAt ht.1)
    (fun _t ht => htimeb ht.1)
    (fun _t _y ht => by simpa using d.expanded_pde ht.1)
    (fun _t _y ht => hresolver ht.1)
    (fun _t ht => hpdeb ht.1)
  exact hcomp s ⟨hs, by dsimp [T]; linarith⟩ x

/-- Forward-time wrapper around the item-0 weighted resolver floor
comparison, used for the crude pre-burn-in decay floor. -/
theorem WholeLineChiPosCanonicalRestartData.ge_of_weighted_subsolution
    {p : CMParams} {u₀ : WholeLineBUC} {t₀ G Dup : ℝ}
    (d : WholeLineChiPosCanonicalRestartData p u₀ t₀ G)
    (hchi : 0 < p.χ) (hG : 0 ≤ G) {b : ℝ → ℝ}
    (hcontb : Continuous b)
    (hbrange : ∀ s, 0 ≤ s → b s ∈ Set.Icc (0 : ℝ) G)
    (hinit : ∀ x, b 0 ≤ d.q 0 x)
    (htimeb : ∀ ⦃s : ℝ⦄, 0 < s → HasDerivAt b (deriv b s) s)
    (hresolver : ∀ ⦃s x : ℝ⦄, 0 < s →
      frozenElliptic p (d.q s) x ≤ Dup)
    (hpdeb : ∀ ⦃s : ℝ⦄, 0 < s →
      deriv b s + p.χ * (b s) ^ p.m * Dup ≤ reactionFun p.α (b s)) :
    ∀ s, 0 ≤ s → ∀ x, b s ≤ d.q s x := by
  intro s hs x
  let T : ℝ := s + 1
  have hT : 0 < T := by dsimp [T]; linarith
  have hcomp := wholeLine_ge_of_weighted_resolver_reaction_subsolution
    p hchi hT hG d.continuous hcontb
    (fun t ht y => d.mem_Icc ht.1 y)
    (fun t ht => hbrange t ht.1)
    hinit
    (fun _t _y ht => d.time_hasDerivAt ht.1)
    (fun _t _y ht => d.space_hasDerivAt ht.1)
    (fun _t _y ht => d.space_deriv_hasDerivAt ht.1)
    (fun _t ht => htimeb ht.1)
    (fun _t _y ht => by simpa using d.expanded_pde ht.1)
    (fun _t _y ht => hresolver ht.1)
    (fun _t ht => hpdeb ht.1)
  exact hcomp s ⟨hs, by dsimp [T]; linarith⟩ x

/-- Forward-time wrapper around the coupled whole-line ceiling comparison. -/
theorem WholeLineChiPosCanonicalRestartData.le_of_weighted_supersolution
    {p : CMParams} {u₀ : WholeLineBUC} {t₀ G Dlo : ℝ}
    (d : WholeLineChiPosCanonicalRestartData p u₀ t₀ G)
    (hchi : 0 < p.χ) (hG : 0 ≤ G) {a : ℝ → ℝ}
    (hconta : Continuous a)
    (harange : ∀ s, 0 ≤ s → a s ∈ Set.Icc (0 : ℝ) G)
    (hinit : ∀ x, d.q 0 x ≤ a 0)
    (htimea : ∀ ⦃s : ℝ⦄, 0 < s → HasDerivAt a (deriv a s) s)
    (hresolver : ∀ ⦃s x : ℝ⦄, 0 < s →
      Dlo ≤ frozenElliptic p (d.q s) x)
    (hpdea : ∀ ⦃s : ℝ⦄, 0 < s →
      reactionFun p.α (a s) +
          p.χ * (a s) ^ p.m * ((a s) ^ p.γ - Dlo) ≤ deriv a s) :
    ∀ s, 0 ≤ s → ∀ x, d.q s x ≤ a s := by
  intro s hs x
  let T : ℝ := s + 1
  have hT : 0 < T := by dsimp [T]; linarith
  have hcomp := wholeLine_le_of_weighted_resolver_reaction_supersolution
    p hchi hT hG d.continuous hconta
    (fun t ht y => d.mem_Icc ht.1 y)
    (fun t ht => harange t ht.1)
    hinit
    (fun _t _y ht => d.time_hasDerivAt ht.1)
    (fun _t _y ht => d.space_hasDerivAt ht.1)
    (fun _t _y ht => d.space_deriv_hasDerivAt ht.1)
    (fun _t ht => htimea ht.1)
    (fun _t _y ht => by simpa using d.expanded_pde ht.1)
    (fun _t _y ht => hresolver ht.1)
    (fun _t ht => hpdea ht.1)
  exact hcomp s ⟨hs, by dsimp [T]; linarith⟩ x

section ForwardComparisonAxiomAudit

#print axioms
  WholeLineChiPosCanonicalRestartData.ge_of_coupled_subsolution
#print axioms
  WholeLineChiPosCanonicalRestartData.ge_of_weighted_subsolution
#print axioms
  WholeLineChiPosCanonicalRestartData.le_of_weighted_supersolution

end ForwardComparisonAxiomAudit

/-! ## One coupled PDE rectangle round -/

/-- A strict-margin eventual rectangle admits the next coupled rectangle.
The floor is improved first; the ceiling comparison is then restarted only
after that new floor is uniform, so its resolver lower bound is available on
the whole forward slab. -/
theorem exists_next_chiPosWholeLineRectangle
    (p : CMParams) (hchi : 0 < p.χ) (hchi_lt : p.χ < 1)
    (hcritical : p.α = p.m + p.γ - 1)
    (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hleft : StrictlyPositiveAtLeft u₀.1)
    {G δ : ℝ} (hG : 0 ≤ G)
    (hglobal : ∀ ⦃t : ℝ⦄, 0 ≤ t → ∀ x,
      wholeLineCauchyGlobalU p u₀ t x ≤ G)
    (hδ : 0 < δ)
    (old : ChiPosWholeLineRectangle p (wholeLineCauchyGlobalU p u₀)) :
    Nonempty {new : ChiPosWholeLineRectangle p
        (wholeLineCauchyGlobalU p u₀) //
      ChiPosWholeLineRectangleStep p δ old new} := by
  obtain ⟨targets⟩ := exists_chiPos_rectangle_round_targets
    hcritical hchi.le hchi_lt old.ell_pos old.ell_lt_one old.one_lt_M
      old.floor_margin old.ceiling_margin hδ
  let H : ℝ := max G old.M
  have hH : 0 ≤ H := hG.trans (le_max_left G old.M)
  have hMH : old.M ≤ H := le_max_right G old.M
  have hglobalH : ∀ ⦃t : ℝ⦄, 0 ≤ t → ∀ x,
      wholeLineCauchyGlobalU p u₀ t x ≤ H := by
    intro t ht x
    exact (hglobal ht x).trans (le_max_left G old.M)
  let t₀ : ℝ := max old.start 1
  have ht₀ : 0 < t₀ :=
    zero_lt_one.trans_le (le_max_right old.start 1)
  have hold_t₀ : old.start ≤ t₀ := le_max_left old.start 1
  let floorData := wholeLineCauchyGlobal_positiveRestartData
    p hregime u₀ hu₀ hleft ht₀ hglobalH
  have hfloorDataM : ∀ ⦃s : ℝ⦄, 0 ≤ s → ∀ x,
      floorData.q s x ≤ old.M := by
    intro s hs x
    rw [floorData.eq_global hs x]
    exact (old.bounds (t₀ + s) (by
      exact hold_t₀.trans (le_add_of_nonneg_right hs)) x).2
  let floorRate : ℝ :=
    chiPosRectangleFloorRate p old.M old.ell targets.Lraw
  let floorBarrier : ℝ → ℝ :=
    chiZeroKPPFloor old.ell targets.Lraw floorRate
  have hfloorRate : 0 < floorRate := by
    exact chiPosRectangleFloorRate_pos old.ell_pos
      (targets.ell_lt_L.trans targets.L_lt_Lraw)
      targets.floor_raw_margin
  have hfloorInit : ∀ x, floorBarrier 0 ≤ floorData.q 0 x := by
    intro x
    rw [show floorBarrier 0 = old.ell by simp [floorBarrier]]
    rw [floorData.eq_global (s := 0) le_rfl x]
    simpa using (old.bounds t₀ hold_t₀ x).1
  have hfloorRange : ∀ s, 0 ≤ s →
      floorBarrier s ∈ Set.Icc (0 : ℝ) H := by
    intro s hs
    have hge : old.ell ≤ floorBarrier s := by
      exact chiZeroKPPFloor_ge_start
        (targets.ell_lt_L.trans targets.L_lt_Lraw).le hfloorRate.le hs
    have hle : floorBarrier s ≤ targets.Lraw := by
      exact chiZeroKPPFloor_le_target
        (targets.ell_lt_L.trans targets.L_lt_Lraw).le
    exact ⟨old.ell_pos.le.trans hge,
      hle.trans (targets.Lraw_le_one.trans
        (old.one_lt_M.le.trans hMH))⟩
  have hfloorAll : ∀ s, 0 ≤ s → ∀ x,
      floorBarrier s ≤ floorData.q s x := by
    apply floorData.ge_of_coupled_subsolution hchi hH
    · rw [continuous_iff_continuousAt]
      intro s
      exact (chiZeroKPPFloor_hasDerivAt
        old.ell targets.Lraw floorRate s).continuousAt
    · exact hfloorRange
    · exact hfloorInit
    · intro s hs
      exact (chiZeroKPPFloor_hasDerivAt
        old.ell targets.Lraw floorRate s).differentiableAt.hasDerivAt
    · intro s x hs
      exact floorData.frozenElliptic_le_of_le
        (M := old.M) (s := s) (x := x)
        (zero_le_one.trans old.one_lt_M.le) hfloorDataM hs
    · intro s hs
      exact targets.floor_weighted_subsolution hcritical hchi.le hchi_lt
        old.ell_pos old.one_lt_M.le hs.le
  have hfloorTend : Tendsto floorBarrier atTop (nhds targets.Lraw) := by
    exact chiZeroKPPFloor_tendsto_target hfloorRate
  have hfloorNhd : Set.Ioi targets.L ∈ nhds targets.Lraw :=
    Ioi_mem_nhds targets.L_lt_Lraw
  obtain ⟨Sfloor, hSfloor⟩ := eventually_atTop.1
    (hfloorTend.eventually hfloorNhd)
  let sfloor : ℝ := max Sfloor 0
  have hsfloor : 0 ≤ sfloor := le_max_right Sfloor 0
  have hS_sfloor : Sfloor ≤ sfloor := le_max_left Sfloor 0
  let t₁ : ℝ := t₀ + sfloor
  have ht₁ : 0 < t₁ := by dsimp [t₁]; linarith
  let ceilingData := wholeLineCauchyGlobal_positiveRestartData
    p hregime u₀ hu₀ hleft ht₁ hglobalH
  have hceilingDataM : ∀ ⦃s : ℝ⦄, 0 ≤ s → ∀ x,
      ceilingData.q s x ≤ old.M := by
    intro s hs x
    rw [ceilingData.eq_global hs x]
    exact (old.bounds (t₁ + s) (by
      have : old.start ≤ t₁ := by
        dsimp [t₁]
        exact hold_t₀.trans (le_add_of_nonneg_right hsfloor)
      exact this.trans (le_add_of_nonneg_right hs)) x).2
  have hceilingDataL : ∀ ⦃s : ℝ⦄, 0 ≤ s → ∀ x,
      targets.L ≤ ceilingData.q s x := by
    intro s hs x
    have helapsed : 0 ≤ sfloor + s := add_nonneg hsfloor hs
    have hbarrier : targets.L ≤ floorBarrier (sfloor + s) := by
      exact (hSfloor (sfloor + s) (hS_sfloor.trans
        (le_add_of_nonneg_right hs))).le
    have hcomp := hfloorAll (sfloor + s) helapsed x
    calc
      targets.L ≤ floorBarrier (sfloor + s) := hbarrier
      _ ≤ floorData.q (sfloor + s) x := hcomp
      _ = ceilingData.q s x := by
        rw [floorData.eq_global helapsed x, ceilingData.eq_global hs x]
        apply congrArg (fun time : ℝ =>
          wholeLineCauchyGlobalU p u₀ time x)
        dsimp [t₁]
        ring
  let ceilingRate : ℝ :=
    chiPosRectangleCeilingRate p targets.L targets.Araw old.M
  let ceilingBarrier : ℝ → ℝ :=
    chiPosTargetCeiling targets.Araw old.M ceilingRate
  have hceilingRate : 0 < ceilingRate := by
    exact chiPosRectangleCeilingRate_pos
      (zero_lt_one.trans_le targets.one_le_Araw)
      (targets.Araw_lt_A.trans targets.A_lt_M)
      targets.ceiling_raw_margin
  have hceilingInit : ∀ x, ceilingData.q 0 x ≤ ceilingBarrier 0 := by
    intro x
    rw [show ceilingBarrier 0 = old.M by simp [ceilingBarrier]]
    exact hceilingDataM le_rfl x
  have hceilingRange : ∀ s, 0 ≤ s →
      ceilingBarrier s ∈ Set.Icc (0 : ℝ) H := by
    intro s hs
    have hge : targets.Araw ≤ ceilingBarrier s :=
      chiPosTargetCeiling_ge_target
        (targets.Araw_lt_A.trans targets.A_lt_M).le
    have hle : ceilingBarrier s ≤ old.M :=
      chiPosTargetCeiling_le_start
        (targets.Araw_lt_A.trans targets.A_lt_M).le hceilingRate.le hs
    exact ⟨(zero_le_one.trans targets.one_le_Araw).trans hge,
      hle.trans hMH⟩
  have hceilingAll : ∀ s, 0 ≤ s → ∀ x,
      ceilingData.q s x ≤ ceilingBarrier s := by
    apply ceilingData.le_of_weighted_supersolution
      (Dlo := targets.L ^ p.γ) (a := ceilingBarrier) hchi hH
    · rw [continuous_iff_continuousAt]
      intro s
      exact (chiPosTargetCeiling_hasDerivAt
        targets.Araw old.M ceilingRate s).continuousAt
    · exact hceilingRange
    · exact hceilingInit
    · intro s hs
      exact (chiPosTargetCeiling_hasDerivAt
        targets.Araw old.M ceilingRate s).differentiableAt.hasDerivAt
    · intro s x hs
      exact ceilingData.frozenElliptic_ge_of_ge
        (ell := targets.L) (s := s) (x := x) hH
        (old.ell_pos.trans targets.ell_lt_L).le hceilingDataL hs
    · intro s hs
      exact targets.ceiling_weighted_supersolution hcritical hchi.le
        hchi_lt old.ell_pos hs.le
  have hceilingTend : Tendsto ceilingBarrier atTop (nhds targets.Araw) := by
    exact chiPosTargetCeiling_tendsto_target hceilingRate
  have hceilingNhd : Set.Iio targets.A ∈ nhds targets.Araw :=
    Iio_mem_nhds targets.Araw_lt_A
  obtain ⟨Sceiling, hSceiling⟩ := eventually_atTop.1
    (hceilingTend.eventually hceilingNhd)
  let sceiling : ℝ := max Sceiling 0
  have hsceiling : 0 ≤ sceiling := le_max_right Sceiling 0
  have hS_sceiling : Sceiling ≤ sceiling := le_max_left Sceiling 0
  let new : ChiPosWholeLineRectangle p
      (wholeLineCauchyGlobalU p u₀) :=
    { ell := targets.L
      M := targets.A
      start := t₁ + sceiling
      ell_pos := old.ell_pos.trans targets.ell_lt_L
      ell_lt_one := targets.L_lt_Lraw.trans_le targets.Lraw_le_one
      one_lt_M := targets.one_le_Araw.trans_lt targets.Araw_lt_A
      floor_margin := targets.next_floor_margin
      ceiling_margin := targets.next_ceiling_margin
      bounds := by
        intro t ht x
        let s : ℝ := t - t₁
        have hs : 0 ≤ s := by
          dsimp [s]
          linarith
        have hsc : sceiling ≤ s := by
          dsimp [s]
          linarith
        have hlower := hceilingDataL hs x
        have hupperComp := hceilingAll s hs x
        have hupperBarrier : ceilingBarrier s ≤ targets.A :=
          (hSceiling s (hS_sceiling.trans hsc)).le
        have heq : t₁ + s = t := by dsimp [s]; ring
        rw [ceilingData.eq_global hs x, heq] at hlower hupperComp
        exact ⟨hlower, hupperComp.trans hupperBarrier⟩ }
  refine ⟨⟨new, ?_⟩⟩
  exact
    { ell_le := targets.ell_lt_L.le
      M_le := targets.A_lt_M.le
      floor_budget := targets.floor_delta
      ceiling_budget := targets.ceiling_delta }

section RectangleRoundAxiomAudit

#print axioms exists_next_chiPosWholeLineRectangle

end RectangleRoundAxiomAudit

/-! ## Initial rectangle -/

/-- Uniform positivity survives the finite ceiling burn-in, after which the
weighted floor barrier produces the first strict-margin rectangle. -/
theorem exists_initial_chiPosWholeLineRectangle
    (p : CMParams) (hchi : 0 < p.χ) (hchi_half : p.χ < 1 / 2)
    (hcritical : p.α = p.m + p.γ - 1)
    (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hpositive : UniformlyPositive u₀.1) :
    Nonempty (ChiPosWholeLineRectangle p
      (wholeLineCauchyGlobalU p u₀)) := by
  have hchi_lt : p.χ < 1 := by linarith
  obtain ⟨M, ellRaw, hMChi, hM1, _hmMargin,
      hellRaw, hellRaw1, hfloorRawExpanded⟩ :=
    exists_chiPos_rectangle_seed p hchi hchi_half hcritical
  have hfloorRaw : 0 < chiPosFloorGap p M ellRaw := by
    simpa [chiPosFloorGap, mul_assoc] using hfloorRawExpanded
  let G : ℝ := max (MChi p) ‖u₀‖
  have hMChiPos : 0 < MChi p := MChi_pos_of_chi_lt_one p hchi_lt
  have hG : 0 ≤ G := hMChiPos.le.trans (le_max_left (MChi p) ‖u₀‖)
  have hG1 : 1 ≤ G :=
    (one_lt_MChi_of_chi_pos_lt_one p hchi hchi_lt).le.trans
      (le_max_left (MChi p) ‖u₀‖)
  have hglobal : ∀ ⦃t : ℝ⦄, 0 ≤ t → ∀ x,
      wholeLineCauchyGlobalU p u₀ t x ≤ G := by
    intro t ht x
    exact wholeLineCauchyGlobal_le_max_of_chi_pos
      p hchi hchi_lt hcritical hregime u₀ hu₀ ht x
  have hleft : StrictlyPositiveAtLeft u₀.1 :=
    hpositive.strictlyPositiveAtLeft
  rcases hpositive with ⟨d₀, hd₀, hd₀le⟩
  let C₀ : ℝ := d₀ / 2
  have hC₀ : 0 < C₀ := by dsimp [C₀]; linarith
  have hd₀norm : d₀ ≤ ‖u₀‖ := by
    exact (hd₀le 0).trans (WholeLineBUC.apply_le_norm u₀ 0)
  have hC₀G : C₀ ≤ G := by
    calc
      C₀ = d₀ / 2 := rfl
      _ ≤ d₀ := by linarith
      _ ≤ ‖u₀‖ := hd₀norm
      _ ≤ G := le_max_right (MChi p) ‖u₀‖
  obtain ⟨tau, htau, htrace⟩ :=
    wholeLineCauchyGlobal_hasUniformInitialTrace p u₀ C₀ hC₀
  let t₀ : ℝ := tau / 2
  have ht₀ : 0 < t₀ := by dsimp [t₀]; linarith
  have ht₀tau : t₀ < tau := by dsimp [t₀]; linarith
  have hUfloor₀ : ∀ x, C₀ ≤ wholeLineCauchyGlobalU p u₀ t₀ x := by
    intro x
    have hclose := htrace t₀ x ht₀.le ht₀tau
    have hlower := neg_lt_of_abs_lt hclose
    have hdatum := hd₀le x
    dsimp [C₀] at hlower ⊢
    linarith
  let decayData := wholeLineCauchyGlobal_positiveRestartData
    p hregime u₀ hu₀ hleft ht₀ hglobal
  let decayRate : ℝ := chiPosDecayFloorRate p G
  let decayBarrier : ℝ → ℝ := chiPosDecayFloor C₀ decayRate
  have hdecayRate : 0 < decayRate :=
    chiPosDecayFloorRate_pos hchi.le hG
  have hdecayRange : ∀ s, 0 ≤ s →
      decayBarrier s ∈ Set.Icc (0 : ℝ) G := by
    intro s hs
    exact ⟨(chiPosDecayFloor_pos hC₀).le,
      (chiPosDecayFloor_le_start hC₀.le hdecayRate.le hs).trans hC₀G⟩
  have hdecayAll : ∀ s, 0 ≤ s → ∀ x,
      decayBarrier s ≤ decayData.q s x := by
    apply decayData.ge_of_weighted_subsolution
      (Dup := G ^ p.γ) (b := decayBarrier) hchi hG
    · rw [continuous_iff_continuousAt]
      intro s
      exact (chiPosDecayFloor_hasDerivAt C₀ decayRate s).continuousAt
    · exact hdecayRange
    · intro x
      rw [show decayBarrier 0 = C₀ by simp [decayBarrier]]
      rw [decayData.eq_global (s := 0) le_rfl x]
      simpa using hUfloor₀ x
    · intro s hs
      exact (chiPosDecayFloor_hasDerivAt
        C₀ decayRate s).differentiableAt.hasDerivAt
    · intro s x hs
      exact decayData.frozenElliptic_le_of_le
        (M := G) (s := s) (x := x) hG
        (fun _r hr y => (decayData.mem_Icc hr y).2) hs
    · intro s hs
      exact chiPosDecayFloor_weighted_subsolution hchi.le hG hC₀ hC₀G hs.le
  have hlimsup := wholeLineCauchyGlobal_uniformLimsupLe_MChi_of_chi_pos
    p hchi hchi_lt hcritical hregime u₀ hu₀
  have hMgap : 0 < M - MChi p := sub_pos.mpr hMChi
  obtain ⟨Tupper, hTupper⟩ := eventually_atTop.1 (hlimsup _ hMgap)
  let t₁ : ℝ := max Tupper t₀
  have ht₁ : 0 < t₁ := ht₀.trans_le (le_max_right Tupper t₀)
  have hTupper_t₁ : Tupper ≤ t₁ := le_max_left Tupper t₀
  have ht₀_t₁ : t₀ ≤ t₁ := le_max_right Tupper t₀
  let s₁ : ℝ := t₁ - t₀
  have hs₁ : 0 ≤ s₁ := sub_nonneg.mpr ht₀_t₁
  have hdecayAt := hdecayAll s₁ hs₁ 0
  have hdecayAtPhysical : decayBarrier s₁ ≤
      wholeLineCauchyGlobalU p u₀ t₁ 0 := by
    rw [decayData.eq_global hs₁ 0] at hdecayAt
    have heq : t₀ + s₁ = t₁ := by dsimp [s₁]; ring
    simpa [heq] using hdecayAt
  let C₁ : ℝ := min (decayBarrier s₁ / 2) (ellRaw / 2)
  have hdecayS₁ : 0 < decayBarrier s₁ := chiPosDecayFloor_pos hC₀
  have hC₁ : 0 < C₁ := by
    dsimp [C₁]
    exact lt_min (half_pos hdecayS₁) (half_pos hellRaw)
  have hC₁_decay : C₁ ≤ decayBarrier s₁ := by
    have hhalf : C₁ ≤ decayBarrier s₁ / 2 := by
      dsimp [C₁]
      exact min_le_left _ _
    linarith
  have hC₁ell : C₁ < ellRaw := by
    have hhalf : C₁ ≤ ellRaw / 2 := by
      dsimp [C₁]
      exact min_le_right _ _
    linarith
  let H : ℝ := max G M
  have hH : 0 ≤ H := hG.trans (le_max_left G M)
  have hMH : M ≤ H := le_max_right G M
  have hglobalH : ∀ ⦃t : ℝ⦄, 0 ≤ t → ∀ x,
      wholeLineCauchyGlobalU p u₀ t x ≤ H := by
    intro t ht x
    exact (hglobal ht x).trans (le_max_left G M)
  let seedData := wholeLineCauchyGlobal_positiveRestartData
    p hregime u₀ hu₀ hleft ht₁ hglobalH
  have hseedDataM : ∀ ⦃s : ℝ⦄, 0 ≤ s → ∀ x,
      seedData.q s x ≤ M := by
    intro s hs x
    rw [seedData.eq_global hs x]
    have ht : Tupper ≤ t₁ + s :=
      hTupper_t₁.trans (le_add_of_nonneg_right hs)
    have := hTupper (t₁ + s) ht x
    simpa using this
  let seedRate : ℝ := chiPosRectangleFloorRate p M C₁ ellRaw
  let seedBarrier : ℝ → ℝ := chiZeroKPPFloor C₁ ellRaw seedRate
  have hseedRate : 0 < seedRate :=
    chiPosRectangleFloorRate_pos hC₁ hC₁ell hfloorRaw
  have hseedRange : ∀ s, 0 ≤ s →
      seedBarrier s ∈ Set.Icc (0 : ℝ) H := by
    intro s hs
    have hge : C₁ ≤ seedBarrier s :=
      chiZeroKPPFloor_ge_start hC₁ell.le hseedRate.le hs
    have hle : seedBarrier s ≤ ellRaw :=
      chiZeroKPPFloor_le_target hC₁ell.le
    exact ⟨hC₁.le.trans hge,
      hle.trans (hellRaw1.le.trans (hM1.le.trans hMH))⟩
  have hseedAll : ∀ s, 0 ≤ s → ∀ x,
      seedBarrier s ≤ seedData.q s x := by
    apply seedData.ge_of_coupled_subsolution
      (Dup := M ^ p.γ) (b := seedBarrier) hchi hH
    · rw [continuous_iff_continuousAt]
      intro s
      exact (chiZeroKPPFloor_hasDerivAt C₁ ellRaw seedRate s).continuousAt
    · exact hseedRange
    · intro x
      rw [show seedBarrier 0 = C₁ by simp [seedBarrier]]
      rw [seedData.eq_global (s := 0) le_rfl x]
      have hdecayAtX := hdecayAll s₁ hs₁ x
      rw [decayData.eq_global hs₁ x] at hdecayAtX
      have heq : t₀ + s₁ = t₁ := by dsimp [s₁]; ring
      rw [heq] at hdecayAtX
      simpa only [add_zero] using hC₁_decay.trans hdecayAtX
    · intro s hs
      exact (chiZeroKPPFloor_hasDerivAt
        C₁ ellRaw seedRate s).differentiableAt.hasDerivAt
    · intro s x hs
      exact seedData.frozenElliptic_le_of_le
        (M := M) (s := s) (x := x)
        (zero_le_one.trans hM1.le) hseedDataM hs
    · intro s hs
      exact chiZeroKPPFloor_weighted_subsolution hcritical hchi.le hchi_lt
        hC₁ hC₁ell hellRaw1.le hM1.le hfloorRaw hs.le
  have hseedTend : Tendsto seedBarrier atTop (nhds ellRaw) :=
    chiZeroKPPFloor_tendsto_target hseedRate
  let ell : ℝ := ellRaw / 2
  have hell : 0 < ell := by dsimp [ell]; positivity
  have hellRawLt : ell < ellRaw := by dsimp [ell]; linarith
  have hseedNhd : Set.Ioi ell ∈ nhds ellRaw := Ioi_mem_nhds hellRawLt
  obtain ⟨Sseed, hSseed⟩ := eventually_atTop.1
    (hseedTend.eventually hseedNhd)
  let sseed : ℝ := max Sseed 0
  have hsseed : 0 ≤ sseed := le_max_right Sseed 0
  have hS_sseed : Sseed ≤ sseed := le_max_left Sseed 0
  have hfloorMargin : 0 < chiPosFloorGap p M ell := by
    have hanti := chiPosFloorGap_strictAntiOn_Ioi
      hcritical hchi.le hchi_lt (zero_le_one.trans hM1.le)
      (show ell ∈ Set.Ioi (0 : ℝ) from hell)
      (show ellRaw ∈ Set.Ioi (0 : ℝ) from hellRaw) hellRawLt
    exact hfloorRaw.trans hanti
  have hceilingMargin : 0 < chiPosCeilingGap p ell M := by
    simpa [chiPosCeilingGap, mul_assoc] using
      chiPos_rectangle_ceiling_margin_pos_of_MChi_lt
        p hchi hchi_lt hcritical hMChi hell.le
  refine ⟨
    { ell := ell
      M := M
      start := t₁ + sseed
      ell_pos := hell
      ell_lt_one := hellRawLt.trans hellRaw1
      one_lt_M := hM1
      floor_margin := hfloorMargin
      ceiling_margin := hceilingMargin
      bounds := ?_ }⟩
  intro t ht x
  let s : ℝ := t - t₁
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hss : sseed ≤ s := by dsimp [s]; linarith
  have hlowerBarrier : ell ≤ seedBarrier s :=
    (hSseed s (hS_sseed.trans hss)).le
  have hlowerComp := hseedAll s hs x
  have heq : t₁ + s = t := by dsimp [s]; ring
  rw [seedData.eq_global hs x, heq] at hlowerComp
  have hupper : wholeLineCauchyGlobalU p u₀ t x ≤ M := by
    have htUpper : Tupper ≤ t := by
      exact hTupper_t₁.trans (by linarith)
    have := hTupper t htUpper x
    simpa using this
  exact ⟨hlowerBarrier.trans hlowerComp, hupper⟩

section InitialRectangleAxiomAudit

#print axioms exists_initial_chiPosWholeLineRectangle

end InitialRectangleAxiomAudit

/-! ## Critical positive-sensitivity convergence -/

/-- In the critical branch `α = m + γ - 1`, the whole-line canonical
solution from uniformly positive BUC data converges uniformly to one whenever
`0 < χ < 1/2` and the canonical ceiling regime is available. -/
theorem
    wholeLineCauchyGlobal_uniformConvergesToConstant_one_of_chi_pos_half
    (p : CMParams) (hchi : 0 < p.χ) (hchi_half : p.χ < 1 / 2)
    (hcritical : p.α = p.m + p.γ - 1)
    (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hpositive : UniformlyPositive u₀.1) :
    UniformConvergesToConstant (wholeLineCauchyGlobalU p u₀) 1 := by
  have hchi_lt : p.χ < 1 := by linarith
  obtain ⟨seed⟩ := exists_initial_chiPosWholeLineRectangle
    p hchi hchi_half hcritical hregime u₀ hu₀ hpositive
  let G : ℝ := max (MChi p) ‖u₀‖
  have hG : 0 ≤ G :=
    (MChi_pos_of_chi_lt_one p hchi_lt).le.trans
      (le_max_left (MChi p) ‖u₀‖)
  have hglobal : ∀ ⦃t : ℝ⦄, 0 ≤ t → ∀ x,
      wholeLineCauchyGlobalU p u₀ t x ≤ G := by
    intro t ht x
    exact wholeLineCauchyGlobal_le_max_of_chi_pos
      p hchi hchi_lt hcritical hregime u₀ hu₀ ht x
  apply uniformConvergesToConstant_one_of_rectangle_successors
    p hchi.le hchi_half hcritical seed
  intro δ hδ old
  exact exists_next_chiPosWholeLineRectangle
    p hchi hchi_lt hcritical hregime u₀ hu₀
      hpositive.strictlyPositiveAtLeft hG hglobal hδ old

section CriticalConvergenceAxiomAudit

#print axioms
  wholeLineCauchyGlobal_uniformConvergesToConstant_one_of_chi_pos_half

end CriticalConvergenceAxiomAudit

end ShenWork.Paper1
