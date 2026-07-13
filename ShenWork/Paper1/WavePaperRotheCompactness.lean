/-
  Adaptive compactness for the whole-line paper Rothe orbit.

  The inner index is selected separately in each orbit, after the outer
  approximate fixed profile has been chosen.  This avoids the false inference
  from pointwise-in-profile orbit convergence to a family-uniform Rothe tail.
  The only analytic input left below is the whole-line Green-step closed graph.
-/
import ShenWork.Paper1.WaveRotheConcrete
import ShenWork.Paper1.WaveG1Bridge
import ShenWork.Paper1.WaveUniformModulusTrap

open Filter Topology Set

noncomputable section

namespace ShenWork.Paper1

/-- The old/new successor gap vanishes locally uniformly along one selected
family of Rothe indices.  This is deliberately an along-family statement, not
a tail uniform over the whole wave trap. -/
def PaperRotheSuccessorGapAlong
    (Z : ℕ → ℕ → ℝ → ℝ) (ks : ℕ → ℕ) : Prop :=
  ∀ R > 0, ∀ ε > 0,
    ∀ᶠ n in atTop, ∀ x ∈ Set.Icc (-R) R,
      |Z n (ks n + 1) x - Z n (ks n) x| < ε

/-- Quantitative growing-window diagonal used to obtain the successor gap.
Both adjacent iterates are close to their own orbit limit on `[-(n+1),n+1]`.
-/
def PaperRotheAdaptiveDiagonal
    (Z : ℕ → ℕ → ℝ → ℝ) (L : ℕ → ℝ → ℝ)
    (ks : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) x, x ∈ Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) →
    |Z n (ks n) x - L n x| < 1 / (4 * ((n : ℝ) + 1)) ∧
      |Z n (ks n + 1) x - L n x| < 1 / (4 * ((n : ℝ) + 1))

/-- Per-orbit local-uniform convergence supplies an adaptive growing-window
index.  The extra `max n` makes the selected indices tend to infinity. -/
theorem exists_adaptiveMovingIndex
    {Z : ℕ → ℕ → ℝ → ℝ} {L : ℕ → ℝ → ℝ}
    (hLU : ∀ n, LocallyUniformConverges (Z n) (L n)) :
    ∃ ks : ℕ → ℕ,
      Tendsto ks atTop atTop ∧ PaperRotheAdaptiveDiagonal Z L ks := by
  have hex : ∀ n : ℕ, ∃ K : ℕ,
      ∀ k : ℕ, K ≤ k → ∀ x ∈ Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1),
        |Z n k x - L n x| < 1 / (4 * ((n : ℝ) + 1)) := by
    intro n
    have hR : 0 < (n : ℝ) + 1 := by positivity
    have hε : 0 < 1 / (4 * ((n : ℝ) + 1)) := by positivity
    exact eventually_atTop.1
      (hLU n ((n : ℝ) + 1) hR (1 / (4 * ((n : ℝ) + 1))) hε)
  let K : ℕ → ℕ := fun n => Classical.choose (hex n)
  let ks : ℕ → ℕ := fun n => max n (K n)
  have hK : ∀ (n k : ℕ), K n ≤ k →
      ∀ x ∈ Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1),
        |Z n k x - L n x| < 1 / (4 * ((n : ℝ) + 1)) := by
    intro n
    exact Classical.choose_spec (hex n)
  have hks_ge : ∀ n, n ≤ ks n := fun n => le_max_left _ _
  have hks_top : Tendsto ks atTop atTop := by
    refine tendsto_atTop.2 fun N => ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    exact le_trans hn (hks_ge n)
  refine ⟨ks, hks_top, ?_⟩
  intro n x hx
  have hbase : K n ≤ ks n := le_max_right _ _
  exact
    ⟨hK n (ks n) hbase x hx,
      hK n (ks n + 1) (le_trans hbase (Nat.le_succ _)) x hx⟩

/-- The adaptive growing-window diagonal gives the exact successor-gap
property needed by the moving-index stationary passage. -/
theorem PaperRotheAdaptiveDiagonal.successorGapAlong
    {Z : ℕ → ℕ → ℝ → ℝ} {L : ℕ → ℝ → ℝ} {ks : ℕ → ℕ}
    (hdiag : PaperRotheAdaptiveDiagonal Z L ks) :
    PaperRotheSuccessorGapAlong Z ks := by
  intro R hR ε hε
  have hwindow : ∀ᶠ n : ℕ in atTop, R ≤ (n : ℝ) + 1 := by
    have htop : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
      apply tendsto_atTop_add_const_right
      exact tendsto_natCast_atTop_atTop
    exact htop.eventually (eventually_ge_atTop R)
  have hδ0 : Tendsto
      (fun n : ℕ => 1 / (4 * ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have htop : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
      apply tendsto_atTop_add_const_right
      exact tendsto_natCast_atTop_atTop
    have htop4 : Tendsto (fun n : ℕ => 4 * ((n : ℝ) + 1)) atTop atTop := by
      exact (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 4)).2 htop
    simpa [one_div] using htop4.inv_tendsto_atTop.const_mul (1 : ℝ)
  have hsmall : ∀ᶠ n : ℕ in atTop,
      1 / (4 * ((n : ℝ) + 1)) < ε / 2 := by
    have hε2 : 0 < ε / 2 := by linarith
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hδ0) (ε / 2) hε2
    filter_upwards [eventually_ge_atTop N] with n hn
    have hδnn : 0 ≤ 1 / (4 * ((n : ℝ) + 1)) := by positivity
    have h := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hδnn] at h
    exact h
  filter_upwards [hwindow, hsmall] with n hnR hnsmall
  intro x hx
  have hxgrow : x ∈ Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) := by
    constructor <;> nlinarith [hx.1, hx.2]
  obtain ⟨hold, hnew⟩ := hdiag n x hxgrow
  have htri :
      |Z n (ks n + 1) x - Z n (ks n) x| ≤
        |Z n (ks n + 1) x - L n x| + |Z n (ks n) x - L n x| := by
    calc
      |Z n (ks n + 1) x - Z n (ks n) x|
          ≤ |Z n (ks n + 1) x - L n x| +
              |L n x - Z n (ks n) x| := abs_sub_le _ _ _
      _ = |Z n (ks n + 1) x - L n x| +
              |Z n (ks n) x - L n x| := by rw [abs_sub_comm (L n x)]
  linarith

/-- The growing-window diagonal tracks any locally-uniform limit of the named
per-orbit limits with both its old and successor iterates. -/
theorem PaperRotheAdaptiveDiagonal.commonLimit
    {Z : ℕ → ℕ → ℝ → ℝ} {L : ℕ → ℝ → ℝ} {ks : ℕ → ℕ}
    {U : ℝ → ℝ}
    (hdiag : PaperRotheAdaptiveDiagonal Z L ks)
    (hL : LocallyUniformConverges L U) :
    LocallyUniformConverges (fun n => Z n (ks n)) U ∧
      LocallyUniformConverges (fun n => Z n (ks n + 1)) U := by
  have hδ0 : Tendsto
      (fun n : ℕ => 1 / (4 * ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have htop : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
      apply tendsto_atTop_add_const_right
      exact tendsto_natCast_atTop_atTop
    have htop4 : Tendsto (fun n : ℕ => 4 * ((n : ℝ) + 1)) atTop atTop := by
      exact (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 4)).2 htop
    simpa [one_div] using htop4.inv_tendsto_atTop.const_mul (1 : ℝ)
  constructor
  · intro R hR ε hε
    have hwindow : ∀ᶠ n : ℕ in atTop, R ≤ (n : ℝ) + 1 := by
      have htop : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
        apply tendsto_atTop_add_const_right
        exact tendsto_natCast_atTop_atTop
      exact htop.eventually (eventually_ge_atTop R)
    have hsmall : ∀ᶠ n : ℕ in atTop,
        1 / (4 * ((n : ℝ) + 1)) < ε / 2 := by
      have hε2 : 0 < ε / 2 := by linarith
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hδ0) (ε / 2) hε2
      filter_upwards [eventually_ge_atTop N] with n hn
      have hδnn : 0 ≤ 1 / (4 * ((n : ℝ) + 1)) := by positivity
      have h := hN n hn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hδnn] at h
      exact h
    have hε2 : 0 < ε / 2 := by linarith
    filter_upwards [hwindow, hsmall, hL R hR (ε / 2) hε2] with n hnR hnsmall hnL
    intro x hx
    have hxgrow : x ∈ Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) := by
      constructor <;> nlinarith [hx.1, hx.2]
    obtain ⟨hold, hnew⟩ := hdiag n x hxgrow
    have hclose : |Z n (ks n) x - L n x| < ε / 2 :=
      lt_trans hold hnsmall
    calc
      |Z n (ks n) x - U x|
          ≤ |Z n (ks n) x - L n x| + |L n x - U x| := abs_sub_le _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add hclose (hnL x hx)
      _ = ε := by ring
  · intro R hR ε hε
    have hwindow : ∀ᶠ n : ℕ in atTop, R ≤ (n : ℝ) + 1 := by
      have htop : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
        apply tendsto_atTop_add_const_right
        exact tendsto_natCast_atTop_atTop
      exact htop.eventually (eventually_ge_atTop R)
    have hsmall : ∀ᶠ n : ℕ in atTop,
        1 / (4 * ((n : ℝ) + 1)) < ε / 2 := by
      have hε2 : 0 < ε / 2 := by linarith
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hδ0) (ε / 2) hε2
      filter_upwards [eventually_ge_atTop N] with n hn
      have hδnn : 0 ≤ 1 / (4 * ((n : ℝ) + 1)) := by positivity
      have h := hN n hn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hδnn] at h
      exact h
    have hε2 : 0 < ε / 2 := by linarith
    filter_upwards [hwindow, hsmall, hL R hR (ε / 2) hε2] with n hnR hnsmall hnL
    intro x hx
    have hxgrow : x ∈ Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) := by
      constructor <;> nlinarith [hx.1, hx.2]
    obtain ⟨hold, hnew⟩ := hdiag n x hxgrow
    have hclose : |Z n (ks n + 1) x - L n x| < ε / 2 :=
      lt_trans hnew hnsmall
    calc
      |Z n (ks n + 1) x - U x|
          ≤ |Z n (ks n + 1) x - L n x| + |L n x - U x| := abs_sub_le _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add hclose (hnL x hx)
      _ = ε := by ring

/-- Adaptive selection in the final form used by the outer compactness
argument: the selected old and successor iterates share the compact-open limit
of the named orbit limits. -/
theorem exists_adaptiveMovingIndex_commonLimit
    {Z : ℕ → ℕ → ℝ → ℝ} {L : ℕ → ℝ → ℝ} {U : ℝ → ℝ}
    (hLU : ∀ n, LocallyUniformConverges (Z n) (L n))
    (hL : LocallyUniformConverges L U) :
    ∃ ks : ℕ → ℕ,
      Tendsto ks atTop atTop ∧
        LocallyUniformConverges (fun n => Z n (ks n)) U ∧
        LocallyUniformConverges (fun n => Z n (ks n + 1)) U ∧
        PaperRotheSuccessorGapAlong Z ks := by
  obtain ⟨ks, hks, hdiag⟩ := exists_adaptiveMovingIndex hLU
  obtain ⟨hold, hnew⟩ := hdiag.commonLimit hL
  exact ⟨ks, hks, hold, hnew, hdiag.successorGapAlong⟩

/-- Whole-line source-tail representation retained by the adaptive Green
closed graph. -/
def PaperGreenSourceTailData (c lam : ℝ) (U : ℝ → ℝ) : Prop :=
  ∃ R : ℝ → ℝ, ∃ B L : ℝ,
    Continuous R ∧ (∀ y, |R y| ≤ B) ∧ Tendsto R atBot (nhds L) ∧
      U = fun x => greenConv c lam R x

/-- The one analytic Paper 1 frontier after adaptive selection.  It is the
sequential closed graph for an actual whole-line Green step: if the frozen
profiles, old iterates, and successor iterates have the same compact-open
limit, then the limiting profile satisfies the self implicit step.  The
differentiability conclusion is the `C¹_loc` part supplied by Green compactness
and is exactly what converts paper stationarity to frozen stationarity. -/
def PaperGreenRotheAdaptiveStepClosedGraphOnTrap
    (p : CMParams) (c lam M κ : ℝ)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ) : Prop :=
  ∀ (seq : ℕ → ℝ → ℝ) (U : ℝ → ℝ) (ks : ℕ → ℕ),
    (∀ n, InMonotoneWaveTrapSet κ M (seq n)) →
      InMonotoneWaveTrapSet κ M U →
      LocallyUniformConverges seq U →
      Tendsto ks atTop atTop →
      LocallyUniformConverges (fun n => rotheSeq (seq n) (ks n)) U →
      LocallyUniformConverges (fun n => rotheSeq (seq n) (ks n + 1)) U →
        (∀ x, paperImplicitStepOp p c (1 / lam) U U x = U x) ∧
          Differentiable ℝ U ∧ Differentiable ℝ (deriv U) ∧
          PaperGreenSourceTailData c lam U

namespace PaperGreenRotheAdaptiveStepClosedGraphOnTrap

variable {p : CMParams} {c lam M κ : ℝ}
  {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}

/-- Convert the Green closed-graph self step to the frozen stationary
equation.  Frozen-drift differentiability is already proved for every trapped
profile, and the power differentiability follows from the `C¹_loc` output. -/
theorem frozenStationary
    (hgraph : PaperGreenRotheAdaptiveStepClosedGraphOnTrap
      p c lam M κ rotheSeq)
    (hlam : 0 < lam)
    {seq : ℕ → ℝ → ℝ} {U : ℝ → ℝ} {ks : ℕ → ℕ}
    (hseq : ∀ n, InMonotoneWaveTrapSet κ M (seq n))
    (hU : InMonotoneWaveTrapSet κ M U)
    (houter : LocallyUniformConverges seq U)
    (hks : Tendsto ks atTop atTop)
    (hold : LocallyUniformConverges
      (fun n => rotheSeq (seq n) (ks n)) U)
    (hnew : LocallyUniformConverges
      (fun n => rotheSeq (seq n) (ks n + 1)) U) :
    ∀ x, frozenWaveOperator p c U U x = 0 := by
  obtain ⟨hstep, hUdiff, _hUderivDiff, _hsourceTail⟩ :=
    hgraph seq U ks hseq hU houter hks hold hnew
  exact frozenWaveOperator_eq_zero_of_paperImplicitStepOp_self
    p c lam U hlam hU.trap.cunif_bdd hU.nonneg hUdiff
    (fun x => frozenElliptic_deriv_differentiableAt p
      hU.trap.cunif_bdd hU.nonneg x)
    (fun x => (hUdiff x).rpow_const (Or.inr p.hm)) hstep

end PaperGreenRotheAdaptiveStepClosedGraphOnTrap

/-- Outer finite-cube approximation plus range compactness and the adaptive
inner diagonal produce a stationary lower-pinned profile.  No continuity of
the single-valued map `u ↦ rotheLimit (rotheSeq u)` and no family-uniform Rothe
tail are used. -/
theorem paperLowerPinned_adaptiveStationary_of_cubeApproxData
    (p : CMParams) (c lam M κ : ℝ) (φ : ℝ → ℝ)
    (hM : 0 ≤ M) (hlam : 0 < lam)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ)
    (hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperRotheOrbitData p c lam M κ rotheSeq u)
    (hlower : RotheOrbitLowerBound κ M φ rotheSeq)
    (Happrox : ProjectedCubeApproxData
      (InLowerPinnedMonotoneTrap κ M φ)
      (fun u => rotheLimit (rotheSeq u)))
    (hgraph : PaperGreenRotheAdaptiveStepClosedGraphOnTrap
      p c lam M κ rotheSeq) :
    ∃ U, InLowerPinnedMonotoneTrap κ M φ U ∧
      (∀ x, frozenWaveOperator p c U U x = 0) ∧
      Differentiable ℝ U ∧ Differentiable ℝ (deriv U) ∧
      PaperGreenSourceTailData c lam U := by
  let Tmap : (ℝ → ℝ) → ℝ → ℝ := fun u => rotheLimit (rotheSeq u)
  obtain ⟨seq, hseq, happrox⟩ :=
    localUniformApproxFixedPointSequence_of_cubeApproxData
      Happrox.toLocalUniformCubeApproxData
  have hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap :=
    paperTmap_compactRange_of_uniformModulus p c lam M κ hM rotheSeq hdata
  obtain ⟨sub, hsub, U, hUbare, hTconv⟩ :=
    hcompact seq (fun n => (hseq n).bare)
  have hTlower : ∀ u, InLowerPinnedMonotoneTrap κ M φ u →
      ∀ x, φ x ≤ Tmap u x :=
    Tmap_lowerInvariant_of_rotheOrbitLowerBound hlower
  have hUlower : ∀ x, φ x ≤ U x := by
    intro x
    exact le_of_tendsto_of_tendsto tendsto_const_nhds (hTconv.tendsto_at x)
      (Eventually.of_forall fun n => hTlower (seq (sub n)) (hseq (sub n)) x)
  have hU : InLowerPinnedMonotoneTrap κ M φ U := ⟨hUbare, hUlower⟩
  have houter : LocallyUniformConverges (fun n => seq (sub n)) U := by
    intro R hR ε hε
    have hε2 : 0 < ε / 2 := by linarith
    have happ : ∀ᶠ n in atTop, ∀ x ∈ Set.Icc (-R) R,
        |Tmap (seq (sub n)) x - seq (sub n) x| < ε / 2 :=
      hsub.tendsto_atTop.eventually (happrox R hR (ε / 2) hε2)
    filter_upwards [happ, hTconv R hR (ε / 2) hε2] with n hn happT
    intro x hx
    have htri : |seq (sub n) x - U x| ≤
        |seq (sub n) x - Tmap (seq (sub n)) x| +
          |Tmap (seq (sub n)) x - U x| := abs_sub_le _ _ _
    have hleft : |seq (sub n) x - Tmap (seq (sub n)) x| < ε / 2 := by
      simpa [abs_sub_comm] using hn x hx
    linarith [htri, hleft, happT x hx]
  let Z : ℕ → ℕ → ℝ → ℝ := fun n => rotheSeq (seq (sub n))
  let L : ℕ → ℝ → ℝ := fun n => Tmap (seq (sub n))
  have horbit : ∀ n, LocallyUniformConverges (Z n) (L n) := by
    intro n
    simpa [Z, L, Tmap] using
      (hdata (seq (sub n)) (hseq (sub n)).bare).locallyUniform hM
  obtain ⟨ks, hks, hold, hnew, _hgap⟩ :=
    exists_adaptiveMovingIndex_commonLimit horbit (by simpa [L] using hTconv)
  obtain ⟨hstep, hUdiff, hUderivDiff, hsourceTail⟩ :=
    hgraph (fun n => seq (sub n)) U ks
      (fun n => (hseq (sub n)).bare) hUbare houter hks
      (by simpa [Z] using hold) (by simpa [Z] using hnew)
  have hstat : ∀ x, frozenWaveOperator p c U U x = 0 :=
    frozenWaveOperator_eq_zero_of_paperImplicitStepOp_self
      p c lam U hlam hUbare.trap.cunif_bdd hUbare.nonneg hUdiff
      (fun x => frozenElliptic_deriv_differentiableAt p
        hUbare.trap.cunif_bdd hUbare.nonneg x)
      (fun x => (hUdiff x).rpow_const (Or.inr p.hm)) hstep
  exact ⟨U, hU, hstat, hUdiff, hUderivDiff, hsourceTail⟩

section AxiomAudit

#print axioms exists_adaptiveMovingIndex
#print axioms PaperRotheAdaptiveDiagonal.successorGapAlong
#print axioms PaperRotheAdaptiveDiagonal.commonLimit
#print axioms exists_adaptiveMovingIndex_commonLimit
#print axioms PaperGreenRotheAdaptiveStepClosedGraphOnTrap.frozenStationary
#print axioms paperLowerPinned_adaptiveStationary_of_cubeApproxData

end AxiomAudit

end ShenWork.Paper1
