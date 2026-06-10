/-
  ShenWork/Paper2/IntervalDomainHresProducer.lean

  **Producer for the iterate-side residual bundle `PicardIterateResidualData`
  (the `Hres` bundle) for the cone-constructed datum `D`, plus the
  horizon-shrink machinery.**

  `IntervalDomainThm11ChiZeroResidual.lean` defines `PicardIterateResidualData`
  and turns each χ₀ = 0 Provider obligation into a clean implication from it.
  This file *assembles* such a bundle for the canonical Picard-limit datum
  produced by `coneGradientMildSolutionData_exists`.

  ## What is genuinely discharged here vs. threaded

  * **`hLcont_lim`** — DISCHARGED.  The limit slice continuity is read off
    `D.hcont` (the cone datum's `HasContinuousSlices`) after rewriting through
    `hDu`, then pushed through `logisticLifted = logisticSourceFun (lift)` on
    `[0,1]` (`logisticLifted_continuousOn_of_continuous`).  No hypothesis needed
    beyond the cone datum itself.

  * **`hLcont_iter`** — DISCHARGED from the iterate slice-continuity bundle
    `hcont_iter` (the cone construction's internal `hcont_iterates`, which `D`
    does not expose).  Same logistic-composition continuity route.

  * **`Wdata`, `hsliceTC`, `hFacts`/`hFacts_T`** — THREADED as honest residual
    hypotheses.  Each is a TRUE statement about the canonical Picard limit,
    satisfiable from the cone construction's internal iterate data, but not
    recoverable from a bare `GradientMildSolutionData`:
      - `Wdata` (per-window K2 data) bottoms out in `PicardRegularityStepData`
        (C² slices), `UniformWiring` (G1/G2 closure — owned by another agent),
        the M1 restart cosine identity, and the cone iterate positivity;
      - `hsliceTC` is the single genuinely-open analytic field (interior
        mild-slice time continuity + `s = 0⁺` initial approach);
      - `hFacts` (the standalone `PicardConvFacts` ball/geometric package) is now
        SATISFIABLE from the cone construction's internal ball/geometric iterate
        data — it carries NO false-in-cone `hmapsTo_nn`/`hmapsTo_pos`.  Exposing it
        from the cone lemma is the follow-up `_with_data` extension (same additive
        pattern as `hcont_iterates`, commit 088d520).  This REPLACES the former
        wrong-shaped `hME : MildExistenceData` field, which was NOT
        cone-constructible.

  ## Horizon-shrink machinery

  `GradientMildSolutionData.restrict` shrinks the horizon `D.T ↦ T'`.  The
  Picard iterates `picardIter p u₀ n t x` are HORIZON-FREE (the only
  horizon-dependence in `picardLimit` is the gate `if 0 < t ∧ t ≤ T`), so
  `picardLimit_restrict_eq` shows the limit is unchanged on the smaller window:
  `picardLimit p u₀ T' t x = picardLimit p u₀ D.T t x` for `0 < t ≤ T'`.  Hence
  `hDu` is PRESERVED under restriction, which is what the consumer needs to
  shrink the horizon to satisfy the GateCondition while keeping `hDu`.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalDomainThm11ChiZeroResidual

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard
  (GradientMildSolutionData MildExistenceData HasContinuousSlices picardIter picardLimit)
open ShenWork.IntervalMildPicardRegularity (logisticSourceFun)
open ShenWork.IntervalPicardLimitBddHcontP (lift_continuousOn_Icc)
open ShenWork.IntervalPicardWeightedC2Bootstrap (IterateWindowC2Data)
open ShenWork.IntervalPicardLimitCoeffConv (PicardConvFacts)

noncomputable section

namespace ShenWork.Paper2.HresProducer

/-! ## 1. Logistic-source continuity from slice continuity.

The `[0,1]`-continuity of a logistic source `logisticLifted p w` follows from
plain continuity of the spatial profile `w`, via the agreement
`logisticLifted = logisticSourceFun (lift w)` on `[0,1]` and the product/rpow
continuity of `logisticSourceFun`.  This is the exact route used in
`logisticLifted_patchedSlice_continuousOn`, abstracted to any continuous slice. -/

/-- `[0,1]`-continuity of the lifted logistic source of any continuous profile. -/
theorem logisticLifted_continuousOn_of_continuous
    (p : CM2Params) {w : intervalDomainPoint → ℝ} (hw : Continuous w) :
    ContinuousOn (logisticLifted p w) (Set.Icc (0 : ℝ) 1) := by
  have hcontLift : ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) :=
    lift_continuousOn_Icc hw
  have hcontSrc : ContinuousOn
      (logisticSourceFun p.a p.b p.α (intervalDomainLift w)) (Set.Icc (0 : ℝ) 1) := by
    unfold logisticSourceFun
    apply ContinuousOn.mul hcontLift
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.mul continuousOn_const
    exact ContinuousOn.rpow_const hcontLift (fun x _ => Or.inr p.hα.le)
  exact hcontSrc.congr
    (fun x hx =>
      ShenWork.IntervalMildPicardRegularity.logisticLifted_eq_logisticSourceFun_on_Icc
        p w hx)

/-! ## 2. Horizon-shrink machinery.

The Picard iterates `picardIter p u₀ n t x` carry no horizon parameter; the only
horizon-dependence in `picardLimit` is the membership gate `if 0 < t ∧ t ≤ T`.
Consequently the limit is horizon-stable on any sub-window. -/

/-- **Horizon stability of the Picard limit.**  For `0 < t ≤ T' ≤ T`, the limit
read at the smaller horizon `T'` coincides with the limit at `T`, because the
iterates are horizon-free and both gates open. -/
theorem picardLimit_restrict_eq (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {T' T : ℝ} (hT'T : T' ≤ T) {t : ℝ} (ht : 0 < t) (htT' : t ≤ T')
    (x : intervalDomainPoint) :
    picardLimit p u₀ T' t x = picardLimit p u₀ T t x := by
  unfold picardLimit
  rw [if_pos ⟨ht, htT'⟩, if_pos ⟨ht, le_trans htT' hT'T⟩]

/-- **Horizon shrink of a packaged mild datum.**  Given `0 < T' ≤ D.T`, restrict
`D` to the horizon `T'`, keeping the SAME trajectory `D.u`.  All side conditions
restrict trivially (a fact required only on `(0,T']` follows from its `(0,D.T]`
form since `t ≤ T' ⟹ t ≤ D.T`). -/
def restrictHorizon {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) {T' : ℝ} (hT'_pos : 0 < T') (hT'_le : T' ≤ D.T) :
    GradientMildSolutionData p u₀ where
  T := T'
  hT := hT'_pos
  M := D.M
  hM := D.hM
  u := D.u
  hmild := fun t ht htT' x => D.hmild t ht (le_trans htT' hT'_le) x
  hbound := fun t ht htT' x => D.hbound t ht (le_trans htT' hT'_le) x
  hnonneg := fun t ht htT' x => D.hnonneg t ht (le_trans htT' hT'_le) x
  hpos := fun t ht htT' x => D.hpos t ht (le_trans htT' hT'_le) x
  hcont := fun t ht htT' => D.hcont t ht (le_trans htT' hT'_le)
  hmeas := D.hmeas

@[simp] theorem restrictHorizon_T {p : CM2Params}
    {u₀ : intervalDomainPoint → ℝ} (D : GradientMildSolutionData p u₀)
    {T' : ℝ} (hT'_pos : 0 < T') (hT'_le : T' ≤ D.T) :
    (restrictHorizon D hT'_pos hT'_le).T = T' := rfl

@[simp] theorem restrictHorizon_u {p : CM2Params}
    {u₀ : intervalDomainPoint → ℝ} (D : GradientMildSolutionData p u₀)
    {T' : ℝ} (hT'_pos : 0 < T') (hT'_le : T' ≤ D.T) :
    (restrictHorizon D hT'_pos hT'_le).u = D.u := rfl

/-- **`hDu` survives horizon shrink only ON the smaller window** (the genuine,
true compatibility).  For every `t ∈ (0,T']` and `x`,
`(restrictHorizon D …).u t x = picardLimit p u₀ T' t x`.

IMPORTANT — the function-level identity `(restrictHorizon D …).u = picardLimit p u₀ T'`
is **FALSE in general**: `(restrictHorizon D …).u = D.u = picardLimit p u₀ D.T` is
generally NONZERO on `(T', D.T]`, whereas `picardLimit p u₀ T'` is identically
`0` there (its gate `t ≤ T'` fails).  So the consumer CANNOT obtain the
function-level `hDu` for the restricted datum by `funext`; it must consume the
canonical-limit identity ONLY on the evaluation window `(0,T']`, where the
iterates are horizon-free and both gates open (`picardLimit_restrict_eq`).  See
the file header / final report's horizon-shrink finding. -/
theorem restrict_picardLimit_eqOn {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) {T' : ℝ} (hT'_pos : 0 < T') (hT'_le : T' ≤ D.T)
    (hDu : D.u = picardLimit p u₀ D.T) :
    ∀ t, 0 < t → t ≤ T' → ∀ x,
      (restrictHorizon D hT'_pos hT'_le).u t x = picardLimit p u₀ T' t x := by
  intro t ht htT' x
  rw [restrictHorizon_u, hDu]
  exact (picardLimit_restrict_eq p u₀ hT'_le ht htT' x).symm

/-! ## 3. The producer.

The bundle for the cone-constructed datum.  Discharges `hLcont_iter`/`hLcont_lim`
from slice continuity; threads `hFacts`, `Wdata`, `hsliceTC` as honest residual
hypotheses (see the file header for satisfiability). -/

/-- **`PicardIterateResidualData` for the cone-constructed datum.**

`hDu` ties `D` to the canonical Picard limit.  The iterate slice-continuity
bundle `hcont_iter` is the cone construction's internal `hcont_iterates` (not
exposed by `D`); from it `hLcont_iter` is discharged, while `hLcont_lim` comes
from `D.hcont` + `hDu`.  The remaining fields (`hFacts`/`hFacts_T`, `Wdata`,
`hsliceTC`) are threaded as honest residual hypotheses. -/
def picardIterateResidualData_of_cone
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (hDu : D.u = picardLimit p u₀ D.T)
    -- iterate slice continuity (cone-internal `hcont_iterates`; not in `D`)
    (hcont_iter : ∀ n : ℕ, HasContinuousSlices D.T (picardIter p u₀ n))
    -- the internal ball/geometric facts package with matching horizon.
    -- Satisfiable from the cone's internal iterate ball/geometric data (no
    -- false-in-cone `hmapsTo_nn`/`hmapsTo_pos`); exposing it from the cone lemma is
    -- the follow-up `_with_data` extension (same pattern as `hcont_iterates`, 088d520).
    (hFacts : PicardConvFacts p u₀) (hFacts_T : hFacts.T = D.T)
    -- per-window K2 data (bottoms out in C² step data + UniformWiring + M1)
    (Wdata : ∀ a', 0 < a' → IterateWindowC2Data p u₀ a' D.T)
    -- the single genuinely-open analytic field
    (hsliceTC : ∀ s₀ ∈ Set.Icc (0 : ℝ) D.T, ∀ ε > 0, ∃ δ > 0,
      ∀ s ∈ Set.Icc (0 : ℝ) D.T, |s - s₀| < δ →
        ∀ y, |ShenWork.IntervalPicardLimitBddHcontP.patchedSlice u₀ D.u s y
              - ShenWork.IntervalPicardLimitBddHcontP.patchedSlice u₀ D.u s₀ y| < ε) :
    Thm11ChiZeroResidual.PicardIterateResidualData p u₀ D where
  hFacts := hFacts
  hFacts_T := hFacts_T
  hLcont_iter := by
    intro n σ hσ hσT
    exact logisticLifted_continuousOn_of_continuous p (hcont_iter n σ hσ hσT)
  hLcont_lim := by
    intro σ hσ hσT
    -- D.u σ = picardLimit p u₀ D.T σ, and D.u has continuous slices
    have hcontσ : Continuous (D.u σ) := D.hcont σ hσ hσT
    have hpl : Continuous (picardLimit p u₀ D.T σ) := by
      have : picardLimit p u₀ D.T σ = D.u σ := by rw [hDu]
      rw [this]; exact hcontσ
    exact logisticLifted_continuousOn_of_continuous p hpl
  Wdata := Wdata
  hsliceTC := hsliceTC

end ShenWork.Paper2.HresProducer
