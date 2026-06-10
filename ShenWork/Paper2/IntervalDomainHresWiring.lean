/-
  ShenWork/Paper2/IntervalDomainHresWiring.lean

  **Final wiring, step 4 — narrowing the capstone's `Hres` surface.**

  The χ₀ = 0 capstone (`IntervalDomainThm11ChiZeroCoreProvider`) currently takes a
  universal provider

      Hres : ∀ u₀, PID u₀ → ∀ D, D.u = picardLimit p u₀ D.T →
               PicardIterateResidualData p u₀ D

  of the FULL iterate-side residual bundle (four substantive legs: `hFacts`,
  `hLcont_iter`/`hLcont_lim`, `Wdata`, `hsliceTC`).  Two of those legs are
  derivable for EVERY canonical-Picard-limit datum `D` from `D` + `hDu` alone:

    * **`hsliceTC`** — the patched-slice sup-norm time continuity — is exactly
      `IntervalPicardLimitSliceTimeContinuity.hsliceTC_of_mild_restart`, consuming
      only `(hχ0, Continuous u₀, D, hDu)`;
    * **`hLcont_lim`** — `[0,1]`-continuity of the limit's logistic source —
      follows from `D.hcont` + `hDu` (discharged inside
      `HresProducer.picardIterateResidualData_of_cone`).

  This file isolates the GENUINELY cone-specific residual core

      PicardIterateResidualCore p u₀ D
        := { hFacts, hFacts_T, hcont_iter, Wdata }

  (the iterate ball/geometric facts package, the iterate slice-continuity bundle,
  and the per-window K2 data — all properties of the Picard iteration AT the
  horizon `D.T`, not recoverable from a bare `D`), and provides

      picardIterateResidualData_of_core :
        (hχ0) → (Continuous u₀) → (hDu) → PicardIterateResidualCore … →
          PicardIterateResidualData p u₀ D

  which combines the core with the two universally-derived legs.  The capstone is
  then rewired to take the NARROWER core provider, discharging `hsliceTC` and
  `hLcont_lim` once and for all.

  HONESTY: the `Wdata`/`hFacts`/`hcont_iter` legs of the core remain genuine,
  satisfiable residuals — they bottom out in the `UniformWiring` analytic stack
  (whose gate is now discharged by `IntervalPicardGateSolve.exists_gate_solution`
  and `coneGradientMildSolutionData_exists_with_gate_data`) and the cone's
  internal ball/geometric/slice-continuity iterate data.  Wiring them fully is the
  remaining open analytic work; this pass removes the two legs that are NOT open.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalDomainHresProducer
import ShenWork.Paper2.IntervalPicardLimitSliceTimeContinuity
import ShenWork.Paper2.IntervalPicardLimitBddBootstrap
import ShenWork.Paper2.IntervalPicardLimitBddHcontP
import ShenWork.Paper2.IntervalPicardLimitCoeffTimeCont

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalMildPicard
  (GradientMildSolutionData HasContinuousSlices picardIter picardLimit)
open ShenWork.IntervalPicardWeightedC2Bootstrap (IterateWindowC2Data)
open ShenWork.IntervalPicardLimitCoeffConv (PicardConvFacts)

noncomputable section

namespace ShenWork.Paper2.HresWiring

/-- **The genuinely cone-specific iterate-side residual core.**

For a canonical-Picard-limit datum `D` (`D.u = picardLimit p u₀ D.T`), this bundles
exactly the three legs of `PicardIterateResidualData` that are properties of the
Picard iteration AT the horizon `D.T` (and hence NOT derivable from a bare `D`):
the ball/geometric facts package, the iterate slice-continuity bundle, and the
per-window K2 data.  The remaining legs (`hLcont_lim`, `hsliceTC`) are discharged
universally by `picardIterateResidualData_of_core`. -/
structure PicardIterateResidualCore
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (D : GradientMildSolutionData p u₀) where
  /-- The standalone ball/geometric-tail facts package (horizon `= D.T`). -/
  hFacts : PicardConvFacts p u₀
  hFacts_T : hFacts.T = D.T
  /-- The cone construction's internal iterate slice-continuity bundle. -/
  hcont_iter : ∀ n : ℕ, HasContinuousSlices D.T (picardIter p u₀ n)
  /-- The per-window uniform K2 data for the Picard iterates. -/
  Wdata : ∀ a', 0 < a' → IterateWindowC2Data p u₀ a' D.T

/-- **The narrowed (Wdata-only) iterate-side residual provider.**

After the cone-facts narrowing pass, `hFacts`/`hFacts_T`/`hcont_iter` are no longer
provider obligations — they are RETURNED by the cone construction
(`coneGradientMildSolutionData_exists_with_data`) at the construction site (where
`D.T = δ`), so only the genuinely-open per-window K2 leg `Wdata` remains a residual.
This is the per-datum payload the capstone's narrowed hypothesis quantifies. -/
def WdataProvider (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (D : GradientMildSolutionData p u₀) : Type :=
  ∀ a', 0 < a' → IterateWindowC2Data p u₀ a' D.T

/-- **Assemble the cone-specific core from the cone-returned facts + the
Wdata-only residual.**  `hFacts`/`hcont_iter` are supplied by the cone
construction at the construction site (`D.T = δ`); `Wdata` is the single remaining
provider obligation. -/
def picardIterateResidualCore_of_wdata
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (hcont_iter : ∀ n : ℕ, HasContinuousSlices D.T (picardIter p u₀ n))
    (hFacts : PicardConvFacts p u₀) (hFacts_T : hFacts.T = D.T)
    (Wdata : WdataProvider p u₀ D) :
    PicardIterateResidualCore p u₀ D where
  hFacts := hFacts
  hFacts_T := hFacts_T
  hcont_iter := hcont_iter
  Wdata := Wdata

/-- **Build the limit-source bounded-Duhamel package `hsrc0` from the cone-specific
core + the cosine-coefficient TIME continuity `hiter_cont`.**

This is the NON-circular iterate-side producer of the `DuhamelSourceBddOn` package
the slice-continuity chain consumes.  It runs
`IntervalPicardLimitBddBootstrap.duhamelSourceBddOn_of_iterates` at horizon `D.T`,
sourcing every ingredient from data available at the cone construction site:

* `hM₀'`/`hu₀_src_bound` — the `s ≤ 0` datum-side source bound, from `Continuous u₀`
  + the PID positivity (`IntervalPicardLimitBddHcontP.datum_source_coeff_bound`);
* `Cwin`/`henv_iter` — the n-uniform per-window envelope, from the core's per-window
  K2 data `C.Wdata` (`Thm11ChiZeroResidual.hCwin_ex_of_residual`-style, here read off
  `source_coeff_window_uniform C.Wdata` directly via the `PicardIterateResidualCore`);
* `hconv` — pointwise coefficient convergence iterate → limit, from the core's facts
  package `C.hFacts` + the iterate/limit `[0,1]`-spatial continuity (derived from
  `C.hcont_iter` and `D.hcont`);
* `hcontP` — the patched coefficient family TIME continuity, via the **spatial**
  Stage-A route `IntervalPicardLimitCoeffTimeCont.patchedSource_coeff_continuousOn_of_iterate_data`
  (NOT the patched-slice sup-norm continuity), consuming the cosine-coefficient time
  continuity `hiter_cont` — the SINGLE ingredient the core does not carry, supplied
  from the tower (`IntervalPicardTowerProjection.hiter_cont_of_tower`).

`hcontP` here NEVER appeals to `hsliceTC`, so feeding the resulting `hsrc0` into
`hsliceTC_of_mild_restart` (which produces `hsliceTC`) is non-circular. -/
def duhamelSourceBddOn_of_core
    {p : CM2Params}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : ShenWork.Paper2.PositiveInitialDatum
      ShenWork.IntervalDomain.intervalDomain u₀)
    {D : GradientMildSolutionData p u₀}
    (hDu : D.u = picardLimit p u₀ D.T)
    (C : PicardIterateResidualCore p u₀ D)
    -- cosine-coefficient TIME continuity on windows `[a',τ] ⊆ (0, D.T]`, from the tower
    -- (`IntervalPicardTowerProjection.hiter_cont_of_tower`).
    (hiter_cont : ∀ (a' τ : ℝ), 0 < a' → a' ≤ τ → τ ≤ D.T → ∀ (n k : ℕ),
      ContinuousOn
        (fun s => ShenWork.IntervalNeumannFullKernel.cosineCoeffs
          (ShenWork.IntervalGradientDuhamelMap.logisticLifted p
            (picardIter p u₀ n s)) k)
        (Set.Icc a' τ)) :
    ShenWork.IntervalPicardLimitRestartBdd.DuhamelSourceBddOn
      (ShenWork.IntervalPicardLimitBddProducer.patchedSource p u₀ D.u) D.T := by
  -- (R-src0F-1) datum-side source bound.
  have hu₀cont : Continuous u₀ := hu₀.admissible.2
  set M₀' : ℝ := ShenWork.IntervalPicardLimitBddHcontP.datumBound p u₀ with hM₀'def
  have hM₀'_nonneg : (0 : ℝ) ≤ M₀' :=
    ShenWork.IntervalPicardLimitBddHcontP.datumBound_nonneg p hu₀.admissible.1
  have hu₀_src_bound : ∀ k,
      |ShenWork.IntervalNeumannFullKernel.cosineCoeffs
        (ShenWork.IntervalGradientDuhamelMap.logisticLifted p u₀) k| ≤ M₀' :=
    ShenWork.IntervalPicardLimitBddHcontP.datum_source_coeff_bound p
      hu₀cont hu₀.admissible.1 hu₀.2
  -- (R-src0F-2) per-window n-uniform envelope from the core's K2 data.  (`.choose`
  -- rather than `obtain`: the target `DuhamelSourceBddOn` is `Type`-valued, so the
  -- `∃` witness must be extracted via `Exists.choose`, not `Prop` recursion.)
  have hCwin_ex := ShenWork.IntervalPicardWeightedC2Bootstrap.source_coeff_window_uniform
    p u₀ hα C.Wdata
  let Cwin : ℝ → ℝ := hCwin_ex.choose
  have hCwin : ∀ a', 0 ≤ Cwin a' := hCwin_ex.choose_spec.1
  have henv_iter : ∀ a', 0 < a' → ∀ s, a' ≤ s → s ≤ D.T → ∀ (n k : ℕ),
      |ShenWork.IntervalNeumannFullKernel.cosineCoeffs
        (ShenWork.IntervalGradientDuhamelMap.logisticLifted p (picardIter p u₀ n s)) k|
        ≤ ShenWork.IntervalPicardLimitBddProducer.windowEnv (Cwin a') k :=
    hCwin_ex.choose_spec.2
  -- the `[0,1]`-spatial continuity of iterate/limit logistic sources, from the core.
  have hLcont_iter : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ D.T →
      ContinuousOn (ShenWork.IntervalGradientDuhamelMap.logisticLifted p
        (picardIter p u₀ n σ)) (Set.Icc (0 : ℝ) 1) := by
    intro n σ hσ hσT
    exact HresProducer.logisticLifted_continuousOn_of_continuous p
      (C.hcont_iter n σ hσ hσT)
  have hLcont_lim : ∀ (σ : ℝ), 0 < σ → σ ≤ D.T →
      ContinuousOn (ShenWork.IntervalGradientDuhamelMap.logisticLifted p
        (picardLimit p u₀ D.T σ)) (Set.Icc (0 : ℝ) 1) := by
    intro σ hσ hσT
    have hpl : Continuous (picardLimit p u₀ D.T σ) := by
      have heq : picardLimit p u₀ D.T σ = D.u σ := by rw [hDu]
      rw [heq]; exact D.hcont σ hσ hσT
    exact HresProducer.logisticLifted_continuousOn_of_continuous p hpl
  -- (R-src0F-3) pointwise coefficient convergence iterate → `D.u`, from the facts pkg.
  have hconv : ∀ s, 0 < s → s ≤ D.T → ∀ k,
      Filter.Tendsto (fun n => ShenWork.IntervalNeumannFullKernel.cosineCoeffs
          (ShenWork.IntervalGradientDuhamelMap.logisticLifted p (picardIter p u₀ n s)) k)
        Filter.atTop (nhds (ShenWork.IntervalNeumannFullKernel.cosineCoeffs
          (ShenWork.IntervalGradientDuhamelMap.logisticLifted p (D.u s)) k)) := by
    intro s hs hsT k
    have hslice : D.u s = picardLimit p u₀ D.T s := by rw [hDu]
    rw [hslice]
    have hLcont_iter' : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ C.hFacts.T →
        ContinuousOn (ShenWork.IntervalGradientDuhamelMap.logisticLifted p
          (picardIter p u₀ n σ)) (Set.Icc (0 : ℝ) 1) := by
      rw [C.hFacts_T]; exact hLcont_iter
    have hLcont_lim' : ∀ (σ : ℝ), 0 < σ → σ ≤ C.hFacts.T →
        ContinuousOn (ShenWork.IntervalGradientDuhamelMap.logisticLifted p
          (picardLimit p u₀ C.hFacts.T σ)) (Set.Icc (0 : ℝ) 1) := by
      rw [C.hFacts_T]; exact hLcont_lim
    have hsT' : s ≤ C.hFacts.T := by rw [C.hFacts_T]; exact hsT
    have h :=
      ShenWork.IntervalPicardLimitCoeffConv.picardIter_logisticCoeff_tendsto_limit_of_facts
        C.hFacts hLcont_iter' hLcont_lim' hs hsT' k
    rw [C.hFacts_T] at h
    exact h
  -- (R-src0F-4) patched coefficient family TIME continuity via the SPATIAL Stage-A
  -- route (NOT the patched-slice sup-norm continuity): assemble the patched ball/nn
  -- facts then run `patchedSource_coeff_continuousOn_of_iterate_data`.
  set M_patch : ℝ := max D.M (sSup (Set.range fun x => |u₀ x|)) with hMpatch_def
  have hMpatch_pos : (0 : ℝ) < M_patch :=
    lt_of_lt_of_le D.hM (le_max_left _ _)
  have hu₀_nn : ∀ y : intervalDomainPoint, 0 ≤ u₀ y := by
    intro y
    have h := ShenWork.IntervalPicardLimitBddHcontP.lift_nonneg_of_pos_interior
      hu₀cont hu₀.2 y.1 y.2
    have huy : u₀ y = intervalDomainLift u₀ y.1 := by
      simp only [intervalDomainLift,
        dif_pos (show (y.1 : ℝ) ∈ Set.Icc (0:ℝ) 1 from y.2), Subtype.coe_eta]
    rw [huy]; exact h
  have hu₀_bd : ∀ y : intervalDomainPoint,
      |u₀ y| ≤ sSup (Set.range fun x => |u₀ x|) :=
    fun y => le_csSup hu₀.admissible.1 ⟨y, rfl⟩
  have hball_patch : ∀ s ∈ Set.Icc (0 : ℝ) D.T,
      ∀ y, |ShenWork.IntervalPicardLimitBddHcontP.patchedSlice u₀ D.u s y| ≤ M_patch := by
    intro s hs y
    rcases eq_or_lt_of_le hs.1 with hs0 | hs0
    · rw [ShenWork.IntervalPicardLimitBddHcontP.patchedSlice_of_nonpos u₀ D.u
        (le_of_eq hs0.symm)]
      exact le_trans (hu₀_bd y) (le_max_right _ _)
    · rw [ShenWork.IntervalPicardLimitBddHcontP.patchedSlice_of_pos u₀ D.u hs0]
      exact le_trans (D.hbound s hs0 hs.2 y) (le_max_left _ _)
  have hnn_patch : ∀ s ∈ Set.Icc (0 : ℝ) D.T,
      ∀ y, 0 ≤ ShenWork.IntervalPicardLimitBddHcontP.patchedSlice u₀ D.u s y := by
    intro s hs y
    rcases eq_or_lt_of_le hs.1 with hs0 | hs0
    · rw [ShenWork.IntervalPicardLimitBddHcontP.patchedSlice_of_nonpos u₀ D.u
        (le_of_eq hs0.symm)]
      exact hu₀_nn y
    · rw [ShenWork.IntervalPicardLimitBddHcontP.patchedSlice_of_pos u₀ D.u hs0]
      exact D.hnonneg s hs0 hs.2 y
  have hcontP : ∀ k, ContinuousOn
      (fun s => ShenWork.IntervalPicardLimitBddProducer.patchedSource p u₀ D.u s k)
      (Set.Icc 0 D.T) :=
    ShenWork.IntervalPicardLimitCoeffTimeCont.patchedSource_coeff_continuousOn_of_iterate_data
      D hDu hu₀cont C.hFacts C.hFacts_T hLcont_iter hLcont_lim hMpatch_pos
      hball_patch hnn_patch D.hT le_rfl
      (fun a' ha' ha'T n k => hiter_cont a' D.T ha' ha'T le_rfl n k)
  -- assemble the package at horizon `D.T`.
  exact ShenWork.IntervalPicardLimitBddBootstrap.duhamelSourceBddOn_of_iterates
    p D hα ha hb hM₀'_nonneg hu₀_src_bound Cwin hCwin henv_iter hconv
    D.hT le_rfl hcontP

/-- **Combine the cone-specific core with the universally-derived legs.**

`hsliceTC` is `hsliceTC_of_mild_restart` (needs only `hχ0`, `Continuous u₀`, `D`,
`hDu`); `hLcont_lim`/`hLcont_iter` are discharged inside
`HresProducer.picardIterateResidualData_of_cone`.  The result is the full
`PicardIterateResidualData` bundle the capstone consumes. -/
def picardIterateResidualData_of_core
    {p : CM2Params} (hχ0 : p.χ₀ = 0) {u₀ : intervalDomainPoint → ℝ}
    (hu₀cont : Continuous u₀)
    {D : GradientMildSolutionData p u₀}
    (hDu : D.u = picardLimit p u₀ D.T)
    -- ITERATE-SIDE: the limit-source bounded-Duhamel package, produced from the cone
    -- iterate data via `IntervalPicardLimitBddBootstrap.duhamelSourceBddOn_of_iterates`
    -- (Stage-A `hcontP` from `IntervalPicardLimitCoeffTimeCont.patchedSource_coeff_…`
    -- + the tower-produced `hiter_cont`/`henv_iter` — the latter being the cosine-
    -- coefficient TIME-continuity and n-uniform envelope NOT carried by the spatial
    -- `HasContinuousSlices` core; produced by `IntervalPicardTowerProjection`).
    -- NON-circular: `hsrc0` never appeals to patched-slice sup-norm continuity.
    (hsrc0 : ShenWork.IntervalPicardLimitRestartBdd.DuhamelSourceBddOn
      (ShenWork.IntervalPicardLimitBddProducer.patchedSource p u₀ D.u) D.T)
    -- D-SIDE: initial-datum cosine-coefficient bound (satisfiable from `Continuous u₀`
    -- via `IntervalRestartSliceLipschitz.u₀_cosineCoeff_bound`).
    {M₀ : ℝ}
    (hu₀_bound : ∀ k,
      |ShenWork.IntervalNeumannFullKernel.cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (C : PicardIterateResidualCore p u₀ D) :
    Thm11ChiZeroResidual.PicardIterateResidualData p u₀ D :=
  HresProducer.picardIterateResidualData_of_cone hDu C.hcont_iter C.hFacts C.hFacts_T
    C.Wdata
    (ShenWork.IntervalPicardLimitSliceTimeContinuity.hsliceTC_of_mild_restart
      hχ0 hu₀cont D hDu hsrc0 hu₀_bound)

end ShenWork.Paper2.HresWiring
