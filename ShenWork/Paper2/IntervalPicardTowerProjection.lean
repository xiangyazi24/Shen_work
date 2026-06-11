/-
  ShenWork/Paper2/IntervalPicardTowerProjection.lean

  **Tower campaign stage 2 — the tower projections (items 14–16).**

  Projects the per-level `TowerLevel` carrier (`IntervalPicardSourceTower`) into the
  capstone's provider surface:

    * `wdata_of_tower` / `wdata_all_of_tower` (item 14) — a DIRECT fill of
      `IterateWindowC2Data p u₀ a' T` (and the `∀ a', 0 < a' →` family, i.e. exactly
      `WdataProvider p u₀ D` when `T = D.T`) from `tower_all`.  The representation
      triple is `iterateReprCoeff` (TowerLevel.hrepr_*), the ball facts come from the
      `TowerInputs` bundle, and the window-uniform G1/G2 scalars are the profile sup
      constants `G1win`/`G2win` (bounding `TowerLevel.hG1`/`hG2`).  Degenerate windows
      `a' > T` are filled vacuously (verdict trap 9).

    * `wdataProvider_of_tower` (item 15) — the `WdataProvider p u₀ D` form, the exact
      provider leg consumed by `paper2_theorem_1_1_chiZero_unconditional`.

    * `HWdata_of_tower` — the universal `HWdata` shape: given `TowerInputs` for every
      cone-constructed datum, the capstone's provider hypothesis is discharged.  The
      one-line final wiring into `paper2_theorem_1_1_chiZero_unconditional` is noted
      in the closing doc-comment (it consumes `HWdata_of_tower` directly).

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalPicardSourceTower
import ShenWork.Paper2.IntervalDomainHresWiring

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalDomain)
open ShenWork.Paper2 (PositiveInitialDatum)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (picardIter picardLimit GradientMildSolutionData)
open ShenWork.IntervalPicardIterateUniform
  (G1profile G2profile G1profile_nonneg)
open ShenWork.IntervalPicardIterateRepresentation (iterateReprCoeff)
open ShenWork.IntervalPicardWeightedC2Bootstrap
  (IterateWindowC2Data windowSourceConst windowSourceConst_nonneg
   iterate_source_windowEnv source_coeff_window_uniform)
open ShenWork.IntervalPicardLimitBddProducer (windowEnv)
open ShenWork.IntervalPicardWdataAssembly
  (G1win G2win G1win_nonneg G2win_nonneg G1profile_le_G1win G2profile_le_G2win)
open ShenWork.IntervalPicardSourceTower (TowerLevel TowerInputs tower_all)
open ShenWork.Paper2.HresWiring (WdataProvider)

noncomputable section

namespace ShenWork.IntervalPicardTowerProjection

/-! ## §1 — One window bundle from the tower. -/

/-- **`IterateWindowC2Data` from the tower (item 14, single window).**

On a window `[a',T]` (`0 < a' ≤ T`), the bundle is filled DIRECTLY from `tower_all`:

  * `bc n σ := iterateReprCoeff p u₀ n σ` — the representation coefficients;
  * `hbsum`/`hagree` — `(tower_all … n).hrepr_sum`/`hrepr_agree`, restricted to
    `[a',T]`;
  * `hpos`/`hub` — the ball facts from the `TowerInputs` bundle;
  * `hG1`/`hG2` — `(tower_all … n).hG1`/`hG2` bounded onto the window constants
    `G1win`/`G2win` via `G1profile_le_G1win`/`G2profile_le_G2win`.

No `UniformWiring` is consumed: the tower already carries the per-level G1/G2
profiles constructively. -/
def wdata_of_tower
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {M A₂ T a' : ℝ}
    (H : TowerInputs p u₀ M A₂ T)
    (ha' : 0 < a') (haT : a' ≤ T) :
    IterateWindowC2Data p u₀ a' T :=
  let hTpos : 0 < T := lt_of_lt_of_le ha' haT
  { M := M
    G1 := G1win p M a' T
    G2 := G2win A₂ a'
    hMnn := H.hMnn
    hG1nn := G1win_nonneg H.hMnn ha' hTpos.le
    hG2nn := G2win_nonneg H.hA₂nn ha'
    bc := fun n σ => iterateReprCoeff p u₀ n σ
    hbsum := fun n σ haσ hσT =>
      (tower_all p u₀ H n).hrepr_sum σ (lt_of_lt_of_le ha' haσ) hσT
    hagree := fun n σ haσ hσT =>
      (tower_all p u₀ H n).hrepr_agree σ (lt_of_lt_of_le ha' haσ) hσT
    hpos := fun n σ haσ hσT x hx =>
      H.hpos n σ (lt_of_lt_of_le ha' haσ) hσT x hx
    hub := fun n σ haσ hσT x hx =>
      H.hub n σ (lt_of_lt_of_le ha' haσ) hσT x hx
    hG1 := by
      intro n σ haσ hσT x _hx
      have hσpos : 0 < σ := lt_of_lt_of_le ha' haσ
      exact le_trans ((tower_all p u₀ H n).hG1 σ hσpos hσT x)
        (G1profile_le_G1win H.hMnn ha' haσ hσT)
    hG2 := by
      intro n σ haσ hσT x _hx
      have hσpos : 0 < σ := lt_of_lt_of_le ha' haσ
      exact le_trans ((tower_all p u₀ H n).hG2 σ hσpos hσT x)
        (G2profile_le_G2win H.hA₂nn ha' haσ) }

/-! ## §2 — The `Wdata` family (item 14). -/

/-- **`wdata_all_of_tower` (item 14).**  The full `∀ a', 0 < a' →
IterateWindowC2Data p u₀ a' T` family from the tower input bundle.  For a window
`a' > T` (degenerate, empty), every per-`σ` field is vacuous (`a' ≤ σ ≤ T` is
unsatisfiable), so the bundle is filled with trivial constants (verdict trap 9). -/
def wdata_all_of_tower
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {M A₂ T : ℝ}
    (H : TowerInputs p u₀ M A₂ T) :
    ∀ a', 0 < a' → IterateWindowC2Data p u₀ a' T := by
  intro a' ha'
  by_cases haT : a' ≤ T
  · exact wdata_of_tower p u₀ H ha' haT
  · refine
      { M := M, G1 := 0, G2 := 0
        hMnn := H.hMnn, hG1nn := le_refl 0, hG2nn := le_refl 0
        bc := fun _ _ _ => 0
        hbsum := ?_, hagree := ?_, hpos := ?_, hub := ?_, hG1 := ?_, hG2 := ?_ } <;>
    · intro n σ haσ hσT
      exact absurd (le_trans haσ hσT) haT

/-! ## §2b — The two iterate-side obligations for the hinterior closure.

The hinterior / `duhamelSourceBddOn_of_iterates` closure consumes two iterate-side
facts about the canonical Picard iterates (both n-UNIFORM):

  (1) `henv_iter` — the n-uniform per-window source-coefficient envelope
      `|coeffs(logistic(uₙ(s))) k| ≤ windowEnv (Cwin a') k` on `[a',T]`;
  (2) `hiter_cont` — the per-iterate, per-mode source-coefficient time continuity
      on `[a',τ]`.

Both are produced DIRECTLY from the tower input bundle `TowerInputs`:

  * (1) is the window-uniform envelope theorem `source_coeff_window_uniform`
    (stage F) applied to the tower's window-data family `wdata_all_of_tower`.  The
    explicit constant `Cwin a' = windowSourceConst p M (G1win p M a' T) (G2win A₂ a')`
    is read off the tower's per-window K2 data — *n-uniform* because the window K2
    scalars `G1win`/`G2win` are themselves n-free (the tower's `hG1`/`hG2` profiles
    are n-uniform).  The `windowEnv` head (`k = 0`) is handled by `windowEnv`'s
    constant head and `slice_source_coeff_zero` inside `iterate_source_windowEnv`.

  * (2) needs NO global source package: `tower_all` now carries, for every level `n`,
    a positive-window `TimeC1On` package up to the endpoint.  Its derivative field
    gives coefficient continuity on `[a',τ]`.
-/

/-- **`henv_iter_of_tower` — obligation (1).**  The n-UNIFORM per-window
source-coefficient envelope, with the explicit window constant `Cwin a'` read off the
tower's window K2 data.  Consumed verbatim by `duhamelSourceBddOn_of_iterates`'s
`henv_iter` leg.  The constant is given by the existential witness of
`source_coeff_window_uniform`; here it is exposed via the same definitional dependent
`Cwin`. -/
theorem henv_iter_of_tower
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {M A₂ T : ℝ}
    (H : TowerInputs p u₀ M A₂ T) :
    ∃ Cwin : ℝ → ℝ, (∀ a', 0 ≤ Cwin a') ∧
      (∀ a', 0 < a' → ∀ s, a' ≤ s → s ≤ T → ∀ (n k : ℕ),
        |cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k|
          ≤ windowEnv (Cwin a') k) :=
  source_coeff_window_uniform p u₀ H.hα (wdata_all_of_tower p u₀ H)

/-- **`hiter_cont_of_tower` — obligation (2).**  Per-iterate, per-mode
source-coefficient time continuity on any window `[a',τ] ⊆ (0,T]`, derived from
the tower-produced positive-window source package. -/
theorem hiter_cont_of_tower
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {M A₂ T : ℝ}
    (H : TowerInputs p u₀ M A₂ T) :
    ∀ (a' τ : ℝ), 0 < a' → a' ≤ τ → τ ≤ T → ∀ (n k : ℕ),
      ContinuousOn
        (fun s => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
        (Set.Icc a' τ) := by
  intro a' τ ha' haτ hτT n k
  by_cases hlt : a' < τ
  · have ha'T : a' < T := lt_of_lt_of_le hlt hτT
    have src := (tower_all p u₀ H n).srcOn a' ha' ha'T
    intro s hs
    exact ((src.hderiv s ⟨hs.1, le_trans hs.2 hτT⟩ k).continuousWithinAt).mono
      (Set.Icc_subset_Icc le_rfl hτT)
  · have hτa : τ = a' := le_antisymm (le_of_not_gt hlt) haτ
    have hIcc : Set.Icc a' τ = ({a'} : Set ℝ) := by
      rw [hτa, Set.Icc_self]
    rw [hIcc]
    exact continuousOn_singleton _ a'

/-! ## §3 — The `WdataProvider` projection (item 15). -/

/-- **`wdataProvider_of_tower` (item 15).**  When the horizon `T` equals `D.T`, the
`wdata_all_of_tower` family is *definitionally* the `WdataProvider p u₀ D` leg (recall
`WdataProvider p u₀ D := ∀ a', 0 < a' → IterateWindowC2Data p u₀ a' D.T`).  This is the
single provider obligation of `paper2_theorem_1_1_chiZero_unconditional`. -/
def wdataProvider_of_tower
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {M A₂ : ℝ}
    (D : GradientMildSolutionData p u₀)
    (H : TowerInputs p u₀ M A₂ D.T) :
    WdataProvider p u₀ D :=
  wdata_all_of_tower p u₀ H

/-! ## §4 — The capstone provider `HWdata` (final wiring).

`paper2_theorem_1_1_chiZero_unconditional` consumes a single hypothesis

    HWdata : ∀ u₀, PositiveInitialDatum u₀ → ∀ D,
             D.u = picardLimit p u₀ D.T → WdataProvider p u₀ D

`HWdata_of_tower` discharges it from a per-datum `TowerInputs` supply: at each
cone-constructed datum `D`, the tower bundle (gate, ball, in-tower source packages,
kernel-G1, G2 endpoints, and adot data) yields `WdataProvider p u₀ D` via
`wdataProvider_of_tower`. -/

/-- **`HWdata_of_tower` — the capstone provider from a per-datum tower supply.**

`HTower` supplies, for every datum `D` (with the canonical-Picard-limit identity),
the `TowerInputs` bundle at the datum's horizon `D.T` (with a per-datum mass `M` and
budget `A₂`).  The capstone's `WdataProvider` leg follows by `wdataProvider_of_tower`.

This is the **final wiring shape**: feeding `HWdata_of_tower HTower` to
`paper2_theorem_1_1_chiZero_unconditional` closes Paper 2 Theorem 1.1 (χ₀ = 0)
from the per-datum tower bundle.  The cone/tower entry point
`IntervalPicardTowerSupply.from_cone_construction` supplies that bundle
unconditionally. -/
def HWdata_of_tower
    (p : CM2Params)
    (HTower : ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
      ∀ D : GradientMildSolutionData p u₀,
        D.u = picardLimit p u₀ D.T →
        Σ' M A₂ : ℝ, TowerInputs p u₀ M A₂ D.T) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
      ∀ D : GradientMildSolutionData p u₀,
        D.u = picardLimit p u₀ D.T → WdataProvider p u₀ D :=
  fun u₀ hu₀ D hDu =>
    wdataProvider_of_tower p u₀ D (HTower u₀ hu₀ D hDu).2.2

end ShenWork.IntervalPicardTowerProjection
