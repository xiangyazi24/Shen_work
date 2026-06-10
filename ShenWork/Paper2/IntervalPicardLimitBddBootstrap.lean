/-
  ShenWork/Paper2/IntervalPicardLimitBddBootstrap.lean

  **F2 iterate-side bootstrap of the bounded-source package.**

  ## Why (the circularity break)

  The Provider needs
    `hsrc0F : DuhamelSourceBddOn (patchedSource p u₀ D.u) D.T`.
  The strict producer `IntervalPicardLimitBddProducer.duhamelSourceBddOn_of_mildData`
  assembles this package, but its `env` field routes the per-window quadratic decay
  through a per-slice *cosine-series proxy* `cs σ` for the limit slice
  `intervalDomainLift (D.u σ)` (the data `bc/hbsum/hagree`).  Every such
  representation is itself PROVEN FROM a `DuhamelSourceBddOn (patchedSource …)`
  package — so feeding `bc/hbsum/hagree` back into the producer that builds
  `hsrc0F` is an unsatisfiable `have`-ordering.

  ## The honest break (this file)

  The genuine new content is to bound the LIMIT source coefficients DIRECTLY from
  the PICARD ITERATES, each of which is genuinely `C²` (n-INDEPENDENT constants),
  passing to the limit by `le_of_tendsto` — the pattern already proven in
  `IntervalPicardLimitRestartWeak.limitSource_l1cont`:

  * `hM` (k-uniform bound on the patched family): built DIRECTLY from `D`'s own
    fields (`D.hbound`/`D.hpos`/`D.hcont` for the canonical part, an initial-datum
    bound for `s ≤ 0`).  NO representation — `D.hcont` gives continuity of the slice
    on `[0,1]`, which is all `cosineCoeffs_abs_le_of_continuous_bounded` needs.

  * `env` (per-window quadratic decay): from n-UNIFORM iterate coefficient
    envelopes `|coeffs(logistic(picardIter n s)) k| ≤ windowEnv C k` (the iterates
    are genuinely C², so the GLOBAL decay machinery applies per iterate with no
    representation circularity) + pointwise coefficient convergence
    `coeffs(logistic(picardIter n s)) k → coeffs(logistic(D.u s)) k`, combined via
    `le_of_tendsto`.

  * `hcont` (time-continuity of each coefficient): NAMED satisfiable, threaded
    exactly as `limitSource_l1cont` / the strict producer do.

  The iterate-side analytic inputs (n-uniform iterate envelope; pointwise
  convergence to the generic mild-solution slice `D.u`) are isolated as PRECISELY
  named hypotheses on this wrapper.  The Provider discharges what it can from its
  in-scope facts and leaves the genuinely-open iterate regularity / convergence as
  named sorried `have`s with route comments.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide` in this file.
-/
import ShenWork.Paper2.IntervalPicardLimitBddProducer

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (GradientMildSolutionData picardIter)
open ShenWork.IntervalPicardLimitRestartBdd (DuhamelSourceBddOn)
open ShenWork.IntervalMildPicardRegularity
  (cosineCoeffs_abs_le_of_continuous_bounded logisticSourceFun
   logisticSourceFun_abs_le_of_bound logisticLifted_eq_logisticSourceFun_on_Icc)
open ShenWork.IntervalLogisticSourceQuantBound (B_log)
open ShenWork.IntervalPicardLimitBddProducer
  (patchedSource patchedSource_eq_of_pos windowEnv windowEnv_summable)
open ShenWork.Paper2 (cosineCoeffs_congr_on_Icc)

noncomputable section

namespace ShenWork.IntervalPicardLimitBddBootstrap

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-! ## 1. The `le_of_tendsto` envelope transfer.

The single genuinely-new analytic step: an n-uniform per-mode bound on the iterate
source coefficients passes to the limit (= `D.u`) coefficients via `le_of_tendsto`,
exactly as `IntervalPicardLimitRestartWeak.limitSource_l1cont.henv_bound` does.  No
hypothesis on the SHAPE of the bound is used, so it serves both the `windowEnv`
(decaying) and the constant `M` instantiations. -/

/-- **Envelope transfer (iterate → limit).**  If every iterate's source coefficient
mode `k` at time `s` is bounded by `E k`, and the iterate coefficients converge to
the limit coefficients, then the limit coefficient is bounded by `E k`. -/
theorem abs_limitCoeff_le_of_iterate
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (s : ℝ) (k : ℕ) {E : ℝ}
    (hbnd : ∀ n, |cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k| ≤ E)
    (hconv : Tendsto
      (fun n => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
      atTop (nhds (cosineCoeffs (logisticLifted p (u s)) k))) :
    |cosineCoeffs (logisticLifted p (u s)) k| ≤ E := by
  have htend : Tendsto
      (fun n => |cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k|)
      atTop (nhds (|cosineCoeffs (logisticLifted p (u s)) k|)) := hconv.abs
  exact le_of_tendsto htend (Filter.Eventually.of_forall hbnd)

/-! ## 2. `hM` directly from the mild-solution data (NO representation).

The k-uniform bound on the patched family on `[0, τ]`.  For `s ≤ 0` the patched
value is the initial-datum source coefficient (bounded by the supplied `M₀'`).  For
`s ∈ (0, τ]` the slice `D.u s` is continuous (`D.hcont`), positive (`D.hpos`) and
sup-bounded (`D.hbound`), so its logistic source is sup-bounded by
`Msup·(a + b·Msup^α)` and hence its cosine coefficients by `2·Msup·(a + b·Msup^α)`
— via `cosineCoeffs_abs_le_of_continuous_bounded`, with the slice's own continuity,
not a series proxy. -/

/-- The patched-family k-uniform bound, built from `D` fields only. -/
theorem patchedSource_abs_le_const
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {M₀' : ℝ}
    (hu₀_src_bound : ∀ k, |cosineCoeffs (logisticLifted p u₀) k| ≤ M₀')
    {τ : ℝ} (hτT : τ ≤ D.T) :
    ∀ s, 0 ≤ s → s ≤ τ → ∀ k,
      |patchedSource p u₀ D.u s k|
        ≤ max M₀' (2 * (D.M * (p.a + p.b * D.M ^ p.α))) := by
  intro s hs hsτ k
  rcases eq_or_lt_of_le hs with hs0 | hspos
  · -- s = 0: patched value is the initial-datum source.
    simp only [patchedSource, ← hs0, le_refl, if_pos]
    exact le_trans (hu₀_src_bound k) (le_max_left _ _)
  · -- s > 0: slice sup bound through the source-fun coefficient bound.
    rw [patchedSource_eq_of_pos p u₀ D.u hspos k]
    have hsT : s ≤ D.T := le_trans hsτ hτT
    have hMnn : 0 ≤ D.M := le_of_lt D.hM
    have hαpos : 0 < p.α := lt_of_lt_of_le one_pos hα
    have hpos_s : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (D.u s) x := by
      intro x hx
      simp only [intervalDomainLift, dif_pos hx]
      exact D.hpos s hspos hsT ⟨x, hx⟩
    have hub_s : ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (D.u s) x ≤ D.M := by
      intro x hx
      simp only [intervalDomainLift, dif_pos hx]
      exact le_trans (le_abs_self _) (D.hbound s hspos hsT ⟨x, hx⟩)
    have hcoeff_eq : cosineCoeffs (logisticLifted p (D.u s)) k
        = cosineCoeffs (logisticSourceFun p.a p.b p.α (intervalDomainLift (D.u s))) k :=
      cosineCoeffs_congr_on_Icc (logisticLifted_eq_logisticSourceFun_on_Icc p (D.u s)) k
    rw [hcoeff_eq]
    have hbd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |logisticSourceFun p.a p.b p.α (intervalDomainLift (D.u s)) x|
          ≤ D.M * (p.a + p.b * D.M ^ p.α) :=
      logisticSourceFun_abs_le_of_bound (B := D.M) hMnn hαpos ha hb
        (fun x hx => by rw [abs_of_pos (hpos_s x hx)]; exact hub_s x hx) hpos_s
    -- continuity of the slice's lift on [0,1] from D.hcont (no series proxy).
    have hgc : ContinuousOn (intervalDomainLift (D.u s)) (Set.Icc (0 : ℝ) 1) := by
      have hcont_s : Continuous (D.u s) := D.hcont s hspos hsT
      rw [continuousOn_iff_continuous_restrict]
      have heq : (Set.Icc (0 : ℝ) 1).restrict (intervalDomainLift (D.u s)) = D.u s := by
        funext ⟨y, hy⟩
        simp only [Set.restrict_apply, intervalDomainLift]
        rw [dif_pos hy]
        exact congr_arg (D.u s) (Subtype.ext rfl)
      rw [heq]; exact hcont_s
    have hpos' : ∀ x, x ∈ Set.Icc (0:ℝ) 1 → intervalDomainLift (D.u s) x ≠ 0 :=
      fun x hx => ne_of_gt (hpos_s x hx)
    have hcont : ContinuousOn
        (logisticSourceFun p.a p.b p.α (intervalDomainLift (D.u s))) (Set.Icc (0 : ℝ) 1) := by
      unfold logisticSourceFun
      apply ContinuousOn.mul hgc
      apply ContinuousOn.sub continuousOn_const
      apply ContinuousOn.mul continuousOn_const
      exact ContinuousOn.rpow_const hgc (fun x hx => Or.inl (hpos' x hx))
    have hMa_nn : 0 ≤ D.M * (p.a + p.b * D.M ^ p.α) := by positivity
    exact le_trans
      (cosineCoeffs_abs_le_of_continuous_bounded hcont hMa_nn hbd k)
      (le_max_right _ _)

/-! ## 3. The iterate-side bootstrap producer.

Assembles `DuhamelSourceBddOn (patchedSource p u₀ D.u) τ` with:

* `hM` — `patchedSource_abs_le_const` (D-side only);
* `hcont` — NAMED satisfiable hypothesis `hcontP` (exactly as the strict producer);
* `env a' := windowEnv (Cwin a')` — the per-window decay constant `Cwin a'` from
  the n-UNIFORM iterate envelope `henv_iter`, transferred to `D.u` via
  `abs_limitCoeff_le_of_iterate` (`le_of_tendsto`); the convergence is the NAMED
  iterate-side hypothesis `hconv`.

The `env`/`henv_bound` content is precisely where the circularity is broken: the
window constant `Cwin a'` is supplied by the iterate side (each iterate is C² with
n-independent K2 constants), NOT by a representation of `D.u`. -/

/-- **F2 iterate-side bootstrap producer.**  Builds the bounded-source package for
the patched canonical limit-source family on `[0, τ]` from:

* the mild-solution data `D` (for `hM`);
* a per-window constant `Cwin : ℝ → ℝ` and an n-UNIFORM iterate envelope
  `henv_iter` showing each iterate's source coefficients are dominated by
  `windowEnv (Cwin a')` on `[a', τ]` (the iterate-side decay — satisfiable from the
  genuinely-C² iterate slices, n-independent constants);
* pointwise coefficient convergence `hconv` of the iterates to `D.u`;
* the named time-continuity hypothesis `hcontP`.

NO `bc`/`hbsum`/`hagree` of the LIMIT enter — the circularity is broken. -/
noncomputable def duhamelSourceBddOn_of_iterates
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    -- s ≤ 0 branch: bound on the initial-datum source coefficients
    {M₀' : ℝ} (hM₀'_nonneg : 0 ≤ M₀')
    (hu₀_src_bound : ∀ k, |cosineCoeffs (logisticLifted p u₀) k| ≤ M₀')
    -- per-window decay constant (iterate-side) + n-uniform iterate envelope
    (Cwin : ℝ → ℝ) (_hCwin : ∀ a', 0 ≤ Cwin a')
    (henv_iter : ∀ a', 0 < a' → ∀ s, a' ≤ s → s ≤ D.T → ∀ (n : ℕ) (k : ℕ),
      |cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k| ≤ windowEnv (Cwin a') k)
    -- pointwise coefficient convergence (iterate-side)
    (hconv : ∀ s, 0 < s → s ≤ D.T → ∀ k,
      Tendsto (fun n => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
        atTop (nhds (cosineCoeffs (logisticLifted p (D.u s)) k)))
    -- time continuity of the patched coefficient family (NAMED SATISFIABLE)
    {τ : ℝ} (_hτ0 : 0 < τ) (hτT : τ ≤ D.T)
    (hcontP : ∀ k, ContinuousOn
      (fun s => patchedSource p u₀ D.u s k) (Set.Icc 0 τ)) :
    DuhamelSourceBddOn (patchedSource p u₀ D.u) τ where
  M := max M₀' (2 * (D.M * (p.a + p.b * D.M ^ p.α)))
  hM_nonneg := le_trans hM₀'_nonneg (le_max_left _ _)
  hM := patchedSource_abs_le_const p D hα ha hb hu₀_src_bound hτT
  hcont := hcontP
  env := fun a' => windowEnv (Cwin a')
  henv_summable := fun _ _ _ => windowEnv_summable
  henv_bound := by
    intro a' ha' s ha's hsτ k
    have hspos : 0 < s := lt_of_lt_of_le ha' ha's
    have hsT : s ≤ D.T := le_trans hsτ hτT
    -- patched = canonical at s > 0.
    rw [patchedSource_eq_of_pos p u₀ D.u hspos k]
    -- n-uniform iterate bound for this window/slice, then le_of_tendsto.
    have hbnd : ∀ n, |cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k|
        ≤ windowEnv (Cwin a') k :=
      fun n => henv_iter a' ha' s ha's hsT n k
    exact abs_limitCoeff_le_of_iterate p u₀ D.u s k hbnd (hconv s hspos hsT k)

end ShenWork.IntervalPicardLimitBddBootstrap
