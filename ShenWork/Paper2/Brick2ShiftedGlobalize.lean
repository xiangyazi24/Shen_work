import ShenWork.PDE.IntervalDuhamelSourceTimeC1On
import ShenWork.PDE.IntervalTimeSoftClamp

/-!
# Brick 2 — windowed `DuhamelSourceTimeC1On` → global `DuhamelSourceTimeC1`

The single load-bearing analytic lift for the χ₀<0 boundedness route.

A `DuhamelSourceTimeC1On a c' d'` is one-sided, *window-local* data: the
coefficient family `a` is `C¹` in time with a summable ℓ¹ envelope, but only over
the closed window `[c', d']`.  The classical-regularity engine instead consumes
the *global* `DuhamelSourceTimeC1 a'`, whose envelope / derivative-bound legs hold
for all `s ≥ 0`.

The bridge is the C¹ soft clamp `φ` of `IntervalTimeSoftClamp`: composing the
windowed family's time argument with `Φ σ := φ c' c d d' (τ + σ)` produces a
genuinely *global* family `a' σ k := a (φ c' c d d' (τ + σ)) k`, because `Φ` maps
**all** of `ℝ` into the window `[c', d']` (`φ_mem_range`).  Over the active
id-zone (`τ + σ ∈ [c, d]`) the clamp is the identity (`φ_eq_id_on`), so `a'`
agrees there with the physical shifted family — all the restart consumers read.

Concretely:
* (a) the windowed `HasDerivWithinAt` on `Icc c' d'` is upgraded to a full-line
  `HasDerivAt` of the composed family, via `HasDerivWithinAt.comp` with the inner
  clamp `HasDerivAt φ` whose image lies in the window (`MapsTo Φ univ (Icc c' d')`);
* (b) `henv_bound` / `hderivBound` extend from `s ∈ Icc c' d'` to all `s` because
  `Φ σ ∈ Icc c' d'` always, and the inner factor `ψ (τ + σ) ∈ [0, 1]`.

Source-agnostic: it knows nothing about chemotaxis or logistics, only the
`DuhamelSourceTimeC1On` interface.  No `sorry`, no `axiom`, no `native_decide`.
-/

open Set
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalTimeSoftClamp

noncomputable section

namespace ShenWork.IntervalDuhamelSourceTimeC1On

/-- **Brick 2 — soft-clamp globalization of a windowed source package.**

From window-local `C¹` source data `DuhamelSourceTimeC1On a c' d'` on a window
`c' < c ≤ d < d'`, build the GLOBAL `DuhamelSourceTimeC1` package for the
soft-clamped, `τ`-shifted family `σ ↦ a (φ c' c d d' (τ + σ))`.  The clamp keeps
the slice index inside `[c', d']` for every `σ`, so the windowed envelope and
derivative bounds become honest global legs. -/
noncomputable def duhamelSourceTimeC1_of_shifted_On
    {a : ℝ → ℕ → ℝ} {τ c' c d d' : ℝ}
    (src : DuhamelSourceTimeC1On a c' d')
    (hc' : c' < c) (hcd : c ≤ d) (hd' : d < d') :
    DuhamelSourceTimeC1 (fun σ k => a (φ c' c d d' (τ + σ)) k) where
  adot := fun σ k => src.adot (φ c' c d d' (τ + σ)) k * ψ c' c d d' (τ + σ)
  hderiv := by
    intro σ n
    have hmem : ∀ r : ℝ, φ c' c d d' (τ + r) ∈ Set.Icc c' d' :=
      fun r => φ_mem_range hc' hcd hd' (τ + r)
    have hmap : Set.MapsTo (fun r : ℝ => φ c' c d d' (τ + r)) Set.univ
        (Set.Icc c' d') := fun r _ => hmem r
    have hΦderiv : HasDerivAt (fun r : ℝ => φ c' c d d' (τ + r))
        (ψ c' c d d' (τ + σ)) σ := by
      have hshift : HasDerivAt (fun s : ℝ => τ + s) 1 σ := (hasDerivAt_id σ).const_add τ
      have h := (hasDerivAt_φ (c' := c') (c := c) (d := d) (d' := d') (τ + σ)).comp σ hshift
      simpa [Function.comp, mul_one] using h
    have hout : HasDerivWithinAt (fun r => a r n)
        (src.adot (φ c' c d d' (τ + σ)) n) (Set.Icc c' d')
        (φ c' c d d' (τ + σ)) := src.hderiv _ (hmem σ) n
    have hcomp := hout.comp σ hΦderiv.hasDerivWithinAt hmap
    simpa [Function.comp] using hcomp
  hadotcont := by
    intro n
    have hmem : ∀ r : ℝ, φ c' c d d' (τ + r) ∈ Set.Icc c' d' :=
      fun r => φ_mem_range hc' hcd hd' (τ + r)
    have hΦcont : Continuous (fun σ : ℝ => φ c' c d d' (τ + σ)) :=
      φ_continuous.comp (continuous_const.add continuous_id)
    have h1 : Continuous (fun σ : ℝ => src.adot (φ c' c d d' (τ + σ)) n) :=
      (src.hadotcont n).comp_continuous hΦcont (fun σ => hmem σ)
    have h2 : Continuous (fun σ : ℝ => ψ c' c d d' (τ + σ)) :=
      ψ_continuous.comp (continuous_const.add continuous_id)
    exact h1.mul h2
  envelope := src.envelope
  henv_summable := src.henv_summable
  henv_bound := by
    intro σ _ n
    exact src.henv_bound (φ c' c d d' (τ + σ)) (φ_mem_range hc' hcd hd' (τ + σ)) n
  derivBound := src.derivBound
  hderivBound := by
    intro σ _ n
    have hc'mem : c' ∈ Set.Icc c' d' := ⟨le_rfl, by linarith [hc'.le, hd'.le]⟩
    have hMnn : 0 ≤ src.derivBound :=
      le_trans (abs_nonneg _) (src.hderivBound c' hc'mem 0)
    have hbnd : |src.adot (φ c' c d d' (τ + σ)) n| ≤ src.derivBound :=
      src.hderivBound (φ c' c d d' (τ + σ)) (φ_mem_range hc' hcd hd' (τ + σ)) n
    rw [abs_mul, abs_of_nonneg (ψ_nonneg (τ + σ))]
    calc |src.adot (φ c' c d d' (τ + σ)) n| * ψ c' c d d' (τ + σ)
        ≤ src.derivBound * 1 :=
          mul_le_mul hbnd (ψ_le_one (τ + σ)) (ψ_nonneg (τ + σ)) hMnn
      _ = src.derivBound := mul_one _

/-- **Id-zone agreement.**  Where the shift lands in the active window
`τ + σ ∈ [c, d]`, the soft clamp is the identity (`φ_eq_id_on`), so the
clamped global family equals the physical `τ`-shifted source family. -/
theorem shiftedClamped_eq_on {a : ℝ → ℕ → ℝ} {τ c' c d d' : ℝ}
    (hc' : c' < c) (hd' : d < d') {σ : ℝ}
    (hσ : τ + σ ∈ Set.Icc c d) (n : ℕ) :
    a (φ c' c d d' (τ + σ)) n = a (τ + σ) n := by
  rw [φ_eq_id_on hc' hd' hσ]

end ShenWork.IntervalDuhamelSourceTimeC1On

#print axioms ShenWork.IntervalDuhamelSourceTimeC1On.duhamelSourceTimeC1_of_shifted_On
#print axioms ShenWork.IntervalDuhamelSourceTimeC1On.shiftedClamped_eq_on
