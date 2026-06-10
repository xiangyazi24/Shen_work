/-
  ShenWork/Paper2/IntervalDuhamelSourceShift.lean

  **Tower campaign stage 1 — File A (items 1–3).**

  The generic shift + congruence layer for the spectral Duhamel coefficients:

    1. `DuhamelSourceTimeC1.shift_nonneg` — a `DuhamelSourceTimeC1` package for the
       canonical source family precomposed with a non-negative time shift
       `s ↦ a (offset + s)`.  Same envelope/derivative bound; `henv_bound` /
       `hderivBound` survive because `0 ≤ offset` keeps the absolute time
       non-negative.

    2. `duhamelSpectralCoeff_congr_on_Icc` — two coefficient families that agree on
       `[0, τ]` (with `0 ≤ τ`) produce equal spectral Duhamel coefficients, because
       `duhamelSpectralCoeff` only reads `a` on the integration window `[0, τ]`.

    3. `localRestartCoeff_congr_on_Icc` — the same congruence lifted to the full
       restart coefficient `cₙ(τ) = e^{−τλₙ} a₀ₙ + bₙ(τ)`: the homogeneous part is
       `a`-independent, the Duhamel part is item 2.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.PDE.IntervalDuhamelClosedC2
import ShenWork.PDE.IntervalSourceCoefficientTimeC1

open MeasureTheory
open scoped Topology

namespace ShenWork.IntervalDuhamelSourceShift

open ShenWork.IntervalDuhamelClosedC2
  (DuhamelSourceTimeC1 duhamelSpectralCoeff)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)

/-! ## §1 — The non-negative time shift of a `DuhamelSourceTimeC1` package. -/

/-- **(1) Non-negative shift of a time-`C¹` source package.**
If `a` is `DuhamelSourceTimeC1` and `0 ≤ offset`, then the shifted family
`s ↦ a (offset + s)` is again `DuhamelSourceTimeC1`, with the same envelope and
derivative bound.  The derivative is `adot (offset + s)` (chain rule through the
affine map `s ↦ offset + s`); the envelope / derivative bounds survive because
`0 ≤ offset` keeps the absolute time `offset + s` non-negative whenever `0 ≤ s`. -/
def DuhamelSourceTimeC1.shift_nonneg {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC1 a) {offset : ℝ} (hoff : 0 ≤ offset) :
    DuhamelSourceTimeC1 (fun s n => a (offset + s) n) where
  adot := fun s n => src.adot (offset + s) n
  hderiv := by
    intro s n
    have hcomp : HasDerivAt (fun r : ℝ => offset + r) (1 : ℝ) s :=
      (hasDerivAt_id s).const_add offset
    have := (src.hderiv (offset + s) n).comp s hcomp
    simpa using this
  hadotcont := by
    intro n
    exact (src.hadotcont n).comp (continuous_const.add continuous_id)
  envelope := src.envelope
  henv_summable := src.henv_summable
  henv_bound := by
    intro s hs n
    exact src.henv_bound (offset + s) (add_nonneg hoff hs) n
  derivBound := src.derivBound
  hderivBound := by
    intro s hs n
    exact src.hderivBound (offset + s) (add_nonneg hoff hs) n

/-! ## §2 — Congruence of the spectral Duhamel coefficient on `[0,τ]`. -/

/-- **(2) Spectral Duhamel coefficient congruence on `[0,τ]`.**
If `a` and `a'` agree on `Set.Icc 0 τ` (with `0 ≤ τ`) — i.e. for every `s ∈ [0,τ]`
and every `n`, `a s n = a' s n` — then their spectral Duhamel coefficients coincide
at `τ`: `duhamelSpectralCoeff a τ n = duhamelSpectralCoeff a' τ n`.  The integrand of
`duhamelSpectralCoeff … τ` reads its source family only on the integration window
`[0,τ] = uIcc 0 τ`. -/
theorem duhamelSpectralCoeff_congr_on_Icc {a a' : ℝ → ℕ → ℝ} {τ : ℝ}
    (hτ : 0 ≤ τ) (hagree : ∀ s ∈ Set.Icc (0 : ℝ) τ, ∀ n, a s n = a' s n) (n : ℕ) :
    duhamelSpectralCoeff a τ n = duhamelSpectralCoeff a' τ n := by
  unfold duhamelSpectralCoeff
  refine intervalIntegral.integral_congr ?_
  rw [Set.uIcc_of_le hτ]
  intro s hs
  simp only [hagree s hs n]

/-! ## §3 — Congruence of the full restart coefficient on `[0,τ]`. -/

/-- **(3) Restart coefficient congruence on `[0,τ]`.**
The full restart coefficient `cₙ(τ) = e^{−τλₙ} a₀ₙ + bₙ(τ)` is congruent under any
two source families agreeing on `[0,τ]` (and the same homogeneous datum `a₀`): the
homogeneous part `e^{−τλₙ} a₀ₙ` is `a`-independent, the Duhamel part is item 2. -/
theorem localRestartCoeff_congr_on_Icc {a₀ : ℕ → ℝ} {a a' : ℝ → ℕ → ℝ} {τ : ℝ}
    (hτ : 0 ≤ τ) (hagree : ∀ s ∈ Set.Icc (0 : ℝ) τ, ∀ n, a s n = a' s n) (n : ℕ) :
    localRestartCoeff a₀ a τ n = localRestartCoeff a₀ a' τ n := by
  unfold localRestartCoeff
  rw [duhamelSpectralCoeff_congr_on_Icc hτ hagree n]

end ShenWork.IntervalDuhamelSourceShift
