/-
# T6 conjunct-7 via the **time-IBP route** — foundations (Lemmas 1–2)

Route (ChatGPT-recommended, matching the honest B1 path of `T5_DESIGN §7.3`): prove
`DuhamelTermInteriorC2` for `D(t) = ∫₀ᵗ S(t−s) g(s) ds` NOT by a Fourier/heat-value
representation (the spectral route needs `∑|ĝₙ| < ∞`, a strong Fourier regularity
that does not match the fixed-point bootstrap; the heat-value form is moreover
*false* for a merely-bounded source — see `IntervalDuhamelRegularity.lean`), but by
**integration by parts in time**.  The target (a later commit) is

  `intervalDuhamelTerm_closedC2_of_timeC1_source`: if the source `g` is `C¹` in time
  (`∂ₛg` exists, continuous, `C⁰` in `x`), then `D(t)` is spatially `C²` on the
  CLOSED `[0,1]`, with
    `∂ₓₓ D(t) = S(t) g(0) − g(t) + ∫₀ᵗ S(t−s)·∂ₛg(s) ds`.
  The integral kernel is `S(t−s)` (NO spatial derivative) — bounded; the
  `(t−s)^{−3/2}` singularity of `∂ₓₓ K_full` is gone.

The seven-step minimal lemma plan: (1) semigroup endpoint `S(r)f → f` as `r↓0`;
(2) heat identity `∂ₓₓ S(r)f = ∂ᵣ S(r)f` (`r>0`) + Neumann endpoints; (3) time
chain rule `d/ds[S(t−s)g(s)] = −∂ₓₓS(t−s)g(s) + S(t−s)∂ₛg(s)`; (4) interval FTC on
`[0,t−ε]`, `ε↓0`; (5) closed continuity of the RHS; (6) assemble `ContDiffOn ℝ 2`
on `[0,1]`; (7) Neumann endpoints of `D`.

## Reusable T1–T5 spectral infrastructure (surveyed — kept from the spectral
## route's survey; still the backbone of this route's per-`r` semigroup analysis)

* Termwise differentiation: `hasDerivAt_tsum`, `hasDerivAt_tsum_of_isPreconnected`.
* Cosine heat value `unitIntervalCosineHeatValue r a x = ∑'ₙ e^{−rλₙ}cos(nπx)aₙ`,
  with `unitIntervalCosineHeatPointWeight`, `unitIntervalCosineHeatGradientValue`,
  `unitIntervalCosineHeatSecondValue`; first/second `x`-derivative
  (`unitIntervalCosineHeatValue_deriv_eq_gradientValue`,
  `unitIntervalCosineHeatGradientValue_deriv`) and `C²`
  (`unitIntervalCosineHeatValue_contDiff_two`); the operator↔value bridge
  `intervalFullSemigroupOperator_eqOn_cosineHeatValue` (on `(0,1)`).
* Per-mode time derivative `unitIntervalCosineHeatPointWeight_hasDerivAt_time`
  (`∂ᵣ e^{−rλₙ}cos = −λₙ e^{−rλₙ}cos`).
* Summable majorants: `unitIntervalCosineHeatTrace_single_exp_summable`,
  `unitIntervalCosineHeatSecondPointWeight_abs_le` (`≤ 4/(r²π²)·1/n²`),
  `reciprocalSquareTerm_summable`.
* Endpoint Neumann: `unitIntervalCosineHeatGradientValue_eq_zero_at_{zero,one}`,
  `unitIntervalCosineHeatValue_deriv_zero_at_endpoint`; parabolic gain
  `parabolicGain_le_one`.

## Lemma 1 (semigroup endpoint) — already in the repo

`S(0)f = f` is FALSE (`heatKernel 0 = 0`); the correct statement is the
approximate-identity limit, already proved:
`ShenWork.IntervalSemigroupApproxIdentity.intervalFullSemigroup_tendsto_id_at_zero`
(`S(t)f x → f x` as `t↓0`, for continuous `f` with `ℓ¹` cosine coeffs + pointwise
reconstruction + the per-slice kernel spectral identity), and its cosine-value form
`unitIntervalCosineHeatValue_tendsto_tsum`.  Lemma 1 is therefore available; this
file does not restate it (no tautological re-export).

## Lemma 2 (heat identity) — proved here

`∂ᵣ S(r)f = ∂ₓₓ S(r)f` at the cosine-heat-value level: both equal
`unitIntervalCosineHeatSecondValue r a x = ∑'ₙ (−λₙ e^{−rλₙ}cos(nπx))·aₙ`.  The
spatial second derivative is the existing gradient-of-gradient; the **time**
derivative is the new termwise-`∂ᵣ` content, dominated on a neighbourhood of `r>0`
by the same reciprocal-square majorant (`secondPointWeight = ∂ᵣ pointWeight`).

No `sorry`/`admit`/custom `axiom`.
-/

import ShenWork.PDE.IntervalDomainRegularityBootstrap
import ShenWork.PDE.IntervalFullKernelRegularity
import ShenWork.Paper2.IntervalDomainJointTimeRegularity
import ShenWork.PDE.IntervalSemigroupApproxIdentity

open MeasureTheory Filter Topology

noncomputable section

namespace ShenWork.IntervalDuhamelClosedC2

open ShenWork.IntervalDomain ShenWork.IntervalDomainRegularityBootstrap
open ShenWork.IntervalFullKernelRegularity

/-- The second-spatial-derivative term-weight equals `−λₙ` times the value
term-weight: `e^{−rλₙ}·(−(nπ)²cos) = −λₙ·e^{−rλₙ}cos`.  In particular it coincides
with the per-mode *time* derivative `∂ᵣ(unitIntervalCosineHeatPointWeight · x n)`
(`unitIntervalCosineHeatPointWeight_hasDerivAt_time`), which is the spectral form of
the heat equation `∂ᵣ = ∂ₓₓ` mode by mode. -/
theorem unitIntervalCosineHeatSecondPointWeight_eq_neg_eigenvalue_mul (r x : ℝ) (n : ℕ) :
    unitIntervalCosineHeatSecondPointWeight r x n =
      -(unitIntervalCosineEigenvalue n) * unitIntervalCosineHeatPointWeight r x n := by
  unfold unitIntervalCosineHeatSecondPointWeight unitIntervalCosineHeatPointWeight
    unitIntervalCosineEigenvalue unitIntervalCosineMode
  ring

/-- **Time derivative of the cosine heat value = the second-spatial-derivative
series.**  For `r > 0` and bounded coefficients, `r ↦ unitIntervalCosineHeatValue r
a x` is differentiable with derivative `unitIntervalCosineHeatSecondValue r a x`
(`= ∑'ₙ −λₙ e^{−rλₙ}cos(nπx)·aₙ`).  This is the **time half** of the spectral heat
equation; termwise `∂ᵣ(e^{−rλₙ}cos) = −λₙ e^{−rλₙ}cos`, dominated near `r` by the
`4/((r/2)²π²)·n⁻²` majorant. -/
theorem unitIntervalCosineHeatValue_hasDerivAt_time
    {r x : ℝ} (hr : 0 < r) {a : ℕ → ℝ} {M : ℝ} (hM : ∀ n, |a n| ≤ M) :
    HasDerivAt (fun s : ℝ => unitIntervalCosineHeatValue s a x)
      (unitIntervalCosineHeatSecondValue r a x) r := by
  classical
  set s : Set ℝ := Set.Ioi (r / 2) with hs_def
  have hr2pos : (0 : ℝ) < r / 2 := by linarith
  have hr_mem : r ∈ s := by rw [hs_def]; exact Set.mem_Ioi.mpr (by linarith)
  -- uniform majorant on `s`, from the worst case `r/2`.
  set C : ℝ := 4 / ((r / 2) ^ 2 * Real.pi ^ 2) with hC_def
  set u : ℕ → ℝ := fun n => C * reciprocalSquareTerm n * |M| with hu_def
  have hu_summable : Summable u := by
    have := (reciprocalSquareTerm_summable.mul_left C).mul_right |M|
    simpa [hu_def, mul_assoc] using this
  -- (hf) per-mode time `HasDerivAt`.
  have hf : ∀ n : ℕ, ∀ w ∈ s,
      HasDerivAt (fun s : ℝ => unitIntervalCosineHeatPointWeight s x n * a n)
        (unitIntervalCosineHeatSecondPointWeight w x n * a n) w := by
    intro n w _hw
    have hd := (ShenWork.Paper2.unitIntervalCosineHeatPointWeight_hasDerivAt_time x n w).mul_const (a n)
    rwa [← unitIntervalCosineHeatSecondPointWeight_eq_neg_eigenvalue_mul] at hd
  -- (hf') uniform bound on `s`.
  have hf' : ∀ n : ℕ, ∀ w ∈ s,
      ‖unitIntervalCosineHeatSecondPointWeight w x n * a n‖ ≤ u n := by
    intro n w hw
    have hwpos : 0 < w := lt_trans hr2pos (Set.mem_Ioi.mp hw)
    have hwge : r / 2 ≤ w := le_of_lt (Set.mem_Ioi.mp hw)
    have hMn : |a n| ≤ |M| := le_trans (hM n) (le_abs_self M)
    rw [Real.norm_eq_abs, abs_mul]
    have hbnd := unitIntervalCosineHeatSecondPointWeight_abs_le hwpos x n
    have hrec_nonneg : (0 : ℝ) ≤ reciprocalSquareTerm n := by
      unfold reciprocalSquareTerm; positivity
    have hCmono : 4 / (w ^ 2 * Real.pi ^ 2) ≤ C := by
      rw [hC_def]
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      have : (r / 2) ^ 2 ≤ w ^ 2 := by nlinarith [hwge, hr2pos]
      nlinarith [this, Real.pi_pos, sq_nonneg Real.pi]
    calc |unitIntervalCosineHeatSecondPointWeight w x n| * |a n|
        ≤ (4 / (w ^ 2 * Real.pi ^ 2) * reciprocalSquareTerm n) * |M| :=
          mul_le_mul hbnd hMn (abs_nonneg _)
            (mul_nonneg (by positivity) hrec_nonneg)
      _ ≤ (C * reciprocalSquareTerm n) * |M| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_right hCmono hrec_nonneg
      _ = u n := by rw [hu_def]
  -- (hf0) the value series converges at `r`.
  have hf0 : Summable (fun n => unitIntervalCosineHeatPointWeight r x n * a n) := by
    apply Summable.of_norm_bounded
      (g := fun n => Real.exp (-r * unitIntervalCosineEigenvalue n) * |M|)
      ((ShenWork.HeatKernelGradientEstimates.unitIntervalCosineHeatTrace_single_exp_summable hr).mul_right |M|)
    intro n
    have hMn : |a n| ≤ |M| := le_trans (hM n) (le_abs_self M)
    rw [Real.norm_eq_abs, abs_mul]
    have hw : |unitIntervalCosineHeatPointWeight r x n| ≤
        Real.exp (-r * unitIntervalCosineEigenvalue n) := by
      unfold unitIntervalCosineHeatPointWeight unitIntervalCosineMode
      rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      calc Real.exp (-r * unitIntervalCosineEigenvalue n) *
              |Real.cos ((n : ℝ) * Real.pi * x)|
          ≤ Real.exp (-r * unitIntervalCosineEigenvalue n) * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_nonneg _)
        _ = Real.exp (-r * unitIntervalCosineEigenvalue n) := by ring
    exact mul_le_mul hw hMn (abs_nonneg _) (Real.exp_nonneg _)
  -- assemble via `hasDerivAt_tsum_of_isPreconnected`.
  have hmain := hasDerivAt_tsum_of_isPreconnected (u := u) (t := s)
    (g := fun n w => unitIntervalCosineHeatPointWeight w x n * a n)
    (g' := fun n w => unitIntervalCosineHeatSecondPointWeight w x n * a n)
    hu_summable isOpen_Ioi (convex_Ioi _).isPreconnected hf hf'
    hr_mem hf0 hr_mem
  simpa [unitIntervalCosineHeatValue, unitIntervalCosineHeatSecondValue] using hmain

/-- **Second spatial derivative of the cosine heat value = the second-derivative
series.**  `∂ₓₓ(unitIntervalCosineHeatValue r a)(x) = unitIntervalCosineHeatSecondValue
r a x`.  Composes the two existing first-derivative identities (`deriv value =
gradientValue`, `deriv gradientValue = secondValue`). -/
theorem unitIntervalCosineHeatValue_spatial_second_deriv
    {r x : ℝ} (hr : 0 < r) {a : ℕ → ℝ} {M : ℝ} (hM : ∀ n, |a n| ≤ M) :
    deriv (fun y : ℝ => deriv (fun z : ℝ => unitIntervalCosineHeatValue r a z) y) x =
      unitIntervalCosineHeatSecondValue r a x := by
  have hderiv_eq :
      (fun y : ℝ => deriv (fun z : ℝ => unitIntervalCosineHeatValue r a z) y)
        = fun y : ℝ => unitIntervalCosineHeatGradientValue r a y := by
    funext y; exact unitIntervalCosineHeatValue_deriv_eq_gradientValue hr hM y
  rw [hderiv_eq]
  exact unitIntervalCosineHeatGradientValue_deriv hr hM x

/-- **Spectral heat identity (the heat equation, cosine-value form).**  For `r > 0`
and bounded coefficients, the second spatial derivative equals the time derivative of
`unitIntervalCosineHeatValue`:

  `∂ₓₓ (S(r) value)(x) = ∂ᵣ (S(r) value)(x)`,

both equal to `unitIntervalCosineHeatSecondValue r a x`.  This is Lemma 2 of the
time-IBP route — the identity `∂ₓₓ S(r) = ∂ᵣ S(r)` driving the time integration by
parts. -/
theorem unitIntervalCosineHeatValue_heat_identity
    {r x : ℝ} (hr : 0 < r) {a : ℕ → ℝ} {M : ℝ} (hM : ∀ n, |a n| ≤ M) :
    deriv (fun y : ℝ => deriv (fun z : ℝ => unitIntervalCosineHeatValue r a z) y) x =
      deriv (fun s : ℝ => unitIntervalCosineHeatValue s a x) r := by
  rw [unitIntervalCosineHeatValue_spatial_second_deriv hr hM,
    (unitIntervalCosineHeatValue_hasDerivAt_time hr hM).deriv]

/-! ## Step 3 — the time chain rule `d/ds[S(t−s)g(s)]`

The Duhamel integrand `Φ(s) = S(t−s)g(s)(x)` is, spectrally,
`∑'ₙ e^{−(t−s)λₙ}cos(nπx)·ĝₙ(s)`.  Its `s`-derivative is a genuine two-variable
chain rule (the heat time `t−s` AND the coefficients `ĝ(s)` both move with `s`),
proved by termwise product rule + dominated differentiation (`hasDerivAt_tsum`),
valid away from the `s=t` singularity.  We build it per mode first. -/

/-- **Per-mode reversed-time derivative.**  The point-weight along the *reversed*
time `s ↦ S(t−s)`-mode, `s ↦ e^{−(t−s)λₙ}cos(nπx)`, has `s`-derivative
`−secondPointWeight(t−s₀)` (`= +λₙ e^{−(t−s₀)λₙ}cos`): the heat time-derivative
`−λₙ·pw` composed with `d/ds(t−s) = −1`.  Spectrally this is the integrand of
`−∂ₓₓ S(t−s)` (the first term of the chain rule). -/
theorem unitIntervalCosineHeatPointWeight_sub_hasDerivAt
    (t x : ℝ) (n : ℕ) (s₀ : ℝ) :
    HasDerivAt (fun s : ℝ => unitIntervalCosineHeatPointWeight (t - s) x n)
      (-(unitIntervalCosineHeatSecondPointWeight (t - s₀) x n)) s₀ := by
  have htime :=
    ShenWork.Paper2.unitIntervalCosineHeatPointWeight_hasDerivAt_time x n (t - s₀)
  have hsub : HasDerivAt (fun s : ℝ => t - s) (-1 : ℝ) s₀ := by
    simpa using (hasDerivAt_id s₀).const_sub t
  have hcomp : HasDerivAt (fun s : ℝ => unitIntervalCosineHeatPointWeight (t - s) x n)
      (-(unitIntervalCosineEigenvalue n) *
        unitIntervalCosineHeatPointWeight (t - s₀) x n * (-1)) s₀ :=
    htime.comp s₀ hsub
  rw [unitIntervalCosineHeatSecondPointWeight_eq_neg_eigenvalue_mul]
  convert hcomp using 1
  ring

end ShenWork.IntervalDuhamelClosedC2
