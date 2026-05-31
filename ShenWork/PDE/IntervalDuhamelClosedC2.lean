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
import ShenWork.PDE.IntervalDuhamelSpectralC2
import ShenWork.PDE.CosineSpectrum

open MeasureTheory Filter Topology

noncomputable section

namespace ShenWork.IntervalDuhamelClosedC2

open ShenWork.IntervalDomain ShenWork.IntervalDomainRegularityBootstrap
open ShenWork.IntervalFullKernelRegularity
open ShenWork.CosineSpectrum (cosineMode cosineMode_hasDerivAt cosineMode_deriv cosineMode_second_deriv cosineMode_neumann_left cosineMode_neumann_right)

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

/-- **Per-mode product rule for the Duhamel integrand.**  For a coefficient family
`a : ℝ → ℕ → ℝ` with per-mode time derivative `adot`, the `n`-th integrand mode
`s ↦ e^{−(t−s)λₙ}cos(nπx)·ĝₙ(s)` has `s`-derivative

  `−secondPointWeight(t−s₀)·ĝₙ(s₀)  +  pointWeight(t−s₀)·ĝ′ₙ(s₀)`,

i.e. (the `n`-th term of) `−∂ₓₓ S(t−s)g(s) + S(t−s)∂ₛg(s)`.  Product of the
reversed-time point-weight derivative (3a) and the coefficient derivative. -/
theorem unitIntervalCosineHeatTerm_sub_hasDerivAt
    (t x : ℝ) (n : ℕ) {a adot : ℝ → ℕ → ℝ} {s₀ : ℝ}
    (hda : HasDerivAt (fun s : ℝ => a s n) (adot s₀ n) s₀) :
    HasDerivAt (fun s : ℝ => unitIntervalCosineHeatPointWeight (t - s) x n * a s n)
      (-(unitIntervalCosineHeatSecondPointWeight (t - s₀) x n) * a s₀ n
        + unitIntervalCosineHeatPointWeight (t - s₀) x n * adot s₀ n) s₀ :=
  (unitIntervalCosineHeatPointWeight_sub_hasDerivAt t x n s₀).mul hda

/-- **Step 3 — the time chain rule (assembled).**  For a uniformly bounded
coefficient family `a` with uniformly bounded per-mode time derivative `adot`, the
Duhamel integrand `Φ(s) = S(t−s)g(s)(x) = unitIntervalCosineHeatValue (t−s) (a s) x`
is `s`-differentiable at any interior `s₀ ∈ (0,t)`, with

  `Φ′(s₀) = −∂ₓₓ S(t−s₀)g(s₀)(x) + S(t−s₀)(∂ₛg(s₀))(x)`
         `= −unitIntervalCosineHeatSecondValue (t−s₀) (a s₀) x`
         `   + unitIntervalCosineHeatValue (t−s₀) (adot s₀) x`.

Termwise product rule (3b) + dominated differentiation (`hasDerivAt_tsum_of_isPreconnected`)
on an interval around `s₀` kept away from `s=t` (so `t−s ≥ (t−s₀)/2 > 0`, killing the
singularity).  The majorant is `C·n⁻² + Mdot·e^{−rₘᵢₙλₙ}` (the `−∂ₓₓ` term's
reciprocal-square + the `S(t−s)∂ₛg` term's Gaussian). -/
theorem duhamelIntegrand_hasDerivAt
    {t x : ℝ} {a adot : ℝ → ℕ → ℝ} {M Mdot : ℝ}
    (hbound : ∀ s n, |a s n| ≤ M) (hbound' : ∀ s n, |adot s n| ≤ Mdot)
    (hda : ∀ s n, HasDerivAt (fun σ : ℝ => a σ n) (adot s n) s)
    {s₀ : ℝ} (hs₀lt : s₀ < t) :
    HasDerivAt (fun s : ℝ => unitIntervalCosineHeatValue (t - s) (a s) x)
      (-(unitIntervalCosineHeatSecondValue (t - s₀) (a s₀) x)
        + unitIntervalCosineHeatValue (t - s₀) (adot s₀) x) s₀ := by
  classical
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hbound s₀ 0)
  have hMdotnn : 0 ≤ Mdot := le_trans (abs_nonneg _) (hbound' s₀ 0)
  -- the neighbourhood `(s₀−δ, s₀+δ)` with `δ = (t−s₀)/2` keeps `s` away from `t`
  -- (so `t−s ≥ rmin > 0`); it may dip below `0` — harmless, `a` is defined on all ℝ.
  set rmin : ℝ := (t - s₀) / 2 with hrmin_def
  have hrmin_pos : 0 < rmin := by rw [hrmin_def]; linarith
  set δ : ℝ := (t - s₀) / 2 with hδ_def
  have hδ_pos : 0 < δ := by rw [hδ_def]; linarith
  set S : Set ℝ := Set.Ioo (s₀ - δ) (s₀ + δ) with hS_def
  have hS_open : IsOpen S := isOpen_Ioo
  have hS_conn : IsPreconnected S := (convex_Ioo _ _).isPreconnected
  have hs₀_mem : s₀ ∈ S := by
    rw [hS_def]; exact ⟨by linarith, by linarith⟩
  -- on `S`: `rmin ≤ t − s` (hence `0 < t − s`).
  have hsub_ge : ∀ s ∈ S, rmin ≤ t - s := by
    intro s hs
    have : s < s₀ + δ := hs.2
    rw [hrmin_def, hδ_def] at *; linarith
  have hsub_pos : ∀ s ∈ S, 0 < t - s := fun s hs =>
    lt_of_lt_of_le hrmin_pos (hsub_ge s hs)
  -- the summable majorant.
  set u : ℕ → ℝ := fun n =>
    (4 / (rmin ^ 2 * Real.pi ^ 2) * reciprocalSquareTerm n) * M
      + Real.exp (-rmin * unitIntervalCosineEigenvalue n) * Mdot with hu_def
  have hu_summable : Summable u := by
    refine Summable.add ?_ ?_
    · have := ((reciprocalSquareTerm_summable.mul_left
        (4 / (rmin ^ 2 * Real.pi ^ 2))).mul_right M)
      simpa [mul_assoc] using this
    · exact (ShenWork.HeatKernelGradientEstimates.unitIntervalCosineHeatTrace_single_exp_summable
        hrmin_pos).mul_right Mdot
  -- (hf) per-mode `HasDerivAt` on `S` (3b).
  have hf : ∀ n : ℕ, ∀ s ∈ S,
      HasDerivAt (fun s : ℝ => unitIntervalCosineHeatPointWeight (t - s) x n * a s n)
        (-(unitIntervalCosineHeatSecondPointWeight (t - s) x n) * a s n
          + unitIntervalCosineHeatPointWeight (t - s) x n * adot s n) s :=
    fun n s _hs => unitIntervalCosineHeatTerm_sub_hasDerivAt t x n (hda s n)
  -- (hf') uniform bound on `S`.
  have hf' : ∀ n : ℕ, ∀ s ∈ S,
      ‖-(unitIntervalCosineHeatSecondPointWeight (t - s) x n) * a s n
        + unitIntervalCosineHeatPointWeight (t - s) x n * adot s n‖ ≤ u n := by
    intro n s hs
    have htspos : 0 < t - s := hsub_pos s hs
    have htsge : rmin ≤ t - s := hsub_ge s hs
    have hrec_nonneg : (0 : ℝ) ≤ reciprocalSquareTerm n := by
      unfold reciprocalSquareTerm; positivity
    -- bound term 1: |−second · a| ≤ (4/((t−s)²π²)·recip)·M ≤ (4/(rmin²π²)·recip)·M
    have hb1 : ‖-(unitIntervalCosineHeatSecondPointWeight (t - s) x n) * a s n‖
        ≤ (4 / (rmin ^ 2 * Real.pi ^ 2) * reciprocalSquareTerm n) * M := by
      rw [Real.norm_eq_abs, abs_mul, abs_neg]
      have hsb := unitIntervalCosineHeatSecondPointWeight_abs_le htspos x n
      have hCmono : 4 / ((t - s) ^ 2 * Real.pi ^ 2) ≤ 4 / (rmin ^ 2 * Real.pi ^ 2) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        have : rmin ^ 2 ≤ (t - s) ^ 2 := by nlinarith [htsge, hrmin_pos.le]
        nlinarith [this, Real.pi_pos, sq_nonneg Real.pi]
      calc |unitIntervalCosineHeatSecondPointWeight (t - s) x n| * |a s n|
          ≤ (4 / ((t - s) ^ 2 * Real.pi ^ 2) * reciprocalSquareTerm n) * M :=
            mul_le_mul hsb (hbound s n) (abs_nonneg _)
              (mul_nonneg (by positivity) hrec_nonneg)
        _ ≤ (4 / (rmin ^ 2 * Real.pi ^ 2) * reciprocalSquareTerm n) * M := by
            apply mul_le_mul_of_nonneg_right _ hMnn
            exact mul_le_mul_of_nonneg_right hCmono hrec_nonneg
    -- bound term 2: |pw · adot| ≤ e^{−(t−s)λ}·Mdot ≤ e^{−rmin λ}·Mdot
    have hb2 : ‖unitIntervalCosineHeatPointWeight (t - s) x n * adot s n‖
        ≤ Real.exp (-rmin * unitIntervalCosineEigenvalue n) * Mdot := by
      rw [Real.norm_eq_abs, abs_mul]
      have hpw : |unitIntervalCosineHeatPointWeight (t - s) x n|
          ≤ Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) := by
        unfold unitIntervalCosineHeatPointWeight unitIntervalCosineMode
        rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
        calc Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) *
                |Real.cos ((n : ℝ) * Real.pi * x)|
            ≤ Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * 1 :=
              mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_nonneg _)
          _ = Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) := by ring
      have hexpmono : Real.exp (-(t - s) * unitIntervalCosineEigenvalue n)
          ≤ Real.exp (-rmin * unitIntervalCosineEigenvalue n) := by
        apply Real.exp_le_exp.mpr
        have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
          unfold unitIntervalCosineEigenvalue; positivity
        nlinarith [htsge, hlam]
      calc |unitIntervalCosineHeatPointWeight (t - s) x n| * |adot s n|
          ≤ Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * Mdot :=
            mul_le_mul hpw (hbound' s n) (abs_nonneg _) (Real.exp_nonneg _)
        _ ≤ Real.exp (-rmin * unitIntervalCosineEigenvalue n) * Mdot :=
            mul_le_mul_of_nonneg_right hexpmono hMdotnn
    calc ‖-(unitIntervalCosineHeatSecondPointWeight (t - s) x n) * a s n
            + unitIntervalCosineHeatPointWeight (t - s) x n * adot s n‖
        ≤ ‖-(unitIntervalCosineHeatSecondPointWeight (t - s) x n) * a s n‖
            + ‖unitIntervalCosineHeatPointWeight (t - s) x n * adot s n‖ :=
          norm_add_le _ _
      _ ≤ u n := by rw [hu_def]; exact add_le_add hb1 hb2
  -- (hf0) the value series converges at `s₀`.
  have hf0 : Summable (fun n => unitIntervalCosineHeatPointWeight (t - s₀) x n * a s₀ n) := by
    have hts₀ : 0 < t - s₀ := by linarith
    apply Summable.of_norm_bounded
      (g := fun n => Real.exp (-(t - s₀) * unitIntervalCosineEigenvalue n) * M)
      ((ShenWork.HeatKernelGradientEstimates.unitIntervalCosineHeatTrace_single_exp_summable
        hts₀).mul_right M)
    intro n
    rw [Real.norm_eq_abs, abs_mul]
    have hpw : |unitIntervalCosineHeatPointWeight (t - s₀) x n|
        ≤ Real.exp (-(t - s₀) * unitIntervalCosineEigenvalue n) := by
      unfold unitIntervalCosineHeatPointWeight unitIntervalCosineMode
      rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      calc Real.exp (-(t - s₀) * unitIntervalCosineEigenvalue n) *
              |Real.cos ((n : ℝ) * Real.pi * x)|
          ≤ Real.exp (-(t - s₀) * unitIntervalCosineEigenvalue n) * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_nonneg _)
        _ = Real.exp (-(t - s₀) * unitIntervalCosineEigenvalue n) := by ring
    exact mul_le_mul hpw (hbound s₀ n) (abs_nonneg _) (Real.exp_nonneg _)
  -- assemble.
  have hmain := hasDerivAt_tsum_of_isPreconnected (u := u) (t := S)
    (g := fun n s => unitIntervalCosineHeatPointWeight (t - s) x n * a s n)
    (g' := fun n s => -(unitIntervalCosineHeatSecondPointWeight (t - s) x n) * a s n
      + unitIntervalCosineHeatPointWeight (t - s) x n * adot s n)
    hu_summable hS_open hS_conn hf hf' hs₀_mem hf0 hs₀_mem
  -- identify the limiting tsum with the named values.
  have hts₀ : 0 < t - s₀ := by linarith
  have summ1 : Summable
      (fun n => -(unitIntervalCosineHeatSecondPointWeight (t - s₀) x n) * a s₀ n) := by
    apply Summable.of_norm_bounded
      (g := fun n => (4 / ((t - s₀) ^ 2 * Real.pi ^ 2) * reciprocalSquareTerm n) * M)
      (by
        have := ((reciprocalSquareTerm_summable.mul_left
          (4 / ((t - s₀) ^ 2 * Real.pi ^ 2))).mul_right M)
        simpa [mul_assoc] using this)
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_neg]
    have hrec_nonneg : (0 : ℝ) ≤ reciprocalSquareTerm n := by
      unfold reciprocalSquareTerm; positivity
    exact mul_le_mul (unitIntervalCosineHeatSecondPointWeight_abs_le hts₀ x n)
      (hbound s₀ n) (abs_nonneg _) (mul_nonneg (by positivity) hrec_nonneg)
  have summ2 : Summable
      (fun n => unitIntervalCosineHeatPointWeight (t - s₀) x n * adot s₀ n) := by
    apply Summable.of_norm_bounded
      (g := fun n => Real.exp (-(t - s₀) * unitIntervalCosineEigenvalue n) * Mdot)
      ((ShenWork.HeatKernelGradientEstimates.unitIntervalCosineHeatTrace_single_exp_summable
        hts₀).mul_right Mdot)
    intro n
    rw [Real.norm_eq_abs, abs_mul]
    have hpw : |unitIntervalCosineHeatPointWeight (t - s₀) x n|
        ≤ Real.exp (-(t - s₀) * unitIntervalCosineEigenvalue n) := by
      unfold unitIntervalCosineHeatPointWeight unitIntervalCosineMode
      rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      calc Real.exp (-(t - s₀) * unitIntervalCosineEigenvalue n) *
              |Real.cos ((n : ℝ) * Real.pi * x)|
          ≤ Real.exp (-(t - s₀) * unitIntervalCosineEigenvalue n) * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_nonneg _)
        _ = Real.exp (-(t - s₀) * unitIntervalCosineEigenvalue n) := by ring
    exact mul_le_mul hpw (hbound' s₀ n) (abs_nonneg _) (Real.exp_nonneg _)
  have hval : (∑' n, (-(unitIntervalCosineHeatSecondPointWeight (t - s₀) x n) * a s₀ n
        + unitIntervalCosineHeatPointWeight (t - s₀) x n * adot s₀ n))
      = -(unitIntervalCosineHeatSecondValue (t - s₀) (a s₀) x)
        + unitIntervalCosineHeatValue (t - s₀) (adot s₀) x := by
    have e1 : (∑' n, -(unitIntervalCosineHeatSecondPointWeight (t - s₀) x n) * a s₀ n)
        = -(unitIntervalCosineHeatSecondValue (t - s₀) (a s₀) x) := by
      rw [unitIntervalCosineHeatSecondValue, ← tsum_neg]
      apply tsum_congr; intro n; ring
    have e2 : (∑' n, unitIntervalCosineHeatPointWeight (t - s₀) x n * adot s₀ n)
        = unitIntervalCosineHeatValue (t - s₀) (adot s₀) x := rfl
    rw [Summable.tsum_add summ1 summ2, e1, e2]
  rw [hval] at hmain
  exact hmain

/-! ## Step 4 — cutoff fundamental theorem of calculus on `[0, t−ε]`

Integrating the chain rule (step 3) over `[0, t−ε]` (avoiding the `s=t`
singularity).  Prerequisite: the integrand `Φ′` is continuous on the compact, hence
interval-integrable — proved from uniform convergence (`continuousOn_tsum`), the
time argument `t−s` staying `≥ t−c > 0`. -/

/-- Continuity of `s ↦ ∂ₓₓ S(t−s)g(s)(x) = unitIntervalCosineHeatSecondValue (t−s)
(a s) x` on `Iic c` for `c < t` (where `t−s ≥ t−c > 0`).  Uniform convergence with
the reciprocal-square majorant `4/((t−c)²π²)·n⁻²·M`. -/
theorem unitIntervalCosineHeatSecondValue_comp_sub_continuousOn
    {t x : ℝ} {a : ℝ → ℕ → ℝ} {M : ℝ}
    (hbound : ∀ s n, |a s n| ≤ M) (hcont : ∀ n, Continuous (fun s : ℝ => a s n))
    {c : ℝ} (hc : c < t) :
    ContinuousOn (fun s : ℝ => unitIntervalCosineHeatSecondValue (t - s) (a s) x)
      (Set.Iic c) := by
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hbound c 0)
  refine continuousOn_tsum
    (u := fun n => 4 / ((t - c) ^ 2 * Real.pi ^ 2) * reciprocalSquareTerm n * M)
    (fun n => ?_) ?_ (fun n s hs => ?_)
  · apply Continuous.continuousOn
    have hpw : Continuous
        (fun s : ℝ => unitIntervalCosineHeatSecondPointWeight (t - s) x n) := by
      unfold unitIntervalCosineHeatSecondPointWeight; fun_prop
    exact hpw.mul (hcont n)
  · have := ((reciprocalSquareTerm_summable.mul_left
      (4 / ((t - c) ^ 2 * Real.pi ^ 2))).mul_right M)
    simpa [mul_assoc] using this
  · have hsc : s ≤ c := hs
    have htspos : 0 < t - s := by linarith
    rw [Real.norm_eq_abs, abs_mul]
    have hsb := unitIntervalCosineHeatSecondPointWeight_abs_le htspos x n
    have hrec_nonneg : (0 : ℝ) ≤ reciprocalSquareTerm n := by
      unfold reciprocalSquareTerm; positivity
    have htc : (0 : ℝ) < t - c := by linarith
    have hCmono : 4 / ((t - s) ^ 2 * Real.pi ^ 2)
        ≤ 4 / ((t - c) ^ 2 * Real.pi ^ 2) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      have hsq : (t - c) ^ 2 ≤ (t - s) ^ 2 := by nlinarith [hsc, hc]
      nlinarith [hsq, sq_nonneg Real.pi]
    calc |unitIntervalCosineHeatSecondPointWeight (t - s) x n| * |a s n|
        ≤ (4 / ((t - s) ^ 2 * Real.pi ^ 2) * reciprocalSquareTerm n) * M :=
          mul_le_mul hsb (hbound s n) (abs_nonneg _)
            (mul_nonneg (by positivity) hrec_nonneg)
      _ ≤ (4 / ((t - c) ^ 2 * Real.pi ^ 2) * reciprocalSquareTerm n) * M := by
          apply mul_le_mul_of_nonneg_right _ hMnn
          exact mul_le_mul_of_nonneg_right hCmono hrec_nonneg

/-- Continuity of `s ↦ S(t−s)g(s)(x) = unitIntervalCosineHeatValue (t−s) (a s) x` on
`Iic c` for `c < t`.  Uniform convergence with the Gaussian majorant
`e^{−(t−c)λₙ}·M`. -/
theorem unitIntervalCosineHeatValue_comp_sub_continuousOn
    {t x : ℝ} {a : ℝ → ℕ → ℝ} {M : ℝ}
    (hbound : ∀ s n, |a s n| ≤ M) (hcont : ∀ n, Continuous (fun s : ℝ => a s n))
    {c : ℝ} (hc : c < t) :
    ContinuousOn (fun s : ℝ => unitIntervalCosineHeatValue (t - s) (a s) x)
      (Set.Iic c) := by
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hbound c 0)
  have htc : (0 : ℝ) < t - c := by linarith
  refine continuousOn_tsum
    (u := fun n => Real.exp (-(t - c) * unitIntervalCosineEigenvalue n) * M)
    (fun n => ?_) ?_ (fun n s hs => ?_)
  · apply Continuous.continuousOn
    have hpw : Continuous
        (fun s : ℝ => unitIntervalCosineHeatPointWeight (t - s) x n) := by
      unfold unitIntervalCosineHeatPointWeight unitIntervalCosineMode; fun_prop
    exact hpw.mul (hcont n)
  · exact (ShenWork.HeatKernelGradientEstimates.unitIntervalCosineHeatTrace_single_exp_summable
      htc).mul_right M
  · have hsc : s ≤ c := hs
    have htspos : 0 < t - s := by linarith
    rw [Real.norm_eq_abs, abs_mul]
    have hpw : |unitIntervalCosineHeatPointWeight (t - s) x n|
        ≤ Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) := by
      unfold unitIntervalCosineHeatPointWeight unitIntervalCosineMode
      rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      calc Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) *
              |Real.cos ((n : ℝ) * Real.pi * x)|
          ≤ Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_nonneg _)
        _ = Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) := by ring
    have hexpmono : Real.exp (-(t - s) * unitIntervalCosineEigenvalue n)
        ≤ Real.exp (-(t - c) * unitIntervalCosineEigenvalue n) := by
      apply Real.exp_le_exp.mpr
      have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
        unfold unitIntervalCosineEigenvalue; positivity
      nlinarith [hsc, hlam]
    calc |unitIntervalCosineHeatPointWeight (t - s) x n| * |a s n|
        ≤ Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * M :=
          mul_le_mul hpw (hbound s n) (abs_nonneg _) (Real.exp_nonneg _)
      _ ≤ Real.exp (-(t - c) * unitIntervalCosineEigenvalue n) * M :=
          mul_le_mul_of_nonneg_right hexpmono hMnn

/-- **Step 4 — cutoff FTC.**  Integrating the chain rule (step 3) over `[0, t−ε]`:

  `∫₀^{t−ε} (−∂ₓₓS(t−s)g(s) + S(t−s)∂ₛg(s))(x) ds = S(ε)g(t−ε)(x) − S(t)g(0)(x)`,

i.e. `∫₀^{t−ε} (−secondValue(t−s)(a s) + value(t−s)(adot s)) = value ε (a(t−ε)) −
value t (a 0)`.  `integral_eq_sub_of_hasDerivAt` with step 3 (`s ≤ t−ε < t`) and the
integrand continuous on the compact (steps-4 continuity lemmas). -/
theorem duhamelCutoff_FTC
    {t x : ℝ} {a adot : ℝ → ℕ → ℝ} {M Mdot : ℝ}
    (hbound : ∀ s n, |a s n| ≤ M) (hbound' : ∀ s n, |adot s n| ≤ Mdot)
    (hda : ∀ s n, HasDerivAt (fun σ : ℝ => a σ n) (adot s n) s)
    (hadotcont : ∀ n, Continuous (fun s : ℝ => adot s n))
    {ε : ℝ} (hε : 0 < ε) (hεt : ε ≤ t) :
    (∫ s in (0:ℝ)..(t - ε), (-(unitIntervalCosineHeatSecondValue (t - s) (a s) x)
        + unitIntervalCosineHeatValue (t - s) (adot s) x))
      = unitIntervalCosineHeatValue ε (a (t - ε)) x
        - unitIntervalCosineHeatValue t (a 0) x := by
  have hac : ∀ n, Continuous (fun s : ℝ => a s n) :=
    fun n => continuous_iff_continuousAt.2 (fun s => (hda s n).continuousAt)
  have hle : (0 : ℝ) ≤ t - ε := by linarith
  have hctlt : t - ε < t := by linarith
  -- hypotheses for the FTC.
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) (t - ε),
      HasDerivAt (fun s : ℝ => unitIntervalCosineHeatValue (t - s) (a s) x)
        (-(unitIntervalCosineHeatSecondValue (t - s) (a s) x)
          + unitIntervalCosineHeatValue (t - s) (adot s) x) s := by
    intro s hs
    rw [Set.uIcc_of_le hle] at hs
    exact duhamelIntegrand_hasDerivAt hbound hbound' hda (by linarith [hs.2])
  have hsub : Set.uIcc (0 : ℝ) (t - ε) ⊆ Set.Iic (t - ε) := by
    rw [Set.uIcc_of_le hle]; exact fun s hs => hs.2
  have hint : IntervalIntegrable
      (fun s : ℝ => -(unitIntervalCosineHeatSecondValue (t - s) (a s) x)
        + unitIntervalCosineHeatValue (t - s) (adot s) x) volume 0 (t - ε) := by
    apply ContinuousOn.intervalIntegrable
    refine (((unitIntervalCosineHeatSecondValue_comp_sub_continuousOn
      hbound hac hctlt).neg).add
      (unitIntervalCosineHeatValue_comp_sub_continuousOn hbound' hadotcont hctlt)).mono hsub
  have hΦ := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hΦ]
  norm_num

/-! ## Step 5 (ε→0) — precise remaining sub-problems (for the next Lean statements)

Steps 1–4 are DONE.  Taking `ε→0⁺` in `duhamelCutoff_FTC` to reach

  `lim_{ε→0} ∫₀^{t−ε} ∂ₓₓS(t−s)g(s)(x) ds = S(t)g(0)(x) − g(t)(x)
      + ∫₀ᵗ S(t−s)∂ₛg(s)(x) ds`   (= R(x))

requires two genuine sub-lemmas, NOT yet trivial from what is built:

**(5a) Joint approximate-identity limit** `S(ε)g(t−ε)(x) → g(t)(x)` as `ε↓0`.
Both the time `ε→0` AND the coefficients `a(t−ε)→a(t)` move.  The repo's
`intervalFullSemigroup_tendsto_id_at_zero` handles `S(ε)f→f(x)` for a *fixed* `f`.
Split `S(ε)g(t−ε) − g(t) = S(ε)(g(t−ε)−g(t)) + (S(ε)g(t) − g(t))`:
* second term `→ 0` by the fixed-`f` approx identity at `f = g(t)`;
* first term `→ 0` by the semigroup `L∞` contraction
  (`intervalFullSemigroupOperator_Linfty_bound`, T2) applied to `g(t−ε)−g(t)`,
  whose sup-norm `→ 0` by time-continuity of `g` (an input of the
  `DuhamelSourceTimeC1` predicate).
At the cosine-value level this is `unitIntervalCosineHeatValue ε (a(t−ε)) x →
∑'ₙ cos(nπx)·(a t n) = g(t)(x)`, needing the pointwise cosine reconstruction of
`g(t)` (`hrecon`-type, ℓ¹ coeffs) — a faithful source-regularity input.

**(5b) Improper → Lebesgue integral** `lim_{ε→0} ∫₀^{t−ε} value(t−s)(adot s) x ds
= ∫₀ᵗ value(t−s)(adot s) x ds`.  The integrand `S(t−s)∂ₛg(s)(x)` is bounded on
`[0,t)` by the semigroup contraction `≤ ‖∂ₛg(s)‖_∞` (NOT by the coefficient series
majorant `Mdot·∑e^{−(t−s)λₙ}`, which blows up as `s→t`).  Hence it is
interval-integrable on `[0,t]`, and `ε ↦ ∫₀^{t−ε}` is continuous in `ε` at `0`
(integral continuous in its endpoint).  Needs: the operator `L∞` bound bridged to
the cosine-value form, and `intervalIntegral` endpoint-continuity.

The secondValue side (`∫₀^{t−ε} secondValue`) is the *improper* limit only — its
integrand is genuinely singular `~(t−s)^{−3/2}` and NOT Lebesgue-integrable on
`[0,t]`; that is exactly why the IBP form (RHS) is needed.  The final
`intervalDuhamelTerm_closedC2_of_timeC1_source` (steps 6–7) consumes `R` as the
`∂ₓₓ` candidate; `R` is continuous in `x` (step 6) — each summand is, and the
`∫₀ᵗ value(t−s)(adot s) ·` term is continuous by dominated convergence. -/

/-- **Step 5a — rearranged cutoff formula.**  Isolating the `∂ₓₓ`-integral:

  `∫₀^{t−ε} ∂ₓₓS(t−s)g(s)(x) ds = S(t)g(0)(x) − S(ε)g(t−ε)(x)
      + ∫₀^{t−ε} S(t−s)∂ₛg(s)(x) ds`,

i.e. `∫₀^{t−ε} secondValue(t−s)(a s) = value t (a 0) − value ε (a(t−ε)) +
∫₀^{t−ε} value(t−s)(adot s)`.  Pure rearrangement of `duhamelCutoff_FTC` (linearity
of the integral + both pieces interval-integrable). -/
theorem duhamelCutoff_secondValue_eq
    {t x : ℝ} {a adot : ℝ → ℕ → ℝ} {M Mdot : ℝ}
    (hbound : ∀ s n, |a s n| ≤ M) (hbound' : ∀ s n, |adot s n| ≤ Mdot)
    (hda : ∀ s n, HasDerivAt (fun σ : ℝ => a σ n) (adot s n) s)
    (hadotcont : ∀ n, Continuous (fun s : ℝ => adot s n))
    {ε : ℝ} (hε : 0 < ε) (hεt : ε ≤ t) :
    (∫ s in (0:ℝ)..(t - ε), unitIntervalCosineHeatSecondValue (t - s) (a s) x)
      = unitIntervalCosineHeatValue t (a 0) x
        - unitIntervalCosineHeatValue ε (a (t - ε)) x
        + ∫ s in (0:ℝ)..(t - ε), unitIntervalCosineHeatValue (t - s) (adot s) x := by
  have hac : ∀ n, Continuous (fun s : ℝ => a s n) :=
    fun n => continuous_iff_continuousAt.2 (fun s => (hda s n).continuousAt)
  have hle : (0 : ℝ) ≤ t - ε := by linarith
  have hctlt : t - ε < t := by linarith
  have hsub : Set.uIcc (0 : ℝ) (t - ε) ⊆ Set.Iic (t - ε) := by
    rw [Set.uIcc_of_le hle]; exact fun s hs => hs.2
  have hint_second : IntervalIntegrable
      (fun s => unitIntervalCosineHeatSecondValue (t - s) (a s) x) volume 0 (t - ε) :=
    ((unitIntervalCosineHeatSecondValue_comp_sub_continuousOn hbound hac hctlt).mono
      hsub).intervalIntegrable
  have hint_value : IntervalIntegrable
      (fun s => unitIntervalCosineHeatValue (t - s) (adot s) x) volume 0 (t - ε) :=
    ((unitIntervalCosineHeatValue_comp_sub_continuousOn hbound' hadotcont hctlt).mono
      hsub).intervalIntegrable
  have hFTC := duhamelCutoff_FTC (x := x) hbound hbound' hda hadotcont hε hεt
  have hadd : (∫ s in (0:ℝ)..(t - ε),
        (-(unitIntervalCosineHeatSecondValue (t - s) (a s) x)
          + unitIntervalCosineHeatValue (t - s) (adot s) x))
      = (∫ s in (0:ℝ)..(t - ε), -(unitIntervalCosineHeatSecondValue (t - s) (a s) x))
        + ∫ s in (0:ℝ)..(t - ε), unitIntervalCosineHeatValue (t - s) (adot s) x :=
    intervalIntegral.integral_add hint_second.neg hint_value
  have hneg : (∫ s in (0:ℝ)..(t - ε), -(unitIntervalCosineHeatSecondValue (t - s) (a s) x))
      = -(∫ s in (0:ℝ)..(t - ε), unitIntervalCosineHeatSecondValue (t - s) (a s) x) := by
    rw [intervalIntegral.integral_neg]
  linarith [hFTC, hadd, hneg]

/-- **Step 5 (limit assembly).**  Taking `ε→0⁺` in `duhamelCutoff_secondValue_eq`,
the cutoff `∂ₓₓ`-integral converges to the closed-form candidate

  `P(t)(x) = S(t)g(0)(x) − g(t)(x) + ∫₀ᵗ S(t−s)∂ₛg(s)(x) ds`
         `= value t (a 0) x − gt + Ig`,

GIVEN the two analytic-frontier convergences (the honest step-5 inputs, NOT hidden):
* `hconv1` — the joint approximate-identity limit `S(ε)g(t−ε)(x) → g(t)(x)` (= `gt`);
* `hconv2` — the improper→Lebesgue integral limit `∫₀^{t−ε} S(t−s)∂ₛg → ∫₀ᵗ … = Ig`.
The assembly itself is pure `Tendsto` algebra over the rearranged cutoff formula. -/
theorem duhamelSecondValue_tendsto
    {t x : ℝ} {a adot : ℝ → ℕ → ℝ} {M Mdot : ℝ}
    (hbound : ∀ s n, |a s n| ≤ M) (hbound' : ∀ s n, |adot s n| ≤ Mdot)
    (hda : ∀ s n, HasDerivAt (fun σ : ℝ => a σ n) (adot s n) s)
    (hadotcont : ∀ n, Continuous (fun s : ℝ => adot s n)) (ht : 0 < t)
    {gt Ig : ℝ}
    (hconv1 : Tendsto (fun ε => unitIntervalCosineHeatValue ε (a (t - ε)) x)
      (𝓝[>] (0:ℝ)) (𝓝 gt))
    (hconv2 : Tendsto
      (fun ε => ∫ s in (0:ℝ)..(t - ε), unitIntervalCosineHeatValue (t - s) (adot s) x)
      (𝓝[>] (0:ℝ)) (𝓝 Ig)) :
    Tendsto
      (fun ε => ∫ s in (0:ℝ)..(t - ε), unitIntervalCosineHeatSecondValue (t - s) (a s) x)
      (𝓝[>] (0:ℝ))
      (𝓝 (unitIntervalCosineHeatValue t (a 0) x - gt + Ig)) := by
  have hmem : Set.Ioc (0:ℝ) t ∈ 𝓝[>] (0:ℝ) := by
    have : Set.Ioi (0:ℝ) ∩ Set.Iic t ∈ 𝓝[>] (0:ℝ) :=
      inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iic_mem_nhds ht))
    simpa [Set.Ioc, Set.Ioi, Set.Iic, Set.inter_def] using this
  have heq : (fun ε => ∫ s in (0:ℝ)..(t - ε),
        unitIntervalCosineHeatSecondValue (t - s) (a s) x)
      =ᶠ[𝓝[>] (0:ℝ)]
      (fun ε => unitIntervalCosineHeatValue t (a 0) x
        - unitIntervalCosineHeatValue ε (a (t - ε)) x
        + ∫ s in (0:ℝ)..(t - ε), unitIntervalCosineHeatValue (t - s) (adot s) x) := by
    filter_upwards [hmem] with ε hε
    exact duhamelCutoff_secondValue_eq hbound hbound' hda hadotcont hε.1 hε.2
  rw [tendsto_congr' heq]
  exact (tendsto_const_nhds.sub hconv1).add hconv2

/-! ## Step 5 — discharging `hconv2` (improper → Lebesgue, spectral form)

`hconv2` is proved WITHOUT the operator contraction, via the per-mode structure
`F(s) = ∑'ₙ fₙ(s)`, `fₙ(s) = e^{−(t−s)λₙ}cos(nπx)·ĝₙ′(s)`.  The L¹-norm series is
summable by the parabolic gain `λₙ ∫₀ᵗ e^{−(t−s)λₙ} ≤ 1` (`parabolicGain_le_one`),
so `∫₀^b F = ∑'ₙ ∫₀^b fₙ` and a dominated tsum-convergence gives the limit. -/

/-- **Per-mode `L¹`-norm summability.**  `∑'ₙ ∫₀ᵗ ‖e^{−(t−s)λₙ}cos(nπx)·ĝₙ′(s)‖ ds <
∞`: each term is `≤ Mdot·∫₀ᵗ e^{−(t−s)λₙ} ds ≤ Mdot/λₙ` (parabolic gain), summable
by comparison with `∑ 1/n²`.  This is the L¹ control that makes the Duhamel
`∂ₛg`-integrand an honest `∑∫ = ∫∑` series. -/
theorem duhamelMode_integralNorm_summable
    {t x : ℝ} {adot : ℝ → ℕ → ℝ} {Mdot : ℝ} (ht : 0 < t)
    (hbound' : ∀ s n, |adot s n| ≤ Mdot)
    (hadotcont : ∀ n, Continuous (fun s : ℝ => adot s n)) :
    Summable (fun n => ∫ s in (0:ℝ)..t,
      ‖unitIntervalCosineHeatPointWeight (t - s) x n * adot s n‖) := by
  have hMdotnn : 0 ≤ Mdot := le_trans (abs_nonneg _) (hbound' 0 0)
  set E : ℕ → ℝ := fun n => ∫ s in (0:ℝ)..t,
    Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) with hE_def
  -- `0 ≤ E n`.
  have hEnn : ∀ n, 0 ≤ E n := by
    intro n
    apply intervalIntegral.integral_nonneg (le_of_lt ht)
    intro s _; exact (Real.exp_nonneg _)
  -- per-mode: `∫₀ᵗ‖fₙ‖ ≤ Mdot·E n`.
  have hcn_le : ∀ n, (∫ s in (0:ℝ)..t,
      ‖unitIntervalCosineHeatPointWeight (t - s) x n * adot s n‖) ≤ Mdot * E n := by
    intro n
    have hkernel : Continuous
        (fun s : ℝ => unitIntervalCosineHeatPointWeight (t - s) x n) := by
      unfold unitIntervalCosineHeatPointWeight unitIntervalCosineMode; fun_prop
    have hII1 : IntervalIntegrable
        (fun s => ‖unitIntervalCosineHeatPointWeight (t - s) x n * adot s n‖) volume 0 t :=
      ((hkernel.mul (hadotcont n)).norm).intervalIntegrable 0 t
    have hII2 : IntervalIntegrable
        (fun s => Mdot * Real.exp (-(t - s) * unitIntervalCosineEigenvalue n)) volume 0 t := by
      apply Continuous.intervalIntegrable; fun_prop
    rw [hE_def, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (le_of_lt ht) hII1 hII2
    intro s _
    rw [Real.norm_eq_abs, abs_mul]
    have hpw : |unitIntervalCosineHeatPointWeight (t - s) x n|
        ≤ Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) := by
      unfold unitIntervalCosineHeatPointWeight unitIntervalCosineMode
      rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      calc Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) *
              |Real.cos ((n : ℝ) * Real.pi * x)|
          ≤ Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_nonneg _)
        _ = Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) := by ring
    calc |unitIntervalCosineHeatPointWeight (t - s) x n| * |adot s n|
        ≤ Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * Mdot :=
          mul_le_mul hpw (hbound' s n) (abs_nonneg _) (Real.exp_nonneg _)
      _ = Mdot * Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) := by ring
  -- `Summable (Mdot·E)` by parabolic gain `E n ≤ 1/λₙ` (n≥1).
  have hmaj : Summable (fun n => Mdot * E n) := by
    have hgsum : Summable
        (fun n : ℕ => Mdot * (1 / Real.pi ^ 2) * (1 / ((n : ℝ) + 1) ^ 2)) := by
      have hp2 : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
        have := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
        simpa using (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).2 this
      exact hp2.mul_left (Mdot * (1 / Real.pi ^ 2))
    have htail : Summable (fun n => Mdot * E (n + 1)) := by
      refine Summable.of_nonneg_of_le
        (fun n => mul_nonneg hMdotnn (hEnn (n + 1))) (fun n => ?_) hgsum
      have hlam_pos : 0 < unitIntervalCosineEigenvalue (n + 1) := by
        unfold unitIntervalCosineEigenvalue
        have : (0:ℝ) < ((n : ℝ) + 1) := by positivity
        positivity
      have hgain := ShenWork.IntervalDuhamelRegularity.parabolicGain_le_one (lam := unitIntervalCosineEigenvalue (n + 1))
        (t := t) hlam_pos.le ht.le
      have hElt : E (n + 1) ≤ 1 / unitIntervalCosineEigenvalue (n + 1) := by
        rw [le_div_iff₀ hlam_pos]
        calc E (n + 1) * unitIntervalCosineEigenvalue (n + 1)
            = unitIntervalCosineEigenvalue (n + 1) * E (n + 1) := by ring
          _ ≤ 1 := hgain
      have hlam_eq : unitIntervalCosineEigenvalue (n + 1)
          = ((n : ℝ) + 1) ^ 2 * Real.pi ^ 2 := by
        unfold unitIntervalCosineEigenvalue; push_cast; ring
      calc Mdot * E (n + 1) ≤ Mdot * (1 / unitIntervalCosineEigenvalue (n + 1)) :=
            mul_le_mul_of_nonneg_left hElt hMdotnn
        _ = Mdot * (1 / Real.pi ^ 2) * (1 / ((n : ℝ) + 1) ^ 2) := by
            rw [hlam_eq]; field_simp; try ring
    exact (summable_nat_add_iff (f := fun n => Mdot * E n) 1).mp htail
  exact Summable.of_nonneg_of_le
    (fun n => intervalIntegral.integral_nonneg (le_of_lt ht) (fun s _ => norm_nonneg _))
    hcn_le hmaj

/-- **Per-mode improper-integral continuity.**  `∫₀^{t−ε} fₙ → ∫₀ᵗ fₙ` as `ε↓0`,
where `fₙ(s) = e^{−(t−s)λₙ}cos(nπx)·ĝₙ′(s)` is continuous (on all of `ℝ`), so its
primitive is continuous and composes with `ε↦t−ε`. -/
theorem duhamelMode_primitive_tendsto
    {t x : ℝ} {adot : ℝ → ℕ → ℝ} (n : ℕ)
    (hadotcont : Continuous (fun s : ℝ => adot s n)) :
    Tendsto (fun ε => ∫ s in (0:ℝ)..(t - ε),
        unitIntervalCosineHeatPointWeight (t - s) x n * adot s n)
      (𝓝[>] (0:ℝ))
      (𝓝 (∫ s in (0:ℝ)..t,
        unitIntervalCosineHeatPointWeight (t - s) x n * adot s n)) := by
  have hfcont : Continuous
      (fun s : ℝ => unitIntervalCosineHeatPointWeight (t - s) x n * adot s n) := by
    have hkernel : Continuous
        (fun s : ℝ => unitIntervalCosineHeatPointWeight (t - s) x n) := by
      unfold unitIntervalCosineHeatPointWeight unitIntervalCosineMode; fun_prop
    exact hkernel.mul hadotcont
  have hprim : Continuous (fun b : ℝ => ∫ s in (0:ℝ)..b,
      unitIntervalCosineHeatPointWeight (t - s) x n * adot s n) :=
    intervalIntegral.continuous_primitive
      (fun a b => hfcont.intervalIntegrable a b) 0
  have hsub : Tendsto (fun ε : ℝ => t - ε) (𝓝[>] (0:ℝ)) (𝓝 t) := by
    have h0 : Tendsto (fun ε : ℝ => t - ε) (𝓝 (0:ℝ)) (𝓝 (t - 0)) :=
      (continuous_const.sub continuous_id).tendsto 0
    simpa using h0.mono_left nhdsWithin_le_nhds
  simpa using (hprim.tendsto t).comp hsub

/-- **Spectral form of the Duhamel `∂ₛg`-integral.**  `∫₀^b S(t−s)∂ₛg(s)(x) ds =
∑'ₙ ∫₀^b fₙ` for `0 ≤ b ≤ t` — the `∑∫=∫∑` swap, valid since `∑'ₙ ∫‖fₙ‖ < ∞`
(`duhamelMode_integralNorm_summable`).  No closed-`[0,t]` integrability of the full
sum is needed; everything is per-mode on the finite interval. -/
theorem duhamelValue_adot_eq_tsum
    {t x : ℝ} {adot : ℝ → ℕ → ℝ} {Mdot : ℝ} (ht : 0 < t)
    (hbound' : ∀ s n, |adot s n| ≤ Mdot)
    (hadotcont : ∀ n, Continuous (fun s : ℝ => adot s n))
    {b : ℝ} (hb0 : 0 ≤ b) (hbt : b ≤ t) :
    (∫ s in (0:ℝ)..b, unitIntervalCosineHeatValue (t - s) (adot s) x)
      = ∑' n, ∫ s in (0:ℝ)..b,
        unitIntervalCosineHeatPointWeight (t - s) x n * adot s n := by
  have hfcont : ∀ n, Continuous
      (fun s : ℝ => unitIntervalCosineHeatPointWeight (t - s) x n * adot s n) := by
    intro n
    have hk : Continuous (fun s : ℝ => unitIntervalCosineHeatPointWeight (t - s) x n) := by
      unfold unitIntervalCosineHeatPointWeight unitIntervalCosineMode; fun_prop
    exact hk.mul (hadotcont n)
  have hint : ∀ n, Integrable
      (fun s => unitIntervalCosineHeatPointWeight (t - s) x n * adot s n)
      (volume.restrict (Set.Ioc 0 b)) :=
    fun n => (intervalIntegrable_iff_integrableOn_Ioc_of_le hb0).1
      ((hfcont n).intervalIntegrable 0 b)
  have hsum : Summable (fun n => ∫ s,
      ‖unitIntervalCosineHeatPointWeight (t - s) x n * adot s n‖
      ∂(volume.restrict (Set.Ioc 0 b))) := by
    refine Summable.of_nonneg_of_le
      (fun n => integral_nonneg (fun s => norm_nonneg _)) (fun n => ?_)
      (duhamelMode_integralNorm_summable (x := x) ht hbound' hadotcont)
    rw [← intervalIntegral.integral_of_le hb0]
    refine intervalIntegral.integral_mono_interval (le_refl 0) hb0 hbt ?_ ?_
    · filter_upwards with s using norm_nonneg _
    · exact ((hfcont n).norm).intervalIntegrable 0 t
  have hswap := integral_tsum_of_summable_integral_norm hint hsum
  calc (∫ s in (0:ℝ)..b, unitIntervalCosineHeatValue (t - s) (adot s) x)
      = ∫ s in Set.Ioc 0 b, unitIntervalCosineHeatValue (t - s) (adot s) x :=
        intervalIntegral.integral_of_le hb0
    _ = ∫ s in Set.Ioc 0 b,
          ∑' n, unitIntervalCosineHeatPointWeight (t - s) x n * adot s n := by
        rfl
    _ = ∑' n, ∫ s in Set.Ioc 0 b,
          unitIntervalCosineHeatPointWeight (t - s) x n * adot s n := hswap.symm
    _ = ∑' n, ∫ s in (0:ℝ)..b,
          unitIntervalCosineHeatPointWeight (t - s) x n * adot s n := by
        exact tsum_congr (fun n => (intervalIntegral.integral_of_le hb0).symm)

/-- **`hconv2` discharged.**  The improper Duhamel `∂ₛg`-integral converges
(spectral form): `∫₀^{t−ε} S(t−s)∂ₛg(s)(x) ds → ∑'ₙ ∫₀ᵗ fₙ` as `ε↓0`.  Tannery's
theorem (`tendsto_tsum_of_dominated_convergence`) over the per-mode primitive limits
(`duhamelMode_primitive_tendsto`), dominated by the summable `∫₀ᵗ‖fₙ‖`
(`duhamelMode_integralNorm_summable`), combined with the `∑∫=∫∑` swap. -/
theorem duhamelValue_adot_improper_tendsto
    {t x : ℝ} {adot : ℝ → ℕ → ℝ} {Mdot : ℝ} (ht : 0 < t)
    (hbound' : ∀ s n, |adot s n| ≤ Mdot)
    (hadotcont : ∀ n, Continuous (fun s : ℝ => adot s n)) :
    Tendsto
      (fun ε => ∫ s in (0:ℝ)..(t - ε), unitIntervalCosineHeatValue (t - s) (adot s) x)
      (𝓝[>] (0:ℝ))
      (𝓝 (∑' n, ∫ s in (0:ℝ)..t,
        unitIntervalCosineHeatPointWeight (t - s) x n * adot s n)) := by
  have hmem : Set.Ioc (0:ℝ) t ∈ 𝓝[>] (0:ℝ) := by
    have : Set.Ioi (0:ℝ) ∩ Set.Iic t ∈ 𝓝[>] (0:ℝ) :=
      inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iic_mem_nhds ht))
    simpa [Set.Ioc, Set.Ioi, Set.Iic, Set.inter_def] using this
  have hfcont : ∀ n, Continuous
      (fun s : ℝ => unitIntervalCosineHeatPointWeight (t - s) x n * adot s n) := by
    intro n
    have hk : Continuous (fun s : ℝ => unitIntervalCosineHeatPointWeight (t - s) x n) := by
      unfold unitIntervalCosineHeatPointWeight unitIntervalCosineMode; fun_prop
    exact hk.mul (hadotcont n)
  have htan : Tendsto
      (fun ε => ∑' n, ∫ s in (0:ℝ)..(t - ε),
        unitIntervalCosineHeatPointWeight (t - s) x n * adot s n)
      (𝓝[>] (0:ℝ))
      (𝓝 (∑' n, ∫ s in (0:ℝ)..t,
        unitIntervalCosineHeatPointWeight (t - s) x n * adot s n)) := by
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun n => ∫ s in (0:ℝ)..t,
        ‖unitIntervalCosineHeatPointWeight (t - s) x n * adot s n‖)
      (duhamelMode_integralNorm_summable (x := x) ht hbound' hadotcont)
      (fun n => duhamelMode_primitive_tendsto (x := x) n (hadotcont n)) ?_
    filter_upwards [hmem] with ε hε n
    have hle1 : ‖∫ s in (0:ℝ)..(t - ε),
          unitIntervalCosineHeatPointWeight (t - s) x n * adot s n‖
        ≤ ∫ s in (0:ℝ)..(t - ε),
          ‖unitIntervalCosineHeatPointWeight (t - s) x n * adot s n‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by linarith [hε.2] : (0:ℝ) ≤ t - ε)
    have hle2 : (∫ s in (0:ℝ)..(t - ε),
          ‖unitIntervalCosineHeatPointWeight (t - s) x n * adot s n‖)
        ≤ ∫ s in (0:ℝ)..t,
          ‖unitIntervalCosineHeatPointWeight (t - s) x n * adot s n‖ :=
      intervalIntegral.integral_mono_interval (le_refl 0)
        (by linarith [hε.2]) (by linarith [hε.1])
        (Filter.Eventually.of_forall (fun s => norm_nonneg _))
        (((hfcont n).norm).intervalIntegrable 0 t)
    exact le_trans hle1 hle2
  have heq : (fun ε => ∫ s in (0:ℝ)..(t - ε),
        unitIntervalCosineHeatValue (t - s) (adot s) x)
      =ᶠ[𝓝[>] (0:ℝ)] (fun ε => ∑' n, ∫ s in (0:ℝ)..(t - ε),
        unitIntervalCosineHeatPointWeight (t - s) x n * adot s n) := by
    filter_upwards [hmem] with ε hε
    exact duhamelValue_adot_eq_tsum (x := x) ht hbound' hadotcont
      (by linarith [hε.2]) (by linarith [hε.1])
  rw [tendsto_congr' heq]; exact htan

/-- **`hconv1` discharged (under ℓ¹ source coefficients).**  The joint
approximate-identity limit `S(ε)g(t−ε)(x) → g(t)(x)` as `ε↓0`, where the source has
uniformly-ℓ¹ cosine coefficients (`|a s n| ≤ c n`, `Summable c` — the honest spatial
regularity of `g`).  Tannery's theorem over the per-mode limits
`e^{−ελₙ}cos(nπx)·ĝₙ(t−ε) → cos(nπx)·ĝₙ(t)` (heat factor `→1`, coefficient continuous
in time), dominated by `c n` (`|e^{−ελₙ}cos| ≤ 1`).  The limit
`g(t)(x) = ∑'ₙ cos(nπx)·ĝₙ(t)` is the cosine reconstruction of the source at time `t`. -/
theorem duhamelValue_a_joint_tendsto
    {t x : ℝ} {a : ℝ → ℕ → ℝ} {c : ℕ → ℝ}
    (hacont : ∀ n, Continuous (fun s : ℝ => a s n))
    (hl1 : ∀ s n, |a s n| ≤ c n) (hc_summable : Summable c) :
    Tendsto (fun ε => unitIntervalCosineHeatValue ε (a (t - ε)) x)
      (𝓝[>] (0:ℝ))
      (𝓝 (∑' n, unitIntervalCosineMode n x * a t n)) := by
  have hsub : Tendsto (fun ε : ℝ => t - ε) (𝓝[>] (0:ℝ)) (𝓝 t) := by
    have h0 : Tendsto (fun ε : ℝ => t - ε) (𝓝 (0:ℝ)) (𝓝 (t - 0)) :=
      (continuous_const.sub continuous_id).tendsto 0
    simpa using h0.mono_left nhdsWithin_le_nhds
  refine tendsto_tsum_of_dominated_convergence (bound := c) hc_summable (fun n => ?_) ?_
  · -- per-mode: e^{−ελₙ}cos·a(t−ε) → cos·a t
    have hpwcont : Continuous
        (fun ε : ℝ => unitIntervalCosineHeatPointWeight ε x n) := by
      unfold unitIntervalCosineHeatPointWeight unitIntervalCosineMode; fun_prop
    have hpw0 : unitIntervalCosineHeatPointWeight 0 x n = unitIntervalCosineMode n x := by
      unfold unitIntervalCosineHeatPointWeight; simp
    have hpw : Tendsto (fun ε => unitIntervalCosineHeatPointWeight ε x n)
        (𝓝[>] (0:ℝ)) (𝓝 (unitIntervalCosineMode n x)) := by
      have := (hpwcont.tendsto 0).mono_left
        (nhdsWithin_le_nhds (a := (0:ℝ)) (s := Set.Ioi 0))
      rwa [hpw0] at this
    have ha : Tendsto (fun ε => a (t - ε) n) (𝓝[>] (0:ℝ)) (𝓝 (a t n)) :=
      ((hacont n).tendsto t).comp hsub
    exact hpw.mul ha
  · -- bound `‖e^{−ελₙ}cos·a(t−ε)‖ ≤ c n` (ε ≥ 0).
    filter_upwards [self_mem_nhdsWithin] with ε hε n
    have hεnn : (0:ℝ) ≤ ε := le_of_lt hε
    rw [Real.norm_eq_abs, abs_mul]
    have hpwle : |unitIntervalCosineHeatPointWeight ε x n| ≤ 1 := by
      unfold unitIntervalCosineHeatPointWeight unitIntervalCosineMode
      rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      have hexple : Real.exp (-ε * unitIntervalCosineEigenvalue n) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
          unfold unitIntervalCosineEigenvalue; positivity
        nlinarith [hεnn, hlam]
      calc Real.exp (-ε * unitIntervalCosineEigenvalue n) *
              |Real.cos ((n : ℝ) * Real.pi * x)|
          ≤ 1 * 1 := mul_le_mul hexple (Real.abs_cos_le_one _) (abs_nonneg _) (by norm_num)
        _ = 1 := by ring
    calc |unitIntervalCosineHeatPointWeight ε x n| * |a (t - ε) n|
        ≤ 1 * c n := mul_le_mul hpwle (hl1 (t - ε) n) (abs_nonneg _) zero_le_one
      _ = c n := one_mul _

/-- **Step 5 capstone — the `∂ₓₓD` candidate `P(t)` as the cutoff limit
(unconditional, under the source-regularity inputs).**  Combining the limit
assembly with the discharged `hconv1`/`hconv2`:

  `∫₀^{t−ε} ∂ₓₓS(t−s)g(s)(x) ds  →  P(t)(x)`,
  `P(t)(x) = S(t)g(0)(x) − g(t)(x) + ∫₀ᵗ S(t−s)∂ₛg(s)(x) ds`
          `= value t (a 0) x − (∑'ₙ cos(nπx)·ĝₙ(t)) + ∑'ₙ ∫₀ᵗ fₙ`.

The honest analytic inputs are exactly: bounded coefficients + time derivative
(`hbound`, `hbound'`, `hda`), continuous `∂ₛg` (`hadotcont`), and uniformly-ℓ¹
source coefficients (`hl1`, `hc_summable`) — the source's `C¹`-in-time + spatial
regularity (`DuhamelSourceTimeC1`).  No hidden hypotheses; both `ε→0` limits are
theorems. -/
theorem duhamelSecondValue_tendsto_closed
    {t x : ℝ} {a adot : ℝ → ℕ → ℝ} {M Mdot : ℝ} {c : ℕ → ℝ}
    (hbound : ∀ s n, |a s n| ≤ M) (hbound' : ∀ s n, |adot s n| ≤ Mdot)
    (hda : ∀ s n, HasDerivAt (fun σ : ℝ => a σ n) (adot s n) s)
    (hadotcont : ∀ n, Continuous (fun s : ℝ => adot s n))
    (hl1 : ∀ s n, |a s n| ≤ c n) (hc_summable : Summable c) (ht : 0 < t) :
    Tendsto
      (fun ε => ∫ s in (0:ℝ)..(t - ε),
        unitIntervalCosineHeatSecondValue (t - s) (a s) x)
      (𝓝[>] (0:ℝ))
      (𝓝 (unitIntervalCosineHeatValue t (a 0) x
        - (∑' n, unitIntervalCosineMode n x * a t n)
        + ∑' n, ∫ s in (0:ℝ)..t,
            unitIntervalCosineHeatPointWeight (t - s) x n * adot s n)) := by
  have hacont : ∀ n, Continuous (fun s : ℝ => a s n) :=
    fun n => continuous_iff_continuousAt.2 (fun s => (hda s n).continuousAt)
  exact duhamelSecondValue_tendsto hbound hbound' hda hadotcont ht
    (duhamelValue_a_joint_tendsto (x := x) hacont hl1 hc_summable)
    (duhamelValue_adot_improper_tendsto (x := x) ht hbound' hadotcont)

/-! ## Steps 6–7 — connecting the cutoff limit to `∂ₓₓD` (precise remaining route)

Step 5 is CLOSED: `lim_{ε→0} ∫₀^{t−ε} ∂ₓₓS(t−s)g(s)(x) ds = P(t)(x)`
(`duhamelSecondValue_tendsto_closed`).  The remaining content is to upgrade this
to `∂ₓₓ D(t)(x) = P(t)(x)` with `D(t)(x) = ∫₀ᵗ S(t−s)g(s)(x) ds`, hence
`DuhamelTermInteriorC2`.  The careful route (avoiding differentiating the singular
`∂ₓₓ`-kernel under the integral, and the non-integrable `∫₀ᵗ secondValue`):

**Step 6 — `P(t)` is continuous in `x` on `[0,1]`.**  `P = value t (a 0) ·
− (∑'ₙ cos(nπ·)·ĝₙ(t)) + (∑'ₙ ∫₀ᵗ fₙ)`.  Each summand is continuous: the heat value
(`C²`); the reconstruction `∑'ₙ cos(nπ·)ĝₙ(t)` by Weierstrass-`M` with the ℓ¹ bound
`c n`; the integral series `∑'ₙ ∫₀ᵗ fₙ` by `continuous_tsum` with the uniform-in-`x`
bound `∫₀ᵗ‖fₙ‖ ≤ Mdot/λₙ` (`duhamelMode_integralNorm_summable`).

**Step 7 — `∂ₓₓD = P` via the double cutoff + space-FTC + Fubini.**  Work with the
cutoff `D'_ε(x) := ∫₀^{t−ε} gradValue(t−s)(a s) x ds` (first `x`-derivative under the
integral — the gradValue kernel `(t−s)^{−1/2}` IS integrable).  Then for `x₀,x`:
  `D'_ε(x) − D'_ε(x₀) = ∫₀^{t−ε} (gradValue x − gradValue x₀) ds
       = ∫₀^{t−ε} ∫_{x₀}^{x} secondValue(t−s)(a s) y dy ds`  (space FTC, `∂_y gradValue
       = secondValue`)
       `= ∫_{x₀}^{x} (∫₀^{t−ε} secondValue(t−s)(a s) y ds) dy`  (Fubini on the FINITE
       `[0,t−ε]×[x₀,x]`, everything bounded/continuous).
  Let `ε→0`: LHS `→ D'(x) − D'(x₀)` (gradValue integral converges, `(t−s)^{−1/2}`
  integrable); the inner `∫₀^{t−ε} secondValue y ds → P(t)(y)` (step 5), and the
  outer `∫_{x₀}^{x}` passes to the limit by dominated convergence (uniform bound on
  the cutoff in `y`).  So `D'(x) − D'(x₀) = ∫_{x₀}^{x} P(t)(y) dy`.  With `P`
  continuous (step 6), `D'` is `C¹` with `(D')' = P`, i.e. `D` is `C²` with
  `∂ₓₓD = P` — `DuhamelTermInteriorC2`, plus Neumann `∂ₓD(t,0)=∂ₓD(t,1)=0` from the
  endpoint vanishing of `gradValue` (`unitIntervalCosineHeatGradientValue_eq_zero_at
  _{zero,one}`, integrated; kernel `(t−s)^{−1/2}` integrable).

These steps need: a first-derivative-under-integral Leibniz (gradValue, integrable
kernel), the space FTC + Fubini on the finite cutoff, and a final
`HasDerivAt`-from-integral assembly — a substantial but singularity-free build,
deferred as the next increment.  Source regularity is the `DuhamelSourceTimeC1`-style
input already isolated (bounded coeffs + time-`C¹` + uniformly-ℓ¹ coeffs). -/

/-! ## Step 7 — the per-mode time integration by parts (the heart of `∂ₓₓD`)

`D(t)(x) = ∑'ₙ bₙ cos(nπx)` with `bₙ = ∫₀ᵗ e^{−(t−s)λₙ}·ĝₙ(s) ds`.  The time IBP
`λₙ bₙ = ĝₙ(t) − e^{−tλₙ}ĝₙ(0) − ∫₀ᵗ e^{−(t−s)λₙ}·ĝₙ′(s) ds` shows `λₙ|bₙ|` is
summable (ℓ¹ source + parabolic gain), hence `D` is `C²` with `∂ₓₓD = −∑'ₙ λₙbₙcos =
P`.  This is the singularity-free heart: no second kernel derivative, the `∂ₛg`
appears instead. -/

/-- **Per-mode time integration by parts.**  For a `C¹`-in-time coefficient
`a` (with derivative `adot`), `λ·∫₀ᵗ e^{−(t−s)λ} a(s) ds = a(t) − e^{−tλ} a(0) −
∫₀ᵗ e^{−(t−s)λ} a′(s) ds`.  (`∫₀ᵗ w′ = w(t)−w(0)` for `w(s)=a(s)e^{−(t−s)λ}`;
`d/ds e^{−(t−s)λ} = λ e^{−(t−s)λ}`.) -/
theorem duhamelCoeff_eigenvalue_mul
    {t lam : ℝ} {a adot : ℝ → ℝ}
    (hda : ∀ s, HasDerivAt a (adot s) s) (hadotcont : Continuous adot) :
    lam * (∫ s in (0:ℝ)..t, Real.exp (-(t - s) * lam) * a s)
      = a t - Real.exp (-t * lam) * a 0
        - ∫ s in (0:ℝ)..t, Real.exp (-(t - s) * lam) * adot s := by
  have hacont : Continuous a :=
    continuous_iff_continuousAt.2 (fun s => (hda s).continuousAt)
  -- `w s = a s · e^{−(t−s)λ}`, `w′ s = adot s · e^{−(t−s)λ} + a s · (λ e^{−(t−s)λ})`.
  have hexp : ∀ s, HasDerivAt (fun s : ℝ => Real.exp (-(t - s) * lam))
      (lam * Real.exp (-(t - s) * lam)) s := by
    intro s
    have harg : HasDerivAt (fun s : ℝ => -(t - s) * lam) lam s := by
      have h1 : HasDerivAt (fun s : ℝ => -(t - s)) 1 s := by
        have : HasDerivAt (fun s : ℝ => s - t) 1 s := by
          simpa using (hasDerivAt_id s).sub_const t
        refine this.congr_of_eventuallyEq ?_
        filter_upwards with y using by ring
      simpa using h1.mul_const lam
    simpa [mul_comm] using harg.exp
  have hw : ∀ s, HasDerivAt (fun s : ℝ => a s * Real.exp (-(t - s) * lam))
      (adot s * Real.exp (-(t - s) * lam)
        + a s * (lam * Real.exp (-(t - s) * lam))) s :=
    fun s => (hda s).mul (hexp s)
  have hcont' : Continuous (fun s : ℝ => adot s * Real.exp (-(t - s) * lam)
      + a s * (lam * Real.exp (-(t - s) * lam))) := by
    have he : Continuous (fun s : ℝ => Real.exp (-(t - s) * lam)) := by fun_prop
    exact (hadotcont.mul he).add (hacont.mul (continuous_const.mul he))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hw s)
    (hcont'.intervalIntegrable 0 t)
  -- evaluate boundary: `w t = a t`, `w 0 = a 0 · e^{−tλ}`.
  have hwt : a t * Real.exp (-(t - t) * lam) = a t := by simp
  have hw0 : a 0 * Real.exp (-(t - 0) * lam) = Real.exp (-t * lam) * a 0 := by
    rw [show -(t - 0) * lam = -t * lam by ring]; ring
  rw [hwt, hw0] at hFTC
  -- split the integral on the LHS of hFTC.
  have hi1 : IntervalIntegrable
      (fun s => adot s * Real.exp (-(t - s) * lam)) volume 0 t := by
    have he : Continuous (fun s : ℝ => Real.exp (-(t - s) * lam)) := by fun_prop
    exact (hadotcont.mul he).intervalIntegrable 0 t
  have hi2 : IntervalIntegrable
      (fun s => a s * (lam * Real.exp (-(t - s) * lam))) volume 0 t := by
    have he : Continuous (fun s : ℝ => Real.exp (-(t - s) * lam)) := by fun_prop
    exact (hacont.mul (continuous_const.mul he)).intervalIntegrable 0 t
  rw [intervalIntegral.integral_add hi1 hi2] at hFTC
  -- `∫ a·(λ·e) = λ·∫ a·e = λ·∫ e·a` ; `∫ adot·e = ∫ e·adot`.
  have he1 : (∫ s in (0:ℝ)..t, a s * (lam * Real.exp (-(t - s) * lam)))
      = lam * ∫ s in (0:ℝ)..t, Real.exp (-(t - s) * lam) * a s := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun s _ => by ring)
  have he2 : (∫ s in (0:ℝ)..t, adot s * Real.exp (-(t - s) * lam))
      = ∫ s in (0:ℝ)..t, Real.exp (-(t - s) * lam) * adot s :=
    intervalIntegral.integral_congr (fun s _ => by ring)
  rw [he1, he2] at hFTC
  linarith [hFTC]

/-! ## General cosine-series `C²` engine

`∑'ₙ bₙ cos(nπx)` is `C²` whenever `∑'ₙ λₙ|bₙ| < ∞` (`λₙ = (nπ)²`).  Termwise
differentiation twice; majorants `|bₙ|`, `(nπ)|bₙ|`, `λₙ|bₙ|`, all dominated by
`∑λₙ|bₙ|`.  This is the engine that turns the time-IBP coefficient decay
(`duhamelCoeff_eigenvalue_mul`) into the `C²` of the Duhamel term. -/

/-- From `∑λₙ|bₙ| < ∞`: `∑(nπ)|bₙ| < ∞` and `∑|bₙ| < ∞` (since `nπ ≤ (nπ)² = λₙ` for
`n ≥ 1`). -/
theorem cosineCoeff_summable_of_eigenvalue_summable {b : ℕ → ℝ}
    (hb : Summable (fun n => unitIntervalCosineEigenvalue n * |b n|)) :
    Summable (fun n : ℕ => ((n : ℝ) * Real.pi) * |b n|) ∧ Summable (fun n => |b n|) := by
  -- `nπ|bₙ| ≤ λₙ|bₙ|` for ALL `n` (n=0: both 0; n≥1: nπ ≤ (nπ)²).
  have hfreq : Summable (fun n : ℕ => ((n : ℝ) * Real.pi) * |b n|) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hb
    have hle : ((n : ℝ) * Real.pi) ≤ unitIntervalCosineEigenvalue n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp [unitIntervalCosineEigenvalue]
      · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
        have hnpi : (1 : ℝ) ≤ (n : ℝ) * Real.pi := by nlinarith [Real.two_le_pi, hn1]
        unfold unitIntervalCosineEigenvalue; nlinarith [hnpi]
    exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)
  refine ⟨hfreq, ?_⟩
  -- `|bₙ|`: drop `n=0`, then `|b(n+1)| ≤ (n+1)π·|b(n+1)|`.
  have htail : Summable (fun n => |b (n + 1)|) := by
    refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
      ((summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) * Real.pi) * |b n|) 1).2 hfreq)
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have hge : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * Real.pi := by
      rw [hcast]; nlinarith [Real.two_le_pi, (by positivity : (0:ℝ) ≤ (n : ℝ))]
    nlinarith [abs_nonneg (b (n + 1)), hge]
  exact (summable_nat_add_iff (f := fun n => |b n|) 1).1 htail

/-! ## Atom closure map (all pieces DONE below)

The time-IBP atom `intervalDuhamelTerm_closedC2_of_timeC1_source` is now fully
discharged.  The pieces, all proved in this file:

**(E) Cosine-series `C²` engine** `cosineCoeffSeries_contDiff_two`:
`∑'ₙ bₙ cos(nπx)` is `ContDiff ℝ 2` from `∑λₙ|bₙ|<∞`.  Two-fold termwise
differentiation (`cosineCoeffSeries_grad_hasDerivAt`, `_grad2_hasDerivAt`) by
`hasDerivAt_tsum` with uniform majorants `(nπ)|bₙ|`, `λₙ|bₙ|`; second series
continuous (`continuous_tsum`); assembled via `contDiff_succ_iff_deriv`.

**(D) Spectral form of `D`** `duhamelSpectral_eq_cosineSeries`:
`D(t)(x) = ∑'ₙ bₙ(t) cos(nπx)`, `bₙ = duhamelSpectralCoeff a t n =
∫₀ᵗ e^{−(t−s)λₙ}ĝₙ(s) ds`, via the `∑∫=∫∑` swap `duhamelValue_adot_eq_tsum`
(summable since the envelope is ℓ¹) + pulling the `s`-constant `cos(nπx)` out.

**(S) `∑λₙ|bₙ|<∞`** `duhamelSpectralCoeff_eigenvalue_summable`: per-mode time IBP
`duhamelCoeff_eigenvalue_mul` gives `λₙbₙ = ĝₙ(t) − e^{−tλₙ}ĝₙ(0) − ∫₀ᵗe^{−(t−s)λₙ}ĝₙ′`,
so `λₙ|bₙ| ≤ 2·envₙ + Ṁ·∫₀ᵗe^{−(t−s)λₙ}` (ℓ¹ envelope + summable parabolic gain
`duhamelGainIntegral_summable`).

**(I) `∂ₓₓD`** `cosineCoeffSeries_deriv2_eq` (4th atom conjunct): the spectral
identity `∂ₓₓ[∑bₙcos] = ∑bₙ(−(nπ)²cos) = −∑λₙbₙcos`.

**(N) Neumann** `cosineCoeffSeries_deriv_at_zero/_one` (atom conjuncts 2–3):
`∂ₓD(t,0)=∂ₓD(t,1)=0` since the grad series carries `sin(nπ·0)=sin(nπ)=0` per mode.

**(A) Atom** `intervalDuhamelTerm_closedC2_of_timeC1_source`: from the honest source
package `DuhamelSourceTimeC1` (time-`C¹` coeffs, ℓ¹ envelope, bounded derivative),
`ContDiff ℝ 2 (D t)` ∧ Neumann at `0,1` ∧ the spectral `∂ₓₓ` formula. -/

/-- **Gradient `HasDerivAt` of the cosine series.**  Termwise differentiation:
`∂ₓ ∑'ₙ bₙ cos(nπx) = ∑'ₙ bₙ·(−nπ·sin(nπx))`, uniformly majorised by `(nπ)|bₙ|`. -/
theorem cosineCoeffSeries_grad_hasDerivAt {b : ℕ → ℝ}
    (hb : Summable (fun n => unitIntervalCosineEigenvalue n * |b n|)) (y : ℝ) :
    HasDerivAt (fun x => ∑' n, b n * cosineMode n x)
      (∑' n, b n * (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * y))) y := by
  obtain ⟨hfreq, hval⟩ := cosineCoeff_summable_of_eigenvalue_summable hb
  have hGbound : ∀ (n : ℕ) (z : ℝ),
      ‖b n * (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * z))‖
        ≤ ((n : ℝ) * Real.pi) * |b n| := by
    intro n z
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg]
    calc |b n| * (|(n : ℝ) * Real.pi| * |Real.sin ((n : ℝ) * Real.pi * z)|)
        ≤ |b n| * (((n : ℝ) * Real.pi) * 1) := by
          gcongr
          · rw [abs_of_nonneg (by positivity)]
          · exact Real.abs_sin_le_one _
      _ = ((n : ℝ) * Real.pi) * |b n| := by ring
  have hvalsum : Summable (fun n => b n * cosineMode n y) := by
    refine Summable.of_norm_bounded hval (fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |b n| * |cosineMode n y| ≤ |b n| * 1 :=
          mul_le_mul_of_nonneg_left (by unfold cosineMode; exact Real.abs_cos_le_one _)
            (abs_nonneg _)
      _ = |b n| := mul_one _
  have hterm1 : ∀ (n : ℕ) (z : ℝ),
      HasDerivAt (fun x => b n * cosineMode n x)
        (b n * (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * z))) z := by
    intro n z
    exact (cosineMode_hasDerivAt n z).const_mul (b n)
  exact hasDerivAt_tsum (𝕜 := ℝ)
    (u := fun n : ℕ => ((n : ℝ) * Real.pi) * |b n|)
    hfreq hterm1 hGbound hvalsum y

/-- **Second-gradient `HasDerivAt` of the cosine series.**  Termwise differentiation of
the gradient series: `∂ₓ ∑'ₙ bₙ(−nπ sin(nπx)) = ∑'ₙ bₙ·(−(nπ)²·cos(nπx))`, majorised
by `λₙ|bₙ|`. -/
theorem cosineCoeffSeries_grad2_hasDerivAt {b : ℕ → ℝ}
    (hb : Summable (fun n => unitIntervalCosineEigenvalue n * |b n|)) (y : ℝ) :
    HasDerivAt
      (fun x => ∑' n, b n * (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * x)))
      (∑' n, b n * (-(((n : ℝ) * Real.pi) ^ 2) * Real.cos ((n : ℝ) * Real.pi * y))) y := by
  obtain ⟨hfreq, hval⟩ := cosineCoeff_summable_of_eigenvalue_summable hb
  have hGbound : ∀ (n : ℕ) (z : ℝ),
      ‖b n * (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * z))‖
        ≤ ((n : ℝ) * Real.pi) * |b n| := by
    intro n z
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg]
    calc |b n| * (|(n : ℝ) * Real.pi| * |Real.sin ((n : ℝ) * Real.pi * z)|)
        ≤ |b n| * (((n : ℝ) * Real.pi) * 1) := by
          gcongr
          · rw [abs_of_nonneg (by positivity)]
          · exact Real.abs_sin_le_one _
      _ = ((n : ℝ) * Real.pi) * |b n| := by ring
  have hHbound : ∀ (n : ℕ) (z : ℝ),
      ‖b n * (-(((n : ℝ) * Real.pi) ^ 2) * Real.cos ((n : ℝ) * Real.pi * z))‖
        ≤ unitIntervalCosineEigenvalue n * |b n| := by
    intro n z
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg]
    have hlam : unitIntervalCosineEigenvalue n = ((n : ℝ) * Real.pi) ^ 2 := by
      unfold unitIntervalCosineEigenvalue; ring
    rw [hlam]
    calc |b n| * (|((n : ℝ) * Real.pi) ^ 2| * |Real.cos ((n : ℝ) * Real.pi * z)|)
        ≤ |b n| * ((((n : ℝ) * Real.pi) ^ 2) * 1) := by
          gcongr
          · rw [abs_of_nonneg (by positivity)]
          · exact Real.abs_cos_le_one _
      _ = ((n : ℝ) * Real.pi) ^ 2 * |b n| := by ring
  have hGsum : Summable
      (fun n => b n * (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * y))) :=
    Summable.of_norm_bounded hfreq (fun n => hGbound n y)
  have hterm2 : ∀ (n : ℕ) (z : ℝ),
      HasDerivAt
        (fun x => b n * (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * x)))
        (b n * (-(((n : ℝ) * Real.pi) ^ 2) * Real.cos ((n : ℝ) * Real.pi * z))) z := by
    intro n z
    have hsin : HasDerivAt (fun x : ℝ => Real.sin ((n : ℝ) * Real.pi * x))
        ((n : ℝ) * Real.pi * Real.cos ((n : ℝ) * Real.pi * z)) z := by
      have := (Real.hasDerivAt_sin ((n : ℝ) * Real.pi * z)).comp z
        ((hasDerivAt_id z).const_mul ((n : ℝ) * Real.pi))
      convert this using 1; ring
    have := (hsin.const_mul (-((n : ℝ) * Real.pi))).const_mul (b n)
    convert this using 1; ring
  exact hasDerivAt_tsum (𝕜 := ℝ)
    (u := fun n => unitIntervalCosineEigenvalue n * |b n|)
    hb hterm2 hHbound hGsum y

/-- **General cosine-series `C²`.**  `x ↦ ∑'ₙ bₙ cos(nπx)` is `ContDiff ℝ 2` when
`∑'ₙ λₙ|bₙ| < ∞`.  Two-fold termwise differentiation
(`cosineCoeffSeries_grad_hasDerivAt`, `cosineCoeffSeries_grad2_hasDerivAt`) with the
second series continuous (`continuous_tsum`, majorant `λₙ|bₙ|`). -/
theorem cosineCoeffSeries_contDiff_two {b : ℕ → ℝ}
    (hb : Summable (fun n => unitIntervalCosineEigenvalue n * |b n|)) :
    ContDiff ℝ 2 (fun x => ∑' n, b n * cosineMode n x) := by
  have hHcont : Continuous
      (fun y => ∑' n, b n * (-(((n : ℝ) * Real.pi) ^ 2) * Real.cos ((n : ℝ) * Real.pi * y))) := by
    refine continuous_tsum (fun n => by fun_prop) hb (fun n y => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg]
    have hlam : unitIntervalCosineEigenvalue n = ((n : ℝ) * Real.pi) ^ 2 := by
      unfold unitIntervalCosineEigenvalue; ring
    rw [hlam]
    calc |b n| * (|((n : ℝ) * Real.pi) ^ 2| * |Real.cos ((n : ℝ) * Real.pi * y)|)
        ≤ |b n| * ((((n : ℝ) * Real.pi) ^ 2) * 1) := by
          gcongr
          · rw [abs_of_nonneg (by positivity)]
          · exact Real.abs_cos_le_one _
      _ = ((n : ℝ) * Real.pi) ^ 2 * |b n| := by ring
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun y => (cosineCoeffSeries_grad_hasDerivAt hb y).differentiableAt, by simp, ?_⟩
  have he1 : deriv (fun x => ∑' n, b n * cosineMode n x)
      = fun y => ∑' n, b n * (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * y)) := by
    funext y; exact (cosineCoeffSeries_grad_hasDerivAt hb y).deriv
  rw [he1, contDiff_one_iff_deriv]
  refine ⟨fun y => (cosineCoeffSeries_grad2_hasDerivAt hb y).differentiableAt, ?_⟩
  have he2 : deriv
      (fun x => ∑' n, b n * (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * x)))
      = fun y => ∑' n, b n * (-(((n : ℝ) * Real.pi) ^ 2) * Real.cos ((n : ℝ) * Real.pi * y)) := by
    funext y; exact (cosineCoeffSeries_grad2_hasDerivAt hb y).deriv
  rw [he2]; exact hHcont

/-- **Spectral second derivative.**  `∂ₓₓ ∑'ₙ bₙ cos(nπx) = ∑'ₙ bₙ·(−(nπ)²cos(nπx))`
`= −∑'ₙ λₙ bₙ cos(nπx)`. -/
theorem cosineCoeffSeries_deriv2_eq {b : ℕ → ℝ}
    (hb : Summable (fun n => unitIntervalCosineEigenvalue n * |b n|)) (y : ℝ) :
    deriv (deriv (fun x => ∑' n, b n * cosineMode n x)) y
      = ∑' n, b n * (-(((n : ℝ) * Real.pi) ^ 2) * Real.cos ((n : ℝ) * Real.pi * y)) := by
  have he1 : deriv (fun x => ∑' n, b n * cosineMode n x)
      = fun z => ∑' n, b n * (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * z)) := by
    funext z; exact (cosineCoeffSeries_grad_hasDerivAt hb z).deriv
  rw [he1]; exact (cosineCoeffSeries_grad2_hasDerivAt hb y).deriv

/-- **Neumann at the left endpoint.**  `∂ₓ ∑'ₙ bₙ cos(nπx)` vanishes at `x = 0`
(each term carries `sin(nπ·0) = 0`). -/
theorem cosineCoeffSeries_deriv_at_zero {b : ℕ → ℝ}
    (hb : Summable (fun n => unitIntervalCosineEigenvalue n * |b n|)) :
    deriv (fun x => ∑' n, b n * cosineMode n x) 0 = 0 := by
  rw [(cosineCoeffSeries_grad_hasDerivAt hb 0).deriv]
  have : (fun n => b n * (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * 0)))
      = fun _ : ℕ => (0 : ℝ) := by
    funext n; simp
  rw [this, tsum_zero]

/-- **Neumann at the right endpoint.**  `∂ₓ ∑'ₙ bₙ cos(nπx)` vanishes at `x = 1`
(each term carries `sin(nπ·1) = sin(nπ) = 0`). -/
theorem cosineCoeffSeries_deriv_at_one {b : ℕ → ℝ}
    (hb : Summable (fun n => unitIntervalCosineEigenvalue n * |b n|)) :
    deriv (fun x => ∑' n, b n * cosineMode n x) 1 = 0 := by
  rw [(cosineCoeffSeries_grad_hasDerivAt hb 1).deriv]
  have : (fun n => b n * (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * 1)))
      = fun _ : ℕ => (0 : ℝ) := by
    funext n
    rw [mul_one, Real.sin_nat_mul_pi]
    ring
  rw [this, tsum_zero]

/-! ## Spectral Duhamel term: closed `C²` under time-`C¹` source regularity -/

/-- **Parabolic-gain integral summability.**  `∑'ₙ Mdot·∫₀ᵗ e^{−(t−s)λₙ} ds < ∞`:
the `n=0` term is `Mdot·t`, and for `n ≥ 1` the gain integral is `≤ 1/λₙ = 1/(π²(n+1)²)`,
a `p=2` series.  (Extracted from the `∂ₛg`-integral majorant.) -/
theorem duhamelGainIntegral_summable {t Mdot : ℝ} (ht : 0 < t) (hMdotnn : 0 ≤ Mdot) :
    Summable (fun n => Mdot * ∫ s in (0:ℝ)..t,
      Real.exp (-(t - s) * unitIntervalCosineEigenvalue n)) := by
  set E : ℕ → ℝ := fun n => ∫ s in (0:ℝ)..t,
    Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) with hE_def
  have hEnn : ∀ n, 0 ≤ E n := by
    intro n
    apply intervalIntegral.integral_nonneg (le_of_lt ht)
    intro s _; exact Real.exp_nonneg _
  have hgsum : Summable (fun n : ℕ => Mdot * (1 / Real.pi ^ 2) * (1 / ((n : ℝ) + 1) ^ 2)) := by
    have hp2 : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
      have := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
      simpa using (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).2 this
    exact hp2.mul_left (Mdot * (1 / Real.pi ^ 2))
  have htail : Summable (fun n => Mdot * E (n + 1)) := by
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg hMdotnn (hEnn (n + 1))) (fun n => ?_) hgsum
    have hlam_pos : 0 < unitIntervalCosineEigenvalue (n + 1) := by
      unfold unitIntervalCosineEigenvalue
      have : (0:ℝ) < ((n : ℝ) + 1) := by positivity
      positivity
    have hgain := ShenWork.IntervalDuhamelRegularity.parabolicGain_le_one
      (lam := unitIntervalCosineEigenvalue (n + 1)) (t := t) hlam_pos.le ht.le
    have hElt : E (n + 1) ≤ 1 / unitIntervalCosineEigenvalue (n + 1) := by
      rw [le_div_iff₀ hlam_pos]
      calc E (n + 1) * unitIntervalCosineEigenvalue (n + 1)
          = unitIntervalCosineEigenvalue (n + 1) * E (n + 1) := by ring
        _ ≤ 1 := hgain
    have hlam_eq : unitIntervalCosineEigenvalue (n + 1)
        = ((n : ℝ) + 1) ^ 2 * Real.pi ^ 2 := by
      unfold unitIntervalCosineEigenvalue; push_cast; ring
    calc Mdot * E (n + 1) ≤ Mdot * (1 / unitIntervalCosineEigenvalue (n + 1)) :=
          mul_le_mul_of_nonneg_left hElt hMdotnn
      _ = Mdot * (1 / Real.pi ^ 2) * (1 / ((n : ℝ) + 1) ^ 2) := by
          rw [hlam_eq]; field_simp; try ring
  exact (summable_nat_add_iff (f := fun n => Mdot * E n) 1).mp htail

/-- **Spectral Duhamel coefficient.**  `bₙ(t) = ∫₀ᵗ e^{−(t−s)λₙ} ĝₙ(s) ds`, the `n`-th
cosine coefficient of the Duhamel term `D(t)(x) = ∫₀ᵗ S(t−s)g(s)(x) ds`. -/
noncomputable def duhamelSpectralCoeff (a : ℝ → ℕ → ℝ) (t : ℝ) (n : ℕ) : ℝ :=
  ∫ s in (0:ℝ)..t, Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * a s n

/-- **Time-`C¹` source regularity** for the spectral Duhamel term.  The cosine
coefficients `s ↦ a s n` are `C¹` in time (`hderiv`, derivative `adot` continuous in
`s`), uniformly summable (`envelope`, an ℓ¹ majorant), with a uniform bound on the time
derivative (`derivBound`).  This is the honest source hypothesis; the `C²` of the term
is the *conclusion*, not packed in here. -/
structure DuhamelSourceTimeC1 (a : ℝ → ℕ → ℝ) where
  /-- Time derivative of the `n`-th coefficient. -/
  adot : ℝ → ℕ → ℝ
  /-- Each coefficient is `C¹` in time with derivative `adot`. -/
  hderiv : ∀ s n, HasDerivAt (fun r => a r n) (adot s n) s
  /-- The derivative coefficients are continuous in time. -/
  hadotcont : ∀ n, Continuous (fun s : ℝ => adot s n)
  /-- ℓ¹ envelope dominating the coefficients uniformly in time. -/
  envelope : ℕ → ℝ
  /-- The envelope is summable. -/
  henv_summable : Summable envelope
  /-- The coefficients are dominated by the envelope, uniformly in time. -/
  henv_bound : ∀ s n, |a s n| ≤ envelope n
  /-- Uniform bound on the time derivative. -/
  derivBound : ℝ
  /-- The derivative is uniformly bounded. -/
  hderivBound : ∀ s n, |adot s n| ≤ derivBound

/-- **(D) Spectral form of the Duhamel term.**  `∫₀ᵗ S(t−s)g(s)(x) ds = ∑'ₙ bₙ(t) cos(nπx)`:
the `∑∫ = ∫∑` swap (`duhamelValue_adot_eq_tsum`, summable since the envelope is ℓ¹), then
pulling the `s`-constant `cos(nπx)` out of each mode integral. -/
theorem duhamelSpectral_eq_cosineSeries {t x : ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC1 a) (ht : 0 < t) :
    (∫ s in (0:ℝ)..t, unitIntervalCosineHeatValue (t - s) (a s) x)
      = ∑' n, duhamelSpectralCoeff a t n * cosineMode n x := by
  have hnn : ∀ n, 0 ≤ src.envelope n := fun n => le_trans (abs_nonneg _) (src.henv_bound 0 n)
  have hunif : ∀ s i, |a s i| ≤ ∑' k, src.envelope k := by
    intro s i
    refine le_trans (src.henv_bound s i) ?_
    have := src.henv_summable.sum_le_tsum {i} (fun j _ => hnn j)
    simpa using this
  have hcont_a : ∀ n, Continuous (fun s : ℝ => a s n) := fun n =>
    continuous_iff_continuousAt.2 (fun s => (src.hderiv s n).continuousAt)
  rw [duhamelValue_adot_eq_tsum (adot := a) (Mdot := ∑' k, src.envelope k)
      ht hunif hcont_a (b := t) ht.le (le_refl t)]
  refine tsum_congr (fun n => ?_)
  calc (∫ s in (0:ℝ)..t, unitIntervalCosineHeatPointWeight (t - s) x n * a s n)
      = ∫ s in (0:ℝ)..t,
          (Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * a s n) * cosineMode n x :=
        intervalIntegral.integral_congr (fun s _ => by
          simp only [unitIntervalCosineHeatPointWeight, unitIntervalCosineMode, cosineMode]; ring)
    _ = (∫ s in (0:ℝ)..t, Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * a s n)
          * cosineMode n x := intervalIntegral.integral_mul_const _ _
    _ = duhamelSpectralCoeff a t n * cosineMode n x := rfl

/-- **(S) Eigenvalue-weighted coefficient summability.**  `∑'ₙ λₙ|bₙ(t)| < ∞`.  Per-mode
time IBP (`duhamelCoeff_eigenvalue_mul`) gives
`λₙ bₙ = ĝₙ(t) − e^{−tλₙ}ĝₙ(0) − ∫₀ᵗ e^{−(t−s)λₙ}ĝₙ′(s) ds`, so
`λₙ|bₙ| ≤ 2·envₙ + Ṁ·∫₀ᵗe^{−(t−s)λₙ}` — ℓ¹ envelope plus the summable parabolic gain. -/
theorem duhamelSpectralCoeff_eigenvalue_summable {t : ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC1 a) (ht : 0 < t) :
    Summable (fun n => unitIntervalCosineEigenvalue n * |duhamelSpectralCoeff a t n|) := by
  have hnn : ∀ n, 0 ≤ src.envelope n := fun n => le_trans (abs_nonneg _) (src.henv_bound 0 n)
  have hdbnn : 0 ≤ src.derivBound := le_trans (abs_nonneg _) (src.hderivBound 0 0)
  have hM : Summable (fun n => 2 * src.envelope n
      + src.derivBound * ∫ s in (0:ℝ)..t,
          Real.exp (-(t - s) * unitIntervalCosineEigenvalue n)) :=
    (src.henv_summable.mul_left 2).add (duhamelGainIntegral_summable ht hdbnn)
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg ?_ (abs_nonneg _)) (fun n => ?_) hM
  · unfold unitIntervalCosineEigenvalue; positivity
  · have hlamnn : (0:ℝ) ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue; positivity
    have hkey := duhamelCoeff_eigenvalue_mul (t := t) (lam := unitIntervalCosineEigenvalue n)
      (a := fun s => a s n) (adot := fun s => src.adot s n)
      (fun s => src.hderiv s n) (src.hadotcont n)
    have hconv : unitIntervalCosineEigenvalue n * |duhamelSpectralCoeff a t n|
        = |a t n - Real.exp (-t * unitIntervalCosineEigenvalue n) * a 0 n
            - ∫ s in (0:ℝ)..t,
                Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n| := by
      have key := congrArg abs hkey
      rw [abs_mul, abs_of_nonneg hlamnn] at key
      exact key
    rw [hconv]
    -- triangle + per-term bounds
    have hb1 : |a t n| ≤ src.envelope n := src.henv_bound t n
    have hexp_le : Real.exp (-t * unitIntervalCosineEigenvalue n) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have : 0 ≤ t * unitIntervalCosineEigenvalue n := mul_nonneg ht.le hlamnn
      linarith
    have hb2 : |Real.exp (-t * unitIntervalCosineEigenvalue n) * a 0 n| ≤ src.envelope n := by
      rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      calc Real.exp (-t * unitIntervalCosineEigenvalue n) * |a 0 n|
          ≤ 1 * |a 0 n| := mul_le_mul_of_nonneg_right hexp_le (abs_nonneg _)
        _ = |a 0 n| := one_mul _
        _ ≤ src.envelope n := src.henv_bound 0 n
    have hI_bound : |∫ s in (0:ℝ)..t,
          Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n|
        ≤ src.derivBound * ∫ s in (0:ℝ)..t,
            Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) := by
      have hkernel : Continuous
          (fun s : ℝ => Real.exp (-(t - s) * unitIntervalCosineEigenvalue n)) := by fun_prop
      have hII1 : IntervalIntegrable
          (fun s => Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n)
          volume 0 t := (hkernel.mul (src.hadotcont n)).intervalIntegrable 0 t
      calc |∫ s in (0:ℝ)..t,
              Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n|
          = ‖∫ s in (0:ℝ)..t,
              Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n‖ :=
            (Real.norm_eq_abs _).symm
        _ ≤ ∫ s in (0:ℝ)..t,
              ‖Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n‖ :=
            intervalIntegral.norm_integral_le_integral_norm ht.le
        _ ≤ ∫ s in (0:ℝ)..t,
              src.derivBound * Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) := by
            apply intervalIntegral.integral_mono_on ht.le hII1.norm
              (by apply Continuous.intervalIntegrable; fun_prop)
            intro s _
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _),
              mul_comm src.derivBound]
            exact mul_le_mul_of_nonneg_left (src.hderivBound s n) (Real.exp_nonneg _)
        _ = src.derivBound * ∫ s in (0:ℝ)..t,
              Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) := by
            rw [intervalIntegral.integral_const_mul]
    calc |a t n - Real.exp (-t * unitIntervalCosineEigenvalue n) * a 0 n
            - ∫ s in (0:ℝ)..t,
                Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n|
        ≤ |a t n - Real.exp (-t * unitIntervalCosineEigenvalue n) * a 0 n|
            + |∫ s in (0:ℝ)..t,
                Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n| := by
          have := abs_add_le (a t n - Real.exp (-t * unitIntervalCosineEigenvalue n) * a 0 n)
            (-(∫ s in (0:ℝ)..t,
                Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n))
          simpa [sub_eq_add_neg, abs_neg] using this
      _ ≤ (|a t n| + |Real.exp (-t * unitIntervalCosineEigenvalue n) * a 0 n|)
            + |∫ s in (0:ℝ)..t,
                Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n| := by
          gcongr
          have := abs_add_le (a t n)
            (-(Real.exp (-t * unitIntervalCosineEigenvalue n) * a 0 n))
          simpa [sub_eq_add_neg, abs_neg] using this
      _ ≤ (src.envelope n + src.envelope n)
            + src.derivBound * ∫ s in (0:ℝ)..t,
                Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) := by
          gcongr
      _ = 2 * src.envelope n
            + src.derivBound * ∫ s in (0:ℝ)..t,
                Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) := by ring

/-- **(A) Closed `C²` for the spectral Duhamel term.**  Under time-`C¹` source regularity,
`x ↦ ∫₀ᵗ S(t−s)g(s)(x) ds` is `ContDiff ℝ 2`, satisfies the Neumann condition at both
endpoints `x = 0, 1`, and has the spectral second derivative
`∂ₓₓ = ∑'ₙ bₙ(t)·(−(nπ)²cos(nπx)) = −∑'ₙ λₙ bₙ cos(nπx)`. -/
theorem intervalDuhamelTerm_closedC2_of_timeC1_source
    {t : ℝ} {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a) (ht : 0 < t) :
    ContDiff ℝ 2 (fun x => ∫ s in (0:ℝ)..t, unitIntervalCosineHeatValue (t - s) (a s) x)
      ∧ deriv (fun x => ∫ s in (0:ℝ)..t, unitIntervalCosineHeatValue (t - s) (a s) x) 0 = 0
      ∧ deriv (fun x => ∫ s in (0:ℝ)..t, unitIntervalCosineHeatValue (t - s) (a s) x) 1 = 0
      ∧ ∀ x, deriv (deriv
            (fun x => ∫ s in (0:ℝ)..t, unitIntervalCosineHeatValue (t - s) (a s) x)) x
          = ∑' n, duhamelSpectralCoeff a t n
              * (-(((n : ℝ) * Real.pi) ^ 2) * Real.cos ((n : ℝ) * Real.pi * x)) := by
  have hS := duhamelSpectralCoeff_eigenvalue_summable src ht
  have hEq : (fun x => ∫ s in (0:ℝ)..t, unitIntervalCosineHeatValue (t - s) (a s) x)
      = fun x => ∑' n, duhamelSpectralCoeff a t n * cosineMode n x := by
    funext x; exact duhamelSpectral_eq_cosineSeries src ht
  rw [hEq]
  exact ⟨cosineCoeffSeries_contDiff_two hS,
    cosineCoeffSeries_deriv_at_zero hS,
    cosineCoeffSeries_deriv_at_one hS,
    fun x => cosineCoeffSeries_deriv2_eq hS x⟩

end ShenWork.IntervalDuhamelClosedC2
