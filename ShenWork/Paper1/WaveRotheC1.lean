/-
  ShenWork/Paper1/WaveRotheC1.lean

  The G2 uniform-`C¹` bound + local-uniform-convergence brick for the B1 Rothe
  traveling-wave map (Shen, arXiv:2605.04401, §6 / B1 doctrine).  This is the
  last analytic underpinning of the `FrozenStationaryMapSchauderData` continuity
  field: it discharges the carried continuity hypothesis `hcont` of
  `rotheLimit_mem_trap` (WaveRotheLimit.lean).

  ROUTE (ChatGPT-Pro-designed, bespoke 1-D finite-grid, no global Arzelà–Ascoli).

  The implicit-Euler (Rothe) step solution is the variation-of-parameters
  convolution `W = greenConv c λ R_W` (committed; `crossImplicitMap = greenConv`
  of the cross-source `R_W`).  Its derivative is the committed `greenConvDeriv`
  (`greenConv_hasDerivAt`), whose explicit two-sided-tail form

      `W'(x) = (1/δ)·[ r₊ e^{r₊x} ∫_x^∞ e^{−r₊y}R_W + r₋ e^{r₋x} ∫_{−∞}^x e^{−r₋y}R_W ]`

  is bounded UNIFORMLY (in `k` AND `u`) by `(2/δ)·B` whenever the source obeys
  `|R_W| ≤ B` — the kernel-derivative `L¹` norm `‖Kλ'‖₁ = 2/δ` reappears as the
  tail constant.  This is the uniform `C¹` bound.

  From the `C¹` bound, each iterate is `LipschitzWith (rotheC1Bound …)` (MVT,
  `Convex.lipschitzWith_of_nnnorm_deriv_le`), UNIFORMLY in `k`.  Uniform Lipschitz
  + pointwise monotone convergence (committed `rotheLimit_tendsto`) gives
  local-uniform convergence by the bespoke finite-`ε`-grid argument:  on `[−R,R]`,
  cover by finitely many grid points, get `ε/3` pointwise there, and interpolate
  by the uniform Lipschitz constant.  Local-uniform convergence of continuous
  iterates then forces the limit continuous (an `ε/3` argument), discharging
  `hcont`.

  Deliverables (namespace `ShenWork.Paper1`):
    1. `crossImplicitStep_deriv_bound` — uniform `C¹` bound, explicit constant
       `rotheC1Bound` (= `rotheSource0Bound + rotheFluxBound` packaging).
    2. `crossImplicitStep_lipschitz` — each iterate `LipschitzWith rotheC1Bound`.
    3. `rotheLimit_locallyUniform` — local-uniform convergence (finite grid).
    4. `rotheLimit_continuous` — limit continuity, DISCHARGING `hcont`.
-/
import ShenWork.Paper1.WaveRotheLimit
import ShenWork.Paper1.WaveConvRepr
import ShenWork.Paper1.WaveRotheStep
import Mathlib.Analysis.Calculus.MeanValue

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

variable {c lam : ℝ}

/-! ## Part 1 — the uniform `C¹` bound on the Rothe step solution

The step solution is `W = greenConv c λ R_W` (committed convolution form of
`crossImplicitMap`).  Its derivative is `greenConvDeriv c λ R_W` (committed
`greenConv_hasDerivAt`).  We bound the two weighted tails of `greenConvDeriv`
uniformly by the sup-bound of the source. -/

/-- **Tail bound (upper).** For `r > 0` and `|H| ≤ B`, the upper tail obeys
`r·e^{r x}·|∫_x^∞ e^{−r y}H| ≤ B`.  The `e^{r x}` from the kernel split cancels
the `e^{−r x}` produced by integrating `e^{−r y}` over `(x,∞)`. -/
theorem tailHi_weighted_abs_le {r B : ℝ} (hr : 0 < r) {H : ℝ → ℝ}
    (hHint : ∀ x, IntegrableOn (gWeight r H) (Ioi x)) (hB : ∀ y, |H y| ≤ B)
    (x : ℝ) :
    r * Real.exp (r * x) * |tailHi r H x| ≤ B := by
  have hBnn : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hexp_int : IntegrableOn (fun y => B * Real.exp (-r * y)) (Ioi x) :=
    ((integrableOn_exp_mul_Ioi (a := -r) (by linarith) x).const_mul B)
  -- |∫ gWeight| ≤ ∫ |gWeight| ≤ ∫ B e^{-r y}
  have hstep1 : |tailHi r H x| ≤ ∫ y in Ioi x, |gWeight r H y| := by
    rw [tailHi]
    have := norm_integral_le_integral_norm
      (μ := (volume : Measure ℝ).restrict (Ioi x)) (gWeight r H)
    simpa [Real.norm_eq_abs] using this
  have hptbd : ∀ y ∈ Ioi x, |gWeight r H y| ≤ B * Real.exp (-r * y) := by
    intro y _
    rw [gWeight, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-r * y) * |H y|
        ≤ Real.exp (-r * y) * B :=
          mul_le_mul_of_nonneg_left (hB y) (Real.exp_pos _).le
      _ = B * Real.exp (-r * y) := by ring
  have hstep2 : (∫ y in Ioi x, |gWeight r H y|) ≤ ∫ y in Ioi x, B * Real.exp (-r * y) :=
    setIntegral_mono_on ((hHint x).abs) hexp_int measurableSet_Ioi hptbd
  have hval : (∫ y in Ioi x, B * Real.exp (-r * y))
      = B * Real.exp (-r * x) / r := by
    rw [integral_const_mul, integral_exp_mul_Ioi (a := -r) (by linarith) x]
    have hrne : r ≠ 0 := ne_of_gt hr
    field_simp
  have htail_abs : |tailHi r H x| ≤ B * Real.exp (-r * x) / r :=
    le_trans hstep1 (le_trans hstep2 (le_of_eq hval))
  -- multiply through by r·e^{r x} ≥ 0
  have hmul := mul_le_mul_of_nonneg_left htail_abs
    (by positivity : (0:ℝ) ≤ r * Real.exp (r * x))
  refine le_trans hmul (le_of_eq ?_)
  have hrne : r ≠ 0 := ne_of_gt hr
  have hexp : Real.exp (r * x) * Real.exp (-r * x) = 1 := by
    rw [← Real.exp_add, show r * x + -r * x = 0 from by ring, Real.exp_zero]
  have key : r * Real.exp (r * x) * (B * Real.exp (-r * x) / r)
      = B * (Real.exp (r * x) * Real.exp (-r * x)) := by
    field_simp
  rw [key, hexp, mul_one]

/-- **Tail bound (lower).** For `r < 0` and `|H| ≤ B`, the lower tail obeys
`(−r)·e^{r x}·|∫_{−∞}^x e^{−r y}H| ≤ B`. -/
theorem tailLo_weighted_abs_le {r B : ℝ} (hr : r < 0) {H : ℝ → ℝ}
    (hHint : ∀ x, IntegrableOn (gWeight r H) (Iic x)) (hB : ∀ y, |H y| ≤ B)
    (x : ℝ) :
    (-r) * Real.exp (r * x) * |tailLo r H x| ≤ B := by
  have hBnn : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hexp_int : IntegrableOn (fun y => B * Real.exp (-r * y)) (Iic x) :=
    ((integrableOn_exp_mul_Iic (a := -r) (by linarith) x).const_mul B)
  have hstep1 : |tailLo r H x| ≤ ∫ y in Iic x, |gWeight r H y| := by
    rw [tailLo]
    simpa [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (μ := (volume : Measure ℝ).restrict (Iic x))
        (gWeight r H)
  have hptbd : ∀ y ∈ Iic x, |gWeight r H y| ≤ B * Real.exp (-r * y) := by
    intro y _
    rw [gWeight, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-r * y) * |H y|
        ≤ Real.exp (-r * y) * B :=
          mul_le_mul_of_nonneg_left (hB y) (Real.exp_pos _).le
      _ = B * Real.exp (-r * y) := by ring
  have hstep2 : (∫ y in Iic x, |gWeight r H y|) ≤ ∫ y in Iic x, B * Real.exp (-r * y) :=
    setIntegral_mono_on ((hHint x).abs) hexp_int measurableSet_Iic hptbd
  have hrne : r ≠ 0 := ne_of_lt hr
  have hval : (∫ y in Iic x, B * Real.exp (-r * y))
      = B * Real.exp (-r * x) / (-r) := by
    rw [integral_const_mul, integral_exp_mul_Iic (a := -r) (by linarith) x]
    field_simp
  have htail_abs : |tailLo r H x| ≤ B * Real.exp (-r * x) / (-r) :=
    le_trans hstep1 (le_trans hstep2 (le_of_eq hval))
  have hnr : (0:ℝ) < -r := by linarith
  have hmul := mul_le_mul_of_nonneg_left htail_abs
    (le_of_lt (mul_pos hnr (Real.exp_pos (r * x))))
  refine le_trans hmul (le_of_eq ?_)
  have hnrne : (-r) ≠ 0 := ne_of_gt hnr
  have hexp : Real.exp (r * x) * Real.exp (-r * x) = 1 := by
    rw [← Real.exp_add, show r * x + -r * x = 0 from by ring, Real.exp_zero]
  have key : (-r) * Real.exp (r * x) * (B * Real.exp (-r * x) / (-r))
      = B * (Real.exp (r * x) * Real.exp (-r * x)) := by
    field_simp
  rw [key, hexp, mul_one]

/-! ### Explicit `C¹` constants

The uniform `C¹` bound is `2·B/δ`, where `B` is the sup-bound on the cross
source `R_W = reaction(W) + λZ − χ∂ₓ(W^m V_u')`.  We package `B` as the sum of a
"reaction+linear-shift" part `rotheSource0Bound` and a "flux" part
`rotheFluxBound`, so the `C¹` constant `rotheC1Bound` is explicitly
`(2/δ)·(rotheSource0Bound + rotheFluxBound)`. -/

/-- Sup-bound of the smooth `reaction(W)+λZ` part of the source, for `0 ≤ W,Z ≤ M`
and `λ`-shift `λM`.  `reaction = s(1−s^a)`, `|reaction| ≤ M(1+M^a)` on `[0,M]`. -/
def rotheSource0Bound (a M lam : ℝ) : ℝ := M * (1 + M ^ a) + lam * M

/-- Sup-bound of the flux part `χ·∂ₓ(W^m V_u')` of the source.  Carried as an
explicit scalar `Bflux` (the flux-derivative bound; see the report — it is the
genuinely-`BV`/second-kernel piece, supplied as a hypothesis). -/
def rotheFluxBound (chi Bflux : ℝ) : ℝ := |chi| * Bflux

/-- The explicit uniform `C¹` constant `(2/δ)·(rotheSource0Bound+rotheFluxBound)`. -/
def rotheC1Bound (p : CMParams) (c lam M Bflux : ℝ) : ℝ :=
  2 * (greenDelta c lam)⁻¹ *
    (rotheSource0Bound p.α M lam + rotheFluxBound p.χ Bflux)

theorem rotheSource0Bound_nonneg {a M lam : ℝ} (hM : 0 ≤ M) (hlam : 0 ≤ lam) :
    0 ≤ rotheSource0Bound a M lam := by
  unfold rotheSource0Bound
  have h1 : 0 ≤ M * (1 + M ^ a) := by positivity
  have h2 : 0 ≤ lam * M := by positivity
  linarith

theorem rotheFluxBound_nonneg {chi Bflux : ℝ} (hBflux : 0 ≤ Bflux) :
    0 ≤ rotheFluxBound chi Bflux := by
  unfold rotheFluxBound; positivity

theorem rotheC1Bound_nonneg (p : CMParams) {c lam M Bflux : ℝ}
    (hM : 0 ≤ M) (hlam : 0 < lam) (hBflux : 0 ≤ Bflux) :
    0 ≤ rotheC1Bound p c lam M Bflux := by
  unfold rotheC1Bound
  have hδ : 0 ≤ (greenDelta c lam)⁻¹ := (inv_pos.mpr (greenDelta_pos (c := c) hlam)).le
  have h1 := rotheSource0Bound_nonneg (a := p.α) hM hlam.le
  have h2 := rotheFluxBound_nonneg (chi := p.χ) hBflux
  have hsum : 0 ≤ rotheSource0Bound p.α M lam + rotheFluxBound p.χ Bflux := by linarith
  exact mul_nonneg (by positivity) hsum

/-- **`greenConvDeriv` sup-bound.**  For a source `H` with `|H| ≤ B` (and the two
weighted tails integrable at every base point), the convolution derivative is
uniformly bounded by `(2/δ)·B`.  Pure algebra of the two tail bounds. -/
theorem greenConvDeriv_abs_le (hlam : 0 < lam) {H : ℝ → ℝ} {B : ℝ}
    (hB : ∀ y, |H y| ≤ B)
    (hHi : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) H) (Ioi x))
    (hLo : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) H) (Iic x))
    (x : ℝ) :
    |greenConvDeriv c lam H x| ≤ 2 * (greenDelta c lam)⁻¹ * B := by
  have hrp := greenRootPlus_pos (c := c) hlam
  have hrm := greenRootMinus_neg (c := c) hlam
  have hδ : 0 < (greenDelta c lam)⁻¹ := inv_pos.mpr (greenDelta_pos (c := c) hlam)
  -- the two weighted tails are each ≤ B
  have hHibd := tailHi_weighted_abs_le (r := greenRootPlus c lam) hrp hHi hB x
  have hLobd := tailLo_weighted_abs_le (r := greenRootMinus c lam) hrm hLo hB x
  -- |greenConvDeriv| ≤ (1/δ)(|r₊ e^{r₊x} tailHi| + |r₋ e^{r₋x} tailLo|)
  rw [greenConvDeriv, abs_mul, abs_of_pos hδ]
  have htri : |greenRootPlus c lam * Real.exp (greenRootPlus c lam * x)
        * tailHi (greenRootPlus c lam) H x
      + greenRootMinus c lam * Real.exp (greenRootMinus c lam * x)
        * tailLo (greenRootMinus c lam) H x|
      ≤ B + B := by
    refine le_trans (abs_add_le _ _) ?_
    have hA : |greenRootPlus c lam * Real.exp (greenRootPlus c lam * x)
          * tailHi (greenRootPlus c lam) H x|
        = greenRootPlus c lam * Real.exp (greenRootPlus c lam * x)
            * |tailHi (greenRootPlus c lam) H x| := by
      rw [abs_mul, abs_mul, abs_of_pos hrp, abs_of_pos (Real.exp_pos _), mul_assoc]
    have hBb : |greenRootMinus c lam * Real.exp (greenRootMinus c lam * x)
          * tailLo (greenRootMinus c lam) H x|
        = (-greenRootMinus c lam) * Real.exp (greenRootMinus c lam * x)
            * |tailLo (greenRootMinus c lam) H x| := by
      rw [abs_mul, abs_mul, abs_of_neg hrm, abs_of_pos (Real.exp_pos _), mul_assoc]
    rw [hA, hBb]
    exact add_le_add hHibd hLobd
  calc (greenDelta c lam)⁻¹
        * |greenRootPlus c lam * Real.exp (greenRootPlus c lam * x)
            * tailHi (greenRootPlus c lam) H x
          + greenRootMinus c lam * Real.exp (greenRootMinus c lam * x)
            * tailLo (greenRootMinus c lam) H x|
      ≤ (greenDelta c lam)⁻¹ * (B + B) :=
        mul_le_mul_of_nonneg_left htri hδ.le
    _ = 2 * (greenDelta c lam)⁻¹ * B := by ring

/-- **Deliverable 1 — uniform `C¹` bound (abstract source form).**
For the step solution `W = greenConv c λ R_W` (the committed convolution form of
`crossImplicitMap`), with the cross-source sup-bounded `|R_W| ≤ B` and the two
weighted tails integrable, the derivative is bounded UNIFORMLY by `(2/δ)·B`.

The `(2/δ)` is the committed kernel-derivative `L¹` norm `‖Kλ'‖₁`; the bound is
uniform in `k` (each step) and in `u` (the frozen profile), depending only on the
sup-bound `B` and `λ`. -/
theorem crossImplicitStep_deriv_bound (hlam : 0 < lam) {R_W : ℝ → ℝ} {B : ℝ}
    (hcont : Continuous R_W) (hB : ∀ y, |R_W y| ≤ B)
    (hHi : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) R_W) (Ioi x))
    (hLo : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) R_W) (Iic x))
    (x : ℝ) :
    |deriv (greenConv c lam R_W) x| ≤ 2 * (greenDelta c lam)⁻¹ * B := by
  rw [(greenConv_hasDerivAt hcont hHi hLo x).deriv]
  exact greenConvDeriv_abs_le hlam hB hHi hLo x

/-- **Deliverable 1, packaged with the explicit `rotheC1Bound` constant.**
When the source sup-bound `B` is the packaged `rotheSource0Bound+rotheFluxBound`,
the `C¹` bound is exactly `rotheC1Bound`. -/
theorem crossImplicitStep_deriv_bound_packaged (p : CMParams) (hlam : 0 < lam)
    {R_W : ℝ → ℝ} {M Bflux : ℝ}
    (hcont : Continuous R_W)
    (hB : ∀ y, |R_W y| ≤ rotheSource0Bound p.α M lam + rotheFluxBound p.χ Bflux)
    (hHi : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) R_W) (Ioi x))
    (hLo : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) R_W) (Iic x))
    (x : ℝ) :
    |deriv (greenConv c lam R_W) x| ≤ rotheC1Bound p c lam M Bflux := by
  have := crossImplicitStep_deriv_bound hlam hcont hB hHi hLo x
  rwa [show rotheC1Bound p c lam M Bflux
      = 2 * (greenDelta c lam)⁻¹
        * (rotheSource0Bound p.α M lam + rotheFluxBound p.χ Bflux) from rfl]

/-! ## Part 2 — uniform Lipschitz of each iterate

From a global derivative bound `|W'| ≤ L`, `W` is `LipschitzWith L` (MVT, via the
committed `Convex.lipschitzWith_of_nnnorm_deriv_le` on `ℝ = Icc -∞ ∞`, but we use
the global `lipschitzWith_of_nnnorm_deriv_le` directly).  Uniform in `k`. -/

/-- **Deliverable 2 — uniform Lipschitz of the step solution.**
If `W` is differentiable everywhere with `|W'| ≤ L` (`0 ≤ L`), then `W` is
`LipschitzWith (Real.toNNReal L)`.  Applied to the step solution with
`L = rotheC1Bound`, this gives the same Lipschitz constant for every `k`. -/
theorem crossImplicitStep_lipschitz {W : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hdiff : Differentiable ℝ W) (hderiv : ∀ x, |deriv W x| ≤ L) :
    LipschitzWith (Real.toNNReal L) W := by
  apply lipschitzWith_of_nnnorm_deriv_le hdiff
  intro x
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal _ hL]
  exact hderiv x

/-! ## Part 3 — local-uniform convergence via the bespoke finite grid

Given (a) pointwise convergence `z k x → f x` at every `x`, and (b) a UNIFORM
Lipschitz constant `Λ` for every `z k` AND for the limit `f`, we prove
`LocallyUniformConverges z f`.

On `[−R,R]`: pick a finite `(ε/(3Λ))`-net of grid points; pointwise convergence
gives `|z k xᵢ − f xᵢ| < ε/3` at each net point for large `k` (finitely many, so
a common `N`); the uniform Lipschitz lets every `x ∈ [−R,R]` be approximated by a
net point within `ε/(3Λ)`, so the two Lipschitz interpolation errors are each
`< ε/3`, giving `|z k x − f x| < ε` for all `x ∈ [−R,R]`. -/

/-- A clean uniform-from-pointwise+equiLipschitz lemma (the bespoke finite-grid
`ε/3`).  We use an integer grid of spacing `η = ε/(3Λ)` (or any positive spacing
if `Λ = 0`); the `Int.floor` snaps each `x ∈ [−R,R]` to the nearest grid node. -/
theorem locallyUniform_of_pointwise_of_equiLipschitz
    {z : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hpt : ∀ x, Tendsto (fun k => z k x) atTop (𝓝 (f x)))
    (hzL : ∀ k, ∀ x y, |z k x - z k y| ≤ Λ * |x - y|)
    (hfL : ∀ x y, |f x - f y| ≤ Λ * |x - y|) :
    LocallyUniformConverges z f := by
  intro R hR ε hε
  -- grid spacing η > 0 with Λ·η ≤ ε/3
  set η : ℝ := ε / (3 * (Λ + 1)) with hη_def
  have hη_pos : 0 < η := by
    rw [hη_def]
    apply div_pos hε
    positivity
  have hΛη : Λ * η ≤ ε / 3 := by
    have h3 : (0:ℝ) < 3 * (Λ + 1) := by positivity
    have hηeq : η = ε / (3 * (Λ + 1)) := hη_def
    have hηval : Λ * η = Λ * ε / (3 * (Λ + 1)) := by rw [hηeq]; ring
    rw [hηval, div_le_iff₀ h3]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0:ℝ) < 3)]
    nlinarith [hΛ, hε]
  -- the finite set of grid nodes covering [−R,R]: g i = -R + i·η, i ∈ Finset.range (Nnode+1)
  obtain ⟨Nnode, hNnode⟩ := exists_nat_gt (2 * R / η)
  -- node positions
  set node : ℕ → ℝ := fun i => -R + (i : ℝ) * η with hnode_def
  -- every x ∈ [−R,R] is within η of some node i ≤ Nnode
  have hcover : ∀ x ∈ Set.Icc (-R) R, ∃ i : ℕ, i ≤ Nnode ∧ |x - node i| ≤ η := by
    intro x hx
    rw [Set.mem_Icc] at hx
    obtain ⟨hx1, hx2⟩ := hx
    -- i = ⌊(x+R)/η⌋
    set t : ℝ := (x + R) / η with ht_def
    have ht_nonneg : 0 ≤ t := by
      rw [ht_def]; apply div_nonneg _ hη_pos.le; linarith
    set i : ℕ := ⌊t⌋₊ with hi_def
    refine ⟨i, ?_, ?_⟩
    · -- i ≤ Nnode
      have hi_le_t : (i : ℝ) ≤ t := Nat.floor_le ht_nonneg
      have ht_le : t ≤ 2 * R / η := by
        rw [ht_def]
        have hnum : x + R ≤ 2 * R := by nlinarith [hx2]
        gcongr
      have hiR : (i : ℝ) < (Nnode : ℝ) := lt_of_le_of_lt (le_trans hi_le_t ht_le) hNnode
      have : i < Nnode := by exact_mod_cast hiR
      exact le_of_lt this
    · -- |x - node i| ≤ η : i = ⌊t⌋, so x+R ∈ [iη, (i+1)η)
      have hi_le_t : (i : ℝ) ≤ t := Nat.floor_le ht_nonneg
      have ht_lt : t < (i : ℝ) + 1 := Nat.lt_floor_add_one t
      have hlow : (i : ℝ) * η ≤ x + R := by
        have := mul_le_mul_of_nonneg_right hi_le_t hη_pos.le
        rwa [ht_def, div_mul_cancel₀ _ (ne_of_gt hη_pos)] at this
      have hhigh : x + R < ((i : ℝ) + 1) * η := by
        have := (mul_lt_mul_of_pos_right ht_lt hη_pos)
        rwa [ht_def, div_mul_cancel₀ _ (ne_of_gt hη_pos)] at this
      rw [hnode_def]
      rw [abs_le]
      constructor <;> [nlinarith [hlow]; nlinarith [hhigh]]
  -- For each node i ≤ Nnode, pointwise convergence gives N_i with |z k (node i) - f (node i)| < ε/3
  have hpt3 : ∀ i : ℕ, ∀ᶠ k in atTop, |z k (node i) - f (node i)| < ε / 3 := by
    intro i
    -- turn tendsto into |·| < ε/3
    have h2 := Metric.tendsto_atTop.mp (hpt (node i)) (ε/3) (by linarith)
    obtain ⟨N, hN⟩ := h2
    rw [eventually_atTop]
    exact ⟨N, fun k hk => by simpa [Real.dist_eq] using hN k hk⟩
  -- common N over the finite node set {0,…,Nnode}
  have hfin : ∀ᶠ k in atTop, ∀ i : ℕ, i ≤ Nnode → |z k (node i) - f (node i)| < ε / 3 := by
    have : ∀ᶠ k in atTop, ∀ i ∈ Finset.range (Nnode + 1),
        |z k (node i) - f (node i)| < ε / 3 := by
      apply (eventually_all_finset (Finset.range (Nnode + 1))).mpr
      intro i _; exact hpt3 i
    filter_upwards [this] with k hk i hi
    exact hk i (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  -- finish: ε/3 triangle
  filter_upwards [hfin] with k hk x hx
  obtain ⟨i, hi_le, hxnode⟩ := hcover x hx
  have hnode_conv := hk i hi_le
  -- |z k x − f x| ≤ |z k x − z k node| + |z k node − f node| + |f node − f x|
  have hΛstep : Λ * |x - node i| ≤ ε / 3 :=
    le_trans (by gcongr) hΛη
  have hΛstep' : Λ * |node i - x| ≤ ε / 3 := by
    rw [abs_sub_comm]; exact hΛstep
  have hL1 : |z k x - z k (node i)| ≤ ε / 3 :=
    le_trans (hzL k x (node i)) hΛstep
  have hL3 : |f (node i) - f x| ≤ ε / 3 :=
    le_trans (hfL (node i) x) hΛstep'
  have htri1 : |z k x - f x|
      ≤ |z k x - z k (node i)| + |z k (node i) - f (node i)| + |f (node i) - f x| := by
    have e : z k x - f x
        = (z k x - z k (node i)) + (z k (node i) - f (node i)) + (f (node i) - f x) := by
      ring
    rw [e]
    calc |(z k x - z k (node i)) + (z k (node i) - f (node i)) + (f (node i) - f x)|
        ≤ |(z k x - z k (node i)) + (z k (node i) - f (node i))| + |f (node i) - f x| :=
          abs_add_le _ _
      _ ≤ |z k x - z k (node i)| + |z k (node i) - f (node i)| + |f (node i) - f x| := by
          have := abs_add_le (z k x - z k (node i)) (z k (node i) - f (node i))
          linarith
  have : |z k x - z k (node i)| + |z k (node i) - f (node i)| + |f (node i) - f x|
      < ε := by linarith [hL1, hL3, hnode_conv]
  linarith [htri1, this]

/-- **Deliverable 3 — local-uniform convergence of the Rothe orbit.**
The pointwise-convergent (committed `rotheLimit_tendsto`), uniformly-Lipschitz
(deliverable 2) orbit converges locally uniformly to `rotheLimit z`.  We carry
the uniform Lipschitz constant `Λ` for the iterates and the limit. -/
theorem rotheLimit_locallyUniform {z : ℕ → ℝ → ℝ} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hanti : ∀ x, Antitone (fun k => z k x))
    (hbdd : ∀ x, BddBelow (Set.range (fun k => z k x)))
    (hzL : ∀ k, ∀ x y, |z k x - z k y| ≤ Λ * |x - y|)
    (hfL : ∀ x y, |rotheLimit z x - rotheLimit z y| ≤ Λ * |x - y|) :
    LocallyUniformConverges z (rotheLimit z) :=
  locallyUniform_of_pointwise_of_equiLipschitz hΛ
    (fun x => rotheLimit_tendsto hanti hbdd x) hzL hfL

/-! ## Part 4 — continuity of the limit (discharging `hcont`)

Local-uniform convergence of continuous functions forces the limit continuous.
We give the direct `ε/3` argument (no committed `continuous_of_locallyUniform`
exists): at any `x₀`, take `R = |x₀|+1`, get a uniform `ε/3` index `k` on
`[−R,R]`, and use continuity of `z k` near `x₀`. -/

/-- **Deliverable 4 — continuity of the locally-uniform limit.**
If `z k` are all continuous and `z → f` locally uniformly, then `f` is
continuous.  This discharges the carried `hcont` of `rotheLimit_mem_trap`. -/
theorem continuous_of_locallyUniform {z : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hcont : ∀ k, Continuous (z k))
    (hLU : LocallyUniformConverges z f) :
    Continuous f := by
  rw [Metric.continuous_iff]
  intro x₀ ε hε
  set R : ℝ := |x₀| + 1 with hR_def
  have hR : 0 < R := by rw [hR_def]; positivity
  have hx₀R : x₀ ∈ Set.Icc (-R) R := by
    have : |x₀| ≤ R := by rw [hR_def]; linarith
    exact abs_le.mp this
  -- pick k with sup error < ε/3 on [−R,R]
  obtain ⟨k, hk⟩ := (hLU R hR (ε/3) (by linarith)).exists
  -- z k continuous at x₀: get δ s.t. dist x x₀ < δ → and x ∈ [−R,R]
  have hzk_cont := (hcont k).continuousAt (x := x₀)
  rw [Metric.continuousAt_iff] at hzk_cont
  obtain ⟨δ₁, hδ₁, hzkδ⟩ := hzk_cont (ε/3) (by linarith)
  -- also keep x within [−R,R]: dist x x₀ < 1 ⟹ |x| ≤ |x₀|+1 = R
  refine ⟨min δ₁ 1, by positivity, fun x hx => ?_⟩
  have hx_lt_δ₁ : dist x x₀ < δ₁ := lt_of_lt_of_le hx (min_le_left _ _)
  have hx_lt_1 : dist x x₀ < 1 := lt_of_lt_of_le hx (min_le_right _ _)
  have hxR : x ∈ Set.Icc (-R) R := by
    rw [Real.dist_eq] at hx_lt_1
    have : |x| ≤ R := by
      have := abs_sub_abs_le_abs_sub x x₀
      rw [hR_def]; nlinarith [abs_nonneg (x - x₀), le_of_lt hx_lt_1]
    exact abs_le.mp this
  -- triangle: dist (f x) (f x₀) ≤ |f x − z k x| + |z k x − z k x₀| + |z k x₀ − f x₀|
  have e1 : |f x - z k x| < ε/3 := by
    rw [abs_sub_comm]; exact hk x hxR
  have e2 : |z k x - z k x₀| < ε/3 := by
    rw [← Real.dist_eq]; exact hzkδ hx_lt_δ₁
  have e3 : |z k x₀ - f x₀| < ε/3 := hk x₀ hx₀R
  rw [Real.dist_eq]
  have e : f x - f x₀ = (f x - z k x) + (z k x - z k x₀) + (z k x₀ - f x₀) := by ring
  rw [e]
  have htri : |(f x - z k x) + (z k x - z k x₀) + (z k x₀ - f x₀)|
      ≤ |f x - z k x| + |z k x - z k x₀| + |z k x₀ - f x₀| := by
    calc |(f x - z k x) + (z k x - z k x₀) + (z k x₀ - f x₀)|
        ≤ |(f x - z k x) + (z k x - z k x₀)| + |z k x₀ - f x₀| := abs_add_le _ _
      _ ≤ |f x - z k x| + |z k x - z k x₀| + |z k x₀ - f x₀| := by
          have := abs_add_le (f x - z k x) (z k x - z k x₀); linarith
  linarith [htri, e1, e2, e3]

/-- **Deliverable 4, applied to the Rothe orbit — `hcont` discharged.**
If every iterate `z k` is continuous and the orbit converges locally uniformly
(deliverable 3), then `rotheLimit z` is continuous — exactly the hypothesis
`hcont` of `rotheLimit_mem_trap`. -/
theorem rotheLimit_continuous {z : ℕ → ℝ → ℝ}
    (hcont : ∀ k, Continuous (z k))
    (hLU : LocallyUniformConverges z (rotheLimit z)) :
    Continuous (rotheLimit z) :=
  continuous_of_locallyUniform hcont hLU

/-! ## Axiom audit -/

section AxiomAudit

#print axioms tailHi_weighted_abs_le
#print axioms tailLo_weighted_abs_le
#print axioms greenConvDeriv_abs_le
#print axioms crossImplicitStep_deriv_bound
#print axioms crossImplicitStep_deriv_bound_packaged
#print axioms crossImplicitStep_lipschitz
#print axioms locallyUniform_of_pointwise_of_equiLipschitz
#print axioms rotheLimit_locallyUniform
#print axioms continuous_of_locallyUniform
#print axioms rotheLimit_continuous

end AxiomAudit

end ShenWork.Paper1
