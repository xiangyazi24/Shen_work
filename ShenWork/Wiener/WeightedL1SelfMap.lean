import ShenWork.Wiener.WeightedL1HeatDeriv
import ShenWork.Wiener.WeightedL1Complete
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# The `√t` divergence-Duhamel self-map bound on `A^r` (brick 6)

This brick assembles the time-integral contraction estimate for the Duhamel
fixed-point map.  For a flux curve `B : ℝ → WA r` the Duhamel-`∂ₓ` integral
`H(t) := ∫₀ᵗ S(t−s) ∂ₓ B(s) ds` (a `WA r`-valued Bochner interval integral, well
defined because `WA r` is a Banach space — `instCompleteSpace`) satisfies

  `‖∫₀ᵗ S(t−s) ∂ₓ B(s) ds‖_{A^r} ≤ √(2/e) · √t · sup_{[0,t]} ‖B‖`.

The three ingredients:

* **`heatDerivOp τ`** — the spatial smoothing operator `S(τ) ∂ₓ` lifted from the
  committed coefficient multiplier `heatDerivMul` (closed under `MemW` by
  `memW_heatDerivMul`) to the bundled algebra `WA r`, with the operator bound
  `‖heatDerivOp τ a‖ ≤ (1/√(2eτ)) · ‖a‖` inherited from `heatDerivMul_bound`.
* **The scalar integral** `∫₀ᵗ (t−s)^{−1/2} ds = 2√t`, computed via the
  substitution `u = t − s` (`intervalIntegral.integral_comp_sub_left`) and
  `integral_rpow` with exponent `−1/2 > −1`.
* **The Bochner norm-integral** `‖∫ F‖ ≤ ∫ ‖F‖`
  (`intervalIntegral.norm_integral_le_integral_norm`) together with the
  pointwise majorant and interval-integral monotonicity on the open interval
  (`intervalIntegral.integral_mono_on_of_le_Ioo`), the majorant
  `s ↦ (Msup/√(2e))·(t−s)^{−1/2}` being interval-integrable (its `t^{−1/2}`
  singularity at `s=t` is integrable, `intervalIntegrable_rpow'`).

The integrability of the integrand `s ↦ heatDerivOp (t−s) (B s)` itself is a
genuine *input* (`hFint`): a sufficient condition, not the conclusion.  It is
satisfiable precisely because the singular majorant is integrable; it is NOT a
disguised assumption of the goal.
-/

open scoped BigOperators
open MeasureTheory intervalIntegral

namespace ShenWork.Wiener

namespace WA

variable {r : ℕ}

/-! ### The lifted `S(τ) ∂ₓ` operator on `WA r`. -/

/-- The divergence-smoothing operator `S(τ) ∂ₓ` lifted to the bundled weighted
Wiener algebra `WA r`: for `τ > 0` it applies the committed multiplier
`heatDerivMul τ` to the coefficients (closed under `MemW` by
`memW_heatDerivMul`); for `τ ≤ 0` (off the physical regime) it is `0`.  The
guard makes the operator a total function `ℝ → WA r → WA r`, so the Duhamel
integrand `s ↦ heatDerivOp (t−s) (B s)` is well defined as a plain curve. -/
noncomputable def heatDerivOp (τ : ℝ) (a : WA r) : WA r :=
  if hτ : 0 < τ then ⟨heatDerivMul τ a.toFun, memW_heatDerivMul hτ a.mem⟩ else 0

/-- On the physical regime `τ > 0`, `heatDerivOp` is the bundled multiplier. -/
@[simp] theorem heatDerivOp_toFun_of_pos {τ : ℝ} (hτ : 0 < τ) (a : WA r) :
    (heatDerivOp τ a).toFun = heatDerivMul τ a.toFun := by
  simp only [heatDerivOp, dif_pos hτ]

/-- The operator bound `‖S(τ) ∂ₓ a‖ ≤ (1/√(2eτ)) · ‖a‖`, inherited from the
committed coefficient bound `heatDerivMul_bound`. -/
theorem norm_heatDerivOp_le {τ : ℝ} (hτ : 0 < τ) (a : WA r) :
    ‖heatDerivOp τ a‖ ≤ (1 / Real.sqrt (2 * Real.exp 1 * τ)) * ‖a‖ := by
  simpa only [norm_def, heatDerivOp_toFun_of_pos hτ] using heatDerivMul_bound hτ a.mem

/-! ### The scalar integral `∫₀ᵗ (t−s)^{−1/2} ds = 2√t`. -/

/-- The real scalar integral `∫₀ᵗ (t−s)^{−1/2} ds = 2√t`, by the substitution
`u = t − s` and `integral_rpow` at exponent `−1/2 > −1`. -/
theorem integral_sub_rpow_neg_half (t : ℝ) :
    (∫ s in (0:ℝ)..t, (t - s) ^ (-(1:ℝ)/2)) = 2 * Real.sqrt t := by
  have hsub : (∫ s in (0:ℝ)..t, (t - s) ^ (-(1:ℝ)/2))
      = ∫ x in (t - t)..(t - 0), x ^ (-(1:ℝ)/2) :=
    integral_comp_sub_left (fun x => x ^ (-(1:ℝ)/2)) t
  rw [hsub, sub_self, sub_zero]
  have hr : (-1 : ℝ) < -(1:ℝ)/2 := by norm_num
  rw [integral_rpow (Or.inl hr)]
  have hexp : -(1:ℝ)/2 + 1 = 1/2 := by norm_num
  rw [hexp]
  have hz : (0:ℝ) ^ ((1:ℝ)/2) = 0 := by
    rw [Real.rpow_eq_zero_iff_of_nonneg le_rfl]; exact ⟨rfl, by norm_num⟩
  rw [hz, sub_zero]
  have hthalf : t ^ ((1:ℝ)/2) = Real.sqrt t := (Real.sqrt_eq_rpow t).symm
  rw [hthalf]
  ring

/-! ### The `√t` divergence-Duhamel self-map bound. -/

/-- Interval-integrability of the singular scalar majorant
`s ↦ (t−s)^{−1/2}` on `0..t` (its `s=t` singularity is integrable). -/
theorem intervalIntegrable_sub_rpow_neg_half (t : ℝ) :
    IntervalIntegrable (fun s => (t - s) ^ (-(1:ℝ)/2)) MeasureTheory.volume 0 t := by
  have hr : (-1 : ℝ) < -(1:ℝ)/2 := by norm_num
  have h0 : IntervalIntegrable (fun x => x ^ (-(1:ℝ)/2)) MeasureTheory.volume t 0 :=
    intervalIntegrable_rpow' hr
  have hcomp := h0.comp_sub_left t
  simpa only [sub_self, sub_zero] using hcomp

/-- **The √t divergence-Duhamel self-map bound (brick 6).**  For a flux curve
`B : ℝ → WA r` whose Duhamel-`∂ₓ` integrand `s ↦ heatDerivOp (t−s) (B s)` is
interval-integrable on `0..t` (`hFint`, a genuine sufficient condition — the
`t^{−1/2}` singularity has an integrable majorant, so this is NOT the
conclusion), and bounded `‖B s‖ ≤ Msup` on the open interval, the Bochner
interval integral satisfies
`‖∫₀ᵗ S(t−s) ∂ₓ B(s) ds‖ ≤ √(2/e) · √t · Msup`. -/
theorem duhamel_selfmap_bound {r : ℕ} {B : ℝ → WA r} {t Msup : ℝ} (ht : 0 < t)
    (hFint : IntervalIntegrable (fun s => heatDerivOp (t - s) (B s))
      MeasureTheory.volume 0 t)
    (hBsup : ∀ s ∈ Set.Ioo (0 : ℝ) t, ‖B s‖ ≤ Msup) (hMsup : 0 ≤ Msup) :
    ‖∫ s in (0:ℝ)..t, heatDerivOp (t - s) (B s)‖
      ≤ Real.sqrt (2 / Real.exp 1) * Real.sqrt t * Msup := by
  set c : ℝ := Msup * (1 / Real.sqrt (2 * Real.exp 1)) with hc
  have hcnn : 0 ≤ c := by positivity
  -- Step 1 (Bochner): ‖∫ F‖ ≤ ∫ ‖F‖.
  have hstep1 : ‖∫ s in (0:ℝ)..t, heatDerivOp (t - s) (B s)‖
      ≤ ∫ s in (0:ℝ)..t, ‖heatDerivOp (t - s) (B s)‖ :=
    norm_integral_le_integral_norm ht.le
  -- The singular majorant and its interval-integrability.
  have hmajint : IntervalIntegrable (fun s => c * (t - s) ^ (-(1:ℝ)/2))
      MeasureTheory.volume 0 t :=
    (intervalIntegrable_sub_rpow_neg_half t).const_mul c
  -- Step 2 (pointwise majorant on the open interval) + monotonicity.
  have hptwise : ∀ s ∈ Set.Ioo (0:ℝ) t,
      ‖heatDerivOp (t - s) (B s)‖ ≤ c * (t - s) ^ (-(1:ℝ)/2) := by
    intro s hs
    have hτ : 0 < t - s := by have := hs.2; linarith
    have hb1 : ‖heatDerivOp (t - s) (B s)‖
        ≤ (1 / Real.sqrt (2 * Real.exp 1 * (t - s))) * ‖B s‖ :=
      norm_heatDerivOp_le hτ (B s)
    have hsplit : Real.sqrt (2 * Real.exp 1 * (t - s))
        = Real.sqrt (2 * Real.exp 1) * Real.sqrt (t - s) := by
      rw [Real.sqrt_mul (by positivity)]
    have hrpow : (t - s) ^ (-(1:ℝ)/2) = 1 / Real.sqrt (t - s) := by
      rw [show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring, Real.rpow_neg hτ.le,
        ← Real.sqrt_eq_rpow, one_div]
    have hcoef : (1 / Real.sqrt (2 * Real.exp 1 * (t - s)))
        = (1 / Real.sqrt (2 * Real.exp 1)) * (t - s) ^ (-(1:ℝ)/2) := by
      rw [hsplit, hrpow]
      rw [one_div, mul_inv, one_div, one_div]
    calc ‖heatDerivOp (t - s) (B s)‖
        ≤ (1 / Real.sqrt (2 * Real.exp 1 * (t - s))) * ‖B s‖ := hb1
      _ ≤ (1 / Real.sqrt (2 * Real.exp 1 * (t - s))) * Msup :=
          mul_le_mul_of_nonneg_left (hBsup s hs)
            (by positivity)
      _ = c * (t - s) ^ (-(1:ℝ)/2) := by rw [hcoef, hc]; ring
  have hstep2 : (∫ s in (0:ℝ)..t, ‖heatDerivOp (t - s) (B s)‖)
      ≤ ∫ s in (0:ℝ)..t, c * (t - s) ^ (-(1:ℝ)/2) :=
    integral_mono_on_of_le_Ioo ht.le hFint.norm hmajint hptwise
  -- Step 3: compute the majorant integral = c · 2√t.
  have hstep3 : (∫ s in (0:ℝ)..t, c * (t - s) ^ (-(1:ℝ)/2))
      = c * (2 * Real.sqrt t) := by
    rw [intervalIntegral.integral_const_mul, integral_sub_rpow_neg_half]
  -- Combine and simplify the constant: c·2√t = √(2/e)·√t·Msup.
  have hconst : c * (2 * Real.sqrt t)
      = Real.sqrt (2 / Real.exp 1) * Real.sqrt t * Msup := by
    have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hse : (0 : ℝ) < Real.sqrt (Real.exp 1) := Real.sqrt_pos.mpr he
    have h2e : Real.sqrt (2 * Real.exp 1) = Real.sqrt 2 * Real.sqrt (Real.exp 1) :=
      Real.sqrt_mul (by norm_num) _
    have hdiv : Real.sqrt (2 / Real.exp 1) = Real.sqrt 2 / Real.sqrt (Real.exp 1) := by
      rw [Real.sqrt_div (by norm_num)]
    -- key scalar identity: (1/√(2e))·2 = √(2/e).
    have hsqrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hkey : (1 / Real.sqrt (2 * Real.exp 1)) * 2 = Real.sqrt (2 / Real.exp 1) := by
      rw [h2e, hdiv]
      field_simp
      rw [hsqrt2]
    rw [hc]
    calc Msup * (1 / Real.sqrt (2 * Real.exp 1)) * (2 * Real.sqrt t)
        = ((1 / Real.sqrt (2 * Real.exp 1)) * 2) * Real.sqrt t * Msup := by ring
      _ = Real.sqrt (2 / Real.exp 1) * Real.sqrt t * Msup := by rw [hkey]
  calc ‖∫ s in (0:ℝ)..t, heatDerivOp (t - s) (B s)‖
      ≤ ∫ s in (0:ℝ)..t, ‖heatDerivOp (t - s) (B s)‖ := hstep1
    _ ≤ ∫ s in (0:ℝ)..t, c * (t - s) ^ (-(1:ℝ)/2) := hstep2
    _ = c * (2 * Real.sqrt t) := hstep3
    _ = Real.sqrt (2 / Real.exp 1) * Real.sqrt t * Msup := hconst

end WA

end ShenWork.Wiener
