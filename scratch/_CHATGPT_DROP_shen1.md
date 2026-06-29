# PAPER1-LOWER-BARRIER-TAIL-SQUEEZE

Repo: `xiangyazi24/Shen_work`  
Relevant commit: `70dbb5e3`  
Task: Lean-facing proof skeleton for the pure lower-barrier squeeze theorem producing `HasWaveRightTailAsymptotic` without carrying the tail as an input.

## 1. Exact existing theorem names to use

From `ShenWork/Paper1/Statements.lean`:

```lean
def HasWaveRightTailAsymptotic (c κ₁ : ℝ) (U : ℝ → ℝ) : Prop :=
  Tendsto
    (fun x => Real.exp ((κ₁ - kappa c) * x) *
      (U x / Real.exp (-(kappa c) * x) - 1))
    atTop (𝓝 0)
```

This is the exact target definition.

The lower-barrier expansion and eventual right-tail branch are already available:

```lean
theorem lowerBarrierRaw_eq_exp_mul (κ κtilde D x : ℝ) :
    lowerBarrierRaw κ κtilde D x =
      Real.exp (-κ * x) * (1 - D * Real.exp (-(κtilde - κ) * x))

theorem lowerBarrierPlateau_eq_raw_of_xplus_lt
    {κ κtilde D x : ℝ} (hx : lowerBarrierXPlus κ κtilde D < x) :
    lowerBarrierPlateau κ κtilde D x = lowerBarrierRaw κ κtilde D x

theorem lowerBarrierPlateau_le_exp
    {κ κtilde D : ℝ} (hκ : 0 ≤ κ) (hD : 0 ≤ D) (x : ℝ) :
    lowerBarrierPlateau κ κtilde D x ≤ Real.exp (-κ * x)
```

The last one is not needed for the main squeeze if we use the trap upper bound, but it is a useful sanity check.

The upper trap projections are:

```lean
theorem InWaveTrapSet.le_upperBarrier {κ M : ℝ} {u : ℝ → ℝ}
    (h : InWaveTrapSet κ M u) (x : ℝ) :
    u x ≤ upperBarrier κ M x

theorem InWaveTrapSet.le_exp {κ M : ℝ} {u : ℝ → ℝ}
    (h : InWaveTrapSet κ M u) (x : ℝ) :
    u x ≤ Real.exp (-κ * x)
```

Use `InWaveTrapSet.le_exp`; it removes any need for assumptions on `M`.

From `ShenWork/Paper1/WaveRotheSchauder.lean`:

```lean
def InLowerPinnedMonotoneTrap
    (κ M : ℝ) (φ : ℝ → ℝ) (U : ℝ → ℝ) : Prop :=
  InMonotoneWaveTrapSet κ M U ∧ ∀ x, φ x ≤ U x

theorem InLowerPinnedMonotoneTrap.bare
    (hU : InLowerPinnedMonotoneTrap κ M φ U) :
    InMonotoneWaveTrapSet κ M U

theorem InLowerPinnedMonotoneTrap.lower
    (hU : InLowerPinnedMonotoneTrap κ M φ U) :
    ∀ x, φ x ≤ U x
```

Since `InMonotoneWaveTrapSet κ M U` is definitionally `InWaveTrapSet κ M U ∧ NonincreasingProfile U`, use `hU.bare.1.le_exp x` for the upper bound and `hU.lower x` for the lower bound.

## 2. Mathematical squeeze

Let `κ = kappa c` and set

```lean
E x := Real.exp (-κ * x)
δ x := D * Real.exp (-(κtilde - κ) * x)
W x := Real.exp ((κ₁ - κ) * x)
```

For all sufficiently large `x`, the plateau is on its raw branch, so

```lean
lowerBarrierPlateau κ κtilde D x
  = lowerBarrierRaw κ κtilde D x
  = E x * (1 - δ x)
```

The lower-pinned trap gives

```lean
E x * (1 - δ x) ≤ U x
```

and trap membership gives

```lean
U x ≤ E x.
```

Since `0 < E x`, divide by `E x`:

```lean
1 - δ x ≤ U x / E x ≤ 1.
```

Equivalently,

```lean
0 ≤ 1 - U x / E x ≤ δ x.
```

Multiplying by the positive weight `W x` gives

```lean
0 ≤ W x * (1 - U x / E x)
W x * (1 - U x / E x) ≤ D * Real.exp ((κ₁ - κtilde) * x).
```

Because `κ₁ < κtilde`, the right side tends to `0` at `atTop`.  Thus

```lean
W x * (1 - U x / E x) → 0,
```

and negating gives exactly

```lean
W x * (U x / E x - 1) → 0.
```

This is precisely `HasWaveRightTailAsymptotic c κ₁ U` after replacing `κ` by `kappa c`.

## 3. Recommended Lean skeleton

The cleanest API is one small eventual squeeze lemma plus the final theorem.  The first lemma is pure algebra/order; the second is pure `Tendsto`/squeeze.

```lean
import ShenWork.Paper1.WaveRotheSchauder

open Filter Topology Real Set

namespace ShenWork.Paper1

/-- Eventual weighted ratio-error bound from the lower-barrier plateau pin.

This is the only real algebraic step.  It uses:
* `lowerBarrierPlateau_eq_raw_of_xplus_lt`, eventually at `+∞`;
* `lowerBarrierRaw_eq_exp_mul`;
* `hU.lower` for the lower bound;
* `hU.bare.1.le_exp` for the upper bound.

No stationarity and no tail asymptotic are assumed. -/
theorem eventually_weighted_ratio_error_le_of_lowerBarrierPlateau_pin
    {κ κtilde D M κ₁ : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D)
    (hU : InLowerPinnedMonotoneTrap κ M
      (lowerBarrierPlateau κ κtilde D) U)
    (hκ₁hi : κ₁ < κtilde) :
    ∀ᶠ x in atTop,
      0 ≤ Real.exp ((κ₁ - κ) * x) *
          (1 - U x / Real.exp (-κ * x)) ∧
      Real.exp ((κ₁ - κ) * x) *
          (1 - U x / Real.exp (-κ * x)) ≤
        D * Real.exp ((κ₁ - κtilde) * x) := by
  -- Work eventually to the right of the plateau/raw transition.
  refine eventually_atTop.2 ⟨lowerBarrierXPlus κ κtilde D + 1, ?_⟩
  intro x hx
  have hxplus : lowerBarrierXPlus κ κtilde D < x := by
    linarith

  -- Positivity of the exponential denominator and weight.
  have hEpos : 0 < Real.exp (-κ * x) := Real.exp_pos _
  have hWnonneg : 0 ≤ Real.exp ((κ₁ - κ) * x) := (Real.exp_pos _).le

  -- Upper trap bound: U x ≤ exp(-κ x).
  have hUleE : U x ≤ Real.exp (-κ * x) :=
    hU.bare.1.le_exp x

  -- Lower pin, rewritten to the raw branch and then to the explicit expansion.
  have hraw_le_U : lowerBarrierRaw κ κtilde D x ≤ U x := by
    have hlower := hU.lower x
    rwa [lowerBarrierPlateau_eq_raw_of_xplus_lt hxplus] at hlower

  have hraw_exp :
      lowerBarrierRaw κ κtilde D x =
        Real.exp (-κ * x) *
          (1 - D * Real.exp (-(κtilde - κ) * x)) :=
    lowerBarrierRaw_eq_exp_mul κ κtilde D x

  have hlower_ratio :
      1 - D * Real.exp (-(κtilde - κ) * x) ≤
        U x / Real.exp (-κ * x) := by
    -- Divide `hraw_le_U` by the positive exponential.
    -- This is the expected compact proof; exact names may require `div_le_iff₀`.
    have hmul :
        Real.exp (-κ * x) *
            (1 - D * Real.exp (-(κtilde - κ) * x)) ≤ U x := by
      simpa [hraw_exp] using hraw_le_U
    -- One possible implementation:
    --   exact (le_div_iff₀ hEpos).2 hmul
    -- If the local Mathlib orientation differs, use:
    --   have := div_le_div_of_nonneg_right hmul hEpos.le
    --   simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc,
    --     inv_mul_cancel₀ (Real.exp_ne_zero _)] using this
    exact (le_div_iff₀ hEpos).2 hmul

  have hupper_ratio : U x / Real.exp (-κ * x) ≤ 1 := by
    -- Divide `U x ≤ exp(-κ x)` by the positive exponential.
    -- Expected implementation:
    --   exact (div_le_one hEpos).2 hUleE
    have h := div_le_div_of_nonneg_right hUleE hEpos.le
    simpa [div_self (Real.exp_ne_zero _)] using h

  have hratio_nonneg : 0 ≤ 1 - U x / Real.exp (-κ * x) := by
    linarith

  have hratio_le_delta :
      1 - U x / Real.exp (-κ * x) ≤
        D * Real.exp (-(κtilde - κ) * x) := by
    linarith

  constructor
  · exact mul_nonneg hWnonneg hratio_nonneg
  · calc
      Real.exp ((κ₁ - κ) * x) *
          (1 - U x / Real.exp (-κ * x))
          ≤ Real.exp ((κ₁ - κ) * x) *
              (D * Real.exp (-(κtilde - κ) * x)) := by
            exact mul_le_mul_of_nonneg_left hratio_le_delta hWnonneg
      _ = D * Real.exp ((κ₁ - κtilde) * x) := by
            rw [← Real.exp_add]
            ring

/-- The decaying exponential envelope used by the squeeze. -/
theorem tendsto_D_mul_exp_kappa1_sub_kappatilde_atTop_zero
    {D κ₁ κtilde : ℝ} (hκ₁hi : κ₁ < κtilde) :
    Tendsto (fun x : ℝ => D * Real.exp ((κ₁ - κtilde) * x)) atTop (𝓝 0) := by
  have hcoef : κ₁ - κtilde < 0 := sub_neg.mpr hκ₁hi
  have hlin : Tendsto (fun x : ℝ => (κ₁ - κtilde) * x) atTop atBot :=
    (tendsto_const_mul_atBot_of_neg hcoef).2 tendsto_id
  have hexp : Tendsto (fun x : ℝ => Real.exp ((κ₁ - κtilde) * x)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hlin
  simpa using tendsto_const_nhds.mul hexp

/-- Pure right-tail squeeze from a lower-barrier plateau pin.

This theorem proves `HasWaveRightTailAsymptotic` directly from the lower pin and
upper trap envelope.  It does not use stationarity, `FrozenStationaryWaveProfile`,
or any carried tail hypothesis. -/
theorem HasWaveRightTailAsymptotic_of_lowerBarrierPlateau_pin
    {c κtilde D M κ₁ : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < kappa c)
    (hgap : 0 < κtilde - kappa c) (hD : 0 < D)
    (hU : InLowerPinnedMonotoneTrap (kappa c) M
      (lowerBarrierPlateau (kappa c) κtilde D) U)
    (hκ₁lo : kappa c < κ₁) (hκ₁hi : κ₁ < κtilde) :
    HasWaveRightTailAsymptotic c κ₁ U := by
  unfold HasWaveRightTailAsymptotic

  let G : ℝ → ℝ := fun x =>
    Real.exp ((κ₁ - kappa c) * x) *
      (1 - U x / Real.exp (-(kappa c) * x))

  have hG_bounds :
      ∀ᶠ x in atTop,
        0 ≤ G x ∧ G x ≤ D * Real.exp ((κ₁ - κtilde) * x) := by
    simpa [G] using
      eventually_weighted_ratio_error_le_of_lowerBarrierPlateau_pin
        (κ := kappa c) (κtilde := κtilde) (D := D) (M := M)
        (κ₁ := κ₁) (U := U) hκ hgap hD hU hκ₁hi

  have hG_nonneg : ∀ᶠ x in atTop, 0 ≤ G x := hG_bounds.mono fun _ hx => hx.1
  have hG_le : ∀ᶠ x in atTop, G x ≤ D * Real.exp ((κ₁ - κtilde) * x) :=
    hG_bounds.mono fun _ hx => hx.2

  have hdecay :
      Tendsto (fun x : ℝ => D * Real.exp ((κ₁ - κtilde) * x)) atTop (𝓝 0) :=
    tendsto_D_mul_exp_kappa1_sub_kappatilde_atTop_zero hκ₁hi

  have hG_tendsto : Tendsto G atTop (𝓝 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hdecay hG_nonneg hG_le

  -- The target function is `-G`; the following equality is only algebra.
  have htarget_eq :
      (fun x : ℝ =>
        Real.exp ((κ₁ - kappa c) * x) *
          (U x / Real.exp (-(kappa c) * x) - 1)) =
      (fun x : ℝ => -G x) := by
    funext x
    simp [G]
    ring

  simpa [htarget_eq] using hG_tendsto.neg

end ShenWork.Paper1
```

## 4. Notes on likely compile adjustments

The skeleton above uses only standard theorem names already present in the repo plus common Mathlib lemmas.  Two tiny compile adjustments may be needed depending on imported lemma orientations:

1. In `hlower_ratio`, if `le_div_iff₀ hEpos` is not found under that exact name/orientation, replace it with the commented `div_le_div_of_nonneg_right` proof and simplify by `Real.exp_ne_zero`.
2. In the final squeeze, if `tendsto_of_tendsto_of_tendsto_of_le_of_le` expects pointwise inequalities rather than eventual inequalities in the local Mathlib version, use the primed/eventual variant if available, or convert `hG_nonneg` and `hG_le` by `filter_mono`/`eventually_of_forall` wrappers.  The repo already uses `tendsto_of_tendsto_of_tendsto_of_le_of_le` in `InWaveTrapSet.tendsto_atTop_zero`, so this is the right family of lemma.

No hypothesis about `M` is necessary.  The trap upper bound goes through `InWaveTrapSet.le_exp`, so the proof does not need `1 ≤ M` or `0 ≤ M`.

The lower assumption `hκ₁lo : kappa c < κ₁` is not used by the squeeze itself, except that it is part of the paper-facing tail range.  It should remain in the theorem signature to match `HasWaveRightTailAsymptotic` call sites and the positive branch frontier.

## 5. Why this is not fake

The proof does not assume `HasWaveRightTailAsymptotic`; it proves it by squeeze.

The proof does not assume stationarity or `FrozenStationaryWaveProfile`; the tail ratio follows from the lower-barrier plateau pin plus the trap upper envelope alone.

The proof does not replace `U` by the logistic profile.

The proof crucially preserves the lower-pinned witness.  If the positive construction erases the lower pin and returns only

```lean
InMonotoneWaveTrapSet (kappa c) M U
```

then this squeeze is no longer available: the upper trap alone gives only `U / exp ≤ 1`, not the lower ratio asymptotic.

## 6. Recommended integration point

Once this theorem is committed in a Lean file, the positive strict-barrier branch/tail assembly can consume it directly for any constructed lower-pinned profile with `κtilde` above the requested `κ₁`.  If the construction chooses

```lean
κtilde = min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1)
```

or any strictly larger internal exponent, then the theorem supplies exactly the full family required by `Paper1PositiveCriticalFrozenStationaryBranch`.
