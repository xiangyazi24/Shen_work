# Q2272 shen2: Route A audit for Paper1 positive right-tail asymptotic

Repo target: `xiangyazi24/Shen_work`, default branch `main` at commit `70dbb5e3`.

## Verdict

**Route A is valid, but only in the precise lower-pinned-trap form.**

From the current definitions, if the same constructed profile `U` is known to satisfy

```lean
InLowerPinnedMonotoneTrap (kappa c) M
  (lowerBarrierPlateau (kappa c) κtilde D) U
```

then the far-right lower barrier and the ordinary upper trap bound squeeze

```lean
U x / Real.exp (-(kappa c) * x) → 1
```

with the stronger rate needed for

```lean
HasWaveRightTailAsymptotic c κ₁ U
```

for every `κ₁ < κtilde`.  No stationary equation, elliptic `V` estimate, or linearized residual is needed for this **pure squeeze** step.

The correction to Q2264/e33be4fe is: the “upper bound alone cannot determine coefficient one” no-go is still true, but the lower-pinned plateau is not an upper bound alone. It carries the missing coefficient-one normalization because on the far right

```text
lowerBarrierRaw κ κtilde D x
  = exp(-κx) * (1 - D * exp(-(κtilde - κ)x)).
```

Thus `lowerBarrierPlateau ≤ U ≤ exp(-κx)` forces the ratio to be between `1 - D exp(-(κtilde-κ)x)` and `1`.

## Relevant current definitions / theorem names

### Tail target

File: `ShenWork/Paper1/Statements.lean`

```lean
def HasWaveRightTailAsymptotic (c κ₁ : ℝ) (U : ℝ → ℝ) : Prop :=
  Tendsto
    (fun x => Real.exp ((κ₁ - kappa c) * x) *
      (U x / Real.exp (-(kappa c) * x) - 1))
    atTop (𝓝 0)
```

### Lower raw barrier

File: `ShenWork/Paper1/Statements.lean`

```lean
def lowerBarrierRaw (κ κtilde D : ℝ) : ℝ → ℝ :=
  fun x => Real.exp (-κ * x) - D * Real.exp (-κtilde * x)
```

Relevant exact rewrite:

```lean
theorem lowerBarrierRaw_eq_exp_mul (κ κtilde D x : ℝ) :
    lowerBarrierRaw κ κtilde D x =
      Real.exp (-κ * x) * (1 - D * Real.exp (-(κtilde - κ) * x))
```

### Plateau barrier

File: `ShenWork/Paper1/Statements.lean`

```lean
def lowerBarrierPlateau (κ κtilde D : ℝ) : ℝ → ℝ :=
  fun x =>
    if x ≤ lowerBarrierXPlus κ κtilde D then
      lowerBarrierRaw κ κtilde D (lowerBarrierXPlus κ κtilde D)
    else
      lowerBarrierRaw κ κtilde D x
```

Far-right raw identification:

```lean
theorem lowerBarrierPlateau_eq_raw_of_xplus_lt
    {κ κtilde D x : ℝ} (hx : lowerBarrierXPlus κ κtilde D < x) :
    lowerBarrierPlateau κ κtilde D x = lowerBarrierRaw κ κtilde D x
```

This is enough because `lowerBarrierXPlus κ κtilde D < x` is eventually true at `atTop`.

### Upper trap

File: `ShenWork/Paper1/Statements.lean`

```lean
def upperBarrier (κ M : ℝ) : ℝ → ℝ :=
  fun x => min M (Real.exp (-κ * x))

lemma/theorem upperBarrier_le_exp (κ M x : ℝ) :
    upperBarrier κ M x ≤ Real.exp (-κ * x)
```

Trap definitions:

```lean
def InWaveTrapSet (κ M : ℝ) (u : ℝ → ℝ) : Prop :=
  IsCUnifBdd u ∧ ∀ x, 0 ≤ u x ∧ u x ≤ upperBarrier κ M x

def InMonotoneWaveTrapSet (κ M : ℝ) (u : ℝ → ℝ) : Prop :=
  InWaveTrapSet κ M u ∧ NonincreasingProfile u
```

Upper accessor:

```lean
theorem InWaveTrapSet.le_exp {κ M : ℝ} {u : ℝ → ℝ}
    (h : InWaveTrapSet κ M u) (x : ℝ) :
    u x ≤ Real.exp (-κ * x)
```

For a lower-pinned profile `hU`, the robust spelling is:

```lean
have hupper : U x ≤ Real.exp (-(kappa c) * x) :=
  ((hU.bare).1).le_exp x
```

If the local dot-notation theorem for the monotone trap is in scope, this may also work:

```lean
hU.bare.trap.le_exp x
```

but the definition-level safe spelling is `((hU.bare).1).le_exp x`.

### Lower-pinned trap

File: `ShenWork/Paper1/WaveRotheSchauder.lean`

```lean
def InLowerPinnedMonotoneTrap
    (κ M : ℝ) (φ : ℝ → ℝ) (U : ℝ → ℝ) : Prop :=
  InMonotoneWaveTrapSet κ M U ∧ ∀ x, φ x ≤ U x
```

Current projection theorems are:

```lean
theorem InLowerPinnedMonotoneTrap.bare
    (hU : InLowerPinnedMonotoneTrap κ M φ U) :
    InMonotoneWaveTrapSet κ M U

theorem InLowerPinnedMonotoneTrap.lower
    (hU : InLowerPinnedMonotoneTrap κ M φ U) :
    ∀ x, φ x ≤ U x
```

There is **not** a separate `InLowerPinnedMonotoneTrap.trap` projection in this file; the named projection is `.bare`.

## Minimal pure squeeze theorem

The clean theorem does not need stationarity. It also does not need `0 < kappa c` for the algebraic squeeze itself. For branch-facing use, keep `hκ₁lo` in the signature even though the proof only uses `κ₁ < κtilde`.

```lean
import ShenWork.Paper1.WaveRotheSchauder

open Filter Topology

namespace ShenWork.Paper1

noncomputable section

/-- Route A / pure squeeze: a lower-pinned plateau with exponent `κtilde`, plus
its inherited upper trap bound with exponent `kappa c`, gives the sharp right-tail
asymptotic for every `κ₁ < κtilde`.

No stationary equation is used. -/
theorem HasWaveRightTailAsymptotic_of_lowerPinnedMonotoneTrap
    {c κ₁ κtilde D M : ℝ} {U : ℝ → ℝ}
    (hD : 0 ≤ D)
    (_hκ₁lo : kappa c < κ₁)
    (hκ₁hi : κ₁ < κtilde)
    (hU : InLowerPinnedMonotoneTrap (kappa c) M
      (lowerBarrierPlateau (kappa c) κtilde D) U) :
    HasWaveRightTailAsymptotic c κ₁ U := by
  -- Proof skeleton:
  -- 1. Work eventually on `x > lowerBarrierXPlus (kappa c) κtilde D`, where
  --    `lowerBarrierPlateau = lowerBarrierRaw`.
  -- 2. Use the lower pin:
  --      lowerBarrierRaw (kappa c) κtilde D x ≤ U x.
  -- 3. Rewrite raw:
  --      lowerBarrierRaw ... x
  --        = exp (-(kappa c)*x) - D * exp (-κtilde*x).
  --    Equivalently, using `lowerBarrierRaw_eq_exp_mul`, after division by
  --    `exp (-(kappa c)*x)`:
  --      1 - D * exp (-(κtilde - kappa c)*x)
  --        ≤ U x / exp (-(kappa c)*x).
  -- 4. Use the upper trap:
  --      U x ≤ exp (-(kappa c)*x),
  --    available as `((hU.bare).1).le_exp x`.
  -- 5. Therefore eventually:
  --      |exp ((κ₁-kappa c)*x) *
  --        (U x / exp (-(kappa c)*x) - 1)|
  --        ≤ D * exp (-(κtilde - κ₁)*x).
  -- 6. Since `0 < κtilde - κ₁`, the RHS tends to zero.
  -- 7. Squeeze the absolute value to zero, hence the target tends to zero.
  sorry

end

end ShenWork.Paper1
```

The `sorry` above is only a placeholder in the proposed theorem skeleton. The proof is pure algebra/order/topology. It should not be introduced as an axiom.

## Slightly more Lean-friendly split

The proof will be easier if split into an eventual weighted-error bound and then the final squeeze.

```lean
import ShenWork.Paper1.WaveRotheSchauder

open Filter Topology

namespace ShenWork.Paper1

noncomputable section

/-- Eventual additive error bound supplied by the lower-pinned plateau. -/
theorem lowerPinnedMonotoneTrap_eventually_abs_sub_exp_le
    {c κtilde D M : ℝ} {U : ℝ → ℝ}
    (hD : 0 ≤ D)
    (hU : InLowerPinnedMonotoneTrap (kappa c) M
      (lowerBarrierPlateau (kappa c) κtilde D) U) :
    ∀ᶠ x in atTop,
      |U x - Real.exp (-(kappa c) * x)| ≤
        D * Real.exp (-κtilde * x) := by
  -- Eventually choose `x > lowerBarrierXPlus (kappa c) κtilde D`.
  -- Then:
  --   lowerBarrierPlateau_eq_raw_of_xplus_lt hx
  --   hU.lower x : lowerBarrierPlateau ... x ≤ U x
  -- gives:
  --   exp (-(kappa c)*x) - D*exp(-κtilde*x) ≤ U x
  -- via `lowerBarrierRaw` or `lowerBarrierRaw_eq_exp_mul`.
  -- The upper trap gives:
  --   U x ≤ exp (-(kappa c)*x)
  -- via `((hU.bare).1).le_exp x`.
  -- Hence `|U x - exp (-(kappa c)*x)| = exp (-(kappa c)*x) - U x`
  -- and this is `≤ D*exp(-κtilde*x)`.
  sorry

/-- Weighted ratio error bound; this is nearly the target, with an explicit
exponentially decaying majorant. -/
theorem lowerPinnedMonotoneTrap_eventually_weighted_ratio_error_le
    {c κ₁ κtilde D M : ℝ} {U : ℝ → ℝ}
    (hD : 0 ≤ D)
    (hU : InLowerPinnedMonotoneTrap (kappa c) M
      (lowerBarrierPlateau (kappa c) κtilde D) U) :
    ∀ᶠ x in atTop,
      |Real.exp ((κ₁ - kappa c) * x) *
        (U x / Real.exp (-(kappa c) * x) - 1)| ≤
        D * Real.exp (-(κtilde - κ₁) * x) := by
  -- Start from `lowerPinnedMonotoneTrap_eventually_abs_sub_exp_le hD hU`.
  -- Use the identity, valid because `Real.exp_ne_zero`:
  --
  --   Real.exp ((κ₁ - kappa c) * x) *
  --       (U x / Real.exp (-(kappa c) * x) - 1)
  --     = Real.exp (κ₁ * x) *
  --       (U x - Real.exp (-(kappa c) * x)).
  --
  -- Then multiply the additive bound by `Real.exp (κ₁*x)` and rewrite:
  --
  --   Real.exp (κ₁*x) * (D * Real.exp (-κtilde*x))
  --     = D * Real.exp (-(κtilde - κ₁)*x).
  sorry

/-- Final pure Route-A squeeze theorem. -/
theorem HasWaveRightTailAsymptotic_of_lowerPinnedMonotoneTrap'
    {c κ₁ κtilde D M : ℝ} {U : ℝ → ℝ}
    (hD : 0 ≤ D)
    (_hκ₁lo : kappa c < κ₁)
    (hκ₁hi : κ₁ < κtilde)
    (hU : InLowerPinnedMonotoneTrap (kappa c) M
      (lowerBarrierPlateau (kappa c) κtilde D) U) :
    HasWaveRightTailAsymptotic c κ₁ U := by
  unfold HasWaveRightTailAsymptotic
  have hbound :=
    lowerPinnedMonotoneTrap_eventually_weighted_ratio_error_le
      (c := c) (κ₁ := κ₁) (κtilde := κtilde) (D := D) (M := M)
      (U := U) hD hU
  have hcoef : 0 < κtilde - κ₁ := sub_pos.mpr hκ₁hi
  have hdecay :
      Tendsto (fun x : ℝ => D * Real.exp (-(κtilde - κ₁) * x))
        atTop (𝓝 0) := by
    -- `Real.tendsto_exp_atBot` after
    -- `Tendsto (fun x => (κtilde - κ₁) * x) atTop atTop`.
    sorry
  -- Use `hbound` to squeeze the norm/absolute value of the target to zero.
  -- Typical ending:
  --   apply tendsto_iff_norm_tendsto_zero.mpr
  --   simpa [Real.norm_eq_abs] using squeeze_zero ... hbound hdecay
  sorry

end

end ShenWork.Paper1
```

## Branch-facing theorem shape

The current Paper1 positive branch wants all

```lean
κ₁ < min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1)
```

for a single produced `U`. A fixed lower pin with exponent `κtilde` only gives rates `< κtilde`. Therefore a branch wrapper needs either:

1. choose/build the pinned fixed point with

```lean
min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1) ≤ κtilde
```

or

2. otherwise only conclude the tail for `κ₁ < κtilde`, which is weaker than the current branch if `κtilde` is below that minimum.

Concrete wrapper:

```lean
import ShenWork.Paper1.WaveRotheSchauder

open Filter Topology

namespace ShenWork.Paper1

noncomputable section

/-- Branch-rate wrapper: the lower-pinned squeeze discharges the whole current
branch tail interval, provided the lower-barrier exponent covers that interval. -/
theorem lowerPinnedMonotoneTrap_tail_family_for_branch
    {p : CMParams} {c κtilde D M : ℝ} {U : ℝ → ℝ}
    (hD : 0 ≤ D)
    (hcover :
      min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1) ≤ κtilde)
    (hU : InLowerPinnedMonotoneTrap (kappa c) M
      (lowerBarrierPlateau (kappa c) κtilde D) U) :
    ∀ κ₁, kappa c < κ₁ →
      κ₁ < min ((1 + p.α) * kappa c)
        (min (p.m * kappa c + 1 / 2) 1) →
      HasWaveRightTailAsymptotic c κ₁ U := by
  intro κ₁ hκ₁lo hκ₁hi
  exact HasWaveRightTailAsymptotic_of_lowerPinnedMonotoneTrap'
    (c := c) (κ₁ := κ₁) (κtilde := κtilde) (D := D) (M := M)
    (U := U) hD hκ₁lo (lt_of_lt_of_le hκ₁hi hcover) hU

end

end ShenWork.Paper1
```

## What is missing, if anything?

For the **pure squeeze theorem**, nothing analytic is missing. The current definitions are enough:

```text
hU.lower x
+ lowerBarrierPlateau_eq_raw_of_xplus_lt eventually
+ lowerBarrierRaw_eq_exp_mul
+ ((hU.bare).1).le_exp x
+ exponential decay when κ₁ < κtilde
```

For use in the **current positive branch**, the necessary exposed field is:

```lean
InLowerPinnedMonotoneTrap (kappa c) (MChi p)
  (lowerBarrierPlateau (kappa c) κtilde D) U
```

or at least the two pointwise facts it provides:

```lean
∀ᶠ x in atTop,
  lowerBarrierRaw (kappa c) κtilde D x ≤ U x

∀ x,
  U x ≤ Real.exp (-(kappa c) * x)
```

If a producer only returns

```lean
InMonotoneWaveTrapSet (kappa c) (MChi p) U
```

then Route A cannot start, because the lower pin is gone. The bare monotone trap gives the upper bound only, and upper bound alone still cannot determine coefficient one.

## Final answer

Route A is mathematically and Lean-API valid from the current definitions, with one branch-level caveat: to cover the full existing `Paper1PositiveCriticalFrozenStationaryBranch` interval, the fixed lower-barrier exponent `κtilde` must dominate the branch ceiling, or the branch target must be weakened to `κ₁ < κtilde`.
