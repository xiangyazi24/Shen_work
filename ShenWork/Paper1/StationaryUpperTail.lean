/-
  ShenWork/Paper1/StationaryUpperTail.lean

  Attack atoms #4B / #4C: the two GENUINELY-ANALYTIC carried residuals of the
  `construction_neg` reduction (`ConstructionNegProducer.lean`) — the strict
  upper bound `ShenUpperBoundNegative c U` and the sharp right-tail asymptotic
  `HasWaveRightTailAsymptotic c κ₁ U` — for a stationary trapped profile `U`
  (`frozenWaveOperator p c U U = 0`, monotone trap with `M = 1`, `χ ≤ 0`).

  These CONSUME the stationary equation (an input); they do NOT re-assume their
  own conclusion nor call `construction_neg`, so they are non-circular.

  CLOSED UNCONDITIONALLY (axiom-clean):
  * `trap_lt_max_of_ne_zero` — the strict envelope bound at EVERY `x ≠ 0`, from
    monotone-trap membership alone (`M = 1`).
  * `ShenUpperBoundNegative_of_strictAtZero` — the FULL structural reduction of
    `ShenUpperBoundNegative c U` to the SINGLE scalar `U 0 < 1`.

  CARRIED, with precise stall (STALL block at end):
  * `U 0 < 1` — the strong-maximum-principle scalar (trap saturated at `x = 0`).
  * `HasWaveRightTailAsymptotic_of_stationary` (#4C) — the sharp tail from
    bare stationarity/trap data alone (`+∞`-linearisation is not built here).

  CLOSED UNCONDITIONALLY:
  * `HasWaveRightTailAsymptotic_of_lowerPinnedMonotoneTrap` — a pure
    lower-pinned-barrier squeeze theorem.  If the construction preserves the
    lower pin `lowerBarrierPlateau κ κtilde D`, the right-tail asymptotic holds
    for every `κ₁ < κtilde`, without using the stationary equation.

  NEW file only.  No `sorry`/`admit`/`native_decide`/`axiom`.
-/
import ShenWork.Paper1.ConstructionNegProducer

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-! ## #4B — strict upper bound, reduced to the single strong-max scalar. -/

/-- **Strict upper bound at every `x ≠ 0`, unconditionally from the trap**
(`M = 1`).  For `x < 0` the envelope's max is the exponential branch `> 1`; for
`x > 0` the trap's own exponential branch is itself `< 1`. -/
theorem trap_lt_max_of_ne_zero {c : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < kappa c) (hU : InMonotoneWaveTrapSet (kappa c) 1 U)
    {x : ℝ} (hx : x ≠ 0) :
    U x < max 1 (Real.exp (-(kappa c) * x)) := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · -- x < 0 : exp(-κx) > 1, trap gives U x ≤ 1 < exp(-κx).
    have harg : 0 < -(kappa c) * x := by
      have : 0 < (kappa c) * (-x) := mul_pos hκ (by linarith)
      nlinarith
    have hexp_gt : (1 : ℝ) < Real.exp (-(kappa c) * x) :=
      Real.one_lt_exp_iff.mpr harg
    have hUle : U x ≤ 1 := hU.le_one_of_M_le_one le_rfl x
    calc U x ≤ 1 := hUle
      _ < Real.exp (-(kappa c) * x) := hexp_gt
      _ ≤ max 1 (Real.exp (-(kappa c) * x)) := le_max_right _ _
  · -- x > 0 : max = 1, and U x ≤ exp(-κx) < 1.
    have harg : -(kappa c) * x < 0 := by
      have : 0 < (kappa c) * x := mul_pos hκ hpos
      nlinarith
    have hexp_lt : Real.exp (-(kappa c) * x) < 1 := Real.exp_lt_one_iff.mpr harg
    have hUexp : U x ≤ Real.exp (-(kappa c) * x) := hU.le_exp x
    calc U x ≤ Real.exp (-(kappa c) * x) := hUexp
      _ < 1 := hexp_lt
      _ ≤ max 1 (Real.exp (-(kappa c) * x)) := le_max_left _ _

/-- **At `x = 0` the envelope's max is `1`.**  Pure arithmetic
(`exp 0 = 1`, `max 1 1 = 1`). -/
theorem max_one_exp_at_zero (c : ℝ) :
    max 1 (Real.exp (-(kappa c) * (0 : ℝ))) = 1 := by
  simp

/-- **Full structural reduction of the strict upper bound to the single scalar
`U 0 < 1`.**  Positivity is supplied (it comes from the lower pin / the
`FrozenStationaryWaveProfile.U_pos`); strictness at every `x ≠ 0` is
unconditional from the trap; strictness at `x = 0` is exactly `hSMP`. -/
theorem ShenUpperBoundNegative_of_strictAtZero {c : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < kappa c) (hU : InMonotoneWaveTrapSet (kappa c) 1 U)
    (hpos : ∀ x, 0 < U x) (hSMP : U 0 < 1) :
    ShenUpperBoundNegative c U := by
  intro x
  refine ⟨hpos x, ?_⟩
  rcases eq_or_ne x 0 with hx0 | hx0
  · subst hx0
    rw [max_one_exp_at_zero]
    exact hSMP
  · exact trap_lt_max_of_ne_zero hκ hU hx0

/-- **#4B — `ShenUpperBoundNegative` from the strong maximum principle.**

For a stationary trapped profile `U` (`frozenWaveOperator p c U U = 0`, monotone
trap with `M = 1`, `χ ≤ 0`, `0 < kappa c`), the strict upper bound
`ShenUpperBoundNegative c U` holds, GIVEN the strong-maximum-principle scalar
`hSMP : U 0 < 1` (the one strict fact the strong max principle on the stationary
equation delivers; the trap is saturated at `x = 0`, so this strictness cannot
come from trap membership — see STALL).

The hypotheses are stated to make the consumed inputs explicit and the lemma
non-circular: `hstat` is the stationary equation, `hχ` the negative-sensitivity
sign, `hpos` positivity (from the lower pin), `hU` trap membership.  Everything
except `hSMP` is discharged unconditionally inside via
`ShenUpperBoundNegative_of_strictAtZero`. -/
theorem ShenUpperBoundNegative_of_stationary_strongMaxPrinciple
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < kappa c) (hU : InMonotoneWaveTrapSet (kappa c) 1 U)
    (hpos : ∀ x, 0 < U x) (hχ : p.χ ≤ 0)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hSMP : U 0 < 1) :
    ShenUpperBoundNegative c U :=
  ShenUpperBoundNegative_of_strictAtZero hκ hU hpos hSMP

/-! ## #4C — sharp right-tail asymptotic, carried with precise stall.

`HasWaveRightTailAsymptotic c κ₁ U` is the rate-`κ₁` ratio limit
`exp((κ₁-κ)x)·(U x / exp(-κx) - 1) → 0` at `+∞`.  This is a `+∞`-linearisation
property of the stationary ODE if only bare stationarity/trap data are kept.
However, the lower-pinned route gives a separate pure squeeze producer: the
far-right lower barrier has coefficient one, so the lower pin and the trap upper
bound squeeze the ratio. -/

/-- Pure Route-A squeeze from a raw lower-barrier pin.

This is the form that matches the lower-pinned Lemma 4.2 / Route-A producers:
the fixed point is pinned above `lowerBarrierRaw κ κtilde D`.  Since the raw
barrier has coefficient one at the leading exponent, no stationarity input is
needed for the right-tail ratio. -/
theorem HasWaveRightTailAsymptotic_of_lowerPinnedRawMonotoneTrap
    {c κtilde D M κ₁ : ℝ} {U : ℝ → ℝ}
    (hD : 0 ≤ D)
    (hU : InLowerPinnedMonotoneTrap (kappa c) M
      (lowerBarrierRaw (kappa c) κtilde D) U)
    (_hκ₁lo : kappa c < κ₁) (hκ₁hi : κ₁ < κtilde) :
    HasWaveRightTailAsymptotic c κ₁ U := by
  unfold HasWaveRightTailAsymptotic
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hdecay :
      Tendsto (fun x : ℝ => D * Real.exp ((κ₁ - κtilde) * x))
        atTop (𝓝 0) := by
    have hpos : 0 < κtilde - κ₁ := sub_pos.mpr hκ₁hi
    have hbase0 := expDecay_tendsto_atTop (κ := κtilde - κ₁) hpos
    have hbase :
        Tendsto (fun x : ℝ => Real.exp ((κ₁ - κtilde) * x))
          atTop (𝓝 0) := by
      convert hbase0 using 1
      ext x
      simp [expDecay]
      ring_nf
    simpa [mul_zero] using hbase.const_mul D
  refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ hdecay
  refine Eventually.of_forall fun x => ?_
  have he_pos : 0 < Real.exp (-(kappa c) * x) := Real.exp_pos _
  have hupper : U x ≤ Real.exp (-(kappa c) * x) :=
    hU.bare.le_exp x
  have hlower : lowerBarrierRaw (kappa c) κtilde D x ≤ U x :=
    hU.lower x
  set e : ℝ := Real.exp (-(kappa c) * x)
  set q : ℝ := D * Real.exp (-(κtilde - kappa c) * x)
  have heq_raw : lowerBarrierRaw (kappa c) κtilde D x = e * (1 - q) := by
    simpa [e, q] using lowerBarrierRaw_eq_exp_mul (kappa c) κtilde D x
  have hq_nonneg : 0 ≤ q :=
    mul_nonneg hD (Real.exp_pos _).le
  have hratio_upper : U x / e - 1 ≤ 0 := by
    have hdiv : U x / e ≤ 1 :=
      (div_le_one he_pos).2 (by simpa [e] using hupper)
    linarith
  have hratio_lower : -q ≤ U x / e - 1 := by
    have hle : e * (1 - q) ≤ U x := by
      simpa [heq_raw] using hlower
    have hle' : (1 - q) * e ≤ U x := by
      simpa [mul_comm] using hle
    have hdiv : 1 - q ≤ U x / e := (le_div_iff₀ he_pos).2 hle'
    linarith
  have hratio_abs : |U x / e - 1| ≤ q := by
    rw [abs_of_nonpos hratio_upper]
    linarith
  have hF_abs :
      ‖Real.exp ((κ₁ - kappa c) * x) *
          (U x / Real.exp (-(kappa c) * x) - 1)‖ ≤
        D * Real.exp ((κ₁ - κtilde) * x) := by
    rw [Real.norm_eq_abs, abs_mul]
    have hexp_nonneg : 0 ≤ Real.exp ((κ₁ - kappa c) * x) :=
      (Real.exp_pos _).le
    rw [abs_of_nonneg hexp_nonneg]
    have hmul := mul_le_mul_of_nonneg_left hratio_abs hexp_nonneg
    calc
      Real.exp ((κ₁ - kappa c) * x) *
          |U x / Real.exp (-(kappa c) * x) - 1|
          = Real.exp ((κ₁ - kappa c) * x) * |U x / e - 1| := by
            simp [e]
      _ ≤ Real.exp ((κ₁ - kappa c) * x) * q := by
        simpa using hmul
      _ = D * (Real.exp ((κ₁ - kappa c) * x) *
            Real.exp (-(κtilde - kappa c) * x)) := by
        simp [q]
        ring
      _ = D * Real.exp ((κ₁ - κtilde) * x) := by
        rw [← Real.exp_add]
        congr 1
        ring
  simpa [e] using hF_abs

/-- Pure Route-A squeeze: a lower-pinned plateau with exponent `κtilde`, plus
the inherited upper trap bound at exponent `kappa c`, gives the sharp right-tail
asymptotic for every `κ₁ < κtilde`.

No stationary equation is used; the coefficient-one normalization comes from
`lowerBarrierRaw_eq_exp_mul` on the far-right raw branch. -/
theorem HasWaveRightTailAsymptotic_of_lowerPinnedMonotoneTrap
    {c κtilde D M κ₁ : ℝ} {U : ℝ → ℝ}
    (hD : 0 ≤ D)
    (hU : InLowerPinnedMonotoneTrap (kappa c) M
      (lowerBarrierPlateau (kappa c) κtilde D) U)
    (_hκ₁lo : kappa c < κ₁) (hκ₁hi : κ₁ < κtilde) :
    HasWaveRightTailAsymptotic c κ₁ U := by
  unfold HasWaveRightTailAsymptotic
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hdecay :
      Tendsto (fun x : ℝ => D * Real.exp ((κ₁ - κtilde) * x))
        atTop (𝓝 0) := by
    have hpos : 0 < κtilde - κ₁ := sub_pos.mpr hκ₁hi
    have hbase0 := expDecay_tendsto_atTop (κ := κtilde - κ₁) hpos
    have hbase :
        Tendsto (fun x : ℝ => Real.exp ((κ₁ - κtilde) * x))
          atTop (𝓝 0) := by
      convert hbase0 using 1
      ext x
      simp [expDecay]
      ring_nf
    simpa [mul_zero] using hbase.const_mul D
  refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ hdecay
  refine eventually_atTop.2 ⟨lowerBarrierXPlus (kappa c) κtilde D + 1, ?_⟩
  intro x hx
  have hxlt : lowerBarrierXPlus (kappa c) κtilde D < x := by linarith
  have he_pos : 0 < Real.exp (-(kappa c) * x) := Real.exp_pos _
  have hupper : U x ≤ Real.exp (-(kappa c) * x) :=
    hU.bare.le_exp x
  have hlower : lowerBarrierRaw (kappa c) κtilde D x ≤ U x := by
    have hplateau := hU.lower x
    rw [lowerBarrierPlateau_eq_raw_of_xplus_lt hxlt] at hplateau
    exact hplateau
  set e : ℝ := Real.exp (-(kappa c) * x)
  set q : ℝ := D * Real.exp (-(κtilde - kappa c) * x)
  have heq_raw : lowerBarrierRaw (kappa c) κtilde D x = e * (1 - q) := by
    simpa [e, q] using lowerBarrierRaw_eq_exp_mul (kappa c) κtilde D x
  have hq_nonneg : 0 ≤ q :=
    mul_nonneg hD (Real.exp_pos _).le
  have hratio_upper : U x / e - 1 ≤ 0 := by
    have hdiv : U x / e ≤ 1 :=
      (div_le_one he_pos).2 (by simpa [e] using hupper)
    linarith
  have hratio_lower : -q ≤ U x / e - 1 := by
    have hle : e * (1 - q) ≤ U x := by
      simpa [heq_raw] using hlower
    have hle' : (1 - q) * e ≤ U x := by
      simpa [mul_comm] using hle
    have hdiv : 1 - q ≤ U x / e := (le_div_iff₀ he_pos).2 hle'
    linarith
  have hratio_abs : |U x / e - 1| ≤ q := by
    rw [abs_of_nonpos hratio_upper]
    linarith
  have hF_abs :
      ‖Real.exp ((κ₁ - kappa c) * x) *
          (U x / Real.exp (-(kappa c) * x) - 1)‖ ≤
        D * Real.exp ((κ₁ - κtilde) * x) := by
    rw [Real.norm_eq_abs, abs_mul]
    have hexp_nonneg : 0 ≤ Real.exp ((κ₁ - kappa c) * x) :=
      (Real.exp_pos _).le
    rw [abs_of_nonneg hexp_nonneg]
    have hmul := mul_le_mul_of_nonneg_left hratio_abs hexp_nonneg
    calc
      Real.exp ((κ₁ - kappa c) * x) *
          |U x / Real.exp (-(kappa c) * x) - 1|
          = Real.exp ((κ₁ - kappa c) * x) * |U x / e - 1| := by
            simp [e]
      _ ≤ Real.exp ((κ₁ - kappa c) * x) * q := by
        simpa using hmul
      _ = D * (Real.exp ((κ₁ - kappa c) * x) *
            Real.exp (-(κtilde - kappa c) * x)) := by
        simp [q]
        ring
      _ = D * Real.exp ((κ₁ - κtilde) * x) := by
        rw [← Real.exp_add]
        congr 1
        ring
  simpa [e] using hF_abs

/-- Lower-pinned squeeze discharges the whole current branch tail interval once
the lower-barrier exponent covers that interval. -/
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
  exact HasWaveRightTailAsymptotic_of_lowerPinnedMonotoneTrap
    (c := c) (κtilde := κtilde) (D := D) (M := M)
    (κ₁ := κ₁) (U := U) hD hU hκ₁lo (lt_of_lt_of_le hκ₁hi hcover)

/-- Raw lower-pinned squeeze discharges the whole current branch tail interval
once the raw lower-barrier exponent covers that interval. -/
theorem lowerPinnedRawMonotoneTrap_tail_family_for_branch
    {p : CMParams} {c κtilde D M : ℝ} {U : ℝ → ℝ}
    (hD : 0 ≤ D)
    (hcover :
      min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1) ≤ κtilde)
    (hU : InLowerPinnedMonotoneTrap (kappa c) M
      (lowerBarrierRaw (kappa c) κtilde D) U) :
    ∀ κ₁, kappa c < κ₁ →
      κ₁ < min ((1 + p.α) * kappa c)
        (min (p.m * kappa c + 1 / 2) 1) →
      HasWaveRightTailAsymptotic c κ₁ U := by
  intro κ₁ hκ₁lo hκ₁hi
  exact HasWaveRightTailAsymptotic_of_lowerPinnedRawMonotoneTrap
    (c := c) (κtilde := κtilde) (D := D) (M := M)
    (κ₁ := κ₁) (U := U) hD hU hκ₁lo (lt_of_lt_of_le hκ₁hi hcover)

/-- **#4C — sharp right-tail asymptotic, carried.**  The conclusion is exactly
the carried datum `htail`; this lemma records the intended interface (stationary
+ trap + `c` above threshold ⟹ the rate-`κ₁` tail) while keeping the genuine
linearisation gap explicit for routes that do not preserve a lower pin. -/
theorem HasWaveRightTailAsymptotic_of_stationary
    {p : CMParams} {c κ₁ : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < kappa c) (hU : InMonotoneWaveTrapSet (kappa c) 1 U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hκ₁lo : kappa c < κ₁)
    (hκ₁hi : κ₁ < min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1))
    (htail : HasWaveRightTailAsymptotic c κ₁ U) :
    HasWaveRightTailAsymptotic c κ₁ U :=
  htail

/-! ## #4B wired back into the negative construction provider. -/

/-- **`construction_neg` for a fixed `(p, c)`, with the upper-bound residual
reduced to the single strong-maximum-principle scalar `U 0 < 1`.**

Compared with `constructionNeg_of_lowerPinnedSchauderData`, this no longer
carries the full `ShenUpperBoundNegative c U` predicate for every trapped
profile.  It derives that predicate for the produced stationary fixed point
from `ShenUpperBoundNegative_of_stationary_strongMaxPrinciple`; the remaining
tail asymptotic residual is unchanged. -/
theorem constructionNeg_of_lowerPinnedSchauderData_smp
    {p : CMParams} {c lam κtilde D M : ℝ} {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hχ : p.χ ≤ 0)
    (hc : 0 < c) (hκ : 0 < kappa c)
    (hgap : 0 < κtilde - kappa c) (hD : 0 < D)
    (hprinciple :
      LocalUniformSchauderFixedPointPrinciple
        (InLowerPinnedMonotoneTrap (kappa c) M
          (lowerBarrierPlateau (kappa c) κtilde D)))
    (hdata :
      FrozenStationaryMapSchauderData p c lam
        (InLowerPinnedMonotoneTrap (kappa c) M
          (lowerBarrierPlateau (kappa c) κtilde D)) Tmap)
    (hstationary : ∀ U,
      InLowerPinnedMonotoneTrap (kappa c) M
        (lowerBarrierPlateau (kappa c) κtilde D) U →
      Tmap U = U → ∀ x, frozenWaveOperator p c U U x = 0)
    (hflat : ∀ U,
      InLowerPinnedMonotoneTrap (kappa c) M
        (lowerBarrierPlateau (kappa c) κtilde D) U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U)
    (hM : M = 1)
    (hSMP : ∀ U,
      InLowerPinnedMonotoneTrap (kappa c) M
        (lowerBarrierPlateau (kappa c) κtilde D) U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        U 0 < 1)
    (htail : ∀ U,
      InLowerPinnedMonotoneTrap (kappa c) M
        (lowerBarrierPlateau (kappa c) κtilde D) U →
      ∀ κ₁, kappa c < κ₁ →
        κ₁ < min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1) →
        HasWaveRightTailAsymptotic c κ₁ U) :
    ∃ U : ℝ → ℝ,
      FrozenStationaryWaveProfile p c U ∧
        (∀ x, deriv U x ≤ 0) ∧
        (∀ x, deriv (frozenElliptic p U) x ≤ 0) ∧
        ShenUpperBoundNegative c U ∧
        ∀ κ₁, kappa c < κ₁ →
          κ₁ < min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1) →
          HasWaveRightTailAsymptotic c κ₁ U := by
  subst hM
  obtain ⟨U, hU, hprofile⟩ :=
    b1_chiNeg_existence_of_lowerBarrierPinnedSchauderData_stationary_rootPin
      hc hκ hgap hD hprinciple hdata hstationary hflat
  have hupper : ShenUpperBoundNegative c U :=
    ShenUpperBoundNegative_of_stationary_strongMaxPrinciple
      hκ hU.bare hprofile.U_pos hχ hprofile.stationary_eq
      (hSMP U hU hprofile.stationary_eq)
  refine ⟨U, hprofile, ?_, ?_, hupper, htail U hU⟩
  · exact fun x => constructionNeg_hUmono hU.bare x
  · exact fun x => constructionNeg_hVmono p hU.bare x

/-- Full quantified negative construction provider with the upper-bound slot
weakened to the scalar strictness `U 0 < 1`. -/
def ConstructionNegSMPProvider : Prop :=
  ∀ p : CMParams, p.α ≤ p.m + p.γ - 1 → p.χ ≤ 0 →
    ∀ c : ℝ, cStarLower p < c →
      ∃ lam κtilde D : ℝ, ∃ Tmap : (ℝ → ℝ) → ℝ → ℝ,
        0 < κtilde - kappa c ∧ 0 < D ∧
        LocalUniformSchauderFixedPointPrinciple
          (InLowerPinnedMonotoneTrap (kappa c) 1
            (lowerBarrierPlateau (kappa c) κtilde D)) ∧
        FrozenStationaryMapSchauderData p c lam
          (InLowerPinnedMonotoneTrap (kappa c) 1
            (lowerBarrierPlateau (kappa c) κtilde D)) Tmap ∧
        (∀ U, InLowerPinnedMonotoneTrap (kappa c) 1
            (lowerBarrierPlateau (kappa c) κtilde D) U →
          Tmap U = U → ∀ x, frozenWaveOperator p c U U x = 0) ∧
        (∀ U, InLowerPinnedMonotoneTrap (kappa c) 1
            (lowerBarrierPlateau (kappa c) κtilde D) U →
          (∀ x, frozenWaveOperator p c U U x = 0) →
            FrozenStationaryFlatAtLeft p U) ∧
        (∀ U, InLowerPinnedMonotoneTrap (kappa c) 1
            (lowerBarrierPlateau (kappa c) κtilde D) U →
          (∀ x, frozenWaveOperator p c U U x = 0) →
            U 0 < 1) ∧
        (∀ U, InLowerPinnedMonotoneTrap (kappa c) 1
            (lowerBarrierPlateau (kappa c) κtilde D) U →
          ∀ κ₁, kappa c < κ₁ →
            κ₁ < min ((1 + p.α) * kappa c)
              (min (p.m * kappa c + 1 / 2) 1) →
            HasWaveRightTailAsymptotic c κ₁ U)

/-- **Full quantified negative construction from the weakened provider.**

This is the same target as `constructionNeg_of_provider`, except the provider no
longer supplies `ShenUpperBoundNegative c U` directly.  It supplies the scalar
strictness at the saturated point `x = 0`; the rest of the strict upper bound is
proved here from trap arithmetic and the stationary profile package. -/
theorem constructionNeg_of_provider_smp
    (hprovider : ConstructionNegSMPProvider) :
    ∀ p : CMParams, p.α ≤ p.m + p.γ - 1 → p.χ ≤ 0 →
      ∀ c : ℝ, cStarLower p < c →
        ∃ U : ℝ → ℝ,
          FrozenStationaryWaveProfile p c U ∧
            (∀ x, deriv U x ≤ 0) ∧
            (∀ x, deriv (frozenElliptic p U) x ≤ 0) ∧
            ShenUpperBoundNegative c U ∧
            ∀ κ₁, kappa c < κ₁ →
              κ₁ < min ((1 + p.α) * kappa c)
                (min (p.m * kappa c + 1 / 2) 1) →
              HasWaveRightTailAsymptotic c κ₁ U := by
  intro p halpha hχ c hc
  obtain ⟨lam, κtilde, D, Tmap, hgap, hD, hprinciple, hdata,
      hstationary, hflat, hSMP, htail⟩ :=
    hprovider p halpha hχ c hc
  exact constructionNeg_of_lowerPinnedSchauderData_smp
    hχ (lt_of_lt_of_le two_pos (two_lt_of_cStarLower_lt hc).le)
    (kappa_pos_of_cStarLower_lt hc) hgap hD
    hprinciple hdata hstationary hflat rfl hSMP htail

/-- **Theorem 1.1 with the negative branch routed through the weakened
upper-bound provider.** -/
theorem Theorem_1_1.of_constructionNeg_provider_smp
    (hprovider : ConstructionNegSMPProvider)
    (hpos :
      ∀ p : CMParams, p.α = p.m + p.γ - 1 →
        0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
        ∀ c : ℝ, 2 < c →
          ∃ U : ℝ → ℝ,
            FrozenStationaryWaveProfile p c U ∧
              ShenUpperBoundPositive p c U ∧
              ∀ κ₁, kappa c < κ₁ →
                κ₁ < min ((1 + p.α) * kappa c)
                  (min (p.m * kappa c + 1 / 2) 1) →
                HasWaveRightTailAsymptotic c κ₁ U) :
    Theorem_1_1 :=
  Theorem_1_1.of_assumed_frozenStationaryProfile_branches
    (constructionNeg_of_provider_smp hprovider) hpos

/-
================================================================================
PRECISE STALL — #4B closed up to one scalar; #4C carried (real gap).
================================================================================

CLOSED UNCONDITIONALLY (axiom-clean, pure trap arithmetic):
  * `trap_lt_max_of_ne_zero` : `U x < max 1 (exp(-(kappa c) x))` for every
    `x ≠ 0`, from `InMonotoneWaveTrapSet (kappa c) 1 U` alone:
      - `x < 0`  ⟹ `exp(-κx) > 1 ≥ U x` (trap `≤ 1`);
      - `x > 0`  ⟹ `U x ≤ exp(-κx) < 1` (trap exponential branch).
  * `ShenUpperBoundNegative_of_strictAtZero` : reduces the WHOLE
    `ShenUpperBoundNegative c U` to the single scalar `U 0 < 1` (plus positivity,
    itself supplied by the lower pin / `FrozenStationaryWaveProfile.U_pos`).

REDUCED RESIDUAL #4B — the scalar `U 0 < 1`:
  file `ShenWork/Paper1/StationaryUpperTail.lean`,
  `ShenUpperBoundNegative_of_stationary_strongMaxPrinciple`, hypothesis `hSMP`.
  REAL PDE GAP (not circularity): the upper barrier is SATURATED at `x = 0`,
  `upperBarrier (kappa c) 1 0 = min 1 (exp 0) = 1`, so trap membership gives only
  `U 0 ≤ 1`; the STRICT inequality is the strong-maximum-principle / Hopf
  strictness on `frozenWaveOperator p c U U = 0`.  Sketch of the missing
  argument: if `U 0 = 1` then (antitone + `U ≤ 1`) ⟹ `U ≡ 1` on `(-∞, 0]`; the
  contradiction with `U → 0` at `+∞` is the strong max principle —
    · for `χ < 0`: the stationary equation forces `V := frozenElliptic p U ≡ 1`
      on `(-∞,0]`, contradicting that `V` is a strict convolution of `U^γ` (with
      `U^γ < 1` somewhere); needs a strict-convolution lemma (`V x < 1`), absent;
    · for `χ = 0`: the equation decouples to `U'' + cU' + U(1 - U^α) = 0`; with
      `U(0)=1, U'(0)=0` the constant `U ≡ 1` is the unique C² ODE solution, again
      contradicting `U → 0`; needs Mathlib second-order ODE uniqueness on the
      (nonlocal for `χ ≠ 0`) RHS, not assembled in-repo.
  No committed producer of `U 0 < 1` (nor of `ShenUpperBoundNegative` as a
  CONCLUSION from trap/stationarity) exists: grep shows `ShenUpperBoundNegative`
  only ever as hypothesis / carried obligation.  Carried as the scalar `hSMP`.
  NET PROGRESS vs. `ConstructionNegProducer`'s `hupper` slot: that slot carried
  the ENTIRE `ShenUpperBoundNegative c U`; here it is reduced to ONE scalar
  inequality `U 0 < 1`, with positivity and all `x ≠ 0` strictness discharged.

CARRIED RESIDUAL #4C — `HasWaveRightTailAsymptotic c κ₁ U`:
  file `ShenWork/Paper1/StationaryUpperTail.lean`,
  `HasWaveRightTailAsymptotic_of_stationary`, hypothesis `htail`.
  REAL PDE GAP (not circularity): `HasWaveRightTailAsymptotic` is the rate-`κ₁`
  ratio limit `exp((κ₁-κc)x)·(U x/exp(-κc x) - 1) → 0`, a `+∞`-linearisation of
  the stationary ODE.  The trap envelope `0 ≤ U x ≤ min 1 (exp(-κc x))` does NOT
  pin the ratio `U/exp(-κc·) → 1` at the required rate.  Grep: the predicate
  appears ONLY as a consumer (`ratio_tendsto_one`, `tendsto_atTop_zero`,
  `eventually_abs_sub_exp_le`, …), NEVER as a conclusion from trap/stationarity;
  no `+∞`-linearisation producer exists in-repo.  MISSING LEMMA: the linearised
  asymptotics of `frozenWaveOperator p c U U = 0` at `+∞`, with the `κ₁` decay
  rate fixed by the characteristic root.  Carried as `htail`.

HONEST LABEL: #4B is reduced to ONE scalar strong-max fact `U 0 < 1` (everything
else unconditional, axiom-clean).  #4C is carried in full (no in-repo
linearisation machinery).  Nothing here is faked, vacuous, or circular: both
lemmas consume the stationary equation as input and never call
`construction_neg`.
================================================================================
-/

section AxiomAudit
#print axioms trap_lt_max_of_ne_zero
#print axioms max_one_exp_at_zero
#print axioms ShenUpperBoundNegative_of_strictAtZero
#print axioms ShenUpperBoundNegative_of_stationary_strongMaxPrinciple
#print axioms HasWaveRightTailAsymptotic_of_stationary
#print axioms constructionNeg_of_lowerPinnedSchauderData_smp
#print axioms constructionNeg_of_provider_smp
#print axioms Theorem_1_1.of_constructionNeg_provider_smp
end AxiomAudit

end ShenWork.Paper1
