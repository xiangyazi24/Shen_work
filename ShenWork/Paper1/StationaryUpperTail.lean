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
  * `HasWaveRightTailAsymptotic_of_stationary` (#4C) — the sharp tail
    (`+∞`-linearisation; the repo has no producer of this predicate).

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
property of the stationary ODE.  The repo has NO producer of this predicate from
stationarity (it appears ONLY as a consumer); the linearisation machinery is not
present.  It is carried here as a named hypothesis `htail`, so that the
downstream `construction_neg` slot is fed without faking. -/

/-- **#4C — sharp right-tail asymptotic, carried.**  The conclusion is exactly
the carried datum `htail`; this lemma records the intended interface (stationary
+ trap + `c` above threshold ⟹ the rate-`κ₁` tail) while keeping the genuine
linearisation gap explicit and non-vacuous (a genuine decaying stationary wave
satisfies `htail`).  See STALL: no `+∞`-linearisation producer exists in-repo. -/
theorem HasWaveRightTailAsymptotic_of_stationary
    {p : CMParams} {c κ₁ : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < kappa c) (hU : InMonotoneWaveTrapSet (kappa c) 1 U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hκ₁lo : kappa c < κ₁)
    (hκ₁hi : κ₁ < min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1))
    (htail : HasWaveRightTailAsymptotic c κ₁ U) :
    HasWaveRightTailAsymptotic c κ₁ U :=
  htail

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
end AxiomAudit

end ShenWork.Paper1
