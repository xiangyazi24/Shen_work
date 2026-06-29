# PAPER1-POSITIVE-STRICT-NOCONTACT-API

Repo: `xiangyazi24/Shen_work`  
Relevant source commit: `5cde97f2`  
Goal: design the next honest Lean API for proving

```lean
∀ x, U x < upperBarrier (kappa c) (MChi p) x
```

for the non-explicit lower-pinned positive stationary profile, without hiding the target inside `ShenUpperBoundPositive` or replacing the constructed profile by an explicit logistic profile.

## 0. Source facts used

The current statement split is already good.  In `ShenWork/Paper1/StatementAssembly.lean`, the original positive branch still asks for `FrozenStationaryWaveProfile p c U ∧ ShenUpperBoundPositive p c U ∧ ...tail...` under the positive critical hypotheses (`Paper1PositiveCriticalFrozenStationaryBranch`, lines 135--157 in the fetched view).  The file already adds the pure normalizing theorem

```lean
ShenUpperBoundPositive.of_pos_strict_upperBarrier_MChi
```

which turns positivity plus strict comparison against `upperBarrier (kappa c) (MChi p)` into `ShenUpperBoundPositive p c U`; its proof is just the `MChi_eq_rpow_of_chi_nonneg_lt_one` rewrite and `upperBarrier` unfolding (fetched `StatementAssembly.lean`, lines 24--39).  The file also defines

```lean
Paper1PositiveCriticalFrozenStationaryStrictBarrierBranch
paper1_positiveCriticalBranch_of_strictBarrier
Paper1MainStatementStrictBarrierData
paper1_mainStatementTargets_of_strictBarrierData
```

so the upper-bound residual is already split down to the strict `MChi` barrier comparison (fetched `StatementAssembly.lean`, lines 41--74 and 90--99, plus lines 8--18 of the follow-up fetch).

`ShenUpperBoundPositive` itself is defined in `Statements.lean` as

```lean
∀ x, 0 < U x ∧
  U x < min ((1 / (1 - p.χ)) ^ (1 / p.α)) (Real.exp (-(kappa c) * x))
```

(fetched `Statements.lean`, lines 13--15).  The upper barrier is

```lean
upperBarrier κ M x = min M (Real.exp (-κ * x))
```

with branch and interface lemmas such as `upperBarrier_eq_M_of_le_exp`, `upperBarrier_eq_exp_of_exp_le`, the local eventual-equality lemmas, one-sided derivative lemmas, and `not_differentiableAt_upperBarrier_of_interface` (fetched `Statements.lean`, lines 12--166 around the `upperBarrier` block).

The lower-pinned profile shape is in `WaveRotheSchauder.lean`:

```lean
def InLowerPinnedMonotoneTrap (κ M : ℝ) (φ : ℝ → ℝ) (U : ℝ → ℝ) : Prop :=
  InMonotoneWaveTrapSet κ M U ∧ ∀ x, φ x ≤ U x
```

with `InLowerPinnedMonotoneTrap.bare`, `.lower`, `.profileNontrivial`, and `.pos` (fetched `WaveRotheSchauder.lean`, lines 3--31).  The sign-agnostic lower-pinned Schauder producer already has the useful output shape

```lean
∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierPlateau κ κtilde D) U ∧
  FrozenStationaryWaveProfile p c U
```

in `b1_chiNeg_existence_of_lowerBarrierPinnedSchauderData_stationary_rootPin` (fetched `WaveRotheSchauder.lean`, lines 37--64).  Despite the historical `chiNeg` name, that theorem is the correct lower-pinned fixed-point wrapper shape for this API.

The positive super-barrier file `WaveSuperBarrierPos.lean` proves the weak supersolution facts.  It says the away-from-interface branch facts are `frozenWaveOperator_upperBarrier_exp_region_nonpos_of_chi_nonneg`, `frozenWaveOperator_upperBarrier_const_region_nonpos_pos`, bundled as `Lemma_4_1_pos_frozen_holds_away_from_interface_at_kappa` (fetched `WaveSuperBarrierPos.lean`, lines 12--18).  It also proves the kink theorem

```lean
frozenWaveOperator_upperBarrier_interface_nonpos_pos
```

(fetched lines 127--133) and the whole-line theorem

```lean
whole_line_super_barrier_pos
```

(fetched lines 179--187).  These are weak `≤ 0` supersolution statements for the barrier, not strict no-contact theorems.

`StationaryStrongMaxPrinciple` in `WaveTrapProps.lean` proves positivity of a nontrivial stationary trapped profile:

```lean
∀ U, InMonotoneWaveTrapSet κ M U →
  (∀ x, frozenWaveOperator p c U U x = 0) →
  ProfileNontrivial U →
  ∀ x, 0 < U x
```

(fetched `WaveTrapProps.lean`, lines 6--12).  The supporting `StationaryLinearGronwallData` and `stationaryStrongMaxPrinciple_of_linearGronwall` are no-zero-contact machinery for `U`, not no-contact machinery for `upperBarrier - U` (fetched lines 88--112).

## 1. Minimal proposed Lean API for strict no-contact

Do **not** introduce a residual field that is already

```lean
∀ x, U x < upperBarrier (kappa c) (MChi p) x
```

unless the field is explicitly labeled as the final strict comparison residual.  A smaller and more honest API is a local contact-contradiction provider.  It does not assert global strictness; it only rules out equality on each smooth branch and at the nonsmooth interface.

```lean
import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper1.WaveRotheSchauder
import ShenWork.Paper1.WaveSuperBarrierPos
import ShenWork.Paper1.WaveTrapProps

open Filter Topology Real Set

namespace ShenWork.Paper1

/-- Branchwise no-contact API for the canonical positive upper barrier.

This is intentionally smaller than
`∀ x, U x < upperBarrier (kappa c) (MChi p) x` and much smaller than
`ShenUpperBoundPositive p c U`.  It says only that equality/contact is impossible
on each local piece of the nonsmooth barrier. -/
structure PositiveUpperBarrierLocalNoContact
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop where
  const_branch :
    ∀ x, MChi p < Real.exp (-(kappa c) * x) →
      U x = MChi p → False
  exp_branch :
    ∀ x, Real.exp (-(kappa c) * x) < MChi p →
      U x = Real.exp (-(kappa c) * x) → False
  interface :
    ∀ x, Real.exp (-(kappa c) * x) = MChi p →
      U x = MChi p → False

/-- Pure assembly target: non-strict trap membership plus branchwise no-contact
implies strict comparison with the nonsmooth upper barrier.  This theorem should
be a short proof by `lt_or_eq_of_le`, `lt_trichotomy`, and
`upperBarrier_eq_M_of_le_exp` / `upperBarrier_eq_exp_of_exp_le`. -/
theorem strict_upperBarrier_MChi_of_localNoContact
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U)
    (hno : PositiveUpperBarrierLocalNoContact p c U) :
    ∀ x, U x < upperBarrier (kappa c) (MChi p) x
-- proof intentionally omitted here: this is an API target, not a fake proof

end ShenWork.Paper1
```

The main residual theorem should then produce this branchwise API from the actual produced object.  Keep all mathematically necessary inputs explicit: the lower pin, stationarity, and the regularity needed for local branch/contact arguments.

```lean
import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper1.WaveRotheSchauder
import ShenWork.Paper1.WaveSuperBarrierPos
import ShenWork.Paper1.WaveTrapProps

open Filter Topology Real Set

namespace ShenWork.Paper1

/-- C² regularity needed by the local no-contact proof.
This should later be discharged from the existing stationary Green/Rothe
regularity route, not from the strict upper-bound conclusion. -/
def PositiveStationaryProfileC2 (U : ℝ → ℝ) : Prop :=
  Differentiable ℝ U ∧ Differentiable ℝ (deriv U)

/-- Main strict no-contact residual producer.

This is the theorem to aim for.  It is not circular: it does not assume
`ShenUpperBoundPositive`; it does not assume global strict comparison; it only
consumes the lower-pinned stationary profile, positive-regime parameters, and C²
regularity, and returns branchwise contact contradictions. -/
theorem positiveUpperBarrier_localNoContact_of_lowerPinnedStationary
    {p : CMParams} {c κtilde D : ℝ} {U : ℝ → ℝ}
    (hα : p.α = p.m + p.γ - 1)
    (hχ_nonneg : 0 ≤ p.χ)
    (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    (hc : 2 < c)
    (hgap : 0 < κtilde - kappa c) (hD : 0 < D)
    (hU : InLowerPinnedMonotoneTrap (kappa c) (MChi p)
      (lowerBarrierPlateau (kappa c) κtilde D) U)
    (hprofile : FrozenStationaryWaveProfile p c U)
    (hreg : PositiveStationaryProfileC2 U) :
    PositiveUpperBarrierLocalNoContact p c U
-- proof intentionally omitted here: this is the genuine branchwise comparison residual

/-- Strict comparison from the branchwise no-contact residual. -/
theorem strict_upperBarrier_MChi_of_positive_lowerPinnedStationary
    {p : CMParams} {c κtilde D : ℝ} {U : ℝ → ℝ}
    (hα : p.α = p.m + p.γ - 1)
    (hχ_nonneg : 0 ≤ p.χ)
    (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    (hc : 2 < c)
    (hgap : 0 < κtilde - kappa c) (hD : 0 < D)
    (hU : InLowerPinnedMonotoneTrap (kappa c) (MChi p)
      (lowerBarrierPlateau (kappa c) κtilde D) U)
    (hprofile : FrozenStationaryWaveProfile p c U)
    (hreg : PositiveStationaryProfileC2 U) :
    ∀ x, U x < upperBarrier (kappa c) (MChi p) x
-- proof should be `strict_upperBarrier_MChi_of_localNoContact hU.bare (...)`

end ShenWork.Paper1
```

If you want even finer residual names, split the producer into exactly three theorem targets:

```lean
theorem positiveUpperBarrier_constBranch_contact_absurd_of_lowerPinnedStationary
    {p : CMParams} {c κtilde D : ℝ} {U : ℝ → ℝ} {x : ℝ}
    (hα : p.α = p.m + p.γ - 1)
    (hχ_nonneg : 0 ≤ p.χ)
    (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    (hc : 2 < c)
    (hgap : 0 < κtilde - kappa c) (hD : 0 < D)
    (hU : InLowerPinnedMonotoneTrap (kappa c) (MChi p)
      (lowerBarrierPlateau (kappa c) κtilde D) U)
    (hprofile : FrozenStationaryWaveProfile p c U)
    (hreg : PositiveStationaryProfileC2 U)
    (hbranch : MChi p < Real.exp (-(kappa c) * x))
    (hcontact : U x = MChi p) :
    False

theorem positiveUpperBarrier_expBranch_contact_absurd_of_lowerPinnedStationary
    {p : CMParams} {c κtilde D : ℝ} {U : ℝ → ℝ} {x : ℝ}
    (hα : p.α = p.m + p.γ - 1)
    (hχ_nonneg : 0 ≤ p.χ)
    (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    (hc : 2 < c)
    (hgap : 0 < κtilde - kappa c) (hD : 0 < D)
    (hU : InLowerPinnedMonotoneTrap (kappa c) (MChi p)
      (lowerBarrierPlateau (kappa c) κtilde D) U)
    (hprofile : FrozenStationaryWaveProfile p c U)
    (hreg : PositiveStationaryProfileC2 U)
    (hbranch : Real.exp (-(kappa c) * x) < MChi p)
    (hcontact : U x = Real.exp (-(kappa c) * x)) :
    False

theorem positiveUpperBarrier_interface_contact_absurd_of_lowerPinnedStationary
    {p : CMParams} {c κtilde D : ℝ} {U : ℝ → ℝ} {x : ℝ}
    (hα : p.α = p.m + p.γ - 1)
    (hχ_nonneg : 0 ≤ p.χ)
    (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    (hc : 2 < c)
    (hgap : 0 < κtilde - kappa c) (hD : 0 < D)
    (hU : InLowerPinnedMonotoneTrap (kappa c) (MChi p)
      (lowerBarrierPlateau (kappa c) κtilde D) U)
    (hprofile : FrozenStationaryWaveProfile p c U)
    (hreg : PositiveStationaryProfileC2 U)
    (hinterface : Real.exp (-(kappa c) * x) = MChi p)
    (hcontact : U x = MChi p) :
    False
```

This is the most transparent non-fake decomposition.  The interface theorem is likely the easiest, because it should mostly consume the one-sided derivative lemmas for `upperBarrier`.  The exponential branch is the real PDE comparison theorem.  The constant branch may split into `0 < p.χ` and `p.χ = 0` cases.

## 2. Wrapper signature into `Paper1PositiveCriticalFrozenStationaryStrictBarrierBranch`

The strict-barrier branch still contains the right-tail field, so the wrapper must also take a tail provider.  Keep that separate from the strict no-contact API.

```lean
import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper1.WaveRotheSchauder

open Filter Topology Real Set

namespace ShenWork.Paper1

/-- Lower-pinned positive profile producer, preserving the lower pin rather than
erasing it to `InMonotoneWaveTrapSet`. -/
def Paper1PositiveLowerPinnedStationaryProfileProducer : Prop :=
  ∀ p : CMParams, p.α = p.m + p.γ - 1 →
    0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
    ∀ c : ℝ, 2 < c →
      ∃ κtilde D : ℝ, ∃ U : ℝ → ℝ,
        0 < κtilde - kappa c ∧ 0 < D ∧
        InLowerPinnedMonotoneTrap (kappa c) (MChi p)
          (lowerBarrierPlateau (kappa c) κtilde D) U ∧
        FrozenStationaryWaveProfile p c U

/-- Regularity provider for the produced lower-pinned stationary profile.  This is
not a theorem-scale conclusion; it is the C² input required by branchwise contact
arguments and should be discharged from the stationary Green/Rothe regularity
route. -/
def Paper1PositiveLowerPinnedStationaryC2Provider : Prop :=
  ∀ p : CMParams, p.α = p.m + p.γ - 1 →
    0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
    ∀ c : ℝ, 2 < c →
      ∀ κtilde D U,
        0 < κtilde - kappa c → 0 < D →
        InLowerPinnedMonotoneTrap (kappa c) (MChi p)
          (lowerBarrierPlateau (kappa c) κtilde D) U →
        FrozenStationaryWaveProfile p c U →
        PositiveStationaryProfileC2 U

/-- Branchwise no-contact provider for produced lower-pinned positive stationary
profiles.  It is smaller than strict global comparison and smaller than
`ShenUpperBoundPositive`. -/
def Paper1PositiveUpperBarrierNoContactProvider : Prop :=
  ∀ p : CMParams, p.α = p.m + p.γ - 1 →
    0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
    ∀ c : ℝ, 2 < c →
      ∀ κtilde D U,
        0 < κtilde - kappa c → 0 < D →
        InLowerPinnedMonotoneTrap (kappa c) (MChi p)
          (lowerBarrierPlateau (kappa c) κtilde D) U →
        FrozenStationaryWaveProfile p c U →
        PositiveStationaryProfileC2 U →
        PositiveUpperBarrierLocalNoContact p c U

/-- Tail provider kept orthogonal to strict no-contact. -/
def Paper1PositiveLowerPinnedTailProvider : Prop :=
  ∀ p : CMParams, p.α = p.m + p.γ - 1 →
    0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
    ∀ c : ℝ, 2 < c →
      ∀ κtilde D U,
        0 < κtilde - kappa c → 0 < D →
        InLowerPinnedMonotoneTrap (kappa c) (MChi p)
          (lowerBarrierPlateau (kappa c) κtilde D) U →
        FrozenStationaryWaveProfile p c U →
        ∀ κ₁, kappa c < κ₁ →
          κ₁ < min ((1 + p.α) * kappa c)
            (min (p.m * kappa c + 1 / 2) 1) →
          HasWaveRightTailAsymptotic c κ₁ U

/-- Assembly wrapper from lower-pinned profile production plus no-contact and tail
providers to the strict-barrier positive branch already expected by
`StatementAssembly.lean`. -/
theorem paper1_positiveStrictBarrierBranch_of_lowerPinnedProfile
    (hprod : Paper1PositiveLowerPinnedStationaryProfileProducer)
    (hreg : Paper1PositiveLowerPinnedStationaryC2Provider)
    (hno : Paper1PositiveUpperBarrierNoContactProvider)
    (htail : Paper1PositiveLowerPinnedTailProvider) :
    Paper1PositiveCriticalFrozenStationaryStrictBarrierBranch
-- proof sketch:
--   intro p hα hχ0 hχsmall c hc
--   rcases hprod p hα hχ0 hχsmall c hc with
--     ⟨κtilde, D, U, hgap, hD, hU, hprofile⟩
--   have hregU := hreg p hα hχ0 hχsmall c hc κtilde D U hgap hD hU hprofile
--   have hnoU := hno p hα hχ0 hχsmall c hc κtilde D U hgap hD hU hprofile hregU
--   refine ⟨U, hprofile, strict_upperBarrier_MChi_of_localNoContact hU.bare hnoU, ?_⟩
--   exact htail p hα hχ0 hχsmall c hc κtilde D U hgap hD hU hprofile

end ShenWork.Paper1
```

This wrapper is honest because:

* `hprod` produces the actual lower-pinned stationary `U`.
* `hreg` exposes the C² obligation needed by local comparison.
* `hno` is branchwise contact contradiction, not the global strict bound.
* `htail` is separate, because the strict no-contact API does not prove right-tail asymptotics.
* the conversion from local no-contact to the strict-barrier branch is pure trap/branch assembly.

## 3. Why existing SMP and super-solution lemmas are not enough directly

### `StationaryStrongMaxPrinciple`

`StationaryStrongMaxPrinciple` is useful but not the direct strict-upper-comparison theorem.  Its target is

```lean
∀ x, 0 < U x
```

from trapped stationarity and nontriviality.  It applies to the stationary profile `U` itself.  It does not apply to

```lean
B - U
```

where `B = upperBarrier (kappa c) (MChi p)`, because the gap is not packaged as an `InMonotoneWaveTrapSet` stationary solution of the same frozen operator, and `B` is nonsmooth at the interface.  The supporting `StationaryLinearGronwallData` similarly proves zero-Cauchy propagation for `U`, not no-contact against a nonsmooth supersolution.

Use SMP to support positivity/nontriviality and perhaps regularity pipelines; do not claim it proves `U < upperBarrier`.

### `whole_line_super_barrier_pos` and away-from-interface facts

`whole_line_super_barrier_pos` proves only

```lean
∀ x, frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0
```

for a trapped frozen old profile `u`.  This is an invariance/supersolution input.  It does not assert that a stationary fixed point strictly below the barrier cannot touch it.  To get strict comparison, one still needs a maximum/comparison principle that turns:

* `frozenWaveOperator p c U U = 0` for the fixed point,
* `frozenWaveOperator p c U B ≤ 0` for the barrier,
* `U ≤ B`, and
* endpoint/lower-pin/nontrivial data

into equality-contact contradiction.

The nonsmooth interface makes a global classical comparison theorem risky.  The existing source already has the interface derivative obstruction `not_differentiableAt_upperBarrier_of_interface`; therefore the comparison API should be branchwise plus a one-sided interface theorem.

## 4. Circular/vacuous inputs to avoid

Avoid these API shapes:

```lean
(hstrict : ∀ x, U x < upperBarrier (kappa c) (MChi p) x) → ...
```

as a “producer” input.  That is the conclusion.

Avoid:

```lean
(hupper : ShenUpperBoundPositive p c U) → ...
```

inside the no-contact producer.  This is stronger than the desired conclusion and would make the route circular.

Avoid deriving strictness from:

```lean
hU.bare : InMonotoneWaveTrapSet (kappa c) (MChi p) U
```

alone.  That only gives non-strict trap membership `U ≤ upperBarrier`.

Avoid using `logisticProfile_shenUpperBoundPositive` or related explicit-profile lemmas for the constructed fixed point unless a new theorem first proves the produced `U` equals `logisticProfile (kappa c)`.  No such equality theorem is part of the current route.

Avoid a global theorem over `upperBarrier - U` that assumes differentiability of `upperBarrier`; the source proves the interface is not differentiable.  If a later “general comparison theorem” is introduced, it should explicitly be a weak/one-sided comparison theorem and internally expose the same three branch/interface obligations listed above.

## 5. Recommended immediate next declarations

In order:

1. `PositiveUpperBarrierLocalNoContact`.
2. `strict_upperBarrier_MChi_of_localNoContact`.
3. `positiveUpperBarrier_interface_contact_absurd_of_lowerPinnedStationary` or the more general calculus lemma for any differentiable `U ≤ upperBarrier`.
4. `positiveUpperBarrier_constBranch_contact_absurd_of_lowerPinnedStationary`.
5. `positiveUpperBarrier_expBranch_contact_absurd_of_lowerPinnedStationary`.
6. `positiveUpperBarrier_localNoContact_of_lowerPinnedStationary`.
7. `paper1_positiveStrictBarrierBranch_of_lowerPinnedProfile`.

That sequence keeps every residual smaller than `ShenUpperBoundPositive`, gives a clean code-facing path into the already-committed strict-barrier branch, and avoids smuggling the target back in as an assumption.
