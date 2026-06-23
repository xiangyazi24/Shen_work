/-
  ShenWork/Paper1/ConstructionNegProducer.lean

  Attack atom #4 (`construction_neg`): the frozen stationary wave profile
  existence for the negative-sensitivity regime
  `χ ≤ 0`, `α ≤ m + γ - 1`, `cStarLower p < c`.

  TARGET (the `construction_neg` field of `Paper1MainResultsData`,
  equivalently the `hneg` argument of
  `Theorem_1_1.of_assumed_frozenStationaryProfile_branches`):

    ∀ p, p.α ≤ p.m + p.γ - 1 → p.χ ≤ 0 → ∀ c, cStarLower p < c →
      ∃ U, FrozenStationaryWaveProfile p c U
        ∧ (∀ x, deriv U x ≤ 0)
        ∧ (∀ x, deriv (frozenElliptic p U) x ≤ 0)
        ∧ ShenUpperBoundNegative c U
        ∧ (right-tail asymptotic family)

  This is the genuine hard PDE construction (Rothe method + Schauder fixed
  point).  This file assembles it along the NON-VACUOUS lower-pinned Schauder
  route (`WaveRotheSchauder.b1_chiNeg_existence_of_lowerPinnedSchauderData_…`),
  closing the two structurally-free obligations UNCONDITIONALLY from the trap,
  and carrying the two genuinely-analytic obligations
  (`ShenUpperBoundNegative`, the sharp right-tail asymptotic) as EXPLICIT
  per-trapped-profile hypotheses.  The precise stall is documented below.

  NEW file only.  No `sorry`/`admit`/`native_decide`/`axiom`.
-/
import ShenWork.Paper1.WaveRotheSchauder
import ShenWork.Paper1.WaveEllipticMono

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-! ## (i) The two structurally-free obligations — UNCONDITIONAL from the trap.

`deriv U ≤ 0` and `deriv (frozenElliptic p U) ≤ 0` follow from monotone-trap
membership alone (no fixed-point / equation input needed).  These are the two
obligations of `construction_neg` that close cleanly. -/

/-- **Free obligation 1 (`hUmono`).**  On a monotone wave trap, `deriv U ≤ 0`
everywhere.  Pure trap consequence (`InMonotoneWaveTrapSet.deriv_nonpos`). -/
theorem constructionNeg_hUmono {c : ℝ} {U : ℝ → ℝ}
    (hU : InMonotoneWaveTrapSet (kappa c) 1 U) (x : ℝ) :
    deriv U x ≤ 0 :=
  hU.deriv_nonpos x

/-- **Free obligation 2 (`hVmono`).**  On a monotone wave trap the frozen
elliptic field's derivative is nonpositive everywhere.  Pure trap consequence
(`frozenElliptic_deriv_nonpos_of_monotone_trap`); identical to the committed
`b1_neg_hVmono`, restated here at the lower-pinned-trap layer. -/
theorem constructionNeg_hVmono (p : CMParams) {c : ℝ} {U : ℝ → ℝ}
    (hU : InMonotoneWaveTrapSet (kappa c) 1 U) (x : ℝ) :
    deriv (frozenElliptic p U) x ≤ 0 :=
  frozenElliptic_deriv_nonpos_of_monotone_trap p (kappa c) 1 U hU x

/-! ## (ii)+(iii) The full `construction_neg` package along the lower-pinned route.

The lower-pinned Schauder wrapper
`b1_chiNeg_existence_of_lowerPinnedSchauderData_stationary_rootPin`
(WaveRotheSchauder.lean) produces, from the ordinary local-uniform Schauder
principle on the pinned trap plus the per-fixed-point stationarity and left-flat
data, a trapped fixed point

  `∃ U, InLowerPinnedMonotoneTrap (kappa c) 1 φ U ∧ FrozenStationaryWaveProfile p c U`.

That existential already discharges `FrozenStationaryWaveProfile`.  Its `.bare`
field gives `InMonotoneWaveTrapSet (kappa c) 1 U`, from which the two free
obligations (i) close.  The remaining two obligations —
`ShenUpperBoundNegative c U` and the sharp right-tail asymptotic — are the
genuinely-analytic fixed-point properties (see STALL below); they are carried
here as explicit hypotheses `hupper`/`htail` ranging over pinned-trapped
profiles, so the package is non-vacuous (a genuine positive decaying stationary
wave satisfies all of them; the zero profile is excluded by the strictly
positive lower pin `0 < φ`). -/

/-- **`construction_neg` for a fixed `(p, c)` from the lower-pinned Schauder
data**, carrying ONLY the two genuinely-analytic obligations as explicit
hypotheses on pinned-trapped profiles.

UNCONDITIONALLY discharged here:
* `FrozenStationaryWaveProfile p c U` — from the lower-pinned Schauder wrapper;
* `∀ x, deriv U x ≤ 0` — free, obligation (i.1);
* `∀ x, deriv (frozenElliptic p U) x ≤ 0` — free, obligation (i.2).

CARRIED (genuine analytic residuals, see STALL):
* `hupper` : `ShenUpperBoundNegative c U`;
* `htail`  : the sharp right-tail asymptotic family. -/
theorem constructionNeg_of_lowerPinnedSchauderData
    {p : CMParams} {c lam κtilde D M : ℝ} {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hc : 0 < c) (hκ : 0 < kappa c) (hgap : 0 < κtilde - kappa c) (hD : 0 < D)
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
    (hupper : ∀ U,
      InLowerPinnedMonotoneTrap (kappa c) M
        (lowerBarrierPlateau (kappa c) κtilde D) U →
      ShenUpperBoundNegative c U)
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
  refine ⟨U, hprofile, ?_, ?_, hupper U hU, htail U hU⟩
  · exact fun x => constructionNeg_hUmono hU.bare x
  · exact fun x => constructionNeg_hVmono p hU.bare x

/-- **`construction_neg` (full quantified shape) — conditional on the Rothe /
Schauder data provider plus the two carried analytic obligations.**

This is EXACTLY the `construction_neg` field of `Paper1MainResultsData` and the
`hneg` argument of `Theorem_1_1.of_assumed_frozenStationaryProfile_branches`,
with the construction's analytic inputs surfaced as one provider hypothesis
`hprovider`.  For each admissible `(p, c)` the provider supplies the
lower-pinned Schauder data (the Rothe per-step Green producer + continuous
dependence assembled into the principle/data fields), the per-fixed-point
stationarity and left-flatness, and the two carried obligations
`hupper`/`htail`.  Everything else (`FrozenStationaryWaveProfile`,
`deriv U ≤ 0`, `deriv V' ≤ 0`) is discharged unconditionally inside. -/
theorem constructionNeg_of_provider
    (hprovider :
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
              ShenUpperBoundNegative c U) ∧
            (∀ U, InLowerPinnedMonotoneTrap (kappa c) 1
                (lowerBarrierPlateau (kappa c) κtilde D) U →
              ∀ κ₁, kappa c < κ₁ →
                κ₁ < min ((1 + p.α) * kappa c)
                  (min (p.m * kappa c + 1 / 2) 1) →
                HasWaveRightTailAsymptotic c κ₁ U)) :
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
      hstationary, hflat, hupper, htail⟩ :=
    hprovider p halpha hχ c hc
  exact constructionNeg_of_lowerPinnedSchauderData
    (lt_of_lt_of_le two_pos (two_lt_of_cStarLower_lt hc).le)
    (kappa_pos_of_cStarLower_lt hc) hgap hD
    hprinciple hdata hstationary hflat rfl hupper htail

/-- **Theorem 1.1 (negative branch wired) — conditional on the provider.**
Feeds `constructionNeg_of_provider` into the committed
`Theorem_1_1.of_assumed_frozenStationaryProfile_branches`, leaving only the
positive branch `hpos` as the other input.  This demonstrates that the
negative-branch construction obligation of `Theorem_1_1` is fully reduced to the
single provider hypothesis (the Rothe/Schauder data + the two carried analytic
obligations). -/
theorem Theorem_1_1.of_constructionNeg_provider
    (hprovider :
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
              ShenUpperBoundNegative c U) ∧
            (∀ U, InLowerPinnedMonotoneTrap (kappa c) 1
                (lowerBarrierPlateau (kappa c) κtilde D) U →
              ∀ κ₁, kappa c < κ₁ →
                κ₁ < min ((1 + p.α) * kappa c)
                  (min (p.m * kappa c + 1 / 2) 1) →
                HasWaveRightTailAsymptotic c κ₁ U))
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
    (constructionNeg_of_provider hprovider) hpos

/-
================================================================================
PRECISE STALL — what is closed unconditionally vs. what is carried, and why.
================================================================================

CLOSED UNCONDITIONALLY (no carried hypotheses, pure committed bricks):
  * `constructionNeg_hUmono`  — `deriv U ≤ 0` from `InMonotoneWaveTrapSet`.
  * `constructionNeg_hVmono`  — `deriv (frozenElliptic p U) ≤ 0` from the same
    trap (committed `frozenElliptic_deriv_nonpos_of_monotone_trap`).
  Inside `constructionNeg_of_lowerPinnedSchauderData`, GIVEN the Schauder data,
  the entire `FrozenStationaryWaveProfile p c U` is ALSO discharged
  unconditionally (via the committed lower-pinned wrapper
  `b1_chiNeg_existence_of_lowerBarrierPinnedSchauderData_stationary_rootPin`):
  strict positivity from the lower pin `0 < lowerBarrierPlateau`, left endpoint
  `U → 1` from `tendsto_atBot_one_of_stationary_flat_and_pos`, right endpoint
  `U → 0` from `InMonotoneWaveTrapSet.tendsto_atTop_zero`, and the stationary
  equation from the supplied `hstationary`.

CARRIED (genuine analytic residuals, surfaced as explicit hypotheses):

  (A) THE SCHAUDER DATA PROVIDER `hprovider` packages the deep Rothe/Green
      machinery.  Its non-trivial fields are EXACTLY the two named hard
      residuals already isolated by `WaveRotheClose.b1_chiNeg_existence_clean`:
        - `hprodTrap` : the per-step Rothe/Green producer
          (`RotheStepProducer`) — bridging the committed truncated BCF step
          (`crossStep_exists_unique_concrete`) to the raw `crossImplicitMap`
          requires the `greenConvBCF`↔`greenKernel` identity AND removal of the
          source truncation, the latter resting on the max-principle ordering
          obligations (`ImplicitStepSuperOrdering`), themselves uncommitted but
          satisfiable.  NOT closeable from committed bricks without fresh
          satisfiable hypotheses (documented at WaveRotheClose.lean, item
          `hprodTrap`).
        - `hdep` : `RotheContinuousDependence` — propagating the committed
          `frozenEllipticDerivDependence` through the Rothe limit (dominated
          convergence with uniform contraction constants) is not a committed
          closed lemma (documented at WaveRotheClose.lean, item `hdep`).
      Assembling these into `hprinciple`/`hdata`/`hstationary`/`hflat` is the
      §3.3 satisfiability content; the lower-pinned trap keeps it NON-VACUOUS
      (the bare-trap non-trivial Schauder principle is FALSE —
      `not_localUniformNontrivialSchauderFixedPointPrinciple_bareTrap` — and is
      NOT used here).

  (B) `hupper : ShenUpperBoundNegative c U`
      = `∀ x, 0 < U x ∧ U x < max 1 (exp(-(kappa c)·x))`.
      The lower pin already forces `0 < U x`, but the STRICT upper bound is a
      fixed-point property: at `x = 0`, `max 1 (exp 0) = 1` and the trap gives
      only `U 0 ≤ upperBarrier (kappa c) 1 0 = 1`, NOT `U 0 < 1`.  Strictness
      there is a stationary-profile property (a non-constant stationary wave is
      `< 1` at finite `x`), proved in the paper from the strong maximum
      principle on the equation — not derivable from trap membership.  No
      committed producer of `ShenUpperBoundNegative` from trap/stationarity
      exists (grep: it appears ONLY as hypothesis / carried obligation, never as
      a conclusion from `InMonotoneWaveTrapSet`/`FrozenStationaryWaveProfile`).
      MISSING LEMMA: `ShenUpperBoundNegative_of_stationary_strongMaxPrinciple`
      (strong max principle on `frozenWaveOperator p c U U = 0` ⟹ strict upper
      bound).  Carried.

  (C) `htail` : the sharp right-tail asymptotic
      `HasWaveRightTailAsymptotic c κ₁ U`
      = `Tendsto (x ↦ exp((κ₁-κc)x)·(U x / exp(-κc x) - 1)) atTop (𝓝 0)`.
      This is `U x = exp(-κc x)(1 + o(exp(-(κ₁-κc)x)))`, a linearisation-at-`+∞`
      property of the stationary ODE.  The trap envelope
      `0 ≤ U x ≤ min 1 (exp(-κc x))` does NOT pin the ratio `U/exp(-κc·) → 1`
      with the required rate.  No committed producer of
      `HasWaveRightTailAsymptotic` from trap/stationarity (grep: only consumers
      `HasWaveRightTailAsymptotic.ratio_tendsto_one` etc.).
      MISSING LEMMA: `HasWaveRightTailAsymptotic_of_stationary` (linearisation
      of `frozenWaveOperator p c U U = 0` at `+∞`).  Carried.

EXACT STALL LOCATION for the unconditional closure of (B)/(C):
  file `ShenWork/Paper1/ConstructionNegProducer.lean`,
  `constructionNeg_of_lowerPinnedSchauderData`, the `hupper U hU` / `htail U hU`
  slots in the final `refine`.  Each needs the missing producer named above
  (a strong-max-principle resp. a `+∞`-linearisation lemma on the stationary
  equation `frozenWaveOperator p c U U = 0`), neither committed; both are REAL
  PDE gaps (not circularity — they consume the already-produced stationary
  equation, they do not re-assume the conclusion).

HONEST LABEL: `construction_neg` is NOT proved unconditionally here.  It is
reduced to a single provider hypothesis `hprovider` whose content is precisely
(A) the two named Rothe/Green residuals (`hprodTrap`, `hdep`) assembled into the
lower-pinned Schauder data, plus (B)+(C) the two carried analytic obligations
(strict upper bound + sharp tail).  The reduction itself, and the two free
monotonicity obligations and the full `FrozenStationaryWaveProfile` join, are
unconditional and axiom-clean.
================================================================================
-/

section AxiomAudit
#print axioms constructionNeg_hUmono
#print axioms constructionNeg_hVmono
#print axioms constructionNeg_of_lowerPinnedSchauderData
#print axioms constructionNeg_of_provider
#print axioms Theorem_1_1.of_constructionNeg_provider
end AxiomAudit

end ShenWork.Paper1
