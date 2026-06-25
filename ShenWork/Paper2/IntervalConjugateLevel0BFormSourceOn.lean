/-
  ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean

  B-form source `DuhamelSourceTimeC1On` for the conjugate Picard level 0
  (the heat semigroup) on a positive window `[c, T]`.

  The B-form source is:
    `bFormSourceCoeffs p (conjugatePicardIter p u₀ 0) s k
      = coupledLogisticSourceCoeffs p (conjugatePicardIter p u₀ 0) s k
        - p.χ₀ * coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ 0) s k`

  The logistic leg is exactly `conjLogSourceTimeC1On_level0` (existing).
  The chemDiv leg is new: it exploits the exponential spatial regularity of the
  heat semigroup `S(t)u₀` for `t ≥ c > 0` to produce the `DuhamelSourceTimeC1On`
  package for the chemotaxis-divergence coefficients.

  The two legs are combined via `bFormSource_duhamelSourceTimeC1On`.

  No existing files are modified.
-/
import ShenWork.Paper2.IntervalConjugateIterSourceTower
import ShenWork.Paper2.IntervalBFormSpectralHtime
import ShenWork.Paper2.IntervalBFormNegPartStrictPosBarrier

open MeasureTheory Set Filter
open scoped Topology
open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalDomain)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalConjugatePicard
  (conjugatePicardIter ConjugateMildExistenceData)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledLogisticSourceCoeffs coupledChemDivSourceCoeffs
   coupledChemDivSourceLift coupledChemicalConcentration)
open ShenWork.IntervalBFormSpectral (bFormSourceCoeffs bFormSource_duhamelSourceTimeC1On)
open ShenWork.Paper2.ConjugateIterSourceTower (conjLogSourceTimeC1On_level0)
open ShenWork.IntervalPicardLevel0SourceTimeC1On (heatCoeff)
open ShenWork.Paper2 (PaperPositiveInitialDatum PositiveInitialDatum)
open ShenWork.IntervalDomain (intervalDomain)

noncomputable section

namespace ShenWork.Paper2.ConjugateLevel0BFormSourceOn

/-! ## Section 1: Definitional equalities

`conjugatePicardIter p u₀ 0` is definitionally `picardIter p u₀ 0`, which is
`fun t x => intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1`.
The logistic and chemDiv coefficient families for the conjugate level 0 are
therefore definitionally equal to those for `picardIter p u₀ 0`. -/

theorem conjChemDivCoeffs_level0_eq (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (s : ℝ) (k : ℕ) :
    coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ 0) s k =
    coupledChemDivSourceCoeffs p (picardIter p u₀ 0) s k := by
  rfl

theorem conjLogCoeffs_level0_eq (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (s : ℝ) (k : ℕ) :
    coupledLogisticSourceCoeffs p (conjugatePicardIter p u₀ 0) s k =
    coupledLogisticSourceCoeffs p (picardIter p u₀ 0) s k := by
  rfl

theorem bFormSourceCoeffs_level0_eq (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (s : ℝ) (k : ℕ) :
    bFormSourceCoeffs p (conjugatePicardIter p u₀ 0) s k =
    bFormSourceCoeffs p (picardIter p u₀ 0) s k := by
  rfl

/-! ## Section 2: ChemDiv source `DuhamelSourceTimeC1On` for heat semigroup level 0

The chemotaxis-divergence source at level 0 is:
  `coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s`
    = `intervalDomainLift (intervalDomainChemotaxisDiv p (u₀_heat s)
        (coupledChemicalConcentration p u₀_heat s))`
where `u₀_heat = conjugatePicardIter p u₀ 0` is the heat semigroup.

For `s ≥ c > 0`, the heat semigroup has exponential coefficient decay
`|cosineCoeffs(S(s)u₀) k| ≤ M₀ · exp(-c · λ_k)`, which gives spatial C∞
regularity.  The chemDiv source inherits spatial C² regularity via the chain
rule through the Neumann resolver.

We package the resulting `DuhamelSourceTimeC1On` as a structure carrying
the sorry'd infrastructure lemmas. -/

/-- **Hypothesis bundle** for the level-0 chemDiv source time-C¹ windowed package.

These hypotheses are in principle derivable from:
  (a) the exponential spatial regularity of the heat semigroup on `[c,T]`,
  (b) the chain rule through the Neumann resolver,
  (c) the resulting weak-H² Neumann and coefficient-decay estimates.

Each field is a genuine mathematical fact about the heat semigroup level 0;
they are taken as hypotheses here because the derivation chain is long
(each needs 50+ lines of new infrastructure connecting heat semigroup
regularity to the chemDiv chain-rule output). -/
structure Level0ChemDivSourceData (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ) (c T : ℝ) where
  /-- Summable envelope for `coupledChemDivSourceCoeffs` on `[c,T]`. -/
  envelope : ℕ → ℝ
  henv_summable : Summable envelope
  henv_bound : ∀ s ∈ Icc c T, ∀ n,
    |coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ 0) s n| ≤ envelope n
  /-- Time derivative of the chemDiv coefficients. -/
  adot : ℝ → ℕ → ℝ
  hderiv : ∀ s ∈ Icc c T, ∀ n,
    HasDerivWithinAt
      (fun r => coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ 0) r n)
      (adot s n) (Icc c T) s
  hadotcont : ∀ n, ContinuousOn (fun s => adot s n) (Icc c T)
  /-- Uniform bound on the time-derivative coefficients. -/
  derivBound : ℝ
  hderivBound : ∀ s ∈ Icc c T, ∀ n, |adot s n| ≤ derivBound

/-- Build `DuhamelSourceTimeC1On` for the chemDiv source at level 0 from the
hypothesis bundle. -/
noncomputable def chemDivSourceTimeC1On_of_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {c T : ℝ}
    (D : Level0ChemDivSourceData p u₀ c T) :
    DuhamelSourceTimeC1On
      (coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ 0)) c T where
  adot := D.adot
  hderiv := D.hderiv
  hadotcont := D.hadotcont
  envelope := D.envelope
  henv_summable := D.henv_summable
  henv_bound := D.henv_bound
  derivBound := D.derivBound
  hderivBound := D.hderivBound

/-! ## Section 3: Constructing `Level0ChemDivSourceData` from heat semigroup regularity

The heat semigroup `S(t)u₀` on `[c,T]` with `c > 0` has:
  - Exponential coefficient decay: `|cosineCoeffs(S(s)u₀) k| ≤ M₀ · exp(-c·λ_k)`
  - Spatial C∞ regularity (all spatial derivatives have exponential coefficient decay)
  - The chemDiv source `∇·(u·χ(v)·∇v)` at each time slice is C² with Neumann BCs
  - The time derivative of the chemDiv coefficients exists and is continuous

The construction below sorry's the individual regularity estimates.  Each sorry
represents a substantial but straightforward derivation from the heat semigroup's
known regularity properties. -/

/-- Summable envelope for the chemDiv source coefficients of the heat semigroup
on a positive window.  The heat semigroup's exponential spatial decay gives
the chemDiv source (which involves products and compositions of C∞ functions)
a quadratic or better coefficient decay, yielding a summable envelope. -/
theorem level0_chemDiv_envelope_summable
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {c T M M₀ : ℝ} (hc : 0 < c) (_hcT : c ≤ T)
    (_hu₀_cont : Continuous u₀)
    (_hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (_hpos : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x)
    (_hub : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x ≤ M) :
    ∃ (envelope : ℕ → ℝ),
      Summable envelope ∧
      ∀ s ∈ Icc c T, ∀ n,
        |coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ 0) s n| ≤ envelope n := by
  -- The heat semigroup S(s)u₀ for s ≥ c > 0 is spatially C∞ on [0,1] with
  -- Neumann boundary conditions.  The chemDiv source is
  --   ∇·(u · χ(v) · ∇v)
  -- where v = (μ - Δ)⁻¹(ν · u^γ) is the chemical concentration.
  -- Since u = S(s)u₀ is C∞ with exponentially decaying coefficients,
  -- v and ∇v are also C∞, and the product/composition is C∞.
  -- The Neumann H² property gives |cosineCoeffs(chemDiv source) k| ≤ C/(kπ)²
  -- for k ≥ 1, yielding a summable envelope.
  sorry

/-- Time-derivative and continuity data for the chemDiv coefficients of the
heat semigroup on a positive window.  The time derivative is computed by the
chain rule: the heat semigroup evolves as ∂ₜu = Δu, so ∂ₜ(chemDiv source)
can be expressed in terms of the spatial derivatives (which are well-controlled
on the positive window). -/
theorem level0_chemDiv_timeDerivData
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {c T M M₀ : ℝ} (hc : 0 < c) (_hcT : c ≤ T)
    (_hu₀_cont : Continuous u₀)
    (_hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (_hpos : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x)
    (_hub : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x ≤ M) :
    ∃ (adot : ℝ → ℕ → ℝ) (Mdot : ℝ),
      (∀ s ∈ Icc c T, ∀ n,
        HasDerivWithinAt
          (fun r => coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ 0) r n)
          (adot s n) (Icc c T) s) ∧
      (∀ n, ContinuousOn (fun s => adot s n) (Icc c T)) ∧
      (∀ s ∈ Icc c T, ∀ n, |adot s n| ≤ Mdot) := by
  -- The time derivative of coupledChemDivSourceCoeffs is computed via the
  -- chain rule.  Since u = S(t)u₀ satisfies ∂ₜu = Δu (the heat equation),
  -- and the chemDiv source is a smooth functional of u and its spatial
  -- derivatives, the time derivative ∂ₜ(chemDiv source coefficients) exists
  -- and is continuous on [c,T] with c > 0.
  --
  -- The uniform bound follows from the uniform bounds on u, ∂ₓu, ∂²ₓu,
  -- ∂ₜu, and ∂ₜ∂ₓu on the compact set [c,T] × [0,1], all of which are
  -- available from the heat semigroup's explicit cosine-series representation.
  sorry

/-- Construct `Level0ChemDivSourceData` from the basic heat semigroup hypotheses.
This combines the envelope and time-derivative data. -/
noncomputable def level0ChemDivSourceData
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {c T M M₀ : ℝ} (hc : 0 < c) (hcT : c ≤ T)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (hpos : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x)
    (hub : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x ≤ M) :
    Level0ChemDivSourceData p u₀ c T := by
  obtain ⟨envelope, hsum, hbound⟩ :=
    level0_chemDiv_envelope_summable p hc hcT hu₀_cont hu₀_bound hpos hub
  obtain ⟨adot, Mdot, hderiv, hadotcont, hMdot⟩ :=
    level0_chemDiv_timeDerivData p hc hcT hu₀_cont hu₀_bound hpos hub
  exact {
    envelope := envelope
    henv_summable := hsum
    henv_bound := hbound
    adot := adot
    hderiv := hderiv
    hadotcont := hadotcont
    derivBound := Mdot
    hderivBound := hMdot
  }

/-! ## Section 4: The logistic source `DuhamelSourceTimeC1On` for level 0

This is an alias for the existing `conjLogSourceTimeC1On_level0`.
We restate it here in terms of `coupledLogisticSourceCoeffs` (which is
definitionally equal to the cosine-coefficient family of `logisticLifted`). -/

/-- The logistic source `DuhamelSourceTimeC1On` for conjugate level 0, restated
in terms of `coupledLogisticSourceCoeffs`.  Definitionally equal to
`conjLogSourceTimeC1On_level0` since
`cosineCoeffs (logisticLifted p (conjugatePicardIter p u₀ 0 s)) k
  = coupledLogisticSourceCoeffs p (conjugatePicardIter p u₀ 0) s k`. -/
noncomputable def level0_logisticSource_timeC1On
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {c T M G1 G2 Udot M₀ : ℝ}
    (hc : 0 < c) (hcT : c < T)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (hpos : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x)
    (hub : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x ≤ M)
    (hG1 : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (conjugatePicardIter p u₀ 0 σ)) x| ≤ G1)
    (hG2 : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (conjugatePicardIter p u₀ 0 σ))) x| ≤ G2)
    (hUdot : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      |ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondValue
        σ (heatCoeff u₀) x| ≤ Udot) :
    DuhamelSourceTimeC1On
      (coupledLogisticSourceCoeffs p (conjugatePicardIter p u₀ 0)) c T :=
  -- `logisticLifted p (conjugatePicardIter p u₀ 0 s)` is definitionally
  -- `coupledLogisticSourceLift p (conjugatePicardIter p u₀ 0) s`, so
  -- `cosineCoeffs (logisticLifted …) k = coupledLogisticSourceCoeffs …` def-eq.
  conjLogSourceTimeC1On_level0 p hc hcT hα ha hb hu₀_cont hu₀_bound
    hpos hub hG1 hG2 hUdot

/-! ## Section 5: The B-form source `DuhamelSourceTimeC1On` for level 0

Combine the logistic and chemDiv legs via `bFormSource_duhamelSourceTimeC1On`. -/

/-- **Main theorem.**  The B-form source coefficients of the heat semigroup
(conjugate Picard level 0) satisfy `DuhamelSourceTimeC1On` on a positive
window `[c, T]`.

**Logistic leg:** Discharged from `conjLogSourceTimeC1On_level0` (existing,
no sorry).

**ChemDiv leg:** Discharged from `Level0ChemDivSourceData` which collects
the summable envelope and time-derivative data for the chemDiv coefficients.
The data is constructed via `level0ChemDivSourceData`, which sorry's
`level0_chemDiv_envelope_summable` and `level0_chemDiv_timeDerivData`.

**Sorry summary:**
  - `level0_chemDiv_envelope_summable`: needs ~100 lines wiring heat semigroup
    exponential spatial decay through the chemDiv chain rule to produce a
    summable `(kπ)⁻²`-type envelope.  The mathematical argument is:
    S(s)u₀ is C∞ for s > 0 ⟹ chemDiv source is weak-H² Neumann ⟹
    coefficient decay ≤ C/(kπ)² ⟹ summable.
  - `level0_chemDiv_timeDerivData`: needs ~100 lines wiring the heat equation
    ∂ₜu = Δu through the chain rule for the chemDiv functional to produce
    the time-derivative coefficients adot, their continuity, and uniform bound.
    The mathematical argument is: ∂ₜ(chemDiv(S(t)u₀)) = chain-rule with ∂ₜu = Δu,
    all spatial derivatives bounded on [c,T]×[0,1]. -/
noncomputable def level0_bFormSource_duhamelSourceTimeC1On
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {c T M G1 G2 Udot M₀ : ℝ}
    (hc : 0 < c) (hcT : c < T)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (hpos : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x)
    (hub : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x ≤ M)
    (hG1 : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (conjugatePicardIter p u₀ 0 σ)) x| ≤ G1)
    (hG2 : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (conjugatePicardIter p u₀ 0 σ))) x| ≤ G2)
    (hUdot : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      |ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondValue
        σ (heatCoeff u₀) x| ≤ Udot)
    (chemData : Level0ChemDivSourceData p u₀ c T) :
    DuhamelSourceTimeC1On
      (bFormSourceCoeffs p (conjugatePicardIter p u₀ 0)) c T :=
  bFormSource_duhamelSourceTimeC1On
    (level0_logisticSource_timeC1On p hc hcT hα ha hb hu₀_cont hu₀_bound
      hpos hub hG1 hG2 hUdot)
    (chemDivSourceTimeC1On_of_data chemData)

/-- **Self-contained variant** that constructs `Level0ChemDivSourceData`
internally from the basic heat semigroup hypotheses.  Uses sorry. -/
noncomputable def level0_bFormSource_duhamelSourceTimeC1On_auto
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {c T M G1 G2 Udot M₀ : ℝ}
    (hc : 0 < c) (hcT : c < T)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (hpos : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x)
    (hub : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x ≤ M)
    (hG1 : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (conjugatePicardIter p u₀ 0 σ)) x| ≤ G1)
    (hG2 : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (conjugatePicardIter p u₀ 0 σ))) x| ≤ G2)
    (hUdot : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      |ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondValue
        σ (heatCoeff u₀) x| ≤ Udot) :
    DuhamelSourceTimeC1On
      (bFormSourceCoeffs p (conjugatePicardIter p u₀ 0)) c T :=
  level0_bFormSource_duhamelSourceTimeC1On p hc hcT hα ha hb hu₀_cont hu₀_bound
    hpos hub hG1 hG2 hUdot
    (level0ChemDivSourceData p hc hcT.le hu₀_cont hu₀_bound hpos hub)

/-! ## Section 6: ConjugateMildExistenceData + PaperPositiveInitialDatum interface

The final consumer typically has `ConjugateMildExistenceData p u₀` (which
carries the ball/positivity/continuity data for the Picard iterates) and
`PaperPositiveInitialDatum` (which carries the initial datum regularity).
We provide a convenience wrapper that extracts the necessary hypotheses
from these structures. -/

/-- Extract the heat-semigroup positivity on `[c,T]` from
`ConjugateMildExistenceData` for level 0. -/
theorem level0_heat_pos_of_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (_D : ConjugateMildExistenceData p u₀)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {c : ℝ} (hc : 0 < c) (_hcT : c ≤ _D.T) :
    ∀ σ ∈ Icc c _D.T, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x := by
  intro σ hσ x hx
  have hσpos : 0 < σ := lt_of_lt_of_le hc hσ.1
  simp only [intervalDomainLift, dif_pos hx, conjugatePicardIter]
  exact ShenWork.Paper2.BFormPositiveDatumNegPart.intervalFullSemigroupOperator_pos_of_positiveInitialDatum
    hu₀ hσpos x

/-- Extract the heat-semigroup sup bound on `[c,T]` from
`ConjugateMildExistenceData` for level 0. -/
theorem level0_heat_sup_of_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀)
    {c : ℝ} (hc : 0 < c) (hcT : c ≤ D.T) :
    ∀ σ ∈ Icc c D.T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x ≤ D.M := by
  intro σ hσ x hx
  -- D.hbase_ball gives |conjugatePicardIter p u₀ 0 t x| ≤ D.M for 0 < t ≤ D.T.
  -- The lift on Icc 0 1 equals the subtype value, so the bound transfers.
  have hσpos : 0 < σ := lt_of_lt_of_le hc hσ.1
  have hσT : σ ≤ D.T := hσ.2
  simp only [intervalDomainLift, dif_pos hx]
  have hball := D.hbase_ball σ hσpos hσT ⟨x, hx⟩
  have hnn := D.hbase_nonneg σ hσpos hσT ⟨x, hx⟩
  linarith [abs_le.mp (abs_le_of_le_of_neg_le (le_of_abs_le hball) (by linarith))]

end ShenWork.Paper2.ConjugateLevel0BFormSourceOn
