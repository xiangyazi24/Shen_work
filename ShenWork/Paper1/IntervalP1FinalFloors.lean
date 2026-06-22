/-
  ShenWork/Paper1/IntervalP1FinalFloors.lean

  Final-floor wiring toward the unconditional `Remark_1_3_2`.

  The headline existence theorem `b1_chiPos_existence_paper_of_cubeApproxData`
  (WaveLemma42G1Discharge.lean) carries the analytic PDE residuals as named
  hypotheses; one of them — `hstationary` — was packaged in
  `IntervalP1RotheLimit.lean` as `RotheLimitStationaryData`, whose ONLY
  genuinely-analytic field was flagged as the local-uniform convergence
  `hLU : LocallyUniformConverges z U` (the equicontinuity output).

  THIS FILE DISCHARGES `hLU` — it is NOT a wall.  The Rothe orbit produced by
  the per-step Green solver carries `PaperRotheOrbitData` (WaveRotheConcrete.lean),
  whose `equiLip`/`limitLip` fields are the UNIFORM Lipschitz bounds (each
  iterate is a Green image with derivative bounded by the kernel-derivative
  `L¹`-norm `2/δ`, landed in `WaveRotheC1.lean` as
  `crossImplicitStep_lipschitz`).  Combined with the antitone-in-`k`
  monotone-convergence (`rotheLimit_tendsto`), the bespoke finite-grid `ε/3`
  upgrade `rotheLimit_locallyUniform` turns uniform Lipschitz + pointwise
  convergence into `LocallyUniformConverges` — exactly `hLU`.  So
  `PaperRotheOrbitData.locallyUniform` IS `hLU`.

  We therefore build `RotheLimitStationaryData` from `PaperRotheOrbitData`
  (supplying `hLU`, the iterate/limit continuity, the pointwise bounds and the
  Green-step recursion from the LANDED orbit data) plus the residual fields that
  genuinely remain — the frozen-drift regularity `V_cont`/`V_bound` of the
  diagonal profile and the per-`U` `GreenIdentity` — and read off the
  `hstationary` obligation with `hLU` no longer a separately carried hypothesis.

  This isolates the precise remaining analytic walls (the per-step solver, the
  Green identity representation, the frozen-drift regularity, the strong max
  principle's ODE realization, and the left-flatness Green-source tail) as the
  genuine PDE-construction residuals — NOT as trap-bound corollaries — and shows
  the equicontinuity floor is closed.

  No `sorry`/`axiom`/`native_decide`/`admit`.  New file only; touches nothing
  existing.  Axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/
import ShenWork.Paper1.IntervalP1RotheLimit
import ShenWork.Paper1.WaveRotheConcrete

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

variable {c lam : ℝ}

/-! ## `hLU` discharged through the landed Rothe orbit data

`PaperRotheOrbitData` already proves `LocallyUniformConverges (rotheSeq u)
(rotheLimit (rotheSeq u))` via `rotheLimit_locallyUniform` (uniform Lipschitz +
pointwise monotone convergence, finite-grid `ε/3`).  That IS the `hLU` field of
`RotheLimitStationaryData`.  We package the rest from the orbit data plus the
genuinely-remaining residual (drift regularity + Green identity). -/

/-- **`RotheLimitStationaryData` from the landed orbit data.**

At the diagonal `u = U` with `z = rotheSeq U` the Schauder-fixed limit
(`hU_def : U = rotheLimit z`), the landed `PaperRotheOrbitData` supplies the
equicontinuity output `hLU`, the iterate/limit continuity, the pointwise bounds
`0 ≤ z k ≤ M` / `0 ≤ U ≤ M`, and the per-step Green recursion `hrec`.  The two
fields it does NOT carry — the frozen-drift regularity `V_cont`/`V_bound` and the
per-`U` Green identity `hgreen` — are taken as the precise reduced residual.
`hLU` is therefore no longer a separately carried hypothesis. -/
theorem RotheLimitStationaryData.of_paperRotheOrbitData
    {p : CMParams} {M κ Bv : ℝ} {U : ℝ → ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hM : 0 ≤ M) (hBv : 0 ≤ Bv)
    (horbit : PaperRotheOrbitData p c lam M κ rotheSeq U)
    (hU_def : U = rotheLimit (rotheSeq U))
    (hrec : ∀ k, rotheSeq U (k + 1)
      = crossImplicitMap p c lam U (rotheSeq U k) (rotheSeq U (k + 1)))
    (hV_cont : Continuous (deriv (frozenElliptic p U)))
    (hV_bound : ∀ y, |deriv (frozenElliptic p U) y| ≤ Bv)
    (hgreen : GreenIdentity p c lam U) :
    RotheLimitStationaryData p c lam U (rotheSeq U) M Bv where
  hM := hM
  hBv := hBv
  hU_def := hU_def
  hrec := hrec
  hLU := by
    have h := horbit.locallyUniform hM
    rwa [← hU_def] at h
  hz_cont := horbit.iterate_cont
  hU_cont := by
    have h := horbit.limit_continuous hM
    rwa [← hU_def] at h
  hV_cont := hV_cont
  hV_bound := hV_bound
  hz_lb := horbit.nonneg
  hz_ub := horbit.le_M
  hU_lb := by
    intro y
    have h := horbit.limit_nonneg y
    rwa [← hU_def] at h
  hU_ub := by
    intro y
    have h := horbit.limit_le_M y
    rwa [← hU_def] at h
  hgreen := hgreen

/-- **`frozenWaveOperator p c U U = 0` from the orbit data + reduced residual.**

Composes `RotheLimitStationaryData.of_paperRotheOrbitData` with the landed
diagonal pass-to-the-limit + collapse engine
`RotheLimitStationaryData.frozenWaveOperator_zero`.  `hLU` is discharged inside,
not assumed. -/
theorem frozenWaveOperator_zero_of_paperRotheOrbitData
    {p : CMParams} {M κ Bv : ℝ} {U : ℝ → ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hlam : 0 < lam) (hM : 0 ≤ M) (hBv : 0 ≤ Bv)
    (horbit : PaperRotheOrbitData p c lam M κ rotheSeq U)
    (hU_def : U = rotheLimit (rotheSeq U))
    (hrec : ∀ k, rotheSeq U (k + 1)
      = crossImplicitMap p c lam U (rotheSeq U k) (rotheSeq U (k + 1)))
    (hV_cont : Continuous (deriv (frozenElliptic p U)))
    (hV_bound : ∀ y, |deriv (frozenElliptic p U) y| ≤ Bv)
    (hgreen : GreenIdentity p c lam U) :
    ∀ x, frozenWaveOperator p c U U x = 0 :=
  (RotheLimitStationaryData.of_paperRotheOrbitData hM hBv horbit hU_def hrec
    hV_cont hV_bound hgreen).frozenWaveOperator_zero hlam

/-! ## `hstationary` with `hLU` eliminated

The `b1_chiPos_existence_paper_of_cubeApproxData` `hstationary` obligation is
`∀ U, P U → rotheLimit (rotheSeq U) = U → ∀ x, frozenWaveOperator p c U U x = 0`.
We supply it from a per-`U` producer that carries the LANDED `PaperRotheOrbitData`
(equicontinuity, bounds, recursion) plus only the reduced residual — drift
regularity + Green identity.  The fixed-point premise `rotheLimit (rotheSeq U) =
U` is fed straight through as `hU_def`; the equicontinuity field is NOT among the
producer's hypotheses, so `hLU` is fully discharged. -/

/-- **`hstationary` from a per-`U` orbit-data + reduced-residual producer.**

For any predicate `P` on profiles (the lower-pinned monotone trap), if every
`P`-profile `U` that is its own Rothe limit carries the landed
`PaperRotheOrbitData` together with the per-step Green recursion, the diagonal
frozen-drift regularity, and the per-`U` Green identity, then the `hstationary`
obligation holds — with the equicontinuity floor `hLU` discharged internally by
`PaperRotheOrbitData.locallyUniform`. -/
theorem hstationary_of_paperRotheOrbitData
    {p : CMParams} {M κ Bv : ℝ} {P : (ℝ → ℝ) → Prop}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hlam : 0 < lam) (hM : 0 ≤ M) (hBv : 0 ≤ Bv)
    (hprod : ∀ U, P U → rotheLimit (rotheSeq U) = U →
      PaperRotheOrbitData p c lam M κ rotheSeq U
        ∧ (∀ k, rotheSeq U (k + 1)
            = crossImplicitMap p c lam U (rotheSeq U k) (rotheSeq U (k + 1)))
        ∧ Continuous (deriv (frozenElliptic p U))
        ∧ (∀ y, |deriv (frozenElliptic p U) y| ≤ Bv)
        ∧ GreenIdentity p c lam U) :
    ∀ U, P U → rotheLimit (rotheSeq U) = U →
      ∀ x, frozenWaveOperator p c U U x = 0 := by
  intro U hU hfix
  obtain ⟨horbit, hrec, hV_cont, hV_bound, hgreen⟩ := hprod U hU hfix
  exact frozenWaveOperator_zero_of_paperRotheOrbitData hlam hM hBv horbit
    hfix.symm hrec hV_cont hV_bound hgreen

/-! ## Axiom audit -/

section AxiomAudit
#print axioms RotheLimitStationaryData.of_paperRotheOrbitData
#print axioms frozenWaveOperator_zero_of_paperRotheOrbitData
#print axioms hstationary_of_paperRotheOrbitData
end AxiomAudit

end ShenWork.Paper1
