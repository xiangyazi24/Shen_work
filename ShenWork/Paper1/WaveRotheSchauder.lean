/-
  ShenWork/Paper1/WaveRotheSchauder.lean

  Parallel stationary-map Schauder bridge for the B1 traveling-wave construction
  (Shen, arXiv:2605.04401, §6 / B1 doctrine).

  This is the ASSEMBLY SCAFFOLD for the ChatGPT-Pro "parallel bridge" route that
  bypasses the continuous-time orbit contract.  Instead of building a
  parabolic-orbit limit map and passing the differential operator to the limit,
  we carry a single self-map `Tmap` together with its *diagonal cross-fixed-point*
  property: for every trapped `u`, the image `Tmap u` solves the self-frozen Green
  equation `crossImplicitMap p c lam u (Tmap u) (Tmap u) = Tmap u`.  This is
  exactly what the committed `rotheLimit_crossImplicitMap_fixed` supplies with
  `Tmap u := rotheLimit (z u)`.

  The analytic/topological inputs are carried as explicit, SATISFIABLE
  hypotheses (each proved elsewhere):
    * the G1 abstract `LocalUniformSchauderFixedPointPrinciple trap` (Statements),
    * the four `FrozenStationaryMapSchauderData` fields (invariance, the diagonal
      cross-fixed-point, local-uniform continuity, local-uniform compact range),
    * the per-fixed-point `GreenIdentity` (`greenIdentity_of_convRepr` + `flux_ibp`).

  Wiring at the outer Schauder fixed point `Tmap U = U`:
    diagonal cross field ⟹ `crossImplicitMap p c lam U (Tmap U) (Tmap U) = Tmap U`
    rewrite `Tmap U = U`  ⟹ `crossImplicitMap p c lam U U U = U`
    `rotheLimit_auxMap_fixed_at_diagonal` ⟹ `auxMap p c lam U = U`
    `fixedPoint_stationary` (+ `GreenIdentity`) ⟹ `∀ x, frozenWaveOperator p c U U x = 0`.

  No `sorry`/`axiom`/`native_decide`/`admit`.  Touches only Paper1; the new
  contract is defined here, not in Statements.lean.
-/
import ShenWork.Paper1.WaveRotheStationary
import ShenWork.Paper1.WaveTrapProps
import ShenWork.Paper1.Statements

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-! ## The parallel stationary-map Schauder data -/

/-- **Parallel stationary-map Schauder data.**
A trap-respecting self-map `Tmap` whose image at every trapped `u` solves the
self-frozen Green equation (the diagonal cross-fixed-point), and which is
local-uniformly continuous with local-uniformly sequentially-compact range.

The diagonal cross-fixed-point field
`crossImplicitMap p c lam u (Tmap u) (Tmap u) = Tmap u`
is precisely what `rotheLimit_crossImplicitMap_fixed` proves for
`Tmap u = rotheLimit (z u)` (the Rothe limit of the `u`-frozen implicit-Euler
orbit).  The continuity/compactness fields reuse the EXACT shapes from
`Statements.lean` (`LocalUniformContinuousOn` / `LocalUniformSequentiallyCompactRange`). -/
def FrozenStationaryMapSchauderData
    (p : CMParams) (c lam : ℝ) (trap : (ℝ → ℝ) → Prop)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ) : Prop :=
  (∀ u, trap u → trap (Tmap u))
    ∧ (∀ u, trap u → crossImplicitMap p c lam u (Tmap u) (Tmap u) = Tmap u)
    ∧ LocalUniformContinuousOn trap Tmap
    ∧ LocalUniformSequentiallyCompactRange trap Tmap

namespace FrozenStationaryMapSchauderData

variable {p : CMParams} {c lam : ℝ} {trap : (ℝ → ℝ) → Prop} {Tmap : (ℝ → ℝ) → ℝ → ℝ}

/-- Invariance field. -/
theorem invariant (h : FrozenStationaryMapSchauderData p c lam trap Tmap) :
    ∀ u, trap u → trap (Tmap u) := h.1

/-- The diagonal cross-fixed-point field: `Tmap u` solves the self-frozen Green
equation. -/
theorem crossDiagonal (h : FrozenStationaryMapSchauderData p c lam trap Tmap) :
    ∀ u, trap u → crossImplicitMap p c lam u (Tmap u) (Tmap u) = Tmap u := h.2.1

/-- Local-uniform continuity field. -/
theorem continuousOn (h : FrozenStationaryMapSchauderData p c lam trap Tmap) :
    LocalUniformContinuousOn trap Tmap := h.2.2.1

/-- Local-uniform sequentially-compact-range field. -/
theorem compactRange (h : FrozenStationaryMapSchauderData p c lam trap Tmap) :
    LocalUniformSequentiallyCompactRange trap Tmap := h.2.2.2

/-! ## The headline: a trapped self-frozen stationary profile -/

/-- **Parallel-bridge existence of a self-frozen stationary profile.**
From the G1 abstract principle (`hprinciple`) and the four data fields
(`hdata`), the Schauder principle produces a trapped fixed point `Tmap U = U`.
The diagonal cross-fixed-point field at `u = U` gives
`crossImplicitMap p c lam U (Tmap U) (Tmap U) = Tmap U`; rewriting `Tmap U = U`
collapses it to `crossImplicitMap p c lam U U U = U`, which
`rotheLimit_auxMap_fixed_at_diagonal` turns into `auxMap p c lam U = U`.  With
the carried per-fixed-point `GreenIdentity` (`hGreen`, discharged elsewhere via
`greenIdentity_of_convRepr` + `flux_ibp`), `fixedPoint_stationary` yields the
self-frozen stationary profile `∀ x, frozenWaveOperator p c U U x = 0`. -/
theorem exists_self_frozen_stationary
    (hprinciple : LocalUniformSchauderFixedPointPrinciple trap)
    (hdata : FrozenStationaryMapSchauderData p c lam trap Tmap)
    (hGreen : ∀ U, trap U → Tmap U = U → GreenIdentity p c lam U) :
    ∃ U, trap U ∧ (∀ x, frozenWaveOperator p c U U x = 0) := by
  -- G1 + invariance/continuity/compactness ⟹ a trapped fixed point.
  obtain ⟨U, hU, hfix⟩ :=
    hprinciple Tmap hdata.invariant hdata.continuousOn hdata.compactRange
  -- diagonal cross-fixed-point field at u = U, then rewrite Tmap U = U.
  have hcrossT : crossImplicitMap p c lam U (Tmap U) (Tmap U) = Tmap U :=
    hdata.crossDiagonal U hU
  have hcross : crossImplicitMap p c lam U U U = U := by
    rw [hfix] at hcrossT; exact hcrossT
  -- diagonal collapse to auxMap, then stationarity via the committed pieces.
  have hstat : ∀ x, frozenWaveOperator p c U U x = 0 :=
    rotheLimit_stationary p c lam U hcross (hGreen U hU hfix)
  exact ⟨U, hU, hstat⟩

end FrozenStationaryMapSchauderData

/-! ## Step 3 — wiring into the committed B1 χ≤0 headline

The produced `U` (trap + `∀ x, frozenWaveOperator p c U U x = 0`) is exactly the
input of the committed profile join `FrozenStationaryWaveProfile.mk_auto_limits`
(Statements.lean), which needs in addition: `0 < c`, strict positivity
`0 < U x`, `IsCUnifBdd U`, and the two endpoint limits `U → 1` at `-∞`, `U → 0`
at `+∞` (these are the committed Shen/tail/`V'≤0`/`U→1` lemmas on the trapped
profile; here they are carried as explicit hypotheses on the produced `U`). -/

/-- **B1 χ≤0 existence from the parallel Schauder data.**
Wires `FrozenStationaryMapSchauderData.exists_self_frozen_stationary` into the
committed `FrozenStationaryWaveProfile.mk_auto_limits`, carrying the
per-fixed-point analytic profile data (positivity, `C¹`-uniform bound, endpoint
limits) as explicit hypotheses on the produced trapped fixed point.

The endpoint/positivity/bound hypotheses are exactly the committed
Shen/tail/`V'≤0`/`U→1` profile lemmas; the elliptic-limit halves are filled in
automatically by `mk_auto_limits` from `frozenElliptic_tendsto_at{Bot,Top}`. -/
theorem b1_chiNeg_existence_of_schauderData
    {p : CMParams} {c lam : ℝ} {trap : (ℝ → ℝ) → Prop} {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hc : 0 < c)
    (hprinciple : LocalUniformSchauderFixedPointPrinciple trap)
    (hdata : FrozenStationaryMapSchauderData p c lam trap Tmap)
    (hGreen : ∀ U, trap U → Tmap U = U → GreenIdentity p c lam U)
    (hpos : ∀ U, trap U → (∀ x, 0 < U x))
    (hbdd : ∀ U, trap U → IsCUnifBdd U)
    (hlim_neg : ∀ U, trap U → Tendsto U atBot (𝓝 1))
    (hlim_pos : ∀ U, trap U → Tendsto U atTop (𝓝 0)) :
    ∃ U, trap U ∧ FrozenStationaryWaveProfile p c U := by
  obtain ⟨U, hU, hstat⟩ :=
    hdata.exists_self_frozen_stationary hprinciple hGreen
  refine ⟨U, hU, ?_⟩
  exact FrozenStationaryWaveProfile.mk_auto_limits hc (hpos U hU) (hbdd U hU)
    hstat (hlim_neg U hU) (hlim_pos U hU)

/-- Monotone-trap Schauder wrapper with the left endpoint produced by route (b).

Compared with `b1_chiNeg_existence_of_schauderData`, this removes the carried
`hlim_neg` profile input.  It instead consumes the flatness of the produced
stationary profile at `-∞`; stationarity makes the left limit a reaction root,
and the paper uniform floor rules out the zero root. -/
theorem b1_chiNeg_existence_of_schauderData_rootPin
    {p : CMParams} {c lam κ M : ℝ} {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hc : 0 < c)
    (hprinciple :
      LocalUniformSchauderFixedPointPrinciple (InMonotoneWaveTrapSet κ M))
    (hdata :
      FrozenStationaryMapSchauderData p c lam
        (InMonotoneWaveTrapSet κ M) Tmap)
    (hGreen : ∀ U, InMonotoneWaveTrapSet κ M U → Tmap U = U →
      GreenIdentity p c lam U)
    (hpos : ∀ U, InMonotoneWaveTrapSet κ M U → (∀ x, 0 < U x))
    (hfloor : ∀ U, InMonotoneWaveTrapSet κ M U → PaperPositiveInitialDatum U)
    (hbdd : ∀ U, InMonotoneWaveTrapSet κ M U → IsCUnifBdd U)
    (hflat : ∀ U, InMonotoneWaveTrapSet κ M U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U)
    (hlim_pos : ∀ U, InMonotoneWaveTrapSet κ M U → Tendsto U atTop (𝓝 0)) :
    ∃ U, InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U := by
  obtain ⟨U, hU, hstat⟩ :=
    hdata.exists_self_frozen_stationary hprinciple hGreen
  have hlim_neg : Tendsto U atBot (𝓝 1) :=
    InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_floor
      (p := p) (c := c) hU (hfloor U hU) (hflat U hU hstat) hstat
  refine ⟨U, hU, ?_⟩
  exact FrozenStationaryWaveProfile.mk_auto_limits hc (hpos U hU) (hbdd U hU)
    hstat hlim_neg (hlim_pos U hU)

/-- Schauder-data wrapper whose fixed-point stationarity is supplied directly,
and whose strict positivity is supplied by the paper-positive floor.

This removes the two profile-surface inputs `hGreen` and `hpos`: the theorem
does not ask for a Green identity, and the pointwise positivity is discharged by
`PaperPositiveInitialDatum.floor`. -/
theorem b1_chiNeg_existence_of_schauderData_stationary_floor
    {p : CMParams} {c lam : ℝ} {trap : (ℝ → ℝ) → Prop}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hc : 0 < c)
    (hprinciple : LocalUniformSchauderFixedPointPrinciple trap)
    (hdata : FrozenStationaryMapSchauderData p c lam trap Tmap)
    (hstationary : ∀ U, trap U → Tmap U = U →
      ∀ x, frozenWaveOperator p c U U x = 0)
    (hfloor : ∀ U, trap U → PaperPositiveInitialDatum U)
    (hbdd : ∀ U, trap U → IsCUnifBdd U)
    (hlim_neg : ∀ U, trap U → Tendsto U atBot (𝓝 1))
    (hlim_pos : ∀ U, trap U → Tendsto U atTop (𝓝 0)) :
    ∃ U, trap U ∧ FrozenStationaryWaveProfile p c U := by
  obtain ⟨U, hU, hfix⟩ :=
    hprinciple Tmap hdata.invariant hdata.continuousOn hdata.compactRange
  refine ⟨U, hU, ?_⟩
  exact FrozenStationaryWaveProfile.mk_auto_limits hc
    ((hfloor U hU).pos) (hbdd U hU)
    (hstationary U hU hfix) (hlim_neg U hU) (hlim_pos U hU)

/-- Monotone-trap Schauder wrapper with direct fixed-point stationarity, paper
floor positivity, and route-b left endpoint from stationary flatness. -/
theorem b1_chiNeg_existence_of_schauderData_stationary_floor_rootPin
    {p : CMParams} {c lam κ M : ℝ} {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hc : 0 < c)
    (hprinciple :
      LocalUniformSchauderFixedPointPrinciple (InMonotoneWaveTrapSet κ M))
    (hdata :
      FrozenStationaryMapSchauderData p c lam
        (InMonotoneWaveTrapSet κ M) Tmap)
    (hstationary : ∀ U, InMonotoneWaveTrapSet κ M U → Tmap U = U →
      ∀ x, frozenWaveOperator p c U U x = 0)
    (hfloor : ∀ U, InMonotoneWaveTrapSet κ M U → PaperPositiveInitialDatum U)
    (hbdd : ∀ U, InMonotoneWaveTrapSet κ M U → IsCUnifBdd U)
    (hflat : ∀ U, InMonotoneWaveTrapSet κ M U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U)
    (hlim_pos : ∀ U, InMonotoneWaveTrapSet κ M U → Tendsto U atTop (𝓝 0)) :
    ∃ U, InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U := by
  obtain ⟨U, hU, hfix⟩ :=
    hprinciple Tmap hdata.invariant hdata.continuousOn hdata.compactRange
  have hstat : ∀ x, frozenWaveOperator p c U U x = 0 :=
    hstationary U hU hfix
  have hlim_neg : Tendsto U atBot (𝓝 1) :=
    InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_floor
      (p := p) (c := c) hU (hfloor U hU) (hflat U hU hstat) hstat
  refine ⟨U, hU, ?_⟩
  exact FrozenStationaryWaveProfile.mk_auto_limits hc
    ((hfloor U hU).pos) (hbdd U hU) hstat hlim_neg (hlim_pos U hU)

section AxiomAudit
#print axioms b1_chiNeg_existence_of_schauderData_rootPin
#print axioms b1_chiNeg_existence_of_schauderData_stationary_floor
#print axioms b1_chiNeg_existence_of_schauderData_stationary_floor_rootPin
end AxiomAudit

end ShenWork.Paper1
