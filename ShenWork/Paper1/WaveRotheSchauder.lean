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

/-- Schauder fixed-point principle strengthened by a non-triviality conclusion.

This is the missing frontier for the present trap: it selects a fixed point
which is positive somewhere.  The ordinary `LocalUniformSchauderFixedPointPrinciple`
does not exclude the zero stationary solution. -/
def LocalUniformNontrivialSchauderFixedPointPrinciple
    (trap : (ℝ → ℝ) → Prop) : Prop :=
  ∀ Tmap : (ℝ → ℝ) → ℝ → ℝ,
    (∀ u, trap u → trap (Tmap u)) →
      LocalUniformContinuousOn trap Tmap →
        LocalUniformSequentiallyCompactRange trap Tmap →
          ∃ U : ℝ → ℝ, trap U ∧ Tmap U = U ∧ ProfileNontrivial U

/-- The constant-zero self-map on profiles. -/
def constantZeroProfileMap : (ℝ → ℝ) → ℝ → ℝ :=
  fun _ _ => 0

/-- The constant-zero self-map is locally-uniformly continuous on every trap. -/
theorem localUniformContinuousOn_constantZeroProfileMap
    (trap : (ℝ → ℝ) → Prop) :
    LocalUniformContinuousOn trap constantZeroProfileMap := by
  intro seq u _hseq _hu _hconv R _hR ε hε
  exact Filter.Eventually.of_forall fun _n x _hx => by
    simpa [constantZeroProfileMap] using hε

/-- The constant-zero self-map has singleton compact range when zero lies in the trap. -/
theorem localUniformSequentiallyCompactRange_constantZeroProfileMap
    {trap : (ℝ → ℝ) → Prop}
    (h0 : trap (fun _ : ℝ => (0 : ℝ))) :
    LocalUniformSequentiallyCompactRange trap constantZeroProfileMap := by
  intro _seq _hseq
  refine ⟨id, strictMono_id, fun _ : ℝ => (0 : ℝ), h0, ?_⟩
  intro R _hR ε hε
  exact Filter.Eventually.of_forall fun _n x _hx => by
    simpa [constantZeroProfileMap] using hε

/-- The strengthened non-trivial Schauder principle is false on the bare monotone
wave trap whenever the zero profile belongs to that trap.

The refuting map is the constant-zero map.  It is trap-invariant, continuous in the
local-uniform topology, and has singleton range.  Its only fixed point is zero,
which fails `ProfileNontrivial`. -/
theorem not_localUniformNontrivialSchauderFixedPointPrinciple_bareTrap
    (κ M : ℝ) (h0 : InMonotoneWaveTrapSet κ M (fun _ : ℝ => (0 : ℝ))) :
    ¬ LocalUniformNontrivialSchauderFixedPointPrinciple
      (InMonotoneWaveTrapSet κ M) := by
  intro hprinciple
  let Tmap0 := constantZeroProfileMap
  have hinv :
      ∀ u, InMonotoneWaveTrapSet κ M u →
        InMonotoneWaveTrapSet κ M (Tmap0 u) := by
    intro _u _hu
    simpa [Tmap0, constantZeroProfileMap] using h0
  have hcont : LocalUniformContinuousOn (InMonotoneWaveTrapSet κ M) Tmap0 := by
    simpa [Tmap0] using
      localUniformContinuousOn_constantZeroProfileMap
        (InMonotoneWaveTrapSet κ M)
  have hcompact :
      LocalUniformSequentiallyCompactRange (InMonotoneWaveTrapSet κ M) Tmap0 := by
    simpa [Tmap0] using
      localUniformSequentiallyCompactRange_constantZeroProfileMap
        (trap := InMonotoneWaveTrapSet κ M) h0
  obtain ⟨U, _hU, hfix, hnontriv⟩ :=
    hprinciple Tmap0 hinv hcont hcompact
  have hnontriv0 : ProfileNontrivial (fun _ : ℝ => (0 : ℝ)) := by
    simpa [Tmap0, constantZeroProfileMap] using
      (show ProfileNontrivial (Tmap0 U) from by
        rw [hfix]
        exact hnontriv)
  exact not_profileNontrivial_zero hnontriv0

/-- Convenient zero-profile refutation under the standard scalar side condition
`0 ≤ M`, using the committed bare-trap membership lemma. -/
theorem not_localUniformNontrivialSchauderFixedPointPrinciple_bareTrap_of_nonneg_M
    (κ M : ℝ) (hM : 0 ≤ M) :
    ¬ LocalUniformNontrivialSchauderFixedPointPrinciple
      (InMonotoneWaveTrapSet κ M) :=
  not_localUniformNontrivialSchauderFixedPointPrinciple_bareTrap κ M
    (InMonotoneWaveTrapSet.zero (κ := κ) (M := M) hM)

/-- Lower-pinned monotone trap: the usual monotone wave trap plus a pointwise
positive lower barrier `φ ≤ U`. -/
def InLowerPinnedMonotoneTrap
    (κ M : ℝ) (φ : ℝ → ℝ) (U : ℝ → ℝ) : Prop :=
  InMonotoneWaveTrapSet κ M U ∧ ∀ x, φ x ≤ U x

namespace InLowerPinnedMonotoneTrap

theorem bare {κ M : ℝ} {φ U : ℝ → ℝ}
    (hU : InLowerPinnedMonotoneTrap κ M φ U) :
    InMonotoneWaveTrapSet κ M U :=
  hU.1

theorem lower {κ M : ℝ} {φ U : ℝ → ℝ}
    (hU : InLowerPinnedMonotoneTrap κ M φ U) :
    ∀ x, φ x ≤ U x :=
  hU.2

/-- A strictly positive lower pin makes every pinned profile non-trivial. -/
theorem profileNontrivial {κ M : ℝ} {φ U : ℝ → ℝ}
    (hφpos : ∀ x, 0 < φ x)
    (hU : InLowerPinnedMonotoneTrap κ M φ U) :
    ProfileNontrivial U :=
  ⟨0, lt_of_lt_of_le (hφpos 0) (hU.lower 0)⟩

/-- A strictly positive lower pin gives pointwise positivity. -/
theorem pos {κ M : ℝ} {φ U : ℝ → ℝ}
    (hφpos : ∀ x, 0 < φ x)
    (hU : InLowerPinnedMonotoneTrap κ M φ U) :
    ∀ x, 0 < U x :=
  fun x => lt_of_lt_of_le (hφpos x) (hU.lower x)

end InLowerPinnedMonotoneTrap

/-- A positive lower pin excludes the zero profile from the pinned trap. -/
theorem not_zero_mem_InLowerPinnedMonotoneTrap
    {κ M : ℝ} {φ : ℝ → ℝ} {x₀ : ℝ}
    (hφpos : 0 < φ x₀) :
    ¬ InLowerPinnedMonotoneTrap κ M φ (fun _ : ℝ => (0 : ℝ)) := by
  intro h0
  have hle0 : φ x₀ ≤ 0 := by
    simpa using h0.lower x₀
  exact not_lt_of_ge hle0 hφpos

/-- The lower-barrier plateau itself is an inhabitant of its pinned trap whenever
it is already a member of the underlying monotone wave trap. -/
theorem lowerBarrierPlateau_mem_InLowerPinnedMonotoneTrap_of_exp_xplus_le
    {κ κtilde D M : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hD : 0 < D)
    (hM : Real.exp (-κ * lowerBarrierXPlus κ κtilde D) ≤ M) :
    InLowerPinnedMonotoneTrap κ M
      (lowerBarrierPlateau κ κtilde D)
      (lowerBarrierPlateau κ κtilde D) :=
  ⟨lowerBarrierPlateau_mem_InMonotoneWaveTrapSet_of_exp_xplus_le
      hκ hgap hD hM,
    fun _ => le_rfl⟩

/-- The lower-barrier pinned trap excludes zero. -/
theorem lowerBarrierPlateau_not_zero_mem_InLowerPinnedMonotoneTrap
    {κ κtilde D M : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hD : 0 < D) :
    ¬ InLowerPinnedMonotoneTrap κ M
      (lowerBarrierPlateau κ κtilde D) (fun _ : ℝ => (0 : ℝ)) :=
  not_zero_mem_InLowerPinnedMonotoneTrap
    (x₀ := 0) (lowerBarrierPlateau_pos hκ hgap hD 0)

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

/-- Restrict bare monotone-trap Schauder data to a lower-pinned trap, provided the
map is genuinely lower-barrier invariant on pinned inputs.

The compact-range field is not merely restricted: the bare compactness gives a
locally-uniform limit in the bare trap, and the lower pin passes to that limit
pointwise. -/
theorem lowerPinned
    {κ M : ℝ} {φ : ℝ → ℝ}
    (hdata :
      FrozenStationaryMapSchauderData p c lam
        (InMonotoneWaveTrapSet κ M) Tmap)
    (hlower : ∀ u, InLowerPinnedMonotoneTrap κ M φ u →
      ∀ x, φ x ≤ Tmap u x) :
    FrozenStationaryMapSchauderData p c lam
      (InLowerPinnedMonotoneTrap κ M φ) Tmap := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u hu
    exact ⟨hdata.invariant u hu.bare, hlower u hu⟩
  · intro u hu
    exact hdata.crossDiagonal u hu.bare
  · intro seq u hseq hu hconv
    exact hdata.continuousOn seq u
      (fun n => (hseq n).bare) hu.bare hconv
  · intro seq hseq
    obtain ⟨subseq, hsubseq, U, hUbare, hconv⟩ :=
      hdata.compactRange seq (fun n => (hseq n).bare)
    refine ⟨subseq, hsubseq, U, ⟨hUbare, ?_⟩, hconv⟩
    intro x
    have hlimit :
        Tendsto (fun n => Tmap (seq (subseq n)) x) atTop (𝓝 (U x)) :=
      hconv.tendsto_at x
    have hconst : Tendsto (fun _ : ℕ => φ x) atTop (𝓝 (φ x)) :=
      tendsto_const_nhds
    exact le_of_tendsto_of_tendsto hconst hlimit
      (Filter.Eventually.of_forall fun n => hlower (seq (subseq n))
        (hseq (subseq n)) x)

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

/-- Non-vacuous root-pin wrapper: a non-trivial fixed point plus the strong
maximum principle supplies pointwise positivity; the flat stationary equation
then pins the left endpoint to `1`.

This theorem carries only satisfiable profile hypotheses.  The zero profile
fails `ProfileNontrivial`, and a genuine positive decaying wave satisfies it.
The strengthened non-trivial fixed-point principle is the exact construction
frontier not provided by the current trap/Schauder data. -/
theorem b1_chiNeg_existence_of_schauderData_stationary_nontrivial_rootPin
    {p : CMParams} {c lam κ M : ℝ} {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hc : 0 < c)
    (hprinciple :
      LocalUniformNontrivialSchauderFixedPointPrinciple
        (InMonotoneWaveTrapSet κ M))
    (hdata :
      FrozenStationaryMapSchauderData p c lam
        (InMonotoneWaveTrapSet κ M) Tmap)
    (hstationary : ∀ U, InMonotoneWaveTrapSet κ M U → Tmap U = U →
      ∀ x, frozenWaveOperator p c U U x = 0)
    (hsmp : StationaryStrongMaxPrinciple p c κ M)
    (hbdd : ∀ U, InMonotoneWaveTrapSet κ M U → IsCUnifBdd U)
    (hflat : ∀ U, InMonotoneWaveTrapSet κ M U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U)
    (hlim_pos : ∀ U, InMonotoneWaveTrapSet κ M U → Tendsto U atTop (𝓝 0)) :
    ∃ U, InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U := by
  obtain ⟨U, hU, hfix, hnontriv⟩ :=
    hprinciple Tmap hdata.invariant hdata.continuousOn hdata.compactRange
  have hstat : ∀ x, frozenWaveOperator p c U U x = 0 :=
    hstationary U hU hfix
  have hpos : ∀ x, 0 < U x := hsmp U hU hstat hnontriv
  have hlim_neg : Tendsto U atBot (𝓝 1) :=
    InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_pos
      hU hpos (hflat U hU hstat) hstat
  refine ⟨U, hU, ?_⟩
  exact FrozenStationaryWaveProfile.mk_auto_limits hc
    hpos (hbdd U hU) hstat hlim_neg (hlim_pos U hU)

/-- Lower-pinned monotone-trap wrapper.

This is the non-vacuous replacement for the bare-trap non-trivial Schauder route.
It uses the ordinary local-uniform Schauder fixed-point principle on the pinned
trap `InLowerPinnedMonotoneTrap κ M φ`.  Non-triviality and pointwise positivity
come from the trap field `φ ≤ U` plus `0 < φ`, not from a strengthened Schauder
principle.  The left endpoint is still pinned by the honest
`tendsto_atBot_one_of_stationary_flat_and_pos` route. -/
theorem b1_chiNeg_existence_of_lowerPinnedSchauderData_stationary_rootPin
    {p : CMParams} {c lam κ M : ℝ} {φ : ℝ → ℝ}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hc : 0 < c) (hκ : 0 < κ)
    (hprinciple :
      LocalUniformSchauderFixedPointPrinciple
        (InLowerPinnedMonotoneTrap κ M φ))
    (hdata :
      FrozenStationaryMapSchauderData p c lam
        (InLowerPinnedMonotoneTrap κ M φ) Tmap)
    (hstationary : ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
      Tmap U = U → ∀ x, frozenWaveOperator p c U U x = 0)
    (hφpos : ∀ x, 0 < φ x)
    (hflat : ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InLowerPinnedMonotoneTrap κ M φ U ∧
      FrozenStationaryWaveProfile p c U := by
  obtain ⟨U, hU, hfix⟩ :=
    hprinciple Tmap hdata.invariant hdata.continuousOn hdata.compactRange
  have hstat : ∀ x, frozenWaveOperator p c U U x = 0 :=
    hstationary U hU hfix
  have hpos : ∀ x, 0 < U x :=
    hU.pos hφpos
  have hlim_neg : Tendsto U atBot (𝓝 1) :=
    InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_pos
      hU.bare hpos (hflat U hU hstat) hstat
  have hlim_pos : Tendsto U atTop (𝓝 0) :=
    hU.bare.tendsto_atTop_zero hκ
  refine ⟨U, hU, ?_⟩
  exact FrozenStationaryWaveProfile.mk_auto_limits hc
    hpos hU.bare.trap.cunif_bdd hstat hlim_neg hlim_pos

/-- Specialization of the lower-pinned wrapper to the committed plateau lower
barrier. -/
theorem b1_chiNeg_existence_of_lowerBarrierPinnedSchauderData_stationary_rootPin
    {p : CMParams} {c lam κ κtilde D M : ℝ}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hc : 0 < c) (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hD : 0 < D)
    (hprinciple :
      LocalUniformSchauderFixedPointPrinciple
        (InLowerPinnedMonotoneTrap κ M
          (lowerBarrierPlateau κ κtilde D)))
    (hdata :
      FrozenStationaryMapSchauderData p c lam
        (InLowerPinnedMonotoneTrap κ M
          (lowerBarrierPlateau κ κtilde D)) Tmap)
    (hstationary : ∀ U,
      InLowerPinnedMonotoneTrap κ M
        (lowerBarrierPlateau κ κtilde D) U →
      Tmap U = U → ∀ x, frozenWaveOperator p c U U x = 0)
    (hflat : ∀ U,
      InLowerPinnedMonotoneTrap κ M
        (lowerBarrierPlateau κ κtilde D) U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InLowerPinnedMonotoneTrap κ M
        (lowerBarrierPlateau κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_of_lowerPinnedSchauderData_stationary_rootPin
    hc hκ hprinciple hdata hstationary
    (lowerBarrierPlateau_pos hκ hgap hD) hflat

section AxiomAudit
#print axioms not_localUniformNontrivialSchauderFixedPointPrinciple_bareTrap
#print axioms lowerBarrierPlateau_not_zero_mem_InLowerPinnedMonotoneTrap
#print axioms lowerBarrierPlateau_mem_InLowerPinnedMonotoneTrap_of_exp_xplus_le
#print axioms b1_chiNeg_existence_of_lowerPinnedSchauderData_stationary_rootPin
#print axioms b1_chiNeg_existence_of_schauderData_rootPin
#print axioms b1_chiNeg_existence_of_schauderData_stationary_floor
#print axioms b1_chiNeg_existence_of_schauderData_stationary_floor_rootPin
#print axioms b1_chiNeg_existence_of_schauderData_stationary_nontrivial_rootPin
end AxiomAudit

end ShenWork.Paper1
