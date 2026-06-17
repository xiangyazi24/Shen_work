/-
  Trap-property lemmas for the monotone wave trap set.

  These discharge the `mk_auto_limits` hypotheses for the B1 traveling-wave
  existence assembly that are pure trap-membership facts (independent of the
  Schauder fixed-point construction):

  * uniform boundedness of a trap profile, and
  * the right limit U → 0 at +∞.

  Both follow directly from `InMonotoneWaveTrapSet κ M U` membership.
  (Strict positivity 0 < U is NOT a trap-membership fact — see the module
  comment at the end.)
-/
import ShenWork.Paper1.Statements
import ShenWork.Paper1.WaveRotheStep

open Filter Topology

namespace ShenWork.Paper1

/-- A monotone-wave-trap profile is `C`-uniformly bounded.

`InMonotoneWaveTrapSet κ M U` packages `InWaveTrapSet κ M U`, whose first
component is exactly `IsCUnifBdd U`, so this is immediate from the trap. -/
theorem inMonotoneWaveTrapSet_isCUnifBdd
    (_p : CMParams) (κ M : ℝ) (U : ℝ → ℝ)
    (hU : InMonotoneWaveTrapSet κ M U) :
    IsCUnifBdd U :=
  hU.trap.cunif_bdd

/-- A monotone-wave-trap profile tends to `0` at `+∞`.

By the squeeze `0 ≤ U x ≤ upperBarrier κ M x ≤ exp (-κ x)` with
`exp (-κ x) → 0` (using `0 < κ`). The positivity of `κ` is a genuine side
condition of the upper-barrier decay, not derivable from trap membership
alone; the existence-assembly callsites supply it. -/
theorem inMonotoneWaveTrapSet_tendsto_atTop_zero
    (_p : CMParams) (κ M : ℝ) (U : ℝ → ℝ)
    (hκ : 0 < κ) (hU : InMonotoneWaveTrapSet κ M U) :
    Filter.Tendsto U Filter.atTop (nhds 0) :=
  hU.trap.tendsto_atTop_zero hκ

/-- Exact universal `hbdd` profile obligation discharged from trap membership. -/
theorem monotoneTrap_profile_hbdd {κ M : ℝ} :
    ∀ U : ℝ → ℝ, InMonotoneWaveTrapSet κ M U → IsCUnifBdd U :=
  fun _U hU => hU.trap.cunif_bdd

/-- Exact universal `hlim_pos` profile obligation discharged from the trap
upper barrier, assuming the exponential rate is strictly positive. -/
theorem monotoneTrap_profile_hlim_pos {κ M : ℝ} (hκ : 0 < κ) :
    ∀ U : ℝ → ℝ,
      InMonotoneWaveTrapSet κ M U → Tendsto U atTop (𝓝 0) :=
  fun _U hU => hU.tendsto_atTop_zero hκ

/-- A paper-positive datum is strictly positive at every point, by its uniform
floor. -/
theorem PaperPositiveInitialDatum.pos {U : ℝ → ℝ}
    (hfloor : PaperPositiveInitialDatum U) :
    ∀ x, 0 < U x :=
  hfloor.floor.pos

/-- Non-triviality of a nonnegative wave profile: positive somewhere.

This is the non-vacuous pin needed before applying the strong maximum
principle.  The zero profile does not satisfy it, while a positive decaying
traveling wave does. -/
def ProfileNontrivial (U : ℝ → ℝ) : Prop :=
  ∃ x : ℝ, 0 < U x

theorem not_profileNontrivial_zero :
    ¬ ProfileNontrivial (fun _ : ℝ => (0 : ℝ)) := by
  rintro ⟨x, hx⟩
  exact (lt_irrefl (0 : ℝ)) hx

/-- The zero profile is a stationary solution of the frozen wave operator. -/
theorem frozenWaveOperator_zero_eq_zero (p : CMParams) (c x : ℝ) :
    frozenWaveOperator p c (fun _ : ℝ => (0 : ℝ))
      (fun _ : ℝ => (0 : ℝ)) x = 0 := by
  unfold frozenWaveOperator
  have hm_ne : p.m ≠ 0 := by linarith [p.hm]
  have hα_ne : p.α ≠ 0 := by linarith [p.hα]
  simp [Real.zero_rpow hm_ne, Real.zero_rpow hα_ne]

/-- A stationary strong-maximum-principle frontier for trapped profiles.

It is intentionally conditional on `ProfileNontrivial U`; hence the zero
stationary solution is excluded by a satisfiable hypothesis, not by a uniform
floor on the whole trap. -/
def StationaryStrongMaxPrinciple
    (p : CMParams) (c κ M : ℝ) : Prop :=
  ∀ U : ℝ → ℝ,
    InMonotoneWaveTrapSet κ M U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        ProfileNontrivial U →
          ∀ x, 0 < U x

/-- The paper-positive floor cannot be carried for every trapped profile:
the zero trapped profile refutes it. -/
theorem not_monotoneTrap_profile_paperPositiveInitialDatum
    {κ M : ℝ} (hM : 0 ≤ M) :
    ¬ (∀ U : ℝ → ℝ,
      InMonotoneWaveTrapSet κ M U → PaperPositiveInitialDatum U) := by
  intro hfloor
  exact not_profileNontrivial_zero
    ⟨0, (hfloor (fun _ : ℝ => (0 : ℝ))
      (InMonotoneWaveTrapSet.zero (κ := κ) (M := M) hM)).pos 0⟩

/-- Exact universal `hpos` profile obligation discharged from the
paper-positive floor carried for each trapped profile. -/
theorem monotoneTrap_profile_hpos_of_floor {κ M : ℝ}
    (hfloor : ∀ U : ℝ → ℝ,
      InMonotoneWaveTrapSet κ M U → PaperPositiveInitialDatum U) :
    ∀ U : ℝ → ℝ, InMonotoneWaveTrapSet κ M U → ∀ x, 0 < U x :=
  fun U hU => (hfloor U hU).pos

/-- A monotone-wave-trap profile has a finite left limit.

This is the monotone-convergence part of the route to the left endpoint:
antitonicity gives the `atBot` limit as the supremum of the range, while the
trap bounds place the limit in `[0, M]`. -/
theorem monotoneTrap_left_limit_exists {κ M : ℝ} {U : ℝ → ℝ}
    (hU : InMonotoneWaveTrapSet κ M U) :
    ∃ L : ℝ, Tendsto U atBot (𝓝 L) ∧ 0 ≤ L ∧ L ≤ M := by
  let L : ℝ := sSup (Set.range U)
  have hbdd : BddAbove (Set.range U) := by
    refine ⟨M, ?_⟩
    rintro y ⟨x, rfl⟩
    exact hU.le_M x
  have hlim : Tendsto U atBot (𝓝 L) := by
    simpa [L] using tendsto_atBot_ciSup hU.antitone hbdd
  have hL0 : 0 ≤ L := by
    have hU0_le : U 0 ≤ L := by
      simpa [L] using le_csSup hbdd (Set.mem_range_self (0 : ℝ))
    exact le_trans (hU.nonneg 0) hU0_le
  have hLM : L ≤ M := by
    have hne : (Set.range U).Nonempty := Set.range_nonempty U
    simpa [L] using csSup_le hne (by
      rintro y ⟨x, rfl⟩
      exact hU.le_M x)
  exact ⟨L, hlim, hL0, hLM⟩

/-- A genuine left lower pin makes a finite left limit strictly positive. -/
theorem StrictlyPositiveAtLeft.limit_pos {U : ℝ → ℝ} {L : ℝ}
    (hleft : StrictlyPositiveAtLeft U) (hlim : Tendsto U atBot (𝓝 L)) :
    0 < L := by
  rcases hleft with ⟨δ, hδ, hδle⟩
  exact lt_of_lt_of_le hδ (ge_of_tendsto hlim hδle)

/-- Positive roots of the logistic reaction `s ↦ s * (1 - s ^ a)` equal `1`. -/
theorem reactionFun_root_eq_one_of_pos {a L : ℝ}
    (ha : 0 < a) (hL : 0 < L) (hroot : reactionFun a L = 0) :
    L = 1 := by
  have hfactor : 1 - L ^ a = 0 := by
    unfold reactionFun at hroot
    rcases mul_eq_zero.mp hroot with hLzero | hfac
    · exact False.elim ((ne_of_gt hL) hLzero)
    · exact hfac
  have hpow : L ^ a = 1 := by linarith
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hpow_lt : L ^ a < 1 := by
      rw [← Real.one_rpow a]
      exact Real.rpow_lt_rpow hL.le hlt ha
    linarith
  · have hpow_gt : 1 < L ^ a := by
      rw [← Real.one_rpow a]
      exact Real.rpow_lt_rpow zero_le_one hgt ha
    linarith

/-- Route-b pin step: a left limit that is a positive reaction root is `1`. -/
theorem tendsto_atBot_one_of_reaction_root_pin
    {a L : ℝ} {U : ℝ → ℝ}
    (ha : 0 < a) (hlim : Tendsto U atBot (𝓝 L))
    (hL : 0 < L) (hroot : reactionFun a L = 0) :
    Tendsto U atBot (𝓝 1) := by
  have hLone : L = 1 := reactionFun_root_eq_one_of_pos ha hL hroot
  simpa [hLone] using hlim

/-- Pointwise positivity plus monotonicity gives the route-b lower pin at
`-∞`: use `U 0` as the eventual lower bound on the left half-line. -/
theorem InMonotoneWaveTrapSet.strictlyPositiveAtLeft_of_pos
    {κ M : ℝ} {U : ℝ → ℝ} (hU : InMonotoneWaveTrapSet κ M U)
    (hpos : ∀ x, 0 < U x) :
    StrictlyPositiveAtLeft U := by
  refine ⟨U 0, hpos 0, ?_⟩
  refine eventually_atBot.2 ⟨0, ?_⟩
  intro x hx
  exact hU.antitone hx

/-- Single-profile route (b): monotone left limit + pointwise positivity
lower-pin + reaction-root at every left limit. -/
theorem InMonotoneWaveTrapSet.tendsto_atBot_one_of_limit_root_and_pos
    {κ M : ℝ} {U : ℝ → ℝ} (p : CMParams)
    (hU : InMonotoneWaveTrapSet κ M U)
    (hpos : ∀ x, 0 < U x)
    (hroot : ∀ L : ℝ, Tendsto U atBot (𝓝 L) → reactionFun p.α L = 0) :
    Tendsto U atBot (𝓝 1) := by
  rcases monotoneTrap_left_limit_exists hU with ⟨L, hlim, _hL0, _hLM⟩
  have hα : 0 < p.α := lt_of_lt_of_le zero_lt_one p.hα
  have hleft : StrictlyPositiveAtLeft U := hU.strictlyPositiveAtLeft_of_pos hpos
  have hL : 0 < L := hleft.limit_pos hlim
  exact tendsto_atBot_one_of_reaction_root_pin hα hlim hL (hroot L hlim)

/-- Single-profile route (b) with the paper-faithful uniform floor as the lower
pin.  The floor is the whole-line version of paper eq. (1.11). -/
theorem InMonotoneWaveTrapSet.tendsto_atBot_one_of_limit_root_and_floor
    {κ M : ℝ} {U : ℝ → ℝ} (p : CMParams)
    (hU : InMonotoneWaveTrapSet κ M U)
    (hfloor : PaperPositiveInitialDatum U)
    (hroot : ∀ L : ℝ, Tendsto U atBot (𝓝 L) → reactionFun p.α L = 0) :
    Tendsto U atBot (𝓝 1) := by
  rcases monotoneTrap_left_limit_exists hU with ⟨L, hlim, _hL0, _hLM⟩
  have hα : 0 < p.α := lt_of_lt_of_le zero_lt_one p.hα
  have hleft : StrictlyPositiveAtLeft U := hfloor.strictlyPositiveAtLeft
  have hL : 0 < L := hleft.limit_pos hlim
  exact tendsto_atBot_one_of_reaction_root_pin hα hlim hL (hroot L hlim)

/-- Flatness of a stationary frozen profile at the left endpoint: the two
linear derivative terms and the chemotactic flux derivative vanish at `-∞`. -/
def FrozenStationaryFlatAtLeft (p : CMParams) (U : ℝ → ℝ) : Prop :=
  Tendsto (fun x => iteratedDeriv 2 U x) atBot (𝓝 0) ∧
    Tendsto (fun x => deriv U x) atBot (𝓝 0) ∧
      Tendsto
        (fun x => deriv
          (fun y => (U y) ^ p.m * deriv (frozenElliptic p U) y) x)
        atBot (𝓝 0)

/-- Stationary-limit root step under the explicit flatness hypotheses at
`-∞`.  This isolates the analytic input still needed to derive `hroot` from
the stationary equation. -/
theorem reactionFun_root_of_stationary_flat_limit
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ} {L : ℝ}
    (hlim : Tendsto U atBot (𝓝 L))
    (hD2 : Tendsto (fun x => iteratedDeriv 2 U x) atBot (𝓝 0))
    (hD1 : Tendsto (fun x => deriv U x) atBot (𝓝 0))
    (hFlux : Tendsto
      (fun x => deriv
        (fun y => (U y) ^ p.m * deriv (frozenElliptic p U) y) x)
      atBot (𝓝 0))
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0) :
    reactionFun p.α L = 0 := by
  have hα_nonneg : 0 ≤ p.α := le_trans zero_le_one p.hα
  have hpow :
      Tendsto (fun x => (U x) ^ p.α) atBot (𝓝 (L ^ p.α)) :=
    hlim.rpow_const (Or.inr hα_nonneg)
  have hreact :
      Tendsto (fun x => reactionFun p.α (U x)) atBot
        (𝓝 (reactionFun p.α L)) := by
    unfold reactionFun
    exact hlim.mul (tendsto_const_nhds.sub hpow)
  have hsum :
      Tendsto
        (fun x =>
          iteratedDeriv 2 U x + c * deriv U x -
            p.χ *
              deriv
                (fun y => (U y) ^ p.m * deriv (frozenElliptic p U) y) x +
            reactionFun p.α (U x))
        atBot (𝓝 (reactionFun p.α L)) := by
    simpa using
      (((hD2.add (hD1.const_mul c)).add (hFlux.const_mul (-p.χ))).add hreact)
  have hop :
      Tendsto (fun x => frozenWaveOperator p c U U x) atBot
        (𝓝 (reactionFun p.α L)) := by
    simpa [frozenWaveOperator, reactionFun, sub_eq_add_neg, mul_assoc] using hsum
  have hzero : Tendsto (fun x => frozenWaveOperator p c U U x) atBot (𝓝 0) := by
    simpa [hstat] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atBot (𝓝 0))
  exact tendsto_nhds_unique hop hzero

/-- Single-profile route (b) with all analytic ingredients explicit:
monotone bounded left limit, stationary-flat root, and paper floor pin. -/
theorem InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_floor
    {κ M : ℝ} {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hU : InMonotoneWaveTrapSet κ M U)
    (hfloor : PaperPositiveInitialDatum U)
    (hflat : FrozenStationaryFlatAtLeft p U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0) :
    Tendsto U atBot (𝓝 1) := by
  refine InMonotoneWaveTrapSet.tendsto_atBot_one_of_limit_root_and_floor
    p hU hfloor ?_
  intro L hlim
  exact reactionFun_root_of_stationary_flat_limit hlim
    hflat.1 hflat.2.1 hflat.2.2 hstat

/-- Single-profile route (b) with pointwise positivity instead of the vacuous
whole-trap paper floor. -/
theorem InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_pos
    {κ M : ℝ} {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hU : InMonotoneWaveTrapSet κ M U)
    (hpos : ∀ x, 0 < U x)
    (hflat : FrozenStationaryFlatAtLeft p U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0) :
    Tendsto U atBot (𝓝 1) := by
  refine InMonotoneWaveTrapSet.tendsto_atBot_one_of_limit_root_and_pos
    p hU hpos ?_
  intro L hlim
  exact reactionFun_root_of_stationary_flat_limit hlim
    hflat.1 hflat.2.1 hflat.2.2 hstat

/-- Strong-maximum-principle route: non-trivial stationary nonnegative trapped
profiles are strictly positive; then the flat left endpoint pins the left
limit to `1`. -/
theorem InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_nontrivial
    {κ M : ℝ} {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hU : InMonotoneWaveTrapSet κ M U)
    (hsmp : StationaryStrongMaxPrinciple p c κ M)
    (hnontriv : ProfileNontrivial U)
    (hflat : FrozenStationaryFlatAtLeft p U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0) :
    Tendsto U atBot (𝓝 1) := by
  exact InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_pos
    hU (hsmp U hU hstat hnontriv) hflat hstat

/-- Formal route (b): monotone left limit + reaction-root + lower-pin. -/
theorem monotoneTrap_profile_hlim_neg_of_limit_root_and_pin
    {κ M : ℝ} (p : CMParams)
    (hroot : ∀ U : ℝ → ℝ, InMonotoneWaveTrapSet κ M U →
      ∀ L : ℝ, Tendsto U atBot (𝓝 L) → reactionFun p.α L = 0)
    (hpin : ∀ U : ℝ → ℝ,
      InMonotoneWaveTrapSet κ M U → StrictlyPositiveAtLeft U) :
    ∀ U : ℝ → ℝ,
      InMonotoneWaveTrapSet κ M U → Tendsto U atBot (𝓝 1) := by
  intro U hU
  rcases monotoneTrap_left_limit_exists hU with ⟨L, hlim, _hL0, _hLM⟩
  have hα : 0 < p.α := lt_of_lt_of_le zero_lt_one p.hα
  have hL : 0 < L := (hpin U hU).limit_pos hlim
  exact tendsto_atBot_one_of_reaction_root_pin hα hlim hL (hroot U hU L hlim)

/-- Route (b) with the lower pin supplied by the usual pointwise positivity
profile obligation.  The remaining input is exactly the stationary-limit
reaction-root fact. -/
theorem monotoneTrap_profile_hlim_neg_of_limit_root_and_pos
    {κ M : ℝ} (p : CMParams)
    (hroot : ∀ U : ℝ → ℝ, InMonotoneWaveTrapSet κ M U →
      ∀ L : ℝ, Tendsto U atBot (𝓝 L) → reactionFun p.α L = 0)
    (hpos : ∀ U : ℝ → ℝ,
      InMonotoneWaveTrapSet κ M U → ∀ x, 0 < U x) :
    ∀ U : ℝ → ℝ,
      InMonotoneWaveTrapSet κ M U → Tendsto U atBot (𝓝 1) :=
  monotoneTrap_profile_hlim_neg_of_limit_root_and_pin p hroot
    (fun U hU => hU.strictlyPositiveAtLeft_of_pos (hpos U hU))

/-- Route (b) with the lower pin supplied by `PaperPositiveInitialDatum`, whose
uniform floor is the faithful paper eq. (1.11) input. -/
theorem monotoneTrap_profile_hlim_neg_of_limit_root_and_floor
    {κ M : ℝ} (p : CMParams)
    (hroot : ∀ U : ℝ → ℝ, InMonotoneWaveTrapSet κ M U →
      ∀ L : ℝ, Tendsto U atBot (𝓝 L) → reactionFun p.α L = 0)
    (hfloor : ∀ U : ℝ → ℝ,
      InMonotoneWaveTrapSet κ M U → PaperPositiveInitialDatum U) :
    ∀ U : ℝ → ℝ,
      InMonotoneWaveTrapSet κ M U → Tendsto U atBot (𝓝 1) :=
  monotoneTrap_profile_hlim_neg_of_limit_root_and_pin p hroot
    (fun U hU => (hfloor U hU).strictlyPositiveAtLeft)

/-- The route-b lower pin is not a monotone-trap fact: the zero profile refutes it. -/
theorem not_monotoneTrap_profile_strictlyPositiveAtLeft
    {κ M : ℝ} (hM : 0 ≤ M) :
    ¬ (∀ U : ℝ → ℝ,
      InMonotoneWaveTrapSet κ M U → StrictlyPositiveAtLeft U) := by
  intro h
  rcases h (fun _ : ℝ => (0 : ℝ))
      (InMonotoneWaveTrapSet.zero (κ := κ) (M := M) hM) with
    ⟨δ, hδ, hδle⟩
  have hδle0 : δ ≤ 0 := by
    exact ge_of_tendsto (f := fun _ : ℝ => (0 : ℝ)) tendsto_const_nhds hδle
  linarith

/-- Strict positivity is not a consequence of monotone-trap membership:
the zero profile is trapped whenever `0 ≤ M`. -/
theorem not_monotoneTrap_profile_hpos {κ M : ℝ} (hM : 0 ≤ M) :
    ¬ (∀ U : ℝ → ℝ,
      InMonotoneWaveTrapSet κ M U → ∀ x, 0 < U x) := by
  intro h
  have h0 : 0 < (0 : ℝ) := by
    simpa using h (fun _ : ℝ => (0 : ℝ))
      (InMonotoneWaveTrapSet.zero (κ := κ) (M := M) hM) 0
  exact (lt_irrefl (0 : ℝ)) h0

/-- The left endpoint limit `U → 1` at `-∞` is not a trap consequence:
the same zero trapped profile would have to tend to both `0` and `1`. -/
theorem not_monotoneTrap_profile_hlim_neg {κ M : ℝ} (hM : 0 ≤ M) :
    ¬ (∀ U : ℝ → ℝ,
      InMonotoneWaveTrapSet κ M U → Tendsto U atBot (𝓝 1)) := by
  intro h
  have hzero : Tendsto (fun _ : ℝ => (0 : ℝ)) atBot (𝓝 1) :=
    h (fun _ : ℝ => (0 : ℝ))
      (InMonotoneWaveTrapSet.zero (κ := κ) (M := M) hM)
  have hconst : Tendsto (fun _ : ℝ => (0 : ℝ)) atBot (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds
  have h01 : (0 : ℝ) = 1 := tendsto_nhds_unique hconst hzero
  norm_num at h01

/-
  STALL REPORT — strict positivity `0 < U x` is NOT a trap-membership fact.

  Target (3),

      inMonotoneWaveTrapSet_pos
        (p : CMParams) (κ M : ℝ) (U : ℝ → ℝ)
        (hU : InMonotoneWaveTrapSet κ M U) (x : ℝ) : 0 < U x,

  does not follow from `InMonotoneWaveTrapSet κ M U` alone.

  Unfolding the definitions (Statements.lean):

    InMonotoneWaveTrapSet κ M u := InWaveTrapSet κ M u ∧ NonincreasingProfile u   (L4377)
    InWaveTrapSet κ M u :=
      IsCUnifBdd u ∧ ∀ x, 0 ≤ u x ∧ u x ≤ upperBarrier κ M x                       (L4371)

  The only lower bound the trap carries is the NON-strict `0 ≤ u x`.  There is
  no lower-barrier component in the membership predicate.  Concretely the zero
  function is a trap member: `InWaveTrapSet.zero` (Statements.lean L4745) proves
  `InWaveTrapSet κ M (fun _ => 0)` for `0 ≤ M`, and it is trivially antitone, so
  `InMonotoneWaveTrapSet κ M (fun _ => 0)` holds while `0 < (fun _ => 0) x` is
  false.  Hence the goal is unprovable from `hU` and is in fact a counterexample.

  The lower barrier `lowerBarrierPlateau κ κtilde D` (Statements.lean L4220),
  which IS strictly positive (`lowerBarrierPlateau_pos`, L4246, needs
  `0 < κ`, `0 < κtilde - κ`, `0 < D`), is used only to EXHIBIT specific trap
  members (`exists_D_gt_lowerBarrierPlateau_mem_InMonotoneWaveTrapSet`, L4968);
  it is not part of trap membership.

  Strict positivity of the constructed wave profile must therefore come from the
  Schauder fixed-point construction / Shen package (where the iterate is pinned
  above the positive lower barrier), supplied to `mk_auto_limits` as the
  hypothesis `hU_pos : ∀ x, 0 < U x` (see the callsite
  `Theorem_1_1.of_raw_frozen_stationary_branches`, Statements.lean L16429,
  which consumes `hU_pos` from the existence proof `hneg`/`hpos`).

  Required extra hypothesis (true one): a strict lower bound on `U`, e.g.
  `∀ x, lowerBarrierPlateau κ κtilde D x ≤ U x` together with the plateau
  positivity, or directly `∀ x, 0 < U x` from the construction.  None of these
  is available from `InMonotoneWaveTrapSet κ M U`.

  STALL REPORT — `hGreen` is likewise not a trap-membership fact.

  Target shape:

      ∀ U, InMonotoneWaveTrapSet κ M U →
        rotheLimit (rotheSeq U) = U → GreenIdentity p c lam U

  The trap supplies only continuity, boundedness, nonnegativity, upper-barrier
  control, and antitonicity.  `GreenIdentity` is the variation-of-parameters
  identity for `auxMap`, and the committed closing theorem is
  `greenIdentity_holds`, which additionally needs source continuity, the two
  weighted Green-tail integrability hypotheses, and the convolution
  representation of `auxMap`.  None of those data are fields of
  `InMonotoneWaveTrapSet`, and the fixed-point equality of the Rothe limit is not
  itself a convolution representation.  Thus `hGreen` remains the genuine
  Green-representation frontier.
-/

section AxiomAudit
#print axioms monotoneTrap_profile_hbdd
#print axioms monotoneTrap_profile_hlim_pos
#print axioms PaperPositiveInitialDatum.pos
#print axioms not_profileNontrivial_zero
#print axioms frozenWaveOperator_zero_eq_zero
#print axioms not_monotoneTrap_profile_paperPositiveInitialDatum
#print axioms monotoneTrap_profile_hpos_of_floor
#print axioms monotoneTrap_left_limit_exists
#print axioms StrictlyPositiveAtLeft.limit_pos
#print axioms reactionFun_root_eq_one_of_pos
#print axioms tendsto_atBot_one_of_reaction_root_pin
#print axioms InMonotoneWaveTrapSet.strictlyPositiveAtLeft_of_pos
#print axioms InMonotoneWaveTrapSet.tendsto_atBot_one_of_limit_root_and_pos
#print axioms InMonotoneWaveTrapSet.tendsto_atBot_one_of_limit_root_and_floor
#print axioms reactionFun_root_of_stationary_flat_limit
#print axioms InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_floor
#print axioms InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_pos
#print axioms InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_nontrivial
#print axioms monotoneTrap_profile_hlim_neg_of_limit_root_and_pin
#print axioms monotoneTrap_profile_hlim_neg_of_limit_root_and_pos
#print axioms monotoneTrap_profile_hlim_neg_of_limit_root_and_floor
#print axioms not_monotoneTrap_profile_strictlyPositiveAtLeft
#print axioms not_monotoneTrap_profile_hpos
#print axioms not_monotoneTrap_profile_hlim_neg
end AxiomAudit

end ShenWork.Paper1
