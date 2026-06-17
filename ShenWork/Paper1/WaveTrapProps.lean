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
#print axioms not_monotoneTrap_profile_hpos
#print axioms not_monotoneTrap_profile_hlim_neg
end AxiomAudit

end ShenWork.Paper1
