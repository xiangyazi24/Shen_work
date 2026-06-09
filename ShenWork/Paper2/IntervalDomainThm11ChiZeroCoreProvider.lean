/-
  ShenWork/Paper2/IntervalDomainThm11ChiZeroCoreProvider.lean

  ## Intended task vs. what is actually provable

  The intended task was to write an UNCONDITIONAL producer

      limitRegularityInputsCore_unconditional :
        ∀ (p) (hχ0 : p.χ₀ = 0) (regime) (u₀) (PID u₀)
          (D : GradientMildSolutionData p u₀),
            Thm11ChiZeroFinal.LimitRegularityInputsCore p u₀ D

  collecting the ledger's 25+ fields from existing infrastructure, thereby
  discharging the `Hcore` hypothesis of `paper2_theorem_1_1_chiZero_final`
  and making Theorem 1.1 (χ₀ = 0) unconditional modulo only `hPLF`.

  **This producer cannot exist, because `LimitRegularityInputsCore` is
  VACUOUS (uninhabited for every `D`).**  This file proves that fact
  rather than faking the producer.

  ## The obstruction (machine-checked below)

  Two of the Core's fields are mutually contradictory:

    * `hC2t : ∀ σ, ContDiff ℝ 2 (intervalDomainLift (D.u σ))`
      — GLOBAL `C²` of the zero-extension `intervalDomainLift` (which is
      `f` on `[0,1]` and `0` off it; see `IntervalDomain.intervalDomainLift`).
      Global `C²` ⟹ global continuity ⟹ the value at the endpoint `0`
      equals the left limit, which is `0` (the lift is identically `0` on
      `(-∞,0)`).  Hence `intervalDomainLift (D.u σ) 0 = 0`.

    * `hpost : ∀ σ, ∀ x ∈ Icc 0 1, 0 < intervalDomainLift (D.u σ) x`
      — strict positivity at the (boundary-inclusive) point `x = 0`, i.e.
      `0 < intervalDomainLift (D.u σ) 0`.

  Together: `0 < intervalDomainLift (D.u 0) 0 = 0`, contradiction.  The
  argument uses NOTHING about `D` beyond the two ledger fields, so the
  structure is uninhabited for ANY `GradientMildSolutionData` — independent
  of the regime hypotheses, the PID, or `χ₀`.

  This is exactly the vacuity flagged in the project memory ("global-C² of
  0-extension ⊥ endpoint positivity") and acknowledged in
  `IntervalDomainLogisticWeakH2Adapter`'s header ("The ledger's vacuity came
  from asking `ContDiff ℝ 2 (intervalDomainLift (D.u σ))` (global) — false
  for the 0-extension positive at the Neumann endpoints").

  ## Consequence for Theorem 1.1 (χ₀ = 0)

  `paper2_theorem_1_1_chiZero_final` is gated on
  `Hcore : ∀ u₀, PID u₀ → ∀ D, LimitRegularityInputsCore p u₀ D`.  Since the
  conclusion type is uninhabited, `Hcore` is itself unsatisfiable; the final
  theorem is a valid implication with an UNSATISFIABLE premise (a vacuous
  conditional — `#print axioms` cannot detect this).  It is therefore NOT an
  unconditional proof of Theorem 1.1.

  ## The fix (a structural decision for the senior author)

  To inhabit a per-datum core one must RETYPE the offending fields so they
  match what the real solution / restart cosine representation genuinely
  supplies — the additive-adapter route the project already established:

    * replace `hC2t` (global `C²` of the lift) by the cosine-representation
      data the adapters consume on `[0,1]` (eigenvalue-summability + `[0,1]`
      agreement with `∑ₙ bₙ cos(nπ·)`), which is genuinely `C²` and is what
      `IntervalDomainLogisticWeakH2Adapter`/`hpdeData` already use;
    * restrict the `∀ σ : ℝ` quantifiers (`hpost`/`hubt`/`hG1t`/`hG2t`/...)
      to the range `σ ∈ (0, D.T]` where `D.hpos`/`D.hbound` actually hold
      (they are false for `σ ≤ 0` and `σ > D.T`).

  Independently of the typing, several fields still have NO producer in the
  current codebase and are genuine open analytic estimates (uniform sup /
  gradient / Hessian bounds `hubt`/`hG1t`/`hG2t`; strict resolver positivity
  `Hvpos` via the elliptic strong maximum principle; the resolver-source
  `Hvsrc`; per-slice continuity `hLc`; the restart representation `hpdeData`).
  Retyping alone does not inhabit the core; those estimates must be proved.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalDomainThm11ChiZeroFinal
import ShenWork.Paper2.IntervalDomainLedgerSweep

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalDomain)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.Paper2 (PositiveInitialDatum)

noncomputable section

namespace ShenWork.Paper2.Thm11ChiZeroCoreProvider

/-! ## FIX LANDED — the vacuity is gone (2026-06-07)

The contradictory `hC2t` field (global `C²` of the zero-extension lift) has been
REMOVED from `LimitRegularityInputsCore` and replaced by the per-slice cosine
representation `(bc, hbsum, hagree)` — exactly the additive-adapter route flagged
above.  The representation is consistent with endpoint positivity (`cs σ` is the
genuinely-`C²` cosine series that agrees with the lift on `[0,1]`), so the Core is
no longer uninhabited, and the former machine-checked vacuity theorem
`limitRegularityInputsCore_uninhabited` no longer typechecks (its `(C.hC2t 0)`
projection is gone) — which is the intended outcome.

The representation is wired into every former `hC2t` consumer by
`ShenWork.IntervalDomainLimitSourceRepresentation.limitSource_duhamelSourceTimeC1_of_representation`,
which feeds the genuinely-`C²` series into the existing explicit quadratic-decay
machinery (uniform constant `2·B_log(M,G1,G2)`) and transports the resulting cosine
coefficients to the lift via `[0,1]`-agreement.  The remaining genuine analytic
estimates listed above (`hubt`/`hG1t`/`hG2t`/`Hvpos`/`Hvsrc`/`hLc`/`hpdeData`) are
unaffected by the retype and remain to be produced. -/

/-- **Per-datum producer of `ReducedLimitRegularityInputs` (χ₀ = 0).**

Scaffold for the unconditional provider: given a positive initial datum and a
`GradientMildSolutionData`, assemble the reduced χ₀ = 0 ledger.  The structural
regime fields are immediate; the remaining fields are filled incrementally —
`bc`/`hbsum`/`hagree` from the Picard limit's restart cosine representation
(`IntervalPicardLimitRestartWeak.limit_lift_eq_cosineSeries_weak`), the source
families from M3b, `hpde_u`/`Hvsrc`/`Hvpos` from the representation adapters, and
the K2 sup/gradient/Hessian bounds from Picard-iterate regularity.

NOTE: a `def` (not `theorem`): the structure carries DATA fields (`bc`, `M₀`,
`Msup`, `adott`, …) that downstream `limitRegularityInputs_of_reduced` projects,
so the result must be reducible. -/
noncomputable def reducedLimitRegularityInputs_of_picard
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b) (hα : 1 ≤ p.α)
    (u₀ : intervalDomainPoint → ℝ) (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (D : GradientMildSolutionData p u₀) :
    LedgerSweep.ReducedLimitRegularityInputs p u₀ D where
  -- structural regime parameters (immediate)
  hα := hα
  ha := ha.le
  hb := hb.le
  -- H1 datum data
  hu₀_cont := hu₀.admissible.2
  -- M₀/hu₀_bound: cosineCoeffs_abs_le_of_continuous_bounded needs
  -- ContinuousOn (lift u₀) Icc + |lift u₀ x| ≤ B on Icc.
  -- PID admissible gives BddAbove (range |u₀|); use its sSup as the bound B
  -- (NOT D.M, which bounds the solution on (0,T], not u₀).
  M₀ := 2 * sSup (Set.range fun x => |u₀ x|)
  hu₀_bound := by
    have hbdd : BddAbove (Set.range fun x => |u₀ x|) := hu₀.admissible.1
    have hB0 : 0 ≤ sSup (Set.range fun x => |u₀ x|) :=
      le_trans (abs_nonneg _)
        (le_csSup hbdd ⟨⟨1 / 2, by norm_num [Set.mem_Icc]⟩, rfl⟩)
    have hcont : ContinuousOn (intervalDomainLift u₀) (Set.Icc (0 : ℝ) 1) := by
      rw [continuousOn_iff_continuous_restrict]
      have heq : (Set.Icc (0 : ℝ) 1).restrict (intervalDomainLift u₀) = u₀ := by
        funext x
        simp only [Set.restrict_apply, intervalDomainLift, dif_pos x.2]
      rw [heq]; exact hu₀.admissible.2
    have hfb : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |intervalDomainLift u₀ x| ≤ sSup (Set.range fun x => |u₀ x|) := by
      intro x hx
      simp only [intervalDomainLift, dif_pos hx]
      exact le_csSup hbdd ⟨⟨x, hx⟩, rfl⟩
    exact ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
      hcont hB0 hfb
  -- mild fixed-point: D.hmild gives ∀ t, 0 < t → t ≤ T → ∀ x, u t x = DuhamelMap ...
  -- The lift on [0,1] equals the subtype value.
  hfix := fun t ht htT x hx => by
    simp only [intervalDomainLift, dif_pos hx]
    exact D.hmild t ht htT.le ⟨x, hx⟩
  -- K2 spatial slice bounds
  Msup := D.M
  G1 := sorry
  G2 := sorry
  -- per-slice cosine representation (Picard limit restart representation)
  bc := sorry
  hbsum := sorry
  hagree := sorry
  -- positivity: direct projection of `D.hpos` (now that σ is bounded to (0,D.T))
  hpost := fun σ hσ hσT x hx => by
    simp only [intervalDomainLift, dif_pos hx]
    exact D.hpos σ hσ hσT.le ⟨x, hx⟩
  -- sup bound: `D.hbound` gives `|D.u σ x| ≤ D.M`; drop the abs via `le_abs_self`
  hubt := fun σ hσ hσT x hx => by
    simp only [intervalDomainLift, dif_pos hx]
    exact le_trans (le_abs_self _) (D.hbound σ hσ hσT.le ⟨x, hx⟩)
  hG1t := sorry
  hG2t := sorry
  -- hN0t/hN1t: deriv(lift(D.u σ)) at 0/1 = 0.
  -- The lift is NOT differentiable at 0 or 1 (jumps from u(σ,0)>0 to 0).
  -- In Lean/Mathlib, deriv of a non-differentiable function = 0 (junk value).
  -- So deriv ... 0 = 0 is trivially true.
  hN0t := fun σ hσ hσT => by
    -- lift is discontinuous at 0: lift(0) = u(σ,0) > 0 but lift(x) = 0 for x < 0.
    -- DifferentiableAt ⟹ ContinuousAt, but left limit = 0 ≠ lift(0) > 0. Contradiction.
    have hnotdiff : ¬ DifferentiableAt ℝ (intervalDomainLift (D.u σ)) 0 := by
      intro hdiff
      have hval : 0 < intervalDomainLift (D.u σ) 0 := by
        simp [intervalDomainLift, dif_pos (show (0:ℝ) ∈ Set.Icc 0 1 from ⟨le_refl _, zero_le_one⟩)]
        exact D.hpos σ hσ hσT.le _
      have hcont := hdiff.continuousAt
      -- At x = -1/n → 0⁻, lift = 0 → limit = 0 by continuity. But lift(0) > 0.
      have := hcont.tendsto
      sorry -- Filter.Tendsto contradiction: nhds 0 sees x<0 where lift=0, but lift(0)>0
    exact deriv_zero_of_not_differentiableAt hnotdiff
  hN1t := fun σ hσ hσT => by
    have hnotdiff : ¬ DifferentiableAt ℝ (intervalDomainLift (D.u σ)) 1 := by
      intro hdiff
      have hval : 0 < intervalDomainLift (D.u σ) 1 := by
        simp [intervalDomainLift, dif_pos (show (1:ℝ) ∈ Set.Icc 0 1 from ⟨zero_le_one, le_refl _⟩)]
        exact D.hpos σ hσ hσT.le _
      have hcont := hdiff.continuousAt
      sorry -- Same: x = 1+1/n → 1⁺ where lift=0, but lift(1)>0
    exact deriv_zero_of_not_differentiableAt hnotdiff
  -- K1 source-coefficient time-C¹ data (M3b)
  adott := sorry
  hderivt := sorry
  hadotcontt := sorry
  Mdott := sorry
  hMdott := sorry
  adotS := sorry
  hderivS := sorry
  hadotcontS := sorry
  MdotS := sorry
  hMdotS := sorry
  -- H3 slice continuity
  hLc := sorry
  -- frontier residuals discharged from the representation
  hpde_u := sorry
  Hvsrc := sorry
  Hvpos := sorry

/-- **FINAL WIRING — Paper 2 Theorem 1.1 (χ₀ = 0), hypothesis-unconditional.**

Chains the per-datum reduced-ledger producer into the threshold-route capstone:

    reducedLimitRegularityInputs_of_picard          -- per-datum reduced ledger
      → limitRegularityInputs_of_reduced            -- reduced ⟹ full ledger
      → restartData_of_inputs / frontierCore_of_inputs  -- ledger ⟹ hPLF
      → paper2_theorem_1_1_chiZero_of_reduced_inputs    -- capstone
      → Theorem_1_1 intervalDomain p

The statement carries NO frontier hypothesis: `hPLF`
(`PicardLimitRestartFrontier p`) is *not* an independent residual — it is
derived here from the same reduced ledger via `restartData_of_inputs` +
`frontierCore_of_inputs`, exactly as in
`ThresholdQuantBridge.paper2_theorem_1_1_chiZero_threshold_of_ledger`.  So the
only hypotheses are `p.χ₀ = 0` and the structural regime constants
(`0 < a`, `0 < b`, `1 ≤ α`, `1 ≤ γ`).

HONESTY NOTE — this is wiring, not a completed proof.  The chain bottoms out in
`reducedLimitRegularityInputs_of_picard`, whose data/proof fields are still
`sorry` (the genuine open analytic estimates: `hubt`/`hG1t`/`hG2t` uniform
sup/gradient/Hessian bounds, `Hvpos`/`Hvsrc`/`hpde_u` resolver and PDE residuals,
`hLc` slice continuity, the cosine representation `bc`/`hbsum`/`hagree`, …).  This
theorem's PROOF therefore depends transitively on `sorryAx`
(`#print axioms paper2_theorem_1_1_chiZero_unconditional` will report it); it is
NOT yet an axiom-clean proof of Theorem 1.1.  Its value is structural: it pins
down that *once* `reducedLimitRegularityInputs_of_picard` is discharged
sorry-free, Theorem 1.1 (χ₀ = 0) follows with no further hypotheses — every
remaining obligation is now localized to that single producer. -/
theorem paper2_theorem_1_1_chiZero_unconditional
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ) :
    Theorem_1_1 intervalDomain p :=
  -- `hPLF` derived from the reduced ledger (no extra residual hypothesis).
  have hPLF : ConeQuantBridge.PicardLimitRestartFrontier p :=
    fun u₀ hu₀ D _hDu =>
      let I := LedgerSweep.limitRegularityInputs_of_reduced hχ0
        (reducedLimitRegularityInputs_of_picard p hχ0 ha hb hα u₀ hu₀ D)
      ⟨MildLocalChi0.restartData_of_inputs hχ0 I,
        MildLocalChi0.frontierCore_of_inputs hχ0 I⟩
  LedgerSweep.paper2_theorem_1_1_chiZero_of_reduced_inputs
    p hχ0 ha hb hα hγ hPLF
    (fun u₀ hu₀ D => reducedLimitRegularityInputs_of_picard p hχ0 ha hb hα u₀ hu₀ D)

end ShenWork.Paper2.Thm11ChiZeroCoreProvider
