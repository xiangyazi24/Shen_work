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

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)

noncomputable section

namespace ShenWork.Paper2.Thm11ChiZeroCoreProvider

/-- **The two ledger fields `hC2t` and `hpost` are mutually contradictory.**

`hC2t 0` makes the zero-extension lift of `D.u 0` globally continuous, which
forces its value at the endpoint `x = 0` to equal the (identically zero) left
limit; `hpost 0` makes that same value strictly positive.  Hence the Core is
uninhabited for every `GradientMildSolutionData D` — so the intended
`limitRegularityInputsCore_unconditional` producer cannot exist.  Nothing about
`D`, the regime, the PID, or `χ₀` is used. -/
theorem limitRegularityInputsCore_uninhabited
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (C : Thm11ChiZeroFinal.LimitRegularityInputsCore p u₀ D) : False := by
  -- `hC2t` at `σ = 0` makes the lift globally continuous.
  have hcont : Continuous (intervalDomainLift (D.u 0)) := (C.hC2t 0).continuous
  -- The lift is identically `0` to the left of `0` (those points are off `[0,1]`).
  have hEq : (intervalDomainLift (D.u 0))
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Iio 0)] (fun _ => (0 : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x < 0 := hx
    have hx' : x ∉ Set.Icc (0 : ℝ) 1 := fun hmem => absurd hmem.1 (not_le.mpr hx0)
    simp only [intervalDomainLift, dif_neg hx']
  -- Continuity ⟹ the endpoint value equals the left limit, which is `0`.
  haveI : (nhdsWithin (0 : ℝ) (Set.Iio 0)).NeBot := nhdsWithin_Iio_self_neBot 0
  have hlim : Filter.Tendsto (intervalDomainLift (D.u 0))
      (nhdsWithin (0 : ℝ) (Set.Iio 0)) (nhds (intervalDomainLift (D.u 0) 0)) :=
    hcont.continuousAt.continuousWithinAt
  have h0 : intervalDomainLift (D.u 0) 0 = 0 :=
    tendsto_nhds_unique (hlim.congr' hEq) tendsto_const_nhds
  -- `hpost` at the endpoint `x = 0` contradicts that.
  have hpos : 0 < intervalDomainLift (D.u 0) 0 :=
    C.hpost 0 0 (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
  rw [h0] at hpos
  exact lt_irrefl 0 hpos

end ShenWork.Paper2.Thm11ChiZeroCoreProvider
