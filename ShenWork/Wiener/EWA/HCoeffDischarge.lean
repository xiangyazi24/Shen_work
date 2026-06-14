import ShenWork.Wiener.EWA.EvenRealClosure
import ShenWork.Wiener.EWA.WLEvenReal
import ShenWork.Wiener.EWA.NonCircularCoeffBridge
import ShenWork.Wiener.EWA.SourceEnvelope
import ShenWork.Wiener.EWA.ChemDivSourceAssembly

/-!
# EWA brick — the `h_coeff` DISCHARGE for the Phase C top-level theorem

This file discharges the value-envelope domination leg `h_coeff` of the assembled
`coupledChemDivSource_timeC1On_of_EWA` to cleaner hypotheses, by chaining four
committed bricks:

1. **Parity closure** (`chemDivEWA_evenReal`, made UNCONDITIONAL via the committed
   Wiener–Lévy parity `FnegEWA_evenReal_Hyp_proved`): `chemDivEWA μ ν γ hμ p U` is
   even-real at every time `τ` when `U` is even-real.
2. **Non-circular coeff bridge** (`ewaCosCoeffAt_eq_cosineCoeffs_of_even_real`):
   for an even-real EWA element whose synthesis realizes a real function `f` on the
   open interior `(0,1)`, the `±`-mode extractor equals `cosineCoeffs f`.
3. **Coefficient/lift def match**:
   `coupledChemDivSourceCoeffs p u s n = cosineCoeffs (coupledChemDivSourceLift p u s) n`
   holds *definitionally* (`coupledChemDivSourceCoeffs` is literally
   `fun s n => cosineCoeffs (coupledChemDivSourceLift p u s) n`).
4. **Source envelope** (`ewaCosCoeffAt_abs_le_envelope`): the `±`-mode extractor is
   pointwise dominated by `sourceEnvelope (chemDivEWA …)`.

The eval factor-realizations of `chemDivEWA` as the real chemotaxis divergence are
taken as the hypothesis `h_eval` (the `SourceEvalBridge` content, discharged later
by the Q2 even-embedding construction); `U` even-real is the hypothesis `hU`.

NO `sorry`, `axiom`, `native_decide`, or `admit`.
-/

open scoped BigOperators
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledChemDivSourceLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDomain (intervalDomainPoint)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-- **The `h_coeff` discharge.**  The chemotaxis-divergence source coefficient
`coupledChemDivSourceCoeffs p u s n` is dominated in absolute value by the EWA
`sourceEnvelope` of `chemDivEWA μ ν γ hμ p U`, for an even-real `U` whose
`chemDivEWA` synthesis realizes the real lift `coupledChemDivSourceLift p u s` on
the interior `(0,1)`.

This drops the assembled top-level theorem's `h_coeff` (the value-envelope
domination leg) to the cleaner hypotheses `hU` (`U` even-real) and `h_eval` (the
eval realization), both discharged later by the Q2 even-embedding construction. -/
theorem chemDiv_coeff_bound_of_EWA
    {μ ν γ : ℝ} (hμ : 0 < μ) (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (U : EWA T 1)
    (hU : EvenRealEWA U)
    (h_eval : ∀ (τ : TimeDom T) (x : ℝ), x ∈ Set.Ioo (0 : ℝ) 1 →
        evalST τ (x : WA.Circ) (chemDivEWA μ ν γ hμ p U)
          = ((coupledChemDivSourceLift p u τ.1 x : ℝ) : ℂ))
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) T) (n : ℕ) :
    |coupledChemDivSourceCoeffs p u s n| ≤ sourceEnvelope (chemDivEWA μ ν γ hμ p U) n := by
  -- Step 1: `chemDivEWA U` is even-real at every time (parity closure made
  -- unconditional via the committed Wiener–Lévy parity).
  have hdiv : EvenRealEWA (chemDivEWA μ ν γ hμ p U) :=
    chemDivEWA_evenReal FnegEWA_evenReal_Hyp_proved hμ p hU
  -- Step 2: pick the time slice `τ` with `τ.1 = s` from `hs : s ∈ Icc 0 T`.
  let τ : TimeDom T := ⟨s, hs⟩
  -- Step 3: the non-circular coeff bridge identifies the `±`-mode extractor with
  -- the committed Neumann cosine coefficient of the real lift at this slice.
  have hbridge : ewaCosCoeffAt (chemDivEWA μ ν γ hμ p U) τ n
      = cosineCoeffs (coupledChemDivSourceLift p u s) n :=
    ewaCosCoeffAt_eq_cosineCoeffs_of_even_real (F := chemDivEWA μ ν γ hμ p U)
      (f := coupledChemDivSourceLift p u s) τ
      (fun m => hdiv.even τ m) (fun m => hdiv.real τ m)
      (fun x hx => h_eval τ x hx) n
  -- Step 4: `coupledChemDivSourceCoeffs p u s n = cosineCoeffs (lift) n` by def,
  -- so the extractor equals the source coefficient; dominate by the envelope.
  have hcoeff : coupledChemDivSourceCoeffs p u s n
      = ewaCosCoeffAt (chemDivEWA μ ν γ hμ p U) τ n := by
    rw [coupledChemDivSourceCoeffs, hbridge]
  rw [hcoeff]
  exact ewaCosCoeffAt_abs_le_envelope (chemDivEWA μ ν γ hμ p U) τ n

end ShenWork.EWA

#print axioms ShenWork.EWA.chemDiv_coeff_bound_of_EWA
