/-
  ShenWork/Paper2/IntervalChiNegEnvBallBanach.lean

  χ₀<0 FINAL — the concrete envelope-lattice Banach instantiation, audited against
  the χ₀=0 datum-provider mechanism.

  ## What this file ESTABLISHES (axiom-clean)

  * `envBall_coeff_mapsTo` — the LANDED coordinate `EnvBall`-invariance
    (`envBall_invariance_coeff`) repackaged as a Mathlib `Set.MapsTo` of the
    concrete three-term coefficient map on the coordinate `EnvBall` set
    `{a : ℕ → ℝ | EnvBall E_base a}`.  This is the CONCRETE chemotaxis leg landed:
    the heat + chemotaxis + logistic Duhamel image of any envelope-dominated
    coefficient datum is again envelope-dominated, UNIFORMLY in `k`.
  * `localExist_via_envBall_banach` — the faithful end wiring: from the THREE
    structural data (complete `EnvBall` metric model `α`, concrete contracting
    `Φ` `MapsTo` the `EnvBall` coordinate set, fixed-point→`cosineCoeffs (u r)`
    readout) plus the logistic source envelope, `localExist_of_envBall_fixedPoint`
    yields `LocalExist E_base Llog u G r` verbatim.  The three structural data are
    threaded as EXPLICIT inputs — never faked.

  ## HONEST ACCOUNTING — DERIVED vs CARRIED (audited against χ₀=0)

  The χ₀=0 datum provider (`chiZeroDatumProviderSupply` →
  `quantitativeLocalExistence_chiZero_datum`) builds local existence through the
  cone/tower construction `coneGradientMildSolutionData_exists_with_gate_data'`,
  NOT through a complete-metric `EnvBall` Banach fixed point.  That cone
  construction is STRUCTURALLY χ₀=0-only: at the contraction/ball steps it does
  `rw [hχ]; ring` to KILL the chemotaxis Duhamel flux term
  (`IntervalMildPicardConeData.lean`, "the flux term vanishes at χ₀ = 0"), leaving
  a two-term value-Duhamel map.  For χ₀<0 the flux leg does NOT vanish — it is
  exactly the chemotaxis term that the `EnvBall` Banach route was created to carry.
  Therefore the χ₀=0 mechanism supplies NONE of the three hypotheses of
  `localExist_of_envBall_fixedPoint`:

    (1) `IsComplete s` for a concrete `EnvBall` metric model — the repo has NO
        concrete `IsComplete`/`CompleteSpace` proof for any coefficient/function
        slice space; `conjugateMild_fixedPoint_from_complete_contraction`
        (IntervalConjugatePicardCoreDischarge) ALSO keeps `α`,`s`,`Φ` abstract and
        takes `IsComplete s` as a hypothesis ("the model-specific construction of
        the complete ball and its metric is the remaining standard fact").
    (2) a concrete contracting `Φ` `MapsTo s s` in the `EnvBall` metric — only the
        SCALAR `q(δ)<1` smallness (`chemMildLocal_smallTime_contracts`) and the
        coordinatewise invariance (DERIVED here as `envBall_coeff_mapsTo`) are
        landed; the sup-metric contraction of the genuine
        `C([0,T],C(Ω̄))`-valued `Φ` restricted to the `EnvBall` is NOT built
        (ChemMildLocal records this as the stall).
    (3) the fixed-point → `cosineCoeffs (u r)` READOUT — NO lemma anywhere
        identifies any concrete-map fixed point with the actual mild solution `u`.

  DERIVED-NEW here (axiom-clean): `envBall_coeff_mapsTo` (the concrete
  coordinatewise `MapsTo` from the landed chemotaxis leg), and
  `localExist_via_envBall_banach` (the faithful three-hypothesis wiring).

  CARRIED (the genuine residual): the three structural data above — the concrete
  complete `EnvBall` metric model, the concrete contracting `Φ`, and the
  fixed-point→`u` readout.  They are EXPLICIT hypotheses here, never faked, never a
  disguised conclusion (no u-specific Duhamel identity, no all-τ domination).
  `hlocalexist` for χ₀<0 is therefore CARRIED, not DERIVED — it does NOT match the
  χ₀=0 unconditional status, because the χ₀=0 concrete construction is unavailable
  once the chemotaxis flux is nonzero.

  No sorry/admit/native_decide/custom axiom.  Lines ≤ 100.
-/
import ShenWork.Paper2.IntervalChiNegLocalExist
import ShenWork.Paper2.IntervalChiNegPersistDischarge

open scoped Topology NNReal

noncomputable section

open Real Filter Set
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2.HSigmaScale (lam)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.IntervalFluxFactorEnvelope (sineEnv)
open ShenWork.Paper2.IntervalChiNegLocalExist (EnvBall envBall_invariance_coeff
  localExist_of_envBall_fixedPoint)
open ShenWork.Paper2.IntervalChiNegPersistDischarge (LocalExist)

namespace ShenWork.Paper2.IntervalChiNegEnvBallBanach

/-- The coordinate `EnvBall` set in the slice-coefficient space `ℕ → ℝ`. -/
def envBallSet (E_base : ℕ → ℝ) : Set (ℕ → ℝ) := {a | EnvBall E_base a}

/-- **The landed chemotaxis leg as a concrete `Set.MapsTo`.**

The three-term Duhamel coefficient map (heat leg of a supersolution datum `u0hat`,
chemotaxis Duhamel leg of a candidate-generic flux source `Qsrc`, logistic leg
`flLeg`) maps the coordinate `EnvBall` set into itself, provided the heat+logistic
legs meet the supersolution margin.  Pure repackaging of the LANDED
`envBall_invariance_coeff` (whose chemotaxis leg is discharged uniformly in `k`).
This is the concrete chemotaxis-leg invariance the χ₀=0 cone provider CANNOT supply
(it kills the flux at χ₀=0); here it lands for any sign of `χ₀`. -/
theorem envBall_coeff_mapsTo {E_base : ℕ → ℝ} (hE0 : ∀ k, 0 ≤ E_base k)
    {δ χ₀ : ℝ} (hδ : 0 ≤ δ) {u0hat : ℕ → ℝ} {Qsrc : ℕ → ℝ → ℝ} {flLeg : ℕ → ℝ}
    (hcont : ∀ k, Continuous (Qsrc k))
    (henv : ∀ k, ∀ s, |Qsrc k s| ≤ sineEnv E_base k)
    (hgap : ∀ k, |Real.exp (-(δ * lam k)) * u0hat k| + |flLeg k|
      ≤ (1 - |χ₀| * δ) * E_base k)
    (a : ℕ → ℝ) (_ha : a ∈ envBallSet E_base) :
    (fun k => Real.exp (-(δ * lam k)) * u0hat k
        + (-χ₀) * duhamelEnergyCoeff 1 Qsrc δ k + flLeg k) ∈ envBallSet E_base := by
  exact envBall_invariance_coeff hE0 hδ hcont henv hgap

/-- **Faithful end wiring — `LocalExist` from the concrete `EnvBall` Banach datum.**

Given the THREE structural data (complete `EnvBall` metric model `α`, concrete
`Φ` `MapsTo` the coordinate set `s` and `dist`-contracting with `q<1`, fixed-point
→ `cosineCoeffs (u r)` readout) and the logistic source envelope,
`localExist_of_envBall_fixedPoint` yields `LocalExist E_base Llog u G r`.  The three
data are CARRIED as explicit hypotheses: the χ₀=0 cone provider supplies none of
them once the chemotaxis flux is nonzero.  No conclusion is faked. -/
theorem localExist_via_envBall_banach
    {E_base : ℕ → ℝ} {Llog : ℝ} {u : ℝ → ℝ → ℝ} {G : ℕ → ℝ → ℝ} {r : ℝ}
    {α : Type*} [MetricSpace α] {s : Set α} {Φ : α → α} {x₀ : α} {q : ℝ}
    (hq : q < 1) (hq_nn : 0 ≤ q)
    (hcomplete : IsComplete s) (hself : MapsTo Φ s s)
    (hdist : ∀ a b : s,
      dist (hself.restrict Φ s s a) (hself.restrict Φ s s b) ≤ q * dist a b)
    (hx₀ : x₀ ∈ s) (hedist : edist x₀ (Φ x₀) ≠ ⊤)
    (hreadout : ∀ y ∈ s, Function.IsFixedPt Φ y →
      (∀ k, |cosineCoeffs (u r) k| ≤ E_base k))
    (hsrc : ∀ k τ, |G k τ| ≤ Llog * E_base k) :
    LocalExist E_base Llog u G r :=
  localExist_of_envBall_fixedPoint hq hq_nn hcomplete hself hdist hx₀ hedist
    hreadout hsrc

/-! ## AxiomAudit -/

section AxiomAudit
#print axioms envBall_coeff_mapsTo
#print axioms localExist_via_envBall_banach
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegEnvBallBanach
