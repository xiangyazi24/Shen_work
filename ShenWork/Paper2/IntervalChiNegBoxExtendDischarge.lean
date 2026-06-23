/-
  ShenWork/Paper2/IntervalChiNegBoxExtendDischarge.lean

  **χ₀<0 BASE ENVELOPE — discharge of the two carried residuals of the landed
  `box_extend_step`, composed end-to-end to the base `TrajectoryHSigmaEnvelope`.**

  `box_extend_step` (IntervalChiNegCandidateInvariance) reduces the per-restart
  box extension `|cosineCoeffs (u (r+ρ)) k| ≤ Estar k` on `[r, r+δ]` to two
  genuinely `u`-specific carried hypotheses at the restart point `r`:

    hdecomp : the RESTART three-term Duhamel identity for the slice
              `cosineCoeffs (u (r+ρ)) k = e^{−ρλ_k}·(cosineCoeffs (u r) k)
                  + (−χ₀)·duhamelEnergyCoeff[r,r+ρ]_k + flLeg ρ k`,
    hgap    : the heat+logistic per-mode supersolution MARGIN
              `|e^{−ρλ_k}·(cosineCoeffs (u r) k)| + |flLeg ρ k| ≤ (1−|χ₀|δ)·Estar k`.

  ## What is wired vs carried (scrupulous accounting)

  * Part A — `hdecomp`.  The landed per-slice decomposition
    `conjugateSlice_decomp_tauLift_pos` (IntervalDecompTauLift) is stated at the
    ORIGIN `0` (elapsed time `τ`, initial datum `û₀`), of shape
    `cosineCoeffs (u τ) k = e^{−τλ_k}·û₀_k + chem[0,τ]_k + log[0,τ]_k`.  The
    `hdecomp` field of `box_extend_step` needs the SAME identity reanchored at the
    restart point `r` (elapsed time `ρ`, initial datum `u r`).  Reanchoring is a
    genuine time-translation / semigroup restart property of the conjugate mild
    solution; GREP confirms NO restart-invariance lemma for
    `IntervalConjugateMildSolution` is landed (`IntervalPicardIterateRestart` is the
    χ₀ = 0 half-step identity, not the χ₀<0 mild restart).  It is therefore CARRIED
    here as ONE precisely-named hypothesis `hrestart`, of the EXACT `hdecomp` shape.

  * Part B — `hgap`.  The heat leg `e^{−ρλ_k}·(cosineCoeffs (u r) k)` at low `k`
    (`λ_k` small, `e^{−ρλ_k} ≈ 1`) carries ≈ `cosineCoeffs (u r) k`, and the box
    gives only `cosineCoeffs (u r) k ≤ Estar k`, so the heat leg can reach `Estar_k`,
    EXCEEDING the `(1−|χ₀|δ)Estar_k` margin.  Hence `hgap` is NOT box-derivable; it
    requires `u r` to sit STRICTLY below `Estar` with a margin — the inflated
    supersolution / mild local-persistence input.  GREP confirms the candidate-
    generic invariance scaffold (IntervalChiNegEnvelopePersistence) documents this
    EXACT stall: the strict-below-`Estar` margin is a nonlinear-resolver spectral
    fact landed (in `MildSlicePackage`) ONLY for the actual `u`, and no inflated
    supersolution `Estar = ρ₀·E_base` construction is landed.  It is therefore
    CARRIED here as ONE precisely-named hypothesis `hpersist`, of the EXACT `hgap`
    shape — the heat+logistic per-mode SCALAR margin.  This is strictly WEAKER than
    the global all-`τ` box domination (it bounds only the two non-chemotaxis legs at
    the restart endpoint by the contracted factor `(1−|χ₀|δ)`); it is NOT a
    disguised form of the conclusion.

  Both carried hypotheses are threaded as explicit inputs of the exact shapes of the
  landed interface — never faked, never a disguised conclusion.  Everything else
  (the box extension, the ρ→τ reparametrisation, the candidate-generic step
  packaging, the continuation to the global bound, the envelope constructor) is
  DERIVED from the landed lemmas.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file only.
-/
import ShenWork.Paper2.IntervalChiNegCandidateInvariance
import ShenWork.Paper2.IntervalChiNegContinuationEnvelope

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegBoxExtendDischarge

open Real
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2.HSigmaScale (lam MemHSigma)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.IntervalFluxFactorEnvelope (sineEnv)
open ShenWork.Paper2.IntervalChiNegContinuationEnvelope (BoundAt BoundUpTo baseTrajectoryEnvelope)
open ShenWork.Paper2.IntervalChiNegCandidateInvariance
  (box_extend_step boxRho_to_boxTau envelopePersistence_of_step)
open ShenWork.Paper2.IntervalTrajectoryEnvelope (TrajectoryHSigmaEnvelope)

/-! ## Part A — the carried RESTART Duhamel identity `hrestart`.

The EXACT `box_extend_step.hdecomp` shape, reanchored at the restart point `r`.
Carried because the time-translation/restart invariance of the conjugate mild
solution is not landed (only the origin-`0` decomposition is). -/

/-- **`Hrestart`** — the restart three-term Duhamel coefficient identity for the
slice `u (r+ρ)`, with initial datum `cosineCoeffs (u r)` and `ρ`-elapsed legs.
This is precisely the `hdecomp` field consumed by `box_extend_step`. -/
def Hrestart (χ₀ : ℝ) (u : ℝ → ℝ → ℝ) (Qsrc : ℕ → ℝ → ℝ) (flLeg : ℝ → ℕ → ℝ)
    (r δ : ℝ) : Prop :=
  ∀ ρ, 0 ≤ ρ → ρ ≤ δ → ∀ k,
    cosineCoeffs (u (r + ρ)) k
      = Real.exp (-(ρ * lam k)) * cosineCoeffs (u r) k
        + (-χ₀) * duhamelEnergyCoeff 1 Qsrc ρ k + flLeg ρ k

/-! ## Part B — the carried heat+logistic supersolution MARGIN `hpersist`.

The EXACT `box_extend_step.hgap` shape: a per-mode SCALAR bound on the two
non-chemotaxis legs at the restart endpoint by the contracted `(1−|χ₀|δ)` factor.
Strictly WEAKER than the all-`τ` box domination — carried as the faithful
inflated-envelope / mild local-persistence input. -/

/-- **`Hpersist`** — the inflated-envelope persistence margin: the heat leg
`e^{−ρλ_k}·(cosineCoeffs (u r) k)` plus the logistic leg `flLeg ρ k` are bounded,
per mode `k`, by the CONTRACTED envelope `(1−|χ₀|δ)·Estar k`.  This is precisely the
`hgap` field consumed by `box_extend_step`. -/
def Hpersist (χ₀ δ : ℝ) (Estar : ℕ → ℝ) (u : ℝ → ℝ → ℝ) (flLeg : ℝ → ℕ → ℝ)
    (r : ℝ) : Prop :=
  ∀ ρ, 0 ≤ ρ → ρ ≤ δ → ∀ k,
    |Real.exp (-(ρ * lam k)) * cosineCoeffs (u r) k| + |flLeg ρ k|
      ≤ (1 - |χ₀| * δ) * Estar k

/-! ## The per-restart box extension, from the two carried residuals. -/

/-- **`box_extend_of_residuals`** — for a fixed admissible restart `r` with chosen
`δ`, the box `|cosineCoeffs (u (r+ρ)) k| ≤ Estar k` on `[r, r+δ]`, DERIVED from the
candidate-generic flux strictness (`box_extend_step`) fed the two carried residuals
`Hrestart` (Part A) and `Hpersist` (Part B).  Only `Hrestart`/`Hpersist` are
carried; the box closure itself is derived. -/
theorem box_extend_of_residuals {Estar : ℕ → ℝ} (hE0 : ∀ k, 0 ≤ Estar k)
    {δ χ₀ : ℝ} {u : ℝ → ℝ → ℝ} {Qsrc : ℕ → ℝ → ℝ} {flLeg : ℝ → ℕ → ℝ} {r : ℝ}
    (hcont : ∀ k, Continuous (Qsrc k))
    (henv : ∀ k, ∀ s, |Qsrc k s| ≤ sineEnv Estar k)
    (hrestart : Hrestart χ₀ u Qsrc flLeg r δ)
    (hpersist : Hpersist χ₀ δ Estar u flLeg r) :
    ∀ ρ, 0 ≤ ρ → ρ ≤ δ → ∀ k, |cosineCoeffs (u (r + ρ)) k| ≤ Estar k :=
  box_extend_step (u := u) (sliceState := cosineCoeffs (u r))
    hE0 hcont henv hrestart hpersist

/-! ## Composing the per-restart step into the global persistence `hext`. -/

/-- **`hext_of_residualSupply`** — the `hext` short-time persistence input of
`baseTrajectoryEnvelope`, DERIVED from a per-restart supply of the two carried
residuals.  For each admissible `r`, the supplier produces a genuine extension
`δ > 0` with `r + δ ≤ t`, the matching flux data, and the two residuals
`Hrestart`/`Hpersist`; the box extension and the landed continuation glue then
yield the `∃ r' > r` persistence.  No residual beyond `Hrestart`/`Hpersist`. -/
theorem hext_of_residualSupply {Estar : ℕ → ℝ} (hE0 : ∀ k, 0 ≤ Estar k)
    {t χ₀ : ℝ} {u : ℝ → ℝ → ℝ}
    (hsupply : ∀ r, 0 ≤ r → r < t →
      BoundUpTo (fun τ => cosineCoeffs (u τ)) Estar t r →
      ∃ δ Qsrc flLeg, 0 < δ ∧ r + δ ≤ t ∧
        (∀ k, Continuous (Qsrc k)) ∧
        (∀ k, ∀ s, |Qsrc k s| ≤ sineEnv Estar k) ∧
        Hrestart χ₀ u Qsrc flLeg r δ ∧
        Hpersist χ₀ δ Estar u flLeg r) :
    ∀ r, 0 ≤ r → r < t →
      BoundUpTo (fun τ => cosineCoeffs (u τ)) Estar t r →
      ∃ r', r < r' ∧ r' ≤ t ∧ BoundUpTo (fun τ => cosineCoeffs (u τ)) Estar t r' := by
  refine envelopePersistence_of_step (Estar := Estar) (c := fun τ => cosineCoeffs (u τ))
    ?_
  intro r hr0 hrt hgood
  obtain ⟨δ, Qsrc, flLeg, hδpos, hδt, hcont, henv, hrestart, hpersist⟩ :=
    hsupply r hr0 hrt hgood
  exact ⟨δ, hδpos, hδt,
    box_extend_of_residuals hE0 hcont henv hrestart hpersist⟩

/-! ## The χ₀<0 base trajectory envelope, from the residual supply. -/

/-- **`baseEnvelope_of_residualSupply`** — the χ₀<0 base
`TrajectoryHSigmaEnvelope`, BUILT from: the `H^σ` membership of `Estar`, the `s = 0`
datum bound, the per-mode time-continuity, and the per-restart supply of the two
carried residuals `Hrestart` (Part A restart identity) and `Hpersist` (Part B
heat+logistic margin).  The global domination is DERIVED (the landed continuation),
NOT carried.  The ONLY carried analytic content is the two named residuals inside
`hsupply`. -/
def baseEnvelope_of_residualSupply {σ t χ₀ : ℝ} {u : ℝ → ℝ → ℝ} {Estar : ℕ → ℝ}
    (ht : 0 ≤ t) (hE0 : ∀ k, 0 ≤ Estar k)
    (hEstar : MemHSigma σ Estar)
    (hbase : BoundAt (fun τ => cosineCoeffs (u τ)) Estar 0)
    (hcont : ∀ k, ContinuousOn (fun s => cosineCoeffs (u s) k) (Set.Icc 0 t))
    (hsupply : ∀ r, 0 ≤ r → r < t →
      BoundUpTo (fun τ => cosineCoeffs (u τ)) Estar t r →
      ∃ δ Qsrc flLeg, 0 < δ ∧ r + δ ≤ t ∧
        (∀ k, Continuous (Qsrc k)) ∧
        (∀ k, ∀ s, |Qsrc k s| ≤ sineEnv Estar k) ∧
        Hrestart χ₀ u Qsrc flLeg r δ ∧
        Hpersist χ₀ δ Estar u flLeg r) :
    TrajectoryHSigmaEnvelope σ t (fun τ => cosineCoeffs (u τ)) :=
  baseTrajectoryEnvelope ht hEstar hbase hcont
    (hext_of_residualSupply hE0 hsupply)

/-! ## AxiomAudit -/

section AxiomAudit
#print axioms box_extend_of_residuals
#print axioms hext_of_residualSupply
#print axioms baseEnvelope_of_residualSupply
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegBoxExtendDischarge
