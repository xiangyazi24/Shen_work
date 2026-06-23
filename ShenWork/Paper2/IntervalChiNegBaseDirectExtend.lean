/-
  ShenWork/Paper2/IntervalChiNegBaseDirectExtend.lean

  **χ₀<0 (C1) closer — the τ-uniform base envelope via DIRECT box-extension.**

  The landed `baseEnvelope_of_residualSupply` (IntervalChiNegBoxExtendDischarge)
  builds the base `TrajectoryHSigmaEnvelope σ t (cosineCoeffs∘u)` by the
  CONTINUATION / box-extension closure (per-mode 1D continuity, NO BCF / NO joint
  continuity / NO τ=0 — the BCF base is τ=0-broken/vacuous).  BUT its per-restart
  step `box_extend_step` bounds the chemotaxis leg via `chemDuhamelContribution_le`
  (the BARE-sineEnv `henv : |Qsrc k s| ≤ sineEnv Estar k`), which forces
  `Estar ≥ gwInflatedBase ∈ H^{σ+1}` (the +1-derivative loss).

  This file re-derives the SAME box closure with the chemotaxis leg deflated by the
  DIRECT Duhamel-output envelope (`chemE.env k = coreEnv ∈ H^σ`, from the genv
  source `M ∈ H^σ` via `chemDuhamel_direct` — NO bare sineEnv, NO `+1` loss):

    * `box_extend_step_direct` — same conclusion as `box_extend_step`
      (`∀ ρ≤δ ∀k, |cosineCoeffs (u (r+ρ)) k| ≤ Estar k`), but the chem leg is
      bounded per-mode by `|χ₀|·chemEenv k` (the DIRECT deflated Duhamel output),
      and the heat+log margin `Hpersist_direct` carries
      `|heat| + |log| ≤ Estar k − |χ₀|·chemEenv k`.  The chem domination is
      supplied DIRECTLY as `hchemD : |duhamelEnergyCoeff 1 Qsrc ρ k| ≤ chemEenv k`
      (the `chemDuhamel_direct.hdom` restriction), NEVER via `chemDuhamelContribution_le`.
    * `box_extend_of_residuals_direct` / `hext_of_residualSupply_direct` — mirror
      the landed `:112` / `:130` chain, swapping the bare-sineEnv `henv` for the
      genv source `hchemD`.
    * `baseEnvelope_of_residualSupply_direct` — mirror `:159`: the deflated direct
      supersolution `Estar` (`memHSigma_deflate`), `hbase` (s=0 TRIVIAL), per-mode
      continuity, and the direct `hsupply` ⟹ the base
      `TrajectoryHSigmaEnvelope σ t (cosineCoeffs∘u)`.

  ## Accounting (two-way audit)
  DERIVED: the box closure (`baseTrajectoryEnvelope` + the continuation glue) with
  the chemotaxis leg routed through the DIRECT deflated envelope — NOT bare sineEnv.
  CARRIED (the genuine `u`-specific residuals, the SAME the landed chain carries,
  threaded as explicit hyps, never faked): the restart Duhamel identity
  `Hrestart`, the direct chem domination `Hchem_direct`, and the heat+log margin
  `Hpersist_direct`.  These come from the actual conjugate mild Duhamel identity
  (`conjugatePicardLimit_is_mildSolution`) + `genv_of_trajectoryEnvelope_uncond`
  (the genv source `M`) + `chemDuhamel_direct` (the deflation).

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file only.  Lines ≤ 100.
-/
import ShenWork.Paper2.IntervalChiNegBoxExtendDischarge
import ShenWork.Paper2.IntervalChiNegDirectSupersolution

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegBaseDirectExtend

open Real
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2.HSigmaScale (lam MemHSigma)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.IntervalChiNegContinuationEnvelope
  (BoundAt BoundUpTo baseTrajectoryEnvelope)
open ShenWork.Paper2.IntervalChiNegBoxExtendDischarge (Hrestart)
open ShenWork.Paper2.IntervalChiNegCandidateInvariance
  (boxRho_to_boxTau envelopePersistence_of_step)
open ShenWork.Paper2.IntervalTrajectoryEnvelope (TrajectoryHSigmaEnvelope)

/-! ## Part B' — the DIRECT chem domination `Hchem_direct` and heat+log margin
`Hpersist_direct`.  Both replace the bare-sineEnv `henv`/`Hpersist` of the landed
chain: the chem leg is dominated by the DEFLATED Duhamel output `chemEenv` (from
`chemDuhamel_direct`), so the margin only needs `Estar − |χ₀|·chemEenv` on the
remaining two legs. -/

/-- **`Hchem_direct`** — the DIRECT per-mode chemotaxis-Duhamel domination: the
Duhamel OUTPUT coefficient of the actual (genv-inflated) flux is bounded by the
DEFLATED envelope `chemEenv k` (the `chemDuhamel_direct.hdom` restriction to the
restart slice `[0,δ]`), NOT by the bare-sineEnv `sineEnv Estar k`. -/
def Hchem_direct (Qsrc : ℕ → ℝ → ℝ) (chemEenv : ℕ → ℝ) (δ : ℝ) : Prop :=
  ∀ ρ, 0 ≤ ρ → ρ ≤ δ → ∀ k, |duhamelEnergyCoeff 1 Qsrc ρ k| ≤ chemEenv k

/-- **`Hpersist_direct`** — the heat+logistic margin against the DEFLATED chem
envelope: the heat leg plus the logistic leg are bounded, per mode, by
`Estar k − |χ₀|·chemEenv k`.  (Strictly weaker than the all-τ box domination; the
chem leg's own `|χ₀|·chemEenv k` slot is reserved.) -/
def Hpersist_direct (χ₀ : ℝ) (Estar chemEenv : ℕ → ℝ) (u : ℝ → ℝ → ℝ)
    (flLeg : ℝ → ℕ → ℝ) (r δ : ℝ) : Prop :=
  ∀ ρ, 0 ≤ ρ → ρ ≤ δ → ∀ k,
    |Real.exp (-(ρ * lam k)) * cosineCoeffs (u r) k| + |flLeg ρ k|
      ≤ Estar k - |χ₀| * chemEenv k

/-! ## The DIRECT box-extension step. -/

/-- **`box_extend_step_direct`** — the box-invariance extension with the chemotaxis
leg deflated.  Same conclusion as the landed `box_extend_step`
(`|cosineCoeffs (u (r+ρ)) k| ≤ Estar k` on `[0,δ]`), but the chem leg is bounded
DIRECTLY by `|χ₀|·chemEenv k` via the supplied `chemDuhamel_direct` domination
`hchemD`, NOT through `chemDuhamelContribution_le` (the bare sineEnv).  The
heat+log margin reserves exactly the chem slot (`Hpersist_direct`). -/
theorem box_extend_step_direct {Estar chemEenv : ℕ → ℝ}
    {δ χ₀ : ℝ} {u : ℝ → ℝ → ℝ} {Qsrc : ℕ → ℝ → ℝ} {flLeg : ℝ → ℕ → ℝ} {r : ℝ}
    (hdecomp : ∀ ρ, 0 ≤ ρ → ρ ≤ δ → ∀ k,
      cosineCoeffs (u (r + ρ)) k
        = Real.exp (-(ρ * lam k)) * cosineCoeffs (u r) k
          + (-χ₀) * duhamelEnergyCoeff 1 Qsrc ρ k + flLeg ρ k)
    (hchemD : Hchem_direct Qsrc chemEenv δ)
    (hgap : Hpersist_direct χ₀ Estar chemEenv u flLeg r δ) :
    ∀ ρ, 0 ≤ ρ → ρ ≤ δ → ∀ k, |cosineCoeffs (u (r + ρ)) k| ≤ Estar k := by
  intro ρ hρ0 hρδ k
  rw [hdecomp ρ hρ0 hρδ k]
  have htri : |Real.exp (-(ρ * lam k)) * cosineCoeffs (u r) k
        + (-χ₀) * duhamelEnergyCoeff 1 Qsrc ρ k + flLeg ρ k|
      ≤ |Real.exp (-(ρ * lam k)) * cosineCoeffs (u r) k|
        + |(-χ₀) * duhamelEnergyCoeff 1 Qsrc ρ k| + |flLeg ρ k| := by
    refine le_trans (abs_add_le _ _) ?_
    gcongr
    exact abs_add_le _ _
  refine le_trans htri ?_
  have hchem : |(-χ₀) * duhamelEnergyCoeff 1 Qsrc ρ k| ≤ |χ₀| * chemEenv k := by
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hchemD ρ hρ0 hρδ k) (abs_nonneg χ₀)
  have hg := hgap ρ hρ0 hρδ k
  have hcomb : |Real.exp (-(ρ * lam k)) * cosineCoeffs (u r) k|
        + |(-χ₀) * duhamelEnergyCoeff 1 Qsrc ρ k| + |flLeg ρ k|
      ≤ (Estar k - |χ₀| * chemEenv k) + |χ₀| * chemEenv k := by
    have hsum : |Real.exp (-(ρ * lam k)) * cosineCoeffs (u r) k| + |flLeg ρ k|
          + |(-χ₀) * duhamelEnergyCoeff 1 Qsrc ρ k|
        ≤ (Estar k - |χ₀| * chemEenv k) + |χ₀| * chemEenv k := add_le_add hg hchem
    linarith
  refine le_trans hcomb ?_
  linarith

/-! ## The per-restart box extension, from the direct residuals. -/

/-- **`box_extend_of_residuals_direct`** — the box on `[r, r+δ]` DERIVED from the
restart identity `Hrestart`, the DIRECT chem domination `Hchem_direct`, and the
direct heat+log margin `Hpersist_direct`.  Mirrors the landed
`box_extend_of_residuals`, swapping the bare-sineEnv `henv`/`Hpersist` for the
genv-source `hchemD`/`Hpersist_direct`. -/
theorem box_extend_of_residuals_direct {Estar chemEenv : ℕ → ℝ}
    {δ χ₀ : ℝ} {u : ℝ → ℝ → ℝ} {Qsrc : ℕ → ℝ → ℝ} {flLeg : ℝ → ℕ → ℝ} {r : ℝ}
    (hrestart : Hrestart χ₀ u Qsrc flLeg r δ)
    (hchemD : Hchem_direct Qsrc chemEenv δ)
    (hgap : Hpersist_direct χ₀ Estar chemEenv u flLeg r δ) :
    ∀ ρ, 0 ≤ ρ → ρ ≤ δ → ∀ k, |cosineCoeffs (u (r + ρ)) k| ≤ Estar k :=
  box_extend_step_direct hrestart hchemD hgap

/-! ## Composing the per-restart step into the global persistence `hext`. -/

/-- **`hext_of_residualSupply_direct`** — the `hext` short-time persistence input of
`baseTrajectoryEnvelope`, DERIVED from a per-restart supply of the DIRECT residuals
(`Hrestart`, `Hchem_direct`, `Hpersist_direct`).  The box extension and the landed
continuation glue then yield the `∃ r' > r` persistence.  No residual beyond the
three direct ones; the chem leg is the deflated Duhamel output, never bare sineEnv. -/
theorem hext_of_residualSupply_direct {Estar chemEenv : ℕ → ℝ}
    {t χ₀ : ℝ} {u : ℝ → ℝ → ℝ}
    (hsupply : ∀ r, 0 ≤ r → r < t →
      BoundUpTo (fun τ => cosineCoeffs (u τ)) Estar t r →
      ∃ δ Qsrc flLeg, 0 < δ ∧ r + δ ≤ t ∧
        Hrestart χ₀ u Qsrc flLeg r δ ∧
        Hchem_direct Qsrc chemEenv δ ∧
        Hpersist_direct χ₀ Estar chemEenv u flLeg r δ) :
    ∀ r, 0 ≤ r → r < t →
      BoundUpTo (fun τ => cosineCoeffs (u τ)) Estar t r →
      ∃ r', r < r' ∧ r' ≤ t ∧ BoundUpTo (fun τ => cosineCoeffs (u τ)) Estar t r' := by
  refine envelopePersistence_of_step (Estar := Estar)
    (c := fun τ => cosineCoeffs (u τ)) ?_
  intro r hr0 hrt hgood
  obtain ⟨δ, Qsrc, flLeg, hδpos, hδt, hrestart, hchemD, hgap⟩ :=
    hsupply r hr0 hrt hgood
  exact ⟨δ, hδpos, hδt,
    box_extend_of_residuals_direct hrestart hchemD hgap⟩

/-! ## The χ₀<0 base trajectory envelope, from the DIRECT residual supply. -/

/-- **`baseEnvelope_of_residualSupply_direct`** — the χ₀<0 base
`TrajectoryHSigmaEnvelope`, BUILT from: the `H^σ` membership of the DEFLATED direct
supersolution `Estar` (via `memHSigma_deflate` / `chemDuhamel_direct`), the `s = 0`
datum bound (TRIVIAL: `conjugatePicardLimit 0 = 0`), the per-mode time-continuity,
and the per-restart supply of the THREE direct residuals.  The global domination is
DERIVED (the landed continuation); the chemotaxis leg is the DIRECT deflated Duhamel
output, NEVER the bare sineEnv.  No BCF / joint continuity / τ=0 anywhere. -/
def baseEnvelope_of_residualSupply_direct {σ t χ₀ : ℝ} {u : ℝ → ℝ → ℝ}
    {Estar chemEenv : ℕ → ℝ}
    (ht : 0 ≤ t) (hEstar : MemHSigma σ Estar)
    (hbase : BoundAt (fun τ => cosineCoeffs (u τ)) Estar 0)
    (hcont : ∀ k, ContinuousOn (fun s => cosineCoeffs (u s) k) (Set.Icc 0 t))
    (hsupply : ∀ r, 0 ≤ r → r < t →
      BoundUpTo (fun τ => cosineCoeffs (u τ)) Estar t r →
      ∃ δ Qsrc flLeg, 0 < δ ∧ r + δ ≤ t ∧
        Hrestart χ₀ u Qsrc flLeg r δ ∧
        Hchem_direct Qsrc chemEenv δ ∧
        Hpersist_direct χ₀ Estar chemEenv u flLeg r δ) :
    TrajectoryHSigmaEnvelope σ t (fun τ => cosineCoeffs (u τ)) :=
  baseTrajectoryEnvelope ht hEstar hbase hcont
    (hext_of_residualSupply_direct hsupply)

/-! ## AxiomAudit -/

section AxiomAudit
#print axioms box_extend_step_direct
#print axioms box_extend_of_residuals_direct
#print axioms hext_of_residualSupply_direct
#print axioms baseEnvelope_of_residualSupply_direct
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegBaseDirectExtend
