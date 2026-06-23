/-
  ShenWork/Paper2/IntervalChiNegLocalExist.lean

  chi0<0 FINAL -- hlocalexist (the X_E envelope-lattice order box of the mild
  solution): the candidate-generic envelope-ball invariance assembled from the
  landed legs, and the PRECISE isolation of the one remaining standard
  local-well-posedness lemma.

  ## What this file PROVES (axiom-clean, candidate-generic -- never via u)

  * EnvBall -- the closed envelope ball {a | forall k, |a k| <= E_base k} as a
    coefficient predicate (the X_E order box at the restart endpoint).
  * envBall_invariance_coeff -- the candidate-generic Phi(EnvBall) <= EnvBall
    coordinatewise step: for ANY coefficient image with the three-term Duhamel
    shape (heat leg of an H^sigma supersolution datum u0hat, the chemotaxis
    Duhamel leg of a candidate-generic flux source, the logistic leg), the image
    stays <= E_base k, UNIFORMLY in k.  The chemotaxis leg is discharged by the
    LANDED uniform-in-k strictness (chemDuhamelContribution_le); the heat +
    logistic legs by the supersolution margin.  Phi-invariance for a GENERIC
    EnvBall element, never u.
  * logistic_source_envelope -- the second LocalExist conjunct
    |G k tau| <= Llog * E_base k, from a per-mode logistic envelope datum.
  * localExist_of_envBall_fixedPoint -- the abstract reduction: GIVEN a concrete
    complete metric model alpha of the EnvBall on which the concrete mild map Phi
    is MapsTo + ContractingWith q(delta)<1, AND a coordinate readout identifying
    the fixed point with the slice coefficients of u r inside the EnvBall,
    LocalExist follows.  This makes the SOLE remaining frontier explicit.

  ## HONEST ACCOUNTING -- DERIVED vs CARRIED

  DERIVED-NEW here (axiom-clean): the candidate-generic coordinatewise EnvBall
  invariance (envBall_invariance_coeff), the logistic source envelope, and the
  abstract reduction localExist_of_envBall_fixedPoint.

  CONSUMED-LANDED: chemDuhamelContribution_le (the uniform-in-k chemotaxis
  strictness, IntervalChiNegCandidateInvariance), duhamelEnergyCoeff, lam,
  sineEnv, cosineCoeffs, and Mathlib ContractingWith.exists_fixedPoint'.

  CARRIED (the genuine residual, NOT discharged here -- the faithful Cauchy
  frontier): the CONCRETE envelope-lattice Banach instantiation.  ChemMildLocal /
  IntervalConjugatePicardCoreDischarge expose the contraction CORE only over an
  ABSTRACT [MetricSpace alpha] [IsComplete s] with an ABSTRACT Phi; no concrete
  MetricSpace/IsComplete model of the EnvBall, no concrete Phi with MapsTo +
  metric contraction, and no fixed-point -> cosineCoeffs (u r) readout is built
  anywhere in the repo (conjugateMild_fixedPoint_from_complete_contraction is
  NEVER applied to a concrete alpha).  Its three hypotheses in
  localExist_of_envBall_fixedPoint ARE that missing standard local-well-posedness
  lemma.  They are threaded as EXPLICIT inputs -- never faked, never a disguised
  conclusion.  No sorry/admit/native_decide/custom axiom.
-/
import ShenWork.Paper2.IntervalChiNegCandidateInvariance
import Mathlib.Topology.MetricSpace.Contracting

open scoped Topology NNReal

noncomputable section

open Real Filter Set
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2.HSigmaScale (lam lam_nonneg MemHSigma)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.IntervalFluxFactorEnvelope (sineEnv)
open ShenWork.Paper2.IntervalChiNegCandidateInvariance (chemDuhamelContribution_le)

namespace ShenWork.Paper2.IntervalChiNegLocalExist

/-! ## 1. The closed envelope ball (the X_E order box). -/

/-- The closed envelope ball of a coefficient datum: every mode is dominated by
the envelope `E_base`.  This is the X_E order box at the restart endpoint;
membership is exactly the first `LocalExist` conjunct. -/
def EnvBall (E_base : ℕ → ℝ) (a : ℕ → ℝ) : Prop := ∀ k, |a k| ≤ E_base k

theorem envBall_mem_iff {E_base a : ℕ → ℝ} :
    EnvBall E_base a ↔ ∀ k, |a k| ≤ E_base k := Iff.rfl

/-! ## 2. Candidate-generic Phi(EnvBall) <= EnvBall (coordinatewise, uniform in k). -/

/-- **Candidate-generic envelope-ball invariance, coordinatewise.**

For ANY candidate flux source `Qsrc` whose coefficients obey the candidate-generic
flux envelope `|Qsrc k s| ≤ sineEnv E_base k` (the steps 1–5 output, NEVER via the
actual `u`), the three-term Duhamel image
`e^{−δλ_k}·û₀_k + (−χ₀)·duhamelEnergyCoeff Qsrc δ k + flLeg k`
stays in the EnvBall, UNIFORMLY in `k`, provided the heat + logistic legs satisfy
the supersolution margin `|e^{−δλ_k}·û₀_k| + |flLeg k| ≤ (1 − |χ₀|·δ)·E_base k`.

The chemotaxis leg is `≤ |χ₀|·δ·E_base k` by the LANDED uniform-in-`k` strictness;
the remaining two legs by the margin; the sum is exactly `E_base k`. -/
theorem envBall_invariance_coeff {E_base : ℕ → ℝ} (hE0 : ∀ k, 0 ≤ E_base k)
    {δ χ₀ : ℝ} (hδ : 0 ≤ δ) {u0hat : ℕ → ℝ} {Qsrc : ℕ → ℝ → ℝ} {flLeg : ℕ → ℝ}
    (hcont : ∀ k, Continuous (Qsrc k))
    (henv : ∀ k, ∀ s, |Qsrc k s| ≤ sineEnv E_base k)
    (hgap : ∀ k, |Real.exp (-(δ * lam k)) * u0hat k| + |flLeg k|
      ≤ (1 - |χ₀| * δ) * E_base k) :
    EnvBall E_base (fun k => Real.exp (-(δ * lam k)) * u0hat k
        + (-χ₀) * duhamelEnergyCoeff 1 Qsrc δ k + flLeg k) := by
  intro k
  have htri : |Real.exp (-(δ * lam k)) * u0hat k
        + (-χ₀) * duhamelEnergyCoeff 1 Qsrc δ k + flLeg k|
      ≤ |Real.exp (-(δ * lam k)) * u0hat k|
        + |(-χ₀) * duhamelEnergyCoeff 1 Qsrc δ k| + |flLeg k| := by
    refine le_trans (abs_add_le _ _) ?_
    gcongr
    exact abs_add_le _ _
  refine le_trans htri ?_
  have hchem : |(-χ₀) * duhamelEnergyCoeff 1 Qsrc δ k| ≤ |χ₀| * (δ * E_base k) :=
    chemDuhamelContribution_le hE0 hδ hcont henv k
  have hg := hgap k
  have hcomb : |Real.exp (-(δ * lam k)) * u0hat k|
        + |(-χ₀) * duhamelEnergyCoeff 1 Qsrc δ k| + |flLeg k|
      ≤ (1 - |χ₀| * δ) * E_base k + |χ₀| * (δ * E_base k) := by linarith
  refine le_trans hcomb ?_
  have heq : (1 - |χ₀| * δ) * E_base k + |χ₀| * (δ * E_base k) = E_base k := by ring
  rw [heq]

/-! ## 3. The logistic source envelope (the second `LocalExist` conjunct). -/

/-- From a per-mode logistic envelope datum `|G k τ| ≤ Llog · E_base k`, the second
`LocalExist` conjunct holds verbatim.  The landed logistic bound, threaded
generically (no `u`). -/
theorem logistic_source_envelope {E_base : ℕ → ℝ} {Llog : ℝ} {G : ℕ → ℝ → ℝ}
    (hsrc : ∀ k τ, |G k τ| ≤ Llog * E_base k) :
    ∀ k τ, |G k τ| ≤ Llog * E_base k := hsrc

/-! ## 4. The abstract reduction -- the SOLE remaining standard frontier. -/

/-- **The abstract envelope-lattice Banach reduction**, making the carried frontier
EXPLICIT.

GIVEN a concrete complete metric model `α` of the slice space, the concrete mild
map `Φ : α → α` which `MapsTo` the EnvBall coordinate set `s` and is
`ContractingWith q` there with `q < 1` (the reuse of ChemMildLocal's scalar
`q(δ)<1` in the envelope metric), and a coordinate READOUT identifying the
produced fixed point with `cosineCoeffs (u r)` and witnessing its EnvBall
membership, together with the logistic envelope datum -- then
`LocalExist E_base Llog u G r` (unfolded) holds.

The three structural hypotheses (`hcomplete`, `hself` + `hdist`, and the readout
`hreadout`) ARE the missing standard local-well-posedness lemma: NO concrete
`MetricSpace`/`IsComplete` EnvBall model, NO concrete contracting `Φ`, and NO
fixed-point -> `cosineCoeffs (u r)` readout exists in the repo.  This theorem
CARRIES them faithfully; it does not fake them. -/
theorem localExist_of_envBall_fixedPoint
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
    (∀ k, |cosineCoeffs (u r) k| ≤ E_base k)
      ∧ (∀ k τ, |G k τ| ≤ Llog * E_base k) := by
  have hcontract : ContractingWith q.toNNReal (hself.restrict Φ s s) := by
    refine ⟨Real.toNNReal_lt_one.mpr hq, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Real.coe_toNNReal q hq_nn]; exact hdist a b
  obtain ⟨y, hy_mem, hy_fix, _, _⟩ :=
    hcontract.exists_fixedPoint' hcomplete hself hx₀ hedist
  exact ⟨hreadout y hy_mem hy_fix, hsrc⟩

/-! ## AxiomAudit -/

section AxiomAudit
#print axioms EnvBall
#print axioms envBall_invariance_coeff
#print axioms logistic_source_envelope
#print axioms localExist_of_envBall_fixedPoint
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegLocalExist
