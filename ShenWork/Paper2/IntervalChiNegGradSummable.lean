/-
  ShenWork/Paper2/IntervalChiNegGradSummable.lean

  χ₀<0 REBUILD — the FINAL piece: per-slice eigenvalue-weighted ℓ¹ gradient
  summability  `Σ_k λ_k · |cosineCoeffs (lift (u τ)) k| < ∞`  for a fixed slice
  `τ > 0`, from the LANDED mild representation
  (`conjugateSlice_decomp_tauLift`'s output shape)

      û_k(τ) = e^{−(τ λ_k)} û₀_k
                 + (−χ₀) · duhamelEnergyCoeff 1 (sineCoeffs ∘ conjQ) τ k
                 + duhamelEnergyCoeff 1 (conjFl) τ k,

  plus the landed heat-smoothing / Duhamel-IBP spectral lemmas.

  This is the spectral analogue of the missing `u_xt` regularity, but in its
  PER-SLICE (τ fixed) form — strictly weaker than the uniform sup-over-τ
  coordinatewise envelope the old architecture stalled on.  For `τ > 0` the heat
  factor `e^{−τ λ_k}` beats any polynomial weight, so the heat leg is
  unconditionally summable; the two Duhamel legs deflate through their own
  time-IBP (`duhamelSpectralCoeff_eigenvalue_summable`) once the source is
  presented at the divergence weight `√λ_k · F`.

  ## Two-way audit (honest accounting)

  * DERIVED:
    - `gradSummable_heat` — the heat leg `Σ_k λ_k e^{−τλ_k} |û₀_k| < ∞`, directly
      from the landed `heatCoeff_eigenvalue_summable` (û₀ coefficients ℓ∞-bounded).
    - `gradSummable_duhamel` — each Duhamel leg
      `Σ_k λ_k |duhamelEnergyCoeff 1 F τ k| < ∞`, from the landed
      `duhamelSpectralCoeff_eigenvalue_summable` (time-IBP) transported across the
      divergence-mode bridge `duhamelEnergyCoeff_eq_duhamelSpectralCoeff_divMode`.
    - `gradSummable_slice` — the triangle assembly over the mild decomposition.
    - `gradSummable_slice_consumes` — the wired form feeding the reconstruction
      consumer `cosineCoeffSeries_grad_hasDerivAt`.

  * CARRIED — the precise, non-faked source inputs (each the honest analytic
    hypothesis, never relabeled):
    - `hM0 : ∀ k, |û₀_k| ≤ M₀` — initial-datum coefficient ℓ∞ bound (record
      regularity of `u₀`); the heat leg's only input.
    - `srcChem : DuhamelSourceTimeC1 (√λ · sineCoeffs ∘ conjQ)`,
      `srcLog  : DuhamelSourceTimeC1 (√λ · conjFl)` — the two divergence-weighted
      source packages: time-`C¹` coefficients, an ℓ¹ envelope, and a uniform
      derivative bound at the H¹-divergence weight.  This is exactly the spectral
      `H^{3/2}`-source regularity the per-slice statement reduces to; it is the
      honest physical input, supplied by the source producer, not assumed away.
    - `hdecomp` — the landed mild decomposition (`conjugateSlice_decomp_tauLift`).

    Failed greps (no pre-existing eigenvalue-weighted ℓ¹ Duhamel summable nor a
    bare-record reconstruction were present):
        grep -rn "Summable.*lam.*duhamelEnergyCoeff"            ShenWork → NONE
        grep -rn "duhamelEnergyCoeff.*eigenvalue_summable"      ShenWork → NONE
    The landed `heatCoeff_eigenvalue_summable`,
    `duhamelSpectralCoeff_eigenvalue_summable`,
    `duhamelEnergyCoeff_eq_duhamelSpectralCoeff_divMode`,
    `cosineCoeffSeries_grad_hasDerivAt` ARE the engines used here.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file only.  Lines ≤ 100.
  Mathlib v4.29.1.  `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.
-/
import ShenWork.Paper2.IntervalDecompTauLift
import ShenWork.Paper2.IntervalSourceBridgeTest
import ShenWork.PDE.IntervalSemigroupNeumann
import ShenWork.PDE.IntervalDuhamelClosedC2

open MeasureTheory
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2.HSigmaScale (lam)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.IntervalSemigroupNeumann (heatCoeff_eigenvalue_summable)
open ShenWork.IntervalDuhamelClosedC2
  (duhamelSpectralCoeff duhamelSpectralCoeff_eigenvalue_summable DuhamelSourceTimeC1)
open ShenWork.Paper2.IntervalSourceBridgeTest
  (duhamelEnergyCoeff_eq_duhamelSpectralCoeff_divMode)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.Paper2.IntervalDecompTauLift (conjQ conjFl)

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegGradSummable

/-- **Heat leg.**  `Σ_k λ_k · |e^{−(τ λ_k)} û₀_k| < ∞` for `τ > 0`, from the
landed `heatCoeff_eigenvalue_summable` (the eigenvalue-weighted ℓ¹ heat smoothing:
`e^{−τ λ_k}` beats the polynomial weight `λ_k`).  `û₀` has ℓ∞-bounded coefficients
(`hM0`).  DERIVED. -/
theorem gradSummable_heat {τ M₀ : ℝ} (hτ : 0 < τ) {uhat0 : ℕ → ℝ}
    (hM0 : ∀ k, |uhat0 k| ≤ M₀) :
    Summable (fun k : ℕ =>
      lam k * |Real.exp (-(τ * lam k)) * uhat0 k|) := by
  have h := heatCoeff_eigenvalue_summable (t := τ) hτ (a := uhat0) (M := M₀) hM0
  refine h.congr (fun k => ?_)
  change unitIntervalCosineEigenvalue k *
      |Real.exp (-τ * unitIntervalCosineEigenvalue k) * uhat0 k|
    = lam k * |Real.exp (-(τ * lam k)) * uhat0 k|
  have hlam : lam k = unitIntervalCosineEigenvalue k := rfl
  rw [hlam, neg_mul]

/-- **Duhamel leg.**  `Σ_k λ_k · |duhamelEnergyCoeff 1 F τ k| < ∞`, from the landed
time-IBP `duhamelSpectralCoeff_eigenvalue_summable` for the divergence-weighted
source `a s n = √(λ_n) · F n s` (packaged honestly as `src`), transported across
the bridge `duhamelEnergyCoeff_eq_duhamelSpectralCoeff_divMode`.  DERIVED. -/
theorem gradSummable_duhamel {τ : ℝ} (hτ : 0 < τ) {F : ℕ → ℝ → ℝ}
    (src : DuhamelSourceTimeC1 (fun s n => Real.sqrt (lam n) * F n s)) :
    Summable (fun k : ℕ => lam k * |duhamelEnergyCoeff 1 F τ k|) := by
  have h := duhamelSpectralCoeff_eigenvalue_summable src hτ
  refine h.congr (fun k => ?_)
  have hbridge := duhamelEnergyCoeff_eq_duhamelSpectralCoeff_divMode F τ k
  change unitIntervalCosineEigenvalue k *
      |duhamelSpectralCoeff (fun s n => Real.sqrt (lam n) * F n s) τ k|
    = lam k * |duhamelEnergyCoeff 1 F τ k|
  have hlam : lam k = unitIntervalCosineEigenvalue k := rfl
  rw [hlam, ← hbridge]

/-- **Per-slice eigenvalue-weighted ℓ¹ gradient summability.**
`Σ_k λ_k · |cosineCoeffs (lift (u τ)) k| < ∞` for the fixed slice `τ > 0`, by the
triangle inequality over the LANDED mild decomposition (`hdecomp`, the output
shape of `conjugateSlice_decomp_tauLift`): heat leg + `|χ₀|·`chem leg + log leg,
each summable by `gradSummable_heat` / `gradSummable_duhamel`.  DERIVED from those
two legs + the carried decomposition.  This is the carried frontier of
`IntervalChiNegH1EnergyDeriv` discharged at fixed `τ`. -/
theorem gradSummable_slice {p : CM2Params} {τ M₀ : ℝ} (hτ : 0 < τ)
    {u : ℝ → intervalDomainPoint → ℝ} {uhat0 : ℕ → ℝ}
    (hM0 : ∀ k, |uhat0 k| ≤ M₀)
    (srcChem : DuhamelSourceTimeC1
      (fun s n => Real.sqrt (lam n) *
        sineCoeffs (conjQ p u s) n))
    (srcLog : DuhamelSourceTimeC1
      (fun s n => Real.sqrt (lam n) *
        conjFl p u n s))
    (hdecomp : ∀ k, cosineCoeffs (intervalDomainLift (u τ)) k
        = Real.exp (-(τ * lam k)) * uhat0 k
          + (-p.χ₀) * duhamelEnergyCoeff 1
              (fun k τ => sineCoeffs (conjQ p u τ) k) τ k
          + duhamelEnergyCoeff 1
              (conjFl p u) τ k) :
    Summable (fun k : ℕ =>
      lam k * |cosineCoeffs (intervalDomainLift (u τ)) k|) := by
  have hheat := gradSummable_heat hτ hM0
  have hchem := gradSummable_duhamel hτ srcChem
  have hlog := gradSummable_duhamel hτ srcLog
  have hmaj := (hheat.add (hchem.mul_left |p.χ₀|)).add hlog
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (by unfold lam unitIntervalCosineEigenvalue; positivity)
      (abs_nonneg _)) (fun k => ?_) hmaj
  rw [hdecomp k]
  have hlamnn : (0:ℝ) ≤ lam k := by
    unfold lam unitIntervalCosineEigenvalue; positivity
  set H := Real.exp (-(τ * lam k)) * uhat0 k with hH
  set C := duhamelEnergyCoeff 1
    (fun k τ => sineCoeffs (conjQ p u τ) k) τ k with hC
  set L := duhamelEnergyCoeff 1
    (conjFl p u) τ k with hL
  calc lam k * |H + (-p.χ₀) * C + L|
      ≤ lam k * (|H| + (|p.χ₀| * |C| + |L|)) := by
        apply mul_le_mul_of_nonneg_left _ hlamnn
        calc |H + (-p.χ₀) * C + L|
            ≤ |H + (-p.χ₀) * C| + |L| := abs_add_le _ _
          _ ≤ (|H| + |(-p.χ₀) * C|) + |L| := by gcongr; exact abs_add_le _ _
          _ = |H| + (|p.χ₀| * |C| + |L|) := by
                rw [show (-p.χ₀) * C = -(p.χ₀ * C) by ring, abs_neg, add_assoc,
                  abs_mul p.χ₀ C]
    _ = lam k * |H| + |p.χ₀| * (lam k * |C|) + lam k * |L| := by ring

/-- **Consumer-facing form.**  The per-slice summability is exactly the hypothesis
`cosineCoeffSeries_grad_hasDerivAt` (and `cosineCoeffSeries_grad2_hasDerivAt`,
`sineSeries_l2_sq`) consume: `Summable (λ_n · |b_n|)` with
`b_n = cosineCoeffs (lift (u τ)) n` (`lam` is definitionally
`unitIntervalCosineEigenvalue`).  Reconstruction wiring of `gradSummable_slice`. -/
theorem gradSummable_slice_consumes {p : CM2Params} {τ M₀ : ℝ} (hτ : 0 < τ)
    {u : ℝ → intervalDomainPoint → ℝ} {uhat0 : ℕ → ℝ}
    (hM0 : ∀ k, |uhat0 k| ≤ M₀)
    (srcChem : DuhamelSourceTimeC1
      (fun s n => Real.sqrt (lam n) *
        sineCoeffs (conjQ p u s) n))
    (srcLog : DuhamelSourceTimeC1
      (fun s n => Real.sqrt (lam n) *
        conjFl p u n s))
    (hdecomp : ∀ k, cosineCoeffs (intervalDomainLift (u τ)) k
        = Real.exp (-(τ * lam k)) * uhat0 k
          + (-p.χ₀) * duhamelEnergyCoeff 1
              (fun k τ => sineCoeffs (conjQ p u τ) k) τ k
          + duhamelEnergyCoeff 1
              (conjFl p u) τ k) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        |cosineCoeffs (intervalDomainLift (u τ)) n|) :=
  gradSummable_slice hτ hM0 srcChem srcLog hdecomp

end ShenWork.Paper2.IntervalChiNegGradSummable

section AxiomAudit
#print axioms ShenWork.Paper2.IntervalChiNegGradSummable.gradSummable_heat
#print axioms ShenWork.Paper2.IntervalChiNegGradSummable.gradSummable_duhamel
#print axioms ShenWork.Paper2.IntervalChiNegGradSummable.gradSummable_slice
#print axioms ShenWork.Paper2.IntervalChiNegGradSummable.gradSummable_slice_consumes
end AxiomAudit
