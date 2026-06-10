/-
  ShenWork/Paper2/IntervalPicardIterateSourcePackage.lean

  **Deliverable B — the per-level source-package producer wiring.**

  Front A's representation-fed producer
  `IntervalPicardIterateSourceRepresentation.picardIterate_source_duhamelSourceTimeC1_of_representation`
  takes the per-slice cosine representation triple `(bc, hbsum, hagree)`, the ball
  value bounds `(hpos, hub)`, the derivative bounds `(hG1, hG2)` on `[0,1]`, and the
  K1 source-coefficient time-`C¹` data `(adot, hderiv, hadotcont, hMdot)` and produces

      DuhamelSourceTimeC1 (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)

  — exactly the `hsrc0`/`srcσ` shape consumed by `picardIterateRestart_cosineIdentity`
  and `uniformWiring_of_data_v2`.

  This file is the clean wiring lemma `iterateSourcePackage_of_inputs` that names the
  exact hypothesis list:

    * **(repr)** the deliverable-A triple, supplied here in the producer's all-`σ`
      interface (`IntervalPicardIterateRepresentation` discharges it on `σ > 0`; the
      producer's interface quantifies over all `σ` — that quantification is the
      producer's boundary, taken verbatim);
    * **(ball)** the cone-exposable value bounds;
    * **(K1)** the time-`C¹` source-coefficient data produced by
      `IntervalPicardIterateTimeC1` (its remaining `hprofile_joint` residual is
      *inside* K1; this producer consumes only the K1 *output* fields).

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalPicardIterateRepresentation
import ShenWork.Paper2.IntervalPicardIterateSourceRepresentation

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildPicardRegularity (logisticSourceFun)
open ShenWork.IntervalPicardIterateSourceRepresentation
  (picardIterate_source_duhamelSourceTimeC1_of_representation)

noncomputable section

namespace ShenWork.IntervalPicardIterateSourcePackage

/-- **Deliverable B — the per-level source-package producer, named wiring.**

A thin, explicitly-typed pass-through to Front A's representation-fed producer.  It
isolates the exact hypothesis list a consumer must discharge per level `n` to obtain
the `DuhamelSourceTimeC1` package (the `hsrc0`/`srcσ` inputs of the restart identity
and of `uniformWiring_of_data_v2`):

  * `(bc, hbsum, hagree)` — the cosine representation (deliverable A on `σ > 0`);
  * `(hpos, hub)` — ball value bounds (cone-exposable);
  * `(hG1, hG2)` — derivative bounds on `[0,1]` (consumed only interiorly);
  * `(adot, hderiv, hadotcont, hMdot)` — K1 time-`C¹` data
    (`IntervalPicardIterateTimeC1`). -/
noncomputable def iterateSourcePackage_of_inputs
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {M G1 G2 : ℝ}
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, Summable (fun k => unitIntervalCosineEigenvalue k * |bc σ k|))
    (hagree : ∀ σ, Set.EqOn
        (intervalDomainLift (picardIter p u₀ n σ))
        (fun x => ∑' k, bc σ k * cosineMode k x) (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (picardIter p u₀ n σ) x)
    (hub : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (picardIter p u₀ n σ) x ≤ M)
    (hG1 : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (picardIter p u₀ n σ)) x| ≤ G1)
    (hG2 : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (picardIter p u₀ n σ))) x| ≤ G2)
    (adot : ℝ → ℕ → ℝ)
    (hderiv : ∀ σ k, HasDerivAt
      (fun r => cosineCoeffs
        (logisticSourceFun p.a p.b p.α
          (intervalDomainLift (picardIter p u₀ n r))) k) (adot σ k) σ)
    (hadotcont : ∀ k, Continuous (fun σ => adot σ k))
    {Mdot : ℝ}
    (hMdot : ∀ σ, 0 ≤ σ → ∀ k, |adot σ k| ≤ Mdot) :
    DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k) :=
  picardIterate_source_duhamelSourceTimeC1_of_representation
    p u₀ n hα ha hb bc hbsum hagree hpos hub hG1 hG2 adot hderiv hadotcont hMdot

end ShenWork.IntervalPicardIterateSourcePackage
