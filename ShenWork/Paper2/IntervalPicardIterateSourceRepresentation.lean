/-
  ShenWork/Paper2/IntervalPicardIterateSourceRepresentation.lean

  FRONT A — the iterate-side **representation cure** for the M3 source
  time-`C¹` producer (`χ₀ = 0`).

  ## Why this file exists

  The legacy iterate producer
  `IntervalPicardIterateSourceC1.picardIterate_source_duhamelSourceTimeC1`
  asks for the GLOBAL field
      `hC2 : ∀ σ, ContDiff ℝ 2 (intervalDomainLift (picardIter p u₀ n σ))`,
  i.e. global `C²` of the ZERO-EXTENSION lift.  This is *unsatisfiable* for a
  profile that is positive at the Neumann endpoints (the zero extension has a
  jump in the derivative at `x = 0, 1`).  The same disease forced
  `hN0`/`hN1` (endpoint-derivative facts of the lift) and made `hG1`/`hG2`
  semantically meaningless at the endpoints.

  The cure — already built on the LIMIT side as
  `IntervalDomainLimitSourceRepresentation.limitSource_duhamelSourceTimeC1_of_representation`
  — replaces the global-`C²` lift field by the per-slice cosine representation
      `lift (w σ) =ᴵᶜᶜ (x ↦ ∑ₙ bc σ n · cos(nπx))`  with  `∑ₙ λₙ |bc σ n| < ∞`,
  whose partial-sum series is genuinely globally `C²`.  Crucially, the limit-side
  producer is stated for an **abstract trajectory** `w : ℝ → intervalDomainPoint → ℝ`,
  so the iterate-side producer is a *one-line instantiation* at
      `w := picardIter p u₀ n`.

  ## What changed vs. the legacy interface (the poisoned-field map)

  * `hC2`  — **DROPPED**.  Replaced by the representation triple `(bc, hbsum, hagree)`.
  * `hN0`, `hN1` — **DROPPED**.  The cosine proxy supplies Neumann endpoints for free.
  * `hG1`, `hG2` — **KEPT** on `Set.Icc 0 1` (the abstract producer's interface),
    but the producer *consumes* them only at interior points: it transfers the
    bound to the genuinely-`C²` cosine proxy on `Set.Ioo 0 1` and re-extends to
    `[0,1]` via the proxy's continuous derivative.  The endpoint values of the
    lift's derivative bound are therefore never exploited (no zero-extension
    pathology enters).
  * `hpos`, `hub` — **KEPT** verbatim (value statements on `[0,1]`, legitimate).
  * `hα ha hb`, the `K1` data `(adot, hderiv, hadotcont, Mdot, hMdot)` — **KEPT**
    in the same shapes (the old `hderiv` already mentions `intervalDomainLift
    (picardIter p u₀ n r)`, which is `w r` here).

  Conclusion is unchanged:
      `DuhamelSourceTimeC1 (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)`
  — exactly the `hsrc0` shape consumed by
  `IntervalPicardIterateRestart.picardIterateRestart_cosineIdentity`.

  ## A3 — K1 reuse note (do NOT clone the K1 chain)

  The K1 data `(adot, hderiv, hadotcont, Mdot, hMdot)` is taken here as hypotheses
  in the SAME shapes as the legacy producer.  It is *already produced* iterate-side
  by `IntervalPicardIterateTimeC1` (its header: the "K1 discharge" from the restart
  representation of the iterate slice — it builds `adot σ k = cosineCoeffs (∂_σ L(w σ)) k`
  with `HasDerivAt` / time-continuity / uniform `Mdot` via
  `restartCosineSeries_hasDerivAt_time`, `restartFieldTimeDeriv`,
  `restartDerivField_continuousOn_joint`, `logisticSourceFun_hasDerivAt_time`,
  `cosineCoeffs_hasDerivAt_of_smooth_param`).  Its remaining named residual is
  `hprofile_joint` (joint continuity of the value field).  We deliberately do NOT
  re-derive any of that here; a consumer wires the `IntervalPicardIterateTimeC1`
  output directly into this producer's `adot`/`hderiv`/`hadotcont`/`hMdot`.

  ## A4 — eigenvalue-summability of the iterate's restart coefficients (route)

  For C²-of-the-restart-series consumers, the λ-weighted summability is
  `IntervalPicardIterateC2Bound.restartSeries_eigenvalue_summable` instantiated at
  the iterate slice's `restartIterateCoeff` family (source
  `fun σ k => cosineCoeffs (logisticLifted p (picardIter p u₀ n (t/2 + σ))) k`,
  half-step homogeneous datum).  That is the same `hbsum`-shaped `Summable
  (fun k => unitIntervalCosineEigenvalue k * |bc σ k|)` this producer consumes, so
  a consumer that already has the restart C²-bound package can feed it straight in.
  We do NOT inline a wrapper here (it would couple this representation producer to
  the C²-bound file's restart bookkeeping with no benefit at this layer); the route
  above is the cheap one-liner when a consumer needs it.

  ## The n = 0 trap

  The `n = 0` iterate is the homogeneous heat slice of `u₀`, not a
  restart-from-previous-source slice.  This producer is `n`-uniform and does NOT
  assume a restart structure on its inputs — it only consumes the representation
  triple, the value bounds, and the K1 data, all of which exist for `n = 0` via the
  homogeneous heat treatment (the semigroup value is `C^∞` with a trivial restart
  source).  So `n = 0` needs no special case HERE; the case split lives upstream,
  where `bc`/`adot` are *produced* (homogeneous heat vs. restart slice).

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalDomainLimitSourceRepresentation
import ShenWork.Paper2.IntervalPicardIterateRestart

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildPicardRegularity (logisticSourceFun)
open ShenWork.IntervalDomainLimitSourceRepresentation
  (limitSource_duhamelSourceTimeC1_of_representation)

noncomputable section

namespace ShenWork.IntervalPicardIterateSourceRepresentation

/-- **FRONT A — iterate source time-`C¹` step, representation-fed (`χ₀ = 0`).**

The representation-cure analogue of
`IntervalPicardIterateSourceC1.picardIterate_source_duhamelSourceTimeC1`: it
discharges the SAME `DuhamelSourceTimeC1` conclusion for the logistic-source
coefficient family of the `n`-th Picard iterate slice, but with the
*unsatisfiable* global-`C²` lift field `hC2` (and the parasitic endpoint
fields `hN0`/`hN1`) removed in favour of the per-slice cosine representation
`(bc, hbsum, hagree)`.  The derivative bounds `hG1`/`hG2` are kept on `Set.Icc 0 1`
to match the abstract limit-side producer's interface, but that producer consumes
them only at interior points (`Set.Ioo 0 1`), transferring to the genuinely-`C²`
cosine series and re-extending to the closed interval via the series' continuous
derivative — so the zero-extension's endpoint-derivative pathology is never used.

This is a one-line instantiation of the abstract-trajectory limit-side producer
at `w := picardIter p u₀ n`: with that substitution the limit-side conclusion
`DuhamelSourceTimeC1 (fun s k => cosineCoeffs (logisticLifted p (w s)) k)` and
every hypothesis become *syntactically* the iterate-side ones (`w r =
picardIter p u₀ n r` definitionally), so no transport or re-proof is needed.

The output is *literally* the `hsrc0` hypothesis of
`IntervalPicardIterateRestart.picardIterateRestart_cosineIdentity`, so this
discharges its `H2` at level `n` without the zero-extension disease. -/
noncomputable def picardIterate_source_duhamelSourceTimeC1_of_representation
    (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {M G1 G2 : ℝ}
    -- per-slice cosine representation (genuinely `C²`; replaces global-`C²`)
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, Summable (fun k => unitIntervalCosineEigenvalue k * |bc σ k|))
    (hagree : ∀ σ, Set.EqOn
        (intervalDomainLift (picardIter p u₀ n σ))
        (fun x => ∑' k, bc σ k * cosineMode k x) (Set.Icc (0 : ℝ) 1))
    -- value bounds on the lift (KEPT verbatim from the legacy producer)
    (hpos : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (picardIter p u₀ n σ) x)
    (hub : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (picardIter p u₀ n σ) x ≤ M)
    -- derivative bounds on the lift (consumed only INTERIORLY by the producer:
    -- it transfers them to the genuinely-`C²` cosine series on `Set.Ioo 0 1`
    -- and re-extends to `[0,1]` by the series' continuous derivative, so the
    -- endpoint values of these lift bounds are never exploited destructively)
    (hG1 : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (picardIter p u₀ n σ)) x| ≤ G1)
    (hG2 : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (picardIter p u₀ n σ))) x| ≤ G2)
    -- K1 source-coefficient time-`C¹` data (KEPT; produced by IntervalPicardIterateTimeC1)
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
  limitSource_duhamelSourceTimeC1_of_representation
    p (picardIter p u₀ n) hα ha hb
    bc hbsum hagree hpos hub hG1 hG2
    adot hderiv hadotcont hMdot

-- #print axioms picardIterate_source_duhamelSourceTimeC1_of_representation

end ShenWork.IntervalPicardIterateSourceRepresentation
