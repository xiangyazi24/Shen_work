# Phase-0 / M1 spec: iterate restart cosine identity (χ₀ = 0)

Target file (NEW, sole writer): ShenWork/Paper2/IntervalPicardIterateRestart.lean

## Goal (R2′ M1, DESIGN_F2_CONSENSUS.md)

For p : CM2Params with hχ0 : p.χ₀ = 0, the Picard iterate
u_{n+1} := fun t x => intervalGradientDuhamelMap p u₀ (picardIter p u₀ n) t x
(NOTE: check how picardIter is defined in ShenWork/Paper2/IntervalMildPicard.lean
and state everything for `picardIter p u₀ (n+1)` directly)
satisfies the half-step restart cosine identity: for 0 < t,

  Set.EqOn (intervalDomainLift (picardIter p u₀ (n+1) t))
    (fun x => ∑' k : ℕ,
      restartDuhamelCoeff
        (cosineCoeffs (intervalDomainLift (picardIter p u₀ (n+1) (t/2))))
        (fun σ k => cosineCoeffs (logisticLifted p (picardIter p u₀ n (t/2 + σ))) k)
        (t/2) k * cosineMode k x)
    (Set.Icc (0:ℝ) 1)

taking as HYPOTHESES (to be discharged later in the induction; do NOT try to
prove them here):
  (H1) hu₀_cont : Continuous (intervalDomainLift u₀)
       and a coefficient bound ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀
  (H2) hsrc : DuhamelSourceTimeC1
         (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
       — or a time-windowed variant if you need the family only on [0,t];
       adjust the windowing honestly if the global form is wrong for the
       restart (the source family in the conclusion is σ ↦ t/2+σ shifted;
       you may need a shifted DuhamelSourceTimeC1, derive it from hsrc or
       take the shifted form as the hypothesis — pick what composes, report).
  (H3) per-slice continuity: ∀ s ∈ (0,t], Continuous (logisticLifted p (picardIter p u₀ n s))
       (this may follow from existing picardIter_ball continuity lemmas —
       reuse if convenient, otherwise hypothesis)

χ₀ = 0 kills the flux term: (−p.χ₀ = 0) so the middle term of
intervalGradientDuhamelMap is 0 * (∫ ...) = 0 — prove a small lemma
`intervalGradientDuhamelMap_eq_of_chi0_zero` first reducing the map to
S(t)u₀ + ∫₀ᵗ S(t−s) L_n(s) ds.

## Proof skeleton (atoms all exist)

1. Spectral form of each piece at interior x then extend to Icc:
   - S1b: ShenWork.IntervalFullKernelSpectralClean.intervalFullSemigroupOperator_eq_cosineHeatValue_Icc
   - Duhamel: per-s spectral form + ∫↔∑ swap =
     ShenWork.IntervalDuhamelClosedC2.duhamelSpectral_eq_cosineSeries (needs hsrc;
     check its exact LHS — it is stated with unitIntervalCosineHeatValue inside
     the s-integral, so first rewrite the integrand pointwise via S1b/Icc,
     using intervalIntegral.integral_congr).
2. So lift(u_{n+1}(t)) x = ∑'k (e^{−tλ_k}·û₀_k + duhamelSpectralCoeff L̂_n t k)·cos(kπx)
   on Icc, and same at t/2.
3. Coefficient extraction at t/2: cosineCoeffs of the series = the coefficients.
   Session B's ShenWork/PDE/IntervalSemigroupComposition.lean (may still be
   build-pending) has cosineCoeffs_unitIntervalCosineHeatValue (extraction for
   the heat series) — READ it; if its form doesn't cover the restart series
   (homogeneous + Duhamel sum), prove the generic ℓ¹ extraction
   `cosineCoeffs_of_l1_series : Summable (fun k => |c k|) →
     cosineCoeffs (fun x => if x ∈ Icc 0 1 then ∑' k, c k * cosineMode k x else 0) = c`
   — careful: cosineCoeffs takes ℝ→ℝ functions; the lift of the iterate slice
   IS the zero-extension, and on Icc it equals the series; cosineCoeffs only
   integrates over [0,1] so only Icc values matter (check the def:
   unitIntervalCosineRawCoeff integrates ∫ in 0..1 — so equality of the
   integrand on [0,1] suffices via intervalIntegral.integral_congr).
4. Restart algebra per mode: with τ := t/2, t = τ + τ:
   e^{−tλ} = e^{−τλ}·e^{−τλ} and
   duhamelSpectralCoeff L̂ t k
     = e^{−τλ_k} · duhamelSpectralCoeff L̂ τ k
       + duhamelSpectralCoeff (fun σ => L̂ (τ+σ)) τ k
   (split ∫₀ᵗ = ∫₀^τ + ∫_τ^t  via intervalIntegral.integral_add_adjacent_intervals,
    factor the exponential, change variables on [τ,t] via
    intervalIntegral.integral_comp_add_left or _comp_add_right — get the σ-shift).
   Integrability for the splits: from hsrc's continuity (hderiv → continuousAt)
   + exp continuity (Continuous.intervalIntegrable).
5. Combine: c_k(t) = e^{−τλ}·c_k(τ) + duhamelCoeff(shifted) τ k
   = restartDuhamelCoeff (extracted-coeffs-at-τ) (shifted family) τ k. Done.

## Key defs/locations
- intervalGradientDuhamelMap, logisticLifted: ShenWork/Paper2/IntervalGradientDuhamelMap.lean
- picardIter: ShenWork/Paper2/IntervalMildPicard.lean (READ its definition first!)
- restartDuhamelCoeff: ShenWork/Paper2/IntervalMildRegularityBootstrap.lean:35
- duhamelSpectralCoeff, DuhamelSourceTimeC1, duhamelSpectral_eq_cosineSeries:
  ShenWork/PDE/IntervalDuhamelClosedC2.lean (~1360-1430)
- cosineMode: ShenWork.CosineSpectrum.cosineMode; orthogonality:
  CosineSpectrum.lean:127 cosineMode_orthogonal
- unitIntervalCosineHeatValue/PointWeight: ShenWork/PDE/HeatSemigroup.lean:1695-1702
- cosineCoeffs def chain: IntervalNeumannFullKernel.lean:83 →
  HeatKernelGradientEstimates.lean:20,73 (raw coeff is a 0..1 interval integral)

## Constraints
- 0 sorry/admit/axiom/native_decide. New file only.
- Hypotheses (H1)-(H3) are allowed; NOTHING ELSE may be assumed beyond p-field
  positivity facts already in CM2Params. Every hypothesis you add must be
  satisfiable-by-design — state in the header why each is dischargeable
  (H1: datum data; H2: M3 module output; H3: iterate continuity, exists).
- Verify on uisai1 via scp + lake env lean (NOT lake build; check
  pgrep -f "lake build" first; missing dependency oleans: lake env lean -o).
- If session B's IntervalSemigroupComposition is red/missing, do NOT import
  it — prove the generic ℓ¹ extraction locally instead.
- Commit ONLY your file: "Phase-0 M1: iterate restart cosine identity (chi0=0)
  from H1-H3", push uisai1 main (handle untracked-copy collision as before).
