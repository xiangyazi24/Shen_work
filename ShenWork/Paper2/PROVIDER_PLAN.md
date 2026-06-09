# Plan: Close reducedLimitRegularityInputs_of_picard sorry

## Provider signature
```
(p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b) (hα : 1 ≤ p.α)
(u₀ : intervalDomainPoint → ℝ) (hu₀ : PositiveInitialDatum intervalDomain u₀)
(D : GradientMildSolutionData p u₀)
```

## Fields and sources

### Closed (5/25)
- hα := hα ✅
- ha := ha.le ✅
- hb := hb.le ✅
- hu₀_cont := hu₀.admissible.2 ✅
- hfix := D.hmild ✅
- Msup := D.M ✅
- hpost := D.hpos ✅
- hubt := D.hbound ✅

### Group A: Datum cosine data (M₀, hu₀_bound)
- M₀: bound on cosineCoeffs(lift u₀). From Continuous u₀ (subtype) + bounded → lift is bounded on [0,1] → cosineCoeffs bounded.
- hu₀_bound: same.
- Issue: cosineCoeffs uses integral over [0,1] of lift × cos. lift on [0,1] = u₀, so this just needs u₀ bounded on [0,1] (from PID admissible bounded).
- Can use: `cosineCoeffs_abs_le_of_continuous_bounded` with ContinuousOn from subtype Continuous.

### Group B: Cosine representation (bc, hbsum, hagree)
- Source: IntervalPicardLimitRestartWeak.limit_lift_eq_cosineSeries_weak
- BUT: that theorem takes Continuous (lift u₀) which we changed.
- Fix: use the cosine series of u₀ as the proxy, or defer.

### Group C: Spatial regularity (G1, G2, hG1t, hG2t, hN0t, hN1t)
- Source: Picard iterate spatial bootstrap → limit.
- These are about deriv/deriv² of lift(D.u σ) on [0,1].
- The Picard iterates have spatial regularity; passing to the limit preserves it.
- But the infrastructure (IntervalPicardIterateRestart) takes Continuous (lift u₀).

### Group D: K1 source coefficients (adott, hderivt, hadotcontt, Mdott, shifted versions)
- Source: limitSource_duhamelSourceTimeC1_of_representation (adapter!)
- Takes: bc/hbsum/hagree/hpos/hub/hG1/hG2/adot/hderiv/hadotcont/hMdot
- This is circular: needs Group B and C as inputs.

### Group E: Individual (hLc, hpde_u, Hvsrc, Hvpos)
- hLc: logistic slice continuity. Needs Continuous(lift(logistic source)).
  0-extension issue → use adapter.
- hpde_u: already proved as hpde_u_of_representation, needs hpdeData.
- Hvsrc: resolverSource_duhamelSourceTimeC1_of_representation (adapter!)
- Hvpos: elliptic strong max principle for resolver.

## Strategy
The sorry form a dependency DAG. The bottom is Group B (cosine representation),
which requires fixing limit_lift_eq_cosineSeries_weak to not need Continuous (lift u₀).
Everything else builds on top of Group B.
