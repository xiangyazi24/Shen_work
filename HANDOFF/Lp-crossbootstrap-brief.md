# Codex brief — discharge `CrossDiffusionBootstrapEstimate` (Paper 2 Lᵖ heart, m=1)

## Goal (single load-bearing open lemma of the whole Lᵖ mountain)
Produce, UNCONDITIONALLY from a classical solution's regularity + v-side estimates:
```
CrossDiffusionBootstrapEstimate intervalDomain p T rho u v   -- rho = 0 for m=1 (linear diffusion)
```
i.e. (Statements.lean:1126):
```
∀ eps>0, ∀ pExp>1, ∃ Ceps, ∀ t∈(0,T),
  intervalDomain.crossDiffusionEnergyTerm p pExp (u t) (v t)
    ≤ eps · ∫ (u t x)^(pExp-2)·(gradNorm (u t) x)^2 dx  +  Ceps · ∫ (u t x)^(pExp+rho) dx
```
where (PDE/IntervalDomain.lean:2931):
```
crossDiffusionEnergyTerm p pExp u v = ∫₀¹ (lift u)^(pExp-1)·|∂ₓ(lift u)|·|∂ₓ(lift v)| / (1+lift v)^β dx
```

## Proof (Q4409 §cross-term, specialized m=1, rho=0)
Write A := v_x/(1+v)^β. Since v≥0, β≥1 ⇒ (1+v)^{-β} ≤ 1 ⇒ |A| ≤ |v_x|.
Young on u^(p-1)|u_x||A| = (2/p)·|∂ₓ(u^(p/2))|·u^(p/2)|A|:
```
∫ u^(p-1)|u_x||A| ≤ eps·∫|∂ₓ(u^(p/2))|² + (1/(4eps))·(2/p)²·∫ u^p·A²
```
and ∫|∂ₓ(u^(p/2))|² = (p/2)²·∫ u^(p-2)|u_x|² (the weighted gradient dissipation).
Remaining: ∫ u^p·A² ≤ Ceps·∫u^p (rho=0) needs a v-gradient sup bound
‖v_x‖_∞ (⇒ A²≤‖v_x‖_∞²): use `H1PhysicalChemResolverSupBefore` /
`resolverGrad_sup_le_of_ub` (ShenWork/Paper2/IntervalChiNegH1PhysicalResolverSupProducer.lean)
— the elliptic v_xx = μv − νu^γ resolver gradient sup bound. If it only gives a u-dependent
bound, feed the u-dependence into the `∫u^(p+rho)` term with the appropriate rho (roadmap: rho=1-m=0
for m=1 works only if ‖v_x‖_∞ is a constant on (0,T); otherwise carry the resolver-sup as a
frontier hypothesis and discharge separately).

## Existing pieces to REUSE (do NOT rebuild)
- Full finite-p energy chain of_frontiers: IntervalDomainEnergyStep.lean
  (intervalDomain_lp_energy_derivative_le_constant_of_explicit_cross_bound = finite-p Gronwall).
- Moser closure: IntervalDomainMoserClosure.lean (StructuredMoserBootstrapData.boundedBefore).
- Regularity→energy frontiers: intervalDomain_LpBootstrapEnergyInequality_of_regularity.
- Resolver ∇v sup bound: H1PhysicalChemResolverSupBefore family.
- RelativeMoserInterpolationBefore producer: IntervalDomainMCL.lean:86.

## Rules
- Write NEW files only (or the producer slot of existing 0-sorry Lp files). Do NOT edit any
  Codex-χ<0 file (IntervalTruncatedWeakBarrierComparison*, resolver EDIT — read/import only).
- `lake env lean` single-file self-check each; commit each clean milestone; #print axioms on the headline.
- No effort cap. If ‖v_x‖ bound is only u-dependent, isolate the exact residual and state it precisely.

## Remaining Moser-bookkeeping frontiers (secondary, after the heart)
hboot (AbstractLpBootstrapHypothesis), hdiss (MoserDissipationDropBefore),
hLpMono, hEndpoint (IntervalDomainMoserQuantitativeEndpoint) — discharge from regularity;
RelativeMoserInterpolationBefore already has a producer.
