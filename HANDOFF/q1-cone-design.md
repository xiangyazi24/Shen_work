# Q1 cone-invariance design (χ₀ = 0 hQuant, Session B)

Goal: `hQuant` for χ₀ = 0 with horizon δ(M) uniform over ALL PIDs |u₀| ≤ M —
no inf-threshold, no ClassicalMinPersistence. Replaces the crude
`corrections < inf u₀` positivity gate in the Picard construction.

## Atoms (ALL GREEN as of 1cf9c46-ish)
- `IntervalSemigroupComposition`: S(s)(S(t)f) = S(s+t)f on [0,1]
  (f continuous, bounded coeffs); cosineCoeffs_semigroup.
- `IntervalSemigroupConeAtoms`: S(t)(c·f) = c·S(t)f;
  duhamel_cone_eval: ∫₀ᵗ S(t−s)(c(s)·S(s)f) ds = (∫c)·S(t)f;
  mono (bounded inputs); strict positivity S(t)f(x) > 0 for continuous
  f ≥ 0 on [0,1], > 0 somewhere.
- `IntervalMildPicardThreshold.gradientMildSolutionData_initialApproach`
  (generic; reuse).

## The cone
Fix M, a := p.a, α := p.α. M_e := e^{a·δ}·M (sup envelope),
K_e := p.b · M_e^α. Choose δ = δ(M) with K_e·(e^{aδ}−1)/a ≤ 1/2 (and the
usual contraction constraint A√δ+Bδ < 1 — both datum-free).
Cone(t): θ(t)·S(t)f₀ ≤ w(t) ≤ e^{at}·S(t)f₀, θ(t) := 1 − K_e(e^{at}−1)/a ≥ ½,
where f₀ := clipped continuous extension of u₀ (S(t)(lift u₀) = S(t)f₀ by
integral congruence on [0,1]; lift u₀ itself is NOT continuous at the
boundary — phrase everything through f₀).

## Preservation (χ₀=0: Φ(w)(t) = S(t)u₀ + ∫₀ᵗS(t−s)L(w s)ds)
- 0 ≤ w (from θ ≥ ½ ≥ 0 + S ≥ 0) ⇒ L(w) = w(a−b·w^α) ≤ a·w ≤ a·e^{as}S(s)f₀.
- w ≤ M_e (from upper cone + |S f₀| ≤ M) ⇒ L(w) ≥ −b·M_e^α·w ≥ −K_e·e^{as}S(s)f₀.
- Operator mono (Icc-version! see TODO) + duhamel_cone_eval with
  c_hi(s) = a·e^{as} (∫₀ᵗ = e^{at}−1) and c_lo(s) = −K_e·e^{as}:
  S(t)f₀·θ(t) ≤ Φ(w)(t) ≤ e^{at}·S(t)f₀.  EXACT invariance.

## TODO list (in order)
1. ✅ DONE (76c1451): `intervalFullSemigroupOperator_mono_of_le_on_Icc`.
2. ✅ DONE (a675cb6, GREEN, axiom-clean): `IntervalMildPicardCone.cone_preserved`
   — (1 − Ke·I(t))·S(t)f₀ ≤ Φ(u₀,w)(t) ≤ (1 + a·I(t))·S(t)f₀ on the cone
   0 ≤ w ≤ e^{as}·S(s)f₀, Ke ≥ b·Mw^α, I = envelopeIntegral.
   Note 1 + a·I(t) = e^{at} (FTC, for the caller), so upper cone is exactly
   invariant; nonneg-preservation needs Ke·I(T) ≤ 1 (uniform small T).
3–7. ✅ ALL DONE (f6f265b, GREEN, axiom-clean):
   - IntervalMildPicardConeData.coneGradientMildSolutionData_exists:
     route (b) executed — χ₀=0-specialised construction (value-Duhamel-only
     ball/contraction/continuity/measurability blocks, ~770 lines), cone
     induction over iterates, limit via ge_of_tendsto, hpos from the cone
     lower output (1−Ke·I(t) ≥ ½) × kernel strict positivity.  Horizon
     δ(p,M) = 1/(2(C_L + C_L_val + Ke·e^a + 1)), fully datum-free.
   - IntervalDomainConeQuantBridge:
     positiveInitialDatum_nonneg (closed-interval nonneg by one-sided
     limits), PicardLimitRestartFrontier (UNIFIED residual — subsumes
     PicardRestartFrontier), quantitativeLocalExistence_chiZero (hQuant
     for χ₀=0 modulo the frontier only — no threshold, no MinPersistence),
     paper2_theorem_1_1_chiZero_of_frontier.

## CAMPAIGN CLOSED. Residual for hQuant(χ₀=0): PicardLimitRestartFrontier
   (= the F2/S-construction, Session A's M-line). General χ₀ ≤ 0 still
   goes through Threshold + ClassicalMinPersistence (Q3 deferred).
