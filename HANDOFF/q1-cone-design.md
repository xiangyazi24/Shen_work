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
3. Iterate induction: picardIter n ∈ Cone for all n (base: iterate 0 =
   S(t)u₀ = 1·S(t)f₀ ∈ Cone since θ ≤ 1 ≤ e^{at}; step: preservation).
4. Limit: picardLimit ∈ Cone (pointwise limit of cone members; cone is
   closed under pointwise limits — le_of_tendsto).
5. Positivity: u(t,x) ≥ ½·S(t)f₀(x) > 0 via strict positivity atom
   (PID gives f₀ ≥ 0 on [0,1], f₀(½) = u₀(½) > 0).
6. Cone-augmented MildExistenceData: hmapsTo_pos quantifies over the
   WHOLE ball — either (a) restrict the trajectory class in a cone-indexed
   variant of the Picard run, or (b) keep MildExistenceData but discharge
   hpos of the final GradientMildSolutionData record directly from 4+5
   (build the record by hand as in gradientMildSolutionData_of_data,
   replacing the hpos field; everything else forwards).  (b) is lighter.
7. hQuant(χ₀=0) assembly: uniform horizon δ(M) + frontier (same
   PicardRestartFrontier shape) → QuantitativeLocalExistence for the
   χ₀ = 0 sub-regime via the ThresholdQuantBridge pattern (no threshold,
   no persistence).
