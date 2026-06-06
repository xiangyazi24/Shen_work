# χ₀=0 ledger: the 3 remaining analytic residuals (drop-in specs)

VERIFIED 2026-06-06: paper2_theorem_1_1_chiZero_of_reduced_inputs and
Hu_of_restart are both axiom-clean ([propext, Classical.choice, Quot.sound]).
The χ₀=0 chain is intact; only these 3 frontier fields + the K1/K2 families
+ GATE instantiation remain. Each is INDEPENDENT and pickup-ready.

Consuming shapes (ShenWork/Paper2/IntervalDomainMildLocalChi0.lean:198-203):
  Hvsrc : DuhamelSourceTimeC1 (fun s k => (intervalNeumannResolverSourceCoeff p (D.u s) k).re)
  HsupNorm : IntervalDomainSupNormDerivativeNonposOn D.u (Set.Ioo 0 D.T)   [worker-3 owns: sliceMax mirror, ea07b42]
  Hvpos : ∀ t, 0<t→t<D.T→ ∀ x, 0 < mildChemicalConcentration p D.u t x

## Hvpos — elliptic STRICT positivity (spectral/Laplace route, NOT ODE)
mildChemicalConcentration p u t = intervalNeumannResolverR p (u t).
Atoms (all in ShenWork/PDE/IntervalResolverPositivity.lean):
- intervalNeumannResolverR_nonneg_of_nonneg_source (R ≥ 0; take its 4 hyps:
  f cont, f ≥ 0, cosineCoeffs f = resolverSourceCoeff.re, ℓ² — satisfiable:
  f = ν·u^γ, u>0 cont).
- laplaceHeatTrunc_tendsto: R(x) = lim_T ∫₀^T e^{−μt}·heatValue(t,f,x) dt.
- laplaceHeatTrunc_nonneg: each truncation ≥ 0 ⟹ truncations monotone ↑ in T
  ⟹ R(x) = sSup ≥ trunc(T₀)(x).
- STRICT: trunc(T₀)(x) > 0 because integrand g(t)=e^{−μt}H(t,x) is ≥0, cont
  on (0,T₀], and →f(x)>0 as t→0+ (intervalFullSemigroup_tendsto_id_at_zero,
  IntervalSemigroupApproxIdentity.lean:165 — needs ℓ¹ + HasSum reconstruction
  + kernel-cosine identity, all available: intervalCosineCoeff_summable_abs,
  intervalCosine_hasSum_pointwise from IntervalCosineInversion.lean,
  intervalNeumannFullKernel_cosineKernel_identity). g>f(x)/2 on (0,δ) ⟹
  ∫ pos via a positive-continuous-on-subinterval integral lemma (grep Mathlib
  intervalIntegral_pos / setIntegral_pos_of). Interior x first; endpoints
  x∈{0,1}: same Laplace rep holds at endpoints (cos(kπ·0/1) defined), the
  approx-identity is interior-only so endpoints need either (a) the source
  f>0 at endpoints + heat value strict-pos extends, or (b) named residual.
Target: ShenWork/Paper2/IntervalResolverStrictPositivity.lean, Hvpos_of_source.

## Hvsrc — power-source DuhamelSourceTimeC1 (mirror logistic M3)
Mirror ShenWork/Paper2/IntervalPicardLimitSourceData.lean limitSource_duhamelSourceTimeC1
for source ν·u^γ instead of logistic. Coefficient bridge resolverSourceCoeff.re
= cosineCoeffs(lift ν·u^γ); chain rule d/dσ(ν u^γ)=νγu^{γ−1}∂_σu (floor m for
rpow); H²ₙ decay via powerSource_intervalWeakH2Neumann (IntervalMildSourceDecayHelper)
+ IntervalSourceDecayQuantitative.intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound
with explicit B (νγ(γ−1)u^{γ−2}(u')²+νγu^{γ−1}u'', u^{γ−2}≤max(m,M)^{γ−2});
time-Leibniz cosineCoeffs_hasDerivAt_of_smooth_param. Assemble via
duhamelSourceTimeC1_of_H2Neumann_timeC1 (IntervalSemigroupNeumann.lean:828).
Target: ShenWork/Paper2/IntervalResolverSourceTimeC1.lean.

## hpde_u — spectral→pointwise PDE bridge (χ₀=0)
∂_t u = Δu + reaction at interior. ∂_t via G4i restartCosineSeries_hasDerivAt_time
(IntervalSourceCoefficientTimeC1.lean:719) on rep(u) (picardLimitRestart_general,
IntervalPicardLimitTimeNhd.lean): d/dτ Σ = Σ(a_k−λ_k c_k)cos. Δu = deriv²(lift)
= −Σλ_k c_k cos termwise (cosineCoeffSeries_grad2 machinery in
IntervalDuhamelClosedC2.lean; eigenvalue-summability restartDuhamelCoeff_eigenvalue_summable).
Σ a_k cos = L(u t)(x) via intervalCosine_hasSum_pointwise. tsum_sub (both
summable) ⟹ ∂_t u = L(u t) + Δu; rw hχ0 (χ₀ term=0); match reaction
u·(a−b u^α). Target: ShenWork/Paper2/IntervalPicardLimitPDE.lean.

## After all 3 + K1/K2 + GATE instantiation
ReducedLimitRegularityInputs fully built ⟹
paper2_theorem_1_1_chiZero_of_reduced_inputs gives Theorem_1_1(χ₀=0)
unconditionally. Then χ₀<0: extend the source with the IBP-conjugate flux
term (architecture in DESIGN_F2_CONSENSUS.md obstruction-2 resolution).
