# PDE Framework Blueprint — fresh C⁰/A^r design ⟷ existing framework ⟷ Shen's actual method

Purpose (Xiang 2026-06-19): treat the from-scratch C⁰/A^r design (Layers 1–7, designed via ChatGPT this
session) as an INDEPENDENT AUDIT of the existing bounded-domain PDE framework (ShenWork/PDE/ + Paper2/Interval*).
Per layer: ① AGREE (validates the framework) ② THEY HAVE MORE (I should learn/reuse) ③ I MAY ADD (赚到 —
to verify). "按图索骥": this is the map.

## Central thesis — THREE independent derivations CONVERGE
1. **Fresh design** (this session, ChatGPT): C⁰ physical-mild on BoundedContinuousFunction + A^r=weighted-ℓ¹
   Fourier regularity engine; local existence via Banach/Schauder on the divergence-form Duhamel map.
2. **Shen's actual method** (回归原著, paper1.pdf §4.2 eq 3.1 + paper2): parabolic Cauchy problem, CONSTANT
   sub/super-solutions + parabolic comparison, DIVERGENCE-form mild representation
   `U(t)=e^{(Δ−I)t}u0 − χ∫e^{(Δ−I)(t−s)}∂x(U^m V_x)ds + ∫e^{(Δ−I)(t−s)}U(2−U^α)ds`, Schauder fixed-point.
3. **Existing framework**: IntervalGradientDuhamelMap (divergence mild, ∂x on S, √T) + IntervalDomainMaxPrinciple
   + IntervalDomainExistence (Schauder/Banach) + EigenL1/FractionalPowerSpace + IntervalDomainMoserClosure.

All three are the SAME parabolic-mild-Schauder engine. This validates the existing framework (Xiang's "如果
差不多说明框架不错"). **KEY COROLLARY:** Paper 1 (whole-line wave) and Paper 2 (bounded domain) existence are
ONE engine on two domains. The discrete-Rothe per-step reframing (Paper1/WavePaperRothe*) — and its m<2 cusp —
is an OVER-DECOMPOSITION ARTIFACT that does NOT appear in Shen's proof (see docs/paper1-mlt2-cusp-obstruction.md).

## Layer-by-layer reconciliation

### L1 — heat semigroup + resolvent
- ① AGREE: `intervalFullSemigroupOperator` + the √t gradient estimate `..._deriv_Linfty_pointwise_sqrt_t` (T1)
  = my `E_phys` + `‖∂xE(t)f‖∞≤Ct^{-1/2}`; heat positivity; `intervalNeumannResolverR` + R''=Rf−f = my positive
  Green's-fn resolvent; resolver positivity `intervalNeumannResolverR_nonneg` (O1) = my designed positivity.
- ② THEY HAVE MORE: sectorial/analytic semigroup (`ShiftedNeumannCoefficientAnalyticSemigroup`,
  AnalyticSemigroupDecay/Gen/Physical), HeatKernelLpEstimates, the full Neumann conjugate kernel + mass
  conservation, the C¹ resolver weak bundle (IntervalResolverWeakBounds). My design DEFERRED sectorial.
- ③ I MAY ADD: explicit even-2-periodic Gaussian-conv as the PRIMARY semigroup def (they use cosine-spectral
  primary). Cosmetic; convergent.

### L2 — C⁰ mild local existence (the existence engine, = Shen §4.2)
- ① AGREE (STRONG): `intervalGradientDuhamelMap` (divergence form, ∂x INSIDE S, √T contraction via
  `gradDuhamel_sup_bound` + `exists_small_contraction_time`) + `IntervalMildSolution` + `IntervalDomainExistence`
  (closed-ball Banach FP) = my L2 Duhamel map = Shen's eq 3.1 mild representation. Both use CLAMP (not a-priori
  positivity) at the foundation. ContractingWith on a closed ball.
- ② THEY HAVE MORE: Atoms B/C/D + O1 + glue1/glue2 DONE (resolver C⁰→C¹ bundle, chemFlux Lipschitz, the √T
  gradient/value bounds, contraction-time). Remaining (T7e): Atom A (weighted complete mild metric space) + E/F
  (Banach→IntervalMildSolution) + the regularity bridge toClassical.
- ③ I MAY ADD: nothing new at L2 — full convergence; my design re-derived their engine.

### L3 — A^r smoothing / regularity bootstrap
- ① AGREE: `EigenL1` (MemEig/eigNorm = weighted-ℓ¹ over the cosine eigenvalues) = my A^r; FractionalPowerSpace
  / FractionalPowerDerivative = my fractional regularity; the T6/T7 Duhamel-C² regularity bootstrap = my smoothing
  bootstrap → classical.
- ② THEY HAVE MORE: GagliardoNirenberg, the explicit T6 atom `intervalDuhamelTerm_closedC2_of_timeC1_source`
  (∂xx of the singular Duhamel via time-IBP), F1ProbeFractionalMultiplier/Smoothing.
- ③ I MAY ADD (TO VERIFY): the explicit Duhamel-gain SPLIT (reaction gains <2, transport gains <1 because of the
  one ∂x) + the m<2 integrability boundary; the time-weighted A^σ SEED lemma (C⁰→A^σ via restart fixed-point,
  since C⁰→A^0 is non-integrable); the A^r Banach-algebra product estimate. If these aren't already explicit in
  the framework, they are candidate contributions to the regularity story. (Verify against
  IntervalCoupledRegularityBootstrap before claiming.)

### L4 — positivity / comparison / SMP
- ① AGREE: `IntervalDomainMaxPrinciple` + `IntervalDomainSupNormMaxPrinciple` + O1 positivity + the L2 energy
  negative-part method = my L4 (u≥0/u≤M by energy testing; strong positivity on the slab).
- ② THEY HAVE MORE: the full max-principle infra + energy combine (IntervalDomainL2UEnergy*).
- ③ I MAY ADD: the explicit "comparison on the STRICT-POSITIVE slab where s^{m-1} is locally Lipschitz" framing
  — directly tied to the m<2 cusp resolution (the cusp only bites where iterates touch 0; on a strict-positive
  slab it's gone). This reframing is the conceptual bridge that explains WHY Shen's parabolic comparison avoids
  the cusp.

### L5/6 — global boundedness / Moser
- ① AGREE: `GlobalBound` + `IntervalDomainMoserClosure` (the Lp→L∞ Moser chain) + GagliardoNirenberg = my L5/6.
- ② THEY HAVE MORE: the full Moser iteration chain (`all_exponents_of_moser_iteration_chain`,
  `boundedBefore_of_moser_iteration_chain_and_GN_Agmon_frontier`), the regime split, the cross-diffusion bootstrap.
- ③ I MAY ADD: the explicit logistic-comparison super-solution route for the χ≤0 / small-χ regime (compare with
  the ODE u'=au−bu^{1+α}, bound by max(u0,(a/b)^{1/α})) as the TRACTABLE first unconditional global theorem,
  before the full Moser machinery. (Verify whether the framework already has this χ≤0 shortcut.)

### L7 — compactness
- ① AGREE: a-priori parabolic estimates + diagonal argument (Shen Claim 1) — the framework's compactness route.
- ② THEY HAVE: the diagonal-argument compactness in IntervalDomainExistence.
- ③ I MAY ADD (TO VERIFY — the strongest 赚到 candidate): A^r-TAIL compactness as a clean Aubin-Lions/Rellich
  REPLACEMENT — `‖P_{>N}a‖_{A^r} ≤ (1+N)^{-δ}‖a‖_{A^{r+δ}}` (weighted-ℓ¹ tail criterion) + finite-mode
  precompactness ⟹ total boundedness, with `A^r↪C^0`. This may be a cleaner, more reusable compactness engine
  than the diagonal argument, and directly supports ω-limit / long-time (Paper 3). Verify it isn't already
  present before claiming.

## 按图索骥 — recommended next steps
1. **Paper 1 pivot (pending Xiang's nod):** drop the discrete-Rothe core (artifact); the faithful route =
   parabolic-mild-Schauder = REUSE the existing engine (IntervalGradientDuhamelMap + max principle + Schauder)
   on the whole line. Barriers already in `PDE/TravelingWaveConstruction.lean` (cappedExp, logisticProfile).
   Recyclable from the Rothe work: the ExpLeftRate machinery, the barrier facts, possibly McShane (for the
   whole-line Schauder compactness if needed). The weighted cusp lemma (00b1197) becomes unnecessary for the
   core (no W≤Z) — keep as a utility.
2. **Paper 2 finish (the closest headline):** Atom A (weighted complete mild metric space) + E/F (Banach→
   IntervalMildSolution) + toClassical → discharges F1/F2 (T7e/T8) → Theorem 1.1 unconditional. No worker
   currently on it (Xiang confirmed). This is the nearest playbook-Layer-3 win.
3. **Verify the ③ candidate additions** (A^r-tail compactness, A^σ seed, m<2 Duhamel split, logistic-comparison
   global, strict-positive-slab comparison) against the framework before claiming them as contributions —
   honest "赚到" only if genuinely absent. Whatever is genuinely new, land as a clean addition.

## Verdict
The fresh design is NOT redundant waste — as an audit it CONFIRMS the existing framework is the right one (it
independently re-derived the same parabolic-mild-Schauder engine that Shen actually uses), and it surfaced a
real structural correction (Paper 1's discrete-Rothe cusp is an artifact; the faithful route is the existing
engine). Candidate additions (③) are flagged for verification. The framework is sound; the map is drawn.
