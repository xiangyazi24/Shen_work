# CODEX SPEC — Paper 1 hcore FINITENESS via ROUTE B (r7): direct tent-weight classical energy estimate

## Why route B (route A walled)
r6 hit the route-A wall: there is NO whole-line mild/Duhamel representation for the GLUED global solution
(only per-segment fixed-point mild identities). Route B AVOIDS this — it estimates the KNOWN classical
solution directly (multiply the classical difference-PDE by a truncated weight, IBP, Gronwall, monotone
convergence). No semigroup theory, no Volterra, no transference, no mild representation. This is the paper's
actual §5 route (weighted energy on the classical solution) and is much shorter.

## Goal
Prove `paperWeightedCoreIntegrability`: for the whole-line global classical solution u (positive-time C²,
0≤u≤M) and wave U, the moving-frame error w = u(t,·+ct) − U has, for every t>0, the weighted integrabilities
`hclose` (∫e^{2ηz}|w|²<∞), `hWx2` (∫e^{2ηz}|w_z|²<∞), `hdiff_int`, `hrem_int`, and `hhalf` — i.e. the
`coreIntegrability` inputs of `paper5WeightedEnergy_deriv_le_concrete_of_coreIntegrability`. NO
sorry/admit/custom axiom.

## Reuse (committed, by exact name)
- r5 `weighted_resolver_L2eta_bounded`, `weighted_resolver_gradient_L2eta_bounded`,
  `weighted_frozenElliptic_gradient_difference_L2eta_bounded` (Theorem12WeightedResolverEta.lean).
- Classical solution: `wholeLineCauchyGlobal_isGlobalClassicalSolution`, its positive-time C² (spatial second
  deriv), `wholeLineCauchyGlobal_le_stableCeiling`, `wholeLineCauchyGlobalV = frozenElliptic`.

## The DAG (ChatGPT Q4994, source arxiv 2605.04401 §5)
A. Weight geometry — CRACKED (Fable): use the ELEMENTARY LOGISTIC EXHAUSTION (no cutoff, no mollifier):
   `capWeight η R z := Real.exp (2*η*z) / (1 + Real.exp (2*η*(z - R)))`.
   Its derivative is EXACT and elementary: with f=exp(2ηz), g=1+exp(2η(z−R)), capWeight=f/g and
   `deriv (capWeight η R) z = 2*η * capWeight η R z / (1 + Real.exp (2*η*(z-R)))` (because f'g−fg' = 2ηf·(g −
   exp(2η(z−R))) = 2ηf, since g − exp(2η(z−R)) = 1). Prove these lemmas (all elementary calculus, use HasDerivAt
   for exp/div — NO mollifier, NO smoothTransition, NO compact support):
   - `capWeight_pos`: 0 < capWeight η R z.
   - `capWeight_le_full`: capWeight η R z ≤ Real.exp (2*η*z)  (denom ≥ 1).
   - `capWeight_le_plateau`: capWeight η R z ≤ Real.exp (2*η*R)  (⟺ exp(2η(z−R)) ≤ 1+exp(2η(z−R))).
   - `capWeight_mono_R`: R ↦ capWeight η R z is monotone increasing (∂_R > 0).
   - `capWeight_tendsto_full`: `Tendsto (fun R => capWeight η R z) atTop (𝓝 (Real.exp (2*η*z)))` (denom→1).
   - `capWeight_hasDerivAt`: HasDerivAt (capWeight η R) (2*η*capWeight η R z/(1+exp(2η(z−R)))) z.
   - `capWeight_abs_deriv_le`: |deriv (capWeight η R) z| ≤ 2*η * capWeight η R z  (since 1/(1+exp)∈(0,1]).
     This is the MODERATE bound, holding on the WHOLE line — the crux. (η>0 assumed; for η<0 not needed.)
   - `capWeight_abs_secondDeriv_le`: |deriv² (capWeight η R) z| ≤ 6*η² * capWeight η R z (differentiate again;
     bounded since the extra factors are all in (0,1] up to constants).
   Integrals ∫ capWeight·w² are finite for each fixed R because capWeight ≤ exp(2ηz) (decays as z→−∞) and
   capWeight ≤ exp(2ηR) (bounded), with w∈L² on the right tail from `HasWaveRightTailAsymptotic`
   (|u−U| ≤ 2e^{−κz} eventually) — NO tail assumption beyond that repo lemma.

B. Scalar nonlinearities — `rpow_sub_abs_le_on_Icc` (|a^p−b^p|≤p M^{p−1}|a−b| on [0,M], p∈{m,γ,α}),
   `logisticReaction_sub_abs_le`, `fluxDifference_decomposition` (u^m v_z − U^m V_z split into terms each
   bounded by |w| or |w_z| times bounded coeffs).
C. Resolver — reuse r5's committed bounds (weighted resolver on L²_η, moderate).
D. Classical energy (the core) — `differencePDE_divergence` (w solves w_t = w_zz + c w_z − χ∂_z(flux diff) +
   (reaction diff), in DIVERGENCE form, from the physical PDE of u minus the wave eq of U — carry U's
   IsTravelingWave + regularity + tail); `tentWeightedEnergy_identity` (d/dt ½∫φ_R w² = ∫φ_R w w_t, then IBP
   all finite since φ_R compact support); `tentWeightedEnergy_inequality` (≤ C_M,η ∫φ_R w² + C ∫φ_R w_z² ...,
   the φ_R' terms bounded by 2η, resolver term by C via reuse, absorb ∫φ_R w_z² using the diffusion −∫φ_R w_zz w
   = ∫φ_R w_z² + ...); `tentWeightedEnergy_gronwall` (E_R(t) ≤ E_R(0)e^{Ct}, C independent of R).
E. Limit — `tentEnergy_mono_limit` (∫φ_R w² ↑ ∫e^{2ηz}w² by monotone convergence), `fullWeightedL2_finite`
   (E(t) ≤ E(0)e^{Ct} < ∞, using E_R(0) ≤ E(0) < ∞ from initial closeness), similarly the gradient +
   resolver integrabilities, then assemble `paperWeightedCoreIntegrability`. NO annular cutoff error survives
   because C is R-independent and the limit is monotone.

## Constraints
- New file `ShenWork/Paper1/Theorem12TentWeightFiniteness.lean`. Do NOT edit Statements.lean /
  WholeLineCauchyGlobalBounds / StableCeilingPDE / Theorem12WeightedAPrioriPropagation / the r5/r6 files.
- **NO git** (only write .lean); orchestrator commits.
- Verify with `env LAKE_NO_UPDATE=1 lake env lean <file>` AND `lake build ShenWork.Paper1.Theorem12TentWeightFiniteness`
  (MODULE build). No full-tree build.
- No sorry/admit/native_decide/custom axiom. ≤100 cols. Reuse committed lemmas by exact name.
- If a sub-step walls, STOP + report precise goal file:line + missing fact. Do NOT fake.

## Report
Theorem names + `#print axioms`, which of A–E closed, whether `paperWeightedCoreIntegrability` (all the
coreIntegrability inputs) is now unconditional for the global classical solution, or the precise residual.
