# R-src0F-2 design: weighted-norm iterate induction (2026-06-10 ~12:50)

SURVEY VERDICT (kernel-smoothing route, see agent report):
- First derivative: package-free chain COMPLETE — T1 kernel gradient
  |∂ₓS(τ)f| ≤ (1/√π)τ^{-1/2}sup|f| (IntervalFullKernelGradientLinfty:490) +
  Atom D |∂ₓ∫S·g| ≤ C·2√t·sup|g| (IntervalGradDuhamelBound:72) + restart
  identity assembly (components exist, single naming lemma missing).
- Second derivative: NO kernel ∂ₓₓ bound exists anywhere; every C² in the
  repo flows through the source-decay package; source decay flows through
  C². The C¹-only bootstrap gives 1/k source decay — misses summability
  by exactly one power.

THE HONEST ROUTE — classical parabolic weighted bootstrap over iterates:
Induct over Picard iterates n in the WEIGHTED norms
  R₁(n) := sup_{σ∈(0,T]} σ^{1/2}·sup_x |∂ₓ lift(uₙ σ)(x)|
  R₂(n) := sup_{σ∈(0,T]} σ·sup_x |∂ₓₓ lift(uₙ σ)(x)|   (weights TBC)
Step n→n+1 via the t/2 restart (IntervalPicardIterateC2Bound's explicit
iterate_abs_deriv_le / deriv2_le):
  σ^{1/2}G₁(n+1,σ) ≤ σ^{1/2}·2M·sqrtEigExpWeight(σ/2) [≈ 2√2·M·univ-const]
    + σ^{1/2}·C₁·B_log(M, G₁(n,·), G₂(n,·) on [σ/2,T])
with the shifted source supported on s ≥ σ/2 where G₁(n,s) ≤ R₁(n)·s^{-1/2}
⟹ G₁(n,s)² ≤ R₁²·(2/σ), and the Duhamel factor √σ absorbs it:
  σ^{1/2}·√σ·(2/σ)·R₁² = 2R₁² — APPEARS UNDAMPED: need either the
  contraction-horizon smallness (T ≤ T₀ from the cone construction gives the
  Duhamel constant an extra T^θ?) or e^{-λσ/2}-weights — AUDIT NEEDED.
Closure: R(n+1) ≤ A + ε(T)·(R(n)² + R(n)) with ε(T)→0 as T→0 ⟹ all
iterates in a fixed ball for the Picard horizon ⟹ n-uniform window K2
⟹ n-uniform source envelope (B_log) ⟹ R-src0F-2 via le_of_tendsto
(bootstrap producer, already wired).
Fallback if the quadratic term is genuinely undamped at fixed T: restrict
to the cone-construction δ-horizon (the consumers construct D with their own
δ anyway — check whether reducedLimitRegularityInputs_of_picard's D always
comes from coneGradientMildSolutionData_exists with small δ).
