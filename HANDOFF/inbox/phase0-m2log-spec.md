# Phase-0 / M2-logistic spec: explicit W^{2,1} bound for the logistic source

Target file (NEW, sole writer): ShenWork/PDE/IntervalLogisticSourceQuantBound.lean

## Goal
Quantitative version of `logisticSourceFun_intervalWeakH2Neumann`'s L¹ bound:
for `g : ℝ → ℝ` with `ContDiff ℝ 2 g`, `0 < g ≤ M` on `[0,1]`,
`|deriv g| ≤ G1` and `|deriv (deriv g)| ≤ G2` on `[0,1]`, `1 ≤ α`, `0 ≤ a`, `0 ≤ b`:

  ∫₀¹ |deriv (deriv (logisticSourceFun a b α g)) x| dx
    ≤ B_log a b α M G1 G2
  where B_log := b*α*(1+α)*M^(α-1)*G1^2 + (a + b*(1+α)*M^α)*G2

(or any explicit closed form ≤-equivalent; the POINT is explicitness in
(a,b,α,M,G1,G2) — no existentials). Then the corollary via
ShenWork.IntervalSourceDecayQuantitative.intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound:

  ∀ k ≥ 1, |cosineCoeffs (logisticSourceFun a b α g) k|
            ≤ 2 * B_log … / ((k:ℝ)*π)²

## Chain rule facts
L(z) = z*(a − b*z^α): L'(z) = a − b*(1+α)*z^α, L''(z) = −b*α*(1+α)*z^(α−1)
(careful: Real.rpow for z > 0; the repo's logisticSourceFun and its
contDiffOn lemmas live in ShenWork/Paper2/IntervalMildPicardRegularity.lean
lines 72–280 — REUSE their differentiability lemmas, do not re-derive
positivity domains). (L∘g)'' = L''(g)·(g')² + L'(g)·g''.

## Constraints
- 0 sorry / 0 admit / 0 axiom / 0 native_decide.
- New file only; do NOT edit any existing file.
- Verify: ssh uisai1 'cd ~/repos/shen_work && export PATH=$HOME/.elan/bin:$PATH && lake env lean ShenWork/PDE/IntervalLogisticSourceQuantBound.lean' must exit 0.
  (Check `pgrep -f "lake build"` first; lake env lean is safe alongside builds.)
- If the exact statement proves awkward, weaker-but-explicit B is acceptable
  (e.g. coarser polynomial); report exactly what you proved.
