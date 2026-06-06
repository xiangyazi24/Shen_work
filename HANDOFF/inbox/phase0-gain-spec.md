# Phase-0 / M-gate-1 spec: quantitative parabolic gains for Duhamel coefficient sums

Target file (NEW, sole writer): ShenWork/PDE/IntervalDuhamelQuantGain.lean
Import: ShenWork.PDE.IntervalDuhamelClosedC2 (has duhamelSpectralCoeff,
unitIntervalCosineEigenvalue λₖ = ((k:ℝ)·π)², DuhamelSourceTimeC1).

## Context
R2′ Phase-0 gate (DESIGN_F2_CONSENSUS.md): the iterate G2-recursion
G2_{n+1}(t) ≤ C(t)·M + gain(τ)·B_log(M, G1_n, G2_n) closes n-uniformly only
because the eigenvalue-weighted Duhamel sum carries a small factor τ^{1/4}.
This module supplies the three explicit estimates.

## Statements (explicit constants; no existentials)

Given a : ℝ → ℕ → ℝ, τ B : ℝ, hτ : 0 < τ, hB : 0 ≤ B,
hdecay : ∀ σ, 0 ≤ σ → ∀ k : ℕ, 1 ≤ k → |a σ k| ≤ 2*B/((k:ℝ)*Real.pi)^2,
hcont : ∀ k, Continuous (fun σ => a σ k)   -- for integrability; adjust as needed

(i) Per-mode bound (k ≥ 1):
  |duhamelSpectralCoeff a τ k| ≤ (2*B/((k:ℝ)*π)^2) * min τ (1/((k:ℝ)*π)^2)
  Proof: |∫₀^τ e^{−(τ−σ)λ}a| ≤ (2B/(kπ)²)·∫₀^τ e^{−(τ−σ)λ}dσ and
  ∫₀^τ e^{−(τ−σ)λ}dσ = (1−e^{−τλ})/λ ≤ min(τ, 1/λ).

(ii) λ-weighted sum with τ^{1/4} gain (the G2 estimate):
  ∑' k : ℕ, unitIntervalCosineEigenvalue k * |duhamelSpectralCoeff a τ k|
    ≤ (2 * (∑' k : ℕ, 1/((k:ℝ)+1)^((3:ℝ)/2)) / Real.pi^((3:ℝ)/2))
        * τ^((1:ℝ)/4) * B
  (Any explicit constant of this shape is fine; reindexing k≥1 via k+1 is
  acceptable. Key inequality: λₖ·|bₖ| ≤ 2B·min(τ·λₖ, 1)/((kπ)²·λₖ)·λₖ
  = 2B/(kπ)²·min(τλₖ,1) and min(x,y) ≤ x^{1/4}·y^{3/4} for x,y ≥ 0, giving
  per-mode 2B·(τλₖ)^{1/4}/(kπ)² = 2B·τ^{1/4}/( (kπ)^{3/2} ).
  Note λ₀ = 0 so k=0 contributes 0 to the sum.
  Summability: p-series 3/2 > 1 (Real.summable_one_div_nat_rpow or
  Real.summable_nat_rpow_inv).

(iii) √λ-weighted sum, τ-free (the G1 estimate):
  ∑' k : ℕ, Real.sqrt (unitIntervalCosineEigenvalue k) * |duhamelSpectralCoeff a τ k|
    ≤ (2 * (∑' k : ℕ, 1/((k:ℝ)+1)^(3:ℕ)) / Real.pi^3) * B
  (per-mode: √λₖ·|bₖ| ≤ 2B/(kπ)²·√λₖ·(1/λₖ) = 2B/((kπ)³).)

## Constraints
- 0 sorry/admit/axiom/native_decide. New file only; do not edit existing files.
- Verify: scp the file to uisai1:~/repos/shen_work/ShenWork/PDE/ then
  ssh uisai1 'cd ~/repos/shen_work && export PATH=$HOME/.elan/bin:$PATH &&
  lake env lean ShenWork/PDE/IntervalDuhamelQuantGain.lean' → exit 0.
  Do NOT run lake build. If an import olean is missing, produce it with
  lake env lean -o (as the M2-logistic agent did).
- If exact constants get awkward, coarser explicit constants are fine;
  report honestly. min(x,y) ≤ x^θ y^{1−θ}: prove via
  min ≤ x, min ≤ y, min = min^θ·min^{1−θ} (Real.rpow algebra), or any route.
- When green: git add ONLY your file, commit
  "Phase-0 M-gate-1: quantitative parabolic gains (tau^{1/4} G2, tau-free G1)",
  push uisai1 main. Another session works concurrently — never git add -A.
