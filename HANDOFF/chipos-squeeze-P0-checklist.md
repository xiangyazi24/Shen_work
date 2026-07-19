# χ>0 Squeeze — P0 integration checklist (from Q84 adversarial audit, verified)

Engine verdict: chiPos_squeeze_gap_step CORRECT + NON-VACUOUS (witness: m=γ=α=1, χ=1/4,
ℓ=1/4→33/50, M=2→28/25, δ=1/200). Index placement correct (floor vs OLD ceiling M,
ceiling vs NEW floor ℓ'; sequential floor-first round). Sharp variant landed:
chiPos_squeeze_gap_step_sharp with ratio χ/(1−χ) (< 2χ throughout χ<1/2).

Before wiring into the round induction, the STEP theorem must enforce:

P0-1  b^m/a^m-weighted contact comparison (NOT the constant-defect wrapper).
      Constant defect χM^m(M^γ−ℓ^γ) is unsatisfiable from tiny floors (m=1 burn-in).
      Already specified: codex-brief-chipos-impl2.md item 0.

P0-2  δ = δ(ε) per requested ε (finitely many rounds per ε), or δ_n → 0.
      A fixed δ only proves entry into radius 2δ/(1−2χ) (sharp: 2δ/(1−2χ)→δ·2/(1−χ)... 
      recompute with sharp ratio: radius 2δ/((1−χ)−χ) = 2δ/(1−2χ) — same radius).
      The final UniformConvergesToConstant quantifier must pick δ(ε) BEFORE the induction.

P0-3  δ is the NORMALIZED per-capita residual (after dividing the contact inequality by
      the positive contact value). Explicit conversion lemma needed:
      raw PDE defect / barrier finite-time miss  →  normalized residual δ.

P0-4  Side-of-root state invariant: the round targets must satisfy BOTH
      0 ≤ F_M(ℓ') ≤ δ  and  0 ≤ C_ℓ'(M') ≤ δ
      (F_M(x) = 1−x^α−χx^{m−1}(M^γ−x^γ); C_ℓ(y) = y^α−1−χy^{m−1}(y^γ−ℓ^γ) normalized).
      The ≥0 side is what makes the barriers reachable (floor increasing / ceiling
      decreasing); the ≤δ side is what feeds the contraction engine.

Verification gate for Codex phase 2 output: check all four before accepting the round
induction. If phase 2 shipped constant-defect wrappers only, refactor to weighted before
assembly.
