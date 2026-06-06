# Phase-0 / M4 spec: limit pass — restart representation of the Picard LIMIT

Target file (NEW, sole writer): ShenWork/Paper2/IntervalPicardLimitRestart.lean

## KEY SIMPLIFICATION (do it this way — S5/G2.5 derivative-convergence BYPASSED)

Do NOT chase uniform convergence of σ-derivative sequences. Order:

(1) **rep(u) by coefficient limit.** u := the Picard limit/mild solution
   (fixed point of intervalGradientDuhamelMap, χ₀=0; the iterates
   u_n → u UNIFORMLY on slices — the geometric machinery is
   picardIter_geometric / picardLimit_* in ShenWork/Paper2/IntervalMildPicard.lean,
   READ what uniform-convergence statements exist).
   From M1's per-iterate identity (IntervalPicardIterateRestart.lean)
   lift(u_{n+1}(t)) = ∑'k restartDuhamelCoeff (coeffs of u_{n+1}(t/2))
                       (source-coeffs of L(u_n)) (t/2) k · cos k x  on Icc:
   pass n → ∞ termwise:
   - cosineCoeffs(lift(u_{n+1}(t/2))) k → cosineCoeffs(lift(u(t/2))) k:
     coefficient functional = 0..1 interval integral of (cos·lift); uniform
     convergence of u_n(t/2) → u(t/2) on the compact slice ⟹ integral
     converges (intervalIntegral.tendsto / dominated convergence — uniform
     bound M exists).
   - source coefficients cosineCoeffs(L(u_n s)) k → cosineCoeffs(L(u s)) k:
     L is Lipschitz on the ball (the contraction machinery has the logistic
     Lipschitz lemma — ShenWork.IntervalLogisticLipschitz
     intervalLogisticReaction_lipschitz_on_bounded or similar; uniform
     convergence transfers through L then through the integral).
   - duhamelSpectralCoeff of the source families converges per-mode:
     dominated convergence in the σ-integral (n-uniform envelope
     |a_n(σ,k)| ≤ Benv/(kπ)²-form as hypothesis).
   - the SERIES passes to the limit: dominated convergence of the tsum
     (n-uniform summable majorant: |restart coeff| ≤ e^{−τλ}·2M + envelope-form;
     use Mathlib tsum dominated convergence — tendsto_tsum_of_dominated... grep
     for `tendsto_tsum` / use Summable + termwise + uniform majorant route:
     e.g. `tendsto_tsum_of_dominated_convergence` exists in some form; if name
     roulette fails, prove via HasSum/uniform tail bounds manually — the
     majorant is geometric-grade, tails are uniform).
   - LHS: lift(u_{n+1}(t)) x → lift(u(t)) x pointwise (uniform convergence).
   ⟹ Set.EqOn (lift (u t)) (restart series of u's own data) (Icc 0 1):
   the mild solution satisfies its OWN half-step restart cosine identity. ★
(2) **C²/G1/G2 for u's slices from rep(u)**: the series with n-uniform-inherited
   envelope bounds (coefficients' bounds pass to limits by le_of_tendsto)
   + M2-uniform abstract lemmas (cosineSeries_abs_deriv_le_sqrtEig_tsum etc.,
   ShenWork/Paper2/IntervalPicardIterateC2Bound.lean) + the existing series-C²
   machinery (restartDuhamelCoeffSeries_contDiff_two etc.).
(3) **K1(u)** via M3b (IntervalPicardIterateTimeC1.lean) applied to rep(u). 
(4) **H2(u) = DuhamelSourceTimeC1 of u's source family** via M3
   (IntervalPicardIterateSourceC1.lean) from K1(u)+K2(u).
   ⚠ watch the order: M3's conclusion is about the family
   (s,k) ↦ cosineCoeffs(logisticLifted p (… s)) — for the LIMIT u replace
   picardIter by u's slices; M3's statement is for picardIter specifically?
   READ IT — if it's iterate-specific, either generalize by copying its proof
   shape for an abstract w (it factors through logisticSourceFun lemmas that
   are already abstract) or take the abstract-profile variant in M3b's style.
(5) **Assemble** GradientMildHalfStepRestartData-shape data for u (a₀ from
   step 1's extraction, a from step 4, hagree from step 1 ★) — match the
   EXACT field shapes of GradientMildHalfStepRestartData
   (ShenWork/Paper2/IntervalMildRegularityBootstrap.lean:422). Output ONE
   theorem producing it under named hypotheses (n-uniform Data fields from
   M-final's PicardIterateUniformData + GATE + the convergence facts that
   IntervalMildPicard already provides).

PRIORITIZE step (1) — it is the genuinely new limit-pass content. Steps
(2)-(5) may be landed as named satisfiable hypotheses/follow-up corollaries
if time-boxed out (honest-partial), but step (1)'s ★ identity must be
genuinely proved.

## Constraints
Standard: new file; scp + ssh uisai1 lake env lean loop (NEVER lake build;
oleans via lake env lean -o); 0 sorry/admit/axiom/native_decide; #print
axioms = 3 standard; named satisfiable hypotheses allowed with header
justification; commit ONLY your file "Phase-0 M4: restart representation of
the Picard limit (coefficient limit pass)"; push uisai1 main (untracked-copy
dance). Pitfalls: set/beta; HO-unification (g:=)(f:=); positivity vs defs;
renames lt_or_le→lt_or_ge, le_or_lt→le_or_gt, tsum_le_tsum→Summable.tsum_le_tsum;
rw [defName]→simp only; grep Mathlib for limit-interchange lemma names before
relying on them.
