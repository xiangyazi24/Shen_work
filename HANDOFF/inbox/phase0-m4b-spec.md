# Phase-0 / M4b spec: BREAK THE CIRCLE — weak-hypothesis ★ + limit envelope

## The circle (why this module exists)
M4's ★ (picardLimitRestart_cosineIdentity, ShenWork/Paper2/
IntervalPicardLimitRestart.lean) consumes hsrc0 : DuhamelSourceTimeC1 of the
LIMIT's source family. But producing that for the limit needs K1(u) (M3b)
which needs rep(u) = ★ itself. Circular.

## The break
DuhamelSourceTimeC1's σ-DERIVATIVE fields are NOT needed for ★'s pipeline:
- duhamelSpectral_eq_cosineSeries (IntervalDuhamelClosedC2.lean:1393) uses
  only src.henv_summable, src.henv_bound, and continuity of σ ↦ a σ n
  (derived there FROM hderiv, but continuity alone suffices — read its proof).
- The other hsrc0 uses in M1/M4's pipeline (abs_duhamelSpectralCoeff_le,
  duhamelSpectralCoeff_halfstep_split — in ShenWork/Paper2/
  IntervalPicardIterateRestart.lean) need only envelope + continuity
  (integrability). VERIFY by reading each use.

## Deliverables (target file, NEW, sole writer:
ShenWork/Paper2/IntervalPicardLimitRestartWeak.lean)

1. Define the weak source package:
   structure DuhamelSourceL1Cont (a : ℝ → ℕ → ℝ) where
     envelope; henv_summable; henv_bound (∀ s, 0 ≤ s → ∀ n, |a s n| ≤ envelope n);
     hcont : ∀ n, Continuous (fun s => a s n)
   plus the forgetful map DuhamelSourceTimeC1 → DuhamelSourceL1Cont.
2. Weak variants of the three pipeline lemmas (PREFERRED: re-prove thin
   wrappers calling the existing proofs' internal structure where possible;
   else copy the ≤60-line proofs adapting hderiv-uses to hcont):
   - duhamelSpectral_eq_cosineSeries_weak (src : DuhamelSourceL1Cont a)
   - the coefficient-bound and halfstep-split lemmas from M1's file in weak
     form (check their exact names/shapes in IntervalPicardIterateRestart.lean
     — if they already only need continuity+envelope, re-export).
3. ★-weak: picardLimitRestart_cosineIdentity_weak — same statement as M4's ★
   but hsrc0 replaced by DuhamelSourceL1Cont. (Adapt M4's proof; it should go
   through with the weak lemmas.)
4. The limit's weak package from n-uniform iterate data:
   theorem limitSource_l1cont — hypotheses (named, satisfiable):
   (a) per-n envelopes: ∀ n σ k(≥1), |cosineCoeffs(L(picardIter n σ)) k| ≤
       Benv/(kπ)² and zeroth ≤ Benv0 (M-final's Data via M3's envelope);
   (b) pointwise convergence cosineCoeffs(L(u_n σ)) k → cosineCoeffs(L(u σ)) k
       (take as hypothesis in the cleanest form, OR prove from uniform
       slice convergence + logistic Lipschitz + interval-integral dominated
       convergence — try to prove it: u_n → u uniformly on slices is
       available from IntervalMildPicard's geometric machinery; READ what
       exact uniform-convergence statements exist (picardIter_*, picardLimit_*);
       L Lipschitz on the ball: grep IntervalLogisticLipschitz);
   (c) continuity of σ ↦ cosineCoeffs(L(u σ)) k: from HasContinuousSlices of
       the limit + L continuity + integral continuity (dominated convergence /
       continuous_of... — or take as named satisfiable hypothesis if heavy).
   Conclusion: DuhamelSourceL1Cont (fun σ k => cosineCoeffs (logisticLifted p (u σ)) k)
   with envelope k := Benv-form (le_of_tendsto passes per-n bounds to the limit).
5. Corollary: ★ for the limit with NO source hypothesis beyond the n-uniform
   iterate data + mild-solution facts — the circle is broken. Then K1(u) via
   M3b (ShenWork/Paper2/IntervalPicardIterateTimeC1.lean) and H2(u) via M3
   become forward derivations (leave as a wiring corollary or named follow-up
   if time-boxed; the priority is 1-4).

## Constraints
Standard set: new file only; scp + ssh uisai1 'cd ~/repos/shen_work && export
PATH=$HOME/.elan/bin:$PATH && lake env lean <file>' loop (NEVER lake build;
oleans via lake env lean -o); 0 sorry/admit/axiom/native_decide; honest-partial
named hypotheses allowed (header justification); #print axioms = 3 standard;
commit ONLY your file "Phase-0 M4b: weak-hypothesis limit restart (circle
broken)"; push uisai1 main (untracked-copy dance; concurrent sessions/agents).
Pitfalls: set/beta; HO-unification (g:=)(f:=); positivity vs defs; renames
lt_or_le→lt_or_ge, le_or_lt→le_or_gt, tsum_le_tsum→Summable.tsum_le_tsum;
rw [defName]→simp only; le_of_tendsto for limit bounds; grep Mathlib names
before relying (tendsto_integral / intervalIntegral dominated convergence).
