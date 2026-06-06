# Phase-0 / M3 spec: iterate source time-C¹ induction step (χ₀=0)

Target file (NEW, sole writer): ShenWork/Paper2/IntervalPicardIterateSourceC1.lean

## Goal
The induction step that discharges M1's hypothesis H2 at the next level:
GIVEN that the iterate slice u_n := picardIter p u₀ n has a restart cosine
representation with quantitative data, DERIVE
  DuhamelSourceTimeC1 (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
(time-windowed to s ∈ [t₁, t₂] with 0 < t₁ if the global form is wrong —
choose the windowing that composes with M1, report what you pick)
with EXPLICIT envelope (2·B_log-form via
ShenWork.IntervalLogisticSourceQuantBound) and explicit derivBound.

Hypotheses you may take (each must be satisfiable; they are the outputs of
the parallel M2-uniform module + M1 at the previous level):
 (K1) the restart representation of u_n slices (M1's conclusion shape at
      level n−1, or for n=0 the homogeneous series S(t)u₀ — you may
      parameterize abstractly: u_n's lift equals a restart cosine series
      with coefficient family (a₀, a) where a has DuhamelSourceTimeC1 and
      |a₀ k| ≤ M₀')
 (K2) explicit slice bounds: ∀ s ∈ window, 0 < m ≤ u_n(s,x) ≤ M (positivity
      + sup bound; positivity floor m needed for the logistic chain rule on
      rpow — check logisticSourceFun_hasDerivAt_time's exact hypotheses),
      |∂ₓ lift| ≤ G1, |∂ₓ² lift| ≤ G2 (for B_log)
 plus C² slice facts as needed (Neumann endpoints for the decay corollary).

## Proof chain (atoms all proved)
1. ∂_σ u_n pointwise: G4i restartCosineSeries_hasDerivAt_time
   (ShenWork/PDE/IntervalSourceCoefficientTimeC1.lean:719) applied to (K1).
   Explicit sup bound on |∂_σ u_n| via the derivative series ≤
   ∑(λ|c| + |a|): use IntervalHomogeneousQuantBound (E₂ weight) +
   IntervalDuhamelQuantGain + the envelope of (K1)'s a-family.
2. Chain rule: logisticSourceFun_hasDerivAt_time
   (IntervalMildPicardRegularity.lean:605) → pointwise σ-derivative of
   L(u_n(σ,x)) with explicit bound.
3. Coefficient level: cosineCoeffs_hasDerivAt_of_smooth_param
   (IntervalMildPicardRegularity.lean:494) → hderiv field; its joint
   continuity input comes from the joint continuity of the derivative
   series (IntervalRestartDerivJointContinuity.lean
   restartDerivField_continuousOn_joint).
4. envelope: 2·B_log/(kπ)² decay via
   logisticSourceFun_cosineCoeff_quadratic_decay_explicit
   (IntervalLogisticSourceQuantBound.lean) + ha0 bound via
   cosineCoeffs_zero_abs_le_of_bound; summability of the envelope: p-series.
5. derivBound: |d/dσ cosineCoeffs(L(u_n σ)) k| = |cosineCoeffs(∂_σL) k| ≤
   2·sup|∂_σ L| (coefficient L¹ bound; reuse
   cosineCoeffs_zero_abs_le_of_bound / the k≥1 2·sup bound — find or prove
   the trivial |cosineCoeffs g k| ≤ 2·sup_{[0,1]}|g| lemma).

## Constraints
Same as previous specs: new file only; 0 sorry/admit/axiom/native_decide;
iterate with scp + ssh uisai1 lake env lean (NEVER lake build); named
satisfiable hypotheses allowed if a sub-step walls (report honestly);
explicit constants everywhere (no existentials in bounds); commit ONLY your
file: "Phase-0 M3: iterate source time-C1 step (explicit envelope/derivBound)",
push uisai1 main (untracked-copy collision: rm remote copy, push, verify).
Read M1 (ShenWork/Paper2/IntervalPicardIterateRestart.lean) FIRST to match
its hypothesis shapes so M3's output literally plugs into M1's H2.
