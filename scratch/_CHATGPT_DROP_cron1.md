# Q780 / cron1: cutoff iteratedFDeriv bound

Repo inspected: xiangyazi24/Shen_work
Branch written: chatgpt-scratch
Question: for

  phi := smoothRightCutoff (c / 2) c

find whether there is a Mathlib/repo route to

  exists B, 0 <= B and forall t,
    norm (iteratedFDeriv Real k phi t) <= B.

## Verdict

There is no obvious one-shot repo theorem of the exact general form

  ContDiff Real infinity f + HasCompactSupport f
    -> exists B, forall x, norm (iteratedFDeriv Real k f x) <= B.

But the needed Mathlib pieces do exist and are already used in the repo:

1. HasCompactSupport.iteratedFDeriv
2. Continuous.bounded_above_of_compact_support
3. ContDiff.continuous_iteratedFDeriv

The cleanest committed model is not the one-sided cutoff, but the two-sided restart cutoff:

  ShenWork.IntervalResolverSpectralJointC2Concrete.restartSmoothCutoff_iteratedFDeriv_bound_exists

It proves, for k <= 2,

  exists C, 0 <= C and forall t,
    norm (iteratedFDeriv Real k (restartSmoothCutoff offset s) t) <= C.

The proof pattern is exactly:

  have hcont : Continuous (fun t => iteratedFDeriv Real k (restartSmoothCutoff offset s) t) :=
    restartSmoothCutoff_contDiff.continuous_iteratedFDeriv ...

  have hcomp : HasCompactSupport
      (fun t => iteratedFDeriv Real k (restartSmoothCutoff offset s) t) :=
    (restartSmoothCutoff_hasCompactSupport htau).iteratedFDeriv k

  rcases hcont.bounded_above_of_compact_support hcomp with <C, hC>

and then replaces C by max C 0 for a nonnegative bound.

So: Mathlib gives the compact-support derivative machinery and the boundedness extraction; the repo has a working example.

## Important distinction: smoothRightCutoff itself is not compactly supported

The repo definition is in

  ShenWork/PDE/IntervalResolverSpectralJointC2Cutoff.lean

  def smoothRightCutoff (c' c : Real) : Real -> Real :=
    fun t => Real.smoothTransition ((c - c')^{-1} * (t - c'))

The same file proves:

  smoothRightCutoff_eq_zero_of_le : t <= c' -> smoothRightCutoff c' c t = 0
  smoothRightCutoff_eq_one_of_ge  : c <= t  -> smoothRightCutoff c' c t = 1
  smoothRightCutoff_eventually_eq_one

Therefore smoothRightCutoff has no HasCompactSupport, because it is eventually 1 on the right.

## Existing partial theorem for the exact one-sided need

On main, the file

  ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean

has a private theorem with the exact intended statement, currently only for k <= 2:

  private theorem smoothRightCutoff_iteratedFDeriv_bound_exists
      (c' c : Real) (k : Nat) (hk : (k : ENat) <= 2) :
      exists B, 0 <= B and forall t,
        norm (iteratedFDeriv Real k (smoothRightCutoff c' c) t) <= B

Its k = 0 branch is already implemented using:

  norm_iteratedFDeriv_zero
  Real.smoothTransition.nonneg
  Real.smoothTransition.le_one

The k >= 1 branch is still a sorry. The comments state the intended route: smoothRightCutoff is locally constant outside [c', c], so its positive-order derivatives have support inside [c', c], hence compact support, hence bounded.

So, if you are trying to close that exact sub-sorry, the theorem skeleton is already there, but not fully proved.

## Best proof route for the one-sided cutoff

For phi := smoothRightCutoff c' c with c' < c:

### Case k = 0

Use the already-working branch:

  norm_iteratedFDeriv_zero
  Real.smoothTransition.nonneg
  Real.smoothTransition.le_one

This gives B = 1.

### Case k > 0

Do not try to prove HasCompactSupport phi. Instead prove compact support of the derivative field:

  HasCompactSupport (fun t => iteratedFDeriv Real k phi t)

with support contained in Set.Icc c' c.

The missing local facts are:

- for t < c', phi is eventually equal near t to the constant 0;
- for c < t, phi is eventually equal near t to the constant 1;
- for positive k, the k-th iterated derivative of a locally constant function is zero.

Once that support fact is obtained, the bound is exactly the restartSmoothCutoff proof pattern:

  have hcont : Continuous (fun t => iteratedFDeriv Real k phi t) :=
    hphi_contDiff.continuous_iteratedFDeriv ...
  have hcomp : HasCompactSupport (fun t => iteratedFDeriv Real k phi t) := ...
  rcases hcont.bounded_above_of_compact_support hcomp with <B, hB>
  exact <max B 0, le_max_right B 0, fun t => (hB t).trans (le_max_left B 0)>

### Alternative route avoiding HasCompactSupport

Prove directly:

1. the derivative is continuous;
2. it is zero outside Set.Icc c' c;
3. it is bounded on Set.Icc c' c by compactness of isCompact_Icc.

This may be easier if the event/local-constant-to-zero iteratedFDeriv lemma is easier to state pointwise than as HasCompactSupport.

## Reusable theorem already available for two-sided cutoff

If the downstream proof can use the two-sided cutoff instead of the one-sided right cutoff, use the committed theorem directly:

  restartSmoothCutoff_iteratedFDeriv_bound_exists

or the packaged majorant:

  restartCutoffDerivMajorant
  restartCutoffDerivMajorant_spec

These are in

  ShenWork/PDE/IntervalResolverSpectralJointC2Concrete.lean

and avoid the one-sided non-compact-support issue because restartSmoothCutoff itself has compact support.

## Bottom line

Mathlib does have the useful ingredients:

  HasCompactSupport.iteratedFDeriv
  Continuous.bounded_above_of_compact_support

The repo has a fully working pattern for compactly supported restartSmoothCutoff.

For smoothRightCutoff itself:

- HasCompactSupport smoothRightCutoff is false.
- k = 0 is bounded by 1.
- k > 0 should be bounded by proving the k-th derivative is supported in [c', c].
- The exact one-sided theorem exists as a private skeleton in IntervalHeatSemigroupHighRegularity.lean, but its k >= 1 branch is currently still sorry.
