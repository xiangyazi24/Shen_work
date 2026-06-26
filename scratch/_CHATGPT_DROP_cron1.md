# Q782 / cron1: C^k compact-support iteratedFDeriv bound

Repo inspected: xiangyazi24/Shen_work
Mathlib ref inspected: leanprover-community/mathlib4 v4.29.1
Branch written: chatgpt-scratch

Question: for f : Real -> Real, if f is C^k and its relevant support is compact, how to prove

  exists B, 0 <= B and forall t,
    norm (iteratedFDeriv Real k f t) <= B

and how to use this for smoothRightCutoff (c / 2) c, whose positive-order derivatives are supported in [c / 2, c]?

## Verdict

Mathlib v4.29.1 has the route. The most direct theorem names are:

1. Compact-set boundedness of a continuous normed-valued function:

   IsCompact.exists_bound_of_continuousOn

   Statement shape:

     lemma IsCompact.exists_bound_of_continuousOn
         [TopologicalSpace alpha] {s : Set alpha} (hs : IsCompact s)
         {f : alpha -> E} (hf : ContinuousOn f s) :
         exists C, forall x in s, norm (f x) <= C

2. Compact-support boundedness of a continuous function:

   Continuous.bounded_above_of_compact_support

   Statement shape:

     lemma Continuous.bounded_above_of_compact_support
         (hf : Continuous f) (h : HasCompactSupport f) :
         exists C, forall x, norm (f x) <= C

3. Compact support is preserved by iterated Frechet derivatives:

   HasCompactSupport.iteratedFDeriv

   Statement shape:

     theorem HasCompactSupport.iteratedFDeriv
         (hf : HasCompactSupport f) (n : Nat) :
         HasCompactSupport (iteratedFDeriv k n f)

4. C^n gives continuity of iteratedFDeriv up to order n:

   ContDiff.continuous_iteratedFDeriv

   Statement shape:

     theorem ContDiff.continuous_iteratedFDeriv
         {m : Nat} (hm : m <= n) (hf : ContDiff k n f) :
         Continuous fun x => iteratedFDeriv k m f x

So if f itself has HasCompactSupport and is C^k, the proof is short:

```lean
theorem compactSupport_iteratedFDeriv_bound
    {f : Real -> Real} {k : Nat}
    (hf : ContDiff Real (k : ENat) f)
    (hcs : HasCompactSupport f) :
    exists B : Real, 0 <= B /\
      forall t : Real, norm (iteratedFDeriv Real k f t) <= B := by
  have hcont : Continuous (fun t : Real => iteratedFDeriv Real k f t) :=
    hf.continuous_iteratedFDeriv (by exact_mod_cast le_rfl)
  have hcsD : HasCompactSupport
      (fun t : Real => iteratedFDeriv Real k f t) :=
    hcs.iteratedFDeriv k
  rcases hcont.bounded_above_of_compact_support hcsD with <C, hC>
  exact <max C 0, le_max_right C 0,
    fun t => (hC t).trans (le_max_left C 0)>
```

This is the cleanest general answer to the compact-support question.

## If support is only contained in a compact set K

If you already have support containment rather than HasCompactSupport, use the compact-set theorem:

```lean
have hcontK : ContinuousOn
    (fun t : Real => norm (iteratedFDeriv Real k f t)) K :=
  (hcont.norm).continuousOn
obtain <B0, hB0> := hK.exists_bound_of_continuousOn hcontK
```

This gives the bound on K. For t outside K, use the hypothesis that the derivative is zero there. Then take max B0 0 if you need a nonnegative B.

Equivalently, if your derivative field has HasCompactSupport, skip K and use:

```lean
hcont.bounded_above_of_compact_support hDerivCompactSupport
```

## Existing repo pattern

The exact compact-support/continuous route is already used in the repo for the two-sided restart cutoff:

File:

  ShenWork/PDE/IntervalResolverSpectralJointC2Concrete.lean

Theorem:

  restartSmoothCutoff_iteratedFDeriv_bound_exists

Key proof pattern:

```lean
have hcont : Continuous
    (fun t : Real => iteratedFDeriv Real k (restartSmoothCutoff offset s) t) :=
  restartSmoothCutoff_contDiff.continuous_iteratedFDeriv ...

have hcomp : HasCompactSupport
    (fun t : Real => iteratedFDeriv Real k (restartSmoothCutoff offset s) t) :=
  (restartSmoothCutoff_hasCompactSupport htau).iteratedFDeriv k

rcases hcont.bounded_above_of_compact_support hcomp with <C, hC>
```

Then it returns max C 0 as the nonnegative bound.

## smoothRightCutoff-specific note

For

  phi := smoothRightCutoff (c / 2) c

HasCompactSupport phi is false: smoothRightCutoff is eventually 1 on the right.

For k = 0, the bound is B = 1, using:

  norm_iteratedFDeriv_zero
  Real.smoothTransition.nonneg
  Real.smoothTransition.le_one

For k >= 1, the right target is not HasCompactSupport phi, but:

  HasCompactSupport (fun t => iteratedFDeriv Real k phi t)

or equivalently support containment in Set.Icc (c / 2) c.

Mathlib has the local-congruence tool that should help prove the derivative is zero off the transition interval:

  Filter.EventuallyEq.iteratedFDeriv

If phi is eventually equal near t to a constant function, then its iteratedFDeriv is eventually equal near t to the iteratedFDeriv of that constant. For t < c / 2 use local equality with 0; for c < t use local equality with 1. For positive k, the positive iterated derivative of a constant is zero.

The repo already has the one-sided theorem skeleton in:

  ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean

Private theorem:

  smoothRightCutoff_iteratedFDeriv_bound_exists

The k = 0 branch is implemented. The k >= 1 branch is still a sorry. The comments there state exactly this plan: the cutoff is constant outside [c', c], so positive-order derivatives vanish outside [c', c], and continuity on compact gives boundedness.

## Recommended proof route for the sub-sorry

For the one-sided cutoff positive derivative bound, there are two viable routes.

### Route A: derive HasCompactSupport of the derivative field

1. Prove off-interval vanishing:

   for t < c / 2 or c < t,
   iteratedFDeriv Real k phi t = 0.

   Use eventual equality to constants plus Filter.EventuallyEq.iteratedFDeriv.

2. Package that as:

   HasCompactSupport (fun t => iteratedFDeriv Real k phi t)

   with compact support inside Icc (c / 2) c.

3. Apply:

   hcont.bounded_above_of_compact_support hcomp

### Route B: stay on Icc and patch outside

1. hcont := smoothRightCutoff_contDiff.continuous_iteratedFDeriv ...
2. apply IsCompact.exists_bound_of_continuousOn to isCompact_Icc and hcont.norm.continuousOn.
3. use off-interval derivative-zero to reduce every t outside Icc (c / 2) c to 0.
4. return max B 0.

Route B avoids constructing a HasCompactSupport object and may be easier if the current goal already has the explicit support interval [c / 2, c].

## Bottom line

Yes: Mathlib has the exact boundedness-from-compact-continuity theorem:

  IsCompact.exists_bound_of_continuousOn

and also the more direct compact-support theorem:

  Continuous.bounded_above_of_compact_support

Together with:

  ContDiff.continuous_iteratedFDeriv
  HasCompactSupport.iteratedFDeriv

this proves the standard C^k compact-support derivative bound. For smoothRightCutoff, first prove the positive-order derivative field is supported in [c / 2, c], because the cutoff itself is not compactly supported.
