# Paper 1: stationary Liouville core for the left endpoint

## Executive verdict

The statement

    every bounded entire stationary profile W with 0 < c1 <= W <= C2 is constant

is **not a free theorem** for the chemotaxis traveling-wave equation.  It is true only under an additional Liouville/stabilization mechanism, or under a monotone-profile route with endpoint/root pinning, or under a smallness/contraction hypothesis strong enough to rule out nonconstant bounded stationary states.

For the Lean formalization, do not hide this inside compactness.  The correct dependency chain is:

    left-translate compactness
    + equation closedness under translates
    + strict positive left floor
    + stationary Liouville theorem
    -> U(x) -> U_- as x -> -infty.

The hard theorem is the stationary Liouville theorem.  It should be a named analytic input unless it is discharged from a proved parabolic stabilization theorem.

For the normalized Paper 1 model, U_- = 1.  For the general logistic source a U - b U^(1+alpha),

    U_- = (a / b)^(1 / alpha).

## 1. Is the Liouville statement true as stated?

Not in full generality.  Boundedness and a positive floor alone do not rule out nonconstant entire stationary profiles for a nonlocal chemotaxis equation.  In parameter regimes with Turing or pattern-forming instability, one should expect nonconstant bounded steady or traveling-frame stationary states.  Even when such states do not exist for the specific paper regime, their absence is a theorem, not a consequence of the elementary bounds.

The statement becomes rigorous under one of the following additional hypotheses.

### Hypothesis A: parabolic stabilization/Liouville theorem

Assume a theorem of the form:

    every globally defined bounded positive solution of the moving-frame parabolic problem
    with a uniform positive floor converges uniformly to U_-
    as t -> infinity.

Then any time-independent stationary solution W satisfying the same bounds must be constant, because the global parabolic solution u(t,x) = W(x) has time-independent distance to U_-.  If the stabilization theorem says

    ||u(t,.) - U_-||_infty -> 0,

then for the stationary solution this gives

    ||W - U_-||_infty = 0.

This is the cleanest source-paper route.  It is also the best Lean dependency: prove or carry the stabilization theorem, then derive the stationary Liouville theorem in a few lines.

### Hypothesis B: monotone profile plus root pinning

If W is monotone, bounded, and bounded away from zero, then both one-sided limits exist:

    L_- = lim_{x -> -infty} W(x),
    L_+ = lim_{x -> +infty} W(x).

Because W is monotone, the total variation is finite.  If W is C2 with bounded W'', then W' is uniformly continuous; finite variation implies W'(x) -> 0 at both ends.  The stationary equation plus elliptic-resolver convergence then pins both limits to algebraic equilibria.

If the positive algebraic equilibrium is unique and the lower bound excludes zero, then

    L_- = L_+ = U_-.

A monotone function with equal limits at both ends is constant.  This proves W == U_-.

This route is valid when the Schauder trap delivers monotonicity.  It is not available for the positive-chi nonmonotone barrier route unless monotonicity is part of the trap.

### Hypothesis C: small Lipschitz/contraction around the equilibrium

Let z = W - U_-.  Suppose the equation can be written as

    L z = -H(z),
    L = d^2/dx^2 + c d/dx - lambda,

and the bounded inverse satisfies

    ||L^{-1} F||_infty <= C_L ||F||_infty.

For the whole-line Green kernel of L with lambda > 0, one typically has C_L = 1/lambda up to sign conventions.

If the nonlinear remainder satisfies a global Lipschitz estimate on the relevant invariant band,

    ||H(z1) - H(z2)||_infty <= L_H ||z1 - z2||_infty,

and

    C_L L_H < 1,

then any bounded solution satisfies

    ||z||_infty <= C_L ||H(z)||_infty <= C_L L_H ||z||_infty,

hence z = 0.

This is rigorous, but it is a **smallness hypothesis**.  It is not automatic from positivity and boundedness, and it may be too strong for the paper's full parameter range.

## 2. Proof route A: stabilization implies stationary Liouville

This is the cleanest fully rigorous route.

Define the stationary profile predicate:

    StationaryProfile p W :=
      W is sufficiently regular,
      V = V[W] solves the elliptic equation,
      W solves the stationary moving-frame equation.

Define a positive floor:

    PositiveFloor W := exists delta > 0, forall x, delta <= W x.

Assume the parabolic stabilization theorem:

    MovingFrameStabilization p Ustar :=
      forall u v,
        GlobalClassicalSolution p u v ->
        BoundedSolution u ->
        PositiveFloorInSpaceTime u ->
        Tendsto (fun t => supNorm (fun x => u t x - Ustar)) atTop (nhds 0).

Then prove:

    theorem stationaryLiouville_of_stabilization
        (hstabilize : MovingFrameStabilization p Ustar) :
        forall W,
          StationaryProfile p W ->
          BoundedProfile W ->
          PositiveFloor W ->
          W = fun _ => Ustar.

Proof:

1. From W build the time-independent parabolic solution:

       u(t,x) = W(x),
       v(t,x) = V[W](x).

2. The stationary equation gives the parabolic equation because u_t = 0.

3. Boundedness and the positive floor are inherited from W.

4. Apply `hstabilize`:

       supNorm (W - Ustar) -> 0.

5. Since the expression is constant in t, it must be zero.

6. Therefore W = Ustar pointwise.

Lean shape:

    def PositiveStationaryLiouville (p : Params) (Ustar : R) : Prop :=
      forall W,
        StationaryProfile p W ->
        BoundedProfile W ->
        (exists delta, 0 < delta and forall x, delta <= W x) ->
          W = fun _ => Ustar

    theorem positiveStationaryLiouville_of_stabilization
        (hstab : MovingFrameGlobalStabilization p Ustar) :
        PositiveStationaryLiouville p Ustar := by
      intro W hstat hbdd hfloor
      -- build time-independent global solution from hstat
      -- apply hstab
      -- constant-in-time convergence forces sup distance zero
      -- turn zero sup distance into pointwise equality
      ...

This theorem is short once the stabilization theorem and the stationary-to-parabolic wrapper exist.  It is the best formal target.

## 3. Proof route B: contraction through the Green inverse

This route is valid only under a strict Lipschitz-smallness condition.

Let Ustar be the positive equilibrium, and set

    z = W - Ustar.

Write the stationary equation as

    L z = -H(z),

where H(0)=0 and H encodes the nonlinear reaction and chemotaxis remainders, including the elliptic response V[Ustar+z] - V[Ustar].

The Green inverse gives

    z = -L^{-1} H(z).

If

    ||L^{-1}||_{Linf -> Linf} <= C_L

and

    ||H(z1) - H(z2)||_infty <= L_H ||z1 - z2||_infty

on the whole allowed band, with C_L L_H < 1, then

    ||z||_infty <= C_L L_H ||z||_infty.

Hence z = 0.

This is complete and Lean-friendly if the constants are available.  However, it is not the general paper Liouville theorem.  It proves a small-coupling or small-band Liouville result.

Care points:

1. The nonlocal resolver must be Lipschitz:

       ||V[Ustar+z1] - V[Ustar+z2]||_{C1} <= C ||z1 - z2||_infty.

2. Powers must be Lipschitz on the positive band `[c1, C2]`.

3. The chemotaxis flux derivative must be estimated in the same norm as the Green source.  This may require C1 or C2 control, not merely Linf, depending on how R is written.

4. The final constant must satisfy C_L L_H < 1.

Thus the contraction route is rigorous but conditional.  It should be formalized as a separate theorem:

    StationaryLiouville_of_GreenContraction.

Do not use it unless the parameter regime supplies the required smallness.

## 4. Proof route C: maximum principle / sliding

The naive maximum-principle argument is not complete for the nonlocal chemotaxis equation.

For a scalar local equation, one might take an approximate point where z = W - Ustar is near its supremum, with z' approximately zero and z'' <= 0, and derive a sign contradiction.  But here the source contains V[W] and flux terms involving V'[W].  At a maximum of W, V[W] need not be at a corresponding maximum, and the term

    d_x(W^m V'[W])

does not have a sign determined only by W at that point.

The maximum principle route becomes rigorous only with additional structure, for example:

1. order-preserving resolver plus a comparison/sliding setup;
2. monotonicity of W;
3. sign of chi and source terms arranged so the nonlocal term has the correct one-sided sign;
4. a strong comparison principle for the coupled elliptic-parabolic system.

Without those hypotheses, the nonlocal coupling breaks the pointwise maximum argument.  So the maximum/sliding route is not the clean generic Liouville proof.

## 5. Monotone version

If the Schauder trap delivers monotonicity, the following theorem is clean and much easier than a nonmonotone Liouville theorem.

Assume:

1. W is C2 and solves the stationary equation;
2. W is monotone, say Antitone W;
3. 0 < c1 <= W <= C2;
4. the elliptic resolver is continuous under limits of constants;
5. stationary flatness/root pinning: whenever W has a one-sided limit L, then L is an algebraic equilibrium;
6. the only algebraic equilibrium in `[c1, C2]` is Ustar.

Then W == Ustar.

Proof:

1. Since W is monotone and bounded, there are limits

       L_- = lim_{x -> -infty} W(x),
       L_+ = lim_{x -> +infty} W(x).

2. The positive floor gives L_-, L_+ >= c1 > 0.

3. Monotonicity implies finite total variation:

       integral |W'| <= L_- - L_+,

   in the classical smooth setting.  With bounded W'', W' is uniformly continuous, hence W'(x) -> 0 at both ends.

4. The elliptic resolver sends constant limits to constant chemical limits:

       V[W](x) -> (nu/mu) L^gamma,
       V'[W](x) -> 0.

5. Passing the stationary equation to each end gives the reaction root

       L (a - b L^alpha) = 0.

6. Since L > 0, L = Ustar.  Hence L_- = L_+ = Ustar.

7. A monotone function with the same limit at both ends is constant:

       Ustar <= W(x) <= Ustar

   for every x.

Lean theorem shape:

    theorem monotone_stationary_liouville
        (hmono : Antitone W)
        (hfloor : exists delta > 0, forall x, delta <= W x)
        (hbdd : forall x, W x <= C2)
        (hstat : StationaryProfile p W)
        (hroot_left : forall L, Tendsto W atBot (nhds L) -> AlgebraicRoot p L)
        (hroot_right : forall L, Tendsto W atTop (nhds L) -> AlgebraicRoot p L)
        (hroot_unique : forall L, delta <= L -> L <= C2 -> AlgebraicRoot p L -> L = Ustar) :
        W = fun _ => Ustar

This monotone theorem is a good fallback if the trap can deliver `W' <= 0`.

## 6. Nonmonotone left-limit theorem using Liouville

For the nonmonotone barrier route, prove the left endpoint by cluster-point uniqueness.

Assume:

1. strict positive left floor for U:

       exists delta A, 0 < delta and forall x <= A, delta <= U x;

2. left-translate compactness:

       for every s_n -> +infty, U(. - s_n) has a locally convergent subsequence;

3. equation closedness:

       every left-translate limit W is a bounded entire stationary solution;

4. Liouville:

       every bounded entire stationary solution with positive floor is Ustar.

Then:

    U(x) -> Ustar as x -> -infty.

Proof by contradiction:

1. If not, choose epsilon > 0 and x_n -> -infty such that

       |U(x_n) - Ustar| >= epsilon.

2. Set s_n = -x_n -> +infty and define

       U_n(y) = U(y - s_n) = U(y + x_n).

3. Extract a locally convergent subsequence U_nj -> W.

4. The left floor passes to W: for each fixed y, y - s_nj <= A eventually, hence delta <= U_nj(y), so delta <= W(y).

5. By equation closedness, W is a bounded entire stationary solution.

6. By Liouville, W == Ustar.

7. Evaluating at y = 0 gives

       U(x_nj) -> Ustar,

   contradicting the epsilon separation.

Lean theorem shape:

    theorem tendsto_atBot_of_left_translate_liouville
        (hcompact : LeftTranslateCompactness U)
        (hclosed : LeftTranslateLimitSolves p U)
        (hleftfloor : StrictlyPositiveAtLeft U)
        (hliouville : PositiveStationaryLiouville p Ustar) :
        Tendsto U atBot (nhds Ustar)

It is often easier to first prove the sequential form:

    theorem tendsto_atBot_seq_of_left_translate_liouville :
      forall xseq, Tendsto xseq atTop atBot ->
        Tendsto (fun n => U (xseq n)) atTop (nhds Ustar)

and then wrap it into a filter `Tendsto` theorem.

## 7. Exact dependency chain for Lean

Use these predicates.

    def StrictlyPositiveAtLeft (U : R -> R) : Prop :=
      exists delta A, 0 < delta and forall x, x <= A -> delta <= U x

    def PositiveFloorEverywhere (W : R -> R) : Prop :=
      exists delta, 0 < delta and forall x, delta <= W x

    def PositiveStationaryLiouville (p : Params) (Ustar : R) : Prop :=
      forall W,
        StationaryProfile p W ->
        BoundedProfile W ->
        PositiveFloorEverywhere W ->
          W = fun _ => Ustar

    structure LeftTranslateCompactness (U : R -> R) : Prop where
      subseq_limit :
        forall s : Nat -> R,
          Tendsto s atTop atTop ->
            exists phi : Nat -> Nat, StrictMono phi and
            exists W : R -> R,
              LocallyUniformConverges
                (fun n y => U (y - s (phi n))) W

    structure LeftTranslateLimitSolves (p : Params) (U : R -> R) : Prop where
      solves :
        forall s phi W,
          Tendsto s atTop atTop ->
          StrictMono phi ->
          LocallyUniformConverges (fun n y => U (y - s (phi n))) W ->
            StationaryProfile p W and BoundedProfile W

Then prove:

    theorem left_translate_limit_positive_floor
        (hfloor : StrictlyPositiveAtLeft U)
        (hs : Tendsto s atTop atTop)
        (hconv : LocallyUniformConverges (fun n y => U (y - s n)) W) :
        PositiveFloorEverywhere W

and finally:

    theorem tendsto_atBot_of_left_translate_liouville
        (hcompact : LeftTranslateCompactness U)
        (hclosed : LeftTranslateLimitSolves p U)
        (hfloor : StrictlyPositiveAtLeft U)
        (hliouville : PositiveStationaryLiouville p Ustar) :
        Tendsto U atBot (nhds Ustar)

Useful Mathlib/filter pieces:

- `Filter.Tendsto.comp`
- `tendsto_const_nhds`
- `Metric.tendsto_nhds` or `tendsto_iff_norm_sub_tendsto_zero`
- `StrictMono.tendsto_atTop`
- negation maps between `atTop` and `atBot`, such as `tendsto_neg_atTop_atBot` or equivalent local lemmas if names differ
- a pointwise consequence of local-uniform convergence, e.g. a project lemma like `LocallyUniformConverges.tendsto_at`

## 8. Bottom line

The Liouville statement is not an elementary consequence of boundedness plus a positive floor.  For the nonmonotone Schauder route, the correct hard input is either:

1. a paper stabilization theorem, giving `PositiveStationaryLiouville`; or
2. a smallness/contraction theorem for the stationary Green map; or
3. monotonicity plus endpoint root pinning.

If the trap can deliver monotonicity, the monotone theorem is the easiest fully internal proof.  If the route intentionally avoids monotonicity, then carry `PositiveStationaryLiouville` as the genuine analytic theorem and use left-translate compactness to obtain the left endpoint.
