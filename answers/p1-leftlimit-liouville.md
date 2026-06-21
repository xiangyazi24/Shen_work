# Paper 1: left limit by left-translate compactness plus Liouville

## Executive verdict

For the non-monotone positive-chi traveling-wave construction, do not try to derive the left endpoint from finite variation or monotonicity.  Uniform C2-type Green bounds and the right tail do not imply

    integral_{-infty}^{x0} |U'(x)| dx < infinity.

A bounded C2 function can oscillate indefinitely as x -> -infty.  The correct non-monotone route is:

1. build a genuine positive left floor from the lower barrier;
2. take left translates U_n(y) = U(y - s_n), with s_n -> +infty;
3. extract a locally convergent subsequence by Arzela-Ascoli and Green/ODE regularity;
4. pass the stationary equation to the limit;
5. apply a Liouville/stabilization theorem: every bounded positive entire stationary solution in the relevant regime is the positive equilibrium;
6. use uniqueness of all left cluster limits to conclude U(x) -> U_- as x -> -infty.

The hard analytic theorem is the Liouville/stabilization input.  It is not automatic from boundedness and positivity alone.

For the normalized Paper 1 model, U_- = 1.  For the general logistic source a U - b U^(1+alpha),

    U_- = (a / b)^(1 / alpha).

## 1. Left-translate compactness and passage to an entire solution

Let U solve the stationary profile equation on the whole line,

    U'' + c U' - lambda U + R(U, V[U]) = 0,

or equivalently, in the normalized Paper 1 form,

    U'' + c U' - chi d_x(U^m V'[U]) + U(1 - U^alpha) = 0.

Assume:

- U is trapped: 0 <= U <= M, and U(+infty)=0 by the right upper barrier;
- U has a strict left floor: there are delta > 0 and A such that delta <= U(x) for all x <= A;
- U has uniform local regularity from the Green representation, at least enough to extract U_n and U_n' locally uniformly;
- the elliptic resolver V[U] is translation-equivariant and continuous under locally uniform convergence of bounded inputs.

Given any sequence s_n -> +infty, define left translates

    U_n(y) = U(y - s_n).

For each fixed compact interval [-R,R], and all large n, y - s_n <= A on that interval.  Therefore

    delta <= U_n(y) <= M

on [-R,R].

Uniform C2-type bounds imply equicontinuity of U_n and U_n'.  By Arzela-Ascoli and a diagonal argument, there are a subsequence n_j and a function W such that

    U_{n_j} -> W locally uniformly,
    U_{n_j}' -> W' locally uniformly.

If one also has equicontinuity of U_n'', then this is C2_loc convergence directly.  If one only has a uniform bound on U_n'', then do not claim C2_loc immediately.  Instead use the equation:

    U_n'' = -c U_n' + lambda U_n - R(U_n, V[U_n]).

The right-hand side converges locally uniformly once R and the elliptic resolver are continuous under bounded locally uniform convergence.  Therefore U_n'' converges locally uniformly to that limiting right-hand side, and W is C2 with

    W'' = -c W' + lambda W - R(W, V[W]).

This proves that W is a genuine entire stationary solution:

    W'' + c W' - lambda W + R(W, V[W]) = 0.

### Chemical convergence

For the whole-line elliptic equation

    -V'' + mu V = nu U^gamma,

write the resolver as convolution with the positive Green kernel G_mu:

    V[U] = G_mu * (nu U^gamma).

If U_n -> W locally uniformly and 0 <= U_n <= M, then U_n^gamma -> W^gamma locally uniformly and remains uniformly bounded.  Since G_mu and its first derivative are integrable on R, dominated convergence with compact-tail splitting gives

    V[U_n] -> V[W] locally uniformly,
    V'[U_n] -> V'[W] locally uniformly.

Using the elliptic equation then gives local convergence of V'' as well.  This is the clean way to pass the nonlocal chemotaxis term to the limit.

### Translation equivariance

Because the whole-line elliptic kernel is translation invariant,

    V[U(. - s)](y) = V[U](y - s).

Thus the translated pair (U_n, V[U_n]) solves the same stationary equation as U, with no additional error term.

## 2. The Liouville/stabilization step

The required theorem is:

    Bounded positive entire stationary profiles are constants.

More explicitly, in the positive-equilibrium regime:

    If W is a bounded entire stationary solution,
       0 < delta <= W <= M on R,
    and W solves the stationary chemotaxis-wave equation,
    then W is identically U_-.

This is the genuine hard core.

It should not be replaced by a formal weighted-energy argument unless that energy identity is actually proved and finite.  The e^{c x / 2} or e^{c x} weighted energy is delicate on the whole line: the weight decays on one side and grows on the other, and the nonlocal chemotaxis term is not generally a simple gradient of a coercive scalar energy.  Moreover, positive bounded entire solutions of a general nonlocal second-order equation need not be constant merely because they are bounded between two positive constants.

The clean rigorous route is to use the paper's stabilization/Liouville theorem.  View the stationary W as a time-independent solution of the moving-frame parabolic problem.  If the stabilization theorem says that every globally defined bounded positive solution with a positive floor converges uniformly to the positive constant equilibrium, then applying it to the stationary solution gives

    ||W - U_-||_infty = ||W(t, .) - U_-||_infty -> 0,

but the left side is independent of t.  Hence

    W == U_-.

This is exactly the type of argument used in the source-paper left-endpoint proof: translate to the left, extract a locally uniform stationary limit with positive infimum, then invoke the stabilization result to force the translated limit to be the positive equilibrium, giving a contradiction if the left endpoint was not U_-.

## 3. From Liouville to the whole left limit

Once every left-translate cluster point is U_-, the full left limit follows by contradiction.

Suppose U(x) does not tend to U_- as x -> -infty.  Then there exist epsilon > 0 and x_n -> -infty such that

    |U(x_n) - U_-| >= epsilon.

Set s_n = -x_n -> +infty and consider

    U_n(y) = U(y - s_n) = U(y + x_n).

By left-translate compactness, a subsequence converges locally to W.  In particular,

    W(0) = lim_j U(x_{n_j}).

The strict left floor passes to W, so W is bounded below by delta > 0.  The limit solves the stationary equation.  By Liouville,

    W == U_-.

Therefore W(0) = U_-, contradicting

    |U(x_{n_j}) - U_-| >= epsilon.

Hence

    U(x) -> U_- as x -> -infty.

This proves the left endpoint without spatial monotonicity.

## 4. What is minimal and what is not

### Not sufficient

The following are not sufficient by themselves:

- 0 <= U <= M;
- U(+infty)=0;
- ||U'||_infty < infinity;
- ||U''||_infty < infinity;
- U > 0 pointwise;
- nontriviality at one point.

These do not exclude persistent left oscillations or left cluster continua.

### Sufficient package

A clean sufficient package is:

1. strict positive left floor:

       exists delta > 0, exists A, forall x <= A, delta <= U x;

2. left-translate compactness:

       for every s_n -> +infty, U(. - s_n) has a locally convergent subsequence;

3. equation-closedness under left translates:

       every such limit W is a bounded entire stationary solution with the same chemical resolver;

4. Liouville/stabilization:

       every bounded entire stationary solution with positive floor equals U_-.

This is the exact non-monotone replacement for the monotone-left-limit route.

## 5. Lean-formalizable predicates

Use explicit predicates rather than hiding the hard theorem inside the final assembly.

### Strict positive left floor

    def StrictlyPositiveAtLeft (U : R -> R) : Prop :=
      exists delta A, 0 < delta and forall x, x <= A -> delta <= U x

For a barrier trap, prove this directly from the lower barrier:

    lower <= U,
    exists delta A, forall x <= A, delta <= lower x.

No monotonicity is needed.

### Left-translate compactness

    structure LeftTranslateCompactness (U : R -> R) : Prop where
      subseq_limit :
        forall s : Nat -> R,
          Tendsto s atTop atTop ->
            exists phi : Nat -> Nat, StrictMono phi and
            exists W : R -> R,
              LocallyUniformConverges
                (fun n y => U (y - s (phi n))) W

If the proof also tracks derivatives, use a stronger version:

    LocallyUniformConverges (fun n y => deriv U (y - s(phi n))) (deriv W)

or package local C1/C2 convergence separately.

### Closedness of the stationary equation

    structure LeftTranslateLimitSolves
        (p : Params) (U : R -> R) : Prop where
      limit_solves :
        forall s phi W,
          Tendsto s atTop atTop ->
          StrictMono phi ->
          LocallyUniformConverges (fun n y => U (y - s (phi n))) W ->
          BoundedProfile W and
          StrictlyPositiveEverywhere W and
          StationaryProfile p W

In practice, split `StrictlyPositiveEverywhere W` out as a consequence of `StrictlyPositiveAtLeft U`.

### Liouville theorem

    def PositiveStationaryLiouville
        (p : Params) (Ustar : R) : Prop :=
      forall W : R -> R,
        StationaryProfile p W ->
        BoundedProfile W ->
        (exists delta > 0, forall x, delta <= W x) ->
          W = fun _ => Ustar

This is the central analytic frontier.  It can be discharged from a paper stabilization theorem.

### Final left-limit theorem

    theorem tendsto_atBot_of_left_translate_liouville
        (hcompact : LeftTranslateCompactness U)
        (hclosed : LeftTranslateLimitSolves p U)
        (hleftpos : StrictlyPositiveAtLeft U)
        (hliouville : PositiveStationaryLiouville p Ustar) :
        Tendsto U atBot (nhds Ustar)

Proof outline in Lean:

1. use the sequential characterization of `Tendsto U atBot (nhds Ustar)`;
2. by contradiction, get epsilon > 0 and a sequence x_n -> -infty with `abs (U x_n - Ustar) >= epsilon`;
3. set s_n = -x_n, so s_n -> +infty;
4. apply `hcompact` to U(. - s_n) and get W;
5. use `hclosed` and `hleftpos` to show W satisfies the Liouville hypotheses;
6. rewrite W = const Ustar;
7. use local-uniform convergence at y=0 to get U(-s_phi_n) -> Ustar;
8. contradiction with the epsilon separation.

Useful Mathlib/filter ideas:

- `Filter.Tendsto.comp`
- `tendsto_atTop_neg` and `tendsto_atBot` variants for `x_n -> -infty` and `-x_n -> +infty`
- `Metric.tendsto_nhds` or `tendsto_iff_norm_sub_tendsto_zero`
- local-uniform convergence should provide a theorem like `LocallyUniformConverges.tendsto_at` at each point.

If the exact sequential characterization of `atBot` is inconvenient, state the theorem in sequence form first:

    forall xseq, Tendsto xseq atTop atBot -> Tendsto (fun n => U (xseq n)) atTop (nhds Ustar)

and later wrap it into `Tendsto U atBot (nhds Ustar)`.

## 6. Passing positivity to the limit

From `StrictlyPositiveAtLeft U`, choose delta, A with

    delta <= U x for x <= A.

For fixed y and s_n -> +infty, eventually

    y - s_n <= A.

Hence

    delta <= U(y - s_n).

Taking the locally uniform, hence pointwise, limit gives

    delta <= W y.

Thus every left-translate limit W satisfies

    forall y, delta <= W y.

This is exactly the positive floor needed by Liouville.

## 7. Passing the ODE to the limit

For the limit W, the equation is obtained as follows.

1. Translate the stationary equation.  Each U_n(y) = U(y - s_n) satisfies the same autonomous equation with chemical V[U_n].

2. Use local convergence U_n -> W and boundedness 0 <= U_n <= M to get U_n^gamma -> W^gamma locally uniformly.

3. Use the whole-line elliptic Green kernel to get

       V[U_n] -> V[W],
       V'[U_n] -> V'[W]

   locally uniformly.

4. The nonlinear source R(U_n,V[U_n]) converges locally uniformly to R(W,V[W]).

5. Since

       U_n'' = -c U_n' + lambda U_n - R(U_n,V[U_n]),

   the right-hand side converges locally uniformly.  Together with U_n -> W and U_n' -> W', this proves W is C2 and satisfies the stationary equation.

This avoids requiring a priori equicontinuity of U_n''.  Uniform boundedness of U_n'' alone gives C1 compactness, and the equation supplies the second derivative of the limit.

## 8. Why the energy/phase-plane shortcuts are not the clean route

### Weighted energy

The weighted transformation may symmetrize the linear operator, but it does not automatically give a finite coercive Lyapunov functional for the full nonlocal chemotaxis equation.  The weight grows on one side of the line and decays on the other, and the chemotaxis term involves the elliptic resolver.  A weighted-energy proof would require a separately proved finite-energy identity and boundary term control.  Without that, it is not a safe formalization route.

### Phase plane

The stationary chemotaxis equation is not a closed two-dimensional autonomous ODE in (U,U'), because V[U] is determined nonlocally by the elliptic equation.  One can enlarge the system to include V,V', but the resulting four-dimensional system can have nontrivial bounded orbits in principle.  A no-nonconstant-bounded-entire theorem is exactly the Liouville/stabilization input, not a trivial phase-plane fact.

## 9. Recommended final assembly lemma

For the non-monotone Schauder route, make the left-tail close through a named theorem:

    theorem leftLimit_eq_equilibrium_of_barrier_translate_liouville
        (htrap : BarrierTrap lower upper U)
        (hleftfloor : StrictlyPositiveAtLeftFromBarrier lower)
        (hcompact : LeftTranslateCompactness U)
        (hclosed : LeftTranslateLimitSolves p U)
        (hliouville : PositiveStationaryLiouville p Ustar) :
        Tendsto U atBot (nhds Ustar)

This is the honest endpoint theorem.  It contains no monotonicity hypothesis.

## 10. Minimal remaining obligations

The real remaining obligations are:

1. prove the lower barrier gives a strict positive left floor;
2. prove left-translate compactness from the Green/regularity bounds;
3. prove closedness of the equation under left-translate limits, including chemical resolver convergence;
4. prove or import the Liouville/stabilization theorem for bounded positive entire stationary solutions.

The first three are compactness and continuity.  The fourth is the hard paper-specific theorem.  Once it is available, the whole-sequence left limit follows by the cluster-point contradiction above.
