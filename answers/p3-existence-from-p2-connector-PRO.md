# Paper 3 persistence: proving the PositiveGlobalBoundedSolution input

## Executive verdict

The desired endgame is mathematically sound, but it has one important connector that must be stated explicitly.

The final pipeline should be:

    local B-form mild solution
    + positivity and nonnegativity
    + positive-time regularity upgrade
    + continuation criterion
    + Paper 2 a-priori boundedness
    -> IsPaper2GlobalClassicalSolution and IsPaper2Bounded
    -> PositiveGlobalBoundedSolution
    -> Paper 3 persistence without carrying PositiveGlobalBoundedSolution as a hypothesis.

The B-form fractional bootstrap is an essential part of the bridge, but it does not by itself equal the full Paper 2 classical-solution interface.  The remaining genuine analytic connector is:

    B-form mild solution with enough positive-time regularity
    -> Paper2 classical solution fields on every finite time interval.

This connector must include pointwise PDE identities, closed-domain positivity of u, nonnegativity of v, Neumann boundary conditions, and the repository's `D.classicalRegularity` field.

## 1. What must be proved for PositiveGlobalBoundedSolution

The Paper 3 persistence theorem consumes

    PositiveGlobalBoundedSolution D p u v.

In the current statement layer this means:

    IsPaper2GlobalClassicalSolution D p u v
    and IsPaper2Bounded D u
    and positivity of u at positive times.

The global classical predicate is:

    forall T > 0, IsPaper2ClassicalSolution D p T u v.

A finite-time classical solution requires the following fields:

1. positive time horizon T;
2. `D.classicalRegularity T u v`;
3. `0 < u t x` for `0 < t < T`, including closed-domain x;
4. `0 <= v t x` for `0 < t < T`;
5. the u equation pointwise on the interior;
6. the elliptic v equation pointwise on the interior;
7. Neumann boundary conditions for u and v.

The boundedness field is weaker:

    IsPaper2Bounded D u := exists M, eventually_atTop (fun t => D.supNorm (u t) <= M).

So any uniform global bound or any eventual sup-norm bound implies it.

## 2. Does conjugatePicardLimit plus fractional smoothing already give classicality?

Not automatically.

The B-form fractional smoothing gives estimates such as:

    u(t) in H^sigma for positive times,
    v(t) in H^{sigma+2},
    flux F(t) in H^rho,
    then u(t) in H1 after the second B-form step.

Those estimates are enough to support the boundedness/source bridge.  But the Paper2 classical interface is stronger.  It asks for pointwise PDE identities and classical regularity, not merely Sobolev regularity of time slices.

To reach `IsPaper2ClassicalSolution`, one still needs a mild-to-classical theorem.  The theorem can be proved from standard one-dimensional parabolic regularity, but it should be a named connector.

A good connector statement is:

    BFormMildClassicalUpgrade:
      if u is the B-form mild solution on [0,T],
      u is bounded on [0,T],
      the elliptic v is the resolver of u,
      and the positive-time fractional bootstrap holds,
      then IsPaper2ClassicalSolution D p T u v.

This is the main remaining analytic bridge if it is not already present.

## 3. Regularity steps from mild to classical

A standard proof goes as follows.

### Step 1: finite-time boundedness

On any finite interval, use the Paper2 a-priori estimates or local branch bounds to get

    0 <= u(t,x) <= M_T.

Then the elliptic equation

    -d2 v_xx + mu v = nu u^gamma

gives high spatial regularity for v.  Since u is bounded, `u^gamma` lies in Lp for every finite p on the interval, and elliptic regularity gives

    v(t) in W^{2,p}

for finite p.  In one dimension this gives `v_x` bounded and often Holder continuous after choosing p large.

### Step 2: rewrite the u equation with controlled coefficients

For m = 1,

    -d_x(u chi(v) v_x)
    = -chi(v) v_x u_x - u [chi'(v) v_x^2 + chi(v) v_xx].

Thus u solves a linear parabolic equation with bounded coefficients plus the logistic nonlinearity:

    u_t = d1 u_xx + B(t,x) u_x + C(t,x) u + u(a - b u^alpha).

The coefficients are controlled by the elliptic estimates for v and the bound on u.

### Step 3: apply parabolic regularity

On every positive-time slab `[s0,T]`, standard one-dimensional parabolic regularity gives enough regularity to conclude that u is classical.  One may use Lp regularity or Schauder regularity.  Once u has enough spatial regularity and time differentiability, the mild equation differentiates to the pointwise PDE.

If the repo wants to avoid external Schauder theory, a high-order Sobolev bootstrap can be used instead: the B-form bootstrap gives positive fractional regularity; elliptic v gains two derivatives; product rules improve the flux; repeated smoothing raises u above the Sobolev threshold for C2 spatial regularity.  This is possible, but it is more work than a single parabolic-regularity connector.

### Step 4: boundary conditions

For v, the Neumann condition is part of the elliptic resolver.

For u, the B-form Neumann heat semigroup and the compatibility of the divergence source should imply the Neumann condition at positive times.  This should be a separate boundary regularity field in the classical upgrade theorem.

### Step 5: initial time

The Paper2 PDE identities are required for `0 < t < T`, not at t = 0.  Thus positive-time classical regularity is enough for the PDE identities.  If `D.classicalRegularity T u v` also asks for continuity up to t = 0, use the mild initial trace and the continuity of the semigroup/Duhamel formula.

## 4. Global existence by continuation

The global step uses the usual continuation principle.

A maximal local solution has a lifespan `Tmax`.  A continuation theorem should say:

    if Tmax is finite, then the continuation norm becomes unbounded as t approaches Tmax.

For this system, a suitable continuation norm is the sup norm of u plus the regularity needed to build the elliptic v.  Because v is elliptically determined by u, an L-infinity bound on u gives uniform bounds for v, v_x, and v_xx by elliptic estimates.

Thus:

1. local existence gives a maximal branch on `[0,Tmax)`;
2. Paper2 a-priori boundedness gives a finite sup-norm bound for u on every finite part of the branch, ideally as `IsPaper2BoundedBefore D Tmax u`;
3. the continuation criterion then forbids finite `Tmax`;
4. hence `Tmax = infinity`.

Important: for continuation, one needs a pre-global estimate on the maximal branch.  Eventual boundedness of an already global solution is not enough to prove global existence.  The boundedness theorem used here must have the `bounded before Tmax` form, or a direct a-priori estimate on every finite branch.

Once global existence is obtained, the same a-priori bound gives `IsPaper2Bounded D u` by `eventually_atTop` or a stronger all-time bound.

## 5. Local existence status

The B-form conjugate Picard construction should provide the local mild solution.  For the endgame, the output must be packaged as a local solution branch with:

1. a positive local time;
2. the B-form Duhamel identity;
3. the elliptic resolver for v;
4. initial trace;
5. uniqueness or a compatible continuation interface;
6. positivity preservation for u and nonnegativity for v;
7. enough regularity to enter the classical-upgrade theorem.

If `conjugatePicardLimit` currently gives only a mild fixed point, then local existence is not the missing idea, but a wrapper is still needed:

    conjugatePicardLimit -> LocalBFormSolutionBranch.

## 6. Positivity and nonnegativity

For paper-positive initial data, one should prove:

    u0 has a closed-domain positive floor
    -> u(t,x) > 0 for all t > 0.

This is a maximum-principle or positivity-preserving-semigroup theorem.

For v:

    -d2 v_xx + mu v = nu u^gamma >= 0

with Neumann boundary implies

    v >= 0

by elliptic comparison.

These facts should not be left implicit, because `IsPaper2ClassicalSolution` includes them as fields.

## 7. Final connector theorem shape

A useful final theorem is:

    theorem exists_positiveGlobalBoundedSolution_of_paper2_pipeline
      (hlocal : LocalBFormPicardExistence p u0)
      (hupgrade : BFormMildClassicalUpgrade p)
      (hpos : PositivityPreservation p u0)
      (hboundedBefore : A_priori_LinftyBoundedBefore_MaximalBranches p u0)
      (hcontinuation : ContinuationCriterion p)
      (hglobalBound : GlobalBoundFromA_priori p u0) :
        exists u v,
          InitialTrace intervalDomain u0 u and
          PositiveGlobalBoundedSolution intervalDomain p u v

Proof structure:

1. use `hlocal` to construct a maximal local branch;
2. use `hboundedBefore` to bound it on finite intervals;
3. use `hcontinuation` to prove the maximal time is infinite;
4. use `hupgrade` to get `forall T > 0, IsPaper2ClassicalSolution ... T u v`;
5. use `hglobalBound` or the global form of the a-priori bound to get `IsPaper2Bounded`;
6. use `hpos` for the positivity and nonnegativity components;
7. assemble `PositiveGlobalBoundedSolution`.

## 8. Status of the links

### Local B-form Picard fixed point

Status: expected from `conjugatePicardLimit`, but the exact output strength must be checked.  If it only returns a mild solution, add a wrapper that gives a local branch with initial trace and continuation compatibility.

### Fractional bootstrap and Paper2 boundedness

Status: this is the Paper2 boundedness route currently being closed.  It supplies the crucial L-infinity a-priori estimate and regularity for the source bridge.

### Classical upgrade

Status: genuine analytic connector unless already proved.  This is the main missing bridge from mild/B-form regularity to the Paper2 classical predicate.

### Positivity preservation

Status: standard but must be explicit.  Use the maximum principle or positivity of the semigroup plus reaction/flux structure, and elliptic comparison for v.

### Continuation

Status: standard but separate.  It must consume the pre-global bounded-before estimate, not merely eventual boundedness of a global solution.

### IsPaper2Bounded

Status: easy after global a-priori boundedness.  Use the existing `IsPaper2Bounded.of_eventually_supNorm_le` or the stronger all-time bound wrapper.

### P3 persistence

Status: once `PositiveGlobalBoundedSolution` is constructed, the conditional persistence theorem becomes unconditional for the chosen initial data and parameter regime.

## 9. Bottom line

The final endgame is:

    conjugatePicard local mild existence
    + Paper2 a-priori boundedness before maximal time
    + continuation
    + mild-to-classical upgrade
    + positivity preservation
    -> exists (u,v), PositiveGlobalBoundedSolution
    -> Paper3 persistence applies without assuming PositiveGlobalBoundedSolution.

The single remaining genuine analytic input, if boundedness is already being closed, is the mild-to-classical connector for the B-form solution.  Fractional smoothing is part of this connector, but the final Paper2 classical interface also needs pointwise PDE identities, time regularity, Neumann boundary conditions, and positivity fields.
