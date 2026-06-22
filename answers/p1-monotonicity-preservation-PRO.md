# Paper 1: monotonicity preservation for the fixed-source Schauder map

## Executive verdict

For the fixed-source linear Green map

    T(u) = greenConv(-(R(u,V[u]) + lambda*u)),

monotonicity of the input `u` does **not** automatically imply monotonicity of `T(u)`.  Some pieces preserve antitonicity, but the crucial source term does not have a robust monotonicity sign.  In particular, the chemotaxis contribution and even the logistic reaction after shifting can destroy spatial monotonicity of the frozen source.

Therefore, if the final proof needs the fixed point `U` to be antitone, one must obtain that property by a separate mechanism:

1. use a monotone sub-trap and prove the actual chosen map preserves it;
2. use the paper's parabolic auxiliary map, whose derivative equation can be handled by a maximum principle;
3. prove a separate sliding/comparison theorem for stationary profiles;
4. or avoid monotonicity and use the left-translate Liouville/stabilization route.

For a Lean formalization, the cleanest honest split is:

    fixed-source linear Schauder map -> existence in barrier trap, no monotonicity;
    monotonicity, if needed -> separate theorem/hypothesis.

Do not silently infer antitonicity of the fixed point from the lower-pinned barrier trap.

## 1. Which pieces preserve antitonicity?

### 1.1 Elliptic chemical resolver

On the whole line, the elliptic resolver

    -d2 V'' + mu V = nu u^gamma

is convolution with a positive even kernel:

    G_mu(x) = C exp(-sqrt(mu/d2) |x|).

If `u` is antitone and nonnegative, then `u^gamma` is antitone for `gamma > 0`.  Convolution with a nonnegative kernel preserves antitonicity:

    x1 <= x2
    -> u^gamma(x1-y) >= u^gamma(x2-y) for every y
    -> V[u](x1) >= V[u](x2).

So, on the whole line,

    u antitone -> V[u] antitone.

Symmetry of the kernel is not actually needed for this monotonicity preservation; positivity and translation invariance are enough.  Symmetry is useful for other estimates.

On a bounded interval with Neumann resolver, the same statement is not automatic from positivity of the kernel alone, because the kernel is not translation-invariant.  It should be proved separately if needed.  For the traveling-wave whole-line resolver, the convolution proof is clean.

### 1.2 Green convolution for the profile operator

Let `K` be the positive Green kernel for the linear resolvent of

    partial_x^2 + c partial_x - lambda,

with `lambda > 0`.  Because of the drift `c partial_x`, the kernel is positive but not symmetric in ordinary Lebesgue measure.  That does not matter.

If

    (K*S)(x) = integral K(y) S(x-y) dy

and `S` is antitone, then `K*S` is antitone:

    x1 <= x2 -> S(x1-y) >= S(x2-y) for all y,

and integration against `K >= 0` preserves the inequality.

Thus:

    frozen source antitone -> T(u) antitone.

This is a valid lemma.

### 1.3 The source is the obstruction

The problem is the source.

Depending on sign convention, the Green source is either `R(u,V[u])`, `-(R(u,V[u])+lambda*u)`, or an equivalent shifted variant.  To prove `T(u)` antitone, the actual source passed to the positive Green operator must be antitone in `x`.

This generally fails.

#### Logistic reaction

The scalar logistic reaction

    f(u) = a*u - b*u^(1+alpha)

is not monotone on the whole trap unless the trap is restricted to a region where

    f'(s) = a - b*(1+alpha)*s^alpha

has a fixed sign.  If the trap crosses the critical value

    (a/(b*(1+alpha)))^(1/alpha),

then even the reaction part does not preserve spatial antitonicity as a function of `u`.

The shifted source can be worse.  For example, if the Green source contains

    b*u^(1+alpha) - (a+lambda)*u,

its derivative with respect to `u` is

    b*(1+alpha)*u^alpha - (a+lambda),

which also has parameter-dependent sign.  If it is decreasing in `u`, then applied to an antitone `u` it becomes increasing in `x`, not antitone.

So the reaction part alone does not give an unconditional monotonicity-preservation theorem.

#### Chemotaxis term

Even if `u` and `V[u]` are antitone, the chemotaxis source is not forced to be antitone.

For example, in divergence form one encounters

    partial_x(u^m V_x)
      = m u^(m-1) u_x V_x + u^m V_xx.

For antitone `u` and `V`, one has `u_x <= 0` and `V_x <= 0` at smooth points, so the first term is nonnegative.  But the second term contains

    V_xx = (mu V - nu u^gamma)/d2,

which can change sign.  Moreover, the spatial derivative of this chemotaxis source has no simple one-sided sign.  Thus it is not an antitone function of `x` in any robust sense.

Conclusion:

    u antitone -> V[u] antitone is true,
    source antitone is not true in general,
    therefore T preserves antitone is not available in general.

## 2. Fixed-source linear map: exact preservation criterion

A correct Lean theorem for the fixed-source map is only this conditional statement:

    theorem greenMap_antitone_of_source_antitone
      (hK_nonneg : forall y, 0 <= K y)
      (hS_anti : Antitone S)
      (hT : T = fun x => integral K(y) * S(x-y) dy) :
      Antitone T.

Then a second theorem would be needed:

    theorem frozenSource_antitone
      (hu : Antitone u)
      (htrap : Trap u) :
      Antitone (fun x => source u x).

The second theorem is exactly what fails for the chemotaxis traveling-wave source without additional assumptions.

So for the fixed-source Schauder map, the dependency chain

    u antitone -> V antitone -> source antitone -> T(u) antitone

breaks at `source antitone`.

## 3. Correct ways to obtain a monotone wave

### Option A: monotone sub-trap plus a monotonicity-preserving map

Define a monotone trap

    K_mono = {u | lower <= u <= upper and Antitone u}.

This set is convex and closed under locally uniform convergence.  If the map `T` preserves `K_mono`, Schauder gives an antitone fixed point.

For the fixed-source linear map, preservation of `K_mono` requires the failed source-monotonicity theorem above.  Therefore this option is clean only if one uses a different map, or proves additional sign/smallness hypotheses that imply source antitonicity.

### Option B: paper-style parabolic auxiliary map

This is the mechanism used in the traveling-wave literature when monotonicity is part of the construction.

Freeze the chemical response from the input `u`, solve a parabolic auxiliary problem in the unknown `W(t,x)` starting from an antitone super-solution, and then define

    T(u) = lim_{t -> infinity} W(t, .).

To prove monotonicity, differentiate the parabolic equation in `x`.  Let

    w = W_x.

One derives a parabolic equation or inequality for `w`.  The initial data satisfies

    w(0,x) <= 0.

Under the paper's sign and parameter assumptions, the equation for `w` is suitable for the maximum principle, so

    w(t,x) <= 0

for all `t > 0`.  Hence `T(u)` is antitone.

This is how the monotonicity-preserving branch should be formalized if one wants a paper-faithful monotone construction.  The central analytic lemma is:

    AuxiliaryFlowPreservesAntitone:
      Antitone initial_superbarrier -> Antitone W(t,.) for all t -> Antitone T(u).

This route does not require the fixed-source source to be antitone.  It uses the PDE satisfied by the derivative of the auxiliary flow.

### Option C: sliding/comparison for the final stationary profile

A sliding method would try to show

    U(x+h) <= U(x) for all h > 0.

For scalar local reaction-diffusion waves this can be done by maximum principles.  For chemotaxis, the equation is nonlocal through `V[U]`, and the difference `U(x+h)-U(x)` couples to `V[U](x+h)-V[U](x)`.  The sign of the chemotaxis difference is not pointwise controlled in general.

Thus a sliding proof is possible only under a separately proved comparison structure for the coupled nonlocal system.  It is not the shortest Lean route unless the paper already proves precisely such a sliding lemma.

### Option D: avoid monotonicity

If the existence route is the fixed-source linear Schauder map on a lower-pinned barrier trap, the most honest route is to avoid monotone Liouville and use the nonmonotone left-tail route:

    left positive floor
    + left-translate compactness
    + equation closedness under limits
    + stationary Liouville/stabilization theorem
    -> left endpoint.

This avoids needing `U' <= 0`.

## 4. What the literature mechanism gives

In Salako-Shen / Chen-Ruau-Shen type traveling-wave constructions, monotonicity is not a formal consequence of a fixed-source linear Green solve.  When monotonicity is obtained, it is obtained by construction:

1. restrict the Schauder map to a monotone class; or
2. use a parabolic auxiliary problem whose spatial derivative satisfies a maximum-principle inequality; or
3. use a comparison/sliding theorem tailored to the sign regime.

For the negative-sensitivity or repulsive branch, derivative maximum-principle arguments are much more natural because the chemotaxis terms have favorable signs.  For attractive positive sensitivity, monotonicity is more delicate and may require smallness restrictions, or it may not be claimed in the same strength.  In some positive-sensitivity traveling-wave results the construction gives right-vanishing and a positive left lower limit, but not necessarily a globally monotone profile.

Therefore, for faithfulness:

- If the source paper states a monotone traveling wave, formalize the paper's monotonicity mechanism, not a fixed-source Green preservation claim.
- If the paper only states right-vanishing plus positive left limit for the positive-chi branch, do not add monotonicity.

## 5. Lean dependency chain for the fixed-source map

For the fixed-source map, the maximal true dependency chain is:

1. Chemical monotonicity:

       Antitone u -> Antitone (u^gamma) -> Antitone V[u]

   on the whole line by positive convolution.

2. Conditional source theorem:

       Antitone source(u) -> Antitone T(u)

   by positive Green convolution.

3. But `Antitone source(u)` is not derivable from the standard trap and antitonicity assumptions because of the logistic and chemotaxis terms.

Thus the fixed-source monotone Schauder theorem should be stated conditionally:

    theorem fixedSourceMap_preserves_antitone
      (hsource : forall u, Trap u -> Antitone u -> Antitone (source u)) :
      forall u, Trap u -> Antitone u -> Antitone (T u).

Then the application should **not** try to supply `hsource` unless a real proof exists.

## 6. Lean dependency chain for the paper-style monotone map

If using the auxiliary parabolic map, the right structure is:

    structure AuxiliaryMonotonicityData where
      initial_antitone : Antitone Uplus
      chemical_from_antitone : forall u, Antitone u -> Antitone (V[u])
      derivative_equation : DerivativeEquationForAuxFlow
      derivative_max_principle :
        initial_derivative_nonpos -> w_t inequality -> forall t x, w t x <= 0
      long_time_limit : W(t,.) -> T(u) locally uniformly
      derivative_sign_passes_to_limit :
        (forall t, Antitone (W t)) -> Antitone (T u)

Then:

    theorem auxiliaryMap_preserves_antitone
      (H : AuxiliaryMonotonicityData) :
      forall u, Trap u -> Antitone u -> Antitone (T u).

Then Schauder on

    K_mono = Trap ∩ Antitone

gives an antitone fixed point.

This is the clean monotone construction.

## 7. Lean dependency chain for sliding

If choosing sliding, isolate it as a final-profile theorem:

    theorem stationaryProfile_antitone_of_sliding
      (hstat : StationaryProfile U)
      (hright : Tendsto U atTop 0)
      (hleftFloor : StrictlyPositiveAtLeft U)
      (hcomparison : SlidingComparisonPrincipleForChemotaxis p) :
      Antitone U.

The hard input is `SlidingComparisonPrincipleForChemotaxis`.  It must encode all signs and nonlocal comparison facts.  Without that, the theorem is not available.

## 8. Recommended final choice

For the current fixed-source Schauder route in a lower-pinned barrier trap:

    Do not claim antitonicity of the fixed point.

Use the nonmonotone left-tail Liouville/stabilization route unless the final theorem explicitly needs monotonicity.

If monotonicity is required, switch to one of these faithful architectures:

1. use the paper's parabolic auxiliary map and prove derivative maximum-principle preservation;
2. restrict to a monotone sub-trap only after proving the chosen map preserves it;
3. carry a separate sliding theorem for stationary profiles.

The exact bottom line is:

    fixed-source T preserves antitone only if its frozen source is antitone;
    the chemotaxis-logistic source is not antitone in general;
    therefore antitone fixed point requires extra structure beyond the lower-pinned barrier Schauder construction.
