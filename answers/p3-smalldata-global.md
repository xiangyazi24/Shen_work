# Paper 3: small-data global existence near the positive equilibrium

## Verdict

After the linearized per-mode spectral gap has been established, the small-data global existence part of Theorem 2.2 is best formalized as a Duhamel fixed-point theorem in an exponentially weighted fractional-domain space.  The genuinely PDE-specific work is not the contraction algebra; it is proving the linear fractional semigroup bound and the quadratic chemotaxis remainder estimate near the positive equilibrium.

The perturbation is

    z(t) = u(t) - u_*,

where

    u_* = (a / b)^(1 / alpha),
    v_* = (nu / mu) * u_*^gamma.

Write the perturbation equation abstractly as

    z_t + A z = -N(z),
    z(0) = z0,

where A is the positive linearized operator and N is the nonlinear remainder.  The mild equation is

    z(t) = exp(-t A) z0 - integral_0^t exp(-(t-s) A) N(z(s)) ds.

The clean Lean target is this integrated Duhamel equation with an exponentially weighted sup norm.

## 1. Abstract contraction setup

Fix sigma in (1/2, 1), choose theta with 0 < theta < omega, and assume the fractional smoothing estimate

    ||A^sigma exp(-t A)|| <= M_sigma * t^(-sigma) * exp(-omega t).

Also assume the semigroup is bounded in the fractional norm:

    ||exp(-t A) z0||_sigma <= M0 * exp(-omega t) * ||z0||_sigma.

Work in the Banach space

    Y_{theta,sigma} = { z : [0,infty) -> D(A^sigma) continuous,
                         sup_{t >= 0} exp(theta t) ||z(t)||_sigma < infinity },

with norm

    ||z||_Y = sup_{t >= 0} exp(theta t) ||z(t)||_sigma.

Assume the nonlinear remainder is quadratic/Lipschitz on the sigma-ball of radius r:

    ||N(z) - N(w)|| <= K * (||z||_sigma + ||w||_sigma) * ||z - w||_sigma,

and N(0)=0.  Hence

    ||N(z)|| <= K * ||z||_sigma^2.

Define

    I_{sigma,omega,theta} = integral_0^infty tau^(-sigma) exp(-(omega-theta) tau) dtau.

This is finite because 0 < sigma < 1 and omega > theta.  Equivalently,

    I_{sigma,omega,theta} = Gamma(1 - sigma) * (omega - theta)^(sigma - 1).

For the Duhamel map Phi,

    Phi(z)(t) = exp(-t A) z0 - integral_0^t exp(-(t-s)A) N(z(s)) ds,

one gets, on the ball ||z||_Y <= r,

    ||Phi z||_Y <= M0 ||z0||_sigma
                 + M_sigma K I_{sigma,omega,theta} ||z||_Y^2,

and for z,w in the same ball,

    ||Phi z - Phi w||_Y <= 2 M_sigma K r I_{sigma,omega,theta} ||z - w||_Y.

Thus Phi is a contraction if

    2 M_sigma K r I_{sigma,omega,theta} <= 1/2,

and it maps the ball to itself if

    M0 ||z0||_sigma + M_sigma K I_{sigma,omega,theta} r^2 <= r.

A convenient sufficient smallness threshold is

    epsilon = min { r / (2 M0),
                    1 / (8 M0 M_sigma K I_{sigma,omega,theta}) }.

The important logical content is:

    ||z0||_sigma <= epsilon
      -> exists a unique global mild solution z
      -> ||z(t)||_sigma <= r exp(-theta t).

The exact numerical constants can be adjusted, but the proof should keep the same structure: one linear term controlled by M0 ||z0||_sigma and one quadratic Duhamel term controlled by M_sigma K I r^2.

## 2. What is standard and what is genuine

The following are standard semigroup/contraction bookkeeping once the constants are supplied:

1. definition of the exponentially weighted space Y_{theta,sigma};
2. Duhamel map Phi;
3. convolution estimate with I_{sigma,omega,theta};
4. ball invariance;
5. contraction estimate;
6. global mild solution and exponential decay.

The genuine analytic obligations are:

1. the per-mode spectral gap for the linearized operator;
2. the fractional smoothing bound for exp(-tA);
3. the embedding D(A^sigma) -> L^infty, and product estimates in that space;
4. the quadratic estimate for the chemotaxis nonlinear remainder;
5. the mild-to-classical upgrade if the theorem is stated for classical solutions.

The nonlinear estimate is the main PDE step.  Around the positive equilibrium, powers such as u^m and u^gamma are smooth functions of the perturbation, and the elliptic resolver for v is linear in the source u^gamma.  For small ||z||_sigma, all remainder terms are at least quadratic, giving the desired Lipschitz-quadratic bound.

## 3. Mathlib / Lean route

Do not rely on Mathlib having a ready-made sectorial-operator and fractional-power analytic-semigroup theorem for this PDE.  The safer route is project-local.

The linear part should be built from the cosine Neumann spectrum on (0,1).  The unit-interval eigenvalues are

    lambda_k = k^2 * pi^2.

If the spectral gap gives positive decay rates a_k >= delta on the nonzero modes, then modewise

    exp(-a_k t) <= exp(-delta t).

For fractional smoothing, use the scalar estimate

    r^sigma exp(-r t) <= (sigma / e)^sigma t^(-sigma),

or, with a gap,

    r^sigma exp(-r t)
      <= (2 sigma / e)^sigma t^(-sigma) exp(-delta t / 2)

for r >= delta.  This gives the concrete bound

    ||A^sigma exp(-tA) P0^perp|| <= M_sigma t^(-sigma) exp(-omega t),

with omega = delta / 2 up to harmless constants.  This per-mode proof is the cleanest Lean path.

The project should therefore have three layers:

Layer A: spectral layer.

    LinearlyStable -> exists delta > 0, forall k != 0, delta <= modeDecayRate k.

Then prove the modewise fractional decay estimate from the scalar inequality above.

Layer B: abstract Duhamel fixed point.

    Given M0, M_sigma, K, I, r, theta, omega, prove small-data global mild existence in the weighted space.

Layer C: PDE nonlinear layer.

    Prove the chemotaxis remainder satisfies the quadratic Lipschitz estimate in D(A^sigma), and prove the mild solution is the classical solution required by the Paper 3 statement.

This separation is the most Lean-friendly architecture.

## 4. Clean Lean-formalizable statement

A good abstract theorem shape is:

    theorem smallDataGlobalMild_of_quadratic_duhamel
      (linear_bound : forall t >= 0, ||S0 t z0||_sigma <= M0 * exp(-omega*t) * ||z0||_sigma)
      (smooth_bound : forall tau > 0, ||S tau f||_sigma <= M_sigma * tau^(-sigma) * exp(-omega*tau) * ||f||)
      (quad_bound : forall z w in ball r,
           ||N z - N w|| <= K * (||z||_sigma + ||w||_sigma) * ||z-w||_sigma)
      (kernel_int : forall t >= 0,
           integral_0^t tau^(-sigma) * exp(-(omega-theta)*tau) dtau <= I)
      (small : ||z0||_sigma <= epsilon)
      (eps_le : epsilon <= min (r/(2*M0)) (1/(8*M0*M_sigma*K*I))) :
        exists z,
          (forall t >= 0,
             z t = S0 t z0 - integral_0^t S (t-s) (N (z s)) ds) and
          (forall t >= 0, ||z t||_sigma <= r * exp(-theta*t)).

For the interval-domain chemotaxis theorem, wrap the PDE-specific assumptions in a structure:

    structure IntervalSmallDataStabilityData where
      sigma_range : 1/2 < sigma and sigma < 1
      theta_pos : 0 < theta
      theta_lt_omega : theta < omega
      linear_gap : LinearizedModeGap unitIntervalNeumannSpectrum p uStar vStar omega
      smoothing : FractionalSemigroupSmoothing p uStar vStar sigma omega M_sigma
      embedding : FractionalDomainEmbedsLinf p sigma
      quadratic : ChemotaxisNonlinearRemainderQuadratic p uStar vStar sigma K
      mild_classical_upgrade : MildSmallSolutionClassical p uStar vStar sigma

Then state:

    theorem interval_smallDataGlobalExistence_of_spectralGap_and_quadratic
      (ha : 0 < p.a) (hb : 0 < p.b)
      (hstable : LinearlyStable unitIntervalNeumannSpectrum p uStar vStar)
      (H : IntervalSmallDataStabilityData p uStar vStar) :
        exists epsilon > 0,
          SmallDataGlobalExistence intervalDomain p uStar epsilon.

Here uStar and vStar are the positive equilibrium values.

## 5. Relation to the existing sectorial frontier

The current interval-domain sectorial statement should remain a frontier rather than pretending the nonlinear Duhamel estimate follows from spectral decay alone.  The right boundary is:

    spectral decay of the concrete Neumann semigroup
    + nonlinear Duhamel small-data comparison
    -> SectorialLocalExponentialRaw / SmallDataGlobalExistence.

This is exactly the correct mathematical split.  The per-mode spectral gap is necessary for the linear exponential decay, but local nonlinear stability and small-data global existence require the quadratic remainder estimate and the Duhamel contraction.

## 6. Final recommended target

Formalize the abstract weighted-sup Duhamel contraction first.  Then instantiate it for the chemotaxis perturbation once these four concrete facts are available:

1. per-mode gap a_k >= delta;
2. fractional semigroup smoothing bound from the cosine spectrum;
3. D(A^sigma) embedding/product estimates;
4. quadratic chemotaxis remainder estimate near the positive equilibrium.

This gives the small-data global solution and exponential decay with explicit smallness threshold

    epsilon = min { r / (2 M0),
                    1 / (8 M0 M_sigma K I_{sigma,omega,theta}) }.
