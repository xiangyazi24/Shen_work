ANSWER Q100 95f9f1ac

# Verdict

Your audit of the legacy pointwise route is substantially correct.

1. The current MoserDissipationDropBefore is over-quantified and false for the intended solution class. The universal quantification over every A B K L_const is a statement-level defect. In fact, the failure persists even after restricting to B ≥ 0.

1. The theorem moser_step_of_energy_dissipation_relative_interpolation is logically valid only conditionally on that overstrong predicate. Its linarith is fine; the invalid part is the expectation that the PDE can supply hdiss.

1. Your integrated replacement is the correct direction, but henergy + hrel + sup Y_p alone gives only a time-integral bound for Y_{p+ρ}. It does not by itself imply sup_t Y_{p+ρ}(t). A second dynamic ingredient at exponent q=p+ρ is required: either a first-crossing argument using the integrated q-energy inequality, or a genuine differential inequality at exponent q followed by Grönwall/uniform Grönwall.

1. The repository already contains most of the right parallel architecture. In particular, P3MoserDissipationShape.lean, P3MoserIntegratedDissipationPDEv2.lean, P3MoserHighExcursionProducer.lean, and P3MoserThresholdPlanProducer.lean implement the correct integrated/first-crossing shape. The remaining architectural action is to stop routing the main closure through the legacy MoserDissipationDropBefore chain.

The one correction to your wording is that choosing L large does not make the premise “vacuously true”; it makes the antecedent energy inequality actually true. The contradiction is stronger for that reason.

# (a) Audit of claims (i) and (ii)

## (i) The universal hdiss predicate is unsound

The exact legacy definition in IntervalDomainMoserClosure.lean is morally:

```javascript
def MoserDissipationDropBefore ... : Prop :=
  ∀ p, p0 ≤ p → ∀ A B K L,
    (∀ t ∈ (0,T),
      (1/p) * Yp'(t) + A*Gp(t) + B*Yp(t) ≤ K*Yq(t) + L) →
    ∀ t ∈ (0,T),
      0 ≤ (1/p) * Yp'(t) + B*Yp(t)
```

where

```plain text
Yp(t) = ∫ u(t)^p,
Gp(t) = ∫ |∇u(t)^(p/2)|²,
Yq(t) = ∫ u(t)^(p+ρ).
```

A direct positive counterexample is a spatially constant decreasing solution. Take a unit-volume abstract domain, p>0, and

```plain text
u(t,x) = exp(-c t),   c>0.
```

Then

```plain text
Gp(t) = 0,
Yp(t) = exp(-c p t),
(1/p)Yp'(t) = -c exp(-c p t) < 0.
```

Choose

```plain text
A = 0, B = 0, K = 0, L = 0.
```

The antecedent is true:

```plain text
(1/p)Yp'(t) ≤ 0.
```

But the conclusion demands

```plain text
0 ≤ (1/p)Yp'(t),
```

which is false. This is not an artificial behavior: spatially constant logistic solutions with negative net reaction can have decreasing L^p moments.

The repository now independently records essentially this diagnosis. P3MoserDissipationShape.lean says that the old predicate quantifies arbitrary B, that merely requiring B ≥ 0 does not repair the analytic issue, and it includes the theorem

```javascript
unitLinearDrop_not_MoserDissipationDropBeforeNonnegB
```

showing failure even for the restricted nonnegative-B version.

Therefore claim (i) is correct.

## (ii) Restricting to the physical constants does not derive the pointwise drop

Suppose the PDE supplies its own coefficients A>0, B>0, K>0, L and

```plain text
(1/p)Yp' + A Gp + B Yp ≤ K Yq + L.       (E_p)
```

The desired deletion condition is

```plain text
0 ≤ (1/p)Yp' + B Yp.                     (D_p)
```

Combining (E_p) and (D_p) gives

```plain text
A Gp ≤ K Yq + L.
```

But (D_p) is not a consequence of (E_p). Rewriting the PDE energy identity schematically gives

```plain text
(1/p)Yp' = -A Gp + chemotaxis + reaction.
```

A lower bound for the left side therefore contains the negative term -A Gp. Unless one already has an upper bound for Gp, or a separate monotonicity/comparison principle that controls the full right side, the proposed lower bound is unavailable. In this route, bounding Gp is precisely the objective, so deriving (D_p) from the same energy calculation is circular.

A nuance: the pointwise theorem is not a logical contradiction if hdiss is supplied by some independent theorem. There are special equations or special parameter regimes where a quantity e^{Bt}Yp(t) might truly be nondecreasing. But no such independent mechanism exists here, and ordinary dissipative chemotaxis/logistic solutions can have decreasing moments. Thus the conditional Lean theorem is logically sound, while the intended PDE producer is not.

Claim (ii) is therefore correct as an audit of the intended construction.

# (b) Exact integrated Moser step

## Step 1: notation and the physical energy inequality

Fix p>0 and put q=p+ρ. Define

```plain text
Yp(t) := ∫ u(t,x)^p dx,
Gp(t) := ∫ |∇(u(t)^(p/2))|² dx,
Yq(t) := ∫ u(t,x)^q dx.
```

Assume the physical witness gives

```plain text
(1/p)Yp'(t) + A Gp(t) + B Yp(t)
  ≤ K Yq(t) + L,                         (1)
```

with A>0, K≥0. In the present repository interface the energy producer supplies B>0, not an arbitrary negative B. This is visible in the newer LpBootstrapEnergyInequalityWithGap:

```javascript
∃ A > 0, ∃ B > 0, ∃ K > 0, ∃ L, ...
```

The positive B Yp term is retained damping. Nonetheless, the algebra below also handles a future interface with arbitrary B.

Assume relative interpolation

```plain text
Yq(t) ≤ ε Gp(t) + Cε Yp(t),              (2)
```

where Cε≥0.

## Step 2: choose ε and retain a positive gradient coefficient

Multiply (1) by p:

```plain text
Yp' + pA Gp + pB Yp ≤ pK Yq + pL.
```

Substitute (2):

```plain text
Yp' + (pA-pKε)Gp
  ≤ p(K Cε-B)Yp + pL.                    (3)
```

There are two useful choices.

### Flexible coefficient choice

Set

```plain text
θ := pA/2,
ε := A/(2K)                 if K>0.
```

Then

```plain text
pKε = pA/2,
pA-pKε = θ > 0.
```

If K=0, no absorption is needed; choose any positive ε and take θ=pA.

### Repository fixed-coefficient choice

The current integrated route normalizes the surviving coefficient to θ=2. For this, require the same-witness gap

```plain text
2 < pA.                                         (4)
```

Choose any ε>0 satisfying

```plain text
pKε ≤ pA-2.                                     (5)
```

For example, when K>0,

```plain text
ε := (pA-2)/(2pK)
```

is positive and satisfies (5). The repository packages exactly this scalar choice in

```javascript
exists_pos_eps_mul_le_sub_of_coeff_gap
```

and attaches the gap to the same A in

```javascript
LpBootstrapEnergyInequalityWithGap.
```

This same-witness requirement matters: a separately quantified statement saying “some energy coefficient has a gap” would repeat the original quantifier bug.

## Step 3: handle B and L

Let

```plain text
dp := max 0 (K*Cε - B),
lp := max 0 L.
```

Because Yp≥0, (3) and θ≤pA-pKε imply

```plain text
Yp'(t) + θ Gp(t)
  ≤ p*dp*Yp(t) + p*lp
  ≤ p*(dp+lp)*max(1,Yp(t)).                    (6)
```

Thus one may take

```plain text
Cp := dp + lp
    = max 0 (K*Cε-B) + max 0 L.                (7)
```

For the actual repository convention B>0, a slightly coarser but simpler bound is

```plain text
Cp := K*Cε + max 0 L,
```

because the favorable term -pB Yp can simply be discarded.

This explains the logistic sign convention cleanly:

- B>0: favorable damping on the left;

- B=0: neutral;

- B<0: growth, paid for by adding max 0 (-B) or, more sharply, by max 0 (K*Cε-B) to Cp.

## Step 4: integrate on a closed time window

Assume the FTC/integrability bridge needed to integrate Yp'. For 0≤t1≤t2≤T, integrate (6):

```plain text
Yp(t2)-Yp(t1) + θ ∫[t1,t2] Gp(s) ds
  ≤ Cp*p ∫[t1,t2] max(1,Yp(s)) ds.             (8)
```

This is the honest replacement for the pointwise drop. In the repository it is represented by

```javascript
IntegratedMoserDissipationDropBeforeCoeff θ ...
```

and the fixed θ=2 specialization is

```javascript
IntegratedMoserDissipationDropBefore.
```

The newer chain derives this from the strict-time energy witness through:

```plain text
LpBootstrapEnergyInequalityWithGap
  + IntegratedMoserEnergyWindowFTC
  + time integrability/nonnegativity
  + RelativeMoserInterpolationBefore
  → IntegratedMoserDissipationDropBefore.
```

## Step 5: what the previous Lp bound actually gives

Assume

```plain text
Yp(t) ≤ Mp       for all 0<t<T.
```

Set

```plain text
M := max 1 Mp,
Tbar := max 1 T.
```

From (8), using Yp(t1)≤M, Yp(t2)≥0, and

```plain text
∫[t1,t2] max(1,Yp) ≤ (t2-t1)M ≤ Tbar*M,
```

we get

```plain text
∫[t1,t2] Gp
  ≤ [M + Cp*p*Tbar*M]/θ.                       (9)
```

Define

```plain text
Gbar := [M + Cp*p*Tbar*M]/θ.                   (10)
```

With the repository normalization θ=2, this is

```plain text
Gbar = (M + Cp*p*(Tbar*M))/2.
```

Now apply relative interpolation with a possibly different parameter η>0:

```plain text
Yq(s) ≤ η Gp(s) + Cη Yp(s).
```

Integrating and using (9):

```plain text
∫[t1,t2] Yq(s) ds
  ≤ η Gbar + Cη*(t2-t1)*M
  ≤ η Gbar + Cη*Tbar*M.                        (11)
```

Set

```plain text
R := η Gbar + Cη*Tbar*M.                       (12)
```

This is only a sliding-window integral bound for Yq. It is not yet a pointwise bound. Continuous functions can have arbitrarily tall narrow spikes while keeping a bounded time integral. Therefore the proposed theorem cannot conclude LpPowerBoundedBefore q from only (8), interpolation, and sup Yp.

## Step 6: convert the average q-bound into a pointwise q-bound

The clean route already implemented in the repository is a first-crossing argument using the integrated energy inequality at exponent q as well.

Assume

```plain text
Yq(t2)-Yq(t1) + θq ∫[t1,t2] Gq
  ≤ Cq*q ∫[t1,t2] max(1,Yq(s)) ds,             (13)
```

with Cq≥0, plus:

- continuity of Yq on [0,T];

- an initial bound Yq(0)≤C0;

- nonnegativity of the gradient time integral.

### Case Cq=0

Equation (13) gives

```plain text
Yq(t2) ≤ Yq(t1),
```

so Yq(t)≤C0.

### Case Cq>0

Choose

```plain text
K0 := max(1,
          C0+1,
          Cq*q*(R+1)+1).                        (14)
```

I claim

```plain text
Yq(t) ≤ 2K0     for all 0<t<T.                 (15)
```

Suppose instead that Yq(t)>2K0. By continuity and Yq(0)<K0, take the last exit time a<t such that

```plain text
Yq(a)=K0,
Yq(s)≥K0≥1 on [a,t].
```

Apply (13) on [a,t]. Since Gq has nonnegative integral and max(1,Yq)=Yq on this window,

```plain text
Yq(t)-K0 ≤ Cq*q ∫[a,t] Yq(s) ds.
```

Because Yq(t)>2K0,

```plain text
K0 < Cq*q ∫[a,t]Yq(s) ds,
K0/(Cq*q) < ∫[a,t]Yq(s) ds.                    (16)
```

But (11) gives

```plain text
∫[a,t]Yq(s) ds ≤ R.                            (17)
```

The choice (14) gives

```plain text
Cq*q*(R+1) < K0,
R+1 < K0/(Cq*q),
```

contradicting (16)–(17). Hence (15) follows.

These are essentially the exact constants already used in P3MoserThresholdPlanProducer.lean:

```plain text
M     = max 1 Mraw,
Tbar  = max 1 T,
Gbar  = (M + Cp*p*(Tbar*M))/2,
R     = Gbar + Tbar*(Ceps*M),       -- η=1
K     = max 1 (max (C0+1) (Cq*q*(R+1)+1)),
next exponent bound = 2*K.
```

The contradiction theorem is

```javascript
LpPowerBoundedBefore_of_crossingThresholdPlan.
```

The assembler is

```javascript
integratedMoserFirstCrossingStep_of_abstract_data.
```

Therefore the exact corrected induction is:

```plain text
bounded Yp
  → p-level integrated drop bounds ∫Gp
  → interpolation bounds ∫Yq
  → q-level integrated drop + continuity + initial q bound
  → first-crossing contradiction
  → bounded Yq.
```

## Grönwall alternative

A Grönwall route is also valid, but it requires more than the integrated p estimate. If, after applying interpolation at exponent q, one obtains a pointwise differential inequality

```plain text
Yq'(t) ≤ aq Yq(t) + bq,                         (18)
```

then

```plain text
Yq(t) ≤ exp(aq(t-t0))Yq(t0)
        + (bq/aq)(exp(aq(t-t0))-1)              if aq>0,
```

with the obvious aq=0 form. This directly gives a finite-horizon pointwise bound from an initial q bound.

Uniform Grönwall can instead combine a sliding-window average bound for Yq with (18). But in Lean it introduces window-length choices and a separate early-time argument. The repository’s last-exit/first-crossing implementation is already complete and is the preferable route.

# (c) Relation to standard Alikakos–Moser chemotaxis arguments

Yes. Standard Alikakos–Moser iteration avoids the bad lower bound on the time derivative.

The canonical pattern is one of the following:

```plain text
Yk' + ck Dk ≤ C bk F(Yk-1),
```

followed by an ODE comparison/Grönwall estimate at level k, or

```plain text
integrated energy at level k-1
  → average control at level k
  → differential/first-crossing control at level k
  → pointwise level-k bound.
```

It does not assume

```plain text
Yk' + Bk Yk ≥ 0
```

in order to erase the derivative. Negative time derivatives are normal and useful in a dissipative parabolic equation.

References worth mirroring:

1. N. D. Alikakos, “L^p Bounds of Solutions of Reaction-Diffusion Equations,” Communications in Partial Differential Equations 4 (1979), 827–868, DOI 10.1080/03605307908820113. This is the foundational parabolic Moser–Alikakos reference.

1. Y. Tao and M. Winkler, “Boundedness in a Quasilinear Parabolic-Parabolic Keller-Segel System with Subcritical Sensitivity,” Journal of Differential Equations 252 (2012), 692–715; arXiv 1106.5345. The paper explicitly describes its final boundedness step as a modified Moser–Alikakos iteration. It is a good chemotaxis-specific model for deriving recursive differential inequalities and closing them without any lower bound on Y'.

1. M. Winkler, “Boundedness in the Higher-Dimensional Parabolic-Parabolic Chemotaxis System with Logistic Source,” Communications in Partial Differential Equations 35 (2010), 1516–1537, DOI 10.1080/03605300903473426. This is the closest standard logistic-chemotaxis reference.

For the exact Lean route, however, the repository’s existing first-crossing implementation is more directly reusable than importing a paper’s final p_k→∞ recursion verbatim. Tao–Winkler’s appendix is best treated as conceptual precedent for the terminal Moser–Alikakos step, not as a substitute for the finite-exponent p→p+ρ first-crossing proof now present in the repo.

# (d) Minimal Lean interface change

## Keep the old predicate only as legacy API

You can keep

```javascript
MoserDissipationDropBefore
```

for source compatibility, but it should be clearly marked legacy/deprecated and must not be required by any new main closure theorem. Do not try to repair it merely by adding 0≤B; P3MoserDissipationShape.lean already proves that the nonnegative-B pointwise shape can still fail.

Similarly, preserve

```javascript
moser_step_of_energy_dissipation_relative_interpolation
moser_iteration_chain_of_energy_dissipation_relative_interpolation
```

only as conditional legacy lemmas.

## Preferred new input bundle

The current parallel files already suggest the right components:

```javascript
LpBootstrapEnergyInequalityWithGap
IntegratedMoserEnergyWindowFTC
IntegratedMoserFirstCrossingRegularity
IntegratedMoserEnergyNonnegativity
RelativeMoserInterpolationBefore
```

The coefficient gap must be attached to the same A supplied by the energy witness:

```javascript
def LpBootstrapEnergyInequalityWithGap ... : Prop :=
  ∀ p, p0 ≤ p →
    ∃ A > 0, ∃ B > 0, ∃ K > 0, ∃ L,
      energy_inequality A B K L ∧
      2 < p*A
```

A more general and slightly cleaner interface would parameterize the surviving coefficient:

```javascript
structure IntegratedMoserAbsorptionWitness (p A K : ℝ) where
  theta : ℝ
  theta_pos : 0 < theta
  eps : ℝ
  eps_pos : 0 < eps
  absorb : p*K*eps ≤ p*A-theta
```

Then no arbitrary normalization to 2 is needed. The existing fixed-2 implementation is acceptable because the repository has already proved the explicit pA>2 threshold for its AcoefPDep.

## New chain theorem

The minimal public replacement should have a shape like:

```javascript
theorem moser_iteration_chain_time_integrated
    {u : ℝ → intervalDomain.Point → ℝ}
    {T p0 rho : ℝ}
    (hboot : AbstractLpBootstrapHypothesis
      intervalDomain u N T rho p0)
    (henergyGap : LpBootstrapEnergyInequalityWithGap
      intervalDomain u T rho p0)
    (hFTC : IntegratedMoserEnergyWindowFTC
      intervalDomain u T p0)
    (hreg : IntegratedMoserFirstCrossingRegularity
      intervalDomain u T p0)
    (hnonneg : IntegratedMoserEnergyNonnegativity
      intervalDomain u T p0)
    (hrel : RelativeMoserInterpolationBefore
      intervalDomain u T rho p0) :
    ∀ n : ℕ,
      LpPowerBoundedBefore intervalDomain (p0 + n*rho) T u := by
  have hdiss : IntegratedMoserDissipationDropBefore
      intervalDomain u T rho p0 :=
    intervalDomain_integratedMoserDissipationDropBefore_of_energyWithGap
      hboot henergyGap hFTC hreg hnonneg hrel

  have hstep : IntegratedMoserFirstCrossingStep
      intervalDomain u T rho p0 :=
    intervalDomain_integratedMoserFirstCrossingStep_of_abstract_data
      hreg hnonneg hdiss hrel
      hboot.rho_pos
      (by derive 0 ≤ p0 from the bootstrap threshold)

  intro n
  induction n with
  | zero => simpa using hboot.initial_lp_bound
  | succ n ih =>
      have hp : p0 ≤ p0 + n*rho := by positivity/linarith
      simpa [Nat.cast_add, add_assoc, mul_add] using
        hstep (p0+n*rho) hp ih
```

At a higher level, bundle these fields into something like:

```javascript
structure IntervalDomainTimeIntegratedMoserBootstrapData ... where
  boot : AbstractLpBootstrapHypothesis ...
  energyGap : LpBootstrapEnergyInequalityWithGap ...
  windowFTC : IntegratedMoserEnergyWindowFTC ...
  regularity : IntegratedMoserFirstCrossingRegularity ...
  energyNonneg : IntegratedMoserEnergyNonnegativity ...
  relativeInterpolation : RelativeMoserInterpolationBefore ...
```

and expose

```javascript
TimeIntegratedMoserBootstrapData.moserChain
TimeIntegratedMoserBootstrapData.allFiniteExponents
TimeIntegratedMoserBootstrapData.boundedBefore
```

## Important correction to “consume only henergy + hrel + previous bound”

That interface is too small. At minimum, the proof also needs:

1. p>0 and ρ>0;

1. an absorption surplus for the actual energy coefficient A;

1. FTC/differentiability and interval integrability to convert Y' into endpoint differences;

1. nonnegativity of Yp and integrated gradient energies;

1. continuity of Yq for last-exit selection;

1. an initial or early-time bound for Yq;

1. the integrated energy/drop inequality at exponent q.

Most of these are routine consequences of IsPaper2ClassicalSolution on [0,1], but Lean must carry them explicitly. The repository’s IntegratedMoserFirstCrossingRegularity is exactly the correct package for items 3, 5, and 6.

# Recommended migration order

1. Leave legacy declarations in place so imports do not break.

1. Mark MoserDissipationDropBefore and its old chain as legacy/unsafe-for-PDE-closure in comments or deprecation attributes.

1. Use the already-proved LpBootstrapEnergyInequalityWithGap producer with the p-dependent AcoefPDep.

1. Produce IntegratedMoserDissipationDropBefore through P3MoserIntegratedDissipationPDEv2.

1. Produce IntegratedMoserFirstCrossingStep through P3MoserThresholdPlanProducer.

1. Add moser_iteration_chain_time_integrated and rewire the all-exponent and endpoint consumers to it.

1. Remove dissipation : MoserDissipationDropBefore ... from the main structured bootstrap data, replacing it by the integrated packages or by a single derived IntegratedMoserFirstCrossingStep field.

# Final assessment

- (i): confirmed. The universal coefficient quantification is a real statement defect; the predicate is false even with nonnegative B.

- (ii): confirmed for the intended PDE producer. The pointwise derivative lower bound is independent and, in this route, circular to obtain.

- Integrated fix: validated with one essential amendment. The integrated p estimate yields ∫Y_{p+ρ}, not sup Y_{p+ρ}. Add the already-formalized q-level first-crossing step.

- B handling: the current physical Lean witness has B>0; retain it as favorable damping. The formula with arbitrary B is Cp=max 0 (K Cε-B)+max 0 L.

- Best Lean change: keep legacy APIs but route all new closure through LpBootstrapEnergyInequalityWithGap → IntegratedMoserDissipationDropBefore → IntegratedMoserFirstCrossingStep → Nat exponent chain.

This is not merely a conceptual recommendation: the repository already contains the needed integrated scalar algebra and first-crossing machinery. The week-saving move is to rewire the main Paper 2 closure to that path rather than trying to manufacture a producer for the old hdiss predicate.