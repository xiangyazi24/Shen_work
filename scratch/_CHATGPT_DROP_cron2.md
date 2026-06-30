# Q2572 (cron2): LowerAverageWindow and UpperGapWitness

GitHub-connector only. No Python, sandbox, `/mnt/data`, or local filesystem access was used.

## Short answer

For one Moser step write

```text
Y(s) := integratedMoserEnergy D u p s
Z(s) := integratedMoserEnergy D u (p+rho) s
G(s) := integratedMoserGradientEnergy D u p s
q := p + rho
```

The correct high-excursion construction uses two levels.  Choose a mid-level `K`, set

```text
Cnext := 2*K,
```

and, if `Z(t) > Cnext`, let `b := t` and let `a` be the last time before `t` at which `Z <= K`:

```text
a := max { s in [0,t] | Z(s) <= K }.
```

Then `0 < a < b < T`, `Z(a) = K`, and `K <= Z(s)` on `[a,b]`.  The current-exponent bound is

```text
M := max 1 Mp,
```

where `Mp` is the witness from `LpPowerBoundedBefore D p T u`.  Thus `1 <= M` and `Y(s) <= M` for all `0 < s < T`, hence on `[a,b]`.

The lower bound should be **length-free**:

```text
lowerBound := K / (Cq*q),
```

where `Cq > 0` is a positive integrated-drop constant at exponent `q=p+rho`.  This is stronger than the continuity-only bound `(b-a)*K`, and it is the bound needed to beat the `eps*Gbound` term in the relative-Moser upper estimate.

## LowerAverageWindow construction

Inputs needed for exponent `p`:

```text
hLp       : LpPowerBoundedBefore D p T u
hreg      : IntegratedMoserFirstCrossingRegularity D u T p0
hdrop     : IntegratedMoserDissipationDropBefore D u T rho p0
hgradNon  : gradient time-integrals are nonnegative
hp        : p0 <= p
hp_nonneg : 0 <= p
rho_pos   : 0 < rho
```

Let `q := p+rho`.  From `hreg.initialPowerBound q` choose `C0` with `Z(0) <= C0`.  Choose `K` with

```text
max 1 C0 < K.
```

This strict inequality guarantees that the last-exit time is not `0`, so the existing wrappers requiring `0 < a` can be used.

Given `0 < t < T` and `2*K < Z(t)`, continuity of `Z` on `[0,T]` gives a last-exit time `a` satisfying

```text
0 < a < t,          b := t,
Z(a) = K,
K <= Z(s) on Icc a b.
```

Apply the integrated drop at exponent `q` on `[a,b]` with a positive constant `Cq`:

```text
Z(b) - Z(a) + 2 * ∫ s in a..b, G_q(s)
  <= Cq*q * ∫ s in a..b, max 1 (Z(s)).
```

Since `K >= 1` and `K <= Z(s)` on `[a,b]`, `max 1 (Z(s)) = Z(s)`.  Since the gradient integral is nonnegative and `Z(b) > 2K`, `Z(a)=K`,

```text
K < Z(b)-Z(a) <= Cq*q * ∫ s in a..b, Z(s).
```

Therefore

```text
K/(Cq*q) <= ∫ s in a..b, Z(s).
```

So the window fields are exactly

```text
b          := t
a          := last exit below K
M          := max 1 Mp
lowerBound := K/(Cq*q)
Cnext      := 2*K
```

The literal average estimate `K <= (1/(b-a))*∫Z` is also true, but it is not the estimate that closes the contradiction.

## UpperGapWitness construction

Use the current-exponent integrated drop at exponent `p` with constant `Cp >= 0`.  For the selected window, the existing fixed-window extraction gives

```text
∫ s in a..b, G(s) <= Gbound,
Gbound := (M + Cp*p*((b-a)*M))/2.
```

Set

```text
Tbar := max 1 T,
Gbar := (M + Cp*p*(Tbar*M))/2.
```

Since `0 <= b-a <= T <= Tbar`, `0 <= p`, `0 <= Cp`, and `1 <= M`, we have `Gbound <= Gbar`.

Now choose a positive epsilon, for example

```text
eps := 1/(4 * max 1 Gbar)
```

(or simply `eps := 1`; the threshold can absorb the resulting constant).  From `RelativeMoserInterpolationBefore` at this exact `eps`, choose the tied constant `Ceps >= 0` such that

```text
Z(s) <= eps*G(s) + Ceps*Y(s)    for 0 < s < T.
```

Define

```text
R := eps*Gbar + Tbar*(Ceps*M).
```

Choose `K` large enough so that both the initial condition above and the strict gap condition hold:

```text
max 1 C0 < K,
(Cq*q)*(R+1) < K.
```

Then, for every last-exit window produced from `Z(t) > 2*K`,

```text
eps*Gbound + (b-a)*(Ceps*M)
  <= eps*Gbar + Tbar*(Ceps*M)
  = R
  < K/(Cq*q)
  = lowerBound.
```

This is exactly the `upper_lt_lower` field of `IntegratedMoserWindowUpperGapWitness`.

## Quantifier order

The safe order is

```text
M, Cp, Cq, eps, Ceps  ->  K  ->  Cnext=2K  ->  last-exit window  ->  contradiction.
```

Do **not** fix an arbitrary `Cnext` first and then hope to find `eps`; without explicit control of the function `eps ↦ Ceps`, this is not justified.  The threshold `K` must be chosen after the tied `Ceps` for the chosen `eps` is known, or the upper-gap lemma must assume the corresponding threshold inequality as a hypothesis.

## Lean-facing brick statements

Recommended new file:

```lean
import ShenWork.PDE.P3MoserIntegratedClosure

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open scoped Interval

noncomputable section
namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedHighExcursion
```

Minimal bricks:

```lean
-- 1. Normalize the current Lp bound.
-- theorem currentEnergy_boundBefore_one_le_of_LpPowerBoundedBefore
--   (hLp : LpPowerBoundedBefore D p T u) :
--   ∃ M, 1 ≤ M ∧ ∀ s, 0 < s → s < T →
--     integratedMoserEnergy D u p s ≤ M

-- 2. Positive drop constant, obtained from IntegratedMoserDissipationDropBefore
-- by replacing C with C+1.
structure IntegratedMoserPositiveDropConst
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T p : ℝ) : Prop where
  C : ℝ
  C_pos : 0 < C
  drop :
    ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
      integratedMoserEnergy D u p t2 - integratedMoserEnergy D u p t1 +
        2 * ∫ s in t1..t2, integratedMoserGradientEnergy D u p s ≤
      C * p * ∫ s in t1..t2,
        max 1 (integratedMoserEnergy D u p s)

-- 3. Abstract gradient nonnegativity, with an interval-domain producer later.
def IntegratedMoserGradientEnergyNonnegativity
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → 0 ≤ p → ∀ a b, 0 < a → a ≤ b → b < T →
    0 ≤ ∫ s in a..b, integratedMoserGradientEnergy D u p s

-- 4. Pure topology: last exit below a level.
-- theorem exists_lastExit_le_level_of_continuousOn
--   (hcont : ContinuousOn Z (Set.Icc (0:ℝ) T))
--   (hK_pos : 0 < K) (hZ0 : Z 0 < K)
--   (ht0 : 0 < t) (htT : t < T) (hhigh : 2*K < Z t) :
--   ∃ a, 0 < a ∧ a < t ∧ a ∈ Set.Icc (0:ℝ) T ∧
--     t ∈ Set.Icc a T ∧ Z a = K ∧ ∀ s ∈ Set.Icc a t, K ≤ Z s

-- 5. Core lower integral from the last-exit window and the q-drop.
-- theorem higherPower_integral_lowerBound_of_lastExit_and_qDrop :
--   K / (Cq * (p+rho)) ≤
--     ∫ s in a..b, integratedMoserEnergy D u (p+rho) s

-- 6. Explicit-Ceps version of the integrated relative-Moser wrapper.
-- theorem relativeMoser_higherPower_timeIntegral_le_explicitCeps
--   (hrel_eps : ∀ s, 0 < s → s < T →
--     integratedMoserEnergy D u (p+rho) s ≤
--       eps * integratedMoserGradientEnergy D u p s +
--       Ceps * integratedMoserEnergy D u p s)
--   (hG_le : ∫ s in a..b, integratedMoserGradientEnergy D u p s ≤ Gbound)
--   (hY_le : ∀ s ∈ Set.Icc a b, integratedMoserEnergy D u p s ≤ M) :
--   ∫ s in a..b, integratedMoserEnergy D u (p+rho) s ≤
--     eps * Gbound + (b-a) * (Ceps * M)
```

Then add a small plan record tying the constants together:

```lean
structure IntegratedMoserCrossingThresholdPlan
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 p : ℝ) : Prop where
  M Cp Cq eps Ceps Tbar Gbar R K : ℝ
  M_one_le : 1 ≤ M
  Cp_nonneg : 0 ≤ Cp
  Cq_pos : 0 < Cq
  eps_pos : 0 < eps
  Ceps_nonneg : 0 ≤ Ceps
  T_le_Tbar : T ≤ Tbar
  Gbar_def : Gbar = (M + Cp*p*(Tbar*M))/2
  R_def : R = eps*Gbar + Tbar*(Ceps*M)
  init_lt_K : integratedMoserEnergy D u (p+rho) 0 < K
  K_one_le : 1 ≤ K
  K_gap : (Cq*(p+rho))*(R+1) < K
```

The lower-window producer should return `IntegratedMoserHighExcursionLowerAverageWindow` with `Cnext = 2*plan.K`, `M = plan.M`, and `lowerBound = plan.K/(plan.Cq*(p+rho))`.

The upper-gap producer should consume that constructed window and return `IntegratedMoserWindowUpperGapWitness` using the same `plan.eps` and `plan.Ceps`.

## Important correction to the existing epsilon frontier

Avoid a statement that says one epsilon beats **all** `IntegratedMoserWindowUpperBoundWitness` values.  That is false: the witness predicate is upward closed in `Ceps`; if a witness works for `Ceps`, it also works for any larger `Ceps'`, and then `(b-a)*(Ceps'*M)` can be made arbitrarily large when `a<b` and `M>0`.

Use a tied witness instead:

```text
choose eps, obtain its specific Ceps from relative interpolation, choose K using that Ceps, then prove the strict gap for that same Ceps.
```

## Final formula summary

```text
M          = max 1 Mp
q          = p + rho
Cnext      = 2*K
a          = last exit before t with Z <= K
b          = t
lowerBound = K/(Cq*q)
Gbound     = (M + Cp*p*((b-a)*M))/2
Gbar       = (M + Cp*p*((max 1 T)*M))/2
R          = eps*Gbar + (max 1 T)*(Ceps*M)
K chosen so (Cq*q)*(R+1) < K and max 1 Z(0) < K
```

Then

```text
lowerBound <= ∫ Z
and
eps*Gbound + (b-a)*Ceps*M < lowerBound,
```

which gives the contradiction through the already existing `false_of_windowUpperBoundWitness_lowerAverage_gap` route.
