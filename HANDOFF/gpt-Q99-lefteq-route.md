ANSWER Q99 3e71c9f2

# Recommendation

Use Route 1: a localized, two-sided rectangle squeeze on a fixed co-moving left half-line. It is now the cheapest correct Lean route because most of the genuinely difficult infrastructure is already committed:

- the whole-line χ-positive rectangle algebra and finite-round contraction;

- the χ-positive weighted-L² convergence and spatial modulus;

- compact-buffer convergence to the wave;

- both sides of the half-line elliptic-kernel split;

- the generic half-line maximum principle;

- χ-positive floor/ceiling barrier families;

- the positive weighted lower-contact comparison that retains the essential b^m factor.

The remaining work is localized assembly plus one positive plateau-persistence producer. Route 2 is not order-theoretically valid for χ>0. The paper’s translation-limit/Liouville route is analytically elegant, but in Lean it would require a new space-time compactness and entire-limit package, so it is more expensive than the already-built half-line machinery.

A crucial refinement of Route 1 is:

Do not use the committed constant-defect buffered wrappers as the iterative engine. They are correct, but they replace the coupled term by χ M^m(...) and lose the sharp rectangle recurrence. Add sharp coupled weighted floor and ceiling comparisons, keeping the barrier value b^m or a^m and treating only the exponentially small kernel tail as an additive defect.

# Quantifier correction about the buffer width

For the target convergence theorem, the correct order is

```plain text
intro ε
choose the contraction error δ = δ(ε)
choose R = R(ε) so that the kernel tail is below δ/2
fix this R throughout the finite Nat iteration
run finitely many rectangle rounds
```

Thus R is chosen before the rectangle rounds, but it cannot be chosen once and for all independently of ε. A fixed finite R leaves an O(exp(-R)) residual and proves convergence only to an O(exp(-R)) neighborhood of 1.

# 1. Co-moving PDE and exact sign structure

After restarting at a positive time t₀, set

```plain text
q(s,x) = u(t₀+s, x+c(t₀+s)),    s ≥ 0,
V(s,x) = frozenElliptic p (q s) x.
```

The expanded co-moving equation is

```plain text
q_s
 = q_xx + c q_x
   - χ m q^(m-1) q_x V_x
   + χ q^m (q^γ - V)
   + q(1-q^α).
```

At a lower contact with a scalar floor b(s), the adverse zeroth-order quantity is

```plain text
χ b^m (V-b^γ).
```

At an upper contact with a scalar ceiling a(s), the adverse quantity is

```plain text
χ a^m (a^γ-V).
```

This is why χ>0 needs both sides of the resolver pinching. The χ≤0 single-floor argument cannot be sign-flipped.

# 2. Exact kernel split and contact inequalities

Assume for all y ≤ x₀+R

```plain text
ell ≤ q(s,y) ≤ M,
```

and globally

```plain text
0 ≤ q(s,y) ≤ G,
```

where

```plain text
0 < ell ≤ 1 ≤ M ≤ G,
tau = exp(-R)/2.
```

For every x ≤ x₀, the already committed resolver theorem gives

```plain text
(1-tau) ell^γ
  ≤ V(s,x)
  ≤ (1-tau) M^γ + tau G^γ.
```

Equivalently,

```plain text
V(s,x) ≤ M^γ + tau (G^γ-M^γ),
V(s,x) ≥ ell^γ - tau ell^γ.
```

Therefore the sharp lower-contact estimate is

```plain text
V-b^γ
 ≤ (M^γ-b^γ) + tau (G^γ-M^γ),

χ b^m(V-b^γ)
 ≤ χ b^m(M^γ-b^γ)
   + χ tau b^m(G^γ-M^γ).
```

The sharp upper-contact estimate is

```plain text
a^γ-V
 ≤ (a^γ-ell^γ) + tau ell^γ,

χ a^m(a^γ-V)
 ≤ χ a^m(a^γ-ell^γ)
   + χ tau a^m ell^γ.
```

Only the second summand in each line is a localization defect. The main coupled terms must remain exactly

```plain text
χ b^m(M^γ-b^γ),
χ a^m(a^γ-ell^γ).
```

If they are replaced by the coarse constants χM^m(M^γ-ell^γ), the small-floor burn-in and the sharp 2χ gap recurrence are lost.

# 3. Uniform tail budget

Let [ell₀,M₀] be the initial buffered rectangle and let G≥M₀≥1 be the global bound. Every later round has

```plain text
ell₀ ≤ ell_n ≤ 1 ≤ M_n ≤ M₀ ≤ G.
```

Define

```plain text
Theta_R = χ * tau * M₀^(m-1) * G^γ.
```

After dividing the scalar floor/ceiling inequalities by the positive barrier value, both tail terms are bounded by Theta_R:

```plain text
χ tau b^(m-1)(G^γ-M_n^γ) ≤ Theta_R,
χ tau a^(m-1) ell_n^γ    ≤ Theta_R.
```

For a requested final power-gap tolerance epsGap, put

```plain text
r       = 2χ,
delta   = epsGap*(1-r)/4,
delta0  = delta/2.
```

Choose R so that

```plain text
Theta_R < delta/2.
```

Then every localized target inequality has effective error at most

```plain text
delta0 + Theta_R < delta.
```

The existing whole-line algebra applies verbatim with delta and yields

```plain text
gap_(n+1) ≤ 2χ gap_n + 2delta,
```

where

```plain text
gap_n = M_n^α - ell_n^α.
```

Consequently

```plain text
gap_n
 ≤ (2χ)^n gap_0 + 2delta/(1-2χ)
 = (2χ)^n gap_0 + epsGap/2.
```

Choose N so that (2χ)^N gap_0 < epsGap/2. Then gap_N<epsGap.

Because α≥1 and ell_N≤1≤M_N, the existing power-gap endgame gives

```plain text
M_N-1 ≤ M_N^α-1 ≤ gap_N,
1-ell_N ≤ 1-ell_N^α ≤ gap_N.
```

Hence |q-1|≤gap_N on the final half-line.

# 4. Best data structure: use perturbed rectangle gaps

The cleanest Lean state stores the actual localized strict margins, not a coarse constant defect.

Define

```javascript
def chiPosBufferedFloorGap
    (p : CMParams) (M G tau x : ℝ) : ℝ :=
  chiPosFloorGap p M x -
    p.χ * tau * x^(p.m-1) * (G^p.γ-M^p.γ)

def chiPosBufferedCeilingGap
    (p : CMParams) (ell tau x : ℝ) : ℝ :=
  chiPosCeilingGap p ell x -
    p.χ * tau * x^(p.m-1) * ell^p.γ
```

At the critical exponent these have the useful forms

```plain text
bufferedFloorGap
 = 1-(1-χ)x^α
   - χ[(1-tau)M^γ+tau G^γ]x^(m-1),

bufferedCeilingGap
 = (1-χ)x^α
   + χ(1-tau)ell^γ x^(m-1)-1.
```

Thus the first remains strictly decreasing and the second strictly increasing on x>0, exactly as in WholeLineChiPosRectangleTargets.lean.

A suitable state is

```javascript
structure ChiPosBufferedLeftRectangle
    (p : CMParams) (q : ℝ → ℝ → ℝ)
    (x₀ R G : ℝ) where
  ell M start : ℝ
  ell_pos      : 0 < ell
  ell_lt_one   : ell < 1
  one_lt_M     : 1 < M
  M_le_G       : M ≤ G
  floor_margin :
    0 < chiPosBufferedFloorGap p M G (Real.exp (-R)/2) ell
  ceiling_margin :
    0 < chiPosBufferedCeilingGap p ell (Real.exp (-R)/2) M
  bounds :
    ∀ t, start ≤ t → ∀ x, x ≤ x₀ + R →
      q t x ∈ Set.Icc ell M
```

The bounds deliberately extend through x₀+R, because the resolver at x≤x₀ needs the entire left half-line plus buffer.

# 5. Exact lemma chain

Below is the recommended nine-link chain. Names marked existing should be reused as written; names marked new are the smallest missing interfaces.

## 1. Positive persistent plateau — new

```javascript
wholeLineCauchyGlobal_exists_persistent_lowerBarrierPlateau_chi_pos_half_natural
```

Hypotheses: the same wave/weighted-data package as the χ-negative theorem, plus

```plain text
0 < χ,
χ < 1/2,
α = m+γ-1.
```

Conclusion: a patched lower-barrier plateau persists on all late co-moving windows.

Implementation route: reuse the χ-free plateau profile and the positive operator ledgers already committed at heights 1/MChi; after the positive ceiling burn-in, normalize the trap height to MChi+r. The sign audit shows there is no sign-dependent barrier shape—only the two resolver-value ledgers must use the positive budgets instead of discarding a favorable term.

## 2. Extract a permanent co-moving left floor — existing verbatim

```javascript
wholeLineCauchyGlobal_eventual_coMoving_left_floor_of_persistent_plateau
```

Conclusion:

```plain text
∃ Tleft Rleft d,
  0<d ∧
  ∀ t≥Tleft, ∀ z≤Rleft,
    d ≤ u(t,z+ct).
```

This theorem is χ-free.

## 3. Produce arbitrary late-time buffer accuracy — existing verbatim

Use

```javascript
wholeLineCauchyGlobal_coMovingWeightedL2Convergence_chi_pos_natural
wholeLineCauchyGlobal_eventuallyUniformMovingFrameSpatialModulus
eventually_coMovingPath_close_on_Icc_of_weightedL2_of_spatialModulus
```

For each rectangle round’s raw targets Lraw<1<Araw, choose

```plain text
ebuf < min(1-Lraw, Araw-1)/4.
```

Move x₀ sufficiently far left that

```plain text
|U(z)-1| < ebuf
```

on [x₀,x₀+R], then wait until

```plain text
|q(t,z)-U(z)| < ebuf
```

there for all later times. This gives the permanent lateral ordering

```plain text
Lraw ≤ q(t,z) ≤ Araw
```

on the buffer.

The existing raw target fields are only stated as Lraw≤1≤Araw, but their strict residual margins imply strict inequalities when χ>0, ell<1<M:

```plain text
chiPosFloorGap p M 1 < 0,
chiPosCeilingGap p ell 1 < 0,
```

whereas the raw margins are positive. Hence Lraw<1<Araw follows from strict monotonicity.

## 4. Pinch the resolver — existing verbatim

```javascript
frozenElliptic_pinched_of_left_halfLine_bounds
```

Use it with endpoint z₀=x₀+R and evaluation point x≤x₀.

## 5. Sharp coupled lower comparison — new

```javascript
leftHalfLine_ge_of_coupled_weighted_resolver_reaction_subsolution
```

It should mirror the committed

```javascript
leftHalfLine_ge_of_weighted_resolver_reaction_subsolution
```

but its scalar hypothesis must retain the -b^γ cancellation:

```plain text
hresolver : V(t,x) ≤ Dup,

hpdeb :
  b'(t) + χ b(t)^m (Dup-b(t)^γ)
    ≤ reactionFun α (b(t)).
```

Instantiate

```plain text
Dup = (1-tau)M^γ + tau G^γ.
```

Then build the target-capped floor with a rate from the buffered floor gap and obtain

```javascript
leftHalfLine_ge_of_buffered_chiPos_coupled_floor
```

on x≤x₀.

## 6. Sharp coupled upper comparison — new

```javascript
leftHalfLine_le_of_coupled_weighted_resolver_reaction_supersolution
```

It mirrors the committed

```javascript
leftHalfLine_le_of_positive_resolver_reaction_supersolution
```

but keeps the barrier-dependent main term:

```plain text
hresolver : Dlo ≤ V(t,x),

hpdea :
  reactionFun α (a(t))
    + χ a(t)^m (a(t)^γ-Dlo)
    ≤ a'(t).
```

Instantiate

```plain text
Dlo = (1-tau)ell^γ.
```

Then build

```javascript
leftHalfLine_le_of_buffered_chiPos_coupled_ceiling
```

using chiPosTargetCeiling and the buffered ceiling gap.

## 7. Initial buffered rectangle — new

```javascript
exists_initial_chiPosBufferedLeftRectangle
```

Inputs:

- the permanent floor d from link 2;

- the global positive range bound wholeLineCauchyGlobal_le_max_of_chi_pos;

- the uniform positive-χ limsup at MChi;

- the buffer ordering from link 3;

- a seed from exists_chiPos_rectangle_seed.

Procedure:

1. wait until the global ceiling is below the seed M₀>MChi;

1. choose ell₀≤d and the buffered floor margin positive;

1. use one localized weighted floor barrier to raise the far-left floor to the seed level;

1. combine the half-line result with the buffer bound to obtain bounds on all x≤x₀+R.

The persistent plateau is essential. Initial positivity on a laboratory left half-line does not by itself survive on the fixed co-moving half-line, because that half-line sweeps right through the original datum.

## 8. One buffered rectangle successor — new, with existing algebra

```javascript
exists_next_chiPosBufferedLeftRectangle
```

Order the substeps exactly as in the whole-line theorem:

1. choose floor targets L<Lraw<1;

1. obtain buffer accuracy for Lraw and run the lower comparison;

1. wait until L is uniform on x≤x₀, combine with the buffer to get L on x≤x₀+R;

1. restart;

1. choose/run the ceiling barrier with the new floor L;

1. publish A and combine half-line plus buffer bounds.

Return a step whose published targets satisfy

```plain text
1-L^α
 ≤ χ L^(m-1)(M_old^γ-L^γ) + delta,

A^α-1
 ≤ χ A^(m-1)(A^γ-L^γ) + delta.
```

Project these fields directly into the existing

```javascript
ChiPosWholeLineRectangleStep.gap_le
```

or, at the scalar level, chiPos_squeeze_gap_step. No localized reproof of the 2χ contraction is needed.

## 9. Finite affine iteration and final theorem — new, algebra reused

```javascript
uniformCoMovingLeftEquilibriumConvergence_of_buffered_rectangle_successors
```

Reuse the affine recurrence and power-gap endgame from

```javascript
uniformConvergesToConstant_one_of_rectangle_successors
```

but conclude only on x≤x₀. Then assemble

```javascript
wholeLineCauchyGlobal_uniformCoMovingLeftEquilibriumConvergence_chi_pos_natural
```

with the same wave/energy hypotheses as the χ-negative theorem and the additional assumptions

```plain text
0<χ<1/2,
α=m+γ-1.
```

# 6. Where the drift term enters

The co-moving drift is

```plain text
c q_x.
```

For a lower comparison, after setting

```plain text
r(t,x)=exp(-Dt)(b(t)-q(t,x)),
```

one has

```plain text
r_x = -exp(-Dt) q_x.
```

The drift contribution becomes

```plain text
c r_x ≤ |c| |r_x|.
```

For an upper comparison with r=exp(-Dt)(q-a), the same estimate holds. It is absorbed into

```plain text
K = |c| + Kgrad
```

in leftHalfLineSlabSup_le_of_scalar_pde.

At an exact interior first contact, r_x=0; the |c||r_x| term is needed only because the whole-line/half-line supremum may not be attained and the proof uses approximate-contact fencing. The drift changes neither the scalar barrier ODE nor the 2χ contraction ratio.

# 7. Boundary condition: initial time is not enough

The lateral boundary ordering at x=x₀ is required for every time in the comparison slab:

```plain text
floor(t) ≤ q(t,x₀),
q(t,x₀) ≤ ceiling(t),
```

not merely at the round’s initial time. Otherwise the first positive comparison violation can enter through the lateral boundary after time zero.

For the forward-time wrappers, this becomes an all-future condition after the restart time. The compact buffer theorem gives exactly what is needed:

```plain text
∀ t≥Tbuf, ∀ x∈[x₀,x₀+R],
  |q(t,x)-1| < ebuf.
```

Choose every rectangle restart time at least Tbuf. Since the floor barrier never exceeds Lraw<1 and the ceiling barrier never goes below Araw>1, the static buffer bounds imply the time-dependent lateral inequalities for the entire round.

The buffer accuracy may be selected separately for each of the finitely many rounds. Each such estimate is eventually permanent, so no circular time interval occurs.

# 8. Complete χ-sign audit

## Persistent plateau

For χ≤0, the raw and constant plateau ledgers discard resolver-value terms because

```plain text
(-χ) W^m V ≥ 0.
```

For χ>0 this term is adverse. Replacement: use the already-built positive raw/constant plateau operator ledgers and spend the resolver term in their χ<1/2 budgets. The lower-barrier spatial profile itself is χ-free and is reusable.

## Lower half-line comparison

For χ≤0, the adverse quantity can be written

```plain text
(-χ) q^m(q^γ-V),
```

and a lower resolver bound controls it. For χ>0, the lower-contact adverse quantity is instead

```plain text
χ q^m(V-q^γ).
```

A lower resolver estimate is useless; use the new upper kernel split.

## Upper half-line comparison

There is no corresponding upper iteration in the χ≤0 proof. For χ>0 it is essential because the global limsup is only MChi>1. At an upper contact use the lower kernel split to control

```plain text
χ q^m(q^γ-V).
```

## Chemotactic gradient term

The term

```plain text
χ m q^(m-1) q_x V_x
```

is bounded in absolute value using |χ|, the global range, and |V_x|≤G^γ. This part is sign-independent and can be copied verbatim.

## Global ceiling

For χ≤0 the explicit ceiling tends to 1, so the upper half of the final estimate is free. For χ>0 the explicit ceiling tends only to MChi>1; it supplies a range/seed but not convergence. Replacement: alternate floor and ceiling rounds.

# 9. Reuse matrix

## Reuse verbatim

- wholeLineCauchyGlobal_coMovingWeightedL2Convergence_chi_pos_natural.

- wholeLineCauchyGlobal_eventuallyUniformMovingFrameSpatialModulus.

- eventually_coMovingPath_close_on_Icc_of_weightedL2_of_spatialModulus.

- wholeLineCauchyGlobal_le_max_of_chi_pos and the positive limsup theorem.

- wholeLineCauchyGlobal_eventual_coMoving_left_floor_of_persistent_plateau.

- paperWaveOperator_fixedPoint_eq_bufferedForm_of_pos.

- frozenElliptic_lower_of_left_halfLine_floor.

- frozenElliptic_upper_of_left_halfLine_ceiling.

- frozenElliptic_pinched_of_left_halfLine_bounds.

- leftHalfLineSlabSup_le_of_scalar_pde and all half-line supremum machinery.

- chiZeroKPPFloor: derivative, range, convergence, restart.

- chiPosTargetCeiling: derivative, range, convergence, restart.

- the |c|+Kgrad first-order fencing estimates.

- exists_chiPos_rectangle_seed and most scalar target-selection ideas.

- chiPos_squeeze_gap_step / ChiPosWholeLineRectangleStep.gap_le.

- the affine recurrence and abs_sub_one_le_rpow_gap endgame.

## Must be re-proved or adapted

- positive plateau persistence for the front datum;

- buffered floor/ceiling gap monotonicity and target selection with tau;

- sharp coupled weighted lower comparison retaining b^m(M^γ-b^γ);

- sharp coupled weighted upper comparison retaining a^m(a^γ-ell^γ);

- the half-line rectangle state and the combine-half-line-with-buffer bookkeeping;

- initial buffered rectangle construction;

- successor-round assembly and final half-line quantifier packaging.

## Correct but not suitable as the contraction engine

The committed theorems

```javascript
leftHalfLine_ge_of_buffered_chiPos_floor
leftHalfLine_le_of_buffered_chiPos_ceiling
```

are mathematically sound. They use fixed defects of the form

```plain text
χ M^m[(M^γ-ell^γ)+tail].
```

They are useful for coarse seed/burn-in estimates. They should not drive the repeating rectangle rounds, because they erase the barrier-dependent b^m/a^m factor needed by the sharp algebra.

# 10. Why Route 2 should be rejected

The χ-positive parabolic-elliptic system is not monotone with respect to the population datum in the way Route 2 needs. Raising the datum on the right raises the resolver everywhere; in the population equation that change can help or hurt depending on whether the contact is lower or upper. Thus

```plain text
u₀≤w₀
```

does not yield a usable scalar order

```plain text
u(t,·)≤w(t,·)
```

for the coupled nonlocal flow.

One could compare a right-modified solution on the left by estimating the resolvent difference as O(exp(-R)), but then one also needs a stability estimate for the two nonlinear flows and control of the chemotactic derivative term. This recreates the same kernel-tail bookkeeping as Route 1, with an extra unknown solution. It is strictly more expensive.

# 11. Why the paper’s translation-limit route is not cheapest in Lean

Now that Proposition 1.2(2) is formalized, the paper’s contradiction route is logically available:

1. assume left-uniform convergence fails;

1. choose t_n→∞, z_n→-∞ at bad points;

1. translate the solution in space-time;

1. extract a locally smooth entire limit with a positive global floor;

1. apply Proposition 1.2(2) to the limit’s time-zero datum;

1. use time-translation invariance/uniqueness to show the entire limit is identically 1;

1. contradict the bad value at (0,0).

This avoids τ-defects, but the repository does not yet expose a ready theorem for space-time translation compactness of the global Cauchy orbit, diagonal extraction on all compact cylinders, convergence of V,V_x, closedness of the PDE, and identification of the limit as the canonical solution from its time-zero slice. Formalizing that package is a larger analytic campaign than finishing the already-committed buffered comparison route.

# Final verdict

Route 1 is sound and cheapest, with the sharp coupled-weighted refinement above.

The two decisive implementation rules are:

1. preserve b^m and a^m in the main rectangle coupling; spend only the tau-tail as an additive error;

1. require the buffer/lateral ordering for all future times of each round, not merely at the restart time.

With delta=epsGap(1-2χ)/4, R chosen so Theta_R<delta/2, and the existing whole-line gap lemma, the localized recurrence is

```plain text
gap_(n+1) ≤ 2χ gap_n + 2delta,
```

so the target follows exactly under χ<1/2.