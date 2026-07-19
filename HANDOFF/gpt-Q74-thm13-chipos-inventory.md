ANSWER Q74 44c18747

# Verdict

The uniqueness mirror for χ > 0 is structurally the same as the χ ≤ 0 proof. Once the χ > 0 version of Theorem 1.2 is available in the bounded whole-line solution class, the rest of Theorem 1.3 requires no sign-specific PDE estimate.

The only genuine adaptation points are:

1. replace the wave cap 1 by Mχ = (1/(1-χ))^(1/α) in every boundedness hypothesis;

1. choose the stability weight η below both κ₁ and the χ > 0 stability cap;

1. prove the two-wave weighted initial closeness directly from the common right-tail asymptotic in (1.23) plus boundedness on the left;

1. feed wave 2 into Theorem 1.2 as a bounded global Cauchy solution;

1. recover V₁ = V₂ from the elliptic resolvent once U₁ = U₂.

No later step uses χ ≤ 0, monotonicity, or the special cap 1.

# 1. Paper-level mirror

Theorem 1.2 assumes, for either sign regime, a wave satisfying

```plain text
0 < U*(x) < min{Mχ, exp(-κx)},
exp((κ₁-κ)x) (U*(x)/exp(-κx) - 1) -> 0             (1.19)
```

for some κ₁ ∈ (κ,1), and initial data satisfying

```plain text
u₀ >= 0,
liminf_{x->-∞} u₀(x) > 0,
∫_R exp(2ηx) |u₀(x)-U*(x)|² dx < ∞.               (1.20)
```

It then gives weighted convergence (1.21) and uniform convergence (1.22). Theorem 1.3 assumes the same cap and right-tail condition for both waves in (1.23). The paper's Section 5.3 says that (1.23) provides an admissible η, the weighted distance is finite, and both profiles are positive at the left; Theorem 1.2 then gives equality of the profiles.

For positive sensitivity, the paper itself already states the cap uniformly as

```plain text
Mχ = (1/(1-χ))^(1/α).
```

Thus the theorem statement is already sign-unified; the proof mirror does not require replacing any argument that intrinsically used Mχ=1.

# 2. Part (a): weighted-L2 closeness still follows when Mχ > 1

Yes. The cap value is irrelevant except through a finite constant on the left half-line.

Let

```plain text
Wi(x) = Ui(x)/exp(-κx) - 1.
```

Condition (1.23) says

```plain text
exp((κ₁-κ)x) Wi(x) -> 0.
```

Hence

```plain text
Ui(x) = exp(-κx) + exp(-κx) Wi(x)
      = exp(-κx) + o(exp(-κ₁x)).
```

Therefore

```plain text
U1(x)-U2(x) = o(exp(-κ₁x))                 as x -> +∞.
```

Choose

```plain text
κ < η < min{κ₁, stabilityWeightCap(χ)}.
```

In the paper's notation the second cap is

```plain text
1/(1+|χ|^(1/6)),
```

and Section 5.3 also writes an extra harmless <1. Since κ₁<1, choosing η<κ₁ already ensures η<1.

Fix ε = (κ₁-η)/2 > 0. For sufficiently large x,

```plain text
|U1(x)-U2(x)| <= C exp(-(κ₁-ε)x).
```

Then

```plain text
exp(2ηx)|U1-U2|²
 <= C² exp(2ηx) exp(-2(κ₁-ε)x)
 =  C² exp(-(κ₁-η)x),
```

which is integrable on [R,+∞).

On the left, (1.23) gives

```plain text
0 < Ui(x) < Mχ.
```

Thus

```plain text
|U1(x)-U2(x)| <= Mχ
```

or, without using positivity sharply,

```plain text
|U1-U2| <= |U1|+|U2| <= 2Mχ.
```

Therefore

```plain text
∫_{-∞}^R exp(2ηx)|U1-U2|² dx
 <= 4 Mχ² ∫_{-∞}^R exp(2ηx) dx
 =  (2Mχ²/η) exp(2ηR) < ∞.
```

So

```plain text
∫_R exp(2ηx)|U1(x)-U2(x)|² dx < ∞.
```

The constant changes from 4/η-type bounds to 4Mχ²/η-type bounds, but no exponent or logical step changes.

## Lean adaptation

The repository already contains the sign-neutral helper

```javascript
WeightedL2InitialCloseness.of_common_waveRightTailAsymptotic
```

and the corrected Theorem 1.3 proof invokes it with the two general upper-tail bounds. The helper is not specialized to cap 1; it consumes boundedness through HasWaveUpperTailBound, whose bound is MChi p.

The existing proof line is conceptually already the χ>0 proof:

```javascript
have hclose : WeightedL2InitialCloseness η U₂ U₁ :=
  WeightedL2InitialCloseness.of_common_waveRightTailAsymptotic
    hηpos hηκ₁ hreg₁.U_cont hreg₂.U_cont
    hstrict₁.hasWaveUpperTailBound hstrict₂.hasWaveUpperTailBound
    htail₁ htail₂
```

No new weighted-integrability theorem is needed. The only check is that the χ>0 theorem supplies the same HasStrictWaveUpperTailBound interface with bound MChi p.

# 3. Part (b): a wave profile is StrictlyPositiveAtLeft

Yes, and this is stronger than needed.

A traveling wave “connecting (1,1) and (0,0)” is defined in the paper by

```plain text
lim_{x->-∞} U(x) = 1,
lim_{x->+∞} U(x) = 0.
```

Hence, taking for example ε=1/2, there exists R such that

```plain text
x <= -R  =>  |U(x)-1| < 1/2,
```

and therefore

```plain text
U(x) > 1/2.
```

Thus

```plain text
liminf_{x->-∞} U(x) >= 1,
```

indeed the limit equals 1, so the initial-data condition in (1.20) is automatic.

This does not use the cap, monotonicity, or the sign of χ.

## Lean adaptation

The repository already has exactly the needed theorem:

```javascript
IsTravelingWave.strictlyPositiveAtLeft hTW₂
```

and the corrected uniqueness proof uses it directly:

```javascript
have hU₂left : StrictlyPositiveAtLeft U₂ :=
  IsTravelingWave.strictlyPositiveAtLeft hTW₂
```

So part (b) is already sign-neutral and closed.

# 4. Feed wave 2 into Theorem 1.2

Define the Cauchy solution generated by wave 2:

```plain text
u₂(t,x) = U₂(x-ct),
v₂(t,x) = V₂(x-ct).
```

It has initial datum U₂ and is a classical solution because (U₂,V₂) satisfies the traveling-wave ODE. Its boundedness is

```plain text
0 < U₂(x-ct) <= Mχ,
|V₂(x-ct)| <= Mχ^γ.
```

The second estimate follows from the positive resolvent kernel:

```plain text
V₂(x)
 = (1/2) ∫_R exp(-|x-y|) U₂(y)^γ dy
 <= (Mχ^γ/2) ∫_R exp(-|x-y|) dy
 = Mχ^γ.
```

This is the sole place where the numerical cap appears in constructing the bounded Cauchy-class witness. For χ≤0 the constants are 1 and 1; for χ>0 they are Mχ and Mχ^γ.

The repository's theorem is already generic:

```javascript
IsTravelingWave.movingWave_isBoundedGlobalCauchySolutionFrom
```

and its proof explicitly uses the bounds MChi p and (MChi p)^p.γ. Thus no separate positive-sensitivity version should be created.

# 5. Apply stability and force stationarity

Apply Theorem 1.2 to wave 1 with initial datum U₂. It gives

```plain text
sup_x |u₂(t,x)-U₁(x-ct)| -> 0.             (1.22)
```

But

```plain text
u₂(t,x)=U₂(x-ct).
```

Set z=x-ct; as x ranges over R, so does z. Therefore for every t,

```plain text
sup_x |U₂(x-ct)-U₁(x-ct)|
 = sup_z |U₂(z)-U₁(z)|.
```

The left side is independent of t, while (1.22) says it tends to zero. Hence

```plain text
sup_z |U₂(z)-U₁(z)| = 0,
```

so

```plain text
U₁ ≡ U₂.
```

This is purely kinematic. It does not use χ, the PDE sign, or any cap.

In Lean this is packaged by the uniform-moving-frame uniqueness lemma used at the end of Theorem_1_3_amended.of_bounded_stability.

# 6. Recover V₁ = V₂

Once U₁=U₂, both elliptic profiles satisfy

```plain text
V_i'' - V_i + U_i^γ = 0
```

in the bounded class. Equivalently,

```plain text
V_i(x) = (1/2) ∫_R exp(-|x-y|) U_i(y)^γ dy.
```

Therefore

```plain text
U₁=U₂  =>  U₁^γ=U₂^γ  =>  V₁=V₂.
```

Again this is independent of χ. The corrected Lean proof explicitly passes the two resolvent identities to

```javascript
Theorem_1_3_profile_eq_of_uniform_movingFrame_and_resolvent.
```

# 7. Exact adaptation inventory with paper references

## A. Theorem statement and wave cap

- Positive-sensitivity existence cap: (1.18).

- Stability cap and right-tail hypothesis: (1.19).

- Two-wave uniqueness hypotheses: (1.23).

Adaptation:

```plain text
1  ->  Mχ = (1/(1-χ))^(1/α).
```

This affects only boundedness constants and the admissible wave class.

## B. Choice of weight

- Initial weighted closeness required in (1.20).

- Section 5.3 chooses

```plain text
κ < η < min{κ₁, 1/(1+|χ|^(1/6)), 1}.
```

Adaptation: use the positive-sensitivity stabilityWeightCap; no other change.

In the current Lean abstraction this is

```javascript
paper531RootMinus ... < η,
η < stabilityWeightCap p,
η < κ₁.
```

The corrected proof obtains this by choosing η below the minimum of the root-tail and stability caps.

## C. Two-wave initial closeness

- Uses (1.23), and the paper cites Remark 4.3(1).

Adaptation: replace the left-side constant by Mχ; the right-tail proof is identical.

Important precision point: Remark 4.3(1) was stated for waves produced by the existence construction, whereas Theorem 1.3 assumes (1.23) directly for arbitrary waves in its uniqueness class. For the formal proof, (1.23) itself is enough; do not make uniqueness depend on “constructed by Theorem 1.1”.

## D. Positivity at the left

- Initial condition in (1.20): liminf_{x->-∞}u₀(x)>0.

- Section 5.3 records this for each wave.

- It follows directly from the definition of connection to (1,1) in the introduction and the traveling-wave hypothesis.

Adaptation: none.

## E. Bounded Cauchy solution generated by wave 2

- The paper suppresses this as standard when it says “by Theorem 1.2”.

- Formalization must show the translated second wave belongs to the bounded solution class.

Adaptation:

```plain text
||u₂||∞ <= Mχ,
||v₂||∞ <= Mχ^γ.
```

The repository's corrected Theorem 1.3 already exposes this missing solution-class step.

## F. Uniform convergence implies profile equality

- Uses (1.22).

Adaptation: none.

## G. Elliptic component equality

- Uses the resolvent representation of the elliptic equation; compare the paper's repeated notation V=Ψ(.;U,1,1) and the kernel computation used in Lemma 5.3, especially (5.12)-(5.13).

Adaptation: none.

# 8. Did the chi<=0 proof use the sign anywhere else?

No, provided the imported Theorem 1.2 has the same bounded-class conclusion for χ>0.

The uniqueness wrapper does not use:

- monotonicity of waves;

- U<=1 specifically;

- the sign of the chemotactic drift;

- the χ<=0 maximum principle;

- the χ<=0 left-half-line comparison;

- the rectangle contraction directly;

- any negative-sensitivity derivative sign.

All sign-dependent work is upstream inside Theorem 1.2 and its parameter budget. Theorem 1.3 is a functional corollary of stability plus the two tail properties.

# 9. Recommended Lean theorem shape

Do not create a second hand-written uniqueness proof for χ>0. Keep the current sign-neutral theorem:

```javascript
Theorem_1_3_amended.of_bounded_stability
  (h12 : Theorem_1_2_amended_bounded)
```

and instantiate it with the completed positive-sensitivity Theorem 1.2 capstone.

The required positive-branch interface must expose:

```javascript
HasStrictWaveUpperTailBound p c U
-- internally: U <= MChi p

exists κ₁,
  kappa c < κ₁ ∧ κ₁ < 1 ∧
  HasWaveRightTailAsymptotic c κ₁ U

η < stabilityWeightCap p

bounded-class stability for every Cauchy solution.
```

The existing uniqueness proof then reuses, unchanged:

```javascript
WeightedL2InitialCloseness.of_common_waveRightTailAsymptotic
IsTravelingWave.nonnegativeInitialDatum
IsTravelingWave.strictlyPositiveAtLeft
IsTravelingWave.movingWave_isBoundedGlobalCauchySolutionFrom
Theorem_1_3_profile_eq_of_uniform_movingFrame_and_resolvent
```

# Bottom line

- (a) Yes. The two tails in (1.23) imply weighted-L2 closeness for any η with 0<η<κ₁; changing the cap from 1 to Mχ only changes the left-tail domination constant to O(Mχ²/η).

- (b) Yes. A traveling wave connecting (1,1) to (0,0) satisfies U₂(x)->1 at -∞, hence StrictlyPositiveAtLeft U₂; this is already a sign-neutral Lean theorem.

- (c) No uniqueness step after invoking Theorem 1.2 uses χ≤0. The exact positive-branch adaptations are the Mχ boundedness constants, the positive-branch stability-weight cap, and instantiation of the bounded-class Theorem 1.2. Everything from weighted closeness through profile equality and elliptic recovery is unchanged.