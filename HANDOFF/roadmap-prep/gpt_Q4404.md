ANSWER Q4404 7faecdda

# N18 Route C: top-level Lean assembly roadmap

## Executive verdict

The capstone can be made extremely small, but the public interfaces between the blocks must be frozen before Codex starts filling proofs.

The clean endpoint is:

```lean
theorem no_rational_point_of_order_18
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 18
```

and its proof should use only two imported capstones:

```lean
N18.all_rational_points_are_cusps
N18.modularPoint_of_exactOrder18
```

Everything involving cubic fields, fractional ideals, Mumford triples, quotient maps, Selmer candidates, formal groups, and finite-field enumeration must be hidden below those two statements.

There is one essential architectural warning:

> `[126] J_1(18)(ℚ) = 0` or “rank zero” does **not** by itself prove that the six rational points are the cusps. B6 must contain a separate finite rational-point classification. Do not accept a B6 implementation that jumps directly from rank zero to `X_1(18)(ℚ) = cusps`.

The recommended finite endgame is:

```text
[126]J18(ℚ)=0
+ reduction at 5 is injective on 126-torsion
+ #J18(F_5)=21
+ an explicit rational cusp-divisor subgroup of order 21
=> J18(ℚ) equals that subgroup
+ finite Abel–Jacobi preimage enumeration
=> every rational point of C is one of the six cusps.
```

This is MW-finite-generation-free and uses no database rank assertion.

---

# 0. Freeze the public types first

Put all public names in one namespace and do not let later files invent alternate models.

```lean
namespace FLT.CyclicExclusion.N18

abbrev Q := ℚ

/-- The cyclic real cubic field `Q(a)`, with `a^3 = 3a + 1`. -/
abbrev L := AdjoinRoot cubicPolynomial

/-- Smooth projective points of `Y^2 = F(X,Z)` over `K`. -/
abbrev CurvePoint (K : Type*) [Field K] := Curve.Point K

/-- The oriented fractional-ideal class group representing `Pic^0(C_K)`. -/
abbrev J (K : Type*) [Field K] := OrientedClass K

/-- Rational elliptic factor `162b1`. -/
def E0 : WeierstrassCurve ℚ := ...

/-- The rational 3-isogenous companion of `E0`. -/
def Ehat0 : WeierstrassCurve ℚ := ...

/-- The six explicitly listed cusps on the sextic model. -/
def cuspFinset : Finset (CurvePoint ℚ) := ...

def IsCusp (P : CurvePoint ℚ) : Prop := P ∈ cuspFinset

/-- Project-local exact-order predicate. -/
def HasRationalPointOfOrder
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) : Prop :=
  ∃ P : (E⁄ℚ).Point, addOrderOf P = n

end FLT.CyclicExclusion.N18
```

If the project already has a preferred exact-order predicate, use it and make `HasRationalPointOfOrder` an abbreviation. The capstone should not depend on a second, subtly different notion of exact order.

The projective point type must include both points at infinity. An affine-only point type is not sufficient for the cusp theorem or for the oriented divisor class.

---

# 1. Main dependency DAG: 25 public lemmas

The following are the block-level acceptance theorems. Internal polynomial identities and finite `decide` tables are not counted separately.

## B1: explicit cubic-field splitting

### T01. `n18_split_data`

```lean
def n18_split_data :
    BiellipticSplitData
      (CurvePoint L)
      (E0.map (algebraMap ℚ L)⁄L).Point
      (Ehat0.map (algebraMap ℚ L)⁄L).Point
```

The structure should contain, at minimum:

```lean
sigma     : CurvePoint L → CurvePoint L
tau       : CurvePoint L → CurvePoint L
qPlus     : CurvePoint L → E0LPoint
qMinus    : CurvePoint L → Ehat0LPoint
sigma_sq  : Function.Involutive sigma
tau_eq    : tau = hyperelliptic ∘ sigma
qPlus_deck  : qPlus (sigma P) = qPlus P
qMinus_deck : qMinus (tau P) = qMinus P
```

Its construction imports all ring certificates:

```text
sigma preserves C;
sigma^2 = id;
quotient equations;
Qplus ≅ E0_L;
Qminus ≅ Ehat0_L.
```

No Picard or descent code belongs in this file.

## B2: the concrete degree-zero divisor-class group

### T02. `j18_addCommGroup`

```lean
noncomputable instance j18_addCommGroup (K : Type*) [Field K] :
    AddCommGroup (J K)
```

This should come from the oriented quotient

```text
Additive(InvFrac(A_K)) × Z / graph(principalIdeal, ord_infinityPlus),
```

formed **before** quotienting principal ideals.

### T03. `j18_mumford_normal_form`

```lean
theorem j18_mumford_normal_form
    (K : Type*) [Field K] [NeZero (2 : K)] :
    Function.Bijective (MumfordTriple.toClass (K := K))
```

If uniqueness is split from existence, export an additive equivalence instead:

```lean
noncomputable def mumfordEquivJ : ReducedMumford K ≃+ J K
```

All later computational maps should be defined on reduced Mumford representatives and transported through this equivalence.

### T04. `j18_baseChange_injective`

```lean
theorem j18_baseChange_injective :
    Function.Injective (J.baseChange (algebraMap ℚ L) : J ℚ →+ J L)
```

This is load-bearing: it is what transports `[126]D=0` from `J L` back to `J ℚ` without invoking a general Picard-scheme theorem.

### T05. `abelJacobi_injective`

Choose one rational cusp `cusp0` as base point.

```lean
noncomputable def abelJacobi : CurvePoint ℚ → J ℚ :=
  fun P ↦ classOfDivisor (P - cusp0)

theorem abelJacobi_injective : Function.Injective abelJacobi
```

For a smooth projective curve, degree-one divisors `P` and `Q` are linearly equivalent only when `P=Q`. In the concrete implementation this should be proved through the reduced Mumford normal form, not through an unavailable abstract Jacobian API.

## B3: bielliptic push-pull

### T06. `j18_transfer_data`

```lean
noncomputable def j18_transfer_data :
    BiellipticTransferData
      (J L)
      (E0.map (algebraMap ℚ L)⁄L).Point
      (Ehat0.map (algebraMap ℚ L)⁄L).Point
```

The structure contains additive homomorphisms:

```lean
pushPlus  : J L →+ E0LPoint
pushMinus : J L →+ Ehat0LPoint
pullPlus  : E0LPoint →+ J L
pullMinus : Ehat0LPoint →+ J L
```

and the two deck-trace identities on divisor classes.

### T07. `hyperelliptic_action_eq_neg`

```lean
theorem hyperelliptic_action_eq_neg :
    hyperellipticPush = -(AddMonoidHom.id (J L))
```

Equivalent pointwise form:

```lean
theorem hyperelliptic_action (D : J L) :
    hyperellipticPush D = -D
```

No rational Weierstrass point is required. It follows from the degree-two map to `P^1` and `Pic^0(P^1)=0`, or directly from the balanced divisor representation.

### T08. `j18_trace_two`

```lean
theorem j18_trace_two (D : J L) :
    j18_transfer_data.pullPlus (j18_transfer_data.pushPlus D) +
      j18_transfer_data.pullMinus (j18_transfer_data.pushMinus D) =
    2 • D
```

This is the exact identity

```text
(1 + sigma_*) + (1 + (h sigma)_*)
= (1 + sigma_*) + (1 - sigma_*)
= [2].
```

There is no correction term in degree zero.

## B4: rational 3-isogeny descent over `L`

### T09. `e0_three_isogeny_data`

```lean
noncomputable def e0_three_isogeny_data :
    ThreeIsogenyData E0 Ehat0
```

It contains the explicit Vélu map `phi`, its dual `phihat`, and:

```lean
phihat_phi : phihat.comp phi = multiplicationBy 3
phi_phihat : phi.comp phihat = multiplicationBy 3
```

All map-preservation claims must be denominator-cleared ring identities.

### T10. `e0_descent_candidates_complete`

```lean
theorem e0_descent_candidates_complete :
    phiSelmerCandidates = {1} ∧
    dualSelmerCandidates = {1, classOf 2, classOf 4}
```

This theorem is the finite 84-candidate result, including the global cohomology identifications and all local conditions. It should be proved by a transparent finite certificate, not by importing an ECNF rank field.

### T11. `e0_weak_three_descent`

Let `H3` be the subgroup generated by the known rational point of order three.

```lean
theorem e0_weak_three_descent
    (P : (E0.map (algebraMap ℚ L)⁄L).Point) :
    ∃ T : H3, ∃ Q : (E0.map (algebraMap ℚ L)⁄L).Point,
      P = (T : (E0.map (algebraMap ℚ L)⁄L).Point) + 3 • Q
```

This—not `finrank Selmer = 1`—is the required B4 capstone. T10 feeds T11 by identifying the surviving quotient class with the known 3-torsion point.

## B5: local 3-adic separatedness and bounded exponents

### T12. `e0_good_reduction_at_pi3`

```lean
theorem e0_good_reduction_at_pi3 :
    GoodReductionData E0LGoodModel pi3
```

The certificate includes:

```text
pi = a - 1;
3(1-pi^2)=pi^3;
v_pi(3)=3;
an explicit change of variables to the integral model;
Delta = -8.
```

### T13. `e0_reduction_exponent_seven`

```lean
theorem e0_reduction_exponent_seven
    (P : E0ReductionF3.Point) :
    7 • P = 0
```

A stronger finite theorem may record `Nat.card E0ReductionF3.Point = 7`.

### T14. `e0_formal_three_step`

```lean
theorem e0_formal_three_step
    {P Q : E0LocalPoint}
    (hP : P ∈ formalKernel)
    (hQ : Q ∈ formalKernel)
    (hPQ : P = 3 • Q)
    (hne : P ≠ 0) :
    formalLevel Q + 1 ≤ formalLevel P
```

The local power-series input is only

```text
[3](T)=3T+T^2 A(T), A integral,
```

which gives

```text
v([3]z) >= min(3+v(z), 2v(z)) >= v(z)+1.
```

Do not state that the whole local group is 3-adically separated; its order-seven reduction subgroup is infinitely 3-divisible.

### T15. `exponent_of_weakDescent_of_filtered`

Generalize the existing shared two-adic theorem to an arbitrary multiplier.

```lean
theorem exponent_of_weakDescent_of_filtered
    {G A Q : Type*}
    [AddCommGroup G] [AddCommGroup A] [AddCommGroup Q]
    (m e : ℕ)
    (H : AddSubgroup G)
    (loc : G →+ A)
    (red : A →+ Q)
    (hloc : Function.Injective loc)
    (hweak : WeakDescent m H)
    (hH : ∀ h : H, e • (h : G) = 0)
    (hred : ∀ q : Q, e • q = 0)
    (hstep : FilterStrictness m red) :
    ∀ x : G, e • x = 0
```

This theorem is pure group/filtration logic and should live outside N18 so N15/N21/N18 share it.

### T16. `e0L_exponent_21`

```lean
theorem e0L_exponent_21
    (P : (E0.map (algebraMap ℚ L)⁄L).Point) :
    21 • P = 0
```

Inputs:

```text
T11: weak descent with m=3;
H3 killed by 3;
T13: reduction quotient killed by 7;
T14: strict formal filtration;
T15 with e=lcm(3,7)=21.
```

### T17. `ehat0L_exponent_63`

```lean
theorem ehat0L_exponent_63
    (P : (Ehat0.map (algebraMap ℚ L)⁄L).Point) :
    63 • P = 0 := by
  have h : 21 • e0_three_isogeny_data.phihat P = 0 :=
    e0L_exponent_21 _
  have := congrArg e0_three_isogeny_data.phi h
  simpa [map_nsmul, e0_three_isogeny_data.phi_phihat, mul_nsmul] using this
```

This avoids a second descent on the companion curve.

### T18. `j18L_exponent_126`

```lean
theorem j18L_exponent_126 (D : J L) : 126 • D = 0 := by
  calc
    126 • D = 63 • (2 • D) := by norm_num [mul_nsmul]
    _ = 63 •
        (j18_transfer_data.pullPlus (j18_transfer_data.pushPlus D) +
         j18_transfer_data.pullMinus (j18_transfer_data.pushMinus D)) := by
          rw [j18_trace_two]
    _ = j18_transfer_data.pullPlus
          (63 • j18_transfer_data.pushPlus D) +
        j18_transfer_data.pullMinus
          (63 • j18_transfer_data.pushMinus D) := by
          simp [nsmul_add, map_nsmul]
    _ = 0 := by
          rw [show 63 • j18_transfer_data.pushPlus D = 0 by
                simpa [show 63 = 3 * 21 by norm_num, mul_nsmul]
                  using congrArg (3 • ·) (e0L_exponent_21 _)]
          rw [ehat0L_exponent_63]
          simp
```

The exact `simp` normal form may differ, but the proof should have only this content.

### T19. `j18Q_exponent_126`

```lean
theorem j18Q_exponent_126 (D : J ℚ) : 126 • D = 0 := by
  apply j18_baseChange_injective
  simpa [map_nsmul] using
    j18L_exponent_126 (J.baseChange (algebraMap ℚ L) D)
```

This is the MW-FG-free rank-zero endpoint.

## B6: finite rational-point classification

### T20. `j18_reduction_five_card`

```lean
theorem j18_reduction_five_card :
    Nat.card (J (ZMod 5)) = 21
```

This should be a finite computation using reduced Mumford triples over `F_5`.

### T21. `j18_reduction_five_injective`

```lean
theorem j18_reduction_five_injective :
    Function.Injective (reduceJ18Five : J ℚ →+ J (ZMod 5))
```

T19 says every source element is killed by 126, and `Nat.Coprime 126 5`. The local kernel of reduction has no nonzero prime-to-five torsion. Prove this using the same filtered-local pattern, specialized to multiplication by 126 on the 5-adic formal kernel. This is a concrete replacement for the unavailable general theorem about good reduction of an abstract genus-two Jacobian.

### T22. `j18Q_eq_cuspSubgroup`

Let `cuspClassSubgroup` be the subgroup generated by explicit cusp differences.

```lean
theorem j18Q_eq_cuspSubgroup :
    cuspClassSubgroup = ⊤
```

Internal inputs:

```text
T20 and T21 => Nat.card (J Q) <= 21;
an explicit cusp divisor has exact order 21;
therefore the cusp subgroup and J Q both have order 21.
```

Do not use a database statement `J(Q)_tors = Z/21`.

### T23. `all_rational_points_are_cusps`

```lean
theorem all_rational_points_are_cusps
    (P : CurvePoint ℚ) : IsCusp P
```

Proof architecture:

```text
abelJacobi(P) lies in the explicit 21-element cusp subgroup by T22;
normalize each of those 21 classes to a reduced Mumford triple;
check which classes can equal [P-cusp0] for a degree-one rational point;
exactly six survive;
use T05 to identify P with the corresponding cusp.
```

The finite enumeration may be exposed as:

```lean
theorem abelJacobi_preimage_certificate
    (P : CurvePoint ℚ) :
    abelJacobi P ∈ cuspAbelJacobiFinset
```

where `cuspAbelJacobiFinset` has exactly six elements.

### T24. `modularPoint_of_exactOrder18`

```lean
theorem modularPoint_of_exactOrder18
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point)
    (hP : addOrderOf P = 18) :
    ∃ Q : CurvePoint ℚ, ¬ IsCusp Q
```

This is the complete modular interpretation. It must include:

```text
Tate normal form / chosen X_1(18) parameterization;
the sextic equation;
exact order 18 implies nonzero discriminant and noncusp denominators;
the resulting projective point is rational.
```

It is independent of B2–B5 and should be built in parallel.

## Capstone

### T25. `no_rational_point_of_order_18`

```lean
theorem no_rational_point_of_order_18
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 18 := by
  rintro ⟨P, hP⟩
  obtain ⟨Q, hQnoncusp⟩ := modularPoint_of_exactOrder18 E P hP
  exact hQnoncusp (all_rational_points_are_cusps Q)
```

That is the entire final proof. If this file contains algebra, valuations, ideals, or finite-field calculations, a lower block has leaked through its interface.

---

# 2. DAG in compact form

```text
                         ┌───────────────┐
                         │ T01 split data│
                         └───────┬───────┘
                                 │
T02 group ─ T03 Mumford ────────┼──────► T06 transfer maps
   │          │                  │              │
   │          ├────► T04 base-change inj       ├────┐
   │          └────► T05 Abel–Jacobi inj       │    │
   │                                            │    ▼
   └──────────────────────────────► T07 h*=-1 ──┴─► T08 trace=[2]

T09 3-isogeny ────────────────┐
                              ├────────────────────────────► T17 Ehat exp 63
T10 finite descent cert ─► T11 weak 3-descent              ▲
                              │                             │
T12 good reduction pi3 ─► T13 reduction exp 7              │
             │                │                             │
             └──────────► T14 formal [3] step               │
                              │                             │
T15 generic shared filtration ┴────► T16 E0 exp 21 ─────────┘

T08 trace=[2] + T16 + T17 ─────► T18 J(L) exp 126
T04 base-change inj + T18 ─────► T19 J(Q) exp 126

T03 Mumford + T19 ─► T20 #J(F5)=21
                 └─► T21 reduction at 5 injective
T20 + T21 + explicit order-21 cusp class ─► T22 J(Q)=cusp subgroup
T05 + T22 + finite degree-one enumeration ─► T23 all Q-points are cusps

T24 exact order 18 gives noncusp ───────────────────────────┐
T23 all Q-points are cusps ─────────────────────────────────┴─► T25 contradiction
```

---

# 3. Parallel build plan

## Wave 0: one shared API commit

Before parallel work, land only:

```text
Basic.lean:
  L, a, relation a^3=3a+1;
  sextic f and projective curve C;
  E0 and Ehat0 equations;
  cusp list and IsCusp;
  J K type abbreviation or opaque declaration;
  HasRationalPointOfOrder.
```

Also land the empty public structures:

```lean
BiellipticSplitData
BiellipticTransferData
WeakDescent
FilterStrictness
```

This prevents incompatible names and model choices.

## Wave 1: fully parallel lanes

### Lane A — B1 splitting

Build T01 from pure ring identities. No dependency on Picard, Selmer, or local fields.

### Lane B — B2 oriented class group

Build T02–T05. This lane depends only on the sextic and generic algebra. It does not depend on the explicit involution or on E0.

### Lane C — B4 3-isogeny descent

Build T09–T11. It depends only on `L`, `E0`, and `Ehat0`.

### Lane D — B5 local filtration

Build T12–T15. The generic theorem T15 and the local good model/formal-group proof are independent of the Selmer enumeration.

### Lane E — modular bridge

Build T24 independently from the Tate normal form and sextic parameterization.

### Lane F — finite-field data

Once reduced Mumford syntax exists, compute the raw `F_5` tables for T20 and the six cusp Abel–Jacobi classes. The mathematical tables can be prepared before the global group proof is finished.

## Wave 2

```text
Lane A + Lane B -> T06–T08 push-pull.
Lane C + Lane D -> T16–T17 elliptic bounded exponents.
B2 normal forms + finite tables -> finite-reduction helper lemmas.
```

## Wave 3

```text
T08 + T16 + T17 -> T18.
T18 + T04 -> T19.
T19 + finite F5 data -> T21–T22.
```

## Wave 4

```text
T05 + T22 -> T23.
T23 + T24 -> T25.
```

Each lane can be assigned to a separate Codex session. No session should edit another lane's public theorem signatures after Wave 0.

---

# 4. Highest-risk lemmas, ranked

## Risk 1 — T03/T04: oriented Mumford completeness and base-change injectivity

**Why highest risk:** current Mathlib has fractional ideals and `ClassGroup`, but not the projective genus-two `Pic^0`, the two-infinity orientation, or a balanced Mumford equivalence. This block must prove:

```text
every oriented class has a reduced triple;
reduction terminates;
reduced representatives are unique;
principal relations include the infinity coordinate;
coefficient extension Q -> L is injective on classes.
```

A superficial implementation that merely injects Mumford triples into a class group is insufficient; T03 requires surjectivity/completeness.

**Pre-solve first:** write the exact oriented quotient, prove the normal-form theorem on paper, and decide how the infinity bit/integer appears in reduction before asking Codex to implement group operations.

## Risk 2 — T06/T08: pushforward/pullback well-defined on oriented classes

**Why:** formulas on affine points are easy; proving that they preserve principal divisor relations and correctly handle ramification and both infinity points is not. The trace identity is short only after the maps are genuine homomorphisms on the whole quotient.

Required hard sublemmas:

```text
pushforward of a principal divisor is principal via function-field norm;
pullback of a principal divisor is principal by composition;
q^* q_* = 1 + deck on divisor classes, including ramified fibers;
orientation/infinity coordinates are respected.
```

**Pre-solve:** specify the maps on the raw `(InvFrac × Z)` group and prove they send the principal graph to the principal graph. Do not start from reduced triples alone unless a theorem proves independence of representative.

## Risk 3 — T10/T11: the 3-isogeny computation must yield weak descent, not only a Selmer dimension

**Why:** the constant `Z/3` kernel and dual `mu_3` kernel have different cohomology over the totally real field. The finite candidate lists must be connected to the actual Kummer maps, and the surviving dual class must be proved to be represented by the known 3-torsion point.

The acceptance statement is:

```text
∀ P, ∃ T ∈ H3, ∃ Q, P = T + 3Q.
```

A theorem saying only `Nat.card Selmer = 3`, or a copied Magma output, does not close Route C.

**Pre-solve:** freeze the two Kummer maps, their codomains, the local-image predicates, and the exact representative of the surviving line.

## Risk 4 — T21–T23: finite rational-point endgame

**Why:** bounded exponent is not a rational-point classification. One must formalize either:

```text
reduction of oriented Mumford classes at 5 and injectivity on 126-torsion,
```

or an equally explicit finite enumeration through the two elliptic quotients. Then one must compute the degree-one Abel–Jacobi preimages.

**Pre-solve:** generate and independently verify:

```text
the complete list of J(F5) reduced triples;
the group table or enough certificates to prove card 21;
the exact order-21 cusp class;
the 21 reduced global cusp-subgroup representatives;
the six representatives that can be [P-cusp0].
```

### Watch item — T12/T14 local-field plumbing

Mathematically this is lower risk because the shared filtration is already formalized at 2. Lean plumbing over the ramified cubic completion is still nontrivial: the valuation is not `padicValRat`, and the rational model must be transported to the good integral model with discriminant `-8`. Treat it as a dedicated lane, but it is less conceptually dangerous than Risks 1–4.

---

# 5. Suggested file decomposition

Use **16 supporting files plus one capstone**, 17 files total.

```text
FLT/CyclicExclusion/N18/
  Basic.lean
  Split.lean

  Picard/
    OrientedClass.lean
    Mumford.lean
    BaseChange.lean
    Transfer.lean

  Elliptic/
    E0Models.lean
    ThreeIsogeny.lean
    ThreeDescentGlobal.lean
    ThreeDescentLocal.lean
    ThreeDescentCertificate.lean
    ThreeAdic.lean

  JacobianExponent.lean

  RationalPoints/
    ReductionFive.lean
    Cusps.lean

  ModularInterpretation.lean
  CyclicExclusion18.lean
```

## File contracts

### `Basic.lean`

Exports only shared definitions and elementary certificates:

```text
L, a, cubic relation;
f and projective C;
squarefreeness/smoothness;
E0, Ehat0;
six cusps;
HasRationalPointOfOrder.
```

### `Split.lean`

Exports T01. Keep every `ring_nf` identity here.

### `Picard/OrientedClass.lean`

Defines the raw fractional-ideal-plus-orientation quotient and T02.

### `Picard/Mumford.lean`

Defines reduced triples, composition/reduction, and T03/T05.

### `Picard/BaseChange.lean`

Defines coefficient extension and proves T04.

### `Picard/Transfer.lean`

Imports `Split`, `Mumford`, and `BaseChange`; proves T06–T08.

### `Elliptic/E0Models.lean`

Contains rational and good local models and explicit changes of variables.

### `Elliptic/ThreeIsogeny.lean`

Contains T09 and all denominator-cleared Vélu identities.

### `Elliptic/ThreeDescentGlobal.lean`

Contains the cubic field arithmetic, unit/S-unit cube-class spaces, and global Kummer maps.

### `Elliptic/ThreeDescentLocal.lean`

Contains local images at the primes over 2 and 3.

### `Elliptic/ThreeDescentCertificate.lean`

Contains the finite 84-candidate `decide` proof T10 and derives T11.

### `Elliptic/ThreeAdic.lean`

Contains T12–T14 and imports the generalized shared-filtration theorem T15 from a reusable non-N18 file, preferably:

```text
FLT/Elliptic/WeakDescent/FilteredExponent.lean
```

If that generic file does not already exist, count it as an eighteenth file outside the N18 directory.

### `JacobianExponent.lean`

Imports `Picard/Transfer`, `ThreeIsogeny`, `ThreeDescentCertificate`, and `ThreeAdic`; proves T16–T19. It should be short.

### `RationalPoints/ReductionFive.lean`

Defines reduction of reduced Mumford representatives, finite `J(F5)`, and proves T20/T21.

### `RationalPoints/Cusps.lean`

Builds the order-21 cusp subgroup, proves T22, runs the finite Abel–Jacobi preimage check, and proves T23.

### `ModularInterpretation.lean`

Proves T24. It must not import Picard or descent modules.

### `CyclicExclusion18.lean`

Imports only:

```lean
public import FLT.CyclicExclusion.N18.RationalPoints.Cusps
public import FLT.CyclicExclusion.N18.ModularInterpretation
```

and contains T25.

---

# 6. Build commands and acceptance gates

Build each lane independently:

```bash
lake build FLT.CyclicExclusion.N18.Split
lake build FLT.CyclicExclusion.N18.Picard.Mumford
lake build FLT.CyclicExclusion.N18.Picard.BaseChange
lake build FLT.CyclicExclusion.N18.Elliptic.ThreeDescentCertificate
lake build FLT.CyclicExclusion.N18.Elliptic.ThreeAdic
lake build FLT.CyclicExclusion.N18.ModularInterpretation
```

Then the joins:

```bash
lake build FLT.CyclicExclusion.N18.Picard.Transfer
lake build FLT.CyclicExclusion.N18.JacobianExponent
lake build FLT.CyclicExclusion.N18.RationalPoints.ReductionFive
lake build FLT.CyclicExclusion.N18.RationalPoints.Cusps
lake build FLT.CyclicExclusion.N18.CyclicExclusion18
```

Do not mark a block complete unless its exact capstone theorem compiles with no additional hypotheses:

```text
B1: n18_split_data
B2: j18_mumford_normal_form + j18_baseChange_injective + abelJacobi_injective
B3: j18_trace_two
B4: e0_weak_three_descent
B5: e0L_exponent_21 and j18Q_exponent_126
B6: all_rational_points_are_cusps
modular bridge: modularPoint_of_exactOrder18
final: no_rational_point_of_order_18
```

The final theorem should have no database assumptions, no Mordell-Weil finite-generation assumption, no `Sha` assumption, and no abstract genus-two Jacobian/abelian-variety dependency.

---

# 7. Minimal capstone file

```lean
module

public import FLT.CyclicExclusion.N18.RationalPoints.Cusps
public import FLT.CyclicExclusion.N18.ModularInterpretation

@[expose] public section

namespace FLT.CyclicExclusion.N18

/-- No elliptic curve over `ℚ` has a rational point of exact order `18`. -/
theorem no_rational_point_of_order_18
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 18 := by
  rintro ⟨P, hP⟩
  obtain ⟨Q, hQnoncusp⟩ := modularPoint_of_exactOrder18 E P hP
  exact hQnoncusp (all_rational_points_are_cusps Q)

end FLT.CyclicExclusion.N18
```

That is the correct top-level shape. The main scheduling recommendation is to pre-solve Risks 1 and 2 before committing the whole build: the oriented Mumford equivalence and the well-defined push-pull maps are the genuinely new genus-two infrastructure. B1, B4, B5, and the modular bridge can all progress independently while those two foundations are being stabilized.