# χ-sign audit for the two left-tail blockers

Source snapshot: `7ea4d1db`.  Line numbers below refer to that snapshot.

## Classification and scope

- **(i) magnitude/cosmetic**: the proof only replaces `-χ` by `|χ|`, puts
  `|χ|` into a budget, or routes to a sign-specific wrapper for which the
  opposite-sign wrapper is already present.  No favorable resolver term is
  discarded.
- **(ii) one-sided sign exploitation**: a coefficient is proved nonnegative
  from `χ ≤ 0`, so an inequality may be multiplied by it, or a favorable
  resolver term is discarded.
- **(iii) structural profile dependence**: the barrier's spatial or temporal
  shape itself changes with the sign.

Pure forwarding sites are listed as **F → (i)** or **F → (ii)**; the class is
the class of the terminal use reached through that forwarding edge.  This is
needed because the top-level theorem passes `hchi` through several wrappers
without inspecting it.

The weighted-convergence branch is stopped at the exact χ-positive mirror
explicitly named in the brief.  It is not part of either blocker: the negative
call is at
`WholeLineWeightedRegularityChiNegPlateauPersistenceNatural.lean:87-88`, and
the replacement is
`wholeLineCauchyGlobal_coMovingWeightedL2Convergence_chi_pos_natural`
(`WholeLineWeightedRegularityWeightedConvergenceChiPosNatural.lean:21-36`).
All direct uses at the persistence theorem, including this boundary, are
nevertheless recorded below.  The plateau seed, threshold, lower-barrier
operator, propagation, buffered comparison, resolver lower bound, and KPP
floor dependency chains are followed to their terminal algebraic uses.

## 1. Persistent lower-barrier plateau

### 1.1 Direct uses in the target theorem

The target is declared at
`WholeLineWeightedRegularityChiNegPlateauPersistenceNatural.lean:29-31`.

| Use of the target `hchi` | What it does | Class |
|---|---|---|
| `WholeLineWeightedRegularityChiNegPlateauPersistenceNatural.lean:81-84` | Supplies only `p.χ ≠ 0` to `paper5WaveStaticNaturalData_of_wave` (whose hypothesis is stated at `WholeLineWeightedRegularityWaveStaticNatural.lean:116-121`).  For χ-positive this is verbatim `ne_of_gt`. | (i) |
| `WholeLineWeightedRegularityChiNegPlateauPersistenceNatural.lean:85-88` | Selects the χ-negative weighted-convergence theorem.  The χ-positive mirror cited above has the same conclusion. | F → (i) |
| `WholeLineWeightedRegularityChiNegPlateauPersistenceNatural.lean:89-99` | Passes `hchi.le` to the late common scaled-trap producer.  Its terminal uses are only ceiling/range routing, detailed in §1.2. | F → (i) |
| `WholeLineWeightedRegularityChiNegPlateauPersistenceNatural.lean:120-128` | Passes strict negativity to the prescribed-time plateau seed.  That seed has class-(i) range/nonzero uses before its terminal `hχ` barrier field. | F → (i), (ii) |
| `WholeLineWeightedRegularityChiNegPlateauPersistenceNatural.lean:129-138` | Copies `hcondQ.hχ` into the coefficient-one condition used on every window. | F → (i), (ii) |
| `WholeLineWeightedRegularityChiNegPlateauPersistenceNatural.lean:146-148` | Passes `hchi.le` into plateau propagation, reaching the one-window range route and both operator ledgers. | F → (i), (ii) |

There are no other occurrences of the target `hchi` in this theorem.

The first row is also terminally sign-symmetric, not merely syntactically so.
`paper5WaveStaticNaturalData_of_wave` uses its nonzero hypothesis only in the
call at `WholeLineWeightedRegularityWaveStaticNatural.lean:150-156` to
`remark_5_1_smooth_part1`; that theorem uses it only to prove
`0 < |p.χ|^σ` at `Statements.lean:12477-12480`.  The quantity and its
positivity lemma are defined/proved at `Statements.lean:12075-12095` entirely
through `|p.χ|`.  The second occurrence of this same nonzero route, in the
fixed-time seed at
`WholeLineWeightedRegularityChiNegFixedTimePlateauSeedNatural.lean:71-73`,
has the identical terminal use.  Both are class **(i)**.

### 1.2 Non-barrier routing branches which receive `hchi`

These are dependencies of the target/seed, but they do not use the sign in a
lower-barrier inequality.

1. **Late common scaled trap.**

   - `exists_eventual_common_global_inTimeWaveTrapSet_chi_nonpos` is declared
     at `WholeLineWeightedRegularityGlobalScaledTrapFamilyNatural.lean:21-58`.
     It forwards `hchi` at lines `59-64` and uses it once more only to build
     `WholeLineCauchyCeilingRegime.of_nonpositive` at lines `76-84`.
   - The forwarded theorem
     `exists_eventual_common_shifted_inTimeWaveTrapSet_chi_nonpos` is declared
     at `WholeLineWeightedRegularityScaledTrapFamilyNatural.lean:76-119`.
     Its only direct sign uses are the ceiling regime at lines `133-134` and
     forwarding to the H1-window producer at lines `135-139`.
   - The terminal producer
     `exists_eventual_common_weighted_H1_restart_window_chi_nonpos` is declared
     at `WholeLineWeightedRegularityLateH1WindowNatural.lean:629-679`.  Its
     complete sign use is: create the nonpositive ceiling regime at lines
     `683-684`, and rewrite `MChi p = 1` to put `MChi` inside the global clamp
     at lines `691-696`.  Everything after line 696 is sign-free.

   Classification: **(i)** for this blocker audit.  It is a range/ceiling
   branch, not a resolver-sign argument and not a barrier-shape choice.  The
   χ-positive replacement needs the χ-positive global range bound rather than
   `MChi_eq_one_of_chi_nonpos`.

2. **Positive-time H0/H1 data used to seed the profile.**

   `wholeLineCauchyGlobal_exists_compatible_lowerBarrierPlateau_seed_at_time_chi_neg`
   is declared at
   `WholeLineWeightedRegularityChiNegFixedTimePlateauSeedNatural.lean:25-58`.
   Before reaching the barrier constructor, it uses `hchi` as follows:

   - ceiling regime: lines `59-60`;
   - nonzero wave-static data: lines `71-73`;
   - H0 slice theorem call: lines `78-92`; the terminal uses in
     `wholeLineCauchyGlobal_fullWeightedL2_integrable_wave_chi_nonpos_of_initialCloseness`
     (declared at `WholeLineWeightedRegularityGlobalSliceH0Natural.lean:20-48`)
     are only the ceiling regime and `MChi p = 1` at lines `57-64`;
   - H1 slice theorem call: lines `93-106`.  The first wrapper,
     `paper5WeightedPopulationX_sq_integrable_global_chi_nonpos_of_initialCloseness`
     (declared at `WholeLineWeightedRegularityGlobalH0.lean:266-301`), uses
     the ceiling regime and `MChi p = 1` at lines `302-309`, then forwards
     `hchi` at lines `315-318`; the terminal
     `paper5WeightedPopulationX_sq_integrable_global_chi_nonpos` (declared at
     `WholeLineWeightedRegularityGradientGlobal.lean:498-532`) again uses only
     the ceiling regime and `MChi p = 1` at lines `533-540`.

   Classification: **(i)**.  These are range wrappers.  In particular, the H0
   positive mirror already exists as
   `wholeLineCauchyGlobal_fullWeightedL2_integrable_wave_chi_pos_of_initialCloseness`
   (`WholeLineWeightedRegularityGlobalSliceH0ChiPosNatural.lean:17-46`), whose
   replacement range argument is at lines `55-66`.

### 1.3 Seed and scalar thresholds

The fixed-time theorem finally forwards `hchi.le` to
`exists_chiNonpos_compatible_lowerBarrierPlateau_seed_of_profile_bounds` at
`WholeLineWeightedRegularityChiNegFixedTimePlateauSeedNatural.lean:136-138`.
That theorem is declared at
`WholeLineWeightedRegularityChiNegCompatiblePlateauSeedNatural.lean:28-56`.
Its **only** use of the hypothesis `hχ : p.χ ≤ 0` is to fill
`PaperLemma42ExactConditions.hχ` at lines `80-88`.  This is F → (i), (ii),
because the field is later inspected by the two operator ledgers in §1.5.
The receiving structure, including the `hχ` field, is declared at
`WaveLemma42Paper.lean:45-54`.

All actual choices made by the seed are sign-symmetric:

- `paperDMin` contains `|χ|`, not a sign hypothesis
  (`WaveLemma42Paper.lean:28-31`), and `paperScaledDMin` does the same
  (`WholeLineWeightedRegularityScaledPlateauOperatorNatural.lean:24-28`).
- `constantSubsolutionThreshold` is
  `min (1/(1+|χ|)) (...)` (`Statements.lean:6060-6063`).
- The seed puts `1/(1+|p.χ|)` into `smallHeight` at
  `WholeLineWeightedRegularityChiNegCompatiblePlateauSeedNatural.lean:112-119`,
  obtains the corresponding splice bound at lines `151-164`, and proves the
  threshold at lines `180-190`.  None of those steps uses `hχ`.

These are all **(i)**.  In particular, `constantSubsolutionThreshold` itself
does not encode `χ ≤ 0`; only the theorem proving that a constant is a
subsolution does.

### 1.4 Barrier shape: no class-(iii) use

The raw profile
`exp(-κx) - D exp(-κtilde x)` is defined without χ at
`Statements.lean:3924-3925`.  Its patched plateau is also defined without χ
at `Statements.lean:4432-4437`.  Thus the negative proof chain has **no
class-(iii) use**: neither the two-exponential tail nor the constant-left
patch depends on the sign.

The existing positive branch confirms this rather than merely suggesting it.
There are three relevant positive results, with importantly different trap
heights:

- For a trap of height exactly `1`,
  `paperWaveOperator_const_subsolution_nonneg_of_chi_nonneg` uses the same
  `constantSubsolutionThreshold` under `0 ≤ χ`, `χ < chiStar`, and the
  exponent equality (`Statements.lean:7393-7457`; its frozen-subsolution
  wrapper is at lines `7459-7469`).  This directly shows that neither the
  constant-left profile nor the threshold is intrinsically negative-sign
  structure.
- For a trap of height exactly `MChi p`,
  `paperWaveOperator_const_subsolution_nonneg_pos_MChi` proves a positive
  constant ledger under the stronger `χ < 1/2` budget
  (`WavePositivePlateauComparison.lean:64-138`).  It uses the alternative
  scalar height `paper1PositivePlateauFloor p`, defined/proved positive at
  lines `19-30`.
- `exists_positivePlateau_D` chooses `D` for that scalar height while keeping
  the same `lowerBarrierPlateau` shape (lines `143-164`), and
  `paperWaveOperator_lowerBarrierPlateau_nonneg_pos_away` combines the
  positive constant and raw ledgers for the full patched barrier away from
  the splice (lines `473-542`).

Thus what changes is the scalar admissibility budget and the treatment of the
resolver-value term, not the spatial profile.  These existing positive
results are not yet a drop-in replacement for the current late-window chain:
the negative propagation has an arbitrary common-trap height `Q ≥ 1` (with no
proof that it equals `1` or `MChi p`), while
the full positive patched theorem assumes height `MChi p` and the full-regime
positive constant theorem in `Statements.lean` assumes height `1`.  At a
general `Q > 1`, an upper bound for the frozen field scales as `Q^γ`, so the
constant-left scalar budget must be redone (or the window normalized).  That
is a class-(ii) ledger/budget issue, not class-(iii) profile shape.

### 1.5 Propagation and every terminal barrier-operator use

`wholeLineCauchyGlobal_ge_lowerBarrierPlateau_on_all_late_windows_chiNonpos`
is declared at
`WholeLineWeightedRegularityChiNegPlateauPropagationNatural.lean:23-53`.
It only forwards `hchi` to the one-window theorem, once in the base case at
lines `69-74` and once in the successor case at lines `92-97`.

The one-window theorem
`wholeLineCauchyGlobal_coMovingRestart_ge_lowerBarrierPlateau_chiNonpos_scaled`
is declared at
`WholeLineWeightedRegularityChiNegPlateauWindowComparisonNatural.lean:27-48`.
It has three sign-relevant edges:

| Use | Terminal effect | Class |
|---|---|---|
| ceiling regime at `WholeLineWeightedRegularityChiNegPlateauWindowComparisonNatural.lean:64-65` | Only selects global regularity/range data. | (i) |
| call to `paperWaveOperator_lowerBarrierPlateau_nonneg_chiNonpos_scaled_away` at lines `233-243` | Reaches both the raw-tail and constant-left ledgers below. | F → (i), (ii) |
| direct constant-subsolution call at the C1 splice at lines `292-298` | Reaches the constant ledger below. | F → (i), (ii) |

The raw-tail terminal theorem is
`paperWaveOperator_lowerBarrierRaw_nonneg_chiNonpos_scaled`, declared at
`WholeLineWeightedRegularityScaledPlateauOperatorNatural.lean:144-155`.
Its auxiliary calls do receive the whole `hcond`, but they do not inspect
`hcond.hχ`: the scaled `DMin` comparison is at lines `38-55`, the scaled
`K`-term estimate at lines `71-142`, and the normalized logistic estimate at
`WaveLemma42Paper.lean:1238-1284`; raw-profile nonnegativity is at
`WaveLemma42Paper.lean:296-311`.  The sign field is first read in the
pointwise operator ledger below.
Its complete use of `hcond.hχ` is:

1. `-p.χ = |p.χ|` at lines `211-212`, followed by the algebraic companion
   `p.χ = -|p.χ|` at line `213`, and use of both rewrites in the exact operator
   expansion at lines `232-242`: **(i)**.
2. The derivative chemotaxis term is bounded by its absolute magnitude at
   lines `218-226`; the sign enters only through the preceding
   `-χ = |χ|` rewrite: **(i)**.  This estimate has a χ-positive analogue with
   the multiplication direction reversed; it does not discard a resolver
   value term.
3. The value-resolver term
   `good = W * (-χ * W^(m-1) * V)` is proved nonnegative from
   `hcond.hχ` and `V ≥ 0` at lines `227-231`, then discarded in `hop_lower` at
   lines `249-253`: **(ii)**.  This is a genuine one-sided use.

The patched wrapper
`paperWaveOperator_lowerBarrierPlateau_nonneg_chiNonpos_scaled_away` is
declared at
`WholeLineWeightedRegularityScaledPlateauOperatorNatural.lean:288-300`.
On its constant-left branch it forwards `hcond.hχ` to the constant theorem at
lines `302-317`; on its raw-right branch it calls the raw theorem at lines
`344-350`.  These introduce no additional sign argument.

Finally, the constant terminal theorem
`paperWaveOperator_const_subsolution_nonneg_of_chi_nonpos` is declared at
`Statements.lean:7328-7334`.  Its complete sign use is:

1. use `d ≤ 1/(1+|χ|)` and the `|χ|` budget at lines `7337-7365`, then rewrite
   `-χ = |χ|` at lines `7366-7370`: **(i)**;
2. prove
   `0 ≤ (-χ) d^(m-1) frozenElliptic(...)` from `hχ` at lines `7371-7379`, and
   discard it in the final `nlinarith` at line `7380`: **(ii)**.

This constant theorem is reached twice in one-window comparison: through the
away-from-splice wrapper
(`WholeLineWeightedRegularityScaledPlateauOperatorNatural.lean:314-317`) and
directly at the splice
(`WholeLineWeightedRegularityChiNegPlateauWindowComparisonNatural.lean:294-298`).

For call-graph clarity, the older unscaled negative ledger
`PaperLemma42PointwiseEstimate_of_badTermEstimate`
(`WaveLemma42Paper.lean:1743-1821`) is not called by this persistent-plateau
chain; the scaled theorem repeats its pointwise algebra.  Its sign reads at
lines `1767-1769` and `1784-1788` are the same class-(i) normalization and
class-(ii) favorable-value discard, so they are not additional mechanisms in
the target chain.

**Plateau verdict.**  Every class-(i) component is already expressed through
`|χ|` or is a range-wrapper replacement.  There is no class-(iii) profile
dependence.  The only genuine negative-sign facts are the two class-(ii)
discarded resolver-value terms: one on the raw tail and one on the constant
plateau.  The repository's positive raw ledger
(`WaveLemma42Paper.lean:3218-3306`, assembled as a general-`M` theorem at
lines `3338-3350`) treats the raw resolver value as an adverse budget rather
than discarding it.  Its condition structure requires
`χ < min (1/2) chiStar` (`WaveLemma42Paper.lean:2582-2592`).  The positive
patched theorem handles the constant branch
at height `MChi p` (`WavePositivePlateauComparison.lean:473-542`), and the
full-`χ < chiStar` constant theorem handles height `1`
(`Statements.lean:7393-7469`).  The unresolved mismatch is the actual
arbitrary `Q > 1` window height, not the barrier shape.

## 2. Buffered KPP floor

### 2.1 Direct uses in `leftHalfLine_ge_chiNegKPPFloor_of_buffer`

The theorem is declared at
`WholeLineWeightedRegularityChiNegBufferedHalfLineComparisonNatural.lean:478-516`.

| Use | Effect | Class |
|---|---|---|
| The defect and returned rate contain `(-p.χ)` at lines `483-485` and `513-518`. | Under `hchi`, this is the magnitude `|p.χ|`; the formulas themselves need no order fact. | (i) |
| `hH : 0 ≤ H` at lines `520-524` | The inner `by linarith` at line 523 uses `hchi` to prove `0 ≤ -p.χ`.  This makes `H` a nonnegative adverse defect. | (ii) |
| application of `leftHalfLine_ge_of_buffered_nonpositive_resolver_reaction_subsolution` at lines `529-531` | Forwards `hchi` to the comparison ledger in §2.2. | F → (ii) |

No later KPP-floor obligation uses `hchi`: lines `525-551` use only positivity
and smallness of the already constructed scalar `H`.

### 2.2 Every terminal use in the buffered comparison ledger

`leftHalfLine_ge_of_buffered_nonpositive_resolver_reaction_subsolution` is
declared at
`WholeLineWeightedRegularityChiNegBufferedHalfLineComparisonNatural.lean:27-66`.
The following are all uses of its `hchi : p.χ ≤ 0` (the `linarith` uses are
implicit-context uses and therefore do not appear in a simple identifier
grep):

1. `Kchem := (-χ) M^m rpowLip(γ,M)` is defined at line `76`; its
   nonnegativity is proved from `hchi` at lines `169-173`: **(ii)**.  The local
   fact `hKchem` is never referenced later, so this is a dead one-sided proof
   site rather than a mathematical dependency of the comparison conclusion.
2. In `hchemZero`, the contact coefficient
   `(-χ) (q t x)^m` is proved nonnegative at lines `339-340`: **(ii)**.
3. The same sign is used to multiply the bound
   `(q t x)^m ≤ M^m` without reversing it at lines `341-343`: **(ii)**.
4. The coefficient `(-χ) M^m` is again proved nonnegative when multiplying
   the rpow Lipschitz estimate at lines `359-364`: **(ii)**.
5. Lines `375-389` multiply the resolver-tail estimate by the nonnegative
   coefficient from item 2, compare it using item 3, and spend `hdefect`.
   This is the terminal tail-defect use of the same one-sided sign: **(ii)**.

There are no other sign uses in this 446-line proof.  In particular:

- the gradient chemotaxis term is treated with `|p.χ|` at lines `229-273`, so
  it is sign-agnostic;
- the algebraic decomposition at lines `390-401` is a ring identity and does
  not use `hchi`;
- the scalar half-line maximum theorem called at lines `464-466` has no χ
  parameter at all (its statement is
  `WholeLineWeightedRegularityHalfLineMaximumNatural.lean:353-377`).

The decisive inequality chain is visible at lines `300-312` and `335-401`:

```text
V(x) >= (1 - exp(-R)/2) a^γ
q(x)^γ - V(x)
  <= (q(x)^γ - a^γ) + (exp(-R)/2) M^γ,
χ q(x)^m (V(x)-q(x)^γ)
  = (-χ) q(x)^m (q(x)^γ-V(x)).
```

Only the last multiplication needs `-χ ≥ 0`.  For `χ > 0`, the adverse
quantity is instead `V(x)-q(x)^γ`; the lower resolver bound supplied by the
buffer gives no upper bound for that quantity.  Replacing `-χ` by `|χ|`
therefore does **not** generalize this comparison.

### 2.3 Resolver and KPP infrastructure are sign-free

- `frozenElliptic_lower_of_left_halfLine_floor` is declared at
  `WholeLineWeightedRegularityHalfLineResolverLowerNatural.lean:23-30`; its
  complete proof, lines `31-94`, has no χ or sign hypothesis.
- `chiZeroKPPFloor C L lam t = L-(L-C)exp(-lam t)` is defined at
  `WholeLineWeightedRegularityChiZeroKPPFloorNatural.lean:19-21`.  Its
  derivative, range, convergence, and reaction-subsolution lemmas are at
  lines `23-104`; none contains χ.
- `chiNegKPPFloorRate alpha C L H` is defined using only the abstract defect
  `H` at `WholeLineWeightedRegularityChiNegKPPFloorNatural.lean:19-22`.
  Its positivity/budget lemmas are at lines `24-55`, and
  `chiNegKPPFloor_deriv_add_defect_le_reaction` is at lines `57-101`; none
  contains χ or a sign hypothesis.

Thus these definitions have no class-(iii) dependence either.  The temporal
floor shape and its defect-reserving rate can be reused once an appropriate
nonnegative defect is available.  The blocker is entirely class (ii): for
χ-positive, obtaining that defect requires an upper resolver control as well
as the lower resolver control, hence a coupled two-sided squeeze rather than
the present single lower floor.

## Mechanism summary

- Persistent plateau: the normalization, thresholds, profile choice, and
  range-wrapper uses are class (i).  The two terminal class-(ii) mechanisms
  are precisely the raw-tail and constant-left resolver-value terms.  The
  existing positive analogues budget those terms instead, subject to their
  stated trap-height/smallness regimes.  There is no class-(iii) profile use.
- Buffered KPP comparison: writing the defect with `-χ` is class (i), while
  proving it nonnegative and multiplying the lower-resolver estimates by it
  are class (ii), at every site enumerated in §2.1–§2.2.  The resolver and
  floor definitions themselves are sign-free, so there is no class-(iii)
  floor-shape use.
