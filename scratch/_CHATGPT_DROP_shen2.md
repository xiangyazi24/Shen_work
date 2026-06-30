# Q2309 shen2: constant-branch / no-left-plateau wiring audit

Repo: `xiangyazi24/Shen_work`, branch `main`.

## Bottom line

The constant-branch route described in the prompt is already present on current `main` in:

```text
ShenWork/Paper1/UpperBarrierContact.lean
```

The left-plateau residual can be discharged from a `FrozenStationaryWaveProfile` only under **strict** positive sensitivity:

```lean
0 < p.χ
```

plus an upper bound such as `p.χ < 1`.  The non-strict assumption

```lean
0 ≤ p.χ
```

is too weak, because the case `p.χ = 0` leaves `MChi p = 1`, and a left plateau at level `1` is not contradicted by the left-end limit `U → 1`.

## 1. Exact projection for the left-end limit

For

```lean
hprofile : FrozenStationaryWaveProfile p c U
```

the projection giving the profile limit is:

```lean
hprofile.lim_neg_inf.1 : Tendsto U atBot (𝓝 (1 : ℝ))
```

The second component is the elliptic profile limit:

```lean
hprofile.lim_neg_inf.2 : Tendsto (frozenElliptic p U) atBot (𝓝 (1 : ℝ))
```

Source shape in `ShenWork/Paper1/Statements.lean` is visible from the constructor wrapper:

```lean
theorem FrozenStationaryWaveProfile.mk_from_stationary
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hc : 0 < c)
    (hU_pos : ∀ x, 0 < U x)
    (hU_bdd : IsCUnifBdd U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hlim_neg : Tendsto U atBot (𝓝 1) ∧ Tendsto (frozenElliptic p U) atBot (𝓝 1))
    (hlim_pos : Tendsto U atTop (𝓝 0) ∧ Tendsto (frozenElliptic p U) atTop (𝓝 0)) :
    FrozenStationaryWaveProfile p c U :=
  { hc
    U_pos := hU_pos
    stationary_eq := hstat
    elliptic_eq := frozenElliptic_ode p hU_bdd (fun x => (hU_pos x).le)
    lim_neg_inf := hlim_neg
    lim_pos_inf := hlim_pos }
```

So the actual extraction expression is exactly:

```lean
exact hprofile.lim_neg_inf.1
```

This is already used in `UpperBarrierContact.lean`:

```lean
theorem no_const_left_plateau_of_profile_chi_pos
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hprofile : FrozenStationaryWaveProfile p c U)
    (hχ_pos : 0 < p.χ) (hχ_lt : p.χ < 1) :
    ∀ x, MChi p < Real.exp (-(kappa c) * x) →
      (∀ y, y ≤ x → U y = MChi p) → False :=
  no_const_left_plateau_of_tendsto_atBot_one
    hprofile.lim_neg_inf.1
    (MChi_ne_one_of_chi_pos_lt_one p hχ_pos hχ_lt)
```

## 2. Existing `MChi p ≠ 1` / `1 < MChi p` API

Current `main` already has both scalar lemmas in `ShenWork/Paper1/UpperBarrierContact.lean`:

```lean
theorem one_lt_MChi_of_chi_pos_lt_one
    (p : CMParams) (hχ_pos : 0 < p.χ) (hχ_lt : p.χ < 1) :
    1 < MChi p
```

and:

```lean
theorem MChi_ne_one_of_chi_pos_lt_one
    (p : CMParams) (hχ_pos : 0 < p.χ) (hχ_lt : p.χ < 1) :
    MChi p ≠ 1
```

The proof route is already exactly the expected one:

```lean
theorem one_lt_MChi_of_chi_pos_lt_one
    (p : CMParams) (hχ_pos : 0 < p.χ) (hχ_lt : p.χ < 1) :
    1 < MChi p := by
  have hden_pos : 0 < 1 - p.χ := by linarith
  have hbase_gt : 1 < 1 / (1 - p.χ) := by
    rw [lt_div_iff₀ hden_pos]
    linarith
  have hα_pos : 0 < p.α := lt_of_lt_of_le zero_lt_one p.hα
  have hexp_pos : 0 < 1 / p.α := div_pos one_pos hα_pos
  rw [MChi_eq_rpow_of_chi_pos p hχ_pos]
  exact Real.one_lt_rpow hbase_gt hexp_pos

theorem MChi_ne_one_of_chi_pos_lt_one
    (p : CMParams) (hχ_pos : 0 < p.χ) (hχ_lt : p.χ < 1) :
    MChi p ≠ 1 :=
  ne_of_gt (one_lt_MChi_of_chi_pos_lt_one p hχ_pos hχ_lt)
```

If the branch hypothesis is the usual Paper1 smallness

```lean
hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p)
```

then get `p.χ < 1` by:

```lean
have hχ_half : p.χ < (1 / 2 : ℝ) :=
  lt_of_lt_of_le hχ_small (min_le_left _ _)
have hχ_lt_one : p.χ < 1 := by linarith
```

If the available upper bound is instead

```lean
hχ_star : p.χ < chiStar p
```

then use:

```lean
have hχ_lt_one : p.χ < 1 := lt_of_lt_of_le hχ_star (chiStar_le_one p)
```

There is no valid lemma from only `0 ≤ p.χ` to `MChi p ≠ 1`; the equality case `p.χ = 0` is the obstruction.

## 3. Minimal wrapper status

### Already existing wrapper to reduce to strict exponential contact

`UpperBarrierContact.lean` already defines the two residual records:

```lean
structure PositiveUpperBarrierRemainingContactResidual
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop where
  no_const_left_plateau :
    ∀ x, MChi p < Real.exp (-(kappa c) * x) →
      (∀ y, y ≤ x → U y = MChi p) → False
  exp_strict_super_at_contact :
    ∀ x, Real.exp (-(kappa c) * x) < MChi p →
      U x = Real.exp (-(kappa c) * x) →
        frozenWaveOperator p c U
          (upperBarrier (kappa c) (MChi p)) x < 0

structure PositiveUpperBarrierExpStrictContactResidual
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop where
  exp_strict_super_at_contact :
    ∀ x, Real.exp (-(kappa c) * x) < MChi p →
      U x = Real.exp (-(kappa c) * x) →
        frozenWaveOperator p c U
          (upperBarrier (kappa c) (MChi p)) x < 0
```

The minimal existing wrapper from profile plus strict positive sensitivity is:

```lean
theorem PositiveUpperBarrierRemainingContactResidual.of_expStrict_profile_chi_pos
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hprofile : FrozenStationaryWaveProfile p c U)
    (hχ_pos : 0 < p.χ) (hχ_lt : p.χ < 1)
    (hstrict : PositiveUpperBarrierExpStrictContactResidual p c U) :
    PositiveUpperBarrierRemainingContactResidual p c U :=
  { no_const_left_plateau :=
      no_const_left_plateau_of_profile_chi_pos
        hprofile hχ_pos hχ_lt
    exp_strict_super_at_contact :=
      hstrict.exp_strict_super_at_contact }
```

That is exactly the requested “residual containing only `exp_strict_super_at_contact`” route.

### Important distinction

There is no wrapper that can produce

```lean
PositiveUpperBarrierExpStrictContactResidual p c U
```

from only

```lean
FrozenStationaryWaveProfile p c U
0 < p.χ
```

because `PositiveUpperBarrierExpStrictContactResidual` is precisely the remaining strict exponential-branch super-barrier residual.  The profile and strict-χ assumptions close the constant branch, not the exponential strict super-barrier field.

If a call site has the strict field as a plain function rather than as a structure, the shortest convenience wrapper would be:

```lean
import ShenWork.Paper1.UpperBarrierContact

open Filter Topology

namespace ShenWork.Paper1

noncomputable section

/-- Convenience wrapper: profile convergence and strict positive sensitivity close
constant-branch contact, leaving only the strict exponential contact function. -/
theorem PositiveUpperBarrierRemainingContactResidual.of_expStrictFun_profile_chi_pos
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hprofile : FrozenStationaryWaveProfile p c U)
    (hχ_pos : 0 < p.χ) (hχ_lt : p.χ < 1)
    (hstrict :
      ∀ x, Real.exp (-(kappa c) * x) < MChi p →
        U x = Real.exp (-(kappa c) * x) →
          frozenWaveOperator p c U
            (upperBarrier (kappa c) (MChi p)) x < 0) :
    PositiveUpperBarrierRemainingContactResidual p c U :=
  PositiveUpperBarrierRemainingContactResidual.of_expStrict_profile_chi_pos
    hprofile hχ_pos hχ_lt
    { exp_strict_super_at_contact := hstrict }

end

end ShenWork.Paper1
```

This is only a convenience theorem; it adds no new math.

## Full downstream no-contact wrapper already present

Once regular stationary data are also available, current `main` already has the wrapper to full contact contradictions:

```lean
theorem PositiveUpperBarrierContactContradictions.of_expStrict_profile_chi_pos_regularStationary
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < kappa c)
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U)
    (hprofile : FrozenStationaryWaveProfile p c U)
    (hχ_pos : 0 < p.χ) (hχ_lt : p.χ < 1)
    (hreg : StationaryC2RegularityFromEquation p c (kappa c) (MChi p))
    (hstrict : PositiveUpperBarrierExpStrictContactResidual p c U) :
    PositiveUpperBarrierContactContradictions p c U
```

It combines:

```lean
positiveUpperBarrierSmoothBranchNoContact_of_expStrict_profile_chi_pos
PositiveUpperBarrierContactContradictions.of_smoothBranchNoContact_regularStationary
```

and uses the existing interface no-contact lemma:

```lean
positiveUpperBarrier_interfaceNoContact_of_regular_stationary
```

## Minimal branch-level implication

For a branch whose hypotheses include strict positive sensitivity, the intended shape is:

```lean
import ShenWork.Paper1.UpperBarrierContact

open Filter Topology

namespace ShenWork.Paper1

noncomputable section

/-- Branch-facing narrowing: strict positive sensitivity and profile convergence
turn the remaining-contact residual into the exp-strict-only residual. -/
theorem remainingContact_of_profile_strictChi_expStrict
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hprofile : FrozenStationaryWaveProfile p c U)
    (hχ_pos : 0 < p.χ)
    (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    (hstrict : PositiveUpperBarrierExpStrictContactResidual p c U) :
    PositiveUpperBarrierRemainingContactResidual p c U := by
  have hχ_half : p.χ < (1 / 2 : ℝ) :=
    lt_of_lt_of_le hχ_small (min_le_left _ _)
  have hχ_lt_one : p.χ < 1 := by linarith
  exact
    PositiveUpperBarrierRemainingContactResidual.of_expStrict_profile_chi_pos
      hprofile hχ_pos hχ_lt_one hstrict

end

end ShenWork.Paper1
```

Again, this wrapper is redundant with the existing theorem plus a two-line derivation of `p.χ < 1`, but it is the compile-oriented branch-facing statement.

## Exact answers

1. Use:

   ```lean
   hprofile.lim_neg_inf.1
   ```

   for `Tendsto U atBot (𝓝 1)`.

2. Yes.  Current main already has:

   ```lean
   one_lt_MChi_of_chi_pos_lt_one
   MChi_ne_one_of_chi_pos_lt_one
   ```

   in `ShenWork/Paper1/UpperBarrierContact.lean`.  They use `MChi_eq_rpow_of_chi_pos` and `Real.one_lt_rpow`.  There is no valid non-strict `0 ≤ p.χ` version.

3. The minimal existing wrapper is:

   ```lean
   PositiveUpperBarrierRemainingContactResidual.of_expStrict_profile_chi_pos
   ```

   It turns profile convergence plus `0 < p.χ`, `p.χ < 1`, and the exp-strict residual into the full remaining-contact residual.  With regular stationary data, the existing theorem

   ```lean
   PositiveUpperBarrierContactContradictions.of_expStrict_profile_chi_pos_regularStationary
   ```

   closes the full no-contact package.
