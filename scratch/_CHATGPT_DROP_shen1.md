# Q2428 shen1 — integrated first-crossing proof-route audit

Repo: `xiangyazi24/Shen_work`

Audited ref: `main` at `8466aff054e1a3dd7fb3d02a0c4523132c6d6722`

Scope: the current Paper2/Paper3 Moser route around `IntegratedMoserDissipationDropBefore`, `RelativeMoserInterpolationBefore`, and the pointwise/nonnegative-`B` consumers.

## Verdict

The current repo has the honest integrated dissipation predicate, but **no integrated-first-crossing consumer yet**.  The existing Moser consumers still run through pointwise/nonnegative-`B` drop:

```lean
MoserDissipationDropBeforeNonnegB
moser_step_of_energy_nonnegB_relative_interpolation
moser_iteration_chain_of_energy_nonnegB_relative_interpolation
all_exponents_of_energy_nonnegB_relative_interpolation_lpmono
intervalDomain_boundedBefore_of_energy_nonnegB_relative_interpolation
intervalDomain_allLpBoundFromBootstrap_of_relative_moser_step_nonnegB
intervalDomain_endpointBoundFromLp_of_quantitative_root_tower_nonnegB
```

and `P3MoserActualWiring` still exposes:

```lean
intervalDomain_allLpBoundFromBootstrap_of_actual_atoms_nonnegB
intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
```

The real next theorem is exactly the one in the prompt: a one-step promotion theorem whose proof uses the integrated estimate and relative interpolation directly.  It must **not** be implemented as an adapter

```lean
IntegratedMoserDissipationDropBefore → MoserDissipationDropBeforeNonnegB
```

because the source already records the counterexample

```lean
unitLinearDrop_not_MoserDissipationDropBeforeNonnegB
```

and the comments in `P3MoserDissipationShape.lean` explicitly identify the integrated first-crossing estimate as the faithful replacement for the false pointwise drop.

The smallest first Lean lemma worth proving next is an algebraic extraction from the integrated inequality:

> from `IntegratedMoserDissipationDropBefore`, endpoint bounds on `Y_p`, and a bound on `∫ max 1 Y_p`, prove a bound on the time integral of the Moser gradient `∫ G_p`.

This is the first nontrivial bridge between the existing integrated predicate and the future first-crossing proof.  It is smaller than the full one-step theorem and does not require any false pointwise drop.

## Existing source facts to reuse

### Integrated predicate and packaging

Current source already defines:

```lean
def IntegratedMoserDissipationDropBefore
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T _rho p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → ∃ C, 0 ≤ C ∧
    ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
      D.integral (fun x => (u t2 x) ^ p) -
          D.integral (fun x => (u t1 x) ^ p) +
        2 * ∫ s in t1..t2,
          D.integral (fun x =>
            (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2) ≤
      C * p * ∫ s in t1..t2,
        max 1 (D.integral (fun x => (u s x) ^ p))
```

and the simple wrapper:

```lean
integratedMoserDissipationDropBefore_of_integrated_energy
```

This wrapper only packages an already-supplied integrated estimate.  It is useful once the PDE estimate is proved, but it does not by itself consume the estimate.

### Relative interpolation and lower-order conversion

The current relative interpolation predicate is:

```lean
def RelativeMoserInterpolationBefore
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → ∀ eps > 0, ∃ Ceps, 0 ≤ Ceps ∧
    ∀ t, 0 < t → t < T →
      D.integral (fun x => (u t x) ^ (p + rho)) ≤
        eps * D.integral (fun x =>
          (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
        Ceps * D.integral (fun x => (u t x) ^ p)
```

The existing lemma

```lean
moser_constant_interpolation_of_relative_interpolation_and_lp_bound
```

already turns this into the constant-form interpolation required by the old pointwise Moser step, using the current `LpPowerBoundedBefore D p T u` bound.  This lemma should be reused in the integrated route too, but only for **time-average control** of the next exponent; it does not produce a pointwise bound without the first-crossing argument.

### Existing stage-1 closure pieces

The following existing lemmas remain reusable once a one-step predicate is available:

```lean
IntervalDomainMoserClosure.all_exponents_of_chain_and_lp_mono
IntervalDomainMoserClosure.intervalDomain_boundedBefore_of_moser_quantitative_endpoint
```

For the concrete interval domain, the current source also has:

```lean
intervalDomain_u_rpow_intervalIntegrable_of_regularity
intervalDomain_LpPowerBoundedBefore_mono_of_integrable_nonneg
lpMono_of_classical_solution_power_integrable
```

These discharge the monotonicity/integrability side in the interval-domain classical-solution route.

### Existing pointwise consumer chain, not reusable for integrated proof

The following are useful as a shape reference, but they should not be called from the integrated route unless the proof genuinely produces their hypotheses:

```lean
moser_step_of_energy_nonnegB_relative_interpolation
moser_iteration_chain_of_energy_nonnegB_relative_interpolation
intervalDomain_all_exponents_of_energy_nonnegB_relative_interpolation_inside
intervalDomain_boundedBefore_of_energy_nonnegB_relative_interpolation
```

They require `MoserDissipationDropBeforeNonnegB`, which is deliberately stronger/different from `IntegratedMoserDissipationDropBefore`.

## Routine Stage 1 consumer layer from a supplied one-step predicate

This layer is buildable and low-risk.  It should live either in `P3MoserDissipationShape.lean` after the integrated predicate, or in a new file such as:

```text
ShenWork/PDE/P3MoserIntegratedConsumer.lean
```

importing:

```lean
import ShenWork.PDE.P3MoserDissipationShape
```

A clean predicate is:

```lean
def IntegratedMoserOneStep
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p →
    LpPowerBoundedBefore D p T u →
      LpPowerBoundedBefore D (p + rho) T u
```

Then the routine consumer layer is:

```lean
theorem moser_iteration_chain_of_integrated_oneStep
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T p0 rho : ℝ}
    (hrho : 0 < rho)
    (hbase : LpPowerBoundedBefore D p0 T u)
    (hstep : IntegratedMoserOneStep D u T rho p0) :
    ∀ n : ℕ, LpPowerBoundedBefore D (p0 + n * rho) T u := by
  intro n
  induction n with
  | zero =>
      simp only [CharP.cast_eq_zero, zero_mul, add_zero]
      exact hbase
  | succ n ih =>
      have hexp_eq :
          p0 + (↑(n + 1) : ℝ) * rho = (p0 + ↑n * rho) + rho := by
        push_cast
        ring
      rw [hexp_eq]
      have hp_ge : p0 ≤ p0 + ↑n * rho :=
        le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hrho.le)
      exact hstep (p0 + ↑n * rho) hp_ge ih
```

and then:

```lean
theorem all_exponents_of_integrated_oneStep_lpmono
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {N T rho p0 : ℝ}
    (hboot : AbstractLpBootstrapHypothesis D u N T rho p0)
    (hstep : IntegratedMoserOneStep D u T rho p0)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore D q T u → LpPowerBoundedBefore D p T u) :
    ∀ pExp > 1, LpPowerBoundedBefore D pExp T u :=
  all_exponents_of_chain_and_lp_mono
    (AbstractLpBootstrapHypothesis.rho_pos hboot)
    (moser_iteration_chain_of_integrated_oneStep
      (AbstractLpBootstrapHypothesis.rho_pos hboot)
      (AbstractLpBootstrapHypothesis.initial_lp_bound hboot)
      hstep)
    hLpMono
```

That is the routine stage.  It should be added only as a consumer of a supplied `hstep`; it must not hide the first-crossing theorem behind an axiom or placeholder.

## The hard theorem: real proof DAG

Target shape:

```lean
theorem integratedMoser_oneStep_of_integrated_dissipation_relative_interpolation
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T rho p0 : ℝ}
    (hrho : 0 < rho)
    (hinteg : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hreg : IntegratedMoserClosedTimeRegularity D u T rho p0) :
    IntegratedMoserOneStep D u T rho p0 :=
  -- real proof work
```

`hrho` is not optional.  `IntegratedMoserDissipationDropBefore` ignores the value of `rho` in its definition, and `RelativeMoserInterpolationBefore` also does not imply `0 < rho`.  The bootstrap route has `AbstractLpBootstrapHypothesis.rho_pos`; the standalone theorem must carry the positivity assumption explicitly.

The proof of the one-step theorem should be decomposed as follows.

### Step A. Normalize the current Lp bound

Input:

```lean
hLp : LpPowerBoundedBefore D p T u
```

Unpack:

```lean
rcases hLp with ⟨Mp, hMp⟩
```

But do not assume `0 ≤ Mp` syntactically.  Either prove it from nonnegativity and an inhabited time slab, or normalize to:

```lean
Mp' := max 0 Mp
```

and use `hYp_le : Y_p(t) ≤ Mp'`.

This avoids a hidden false assumption: `LpPowerBoundedBefore` stores only an existential upper bound; it does not store nonnegativity of the bound.

### Step B. Convert relative interpolation to constant interpolation at exponent `p`

Reuse:

```lean
moser_constant_interpolation_of_relative_interpolation_and_lp_bound
  hLp (hrel p hp)
```

This gives:

```lean
∀ eps > 0, ∃ Cconst, ∀ t, 0 < t → t < T →
  Y_{p+rho}(t) ≤ eps * G_p(t) + Cconst
```

where:

```lean
Y_r(t) := D.integral (fun x => (u t x) ^ r)
G_p(t) := D.integral (fun x =>
  (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2)
```

This is only a pointwise estimate in terms of `G_p(t)`.  It is not yet a pointwise bound on `Y_{p+rho}`.

### Step C. Extract a time-integrated gradient bound from `hinteg` at exponent `p`

From `hinteg p hp`, choose `C ≥ 0`.  For `a,b` with `0 ≤ a ≤ b ≤ T`, the integrated estimate gives:

```lean
Y_p(b) - Y_p(a) + 2 * ∫ s in a..b, G_p(s)
  ≤ C * p * ∫ s in a..b, max 1 (Y_p(s))
```

Using:

```lean
Y_p(a) ≤ Mp'
0 ≤ Y_p(b)
∫ s in a..b, max 1 (Y_p(s)) ≤ (b - a) * max 1 Mp'
0 ≤ C * p
```

one obtains:

```lean
2 * ∫ s in a..b, G_p(s)
  ≤ Mp' + C * p * ((b - a) * max 1 Mp')
```

This is the first real bridge lemma worth proving.

### Step D. Convert the gradient bound plus relative interpolation to a time-average bound for `Y_{p+rho}`

Integrate the constant-form interpolation from Step B over `a..b` and use Step C:

```lean
∫ s in a..b, Y_{p+rho}(s)
  ≤ eps * ∫ s in a..b, G_p(s) + Cconst * (b - a)
```

With `eps = 1`, this yields a finite bound on the time average of `Y_q`, `q = p + rho`, over interior windows.

This is where the all-exponent time-integrability part of `hreg` is needed.  Without it, Lean cannot justify interval integration of `Y_q`, and mathematically the average argument is not available.

### Step E. Pick a good time for `Y_q`

From a bound on

```lean
∫ s in a..b, Y_q(s)
```

with `a < b`, prove there exists `s ∈ (a,b)` such that

```lean
Y_q(s) ≤ average_bound / (b - a)
```

This needs:

```lean
0 < b - a
0 ≤ Y_q(s)       -- or a one-sided lower bound sufficient for average selection
IntervalIntegrable (fun s => Y_q(s)) volume a b
```

The proof is a standard contrapositive: if `Y_q(s)` is strictly above the average bound everywhere, then the integral is strictly above the bound.  This is a measure/interval-integral lemma, not a PDE estimate.

### Step F. Propagate from the good time to the target time using `hinteg` at exponent `q = p + rho`

Since `hrho : 0 < rho` and `hp : p0 ≤ p`, we have:

```lean
p0 ≤ q
```

Apply `hinteg q` on `[s,t]`:

```lean
Y_q(t) - Y_q(s) + 2 * ∫ r in s..t, G_q(r)
  ≤ Cq * q * ∫ r in s..t, max 1 (Y_q(r))
```

Drop the nonnegative gradient integral and use a Gronwall/first-crossing lemma for:

```lean
Y_q(t) ≤ Y_q(s) + Cq * q * ∫ r in s..t, max 1 (Y_q(r))
```

Equivalently for `F(t) := max 1 (Y_q(t))`:

```lean
F(t) ≤ max 1 (Y_q(s)) + Cq * q * ∫ r in s..t, F(r)
```

The repo already imports `Mathlib.Analysis.ODE.Gronwall` in `IntervalDomainLpMonotonicity.lean`, so the first-crossing/Gronwall component should use that API or a small local integral-Gronwall lemma.

### Step G. Handle the near-zero window without making the theorem vacuous

The average/good-time strategy over a window before `t` can blow up as `t → 0`.  The theorem therefore needs a **near-zero closed-time high-exponent seed** for `q`, or an initial trace/sup-norm input that implies one.

Do not hide this by assuming global `LpPowerBoundedBefore D q T u`; that is exactly the conclusion.  A non-vacuous regularity field should be local, for example:

```lean
∀ q, 1 < q → ∃ τ M, 0 < τ ∧ τ < T ∧
  ∀ t, 0 < t → t ≤ τ → D.integral (fun x => (u t x) ^ q) ≤ M
```

For interval-domain classical solutions this should ultimately come from initial trace plus bounded positive initial datum / closed-domain regularity, not from the Moser conclusion.

Then prove the first-crossing propagation only for `τ ≤ t < T`, using a good time in a fixed interior window, and use the near-zero seed for `0 < t ≤ τ`.

## Missing lemma family

### 1. Routine supplied-step consumer

These are buildable immediately from a supplied one-step predicate:

```lean
IntegratedMoserOneStep
moser_iteration_chain_of_integrated_oneStep
all_exponents_of_integrated_oneStep_lpmono
intervalDomain_boundedBefore_of_integrated_oneStep_quantitative_endpoint
```

The last one should mirror:

```lean
intervalDomain_boundedBefore_of_energy_nonnegB_relative_interpolation
```

but take `IntegratedMoserOneStep` instead of pointwise dissipation/energy.

### 2. Time-integrated gradient extraction

First proof target:

```lean
-- target statement, not yet present in the repo
 theorem integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M H : ℝ}
    (hinteg : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hp : p0 ≤ p) (hp_nonneg : 0 ≤ p)
    (haT : a ∈ Set.Icc (0 : ℝ) T)
    (hbT : b ∈ Set.Icc a T)
    (hYa : D.integral (fun x => (u a x) ^ p) ≤ M)
    (hYb_nonneg : 0 ≤ D.integral (fun x => (u b x) ^ p))
    (hmaxInt :
      ∫ s in a..b, max 1 (D.integral (fun x => (u s x) ^ p)) ≤ H) :
    ∃ C, 0 ≤ C ∧
      2 * ∫ s in a..b,
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2) ≤
        M + C * p * H
```

This is deliberately algebraic.  It should be provable directly from `hinteg p hp`, monotonicity of multiplication by `C * p`, and `linarith`/`nlinarith` after selecting `C`.

After this, prove the more usable corollary where `M` and `H` are supplied from `LpPowerBoundedBefore` plus time-integrability/closed-time nonnegativity.

### 3. Bound `∫ max 1 Y_p` from an Lp bound

Needed next:

```lean
∫ s in a..b, max 1 (Y_p s) ≤ (b - a) * max 1 Mp
```

Assumptions required:

```lean
a ≤ b
∀ s ∈ Set.Icc a b, Y_p s ≤ Mp
IntervalIntegrable (fun s => max 1 (Y_p s)) volume a b
```

This is not in the repo yet as a generic lemma.  It is measure-theoretic bookkeeping.

### 4. Time-average bound for the next exponent

Combine relative interpolation and the gradient integral bound:

```lean
integratedMoser_nextExponent_timeAverage_bound
```

Target form:

```lean
∀ a b, 0 < a → a < b → b < T →
  ∃ Bavg, ∫ s in a..b, D.integral (fun x => (u s x) ^ (p + rho)) ≤ Bavg
```

or with an explicit bound if convenient.

### 5. Good-time lemma

A pure interval-integral lemma:

```lean
exists_time_le_average_of_nonneg_intervalIntegral
```

Shape:

```lean
∀ f a b B, a < b →
  IntervalIntegrable f volume a b →
  (∀ᵐ? or ∀ s ∈ Set.Icc a b, 0 ≤ f s) →
  ∫ s in a..b, f s ≤ B →
    ∃ s ∈ Set.Ioo a b, f s ≤ B / (b - a)
```

For Lean, it may be easier to state the contrapositive with a strict lower bound and use `intervalIntegral.integral_mono_on`.

### 6. Integrated self-Gronwall / first-crossing propagation

Needed for `q = p + rho`:

```lean
integratedMoser_self_bound_from_good_time
```

Shape:

```lean
(hinteg : IntegratedMoserDissipationDropBefore D u T rho p0)
(hq : p0 ≤ q) (hq_nonneg : 0 ≤ q)
(hs : s ∈ Set.Icc 0 T) (ht : t ∈ Set.Icc s T)
(hYs : Y_q s ≤ B)
(hY_nonneg : ∀ r ∈ Set.Icc s t, 0 ≤ Y_q r)
(hY_int : IntervalIntegrable (fun r => max 1 (Y_q r)) volume s t) :
  Y_q t ≤ max 1 B * Real.exp (Cq * q * (t - s))
```

The exact constant can be adjusted.  The key is that this lemma must consume `hinteg q hq` directly and prove a bound on `Y_q(t)` by integral Gronwall, not by converting to `MoserDissipationDropBeforeNonnegB`.

### 7. Near-zero seed / closed-time regularity bridge

The one-step theorem needs a non-vacuous regularity package.  A safe structure is:

```lean
structure IntegratedMoserClosedTimeRegularity
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ) (T : ℝ) : Prop where
  Y_nonneg :
    ∀ p t, 0 < t → t < T →
      0 ≤ D.integral (fun x => (u t x) ^ p)
  Y_intervalIntegrable :
    ∀ p a b, 0 ≤ a → a ≤ b → b ≤ T →
      IntervalIntegrable
        (fun t => D.integral (fun x => (u t x) ^ p))
        MeasureTheory.volume a b
  maxY_intervalIntegrable :
    ∀ p a b, 0 ≤ a → a ≤ b → b ≤ T →
      IntervalIntegrable
        (fun t => max 1 (D.integral (fun x => (u t x) ^ p)))
        MeasureTheory.volume a b
  local_closed_bound :
    ∀ p a b, 0 < a → a ≤ b → b < T →
      ∃ M, ∀ t, a ≤ t → t ≤ b →
        D.integral (fun x => (u t x) ^ p) ≤ M
  near_zero_bound :
    ∀ p, 1 < p →
      ∃ τ M, 0 < τ ∧ τ < T ∧
        ∀ t, 0 < t → t ≤ τ →
          D.integral (fun x => (u t x) ^ p) ≤ M
```

This structure is only a proposal.  It should be specialized later for `intervalDomain` from `IsPaper2ClassicalSolution`, `InitialTrace`, and positive/bounded initial data.  Do not replace it by a global `∀ p, LpPowerBoundedBefore D p T u`; that would make the one-step theorem vacuous.

## Hidden false assumptions and vacuity risks

1. **No integrated-to-pointwise adapter.**  The current source has `unitLinearDrop_not_MoserDissipationDropBeforeNonnegB`, and the integrated predicate is explicitly documented as the faithful replacement for the pointwise drop.

2. **`rho > 0` must be explicit.**  The integrated predicate ignores `_rho`; the standalone one-step theorem must carry `hrho : 0 < rho` or be stated under `AbstractLpBootstrapHypothesis`.

3. **Endpoint mismatch:** `LpPowerBoundedBefore` is an open-time predicate:

```lean
∃ M, ∀ t, 0 < t → t < Tmax → ...
```

but `IntegratedMoserDissipationDropBefore` is stated on closed intervals `t1 ∈ Icc 0 T`, `t2 ∈ Icc t1 T`.  First lemmas should either work on strictly interior windows `0 < a`, `b < T`, or carry closed-time regularity explicitly.

4. **Relative interpolation has a lower-order factor.**  The term is `Ceps * Y_p(t)`, not a constant.  You must use `moser_constant_interpolation_of_relative_interpolation_and_lp_bound` or its integrated analogue with the current `LpPowerBoundedBefore` input.

5. **Average control is not pointwise control.**  Integrated dissipation at exponent `p` plus relative interpolation gives time-average control of `Y_{p+rho}`.  The pointwise `LpPowerBoundedBefore` conclusion needs a good-time lemma plus integrated self-Gronwall at exponent `p+rho`.

6. **Near-zero behavior is not automatic.**  A first-crossing argument on interior windows can bound later times, but it does not uniformly control `t → 0`.  The theorem needs a non-vacuous near-zero high-exponent bound from regularity/initial data.

7. **No old GN route.**  Do not use:

```lean
OldUnitIntervalPowerGNYoungForMoser
```

It is explicitly marked false for constants.  Also avoid the refuted global `IntervalDomainInterpolation` route.

## Smallest first Lean lemma to prove next

Prove the algebraic gradient-integral extraction lemma first.  It should go in `P3MoserDissipationShape.lean` after `IntegratedMoserDissipationDropBefore`, or in a new integrated-consumer file importing it.

A practical statement is:

```lean
namespace ShenWork.IntervalDomainExistence.P3MoserDissipationShape

/-- Algebraic consequence of the integrated Moser inequality: once the endpoint
`Y_p` values and the time integral of `max 1 Y_p` are controlled on a window,
the time integral of the Moser gradient is controlled on that window. -/
theorem integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M H : ℝ}
    (hinteg : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hp : p0 ≤ p) (hp_nonneg : 0 ≤ p)
    (haT : a ∈ Set.Icc (0 : ℝ) T)
    (hbT : b ∈ Set.Icc a T)
    (hYa : D.integral (fun x => (u a x) ^ p) ≤ M)
    (hYb_nonneg : 0 ≤ D.integral (fun x => (u b x) ^ p))
    (hmaxInt :
      ∫ s in a..b, max 1 (D.integral (fun x => (u s x) ^ p)) ≤ H) :
    ∃ C, 0 ≤ C ∧
      2 * ∫ s in a..b,
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2) ≤
        M + C * p * H := by
  -- Expected proof outline:
  --   rcases hinteg p hp with ⟨C, hC, hCineq⟩
  --   specialize hCineq a haT b hbT
  --   have hCp_nonneg : 0 ≤ C * p := mul_nonneg hC hp_nonneg
  --   have hrhs := mul_le_mul_of_nonneg_left hmaxInt hCp_nonneg
  --   linarith
  -- This should be a short algebra/linarith proof, not an analytic proof.
  ...

end ShenWork.IntervalDomainExistence.P3MoserDissipationShape
```

This lemma is small enough to prove next because it does not require the good-time lemma, Gronwall, or endpoint regularity.  It confirms the integrated predicate has the right usable form before introducing the more delicate measure/first-crossing infrastructure.

After it builds, the next two lemmas should be:

```lean
integratedMoser_maxY_timeIntegral_le_of_LpPowerBoundedBefore
integratedMoser_nextExponent_timeAverage_bound
```

Then proceed to the good-time and self-Gronwall lemmas.

## Final proof DAG summary

```text
IntegratedMoserDissipationDropBefore p
  + LpPowerBoundedBefore p
  + nonneg/integrability regularity
    -> time-integrated gradient bound for G_p

RelativeMoserInterpolationBefore p
  + LpPowerBoundedBefore p
    -> constant-form pointwise interpolation for Y_{p+rho}

constant interpolation
  + time-integrated G_p bound
  + time-integrability
    -> time-average bound for Y_{p+rho}

time-average bound
  + good-time lemma
    -> exists s < t with controlled Y_{p+rho}(s)

IntegratedMoserDissipationDropBefore (p+rho)
  + controlled Y_{p+rho}(s)
  + self-Gronwall/first-crossing
    -> controlled Y_{p+rho}(t)

near-zero high-exponent regularity
  + later-time first-crossing bound
    -> LpPowerBoundedBefore (p+rho)

one-step theorem
  + routine Stage 1 induction
  + existing all_exponents_of_chain_and_lp_mono
  + existing quantitative endpoint
    -> replacement integrated Moser route for Corollary 2.1 / Proposition 2.5
```

That is the real route.  The first buildable analytic lemma is the gradient-integral extraction lemma above; the first buildable non-analytic layer is the supplied-one-step consumer induction.
