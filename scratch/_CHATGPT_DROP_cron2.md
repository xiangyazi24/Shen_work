# Q83 (cron2): χ₀<0 chemotaxis — global-existence assembly from the order box

## Executive verdict

Yes: **if your local Picard theorem really gives a lifespan depending only on the `L∞`/order-box size of the datum**, then global existence follows from the uniform `L∞` order box alone. The uniform `H¹` estimate is then not needed to prevent finite-time breakdown; it is needed for the stronger global boundedness/regularity theorem and for downstream compactness/asymptotics.

The clean dependency split is:

```text
Global existence as a mild/order-box solution:
  local existence with τ=τ(M)
  + order-box preservation 0≤u≤M
  + finite restart/gluing
  ⇒ solution on every [0,T].

Global bounded H¹/classical solution:
  global mild/order-box solution on every [0,T]
  + uniform H¹ a-priori estimate on finite horizons
  + classicality/smoothing constructor
  ⇒ global bounded classical solution, classical for t>0.
```

So the `H¹` estimate buys the **uniform H¹ clause**, stronger continuation criteria, source regularity, compactness, and classical regularity. It is not logically necessary for bare global mild existence if the local theory is genuinely `L∞`-order-box controlled.

## 1. Continuation mechanism when lifespan depends only on `L∞`

The local theorem you want to use should have this shape:

```lean
local_order_box_existence :
  ∀ M, 0 ≤ M → ∃ τ > 0,
    ∀ w, DataSpace w → (∀ x, 0 ≤ w x) → (∀ x, w x ≤ M) →
      ∃ u, MildSolutionOn [0, τ] w u ∧
           (∀ t ∈ [0,τ], ∀ x, 0 ≤ u t x ∧ u t x ≤ M)
```

or, if the logistic upper box is `Mbar=max(Mdata,K)`, use `Mbar` everywhere.

Then global existence follows by restart:

1. Let `Mbar` be the invariant order-box bound from the maximum principle.
2. Choose `τ=τ(Mbar)>0` from local existence.
3. Build the solution on `[0,τ]` from `u₀`.
4. At time `τ`, the slice `u(τ)` is again admissible and satisfies `0≤u(τ)≤Mbar`.
5. Restart from `u(τ)` for another interval of length `τ`.
6. Repeat finitely many times to cover any prescribed `[0,T]`.

The `H¹` bound is not used in this restart argument unless the local theorem's `DataSpace` requires `H¹` and the local lifespan actually depends on the `H¹` norm. You stated that the lifespan depends on the `L∞`/order-box bound; under that hypothesis, the order box is enough.

### Critical audit point

Make sure the local theorem really has a lifespan lower bound controlled only by `Mbar`. Many Sobolev Picard theorems are stated as

```text
τ = τ(||w||_{H^σ})
```

or

```text
τ = τ(||w||_{X})
```

for the phase space `X`. If your theorem still depends on an `H^σ` or `H¹` norm, then the `L∞` box alone is not enough; you need the uniform norm bound in that phase space. But if your current Picard setup has an order-box-based contraction time, then yes, global mild existence is an immediate restart consequence of the order box.

## 2. What the H¹ bound buys beyond global existence

The `H¹` estimate is still valuable. It gives:

```text
sup_t ||u(t)||_{H¹} ≤ C,
```

which implies or supports:

- a norm-based continuation criterion if you later switch the phase space to `H¹`;
- uniform control of the gradient / spectral energy;
- uniform source bounds for the flux and logistic terms;
- compactness of trajectories in lower norms after smoothing;
- input to asymptotic/omega-limit arguments;
- a headline theorem saying the global solution is uniformly bounded in `H¹`;
- classicality for `t>0` via smoothing or your `IsPaper2ClassicalSolution` constructor.

So the right formal order is:

```text
first global mild existence by L∞ restart;
then apply the already-built H¹ a-priori theorem on each finite horizon;
then attach classicality / stronger regularity.
```

## 3. Restart/gluing subtleties

### 3.1 The restart datum must be in the local data space

At every restart time `t₀`, you need:

```text
DataSpace (u t₀),
0 ≤ u t₀,
u t₀ ≤ Mbar.
```

The order inequalities come from the maximum principle. The `DataSpace` membership usually comes from continuity of the mild solution in the phase space. If `DataSpace` is `C([0,1])`, `L∞`, `H^σ`, or the cosine phase space used by Picard, ensure the local solution is continuous into that space up to the endpoint.

If the local classical theorem requires Neumann compatibility at the initial time, do not use that theorem for restart. Use the mild local theorem for restart; recover classicality later for positive times. Time slices of a classical solution may satisfy compatibility, but formalizing that is avoidable.

### 3.2 The local equation must be autonomous or time-shift invariant

The restarted local solution from `w=u(t₀)` is naturally written in shifted time:

```text
z(s),  s∈[0,τ],  z(0)=u(t₀).
```

The global piece is

```text
u(t) = z(t-t₀),  t∈[t₀,t₀+τ].
```

You need a lemma that the PDE/mild formulation is invariant under this time shift.

### 3.3 Gluing mild solutions

A good concatenation lemma is:

```lean
mild_concat :
  MildSolutionOn [0,a] u0 u₁ →
  MildSolutionOn [0,b] (u₁ a) u₂ →
  u₂ 0 = u₁ a →
  MildSolutionOn [0,a+b] u0 (glue u₁ (shift_by a u₂))
```

For a Duhamel/mild formulation, the proof for `t>a` uses the semigroup identity:

```text
u₁(a) = S(a)u₀ + ∫₀ᵃ S(a-r)N(u₁(r)) dr,

u(t) = S(t-a)u₁(a) + ∫ₐᵗ S(t-s)N(u(s)) ds
     = S(t)u₀ + ∫₀ᵃ S(t-r)N(u(r)) dr
              + ∫ₐᵗ S(t-s)N(u(s)) ds.
```

The seam value agrees because `u₂(0)=u₁(a)`. Continuity at the seam is then automatic.

You do not need uniqueness for existence-by-gluing, but uniqueness is useful to prove that different restart partitions give the same solution and to state a canonical global solution.

### 3.4 Classicality at the glue times

If you glue only as a mild solution, do not try to prove time differentiability piecewise at the artificial seam times. First prove the concatenated object is a mild solution on the whole interval. Then use the smoothing/classicality theorem for mild solutions on the whole interval. That avoids seam-regularity headaches.

## 4. Avoiding maximal-time machinery: finite-horizon induction

For Lean, the cleanest first theorem is probably finite-horizon existence:

```lean
global_mild_on_finite_horizon :
  ∀ T > 0, ∃ u,
    MildSolutionOn [0,T] u₀ u ∧
    (∀ t ∈ [0,T], ∀ x, 0 ≤ u t x ∧ u t x ≤ Mbar)
```

Proof outline:

1. Choose `τ>0` from `local_order_box_existence Mbar`.
2. Pick `N : ℕ` such that `T ≤ N*τ`; for example `N = Nat.ceil (T/τ) + 1` in whatever real/NNReal formulation is easiest.
3. Prove by induction on `n`:

   ```lean
   ∃ u, MildSolutionOn [0,n*τ] u₀ u ∧ order_box_on [0,n*τ] u
   ```

4. The successor step restarts from the endpoint and glues using `mild_concat`.
5. Restrict the solution on `[0,N*τ]` to `[0,T]`.

This avoids defining a maximal solution, proving a blow-up alternative, or reasoning with `limsup` at a finite endpoint.

Later, if you need an actual global function `u : ℝ≥0 → X`, obtain it from the compatible finite-horizon family using uniqueness, or define it by choosing a finite-horizon solution on `[0,n]` and using consistency. But for many formal paper statements, `∀ T, ∃ solution on [0,T]` is already the easiest global existence formulation.

## 5. Minimal theorem to formalize first

The first theorem should separate existence from the H¹ estimate.

### Theorem 1: global order-box mild solution on finite horizons

```lean
 theorem exists_mild_solution_on_every_finite_horizon
   (u₀_nonneg : ∀ x, 0 ≤ u₀ x)
   (u₀_box : ∀ x, u₀ x ≤ Mbar)
   ... :
   ∀ T > 0, ∃ u,
     MildSolutionOn (Set.Icc 0 T) u₀ u ∧
     (∀ t ∈ Set.Icc 0 T, ∀ x, 0 ≤ u t x ∧ u t x ≤ Mbar)
```

This theorem needs only:

```text
local order-box existence with τ(Mbar)>0,
maximum-principle/order-box preservation,
restart/gluing.
```

It does **not** need the uniform H¹ estimate.

### Theorem 2: global finite-horizon H¹ bound

Apply the already-built a-priori estimate to the solution from Theorem 1:

```lean
 theorem exists_mild_solution_on_every_finite_horizon_with_H1_bound
   ... :
   ∀ T > 0, ∃ u,
     MildSolutionOn (Set.Icc 0 T) u₀ u ∧
     order_box_on [0,T] u ∧
     (∀ t ∈ Set.Icc 0 T, ||u t||_{H¹} ≤ C)
```

If the initial datum is not in `H¹`, replace `[0,T]` by `(0,T]` or `[ε,T]` in the H¹ clause:

```text
∀ ε>0, ∀ t∈[ε,T], ||u(t)||_{H¹}≤C(ε).
```

If your current uniform bound is genuinely `sup_{t>0} ||u(t)||_{H¹}≤C` independent of `ε`, then use `(0,T]`. But be careful: such a bound including arbitrarily small positive times usually requires either `u₀∈H¹` or a very strong smoothing estimate with possible singularity already controlled.

### Theorem 3: global bounded classical solution

```lean
 theorem global_bounded_classical_solution
   ... :
   ∀ T > 0, ∃ u v,
     IsPaper2ClassicalSolutionOn (Set.Icc 0 T) u v ∧
     order_box_on [0,T] u ∧
     (∀ t ∈ ..., ||u t||_{H¹} ≤ C) ∧
     resolver_relation u v
```

or, more naturally for classicality,

```text
classical on (0,T] or [ε,T].
```

This theorem uses the H¹/source regularity/classicality constructor.

## 6. Which statement needs H¹?

Bare finite-horizon existence:

```text
∀T, ∃ mild solution on [0,T]
```

needs only `L∞` restart, assuming local lifespan is controlled by `L∞`.

Order-box bounded global mild existence:

```text
∀T, ∃ mild solution on [0,T] with 0≤u≤Mbar
```

also needs only `L∞` restart plus the maximum principle.

Uniform-H¹ global boundedness:

```text
∀T, ∃ solution on [0,T] with ||u(t)||H¹≤C
```

needs the H¹ a-priori theorem, but not for continuation.

Global classical solution:

```text
classical for t>0 with resolver/source regularity
```

needs smoothing/classicality inputs, typically supported by H¹ or stronger source estimates.

## 7. Final recommendation

Formalize in this order:

1. **`mild_concat` / restart lemma.** This is the main infrastructure.
2. **Finite-horizon global mild existence by induction on the number of steps.** Use only the order-box local lifespan.
3. **Attach the uniform order box on the whole finite horizon.** This should be preserved by each local piece and by gluing.
4. **Apply the uniform H¹ a-priori estimate on the finite-horizon solution.** This gives the global boundedness theorem.
5. **Feed the bounded global mild solution into `IsPaper2ClassicalSolution` / smoothing.** This gives the paper-style global bounded classical solution.

This route avoids maximal-time machinery and uses the `H¹` estimate exactly where it belongs: not to force existence, but to strengthen the global solution to a uniformly bounded `H¹`/classical one.
