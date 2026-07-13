ANSWER Q4618 b8276c9d

# Executive verdict

Yes: the restriction `α ≥ 1 ∧ γ ≥ 1` is not part of the mathematics of local existence for **strictly positive continuous data**. The correct fixed-point domain is a positive strip

\[
\mathcal K_{c,M,T}
 = \{u\in C([0,T];C([0,1])): c\le u(t,x)\le M\},
\]

with `c > 0` chosen from the datum. On this strip every positive power is Lipschitz, including `u ↦ u^γ` when `0 < γ < 1`.

There are, however, two important corrections to the premise of the question.

1. **`γ < 1` is the genuine floorless obstruction.** The elliptic source is `u^γ`, and its derivative `γu^(γ-1)` is unbounded at zero. A Banach contraction on a ball containing zero therefore cannot use a finite power-Lipschitz constant.

2. **`α < 1` is not a genuine obstruction for the logistic reaction.** The PDE reaction is
   \[
   F(u)=u(a-bu^\alpha)=au-bu^{1+\alpha},
   \]
   not the isolated map `u ↦ u^α`. Since `1+α>1`, `u ↦ u^(1+α)` is Lipschitz on `[0,M]` for every `α>0`. The current Lean hypothesis `α ≥ 1` comes from a nonoptimal proof that splits `u·u^α` and asks separately for `u^α` to be floorlessly Lipschitz. It can be removed even before introducing a positive floor.

The published paper already uses the positive-strip argument. In arXiv:2512.14858v1, Proposition 1.1 assumes

\[
u_0\in C(\overline\Omega),\qquad \inf_{\overline\Omega}u_0>0,
\]

and Section 2.2, Step 3 chooses

\[
0<r<\inf u_0\le \sup u_0<R
\]

and applies the Mean Value Theorem to `ξ^γ`, `ξ^m`, and `ξ^(1+α)` on `[r,R]`. Thus its local-existence proof has no `α≥1` or `γ≥1` assumption.

For the Lean repository, the needed conclusion is:

```lean
theorem intervalDomain_localExistence_paperPositive_allExponents
    (p : CM2Params) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PaperPositiveInitialDatum intervalDomain u₀ →
        ∃ T > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
          IsPaper2ClassicalSolution intervalDomain p T u v ∧
          InitialTrace intervalDomain u₀ u
```

No theorem-1.2 threshold, sign condition on `χ₀`, or guard `a=0 ∨ b>0` is needed for this local theorem. Those assumptions belong to the later a-priori/global argument.

There is one architectural caveat: for `γ<1`, the contraction time necessarily depends on the **datum floor** in this proof. The existing `ChiNegDatumUniformConstructionPPID` interface chooses `T` from only a sup bound `M`, before seeing the datum. That floorless interface cannot simply be reused with the same constants, because the class of PPID data with a fixed upper bound has no common positive floor. A floor-aware or per-datum local factory is required.

---

# 1. Where the current `geOne` assumptions enter

## 1.1 The published proof

The paper writes the elliptic variable as

\[
v[u]=\nu(\mu I-\Delta_N)^{-1}(u^\gamma)
\]

and applies a fixed-point map to `u`. In Section 2.2, Step 3, the candidate set is the positive strip `S_{r,R,T}`. For `u_1,u_2` in this strip it uses

\[
\|u_1^\gamma-u_2^\gamma\|_\infty
 \le \gamma\max_{\xi\in[r,R]}\xi^{\gamma-1}
       \|u_1-u_2\|_\infty,
\]

and similarly

\[
\|u_1^m-u_2^m\|_\infty
 \le m\max_{\xi\in[r,R]}\xi^{m-1}
       \|u_1-u_2\|_\infty,
\]

\[
\|u_1^{1+\alpha}-u_2^{1+\alpha}\|_\infty
 \le (1+\alpha)\max_{\xi\in[r,R]}\xi^{\alpha}
       \|u_1-u_2\|_\infty.
\]

Every constant is finite because `r>0`. This is precisely why the paper permits arbitrary positive `m,α,γ`.

For the branch in this question, `m=1`, so the `u^m` difference has constant exactly one. Only the `u^γ` source needs the lower floor.

## 1.2 The current Lean local core

The restriction is visible in the following chain.

### `IntervalUniformConjugateCore.lean`

```lean
uniformConjugateMildExistenceCore_exists
    (p : CM2Params)
    (hα_ge : 1 ≤ p.α)
    (hγ_ge : 1 ≤ p.γ)
    (M : ℝ) (hM : 0 < M) : ...
```

This is explicitly a **uniform, floor-free** construction on a sup-norm ball. The time is chosen from `(p,M)` before the datum is introduced.

* `hα_ge` is passed to
  `truncatedLogisticLocal_lipschitz_on_bounded`.
* `hγ_ge` is used in the resolver difference constants through
  `p.γ * R ^ (p.γ - 1)`, interpreted as a Lipschitz constant on `[0,R]`.

The latter is valid on an interval containing zero only when `γ≥1`. For `0<γ<1` it is not merely a missing Lean lemma: no finite Lipschitz constant on `[0,R]` exists.

### `IntervalTruncatedLogisticLipschitz.lean`

The current proof estimates

```text
r * (positivePart r)^α - r' * (positivePart r')^α
```

by splitting the product, then asks for `(positivePart ·)^α` to be Lipschitz on `[0,M]`. That introduces `α≥1`.

This can be replaced by the exact identity, valid for every `α>0`,

\[
r(\max\{r,0\})^\alpha=(\max\{r,0\})^{1+\alpha}.
\]

Hence

\[
\operatorname{trLog}(r)
 = ar-b(\max\{r,0\})^{1+\alpha}
\]

is Lipschitz on `[-M,M]` with, for example,

\[
L_{\rm log}(M)=a+b(1+\alpha)M^\alpha.
\]

Thus `hα_ge` is an artifact of the present factorization, not a mathematical requirement.

### Propagation to the theorem-1.2 file

`IntervalChiNegV6DirectClassical.lean` passes both hypotheses to the uniform core, and
`IntervalDomainTheorem12PositiveCriticalUnconditional.lean` exposes them as

```lean
positiveCriticalQuantitativeLocalPPID_geOne
positiveCriticalLocalExistence_geOne
```

There is also a separate `γ≥1` use in

```lean
positiveCriticalOverlapUnique_geOne
```

through a floorless `L²` uniqueness estimate. Therefore, removing `geOne` from the **whole unconditional headline** requires both:

1. the floor-aware local construction discussed below; and
2. a floor-aware overlap-uniqueness argument.

The local-existence theorem itself is independent of the positive-critical global assumptions.

---

# 2. Scalar power estimates on a positive strip

Let

\[
q>0,\qquad 0<c\le r,s\le M.
\]

The Mean Value Theorem gives

\[
|r^q-s^q|\le L_q(c,M)|r-s|,
\]

where one uniform formula is

\[
\boxed{
L_q(c,M)
 =q\max\{c^{q-1},M^{q-1}\}.
}
\]

Equivalently,

\[
L_q(c,M)=
\begin{cases}
q c^{q-1},&0<q\le1,\\
q M^{q-1},&q\ge1.
\end{cases}
\]

In particular, with `c=c₀/2`,

\[
\boxed{
0<\alpha<1
\quad\Longrightarrow\quad
|r^\alpha-s^\alpha|
 \le \alpha(c_0/2)^{\alpha-1}|r-s|.
}
\]

The same formula with `γ` gives the elliptic-source constant. It is finite for each datum and diverges only as the chosen floor tends to zero.

For the actual logistic reaction

\[
F(r)=ar-br^{1+\alpha},
\]

one has on `[0,M]`, for every `α>0`,

\[
\boxed{
|F(r)-F(s)|
 \le \bigl(a+b(1+\alpha)M^\alpha\bigr)|r-s|.
}
\]

Also

\[
|F(r)|\le aM+bM^{1+\alpha}.
\]

If the shifted semigroup `e^{t(\Delta-\mu)}` is used as in the paper, replace `a` in these two constants by `a+\mu`.

A suitable Lean scalar lemma is:

```lean
theorem rpow_lipschitz_on_Icc_pos
    {q c M : ℝ}
    (hq : 0 < q) (hc : 0 < c) (hcM : c ≤ M) :
    ∀ r ∈ Set.Icc c M, ∀ s ∈ Set.Icc c M,
      |r ^ q - s ^ q| ≤
        (q * max (c ^ (q - 1)) (M ^ (q - 1))) * |r - s|
```

The proof should use `Real.hasDerivAt_rpow_const` and the convex-set Mean Value Theorem. A separate corollary can simplify the maximum when `q≤1`.

---

# 3. Exact floor-preserving fixed-point argument

Work on `I=[0,1]` with the Neumann heat semigroup `S(t)=e^{t\Delta_N}`. Define

\[
X_T=C([0,T];C(\bar I)),
\qquad
\|u\|_{X_T}=\sup_{0\le t\le T}\|u(t)\|_\infty.
\]

Let the datum satisfy

\[
u_0(x)\ge c_0>0.
\]

Set

\[
c:=\frac{c_0}{2},
\qquad
U_0:=\|u_0\|_\infty,
\qquad
M:=2U_0.
\]

Since `U₀≥c₀>0`, the datum lies in the strip

\[
\mathcal K_{c,M,T}
 =\{u\in X_T:c\le u(t,x)\le M\}.
\]

This is a closed subset of the Banach space `X_T`, hence complete.

## 3.1 Elliptic resolver bounds

Write

\[
\mathcal R_\mu=(\mu I-\partial_{xx,N})^{-1}.
\]

Fix operator constants `C₀,C₁≥0` such that

\[
\|\mathcal R_\mu f\|_\infty\le C_0\|f\|_\infty,
\qquad
\|\partial_x\mathcal R_\mu f\|_\infty\le C_1\|f\|_\infty.
\]

The first may be taken as `C₀=1/μ`; the exact value of `C₁` is immaterial for the contraction.

For `u∈K`, put

\[
v[u]=\nu\mathcal R_\mu(u^\gamma).
\]

Then

\[
0\le v[u],
\quad
\|v[u]\|_\infty\le B_v:=\nu C_0M^\gamma,
\quad
\|v_x[u]\|_\infty\le B_g:=\nu C_1M^\gamma.
\]

For `u,w∈K`, let

\[
L_\gamma:=L_\gamma(c,M)
 =\gamma\max\{c^{\gamma-1},M^{\gamma-1}\}.
\]

Then

\[
\|v[u]-v[w]\|_\infty
 \le L_v\|u-w\|_{X_T},
\qquad
L_v:=\nu C_0L_\gamma,
\]

and

\[
\|v_x[u]-v_x[w]\|_\infty
 \le L_g\|u-w\|_{X_T},
\qquad
L_g:=\nu C_1L_\gamma.
\]

These are exactly the current resolver estimates with the floorless factor

```text
γ * R^(γ-1)
```

replaced by

```text
γ * max (c^(γ-1)) (R^(γ-1)).
```

## 3.2 Flux bounds

For `m=1`, define

\[
Q(u)=u\,(1+v[u])^{-\beta}v_x[u].
\]

Since `v[u]≥0`,

\[
0<(1+v[u])^{-\beta}\le1
\]

and

\[
|(1+r)^{-\beta}-(1+s)^{-\beta}|
 \le\beta|r-s|
\qquad(r,s\ge0).
\]

Thus

\[
\|Q(u)\|_\infty\le B_Q:=MB_g.
\]

A three-term telescoping identity gives

\[
\boxed{
\|Q(u)-Q(w)\|_\infty
 \le L_Q\|u-w\|_{X_T},
}
\]

with

\[
\boxed{
L_Q=B_g+ML_g+MB_g\beta L_v.
}
\]

This is the same constant pattern already proved in
`IntervalChemFluxLipschitz.lean`.

## 3.3 The mild map

Use the map from the question:

\[
\begin{aligned}
(\Phi u)(t)
={}&S(t)u_0
-\chi_0\int_0^t\partial_xS(t-s)Q(u(s))\,ds\\
&+\int_0^tS(t-s)F(u(s))\,ds,
\end{aligned}
\]

where `F(r)=ar-br^(1+α)`.

Let `C_H` satisfy the interval heat-gradient estimate

\[
\|\partial_xS(\tau)f\|_\infty
 \le C_H\tau^{-1/2}\|f\|_\infty.
\]

Then

\[
\left\|\int_0^t\partial_xS(t-s)g(s)\,ds\right\|_\infty
 \le2C_H\sqrt t\,\|g\|_{X_t}.
\]

Consequently, for every `u∈K`,

\[
\|\Phi u(t)-S(t)u_0\|_\infty
 \le D(T),
\]

where

\[
\boxed{
D(T)=2|\chi_0|C_HB_Q\sqrt T
     +(aM+bM^{1+\alpha})T.
}
\]

## 3.4 Pointwise lower floor

This is the place where the proof must be stated pointwise. A lower bound on the **norm** `‖Φu(t)‖∞` does not imply `Φu(t,x)≥c`.

There are two valid implementations.

### Route A: semigroup order preservation

The Neumann heat semigroup preserves constants and order, so

\[
u_0\ge c_0\quad\Longrightarrow\quad S(t)u_0\ge c_0.
\]

Hence

\[
(\Phi u)(t,x)\ge c_0-D(T).
\]

Choose `T` with `D(T)≤c₀/2`; then `Φu≥c₀/2=c`.

### Route B: strong continuity at the datum

This route also works for the shifted/conjugate semigroup. Put

\[
H(T)=\sup_{0\le t\le T}\|S(t)u_0-u_0\|_\infty.
\]

Strong continuity gives `H(T)→0`. Pointwise,

\[
(\Phi u)(t,x)
 \ge u_0(x)-H(T)-D(T).
\]

Choose

\[
H(T)\le c_0/4,
\qquad
D(T)\le c_0/4.
\]

Then

\[
\Phi u(t,x)\ge c_0/2.
\]

The same estimate gives

\[
\Phi u(t,x)\le U_0+H(T)+D(T)\le U_0+c_0/2\le2U_0=M.
\]

Thus `Φ(K)⊆K`.

This establishes the floor **before** the fixed point exists. It is preferable to invoking a comparison principle for a solution that has not yet been constructed. After the fixed point is obtained, a maximum-principle or ODE comparison can provide a stronger continuation floor.

## 3.5 Contraction

For `u,w∈K`, the semigroup bounds and the Lipschitz estimates above yield

\[
\boxed{
\|\Phi u-\Phi w\|_{X_T}
 \le K(T)\|u-w\|_{X_T},
}
\]

where

\[
\boxed{
K(T)=2|\chi_0|C_HL_Q\sqrt T
     +L_FT,
\qquad
L_F=a+b(1+\alpha)M^\alpha.
}
\]

Since `D(T)→0`, `H(T)→0`, and `K(T)→0`, choose `T>0` satisfying simultaneously

```text
H(T) ≤ c₀/4,
D(T) ≤ c₀/4,
K(T) < 1/2.
```

Banach's theorem gives a unique fixed point in `K`, and therefore

\[
u(t,x)\ge c_0/2>0\qquad(0\le t\le T).
\]

No `α≥1` or `γ≥1` hypothesis has been used.

---

# 4. From the mild fixed point to a classical solution

The fixed point has a uniform positive range `[c,M]`. Therefore:

* `u^γ` is continuous and locally Lipschitz as a function of `u`;
* the elliptic resolver gives `v(t,·)∈C^2` with Neumann boundary condition;
* `u(1+v)^(-β)v_x` has the regularity required by the gradient Duhamel operator;
* `au-bu^(1+α)` is locally Lipschitz for every `α>0`;
* parabolic smoothing yields `C^{1,2}` regularity for every positive time.

The theorem should assert classicality on `(0,T)`, together with the sup-norm initial trace as `t↓0`. Continuous initial data need not satisfy a Neumann compatibility condition at `t=0`; the paper's Definition 1.1 and Proposition 1.1 likewise require classical regularity only at positive times.

The existing direct chain

```text
conjugate mild solution
→ joint time derivative / resolver regularity
→ reduced classical core
→ IsPaper2ClassicalSolution
```

can be reused once the new floor-aware core supplies the mild fixed point and strict positivity. The negative-part/Jensen machinery is not needed to prove positivity for this local construction, because positivity is built into the invariant strip.

---

# 5. What `PaperPositiveInitialDatum` supplies

In the current repository, `Statements.lean` defines

```lean
def PaperPositiveInitialDatum
    (D : BoundedDomainData) (u₀ : D.Point → ℝ) : Prop :=
  D.initialAdmissible u₀ ∧
    ∃ η : ℝ, 0 < η ∧ ∀ x : D.Point, η ≤ u₀ x
```

and exports `PaperPositiveInitialDatum.floor`. Therefore the exact witness required by the construction is already present:

```lean
obtain ⟨η, hη, hfloor⟩ := hu₀.floor
let c := η / 2
```

No compactness proof is needed at the call site.

The repository also defines a weaker `PositiveInitialDatum`, which asks only for positivity on the open interior. That is not sufficient for this argument: `u₀(x)=x(1-x)` is continuous and positive on `(0,1)` but has infimum zero on the closed interval.

Mathematically, if one starts instead from

```text
u₀ continuous on [0,1]
and
∀ x ∈ [0,1], 0 < u₀(x),
```

then compactness gives a minimizer `x₀`, and

\[
c_0:=u_0(x_0)=\min_{[0,1]}u_0>0.
\]

So closed-domain pointwise positivity plus continuity is equivalent to the existence of the needed positive floor. Pointwise positivity only on the open interval is not.

Also note the distinction between:

* a floor for each individual PPID datum; and
* a floor uniform over all PPID data with a common upper bound.

`IntervalDomainPPIDNoUniformFloor.lean` proves that the latter does not exist: positive constant data can tend to zero. This is why the new local time must be allowed to depend on the datum floor.

---

# 6. Lean implementation plan, in dependency order

## Lemma 1 — positive-interval power Lipschitz

**Difficulty: medium scalar analysis.**

```lean
theorem rpow_lipschitz_on_Icc_pos
    {q c M : ℝ}
    (hq : 0 < q) (hc : 0 < c) (hcM : c ≤ M) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ r ∈ Set.Icc c M, ∀ s ∈ Set.Icc c M,
        |r ^ q - s ^ q| ≤ L * |r - s|
```

Use the explicit witness

```lean
q * max (c ^ (q - 1)) (M ^ (q - 1)).
```

Add the `q<1` corollary with witness `q*c^(q-1)`.

## Lemma 2 — all-positive-`α` truncated logistic Lipschitz

**Difficulty: medium; high leverage.**

```lean
theorem truncatedLogisticLocal_lipschitz_allAlpha
    (p : CM2Params) {M : ℝ} (hM : 0 ≤ M) :
    ∀ r r' : ℝ, |r| ≤ M → |r'| ≤ M →
      |truncatedLogisticLocal p r -
        truncatedLogisticLocal p r'|
      ≤ (p.a + p.b * (1 + p.α) * M ^ p.α) * |r-r'|
```

Prove first

```lean
r * (positivePart r) ^ p.α = (positivePart r) ^ (1 + p.α)
```

by splitting `r≤0` and `0≤r`. This lemma removes the `α≥1` argument from the existing floorless core independently of the `γ` work.

## Lemma 3 — floor-aware resolver and flux Lipschitz package

**Difficulty: hard.**

```lean
structure PositiveStripResolverBounds
    (p : CM2Params) (c M : ℝ) where
  gammaLip : ℝ
  gamma_power_diff : ...
  v_bound : ...
  gradV_bound : ...
  v_diff : ...
  gradV_diff : ...
  flux_bound : ...
  flux_diff : ...
```

Reuse the existing resolver-weight/square-sum estimates. The essential edit is replacing every floorless `γ*R^(γ-1)` by `L_γ(c,R)` from Lemma 1. Then instantiate the already proved `chemFlux_div_lipschitz` theorem.

## Lemma 4 — positive-strip invariance of the Duhamel map

**Difficulty: hardest new analytic seam.**

```lean
theorem conjugateDuhamelMap_maps_positiveStrip
    (hu₀_floor : ∀ x, c₀ ≤ u₀ x)
    (hu₀_bound : ∀ x, |u₀ x| ≤ U₀)
    (...) :
    ∃ T > 0,
      ∀ w ∈ PositiveStrip (c₀/2) (2*U₀) T,
        intervalConjugateDuhamelMap p u₀ w ∈
          PositiveStrip (c₀/2) (2*U₀) T
```

Do not derive the lower bound from `‖Φw‖∞`. Prove the pointwise inequality via either:

```text
semigroup monotonicity + preservation of constants
```

or

```text
uniform strong continuity at u₀ + an absolute Duhamel correction bound.
```

`IntervalSemigroupConeAtoms.lean` already supplies semigroup monotonicity; the strong-continuity route may fit the existing initial-trace infrastructure more directly.

## Lemma 5 — contraction and simultaneous small-time choice

**Difficulty: medium after Lemmas 1–4.**

```lean
theorem conjugateDuhamelMap_contraction_on_positiveStrip :
    ∃ T > 0, ∃ κ, 0 ≤ κ ∧ κ < 1 ∧
      ∀ u w ∈ PositiveStrip c M T,
        dist (Φ u) (Φ w) ≤ κ * dist u w
```

The target coefficient is

```text
κ(T) = A * sqrt T + B * T,
```

with `A=2*|χ₀|*C_H*L_Q(c,M)` and
`B=L_F(M)`. Reuse `exists_small_contraction_time` or its target-budget variant, and combine its time with the strip-invariance time by taking a minimum.

## Lemma 6 — local classical capstone

**Difficulty: hard structural integration.**

```lean
theorem intervalDomain_localExistence_paperPositive_allExponents
    (p : CM2Params) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PaperPositiveInitialDatum intervalDomain u₀ →
        ∃ T > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
          IsPaper2ClassicalSolution intervalDomain p T u v ∧
          InitialTrace intervalDomain u₀ u
```

Proof outline:

```lean
intro u₀ hu₀
obtain ⟨c₀, hc₀, hfloor⟩ := hu₀.floor
obtain ⟨U₀, hU₀⟩ := hu₀.admissible.1
let c := c₀ / 2
let M := 2 * max U₀ c₀
obtain ⟨T, hT, hmap, hcontr⟩ :=
  positiveStripCore_exists p hu₀.admissible.2 hfloor hU₀
obtain ⟨u, hu_fixed⟩ := banach_fixedPoint_on_closedStrip ...
let v := mildChemicalConcentration p u
refine ⟨T, hT, u, v, ?_, ?_⟩
```

Then feed the fixed-point equation, strict floor, resolver regularity, and initial trace into the existing mild-to-classical chain.

---

# 7. Required API change: per-datum or floor-indexed time

The current factory has the quantifier order

```text
∀ M>0, ∃ T=T(p,M)>0, ∀ u₀ with ‖u₀‖∞≤M, ...
```

For the positive-strip Banach proof with `0<γ<1`, the resolver Lipschitz constant contains

\[
\gamma c^{\gamma-1},
\]

which diverges as `c↓0`. Since PPID data with a fixed upper bound can have arbitrarily small floors, the same proof cannot produce `T(p,M)` uniformly over that class.

Use one of the following faithful interfaces.

## Per-datum interface

```lean
def PaperPositiveLocalExistence (p : CM2Params) : Prop :=
  ∀ u₀,
    PaperPositiveInitialDatum intervalDomain u₀ →
      ∃ T > 0, ∃ u v, ...
```

This matches Proposition 1.1, whose maximal time is `Tmax(u₀)`.

## Floor-indexed quantitative interface

```lean
def PositiveFloorQuantitativeLocalPPID (p : CM2Params) : Prop :=
  ∀ M c : ℝ, 0 < c → c ≤ M →
    ∃ T > 0,
      ∀ u₀,
        PaperPositiveInitialDatum intervalDomain u₀ →
        (∀ x, c ≤ u₀ x) →
        (∀ x, |u₀ x| ≤ M) →
          ∃ u v, IsPaper2ClassicalSolution ... ∧ InitialTrace ...
```

This is the better interface for restart arguments because it makes all dependencies explicit.

---

# 8. What remains for the full unconditional theorem-1.2 construction

The requested local theorem is solved by the strip argument, but two downstream points must be adjusted to remove `geOne` from the complete global assembly.

## 8.1 Uniform restart length near a finite maximal horizon

The current `positiveCritical_reachablePast_of_bounded_geOne` obtains a restart time from only an upper bound `M`. A floor-aware local factory instead needs a lower bound `c_*` for the restart slices.

For `m=1`, boundedness supplies such a floor on every finite time interval. After expanding the chemotaxis divergence, use upper bounds for `u`, `v`, and `v_x` to obtain a scalar inequality of the form

\[
\partial_tu
 \ge \partial_{xx}u+B(t,x)\partial_xu-C(M)u.
\]

The Neumann minimum principle then gives

\[
\min_xu(t,x)
 \ge \min_xu_0(x)e^{-C(M)t}>0.
\]

Equivalently, one may formalize the ODE subsolution used in Proposition 1.1, Step 5. The crucial point is that, when `m=1`, all remaining powers are `u`, `u^(1+γ)`, and `u^(1+α)`; under `u≤M` they are bounded by constants times `u`, regardless of whether `α` or `γ` is below one.

This yields a common floor `c_*(M,T,u₀)>0` for slices near the putative finite horizon and hence a common restart duration `δ(p,M,c_*)`.

## 8.2 Overlap uniqueness

The current theorem `positiveCriticalOverlapUnique_geOne` also assumes `γ≥1`. Replace its floorless power estimate by a common positive floor on the overlap:

* near time zero, the initial trace and the datum floor give `u_i≥c₀/2` for both solutions;
* away from time zero, positivity and compactness, or the preceding ODE barrier, give a common floor;
* apply the `L_γ(c,M)` estimate and the existing Grönwall argument.

Thus the same positivity mechanism removes `γ≥1` from uniqueness as well.

---

# 9. Direct answers to the numbered questions

## (1) Where exactly do `α≥1` and `γ≥1` enter?

* `γ≥1` enters genuinely in the **floorless** resolver-source difference
  \[
  \|u^\gamma-w^\gamma\|_\infty
   \le \gamma R^{\gamma-1}\|u-w\|_\infty
  \]
  on `[0,R]`. This estimate is false for `0<γ<1`.
* `α≥1` enters the current Lean proof because it estimates `(positivePart u)^α` separately. It is unnecessary for the actual reaction `au-bu^(1+α)`, which is Lipschitz on `[0,M]` for every `α>0`.
* In the complete current theorem file, `γ≥1` also enters overlap uniqueness, not only local construction.

## (2) Does positivity fix the problem?

Yes. Extract `c₀>0`, restrict the Banach map to `u∈[c₀/2,M]`, prove strip invariance by a pointwise small-Duhamel estimate, and use

\[
L_\gamma(c_0/2,M)
 =\gamma\max\{(c_0/2)^{\gamma-1},M^{\gamma-1}\}.
\]

For `0<γ<1`, this is exactly `γ(c₀/2)^(γ-1)`. Choose `T` so the map correction is at most `c₀/2` and the contraction coefficient `A√T+BT` is below one.

The logistic term needs no floor, although using the same strip is harmless.

## (3) Does `PaperPositiveInitialDatum` provide the floor?

Yes, directly. Its repository definition contains

```lean
∃ η > 0, ∀ x, η ≤ u₀ x.
```

If the starting hypothesis were merely continuous closed-domain pointwise positivity, compactness of `[0,1]` would produce the same witness. Interior-only positivity would not.

## (4) What should be formalized?

Formalize the six lemmas in Section 6 and expose the capstone

```lean
intervalDomain_localExistence_paperPositive_allExponents
```

with no `geOne` assumptions. The most difficult new theorem is the pointwise positive-strip invariance of the Duhamel map; the second major seam is packaging its Banach fixed point into the existing mild-to-classical API. For the full unconditional global theorem, additionally add the finite-horizon lower barrier and floor-aware overlap uniqueness.

# Bottom line

The mathematically faithful repair is not a new existence method. It is to formalize the same invariant positive strip used in the paper:

```text
PPID datum supplies c₀>0
→ work on c₀/2 ≤ u ≤ M
→ all positive powers are Lipschitz there
→ Φ preserves the strip for small T
→ Φ is a contraction for small T
→ positive mild fixed point
→ classical solution for every α,γ>0.
```

The only substantive API redesign is that, for `γ<1`, the local time must be allowed to depend on the datum floor (or on a separately supplied uniform floor).