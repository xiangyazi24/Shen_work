# ChatGPT git-drop (cron1)

## Q68 — χ₀<0 coordinatewise H^σ envelope and Fubini swap

### Executive verdict

**Q1.** The fixed-`Estar` restart/continuation route is sound for arbitrary finite data **only after** it is formulated as a genuinely coordinatewise, robust invariant-envelope argument. It does **not** follow from a scalar `H^σ` budget such as `B(Estar) ~ ‖Estar‖_{H^σ}²` alone, and it does **not** follow from the landed `L∞` order-box existence alone. The right statement is:

```lean
hstrict : Tδ (ρ • Estar) ≤ Estar        -- coordinatewise, with ρ > 1
```

or, less robustly,

```lean
hstrict : Tδ Estar ≤ θ • Estar          -- coordinatewise, θ < 1
```

plus a local restricted-contraction/invariance step in the `Estar` envelope box. With that, the time step `δ` may be data-dependent and very small, but positive; finitely many steps cover a fixed finite `[0,T]`. No small-data assumption is inherently needed. What is needed is a **coordinatewise supersolution certificate**, not just a norm estimate.

**Q2.** The Fubini/coefficient swap is valid. The jump at the diagonal `s = τ` is harmless because it is a null time slice, and Bochner integrals are insensitive to a.e. changes. The minimal hypotheses are `AEStronglyMeasurable` plus an integrable majorant. In Mathlib, either use `ContinuousLinearMap.integral_comp_comm` for a continuous linear coefficient functional, or use scalar Fubini via `MeasureTheory.intervalIntegral_intervalIntegral_swap` / `MeasureTheory.integral_integral_swap`. The diagonal convention `S(0)=0` causes no mathematical obstruction.

---

## Q1 — fixed supersolution versus small data

### 1. What the fixed-`Estar` route must actually prove

Let

```lean
BoundUpTo Estar r :=
  ∀ s ∈ Set.Icc (0:ℝ) r, ∀ k,
    |cosineCoeffs (u s) k| ≤ Estar k
```

and suppose `Estar ∈ H^σ`, i.e.

```lean
hEstar : MemHSigma σ Estar
```

with `σ > 1/2` and, for a ratio/inflated-box argument, preferably

```lean
hEstar_pos : ∀ k, 0 < Estar k
```

or else a harmless positive `H^σ` tail has to be added.

The non-circular continuation step should not say:

> Since `BoundUpTo Estar r` holds, estimate the new interval `[r,r+δ]` from the old bound.

That is circular for the chemotaxis flux, because the Duhamel integral over `[r,s]` depends on `u(τ)` for `τ ∈ [r,s]`, and the envelope on that new interval is exactly what is being proved.

The correct local step is instead:

1. Build a local candidate path space on `[r,r+δ]` consisting of paths in the landed `L∞` order box **and** satisfying the coefficient envelope `Estar` (or `ρ • Estar`) on the new interval.
2. Concatenate each candidate with the already-known old solution on `[0,r]`.
3. On this candidate history, the whole interval `[0,r+δ]` satisfies the envelope bound by construction, so all factor envelopes can be built from `Estar` or `ρ • Estar` without circularity.
4. Prove the mild map sends this restricted candidate space into itself using the coordinatewise supersolution inequality.
5. Use the already-landed `L∞` contraction metric restricted to this closed invariant subset. The contraction constant is inherited from the `L∞` order-box contraction.
6. Use uniqueness in the larger `L∞` order box to identify this restricted fixed point with the pre-existing mild solution.

This gives the carried extension field:

```lean
hext : ∀ r, 0 ≤ r → r < T → BoundUpTo Estar r →
  ∃ r' > r, r' ≤ T ∧ BoundUpTo Estar r'
```

without assuming the conclusion on the actual solution.

### 2. Why the `L∞` short-piece estimate alone does not close

The tempting shortcut is to restart at time `r` and estimate the short tail `[r,s]` using only the `L∞` order box:

```text
|u(τ,x)| ≤ M'
```

This is not enough for a coordinatewise `H^σ` envelope. A bounded source has at best a flat coefficient bound

```text
|F_k(τ)| ≲ M'
```

or some weak heat-smoothed tail. For the gradient/chemotaxis Duhamel mode one sees the obstruction already in the model estimate

```text
sqrt(λ_k) ∫_r^s exp(-(s-a)λ_k) C da
  = C * (1 - exp(-(s-r)λ_k)) / sqrt(λ_k).
```

For fixed `k` this tends to zero as `s-r → 0`, but not uniformly relative to an arbitrary `H^σ` coordinate envelope. For high modes `k >> (s-r)^(-1/2)`, this behaves like `C / sqrt(λ_k) ~ C/k`. A typical `H^σ` envelope with `σ > 1/2` may decay faster than `1/k`, so the ratio to `Estar k` can blow up. Thus:

```text
L∞ order-box bound + small δ
```

is not a coordinatewise `H^σ` persistence theorem.

This is the same basic reason that a uniform `L²` or `H^σ` norm bound does not imply a single coordinatewise summable envelope: `sup_τ Σ_k ...` does not imply `Σ_k sup_τ ...`.

### 3. What the elapsed-time factor really buys

You wrote a landed estimate of the form

```text
(1+λ_k)^(σ/2) * |Duhamel_k(δ)|
  ≤ C * sup_s |F_k(s)| * δ^((1-σ)/2) / ((1-σ)/2).
```

This is useful, but with two caveats.

First, the displayed `δ^((1-σ)/2)` is a small factor only when

```text
σ < 1.
```

If `σ ≥ 1`, the exponent is nonpositive and this direct endpoint estimate is not a small-gain base estimate. For the `σ ∈ (1/2, 3/2)` regime, the formal route should start with a seed level `< 1` and then use the already-landed σ-ladder / Duhamel gain step with gain `< 1` to reach `H¹`. Do not use the displayed base estimate directly at `σ ≥ 1`.

Second, a scalar quadratic budget

```text
B(Estar) ~ ‖Estar‖_{H^σ}²
```

is not itself a coordinatewise supersolution. The inequality needed by the bootstrap is not merely

```text
‖D_Q(G_Q(Estar))‖_{H^σ} ≤ C B(Estar),
```

but

```lean
∀ k,
  heatPart_k + |χ₀| * chemPart_k + logPart_k ≤ Estar k.
```

This is strictly stronger. In particular, a bound by a canonical tail like

```text
C * B(Estar) * (1+λ_k)^(-σ/2)
```

would not even be an `H^σ` envelope by itself: multiplying its square by `(1+λ_k)^σ` gives a non-summable constant tail. The actual proof must use the real envelope sequence produced by the Duhamel propagator, convolution algebra, and source envelopes, not only a scalar norm budget.

### 4. Does arbitrary data force small-data?

No small-data assumption is inherent **provided** the following are available:

```lean
-- coordinatewise robust supersolution, with δ allowed to depend on Estar
hstrict : ∀ k, Tδ (ρ • Estar) k ≤ Estar k

-- local restricted-contraction/invariance in the Estar or ρ•Estar box
hext_local : BoundUpTo Estar r → ∃ r' > r, r' ≤ T ∧ BoundUpTo Estar r'
```

For large data, the admissible step size may be tiny, e.g.

```text
δ_max ~ (margin / (|χ₀| * C * B(Estar)))^p,
```

with `p > 0`, but it is still positive if the coordinatewise margin is positive. Then `ceil(T / δ_max)` steps cover `[0,T]`.

Thus the route is **local-in-time invariant box iteration**, not small-data. The data-size dependence moves into the chosen local time step. This is a standard continuation mechanism.

But if the only proven fact is a global scalar `H^σ` or `L²` bound, then the route does not close. One needs the coordinatewise supersolution certificate or an alternative energy/Gronwall theorem that directly constructs a coordinatewise envelope.

### 5. The low mode and margin issue

The heat factor gives no help at `k = 0` because `λ_0 = 0`, and only weak help for small positive modes over short times. Therefore the supersolution has to include the mean/logistic low-mode budget explicitly. The mean-fixed formal route does this by patching the zero mode with a direct mean bound rather than relying on the false mean-conservation row.

For the continuation proof, the robust form

```lean
Tδ (ρ • Estar) ≤ Estar
```

is cleaner than relying on pointwise strictness

```lean
Tδ Estar ≤ θ • Estar.
```

The latter gives a margin `(1-θ) Estar k`, which tends to zero as `k → ∞`. Per-mode continuity cannot exploit that uniformly in `k`. The restricted-contraction/invariant-subset proof avoids needing a uniform-in-`k` continuity radius.

### 6. Lean-formalizable shape for Q1

The clean local theorem should be stated around an invariant restricted space, not around per-mode openness.

Suggested abstract definitions:

```lean
def BoundAt (E : ℕ → ℝ) (s : ℝ) : Prop :=
  ∀ k, |cosineCoeffs (u s) k| ≤ E k

def BoundUpTo (E : ℕ → ℝ) (r : ℝ) : Prop :=
  ∀ s ∈ Set.Icc (0:ℝ) r, BoundAt E s
```

For a restart at `r`, define a candidate subtype of the already-landed `L∞` order-box path space:

```lean
def EnvOrderBox (E : ℕ → ℝ) (r δ : ℝ) : Set Path :=
  { w |
      LinftyOrderBox w ∧
      restart_initial_condition w r ∧
      ∀ s ∈ Set.Icc r (min T (r + δ)),
        ∀ k, |cosineCoeffs (w s) k| ≤ E k }
```

Then prove:

```lean
hclosed_env : IsClosed (EnvOrderBox E r δ)
hcomplete_env : CompleteSpace {w // w ∈ EnvOrderBox E r δ}
hmaps_env : MapsTo (restrictedMildMap r δ) (EnvOrderBox E r δ) (EnvOrderBox E r δ)
hcontract_env : ContractingWith q (restrictedMildMap r δ on the subtype)
```

`hcontract_env` should be inherited from the landed `L∞` contraction, because the metric is still the `L∞` metric and the subtype is smaller. The only new analytic work is `hmaps_env`, the invariant-envelope proof. This is exactly where the supersolution inequality is used.

The conclusion is:

```lean
theorem hext_of_restricted_contraction
    (hgood : BoundUpTo Estar r)
    (hstrict : Tδ (ρ • Estar) ≤ Estar)
    (hrestricted : restricted L∞ contraction + invariant EnvOrderBox)
    (huniq : uniqueness in the larger L∞ order box) :
  ∃ r' > r, r' ≤ T ∧ BoundUpTo Estar r'
```

This is more Lean-tractable than building a new Banach contraction in

```text
X_E = { a : ℕ → ℝ | sup_k |a_k| / E_k < ∞ }.
```

`X_E` is mathematically a Banach space if `E_k > 0`, since it is isometric to `ℓ∞`. But proving the nonlinear chemotaxis map is Lipschitz in that weighted coefficient norm requires new difference estimates for resolver, denominator composition, Wiener products, and the mixed product. The restricted-subset route reuses the landed `L∞` contraction and only adds an invariance lemma.

---

## Q2 — Fubini/coefficient swap with the diagonal convention `S(0)=0`

### 1. Mathematical statement

For fixed `τ` and `k`, set

```text
H(s,x) = S(τ-s)(f(s))(x)
```

for `s < τ`, and set `H(τ,x) = 0` by convention. The desired identity is

```text
cosineCoeffs (fun x => ∫ s in 0..τ, H(s,x) ds) k
  = ∫ s in 0..τ, cosineCoeffs (fun x => H(s,x)) k ds.
```

The diagonal issue is harmless. For fixed `τ`, the bad set is the time slice `{τ}` times the spatial interval. This set has product measure zero. Changing the integrand there does not change either the Bochner integral in time or the product integral used by Fubini.

So the convention `S(0)=0`, even though the left limit as `s → τ-` is `f(τ)`, causes no problem.

### 2. Minimal hypotheses

For fixed `τ`, it is enough to have the following on the rectangle `[0,τ] × [0,1]`:

1. `AEStronglyMeasurable` of the scalar integrand

```lean
fun z : ℝ × ℝ => Real.cos ((k:ℝ) * Real.pi * z.2) * H z.1 z.2
```

with respect to the product of restricted Lebesgue measures.

2. An integrable majorant. A typical bound is

```text
|H(s,x)| ≤ C_f
```

coming from

```text
‖S(τ-s) f(s)‖∞ ≤ ‖f(s)‖∞ ≤ C_f.
```

Since `|cos| ≤ 1` and `[0,τ] × [0,1]` has finite measure, the product integrand is integrable.

3. The coefficient normalization is a finite scalar multiple of a spatial integral, e.g.

```text
cosineCoeffs g k = c_k ∫ x in 0..1, cos(kπx) * g x dx
```

with `c_0 = 1`, `c_k = 2` for `k ≥ 1` depending on your normalization.

No joint continuity at the diagonal is required. A.e. strong measurability plus integrability is enough.

### 3. Clean Mathlib path A: continuous linear coefficient functional

If your time-dependent heat output is represented as a Bochner-integrable path into a Banach function space, this is the cleanest route.

Define a continuous linear map

```lean
cosCoeffCLM (k : ℕ) : C(Icc01, ℝ) →L[ℝ] ℝ
```

or an analogous continuous linear functional on an `L¹`/interval-integrable function space, with

```lean
cosCoeffCLM k g = cosineCoeffs g k.
```

Then use:

```lean
ContinuousLinearMap.integral_comp_comm
```

in the form

```lean
∫ s, cosCoeffCLM k (Φ s) ∂μ
  = cosCoeffCLM k (∫ s, Φ s ∂μ)
```

or its symmetric rewrite. Mathlib also has evaluation support for continuous-map-valued integrals:

```lean
ContinuousMap.integral_apply
```

This path avoids a manual two-variable Fubini proof. The diagonal jump is still harmless because the time path only needs to be Bochner integrable, not continuous everywhere.

### 4. Clean Mathlib path B: scalar Fubini on the rectangle

If the coefficient is already unfolded as an interval integral, use scalar Fubini.

Let

```lean
def K (x s : ℝ) : ℝ :=
  Real.cos ((k:ℝ) * Real.pi * x) * H s x
```

Prove

```lean
hK_int : IntegrableOn K.uncurry (Set.uIoc 0 1 ×ˢ Set.uIoc 0 τ)
```

or with the variables swapped depending on the lemma orientation. Then use:

```lean
MeasureTheory.intervalIntegral_intervalIntegral_swap
```

which has shape:

```lean
∫ x in a..b, ∫ y in c..d, F x y
  = ∫ y in c..d, ∫ x in a..b, F x y
```

from an `IntegrableOn F.uncurry (uIoc a b ×ˢ uIoc c d)` hypothesis.

For one interval and one arbitrary measure, Mathlib also has:

```lean
MeasureTheory.intervalIntegral_integral_swap
```

and the fully product-measure version:

```lean
MeasureTheory.integral_integral_swap
```

with hypothesis

```lean
Integrable (Function.uncurry f) (μ.prod ν)
```

The useful surrounding lemmas are:

```lean
MeasureTheory.integral_prod
MeasureTheory.integral_prod_symm
MeasureTheory.integral_integral
MeasureTheory.integral_integral_swap
MeasureTheory.Integrable.integral_prod_left
MeasureTheory.Integrable.integral_prod_right
MeasureTheory.integrable_prod_iff
```

For integrability from a bounded majorant on a finite rectangle, use:

```lean
MeasureTheory.IntegrableOn.of_bound
```

with an `AEStronglyMeasurable` proof and an eventual norm bound, plus the finite-measure proof for the rectangle. If you need to replace the diagonal convention by a nicer version that uses `S(0)f = f`, use:

```lean
MeasureTheory.IntegrableOn.congr_fun_ae
MeasureTheory.integrableOn_congr_fun_ae
MeasureTheory.integral_congr_ae
```

The diagonal null set is handled by showing the two versions are equal a.e. with respect to the restricted product measure.

### 5. Skeleton of the scalar proof

After unfolding `cosineCoeffs`, prove:

```lean
have hswap :
  (∫ x in (0:ℝ)..1, ∫ s in (0:ℝ)..τ,
      Real.cos ((k:ℝ) * Real.pi * x) * H s x)
    =
  (∫ s in (0:ℝ)..τ, ∫ x in (0:ℝ)..1,
      Real.cos ((k:ℝ) * Real.pi * x) * H s x) := by
  exact MeasureTheory.intervalIntegral_intervalIntegral_swap hK_int
```

Then use interval-integral linearity to move the `x`-dependent cosine through the inner time integral:

```lean
∫ s in 0..τ, Real.cos (...) * H s x
  = Real.cos (...) * ∫ s in 0..τ, H s x
```

This is by `intervalIntegral.integral_const_mul` / scalar multiplication rewrites, assuming the relevant integrability.

On the right side, fold the spatial integral back into `cosineCoeffs (fun x => H s x) k`, using your existing lemma for the cosine coefficient integral formula.

### 6. Final Q2 verdict

The swap holds. The diagonal jump is genuinely harmless. The correct formal target is not continuity on the closed triangle, but:

```lean
AEStronglyMeasurable K (restricted product measure)
IntegrableOn K rectangle
```

plus Fubini. The boundedness of `f`, the `L∞` contraction/order box, and heat-semigroup sup-norm contraction supply the integrable majorant. The convention `S(0)=0` can be erased by `integral_congr_ae` because it changes only a null time slice.

---

## Bottom line

For Q1, the fixed-`Estar` route is a sound arbitrary-data continuation method **if** the proof is built around a coordinatewise robust supersolution and an invariant restricted local fixed-point space. The step size becomes data-dependent; no small data is required. But scalar `H^σ` budgets and `L∞` order-box bounds are insufficient by themselves, and the displayed `δ^((1-σ)/2)` base gain only gives smallness for `σ < 1`.

For Q2, use Bochner/Fubini under `AEStronglyMeasurable + IntegrableOn`; the diagonal discontinuity from the `S(0)=0` convention is null and harmless. The most Lean-friendly proof is either `ContinuousLinearMap.integral_comp_comm` for a coefficient continuous linear map, or `MeasureTheory.intervalIntegral_intervalIntegral_swap` after unfolding the coefficient integral.
