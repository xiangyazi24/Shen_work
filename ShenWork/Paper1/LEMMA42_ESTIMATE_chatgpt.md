═══ BRIDGE cron | ee1f0885 | 8655 chars 1458 words 332 lines | 827s | prov=network | OK ═══
═══ BRIDGE cron | ee1f0885 | 8655 chars 1458 words 332 lines | 827s | prov=network | OK ═══
## First: align the operator

The paper’s Lemma 4.2 is for the auxiliary operator

```text
A(W;u)
= Wₓₓ + c Wₓ
  - χ m W^{m-1} Vₓ Wₓ
  + W (1 - χ W^{m-1}V - (W^α - χ W^{m+γ-1}))
```

where `V = Ψ(x; u^γ,1,1)` is frozen from the input `u`. This is exactly the shape of the repo’s `paperWaveOperator`, not the literal `frozenWaveOperator` after expanding `Vₓₓ = V - u^γ`; the repo’s `frozenWaveOperator` keeps `-χ ∂x(W^m V_u') + W(1-W^α)`, while `paperWaveOperator` has the `W^{m+γ-1}` term. fileciteturn119file0L3-L13 The paper defines the same `A(W;u)` before Lemma 4.1. citeturn535451view3

This matters: if you expand the literal frozen divergence operator, you get a term `χ W^m u^γ`; the paper’s `A` has `χ W^{m+γ}`. These agree only at the fixed point `W = u`. So the faithful Lemma 4.2 target in Lean should be a theorem about `paperWaveOperator`, or about a paper-style auxiliary map whose off-diagonal equation is (4.12). If your current lower-barrier preservation theorem asks for

```lean
0 ≤ frozenWaveOperator p c u φ x
```

for arbitrary frozen `u`, Lemma 4.2 does **not** directly prove it.

---

## (1) Exact χ≤0 estimate

Let

```text
U(x) = U_{κ,κ~,D}(x) = e^{-κx} - D e^{-κ~x},
δ = cκ~ - κ~² - 1,
c = κ + κ⁻¹.
```

The repo has the same raw lower barrier definition. fileciteturn116file0L3-L4 The scalar linear part is

```text
U'' + cU' + U = D δ e^{-κ~x}.
```

The repo already proves this algebraically as

```lean
lowerBarrierRaw_linear_part_eq_speed_denominator
```

and proves `δ > 0` under `0<κ<1`, `κ<κ~≤1`, `c=κ+κ⁻¹`. fileciteturn116file0L113-L147

For `χ≤0`, write `|χ| = -χ`. The paper rewrites

```text
A(W;u)
= W'' + cW'
  + |χ| m W^{m-1} Vx Wx
  + W(1 + |χ| W^{m-1}V - (W^α + |χ|W^{m+γ-1})).
```

For `W = U`, on the region `x ≥ x^-` where `U ≥ 0`, the paper estimates

```text
A(U;u)
≥ Dδ e^{-κ~x}
  + |χ|m U^{m-1}(κ~D e^{-κ~x} - κe^{-κx}) Vx
  - U(U^α + |χ|U^{m+γ-1}).
```

The good term is

```text
+ |χ| U^m V ≥ 0
```

because `V ≥ 0`; the paper simply drops it. The bad terms are

```text
-U^{α+1},
-|χ|U^{m+γ},
and the first-derivative chemotaxis term
 |χ|mU^{m-1}U'Vx,
```

because `Vx ≤ 0` but `U'` changes sign: it is positive on the rising part `[x^-,x^+]` and nonpositive after `x^+`. The proof bounds the chemotaxis derivative term from below by its worst absolute value using the `Vx` bounds. citeturn474877view0

The paper’s key lower bound is

```text
A(U_{κ,κ~,D};u)(x)
≥ ( D(cκ~ - κ~² - 1) - 1 - |χ| K_{M,κ,κ~,m,γ} ) e^{-κ~x}
```

for `x > x^-`. Therefore,

```text
D ≥ D_{M,κ,κ~,χ,m,γ}
  := (1 + |χ| K_{M,κ,κ~,m,γ}) / (cκ~ - κ~² - 1)
```

implies

```text
A(U_{κ,κ~,D};u)(x) ≥ 0   for x ≥ x^-.
```

This is precisely the last step of Lemma 4.2’s χ≤0 proof. citeturn396707view0

The important point for `m=1`: nothing in this estimate requires smallness of a plateau value or order separation between `C` and `C^m`. The parameter `m` only enters the constant `K`; at `m=1`, `K` is still finite, and the required `D` just grows linearly with `|χ|K`. Thus the scalar margin

```text
Dδ e^{-κ~x}
```

absorbs the chemotaxis loss by choosing `D` large enough. That is the paper’s mechanism.

---

## (2) Precise hypotheses and constants

Lemma 4.2 assumes:

```text
0 < κ < 1,
0 < κ < κ~ ≤ min{(1+α)κ, mκ + 1/2, 1},
M ≥ 1,
u ∈ E_{κ,M,T}.
```

For the raw lower solution, it assumes

```text
D > D_{M,κ,κ~,χ,m,γ}.
```

The paper defines

```text
D_{M,κ,κ~,χ,m,γ}
= (1 + |χ| K_{M,κ,κ~,m,γ}) / (cκ~ - κ~² - 1),
c = κ + κ⁻¹.
```

citeturn474877view0

The constant `K_{M,κ,κ~,m,γ}` is the coefficient that packages the `V` and `Vx` bounds from (4.7)–(4.8). In readable form:

```text
K_{M,κ,κ~,m,γ} =
  (m(κ~+κ)+1)(M^γ + 3/4),
    if γκ = 1;

  (m(κ~+κ)+1) / (1 - γ²κ²),
    if γκ < 1;

  (m(κ~+κ)+1) · (M^γ(κ²γ² - 1) + γκ) / (κ²γ² - 1),
    if γκ > 1.
```

The paper first proves the corresponding pointwise bounds for `V` and `-|Vx|`, then inserts them into the `A(U;u)` estimate. citeturn474877view0

For the negative-sensitivity theorem, the speed condition is stated as

```text
c > c*_{χ,m,γ}
:= max { m + 1/m,
         sqrt(mγ|χ| + γ²|χ| + γ²)
           + 1 / sqrt(mγ|χ| + γ²|χ| + γ²) }.
```

The paper then sets

```text
κ = (c - sqrt(c² - 4))/2,
```

so that `c = κ + κ⁻¹`, and chooses `κ₁, κ~` with

```text
κ < κ₁ < min{(α+1)κ, mκ + 1/2, 1},
κ₁ < κ~ ≤ min{(α+1)κ, mκ + 1/2, 1}.
```

citeturn382834view0 citeturn396707view0

For Lean, the core theorem should be shaped like this:

```lean
theorem paperA_lowerBarrierRaw_nonneg
    (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hκtilde : κ < κtilde)
    (hκtilde_le :
      κtilde ≤ min ((1 + p.α) * κ) (min (p.m * κ + 1/2) 1))
    (hc : c = κ + κ⁻¹)
    (hM : 1 ≤ M)
    (hD : D ≥ Dcrit M κ κtilde p.χ p.m p.γ)
    {u : ℝ → ℝ}
    (hu : InPaperE κ M T u)
    {x : ℝ} (hx : lowerBarrierXMinus κ κtilde D ≤ x) :
    0 ≤ paperWaveOperator p c u (lowerBarrierRaw κ κtilde D) x
```

with

```lean
Dcrit = (1 + |χ| * Kcrit) / (c * κtilde - κtilde^2 - 1).
```

If your target is instead `frozenWaveOperator`, insert a separate bridge theorem and be careful: off the fixed point, the sign is not automatic.

---

## (3) Positivity and the exact lower barrier

The raw function

```text
U_{κ,κ~,D}(x) = e^{-κx} - D e^{-κ~x}
```

is negative for

```text
x < x^- = log D / (κ~ - κ).
```

The paper does **not** use `max(0,U)` as the global lower trap. It defines two points:

```text
x^- = log D / (κ~ - κ),
x^+ = log(κ~D/κ) / (κ~ - κ),
```

where `x^-` is the zero and `x^+` is the maximum point of the raw two-exponential function. Then it defines the global lower function

```text
U^-_{κ,κ~,D}(x) =
  U_{κ,κ~,D}(x^+)   if x ≤ x^+,
  U_{κ,κ~,D}(x)     if x > x^+.
```

citeturn474877view0

This is exactly the repo’s `lowerBarrierPlateau`: constant on the left of `x^+`, raw on the right. fileciteturn117file0L211-L227 The repo also proves the derivative of the raw function is zero at `x^+`, which is why this plateau avoids the bad kink that `max(0,U)` would have at `x^-`. fileciteturn117file0L83-L120

The trap in the theorem is then

```text
E_{κ,M}
= { u ∈ C_b^unif(R) | U^-_{κ,κ~,D}(x) ≤ u(x) ≤ U^+_{κ,M}(x) for all x },
```

and the monotone subset `E'_{κ,M}` adds nonincreasingness. The paper uses Lemmas 4.1 and 4.2 to obtain

```text
U^-_{κ,κ~,D}(x)
≤ u(t,x; U^+_{κ,1},u)
≤ U^+_{κ,1}(x)
```

for the parabolic map whose long-time limit becomes the Schauder map. citeturn396707view0

So, for Lean:

```text
Do not use max(0, raw).
Use lowerBarrierPlateau.
```

But also do not pretend the plateau is a classical `C²` function everywhere. It is `C¹` at `x^+`, but the second derivative generally jumps. The comparison proof should be formalized as a **patched subsolution**:

1. On `x > x^+`, use the raw-tail theorem from Lemma 4.2(1).
2. On `x < x^+`, use Lemma 4.2(2), the constant-subsolution theorem.
3. At `x = x^+`, use a viscosity/weak comparison lemma, or split the parabolic comparison on the two regions and use continuity/C¹ matching at the interface.

Lemma 4.2(2) states that a constant `d` is a subsolution if

```text
0 < d ≤ min {
  1/(1+|χ|),
  (κ/(κ~D))^{κ/(κ~-κ)} (1 - κ/κ~)
}.
```

The second quantity is exactly the plateau height `U(x^+)`. citeturn474877view0 Therefore, to use the actual plateau height as the left constant, you also need the side condition

```text
U(x^+) ≤ 1/(1+|χ|),
```

or equivalently choose `D` large enough so that this holds. The paper’s proof says “by Lemmas 4.1 and 4.2” when establishing the lower bound; for a Lean proof I would make this explicit by defining

```lean
Dtotal :=
  max Dcrit Dplateau
```

where `Dplateau` guarantees

```lean
lowerBarrierRaw κ κtilde D (lowerBarrierXPlus κ κtilde D)
  ≤ 1 / (1 + |χ|).
```

Then prove:

```lean
theorem lowerBarrierPlateau_paper_subsolution
    (hD : Dtotal ≤ D) :
    PaperPatchedSubsolution p c κ κtilde D M u
      (lowerBarrierPlateau κ κtilde D)
```

This avoids relying on hidden “D large enough” reasoning and is much more robust for Lean.

---

## The formalization warning

The faithful path is:

```lean
paperWaveOperator lowerBarrierRaw ≥ 0     -- Lemma 4.2 tail
paperWaveOperator constant ≥ 0            -- Lemma 4.2 plateau
patched lowerBarrierPlateau comparison    -- weak/viscosity or split max principle
```

not:

```lean
frozenWaveOperator lowerBarrierPlateau ≥ 0
```

as a pointwise classical theorem.

At the final fixed point the paper operator and the true stationary operator coincide, because the frozen input and the output are the same. But for **preserving the lower pin during the Schauder/parabolic map**, the off-diagonal operator must match the paper’s `A(W;u)` / equation (4.12).
