═══ BRIDGE cron2 | a59e7356 | 10022 chars 1365 words 283 lines | 349s | prov=network | OK ═══
═══ BRIDGE cron2 | a59e7356 | 10022 chars 1365 words 283 lines | 349s | prov=network | OK ═══
## Verdict

For this exact lemma, the genuine hard brick is:

```lean
intervalNeumannFullKernel_secondDeriv_weighted_mass
```

i.e.

```lean
∫₀¹ |∂ₓₓ K_N(t,x,y)| * |x-y|^θ dy
  ≤ Cθ * t ^ (-1 + θ / 2)
```

Everything after that is routine: subtracting `h x`, applying the Hölder modulus, and integrating the time singularity. At commit `1b85924`, the repository already follows the right route: **method-of-images Gaussian for the kernel-moment estimate**, with spectral/cosine used only where it is simpler for semigroup identities. The file header says the needed cancellation estimate is exactly `‖∂ₓₓS(σ)h‖∞ ≤ Cθ σ^{-1+θ/2} [h]_{C^θ}`, and identifies the mean-zero cancellation as the key way to avoid the non-integrable naive `σ^{-1}`/`σ^{-3/2}` endpoint. fileciteturn110file0L6-L23

So the recommendation is:

```text
Use route (B), the method-of-images Gaussian route, for the σ^{(θ-2)/2} bound.
Use cosine/spectral only for semigroup composition, Neumann algebra, and kernel↔series identities.
```

---

## (1) Mathlib availability

### (a) Gaussian heat kernel and spatial derivative bounds

Mathlib has strong Gaussian integral infrastructure, but it does **not** hand you the full heat-kernel PDE package as a ready “heat semigroup with derivative estimates” API. In this repository, the whole-line heat kernel is defined manually as

```lean
def heatKernel (t : ℝ) (x : ℝ) : ℝ :=
  1 / Real.sqrt (4 * Real.pi * t) * Real.exp (-x ^ 2 / (4 * t))
```

and the semigroup is likewise defined manually by convolution. The file imports Mathlib’s Gaussian integral and exponential-derivative material, then proves the kernel mass and derivative facts itself. fileciteturn124file0L18-L36

The second derivative formula and the pointwise Hessian bound are also custom repo lemmas, not Mathlib off-the-shelf lemmas:

```lean
heatKernel_secondDeriv_hasDerivAt
deriv_deriv_heatKernel
abs_secondDeriv_heatKernel_le
```

The bound in the repo has the right half-rate Gaussian shape:

```lean
|∂ₓₓ heatKernel t x|
  ≤ heatHessPointwiseBound t * exp (-x^2 / (4 * (2*t)))
```

where `heatHessPointwiseBound t` scales like `t^{-3/2}`. fileciteturn115file0L53-L98

So: **Mathlib gives the calculus/integrability tools; the actual heat-kernel derivative estimates are repo-level lemmas.**

### (b) Gaussian moment integrals

Mathlib does have the key background lemmas. The official docs for `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral` list:

```lean
integrable_rpow_mul_exp_neg_mul_sq
integrable_exp_neg_mul_sq
integral_gaussian
```

and related Gaussian integral results. citeturn311904view0

But the exact scaled absolute moment needed here,

```lean
∫ w, |w|^θ * exp (-w^2 / c)
  = c ^ ((θ + 1) / 2) * gaussianAbsMoment θ
```

is not something I would expect to be a one-line Mathlib theorem. The repo defines

```lean
gaussianAbsMoment θ := ∫ u, |u|^θ * exp (-u^2)
```

then proves the scaling theorem

```lean
gaussian_abs_moment_scaling
```

using `Measure.integral_comp_mul_right`, `Real.sqrt`, and rpow algebra. fileciteturn110file0L88-L100 fileciteturn111file0L4-L47

So: **Mathlib has the integrability and Gaussian integral base; the exact `|z|^θ` scaled-moment lemma is a repo lemma.**

### (c) Bounded interval Neumann heat semigroup

Mathlib does not appear to provide a ready 1-D bounded-interval Neumann heat semigroup with kernel, boundary condition, and derivative bounds. The repo builds it from scratch as the full periodized image kernel:

```lean
K_full t x y =
  ∑' k : ℤ, heatKernel t (x - y + 2*k)
          + heatKernel t (x + y + 2*k)
```

and defines

```lean
intervalFullSemigroupOperator t f x =
  ∫ y, intervalNeumannFullKernel t x y * f y ∂ intervalMeasure 1
```

fileciteturn123file0L3-L19 fileciteturn123file0L70-L82

The repo also proves the period-2 Poisson summation identity connecting the image kernel to the cosine spectral kernel, from Mathlib’s `Complex.tsum_exp_neg_quadratic`. fileciteturn123file0L23-L33 fileciteturn123file0L95-L116

So: **for this project, the interval Neumann semigroup is repo infrastructure, not a Mathlib API.**

---

## (2) Difficulty ranking

### 1. Hardest: (iii) the σ-power weighted kernel mass

The load-bearing brick is:

```lean
theorem intervalNeumannFullKernel_secondDeriv_weighted_mass
    {t θ : ℝ} (ht : 0 < t)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) {x : ℝ}
    (hx : x ∈ Set.Icc (0:ℝ) 1) :
    ∫ y in (0:ℝ)..1,
      |∂ₓₓK_full(t,x,y)| * |x-y|^θ
    ≤ weightedHeatHessConst θ * t ^ (-1 + θ / 2)
```

The theorem’s docstring explains the proof: dominate the interval kernel by the reflected lattice series, transfer `|x-y|^θ` to the image arguments, fold the image sum over period cells into a whole-line weighted Gaussian integral, and apply the whole-line bound. fileciteturn112file0L115-L134

This is hard because it bundles all the real analysis:

```text
pointwise Gaussian Hessian bound
lattice/image summability
Tonelli / integral_tsum
period-cell tiling
Gaussian absolute-moment scaling
rpow algebra for t^{-1+θ/2}
```

The repo proof explicitly uses the image/lattice structure, summability of weighted shifted Hessians, interval integrability, `integral_tsum_of_summable_integral_norm`, and a cell-tiling identity before applying the whole-line weighted bound. fileciteturn112file0L42-L58 fileciteturn120file0L70-L134

### 2. Medium-hard: second derivative-under-integral, if not already available

For this file, the mean-zero proof relies on an already-committed second-order derivative-under-integral lemma:

```lean
intervalFullSemigroupOperator_hasDerivAt_deriv_fst
```

The mean-zero theorem uses it to identify the second derivative of `S(t)(const 1)` with `∫ ∂ₓₓK`. fileciteturn110file0L49-L84

If that DUI theorem were not already present, it would be comparable in difficulty to the weighted-mass lemma. But for the present brick, it is a dependency, not the hard new target.

### 3. Routine after DUI: (i) constant preservation / mean-zero

The constant preservation theorem is:

```lean
intervalFullSemigroupOperator_const
```

It follows from kernel mass one:

```lean
∫ K_N(t,x,y) dy = 1.
```

Then `intervalNeumannFullKernel_secondDeriv_integral_zero` follows by differentiating `S(t)(1)=1` twice. fileciteturn110file0L37-L84

Conceptually, this is easy. In Lean, it is only medium if the second-order DUI is unavailable.

### 4. Routine: (ii) cancellation rewrite

Once you have

```lean
∫ K₂ y dy = 0
```

the cancellation identity is just:

```lean
∫ K₂ y * h y dy
= ∫ K₂ y * (h y - h x) dy
```

The final theorem `neumannHeatSecondDeriv_Ctheta_to_Linfty` performs exactly this step using `hmean0` and the integral of `K y * h x`. fileciteturn121file0L39-L51

### 5. Easy: (iv) Duhamel time-integral convergence

After the kernel estimate, the time singularity is:

```text
∫₀ᵗ σ^{-1+θ/2} dσ = (2/θ) t^{θ/2}
```

which is finite exactly because `θ > 0`. The route note states this explicitly. fileciteturn117file0L53-L59

In Lean this is a calculus/integrability lemma for `rpow` on `Ioc/Ioo`; it is not the analytic bottleneck.

---

## (3) Route recommendation: cosine series or method of images?

Use **method of images** for this lemma.

The target estimate is a kernel moment estimate:

```text
∫ |∂ₓₓK_N(σ,x,y)| |x-y|^θ dy
  ≤ Cθ σ^{-1+θ/2}.
```

The image-kernel proof reduces it to the whole-line Gaussian Hessian moment plus a lattice tiling argument. That is exactly what the current file does: it defines the full Neumann image kernel, proves Gaussian/Hessian bounds, proves the weighted whole-line mass, and then proves the interval weighted mass. fileciteturn123file0L70-L82 fileciteturn111file0L59-L70 fileciteturn112file0L115-L134

The cosine-series route is tempting because cancellation is automatic: the `n=0` mode vanishes under `∂ₓₓ`, so `∫ ∂ₓₓK = 0` is algebraically clear. But the actual Hölder bound is not a simple coefficient-decay exercise. A naive `C^θ` coefficient bound plus

```text
Σ n² e^{-n²σ} |a_n|
```

does not transparently give the sharp `σ^{-1+θ/2}` Schauder exponent; you end up needing a Fourier multiplier/Hölder-space theorem or dyadic Littlewood–Paley style estimates. That is more infrastructure than the Gaussian moment argument.

The shortest path in Lean is the hybrid already present:

```text
B / images:
  prove C^θ → L∞ Hessian estimate by kernel cancellation and weighted Gaussian mass.

A / spectral:
  use cosine series where semigroup composition, commutation, and Neumann spectral identities are easier.
```

`ChemMildC1eta.lean` confirms this design: it says the kernel-side bricks are mean-zero, weighted mass, and `C^θ→L∞`; then it packages the stronger `C^θ→C^η` estimate via a Route-B semigroup split/commutation, avoiding a third-derivative kernel. fileciteturn73file0L21-L38 fileciteturn73file0L53-L63

---

## The lemma stack I would keep

Use the current theorem names and make the target theorem depend only on them:

```lean
-- 1. constant preservation
intervalFullSemigroupOperator_const

-- 2. mean-zero
intervalNeumannFullKernel_secondDeriv_integral_zero

-- 3. whole-line Gaussian weighted Hessian mass
heatKernel_secondDeriv_weighted_abs_integral_le

-- 4. interval image-kernel weighted mass
intervalNeumannFullKernel_secondDeriv_weighted_mass

-- 5. final Hölder cancellation
neumannHeatSecondDeriv_Ctheta_to_Linfty
```

The final theorem already has the exact target shape:

```lean
|deriv (fun z => deriv (fun w =>
    intervalFullSemigroupOperator t h w) z) x|
  ≤ weightedHeatHessConst θ * t ^ (-1 + θ / 2 : ℝ) * Hh
```

under `0 < t`, `0 < θ`, `θ < 1`, bounded measurable `h`, and the Hölder condition on `[0,1]`. fileciteturn121file0L15-L22

So the single load-bearing brick is not the algebraic cancellation and not the Duhamel integral. It is the image-kernel weighted mass:

```lean
intervalNeumannFullKernel_secondDeriv_weighted_mass
```

If that theorem compiles, the rest of the endpoint Hölder-cancellation lemma should be plumbing.
