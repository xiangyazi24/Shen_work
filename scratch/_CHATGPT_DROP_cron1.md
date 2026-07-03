# Q3210 (cron1) — EWA gap vs paper semigroup route

Repository: `xiangyazi24/Shen_work`  
Branch: `chatgpt-scratch`  
Target file: `scratch/_CHATGPT_DROP_cron1.md`

## Executive answer

I partly agree with the previous advisor, but they blurred two different issues.

They were right that

```text
PaperPositiveInitialDatum -> Wiener / WA1 initial datum
```

is mathematically false. Continuity plus a positive lower bound gives no absolute summability of Fourier/cosine coefficients. So the EWA proof cannot honestly claim the original Shen initial-data class unless it adds a stronger datum predicate or replaces the local-existence route.

They were also right that the current `DatumWienerData` structure contains a **uniform floor by M**:

```lean
∀ M > 0, ∃ fm > 0, ∀ u₀, PaperPositiveInitialDatum u₀ → |u₀| ≤ M → fm ≤ W.floor
```

That is false for the paper’s positive data class: the constant data `u₀ ≡ ε` with `0 < ε ≤ M` have floors tending to `0`. A positive floor exists **per datum**, not uniformly over all positive data bounded above by `M`.

Where I disagree: neither issue shows that the PDE theorem is impossible. It shows that the **EWA-uniform-core formulation is too strong for the paper statement**. Shen’s semigroup proof is per-datum local existence: the local time may depend on `inf u₀`, `‖u₀‖∞`, and regularity bounds. Global existence then follows by a priori estimates / continuation. The paper does not need a uniform local existence time over all positive data with only an upper bound.

What the advisor missed:

1. `DatumWienerData` has **two** non-paper assumptions: WA1 regularity and a uniform-in-class lower floor. Adding `PaperWienerInitialDatum` fixes the first, but not the second unless the uniform bridge is also weakened to per-datum data or the datum class includes a uniform lower floor.
2. The EWA chain can still be a valid **high-regularity theorem** (`C³`/`WA1` data), but it is not the fastest way to recover the original continuous-positive theorem.
3. The repo already has explicit interval heat/cosine machinery, so the fastest faithful route is not full abstract semigroup theory; it is a **hybrid explicit-kernel semigroup proof** on `[0,1]`.

My recommendation for an unconditional theorem matching Shen’s initial data is option **C**:

```text
Use the explicit Neumann heat kernel / cosine kernel to prove exactly the semigroup estimates needed by the paper, then run the paper’s fixed point argument in C([0,T], C[0,1]).
```

Option A gives a clean weaker theorem. Option B is the most infrastructure-heavy. Option C is the shortest route to the original theorem with clean axioms.

## Q1. What exists in Mathlib as of mid-2026?

The practical answer: **not enough to replay Shen’s abstract semigroup proof off the shelf.**

Mathlib has many building blocks:

```text
Normed spaces, Banach spaces, continuous linear maps
Bochner integrals and interval integrals
Lp spaces and measure theory
filters, derivatives, ContDiff, asymptotics
some Fourier and special-function infrastructure
```

But the following PDE semigroup layer is not available as a ready-to-use stack for this problem:

### (a) Analytic semigroups / C0 semigroups on Banach spaces

There is no production-ready, theorem-rich Mathlib API that gives you:

```text
closed densely defined operator A
sectorial / generator hypotheses
C0 analytic semigroup e^{tA}
mild solution theory
variation-of-constants theorem
contraction mapping local existence for semilinear parabolic PDE
```

in the form Shen uses. You would have to build the abstraction and the concrete Neumann Laplacian instance.

### (b) Fractional powers of sectorial operators

Not available in the needed PDE form. A formalization of

```text
A^σ, domains D(A^σ), sectorial functional calculus,
‖A^σ T(t)‖ ≤ C t^{-σ}
```

would be a major project. It is not the route to take for a final gap.

### (c) Lp estimates for the Neumann heat semigroup on bounded domains

Not available generically. Mathlib will not currently hand you Shen’s

```text
‖A^σ T(t)‖_{p→p} ≤ C t^{-σ} e^{-δt}
```

for the Neumann Laplacian on a smooth bounded domain. For `[0,1]`, the repo’s own kernel/cosine infrastructure is far more relevant than Mathlib’s generic libraries.

### (d) Sobolev embedding `W^{2σ,p} -> C(Ω̄)`

There is no convenient bounded-domain Sobolev embedding theorem in Mathlib that will close this route directly. Formalizing the full Sobolev/fractional-domain chain would be comparable to, or harder than, the PDE theorem itself.

So a full abstract semigroup proof is mathematically elegant but not Lean-efficient right now.

## Q2. Can the explicit Neumann kernel replace abstract semigroup theory?

Yes. This is the right direction.

For the 1D interval, do not try to formalize sectorial fractional powers first. Prove the actual estimates Shen’s fixed point uses by explicit kernels / cosine series.

The important estimates are not necessarily best stated as `A^σ T(t)` estimates. For the fixed point map, it is enough to prove concrete smoothing bounds such as:

```text
‖S(t) f‖∞ ≤ ‖f‖∞
S(t) preserves nonnegativity and positive lower bounds
S(t)f -> f uniformly as t -> 0+ for continuous f
‖∂x S(t) f‖∞ ≤ C t^{-1/2} ‖f‖∞
‖∂xx S(t) f‖∞ ≤ C t^{-1} ‖f‖∞       when needed
```

and the divergence-Duhamel estimate:

```text
‖∫₀ᵗ ∂x S(t-s) B(s) ds‖∞
  ≤ C √t * sup_{s≤t} ‖B(s)‖∞.
```

That last estimate is exactly the small-time factor needed for the chemotaxis contraction. It avoids the derivative-loss issue because the chemotaxis term is in divergence form and the Duhamel kernel contributes one spatial derivative with an integrable `(t-s)^(-1/2)` singularity in 1D.

### Avoid a crude coefficient proof

A warning: a naive coefficient estimate

```text
|c_n(f)| ≤ C ‖f‖∞
∑ (n²)^σ e^{-n²π²t} |c_n(f)|
```

produces an extra `t^{-1/2}` loss from summing modes. That is too crude for the sharp analytic-semigroup bound. Use kernel derivative `L¹_y` bounds instead:

```text
sup_x ∫ |∂x K(t,x,y)| dy ≤ C t^{-1/2}
sup_x ∫ |∂xx K(t,x,y)| dy ≤ C t^{-1}
```

For Neumann heat on `[0,1]`, these can be proved from the reflected Gaussian kernel or from existing cosine-kernel estimates if the repo already has them.

### What to build concretely

A minimal local-existence fixed point in `C([0,T], C[0,1])` needs:

```lean
import ShenWork.PDE.IntervalDomain
import ShenWork.PDE.IntervalNeumannFullKernel
import ShenWork.PDE.HeatKernelGradientEstimates
import ShenWork.Paper2.Statements

noncomputable section

namespace ShenWork.Paper2.IntervalSemigroupLocal

open Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel

/-
Core estimates to land, preferably for the existing interval semigroup operator:

1. supnorm contraction:
   theorem heat_supnorm_le
     (t : ℝ) (ht : 0 ≤ t) (f : intervalDomainPoint → ℝ) :
       supNorm (S t f) ≤ supNorm f

2. positivity / lower floor:
   theorem heat_floor_preserve
     (t : ℝ) (ht : 0 ≤ t) {η : ℝ} (hη : ∀ x, η ≤ f x) :
       ∀ x, η ≤ S t f x

3. strong continuity at zero for continuous data:
   theorem heat_tendsto_zero_uniform
     (hf : Continuous f) :
       Tendsto (fun t => supNorm (S t f - f)) (nhdsWithin 0 (Ioi 0)) (nhds 0)

4. gradient smoothing:
   theorem heat_grad_sup_le
     (t : ℝ) (ht : 0 < t) :
       supNorm (∂x S t f) ≤ C * t^(-1/2) * supNorm f

5. divergence Duhamel:
   theorem divergence_duhamel_sup_le
     {B : ℝ → intervalDomainPoint → ℝ}
     (hB : ∀ s ∈ Icc 0 T, supNorm (B s) ≤ MB) :
       supNorm (fun x => ∫ s in 0..t, ∂x S (t-s) (B s) x)
         ≤ C * sqrt t * MB
-/

end ShenWork.Paper2.IntervalSemigroupLocal
```

Once these are available, the paper’s contraction map can be formalized without `WA1` initial data.

## Q3. Fastest path to an unconditional Theorem 1.1

### Option A — stay EWA, accept `C³` Neumann / `WA1` data

This is fastest if the goal is a clean theorem with stronger hypotheses:

```text
PaperWienerInitialDatum -> Theorem_1_1_strongDatum
```

It is not the original theorem for continuous positive data. It is still valuable and probably easy to make axiom-clean.

But two caveats:

1. `C³ Neumann -> DatumWienerLifting` fixes the Fourier regularity gap, but **does not** fix the uniform floor field in `DatumWienerData.liftM`. You must either remove the uniform-by-`M` floor requirement or strengthen the datum class to include a lower bound depending on `M`.
2. The final theorem should be named honestly, e.g.

```text
Theorem_1_1_of_PaperWienerInitialDatum
```

not the original theorem unless the original statement is also changed.

### Option B — full abstract semigroup proof

This is the slowest. It requires building:

```text
C0 / analytic semigroup theory
sectorial fractional powers
Neumann Laplacian generator theory
Lp heat semigroup estimates
Sobolev embedding on bounded domains
semilinear parabolic fixed point framework
```

That is a library project, not a final-gap patch.

### Option C — hybrid explicit kernel + paper fixed point

This is the fastest path to the original theorem.

Build only the estimates actually used in Section 2.2, and only for `[0,1]`. Use the repo’s explicit Neumann kernel / cosine infrastructure. Work in the concrete Banach space

```text
ContinuousMap intervalDomainPoint ℝ
```

with sup norm, and define the local fixed point map directly:

```text
G(u)(t) = S(t)u0
  - χ₀ ∫₀ᵗ ∂x S(t-s) (u(s) * v_x(s) / (1+v(s))^β) ds
  + ∫₀ᵗ S(t-s) (u(s) * (a - b u(s)^α)) ds
```

Then prove:

```text
mapsTo S_{r,R,T}
contraction on S_{r,R,T}
fixed point exists
positivity / lower floor on short time
initial trace
mild equation
regularity bootstrap for t > 0
continuation by existing a priori/global estimates
```

This avoids both impossible EWA datum gaps:

```text
continuous positive data is enough;
per-datum floor η > 0 is enough;
no WA1 membership is required.
```

## What the previous advisor missed

### 1. The uniform floor problem is a formulation bug, not a PDE obstacle

`PaperPositiveInitialDatum` gives a per-datum floor:

```text
∃ η > 0, ∀ x, η ≤ u0 x.
```

It cannot give a floor uniform over all data with `|u0| ≤ M`. The current `DatumWienerData` asks for exactly such an `fm`. That is stronger than the paper and false.

The correct local theory should use per-datum constants. If later global estimates need a uniform continuation criterion, they should depend on a priori bounds produced by the PDE, not on a uniform initial floor over the entire data class.

### 2. `C³ Neumann -> DatumWienerLifting` is only a high-regularity theorem

It is a good auxiliary theorem, but not a solution to the original continuous-data theorem. It should be presented as a strong-data result.

### 3. The semigroup route does not require all of Mathlib’s abstract semigroup theory

The paper’s proof is phrased abstractly, but on `[0,1]` the needed estimates are explicit kernel estimates. The repo already has interval heat kernel/cosine machinery, so reproducing the exact estimates is much cheaper than building sectorial operators.

### 4. The EWA proof still has value

Keep EWA as:

```text
high-regularity local existence / verification path;
source envelope and spectral regularity toolkit;
sanity-check for kernel estimates.
```

But do not force it to carry the original theorem’s weakest initial data.

## Recommended implementation plan

### Phase 1 — salvage the current chain honestly

Add a strong-data theorem:

```lean
import ShenWork.Wiener.EWA.SourceChiNegUniformBridge
import ShenWork.Paper2.Statements

noncomputable section

namespace ShenWork.EWA

/-- Strong initial datum class for the EWA theorem. -/
structure PaperWienerInitialDatum
    (u0 : ShenWork.IntervalDomain.intervalDomainPoint → ℝ) : Prop where
  ppid : ShenWork.Paper2.PaperPositiveInitialDatum ShenWork.IntervalDomain.intervalDomain u0
  lifting : DatumWienerLifting u0

/-
Target theorem:
  theorem theorem_1_1_of_paperWienerInitialDatum_or_data

Do not claim PPID implies this.
-/

end ShenWork.EWA
```

Also fix the uniform floor issue by replacing `DatumWienerData` with a per-datum version, or explicitly include a lower-floor parameter in the theorem statement.

### Phase 2 — build explicit-kernel local existence

Create a new path independent of EWA membership:

```text
ShenWork/Paper2/IntervalKernelLocalExistence.lean
ShenWork/Paper2/IntervalKernelFixedPoint.lean
ShenWork/Paper2/IntervalKernelToCore.lean
```

Core lemmas:

```text
heat_supnorm_le
heat_floor_preserve
heat_strong_continuity_uniform
heat_grad_sup_le
divergence_duhamel_sup_le
resolver_sup_lipschitz
flux_lipschitz_on_box
logistic_lipschitz_on_box
fixedPoint_mapsTo
fixedPoint_contracting
```

### Phase 3 — connect to global theorem

Use the existing a priori/global continuation machinery. If the current theorem path expects `ChiNegDatumUniformCore`, consider adding a per-datum core path:

```text
ChiNegDatumCore p : Prop :=
  ∀ u0, PPID u0 -> ∃ T > 0, ∃ u, local core p T u0 u
```

and then prove global existence by continuation. Do not require a local time uniform over all bounded positive data unless the paper explicitly proves such a uniform statement with a lower-bound parameter.

## Answer summary

1. **Mathlib status:** not enough abstract semigroup/fractional-power/Sobolev PDE infrastructure to replay Shen Section 2.2 directly.
2. **Explicit formula:** yes, use it. Prove concrete heat kernel estimates, especially the divergence-Duhamel `√T` bound, rather than abstract `A^σ` theory.
3. **Fastest clean path:**
   * A = fastest weaker theorem;
   * B = too large;
   * C = fastest faithful theorem.

Final recommendation:

```text
Short term: land a strong-data EWA theorem honestly.
Main theorem: pivot to the explicit-kernel semigroup fixed point on C([0,T], C[0,1]).
```

This resolves both “impossible gaps” without weakening Shen’s theorem: Wiener membership disappears, and only the per-datum positive floor is used.
