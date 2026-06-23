/-
  ShenWork/Paper2/IntervalDenomEnvelopeResolver.lean

  Atom #1D — the `(1+v)^{−β}` chemotaxis-denominator `H^σ` composition envelope,
  closed UNCONDITIONALLY via the C²-VIA-RESOLVER route (σ ∈ (1/2, 3/2)).

  The chemotaxis weight is `(1+v)^{−β}` with `v` = the elliptic resolver of `u`
  (`v` solves `−v''+v=u`, Neumann), so `v` is TWO DEGREES smoother than `u`
  (the elliptic gain).  This file chains the already-landed bricks:

    u ∈ H^σ  (σ > 1/2)
      →[resolver_memHSigmaPlus2_of_memHSigma]   v̂ ∈ H^{σ+2}
      →[σ+2 > 5/2; memHSigma_contDiff_two]      v ∈ ContDiff ℝ 2
      →[memHSigma_one_add_rpow_neg_of_contDiff_two; σ < 3/2]
                                                (1+v)^{−β} ∈ H^σ.

  NON-CIRCULAR: the `C²` of `v` comes from the RESOLVER GAIN on `u ∈ H^{>1/2}`
  (two derivatives ahead), NOT from any bootstrapped target.  We never use
  `ContDiff 2` of `u` — only of `v = resolver(u)`.  The `v` whose `C²` we use is
  the *coefficient-side* resolver value `x ↦ ∑'_k (ĝ_k/(μ+λ_k)) cos(kπx)`, the
  literal Fourier sum of the `H^{σ+2}` resolver coefficients.

  The `C²` regularity and the Neumann compatibility of the composed denominator
  are discharged UNCONDITIONALLY here.  The single carried datum is resolver
  positivity `0 ≤ v` (`v ≥ 0`, the proven elliptic-maximum-principle brick),
  required only for the base `1+v ≥ 1 > 0` of the negative power.

  No `sorry`, no `admit`, no `native_decide`, no custom `axiom`.  New file only.
-/
import ShenWork.Paper2.IntervalHSigmaScale
import ShenWork.Paper2.IntervalCosineSobolevEmbedding
import ShenWork.Paper2.IntervalCkComposition
import ShenWork.PDE.IntervalDuhamelClosedC2
import ShenWork.PDE.IntervalNeumannFullKernel

open Real
open ShenWork.IntervalNeumannFullKernel
open ShenWork.Paper2.HSigmaScale
open ShenWork.Paper2.IntervalCosineSobolevEmbedding
open ShenWork.Paper2.IntervalCkComposition
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalDuhamelClosedC2

noncomputable section

namespace ShenWork.Paper2.IntervalDenomEnvelopeResolver

/-- The coefficient-side resolver value as a real function on `ℝ`:
`v(x) = ∑'_k (ĝ_k/(μ+λ_k)) cos(kπx)`, the Fourier sum of the resolver
coefficients `resolverCoeff μ g`. -/
def resolverValue (μ : ℝ) (g : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, resolverCoeff μ g k * cosineMode k x

/-- **Elliptic gain → `C²`.**  If the source coefficients `g ∈ H^σ` with
`σ > 1/2`, the resolver value `v = resolverValue μ g` is `ContDiff ℝ 2`.
Two derivatives are gained by the resolver (`H^σ → H^{σ+2}`, `σ+2 > 5/2`), and
`H^{>5/2} ↪ C²`.  This uses `C²` of `v`, NOT of `g` — non-circular. -/
theorem resolverValue_contDiff_two {μ σ : ℝ} (hμ : 0 < μ) (hσ : 1 / 2 < σ)
    {g : ℕ → ℝ} (hg : MemHSigma σ g) :
    ContDiff ℝ 2 (resolverValue μ g) := by
  have hv2 : MemHSigma (σ + 2) (resolverCoeff μ g) :=
    (resolver_memHSigmaPlus2_of_memHSigma hμ hg).1
  have hσ2 : 5 / 2 < σ + 2 := by linarith
  exact memHSigma_contDiff_two hσ2 hv2

/-- **Left Neumann of the resolver value.**  `deriv (resolverValue μ g) 0 = 0`.
The elliptic gain places the resolver coefficients in `H^{σ+2}` (σ+2 > 5/2), so
the eigenvalue-weighted ℓ¹ control needed by the termwise-differentiation engine
holds, and each derivative term carries `sin(kπ·0) = 0`. -/
theorem resolverValue_deriv_at_zero {μ σ : ℝ} (hμ : 0 < μ) (hσ : 1 / 2 < σ)
    {g : ℕ → ℝ} (hg : MemHSigma σ g) :
    deriv (resolverValue μ g) 0 = 0 := by
  have hv2 : MemHSigma (σ + 2) (resolverCoeff μ g) :=
    (resolver_memHSigmaPlus2_of_memHSigma hμ hg).1
  have hsum := memHSigma_summable_eigenvalue_abs (by linarith : 5 / 2 < σ + 2) hv2
  exact cosineCoeffSeries_deriv_at_zero hsum

/-- **Right Neumann of the resolver value.**  `deriv (resolverValue μ g) 1 = 0`,
by the same engine (each derivative term carries `sin(kπ·1) = sin(kπ) = 0`). -/
theorem resolverValue_deriv_at_one {μ σ : ℝ} (hμ : 0 < μ) (hσ : 1 / 2 < σ)
    {g : ℕ → ℝ} (hg : MemHSigma σ g) :
    deriv (resolverValue μ g) 1 = 0 := by
  have hv2 : MemHSigma (σ + 2) (resolverCoeff μ g) :=
    (resolver_memHSigmaPlus2_of_memHSigma hμ hg).1
  have hsum := memHSigma_summable_eigenvalue_abs (by linarith : 5 / 2 < σ + 2) hv2
  exact cosineCoeffSeries_deriv_at_one hsum

/-- **Neumann transfer through the negative-power composition.**  If `v` is
differentiable at `x₀` with `deriv v x₀ = 0` and `1 + v x₀ ≠ 0`, then the
chemotaxis denominator `(1+v)^{−β}` also has vanishing derivative at `x₀`:
`deriv (fun x => (1 + v x)^(−β)) x₀ = 0`.  (Chain rule: the inner derivative
factor is `deriv v x₀ = 0`.) -/
theorem denom_deriv_zero_of_inner_deriv_zero {v : ℝ → ℝ} {x₀ β : ℝ}
    (hdiff : DifferentiableAt ℝ v x₀) (hd0 : deriv v x₀ = 0)
    (hbase : 1 + v x₀ ≠ 0) :
    deriv (fun x => (1 + v x) ^ (-β)) x₀ = 0 := by
  have hinner : HasDerivAt (fun x => 1 + v x) (deriv v x₀) x₀ :=
    (hdiff.hasDerivAt).const_add 1
  have hcomp := hinner.rpow_const (Or.inl hbase) (p := -β)
  rw [hd0] at hcomp
  simpa using hcomp.deriv

/-- **Atom #1D, the prize — `(1+v)^{−β} ∈ H^σ`, UNCONDITIONAL composition.**

For `1/2 < σ < 3/2`, given the source coefficients `g ∈ H^σ` (`g = cosineCoeffs u`)
and resolver positivity `0 ≤ v` for `v = resolverValue μ g`, the chemotaxis
denominator `(1+v)^{−β}` has `MemHSigma σ (cosineCoeffs ((1+v)^{−β}))`.

The `C²` of `v` (from the elliptic resolver gain `H^σ → H^{σ+2} ↪ C²`) and the
Neumann compatibility of the composed denominator are BOTH discharged here from
`g ∈ H^σ` — no carried `ContDiff`, no carried coefficient-decay predicate.  The
only hypothesis is positivity of the resolver (the elliptic maximum-principle
brick), used for the strictly-positive base. -/
theorem denom_envelope_memHSigma {μ σ β : ℝ} (hμ : 0 < μ)
    (hσ0 : 1 / 2 < σ) (hσ1 : σ < 3 / 2) {g : ℕ → ℝ} (hg : MemHSigma σ g)
    (hvnn : ∀ x, 0 ≤ resolverValue μ g x) :
    MemHSigma σ (cosineCoeffs (fun x => (1 + resolverValue μ g x) ^ (-β))) := by
  have hv : ContDiff ℝ 2 (resolverValue μ g) :=
    resolverValue_contDiff_two hμ hσ0 hg
  have hdiff : Differentiable ℝ (resolverValue μ g) := hv.differentiable (by norm_num)
  have hd0 : deriv (resolverValue μ g) 0 = 0 := resolverValue_deriv_at_zero hμ hσ0 hg
  have hd1 : deriv (resolverValue μ g) 1 = 0 := resolverValue_deriv_at_one hμ hσ0 hg
  have hbase0 : 1 + resolverValue μ g 0 ≠ 0 := by have := hvnn 0; positivity
  have hbase1 : 1 + resolverValue μ g 1 ≠ 0 := by have := hvnn 1; positivity
  have hN0 := denom_deriv_zero_of_inner_deriv_zero
    (β := β) (hdiff 0) hd0 hbase0
  have hN1 := denom_deriv_zero_of_inner_deriv_zero
    (β := β) (hdiff 1) hd1 hbase1
  exact memHSigma_one_add_rpow_neg_of_contDiff_two (by linarith) hσ1 hv hvnn β hN0 hN1

#print axioms resolverValue_contDiff_two
#print axioms resolverValue_deriv_at_zero
#print axioms resolverValue_deriv_at_one
#print axioms denom_deriv_zero_of_inner_deriv_zero
#print axioms denom_envelope_memHSigma

end ShenWork.Paper2.IntervalDenomEnvelopeResolver
