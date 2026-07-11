import Mathlib

/-!
# Elliptic resolver `+2` multiplier bound (Q4356)

For the generic Neumann elliptic operator `(μ - ν∂ₓₓ)`, the diagonal resolver
multiplier at eigenvalue `t = λ_k ≥ 0` is `r(t) = (1+t)/(μ+νt)` (`μ,ν>0`).  Its
sharp uniform bound is `r(t) ≤ max(1/μ, 1/ν)`, and the squared version
`(1+t)²/(μ+νt)² ≤ max(1/μ,1/ν)²` — this is the `+2` Sobolev gain feeding
`SourceFromSolutionEnvelopePass`.

The ChatGPT audit (Q4356) established `r` is monotone (sign of `r' = (μ-ν)/(μ+νt)²`
is constant), so the sup is an endpoint value `max(1/μ,1/ν)`.  We formalize the
load-bearing pointwise bounds via the direct cross-multiplication route (cleaner
than calculus), fully general over `t ≥ 0`.  Self-contained: Mathlib only.

NOTE (audit residual, not acted on here — would edit an existing file): Q4356
flags that the *currently compiled* concrete resolver in
`IntervalNeumannEllipticResolverR.lean` has denominator `p.μ + λ_k` (elliptic
diffusion normalized to `1`, with `p.ν` a source prefactor `p.ν u^γ`), NOT
`p.μ + p.ν λ_k`.  So the `SourceFromSolutionEnvelopePass` docstring's `μ+νλₖ` is
inconsistent with the code; the one-parameter `HSigmaScale.elliptic_multiplier_le`
already covers the compiled resolver.  The two-parameter lemmas here are the
correct replacement *iff* the operator is genuinely generalized to `μ - ν∂ₓₓ`.
-/

namespace ShenWork.Paper2.EllipticMultiplierBound

/-- **Sharp uniform multiplier bound.**  `(1+t)/(μ+νt) ≤ max(1/μ, 1/ν)` for all
`t ≥ 0`, `μ,ν > 0`.  Direct two-case cross-multiplication. -/
theorem elliptic_multiplier_two_param_le
    {μ ν t : ℝ} (hμ : 0 < μ) (hν : 0 < ν) (ht : 0 ≤ t) :
    (1 + t) / (μ + ν * t) ≤ max (1 / μ) (1 / ν) := by
  have hden : 0 < μ + ν * t := add_pos_of_pos_of_nonneg hμ (mul_nonneg hν.le ht)
  rcases le_total μ ν with hμν | hνμ
  · -- μ ≤ ν: compare with 1/μ
    have hq : (1 + t) / (μ + ν * t) ≤ 1 / μ := by
      rw [div_le_div_iff₀ hden hμ]
      nlinarith [mul_nonneg (sub_nonneg.mpr hμν) ht]
    exact hq.trans (le_max_left _ _)
  · -- ν ≤ μ: compare with 1/ν
    have hq : (1 + t) / (μ + ν * t) ≤ 1 / ν := by
      rw [div_le_div_iff₀ hden hν]
      nlinarith [mul_nonneg (sub_nonneg.mpr hνμ) ht]
    exact hq.trans (le_max_right _ _)

/-- **Squared multiplier bound** (the `H^σ` energy version):
`(1+t)²/(μ+νt)² ≤ max(1/μ,1/ν)²`. -/
theorem elliptic_multiplier_two_param_sq_le
    {μ ν t : ℝ} (hμ : 0 < μ) (hν : 0 < ν) (ht : 0 ≤ t) :
    (1 + t) ^ 2 / (μ + ν * t) ^ 2 ≤ (max (1 / μ) (1 / ν)) ^ 2 := by
  have hden : 0 < μ + ν * t := add_pos_of_pos_of_nonneg hμ (mul_nonneg hν.le ht)
  have hratio_nonneg : 0 ≤ (1 + t) / (μ + ν * t) :=
    div_nonneg (by linarith) hden.le
  have hsq := pow_le_pow_left₀ hratio_nonneg
    (elliptic_multiplier_two_param_le hμ hν ht) 2
  simpa [div_pow] using hsq

/-- **Antitone case** `μ ≤ ν`: `t ↦ (1+t)/(μ+νt)` is antitone on `[0,∞)`
(the sup is attained at `t=0`, value `1/μ`).  Cross-multiplication route. -/
theorem elliptic_multiplier_antitoneOn
    {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν) (hμν : μ ≤ ν) :
    AntitoneOn (fun t => (1 + t) / (μ + ν * t)) (Set.Ici (0 : ℝ)) := by
  intro s hs t ht hst
  have hs0 : 0 ≤ s := Set.mem_Ici.mp hs
  have ht0 : 0 ≤ t := Set.mem_Ici.mp ht
  have hsden : 0 < μ + ν * s := add_pos_of_pos_of_nonneg hμ (mul_nonneg hν.le hs0)
  have htden : 0 < μ + ν * t := add_pos_of_pos_of_nonneg hμ (mul_nonneg hν.le ht0)
  simp only
  rw [div_le_div_iff₀ htden hsden]
  nlinarith [mul_nonneg (sub_nonneg.mpr hμν) (sub_nonneg.mpr hst)]

/-- **Monotone case** `ν ≤ μ`: `t ↦ (1+t)/(μ+νt)` is monotone on `[0,∞)`
(the sup is approached as `t→∞`, value `1/ν`). -/
theorem elliptic_multiplier_monotoneOn
    {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν) (hνμ : ν ≤ μ) :
    MonotoneOn (fun t => (1 + t) / (μ + ν * t)) (Set.Ici (0 : ℝ)) := by
  intro s hs t ht hst
  have hs0 : 0 ≤ s := Set.mem_Ici.mp hs
  have ht0 : 0 ≤ t := Set.mem_Ici.mp ht
  have hsden : 0 < μ + ν * s := add_pos_of_pos_of_nonneg hμ (mul_nonneg hν.le hs0)
  have htden : 0 < μ + ν * t := add_pos_of_pos_of_nonneg hμ (mul_nonneg hν.le ht0)
  simp only
  rw [div_le_div_iff₀ hsden htden]
  nlinarith [mul_nonneg (sub_nonneg.mpr hνμ) (sub_nonneg.mpr hst)]

end ShenWork.Paper2.EllipticMultiplierBound
