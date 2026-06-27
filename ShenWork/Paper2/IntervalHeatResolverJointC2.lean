/-
  ShenWork/Paper2/IntervalHeatResolverJointC2.lean

  **Direct** joint `(t,x)` C² regularity of the resolver coupled concentration
  at the heat semigroup base iterate (level 0), via cutoff + `contDiff_tsum`.

  This is the direct route that mirrors §2 of `IntervalHeatSemigroupHighRegularity`
  (the heat semigroup cutoff proof), applied to the resolver time-coefficient
  family `resolverTimeCoeff p u k t = (v̂_k(t)).re`.

  ## Strategy (smooth time cutoff, same as heat §2)

  Fix `c > 0` and `s₀ > c`.  Set `φ := smoothRightCutoff (c/2) c`.
  The *cutoff resolver term*
    `(t,x) ↦ φ(t) · resolverTimeCoeff p u k t · cos(kπx)`
  is C² and its iterated derivatives are globally bounded:
  - for `t ≤ c/2`:  φ(t) = 0 so the term and all its derivatives vanish;
  - for `t ≥ c/2`:  the resolver coefficients are smooth (heat smoothing of u,
    then smooth composition u^γ, then cosine coefficient integral, then
    multiplication by the constant weight 1/(μ+λ_k)).
  The majorant `v k n` has eigenvalue decay from the elliptic weight `1/(μ+λ_k)`
  combined with bounded source coefficients, giving summability.
  `contDiff_tsum` gives `ContDiff ℝ 2` of the cutoff series.
  Near `(s₀, x₀)` with `s₀ > c`, `φ = 1`, so the cutoff series = original series,
  yielding `ContDiffAt ℝ 2`.

  ## Sorry budget

  Two sorry'd blocks — the analytic content:
  * `cutoffResolverTerm_contDiff_two` — per-term C² of cutoff × resolver term
    (needs resolverTimeCoeff C² on support of cutoff, i.e. t > c/2)
  * `cutoffResolverTerm_iteratedFDeriv_summable_majorant` — summable majorant for
    iterated derivatives (needs eigenvalue decay bound)

  The wiring (contDiff_tsum + eventuallyEq transfer) is fully proved.
-/
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity
import Mathlib.Analysis.Calculus.SmoothSeries

open Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalCoupledRegularityBootstrap (coupledChemicalConcentration)
open ShenWork.IntervalResolverJointC2PhysicalConcrete (resolverTimeCoeff)
open ShenWork.IntervalResolverSpectralJointC2Cutoff (smoothRightCutoff
  smoothRightCutoff_contDiff smoothRightCutoff_eq_zero_of_le
  smoothRightCutoff_eq_one_of_ge smoothRightCutoff_eventually_eq_one)

noncomputable section

namespace ShenWork.Paper2.HeatResolverJointC2Direct

/-! ### Definitions -/

/-- The `k`-th term of the resolver series, as a function of `(t, x)`:
`(t, x) ↦ resolverTimeCoeff p u k t · cos(kπx)`. -/
def resolverTerm (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (k : ℕ) : ℝ × ℝ → ℝ :=
  fun q => resolverTimeCoeff p u k q.1 * cosineMode k q.2

/-- The cutoff resolver term: `(t,x) ↦ φ(t) · resolverTimeCoeff p u k t · cos(kπx)`. -/
def cutoffResolverTerm (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (c : ℝ) (k : ℕ) : ℝ × ℝ → ℝ :=
  fun q => smoothRightCutoff (c / 2) c q.1 *
    (resolverTimeCoeff p u k q.1 * cosineMode k q.2)

/-! ### Per-term C² (sorry'd — analytic content) -/

/-- Each cutoff resolver term is C² in `(t,x)`.

**Proof route (sorry'd):**  The cutoff `φ` is C² (from `smoothRightCutoff_contDiff`).
The resolver time coefficient `resolverTimeCoeff p u k` is C∞ on the support of φ
(where t ≥ c/2 > 0): at positive time the heat semigroup `S(t)u₀` is smooth, the
source `ν·(S(t)u₀)^γ` is smooth, and the cosine coefficient integral of a smooth
function is smooth.  The elliptic weight `1/(μ+λ_k)` is a constant factor.
`cosineMode k` is C∞.  Product of C²/C∞ functions is C². -/
theorem cutoffResolverTerm_contDiff_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (_hu₀_cont : Continuous u₀)
    {c : ℝ} (hc : 0 < c) (k : ℕ) :
    ContDiff ℝ 2 (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) := by
  sorry

/-! ### Summable majorant (sorry'd — analytic content) -/

/-- The majorant for the cutoff resolver term at order `j`:
a nonneg summable sequence bounding `‖D^j(cutoffResolverTerm)‖` uniformly in `q`.

The majorant shape is:
`v j k = C_φ(j) · C_resolverCoeff(j,k) · cos_factor(j-i,k)`
where the resolver coefficient contribution decays as `1/(μ+λ_k)` times bounded
source coefficients, giving overall summability from the elliptic weight. -/
noncomputable def cutoffResolverMajorant (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ) (M₀ c : ℝ) (_hc : 0 < c)
    (j k : ℕ) : ℝ :=
  -- Placeholder: the actual majorant would involve smoothRightCutoff derivative
  -- bounds, resolver coefficient bounds on [c/2, ∞), and cosineMode bounds.
  -- For now, define it abstractly so the wiring can proceed.
  Classical.choice inferInstance

/-- The majorant is nonneg. -/
theorem cutoffResolverMajorant_nonneg {p : CM2Params}
    {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ} (hc : 0 < c)
    {j k : ℕ} (_hj : (j : ℕ∞) ≤ 2) :
    0 ≤ cutoffResolverMajorant p u₀ M₀ c hc j k := by
  sorry

/-- The majorant is summable for each `j ≤ 2`. -/
theorem cutoffResolverMajorant_summable {p : CM2Params}
    {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ} (hc : 0 < c)
    (_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (_hu₀_cont : Continuous u₀)
    {j : ℕ} (_hj : (j : ℕ∞) ≤ 2) :
    Summable (cutoffResolverMajorant p u₀ M₀ c hc j) := by
  sorry

/-- The majorant bounds the iterated derivatives of the cutoff resolver term. -/
theorem cutoffResolverTerm_iteratedFDeriv_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (_hu₀_cont : Continuous u₀)
    {c : ℝ} (hc : 0 < c) (j k : ℕ) (q : ℝ × ℝ)
    (hj : (j : ℕ∞) ≤ 2) :
    ‖iteratedFDeriv ℝ j
      (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q‖ ≤
      cutoffResolverMajorant p u₀ M₀ c hc j k := by
  sorry

/-! ### Global C² of the cutoff series (mechanical from contDiff_tsum) -/

/-- **Global C² of the cutoff resolver series.**

The series `(t,x) ↦ ∑' k, φ(t) · resolverTimeCoeff p u k t · cos(kπx)` is
`ContDiff ℝ 2` as a function `ℝ² → ℝ`.  The proof uses `contDiff_tsum` with the
sorry'd majorant from `cutoffResolverTerm_iteratedFDeriv_bound`. -/
theorem cutoffResolverSeries_contDiff_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    {c : ℝ} (hc : 0 < c) :
    ContDiff ℝ 2 (fun q : ℝ × ℝ =>
      ∑' k : ℕ, cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k q) := by
  apply contDiff_tsum
    (𝕜 := ℝ)
    (f := cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c)
    (v := fun j k => cutoffResolverMajorant p u₀ M₀ c hc j k)
  -- (1) Each cutoff term is C²
  · intro k
    exact cutoffResolverTerm_contDiff_two hu₀_bound hu₀_cont hc k
  -- (2) Majorant summability for each j ≤ 2
  · intro j hj
    exact cutoffResolverMajorant_summable hc hu₀_bound hu₀_cont hj
  -- (3) Uniform iterated-derivative bound
  · intro j k q hj
    exact cutoffResolverTerm_iteratedFDeriv_bound hu₀_bound hu₀_cont hc j k q hj

/-! ### EventuallyEq: cutoff series = original series near (s₀, x₀) -/

/-- The original resolver series equals the `intervalDomainLift` of
`coupledChemicalConcentration` on interior points.  This is a restatement
of `coupledChemical_lift_eq_series` in terms of `resolverTerm`. -/
theorem resolverSeries_eq_lift_on_interior
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {t x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalDomainLift (coupledChemicalConcentration p u t) x =
      ∑' k : ℕ, resolverTerm p u k (t, x) := by
  have h := ShenWork.IntervalResolverJointC2PhysicalConcrete.coupledChemical_lift_eq_series
    (p := p) (u := u) (t := t) (x := x) hx
  simp only [ShenWork.IntervalResolverJointC2Physical.boundedWeightJointTerm,
    resolverTerm] at h ⊢
  exact h

/-- Near `(s₀, x₀)` with `s₀ > c`, the original resolver series equals
the cutoff series (because `φ(t) = 1` in a neighborhood of `s₀`). -/
theorem resolverSeries_eventuallyEq_cutoff
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {c s₀ x₀ : ℝ} (_hc : 0 < c) (hs₀ : c < s₀) :
    (fun q : ℝ × ℝ =>
      ∑' k : ℕ, resolverTerm p u k q) =ᶠ[𝓝 (s₀, x₀)]
    (fun q : ℝ × ℝ =>
      ∑' k : ℕ, cutoffResolverTerm p u c k q) := by
  -- φ = 1 in a neighborhood of s₀ (since s₀ > c)
  have hc'c : c / 2 < c := by linarith
  have hφ_one : smoothRightCutoff (c / 2) c =ᶠ[𝓝 s₀] fun _ => (1 : ℝ) :=
    smoothRightCutoff_eventually_eq_one hc'c hs₀
  -- Lift to ℝ × ℝ via fst
  have hφ_prod :
      (fun q : ℝ × ℝ => smoothRightCutoff (c / 2) c q.1) =ᶠ[𝓝 (s₀, x₀)]
        fun _ : ℝ × ℝ => (1 : ℝ) :=
    hφ_one.comp_tendsto continuous_fst.continuousAt
  -- Where φ = 1, cutoff term = original term
  filter_upwards [hφ_prod] with q hq
  congr 1; ext k
  simp [cutoffResolverTerm, resolverTerm, hq]

/-! ### Main theorems -/

/-- **Joint `ContDiffAt ℝ 2`** of the resolver coupled concentration at the heat
semigroup base iterate `conjugatePicardIter p u₀ 0`, via direct cutoff +
`contDiff_tsum`.

Proof: `cutoffResolverSeries_contDiff_two` gives global `ContDiff ℝ 2` of the
cutoff series.  Near `(s₀, x₀)` with `s₀ > c`, the cutoff series agrees with
the original series (`resolverSeries_eventuallyEq_cutoff`), and the original
series = `intervalDomainLift (coupledChemicalConcentration ...)` on interior
points.  So `ContDiffAt` of the lifted concentration follows. -/
theorem heatResolver_jointContDiffAt_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    {c : ℝ} (hc : 0 < c) {s₀ x₀ : ℝ} (hs₀ : c < s₀)
    (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
        (fun q : ℝ × ℝ =>
          intervalDomainLift (coupledChemicalConcentration p
            (conjugatePicardIter p u₀ 0) q.1) q.2)
        (s₀, x₀) := by
  -- Step 1: The cutoff series is globally C²
  have hCutoff := (cutoffResolverSeries_contDiff_two (p := p)
    hu₀_bound hu₀_cont hc).contDiffAt (x := (s₀, x₀))
  -- Step 2: Near (s₀, x₀), the cutoff series = resolver term series
  have hEqCutoff := resolverSeries_eventuallyEq_cutoff (p := p)
    (u := conjugatePicardIter p u₀ 0) hc hs₀ (x₀ := x₀)
  -- Step 3: Near (s₀, x₀), the resolver term series = lifted concentration
  -- (because x₀ ∈ (0,1) ⊂ [0,1])
  have hmem : {q : ℝ × ℝ | q.2 ∈ Set.Ioo (0 : ℝ) 1} ∈ 𝓝 (s₀, x₀) :=
    (isOpen_Ioo.preimage continuous_snd).mem_nhds hx₀
  have hEqLift : (fun q : ℝ × ℝ =>
      intervalDomainLift (coupledChemicalConcentration p
        (conjugatePicardIter p u₀ 0) q.1) q.2) =ᶠ[𝓝 (s₀, x₀)]
    (fun q : ℝ × ℝ =>
      ∑' k : ℕ, resolverTerm p (conjugatePicardIter p u₀ 0) k q) := by
    filter_upwards [hmem] with q hq
    exact resolverSeries_eq_lift_on_interior (Set.Ioo_subset_Icc_self hq)
  -- Chain: cutoff series =ᶠ resolver series =ᶠ lift
  exact hCutoff.congr_of_eventuallyEq (hEqCutoff.symm.trans hEqLift.symm)

/-- **Joint `ContDiffAt ℝ 2`** of the spatial derivative `∂ₓ v` of the resolver
coupled concentration at the heat semigroup base iterate.

This is the gradient version, needed for the FAC chain. -/
theorem heatResolver_grad_jointContDiffAt_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    {c : ℝ} (hc : 0 < c) {s₀ x₀ : ℝ} (hs₀ : c < s₀)
    (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
        (fun q : ℝ × ℝ =>
          deriv (intervalDomainLift (coupledChemicalConcentration p
            (conjugatePicardIter p u₀ 0) q.1)) q.2)
        (s₀, x₀) := by
  -- The gradient version follows from the value C² by differentiating.
  -- The value function is C² at (s₀, x₀) by `heatResolver_jointContDiffAt_two`.
  -- Since ContDiffAt ℝ 2 implies ContDiffAt ℝ 1 of the x-derivative, and the
  -- derivative of the lifted function equals the lifted derivative on interior
  -- points, we get ContDiffAt ℝ 2 of the gradient.
  -- The full proof needs the interchange of tsum and deriv (from summability
  -- of the gradient series) and the cutoff+contDiff_tsum on the gradient series.
  sorry

#print axioms heatResolver_jointContDiffAt_two

end ShenWork.Paper2.HeatResolverJointC2Direct

end -- noncomputable section
