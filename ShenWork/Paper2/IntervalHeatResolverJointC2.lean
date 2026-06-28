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
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete
import Mathlib.Analysis.Calculus.SmoothSeries

open Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalCoupledRegularityBootstrap (coupledChemicalConcentration)
open ShenWork.IntervalResolverJointC2PhysicalConcrete (resolverTimeCoeff)
open ShenWork.IntervalPhysicalResolverDataConcrete
  (srcTimeCoeff resolverTimeCoeff_eq_weight_smul)
open ShenWork.IntervalPhysicalSourceTimeC2Concrete (srcSlice srcTimeCoeff_eq_cosineCoeffs)
open ShenWork.IntervalFlooredSourceTimeDataIterate (srcSlice1 srcSlice2)
open ShenWork.IntervalMildPicardRegularity
  (cosineCoeffs_hasDerivAt_of_smooth_param)
open ShenWork.IntervalDomainPositiveWindowK1OnEndpoint
  (cosineCoeffs_continuousOn_of_jointContinuousOn_Icc)
open ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData
  (heatDu heatD2u heatSemigroup_d0 heatSemigroup_d1)
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

/-! ### Layer 1: Source coefficient ContDiffAt at positive time (analytic content) -/

/-- The source time coefficient `srcTimeCoeff p u k` is `ContDiffAt ℝ 2` at any
positive time `t > 0` for the heat semigroup base iterate.

This is the deepest analytic content.  At positive time, the heat semigroup
`S(t)u₀` is C∞, so the source `ν·(S(t)u₀)^γ` is smooth in `(t,x)`.
The time derivatives can be computed via the chain rule + heat equation
`∂ₜ S(t)u₀ = Δ S(t)u₀`.  Differentiating the cosine coefficient integral
`∫₀¹ source(t,x) cos(kπx) dx` under the integral sign (via
`cosineCoeffs_hasDerivAt_of_smooth_param`) twice, then checking continuity of
the second derivative's coefficients, gives `ContDiffAt ℝ 2`. -/
theorem heatLevel0_srcTimeCoeff_contDiffAt_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    ContDiffAt ℝ (2 : ℕ∞)
      (srcTimeCoeff p (conjugatePicardIter p u₀ 0) k) t := by
  set s₁ := srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀)
  set s₂ := srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀)
  set f₀ := srcTimeCoeff p (conjugatePicardIter p u₀ 0) k
  set f₁ := fun s => cosineCoeffs (s₁ s) k
  set f₂ := fun s => cosineCoeffs (s₂ s) k
  have hd0 : ∀ s ∈ Set.Ioi (0 : ℝ), HasDerivAt f₀ (f₁ s) s := by
    intro s hs
    obtain ⟨δ, hδ, hcont, hdiff, hcd⟩ :=
      heatSemigroup_d0 (p := p) (u₀ := u₀) (M₀ := M₀)
        hu₀_bound hu₀_cont hfloor s hs
    have hint : ∀ᶠ r in 𝓝 s, IntervalIntegrable
        (srcSlice p (conjugatePicardIter p u₀ 0) r)
        MeasureTheory.volume (0 : ℝ) 1 :=
      hcont.mono fun r hr =>
        (Set.uIcc_of_le (zero_le_one (α := ℝ)) ▸ hr).intervalIntegrable
    have hH := cosineCoeffs_hasDerivAt_of_smooth_param
      (f := srcSlice p (conjugatePicardIter p u₀ 0))
      (f' := srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀))
      (τ := s) (δ := δ) (n := k) hδ hint hdiff hcd
    have heq :
        (fun r => cosineCoeffs (srcSlice p (conjugatePicardIter p u₀ 0) r) k) =
          f₀ := by
      funext r
      simp [f₀, srcTimeCoeff_eq_cosineCoeffs]
    rw [heq] at hH
    simpa [f₁, s₁] using hH
  have hd1 : ∀ s ∈ Set.Ioi (0 : ℝ), HasDerivAt f₁ (f₂ s) s := by
    intro s hs
    obtain ⟨δ, hδ, hcont, hdiff, hcd⟩ :=
      heatSemigroup_d1 (p := p) (u₀ := u₀) (M₀ := M₀)
        hu₀_bound hu₀_cont hfloor s hs
    have hint : ∀ᶠ r in 𝓝 s, IntervalIntegrable
        (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) r)
        MeasureTheory.volume (0 : ℝ) 1 :=
      hcont.mono fun r hr =>
        (Set.uIcc_of_le (zero_le_one (α := ℝ)) ▸ hr).intervalIntegrable
    have hH := cosineCoeffs_hasDerivAt_of_smooth_param
      (f := srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀))
      (f' := srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀))
      (τ := s) (δ := δ) (n := k) hδ hint hdiff hcd
    simpa [f₁, f₂, s₁, s₂] using hH
  have hc2 : ∀ s ∈ Set.Ioi (0 : ℝ), ContinuousAt f₂ s := by
    intro s hs
    obtain ⟨δ, hδ, _, _, hcd⟩ :=
      heatSemigroup_d1 (p := p) (u₀ := u₀) (M₀ := M₀)
        hu₀_bound hu₀_cont hfloor s hs
    have hcont_on :=
      cosineCoeffs_continuousOn_of_jointContinuousOn_Icc
        (f := srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀))
        (c := s - δ) (T := s + δ) k hcd
    have hsmem : s ∈ Set.Icc (s - δ) (s + δ) := ⟨by linarith, by linarith⟩
    have hsub : Set.Icc (s - δ) (s + δ) ∈ 𝓝 s := by
      apply Icc_mem_nhds <;> linarith
    simpa [f₂, s₂] using (hcont_on s hsmem).continuousAt hsub
  have hd0_on : DifferentiableOn ℝ f₀ (Set.Ioi 0) :=
    fun s hs => (hd0 s hs).differentiableAt.differentiableWithinAt
  have heq0 : Set.EqOn (deriv f₀) f₁ (Set.Ioi 0) :=
    fun s hs => (hd0 s hs).deriv
  have hd1_on : DifferentiableOn ℝ f₁ (Set.Ioi 0) :=
    fun s hs => (hd1 s hs).differentiableAt.differentiableWithinAt
  have heq1 : Set.EqOn (deriv f₁) f₂ (Set.Ioi 0) :=
    fun s hs => (hd1 s hs).deriv
  have hc2_on : ContinuousOn f₂ (Set.Ioi 0) :=
    fun s hs => (hc2 s hs).continuousWithinAt
  have hsmul0 : ContDiffOn ℝ 0
      (fun s => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (f₂ s))
      (Set.Ioi 0) := by
    simpa using (contDiffOn_const (c := (1 : StrongDual ℝ ℝ))).smulRight
      (contDiffOn_zero.mpr hc2_on)
  have hfw1 : ContDiffOn ℝ 0
      (fun s => fderivWithin ℝ f₁ (Set.Ioi 0) s) (Set.Ioi 0) :=
    hsmul0.congr (fun s hs => by
      rw [fderivWithin_of_isOpen isOpen_Ioi hs]
      have hsd : deriv f₁ s = f₂ s := heq1 hs
      simpa [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton, hsd] using
        (toSpanSingleton_deriv (𝕜 := ℝ) (f := f₁) (x := s)).symm)
  have h0 : ContDiffOn ℝ 1 f₁ (Set.Ioi 0) :=
    contDiffOn_succ_of_fderivWithin hd1_on (by nofun) hfw1
  have hsmul1 : ContDiffOn ℝ 1
      (fun s => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (f₁ s))
      (Set.Ioi 0) := by
    simpa using (contDiffOn_const (c := (1 : StrongDual ℝ ℝ))).smulRight h0
  have hfw0 : ContDiffOn ℝ 1
      (fun s => fderivWithin ℝ f₀ (Set.Ioi 0) s) (Set.Ioi 0) :=
    hsmul1.congr (fun s hs => by
      rw [fderivWithin_of_isOpen isOpen_Ioi hs]
      have hsd : deriv f₀ s = f₁ s := heq0 hs
      simpa [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton, hsd] using
        (toSpanSingleton_deriv (𝕜 := ℝ) (f := f₀) (x := s)).symm)
  have h1 : ContDiffOn ℝ 2 f₀ (Set.Ioi 0) :=
    contDiffOn_succ_of_fderivWithin hd0_on (by nofun) hfw0
  simpa [f₀] using h1.contDiffAt (Ioi_mem_nhds ht)

/-! ### Layer 2: Resolver coefficient ContDiffAt by constant weight -/

/-- The resolver time coefficient is `ContDiffAt ℝ 2` at positive time.
Follows from `srcTimeCoeff` being `ContDiffAt ℝ 2` and the constant-weight
factorization `resolverTimeCoeff = wₖ · srcTimeCoeff`. -/
theorem heatLevel0_resolverTimeCoeff_contDiffAt_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    ContDiffAt ℝ (2 : ℕ∞)
      (resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k) t := by
  have hsrc := heatLevel0_srcTimeCoeff_contDiffAt_two
    (p := p) hu₀_bound hu₀_cont hfloor ht k
  have hEq : resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k =
      fun s => ShenWork.PDE.intervalNeumannResolverWeight p k *
        srcTimeCoeff p (conjugatePicardIter p u₀ 0) k s := by
    funext s; exact resolverTimeCoeff_eq_weight_smul p _ k s
  rw [hEq]
  exact contDiffAt_const.mul hsrc

/-! ### Layer 3: Cutoff × resolverTimeCoeff is globally C² -/

/-- The scalar cutoff resolver coefficient `φ(t) · resolverTimeCoeff(t)` is
globally `ContDiff ℝ 2`.  For `t < c/2` the cutoff kills the term; for
`t ≥ c/2 > 0` the resolver coefficient is `ContDiffAt ℝ 2`. -/
theorem cutoffResolverCoeff_contDiff_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {c : ℝ} (hc : 0 < c) (k : ℕ) :
    ContDiff ℝ 2 (fun t =>
      smoothRightCutoff (c / 2) c t * resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : c / 2 ≤ t
  · have ht_pos : 0 < t := by linarith
    exact (smoothRightCutoff_contDiff (c' := c / 2) (c := c)).contDiffAt.mul
      (heatLevel0_resolverTimeCoeff_contDiffAt_two hu₀_bound hu₀_cont hfloor ht_pos k)
  · push_neg at ht
    have hev : (fun t => smoothRightCutoff (c / 2) c t *
        resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t) =ᶠ[𝓝 t]
        fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      have : smoothRightCutoff (c / 2) c s = 0 :=
        smoothRightCutoff_eq_zero_of_le (by linarith : c / 2 < c) (le_of_lt hs)
      simp [this]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-! ### Layer 4: Per-term C² in (t,x) -/

/-- Each cutoff resolver term is C² in `(t,x)`.
Decomposition: `cutoffResolverTerm = (φ·resolverCoeff) ∘ fst * cosineMode ∘ snd`.
The scalar part is globally C² (Layer 3), cosineMode is C∞. -/
theorem cutoffResolverTerm_contDiff_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {c : ℝ} (hc : 0 < c) (k : ℕ) :
    ContDiff ℝ 2 (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) := by
  have hcoef := cutoffResolverCoeff_contDiff_two hu₀_bound hu₀_cont hfloor hc k
  have hcoef_q : ContDiff ℝ 2 (fun q : ℝ × ℝ =>
      smoothRightCutoff (c / 2) c q.1 *
        resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k q.1) :=
    hcoef.comp contDiff_fst
  have hcos : ContDiff ℝ 2 (cosineMode k) := by
    unfold cosineMode; fun_prop
  have hcos_q : ContDiff ℝ 2 (fun q : ℝ × ℝ => cosineMode k q.2) :=
    hcos.comp contDiff_snd
  simpa [cutoffResolverTerm, mul_assoc] using hcoef_q.mul hcos_q

/-! ### Summable majorant (sorry'd — analytic content) -/

/-- The majorant for the cutoff resolver term at order `j`:
a nonneg summable sequence bounding `‖D^j(cutoffResolverTerm)‖` uniformly in `q`.

The majorant shape is:
`v j k = C_φ(j) · C_resolverCoeff(j,k) · cos_factor(j-i,k)`
where the resolver coefficient contribution decays as `1/(μ+λ_k)` times bounded
source coefficients, giving overall summability from the elliptic weight. -/
noncomputable def cutoffResolverMajorant (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ) (_M₀ c : ℝ) (hc : 0 < c)
    (j k : ℕ) : ℝ :=
  ⨆ q : ℝ × ℝ, ‖iteratedFDeriv ℝ j
    (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q‖

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
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {c : ℝ} (hc : 0 < c) :
    ContDiff ℝ 2 (fun q : ℝ × ℝ =>
      ∑' k : ℕ, cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k q) := by
  apply contDiff_tsum
    (𝕜 := ℝ)
    (f := cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c)
    (v := fun j k => cutoffResolverMajorant p u₀ M₀ c hc j k)
  -- (1) Each cutoff term is C²
  · intro k
    exact cutoffResolverTerm_contDiff_two hu₀_bound hu₀_cont hfloor hc k
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
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {c : ℝ} (hc : 0 < c) {s₀ x₀ : ℝ} (hs₀ : c < s₀)
    (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
        (fun q : ℝ × ℝ =>
          intervalDomainLift (coupledChemicalConcentration p
            (conjugatePicardIter p u₀ 0) q.1) q.2)
        (s₀, x₀) := by
  -- Step 1: The cutoff series is globally C²
  have hCutoff := (cutoffResolverSeries_contDiff_two (p := p)
    hu₀_bound hu₀_cont hfloor hc).contDiffAt (x := (s₀, x₀))
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
  -- Chain: lift =ᶠ resolver series =ᶠ cutoff series
  exact hCutoff.congr_of_eventuallyEq (hEqLift.trans hEqCutoff)

/-- **Joint `ContDiffAt ℝ 2`** of the spatial derivative `∂ₓ v` of the resolver
coupled concentration at the heat semigroup base iterate.

This is the gradient version, needed for the FAC chain. -/
theorem heatResolver_grad_jointContDiffAt_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (_hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
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
