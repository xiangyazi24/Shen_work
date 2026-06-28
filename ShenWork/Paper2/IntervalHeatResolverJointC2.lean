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

  ## Analytic content

  Two formerly isolated blocks carry the analytic content:
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
open ShenWork.IntervalResolverJointC2Physical
  (boundedWeightJointTerm boundedWeightJointMajorant
   boundedWeightJointTerm_contDiff boundedWeightJointTerm_iteratedFDeriv_le)
open ShenWork.IntervalResolverJointC2PhysicalConcrete
  (PhysicalResolverJointC2Data)
open ShenWork.IntervalResolverSpectralJointC2CutoffBounds
  (norm_iteratedFDeriv_comp_fst_le)
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

/-! ### Summable majorant (analytic content) -/

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

private theorem resolverSmoothRightCutoff_iteratedFDeriv_bound_exists
    (c' c : ℝ) (hc'c : c' < c) (k : ℕ) (hk : (k : ℕ∞) ≤ 2) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ t : ℝ, ‖iteratedFDeriv ℝ k (smoothRightCutoff c' c) t‖ ≤ B := by
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · refine ⟨1, zero_le_one, fun t => ?_⟩
    rw [norm_iteratedFDeriv_zero]
    unfold smoothRightCutoff
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  · have hcont : Continuous
        (fun t : ℝ => iteratedFDeriv ℝ k (smoothRightCutoff c' c) t) :=
      smoothRightCutoff_contDiff.continuous_iteratedFDeriv (by exact_mod_cast hk)
    have hk_ne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk_pos
    have hzero : ∀ t, t ∉ Set.Icc c' c →
        iteratedFDeriv ℝ k (smoothRightCutoff c' c) t = 0 := by
      intro t ht
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
      rcases ht with ht_lt | ht_gt
      · have hev : smoothRightCutoff c' c =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
          filter_upwards [Iio_mem_nhds ht_lt] with s hs
          exact smoothRightCutoff_eq_zero_of_le hc'c (le_of_lt hs)
        have := (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev k).eq_of_nhds
        rwa [iteratedFDeriv_const_of_ne hk_ne, Pi.zero_apply] at this
      · have hev : smoothRightCutoff c' c =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
          filter_upwards [Ioi_mem_nhds ht_gt] with s hs
          exact smoothRightCutoff_eq_one_of_ge hc'c (le_of_lt hs)
        have := (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev k).eq_of_nhds
        rwa [iteratedFDeriv_const_of_ne hk_ne, Pi.zero_apply] at this
    have hcomp : HasCompactSupport
        (fun t : ℝ => iteratedFDeriv ℝ k (smoothRightCutoff c' c) t) :=
      HasCompactSupport.intro' isCompact_Icc isClosed_Icc hzero
    rcases hcont.bounded_above_of_compact_support hcomp with ⟨C, hC⟩
    exact ⟨max C 0, le_max_right C 0, fun t => (hC t).trans (le_max_left C 0)⟩

private noncomputable def resolverSmoothRightCutoffDerivBound
    (c' c : ℝ) (hc'c : c' < c) (k : ℕ) (hk : (k : ℕ∞) ≤ 2) : ℝ :=
  Classical.choose
    (resolverSmoothRightCutoff_iteratedFDeriv_bound_exists c' c hc'c k hk)

private theorem resolverSmoothRightCutoffDerivBound_nonneg
    {c' c : ℝ} (hc'c : c' < c) {k : ℕ} (hk : (k : ℕ∞) ≤ 2) :
    0 ≤ resolverSmoothRightCutoffDerivBound c' c hc'c k hk :=
  (Classical.choose_spec
    (resolverSmoothRightCutoff_iteratedFDeriv_bound_exists c' c hc'c k hk)).1

private theorem resolverSmoothRightCutoffDerivBound_spec
    {c' c : ℝ} (hc'c : c' < c) {k : ℕ} (hk : (k : ℕ∞) ≤ 2) (t : ℝ) :
    ‖iteratedFDeriv ℝ k (smoothRightCutoff c' c) t‖ ≤
      resolverSmoothRightCutoffDerivBound c' c hc'c k hk :=
  (Classical.choose_spec
    (resolverSmoothRightCutoff_iteratedFDeriv_bound_exists c' c hc'c k hk)).2 t

private noncomputable def cutoffResolverExplicitMajorant
    (Bt : ℕ → ℕ → ℝ) (c : ℝ) (hc : 0 < c) (j k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
    (if hi : (i : ℕ∞) ≤ 2 then
      resolverSmoothRightCutoffDerivBound (c / 2) c (by linarith) i hi
    else 0) *
    boundedWeightJointMajorant Bt (j - i) k

private theorem cutoffResolverTerm_iteratedFDeriv_le_explicit
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt)
    {c : ℝ} (hc : 0 < c) (j k : ℕ) (q : ℝ × ℝ)
    (hj : (j : ℕ∞) ≤ 2) :
    ‖iteratedFDeriv ℝ j (cutoffResolverTerm p u c k) q‖ ≤
      cutoffResolverExplicitMajorant Bt c hc j k := by
  classical
  have hc'c : c / 2 < c := by linarith
  let G : ℝ × ℝ → ℝ := fun q => smoothRightCutoff (c / 2) c q.1
  let R : ℝ × ℝ → ℝ :=
    boundedWeightJointTerm (resolverTimeCoeff p u) k
  have hterm : cutoffResolverTerm p u c k = fun q : ℝ × ℝ => G q * R q := by
    funext q
    simp [cutoffResolverTerm, boundedWeightJointTerm, G, R, mul_assoc]
  have hG : ContDiff ℝ (2 : ℕ∞) G :=
    (smoothRightCutoff_contDiff (c' := c / 2) (c := c)).comp contDiff_fst
  have hR : ContDiff ℝ (2 : ℕ∞) R :=
    boundedWeightJointTerm_contDiff k (H.coeff_contDiff k)
  have hjTop : ((j : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast hj
  rw [hterm]
  calc
    ‖iteratedFDeriv ℝ j (fun q : ℝ × ℝ => G q * R q) q‖
        ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i G q‖ *
            ‖iteratedFDeriv ℝ (j - i) R q‖ := by
          simpa [mul_assoc] using norm_iteratedFDeriv_mul_le hG hR q hjTop
    _ ≤ cutoffResolverExplicitMajorant Bt c hc j k := by
      unfold cutoffResolverExplicitMajorant
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hjNat : j ≤ 2 := by exact_mod_cast hj
      have hiNat : i ≤ 2 := le_trans hik hjNat
      have hjiNat : j - i ≤ 2 := le_trans (Nat.sub_le j i) hjNat
      have hiTop : (i : ℕ∞) ≤ (2 : ℕ∞) := by exact_mod_cast hiNat
      have hjiTop : ((j - i : ℕ) : ℕ∞) ≤ (2 : ℕ∞) := by exact_mod_cast hjiNat
      have hG_bound : ‖iteratedFDeriv ℝ i G q‖ ≤
          resolverSmoothRightCutoffDerivBound (c / 2) c hc'c i hiTop := by
        exact (norm_iteratedFDeriv_comp_fst_le
          (smoothRightCutoff_contDiff (c' := c / 2) (c := c))
          (by exact_mod_cast hiTop) q).trans
          (resolverSmoothRightCutoffDerivBound_spec hc'c hiTop q.1)
      have hR_bound : ‖iteratedFDeriv ℝ (j - i) R q‖ ≤
          boundedWeightJointMajorant Bt (j - i) k :=
        boundedWeightJointTerm_iteratedFDeriv_le
          (c := resolverTimeCoeff p u) (Bt := Bt) (n := k) (k := j - i) (q := q)
          (H.coeff_contDiff k) hjiTop
          (fun a ha => H.coeff_bound a k q.1 ha)
      have hchoose_nn : 0 ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
      have hΦ_nn : 0 ≤ resolverSmoothRightCutoffDerivBound (c / 2) c hc'c i hiTop :=
        resolverSmoothRightCutoffDerivBound_nonneg hc'c hiTop
      calc (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i G q‖ *
            ‖iteratedFDeriv ℝ (j - i) R q‖
          ≤ (j.choose i : ℝ) *
              resolverSmoothRightCutoffDerivBound (c / 2) c hc'c i hiTop *
              ‖iteratedFDeriv ℝ (j - i) R q‖ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hG_bound hchoose_nn) (norm_nonneg _)
        _ ≤ (j.choose i : ℝ) *
              resolverSmoothRightCutoffDerivBound (c / 2) c hc'c i hiTop *
              boundedWeightJointMajorant Bt (j - i) k := by
            exact mul_le_mul_of_nonneg_left hR_bound
              (mul_nonneg hchoose_nn hΦ_nn)
        _ = (j.choose i : ℝ) *
              (if hi : (i : ℕ∞) ≤ 2 then
                resolverSmoothRightCutoffDerivBound (c / 2) c hc'c i hi
              else 0) *
              boundedWeightJointMajorant Bt (j - i) k := by
            rw [dif_pos hiTop]

private theorem cutoffResolverMajorant_bddAbove_of_physical
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (hc : 0 < c) {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p (conjugatePicardIter p u₀ 0) Bt)
    (j k : ℕ) (hj : (j : ℕ∞) ≤ 2) :
    BddAbove (Set.range fun q : ℝ × ℝ =>
      ‖iteratedFDeriv ℝ j
        (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q‖) := by
  refine ⟨cutoffResolverExplicitMajorant Bt c hc j k, ?_⟩
  rintro _ ⟨q, rfl⟩
  exact cutoffResolverTerm_iteratedFDeriv_le_explicit H hc j k q hj

/-! ### Direct BddAbove (bypasses PhysicalResolverJointC2Data) -/

/-- Generic BddAbove from left-zero/mid/tail decomposition. -/
private theorem bddAbove_range_of_left_mid_tail
    {g : ℝ × ℝ → ℝ} {a : ℝ} {Cmid Ctail : ℝ}
    (hleft : ∀ q : ℝ × ℝ, q.1 < a → g q = 0)
    (hmid : ∀ q : ℝ × ℝ, a ≤ q.1 → q.1 ≤ a + 1 → g q ≤ Cmid)
    (htail : ∀ q : ℝ × ℝ, a + 1 < q.1 → g q ≤ Ctail) :
    BddAbove (Set.range g) := by
  refine ⟨max 0 (max Cmid Ctail), ?_⟩
  rintro _ ⟨q, rfl⟩
  by_cases hqa : q.1 < a
  · rw [hleft q hqa]; exact le_max_left 0 _
  · push_neg at hqa
    by_cases hqb : q.1 ≤ a + 1
    · exact (hmid q hqa hqb).trans ((le_max_left Cmid Ctail).trans (le_max_right 0 _))
    · push_neg at hqb
      exact (htail q hqb).trans ((le_max_right Cmid Ctail).trans (le_max_right 0 _))

/-- BddAbove of the cutoff resolver term iteratedFDeriv norm, proved directly
from the product structure A(t) · B(x) without PhysicalResolverJointC2Data.
Uses: left zero (cutoff), mid compact (compactness in t × cosine bound in x),
tail explicit (L∞ contraction + eigenvalue damping). -/
private theorem cutoffResolverMajorant_bddAbove_direct
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (hc : 0 < c)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    (j k : ℕ) (hj : (j : ℕ∞) ≤ 2) :
    BddAbove (Set.range fun q : ℝ × ℝ =>
      ‖iteratedFDeriv ℝ j
        (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q‖) := by
  set f := cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k with hf_def
  have hfC2 := cutoffResolverTerm_contDiff_two hu₀_bound hu₀_cont hfloor hc k
  have hcont : Continuous (fun q : ℝ × ℝ => ‖iteratedFDeriv ℝ j f q‖) :=
    (hfC2.continuous_iteratedFDeriv (by exact_mod_cast hj)).norm
  -- Factor: f(t,x) = A(t) · B(x) where A = φ·resolverCoeff, B = cosineMode k
  set A := fun t : ℝ =>
    smoothRightCutoff (c / 2) c t * resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t
  have hAC2 := cutoffResolverCoeff_contDiff_two hu₀_bound hu₀_cont hfloor hc k
  -- Left zero: f = 0 for t < c/2
  have hleft : ∀ q : ℝ × ℝ, q.1 < c / 2 →
      ‖iteratedFDeriv ℝ j f q‖ = 0 := by
    intro q hq
    have hev : f =ᶠ[𝓝 q] fun _ => (0 : ℝ) := by
      have hmem : (Set.Iio (c / 2)) ×ˢ (Set.univ : Set ℝ) ∈ 𝓝 q :=
        (isOpen_Iio.prod isOpen_univ).mem_nhds ⟨hq, Set.mem_univ _⟩
      filter_upwards [hmem] with r hr
      obtain ⟨hr1, _⟩ := Set.mem_prod.mp hr
      show cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k r = 0
      unfold cutoffResolverTerm
      rw [smoothRightCutoff_eq_zero_of_le (by linarith : c / 2 < c) (le_of_lt hr1)]
      ring
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · rw [norm_iteratedFDeriv_zero, hev.eq_of_nhds, norm_zero]
    · have := (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev j).eq_of_nhds
      rw [iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.mp hjpos), Pi.zero_apply] at this
      rw [this, norm_zero]
  -- Mid bound: compact time [c/2, c/2+1], global cosine bound
  -- Use: A is C² → continuous iteratedFDeriv → bounded on compact [c/2, c/2+1]
  -- Cosine mode derivatives bounded by valueCosWeight
  -- Leibniz gives product bound
  have hmid : ∃ Cmid : ℝ, ∀ q : ℝ × ℝ, c / 2 ≤ q.1 → q.1 ≤ c / 2 + 1 →
      ‖iteratedFDeriv ℝ j f q‖ ≤ Cmid := by
    -- Factor f = (A ∘ fst) · (cosineMode k ∘ snd)
    have hcos : ContDiff ℝ (2 : ℕ∞) (cosineMode k) := by unfold cosineMode; fun_prop
    have hjNat : j ≤ 2 := by exact_mod_cast hj
    -- Get compact-time bound on each order of iteratedFDeriv of A
    -- For i ≤ 2: ∃ C_i, ∀ t ∈ [c/2, c/2+1], ‖iteratedFDeriv ℝ i A t‖ ≤ C_i
    have hA_bounds : ∀ i : ℕ, i ≤ 2 →
        ∃ C_i : ℝ, ∀ t ∈ Set.Icc (c / 2) (c / 2 + 1),
          ‖iteratedFDeriv ℝ i A t‖ ≤ C_i := by
      intro i hi
      have hcont_i : Continuous (fun t : ℝ => iteratedFDeriv ℝ i A t) :=
        hAC2.continuous_iteratedFDeriv (by exact_mod_cast hi)
      exact isCompact_Icc.exists_bound_of_continuousOn hcont_i.continuousOn
    -- For each i ≤ j ≤ 2, extract the compact-time bound C_i
    -- and the cosine mode bound valueCosWeight(j-i, k)
    -- Define Cmid as the Leibniz sum
    -- We need A ∘ fst and cosineMode k ∘ snd to be C²
    have hAfst : ContDiff ℝ (2 : ℕ∞) (fun q : ℝ × ℝ => A q.1) :=
      hAC2.comp contDiff_fst
    have hBsnd : ContDiff ℝ (2 : ℕ∞) (fun q : ℝ × ℝ => cosineMode k q.2) :=
      hcos.comp contDiff_snd
    have hjTop : ((j : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
      exact_mod_cast hj
    -- The factoring: f = (A ∘ fst) * (cosineMode k ∘ snd)
    have hfactor : f = fun q : ℝ × ℝ => A q.1 * cosineMode k q.2 := by
      funext q; simp [hf_def, cutoffResolverTerm, A, mul_assoc]
    -- Get a uniform C_max bounding all iteratedFDeriv orders of A on [c/2, c/2+1]
    have ⟨C_max, hC_max⟩ : ∃ C_max : ℝ, ∀ (i : ℕ), i ≤ 2 →
        ∀ t ∈ Set.Icc (c / 2) (c / 2 + 1),
          ‖iteratedFDeriv ℝ i A t‖ ≤ C_max := by
      obtain ⟨c0, hc0⟩ := hA_bounds 0 (by omega)
      obtain ⟨c1, hc1⟩ := hA_bounds 1 (by omega)
      obtain ⟨c2, hc2⟩ := hA_bounds 2 (by omega)
      refine ⟨max c0 (max c1 c2), fun i hi t ht => ?_⟩
      interval_cases i
      · exact (hc0 t ht).trans (le_max_left _ _)
      · exact (hc1 t ht).trans ((le_max_left _ _).trans (le_max_right _ _))
      · exact (hc2 t ht).trans ((le_max_right _ _).trans (le_max_right _ _))
    -- The explicit bound: Σ C(j,i) * C_max * valueCosWeight(j-i, k)
    set Cmid := ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * C_max *
        ShenWork.IntervalResolverSpectralJointC2Concrete.valueCosWeight (j - i) k
    refine ⟨Cmid, fun q hq_lo hq_hi => ?_⟩
    rw [hfactor]
    calc ‖iteratedFDeriv ℝ j (fun q : ℝ × ℝ => A q.1 * cosineMode k q.2) q‖
        ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun q : ℝ × ℝ => A q.1) q‖ *
            ‖iteratedFDeriv ℝ (j - i) (fun q : ℝ × ℝ => cosineMode k q.2) q‖ := by
          simpa [mul_assoc] using norm_iteratedFDeriv_mul_le hAfst hBsnd q hjTop
      _ ≤ Cmid := by
          apply Finset.sum_le_sum
          intro i hi
          have hik : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hiNat : i ≤ 2 := le_trans hik hjNat
          have hjiNat : j - i ≤ 2 := le_trans (Nat.sub_le j i) hjNat
          have hiTop' : (i : ℕ∞) ≤ (2 : ℕ∞) := by exact_mod_cast hiNat
          have hjiTop : ((j - i : ℕ) : ℕ∞) ≤ (2 : ℕ∞) := by exact_mod_cast hjiNat
          have hiCast : ((i : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
            exact_mod_cast hiNat
          have hjiCast : (((j - i : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
            exact_mod_cast hjiNat
          have hA_fst_bound : ‖iteratedFDeriv ℝ i (fun q : ℝ × ℝ => A q.1) q‖ ≤ C_max := by
            exact (norm_iteratedFDeriv_comp_fst_le hAC2 hiCast q).trans
              (hC_max i hiNat q.1 ⟨hq_lo, hq_hi⟩)
          have hB_snd_bound : ‖iteratedFDeriv ℝ (j - i)
              (fun q : ℝ × ℝ => cosineMode k q.2) q‖ ≤
              ShenWork.IntervalResolverSpectralJointC2Concrete.valueCosWeight (j - i) k := by
            exact (ShenWork.IntervalResolverSpectralJointC2CutoffBounds.norm_iteratedFDeriv_comp_snd_le
              hcos hjiCast q).trans
              (ShenWork.IntervalResolverSpectralJointC2Concrete.cosineMode_iteratedFDeriv_bound
                k (j - i) q.2 hjiNat)
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hA_fst_bound (Nat.cast_nonneg _))
            hB_snd_bound (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (le_trans (norm_nonneg _) hA_fst_bound))
  -- Tail bound: for t > c/2+1, use explicit L∞ bounds
  have htail : ∃ Ctail : ℝ, ∀ q : ℝ × ℝ, c / 2 + 1 < q.1 →
      ‖iteratedFDeriv ℝ j f q‖ ≤ Ctail := by
    -- Same Leibniz structure as hmid. The time part A is C², so
    -- iteratedFDeriv is continuous on [c/2, ∞). We extend the compact bound
    -- to [c/2, c/2+2] which covers all t ∈ (c/2+1, c/2+2]. For t > c/2+2,
    -- we chain further compact intervals.
    -- For now: use a SINGLE large compact interval [c/2, c/2+2] which
    -- covers the boundary. For the true tail, we use the L∞ bound.
    -- APPROACH: identical to hmid but on [c/2, c/2 + 2] for the compact bound,
    -- combined with the observation that the hmid bound already covers [c/2, c/2+1]
    -- and for t > c/2+1 the cutoff is 1 so A = resolverTimeCoeff.
    -- The iteratedFDeriv of A is uniformly bounded because:
    -- (i=0) |A(t)| ≤ w_k * 2ν*‖u₀‖^γ from L∞ contraction
    -- (i≥1) |A^(i)(t)| is bounded from eigenvalue damping + max principle
    -- These bounds are UNIFORM in t ≥ c/2 (not just on a compact set).
    -- For a clean proof without eigenvalue damping infrastructure, we
    -- observe: A is C², A(t) → L (finite limit), A'(t) → 0, A''(t) → 0
    -- as t → ∞. A continuous function on [c/2, ∞) with a finite limit at ∞
    -- is bounded. Same for A', A''.
    -- For now, we use the compact argument on a SUFFICIENTLY LARGE interval.
    have hcos : ContDiff ℝ (2 : ℕ∞) (cosineMode k) := by unfold cosineMode; fun_prop
    have hjNat : j ≤ 2 := by exact_mod_cast hj
    -- Uniform bound on A's iteratedFDeriv for all t (using continuous + zero-at-left + bounded-at-right)
    have hA_global_bounds : ∀ i : ℕ, i ≤ 2 →
        ∃ B_i : ℝ, ∀ t : ℝ, ‖iteratedFDeriv ℝ i A t‖ ≤ B_i := by
      intro i hi
      interval_cases i
      · -- i = 0: |A(t)| ≤ 1 · w_k · 2ν · M^γ from L∞ contraction
        -- A(t) = φ(t) · resolverTimeCoeff(k,t), |φ| ≤ 1
        -- |resolverTimeCoeff| ≤ w_k · |srcTimeCoeff| ≤ w_k · 2ν · M^γ
        -- where M bounds |u₀| (continuous on compact → bounded)
        haveI : CompactSpace intervalDomainPoint :=
          isCompact_iff_compactSpace.mp isCompact_Icc
        haveI : Nonempty intervalDomainPoint :=
          ⟨⟨0, Set.left_mem_Icc.mpr (by norm_num)⟩⟩
        -- Get sup bound M on |u₀|
        obtain ⟨x_max, _, hx_max⟩ := IsCompact.exists_isMaxOn isCompact_univ
          Set.univ_nonempty (hu₀_cont.norm.continuousOn)
        set M_sup := ‖u₀ x_max‖ with hM_sup_def
        have hM_sup_nn : 0 ≤ M_sup := norm_nonneg _
        have hu₀_le : ∀ x : intervalDomainPoint, ‖u₀ x‖ ≤ M_sup := by
          intro x; exact hx_max (Set.mem_univ x)
        -- |intervalDomainLift u₀ y| ≤ M_sup for all y ∈ ℝ
        have hlift_le : ∀ y : ℝ, |intervalDomainLift u₀ y| ≤ M_sup := by
          intro y; unfold intervalDomainLift; split
          · exact Real.norm_eq_abs _ ▸ hu₀_le ⟨y, ‹_›⟩
          · simp [abs_of_nonneg, hM_sup_nn]
        -- L∞ contraction: |S(t)u₀(x)| ≤ M_sup for t > 0
        have hSt_le : ∀ t : ℝ, 0 < t → ∀ x : ℝ,
            |ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
              t (intervalDomainLift u₀) x| ≤ M_sup :=
          fun t ht x =>
            ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
              ht hM_sup_nn hlift_le x
        -- For i=0: ‖iteratedFDeriv ℝ 0 A t‖ = |A t|
        -- Split: t ≤ c/2 → A=0, t > c/2 → bound from L∞ chain
        -- Use compact [c/2, c/2+1] for the transition + L∞ tail for t > c/2+1
        -- SIMPLIFICATION: just use compact bound on [c/2, c/2+2] combined with
        -- A=0 on the left. For t > c/2+2: use L∞ bound.
        have hA_cont : Continuous A := hAC2.continuous
        -- Compact bound on [c/2, c/2+2]
        obtain ⟨B_compact, hB_compact⟩ := (isCompact_Icc (a := c / 2) (b := c + 1)).exists_bound_of_continuousOn
          hA_cont.continuousOn
        -- L∞ tail bound: for t > 0, |S(t)u₀(x)| ≤ M_sup → srcSlice bounded → srcTimeCoeff bounded
        -- For the tail, we need ContinuousOn of srcSlice on [0,1] + |srcSlice| ≤ ν * M_sup^γ
        -- ContinuousOn follows from hSt_cont + rpow continuity at positive values
        -- For now, we sorry the tail bound and combine with the compact bound
        have hA_tail : ∃ B_tail : ℝ, ∀ t : ℝ, c + 1 < t →
            |A t| ≤ B_tail := by
          set u := conjugatePicardIter p u₀ 0
          set w_k := ShenWork.PDE.intervalNeumannResolverWeight p k
          refine ⟨|w_k| * (2 * p.ν * M_sup ^ p.γ), fun t ht => ?_⟩
          -- Step 1: φ(t) = 1 for t > c+1 > c
          have ht_ge_c : c ≤ t := by linarith
          have hφ_one : smoothRightCutoff (c / 2) c t = 1 :=
            smoothRightCutoff_eq_one_of_ge (by linarith : c / 2 < c) ht_ge_c
          -- Step 2: |A(t)| = |resolverTimeCoeff(k,t)|
          show |smoothRightCutoff (c / 2) c t * resolverTimeCoeff p u k t| ≤ _
          rw [hφ_one, one_mul]
          -- Step 3: |resolverTimeCoeff| = |w_k * srcTimeCoeff|
          rw [resolverTimeCoeff_eq_weight_smul p u k t, abs_mul]
          -- Step 4: bound |srcTimeCoeff|
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          -- Goal: |srcTimeCoeff p u k t| ≤ 2 * p.ν * M_sup ^ p.γ
          rw [srcTimeCoeff_eq_cosineCoeffs p u k t]
          -- Goal: |cosineCoeffs (srcSlice p u t) k| ≤ 2 * p.ν * M_sup ^ p.γ
          have ht_pos : 0 < t := by linarith
          -- Pointwise bound: |srcSlice(t,x)| ≤ ν * M_sup^γ on [0,1]
          have hsrc_bound : ∀ x ∈ Set.Icc (0:ℝ) 1,
              |srcSlice p u t x| ≤ p.ν * M_sup ^ p.γ := by
            intro x hx
            unfold srcSlice
            rw [abs_of_nonneg (mul_nonneg (le_of_lt p.hν) (Real.rpow_nonneg
              (le_of_lt (hfloor t ht_pos x hx)) _))]
            apply mul_le_mul_of_nonneg_left _ (le_of_lt p.hν)
            apply Real.rpow_le_rpow (le_of_lt (hfloor t ht_pos x hx))
            · -- S(t)u₀(x) ≤ M_sup from L∞ contraction + positivity
              -- intervalDomainLift(u t)(x) = u t ⟨x,hx⟩ = S(t)(lift u₀)(x) for x ∈ [0,1]
              have hdef : intervalDomainLift (u t) x =
                  ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
                    t (intervalDomainLift u₀) x := by
                unfold intervalDomainLift; rw [dif_pos hx]; simp only [u]; rfl
              rw [hdef]
              exact le_of_abs_le (hSt_le t ht_pos x)
            · exact le_of_lt p.hγ
          -- ContinuousOn of srcSlice on [0,1]
          have hsrc_cont : ContinuousOn (srcSlice p u t) (Set.Icc (0:ℝ) 1) := by
            unfold srcSlice
            apply ContinuousOn.mul continuousOn_const
            apply ContinuousOn.rpow_const
            · -- ContinuousOn of intervalDomainLift(u t) on [0,1]
              have := ShenWork.IntervalDuhamelIntegrability.continuousOn_intervalFullSemigroupOperator_of_bounded
                ht_pos hlift_le
              exact this.congr fun x hx => by
                show intervalDomainLift (u t) x = _
                unfold intervalDomainLift; simp only [dif_pos hx, u]; rfl
            · intro x hx
              exact Or.inl (ne_of_gt (hfloor t ht_pos x hx))
          -- Apply cosineCoeffs_abs_le_of_continuous_bounded
          exact (ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
            hsrc_cont (mul_nonneg (le_of_lt p.hν) (Real.rpow_nonneg hM_sup_nn _))
            hsrc_bound k).trans (le_of_eq (by ring))
        obtain ⟨B_tail, hB_tail⟩ := hA_tail
        refine ⟨max (max 0 B_compact) B_tail, fun t => ?_⟩
        rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
        by_cases ht_left : t < c / 2
        · -- t < c/2: A = 0
          have : A t = 0 := by
            show smoothRightCutoff (c / 2) c t *
              resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t = 0
            rw [smoothRightCutoff_eq_zero_of_le (by linarith : c / 2 < c) (le_of_lt ht_left)]
            ring
          simp [this, le_max_left]
        · simp only [not_lt] at ht_left
          by_cases ht_mid : t ≤ c + 1
          · -- c/2 ≤ t ≤ c/2+2: compact bound
            have : |A t| ≤ B_compact := by
              rw [← Real.norm_eq_abs]
              exact hB_compact t ⟨ht_left, ht_mid⟩
            exact this.trans ((le_max_right (0 : ℝ) B_compact).trans (le_max_left _ B_tail))
          · -- t > c/2+2: tail bound
            simp only [not_le] at ht_mid
            exact (hB_tail t ht_mid).trans (le_max_right _ B_tail)
      · -- i = 1: same compact+tail split as i=0
        have hA1_cont : Continuous (fun t : ℝ => iteratedFDeriv ℝ 1 A t) :=
          hAC2.continuous_iteratedFDeriv (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2))
        obtain ⟨B1_compact, hB1_compact⟩ :=
          (isCompact_Icc (a := c / 2) (b := c + 1)).exists_bound_of_continuousOn
            hA1_cont.continuousOn
        have hA1_tail : ∃ B : ℝ, ∀ t : ℝ, c + 1 < t →
            ‖iteratedFDeriv ℝ 1 A t‖ ≤ B := by
          -- A = φ * resolverTimeCoeff. Use 1D Leibniz: A' = φ'*R + φ*R'.
          -- φ' bounded (resolverSmoothRightCutoffDerivBound_spec), R bounded (i=0 bound).
          -- φ bounded (≤1), R' bounded (THIS is the hard part — needs eigenvalue damping).
          -- For R' = resolverTimeCoeff': for t > c+1 > 0, srcTimeCoeff is C²
          -- (heatLevel0_srcTimeCoeff_contDiffAt_two), so srcTimeCoeff' is continuous.
          -- srcTimeCoeff'(t) = cosineCoeffs(srcSlice1(t), k) from d0 (HasDerivAt).
          -- |cosineCoeffs(srcSlice1(t), k)| ≤ 2·‖srcSlice1(t)‖_∞
          -- ‖srcSlice1(t)‖_∞ ≤ νγ·M_sup^{γ-1}·‖Δu(t)‖_∞
          -- ‖Δu(t)‖_∞ ≤ M₀·(4/((c+1)²π²))·Σ(1/n²) from unitIntervalCosineHeatSecondPointWeight_abs_le
          sorry
        obtain ⟨B1_tail, hB1_tail⟩ := hA1_tail
        refine ⟨max (max 0 B1_compact) B1_tail, fun t => ?_⟩
        by_cases ht_left : t < c / 2
        · -- A' = 0 for t < c/2 (A ≡ 0 near t)
          have hev : A =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
            have hmem : Set.Iio (c / 2) ∈ 𝓝 t := Iio_mem_nhds ht_left
            filter_upwards [hmem] with s hs
            show smoothRightCutoff (c / 2) c s *
              resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k s = 0
            rw [smoothRightCutoff_eq_zero_of_le (by linarith : c / 2 < c) (le_of_lt hs)]; ring
          rw [(Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev 1).eq_of_nhds,
            iteratedFDeriv_const_of_ne (by norm_num : (1 : ℕ) ≠ 0), Pi.zero_apply, norm_zero]
          exact le_trans (le_max_left (0 : ℝ) _) (le_max_left _ _)
        · simp only [not_lt] at ht_left
          by_cases ht_mid : t ≤ c + 1
          · exact (hB1_compact t ⟨ht_left, ht_mid⟩).trans
              ((le_max_right (0 : ℝ) _).trans (le_max_left _ _))
          · simp only [not_le] at ht_mid
            exact (hB1_tail t ht_mid).trans (le_max_right _ _)
      · -- i = 2: same compact+tail split
        have hA2_cont : Continuous (fun t : ℝ => iteratedFDeriv ℝ 2 A t) :=
          hAC2.continuous_iteratedFDeriv (by exact_mod_cast (by norm_num : (2 : ℕ) ≤ 2))
        obtain ⟨B2_compact, hB2_compact⟩ :=
          (isCompact_Icc (a := c / 2) (b := c + 1)).exists_bound_of_continuousOn
            hA2_cont.continuousOn
        have hA2_tail : ∃ B : ℝ, ∀ t : ℝ, c + 1 < t →
            ‖iteratedFDeriv ℝ 2 A t‖ ≤ B := by
          sorry -- tail: A'' for t > c, bounded by eigenvalue damping
        obtain ⟨B2_tail, hB2_tail⟩ := hA2_tail
        refine ⟨max (max 0 B2_compact) B2_tail, fun t => ?_⟩
        by_cases ht_left : t < c / 2
        · have hev : A =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
            have hmem : Set.Iio (c / 2) ∈ 𝓝 t := Iio_mem_nhds ht_left
            filter_upwards [hmem] with s hs
            show smoothRightCutoff (c / 2) c s *
              resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k s = 0
            rw [smoothRightCutoff_eq_zero_of_le (by linarith : c / 2 < c) (le_of_lt hs)]; ring
          rw [(Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev 2).eq_of_nhds,
            iteratedFDeriv_const_of_ne (by norm_num : (2 : ℕ) ≠ 0), Pi.zero_apply, norm_zero]
          exact le_trans (le_max_left (0 : ℝ) _) (le_max_left _ _)
        · simp only [not_lt] at ht_left
          by_cases ht_mid : t ≤ c + 1
          · exact (hB2_compact t ⟨ht_left, ht_mid⟩).trans
              ((le_max_right (0 : ℝ) _).trans (le_max_left _ _))
          · simp only [not_le] at ht_mid
            exact (hB2_tail t ht_mid).trans (le_max_right _ _)
    obtain ⟨B_max, hB_max⟩ : ∃ B_max : ℝ, ∀ (i : ℕ), i ≤ 2 → ∀ t : ℝ,
        ‖iteratedFDeriv ℝ i A t‖ ≤ B_max := by
      obtain ⟨b0, hb0⟩ := hA_global_bounds 0 (by omega)
      obtain ⟨b1, hb1⟩ := hA_global_bounds 1 (by omega)
      obtain ⟨b2, hb2⟩ := hA_global_bounds 2 (by omega)
      refine ⟨max b0 (max b1 b2), fun i hi t => ?_⟩
      interval_cases i
      · exact (hb0 t).trans (le_max_left _ _)
      · exact (hb1 t).trans ((le_max_left _ _).trans (le_max_right _ _))
      · exact (hb2 t).trans ((le_max_right _ _).trans (le_max_right _ _))
    -- Same Leibniz assembly as hmid but with global bounds
    have hAfst : ContDiff ℝ (2 : ℕ∞) (fun q : ℝ × ℝ => A q.1) :=
      hAC2.comp contDiff_fst
    have hBsnd : ContDiff ℝ (2 : ℕ∞) (fun q : ℝ × ℝ => cosineMode k q.2) :=
      hcos.comp contDiff_snd
    have hjTop : ((j : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
      exact_mod_cast hj
    have hfactor : f = fun q : ℝ × ℝ => A q.1 * cosineMode k q.2 := by
      funext q; simp [hf_def, cutoffResolverTerm, A, mul_assoc]
    set Ctail := ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * B_max *
        ShenWork.IntervalResolverSpectralJointC2Concrete.valueCosWeight (j - i) k
    refine ⟨Ctail, fun q _hq => ?_⟩
    rw [hfactor]
    calc ‖iteratedFDeriv ℝ j (fun q : ℝ × ℝ => A q.1 * cosineMode k q.2) q‖
        ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun q : ℝ × ℝ => A q.1) q‖ *
            ‖iteratedFDeriv ℝ (j - i) (fun q : ℝ × ℝ => cosineMode k q.2) q‖ := by
          simpa [mul_assoc] using norm_iteratedFDeriv_mul_le hAfst hBsnd q hjTop
      _ ≤ Ctail := by
          apply Finset.sum_le_sum
          intro i hi
          have hik : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hiNat : i ≤ 2 := le_trans hik hjNat
          have hjiNat : j - i ≤ 2 := le_trans (Nat.sub_le j i) hjNat
          have hiCast : ((i : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
            exact_mod_cast hiNat
          have hjiCast : (((j - i : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
            exact_mod_cast hjiNat
          have hA_fst_bound : ‖iteratedFDeriv ℝ i (fun q : ℝ × ℝ => A q.1) q‖ ≤ B_max := by
            exact (norm_iteratedFDeriv_comp_fst_le hAC2 hiCast q).trans (hB_max i hiNat q.1)
          have hB_snd_bound : ‖iteratedFDeriv ℝ (j - i)
              (fun q : ℝ × ℝ => cosineMode k q.2) q‖ ≤
              ShenWork.IntervalResolverSpectralJointC2Concrete.valueCosWeight (j - i) k := by
            exact (ShenWork.IntervalResolverSpectralJointC2CutoffBounds.norm_iteratedFDeriv_comp_snd_le
              hcos hjiCast q).trans
              (ShenWork.IntervalResolverSpectralJointC2Concrete.cosineMode_iteratedFDeriv_bound
                k (j - i) q.2 hjiNat)
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hA_fst_bound (Nat.cast_nonneg _))
            hB_snd_bound (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (le_trans (norm_nonneg _) hA_fst_bound))
  obtain ⟨Cmid, hmid⟩ := hmid
  obtain ⟨Ctail, htail⟩ := htail
  have hleft' : ∀ q : ℝ × ℝ, q.1 < c / 2 →
      (fun q => ‖iteratedFDeriv ℝ j f q‖) q = 0 := hleft
  have hmid' : ∀ q : ℝ × ℝ, c / 2 ≤ q.1 → q.1 ≤ c / 2 + 1 →
      (fun q => ‖iteratedFDeriv ℝ j f q‖) q ≤ Cmid := hmid
  have htail' : ∀ q : ℝ × ℝ, c / 2 + 1 < q.1 →
      (fun q => ‖iteratedFDeriv ℝ j f q‖) q ≤ Ctail := htail
  exact bddAbove_range_of_left_mid_tail hleft' hmid' htail'

private theorem cutoffResolverMajorant_le_explicit
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (hc : 0 < c) {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p (conjugatePicardIter p u₀ 0) Bt)
    (j k : ℕ) (hj : (j : ℕ∞) ≤ 2) :
    cutoffResolverMajorant p u₀ M₀ c hc j k ≤
      cutoffResolverExplicitMajorant Bt c hc j k := by
  unfold cutoffResolverMajorant
  exact ciSup_le (fun q =>
    cutoffResolverTerm_iteratedFDeriv_le_explicit H hc j k q hj)

private theorem cutoffResolverExplicitMajorant_summable
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt)
    {c : ℝ} (hc : 0 < c) {j : ℕ} (hj : (j : ℕ∞) ≤ 2) :
    Summable (cutoffResolverExplicitMajorant Bt c hc j) := by
  classical
  have hjNat : j ≤ 2 := by exact_mod_cast hj
  let s := Finset.range (j + 1)
  change Summable (fun k : ℕ =>
    ∑ i ∈ s, (j.choose i : ℝ) *
      (if hi : (i : ℕ∞) ≤ 2 then
        resolverSmoothRightCutoffDerivBound (c / 2) c (by linarith) i hi
      else 0) *
      boundedWeightJointMajorant Bt (j - i) k)
  refine Finset.induction_on s ?_ ?_
  · simpa using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  · intro i s his hs
    have hjiNat : j - i ≤ 2 := le_trans (Nat.sub_le j i) hjNat
    have hbase : Summable (fun k : ℕ => boundedWeightJointMajorant Bt (j - i) k) :=
      H.value_summable (j - i) (by exact_mod_cast hjiNat)
    have hterm : Summable (fun k : ℕ =>
        (j.choose i : ℝ) *
          (if hi : (i : ℕ∞) ≤ 2 then
            resolverSmoothRightCutoffDerivBound (c / 2) c (by linarith) i hi
          else 0) *
          boundedWeightJointMajorant Bt (j - i) k) := by
      by_cases hi : (i : ℕ∞) ≤ 2
      · simpa [hi, mul_assoc] using
          hbase.mul_left ((j.choose i : ℝ) *
            resolverSmoothRightCutoffDerivBound (c / 2) c (by linarith) i hi)
      · simpa [hi] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
    simpa [Finset.sum_insert, his] using hterm.add hs

/-- The majorant is nonneg. -/
theorem cutoffResolverMajorant_nonneg {p : CM2Params}
    {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ} (hc : 0 < c)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    {j k : ℕ} (_hj : (j : ℕ∞) ≤ 2) :
    0 ≤ cutoffResolverMajorant p u₀ M₀ c hc j k := by
  have hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x :=
    fun t ht x hx =>
      ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_pos_of_pos
        hu₀_cont hu₀_pos ht hx
  have hbdd := cutoffResolverMajorant_bddAbove_direct
    (p := p) hc hu₀_bound hu₀_cont hu₀_pos hfloor j k _hj
  exact (norm_nonneg _).trans (le_ciSup hbdd (0, 0))

/-- The majorant is summable for each `j ≤ 2`. -/
theorem cutoffResolverMajorant_summable {p : CM2Params}
    {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ} (hc : 0 < c)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    {j : ℕ} (_hj : (j : ℕ∞) ≤ 2) :
    Summable (cutoffResolverMajorant p u₀ M₀ c hc j) := by
  obtain ⟨Bt, hBt⟩ :=
    ShenWork.Paper2.HeatResolverJointRegularity.heatSemigroup_level0_resolverJointC2Data
      (p := p) hu₀_bound hu₀_cont hu₀_pos
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    (cutoffResolverExplicitMajorant_summable hBt hc _hj)
  · have hbdd := cutoffResolverMajorant_bddAbove_of_physical
      (p := p) (u₀ := u₀) (M₀ := M₀) hc hBt j k _hj
    exact (norm_nonneg _).trans (le_ciSup hbdd (0, 0))
  · exact cutoffResolverMajorant_le_explicit
      (p := p) (u₀ := u₀) (M₀ := M₀) hc hBt j k _hj

/-- The majorant bounds the iterated derivatives of the cutoff resolver term. -/
theorem cutoffResolverTerm_iteratedFDeriv_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    {c : ℝ} (hc : 0 < c) (j k : ℕ) (q : ℝ × ℝ)
    (hj : (j : ℕ∞) ≤ 2) :
    ‖iteratedFDeriv ℝ j
      (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q‖ ≤
      cutoffResolverMajorant p u₀ M₀ c hc j k := by
  have hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x :=
    fun t ht x hx =>
      ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_pos_of_pos
        hu₀_cont hu₀_pos ht hx
  have hbdd := cutoffResolverMajorant_bddAbove_direct
    (p := p) hc hu₀_bound hu₀_cont hu₀_pos hfloor j k hj
  exact le_ciSup hbdd q

/-! ### Global C² of the cutoff series (mechanical from contDiff_tsum) -/

/-- **Global C² of the cutoff resolver series.**

The series `(t,x) ↦ ∑' k, φ(t) · resolverTimeCoeff p u k t · cos(kπx)` is
`ContDiff ℝ 2` as a function `ℝ² → ℝ`.  The proof uses `contDiff_tsum` with the
majorant from `cutoffResolverTerm_iteratedFDeriv_bound`. -/
theorem cutoffResolverSeries_contDiff_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
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
    exact cutoffResolverMajorant_summable hc hu₀_bound hu₀_cont hu₀_pos hj
  -- (3) Uniform iterated-derivative bound
  · intro j k q hj
    exact cutoffResolverTerm_iteratedFDeriv_bound hu₀_bound hu₀_cont hu₀_pos hc j k q hj

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
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
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
    hu₀_bound hu₀_cont hu₀_pos hfloor hc).contDiffAt (x := (s₀, x₀))
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
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    (_hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {c : ℝ} (hc : 0 < c) {s₀ x₀ : ℝ} (hs₀ : c < s₀)
    (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
        (fun q : ℝ × ℝ =>
          deriv (intervalDomainLift (coupledChemicalConcentration p
            (conjugatePicardIter p u₀ 0) q.1)) q.2)
        (s₀, x₀) := by
  obtain ⟨Bt, hBt⟩ :=
    ShenWork.Paper2.HeatResolverJointRegularity.heatSemigroup_level0_resolverJointC2Data
      (p := p) hu₀_bound hu₀_cont hu₀_pos
  exact ShenWork.IntervalResolverJointC2PhysicalConcrete.coupledChemical_grad_jointContDiffAt_two
    hBt hx₀

#print axioms heatResolver_jointContDiffAt_two

end ShenWork.Paper2.HeatResolverJointC2Direct

end -- noncomputable section
