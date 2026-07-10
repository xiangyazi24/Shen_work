/-
  ShenWork/Paper2/IntervalResolverSourceWindowHuPowerK1Producer.lean

  Produce the remaining power-source K1 fields in
  `ResolverSourceWindowHuNoEnvelopeInputs` directly from the u-side
  time-neighborhood spectral agreement.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalHuRestartCoeffFiniteCoverProducer
import ShenWork.PDE.IntervalMildFrontierFromSpectral
import ShenWork.Paper2.IntervalDomainPositiveWindowK1OnEndpoint

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalMildTimeDerivContinuity (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalMildPicardRegularity
  (cosineCoeffs_abs_le_of_continuous_bounded cosineCoeffs_hasDerivAt_of_smooth_param)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDomainPositiveWindowK1OnEndpoint
  (cosineCoeffs_continuousOn_of_jointContinuousOn_Icc)

noncomputable section

namespace ShenWork.Paper2.ResolverSourceWindowInput

/-- The power source slice `ν * u(t,x)^γ`. -/
def resolverPowerHuSlice (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (σ x : ℝ) : ℝ :=
  p.ν * (intervalDomainLift (u σ) x) ^ p.γ

/-- The pointwise time derivative of `resolverPowerHuSlice`, written with
Lean's `deriv` of the lifted solution. -/
def resolverPowerHuDerivSlice (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (σ x : ℝ) : ℝ :=
  p.ν * p.γ * (intervalDomainLift (u σ) x) ^ (p.γ - 1) *
    deriv (fun r => intervalDomainLift (u r) x) σ

/-- The power-source K1 derivative coefficients extracted from `Hu`. -/
def resolverPowerHuAdotPow (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (σ : ℝ) (k : ℕ) : ℝ :=
  cosineCoeffs (resolverPowerHuDerivSlice p u σ) k

private theorem lift_pos_of_gradient_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    {σ x : ℝ} (hσ0 : 0 < σ) (hσT : σ < D.T)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 < intervalDomainLift (D.u σ) x := by
  simpa [intervalDomainLift, hx] using
    D.hpos σ hσ0 hσT.le ⟨x, hx⟩

/-- Joint continuity of the Hu power-derivative slice on the closed spatial
slab. -/
theorem resolverPowerHuDerivSlice_continuousOn_closed
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u) :
    ContinuousOn (Function.uncurry (resolverPowerHuDerivSlice p D.u))
      (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hlift : ContinuousOn
      (Function.uncurry (fun σ x => intervalDomainLift (D.u σ) x))
      (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1) :=
    ShenWork.IntervalMildFrontierFromSpectral.mildSolution_jointContinuousOn_closed Hu
  have htime : ContinuousOn
      (Function.uncurry
        (fun σ x => deriv (fun r => intervalDomainLift (D.u r) x) σ))
      (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1) :=
    ShenWork.IntervalMildFrontierFromSpectral.mildSolution_timeDeriv_jointContinuousOn_closed Hu
  have hpow : ContinuousOn
      (fun q : ℝ × ℝ => (intervalDomainLift (D.u q.1) q.2) ^ (p.γ - 1))
      (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1) := by
    refine ContinuousOn.rpow_const hlift ?_
    intro q hq
    obtain ⟨hσ, hx⟩ := Set.mem_prod.mp hq
    exact Or.inl (ne_of_gt (lift_pos_of_gradient_data D hσ.1 hσ.2 hx))
  have hfactor : ContinuousOn
      (fun q : ℝ × ℝ =>
        p.ν * p.γ * (intervalDomainLift (D.u q.1) q.2) ^ (p.γ - 1))
      (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1) :=
    (continuousOn_const.mul continuousOn_const).mul hpow
  exact (hfactor.mul htime).congr
    (by
      intro q hq
      simp [resolverPowerHuDerivSlice, Function.uncurry])

private theorem resolverPowerHuSlice_continuousOn_of_mem
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    {Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u}
    {σ : ℝ} (hσ : σ ∈ Set.Ioo (0 : ℝ) D.T) :
    ContinuousOn (resolverPowerHuSlice p D.u σ) (Set.Icc (0 : ℝ) 1) := by
  have hlift_joint : ContinuousOn
      (Function.uncurry (fun σ x => intervalDomainLift (D.u σ) x))
      (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1) :=
    ShenWork.IntervalMildFrontierFromSpectral.mildSolution_jointContinuousOn_closed Hu
  have hlift_sec : ContinuousOn (fun x => intervalDomainLift (D.u σ) x)
      (Set.Icc (0 : ℝ) 1) :=
    hlift_joint.comp (continuousOn_const.prodMk continuousOn_id)
      (fun x hx => Set.mem_prod.mpr ⟨hσ, hx⟩)
  have hpow : ContinuousOn
      (fun x => (intervalDomainLift (D.u σ) x) ^ p.γ)
      (Set.Icc (0 : ℝ) 1) := by
    refine ContinuousOn.rpow_const hlift_sec ?_
    intro x hx
    exact Or.inl (ne_of_gt (lift_pos_of_gradient_data (x := x) D hσ.1 hσ.2 hx))
  exact continuousOn_const.mul hpow

private theorem intervalDomainLift_hasDerivAt_time_from_Hu
    {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u)
    {σ x : ℝ} (hσ0 : 0 < σ) (hσT : σ < D.T)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (fun r => intervalDomainLift (D.u r) x)
      (deriv (fun r => intervalDomainLift (D.u r) x) σ) σ := by
  obtain ⟨a₀, M, hM, ha₀, a, src, offset, hτ, hagree_nhd⟩ :=
    Hu.exists_data σ hσ0 hσT
  have hraw :=
    ShenWork.IntervalMildTimeDerivContinuity.intervalDomainLift_hasDerivAt_time
      (u := D.u) hM ha₀ src hτ hagree_nhd hx
  convert hraw using 1
  exact hraw.deriv

/-- HasDerivAt of the power-source cosine coefficient, produced directly from
`Hu`. -/
theorem resolverPowerHuAdotPow_hasDerivAt
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u)
    {σ : ℝ} (hσ0 : 0 < σ) (hσT : σ < D.T) (k : ℕ) :
    HasDerivAt
      (fun r => cosineCoeffs (resolverPowerHuSlice p D.u r) k)
      (resolverPowerHuAdotPow p D.u σ k) σ := by
  set δ : ℝ := min σ (D.T - σ) / 2 with hδdef
  have hδ1 : 0 < σ := hσ0
  have hδ2 : 0 < D.T - σ := by linarith
  have hδ : 0 < δ := by
    rw [hδdef]
    have := lt_min hδ1 hδ2
    linarith
  have hδle1 : δ ≤ σ / 2 := by
    rw [hδdef]
    have := min_le_left σ (D.T - σ)
    linarith
  have hδle2 : δ ≤ (D.T - σ) / 2 := by
    rw [hδdef]
    have := min_le_right σ (D.T - σ)
    linarith
  have hball : Metric.ball σ δ ⊆ Set.Ioo (0 : ℝ) D.T := by
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    exact ⟨by linarith [hs.1, hδle1, hσ0],
      by linarith [hs.2, hδle2, hσT]⟩
  have hslab : Set.Icc (σ - δ) (σ + δ) ⊆ Set.Ioo (0 : ℝ) D.T := by
    intro s hs
    exact ⟨by linarith [hs.1, hδle1, hσ0],
      by linarith [hs.2, hδle2, hσT]⟩
  have hf_int : ∀ᶠ s in 𝓝 σ,
      IntervalIntegrable (resolverPowerHuSlice p D.u s) volume (0 : ℝ) 1 := by
    refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ⟨hσ0, hσT⟩) ?_
    intro s hs
    have hcont := resolverPowerHuSlice_continuousOn_of_mem
      (p := p) (D := D) (Hu := Hu) hs
    exact (Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1) ▸ hcont).intervalIntegrable
  have h_diff : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball σ δ,
      HasDerivAt (fun r => resolverPowerHuSlice p D.u r x)
        (resolverPowerHuDerivSlice p D.u s x) s := by
    intro x hx s hs
    have hsIoo := hball hs
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
    have hdu := intervalDomainLift_hasDerivAt_time_from_Hu
      (p := p) (D := D) Hu hsIoo.1 hsIoo.2 hxIcc
    have hpos := lift_pos_of_gradient_data D hsIoo.1 hsIoo.2 hxIcc
    have hpow : HasDerivAt
        (fun r => (intervalDomainLift (D.u r) x) ^ p.γ)
        (deriv (fun r => intervalDomainLift (D.u r) x) s *
          p.γ * (intervalDomainLift (D.u s) x) ^ (p.γ - 1)) s :=
      hdu.rpow_const (Or.inl (ne_of_gt hpos))
    have hmul := hpow.const_mul p.ν
    refine hmul.congr_deriv ?_
    unfold resolverPowerHuDerivSlice
    ring
  have h_cont_deriv : ContinuousOn (Function.uncurry (resolverPowerHuDerivSlice p D.u))
      (Set.Icc (σ - δ) (σ + δ) ×ˢ Set.Icc (0 : ℝ) 1) :=
    (resolverPowerHuDerivSlice_continuousOn_closed (p := p) (D := D) Hu).mono
      (by
        intro q hq
        obtain ⟨hσq, hxq⟩ := Set.mem_prod.mp hq
        exact Set.mem_prod.mpr ⟨hslab hσq, hxq⟩)
  exact cosineCoeffs_hasDerivAt_of_smooth_param
    (f := resolverPowerHuSlice p D.u)
    (f' := resolverPowerHuDerivSlice p D.u)
    (τ := σ) (δ := δ) (n := k) hδ hf_int h_diff h_cont_deriv

/-- Continuity of the Hu-produced power-source derivative coefficients. -/
theorem resolverPowerHuAdotPow_continuousOn
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u)
    (k : ℕ) :
    ContinuousOn (fun σ => resolverPowerHuAdotPow p D.u σ k)
      (Set.Ioo (0 : ℝ) D.T) := by
  intro σ hσ
  obtain ⟨hσ0, hσT⟩ := hσ
  set δ : ℝ := min σ (D.T - σ) / 2 with hδdef
  have hδ1 : 0 < σ := hσ0
  have hδ2 : 0 < D.T - σ := by linarith
  have hδ : 0 < δ := by
    rw [hδdef]
    have := lt_min hδ1 hδ2
    linarith
  have hδle1 : δ ≤ σ / 2 := by
    rw [hδdef]
    have := min_le_left σ (D.T - σ)
    linarith
  have hδle2 : δ ≤ (D.T - σ) / 2 := by
    rw [hδdef]
    have := min_le_right σ (D.T - σ)
    linarith
  have hslab : Set.Icc (σ - δ) (σ + δ) ⊆ Set.Ioo (0 : ℝ) D.T := by
    intro s hs
    exact ⟨by linarith [hs.1, hδle1, hσ0],
      by linarith [hs.2, hδle2, hσT]⟩
  have hcont_slab : ContinuousOn (Function.uncurry (resolverPowerHuDerivSlice p D.u))
      (Set.Icc (σ - δ) (σ + δ) ×ˢ Set.Icc (0 : ℝ) 1) :=
    (resolverPowerHuDerivSlice_continuousOn_closed (p := p) (D := D) Hu).mono
      (by
        intro q hq
        obtain ⟨hσq, hxq⟩ := Set.mem_prod.mp hq
        exact Set.mem_prod.mpr ⟨hslab hσq, hxq⟩)
  have hcoeff_cont : ContinuousOn
      (fun r => cosineCoeffs (resolverPowerHuDerivSlice p D.u r) k)
      (Set.Icc (σ - δ) (σ + δ)) :=
    cosineCoeffs_continuousOn_of_jointContinuousOn_Icc
      (f := resolverPowerHuDerivSlice p D.u)
      (c := σ - δ) (T := σ + δ) k hcont_slab
  have hσmem : σ ∈ Set.Icc (σ - δ) (σ + δ) := ⟨by linarith, by linarith⟩
  have hI_nhds : Set.Icc (σ - δ) (σ + δ) ∈ 𝓝 σ := by
    apply Icc_mem_nhds <;> linarith
  have hcont_at :
      ContinuousAt (fun r => cosineCoeffs (resolverPowerHuDerivSlice p D.u r) k) σ :=
    (hcoeff_cont.continuousWithinAt hσmem).continuousAt hI_nhds
  exact hcont_at.continuousWithinAt

set_option maxHeartbeats 800000 in
/-- Compact-window bound for the Hu-produced power-source derivative
coefficients. -/
theorem resolverPowerHuAdotPow_window_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u) :
    ∀ a b, 0 < a → b < D.T →
      ∃ Mdot, ∀ σ ∈ Set.Icc a b, ∀ k, |resolverPowerHuAdotPow p D.u σ k| ≤ Mdot := by
  intro a b ha hb
  set K : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1 with hKdef
  have hKsub : K ⊆ Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1 := by
    intro q hq
    obtain ⟨hσ, hx⟩ := Set.mem_prod.mp hq
    exact Set.mem_prod.mpr
      ⟨⟨lt_of_lt_of_le ha hσ.1, lt_of_le_of_lt hσ.2 hb⟩, hx⟩
  have hKcompact : IsCompact K := by
    rw [hKdef]
    exact isCompact_Icc.prod isCompact_Icc
  have hcontK : ContinuousOn (Function.uncurry (resolverPowerHuDerivSlice p D.u)) K :=
    (resolverPowerHuDerivSlice_continuousOn_closed (p := p) (D := D) Hu).mono hKsub
  obtain ⟨B, hB⟩ := hKcompact.bddAbove_image hcontK.norm
  set B' := max B 0 with hB'def
  have hB'nn : 0 ≤ B' := le_max_right _ _
  have hbd : ∀ σ ∈ Set.Icc a b, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |resolverPowerHuDerivSlice p D.u σ x| ≤ B' := by
    intro σ hσ x hx
    have hmem : (σ, x) ∈ K := by
      rw [hKdef]
      exact Set.mem_prod.mpr ⟨hσ, hx⟩
    have : ‖Function.uncurry (resolverPowerHuDerivSlice p D.u) (σ, x)‖ ≤ B :=
      hB (Set.mem_image_of_mem _ hmem)
    simp only [Function.uncurry, Real.norm_eq_abs] at this
    exact le_trans this (le_max_left _ _)
  refine ⟨2 * B', fun σ hσ k => ?_⟩
  have hsec : ContinuousOn (resolverPowerHuDerivSlice p D.u σ) (Set.Icc (0 : ℝ) 1) := by
    have hmaps : Set.MapsTo (fun x : ℝ => ((σ, x) : ℝ × ℝ))
        (Set.Icc (0 : ℝ) 1) K :=
      fun x hx => by
        rw [hKdef]
        exact Set.mem_prod.mpr ⟨hσ, hx⟩
    exact hcontK.comp (continuousOn_const.prodMk continuousOn_id) hmaps
  exact cosineCoeffs_abs_le_of_continuous_bounded hsec hB'nn
    (fun x hx => hbd σ hσ x hx) k

/-- Produce the no-envelope Hu input package: the compact Hu coefficient
envelope is already produced elsewhere from `Hu`, and the remaining K1 fields
come from the closed-slab time-neighborhood spectral agreement. -/
def resolverSourceWindowHuNoEnvelopeInputs_of_timeNeighborhood
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u) :
    ResolverSourceWindowHuNoEnvelopeInputs p D Hu where
  adotPow := resolverPowerHuAdotPow p D.u
  hderivPow := fun σ hσ0 hσT k =>
    resolverPowerHuAdotPow_hasDerivAt (p := p) (D := D) Hu (σ := σ) hσ0 hσT k
  hadotPowCont := fun k =>
    resolverPowerHuAdotPow_continuousOn (p := p) (D := D) Hu k
  hMdotPow := resolverPowerHuAdotPow_window_bound (p := p) (D := D) Hu

end ShenWork.Paper2.ResolverSourceWindowInput
