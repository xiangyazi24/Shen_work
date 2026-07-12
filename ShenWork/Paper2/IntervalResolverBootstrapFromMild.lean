import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.Paper2.IntervalMildToClassical
import ShenWork.Paper2.IntervalResolverDirectTimeRegularity
import ShenWork.Paper2.IntervalDomainResolverStrictPos
import ShenWork.Paper2.IntervalResolverWeakBounds
import ShenWork.PDE.IntervalResolverGradientBridge

open Set Filter Topology MeasureTheory
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalConjugatePicard (ConjugateMildSolutionData)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalResolverDirectTimeRegularity (HasResolverDirectSpectralData)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalDomainResolverStrictPos
  (cosineCoeffs_const resolverR_pos_of_representation)
open ShenWork.IntervalResolverWeakBounds
  (resolverSourceCoeff_re_sq_summable_of_continuousOn)
open ShenWork.IntervalPicardLimitCoeffConv (cosineCoeffs_sub_eq)
open ShenWork.IntervalResolverGradientBridge (resolverCoeff_re_eq resolverR_apply_eq)
open ShenWork.PDE
  (intervalNeumannResolverR intervalNeumannResolverSourceCoeff
   intervalNeumannResolverWeight)
open ShenWork.Paper2 (intervalNeumannResolverSourceCoeff_zero)

noncomputable section

namespace ShenWork.Paper2.IntervalResolverBootstrapFromMild

private def clip : ℝ → intervalDomainPoint := fun x =>
  ⟨max 0 (min x 1), le_max_left 0 _, max_le (by norm_num) (min_le_right x 1)⟩

private theorem clip_continuous : Continuous clip :=
  Continuous.subtype_mk
    (continuous_const.max (continuous_id.min continuous_const)) _

private theorem clip_comp_eq_lift_on_Icc (g : intervalDomainPoint → ℝ)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (g ∘ clip) x = intervalDomainLift g x := by
  have hclip_eq : max 0 (min x 1) = x := by
    rw [min_eq_left hx.2, max_eq_right hx.1]
  simp only [Function.comp, clip, intervalDomainLift, dif_pos hx]
  exact congrArg g (Subtype.ext hclip_eq)

/-- Strict positivity of the elliptic resolver for a B-form mild solution slice. -/
theorem hResolverPos_of_conjugateMild
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀) :
    ∀ t, 0 < t → t < S.T → ∀ x : intervalDomainPoint,
      0 < mildChemicalConcentration p S.u t x := by
  intro t ht htT x
  have htT' : t ≤ S.T := le_of_lt htT
  set g₀ : intervalDomainPoint → ℝ := S.u t with hg₀
  have hg₀_cont : Continuous g₀ := S.hcont t ht htT'
  set cs : ℝ → ℝ := g₀ ∘ clip with hcs
  have hcs_cont : Continuous cs := hg₀_cont.comp clip_continuous
  have hagree : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift g₀ y = cs y := fun y hy =>
    (clip_comp_eq_lift_on_Icc g₀ hy).symm
  have hIcc_ne : (Set.Icc (0 : ℝ) 1).Nonempty := ⟨0, by norm_num⟩
  obtain ⟨x₀, hx₀mem, hx₀min⟩ :=
    isCompact_Icc.exists_isMinOn hIcc_ne hcs_cont.continuousOn
  set m : ℝ := cs x₀ with hm
  have hcs_lb : ∀ y ∈ Set.Icc (0 : ℝ) 1, m ≤ cs y := fun y hy => hx₀min hy
  have hm_pos : 0 < m := by
    rw [hm, hcs, Function.comp]
    exact S.hpos t ht htT' (clip x₀)
  have hcs_ub : ∀ y ∈ Set.Icc (0 : ℝ) 1, cs y ≤ S.M := fun y hy => by
    rw [hcs, Function.comp]
    have : g₀ (clip y) ≤ |g₀ (clip y)| := le_abs_self _
    exact le_trans this (S.hbound t ht htT' (clip y))
  have hsrc_coeff : ∀ k,
      cosineCoeffs (fun y => p.ν * intervalDomainLift g₀ y ^ p.γ) k
        = (intervalNeumannResolverSourceCoeff p g₀ k).re := by
    intro k
    simp [cosineCoeffs, intervalNeumannResolverSourceCoeff, Complex.ofReal_re]
  have hUcont : ContinuousOn (intervalDomainLift g₀) (Set.Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have hres : Set.restrict (Set.Icc (0 : ℝ) 1) (intervalDomainLift g₀) = g₀ := by
      funext z
      obtain ⟨z, hz⟩ := z
      show intervalDomainLift g₀ z = g₀ ⟨z, hz⟩
      rw [intervalDomainLift, dif_pos hz]
    rw [hres]
    exact hg₀_cont
  have hâ : Summable (fun k =>
      (cosineCoeffs (fun y => p.ν * intervalDomainLift g₀ y ^ p.γ) k) ^ 2) := by
    have h := resolverSourceCoeff_re_sq_summable_of_continuousOn p hUcont
    simp only [intervalNeumannResolverSourceCoeff_zero, sub_zero] at h
    exact h.congr (fun k => by rw [hsrc_coeff k])
  set c₀ : ℝ := p.ν * m ^ p.γ with hc₀def
  have hĝ : Summable (fun k =>
      (cosineCoeffs (fun y => p.ν * intervalDomainLift g₀ y ^ p.γ - c₀) k) ^ 2) := by
    have hsplit : ∀ k,
        cosineCoeffs (fun y => p.ν * intervalDomainLift g₀ y ^ p.γ - c₀) k
          = cosineCoeffs (fun y => p.ν * intervalDomainLift g₀ y ^ p.γ) k
            - cosineCoeffs (fun _ => c₀) k := by
      intro k
      have hgc : ContinuousOn (fun y => p.ν * intervalDomainLift g₀ y ^ p.γ)
          (Set.Icc (0 : ℝ) 1) :=
        continuousOn_const.mul (hUcont.rpow_const (fun y _ => Or.inr p.hγ.le))
      exact cosineCoeffs_sub_eq hgc continuousOn_const k
    have hupd : (fun k =>
        (cosineCoeffs (fun y => p.ν * intervalDomainLift g₀ y ^ p.γ - c₀) k) ^ 2)
        = Function.update
            (fun k => (cosineCoeffs
              (fun y => p.ν * intervalDomainLift g₀ y ^ p.γ) k) ^ 2)
            0
            ((cosineCoeffs
              (fun y => p.ν * intervalDomainLift g₀ y ^ p.γ - c₀) 0) ^ 2) := by
      funext k
      by_cases hk : k = 0
      · subst hk
        rw [Function.update_self]
      · rw [Function.update_of_ne hk, hsplit k, cosineCoeffs_const, if_neg hk, sub_zero]
    rw [hupd]
    exact hâ.update 0 _
  show 0 < intervalNeumannResolverR p (S.u t) x
  exact resolverR_pos_of_representation p hcs_cont hagree hm_pos hcs_lb hcs_ub
    hsrc_coeff hâ hĝ x

/-- Exact residual needed for resolver spectral data from a bare B-form mild record. -/
def ResolverSourceWitnessFromMild
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀) : Prop :=
  ∀ t₀, 0 < t₀ → t₀ < S.T →
    ∃ (aC : ℝ → ℕ → ℝ) (_ : DuhamelSourceTimeC1 aC) (W : Set ℝ),
      W ∈ 𝓝 t₀ ∧
      (∀ s ∈ W, ∀ k,
        aC s k = (intervalNeumannResolverSourceCoeff p (S.u s) k).re)

/-- Algebraic resolver reconstruction from canonical source coefficients. -/
theorem mildChemicalConcentration_eq_sourceWeight_series
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (s : ℝ)
    (x : intervalDomainPoint) :
    mildChemicalConcentration p u s x =
      ∑' k, (intervalNeumannResolverSourceCoeff p (u s) k).re *
        intervalNeumannResolverWeight p k * cosineMode k x.1 := by
  simp only [mildChemicalConcentration, resolverR_apply_eq, cosineMode]
  refine tsum_congr (fun k => ?_)
  rw [resolverCoeff_re_eq, intervalNeumannResolverWeight]
  ring

/-- Resolver direct spectral data from the per-interior-time source witness. -/
theorem hResolverData_of_sourceWitness
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {S : ConjugateMildSolutionData p u₀}
    (H : ResolverSourceWitnessFromMild p S) :
    HasResolverDirectSpectralData S.T
      (mildChemicalConcentration p S.u) p := by
  unfold HasResolverDirectSpectralData
  intro t₀ ht₀ ht₀T
  obtain ⟨aC, src, W, hW_nhds, hW_agree⟩ := H t₀ ht₀ ht₀T
  refine ⟨aC, src, ?_⟩
  filter_upwards [hW_nhds] with s hs x
  rw [mildChemicalConcentration_eq_sourceWeight_series p S.u s x]
  refine tsum_congr (fun k => ?_)
  rw [hW_agree s hs k]

/-- The two resolver fields required by the mild spectral bootstrap record. -/
structure ResolverBootstrapFromMildData
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀) : Prop where
  hResolverData : HasResolverDirectSpectralData S.T
    (mildChemicalConcentration p S.u) p
  hResolverPos : ∀ t, 0 < t → t < S.T → ∀ x : intervalDomainPoint,
    0 < mildChemicalConcentration p S.u t x

/-- The two resolver fields required by `BFormMildSpectralBootstrapData`. -/
def resolverFields_of_sourceWitness
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    (H : ResolverSourceWitnessFromMild p S) :
    ResolverBootstrapFromMildData p S where
  hResolverData := hResolverData_of_sourceWitness H
  hResolverPos := hResolverPos_of_conjugateMild p S

end ShenWork.Paper2.IntervalResolverBootstrapFromMild
