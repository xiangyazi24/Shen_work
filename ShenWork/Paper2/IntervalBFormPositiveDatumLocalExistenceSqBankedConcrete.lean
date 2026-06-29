import ShenWork.Paper2.IntervalBFormPositiveDatumLocalExistenceSqBanked
import ShenWork.Paper2.IntervalMildRegularityFrontierAssembly
import ShenWork.Paper2.IntervalResolverStrictPositivity
import ShenWork.Paper2.IntervalResolverWeakBounds

open Set Filter Topology MeasureTheory

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData ConjugateMildSolutionData
   conjugateMildSolutionData_of_data conjugatePicardLimit)
open ShenWork.IntervalMildToClassical
  (mildChemicalConcentration)
open ShenWork.IntervalMildTimeDerivContinuity
  (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalResolverDirectTimeRegularity
  (HasResolverDirectSpectralData)
open ShenWork.IntervalDuhamelClosedC2
  (DuhamelSourceTimeC1)
open ShenWork.PDE
  (intervalNeumannResolverR intervalNeumannResolverSourceCoeff)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs)
open ShenWork.IntervalDomainResolverStrictPos
  (cosineCoeffs_const resolverR_pos_of_representation)
open ShenWork.IntervalResolverWeakBounds
  (resolverGrad_sup_le_of_bounded resolverSourceCoeff_re_sq_summable_of_continuousOn)
open ShenWork.IntervalPicardLimitCoeffConv
  (cosineCoeffs_sub_eq)
open ShenWork.Paper2
open ShenWork.Paper2.BFormPositiveDatumNegPart
open scoped Topology BigOperators

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumLocalSq

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

private theorem continuousOn_intervalDomainLift_of_continuous
    {g : intervalDomainPoint → ℝ} (hg : Continuous g) :
    ContinuousOn (intervalDomainLift g) (Set.Icc (0 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_restrict]
  have hres :
      Set.restrict (Set.Icc (0 : ℝ) 1) (intervalDomainLift g) = g := by
    funext z
    obtain ⟨z, hz⟩ := z
    change intervalDomainLift g z = g ⟨z, hz⟩
    rw [intervalDomainLift, dif_pos hz]
  rw [hres]
  exact hg

/-- Strict resolver positivity for the B-form Picard limit.  This is the same
resolver positivity argument as `IntervalResolverStrictPositivity`, but it reads
the positivity, boundedness, and continuity fields from
`conjugateMildSolutionData_of_data`, so no gradient-mild bridge is needed. -/
theorem bform_mildChemicalConcentration_pos_of_conjugate_data
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) :
    ∀ t, 0 < t → t < DB.T → ∀ x : intervalDomainPoint,
      0 < mildChemicalConcentration p
        (conjugatePicardLimit p u₀ DB.T) t x := by
  intro t ht htT x
  let D : ConjugateMildSolutionData p u₀ := conjugateMildSolutionData_of_data DB
  have htT' : t ≤ D.T := by
    change t ≤ DB.T
    exact le_of_lt htT
  set g₀ : intervalDomainPoint → ℝ := D.u t with hg₀
  have hg₀_cont : Continuous g₀ := D.hcont t ht htT'
  set cs : ℝ → ℝ := g₀ ∘ clip with hcs
  have hcs_cont : Continuous cs := hg₀_cont.comp clip_continuous
  have hagree : ∀ y ∈ Set.Icc (0:ℝ) 1,
      intervalDomainLift g₀ y = cs y := fun y hy =>
    (clip_comp_eq_lift_on_Icc g₀ hy).symm
  have hIcc_ne : (Set.Icc (0:ℝ) 1).Nonempty := ⟨0, by norm_num⟩
  obtain ⟨x₀, hx₀mem, hx₀min⟩ :=
    isCompact_Icc.exists_isMinOn hIcc_ne hcs_cont.continuousOn
  set m : ℝ := cs x₀ with hm
  have hcs_lb : ∀ y ∈ Set.Icc (0:ℝ) 1, m ≤ cs y := fun y hy => hx₀min hy
  have hm_pos : 0 < m := by
    rw [hm, hcs, Function.comp]
    exact D.hpos t ht htT' (clip x₀)
  have hcs_ub : ∀ y ∈ Set.Icc (0:ℝ) 1, cs y ≤ D.M := fun y hy => by
    rw [hcs, Function.comp]
    have : g₀ (clip y) ≤ |g₀ (clip y)| := le_abs_self _
    exact le_trans this (D.hbound t ht htT' (clip y))
  have hUcont : ContinuousOn (intervalDomainLift g₀) (Set.Icc (0:ℝ) 1) :=
    continuousOn_intervalDomainLift_of_continuous hg₀_cont
  have hsrc_coeff : ∀ k,
      cosineCoeffs (fun y => p.ν * intervalDomainLift g₀ y ^ p.γ) k
        = (intervalNeumannResolverSourceCoeff p g₀ k).re := by
    intro k
    simp [cosineCoeffs, intervalNeumannResolverSourceCoeff, Complex.ofReal_re]
  have hâ : Summable (fun k =>
      (cosineCoeffs (fun y => p.ν * intervalDomainLift g₀ y ^ p.γ) k) ^ 2) := by
    have h := resolverSourceCoeff_re_sq_summable_of_continuousOn p hUcont
    simp only [ShenWork.Paper2.intervalNeumannResolverSourceCoeff_zero, sub_zero] at h
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
          (Set.Icc (0:ℝ) 1) :=
        continuousOn_const.mul (hUcont.rpow_const (fun y _ => Or.inr p.hγ.le))
      exact cosineCoeffs_sub_eq hgc continuousOn_const k
    have hupd : (fun k =>
        (cosineCoeffs (fun y => p.ν * intervalDomainLift g₀ y ^ p.γ - c₀) k) ^ 2)
        = Function.update
            (fun k =>
              (cosineCoeffs (fun y => p.ν * intervalDomainLift g₀ y ^ p.γ) k) ^ 2)
            0
            ((cosineCoeffs (fun y => p.ν * intervalDomainLift g₀ y ^ p.γ - c₀) 0) ^ 2) := by
      funext k
      by_cases hk : k = 0
      · subst hk
        rw [Function.update_self]
      · rw [Function.update_of_ne hk, hsplit k, cosineCoeffs_const, if_neg hk, sub_zero]
    rw [hupd]
    exact hâ.update 0 _
  change 0 < intervalNeumannResolverR p (D.u t) x
  exact resolverR_pos_of_representation p hcs_cont hagree hm_pos hcs_lb hcs_ub
    hsrc_coeff hâ hĝ x

def bformConcreteResolverGradBound (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) : ℝ :=
  Real.sqrt (∑' k : ℕ, (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
    (2 * (p.ν * DB.M ^ p.γ))

def bformConcreteDriftA (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) : ℝ :=
  |p.χ₀| * bformConcreteResolverGradBound p DB

def bformConcreteDbar (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) : ℝ :=
  p.b * DB.M ^ p.α

def bformConcreteM (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) : ℝ :=
  (bformConcreteDriftA p DB) ^ 2 / 2 + bformConcreteDbar p DB

/-- The concrete drift coefficient matching the currently compiled B-form flux
`u * R_x / (1+R)^β`. -/
def bformConcreteDrift (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) : ℝ → ℝ → ℝ :=
  fun t x =>
    -p.χ₀ *
      ShenWork.Paper2.resolverGradReal p
        ((conjugatePicardLimit p u₀ DB.T) t) x /
      (1 +
        intervalDomainLift
          (intervalNeumannResolverR p ((conjugatePicardLimit p u₀ DB.T) t)) x) ^ p.β

def bformConcreteReact (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) : ℝ → ℝ → ℝ :=
  fun t x => p.a - p.b *
    (intervalDomainLift ((conjugatePicardLimit p u₀ DB.T) t) x) ^ p.α

private theorem bformConcreteResolverGradBound_nonneg
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) :
    0 ≤ bformConcreteResolverGradBound p DB := by
  unfold bformConcreteResolverGradBound
  have hMnn : 0 ≤ DB.M := le_of_lt DB.hM
  exact mul_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg (by norm_num)
      (mul_nonneg p.hν.le (Real.rpow_nonneg hMnn p.γ)))

theorem bformConcreteM_nonneg
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) :
    0 ≤ bformConcreteM p DB := by
  unfold bformConcreteM bformConcreteDbar
  have hMnn : 0 ≤ DB.M := le_of_lt DB.hM
  have hDnn : 0 ≤ p.b * DB.M ^ p.α :=
    mul_nonneg p.hb (Real.rpow_nonneg hMnn p.α)
  nlinarith [sq_nonneg (bformConcreteDriftA p DB)]

theorem bformConcreteM_closes
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) :
    (bformConcreteDriftA p DB) ^ 2 / 2 + bformConcreteDbar p DB ≤
      bformConcreteM p DB := by
  rfl

private theorem bformConcreteDrift_bound
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) :
    ∀ s x, 0 < s → s < DB.T →
      x ∈ Set.Ioo (0 : ℝ) 1 →
        |bformConcreteDrift p DB s x| ≤ bformConcreteDriftA p DB := by
  intro s x hs hsT hxIoo
  let D : ConjugateMildSolutionData p u₀ := conjugateMildSolutionData_of_data DB
  have hsTle : s ≤ D.T := by
    change s ≤ DB.T
    exact le_of_lt hsT
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hxIoo.1, le_of_lt hxIoo.2⟩
  set u : intervalDomainPoint → ℝ := (conjugatePicardLimit p u₀ DB.T) s with hu
  have hu_cont : Continuous u := by
    change Continuous (D.u s)
    exact D.hcont s hs hsTle
  have hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0:ℝ) 1) :=
    continuousOn_intervalDomainLift_of_continuous hu_cont
  have hlb : ∀ y ∈ Set.Icc (0:ℝ) 1, 0 ≤ intervalDomainLift u y := by
    intro y hy
    change 0 ≤ intervalDomainLift (D.u s) y
    rw [intervalDomainLift, dif_pos hy]
    exact D.hnonneg s hs hsTle ⟨y, hy⟩
  have hub : ∀ y ∈ Set.Icc (0:ℝ) 1, intervalDomainLift u y ≤ DB.M := by
    intro y hy
    have h₁ : intervalDomainLift u y ≤ |intervalDomainLift u y| := le_abs_self _
    have h₂ : |intervalDomainLift u y| ≤ DB.M := by
      change |intervalDomainLift (D.u s) y| ≤ D.M
      rw [intervalDomainLift, dif_pos hy]
      exact D.hbound s hs hsTle ⟨y, hy⟩
    exact le_trans h₁ h₂
  have hgrad :
      |ShenWork.Paper2.resolverGradReal p u x| ≤
        bformConcreteResolverGradBound p DB := by
    simpa [bformConcreteResolverGradBound, hu] using
      resolverGrad_sup_le_of_bounded p hUcont hlb hub (x := x) hxIcc
  have hRpos :
      0 < intervalDomainLift (intervalNeumannResolverR p u) x := by
    change 0 <
      intervalDomainLift
        (intervalNeumannResolverR p ((conjugatePicardLimit p u₀ DB.T) s)) x
    have hv := bform_mildChemicalConcentration_pos_of_conjugate_data p DB
      s hs hsT ⟨x, hxIcc⟩
    rw [intervalDomainLift, dif_pos hxIcc]
    exact hv
  set denom : ℝ :=
    (1 + intervalDomainLift (intervalNeumannResolverR p u) x) ^ p.β with hdenom
  have hden_ge_one : 1 ≤ denom := by
    rw [hdenom]
    have hbase : 1 ≤ 1 + intervalDomainLift (intervalNeumannResolverR p u) x := by
      linarith
    exact Real.one_le_rpow hbase p.hβ
  have hden_pos : 0 < denom :=
    lt_of_lt_of_le zero_lt_one hden_ge_one
  have hGnn : 0 ≤ bformConcreteResolverGradBound p DB :=
    bformConcreteResolverGradBound_nonneg p DB
  have hnum_nonneg : 0 ≤ |p.χ₀| * bformConcreteResolverGradBound p DB :=
    mul_nonneg (abs_nonneg _) hGnn
  calc
    |bformConcreteDrift p DB s x|
        = |(-p.χ₀ * ShenWork.Paper2.resolverGradReal p u x) / denom| := by
          simp [bformConcreteDrift, hu, hdenom]
    _ = |p.χ₀| * |ShenWork.Paper2.resolverGradReal p u x| / denom := by
          rw [abs_div, abs_of_pos hden_pos, abs_mul, abs_neg]
    _ ≤ |p.χ₀| * bformConcreteResolverGradBound p DB /
            denom := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hgrad (abs_nonneg _)) hden_pos.le
    _ ≤ |p.χ₀| * bformConcreteResolverGradBound p DB := by
          rw [div_le_iff₀ hden_pos]
          calc
            |p.χ₀| * bformConcreteResolverGradBound p DB
                ≤ |p.χ₀| * bformConcreteResolverGradBound p DB *
                    denom := by
                  simpa [mul_one] using
                    (mul_le_mul_of_nonneg_left hden_ge_one hnum_nonneg)

private theorem bformConcreteReact_bound
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) :
    ∀ s x, 0 < s → s < DB.T →
      x ∈ Set.Ioo (0 : ℝ) 1 →
        -bformConcreteReact p DB s x ≤ bformConcreteDbar p DB := by
  intro s x hs hsT hxIoo
  let D : ConjugateMildSolutionData p u₀ := conjugateMildSolutionData_of_data DB
  have hsTle : s ≤ D.T := by
    change s ≤ DB.T
    exact le_of_lt hsT
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hxIoo.1, le_of_lt hxIoo.2⟩
  have hu_nonneg :
      0 ≤ intervalDomainLift ((conjugatePicardLimit p u₀ DB.T) s) x := by
    change 0 ≤ intervalDomainLift (D.u s) x
    rw [intervalDomainLift, dif_pos hxIcc]
    exact D.hnonneg s hs hsTle ⟨x, hxIcc⟩
  have hu_le :
      intervalDomainLift ((conjugatePicardLimit p u₀ DB.T) s) x ≤ DB.M := by
    have h₁ :
        intervalDomainLift ((conjugatePicardLimit p u₀ DB.T) s) x ≤
          |intervalDomainLift ((conjugatePicardLimit p u₀ DB.T) s) x| :=
      le_abs_self _
    have h₂ :
        |intervalDomainLift ((conjugatePicardLimit p u₀ DB.T) s) x| ≤ DB.M := by
      change |intervalDomainLift (D.u s) x| ≤ D.M
      rw [intervalDomainLift, dif_pos hxIcc]
      exact D.hbound s hs hsTle ⟨x, hxIcc⟩
    exact le_trans h₁ h₂
  have hpow :
      (intervalDomainLift ((conjugatePicardLimit p u₀ DB.T) s) x) ^ p.α
        ≤ DB.M ^ p.α :=
    Real.rpow_le_rpow hu_nonneg hu_le p.hα.le
  unfold bformConcreteReact bformConcreteDbar
  have hmul :
      p.b *
          (intervalDomainLift ((conjugatePicardLimit p u₀ DB.T) s) x) ^ p.α
        ≤ p.b * DB.M ^ p.α :=
    mul_le_mul_of_nonneg_left hpow p.hb
  linarith [p.ha, hmul]

theorem bformConcreteDrift_bound_restart
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) :
    ∀ τ, 0 < τ → τ < DB.T →
      ∀ s x, 0 < s → s < DB.T - τ →
        x ∈ Set.Ioo (0 : ℝ) 1 →
          |bformConcreteDrift p DB (τ + s) x| ≤ bformConcreteDriftA p DB := by
  intro τ hτ hτT s x hs hsL hx
  exact bformConcreteDrift_bound p DB (τ + s) x
    (by linarith) (by linarith) hx

theorem bformConcreteReact_bound_restart
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) :
    ∀ τ, 0 < τ → τ < DB.T →
      ∀ s x, 0 < s → s < DB.T - τ →
        x ∈ Set.Ioo (0 : ℝ) 1 →
          -bformConcreteReact p DB (τ + s) x ≤ bformConcreteDbar p DB := by
  intro τ hτ hτT s x hs hsL hx
  exact bformConcreteReact_bound p DB (τ + s) x
    (by linarith) (by linarith) hx

structure PositiveDatumBFormSqBankedConcreteHypotheses
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) where
  bank :
    ShenWork.Paper2.BFormDirectClassical.BFormBankedInputs p DB
  hTimeNhd :
    HasTimeNeighborhoodSpectralAgreement DB.T
      (conjugatePicardLimit p u₀ DB.T)
  hResolverCoeffTimeC1 :
    ∀ t₀, 0 < t₀ → t₀ < DB.T →
      ∃ (aC : ℝ → ℕ → ℝ) (_ : DuhamelSourceTimeC1 aC) (W : Set ℝ),
        W ∈ 𝓝 t₀ ∧
        (∀ s ∈ W, ∀ k,
          aC s k =
            (intervalNeumannResolverSourceCoeff p
              ((conjugatePicardLimit p u₀ DB.T) s) k).re)
  DT : TruncatedConjugateMildExistenceData p u₀
  Hbridge : TruncatedConjugateLimitBridge p DB DT
  HmildWeak : TruncatedMildToWeakAvailable p DB
  Henergy : NegativePartEnergyCoreData p DB
  hLinearStripCore :
    ∀ τ, 0 < τ → τ < DB.T →
      NeumannLinearDriftCoefficientsRegular (DB.T - τ)
        (restartTimeShift τ (bformConcreteDrift p DB))
        (restartTimeShift τ (bformConcreteReact p DB)) ∧
      IsClassicalNeumannLinearDriftSuperSolution (DB.T - τ)
        (restartTimeShift τ (bformConcreteDrift p DB))
        (restartTimeShift τ (bformConcreteReact p DB))
        (restartTimeShift τ (bformConjugatePicardLift p DB))

/-- Assemble the old banked plumbing with the concrete fields discharged:
resolver positivity, resolver spectral data, `A/Dbar/M`, and the two numeric
coefficient bounds are produced here from the bounded B-form Picard solution
and the weak resolver-gradient bound. -/
def positiveDatumBFormSqBankedPlumbing_of_solution
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (H : PositiveDatumBFormSqBankedConcreteHypotheses p DB) :
    PositiveDatumBFormSqBankedPlumbing p DB where
  bank := H.bank
  hTimeNhd := H.hTimeNhd
  hResolverData :=
    ShenWork.Paper2.RegularityFrontierAssembly.hasResolverDirectSpectralData_of_clamped_perT0
      (p := p) (T := DB.T) (u := conjugatePicardLimit p u₀ DB.T)
      H.hResolverCoeffTimeC1
  hVpos := bform_mildChemicalConcentration_pos_of_conjugate_data p DB
  DT := H.DT
  Hbridge := H.Hbridge
  HmildWeak := H.HmildWeak
  Henergy := H.Henergy
  A := bformConcreteDriftA p DB
  Dbar := bformConcreteDbar p DB
  M := bformConcreteM p DB
  hM_nonneg := bformConcreteM_nonneg p DB
  hM := bformConcreteM_closes p DB
  drift := bformConcreteDrift p DB
  react := bformConcreteReact p DB
  hstrip := by
    intro τ hτ hτT
    obtain ⟨hreg, hsuper⟩ := H.hLinearStripCore τ hτ hτT
    exact ⟨hreg, hsuper,
      bformConcreteDrift_bound_restart p DB τ hτ hτT,
      bformConcreteReact_bound_restart p DB τ hτ hτT⟩

theorem hbanked_concrete_of_deep_hypotheses
    {p : CM2Params}
    (hdeep :
      ∀ u₀ : intervalDomainPoint → ℝ,
        PaperPositiveInitialDatum intervalDomain u₀ →
          ∃ DB : ConjugateMildExistenceData p u₀,
            Nonempty (PositiveDatumBFormSqBankedConcreteHypotheses p DB)) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PaperPositiveInitialDatum intervalDomain u₀ →
        ∃ DB : ConjugateMildExistenceData p u₀,
          Nonempty (PositiveDatumBFormSqBankedPlumbing p DB) := by
  intro u₀ hu₀
  rcases hdeep u₀ hu₀ with ⟨DB, ⟨H⟩⟩
  exact ⟨DB, ⟨positiveDatumBFormSqBankedPlumbing_of_solution H⟩⟩

theorem paper2_theorem_1_1_general_chi_bformSq_of_concrete_banked
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hdeep :
      ∀ u₀ : intervalDomainPoint → ℝ,
        PaperPositiveInitialDatum intervalDomain u₀ →
          ∃ DB : ConjugateMildExistenceData p u₀,
            Nonempty (PositiveDatumBFormSqBankedConcreteHypotheses p DB))
    (hUniform : IntervalDomainUniformLocalExistence p) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bformSq_of_banked
    p hχ ha hb hγ_ge_one
    (hbanked_concrete_of_deep_hypotheses hdeep)
    hUniform

end ShenWork.Paper2.BFormPositiveDatumLocalSq
