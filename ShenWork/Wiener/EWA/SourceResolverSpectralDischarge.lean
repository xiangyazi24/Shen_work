/-
  ShenWork/Wiener/EWA/SourceResolverSpectralDischarge.lean

  **χ₀<0 capstone — discharging the resolver-side carried hyps of
  `realSlice_classicalRegularity` for `v = mildChemicalConcentration p (realSlice u_star)`.**

  `realSlice_classicalRegularity` (SourceClassicalRegularity.lean:120) carries three
  `v`-side resolver atoms:

    * `hdecay : ∀ t ∈ Ioo 0 T, SourceCoeffQuadraticDecay p (realSlice u_star t)`
    * `Hvpos  : ∀ t ∈ Ioo 0 T, ∀ x, 0 < mildChemicalConcentration p (realSlice u_star) t x`
    * `Hv     : HasResolverDirectSpectralData T (mildChemicalConcentration p (realSlice u_star)) p`

  Two of the three are DERIVED here from atoms `realSlice_classicalRegularity`
  ALREADY carries (the eigenvalue-ℓ¹ summability `hsumE`, the slab `realizes`
  `hrealizes`, the endpoint nonvanishing `huNE0`/`huNE1`) plus the heat-floor
  positivity atoms (`hδρ`/`hheat`/`hu_ball`, which feed `realSlice_pos`).

  Route (verified analysis): the resolver `v` solves `μ v − v_xx = u`, so
  `v̂_n = û_n/(μ+λ_n)`; division by `(μ+λ_n)` gains two derivatives.

  * **`hdecay`** (PROVED HERE): the `u`-slice cosine series is closed `C²`-Neumann on
    `[0,1]` (`intervalDomainCosineSlice_conjunct7` from `hsumE`+`hrealizes`+
    endpoint-nonvanishing, plus the genuine one-sided Neumann limits
    `intervalDomainCosineSlice_neumann_limit_{left,right}`) and strictly positive
    (`realSlice_pos`), so the source `ν·u^γ` is genuinely `C²`-Neumann and the
    UNCONDITIONAL producer `sourceCoeffQuadraticDecay_of_closedC2_neumann_slice`
    yields the quadratic decay.

  * **`Hvpos`** (PROVED HERE): the positive Neumann resolver kernel maps a source
    `≥ c₀ = ν·m^γ > 0` to a value `≥ c₀/μ > 0`
    (`resolverR_pos_of_representation`), with the globally-continuous source
    extension taken to be the `u`-slice cosine series itself (globally `C²` by
    `cosineCoeffSeries_contDiff_two`, agreeing with the lift on `[0,1]` by
    `hrealizes`).  Strict positivity comes from `realSlice_pos`, NOT a spectral fact.

  * **`Hv`** (RESIDUAL, not discharged here): the per-`t₀` resolver spectral datum
    needs a `DuhamelSourceTimeC1` of the resolver source coefficients
    `s ↦ (intervalNeumannResolverSourceCoeff p (realSlice u_star s) k).re`, i.e. the
    TIME-`C¹` quadruple (`HasDerivAt`/continuity/uniform-bound) of the source cosine
    coefficients of `s ↦ ν·(realSlice u_star s)^γ`.  That time-`C¹` datum is NOT among
    the atoms `realSlice_classicalRegularity` carries (it controls only spatial
    regularity and per-slice positivity), so it is left as a precise residual.
    See `realSlice_resolverSpectralData_residual` below.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceClassicalRegularity
import ShenWork.Wiener.EWA.SourcePositivity
import ShenWork.PDE.IntervalCoupledRegularityBootstrap
import ShenWork.Paper2.IntervalDomainResolverStrictPos
import ShenWork.Paper2.IntervalResolverWeakBounds
import ShenWork.Paper2.IntervalPicardLimitCoeffConv
import ShenWork.Paper2.IntervalMildRegularityFrontierAssembly

noncomputable section

namespace ShenWork.EWA

open ShenWork.GWA ShenWork.Wiener
open Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)
open ShenWork.Paper2 (SourceCoeffQuadraticDecay
  intervalNeumannResolverSourceCoeff_zero)
open ShenWork.IntervalResolverDirectTimeRegularity (HasResolverDirectSpectralData)
open ShenWork.IntervalCosineSliceRegularity
  (intervalDomainCosineSlice_conjunct7
   intervalDomainCosineSlice_neumann_limit_left
   intervalDomainCosineSlice_neumann_limit_right)
open ShenWork.IntervalCoupledRegularityBootstrap
  (sourceCoeffQuadraticDecay_of_closedC2_neumann_slice)
open ShenWork.IntervalDuhamelClosedC2 (cosineCoeffSeries_contDiff_two)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.PDE (intervalNeumannResolverR intervalNeumannResolverSourceCoeff)
open ShenWork.IntervalDomainResolverStrictPos (cosineCoeffs_const resolverR_pos_of_representation)
open ShenWork.IntervalResolverWeakBounds
  (resolverSourceCoeff_re_sq_summable_of_continuousOn)
open ShenWork.IntervalPicardLimitCoeffConv (cosineCoeffs_sub_eq)
open ShenWork.Paper2.RegularityFrontierAssembly
  (hasResolverDirectSpectralData_of_clamped_perT0)

variable {T : ℝ}

/-! ### Shared spatial bridges. -/

/-- The lift of `realSlice u_star t` agrees on `Icc 0 1` with the `u`-slice cosine
series (the `EqOn` form of the carried slab `realizes` at a fixed interior `t`). -/
private theorem realSlice_eqOn_cosineSeries
    (p : CM2Params) (u_star : EWA T 1) (u₀cos : ℕ → ℝ) {t : ℝ}
    (hrep : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x
        = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x) :
    Set.EqOn (intervalDomainLift (realSlice u_star t))
      (fun x => ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x)
      (Set.Icc (0 : ℝ) 1) :=
  fun x hx => hrep x hx

/-- The lift of `realSlice u_star t` is continuous on `Icc 0 1`: on `Icc` it equals
the globally-`C²` `u`-slice cosine series. -/
private theorem realSlice_lift_continuousOn_Icc
    (p : CM2Params) (u_star : EWA T 1) (u₀cos : ℕ → ℝ) {t : ℝ}
    (hsumE : Summable (fun n => unitIntervalCosineEigenvalue n *
      |fullSourceCoeff p (realSlice u_star) u₀cos t n|))
    (hrep : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x
        = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x) :
    ContinuousOn (intervalDomainLift (realSlice u_star t)) (Set.Icc (0 : ℝ) 1) :=
  ((cosineCoeffSeries_contDiff_two hsumE).continuous.continuousOn).congr
    (fun x hx => hrep x hx)

/-- The lift of `realSlice u_star t` is strictly positive on `Icc 0 1` (the genuine
heat-floor positivity `realSlice_pos`, read at the subtype point). -/
private theorem realSlice_lift_pos_Icc
    (u_star : EWA T 1) {u₀E : WA 1} {δ ρ : ℝ} (hδρ : 0 < δ - ρ)
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ)
    (hu_ball : u_star ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (realSlice u_star t) x := by
  intro x hx
  rw [intervalDomainLift, dif_pos hx]
  exact realSlice_pos hδρ hheat hu_ball ⟨ht.1.le, ht.2.le⟩ ⟨x, hx⟩

/-! ### `hdecay` — quadratic decay of the resolver source coefficients. -/

/-- **`hdecay` DISCHARGED.**  For each interior `t`, the source coefficients
`(intervalNeumannResolverSourceCoeff p (realSlice u_star t) k).re` of `ν·u^γ` have
quadratic decay `|·| ≤ C/(kπ)²`.

The `u`-slice lift is closed `C²`-Neumann on `[0,1]` and strictly positive there, so
`ν·u^γ` is genuinely `C²`-Neumann; the unconditional producer
`sourceCoeffQuadraticDecay_of_closedC2_neumann_slice` yields the decay.  All inputs
are atoms `realSlice_classicalRegularity` already carries (`hsumE`, `hrealizes`,
`huNE0`, `huNE1`) plus the heat-floor positivity atoms. -/
def realSlice_resolverDecay
    (p : CM2Params) (u_star : EWA T 1) (u₀cos : ℕ → ℝ)
    {u₀E : WA 1} {δ ρ : ℝ} (hδρ : 0 < δ - ρ)
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ)
    (hu_ball : u_star ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ)
    (hsumE : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Summable (fun n => unitIntervalCosineEigenvalue n *
        |fullSourceCoeff p (realSlice u_star) u₀cos t n|))
    (hrealizes : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x
        = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x)
    (huNE0 : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      intervalDomainLift (realSlice u_star t) 0 ≠ 0)
    (huNE1 : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      intervalDomainLift (realSlice u_star t) 1 ≠ 0) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T,
      SourceCoeffQuadraticDecay p (realSlice u_star t) := by
  intro t ht
  have hagree := realSlice_eqOn_cosineSeries p u_star u₀cos (hrealizes t ht)
  -- closed C² on Icc (conjunct 7), with the genuine endpoint-deriv = 0 data.
  have hC2 :
      ContDiffOn ℝ 2 (intervalDomainLift (realSlice u_star t)) (Set.Icc (0 : ℝ) 1) :=
    (intervalDomainCosineSlice_conjunct7 (hsumE t ht) hagree
      (huNE0 t ht) (huNE1 t ht)).1
  -- genuine one-sided Neumann limits of the derivative at the endpoints.
  have hN0 := intervalDomainCosineSlice_neumann_limit_left (hsumE t ht) hagree
  have hN1 := intervalDomainCosineSlice_neumann_limit_right (hsumE t ht) hagree
  -- strict positivity of the slice on Icc.
  have hpos := realSlice_lift_pos_Icc u_star hδρ hheat hu_ball ht
  exact sourceCoeffQuadraticDecay_of_closedC2_neumann_slice hC2 hN0 hN1 hpos

/-! ### `Hvpos` — strict positivity of the chemical concentration. -/

/-- **`Hvpos` DISCHARGED.**  For each interior `t` and every `x`,
`0 < mildChemicalConcentration p (realSlice u_star) t x`.

`mildChemicalConcentration p u t = intervalNeumannResolverR p (u t)`.  The source
`ν·u^γ` is bounded below by a strictly positive constant `c₀ = ν·m^γ` (`m` = min of
the slice over `[0,1]`, positive by `realSlice_pos`), and the positive Neumann
resolver kernel maps it to a value `≥ c₀/μ > 0`
(`resolverR_pos_of_representation`).  The globally-continuous source extension is the
`u`-slice cosine series (globally `C²`, agreeing with the lift on `[0,1]` by
`hrealizes`).  This is a positive-kernel fact, NOT a spectral fact. -/
theorem realSlice_resolverPos
    (p : CM2Params) (u_star : EWA T 1) (u₀cos : ℕ → ℝ)
    {u₀E : WA 1} {δ ρ : ℝ} (hδρ : 0 < δ - ρ)
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ)
    (hu_ball : u_star ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ)
    (hsumE : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Summable (fun n => unitIntervalCosineEigenvalue n *
        |fullSourceCoeff p (realSlice u_star) u₀cos t n|))
    (hrealizes : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x
        = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint,
      0 < mildChemicalConcentration p (realSlice u_star) t x := by
  intro t ht x
  set g₀ : intervalDomainPoint → ℝ := realSlice u_star t with hg₀
  -- globally continuous source extension = the u-slice cosine series.
  set cs : ℝ → ℝ :=
    fun y => ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n y
    with hcs
  have hcs_cont : Continuous cs := (cosineCoeffSeries_contDiff_two (hsumE t ht)).continuous
  -- agreement of the lift with cs on Icc (the slab realizes).
  have hagree : ∀ y ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift g₀ y = cs y :=
    fun y hy => hrealizes t ht y hy
  -- positive lower bound m = min cs over the compact [0,1].
  have hIcc_ne : (Set.Icc (0 : ℝ) 1).Nonempty := ⟨0, by norm_num⟩
  obtain ⟨x₀, hx₀mem, hx₀min⟩ :=
    isCompact_Icc.exists_isMinOn hIcc_ne hcs_cont.continuousOn
  set m : ℝ := cs x₀ with hm
  have hcs_lb : ∀ y ∈ Set.Icc (0 : ℝ) 1, m ≤ cs y := fun y hy => hx₀min hy
  have hm_pos : 0 < m := by
    rw [hm, ← hagree x₀ hx₀mem]
    exact realSlice_lift_pos_Icc u_star hδρ hheat hu_ball ht x₀ hx₀mem
  -- upper bound M = max cs over the compact [0,1].
  obtain ⟨x₁, _, hx₁max⟩ :=
    isCompact_Icc.exists_isMaxOn hIcc_ne hcs_cont.continuousOn
  set M : ℝ := cs x₁ with hM
  have hcs_ub : ∀ y ∈ Set.Icc (0 : ℝ) 1, cs y ≤ M := fun y hy => hx₁max hy
  -- source coefficient matching: cosineCoeffs (ν·lift g₀^γ) = (sourceCoeff).re.
  have hsrc_coeff : ∀ k,
      cosineCoeffs (fun y => p.ν * intervalDomainLift g₀ y ^ p.γ) k
        = (intervalNeumannResolverSourceCoeff p g₀ k).re := by
    intro k
    simp [cosineCoeffs, intervalNeumannResolverSourceCoeff, Complex.ofReal_re]
  -- ℓ² of the source coefficients (cosine–Bessel, source continuous on Icc).
  have hUcont : ContinuousOn (intervalDomainLift g₀) (Set.Icc (0 : ℝ) 1) :=
    realSlice_lift_continuousOn_Icc p u_star u₀cos (hsumE t ht) (hrealizes t ht)
  have hâ : Summable (fun k =>
      (cosineCoeffs (fun y => p.ν * intervalDomainLift g₀ y ^ p.γ) k) ^ 2) := by
    have h := resolverSourceCoeff_re_sq_summable_of_continuousOn p hUcont
    simp only [intervalNeumannResolverSourceCoeff_zero, sub_zero] at h
    exact h.congr (fun k => by rw [hsrc_coeff k])
  -- ℓ² of the shifted source `ν·lift g₀^γ − ν·m^γ` (differs only at mode 0).
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
            (fun k => (cosineCoeffs (fun y => p.ν * intervalDomainLift g₀ y ^ p.γ) k) ^ 2)
            0
            ((cosineCoeffs (fun y => p.ν * intervalDomainLift g₀ y ^ p.γ - c₀) 0) ^ 2) := by
      funext k
      by_cases hk : k = 0
      · subst hk; rw [Function.update_self]
      · rw [Function.update_of_ne hk, hsplit k, cosineCoeffs_const, if_neg hk, sub_zero]
    rw [hupd]
    exact hâ.update 0 _
  -- discharge via the positive-kernel representation lemma.
  show 0 < intervalNeumannResolverR p (realSlice u_star t) x
  exact resolverR_pos_of_representation p hcs_cont hagree hm_pos hcs_lb hcs_ub
    hsrc_coeff hâ hĝ x

/-! ### `Hv` — resolver direct spectral data (RESIDUAL). -/

/-- **`Hv` wired from the per-`t₀` clamped resolver-source witness.**

`HasResolverDirectSpectralData T (mildChemicalConcentration p (realSlice u_star)) p`
is obtained from `hasResolverDirectSpectralData_of_clamped_perT0` once, for each
interior `t₀`, a clamped spectral family `aC` with a `DuhamelSourceTimeC1 aC` package
and a window `W ∈ 𝓝 t₀` on which `aC` agrees with the canonical resolver source
coefficients `s ↦ (intervalNeumannResolverSourceCoeff p (realSlice u_star s) k).re`,
is supplied.

This is the consumer-facing entry point; the hypothesis `Hclamp` is the genuine
χ₀<0 resolver-source TIME-`C¹` frontier (see `realSlice_resolverSpectralData_residual`
below).  It is NOT discharged from the atoms `realSlice_classicalRegularity` carries,
which control only spatial regularity and per-slice positivity. -/
theorem realSlice_resolverSpectralData
    (p : CM2Params) (u_star : EWA T 1)
    (Hclamp : ∀ t₀, 0 < t₀ → t₀ < T →
      ∃ (aC : ℝ → ℕ → ℝ)
        (_ : ShenWork.IntervalDuhamelClosedC2.DuhamelSourceTimeC1 aC) (W : Set ℝ),
        W ∈ 𝓝 t₀ ∧
        (∀ s ∈ W, ∀ k, aC s k =
          (intervalNeumannResolverSourceCoeff p (realSlice u_star s) k).re)) :
    HasResolverDirectSpectralData T
      (mildChemicalConcentration p (realSlice u_star)) p :=
  hasResolverDirectSpectralData_of_clamped_perT0 (realSlice u_star) Hclamp

/-- **`Hv` RESIDUAL (precise statement of the missing datum).**

To discharge `Hv` it suffices to produce, for each interior `t₀ ∈ (0,T)`, a
`DuhamelSourceTimeC1` package for the resolver source cosine coefficients on a time
window around `t₀`.  The honest missing piece is the TIME-`C¹` quadruple of the
source coefficients of `s ↦ ν·(realSlice u_star s)^γ`:

  * `HasDerivAt (fun r => cosineCoeffs (ν·(lift (realSlice u_star r))^γ) k) (adot s k) s`,
  * continuity of `s ↦ adot s k`,
  * a uniform bound `|adot s k| ≤ Mdot`,

together with the quadratic-decay envelope of the source coefficients (already
available pointwise in `s` from `realSlice_resolverDecay`).  Producer to feed:
`ShenWork.Paper2.ResolverSourceTimeC1.resolverSource_timeC1_of_global_representation`
(GLOBAL form) or the soft-clamped windowed form
`ShenWork.IntervalResolverSourceClampedWitness` /
`hasResolverDirectSpectralData_of_clamped_perT0`
(`IntervalMildRegularityFrontierAssembly.lean:241`).

`realSlice_classicalRegularity` carries no time-differentiability atom for the
`u`-slice source, so this residual cannot be closed from its inputs alone; it is the
χ₀<0 resolver-source frontier.  This lemma is the trivial restatement that `Hv`
follows from exactly that clamped witness. -/
theorem realSlice_resolverSpectralData_residual
    (p : CM2Params) (u_star : EWA T 1)
    (Hclamp : ∀ t₀, 0 < t₀ → t₀ < T →
      ∃ (aC : ℝ → ℕ → ℝ)
        (_ : ShenWork.IntervalDuhamelClosedC2.DuhamelSourceTimeC1 aC) (W : Set ℝ),
        W ∈ 𝓝 t₀ ∧
        (∀ s ∈ W, ∀ k, aC s k =
          (intervalNeumannResolverSourceCoeff p (realSlice u_star s) k).re)) :
    HasResolverDirectSpectralData T
      (mildChemicalConcentration p (realSlice u_star)) p :=
  realSlice_resolverSpectralData p u_star Hclamp

end ShenWork.EWA
