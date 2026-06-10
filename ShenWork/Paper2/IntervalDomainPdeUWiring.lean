/-
  ShenWork/Paper2/IntervalDomainPdeUWiring.lean

  **Producer of `HasSpectralPdeAgreement` from time-localized ledger data.**

  `IntervalDomainPdeUProducer.mildSolution_pde_u_of_spectral` turns the per-time
  predicate `HasSpectralPdeAgreement p T u` into the ledger's `hpde_u` field
  (`∂ₜu = Δu − χ₀·chemotaxis + reaction` at every interior point of every interior
  time, with the chemotaxis term dropped for `χ₀ = 0`).  Its single hypothesis is a
  per-`(t₀,x)` existential bundling the restart cosine representation data plus the
  source-coefficient identity, the source continuity / Fourier-summability, and the
  three spectral summabilities.

  This file PRODUCES that predicate from the SAME time-localized ledger ingredients
  that `TimeNhdSubtype.Hu_of_restart_localized_of_subtypeCont` consumes (the
  satisfiable, subtype-continuity form: per-slice cosine representation / `K2`
  sup-gradient-Hessian bounds / `K1` time-`C¹` coefficient data on `(0,T)`, with
  constExtend slice continuity).  The witness tuple is the soft-clamped family
  `aC σ k = cosineCoeffs (logisticSourceFun … (lift (u (φ (τ+σ))))) k` with
  `τ = t₀/2`, exactly as in the localized `Hu` witness; the restart representation
  `hrep` is transferred verbatim through `picardLimitRestart_general_of_subtypeCont`.

  ## The former obstruction, now resolved by the continuous surrogate

  Earlier, two fields of `HasSpectralPdeAgreement` pinned the GLOBAL zero-extension
  `intervalDomainLift (u t₀)`, which JUMPS from `u t₀ > 0` at the Neumann endpoints
  to `0` outside `[0,1]` (the `hpost` positivity).  `logisticSourceFun … (lift
  (u t₀))` is therefore GENUINELY DISCONTINUOUS, and the cosine-inversion engine it
  fed (`intervalCosine_hasSum_pointwise`, which bundles `reflCircle f` into a
  *continuous* map `C(AddCircle 2, ℂ)`) needed that global continuity essentially —
  an unprovable `Continuous (lift (u t₀))`.

  `HasSpectralPdeAgreement` has since been retyped (in `IntervalDomainPdeUProducer`)
  to consume an EXISTENTIALLY QUANTIFIED CONTINUOUS SURROGATE `g` that agrees with
  the lift's logistic source on `[0,1]`, together with the `[0,1]` agreement, the
  surrogate's `reflCircle` Fourier-summability, and `hsrc_coeff` restated against
  `cosineCoeffs g`.  Here the surrogate is the CONSTANT EXTENSION of the per-slice
  logistic source, `g := intervalDomainConstExtend (intervalLogisticSource p (u t₀))`:

  * continuity of `g` is the in-scope hypothesis `hLc_ce` (instantiated at the slice
    `s = t = t₀`);
  * `[0,1]` agreement is `constExtend_eq_lift_on_Icc` composed with
    `logisticLifted_eq_logisticSourceFun_on_Icc`;
  * the `reflCircle` Fourier-summability of `g` comes from the converse bridge
    `fourierCoeff_reflCircle_summable_of_cosineCoeff_abs`, fed by the quadratic-decay
    envelope of the clamped source family (`|cosineCoeffs g n| = |aC (t₀−τ) n| ≤
    envelope n`, summable) — no continuity of the discontinuous lift is ever invoked.

  Thus EVERY field of `HasSpectralPdeAgreement` is now produced sorry-free.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalDomainPdeUProducer
import ShenWork.Paper2.IntervalPicardLimitTimeNhdSubtype

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalDomainConstExtend)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1 duhamelSpectralCoeff)
open ShenWork.IntervalGradientDuhamelMap (intervalGradientDuhamelMap logisticLifted)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalMildPicardRegularity
  (logisticSourceFun cosineCoeffs_abs_le_of_continuous_bounded)
open ShenWork.IntervalPicardLimitRestartWeak
  (DuhamelSourceL1Cont DuhamelSourceL1ContOn)
open ShenWork.IntervalCosineInversion (reflCircle)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.Paper2.ClampedSourceRepresentation
  (clampedSource_duhamelSourceTimeC1 clampedFamily_eq_on)
open ShenWork.IntervalTimeSoftClamp (φ)
open ShenWork.IntervalDomainPdeUProducer (HasSpectralPdeAgreement)

noncomputable section

namespace ShenWork.Paper2.PdeUWiring

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-- **Converse summability bridge: cosine-`ℓ¹` ⟹ `reflCircle` Fourier-`ℓ¹`.**

For a CONTINUOUS `g`, the even-reflection Fourier coefficient `fourierCoeff
(reflCircle g) n` is real and (up to the `1/2` mode factor) equals `cosineCoeffs g
|n|`; in particular `‖fourierCoeff (reflCircle g) (±n)‖ ≤ |cosineCoeffs g n|`.  Hence
absolute summability of the `ℕ`-indexed cosine coefficients of `g` forces
summability of the `ℤ`-indexed `reflCircle` Fourier coefficients.

This is the converse direction of `intervalCosineCoeff_summable_abs`, and it is what
lets us discharge the inversion engine's regularity input from the quadratic-decay
envelope of the (clamped) source family — no continuity of the discontinuous lift is
ever needed; only the continuous surrogate `g`. -/
theorem fourierCoeff_reflCircle_summable_of_cosineCoeff_abs
    {g : ℝ → ℝ} (hg : Continuous g)
    (hcos : Summable (fun n : ℕ => |cosineCoeffs g n|)) :
    Summable (fun n : ℤ => fourierCoeff (reflCircle g) n) := by
  classical
  -- `‖fourierCoeff (reflCircle g) (n:ℤ)‖ ≤ |cosineCoeffs g n|` for `n : ℕ`.
  have hbnd : ∀ n : ℕ,
      ‖fourierCoeff (reflCircle g) (n : ℤ)‖ ≤ |cosineCoeffs g n| := by
    intro n
    -- the coefficient is real, so its norm is the abs of its real part.
    have hre : ‖fourierCoeff (reflCircle g) (n : ℤ)‖
        = |(fourierCoeff (reflCircle g) (n : ℤ)).re| := by
      rw [← ShenWork.IntervalCosineInversion.fourierCoeff_ofReal_re g hg (n : ℤ),
        Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
    -- `cosineCoeffs g n = (1 or 2) · (fourierCoeff (reflCircle g) n).re`.
    have hcoeff : cosineCoeffs g n
        = (if n = 0 then (1 : ℝ) else 2)
            * (fourierCoeff (reflCircle g) (n : ℤ)).re := by
      rw [ShenWork.IntervalCosineInversion.cosineCoeffs_eq g hg n,
        ShenWork.IntervalCosineInversion.fourierCoeff_reflCircle]
    rw [hre, hcoeff, abs_mul]
    -- `|if n=0 then 1 else 2| ≥ 1`, so `|re| ≤ |if…| · |re|`.
    have hfac : (1 : ℝ) ≤ |(if n = 0 then (1 : ℝ) else 2)| := by
      rcases eq_or_ne n 0 with h | h <;> simp [h]
    nlinarith [hfac, abs_nonneg ((fourierCoeff (reflCircle g) (n : ℤ)).re)]
  -- evenness of the coefficient in the frequency.
  have heven : ∀ n : ℤ,
      fourierCoeff (reflCircle g) (-n) = fourierCoeff (reflCircle g) n := by
    intro n
    rw [ShenWork.IntervalCosineInversion.fourierCoeff_reflCircle,
      ShenWork.IntervalCosineInversion.fourierCoeff_reflCircle,
      ShenWork.IntervalCosineInversion.fco_neg g hg]
  rw [← summable_norm_iff]
  apply Summable.of_nat_of_neg_add_one
  · -- positive part: `‖fourierCoeff (reflCircle g) (n:ℤ)‖`
    exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbnd hcos
  · -- negative part: `‖fourierCoeff (reflCircle g) (-(n+1))‖`, even ⇒ same bound
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => ?_) (hcos.comp_injective (add_left_injective 1))
    rw [show (-((n : ℤ) + 1)) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, heven]
    simpa using hbnd (n + 1)

/-- **`HasSpectralPdeAgreement` from time-localized data (subtype-continuity
form).**

Mirror of `TimeNhdSubtype.Hu_of_restart_localized_of_subtypeCont`: the witness
tuple (`a₀ = coeffs (lift (u τ))`, `M = 2·Msup`, the soft-clamped family `aC`,
`srcC : DuhamelSourceTimeC1 aC`, `offset = τ = t₀/2`) and the eventually-nhds
restart representation `hrep` are IDENTICAL.  In addition this produces, per
`(t₀,x)`:

* the continuous surrogate `g := constExtend (intervalLogisticSource p (u t₀))`,
  its continuity (`hLc_ce` at the slice `t₀`), its `[0,1]` agreement with the lift's
  logistic source, and `hsrc_coeff`: `aC (t₀−τ) n = cosineCoeffs g n` — via
  `clampedFamily_eq_on` (`τ + (t₀−τ) = t₀ ∈ [τ,d]` where `φ = id`) plus
  `cosineCoeffs_congr_on_Icc`;
* the surrogate's `reflCircle` Fourier-summability — from the cosine-envelope
  bound through `fourierCoeff_reflCircle_summable_of_cosineCoeff_abs`;
* the eigenvalue-weighted summability of `localRestartCoeff` (`hsum_b`) — from the
  homogeneous geometric tail (`unitIntervalCosineEigenvalue_mul_exp_summable`) plus
  the Duhamel envelope (`eigenvalue_mul_abs_duhamelSpectralCoeff_le_envelope`);
* the pointwise summabilities `hsum_src`, `hsum_lb` — by comparison `|cos| ≤ 1`
  against `hsum_src ≤ envelope` and `hsum_b`. -/
theorem hasSpectralPdeAgreement_of_localized_data
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ} (u : ℝ → intervalDomainPoint → ℝ)
    {T : ℝ}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hfix : ∀ s, 0 < s → s < T → ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
      intervalDomainLift (u s) x = intervalGradientDuhamelMap p u₀ u s ⟨x, hx⟩)
    (hsrc0 : DuhamelSourceL1ContOn
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k) T)
    {Msup : ℝ}
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, 0 < σ → σ < T →
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ, 0 < σ → σ < T → Set.EqOn (intervalDomainLift (u σ))
      (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpost : ∀ σ, 0 < σ → σ < T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u σ) x)
    (hubt : ∀ σ, 0 < σ → σ < T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (u σ) x ≤ Msup)
    (hG1t : ∀ a' b', 0 < a' → b' < T → ∃ G1, ∀ σ ∈ Set.Icc a' b',
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (intervalDomainLift (u σ)) x| ≤ G1)
    (hG2t : ∀ a' b', 0 < a' → b' < T → ∃ G2, ∀ σ ∈ Set.Icc a' b',
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv (intervalDomainLift (u σ))) x| ≤ G2)
    (adott : ℝ → ℕ → ℝ)
    (hderivt : ∀ σ, 0 < σ → σ < T → ∀ k, HasDerivAt
      (fun r => cosineCoeffs
        (logisticSourceFun p.a p.b p.α (intervalDomainLift (u r))) k)
      (adott σ k) σ)
    (hadotcontt : ∀ k, ContinuousOn (fun σ => adott σ k) (Set.Ioo 0 T))
    (hMdott : ∀ a' b', 0 < a' → b' < T → ∃ Mdot, ∀ σ ∈ Set.Icc a' b',
      ∀ k, |adott σ k| ≤ Mdot)
    -- H3 slice continuity — constExtend (subtype) form
    (hLc_ce : ∀ t, 0 < t → t < T →
      ∀ s, 0 < s → s ≤ t →
        Continuous (intervalDomainConstExtend (intervalLogisticSource p (u s)))) :
    HasSpectralPdeAgreement p T u := by
  constructor
  intro t₀ ht₀ ht₀T x hx
  -- restart base / offset
  set τ : ℝ := t₀ / 2 with hτdef
  have hτpos : 0 < τ := by rw [hτdef]; linarith
  have hτT : τ < T := by rw [hτdef]; linarith
  -- clamp window: id-zone [c,d] = [τ, (t₀+T)/2], range window [c',d'] ⊂ (0,T)
  set c' : ℝ := t₀ / 4 with hc'def
  set d : ℝ := (t₀ + T) / 2 with hddef
  set d' : ℝ := (t₀ + 3 * T) / 4 with hd'def
  have hc' : c' < τ := by rw [hc'def, hτdef]; linarith
  have hcd : τ ≤ d := by rw [hddef, hτdef]; linarith
  have hd' : d < d' := by rw [hddef, hd'def]; linarith
  have hc'pos : 0 < c' := by rw [hc'def]; linarith
  have hd'T : d' < T := by rw [hd'def]; linarith
  -- window membership facts
  have hwin : ∀ σ ∈ Set.Icc c' d', 0 < σ ∧ σ < T := fun σ hσ =>
    ⟨lt_of_lt_of_le hc'pos hσ.1, lt_of_le_of_lt hσ.2 hd'T⟩
  -- per-compact bounds on the window
  obtain ⟨G1, hG1⟩ := hG1t c' d' hc'pos hd'T
  obtain ⟨G2, hG2⟩ := hG2t c' d' hc'pos hd'T
  obtain ⟨Mdot, hMdot⟩ := hMdott c' d' hc'pos hd'T
  -- the clamped TimeC1 witness package (verbatim the localized witness)
  have srcC : DuhamelSourceTimeC1
      (fun σ k => cosineCoeffs (logisticSourceFun p.a p.b p.α
        (intervalDomainLift (u (φ c' τ d d' (τ + σ))))) k) :=
    clampedSource_duhamelSourceTimeC1 p u hα ha hb hc' hcd hd'
      bc
      (fun σ hσ => hbsum σ (hwin σ hσ).1 (hwin σ hσ).2)
      (fun σ hσ => hagree σ (hwin σ hσ).1 (hwin σ hσ).2)
      (fun σ hσ => hpost σ (hwin σ hσ).1 (hwin σ hσ).2)
      (fun σ hσ => hubt σ (hwin σ hσ).1 (hwin σ hσ).2)
      hG1 hG2 adott
      (fun σ hσ k => hderivt σ (hwin σ hσ).1 (hwin σ hσ).2 k)
      (fun k => (hadotcontt k).mono
        (fun σ hσ => ⟨(hwin σ hσ).1, (hwin σ hσ).2⟩))
      hMdot
  -- abbreviations for the clamped family and the restart base coefficients
  set a₀ : ℕ → ℝ := cosineCoeffs (intervalDomainLift (u τ)) with ha₀def
  set aC : ℝ → ℕ → ℝ := fun σ k => cosineCoeffs (logisticSourceFun p.a p.b p.α
    (intervalDomainLift (u (φ c' τ d d' (τ + σ))))) k with haCdef
  -- `Msup` nonnegativity (window nonempty)
  have hMnn : 0 ≤ Msup := by
    have h1 := hubt τ hτpos hτT 0 ⟨le_rfl, zero_le_one⟩
    have h2 := hpost τ hτpos hτT 0 ⟨le_rfl, zero_le_one⟩
    linarith
  -- restart-base coefficient bound: |a₀ k| ≤ 2·Msup
  have ha₀_bd : ∀ k, |a₀ k| ≤ 2 * Msup := by
    intro k
    refine cosineCoeffs_abs_le_of_continuous_bounded
      (((ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_contDiff_two
        (hbsum τ hτpos hτT)).continuous.continuousOn).congr
          (hagree τ hτpos hτT)) hMnn ?_ k
    intro y hy
    rw [abs_of_pos (hpost τ hτpos hτT y hy)]
    exact hubt τ hτpos hτT y hy
  -- 0 < t₀ − offset = τ
  have hoff : 0 < t₀ - τ := by rw [hτdef]; linarith
  -- t₀ − τ = τ (offset = τ = t₀/2)
  have htmτ : t₀ - τ = τ := by rw [hτdef]; ring
  -- the restart cosine representation in a time-neighbourhood of t₀
  have hrep : ∀ᶠ s in 𝓝 t₀, ∀ y : intervalDomainPoint,
      u s y = ∑' n, localRestartCoeff a₀ aC (s - τ) n * cosineMode n y.1 := by
    have hmem : t₀ ∈ Set.Ioo τ d := ⟨by rw [hτdef]; linarith, by rw [hddef]; linarith⟩
    filter_upwards [(isOpen_Ioo (a := τ) (b := d)).mem_nhds hmem] with s hs
    have hτs : τ < s := hs.1
    have hsd : s < d := hs.2
    have hsT : s < T := lt_trans hsd (lt_trans hd' hd'T)
    have hspos : 0 < s := lt_trans hτpos hτs
    have heqon := ShenWork.Paper2.TimeNhdSubtype.picardLimitRestart_general_of_subtypeCont
      p hχ0 u₀ u (fun r hr hrs => hfix r hr (lt_of_le_of_lt hrs hsT))
      hu₀_cont hu₀_bound hsrc0 hτpos hτs hsT.le
      (fun r hr hrs => hLc_ce s hspos hsT r hr hrs)
    intro y
    have hy1 : y.1 ∈ Set.Icc (0:ℝ) 1 := y.2
    have hlift : u s y = intervalDomainLift (u s) y.1 := by
      simp only [intervalDomainLift, hy1, dif_pos, Subtype.eta]
    rw [hlift, heqon hy1]
    refine tsum_congr (fun k => ?_)
    congr 1
    rw [ShenWork.IntervalPicardLimitSourceData.restartDuhamelCoeff_eq_localRestartCoeff]
    unfold localRestartCoeff
    congr 1
    unfold duhamelSpectralCoeff
    apply intervalIntegral.integral_congr
    intro σ hσ
    rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ s - τ)] at hσ
    have hmem_cd : τ + σ ∈ Set.Icc τ d :=
      ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    simp only [aC]
    congr 1
    rw [clampedFamily_eq_on p u hc' hd' hmem_cd k]
    exact congrFun (congrFun (ShenWork.IntervalPicardLimitSourceData.source_family_eq_w p u)
      (τ + σ)) k
  -- aC (t₀−τ) n = coeffs (logisticSourceFun … (lift (u t₀))) n
  have hmem_t₀ : τ + (t₀ - τ) ∈ Set.Icc τ d :=
    ⟨by linarith, by rw [hddef]; linarith⟩
  have hsrc_lift : ∀ n, aC (t₀ - τ) n
      = cosineCoeffs (logisticSourceFun p.a p.b p.α (intervalDomainLift (u t₀))) n := by
    intro n
    simp only [aC]
    rw [clampedFamily_eq_on p u hc' hd' hmem_t₀ n]
    rw [show τ + (t₀ - τ) = t₀ by ring]
  -- envelope of the clamped Duhamel source restricted to horizon τ
  have hsrcOn : DuhamelSourceL1ContOn aC τ := (DuhamelSourceL1Cont.ofTimeC1 srcC).toOn τ
  -- ════════ continuous surrogate `g` for the discontinuous lift's logistic source ════════
  -- `g` is the CONSTANT EXTENSION of the per-slice logistic source; it is globally
  -- continuous (hLc_ce, instantiated at s = t = t₀) and agrees with the lift's
  -- logistic source on [0,1].
  set g : ℝ → ℝ := intervalDomainConstExtend (intervalLogisticSource p (u t₀)) with hgdef
  -- continuity of g from the constExtend slice-continuity hypothesis at t₀
  have hcont : Continuous g := hLc_ce t₀ ht₀ ht₀T t₀ ht₀ le_rfl
  -- g agrees with the lift's logistic source on [0,1]:
  --   constExtend f = lift f on [0,1]; lift (intervalLogisticSource …) = logisticLifted;
  --   logisticLifted ≈ logisticSourceFun … (lift (u t₀)) on [0,1].
  have hgeq : Set.EqOn g
      (logisticSourceFun p.a p.b p.α (intervalDomainLift (u t₀)))
      (Set.Icc (0:ℝ) 1) := by
    intro y hy
    rw [hgdef,
      ShenWork.IntervalDomain.constExtend_eq_lift_on_Icc hy]
    have hLL : intervalDomainLift (intervalLogisticSource p (u t₀)) y
        = logisticLifted p (u t₀) y := rfl
    rw [hLL]
    exact ShenWork.IntervalMildPicardRegularity.logisticLifted_eq_logisticSourceFun_on_Icc
      p (u t₀) hy
  -- hsrc_coeff (against g): cosineCoeffs g = cosineCoeffs (lift's source) on [0,1].
  have hsrc_coeff : ∀ n, aC (t₀ - τ) n = cosineCoeffs g n := by
    intro n
    rw [hsrc_lift n]
    exact ShenWork.Paper2.cosineCoeffs_congr_on_Icc
      (fun y hy => (hgeq hy).symm) n
  -- |cosineCoeffs g n| ≤ envelope n, hence ℓ¹-summable cosine coefficients of g.
  have hcos_sum : Summable (fun n : ℕ => |cosineCoeffs g n|) := by
    refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
      hsrcOn.henv_summable
    rw [← hsrc_coeff n, htmτ]
    exact hsrcOn.henv_bound τ hτpos.le le_rfl n
  -- reflCircle Fourier-summability of g via the converse bridge (NO discontinuous lift).
  have hsum_fourier : Summable (fun n : ℤ => fourierCoeff (reflCircle g) n) :=
    fourierCoeff_reflCircle_summable_of_cosineCoeff_abs hcont hcos_sum
  -- hsum_b: eigenvalue-weighted summability of localRestartCoeff a₀ aC (t₀−τ)
  have hsum_b : Summable (fun n => unitIntervalCosineEigenvalue n
      * |localRestartCoeff a₀ aC (t₀ - τ) n|) := by
    refine Summable.of_nonneg_of_le
      (f := fun n => 2 * Msup * ((λ_ n) * Real.exp (-τ * (λ_ n))) + hsrcOn.envelope n)
      (fun n => mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity) (abs_nonneg _))
      (fun n => ?_) ?_
    · -- λ_n |localRestartCoeff| ≤ 2Msup·λ_n exp(-τλ) + envelope_n
      change unitIntervalCosineEigenvalue n * |localRestartCoeff a₀ aC (t₀ - τ) n|
        ≤ 2 * Msup * (unitIntervalCosineEigenvalue n
            * Real.exp (-τ * unitIntervalCosineEigenvalue n)) + hsrcOn.envelope n
      rw [htmτ]
      unfold localRestartCoeff
      set eig : ℝ := unitIntervalCosineEigenvalue n with heig
      have heignn : (0:ℝ) ≤ eig := by rw [heig]; unfold unitIntervalCosineEigenvalue; positivity
      have hsplit : eig * |Real.exp (-τ * eig) * a₀ n + duhamelSpectralCoeff aC τ n|
          ≤ eig * (Real.exp (-τ * eig) * |a₀ n|)
            + eig * |duhamelSpectralCoeff aC τ n| := by
        have hstep := mul_le_mul_of_nonneg_left
          (abs_add_le (Real.exp (-τ * eig) * a₀ n) (duhamelSpectralCoeff aC τ n)) heignn
        rw [mul_add] at hstep
        refine le_trans hstep (add_le_add (le_of_eq ?_) le_rfl)
        rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      refine le_trans hsplit (add_le_add ?_ ?_)
      · -- 2Msup·λ_n exp(-τλ) bound on the homogeneous part
        rw [show 2 * Msup * (eig * Real.exp (-τ * eig))
            = eig * (Real.exp (-τ * eig) * (2 * Msup)) by ring]
        refine mul_le_mul_of_nonneg_left ?_ heignn
        exact mul_le_mul_of_nonneg_left (ha₀_bd n) (Real.exp_nonneg _)
      · exact eigenvalue_mul_abs_duhamelSpectralCoeff_le_envelope hsrcOn hτpos le_rfl n
    · -- summability of the envelope
      exact (((ShenWork.IntervalMildRegularityBootstrap.unitIntervalCosineEigenvalue_mul_exp_summable
        hτpos).mul_left (2 * Msup)).add hsrcOn.henv_summable)
  -- hsum_src: summability of aC (t₀−τ) n · cos
  have hsum_src : Summable (fun n => aC (t₀ - τ) n * cosineMode n x.1) := by
    refine Summable.of_norm_bounded (g := fun n => hsrcOn.envelope n) hsrcOn.henv_summable ?_
    intro n
    rw [htmτ]
    rw [Real.norm_eq_abs, abs_mul]
    have hcos : |cosineMode n x.1| ≤ 1 := by
      unfold cosineMode; exact Real.abs_cos_le_one _
    refine le_trans (mul_le_mul_of_nonneg_left hcos (abs_nonneg _)) ?_
    rw [mul_one]
    exact hsrcOn.henv_bound τ hτpos.le le_rfl n
  -- hsum_lb: summability of λ_n · localRestartCoeff · cos
  have hsum_lb : Summable (fun n => unitIntervalCosineEigenvalue n
      * localRestartCoeff a₀ aC (t₀ - τ) n * cosineMode n x.1) := by
    refine Summable.of_norm_bounded
      (g := fun n => unitIntervalCosineEigenvalue n * |localRestartCoeff a₀ aC (t₀ - τ) n|)
      hsum_b ?_
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (by unfold unitIntervalCosineEigenvalue; positivity : (0:ℝ) ≤ λ_ n),
      mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by unfold unitIntervalCosineEigenvalue; positivity)
    have hcos : |cosineMode n x.1| ≤ 1 := by
      unfold cosineMode; exact Real.abs_cos_le_one _
    refine le_trans (mul_le_mul_of_nonneg_left hcos (abs_nonneg _)) ?_
    rw [mul_one]
  -- assemble the witness tuple
  exact ⟨a₀, 2 * Msup, by linarith, ha₀_bd, aC, srcC, τ, hoff, g,
    hrep, hcont, hgeq, hsum_fourier, hsrc_coeff, hsum_b, hsum_src, hsum_lb⟩

end ShenWork.Paper2.PdeUWiring
