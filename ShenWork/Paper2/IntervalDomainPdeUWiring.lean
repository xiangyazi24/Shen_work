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

  ## The one genuine obstruction (isolated as a single named `sorry`)

  Two fields of `HasSpectralPdeAgreement` —

  * `Continuous (logisticSourceFun … (intervalDomainLift (u t₀)))`, and
  * `Summable (fun n : ℤ => fourierCoeff (reflCircle (logisticSourceFun …
      (intervalDomainLift (u t₀)))) n)` —

  pin the GLOBAL zero-extension `intervalDomainLift (u t₀)`, which JUMPS from
  `u t₀ > 0` at the Neumann endpoints to `0` outside `[0,1]` (the `hpost`
  positivity).  Hence `logisticSourceFun … (lift (u t₀))` is GENUINELY
  DISCONTINUOUS, and the cosine-inversion engine it feeds
  (`intervalCosine_hasSum_pointwise`, which bundles `reflCircle f` into a
  *continuous* map `C(AddCircle 2, ℂ)`) needs that global continuity essentially.

  These two facts are NOT among the data the existential lets us choose: the
  structure pins `u`, and `lift` is applied to `u t₀`.  The constExtend cosine
  series `cs t₀` IS globally continuous and shares the cosine coefficients
  (`cosineCoeffs` integrates only over `[0,1]`), but the structure as typed in
  `IntervalDomainPdeUProducer` requires the LIFT function itself, not its `[0,1]`
  cosine surrogate — so the surrogate cannot be substituted without editing that
  (off-limits) structure.  This is the SAME wall documented as the residual `sorry`
  in `LedgerSweep.Hu_of_reduced` (false `Continuous (intervalDomainLift u₀)`),
  pushed one level up to the logistic source of `u t₀`.

  It is therefore isolated here as the SINGLE named hypothesis-lemma
  `logisticSourceLift_cont_and_fourierSummable`, with its exact statement; every
  other field of `HasSpectralPdeAgreement` is produced sorry-free below.

  No `admit`, no custom `axiom`, no `native_decide`.
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

/-- **The single genuine obstruction (isolated `sorry`).**

`Continuous (logisticSourceFun … (lift (u t₀)))` and the matching `reflCircle`
Fourier-summability.  Both are FALSE for the zero-extension lift of strictly
positive boundary data (the lift jumps to `0` outside `[0,1]`), and the
cosine-inversion engine `intervalCosine_hasSum_pointwise` consumes the global
continuity essentially (it bundles `reflCircle f` into `C(AddCircle 2, ℂ)`).  This
is the only fact of `HasSpectralPdeAgreement` not produced sorry-free below; it is
the same wall as `LedgerSweep.Hu_of_reduced`'s residual `sorry`, here on the
logistic source of `u t₀`.

The honest fix requires retyping `HasSpectralPdeAgreement` (in the off-limits
`IntervalDomainPdeUProducer`) to consume the `[0,1]`-cosine surrogate `cs t₀` —
which IS globally continuous and shares all cosine coefficients — instead of the
discontinuous lift.  Until then this stays a single, precisely-localized hole. -/
theorem logisticSourceLift_cont_and_fourierSummable
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (t₀ : ℝ) :
    Continuous (logisticSourceFun p.a p.b p.α (intervalDomainLift (u t₀))) ∧
    Summable (fun n : ℤ => fourierCoeff
      (reflCircle (logisticSourceFun p.a p.b p.α (intervalDomainLift (u t₀)))) n) :=
  sorry

/-- **`HasSpectralPdeAgreement` from time-localized data (subtype-continuity
form).**

Mirror of `TimeNhdSubtype.Hu_of_restart_localized_of_subtypeCont`: the witness
tuple (`a₀ = coeffs (lift (u τ))`, `M = 2·Msup`, the soft-clamped family `aC`,
`srcC : DuhamelSourceTimeC1 aC`, `offset = τ = t₀/2`) and the eventually-nhds
restart representation `hrep` are IDENTICAL.  In addition this produces, per
`(t₀,x)`:

* `hsrc_coeff`: `aC (t₀−τ) n = coeffs (logisticSourceFun … (lift (u t₀))) n`, via
  `clampedFamily_eq_on` (`τ + (t₀−τ) = t₀ ∈ [τ,d]` where `φ = id`);
* the source continuity / `reflCircle` Fourier-summability — the single isolated
  obstruction `logisticSourceLift_cont_and_fourierSummable`;
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
  -- hsrc_coeff: aC (t₀−τ) n = coeffs (logisticSourceFun … (lift (u t₀))) n
  have hmem_t₀ : τ + (t₀ - τ) ∈ Set.Icc τ d :=
    ⟨by linarith, by rw [hddef]; linarith⟩
  have hsrc_coeff : ∀ n, aC (t₀ - τ) n
      = cosineCoeffs (logisticSourceFun p.a p.b p.α (intervalDomainLift (u t₀))) n := by
    intro n
    simp only [aC]
    rw [clampedFamily_eq_on p u hc' hd' hmem_t₀ n]
    rw [show τ + (t₀ - τ) = t₀ by ring]
  -- continuity + reflCircle Fourier-summability (the single isolated obstruction)
  obtain ⟨hcont, hsum_fourier⟩ :=
    logisticSourceLift_cont_and_fourierSummable p u t₀
  -- envelope of the clamped Duhamel source restricted to horizon τ
  have hsrcOn : DuhamelSourceL1ContOn aC τ := (DuhamelSourceL1Cont.ofTimeC1 srcC).toOn τ
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
  exact ⟨a₀, 2 * Msup, by linarith, ha₀_bd, aC, srcC, τ, hoff,
    hrep, hsrc_coeff, hcont, hsum_fourier, hsum_b, hsum_src, hsum_lb⟩

end ShenWork.Paper2.PdeUWiring
