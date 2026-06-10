/-
  ShenWork/Paper2/IntervalPicardLimitK1.lean

  **K1 producer (R2 route): the source-coefficient time-C¹ quadruple
  `(adott, hderivt, hadotcontt, hMdott)` from the WEAK package + per-compact K2.**

  This is the largest remaining ledger producer.  It dissolves the Provider's
  K1 quadruple

      ∃ adott,
        (∀ σ, 0<σ → σ<T → ∀ k, HasDerivAt
          (fun r => cosineCoeffs (logisticSourceFun p.a p.b p.α (lift (u r))) k)
          (adott σ k) σ)
        ∧ (∀ k, ContinuousOn (fun σ => adott σ k) (Ioo 0 T))
        ∧ (∀ a' b', 0<a' → b'<T → ∃ Mdot, ∀ σ∈Icc a' b', ∀ k, |adott σ k| ≤ Mdot)

  with NO new analytic estimate — pure assembly of already-formalized pieces.

  ## Mathematical chain (verdict: HANDOFF/chatgpt-k1-r2-verdict.md, SOUND)

  1. **Weak restart identity** (`picardLimitRestart_general`) at base `τ := σ/2`
     gives, on a genuine NEIGHBOURHOOD `Ioo τ d ∋ σ`,
        `lift (u r) x = ∑' n, localRestartCoeff a₀ aC (r−τ) n · cos n x`,
     where `aC` is the soft-clamped source family (= the genuine family on the
     id-zone `[τ,d]`), whose `DuhamelSourceTimeC1` package `srcC` is built by
     `clampedSource_duhamelSourceTimeC1` from per-compact K2 + UNSHIFTED K1.
     The τ=σ/2 choice is the ChatGPT adversarial correction: it makes the
     representation hold on an open two-sided neighbourhood, so the per-mode
     FTC gives a genuine two-sided `HasDerivAt` (not a one-sided one).

  2. **Per-mode FTC + series** (`restartCosineSeries_hasDerivAt_time`):
        `HasDerivAt (fun r => lift (u r) x)
          (∑' n, (aC (r−τ) n − λₙ · localRestartCoeff a₀ aC (r−τ) n) cos) σ`,
     for every `r` in the representation neighbourhood — Lemma 2+3 together.

  3. **Chain rule through the logistic** (`logisticSourceFun_hasDerivAt_time`):
        `HasDerivAt (fun r => logisticSourceFun … (lift (u r)) x)
          (v σ x · (a − b(1+α)(lift (u σ) x)^α)) σ`,
     with `v σ x := deriv (fun r => lift (u r) x) σ` (Lemma 4's integrand deriv).

  4. **Parametric cosine coefficient** (`cosineCoeffs_hasDerivAt_of_smooth_param`):
        `HasDerivAt (fun r => cosineCoeffs (logisticSourceFun … (lift (u r))) k)
          (adott σ k) σ`,  `adott σ k := cosineCoeffs (f'σ) k`,
     `f'σ x := v σ x · (a − b(1+α)(lift (u σ) x)^α)`  (Lemma 4 = K1(i)).

  5. **Continuity / compact bound** of `adott` (Lemma 5 = K1(ii),(iii)).

  Hypothesis sets mirror `IntervalPicardLimitTimeNhdLocalized.Hu_of_restart_localized`:
  time-localized `hbsum/hagree/hpost/hubt`, per-compact `hG1t/hG2t`, the weak
  `hsrc0`, `hfix`, slice continuity `hLc`, and the UNSHIFTED source K1 data
  `adott₀/hderivt₀/hadotcontt₀/hMdott₀` consumed by the clamped package.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalPicardLimitTimeNhdLocalized
import ShenWork.Paper2.IntervalPicardLimitRestartBdd

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1 duhamelSpectralCoeff)
open ShenWork.IntervalGradientDuhamelMap (intervalGradientDuhamelMap logisticLifted)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildRegularityBootstrap (restartDuhamelCoeff)
open ShenWork.IntervalSourceCoefficientTimeC1
  (localRestartCoeff restartCosineSeries_hasDerivAt_time
    restartDerivSeries_jointContinuousOn)
open ShenWork.IntervalMildPicardRegularity
  (logisticSourceFun logisticSourceFun_hasDerivAt_time
    cosineCoeffs_hasDerivAt_of_smooth_param cosineCoeffs_eq_factor_mul_integral
    cosineCoeffs_abs_le_of_continuous_bounded)
open ShenWork.IntervalPicardLimitRestartWeak (DuhamelSourceL1ContOn)
open ShenWork.IntervalPicardLimitSourceData
  (restartDuhamelCoeff_eq_localRestartCoeff source_family_eq_w)
open ShenWork.IntervalPicardLimitTimeNhd (picardLimitRestart_general)
open ShenWork.Paper2.ClampedSourceRepresentation
  (clampedSource_duhamelSourceTimeC1 clampedFamily_eq_on)
open ShenWork.IntervalTimeSoftClamp (φ)

noncomputable section

namespace ShenWork.Paper2.PicardLimitK1

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-! ## 0. The K1 derivative datum `adott`.

`adott σ k` is the `k`-th cosine coefficient of the spatial slice
`x ↦ v σ x · (a − b(1+α)(lift (u σ) x)^α)`, where `v σ x` is the genuine time
derivative `deriv (fun r => lift (u r) x) σ` of the solution slice.  All of this
is intrinsic to `u`; the clamped restart machinery only PROVES the `HasDerivAt`
identity, it does not enter the datum. -/

/-- The time-derivative of the solution slice at `(σ, x)` (intrinsic). -/
def slopeSlice (u : ℝ → intervalDomainPoint → ℝ) (σ x : ℝ) : ℝ :=
  deriv (fun r => intervalDomainLift (u r) x) σ

/-- The chain-rule integrand: `f'(u(σ,x)) · ∂_σ u(σ,x)`, the spatial slice whose
cosine coefficients are `adott σ`. -/
def sourceDerivSlice (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (σ x : ℝ) : ℝ :=
  slopeSlice u σ x *
    (p.a - p.b * (1 + p.α) * (intervalDomainLift (u σ) x) ^ p.α)

/-- **The K1 derivative coefficients.**  `adottOf σ k = cosineCoeffs (f'σ) k`. -/
def adottOf (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (σ : ℝ) (k : ℕ) : ℝ :=
  cosineCoeffs (sourceDerivSlice p u σ) k

/-! ## 1. The local restart engine.

For a fixed interior `σ ∈ (0,T)` we set `τ := σ/2` and reproduce the clamped
witness of `Hu_of_restart_localized`: the clamped `DuhamelSourceTimeC1` package
`srcC` and the restart representation, valid on the open neighbourhood
`Ioo τ d ∋ σ`.  This is the τ=σ/2 two-sided correction. -/

/-- **Bundle of the local restart data at an interior time `σ`.**  Mirrors the
clamp setup of `Hu_of_restart_localized`.  Fields: the clamp window endpoints,
the restart-base coefficients `a₀`, their uniform bound `M`, the clamped source
family `aC` with its `DuhamelSourceTimeC1` package `srcC`, and the open
representation neighbourhood `Ioo τ d`. -/
structure LocalRestart
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (T σ : ℝ) where
  τ : ℝ
  d : ℝ
  hτpos : 0 < τ
  hστ : τ < σ
  hσd : σ < d
  hdT : d < T
  /-- the restart-base coefficients `coeffs u(τ)`. -/
  a₀ : ℕ → ℝ
  M : ℝ
  hM_nonneg : 0 ≤ M
  ha₀ : ∀ n, |a₀ n| ≤ M
  /-- the clamped source family. -/
  aC : ℝ → ℕ → ℝ
  srcC : DuhamelSourceTimeC1 aC
  /-- restart representation on the right-neighbourhood `Ioo τ d`. -/
  hrep : ∀ r, r ∈ Set.Ioo τ d → ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 →
    intervalDomainLift (u r) x
      = ∑' n, localRestartCoeff a₀ aC (r - τ) n * cosineMode n x
  /-- positivity of the slice on the representation nbhd (for `rpow`). -/
  hpos : ∀ r, r ∈ Set.Ioo τ d → ∀ x ∈ Set.Icc (0 : ℝ) 1,
    0 < intervalDomainLift (u r) x
  /-- `1 ≤ α` (carried for the chain rule's positivity needs). -/
  hα : 1 ≤ p.α

/-- **Construction of the local restart data.**  The hypothesis set mirrors
`Hu_of_restart_localized` (time-localized `hbsum/hagree/hpost/hubt`, per-compact
`hG1t/hG2t`, the weak `hsrc0`, `hfix`, slice continuity `hLc`, and the UNSHIFTED
K1 data); the clamped `DuhamelSourceTimeC1` and the restart representation are
produced exactly as in that theorem's body. -/
def localRestart_of_ledger
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ} (u : ℝ → intervalDomainPoint → ℝ)
    {T : ℝ}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
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
    (hLc : ∀ t, 0 < t → t < T →
      ∀ s, 0 < s → s ≤ t → Continuous (logisticLifted p (u s)))
    {σ : ℝ} (hσ0 : 0 < σ) (hσT : σ < T) :
    LocalRestart p u T σ := by
  -- restart base / offset (τ = σ/2 — the two-sided correction)
  set τ : ℝ := σ / 2 with hτdef
  have hτpos : 0 < τ := by rw [hτdef]; linarith
  have hτσ : τ < σ := by rw [hτdef]; linarith
  have hτT : τ < T := lt_trans hτσ hσT
  -- clamp window: id-zone [c,d] = [τ, (σ+T)/2], range window [c',d'] ⊂ (0,T)
  set c' : ℝ := σ / 4 with hc'def
  set d : ℝ := (σ + T) / 2 with hddef
  set d' : ℝ := (σ + 3 * T) / 4 with hd'def
  have hc' : c' < τ := by rw [hc'def, hτdef]; linarith
  have hcd : τ ≤ d := by rw [hddef, hτdef]; linarith
  have hd' : d < d' := by rw [hddef, hd'def]; linarith
  have hc'pos : 0 < c' := by rw [hc'def]; linarith
  have hd'T : d' < T := by rw [hd'def]; linarith
  have hσd : σ < d := by rw [hddef]; linarith
  have hdT : d < T := lt_trans hd' hd'T
  -- per-compact bounds on the window [c',d'] ⊂ (0,T)
  have hwin : ∀ s ∈ Set.Icc c' d', 0 < s ∧ s < T := fun s hs =>
    ⟨lt_of_lt_of_le hc'pos hs.1, lt_of_le_of_lt hs.2 hd'T⟩
  set G1 := (hG1t c' d' hc'pos hd'T).choose with hG1def
  have hG1 := (hG1t c' d' hc'pos hd'T).choose_spec
  set G2 := (hG2t c' d' hc'pos hd'T).choose with hG2def
  have hG2 := (hG2t c' d' hc'pos hd'T).choose_spec
  set Mdot := (hMdott c' d' hc'pos hd'T).choose with hMdotdef
  have hMdot := (hMdott c' d' hc'pos hd'T).choose_spec
  -- the clamped TimeC1 witness package (identical to Hu_of_restart_localized)
  have srcC : DuhamelSourceTimeC1
      (fun ρ k => cosineCoeffs (logisticSourceFun p.a p.b p.α
        (intervalDomainLift (u (φ c' τ d d' (τ + ρ))))) k) :=
    clampedSource_duhamelSourceTimeC1 p u hα ha hb hc' hcd hd'
      bc
      (fun ρ hρ => hbsum ρ (hwin ρ hρ).1 (hwin ρ hρ).2)
      (fun ρ hρ => hagree ρ (hwin ρ hρ).1 (hwin ρ hρ).2)
      (fun ρ hρ => hpost ρ (hwin ρ hρ).1 (hwin ρ hρ).2)
      (fun ρ hρ => hubt ρ (hwin ρ hρ).1 (hwin ρ hρ).2)
      hG1 hG2 adott
      (fun ρ hρ k => hderivt ρ (hwin ρ hρ).1 (hwin ρ hρ).2 k)
      (fun k => (hadotcontt k).mono
        (fun ρ hρ => ⟨(hwin ρ hρ).1, (hwin ρ hρ).2⟩))
      hMdot
  -- the restart-base bound
  have hMnn : 0 ≤ Msup := by
    have h1 := hubt τ hτpos hτT 0 ⟨le_rfl, zero_le_one⟩
    have h2 := hpost τ hτpos hτT 0 ⟨le_rfl, zero_le_one⟩
    linarith
  have ha₀ : ∀ k, |cosineCoeffs (intervalDomainLift (u τ)) k| ≤ 2 * Msup := by
    intro k
    refine ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
      (((ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_contDiff_two
        (hbsum τ hτpos hτT)).continuous.continuousOn).congr
          (hagree τ hτpos hτT)) (by linarith) ?_ k
    intro x hx
    rw [abs_of_pos (hpost τ hτpos hτT x hx)]
    exact hubt τ hτpos hτT x hx
  refine
    { τ := τ, d := d, hτpos := hτpos, hστ := hτσ, hσd := hσd, hdT := hdT
      a₀ := cosineCoeffs (intervalDomainLift (u τ)), M := 2 * Msup
      hM_nonneg := by linarith, ha₀ := ha₀
      aC := fun ρ k => cosineCoeffs (logisticSourceFun p.a p.b p.α
        (intervalDomainLift (u (φ c' τ d d' (τ + ρ))))) k
      srcC := srcC
      hpos := fun r hr x hx =>
        hpost r (lt_trans hτpos hr.1) (lt_trans hr.2 hdT) x hx
      hα := hα, hrep := ?_ }
  -- restart representation on Ioo τ d
  intro r hr x hx
  have hτr : τ < r := hr.1
  have hrd : r < d := hr.2
  have hrT : r < T := lt_trans hrd hdT
  have hrpos : 0 < r := lt_trans hτpos hτr
  -- general restart identity at time r, base τ, horizon r − τ (canonical family)
  have heqon := picardLimitRestart_general p hχ0 u₀ u
    (fun s hs hsr => hfix s hs (lt_of_le_of_lt hsr hrT))
    hu₀_cont hu₀_bound hsrc0 hτpos hτr hrT.le
    (fun s hs hsr => hLc r hrpos hrT s hs hsr)
  rw [heqon hx]
  refine tsum_congr (fun k => ?_)
  congr 1
  -- restartDuhamelCoeff (canonical shifted) = localRestartCoeff (clamped)
  rw [restartDuhamelCoeff_eq_localRestartCoeff]
  unfold localRestartCoeff
  congr 1
  -- Duhamel parts: integrands agree on [0, r−τ] (absolute times in [τ,r] ⊆ [τ,d])
  unfold duhamelSpectralCoeff
  apply intervalIntegral.integral_congr
  intro ρ hρ
  rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ r - τ)] at hρ
  have hmem_cd : τ + ρ ∈ Set.Icc τ d :=
    ⟨by linarith [hρ.1], by linarith [hρ.2, hrd.le]⟩
  simp only
  congr 1
  rw [clampedFamily_eq_on p u hc' hd' hmem_cd k]
  exact congrFun (congrFun (source_family_eq_w p u) (τ + ρ)) k

/-! ## 2. Time derivative of the solution slice (Lemmas 2+3). -/

namespace LocalRestart

variable {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {T σ : ℝ}
  (L : LocalRestart p u T σ)

/-- The restart time-derivative series at offset time `ρ` (= `r − τ`):
`v_series ρ x = ∑' n, (aC ρ n − λₙ · localRestartCoeff a₀ aC ρ n) cos(nπx)`. -/
def vSeries (ρ x : ℝ) : ℝ :=
  ∑' n, (L.aC ρ n - unitIntervalCosineEigenvalue n *
    localRestartCoeff L.a₀ L.aC ρ n) * cosineMode n x

/-- **Lemma 2+3: time derivative of the solution slice.**  For `r` in the open
representation neighbourhood `Ioo τ d`, the slice `s ↦ lift (u s) x` has time
derivative `vSeries L (r − τ) x` at `r` (`restartCosineSeries_hasDerivAt_time`
through the `s ↦ s − τ` chain rule, transferred by `congr_of_eventuallyEq`). -/
theorem hasDerivAt_slice {r : ℝ} (hr : r ∈ Set.Ioo L.τ L.d)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    HasDerivAt (fun s => intervalDomainLift (u s) x) (L.vSeries (r - L.τ) x) r := by
  have hrτ : 0 < r - L.τ := by have := hr.1; linarith
  -- the restart series HasDerivAt at offset r − τ
  have hspec := restartCosineSeries_hasDerivAt_time L.hM_nonneg L.ha₀ L.srcC hrτ x
  have hshift : HasDerivAt (fun s : ℝ => s - L.τ) 1 r :=
    (hasDerivAt_id r).sub_const L.τ
  have hcomp := hspec.comp r hshift
  simp only [mul_one] at hcomp
  -- transfer to the genuine slice via the representation on the open nbhd.
  -- The representation `hrep` is stated only on Icc 0 1, but for r' ranging in the
  -- open nbhd Ioo τ d the FIXED x ∈ Icc 0 1 always lands in the agreement set.
  have hev : (fun s => intervalDomainLift (u s) x) =ᶠ[𝓝 r]
      (fun s => ∑' n, localRestartCoeff L.a₀ L.aC (s - L.τ) n * cosineMode n x) := by
    refine Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hr) (fun s hs => ?_)
    exact L.hrep s hs x hx
  exact (hcomp.congr_of_eventuallyEq hev).congr_deriv rfl

/-- `σ ∈ Ioo τ d`, so the slice derivative at `σ` is the series at offset `σ − τ`. -/
theorem hσ_mem : σ ∈ Set.Ioo L.τ L.d := ⟨L.hστ, L.hσd⟩

/-- **The intrinsic slope equals the restart-derivative series**, at any `r` in
the representation neighbourhood. -/
theorem slopeSlice_eq {r : ℝ} (hr : r ∈ Set.Ioo L.τ L.d)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    slopeSlice u r x = L.vSeries (r - L.τ) x :=
  (L.hasDerivAt_slice hr hx).deriv

/-- **Joint continuity of the restart-derivative series.**  On `Ioi 0 ×ˢ univ`,
`(ρ, x) ↦ vSeries L ρ x` is jointly continuous (`restartDerivSeries_jointContinuousOn`). -/
theorem vSeries_jointContinuousOn :
    ContinuousOn (Function.uncurry (fun ρ x => L.vSeries ρ x))
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) :=
  restartDerivSeries_jointContinuousOn L.hM_nonneg L.ha₀ L.srcC

/-- The restart VALUE series: `lift (u r) x = ∑' localRestartCoeff a₀ aC (r−τ) n cos`. -/
def valueSeries (ρ x : ℝ) : ℝ :=
  ∑' n, localRestartCoeff L.a₀ L.aC ρ n * cosineMode n x

/-- `lift (u r) x = valueSeries L (r − τ) x` on the representation nbhd × Icc 0 1. -/
theorem lift_eq_valueSeries {r : ℝ} (hr : r ∈ Set.Ioo L.τ L.d)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    intervalDomainLift (u r) x = L.valueSeries (r - L.τ) x :=
  L.hrep r hr x hx

/-- **Joint continuity of the restart value series** on `Ioi 0 ×ˢ univ`
(`restartSeries_jointContinuousOn`). -/
theorem valueSeries_jointContinuousOn :
    ContinuousOn (Function.uncurry (fun ρ x => L.valueSeries ρ x))
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) :=
  ShenWork.IntervalSourceCoefficientTimeC1.restartSeries_jointContinuousOn
    L.hM_nonneg L.ha₀ L.srcC

/-! ### 2b. The chain rule through the logistic nonlinearity (Lemma 4 core). -/

/-- **Pointwise time-derivative of the logistic source.**  For `r` in the
representation nbhd and `x ∈ Icc 0 1`, the value `logisticSourceFun … (lift(u r)) x`
has time derivative `sourceDerivSlice p u r x` at `r` — the chain rule
`logisticSourceFun_hasDerivAt_time` applied to `hasDerivAt_slice` (positivity
from `hpos`). -/
theorem hasDerivAt_logisticSlice {r : ℝ} (hr : r ∈ Set.Ioo L.τ L.d)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    HasDerivAt (fun s => logisticSourceFun p.a p.b p.α (intervalDomainLift (u s)) x)
      (sourceDerivSlice p u r x) r := by
  have hslice := L.hasDerivAt_slice hr hx
  have hpos := L.hpos r hr x hx
  have hα0 : 0 < p.α := lt_of_lt_of_le zero_lt_one L.hα
  have hchain := logisticSourceFun_hasDerivAt_time (a := p.a) (b := p.b) (α := p.α)
    (f := fun s => intervalDomainLift (u s) x) (σ := r) hα0 hpos hslice
  -- rewrite both the function (logisticSourceFun unfold) and the value (sourceDerivSlice)
  unfold logisticSourceFun sourceDerivSlice slopeSlice
  rw [(L.hasDerivAt_slice hr hx).deriv]
  exact hchain

/-! ### 2c. Continuity of the chain-rule derivative slice (Lemma 5 core). -/

/-- The chain-rule derivative slice in SERIES form, valid on the nbhd × Icc 0 1.
`sourceDerivSlice p u r x = vSeries L (r−τ) x · (a − b(1+α)(valueSeries L (r−τ) x)^α)`. -/
theorem sourceDerivSlice_eq_series {r : ℝ} (hr : r ∈ Set.Ioo L.τ L.d)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    sourceDerivSlice p u r x
      = L.vSeries (r - L.τ) x *
        (p.a - p.b * (1 + p.α) * (L.valueSeries (r - L.τ) x) ^ p.α) := by
  unfold sourceDerivSlice
  rw [L.slopeSlice_eq hr hx, L.lift_eq_valueSeries hr hx]

/-- **Joint continuity of the chain-rule derivative slice** on the time-slab
`Icc a' b' ⊆ Ioo τ d` against `Icc 0 1`.  From the series form: `vSeries` and
`valueSeries` are jointly continuous (with the shift `s ↦ s − τ`), the base of
the `rpow` is positive (`hpos`), so `(valueSeries)^α` is jointly continuous. -/
theorem sourceDerivSlice_continuousOn_slab {a' b' : ℝ}
    (hsub : Set.Icc a' b' ⊆ Set.Ioo L.τ L.d) :
    ContinuousOn (Function.uncurry (fun s x => sourceDerivSlice p u s x))
      (Set.Icc a' b' ×ˢ Set.Icc (0:ℝ) 1) := by
  -- shift map (s, x) ↦ (s − τ, x), mapping the slab into Ioi 0 ×ˢ univ
  set Φ : ℝ × ℝ → ℝ × ℝ := fun q => (q.1 - L.τ, q.2) with hΦ
  have hΦcont : Continuous Φ := (continuous_fst.sub continuous_const).prodMk continuous_snd
  have hmaps : Set.MapsTo Φ (Set.Icc a' b' ×ˢ Set.Icc (0:ℝ) 1)
      (Set.Ioi (0:ℝ) ×ˢ Set.univ) := by
    intro q hq
    obtain ⟨hq1, _⟩ := Set.mem_prod.mp hq
    refine Set.mem_prod.mpr ⟨?_, Set.mem_univ _⟩
    have hr : q.1 ∈ Set.Ioo L.τ L.d := hsub hq1
    exact Set.mem_Ioi.mpr (by have := hr.1; simp only [Φ]; linarith)
  -- vSeries ∘ Φ and valueSeries ∘ Φ jointly continuous on the slab
  have hvS : ContinuousOn (fun q : ℝ × ℝ => L.vSeries (q.1 - L.τ) q.2)
      (Set.Icc a' b' ×ˢ Set.Icc (0:ℝ) 1) :=
    (L.vSeries_jointContinuousOn.comp hΦcont.continuousOn hmaps)
  have hwS : ContinuousOn (fun q : ℝ × ℝ => L.valueSeries (q.1 - L.τ) q.2)
      (Set.Icc a' b' ×ˢ Set.Icc (0:ℝ) 1) :=
    (L.valueSeries_jointContinuousOn.comp hΦcont.continuousOn hmaps)
  -- positivity of the rpow base on the slab
  have hposS : ∀ q ∈ Set.Icc a' b' ×ˢ Set.Icc (0:ℝ) 1,
      0 < L.valueSeries (q.1 - L.τ) q.2 := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := Set.mem_prod.mp hq
    rw [← L.lift_eq_valueSeries (hsub hq1) hq2]
    exact L.hpos q.1 (hsub hq1) q.2 hq2
  -- (valueSeries)^α jointly continuous (positive base)
  have hpow : ContinuousOn
      (fun q : ℝ × ℝ => (L.valueSeries (q.1 - L.τ) q.2) ^ p.α)
      (Set.Icc a' b' ×ˢ Set.Icc (0:ℝ) 1) := by
    apply ContinuousOn.rpow_const hwS
    intro q hq; exact Or.inl (ne_of_gt (hposS q hq))
  -- assemble the product
  have hprod : ContinuousOn
      (fun q : ℝ × ℝ => L.vSeries (q.1 - L.τ) q.2 *
        (p.a - p.b * (1 + p.α) * (L.valueSeries (q.1 - L.τ) q.2) ^ p.α))
      (Set.Icc a' b' ×ˢ Set.Icc (0:ℝ) 1) :=
    hvS.mul ((continuousOn_const).sub ((continuousOn_const).mul hpow))
  -- congr to sourceDerivSlice on the slab
  apply hprod.congr
  intro q hq
  obtain ⟨hq1, hq2⟩ := Set.mem_prod.mp hq
  simp only [Function.uncurry]
  exact L.sourceDerivSlice_eq_series (hsub hq1) hq2

/-- **Spatial continuity of the logistic source slice** at a single time `r` in
the nbhd, on `Icc 0 1` (the `hf_cont` ingredient).  From the value series form
of `lift(u r)` on `Icc 0 1`. -/
theorem logisticSlice_continuousOn {r : ℝ} (hr : r ∈ Set.Ioo L.τ L.d) :
    ContinuousOn (logisticSourceFun p.a p.b p.α (intervalDomainLift (u r)))
      (Set.Icc (0:ℝ) 1) := by
  -- value series in x (fixed time r), continuous on Icc 0 1
  have hrτ : 0 < r - L.τ := by have := hr.1; linarith
  have hsec : ContinuousOn (fun x => L.valueSeries (r - L.τ) x) (Set.Icc (0:ℝ) 1) := by
    have hmaps : Set.MapsTo (fun x : ℝ => ((r - L.τ, x) : ℝ × ℝ))
        (Set.Icc (0:ℝ) 1) (Set.Ioi (0:ℝ) ×ˢ Set.univ) :=
      fun x _ => Set.mem_prod.mpr ⟨Set.mem_Ioi.mpr hrτ, Set.mem_univ _⟩
    exact L.valueSeries_jointContinuousOn.comp
      (continuousOn_const.prodMk continuousOn_id) hmaps
  have hpos : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 < L.valueSeries (r - L.τ) x := by
    intro x hx; rw [← L.lift_eq_valueSeries hr hx]; exact L.hpos r hr x hx
  have hpow : ContinuousOn (fun x => (L.valueSeries (r - L.τ) x) ^ p.α)
      (Set.Icc (0:ℝ) 1) :=
    hsec.rpow_const (fun x hx => Or.inl (ne_of_gt (hpos x hx)))
  have hbody : ContinuousOn (fun x => L.valueSeries (r - L.τ) x *
      (p.a - p.b * (L.valueSeries (r - L.τ) x) ^ p.α)) (Set.Icc (0:ℝ) 1) :=
    hsec.mul (continuousOn_const.sub (continuousOn_const.mul hpow))
  apply hbody.congr
  intro x hx
  unfold logisticSourceFun
  rw [L.lift_eq_valueSeries hr hx]

include L in
/-- **Lemma 4 = K1(i).**  The source coefficient `r ↦ cosineCoeffs (logisticSourceFun
… (lift(u r))) k` has time derivative `adottOf p u σ k` at `σ`. -/
theorem hasDerivAt_sourceCoeff (k : ℕ) :
    HasDerivAt
      (fun r => cosineCoeffs
        (logisticSourceFun p.a p.b p.α (intervalDomainLift (u r))) k)
      (adottOf p u σ k) σ := by
  set δ : ℝ := min (σ - L.τ) (L.d - σ) / 2 with hδdef
  have hδ1 : 0 < σ - L.τ := by have := L.hστ; linarith
  have hδ2 : 0 < L.d - σ := by have := L.hσd; linarith
  have hδ : 0 < δ := by rw [hδdef]; have := lt_min hδ1 hδ2; linarith
  have hδle1 : δ ≤ (σ - L.τ) / 2 := by
    rw [hδdef]; have := min_le_left (σ - L.τ) (L.d - σ); linarith
  have hδle2 : δ ≤ (L.d - σ) / 2 := by
    rw [hδdef]; have := min_le_right (σ - L.τ) (L.d - σ); linarith
  -- ball σ δ ⊆ Ioo τ d
  have hball : Metric.ball σ δ ⊆ Set.Ioo L.τ L.d := by
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    exact ⟨by linarith [hs.1, hδle1], by linarith [hs.2, hδle2]⟩
  -- slab Icc(σ-δ)(σ+δ) ⊆ Ioo τ d
  have hslab : Set.Icc (σ - δ) (σ + δ) ⊆ Set.Ioo L.τ L.d := by
    intro s hs
    exact ⟨by linarith [hs.1, hδle1], by linarith [hs.2, hδle2]⟩
  -- assemble the three smooth-param hypotheses
  have hf_cont : ∀ᶠ s in 𝓝 σ,
      ContinuousOn (logisticSourceFun p.a p.b p.α (intervalDomainLift (u s)))
        (Set.Icc (0:ℝ) 1) := by
    refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds L.hσ_mem) (fun s hs => ?_)
    exact L.logisticSlice_continuousOn hs
  have h_diff : ∀ x ∈ Set.Ioo (0:ℝ) 1, ∀ s ∈ Metric.ball σ δ,
      HasDerivAt (fun r => logisticSourceFun p.a p.b p.α (intervalDomainLift (u r)) x)
        (sourceDerivSlice p u s x) s := by
    intro x hx s hs
    exact L.hasDerivAt_logisticSlice (hball hs) (Set.Ioo_subset_Icc_self hx)
  have h_cont_deriv : ContinuousOn (Function.uncurry (sourceDerivSlice p u))
      (Set.Icc (σ - δ) (σ + δ) ×ˢ Set.Icc (0:ℝ) 1) :=
    L.sourceDerivSlice_continuousOn_slab hslab
  have hmain := cosineCoeffs_hasDerivAt_of_smooth_param
    (f := fun r => logisticSourceFun p.a p.b p.α (intervalDomainLift (u r)))
    (f' := sourceDerivSlice p u) (τ := σ) (n := k)
    hδ hf_cont h_diff h_cont_deriv
  -- the derivative value is cosineCoeffs (sourceDerivSlice p u σ) k = adottOf p u σ k
  exact hmain

end LocalRestart

/-! ## 3. The K1 producer: assembling the quadruple. -/

open ShenWork.Paper2.PicardLimitK1.LocalRestart

set_option maxHeartbeats 1600000 in
set_option linter.style.maxHeartbeats false in
/-- **The K1 producer (final).**  From the same ledger hypotheses as
`Hu_of_restart_localized` (time-localized `hbsum/hagree/hpost/hubt`, per-compact
`hG1t/hG2t`, weak `hsrc0`, `hfix`, slice continuity `hLc`, and the UNSHIFTED
source K1 data), the source-coefficient family `adottOf p u` satisfies the
Provider's K1 quadruple: pointwise time `HasDerivAt` on `(0,T)`, per-`k`
`ContinuousOn` on `Ioo 0 T`, and the per-compact uniform bound. -/
theorem k1_quadruple
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ} (u : ℝ → intervalDomainPoint → ℝ)
    {T : ℝ}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
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
    (adott0 : ℝ → ℕ → ℝ)
    (hderivt0 : ∀ σ, 0 < σ → σ < T → ∀ k, HasDerivAt
      (fun r => cosineCoeffs
        (logisticSourceFun p.a p.b p.α (intervalDomainLift (u r))) k)
      (adott0 σ k) σ)
    (hadotcontt0 : ∀ k, ContinuousOn (fun σ => adott0 σ k) (Set.Ioo 0 T))
    (hMdott0 : ∀ a' b', 0 < a' → b' < T → ∃ Mdot, ∀ σ ∈ Set.Icc a' b',
      ∀ k, |adott0 σ k| ≤ Mdot)
    (hLc : ∀ t, 0 < t → t < T →
      ∀ s, 0 < s → s ≤ t → Continuous (logisticLifted p (u s))) :
    (∀ σ, 0 < σ → σ < T → ∀ k, HasDerivAt
        (fun r => cosineCoeffs
          (logisticSourceFun p.a p.b p.α (intervalDomainLift (u r))) k)
        (adottOf p u σ k) σ)
      ∧ (∀ k, ContinuousOn (fun σ => adottOf p u σ k) (Set.Ioo 0 T))
      ∧ (∀ a' b', 0 < a' → b' < T → ∃ Mdot, ∀ σ ∈ Set.Icc a' b',
          ∀ k, |adottOf p u σ k| ≤ Mdot) := by
  -- per-point local restart bundle
  have mkL : ∀ σ, 0 < σ → σ < T → LocalRestart p u T σ := fun σ hσ0 hσT =>
    localRestart_of_ledger hχ0 u hα ha hb hu₀_cont hu₀_bound hfix hsrc0 bc
      hbsum hagree hpost hubt hG1t hG2t adott0 hderivt0 hadotcontt0 hMdott0 hLc hσ0 hσT
  -- K1(i): the HasDerivAt, per point, via the local engine
  have hderiv : ∀ σ, 0 < σ → σ < T → ∀ k, HasDerivAt
      (fun r => cosineCoeffs
        (logisticSourceFun p.a p.b p.α (intervalDomainLift (u r))) k)
      (adottOf p u σ k) σ :=
    fun σ hσ0 hσT k => (mkL σ hσ0 hσT).hasDerivAt_sourceCoeff k
  -- Global joint continuity of the chain-rule slice on Ioo 0 T ×ˢ Icc 0 1.
  have hslice_cont : ContinuousOn (Function.uncurry (sourceDerivSlice p u))
      (Set.Ioo 0 T ×ˢ Set.Icc (0:ℝ) 1) := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := Set.mem_prod.mp hq
    set σ₀ := q.1 with hσ₀
    have hσ₀0 : 0 < σ₀ := hq1.1
    have hσ₀T : σ₀ < T := hq1.2
    set L := mkL σ₀ hσ₀0 hσ₀T with hLdef
    -- a closed time-window strictly inside Ioo τ d, with σ₀ interior
    set δ : ℝ := min (σ₀ - L.τ) (L.d - σ₀) / 2 with hδdef
    have hδ1 : 0 < σ₀ - L.τ := by have := L.hστ; linarith
    have hδ2 : 0 < L.d - σ₀ := by have := L.hσd; linarith
    have hδ : 0 < δ := by rw [hδdef]; have := lt_min hδ1 hδ2; linarith
    have hδle1 : δ ≤ (σ₀ - L.τ) / 2 := by
      rw [hδdef]; have := min_le_left (σ₀ - L.τ) (L.d - σ₀); linarith
    have hδle2 : δ ≤ (L.d - σ₀) / 2 := by
      rw [hδdef]; have := min_le_right (σ₀ - L.τ) (L.d - σ₀); linarith
    have hslab_sub : Set.Icc (σ₀ - δ) (σ₀ + δ) ⊆ Set.Ioo L.τ L.d := fun s hs =>
      ⟨by linarith [hs.1, hδle1], by linarith [hs.2, hδle2]⟩
    have hslabcont := L.sourceDerivSlice_continuousOn_slab hslab_sub
    -- the slab is a neighborhood-within of q in the ambient product
    have hmem : q ∈ Set.Icc (σ₀ - δ) (σ₀ + δ) ×ˢ Set.Icc (0:ℝ) 1 :=
      Set.mem_prod.mpr ⟨⟨by linarith, by linarith⟩, hq2⟩
    have hnhds : Set.Icc (σ₀ - δ) (σ₀ + δ) ×ˢ Set.Icc (0:ℝ) 1
        ∈ 𝓝[Set.Ioo 0 T ×ˢ Set.Icc (0:ℝ) 1] q := by
      -- the open box `Ioo(σ₀-δ)(σ₀+δ) ×ˢ univ` is a nbhd of q; intersected with
      -- the ambient set it lands inside the closed slab.
      have hopen : Set.Ioo (σ₀ - δ) (σ₀ + δ) ×ˢ (Set.univ : Set ℝ) ∈ 𝓝 q := by
        apply (isOpen_Ioo.prod isOpen_univ).mem_nhds
        exact Set.mem_prod.mpr ⟨⟨by linarith, by linarith⟩, Set.mem_univ _⟩
      have hinter := Filter.inter_mem (Filter.mem_inf_of_left hopen)
        (self_mem_nhdsWithin (a := q) (s := Set.Ioo 0 T ×ˢ Set.Icc (0:ℝ) 1))
      refine Filter.mem_of_superset hinter ?_
      intro y hy
      obtain ⟨hy1, hy2⟩ := hy
      exact Set.mem_prod.mpr ⟨⟨(Set.mem_prod.mp hy1).1.1.le,
        (Set.mem_prod.mp hy1).1.2.le⟩, (Set.mem_prod.mp hy2).2⟩
    exact (hslabcont.continuousWithinAt hmem).mono_of_mem_nhdsWithin hnhds
  -- K1(ii): continuity of each coefficient via parametric integral continuity.
  -- adottOf σ k = factor · ∫_{Icc 0 1} cos(kπx)·sourceDerivSlice σ x dx; the
  -- integrand is jointly continuous on the slab, so the parametric integral is
  -- continuous (`continuous_parametric_integral_of_continuous` on a compact
  -- time-subtype), transferred to a `ContinuousWithinAt` at each σ₀.
  have hcont : ∀ k, ContinuousOn (fun σ => adottOf p u σ k) (Set.Ioo 0 T) := by
    intro k σ₀ hσ₀
    have hσ₀0 : 0 < σ₀ := hσ₀.1
    have hσ₀T : σ₀ < T := hσ₀.2
    set L := mkL σ₀ hσ₀0 hσ₀T with hLdef
    set δ : ℝ := min (σ₀ - L.τ) (L.d - σ₀) / 2 with hδdef
    have hδ1 : 0 < σ₀ - L.τ := by have := L.hστ; linarith
    have hδ2 : 0 < L.d - σ₀ := by have := L.hσd; linarith
    have hδ : 0 < δ := by rw [hδdef]; have := lt_min hδ1 hδ2; linarith
    have hδle1 : δ ≤ (σ₀ - L.τ) / 2 := by
      rw [hδdef]; have := min_le_left (σ₀ - L.τ) (L.d - σ₀); linarith
    have hδle2 : δ ≤ (L.d - σ₀) / 2 := by
      rw [hδdef]; have := min_le_right (σ₀ - L.τ) (L.d - σ₀); linarith
    set I : Set ℝ := Set.Icc (σ₀ - δ) (σ₀ + δ) with hIdef
    have hIsub : I ⊆ Set.Ioo L.τ L.d := fun s hs =>
      ⟨by linarith [hs.1, hδle1], by linarith [hs.2, hδle2]⟩
    have hσ₀mem : σ₀ ∈ I := ⟨by linarith, by linarith⟩
    have hslabcont := L.sourceDerivSlice_continuousOn_slab hIsub
    -- the weighted integrand
    set F : ℝ → ℝ → ℝ := fun σ x =>
      Real.cos ((k : ℝ) * Real.pi * x) * sourceDerivSlice p u σ x with hFdef
    have hcos_cont : Continuous (fun x : ℝ => Real.cos ((k : ℝ) * Real.pi * x)) :=
      Real.continuous_cos.comp (continuous_const.mul continuous_id')
    have hFcont : ContinuousOn (Function.uncurry F) (I ×ˢ Set.Icc (0:ℝ) 1) :=
      (hcos_cont.comp continuous_snd).continuousOn.mul hslabcont
    -- uniform bound `B'` on the integrand over the slab (compactness)
    have hKcompact : IsCompact (I ×ˢ Set.Icc (0:ℝ) 1) := isCompact_Icc.prod isCompact_Icc
    obtain ⟨B, hB⟩ := (hKcompact.bddAbove_image hFcont.norm)
    set B' := max B 0 with hB'def
    have hB'nn : 0 ≤ B' := le_max_right _ _
    have hFbd : ∀ σ ∈ I, ∀ x ∈ Set.Icc (0:ℝ) 1, ‖F σ x‖ ≤ B' := by
      intro σ hσ x hx
      have : ‖Function.uncurry F (σ, x)‖ ≤ B :=
        hB (Set.mem_image_of_mem _ (Set.mem_prod.mpr ⟨hσ, hx⟩))
      exact le_trans this (le_max_left _ _)
    -- section continuity in x (for measurability, near σ₀)
    have hsec_cont : ∀ σ ∈ I, ContinuousOn (F σ) (Set.Icc (0:ℝ) 1) := by
      intro σ hσ
      have hsslice : ContinuousOn (sourceDerivSlice p u σ) (Set.Icc (0:ℝ) 1) :=
        hslabcont.comp (continuousOn_const.prodMk continuousOn_id)
          (fun x hx => Set.mem_prod.mpr ⟨hσ, hx⟩)
      exact (hcos_cont.continuousOn).mul hsslice
    -- I is a neighbourhood of σ₀
    have hInhds : I ∈ 𝓝 σ₀ := by
      have : Set.Ioo (σ₀ - δ) (σ₀ + δ) ⊆ I := fun y hy => ⟨hy.1.le, hy.2.le⟩
      exact Filter.mem_of_superset
        (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩) this
    -- ContinuousAt of the interval integral at σ₀, via dominated convergence
    have hint_cont : ContinuousAt (fun σ => ∫ x in (0:ℝ)..1, F σ x) σ₀ := by
      refine intervalIntegral.continuousAt_of_dominated_interval
        (bound := fun _ => B') ?_ ?_ intervalIntegrable_const ?_
      · -- measurability of (F σ) on Ι 0 1, for σ near σ₀
        filter_upwards [hInhds] with σ hσ
        have : ContinuousOn (F σ) (Set.uIcc (0:ℝ) 1) := by
          rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hsec_cont σ hσ
        exact (this.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
      · -- dominating bound near σ₀
        filter_upwards [hInhds] with σ hσ
        refine Filter.Eventually.of_forall (fun x hx => ?_)
        rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
        exact hFbd σ hσ x ⟨hx.1.le, hx.2⟩
      · -- a.e. x: ContinuousAt (fun σ => F σ x) σ₀ from joint continuity
        refine Filter.Eventually.of_forall (fun x hx => ?_)
        rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
        have hxIcc : x ∈ Set.Icc (0:ℝ) 1 := ⟨hx.1.le, hx.2⟩
        have hpt : (σ₀, x) ∈ I ×ˢ Set.Icc (0:ℝ) 1 :=
          Set.mem_prod.mpr ⟨hσ₀mem, hxIcc⟩
        have hcwa : ContinuousWithinAt (fun σ => F σ x) I σ₀ := by
          have := (hFcont.comp (continuousOn_id.prodMk continuousOn_const)
            (fun σ hσ => Set.mem_prod.mpr ⟨hσ, hxIcc⟩)).continuousWithinAt hσ₀mem
          simpa [Function.uncurry] using this
        exact hcwa.continuousAt hInhds
    -- adottOf σ k = factor · ∫ 0..1 F σ x
    have hadeq : ∀ σ, adottOf p u σ k =
        (if k = 0 then (1:ℝ) else 2) * ∫ x in (0:ℝ)..1, F σ x := by
      intro σ; unfold adottOf; rw [cosineCoeffs_eq_factor_mul_integral]
    have hcont_at : ContinuousAt (fun σ => adottOf p u σ k) σ₀ := by
      have hfun : (fun σ => adottOf p u σ k)
          = (fun σ => (if k = 0 then (1:ℝ) else 2) * ∫ x in (0:ℝ)..1, F σ x) :=
        funext hadeq
      rw [hfun]
      exact hint_cont.const_mul _
    exact hcont_at.continuousWithinAt
  -- K1(iii): per-compact uniform bound from compactness of the slab.
  have hbound : ∀ a' b', 0 < a' → b' < T → ∃ Mdot, ∀ σ ∈ Set.Icc a' b',
      ∀ k, |adottOf p u σ k| ≤ Mdot := by
    intro a' b' ha' hb'
    -- the compact slab sits inside Ioo 0 T ×ˢ Icc 0 1
    set K := Set.Icc a' b' ×ˢ Set.Icc (0:ℝ) 1 with hKdef
    have hKsub : K ⊆ Set.Ioo 0 T ×ˢ Set.Icc (0:ℝ) 1 := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := Set.mem_prod.mp hq
      exact Set.mem_prod.mpr ⟨⟨lt_of_lt_of_le ha' hq1.1, lt_of_le_of_lt hq1.2 hb'⟩, hq2⟩
    have hKcompact : IsCompact K := (isCompact_Icc).prod (isCompact_Icc)
    -- continuity of the slice on K ⟹ bounded
    have hcontK : ContinuousOn (Function.uncurry (sourceDerivSlice p u)) K :=
      hslice_cont.mono hKsub
    obtain ⟨B, hB⟩ := (hKcompact.bddAbove_image
      (hcontK.norm)).imp (fun B hB => hB)
    -- B bounds ‖sourceDerivSlice σ x‖ on K; set B' := max B 0 ≥ 0
    set B' := max B 0 with hB'def
    have hB'nn : 0 ≤ B' := le_max_right _ _
    have hbd : ∀ σ ∈ Set.Icc a' b', ∀ x ∈ Set.Icc (0:ℝ) 1,
        |sourceDerivSlice p u σ x| ≤ B' := by
      intro σ hσ x hx
      have hmem : (σ, x) ∈ K := Set.mem_prod.mpr ⟨hσ, hx⟩
      have : ‖Function.uncurry (sourceDerivSlice p u) (σ, x)‖ ≤ B :=
        hB (Set.mem_image_of_mem _ hmem)
      simp only [Function.uncurry, Real.norm_eq_abs] at this
      exact le_trans this (le_max_left _ _)
    refine ⟨2 * B', fun σ hσ k => ?_⟩
    -- slice continuity in x for fixed σ ∈ Icc a' b'
    have hsec : ContinuousOn (sourceDerivSlice p u σ) (Set.Icc (0:ℝ) 1) := by
      have hmaps : Set.MapsTo (fun x : ℝ => ((σ, x) : ℝ × ℝ))
          (Set.Icc (0:ℝ) 1) K :=
        fun x hx => Set.mem_prod.mpr ⟨hσ, hx⟩
      exact hcontK.comp (continuousOn_const.prodMk continuousOn_id) hmaps
    exact cosineCoeffs_abs_le_of_continuous_bounded hsec hB'nn
      (fun x hx => hbd σ hσ x hx) k
  exact ⟨hderiv, hcont, hbound⟩

end ShenWork.Paper2.PicardLimitK1
