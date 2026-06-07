/-
  ShenWork/Paper2/IntervalPicardLimitTimeNhd.lean

  Ledger reduction — discharge `Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u`
  from the limit's restart representation, GENERALISED to an arbitrary restart
  point.

  ## What ★-weak gives, and what `Hu` needs

  `IntervalPicardLimitRestartWeak.picardLimitRestart_cosineIdentity_weak` (★-weak)
  proves, for EACH time `t`, the restart identity AT TIME `t` with restart point
  `t/2`:

      u t = ∑ₖ restartDuhamelCoeff (coeffs u(t/2)) (source from t/2) (t/2) · cos.

  But `HasTimeNeighborhoodSpectralAgreement` (the `Hu` residual) asks, at each
  interior `t₀`, for ONE choice `offset := t₀/2` and ONE source family `a`, such
  that for ALL `s` in a neighbourhood of `t₀`:

      u s = ∑ₖ localRestartCoeff a₀ a (s − offset) · cos.

  That is the restart identity AT TIME `s` with restart point `t₀/2` (NOT `s/2`)
  and horizon `s − t₀/2` varying — a DIFFERENT identity from ★-weak's.

  ## The general restart identity (provable by the same pipeline)

  The algebra of ★-weak factors through `duhamelSpectralCoeff_halfstep_split`,
  which splits `∫₀^{τ+τ} = ∫₀^τ + ∫_τ^{τ+τ}` (restart at `τ = t/2`).  The general
  split `∫₀ᵗ = ∫₀^τ + ∫_τ^t` for ANY `0 < τ < t` is the SAME algebra; we prove it
  here as `duhamelSpectralCoeff_general_split`.  With it, the coefficient-level
  identity

      limitCoeff t = restartDuhamelCoeff (coeffs u(τ)) (source from τ) (t − τ)

  follows for any `0 < τ < t` (`limitCoeff_eq_restartDuhamelCoeff_general`), where
  `coeffs u(τ) = limitCoeff τ` is supplied by ★-weak's already-general
  `cosineCoeffs_halfstep_eq_limitCoeff_weak` (its `τ` hypothesis is `0 < τ`, NOT
  `τ = t/2`).  Combined with the limit's restart representation
  `limit_lift_eq_cosineSeries_weak`, this yields the EqOn

      picardLimitRestart_general : u t = ∑ₖ restartDuhamelCoeff (coeffs u(τ))
        (source from τ) (t − τ) · cos      on [0,1],   for 0 < τ < t.

  ## Discharging `Hu`

  At `t₀ ∈ (0,T)` pick `offset := t₀/2`, `a₀ := coeffs u(t₀/2)`, `a := source
  family from t₀/2`.  For `s` in the right half-neighbourhood `(t₀/2, T) ∩ 𝓝 t₀`
  (eventually-nhds via the open interval `Ioo (t₀/2) T ∋ t₀`), the general identity
  with `τ := t₀/2`, `t := s`, horizon `s − t₀/2` holds; the restart-coefficient
  bridge `restartDuhamelCoeff_eq_localRestartCoeff` rewrites it into the
  `localRestartCoeff`/`x.1` shape the def demands.  The `∃`-fields:
    * `M := 2·Msup`, `|a₀ k| ≤ M` from `cosineCoeffs_abs_le_of_continuous_bounded`
      on the slice `lift (u(t₀/2))` (continuous, bounded by `Msup`);
    * `a := source from t₀/2`, with `DuhamelSourceTimeC1 a` forward-derived by the
      ledger's own `limitSource_duhamelSourceTimeC1` from the SAME `t/2`-shifted
      K2/K1 families the ledger already carries — NO new residual;
    * `offset := t₀/2`, `0 < t₀ − offset = t₀/2`.

  ## Net ledger reduction

  `Hu_of_restart` produces `HasTimeNeighborhoodSpectralAgreement D.T D.u` from
  hypotheses ALREADY present in `LimitRegularityInputs` (the χ₀ = 0 regime params,
  the H1 datum data, the fixed-point equation, the K2 slice bounds, the K1
  source-coefficient time-`C¹` families incl. the `t/2`-shift, and the H3 slice
  continuity) plus the limit's WEAK source package — itself producible from those
  same families via `DuhamelSourceL1Cont.ofTimeC1 ∘ limitSource_duhamelSourceTimeC1`.
  No hypothesis stronger than the ledger is introduced: this is a strict ledger
  reduction (the `Hu` field becomes derivable).

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalPicardLimitRestartWeak
import ShenWork.Paper2.IntervalPicardLimitSourceData
import ShenWork.Paper2.IntervalDomainLimitSourceRepresentation
import ShenWork.PDE.IntervalMildTimeDerivContinuity

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1 duhamelSpectralCoeff)
open ShenWork.IntervalGradientDuhamelMap (intervalGradientDuhamelMap logisticLifted)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalMildRegularityBootstrap (restartDuhamelCoeff)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalMildPicardRegularity
  (logisticSourceFun cosineCoeffs_abs_le_of_continuous_bounded)
open ShenWork.IntervalMildTimeDerivContinuity (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalPicardLimitRestartWeak
  (DuhamelSourceL1Cont limit_lift_eq_cosineSeries_weak
   cosineCoeffs_halfstep_eq_limitCoeff_weak)
open ShenWork.IntervalPicardLimitSourceData
  (restartDuhamelCoeff_eq_localRestartCoeff limitSource_duhamelSourceTimeC1)
open ShenWork.IntervalDomainLimitSourceRepresentation
  (limitSource_duhamelSourceTimeC1_of_representation)

noncomputable section

namespace ShenWork.IntervalPicardLimitTimeNhd

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-! ## 1. The general restart split.

`duhamelSpectralCoeff a t k = e^{−(t−τ)λₖ}·duhamelSpectralCoeff a τ k
  + duhamelSpectralCoeff (σ ↦ a (τ+σ)) (t−τ) k`,  for `0 < τ ≤ t`.

`∫₀ᵗ = ∫₀^τ + ∫_τ^t`; the first factors `e^{−(t−s)λ} = e^{−(t−τ)λ}e^{−(τ−s)λ}`,
the second σ-shifts by `s = τ+σ` over `[0, t−τ]`.  This is the `τ ≠ t/2`
generalisation of M1's `duhamelSpectralCoeff_halfstep_split`. -/
theorem duhamelSpectralCoeff_general_split
    {a : ℝ → ℕ → ℝ} (ha_cont : ∀ k, Continuous (fun s => a s k))
    (τ t : ℝ) (k : ℕ) :
    duhamelSpectralCoeff a t k
      = Real.exp (-(t - τ) * (λ_ k)) * duhamelSpectralCoeff a τ k
        + duhamelSpectralCoeff (fun σ k => a (τ + σ) k) (t - τ) k := by
  unfold duhamelSpectralCoeff
  -- integrability of the integrand on any interval
  have hint : ∀ b c : ℝ, IntervalIntegrable
      (fun s => Real.exp (-(t - s) * (λ_ k)) * a s k) volume b c := by
    intro b c
    apply Continuous.intervalIntegrable
    have hexp : Continuous (fun s => Real.exp (-(t - s) * (λ_ k))) := by fun_prop
    exact hexp.mul (ha_cont k)
  -- split the integral at τ
  rw [← intervalIntegral.integral_add_adjacent_intervals
        (hint 0 τ) (hint τ t)]
  congr 1
  · -- first piece: factor e^{−(t−τ)λ}
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _hs
    show Real.exp (-(t - s) * (λ_ k)) * a s k
      = Real.exp (-(t - τ) * (λ_ k)) * (Real.exp (-(τ - s) * (λ_ k)) * a s k)
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  · -- second piece: change of variables s = τ + σ on [0, t−τ]
    have hcv := intervalIntegral.integral_comp_add_left
      (a := (0:ℝ)) (b := t - τ)
      (fun s => Real.exp (-(t - s) * (λ_ k)) * a s k) τ
    simp only [add_zero] at hcv
    have hbnd : τ + (t - τ) = t := by ring
    rw [hbnd] at hcv
    rw [← hcv]
    apply intervalIntegral.integral_congr
    intro σ _hσ
    show Real.exp (-(t - (τ + σ)) * (λ_ k)) * a (τ + σ) k
      = Real.exp (-(t - τ - σ) * (λ_ k)) * a (τ + σ) k
    congr 2
    ring

/-! ## 2. The general coefficient identity.

`limitCoeff t = restartDuhamelCoeff (coeffs u(τ)) (source from τ) (t − τ)`. -/

/-- **General restart coefficient identity.**  For the Picard limit `u` with the
weak source package, the heat+Duhamel-from-0 coefficient `limitCoeff t` equals the
restart coefficient at base `τ` and horizon `t − τ`, for any `0 < τ < t`.  The
restart-base coefficient `coeffs u(τ) = limitCoeff τ` is supplied by ★-weak's
`cosineCoeffs_halfstep_eq_limitCoeff_weak` (general in `τ`); the residual integral
is re-expressed via `duhamelSpectralCoeff_general_split`. -/
theorem limitCoeff_eq_restartDuhamelCoeff_general
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    (hfix : ∀ t, 0 < t → ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
      intervalDomainLift (u t) x = intervalGradientDuhamelMap p u₀ u t ⟨x, hx⟩)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceL1Cont
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k))
    {τ t : ℝ} (hτ : 0 < τ) (_hτt : τ < t)
    (hL_cont : ∀ s, 0 < s → s ≤ τ → Continuous (logisticLifted p (u s)))
    (k : ℕ) :
    ShenWork.IntervalPicardLimitRestart.limitCoeff p u₀ u t k
      = restartDuhamelCoeff
          (cosineCoeffs (intervalDomainLift (u τ)))
          (fun σ k => cosineCoeffs (logisticLifted p (u (τ + σ))) k)
          (t - τ) k := by
  have ha_cont : ∀ k, Continuous
      (fun s => cosineCoeffs (logisticLifted p (u s)) k) := hsrc0.hcont
  -- restart-base coefficient: coeffs u(τ) = limitCoeff τ
  have hbase : cosineCoeffs (intervalDomainLift (u τ)) k
      = ShenWork.IntervalPicardLimitRestart.limitCoeff p u₀ u τ k :=
    cosineCoeffs_halfstep_eq_limitCoeff_weak p hχ0 u₀ u hfix hu₀_cont hu₀_bound
      hsrc0 hτ hL_cont k
  unfold restartDuhamelCoeff
  rw [hbase]
  unfold ShenWork.IntervalPicardLimitRestart.limitCoeff
  -- general split of the source Duhamel coefficient at base τ
  have hsplit := duhamelSpectralCoeff_general_split (a :=
      fun s k => cosineCoeffs (logisticLifted p (u s)) k) ha_cont τ t k
  -- factor the homogeneous part: e^{−tλ} = e^{−(t−τ)λ}·e^{−τλ}
  have hexp : Real.exp (-t * (λ_ k))
      = Real.exp (-(t - τ) * (λ_ k)) * Real.exp (-τ * (λ_ k)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp, hsplit]
  ring

/-! ## 3. The general restart representation (EqOn). -/

/-- **`picardLimitRestart_general` — the general restart identity.**  Identical
to ★-weak's conclusion but with restart base `τ` an arbitrary point of `(0,t)`
(★-weak is the special case `τ = t/2`).  For the limit `u`, `u t` agrees on
`[0,1]` with the restart cosine series at base `τ` and horizon `t − τ`. -/
theorem picardLimitRestart_general
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    (hfix : ∀ t, 0 < t → ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
      intervalDomainLift (u t) x = intervalGradientDuhamelMap p u₀ u t ⟨x, hx⟩)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceL1Cont
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k))
    {τ t : ℝ} (hτ : 0 < τ) (hτt : τ < t)
    (hL_cont : ∀ s, 0 < s → s ≤ t → Continuous (logisticLifted p (u s))) :
    Set.EqOn (intervalDomainLift (u t))
      (fun x => ∑' k : ℕ,
        restartDuhamelCoeff
          (cosineCoeffs (intervalDomainLift (u τ)))
          (fun σ k => cosineCoeffs (logisticLifted p (u (τ + σ))) k)
          (t - τ) k * cosineMode k x)
      (Set.Icc (0:ℝ) 1) := by
  have ht : 0 < t := lt_trans hτ hτt
  intro x hx
  rw [limit_lift_eq_cosineSeries_weak p hχ0 u₀ u hfix hu₀_cont hu₀_bound hsrc0 ht
        hL_cont hx]
  refine tsum_congr (fun k => ?_)
  congr 1
  exact limitCoeff_eq_restartDuhamelCoeff_general p hχ0 u₀ u hfix hu₀_cont hu₀_bound
    hsrc0 hτ hτt (fun s hs hsτ => hL_cont s hs (le_of_lt (lt_of_le_of_lt hsτ hτt))) k

/-! ## 4. Discharging `Hu` from the ledger families. -/

/-- **`Hu_of_restart` — `HasTimeNeighborhoodSpectralAgreement` from the general
restart identity.**

For each interior `t₀ ∈ (0,T)` we pick `offset := t₀/2`, restart data
`a₀ := coeffs u(t₀/2)` and source family `a := σ ↦ coeffs (logisticLifted p
(u(t₀/2+σ)))`.  The general restart identity (`picardLimitRestart_general`) with
`τ := t₀/2` holds at every time `s` in the open right half-neighbourhood
`Ioo (t₀/2) T` (which contains `t₀`, giving the eventually-nhds), and the
restart-coefficient bridge rewrites it into the `localRestartCoeff`/`x.1` shape.

The `∃`-fields are all supplied from data ALREADY in `LimitRegularityInputs`:
* `M := 2·Msup`, `|a₀ k| ≤ M` via `cosineCoeffs_abs_le_of_continuous_bounded`;
* `DuhamelSourceTimeC1 a` via the ledger's own `limitSource_duhamelSourceTimeC1`
  applied to the `t₀/2`-shifted K2/K1 families (`hC2t`,…,`hMdotS t₀`);
* `offset := t₀/2`, `0 < t₀ − offset = t₀/2`.

Hence `Hu` becomes derivable: a net ledger reduction. -/
theorem Hu_of_restart
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ} (u : ℝ → intervalDomainPoint → ℝ)
    {T : ℝ}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hfix : ∀ t, 0 < t → ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
      intervalDomainLift (u t) x = intervalGradientDuhamelMap p u₀ u t ⟨x, hx⟩)
    (hsrc0 : DuhamelSourceL1Cont
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k))
    -- K2 spatial slice bounds (per time slice)
    {Msup G1 G2 : ℝ}
    -- per-slice cosine representation (replaces the unsatisfiable global-`C²` field)
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ, Set.EqOn (intervalDomainLift (u σ))
      (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpost : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u σ) x)
    (hubt : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (u σ) x ≤ Msup)
    (hG1t : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (u σ)) x| ≤ G1)
    (hG2t : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (u σ))) x| ≤ G2)
    -- K1 for the t/2-SHIFTED limit source family
    (adotS : ℝ → ℝ → ℕ → ℝ)
    (hderivS : ∀ t, ∀ σ k, HasDerivAt
      (fun r => cosineCoeffs
        (logisticSourceFun p.a p.b p.α (intervalDomainLift (u (t/2 + r)))) k)
      (adotS t σ k) σ)
    (hadotcontS : ∀ t, ∀ k, Continuous (fun σ => adotS t σ k))
    {MdotS : ℝ}
    (hMdotS : ∀ t, ∀ σ, 0 ≤ σ → ∀ k, |adotS t σ k| ≤ MdotS)
    -- H3 slice continuity
    (hLc : ∀ t, 0 < t → t < T →
      ∀ s, 0 < s → s ≤ t → Continuous (logisticLifted p (u s))) :
    HasTimeNeighborhoodSpectralAgreement T u := by
  constructor
  intro t₀ ht₀ ht₀T
  -- restart base / offset
  set τ : ℝ := t₀ / 2 with hτdef
  have hτpos : 0 < τ := by rw [hτdef]; linarith
  -- restart data a₀ = coeffs u(τ); bound via continuous-bounded coefficient lemma
  refine ⟨cosineCoeffs (intervalDomainLift (u τ)), 2 * Msup, ?_, ?_,
    (fun σ k => cosineCoeffs (logisticLifted p (u (τ + σ))) k), ?_, τ, ?_, ?_⟩
  · -- 0 ≤ 2·Msup
    have hMnn : 0 ≤ Msup := by
      have h1 := hubt τ 0 (by constructor <;> norm_num)
      have h2 := hpost τ 0 (by constructor <;> norm_num)
      linarith
    linarith
  · -- |coeffs u(τ) k| ≤ 2·Msup
    have hMnn : 0 ≤ Msup := by
      have h1 := hubt τ 0 (by constructor <;> norm_num)
      have h2 := hpost τ 0 (by constructor <;> norm_num)
      linarith
    intro k
    refine cosineCoeffs_abs_le_of_continuous_bounded
      (((ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_contDiff_two
        (hbsum τ)).continuous.continuousOn).congr (hagree τ)) hMnn ?_ k
    intro x hx
    rw [abs_of_pos (hpost τ x hx)]; exact hubt τ x hx
  · -- DuhamelSourceTimeC1 of the τ-shifted source family, via ledger's own H2(u)
    have hshift : (fun σ k => cosineCoeffs (logisticLifted p (u (τ + σ))) k)
        = fun σ k => cosineCoeffs (logisticLifted p ((fun s => u (t₀/2 + s)) σ)) k := by
      funext σ k; rw [hτdef]
    rw [hshift]
    exact limitSource_duhamelSourceTimeC1_of_representation p (fun s => u (t₀/2 + s)) hα ha hb
      (fun σ => bc (t₀/2 + σ))
      (fun σ => hbsum (t₀/2 + σ))
      (fun σ => hagree (t₀/2 + σ))
      (fun σ => hpost (t₀/2 + σ))
      (fun σ => hubt (t₀/2 + σ))
      (fun σ => hG1t (t₀/2 + σ))
      (fun σ => hG2t (t₀/2 + σ))
      (adotS t₀) (hderivS t₀) (hadotcontS t₀) (hMdotS t₀)
  · -- 0 < t₀ − offset = τ
    rw [hτdef]; linarith
  · -- eventually-nhds agreement on the open right half-neighbourhood Ioo τ T
    have hmem : t₀ ∈ Set.Ioo τ T := by
      refine ⟨?_, ht₀T⟩; rw [hτdef]; linarith
    have hopen : IsOpen (Set.Ioo τ T) := isOpen_Ioo
    filter_upwards [hopen.mem_nhds hmem] with s hs
    -- general restart identity at time s, base τ, horizon s − τ
    have hτs : τ < s := hs.1
    have hsT : s < T := hs.2
    have hspos : 0 < s := lt_trans hτpos hτs
    have heqon := picardLimitRestart_general p hχ0 u₀ u hfix hu₀_cont hu₀_bound
      hsrc0 hτpos hτs
      (fun r hr hrs => hLc s hspos hsT r hr hrs)
    intro x
    have hx1 : x.1 ∈ Set.Icc (0:ℝ) 1 := x.2
    have hlift : u s x = intervalDomainLift (u s) x.1 := by
      simp only [intervalDomainLift, hx1, dif_pos, Subtype.eta]
    rw [hlift, heqon hx1]
    refine tsum_congr (fun k => ?_)
    rw [restartDuhamelCoeff_eq_localRestartCoeff]

end ShenWork.IntervalPicardLimitTimeNhd
