/-
  ShenWork/Paper2/IntervalRestartSliceLipschitz.lean

  **The fixed-base restart sup-norm Lipschitz bound for the canonical mild slice,
  and the `hinterior` interior-regime continuity it produces.**

  Wiring layer: take the spectral restart EqOn representation
  (`picardLimitRestart_general_of_subtypeCont`, NON-circular, fed by the iterate-side
  `DuhamelSourceBddOn` package `hsrc0`) at the FIXED base `τ = s₀/2`, subtract the
  two cosine series at horizons `s` and `s₀`, and apply the analytic engine
  `IntervalRestartSeriesLipschitz.restartSeries_sup_diff_le` to conclude

      sup_y |D.u s y − D.u s₀ y| ≤ |s − s₀| · C(τ).

  The damping floor `m := τ/2` is below both horizons (`s − τ ≥ τ/2`,
  `s₀ − τ = τ ≥ τ/2`) in the interior regime, giving the heat-damped homogeneous sum
  its convergence.

  The single grown hypothesis is `hsrc0 : DuhamelSourceBddOn (patchedSource …) D.T`
  — produced ENTIRELY iterate-side via `duhamelSourceBddOn_of_iterates` with no
  appeal to the patched-slice continuity it is helping to prove.

  No `sorry`, no `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalRestartSeriesLipschitz
import ShenWork.Paper2.IntervalPicardLimitTimeNhdSubtype
import ShenWork.Paper2.IntervalDomainConstExtendAdapter

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalDomainConstExtend)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalGradientDuhamelMap
  (logisticLifted intervalGradientDuhamelMap)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalMildPicard (GradientMildSolutionData picardLimit)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildRegularityBootstrap (restartDuhamelCoeff)
open ShenWork.IntervalPicardLimitBddProducer (patchedSource patchedSource_eq_of_pos)
open ShenWork.IntervalPicardLimitRestartBdd (DuhamelSourceBddOn)
open ShenWork.IntervalRestartSeriesLipschitz

noncomputable section

namespace ShenWork.IntervalRestartSliceLipschitz

variable {p : CM2Params}

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-- **Initial-datum cosine-coefficient bound** from continuity (compactness of the
unit interval domain).  `M₀ := 2·sup|u₀|`. -/
theorem u₀_cosineCoeff_bound {u₀ : intervalDomainPoint → ℝ} (hu₀cont : Continuous u₀) :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀ := by
  haveI : CompactSpace intervalDomainPoint :=
    isCompact_iff_compactSpace.mp (isCompact_Icc (a := (0:ℝ)) (b := 1))
  have hbdd : BddAbove (Set.range fun x => |u₀ x|) :=
    (isCompact_range (hu₀cont.abs)).bddAbove
  set B : ℝ := sSup (Set.range fun x => |u₀ x|) with hBdef
  have hB0 : 0 ≤ B :=
    le_trans (abs_nonneg _)
      (le_csSup hbdd ⟨⟨1 / 2, ⟨by norm_num, by norm_num⟩⟩, rfl⟩)
  refine ⟨2 * B, by positivity, fun k => ?_⟩
  have hcont : ContinuousOn (intervalDomainLift u₀) (Set.Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : (Set.Icc (0 : ℝ) 1).restrict (intervalDomainLift u₀) = u₀ := by
      funext ⟨y, hy⟩
      simp only [Set.restrict_apply, intervalDomainLift]
      split_ifs
      exact congr_arg u₀ (Subtype.ext rfl)
    rw [heq]; exact hu₀cont
  have hbound : ∀ x ∈ Set.Icc (0:ℝ) 1, |intervalDomainLift u₀ x| ≤ B := by
    intro x hx
    simp only [intervalDomainLift, dif_pos hx]
    exact le_csSup hbdd ⟨⟨x, hx⟩, rfl⟩
  exact ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
    hcont hB0 hbound k

/-- **Slice cosine-coefficient bound** at a positive time `σ`.  `|cosineCoeffs (lift
(D.u σ)) k| ≤ 2·D.M` from `D.hcont`/`D.hbound`. -/
theorem slice_cosineCoeff_bound {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    {σ : ℝ} (hσ : 0 < σ) (hσT : σ ≤ D.T) (k : ℕ) :
    |cosineCoeffs (intervalDomainLift (D.u σ)) k| ≤ 2 * D.M := by
  have hcont : ContinuousOn (intervalDomainLift (D.u σ)) (Set.Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : (Set.Icc (0 : ℝ) 1).restrict (intervalDomainLift (D.u σ)) = D.u σ := by
      funext ⟨y, hy⟩
      simp only [Set.restrict_apply, intervalDomainLift]
      split_ifs
      exact congr_arg (D.u σ) (Subtype.ext rfl)
    rw [heq]; exact D.hcont σ hσ hσT
  have hbound : ∀ x ∈ Set.Icc (0:ℝ) 1, |intervalDomainLift (D.u σ) x| ≤ D.M := by
    intro x hx
    simp only [intervalDomainLift, dif_pos hx]
    exact D.hbound σ hσ hσT ⟨x, hx⟩
  exact ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
    hcont D.hM.le hbound k

/-- **Restart-source envelope/continuity facts** at base `τ` extracted from
`hsrc0`.  The restart source `σ ↦ cosineCoeffs (logisticLifted (D.u (τ+σ))) k` equals
`patchedSource (τ+σ) k` for `τ+σ > 0`, so its envelope and time-continuity come
verbatim from the `DuhamelSourceBddOn` package. -/
theorem restartSource_facts {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (hsrc0 : DuhamelSourceBddOn (patchedSource p u₀ D.u) D.T)
    {τ x : ℝ} (hτpos : 0 < τ) (hx0 : 0 ≤ x) (hxT : τ + x ≤ D.T) :
    (∀ n, ContinuousOn
        (fun σ => cosineCoeffs (logisticLifted p (D.u (τ + σ))) n) (Set.uIcc (0:ℝ) x))
      ∧ (∀ n, ∀ σ ∈ Set.uIcc (0:ℝ) x,
        |cosineCoeffs (logisticLifted p (D.u (τ + σ))) n| ≤ hsrc0.env (τ / 2) n) := by
  have hτhalf : 0 < τ / 2 := by linarith
  have hτhalfT : τ / 2 ≤ D.T := by
    have : τ ≤ D.T := le_trans (by linarith) hxT
    linarith
  constructor
  · -- continuity-on, via `hsrc0.hcont` composed with `σ ↦ τ + σ` and `patchedSource_eq_of_pos`.
    intro n
    have hmap : ContinuousOn (fun σ : ℝ => τ + σ) (Set.uIcc (0:ℝ) x) := by fun_prop
    have hmaps : Set.MapsTo (fun σ : ℝ => τ + σ) (Set.uIcc (0:ℝ) x) (Set.Icc 0 D.T) := by
      intro σ hσ
      rw [Set.uIcc_of_le hx0] at hσ
      exact ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    have hcomp : ContinuousOn (fun σ => patchedSource p u₀ D.u (τ + σ) n) (Set.uIcc (0:ℝ) x) :=
      (hsrc0.hcont n).comp hmap hmaps
    refine hcomp.congr ?_
    intro σ hσ
    rw [Set.uIcc_of_le hx0] at hσ
    have hpos : 0 < τ + σ := by linarith [hσ.1]
    show cosineCoeffs (logisticLifted p (D.u (τ + σ))) n = patchedSource p u₀ D.u (τ + σ) n
    exact (patchedSource_eq_of_pos p u₀ D.u hpos n).symm
  · -- envelope bound on `[τ/2, T] ⊇ [τ, τ+x]`.
    intro n σ hσ
    rw [Set.uIcc_of_le hx0] at hσ
    have hpos : 0 < τ + σ := by linarith [hσ.1]
    rw [show cosineCoeffs (logisticLifted p (D.u (τ + σ))) n
        = patchedSource p u₀ D.u (τ + σ) n from (patchedSource_eq_of_pos p u₀ D.u hpos n).symm]
    exact hsrc0.henv_bound (τ / 2) hτhalf (τ + σ) (by linarith [hσ.1]) (by linarith [hσ.2]) n

/-- **The fixed-base restart sup-norm Lipschitz bound.**  In the interior regime
`τ < s, s₀ ≤ T` with `τ = s₀/2`, the canonical mild slice difference is `|s − s₀|`-
Lipschitz uniformly in the spatial point. -/
theorem restartSlice_sup_lipschitz
    (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ} (hu₀cont : Continuous u₀)
    (D : GradientMildSolutionData p u₀)
    (hsrc0 : DuhamelSourceBddOn (patchedSource p u₀ D.u) D.T)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {s₀ : ℝ} (hs₀ : 0 < s₀) (hs₀T : s₀ ≤ D.T) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ s, 3 * s₀ / 4 ≤ s → s ≤ D.T →
        ∀ y : intervalDomainPoint, |D.u s y - D.u s₀ y| ≤ |s - s₀| * C := by
  set τ : ℝ := s₀ / 2 with hτdef
  have hτpos : 0 < τ := by rw [hτdef]; linarith
  have hτs₀ : τ < s₀ := by rw [hτdef]; linarith
  have hτT : τ ≤ D.T := le_trans hτs₀.le hs₀T
  have hm : 0 < τ / 2 := by linarith
  set B₀ : ℝ := 2 * D.M with hB₀def
  have hB₀nn : 0 ≤ B₀ := by rw [hB₀def]; have := D.hM.le; positivity
  -- the analytic-engine constant.
  set Cval : ℝ :=
    (∑' n : ℕ, ((λ_ n) * Real.exp (-(τ / 2 * (λ_ n))) * B₀ + 2 * hsrc0.env (τ / 2) n))
    with hCdef
  have hCval_nonneg : 0 ≤ Cval := by
    rw [hCdef]
    apply tsum_nonneg
    intro n
    have hlam : 0 ≤ (λ_ n) := by unfold unitIntervalCosineEigenvalue; positivity
    have henvnn : 0 ≤ hsrc0.env (τ / 2) n :=
      le_trans (abs_nonneg _) (hsrc0.henv_bound (τ / 2) hm τ (by linarith) hτT n)
    have := hB₀nn
    positivity
  refine ⟨Cval, hCval_nonneg, ?_⟩
  intro s hs34 hsT y
  -- interior regime: `s ≥ 3s₀/4 = 3τ/2`, so `s − τ ≥ τ/2` and `s > τ`.
  have hsτ : τ < s := by have h := hτdef; linarith
  have hfloor_s : τ / 2 ≤ s - τ := by have h := hτdef; linarith
  -- `hfix`, `hLc_ce`.
  have hfix : ∀ r, 0 < r → r ≤ D.T → ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
      intervalDomainLift (D.u r) x = intervalGradientDuhamelMap p u₀ D.u r ⟨x, hx⟩ :=
    fun r hr hrT x hx => by
      simp only [intervalDomainLift, dif_pos hx]
      exact D.hmild r hr hrT ⟨x, hx⟩
  have hLc_ce : ∀ r, 0 < r → r ≤ D.T →
      Continuous (intervalDomainConstExtend (intervalLogisticSource p (D.u r))) :=
    fun r hr hrT =>
      ShenWork.Paper2.ConstExtendAdapter.logisticSource_constExtend_continuous D hr hrT
  -- restart EqOn at horizon `s` and at `s₀`, SAME base `τ`.
  have hEqOnS :=
    ShenWork.Paper2.TimeNhdSubtype.picardLimitRestart_general_of_subtypeCont
      p hχ0 u₀ D.u (fun r hr hrs => hfix r hr (le_trans hrs hsT))
      hu₀cont hu₀_bound hsrc0 hτpos hsτ hsT
      (fun r hr hrs => hLc_ce r hr (le_trans hrs hsT))
  have hEqOnS₀ :=
    ShenWork.Paper2.TimeNhdSubtype.picardLimitRestart_general_of_subtypeCont
      p hχ0 u₀ D.u (fun r hr hrs => hfix r hr (le_trans hrs hs₀T))
      hu₀cont hu₀_bound hsrc0 hτpos hτs₀ hs₀T
      (fun r hr hrs => hLc_ce r hr (le_trans hrs hs₀T))
  have hyIcc : y.1 ∈ Set.Icc (0:ℝ) 1 := y.2
  have hSval := hEqOnS hyIcc
  have hS₀val := hEqOnS₀ hyIcc
  have hlift_s : intervalDomainLift (D.u s) y.1 = D.u s y := by
    simp only [intervalDomainLift, dif_pos hyIcc, Subtype.coe_eta]
  have hlift_s₀ : intervalDomainLift (D.u s₀) y.1 = D.u s₀ y := by
    simp only [intervalDomainLift, dif_pos hyIcc, Subtype.coe_eta]
  -- abbreviations for the engine inputs.
  set a₀ : ℕ → ℝ := cosineCoeffs (intervalDomainLift (D.u τ)) with ha₀def
  set asrc : ℝ → ℕ → ℝ := fun σ k => cosineCoeffs (logisticLifted p (D.u (τ + σ))) k
    with hasrcdef
  -- engine input facts.
  have hB₀ : ∀ n, |a₀ n| ≤ B₀ := fun n => by
    rw [ha₀def]; exact slice_cosineCoeff_bound D hτpos hτT n
  have henv : Summable (hsrc0.env (τ / 2)) := hsrc0.henv_summable (τ / 2) hm (by linarith)
  -- range facts: `s − τ ≥ 0` and `τ + (s−τ) = s ≤ T`; `s₀ − τ ≥ 0` and `τ + (s₀−τ) = s₀ ≤ T`.
  have hsτ0 : 0 ≤ s - τ := by linarith
  have hs₀τ0 : 0 ≤ s₀ - τ := by linarith
  have hsumS : Set.uIcc (0:ℝ) (s - τ) ⊆ Set.uIcc (0:ℝ) (s - τ) := le_refl _
  -- source facts on horizon (s − τ).
  obtain ⟨hcontS, hbndS⟩ := restartSource_facts D hsrc0 hτpos hsτ0 (by linarith)
  -- source facts on horizon (s₀ − τ).
  obtain ⟨hcontS₀, hbndS₀⟩ := restartSource_facts D hsrc0 hτpos hs₀τ0 (by linarith)
  -- per-horizon summability for the `tsum_sub`.
  have hsumblS : Summable (fun n => restartDuhamelCoeff a₀ asrc (s - τ) n * cosineMode n y.1) :=
    restartCosineSeries_summable (by linarith) hB₀ henv hbndS y.1
  have hsumblS₀ : Summable (fun n => restartDuhamelCoeff a₀ asrc (s₀ - τ) n * cosineMode n y.1) :=
    restartCosineSeries_summable (by linarith) hB₀ henv hbndS₀ y.1
  -- the difference equals the series of restart-coefficient differences.
  have hdiff_eq :
      D.u s y - D.u s₀ y
        = ∑' n : ℕ, (restartDuhamelCoeff a₀ asrc (s - τ) n
              - restartDuhamelCoeff a₀ asrc (s₀ - τ) n) * cosineMode n y.1 := by
    rw [← hlift_s, ← hlift_s₀, hSval, hS₀val, ← (hsumblS.tsum_sub hsumblS₀)]
    refine tsum_congr (fun n => ?_); ring
  -- apply the engine: damping floor `m = τ/2`, horizons `x = s − τ`, `y_ = s₀ − τ`.
  -- WLOG s ≥ s₀ or s ≤ s₀; the engine handles `min(x,y_) ≥ m` from `m ≤ y_ ≤ x`
  -- (resp. symmetric).  We use it on the larger/smaller pair.
  rw [hdiff_eq]
  -- damping floor `m = τ/2` is below BOTH horizons in the interior regime:
  --   `s₀ − τ = τ ≥ τ/2` and `s − τ ≥ τ/2` (from `s ≥ 3s₀/4`, `hfloor_s`).
  have hCeq : Cval = ∑' n : ℕ, ((λ_ n) * Real.exp (-(τ / 2 * (λ_ n))) * B₀
      + 2 * hsrc0.env (τ / 2) n) := hCdef
  rcases le_total (s₀ - τ) (s - τ) with hle | hge
  · -- s₀ ≤ s : larger horizon `x = s − τ`, smaller `y_ = s₀ − τ`; floor `m = τ/2 ≤ s₀ − τ`.
    have hmfloor : τ / 2 ≤ s₀ - τ := by rw [hτdef]; linarith
    have hkey := restartSeries_sup_diff_le (a₀ := a₀) (a := asrc)
      (x := s - τ) (y := s₀ - τ) (m := τ / 2) (B₀ := B₀) (env := hsrc0.env (τ / 2))
      hmfloor hle hm hB₀ henv hcontS hbndS y.1
    have habs : |(s - τ) - (s₀ - τ)| = |s - s₀| := by congr 1; ring
    rw [habs] at hkey
    calc |∑' n, (restartDuhamelCoeff a₀ asrc (s - τ) n
            - restartDuhamelCoeff a₀ asrc (s₀ - τ) n) * cosineMode n y.1|
        ≤ |s - s₀| * (∑' n, ((λ_ n) * Real.exp (-(τ / 2 * (λ_ n))) * B₀
            + 2 * hsrc0.env (τ / 2) n)) := hkey
      _ = |s - s₀| * Cval := by rw [hCeq]
  · -- s ≤ s₀ : larger horizon `x = s₀ − τ`, smaller `y_ = s − τ`; floor `m = τ/2 ≤ s − τ`.
    have hkey := restartSeries_sup_diff_le (a₀ := a₀) (a := asrc)
      (x := s₀ - τ) (y := s - τ) (m := τ / 2) (B₀ := B₀) (env := hsrc0.env (τ / 2))
      hfloor_s hge hm hB₀ henv hcontS₀ hbndS₀ y.1
    have habs : |(s₀ - τ) - (s - τ)| = |s - s₀| := by rw [abs_sub_comm]; congr 1; ring
    rw [habs] at hkey
    have hflip : ∑' n : ℕ, (restartDuhamelCoeff a₀ asrc (s - τ) n
            - restartDuhamelCoeff a₀ asrc (s₀ - τ) n) * cosineMode n y.1
        = -(∑' n : ℕ, (restartDuhamelCoeff a₀ asrc (s₀ - τ) n
            - restartDuhamelCoeff a₀ asrc (s - τ) n) * cosineMode n y.1) := by
      rw [← tsum_neg]; refine tsum_congr (fun n => ?_); ring
    rw [hflip, abs_neg]
    calc |∑' n, (restartDuhamelCoeff a₀ asrc (s₀ - τ) n
            - restartDuhamelCoeff a₀ asrc (s - τ) n) * cosineMode n y.1|
        ≤ |s - s₀| * (∑' n, ((λ_ n) * Real.exp (-(τ / 2 * (λ_ n))) * B₀
            + 2 * hsrc0.env (τ / 2) n)) := hkey
      _ = |s - s₀| * Cval := by rw [hCeq]

/-- **`hinterior` — the interior-regime slice continuity** produced from the restart
sup-norm Lipschitz bound.  Pick `δ₀ = min (s₀/4) (ε/(C+1))`; the `δ₀ ≤ s₀/4`
constraint forces the admissible `s` into the regime `s ≥ 3s₀/4` where the Lipschitz
bound holds, and `δ₀ ≤ ε/(C+1)` closes the `ε`. -/
theorem hinterior_of_src0
    (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ} (hu₀cont : Continuous u₀)
    (D : GradientMildSolutionData p u₀)
    (hsrc0 : DuhamelSourceBddOn (patchedSource p u₀ D.u) D.T)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {s₀ : ℝ} (hs₀ : 0 < s₀) (hs₀T : s₀ ≤ D.T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ > 0, ∀ s, s₀ / 2 < s → s ≤ D.T → |s - s₀| < δ₀ →
      ∀ y : intervalDomainPoint, |D.u s y - D.u s₀ y| < ε := by
  obtain ⟨C, hCnn, hLip⟩ :=
    restartSlice_sup_lipschitz hχ0 hu₀cont D hsrc0 hu₀_bound hs₀ hs₀T
  refine ⟨min (s₀ / 4) (ε / (C + 1)), lt_min (by linarith) (by positivity), ?_⟩
  intro s _ hsT hsδ y
  -- `|s − s₀| < s₀/4` forces `s ≥ 3s₀/4`.
  have hsδ4 : |s - s₀| < s₀ / 4 := lt_of_lt_of_le hsδ (min_le_left _ _)
  have hsδC : |s - s₀| < ε / (C + 1) := lt_of_lt_of_le hsδ (min_le_right _ _)
  have hs34 : 3 * s₀ / 4 ≤ s := by
    have h1 : s₀ - s ≤ |s - s₀| := by rw [abs_sub_comm]; exact le_abs_self _
    have : s₀ - s < s₀ / 4 := lt_of_le_of_lt h1 hsδ4
    linarith
  -- apply the Lipschitz bound and close ε.
  have hbound := hLip s hs34 hsT y
  have hCp1 : 0 < C + 1 := by linarith
  calc |D.u s y - D.u s₀ y| ≤ |s - s₀| * C := hbound
    _ ≤ |s - s₀| * (C + 1) := by
        apply mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    _ < ε / (C + 1) * (C + 1) := by
        apply mul_lt_mul_of_pos_right hsδC hCp1
    _ = ε := by field_simp

end ShenWork.IntervalRestartSliceLipschitz
