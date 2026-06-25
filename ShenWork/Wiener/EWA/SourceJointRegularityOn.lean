/-
  ShenWork/Wiener/EWA/SourceJointRegularityOn.lean

  **Windowed χ₀<0 JOINT (t,x)-regularity on `Ioo 0 T`.**

  Windowed analogues of the five joint-continuity theorems from
  `SourceJointRegularity.lean`, taking `DuhamelSourceTimeC1On a 0 T` in place
  of the global `DuhamelSourceTimeC1 a`.

  The heat leg depends only on the initial data bound (no `DuhamelSourceTimeC1`),
  so we reproduce the heat-leg helpers here (they are `private` in the original).

  The Duhamel legs are adapted: per-term continuity comes from the windowed
  `duhamelSpectralCoeff_continuous_of_on` and
  `duhamelSpectralCoeff_hasDerivAt_of_on` (IntervalDuhamelSpectralDerivOn.lean),
  and the coefficient bounds use `src.henv_bound s hs n` with `hs : s ∈ Icc 0 T`.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceTimeRegularitySlice
import ShenWork.Wiener.EWA.SourceTimeRegularityMajorant
import ShenWork.PDE.IntervalDuhamelSpectralDerivOn

noncomputable section

namespace ShenWork.EWA

open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.IntervalDuhamelSpectralDerivOn
  (duhamelSpectralCoeff_continuous_of_on duhamelSpectralCoeff_hasDerivAt_of_on)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs)
open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.IntervalDomainRegularityBootstrap
  (reciprocalSquareTerm reciprocalSquareTerm_summable)
open ShenWork.CosineSpectrum (cosineMode)
open Set Filter Topology

/-! ## Cosine-mode helpers -/

/-- `|cosineMode n x| ≤ 1`. -/
private theorem cosineMode_abs_le_one' (n : ℕ) (x : ℝ) : |cosineMode n x| ≤ 1 := by
  simp only [cosineMode]; exact Real.abs_cos_le_one _

/-- `cosineMode n` is continuous. -/
private theorem cosineMode_continuous' (n : ℕ) : Continuous (fun x : ℝ => cosineMode n x) :=
  Real.continuous_cos.comp (continuous_const.mul continuous_id)

/-! ## Heat-leg joint continuity (reproduced from SourceJointRegularity, which has them private). -/

/-- **HEAT VALUE leg — joint continuity** on `Ioi 0 ×ˢ univ`. -/
private theorem heatValueSeries_jointContinuousOn' (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0) :
    ContinuousOn
      (fun q : ℝ × ℝ =>
        ∑' n, Real.exp (-q.1 * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n q.2)
      (Ioi (0 : ℝ) ×ˢ univ) := by
  have hMu0 : 0 ≤ Mu0 := le_trans (abs_nonneg _) (hu0bd 0)
  apply continuousOn_of_forall_continuousAt
  intro p hp
  obtain ⟨hp1, _⟩ := mem_prod.1 hp
  have hp1 : 0 < p.1 := mem_Ioi.1 hp1
  set c := p.1 / 2 with hc_def
  have hc : 0 < c := by positivity
  have hcont : ContinuousOn
      (fun q : ℝ × ℝ =>
        ∑' n, Real.exp (-q.1 * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n q.2)
      (Ioo c (p.1 + 1) ×ˢ univ) := by
    apply continuousOn_tsum
    · intro n
      have hheat : Continuous (fun t : ℝ =>
          Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n) :=
        (Real.continuous_exp.comp (continuous_id.neg.mul continuous_const)).mul continuous_const
      exact ((hheat.comp continuous_fst).mul
        ((cosineMode_continuous' n).comp continuous_snd)).continuousOn
    · exact (ShenWork.HeatKernelGradientEstimates.unitIntervalCosineHeatTrace_single_exp_summable
        hc).mul_left Mu0
    · intro n q hq
      obtain ⟨ht, _⟩ := mem_prod.1 hq
      obtain ⟨hct, _⟩ := mem_Ioo.1 ht
      have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
        unfold unitIntervalCosineEigenvalue; positivity
      rw [Real.norm_eq_abs,
        show Real.exp (-q.1 * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n q.2
          = Real.exp (-q.1 * unitIntervalCosineEigenvalue n) * (u₀cos n * cosineMode n q.2)
          from by ring, abs_mul, abs_of_nonneg (Real.exp_nonneg _), mul_comm Mu0]
      refine mul_le_mul ?_ ?_ (abs_nonneg _) (Real.exp_nonneg _)
      · exact Real.exp_le_exp_of_le (by nlinarith)
      · rw [abs_mul]
        calc |u₀cos n| * |cosineMode n q.2|
            ≤ Mu0 * 1 := mul_le_mul (hu0bd n) (cosineMode_abs_le_one' n q.2) (abs_nonneg _) hMu0
          _ = Mu0 := mul_one _
  exact hcont.continuousAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      (mem_prod.2 ⟨mem_Ioo.2 ⟨by simp [hc_def]; linarith, by linarith⟩, mem_univ _⟩))

/-- **HEAT DERIVATIVE leg — joint continuity** on `Ioi 0 ×ˢ univ`. -/
private theorem heatDerivSeries_jointContinuousOn' (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0) :
    ContinuousOn
      (fun q : ℝ × ℝ =>
        ∑' n, -(unitIntervalCosineEigenvalue n) *
          Real.exp (-q.1 * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n q.2)
      (Ioi (0 : ℝ) ×ˢ univ) := by
  have hMu0 : 0 ≤ Mu0 := le_trans (abs_nonneg _) (hu0bd 0)
  apply continuousOn_of_forall_continuousAt
  intro p hp
  obtain ⟨hp1, _⟩ := mem_prod.1 hp
  have hp1 : 0 < p.1 := mem_Ioi.1 hp1
  set c := p.1 / 2 with hc_def
  have hc : 0 < c := by positivity
  have hcont : ContinuousOn
      (fun q : ℝ × ℝ =>
        ∑' n, -(unitIntervalCosineEigenvalue n) *
          Real.exp (-q.1 * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n q.2)
      (Ioo c (p.1 + 1) ×ˢ univ) := by
    apply continuousOn_tsum
    · intro n
      have hheat : Continuous (fun t : ℝ => -(unitIntervalCosineEigenvalue n) *
          Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n) :=
        (continuous_const.mul
          (Real.continuous_exp.comp (continuous_id.neg.mul continuous_const))).mul continuous_const
      exact ((hheat.comp continuous_fst).mul
        ((cosineMode_continuous' n).comp continuous_snd)).continuousOn
    · exact (ShenWork.IntervalMildRegularityBootstrap.unitIntervalCosineEigenvalue_mul_exp_summable
        hc).mul_left Mu0
    · intro n q hq
      obtain ⟨ht, _⟩ := mem_prod.1 hq
      obtain ⟨hct, _⟩ := mem_Ioo.1 ht
      have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
        unfold unitIntervalCosineEigenvalue; positivity
      rw [Real.norm_eq_abs,
        show -(unitIntervalCosineEigenvalue n) *
            Real.exp (-q.1 * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n q.2
          = -(unitIntervalCosineEigenvalue n *
              Real.exp (-q.1 * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n q.2)
          from by ring, abs_neg, abs_mul, abs_mul, abs_mul, abs_of_nonneg hlam,
        abs_of_nonneg (Real.exp_nonneg _)]
      have hexp : Real.exp (-q.1 * unitIntervalCosineEigenvalue n) ≤
          Real.exp (-c * unitIntervalCosineEigenvalue n) :=
        Real.exp_le_exp_of_le (by nlinarith)
      calc unitIntervalCosineEigenvalue n *
            Real.exp (-q.1 * unitIntervalCosineEigenvalue n) * |u₀cos n| * |cosineMode n q.2|
          ≤ unitIntervalCosineEigenvalue n *
              Real.exp (-c * unitIntervalCosineEigenvalue n) * Mu0 * 1 := by
            apply mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hexp hlam) (hu0bd n)
              (abs_nonneg _) (by positivity)) (cosineMode_abs_le_one' n q.2)
              (abs_nonneg _) (by positivity)
        _ = Mu0 * (unitIntervalCosineEigenvalue n *
              Real.exp (-c * unitIntervalCosineEigenvalue n)) := by ring
  exact hcont.continuousAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      (mem_prod.2 ⟨mem_Ioo.2 ⟨by simp [hc_def]; linarith, by linarith⟩, mem_univ _⟩))

/-! ## Heat-leg summabilities (reproduced, private in original). -/

/-- Heat-leg value summability at `t > 0`. -/
private theorem heatVal_summable' (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Summable (fun n =>
      Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n x) := by
  have hMu0 : 0 ≤ Mu0 := le_trans (abs_nonneg _) (hu0bd 0)
  refine Summable.of_norm_bounded
    (g := fun n => Real.exp (-t * unitIntervalCosineEigenvalue n) * Mu0)
    ((ShenWork.HeatKernelGradientEstimates.unitIntervalCosineHeatTrace_single_exp_summable
      ht).mul_right Mu0) (fun n => ?_)
  rw [Real.norm_eq_abs,
    show Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n x
      = Real.exp (-t * unitIntervalCosineEigenvalue n) * (u₀cos n * cosineMode n x) from by ring,
    abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
  rw [abs_mul]
  calc |u₀cos n| * |cosineMode n x|
      ≤ Mu0 * 1 := mul_le_mul (hu0bd n) (cosineMode_abs_le_one' n x) (abs_nonneg _) hMu0
    _ = Mu0 := mul_one _

/-- Heat-leg derivative summability at `t > 0`. -/
private theorem heatDerivVal_summable' (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Summable (fun n => -(unitIntervalCosineEigenvalue n) *
      Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n x) := by
  have hMu0 : 0 ≤ Mu0 := le_trans (abs_nonneg _) (hu0bd 0)
  refine Summable.of_norm
    (((ShenWork.IntervalMildRegularityBootstrap.unitIntervalCosineEigenvalue_mul_exp_summable
      ht).mul_left Mu0).of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_))
  have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue; positivity
  rw [Real.norm_eq_abs, show -(unitIntervalCosineEigenvalue n) *
      Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n x =
      -(unitIntervalCosineEigenvalue n * Real.exp (-t * unitIntervalCosineEigenvalue n)
        * u₀cos n * cosineMode n x) from by ring, abs_neg, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg hlam, abs_of_nonneg (Real.exp_nonneg _)]
  calc unitIntervalCosineEigenvalue n * Real.exp (-t * unitIntervalCosineEigenvalue n)
        * |u₀cos n| * |cosineMode n x|
      ≤ unitIntervalCosineEigenvalue n * Real.exp (-t * unitIntervalCosineEigenvalue n)
          * Mu0 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hu0bd n) (by positivity))
          (cosineMode_abs_le_one' n x) (abs_nonneg _) (by positivity)
    _ = Mu0 * (unitIntervalCosineEigenvalue n
          * Real.exp (-t * unitIntervalCosineEigenvalue n)) := by ring

/-! ## Windowed Duhamel-leg bounds -/

/-- Windowed `|duhamelSpectralCoeff a t n| ≤ t * envelope n` for `0 < t ≤ T`. -/
private theorem abs_duhamelSpectralCoeff_le_on {a : ℝ → ℕ → ℝ} {T : ℝ}
    (src : DuhamelSourceTimeC1On a 0 T)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (n : ℕ) :
    |duhamelSpectralCoeff a t n| ≤ t * src.envelope n := by
  simp only [duhamelSpectralCoeff]
  have henv_nn : 0 ≤ src.envelope n :=
    le_trans (abs_nonneg _) (src.henv_bound 0 ⟨le_refl _, by linarith⟩ n)
  have h_norm := intervalIntegral.norm_integral_le_integral_norm
    (μ := MeasureTheory.MeasureSpace.volume) ht.le
    (f := fun s => Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * a s n)
  rw [Real.norm_eq_abs] at h_norm
  calc |∫ s in (0:ℝ)..t,
        Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * a s n|
      ≤ ∫ s in (0:ℝ)..t,
          ‖Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * a s n‖ := h_norm
    _ ≤ ∫ s in (0:ℝ)..t, src.envelope n := by
        apply intervalIntegral.integral_mono_on ht.le
        · have hcontOn : ContinuousOn (fun s => a s n) (Icc 0 T) :=
            fun s hs => (src.hderiv s hs n).continuousWithinAt
          exact ((((Real.continuous_exp.comp (by fun_prop : Continuous (fun s =>
              -(t - s) * unitIntervalCosineEigenvalue n))).continuousOn).mul
            (hcontOn.mono (Icc_subset_Icc le_rfl htT))).norm).intervalIntegrable_of_Icc ht.le
        · exact intervalIntegrable_const
        · intro s hs
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
          calc Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * |a s n|
              ≤ 1 * src.envelope n := by
                gcongr
                · exact Real.exp_le_one_iff.2 (by
                    have hlam_nn : (0 : ℝ) ≤ unitIntervalCosineEigenvalue n := by
                      unfold unitIntervalCosineEigenvalue; positivity
                    nlinarith [hs.2])
                · exact src.henv_bound s ⟨hs.1, le_trans hs.2 htT⟩ n
            _ = src.envelope n := one_mul _
    _ = t * src.envelope n := by
        rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]

/-- Windowed `|a(t,n) − λₙ·bₙ(t)| ≤ envelope(n) + derivBound·reciprocalSquareTerm(n)`. -/
private theorem duhamel_deriv_bound_on {a : ℝ → ℕ → ℝ} {T : ℝ}
    (src : DuhamelSourceTimeC1On a 0 T)
    {t : ℝ} (ht0 : 0 < t) (htT : t ≤ T) (n : ℕ) :
    |a t n - unitIntervalCosineEigenvalue n *
      duhamelSpectralCoeff a t n| ≤
      src.envelope n + src.derivBound * reciprocalSquareTerm n := by
  have hdb_nn : 0 ≤ src.derivBound :=
    le_trans (abs_nonneg _) (src.hderivBound 0 ⟨le_refl _, by linarith⟩ 0)
  have hlam_nn : (0 : ℝ) ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue; positivity
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    have h1 : unitIntervalCosineEigenvalue 0 = 0 := by
      simp [unitIntervalCosineEigenvalue]
    have h2 : reciprocalSquareTerm 0 = 0 := by
      simp [reciprocalSquareTerm]
    simp only [h1, zero_mul, sub_zero, h2, mul_zero, add_zero]
    exact src.henv_bound t ⟨ht0.le, htT⟩ 0
  · have hlam_pos : 0 < unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      have : (0 : ℝ) < n := Nat.cast_pos.2 hn
      positivity
    have hkey := ShenWork.IntervalDuhamelSourceTimeC1On.duhamelCoeff_eigenvalue_mul_on
      (lo := 0) (hi := T) (t := t) (lam := unitIntervalCosineEigenvalue n)
      (a := fun s => a s n) (adot := fun s => src.adot s n)
      (by linarith) ht0.le htT
      (fun s hs => src.hderiv s ⟨hs.1, le_trans hs.2 htT⟩ n) (src.hadotcont n)
    simp only [sub_zero] at hkey
    have hres : a t n - unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a t n
        = Real.exp (-t * unitIntervalCosineEigenvalue n) * a 0 n
          + ∫ s in (0:ℝ)..t,
            Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n := by
      simp only [duhamelSpectralCoeff] at *; linarith
    rw [hres]
    have h_exp_piece : |Real.exp (-t * unitIntervalCosineEigenvalue n) * a 0 n| ≤
        src.envelope n := by
      rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      calc Real.exp (-t * unitIntervalCosineEigenvalue n) * |a 0 n|
          ≤ 1 * |a 0 n| := by
            gcongr; exact Real.exp_le_one_iff.2 (by nlinarith)
        _ = |a 0 n| := one_mul _
        _ ≤ src.envelope n := src.henv_bound 0 ⟨le_refl _, by linarith⟩ n
    have h_int_piece : |∫ s in (0:ℝ)..t,
          Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n| ≤
        src.derivBound * reciprocalSquareTerm n := by
      have hadotcontOn : ContinuousOn (fun s => src.adot s n) (Icc 0 T) := src.hadotcont n
      have h_inorm := intervalIntegral.norm_integral_le_integral_norm
        (μ := MeasureTheory.MeasureSpace.volume) ht0.le
        (f := fun s => Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n)
      rw [Real.norm_eq_abs] at h_inorm
      calc |∫ s in (0:ℝ)..t,
              Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n|
          ≤ ∫ s in (0:ℝ)..t,
              ‖Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n‖ := h_inorm
        _ ≤ ∫ s in (0:ℝ)..t,
              src.derivBound * Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) := by
            apply intervalIntegral.integral_mono_on ht0.le
            · exact ((((Real.continuous_exp.comp (by fun_prop : Continuous (fun s =>
                  -(t - s) * unitIntervalCosineEigenvalue n))).continuousOn).mul
                (hadotcontOn.mono (Icc_subset_Icc le_rfl htT))).norm).intervalIntegrable_of_Icc
                ht0.le
            · have : Continuous (fun s =>
                  src.derivBound * Real.exp (-(t - s) * unitIntervalCosineEigenvalue n)) :=
                by fun_prop
              exact this.continuousOn.intervalIntegrable_of_Icc ht0.le
            · intro s hs
              rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _), mul_comm]
              exact mul_le_mul_of_nonneg_right
                (src.hderivBound s ⟨hs.1, le_trans hs.2 htT⟩ n) (Real.exp_nonneg _)
        _ = src.derivBound * ∫ s in (0:ℝ)..t,
              Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) := by
            rw [intervalIntegral.integral_const_mul]
        _ ≤ src.derivBound * (1 / unitIntervalCosineEigenvalue n) := by
            gcongr
            rw [le_div_iff₀ hlam_pos]
            linarith [ShenWork.IntervalDuhamelRegularity.parabolicGain_le_one hlam_nn ht0.le]
        _ ≤ src.derivBound * reciprocalSquareTerm n := by
            gcongr
            rw [reciprocalSquareTerm, unitIntervalCosineEigenvalue]
            apply div_le_div_of_nonneg_left (by linarith) (by positivity)
            calc ((n : ℝ) * Real.pi) ^ 2
                = (n : ℝ) ^ 2 * Real.pi ^ 2 := by ring
              _ ≥ (n : ℝ) ^ 2 * 1 := by
                  apply mul_le_mul_of_nonneg_left _ (by positivity)
                  nlinarith [Real.pi_gt_three]
              _ = (n : ℝ) ^ 2 := mul_one _
    linarith [abs_add_le
      (Real.exp (-t * unitIntervalCosineEigenvalue n) * a 0 n)
      (∫ s in (0:ℝ)..t,
        Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n)]

/-! ## Windowed Duhamel-leg joint continuity -/

/-- **Windowed Duhamel VALUE leg — joint continuity on `Ioo 0 T ×ˢ univ`.**
`(t,x) ↦ ∑' n, bₙ(t) cos(nπx)` from `DuhamelSourceTimeC1On a 0 T`. -/
theorem duhamelSeries_jointContinuousOn_of_on {a : ℝ → ℕ → ℝ} {T : ℝ}
    (src : DuhamelSourceTimeC1On a 0 T) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          ∑' n, duhamelSpectralCoeff a t n * cosineMode n x))
      (Ioo (0 : ℝ) T ×ˢ univ) := by
  change ContinuousOn
    (fun p : ℝ × ℝ => ∑' n, duhamelSpectralCoeff a p.1 n * cosineMode n p.2)
    (Ioo 0 T ×ˢ univ)
  apply continuousOn_of_forall_continuousAt
  intro p hp
  obtain ⟨hτ₀, _⟩ := mem_prod.1 hp
  have hτ₀_pos : 0 < p.1 := (mem_Ioo.1 hτ₀).1
  have hτ₀_lt_T : p.1 < T := (mem_Ioo.1 hτ₀).2
  set c := p.1 / 2 with hc_def
  set d := (p.1 + T) / 2 with hd_def
  have hc_pos : 0 < c := by positivity
  have hd_le_T : d ≤ T := by simp [hd_def]; linarith
  have hp_in_cd : p.1 ∈ Ioo c d := by
    constructor <;> simp [hc_def, hd_def] <;> linarith
  have henv_nn : ∀ n, 0 ≤ src.envelope n := fun n =>
    le_trans (abs_nonneg _) (src.henv_bound 0 ⟨le_refl _, by linarith⟩ n)
  have hu : Summable (fun n => T * src.envelope n) :=
    src.henv_summable.mul_left T
  have hcont_on : ContinuousOn
      (fun q : ℝ × ℝ => ∑' n, duhamelSpectralCoeff a q.1 n * cosineMode n q.2)
      (Ioo c d ×ˢ univ) := by
    apply continuousOn_tsum
    · intro n
      apply ContinuousOn.mul
      · exact ((duhamelSpectralCoeff_continuous_of_on src n).comp
          continuous_fst.continuousOn (fun q hq =>
            let ⟨hτ, _⟩ := mem_prod.1 hq
            ⟨lt_trans hc_pos (mem_Ioo.1 hτ).1,
             lt_of_lt_of_le (mem_Ioo.1 hτ).2 hd_le_T⟩))
      · exact (Real.continuous_cos.comp
          (continuous_const.mul continuous_snd)).continuousOn
    · exact hu
    · intro n q hq
      obtain ⟨hτ, _⟩ := mem_prod.1 hq
      have hτ_pos : 0 < q.1 := lt_trans hc_pos (mem_Ioo.1 hτ).1
      have hτ_le_T : q.1 ≤ T := le_trans (mem_Ioo.1 hτ).2.le hd_le_T
      rw [Real.norm_eq_abs, abs_mul]
      calc |duhamelSpectralCoeff a q.1 n| * |cosineMode n q.2|
          ≤ (q.1 * src.envelope n) * 1 :=
            mul_le_mul (abs_duhamelSpectralCoeff_le_on src hτ_pos hτ_le_T n)
              (cosineMode_abs_le_one' n q.2) (abs_nonneg _)
              (mul_nonneg hτ_pos.le (henv_nn n))
        _ = q.1 * src.envelope n := mul_one _
        _ ≤ T * src.envelope n :=
            mul_le_mul_of_nonneg_right hτ_le_T (henv_nn n)
  exact hcont_on.continuousAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      (mem_prod.2 ⟨hp_in_cd, mem_univ _⟩))

/-- **Windowed Duhamel DERIVATIVE leg — joint continuity on `Ioo 0 T ×ˢ univ`.** -/
theorem duhamelDerivSeries_jointContinuousOn_of_on {a : ℝ → ℕ → ℝ} {T : ℝ}
    (src : DuhamelSourceTimeC1On a 0 T) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          ∑' n, (a t n - unitIntervalCosineEigenvalue n *
            duhamelSpectralCoeff a t n) * cosineMode n x))
      (Ioo (0 : ℝ) T ×ˢ univ) := by
  change ContinuousOn
    (fun p : ℝ × ℝ => ∑' n,
      (a p.1 n - unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a p.1 n) *
        cosineMode n p.2)
    (Ioo 0 T ×ˢ univ)
  apply continuousOn_of_forall_continuousAt
  intro p hp
  obtain ⟨hτ₀, _⟩ := mem_prod.1 hp
  have hτ₀_pos : 0 < p.1 := (mem_Ioo.1 hτ₀).1
  have hτ₀_lt_T : p.1 < T := (mem_Ioo.1 hτ₀).2
  set c := p.1 / 2 with hc_def
  set d := (p.1 + T) / 2 with hd_def
  have hc_pos : 0 < c := by positivity
  have hd_le_T : d ≤ T := by simp [hd_def]; linarith
  have hp_in_cd : p.1 ∈ Ioo c d := by
    constructor <;> simp [hc_def, hd_def] <;> linarith
  have hu : Summable (fun n => src.envelope n + src.derivBound * reciprocalSquareTerm n) :=
    src.henv_summable.add (reciprocalSquareTerm_summable.mul_left src.derivBound)
  have hu_nn : ∀ n, 0 ≤ src.envelope n + src.derivBound * reciprocalSquareTerm n := fun n =>
    add_nonneg (le_trans (abs_nonneg _) (src.henv_bound 0 ⟨le_refl _, by linarith⟩ n))
      (mul_nonneg (le_trans (abs_nonneg _) (src.hderivBound 0 ⟨le_refl _, by linarith⟩ 0))
        (by unfold reciprocalSquareTerm; positivity))
  have hcont_on : ContinuousOn
      (fun q : ℝ × ℝ => ∑' n,
        (a q.1 n - unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a q.1 n) *
          cosineMode n q.2)
      (Ioo c d ×ˢ univ) := by
    apply continuousOn_tsum
    · intro n
      apply ContinuousOn.mul
      · apply ContinuousOn.sub
        · have : ContinuousOn (fun s => a s n) (Icc 0 T) :=
            fun s hs => (src.hderiv s hs n).continuousWithinAt
          exact (this.comp continuous_fst.continuousOn (fun q hq =>
            let ⟨hτ, _⟩ := mem_prod.1 hq
            ⟨le_of_lt (lt_trans hc_pos (mem_Ioo.1 hτ).1),
             le_trans (mem_Ioo.1 hτ).2.le hd_le_T⟩))
        · exact ((continuous_const).continuousOn.mul
            ((duhamelSpectralCoeff_continuous_of_on src n).comp
              continuous_fst.continuousOn (fun q hq =>
                let ⟨hτ, _⟩ := mem_prod.1 hq
                ⟨lt_trans hc_pos (mem_Ioo.1 hτ).1,
                 lt_of_lt_of_le (mem_Ioo.1 hτ).2 hd_le_T⟩)))
      · exact (Real.continuous_cos.comp
          (continuous_const.mul continuous_snd)).continuousOn
    · exact hu
    · intro n q hq
      obtain ⟨hτ, _⟩ := mem_prod.1 hq
      have hτ_pos : 0 < q.1 := lt_trans hc_pos (mem_Ioo.1 hτ).1
      have hτ_le_T : q.1 ≤ T := le_trans (mem_Ioo.1 hτ).2.le hd_le_T
      rw [Real.norm_eq_abs, abs_mul]
      calc |a q.1 n - unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a q.1 n| *
            |cosineMode n q.2|
          ≤ (src.envelope n + src.derivBound * reciprocalSquareTerm n) * 1 :=
            mul_le_mul (duhamel_deriv_bound_on src hτ_pos hτ_le_T n)
              (cosineMode_abs_le_one' n q.2) (abs_nonneg _) (hu_nn n)
        _ = src.envelope n + src.derivBound * reciprocalSquareTerm n := mul_one _
  exact hcont_on.continuousAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      (mem_prod.2 ⟨hp_in_cd, mem_univ _⟩))

/-! ## Windowed three-leg summabilities and tsum split -/

/-- Duhamel-leg value summability at `0 < t ≤ T` (windowed). -/
private theorem duhamelVal_summable_on {a : ℝ → ℕ → ℝ} {T : ℝ}
    (src : DuhamelSourceTimeC1On a 0 T)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (x : ℝ) :
    Summable (fun n => duhamelSpectralCoeff a t n * cosineMode n x) := by
  refine Summable.of_norm ((src.henv_summable.mul_left t).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun n => ?_))
  rw [Real.norm_eq_abs, abs_mul]
  calc |duhamelSpectralCoeff a t n| * |cosineMode n x|
      ≤ (t * src.envelope n) * 1 :=
        mul_le_mul (abs_duhamelSpectralCoeff_le_on src ht htT n) (cosineMode_abs_le_one' n x)
          (abs_nonneg _) (mul_nonneg ht.le
            (le_trans (abs_nonneg _) (src.henv_bound 0 ⟨le_refl _, by linarith⟩ n)))
    _ = t * src.envelope n := mul_one _

/-- Duhamel-leg derivative summability at `0 < t ≤ T` (windowed). -/
private theorem duhamelDerivVal_summable_on {a : ℝ → ℕ → ℝ} {T : ℝ}
    (src : DuhamelSourceTimeC1On a 0 T)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (x : ℝ) :
    Summable (fun n => (a t n - unitIntervalCosineEigenvalue n *
      duhamelSpectralCoeff a t n) * cosineMode n x) := by
  refine Summable.of_norm ((src.henv_summable.add
    (reciprocalSquareTerm_summable.mul_left src.derivBound)).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun n => ?_))
  rw [Real.norm_eq_abs, abs_mul]
  have hnn : 0 ≤ src.envelope n + src.derivBound * reciprocalSquareTerm n :=
    add_nonneg (le_trans (abs_nonneg _) (src.henv_bound 0 ⟨le_refl _, by linarith⟩ n))
      (mul_nonneg (le_trans (abs_nonneg _) (src.hderivBound 0 ⟨le_refl _, by linarith⟩ 0))
        (by unfold reciprocalSquareTerm; positivity))
  calc |a t n - unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a t n| * |cosineMode n x|
      ≤ (src.envelope n + src.derivBound * reciprocalSquareTerm n) * 1 :=
        mul_le_mul (duhamel_deriv_bound_on src ht htT n)
          (cosineMode_abs_le_one' n x) (abs_nonneg _) hnn
    _ = src.envelope n + src.derivBound * reciprocalSquareTerm n := mul_one _

/-- Value tsum = heat + chem + log on `Ioo 0 T ×ˢ univ` (windowed). -/
private theorem fullSourceCoeff_tsum_split_on {T : ℝ} (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p u) 0 T)
    (hlog : DuhamelSourceTimeC1On (coupledLogisticSourceCoeffs p u) 0 T)
    {q : ℝ × ℝ} (hq : q ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)) :
    (∑' n, fullSourceCoeff p u u₀cos q.1 n * cosineMode n q.2) =
      (∑' n, Real.exp (-q.1 * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n q.2)
      + (-p.χ₀) * (∑' n, duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) q.1 n
          * cosineMode n q.2)
      + (∑' n, duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) q.1 n
          * cosineMode n q.2) := by
  obtain ⟨hq1, _⟩ := mem_prod.1 hq
  have hqp : 0 < q.1 := (mem_Ioo.1 hq1).1
  have hqT : q.1 < T := (mem_Ioo.1 hq1).2
  have hheat := heatVal_summable' u₀cos hu0bd hqp q.2
  have hchemS := (duhamelVal_summable_on hchem hqp hqT.le q.2).mul_left (-p.χ₀)
  have hlogS := duhamelVal_summable_on hlog hqp hqT.le q.2
  rw [← tsum_mul_left (a := -p.χ₀), ← hheat.tsum_add hchemS,
    ← (hheat.add hchemS).tsum_add hlogS]
  refine (tsum_congr (fun n => ?_)).symm
  simp only [fullSourceCoeff]; ring

/-- Derivative tsum = heat + chem + log on `Ioo 0 T ×ˢ univ` (windowed). -/
private theorem fullSourceCoeffDot_tsum_split_on {T : ℝ} (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p u) 0 T)
    (hlog : DuhamelSourceTimeC1On (coupledLogisticSourceCoeffs p u) 0 T)
    {q : ℝ × ℝ} (hq : q ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)) :
    (∑' n, fullSourceCoeffDot p u u₀cos q.1 n * cosineMode n q.2) =
      (∑' n, -(unitIntervalCosineEigenvalue n) *
          Real.exp (-q.1 * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n q.2)
      + (-p.χ₀) * (∑' n, (coupledChemDivSourceCoeffs p u q.1 n
          - unitIntervalCosineEigenvalue n
            * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) q.1 n) * cosineMode n q.2)
      + (∑' n, (coupledLogisticSourceCoeffs p u q.1 n
          - unitIntervalCosineEigenvalue n
            * duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) q.1 n) * cosineMode n q.2)
      := by
  obtain ⟨hq1, _⟩ := mem_prod.1 hq
  have hqp : 0 < q.1 := (mem_Ioo.1 hq1).1
  have hqT : q.1 < T := (mem_Ioo.1 hq1).2
  have hheat := heatDerivVal_summable' u₀cos hu0bd hqp q.2
  have hchemS := (duhamelDerivVal_summable_on hchem hqp hqT.le q.2).mul_left (-p.χ₀)
  have hlogS := duhamelDerivVal_summable_on hlog hqp hqT.le q.2
  rw [← tsum_mul_left (a := -p.χ₀), ← hheat.tsum_add hchemS,
    ← (hheat.add hchemS).tsum_add hlogS]
  refine (tsum_congr (fun n => ?_)).symm
  simp only [fullSourceCoeffDot]; ring

/-! ## Windowed full-field joint continuity -/

/-- **VALUE field — windowed joint continuity on `Ioo 0 T ×ˢ univ`.** -/
private theorem fullSourceCoeff_jointContinuousOn_on {T : ℝ} (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p u) 0 T)
    (hlog : DuhamelSourceTimeC1On (coupledLogisticSourceCoeffs p u) 0 T) :
    ContinuousOn
      (fun q : ℝ × ℝ => ∑' n, fullSourceCoeff p u u₀cos q.1 n * cosineMode n q.2)
      (Ioo (0 : ℝ) T ×ˢ univ) := by
  have hsub : Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ) ⊆ Ioi (0 : ℝ) ×ˢ univ :=
    prod_mono (fun _ ht => mem_Ioi.2 (mem_Ioo.1 ht).1) (subset_refl _)
  have hheat := (heatValueSeries_jointContinuousOn' u₀cos hu0bd).mono hsub
  have hchemJ := duhamelSeries_jointContinuousOn_of_on hchem
  have hlogJ := duhamelSeries_jointContinuousOn_of_on hlog
  have hsum := ((hheat.add (hchemJ.const_smul (-p.χ₀))).add hlogJ)
  refine hsum.congr (fun q hq => ?_)
  have := fullSourceCoeff_tsum_split_on p u u₀cos hu0bd hchem hlog hq
  simp only [Pi.add_apply, Function.uncurry, smul_eq_mul] at this ⊢
  rw [this]

/-- **TIME-DERIV field — windowed joint continuity on `Ioo 0 T ×ˢ univ`.** -/
private theorem fullSourceCoeffDot_jointContinuousOn_on {T : ℝ} (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p u) 0 T)
    (hlog : DuhamelSourceTimeC1On (coupledLogisticSourceCoeffs p u) 0 T) :
    ContinuousOn
      (fun q : ℝ × ℝ => ∑' n, fullSourceCoeffDot p u u₀cos q.1 n * cosineMode n q.2)
      (Ioo (0 : ℝ) T ×ˢ univ) := by
  have hsub : Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ) ⊆ Ioi (0 : ℝ) ×ˢ univ :=
    prod_mono (fun _ ht => mem_Ioi.2 (mem_Ioo.1 ht).1) (subset_refl _)
  have hheat := (heatDerivSeries_jointContinuousOn' u₀cos hu0bd).mono hsub
  have hchemJ := duhamelDerivSeries_jointContinuousOn_of_on hchem
  have hlogJ := duhamelDerivSeries_jointContinuousOn_of_on hlog
  have hsum := ((hheat.add (hchemJ.const_smul (-p.χ₀))).add hlogJ)
  refine hsum.congr (fun q hq => ?_)
  have := fullSourceCoeffDot_tsum_split_on p u u₀cos hu0bd hchem hlog hq
  simp only [Pi.add_apply, Function.uncurry, smul_eq_mul] at this ⊢
  rw [this]

/-! ## The five windowed frontier theorems -/

/-- **(1) Windowed joint continuity of the value field on `Ioo 0 T ×ˢ Icc 0 1`.** -/
theorem fullSourceCoeff_jointSolutionClosed_on {T : ℝ} (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p u) 0 T)
    (hlog : DuhamelSourceTimeC1On (coupledLogisticSourceCoeffs p u) 0 T) :
    ContinuousOn
      (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
        ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
  (fullSourceCoeff_jointContinuousOn_on p u u₀cos hu0bd hchem hlog).mono
    (prod_mono (subset_refl _) (subset_univ _))

/-- **(2) Windowed joint continuity of the time-derivative field on `Ioo 0 T ×ˢ Icc 0 1`.** -/
theorem fullSourceCoeffDot_jointTimeDerivClosed_on {T : ℝ} (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p u) 0 T)
    (hlog : DuhamelSourceTimeC1On (coupledLogisticSourceCoeffs p u) 0 T) :
    ContinuousOn
      (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
        ∑' n, fullSourceCoeffDot p u u₀cos t n * cosineMode n x))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
  (fullSourceCoeffDot_jointContinuousOn_on p u u₀cos hu0bd hchem hlog).mono
    (prod_mono (subset_refl _) (subset_univ _))

/-- **(3) Windowed joint continuity of the time-derivative field on `Ioo 0 T ×ˢ Ioo 0 1`.** -/
theorem fullSourceCoeffDot_jointTimeDerivInterior_on {T : ℝ} (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p u) 0 T)
    (hlog : DuhamelSourceTimeC1On (coupledLogisticSourceCoeffs p u) 0 T) :
    ContinuousOn
      (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
        ∑' n, fullSourceCoeffDot p u u₀cos t n * cosineMode n x))
      (Ioo (0 : ℝ) T ×ˢ Ioo (0 : ℝ) 1) :=
  (fullSourceCoeffDot_jointContinuousOn_on p u u₀cos hu0bd hchem hlog).mono
    (prod_mono (subset_refl _) (subset_univ _))

end ShenWork.EWA
