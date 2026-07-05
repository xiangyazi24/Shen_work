/-
  ShenWork/Wiener/EWA/SourceInitialTraceDischarge.lean

  **Auto-discharge of the initial trace atoms `(hdefect, htrace)` from the
  `DuhamelSourceL1ContOn` data + datum summability.**

  `hdefect`: `∀ t ∈ (0,T), Summable (fun n => |fullSourceCoeff … t n − u₀cos n|)`
  `htrace`:  `Tendsto (fun t => ∑' n |…|) (𝓝[>] 0) (𝓝 0)`

  Both follow from triangle + DCT (Tannery's theorem in Mathlib).

  Key bound:
    `|fullSourceCoeff p u u₀cos t n − u₀cos n|`
    `≤ 2·|u₀cos n| + |χ₀|·t·chem_env n + t·log_env n`
    `≤ 2·|u₀cos n| + |χ₀|·T·chem_env n + T·log_env n` =: `G n`.

  `G n` is summable (from `hsumc` + L1ContOn envelopes).  Per mode, the defect
  → 0 as `t → 0⁺` since `exp(−tλₙ) → 1` and `|duhamel(t,n)| ≤ t·env n → 0`.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceStrongSolution
import ShenWork.Paper2.IntervalPicardLimitRestartWeak
import ShenWork.PDE.HeatSemigroup
import Mathlib.Analysis.Normed.Group.Tannery

open scoped BigOperators
open Set Filter Topology
open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs)
open ShenWork.IntervalPicardLimitRestartWeak
  (DuhamelSourceL1ContOn abs_duhamelSpectralCoeff_le_weak)
open ShenWork.IntervalDomain (intervalDomainPoint)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### Part 1 — the pointwise defect identity and bound. -/

theorem fullSourceCoeff_sub_eq (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) (t : ℝ) (n : ℕ) :
    fullSourceCoeff p u u₀cos t n - u₀cos n
      = (Real.exp (-t * unitIntervalCosineEigenvalue n) - 1) * u₀cos n
        + (-p.χ₀) * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n
        + duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) t n := by
  unfold fullSourceCoeff; ring

private theorem abs_exp_sub_one_le (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    |Real.exp (-t * unitIntervalCosineEigenvalue n) - 1| ≤ 2 := by
  rw [abs_le]
  constructor
  · linarith [Real.exp_pos (-t * unitIntervalCosineEigenvalue n)]
  · have : Real.exp (-t * unitIntervalCosineEigenvalue n) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ unitIntervalCosineEigenvalue n := by
        unfold unitIntervalCosineEigenvalue; positivity
      linarith [mul_nonneg ht this]
    linarith

/-! ### Part 2 — `hdefect` from L1ContOn. -/

theorem fullSourceCoeff_defect_summable_of_L1ContOn (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ)
    (hsumc : Summable (fun k => |u₀cos k|))
    (hchem : DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs p u) T)
    (hlog : DuhamelSourceL1ContOn (coupledLogisticSourceCoeffs p u) T) :
    ∀ t ∈ Ioo (0 : ℝ) T,
      Summable (fun n =>
        |fullSourceCoeff p u u₀cos t n - u₀cos n|) := by
  intro t ht
  have htpos := ht.1
  have htT := ht.2.le
  have hT_nonneg : 0 ≤ T := le_trans htpos.le htT
  refine Summable.of_nonneg_of_le
    (f := fun n =>
      2 * |u₀cos n| + |p.χ₀| * (T * hchem.envelope n) + T * hlog.envelope n)
    (g := fun n => |fullSourceCoeff p u u₀cos t n - u₀cos n|)
    (fun n => abs_nonneg _) (fun n => ?_) ?_
  · change |fullSourceCoeff p u u₀cos t n - u₀cos n| ≤
      2 * |u₀cos n| + |p.χ₀| * (T * hchem.envelope n) + T * hlog.envelope n
    rw [fullSourceCoeff_sub_eq]
    calc |(Real.exp (-t * unitIntervalCosineEigenvalue n) - 1) * u₀cos n
            + (-p.χ₀) * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n
            + duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) t n|
        ≤ |(Real.exp (-t * unitIntervalCosineEigenvalue n) - 1) * u₀cos n|
          + |(-p.χ₀) * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n|
          + |duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) t n| := by
            linarith [abs_add_le
              ((Real.exp (-t * unitIntervalCosineEigenvalue n) - 1) * u₀cos n
                + (-p.χ₀) * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n)
              (duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) t n),
              abs_add_le
                ((Real.exp (-t * unitIntervalCosineEigenvalue n) - 1) * u₀cos n)
                ((-p.χ₀) * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n)]
      _ ≤ 2 * |u₀cos n|
          + |p.χ₀| * (T * hchem.envelope n)
          + T * hlog.envelope n := by
            gcongr
            · rw [abs_mul]; gcongr; exact abs_exp_sub_one_le t htpos.le n
            · rw [abs_mul, abs_neg]; gcongr
              exact le_trans (abs_duhamelSpectralCoeff_le_weak hchem htpos htT n)
                (by
                  have henv_nonneg : 0 ≤ hchem.envelope n :=
                    le_trans (abs_nonneg _) (hchem.henv_bound 0 le_rfl hT_nonneg n)
                  exact mul_le_mul_of_nonneg_right htT henv_nonneg)
            · exact le_trans (abs_duhamelSpectralCoeff_le_weak hlog htpos htT n)
                (by
                  have henv_nonneg : 0 ≤ hlog.envelope n :=
                    le_trans (abs_nonneg _) (hlog.henv_bound 0 le_rfl hT_nonneg n)
                  exact mul_le_mul_of_nonneg_right htT henv_nonneg)
  · exact ((hsumc.mul_left 2).add
      ((hchem.henv_summable.mul_left (|p.χ₀| * T)).congr (fun n => by ring))).add
      ((hlog.henv_summable.mul_left T).congr (fun n => by ring))

/-! ### Part 3 — `htrace` via Tannery (ℓ¹ DCT). -/

theorem fullSourceCoeff_trace_tendsto_of_L1ContOn (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ)
    (hsumc : Summable (fun k => |u₀cos k|))
    (hchem : DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs p u) T)
    (hlog : DuhamelSourceL1ContOn (coupledLogisticSourceCoeffs p u) T)
    (hTpos : 0 < T) :
    Tendsto
      (fun t => ∑' n, |fullSourceCoeff p u u₀cos t n - u₀cos n|)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  set G : ℕ → ℝ := fun n =>
    2 * |u₀cos n| + |p.χ₀| * T * hchem.envelope n + T * hlog.envelope n with hG_def
  have hGsum : Summable G :=
    ((hsumc.mul_left 2).add
      ((hchem.henv_summable.mul_left (|p.χ₀| * T)).congr (fun n => by ring))).add
      ((hlog.henv_summable.mul_left T).congr (fun n => by ring))
  -- Use Tannery's theorem with f t n = |defect t n| (nonneg → ‖f t n‖ = f t n)
  -- We need: ∀ k, f t k → g k = 0 per mode, and ‖f t k‖ ≤ bound k eventually.
  have hpoint : ∀ n : ℕ,
      Tendsto (fun t : ℝ => |fullSourceCoeff p u u₀cos t n - u₀cos n|)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    intro n
    -- Per-mode convergence: |defect t n| → 0 as t → 0⁺.
    set upper : ℝ → ℝ := fun t =>
      |Real.exp (-t * unitIntervalCosineEigenvalue n) - 1| * |u₀cos n|
        + |p.χ₀| * (t * hchem.envelope n) + t * hlog.envelope n with hupper
    refine squeeze_zero'
      (t₀ := 𝓝[>] (0 : ℝ))
      (f := fun t => |fullSourceCoeff p u u₀cos t n - u₀cos n|)
      (g := upper)
      (Eventually.of_forall (fun t => abs_nonneg _)) ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT hTpos] with t ht
      show |fullSourceCoeff p u u₀cos t n - u₀cos n| ≤ upper t
      rw [fullSourceCoeff_sub_eq]
      calc |(Real.exp (-t * unitIntervalCosineEigenvalue n) - 1) * u₀cos n
              + (-p.χ₀) * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n
              + duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) t n|
          ≤ |(Real.exp (-t * unitIntervalCosineEigenvalue n) - 1) * u₀cos n|
            + |(-p.χ₀) * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n|
            + |duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) t n| := by
              linarith [abs_add_le
                ((Real.exp (-t * unitIntervalCosineEigenvalue n) - 1) * u₀cos n
                  + (-p.χ₀) * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n)
                (duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) t n),
                abs_add_le
                  ((Real.exp (-t * unitIntervalCosineEigenvalue n) - 1) * u₀cos n)
                  ((-p.χ₀) * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n)]
        _ ≤ upper t := by
              have hchem_le :
                  |(-p.χ₀) *
                    duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n|
                    ≤ |p.χ₀| * (t * hchem.envelope n) := by
                rw [abs_mul, abs_neg]
                exact mul_le_mul_of_nonneg_left
                  (abs_duhamelSpectralCoeff_le_weak hchem ht.1 ht.2.le n)
                  (abs_nonneg _)
              have hlog_le :
                  |duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) t n|
                    ≤ t * hlog.envelope n :=
                abs_duhamelSpectralCoeff_le_weak hlog ht.1 ht.2.le n
              rw [hupper, abs_mul]
              linarith
    · show Tendsto upper (𝓝[>] (0 : ℝ)) (𝓝 0)
      have hexp_tend : Tendsto (fun t : ℝ =>
          |Real.exp (-t * ↑(unitIntervalCosineEigenvalue n)) - 1|)
          (𝓝 (0 : ℝ)) (𝓝 0) := by
        have hinner : Continuous (fun t : ℝ => -t * unitIntervalCosineEigenvalue n) :=
          continuous_id.neg.mul continuous_const
        have hexp : Continuous (fun t : ℝ =>
            Real.exp (-t * unitIntervalCosineEigenvalue n)) :=
          Real.continuous_exp.comp hinner
        have hsub : Continuous (fun t : ℝ =>
            Real.exp (-t * unitIntervalCosineEigenvalue n) - 1) :=
          hexp.sub continuous_const
        have habs : Continuous (fun t : ℝ =>
            |Real.exp (-t * unitIntervalCosineEigenvalue n) - 1|) :=
          hsub.abs
        simpa using habs.tendsto (0 : ℝ)
      have ht_nhds : Tendsto id (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have h1 : Tendsto (fun t : ℝ =>
          |Real.exp (-t * ↑(unitIntervalCosineEigenvalue n)) - 1| * |u₀cos n|)
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        simpa using
          ((hexp_tend.mono_left nhdsWithin_le_nhds).mul
            (tendsto_const_nhds : Tendsto (fun _ : ℝ => |u₀cos n|)
              (𝓝[>] (0 : ℝ)) (𝓝 |u₀cos n|)))
      have h2 : Tendsto (fun t : ℝ => |p.χ₀| * (t * hchem.envelope n))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        simpa using
          ((tendsto_const_nhds : Tendsto (fun _ : ℝ => |p.χ₀|)
              (𝓝[>] (0 : ℝ)) (𝓝 |p.χ₀|)).mul
            (ht_nhds.mul
              (tendsto_const_nhds : Tendsto (fun _ : ℝ => hchem.envelope n)
                (𝓝[>] (0 : ℝ)) (𝓝 (hchem.envelope n)))))
      have h3 : Tendsto (fun t : ℝ => t * hlog.envelope n)
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        simpa using
          (ht_nhds.mul
            (tendsto_const_nhds : Tendsto (fun _ : ℝ => hlog.envelope n)
              (𝓝[>] (0 : ℝ)) (𝓝 (hlog.envelope n))))
      have := h1.add (h2.add h3)
      rwa [show (0 : ℝ) + (0 + 0) = 0 from by ring,
        show (fun t => |Real.exp (-t * ↑(unitIntervalCosineEigenvalue n)) - 1| * |u₀cos n|
          + (|p.χ₀| * (t * hchem.envelope n) + t * hlog.envelope n))
          = upper from funext (fun t => by rw [hupper]; ring)] at this
  have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ k : ℕ,
      ‖|fullSourceCoeff p u u₀cos t k - u₀cos k|‖ ≤ G k := by
    -- Domination: ‖|defect t n|‖ = |defect t n| ≤ G n for t near 0⁺.
    filter_upwards [Ioo_mem_nhdsGT hTpos] with t ht
    intro n
    have hT_nonneg : 0 ≤ T := le_trans ht.1.le ht.2.le
    rw [Real.norm_eq_abs, abs_abs]
    rw [fullSourceCoeff_sub_eq]
    calc |(Real.exp (-t * unitIntervalCosineEigenvalue n) - 1) * u₀cos n
            + (-p.χ₀) * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n
            + duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) t n|
        ≤ |(Real.exp (-t * unitIntervalCosineEigenvalue n) - 1) * u₀cos n|
          + |(-p.χ₀) * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n|
          + |duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) t n| := by
            linarith [abs_add_le
              ((Real.exp (-t * unitIntervalCosineEigenvalue n) - 1) * u₀cos n
                + (-p.χ₀) * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n)
              (duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) t n),
              abs_add_le
                ((Real.exp (-t * unitIntervalCosineEigenvalue n) - 1) * u₀cos n)
                ((-p.χ₀) * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n)]
      _ ≤ 2 * |u₀cos n|
          + |p.χ₀| * (T * hchem.envelope n)
          + T * hlog.envelope n := by
            gcongr
            · rw [abs_mul]; gcongr; exact abs_exp_sub_one_le t ht.1.le n
            · rw [abs_mul, abs_neg]; gcongr
              exact le_trans (abs_duhamelSpectralCoeff_le_weak hchem ht.1 ht.2.le n)
                (by
                  have henv_nonneg : 0 ≤ hchem.envelope n :=
                    le_trans (abs_nonneg _) (hchem.henv_bound 0 le_rfl hT_nonneg n)
                  exact mul_le_mul_of_nonneg_right ht.2.le henv_nonneg)
            · exact le_trans (abs_duhamelSpectralCoeff_le_weak hlog ht.1 ht.2.le n)
                (by
                  have henv_nonneg : 0 ≤ hlog.envelope n :=
                    le_trans (abs_nonneg _) (hlog.henv_bound 0 le_rfl hT_nonneg n)
                  exact mul_le_mul_of_nonneg_right ht.2.le henv_nonneg)
      _ = G n := by
            rw [hG_def]
            ring
  simpa using
    (tendsto_tsum_of_dominated_convergence
      (α := ℝ) (β := ℕ) (G := ℝ)
      (𝓕 := 𝓝[>] (0 : ℝ))
      (f := fun t n => |fullSourceCoeff p u u₀cos t n - u₀cos n|)
      (g := fun _n : ℕ => 0)
      (bound := G)
      hGsum hpoint hbound)

end ShenWork.EWA
