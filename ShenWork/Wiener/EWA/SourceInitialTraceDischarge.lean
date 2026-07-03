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

open scoped BigOperators
open Set Filter Topology
open ShenWork.Wiener (unitIntervalCosineEigenvalue)
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
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_) ?_
  · rw [fullSourceCoeff_sub_eq]
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
                (by nlinarith)
            · exact le_trans (abs_duhamelSpectralCoeff_le_weak hlog htpos htT n)
                (by nlinarith)
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
    2 * |u₀cos n| + |p.χ₀| * T * hchem.envelope n + T * hlog.envelope n
  have hGsum : Summable G :=
    ((hsumc.mul_left 2).add
      ((hchem.henv_summable.mul_left (|p.χ₀| * T)).congr (fun n => by ring))).add
      ((hlog.henv_summable.mul_left T).congr (fun n => by ring))
  -- Use Tannery's theorem with f t n = |defect t n| (nonneg → ‖f t n‖ = f t n)
  -- We need: ∀ k, f t k → g k = 0 per mode, and ‖f t k‖ ≤ bound k eventually.
  rw [show (0 : ℝ) = ∑' n, (0 : ℝ) from (tsum_zero).symm]
  refine tendsto_tsum_of_dominated_convergence hGsum (fun n => ?_) ?_
  · -- Per-mode convergence: |defect t n| → 0 as t → 0⁺
    set upper : ℝ → ℝ := fun t =>
      |Real.exp (-t * unitIntervalCosineEigenvalue n) - 1| * |u₀cos n|
        + |p.χ₀| * (t * hchem.envelope n) + t * hlog.envelope n
    refine squeeze_zero' (Eventually.of_forall (fun t => abs_nonneg _)) ?_ ?_
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
              unfold_let upper; gcongr
              · exact (abs_mul _ _).le
              · rw [abs_mul, abs_neg]; gcongr
                exact abs_duhamelSpectralCoeff_le_weak hchem ht.1 ht.2.le n
              · exact abs_duhamelSpectralCoeff_le_weak hlog ht.1 ht.2.le n
    · show Tendsto upper (𝓝[>] (0 : ℝ)) (𝓝 0)
      have hexp_tend : Tendsto (fun t : ℝ =>
          |Real.exp (-t * ↑(unitIntervalCosineEigenvalue n)) - 1|)
          (𝓝 (0 : ℝ)) (𝓝 0) := by
        have := ((Real.continuous_exp.comp
          (continuous_neg.mul continuous_const)).sub
          continuous_const).norm.tendsto (0 : ℝ)
        simp at this; exact this
      have ht_nhds : Tendsto id (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have h1 : Tendsto (fun t : ℝ =>
          |Real.exp (-t * ↑(unitIntervalCosineEigenvalue n)) - 1| * |u₀cos n|)
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        rw [show (0 : ℝ) = 0 * |u₀cos n| from by ring]
        exact (hexp_tend.mono_left nhdsWithin_le_nhds).mul tendsto_const_nhds
      have h2 : Tendsto (fun t : ℝ => |p.χ₀| * (t * hchem.envelope n))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        rw [show (0 : ℝ) = |p.χ₀| * (0 * hchem.envelope n) from by ring]
        exact tendsto_const_nhds.mul (ht_nhds.mul tendsto_const_nhds)
      have h3 : Tendsto (fun t : ℝ => t * hlog.envelope n)
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        rw [show (0 : ℝ) = 0 * hlog.envelope n from by ring]
        exact ht_nhds.mul tendsto_const_nhds
      have := h1.add (h2.add h3)
      rwa [show (0 : ℝ) + (0 + 0) = 0 from by ring,
        show (fun t => |Real.exp (-t * ↑(unitIntervalCosineEigenvalue n)) - 1| * |u₀cos n|
          + (|p.χ₀| * (t * hchem.envelope n) + t * hlog.envelope n))
          = upper from funext (fun t => by unfold_let upper; ring)] at this
  · -- Domination: ‖|defect t n|‖ = |defect t n| ≤ G n for t near 0⁺
    filter_upwards [Ioo_mem_nhdsGT hTpos] with t ht
    intro n
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
                (by nlinarith)
            · exact le_trans (abs_duhamelSpectralCoeff_le_weak hlog ht.1 ht.2.le n)
                (by nlinarith)

end ShenWork.EWA
