/-
  ShenWork/Wiener/EWA/SourceChiNegDatumWienerDataObstruction.lean

  The monolithic `DatumWienerData` residual used by the current strict-negative
  uniform bridge already implies a common positive floor for every bounded
  positive constant datum, hence is not satisfiable over all interval PPID data.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceChiNegUniformBridge
import ShenWork.Paper2.IntervalDomainPPIDNoUniformFloor
import ShenWork.Paper2.IntervalDomainPdeUWiring

open Set
open ShenWork.IntervalDomain (intervalDomain intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalCosineInversion (intervalCosine_hasSum_pointwise reflCircle)
open ShenWork.Paper2 (PaperPositiveInitialDatum)

noncomputable section

namespace ShenWork.EWA

/-- A `DatumWienerData` package gives a common lower bound for every positive
constant PPID datum bounded by `1`.  The proof reads the lifting floor through
`DatumWienerLifting.hrecon` using pointwise cosine inversion at the midpoint. -/
theorem commonConstantFloor_of_datumWienerData
    {p : CM2Params} (hD : DatumWienerData p) :
    ∃ fm : ℝ, 0 < fm ∧
      ∀ a : ℝ, 0 < a → a ≤ 1 → fm ≤ a := by
  obtain ⟨fm, hfm, _WM, _hWM, hbody⟩ := hD.liftM 1 zero_lt_one
  refine ⟨fm, hfm, ?_⟩
  intro a ha_pos ha_le_one
  have hpaper : PaperPositiveInitialDatum intervalDomain
      (fun _ : intervalDomainPoint => a) :=
    ShenWork.Paper2.intervalDomain_const_paperPositive ha_pos
  have hbd : ∀ x : intervalDomainPoint, |(fun _ : intervalDomainPoint => a) x| ≤
      (1 : ℝ) := by
    intro x
    rw [abs_of_pos ha_pos]
    exact ha_le_one
  obtain ⟨W, hfloor, _hnorm⟩ := hbody hpaper hbd
  let xmid : intervalDomainPoint :=
    ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩
  have hfourier :
      Summable (fun n : ℤ => fourierCoeff (reflCircle W.u₀) n) :=
    ShenWork.Paper2.PdeUWiring.fourierCoeff_reflCircle_summable_of_cosineCoeff_abs
      W.hu₀ W.hsumc
  have hxmid : xmid.1 ∈ Set.Ioo (0 : ℝ) 1 := by
    norm_num
  have hinv :=
    intervalCosine_hasSum_pointwise W.u₀ W.hu₀ hxmid hfourier
  have hseries :
      (∑' n : ℕ, cosineCoeffs W.u₀ n * cosineMode n xmid.1)
        = W.u₀ xmid.1 := by
    rw [← hinv.tsum_eq]
    refine tsum_congr (fun n => ?_)
    simp only [cosineMode, unitIntervalCosineMode]
    ring
  calc
    fm ≤ W.floor := hfloor
    _ ≤ W.u₀ xmid.1 := W.hfloor _
    _ = a := by
      rw [← hseries]
      exact (W.hrecon xmid).symm

/-- Consequently the monolithic all-PPID `DatumWienerData` interface is not
satisfiable on the interval domain. -/
theorem not_datumWienerData (p : CM2Params) :
    ¬ DatumWienerData p := by
  intro hD
  obtain ⟨fm, hfm, hconst⟩ := commonConstantFloor_of_datumWienerData hD
  let a : ℝ := min (fm / 2) (1 / 2)
  have ha_pos : 0 < a := by
    dsimp [a]
    exact lt_min (by linarith) (by norm_num)
  have ha_le_one : a ≤ 1 := by
    dsimp [a]
    have hmin : min (fm / 2) (1 / 2) ≤ 1 / 2 :=
      min_le_right _ _
    linarith
  have ha_lt_fm : a < fm := by
    dsimp [a]
    have hmin : min (fm / 2) (1 / 2) ≤ fm / 2 :=
      min_le_left _ _
    linarith
  have hle : fm ≤ a := hconst a ha_pos ha_le_one
  linarith

end ShenWork.EWA

#print axioms ShenWork.EWA.not_datumWienerData
