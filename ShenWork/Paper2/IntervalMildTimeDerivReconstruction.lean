import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.Paper2.IntervalBFormSpectralHtime
import ShenWork.PDE.IntervalDuhamelCoeffFTC

open Set

noncomputable section

namespace ShenWork.Paper2.IntervalMildTimeDerivReconstruction

open ShenWork.IntervalConjugatePicard (ConjugateMildSolutionData)
open ShenWork.IntervalDuhamelCoeffFTC
  (localRestartCoeff_hasDerivAt_of_contSource)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalBFormSpectral (bFormSourceCoeffs)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs)
open ShenWork.IntervalDomain (intervalDomainPoint)

private theorem coeff_continuousOn_of_timeC1On
    {a : ℝ → ℕ → ℝ} {lo hi : ℝ}
    (src : DuhamelSourceTimeC1On a lo hi) (k : ℕ) :
    ContinuousOn (fun s : ℝ => a s k) (Icc lo hi) := by
  intro s hs
  exact (src.hderiv s hs k).continuousWithinAt

private theorem coeff_continuousOn_window_of_timeC1On
    {a : ℝ → ℕ → ℝ} {T c d : ℝ}
    (src : DuhamelSourceTimeC1On a 0 T) (k : ℕ)
    (hc : 0 < c) (hd : d < T) :
    ContinuousOn (fun s : ℝ => a s k) (Icc c d) := by
  have hbase : ContinuousOn (fun s : ℝ => a s k) (Icc (0 : ℝ) T) :=
    coeff_continuousOn_of_timeC1On src k
  refine hbase.mono ?_
  intro s hs
  exact ⟨le_of_lt (lt_of_lt_of_le hc hs.1), le_of_lt (lt_of_le_of_lt hs.2 hd)⟩

/-- B-form source coefficient continuity on a positive window, from the separate
logistic and chem-div source packages. -/
theorem bFormSourceCoeff_continuousOn_of_mild
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀) (k : ℕ)
    {c d : ℝ} (hc : 0 < c) (hd : d < S.T)
    (hlog_on : DuhamelSourceTimeC1On
      (coupledLogisticSourceCoeffs p S.u) 0 S.T)
    (hchem_on : DuhamelSourceTimeC1On
      (coupledChemDivSourceCoeffs p S.u) 0 S.T) :
    ContinuousOn (fun s => bFormSourceCoeffs p S.u s k) (Icc c d) := by
  have hlog :
      ContinuousOn (fun s => coupledLogisticSourceCoeffs p S.u s k) (Icc c d) :=
    coeff_continuousOn_window_of_timeC1On hlog_on k hc hd
  have hchem :
      ContinuousOn (fun s => coupledChemDivSourceCoeffs p S.u s k) (Icc c d) :=
    coeff_continuousOn_window_of_timeC1On hchem_on k hc hd
  simpa [bFormSourceCoeffs] using hlog.sub (continuousOn_const.mul hchem)

/-- Per-mode B-form restart ODE from source continuity, using the landed FTC in
`IntervalDuhamelCoeffFTC`. -/
theorem mildSolution_hasDerivAt_of_sourceContAndEnvelope
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    {a₀ : ℕ → ℝ} {c d t : ℝ} (hc : 0 < c)
    (hct : c < t) (htd : t < d) (hd : d < S.T) (k : ℕ)
    (hlog_on : DuhamelSourceTimeC1On
      (coupledLogisticSourceCoeffs p S.u) 0 S.T)
    (hchem_on : DuhamelSourceTimeC1On
      (coupledChemDivSourceCoeffs p S.u) 0 S.T) :
    HasDerivAt
      (fun τ =>
        localRestartCoeff a₀
          (fun ρ n => bFormSourceCoeffs p S.u (c + ρ) n) (τ - c) k)
      (bFormSourceCoeffs p S.u t k
        - unitIntervalCosineEigenvalue k *
          localRestartCoeff a₀
            (fun ρ n => bFormSourceCoeffs p S.u (c + ρ) n) (t - c) k) t := by
  have hcont :
      ContinuousOn (fun s => bFormSourceCoeffs p S.u s k) (Icc c d) :=
    bFormSourceCoeff_continuousOn_of_mild p S k hc hd hlog_on hchem_on
  exact localRestartCoeff_hasDerivAt_of_contSource hct htd k hcont

end ShenWork.Paper2.IntervalMildTimeDerivReconstruction
