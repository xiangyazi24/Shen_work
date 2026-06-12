import ShenWork.Paper2.IntervalChiNegResolverC2HeatFactor

/-!
# χ₀ < 0 resolver C2 restart audit

This file pins the remaining branch to the committed restart definitions.
The K1 restart gives a positive target shift and a homogeneous heat term in the
solution restart coefficient.  The C2 source package, however, is attached to
the raw clamped source family `aC`.
-/

noncomputable section

open ShenWork.IntervalDuhamelClosedC2
  (DuhamelSourceTimeC1 duhamelSpectralCoeff)
open ShenWork.IntervalResolverSpectralTimeC2 (DuhamelSourceTimeC2Coeff)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.Paper2.PicardLimitK1 (LocalRestart)
open ShenWork.Paper2.PicardLimitK1C2Coeff
  (LocalRestartC2 SourceC2CoeffFields)

namespace ShenWork.Paper2.ChiNegResolverC2RestartAudit

variable {p : CM2Params}
variable {u : ℝ → ShenWork.IntervalDomain.intervalDomainPoint → ℝ}
variable {T σ : ℝ}

/-- The K1 target is evaluated at positive shifted restart time. -/
theorem localRestart_target_shift_pos (L : LocalRestart p u T σ) :
    0 < σ - L.τ := by
  linarith [L.hστ]

/-- The committed restart coefficient is homogeneous heat plus Duhamel source. -/
theorem localRestartCoeff_eq_heat_plus_duhamel
    (a₀ : ℕ → ℝ) (a : ℝ → ℕ → ℝ) (τ : ℝ) (n : ℕ) :
    localRestartCoeff a₀ a τ n =
      Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n +
        duhamelSpectralCoeff a τ n := by
  rfl

/-- At the K1 target, the solution coefficient still contains the Duhamel
source remainder unless that term is separately eliminated. -/
theorem target_restartCoeff_eq_heat_plus_duhamel
    (L : LocalRestart p u T σ) (n : ℕ) :
    localRestartCoeff L.a₀ L.aC (σ - L.τ) n =
      Real.exp (-(σ - L.τ) * unitIntervalCosineEigenvalue n) * L.a₀ n +
        duhamelSpectralCoeff L.aC (σ - L.τ) n := by
  rfl

/-- The K1 restart's available C1 source package is for the raw clamped source
family `aC`, not for the full restart coefficient. -/
def rawClampedSourceTimeC1 (L : LocalRestart p u T σ) :
    DuhamelSourceTimeC1 L.aC :=
  L.srcC

/-- The strengthened K1 package required by the resolver is likewise a C2
package for the same raw clamped source family. -/
def rawClampedSourceC2Coeff (L : LocalRestartC2 p u T σ) :
    DuhamelSourceTimeC2Coeff L.base.aC :=
  L.srcC2

/-- The precise remaining regularity need is the source-side C2 envelope package
for the raw clamped source `L.aC`. -/
abbrev rawClampedSourceRegularityNeed (L : LocalRestart p u T σ) : Type :=
  SourceC2CoeffFields L.srcC

/-- Upgrading by source fields targets `L.aC` exactly. -/
theorem ofSourceFields_targets_raw_aC
    (L : LocalRestart p u T σ) (F : SourceC2CoeffFields L.srcC) :
    (LocalRestartC2.ofSourceFields L F).srcC2.toTimeC1 = L.srcC := by
  rfl

end ShenWork.Paper2.ChiNegResolverC2RestartAudit
