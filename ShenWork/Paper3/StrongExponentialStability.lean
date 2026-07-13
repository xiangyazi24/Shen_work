/-
  Strong fractional-power, all-time nonlinear stability interface.

  This is deliberately separate from the weak/sup-norm eventual theorem.  It
  also records an actual initial state at `t = 0`, since the legacy
  `InitialTrace` predicate constrains only the right limit and permits arbitrary
  values of both solution components at zero.
-/
import ShenWork.Paper3.IntervalDomainSectorial
import ShenWork.PDE.FractionalPowerSpace
import ShenWork.Paper3.IntervalDomainConstantResolver

namespace ShenWork.Paper3

open ShenWork.PDE.FractionalPower
open ShenWork.PDE
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.Paper2

noncomputable section

/-- Cosine coefficient of the physical perturbation `w-uStar`. -/
def intervalDomainPerturbationCosineCoeff
    (uStar : ℝ) (w : intervalDomainPoint → ℝ) (n : ℕ) : ℂ :=
  (cosineCoeffs (fun x => intervalDomainLift w x - uStar) n : ℂ)

/-- Membership of the perturbation in the spectral Hilbert realization of
`X_2^sigma = D((I-Delta_N)^sigma)`. -/
def IntervalDomainX2SigmaPerturbation
    (sigma uStar : ℝ) (w : intervalDomainPoint → ℝ) : Prop :=
  Summable fun n : ℕ =>
    fractionalPowerEnergyTerm 1 sigma
      (intervalDomainPerturbationCosineCoeff uStar w) n

/-- Strong spectral norm of the perturbation.  Consumers pair this real value
with `IntervalDomainX2SigmaPerturbation`; the membership hypothesis prevents
the usual `tsum`-of-a-nonsummable-series convention from being misread as a
finite norm. -/
def intervalDomainX2SigmaDistance
    (sigma uStar : ℝ) (w : intervalDomainPoint → ℝ) : ℝ :=
  Real.sqrt (∑' n : ℕ,
    fractionalPowerEnergyTerm 1 sigma
      (intervalDomainPerturbationCosineCoeff uStar w) n)

/-- Genuine time-zero identification for the strong theorem.  The elliptic
component is initialized by the Neumann resolver, so the all-time `C¹` output
cannot be defeated by changing `v 0` while keeping the same positive-time
solution. -/
def IntervalDomainStrongInitialState
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u v : ℝ → intervalDomainPoint → ℝ) : Prop :=
  u 0 = u₀ ∧ v 0 = intervalNeumannResolverR p u₀

/-- Stage A (Henry form): smallness in a strong fractional-power phase norm
gives all-time exponential decay in that norm and, because `sigma>3/4` in the
unit-interval Hilbert realization, in the concrete `C¹` distance.  This is a
correct nearby theorem, not the paper's flawed all-time claim from a weak
`L∞` ball. -/
def IntervalDomainStrongSpectralSemigroupOrbitBound
    (p : CM2Params) : Prop :=
  p.m = 1 ∧
  ∀ sigma uStar vStar,
    3 / 4 < sigma → sigma < 1 →
    Paper3ConstantEquilibrium p uStar vStar →
    LinearlyStable unitIntervalNeumannSpectrum p uStar vStar →
      ∃ eps > 0, ∃ C > 0, ∃ rate > 0,
        ∀ u₀ : intervalDomainPoint → ℝ,
          PositiveInitialDatum intervalDomain u₀ →
          IntervalDomainX2SigmaPerturbation sigma uStar u₀ →
          intervalDomainX2SigmaDistance sigma uStar u₀ ≤ eps →
          EquilibriumInitialMassCompatible intervalDomain p uStar u₀ →
            ∀ u v : ℝ → intervalDomainPoint → ℝ,
              IsPaper2GlobalClassicalSolution intervalDomain p u v →
              InitialTrace intervalDomain u₀ u →
              IntervalDomainStrongInitialState p u₀ u v →
                ∀ t, 0 ≤ t →
                  IntervalDomainX2SigmaPerturbation sigma uStar (u t) ∧
                  intervalDomainX2SigmaDistance sigma uStar (u t) ≤
                    C * Real.exp (-rate * t) *
                      intervalDomainX2SigmaDistance sigma uStar u₀ ∧
                  intervalDomainSectorialC1Distance (u t) (fun _ => uStar) +
                    intervalDomainSectorialC1Distance (v t) (fun _ => vStar) ≤
                      C * Real.exp (-rate * t) *
                        intervalDomainX2SigmaDistance sigma uStar u₀

/-- Stage B is the already repaired weak-data interface: the input gauge is
the concrete sup distance and the `C¹` estimate begins only after a uniform
positive smoothing time. -/
abbrev IntervalDomainWeakSupEventualSpectralSemigroupOrbitBound
    (p : CM2Params) : Prop :=
  IntervalDomainSpectralSemigroupOrbitBoundCorrected p
    intervalDomainSectorialStabilityNorms

#print axioms intervalDomainPerturbationCosineCoeff
#print axioms intervalDomainX2SigmaDistance

end

end ShenWork.Paper3
