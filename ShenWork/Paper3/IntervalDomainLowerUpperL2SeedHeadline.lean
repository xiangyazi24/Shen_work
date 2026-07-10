import ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly
import ShenWork.Paper2.IntervalDomainL2SeedFrontierProducer
import ShenWork.PDE.P3MoserIntegratedDissipationPDEv2

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open ShenWork.IntervalDomainExistence.P3MoserIntegratedDissipationPDEv2
open ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
open ShenWork.IntervalDomainExistence.P3MoserRegularityProducer
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainMoserClosure

namespace ShenWork.Paper3

noncomputable section

/-!
This file thins the actual-linear lower/upper Moser headline at its L2 seed.

The previous headline asks for a full `ClosedEnergyIdentityTraceData` package
and immediately projects it to `IntervalDomainL2SeedRegularityFrontier`.  The
route below takes that exact consumer-facing L2 regularity frontier instead.
The lower/upper first-crossing and quantitative endpoint frontiers are
unchanged.
-/

/-- Actual-linear lower/upper Moser residuals at the exact L2 seed interface
consumed by the a-priori global-existence route. -/
structure
    IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerUpperL2SeedResiduals
    (p : CM2Params) : Prop where
  boundednessHyp : IntervalDomainBoundednessHyp p
  l2SeedRegularity :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainL2SeedRegularityFrontier T u
  lowerUpperFrontiers :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        Nonempty
          (IntegratedMoserFirstCrossingLowerUpperFrontiers
            intervalDomain u T rho p0)
  quantitativeEndpoint :
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
    ∀ {T : ℝ}, 0 < T →
    ∀ {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
    ∀ pExp,
      max (p.N : ℝ)
          (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
      LpPowerBoundedBefore intervalDomain pExp T u →
        ∃ pSeq rootBound : ℕ → ℝ,
          (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
            IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound

namespace
    IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerUpperL2SeedResiduals

/-- Supply the reusable lower/upper residual package without passing through
the stronger closed-energy trace package. -/
def to_lowerUpperFrontierResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerUpperL2SeedResiduals
        p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainMassLpSmoothingLowerUpperFrontierResiduals p where
  a_pos := ha
  chi_nonneg := le_of_lt hχ0
  boundednessHyp := h.boundednessHyp
  l2SeedRegularity := h.l2SeedRegularity
  lowerUpperFrontiers := fun hsol hcross hboot =>
    Classical.choice (h.lowerUpperFrontiers hsol hcross hboot)
  quantitativeEndpoint := h.quantitativeEndpoint

/-- Produce the mass/Lp/smoothing route used by continuation from the thinner
L2-seed lower/upper frontier. -/
def to_routeResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerUpperL2SeedResiduals
        p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainMassLpSmoothingRouteResiduals p :=
  (h.to_lowerUpperFrontierResiduals ha hχ0).to_routeResiduals

end
    IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerUpperL2SeedResiduals

/-- Sectorial actual-linear facts whose Moser component exposes only the L2
seed regularity consumed downstream. -/
structure IntervalDomainSectorialMainlineMoserActualLinearSmallLowerUpperL2SeedFacts
    (p : CM2Params) : Prop where
  spectralSemigroupOrbitBound :
    IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p
  continuation : IntervalDomainStandardContinuationGluingData p
  massLpSmoothing :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerUpperL2SeedResiduals
      p

namespace
    IntervalDomainSectorialMainlineMoserActualLinearSmallLowerUpperL2SeedFacts

/-- Convert the L2-seed lower/upper facts to the existing actual-linear
a-priori mainline facts. -/
def to_aprioriActualLinearSmallFacts
    {p : CM2Params}
    (h :
      IntervalDomainSectorialMainlineMoserActualLinearSmallLowerUpperL2SeedFacts
        p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts p where
  spectralSemigroupOrbitBound := h.spectralSemigroupOrbitBound
  continuation := h.continuation
  massLpSmoothing := h.massLpSmoothing.to_routeResiduals ha hχ0

end
    IntervalDomainSectorialMainlineMoserActualLinearSmallLowerUpperL2SeedFacts

/-- Thin Paper3 mainline frontiers with the closed-energy headline field
removed in favor of the exact L2 seed regularity floor. -/
structure
    IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperL2SeedThinFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop) : Prop where
  core :
    IntervalDomainSectorialMainlineMoserActualLinearSmallLowerUpperL2SeedFacts
      p
  initialContinuity : IntervalDomainInitialContinuityRaw p
  compactness :
    IntervalDomainPaper3SupNormCompactnessAPosData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound
  stability24 :
    IntervalDomainPaper3Stability24ActualLinearFrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Assemble the interval-domain Paper3 mainline from the L2-seed lower/upper
headline frontiers. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_lowerUpperL2SeedThinData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperL2SeedThinFrontierData
        p M0 uBar vLower locallyConverges neumannResolventGradientBound) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  intervalDomain_paper3_mainlineTargets_of_aprioriActualLinearSmallFrontierData
    p M0 uBar vLower
    (intervalDomainSupNormCompactnessData
      locallyConverges neumannResolventGradientBound)
    ha hb hχ0 hm hβ hχ
    { core := hData.core.to_aprioriActualLinearSmallFacts ha hχ0
      compactness :=
        (hData.compactness.toSupNormData ha hData.initialContinuity).toConcrete
      stability := hData.stability24.toStability23To25 ha hχ0 }

/-- Instance-facing L2-seed lower/upper Paper3 mainline. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_lowerUpperL2SeedThinDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperL2SeedThinFrontierData
        p M0 uBar vLower locallyConverges neumannResolventGradientBound)] :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  intervalDomain_paper3_mainlineTargets_of_lowerUpperL2SeedThinData
    p M0 uBar vLower locallyConverges neumannResolventGradientBound
    ha hb hχ0 hm hβ hχ hData.out

/-- Full statement data for the L2-seed lower/upper headline, with Paper2
supplying Propositions 1.3 and 1.4. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperL2SeedThinP2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop) : Prop where
  paper2Main : IntervalDomainPaper2MainTheoremTargets p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperL2SeedThinFrontierData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound

/-- Full Paper3 statement target from the L2-seed lower/upper headline. -/
theorem
    intervalDomain_paper3_statementTargets_of_lowerUpperL2SeedThinP2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperL2SeedThinP2MainNoNegData
        p C M0 uBar vLower locallyConverges
          neumannResolventGradientBound) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  { left :=
      intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsData
        p C
        { negativeBound :=
            intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos
              p hχ0
          paper2Main := hData.paper2Main }
    right :=
      intervalDomain_paper3_mainlineTargets_of_lowerUpperL2SeedThinData
        p M0 uBar vLower locallyConverges neumannResolventGradientBound
        ha hb hχ0 hm hβ hχ hData.mainline }

/-! ### PDE-atom headline

The lower/upper package above is a useful consumer interface, but it still
stores three conclusions of internal producer chains: the complete L2 seed,
the first-crossing lower/upper bundle, and the quantitative endpoint bundle.
The route below exposes the smaller analytic inputs used by those producers.

This is still a conditional residual surface, not a playbook B/C completion:
none of the PDE, continuation, compactness, orbit, or stability frontiers below
is asserted to follow from the displayed parameter assumptions alone.
-/

/-- Endpoint data not supplied by the strict-interior classical-solution API.
All other fields of the L2 seed are derived from classical regularity. -/
structure IntervalDomainL2SeedEndpointFrontiers
    (T : ℝ) (u : ℝ → intervalDomain.Point → ℝ) : Prop where
  endpointEnergy : IntervalDomainPowerEnergyEndpointContinuity u T 2
  zeroRightDerivative : IntervalDomainL2SeedZeroRightDerivative u

/-- Analytic residuals below the consumer-shaped lower/upper Moser package.

`energyWindowFTC` and `energyWithGap` are the remaining integrated energy
frontiers.  Together with classical regularity and relative interpolation they
produce integrated dissipation and hence the first-crossing step.  The final
pointwise power estimate is kept explicit; only its sequence/root packaging is
constructed internally. -/
structure
    IntervalDomainMassLpSmoothingMoserActualLinearSmallPDEAtomResiduals
    (p : CM2Params) : Prop where
  boundednessCore : IntervalDomainMoserActualLinearSmallBoundednessCore p
  l2SeedEndpoint :
    ∀ {T : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
        IntervalDomainL2SeedEndpointFrontiers T u
  classicalRegularity :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntervalDomainIntegratedMoserClassicalRegularityData u T p0
  energyWindowFTC :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntegratedMoserEnergyWindowFTC intervalDomain u T p0
  relativeMoserInterpolation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        RelativeMoserInterpolationBefore intervalDomain u T rho p0
  energyWithGap :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        LpBootstrapEnergyInequalityWithGap intervalDomain u T rho p0
  terminalPointwise :
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
    ∀ {T : ℝ}, 0 < T →
    ∀ {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
    ∀ pExp,
      max (p.N : ℝ)
          (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
      LpPowerBoundedBefore intervalDomain pExp T u →
        ∃ q R, 0 < q ∧ 0 ≤ R ∧
          IntervalDomainMoserPointwisePowerControlBefore u T q R

namespace
    IntervalDomainMassLpSmoothingMoserActualLinearSmallPDEAtomResiduals

/-- Produce the integrated-step route from the PDE-facing energy atoms. -/
def to_integratedStepResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallPDEAtomResiduals p)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀) :
    IntervalDomainMassLpSmoothingIntegratedStepResiduals p where
  a_pos := ha
  chi_nonneg := le_of_lt hχ0
  boundednessHyp := h.boundednessCore.to_boundednessHyp hb
  l2SeedRegularity := by
    intro _u₀ _hu₀ T hT u v hsol _htrace
    let hend := h.l2SeedEndpoint hsol
    exact
      intervalDomainL2SeedRegularityFrontier_of_classical_and_endpointContinuity
        hT hsol hend.endpointEnergy hend.zeroRightDerivative
  integratedStep := by
    intro T rho p0 u v hsol hcross hboot
    let hreg := h.classicalRegularity hsol hcross hboot
    let hrel := h.relativeMoserInterpolation hsol hcross hboot
    have hdiss :
        IntegratedMoserDissipationDropBefore intervalDomain u T rho p0 :=
      intervalDomain_integratedMoserDissipationDropBefore_of_globalPDE_v2
        hsol hcross hboot (h.energyWindowFTC hsol hcross hboot)
        hrel hreg (h.energyWithGap hsol hcross hboot)
    exact
      intervalDomain_firstCrossingStep_of_classicalRegularityData_integratedData
        hreg hsol hdiss hrel
        (AbstractLpBootstrapHypothesis.rho_pos hboot)
        (p0_nonneg_of_abstractLpBootstrapHypothesis hboot)
  quantitativeEndpoint := by
    intro u₀ hu₀ T hT u v hsol htrace pExp hpExp hLp
    exact
      intervalDomainMoserQuantitativeEndpoint_of_terminalPointwisePowerControl
        h.terminalPointwise hu₀ hT hsol htrace pExp hpExp hLp

/-- Produce the exact a-priori route consumed by continuation. -/
def to_routeResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallPDEAtomResiduals p)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀) :
    IntervalDomainMassLpSmoothingRouteResiduals p :=
  (h.to_integratedStepResiduals ha hb hχ0).to_routeResiduals

end
    IntervalDomainMassLpSmoothingMoserActualLinearSmallPDEAtomResiduals

/-- Sectorial mainline facts at the PDE-atom Moser interface. -/
structure IntervalDomainSectorialMainlineMoserActualLinearSmallPDEAtomFacts
    (p : CM2Params) : Prop where
  spectralSemigroupOrbitBound :
    IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p
  continuation : IntervalDomainStandardContinuationGluingData p
  massLpSmoothing :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallPDEAtomResiduals p

namespace IntervalDomainSectorialMainlineMoserActualLinearSmallPDEAtomFacts

def to_aprioriActualLinearSmallFacts
    {p : CM2Params}
    (h : IntervalDomainSectorialMainlineMoserActualLinearSmallPDEAtomFacts p)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀) :
    IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts p where
  spectralSemigroupOrbitBound := h.spectralSemigroupOrbitBound
  continuation := h.continuation
  massLpSmoothing := h.massLpSmoothing.to_routeResiduals ha hb hχ0

end IntervalDomainSectorialMainlineMoserActualLinearSmallPDEAtomFacts

/-- Paper3 mainline data with consumer-shaped Moser bundles eliminated. -/
structure
    IntervalDomainPaper3MainlineMoserActualLinearSmallPDEAtomThinFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop) : Prop where
  core : IntervalDomainSectorialMainlineMoserActualLinearSmallPDEAtomFacts p
  initialContinuity : IntervalDomainInitialContinuityRaw p
  compactness :
    IntervalDomainPaper3SupNormCompactnessAPosData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound
  stability24 :
    IntervalDomainPaper3Stability24ActualLinearFrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Assemble the mainline from genuine PDE atoms rather than Moser conclusion
bundles. -/
theorem intervalDomain_paper3_mainlineTargets_of_PDEAtomThinData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3MainlineMoserActualLinearSmallPDEAtomThinFrontierData
        p M0 uBar vLower locallyConverges neumannResolventGradientBound) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  intervalDomain_paper3_mainlineTargets_of_aprioriActualLinearSmallFrontierData
    p M0 uBar vLower
    (intervalDomainSupNormCompactnessData
      locallyConverges neumannResolventGradientBound)
    ha hb hχ0 hm hβ hχ
    { core := hData.core.to_aprioriActualLinearSmallFacts ha hb hχ0
      compactness :=
        (hData.compactness.toSupNormData ha hData.initialContinuity).toConcrete
      stability := hData.stability24.toStability23To25 ha hχ0 }

/-- Full Paper3 headline data at the PDE-atom interface, with Paper2 supplying
Propositions 1.3 and 1.4. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallPDEAtomThinP2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop) : Prop where
  paper2Main : IntervalDomainPaper2MainTheoremTargets p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallPDEAtomThinFrontierData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound

/-- Full Paper3 statement target from the PDE-atom headline. -/
theorem intervalDomain_paper3_statementTargets_of_PDEAtomThinP2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallPDEAtomThinP2MainNoNegData
        p C M0 uBar vLower locallyConverges
          neumannResolventGradientBound) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  { left :=
      intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsData
        p C
        { negativeBound :=
            intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos
              p hχ0
          paper2Main := hData.paper2Main }
    right :=
      intervalDomain_paper3_mainlineTargets_of_PDEAtomThinData
        p M0 uBar vLower locallyConverges neumannResolventGradientBound
        ha hb hχ0 hm hβ hχ hData.mainline }

#print axioms
  IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerUpperL2SeedResiduals.to_routeResiduals
#print axioms
  intervalDomain_paper3_mainlineTargets_of_lowerUpperL2SeedThinData
#print axioms
  intervalDomain_paper3_statementTargets_of_lowerUpperL2SeedThinP2MainNoNegData
#print axioms
  IntervalDomainMassLpSmoothingMoserActualLinearSmallPDEAtomResiduals.to_routeResiduals
#print axioms intervalDomain_paper3_mainlineTargets_of_PDEAtomThinData
#print axioms
  intervalDomain_paper3_statementTargets_of_PDEAtomThinP2MainNoNegData

end

end ShenWork.Paper3
