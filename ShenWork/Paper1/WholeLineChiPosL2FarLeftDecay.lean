import ShenWork.Paper1.WholeLineAbstractEnergyDecay
import ShenWork.Paper1.WholeLineChiPosL2DeficitEnergy

/-!
# Abstract far-left L² decay after edge absorption

This module is the scalar-decay bridge for the localized deficit energy.
For `0 < χ < 4`, Step 2 gives

`E' ≤ -2 γ(χ) E + edge`, where `γ(χ) = 2√χ - χ`.

The shallow-regime input is the precise absorption estimate
`edge ≤ γ(χ) E`.  The resulting inequality
`E' ≤ -γ(χ) E` fits `WholeLineAbstractEnergyDecay` with decay parameter
`γ(χ) / 2`.  Its landed capstone then gives both decay of the energy and
decay of the weighted physical `L²` deficit.

No PDE estimate is hidden here: the edge absorption is an explicit field
that later gluing must discharge.
-/

open Filter MeasureTheory Topology

noncomputable section

namespace ShenWork.Paper1

/-- The squared physical `L²` mass of a localized Schwartz deficit. -/
def farLeftL2DeficitMass
    (p : SchwartzMap ℝ ℂ) : ℝ :=
  ∫ x : ℝ, ‖p x‖ ^ 2

/-- The weighted squared deficit mass associated with `f = ηp`. -/
def farLeftWeightedL2Deficit
    (eta : ℝ → ℝ) (p : ℝ → ℂ) : ℝ :=
  ∫ x : ℝ, eta x ^ 2 * ‖p x‖ ^ 2

/-- A localized deficit evolution whose complete edge production has been
absorbed by one copy of the sharp spectral gap. -/
structure FarLeftL2AbsorbedEvolution (chi c : ℝ) where
  evolution : FarLeftL2DeficitEvolution
  hchi : 0 < chi
  hchi4 : chi < 4
  edge_absorbed : ∀ t : ℝ,
    farLeftL2EdgeProduction chi c
        (evolution.profile t) (evolution.velocity t) ≤
      farLeftL2Gap chi *
        farLeftL2DeficitEnergy (evolution.profile t)

namespace FarLeftL2AbsorbedEvolution

variable {chi c : ℝ} (H : FarLeftL2AbsorbedEvolution chi c)

/-- The absorbed localized evolution as the landed scalar energy-decay
structure, with `lam = γ(χ)/2`. -/
def toAbstractEnergyDecay : ShenWork.Paper1.AbstractEnergyDecay where
  E := fun t => farLeftL2DeficitEnergy (H.evolution.profile t)
  D := fun t =>
    farLeftL2DeficitProduction
      (H.evolution.profile t) (H.evolution.velocity t)
  lam := farLeftL2Gap chi / 2
  hlam := by
    exact half_pos
      (ShenWork.Paper1.farLeftL2Gap_pos H.hchi H.hchi4)
  E_nonneg := fun t =>
    ShenWork.Paper1.farLeftL2DeficitEnergy_nonneg
      (H.evolution.profile t)
  E_deriv := fun t =>
    H.evolution.energy_hasDerivAt t
  coercive := fun t => by
    have hdiss :=
      H.evolution.energy_dissipation_le H.hchi H.hchi4 c t
    have hedge := H.edge_absorbed t
    nlinarith

/-- Exponential estimate for the localized deficit energy. -/
theorem energy_le (t : ℝ) (ht : 0 ≤ t) :
    farLeftL2DeficitEnergy (H.evolution.profile t) ≤
      farLeftL2DeficitEnergy (H.evolution.profile 0) *
        Real.exp (-farLeftL2Gap chi * t) := by
  have h :=
    ShenWork.Paper1.AbstractEnergyDecay.energy_le
      H.toAbstractEnergyDecay t ht
  change
    farLeftL2DeficitEnergy (H.evolution.profile t) ≤
      farLeftL2DeficitEnergy (H.evolution.profile 0) *
        Real.exp (-2 * (farLeftL2Gap chi / 2) * t) at h
  have hexponent :
      -2 * (farLeftL2Gap chi / 2) * t =
        -farLeftL2Gap chi * t := by
    ring
  rwa [hexponent] at h

/-- The absorbed localized deficit energy tends to zero. -/
theorem energy_tendsto_zero :
    Tendsto
      (fun t => farLeftL2DeficitEnergy (H.evolution.profile t))
      atTop (𝓝 0) := by
  exact ShenWork.Paper1.AbstractEnergyDecay.decay_to_zero
    H.toAbstractEnergyDecay

/-- The physical squared `L²` mass of the localized deficit tends to zero. -/
theorem deficitMass_tendsto_zero :
    Tendsto
      (fun t => farLeftL2DeficitMass (H.evolution.profile t))
      atTop (𝓝 0) := by
  have hE := H.energy_tendsto_zero
  have hscaled :
      Tendsto
        (fun t =>
          (2 : ℝ) *
            farLeftL2DeficitEnergy (H.evolution.profile t))
        atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hE)
  convert hscaled using 1
  · funext t
    rw [farLeftL2DeficitEnergy_eq_half_norm_sq,
      schwartz_norm_toLp_two_sq]
    unfold farLeftL2DeficitMass
    ring

/-- If the Schwartz profile is the cutoff deficit `ηp`, then the corresponding
weighted far-left `L²` deficit tends to zero. -/
theorem weightedDeficit_tendsto_zero
    (eta : ℝ → ℝ) (p : ℝ → ℝ → ℂ)
    (hlocalized : ∀ t x : ℝ,
      H.evolution.profile t x = (eta x : ℂ) * p t x) :
    Tendsto
      (fun t => farLeftWeightedL2Deficit eta (p t))
      atTop (𝓝 0) := by
  have hE := H.energy_tendsto_zero
  have hscaled :
      Tendsto
        (fun t =>
          (2 : ℝ) *
            farLeftL2DeficitEnergy (H.evolution.profile t))
        atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hE)
  convert hscaled using 1
  · funext t
    have hweight :=
      farLeftL2DeficitEnergy_eq_weighted
        (H.evolution.profile t) eta (p t) (hlocalized t)
    unfold farLeftWeightedL2Deficit
    nlinarith

end FarLeftL2AbsorbedEvolution

section AxiomAudit

#print axioms FarLeftL2AbsorbedEvolution.toAbstractEnergyDecay
#print axioms FarLeftL2AbsorbedEvolution.energy_le
#print axioms FarLeftL2AbsorbedEvolution.energy_tendsto_zero
#print axioms FarLeftL2AbsorbedEvolution.deficitMass_tendsto_zero
#print axioms FarLeftL2AbsorbedEvolution.weightedDeficit_tendsto_zero

end AxiomAudit

end ShenWork.Paper1
