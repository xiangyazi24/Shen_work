import ShenWork.Paper1.WholeLineChiPosWeightedEntropyProducer
import ShenWork.Paper1.WholeLineAbstractEnergyDecay
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Sub-Turing whole-line entropy Liouville theorem

The fixed-time weighted entropy estimate has a stronger consequence than a
small-plateau basin argument.  An entire co-moving orbit with a uniform
positive floor and a bounded range must be the equilibrium.

Indeed, if `mu = 1 - chiOneWeightedEntropyLoss chi c ell k > 0`, then

`E' <= -mu W <= -mu*ell E`.

Starting this estimate at time `t-T` gives

`E(t) <= E(t-T) exp (-mu*ell*T)`.

The bounded range makes `E(t-T)` uniformly bounded, so `T -> infinity` forces
`E(t)=0`.  The dissipation inequality then gives `W(t)=0`, and continuity plus
strict positivity of the localization weight yields `u(t,x)=1` everywhere.

This is the Liouville closure required by a far-left translate-compactness
argument.  The remaining bridge to the canonical orbit is now isolated to
producing the time-Leibniz field and the fixed-time IBP data for the translated
entire limit; no small nonlinear remainder or Bernstein estimate is needed in
the normalized case.
-/

open Filter MeasureTheory Real Set Topology

noncomputable section

namespace ShenWork.Paper1

def chiOneWeightedEntropyEnergy
    (k x₀ : ℝ) (u : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℝ,
    localizingWeightAt k x₀ x * chiOneRelativeEntropy (u t x)

/-- An entire co-moving orbit carrying exactly the analytic data consumed by
the entropy Liouville argument.  `band` is inherited by a far-left compactness
limit from the global `L∞` ceiling; it is used only to bound the entropy at
time `t-T`. -/
structure ChiOneEntireWeightedEntropyData
    (chi c ell k x₀ : ℝ)
    (u ux uxx ut r rx rxx : ℝ → ℝ → ℝ) : Prop where
  hkpos : 0 < k
  slice : ∀ t : ℝ,
    ChiOneWeightedEntropyData chi c ell k x₀
      (u t) (ux t) (uxx t) (ut t) (r t) (rx t) (rxx t)
  entropy_integrable : ∀ t : ℝ, Integrable
    (fun x : ℝ =>
      localizingWeightAt k x₀ x * chiOneRelativeEntropy (u t x))
  entropy_deriv : ∀ t : ℝ,
    HasDerivAt (chiOneWeightedEntropyEnergy k x₀ u)
      (chiOneWeightedEntropyProduction k x₀ (u t) (ut t)) t
  u_continuous : ∀ t : ℝ, Continuous (u t)
  band : ∃ B : ℝ, 0 ≤ B ∧ ∀ t x : ℝ, |u t x - 1| ≤ B

namespace ChiOneEntireWeightedEntropyData

variable {chi c ell k x₀ : ℝ}
    {u ux uxx ut r rx rxx : ℝ → ℝ → ℝ}
    (H : ChiOneEntireWeightedEntropyData chi c ell k x₀
      u ux uxx ut r rx rxx)

include H

theorem energy_nonneg (t : ℝ) :
    0 ≤ chiOneWeightedEntropyEnergy k x₀ u t := by
  unfold chiOneWeightedEntropyEnergy
  exact integral_nonneg fun x =>
    mul_nonneg (localizingWeightAt_pos k x₀ x).le
      (chiOneRelativeEntropy_nonneg ((H.slice t).u_pos x))

/-- Relative entropy is controlled by the displacement energy using only the
uniform positive floor. -/
theorem ell_mul_energy_le_displacement (t : ℝ) :
    ell * chiOneWeightedEntropyEnergy k x₀ u t ≤
      chiOneWeightedSourceSquare k x₀ (fun x => u t x - 1) := by
  unfold chiOneWeightedEntropyEnergy chiOneWeightedSourceSquare
  rw [← integral_const_mul]
  apply integral_mono
    ((H.entropy_integrable t).const_mul ell)
    (H.slice t).toChiOneWeightedResolverData.sourceSquare_integrable
  intro x
  have hent := chiOneRelativeEntropy_le_sq_div
    (H.slice t).hell ((H.slice t).u_floor x)
  have hphi : 0 ≤ localizingWeightAt k x₀ x :=
    (localizingWeightAt_pos k x₀ x).le
  have hell := (H.slice t).hell
  have hscaled := mul_le_mul_of_nonneg_left hent
    (mul_nonneg hell.le hphi)
  field_simp [hell.ne'] at hscaled
  nlinarith

/-- The bounded range and the integrable localization weight give a uniform
entropy bound on the entire orbit. -/
theorem exists_uniform_energy_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ,
      chiOneWeightedEntropyEnergy k x₀ u t ≤ K := by
  obtain ⟨B, hB, hband⟩ := H.band
  let K : ℝ := (B ^ 2 / ell) * (2 / k)
  have hK : 0 ≤ K := by
    dsimp [K]
    have hell := (H.slice 0).hell
    exact mul_nonneg
      (div_nonneg (sq_nonneg B) hell.le)
      (div_nonneg (by norm_num) H.hkpos.le)
  refine ⟨K, hK, fun t => ?_⟩
  have hmajorInt : Integrable (fun x : ℝ =>
      (B ^ 2 / ell) * localizingWeightAt k x₀ x) :=
    (localizingWeightAt_integrable H.hkpos x₀).const_mul _
  have hpoint : ∀ x : ℝ,
      localizingWeightAt k x₀ x * chiOneRelativeEntropy (u t x) ≤
        (B ^ 2 / ell) * localizingWeightAt k x₀ x := by
    intro x
    have hent := chiOneRelativeEntropy_le_sq_div
      (H.slice t).hell ((H.slice t).u_floor x)
    have hwabs := hband t x
    have hw2 : (u t x - 1) ^ 2 ≤ B ^ 2 := by
      have hprod : 0 ≤ (B - |u t x - 1|) * (B + |u t x - 1|) :=
        mul_nonneg (sub_nonneg.mpr hwabs)
          (add_nonneg hB (abs_nonneg _))
      nlinarith [sq_abs (u t x - 1)]
    have hell := (H.slice t).hell
    have hquot : (u t x - 1) ^ 2 / ell ≤ B ^ 2 / ell :=
      div_le_div_of_nonneg_right hw2 hell.le
    have hphi : 0 ≤ localizingWeightAt k x₀ x :=
      (localizingWeightAt_pos k x₀ x).le
    calc
      localizingWeightAt k x₀ x * chiOneRelativeEntropy (u t x) ≤
          localizingWeightAt k x₀ x * ((u t x - 1) ^ 2 / ell) :=
        mul_le_mul_of_nonneg_left hent hphi
      _ ≤ localizingWeightAt k x₀ x * (B ^ 2 / ell) :=
        mul_le_mul_of_nonneg_left hquot hphi
      _ = (B ^ 2 / ell) * localizingWeightAt k x₀ x := by ring
  have hint :
      chiOneWeightedEntropyEnergy k x₀ u t ≤
        (B ^ 2 / ell) *
          (∫ x : ℝ, localizingWeightAt k x₀ x) := by
    unfold chiOneWeightedEntropyEnergy
    calc
      (∫ x : ℝ,
          localizingWeightAt k x₀ x * chiOneRelativeEntropy (u t x)) ≤
          ∫ x : ℝ, (B ^ 2 / ell) * localizingWeightAt k x₀ x :=
        integral_mono (H.entropy_integrable t) hmajorInt hpoint
      _ = (B ^ 2 / ell) *
          (∫ x : ℝ, localizingWeightAt k x₀ x) := by
        rw [integral_const_mul]
  exact hint.trans <| by
    dsimp [K]
    exact mul_le_mul_of_nonneg_left
      (integral_localizingWeightAt_le_two_div H.hkpos x₀)
      (div_nonneg (sq_nonneg B) (H.slice t).hell.le)

theorem production_coercive
    (hloss : chiOneWeightedEntropyLoss chi c ell k < 1) (t : ℝ) :
    chiOneWeightedEntropyProduction k x₀ (u t) (ut t) ≤
      -(1 - chiOneWeightedEntropyLoss chi c ell k) * ell *
        chiOneWeightedEntropyEnergy k x₀ u t := by
  have hdiss := (H.slice t).entropy_decay
  have hEW := H.ell_mul_energy_le_displacement t
  have hmu : 0 < 1 - chiOneWeightedEntropyLoss chi c ell k :=
    sub_pos.mpr hloss
  have hscaled := mul_le_mul_of_nonpos_left hEW (neg_nonpos.mpr hmu.le)
  nlinarith

/-- Time translation turns the entire orbit into an `AbstractEnergyDecay`
starting at time zero. -/
def shiftedDecay
    (hloss : chiOneWeightedEntropyLoss chi c ell k < 1) (s : ℝ) :
    AbstractEnergyDecay where
  E := fun tau => chiOneWeightedEntropyEnergy k x₀ u (s + tau)
  D := fun tau =>
    chiOneWeightedEntropyProduction k x₀ (u (s + tau)) (ut (s + tau))
  lam := ((1 - chiOneWeightedEntropyLoss chi c ell k) * ell) / 2
  hlam := by
    have hmu : 0 < 1 - chiOneWeightedEntropyLoss chi c ell k :=
      sub_pos.mpr hloss
    have hell := (H.slice 0).hell
    positivity
  E_nonneg := fun tau => H.energy_nonneg (s + tau)
  E_deriv := fun tau => by
    have hshift : HasDerivAt (fun q : ℝ => s + q) 1 tau :=
      (hasDerivAt_id tau).const_add s
    have hcomp := (H.entropy_deriv (s + tau)).comp tau hshift
    simpa only [Function.comp_apply, mul_one] using hcomp
  coercive := fun tau => by
    have h := H.production_coercive hloss (s + tau)
    convert h using 1 <;> ring

/-- The entropy of an entire bounded orbit vanishes at every time. -/
theorem energy_eq_zero
    (hloss : chiOneWeightedEntropyLoss chi c ell k < 1) (t : ℝ) :
    chiOneWeightedEntropyEnergy k x₀ u t = 0 := by
  obtain ⟨K, _hK, hbound⟩ := H.exists_uniform_energy_bound
  let rho : ℝ := (1 - chiOneWeightedEntropyLoss chi c ell k) * ell
  have hrho : 0 < rho := by
    dsimp [rho]
    exact mul_pos (sub_pos.mpr hloss) (H.slice 0).hell
  have hupper : ∀ T : ℝ, 0 ≤ T →
      chiOneWeightedEntropyEnergy k x₀ u t ≤
        K * Real.exp (-rho * T) := by
    intro T hT
    let A : AbstractEnergyDecay := H.shiftedDecay hloss (t - T)
    have hdec := A.energy_le T hT
    have hdec' :
        chiOneWeightedEntropyEnergy k x₀ u t ≤
          chiOneWeightedEntropyEnergy k x₀ u (t - T) *
            Real.exp (-rho * T) := by
      convert hdec using 1 <;> dsimp [A, shiftedDecay, rho] <;> ring
    exact hdec'.trans <| mul_le_mul_of_nonneg_right
      (hbound (t - T)) (Real.exp_pos _).le
  have hlin : Tendsto (fun T : ℝ => -rho * T) atTop atBot := by
    have htop : Tendsto (fun T : ℝ => rho * T) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hrho tendsto_id
    have hneg := tendsto_neg_atTop_atBot.comp htop
    simpa only [neg_mul] using hneg
  have hexp : Tendsto (fun T : ℝ => Real.exp (-rho * T)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hlin
  have hKexp : Tendsto (fun T : ℝ => K * Real.exp (-rho * T))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hexp)
  have hzero : Tendsto
      (fun _T : ℝ => chiOneWeightedEntropyEnergy k x₀ u t)
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hKexp ?_ ?_
    · exact Eventually.of_forall fun _T => H.energy_nonneg t
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      exact hupper T hT
  exact tendsto_nhds_unique tendsto_const_nhds hzero

theorem displacementSquare_eq_zero
    (hloss : chiOneWeightedEntropyLoss chi c ell k < 1) (t : ℝ) :
    chiOneWeightedSourceSquare k x₀ (fun x => u t x - 1) = 0 := by
  have hEfun : chiOneWeightedEntropyEnergy k x₀ u = fun _ : ℝ => 0 := by
    funext s
    exact H.energy_eq_zero hloss s
  have hzeroDeriv : HasDerivAt (chiOneWeightedEntropyEnergy k x₀ u) 0 t := by
    rw [hEfun]
    exact hasDerivAt_const t 0
  have hprod0 :
      chiOneWeightedEntropyProduction k x₀ (u t) (ut t) = 0 :=
    (H.entropy_deriv t).unique hzeroDeriv
  have hdiss := (H.slice t).entropy_decay
  have hW := (H.slice t).toChiOneWeightedResolverData.sourceSquare_nonneg
  have hmu : 0 < 1 - chiOneWeightedEntropyLoss chi c ell k :=
    sub_pos.mpr hloss
  nlinarith

/-- **Whole-line entropy Liouville theorem.** -/
theorem population_eq_one
    (hloss : chiOneWeightedEntropyLoss chi c ell k < 1) :
    ∀ t x : ℝ, u t x = 1 := by
  intro t
  have hW := H.displacementSquare_eq_zero hloss t
  have hint := (H.slice t).toChiOneWeightedResolverData.sourceSquare_integrable
  have hnonneg : 0 ≤ fun x : ℝ =>
      localizingWeightAt k x₀ x * (u t x - 1) ^ 2 := fun x =>
    mul_nonneg (localizingWeightAt_pos k x₀ x).le (sq_nonneg _)
  have hintegral :
      (∫ x : ℝ, localizingWeightAt k x₀ x * (u t x - 1) ^ 2) = 0 := by
    simpa [chiOneWeightedSourceSquare] using hW
  have hae :
      (fun x : ℝ => localizingWeightAt k x₀ x * (u t x - 1) ^ 2) =ᵐ[volume]
        0 :=
    (integral_eq_zero_iff_of_nonneg hnonneg hint).1 hintegral
  have hdens_cont : Continuous (fun x : ℝ =>
      localizingWeightAt k x₀ x * (u t x - 1) ^ 2) := by
    have hwcont : Continuous (fun x : ℝ => (u t x - 1) ^ 2) :=
      ((H.u_continuous t).sub continuous_const).pow 2
    exact continuous_localizingWeightAt.mul hwcont
  have hfun :
      (fun x : ℝ => localizingWeightAt k x₀ x * (u t x - 1) ^ 2) =
        fun _ : ℝ => 0 :=
    MeasureTheory.Measure.eq_of_ae_eq (μ := volume)
      hae hdens_cont continuous_const
  intro x
  have hx := congr_fun hfun x
  have hsquare : (u t x - 1) ^ 2 = 0 :=
    (mul_eq_zero.mp hx).resolve_left
      (ne_of_gt (localizingWeightAt_pos k x₀ x))
  nlinarith [sq_nonneg (u t x - 1)]

end ChiOneEntireWeightedEntropyData

/-- The Liouville conclusion is available for the entire sharp nonlinear
range `0 <= chi < 4`. -/
theorem exists_chiOne_entropyLiouvilleSlope_full_sharp_range
    {chi c ell : ℝ} (hchi : 0 ≤ chi) (hchi4 : chi < 4) (hell : 0 < ell) :
    ∃ k : ℝ, 0 < k ∧ k < 1 ∧
      ∀ (x₀ : ℝ) (u ux uxx ut r rx rxx : ℝ → ℝ → ℝ),
        ChiOneEntireWeightedEntropyData chi c ell k x₀
          u ux uxx ut r rx rxx →
        ∀ t x : ℝ, u t x = 1 := by
  obtain ⟨k, hkpos, hk1, hloss⟩ :=
    exists_chiOne_localizationSlope_full_sharp_range hchi hchi4 hell
  refine ⟨k, hkpos, hk1, ?_⟩
  intro x₀ u ux uxx ut r rx rxx H
  exact H.population_eq_one hloss

section AxiomAudit

#print axioms ChiOneEntireWeightedEntropyData.exists_uniform_energy_bound
#print axioms ChiOneEntireWeightedEntropyData.energy_eq_zero
#print axioms ChiOneEntireWeightedEntropyData.displacementSquare_eq_zero
#print axioms ChiOneEntireWeightedEntropyData.population_eq_one
#print axioms exists_chiOne_entropyLiouvilleSlope_full_sharp_range

end AxiomAudit

end ShenWork.Paper1
