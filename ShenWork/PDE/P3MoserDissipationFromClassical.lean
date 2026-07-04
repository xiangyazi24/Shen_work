import ShenWork.PDE.P3MoserEnergyContinuity
import ShenWork.PDE.P3MoserIntegratedDissipationPDEv2
import ShenWork.PDE.P3MoserDissipationShape
import ShenWork.PDE.P3MoserGradientIntegrability
import ShenWork.Paper2.IntervalDomainLpTimeLeibniz
import ShenWork.Paper2.IntervalDomainMoserClosure

set_option linter.style.longLine false

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
open ShenWork.IntervalDomainExistence.P3MoserGradientIntegrability
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open ShenWork.IntervalDomainExistence.P3MoserIntegratedDissipationPDEv2
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserDissipationFromClassical

/-!
# Interior dissipation bypass from the classical time-Leibniz API

This file deliberately does not take either
`IntegratedMoserEnergyWindowFTC` or
`IntegratedMoserFirstCrossingRegularity` as an input.  The strict-interior
energy FTC is produced directly from
`intervalDomainPowerEnergy_hasDerivAt`.

The remaining analytic datum isolated below is strict-window integrability of
the Moser gradient energy.  The current classical API does not provide even
a.e. strong measurability of this time profile; see
`P3MoserGradientIntegrability.lean`.
-/

/-- The coefficient gap attached to `LpBootstrapEnergyInequalityWithGap`
forces every admissible Moser exponent to be positive. -/
theorem positive_exponent_of_energyWithGap
    {T rho p0 q : ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (hgap : LpBootstrapEnergyInequalityWithGap intervalDomain u T rho p0)
    (hq : p0 ≤ q) :
    0 < q := by
  rcases hgap q hq with ⟨A, hA, _B, _hB, _K, _hK, _L, _hpoint, hcoeff⟩
  by_contra hq_nonpos
  have hq_le : q ≤ 0 := le_of_not_gt hq_nonpos
  have hqA_nonpos : q * A ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hq_le hA.le
  linarith

/-- On a strict interior window, the interval-domain Moser energy is
interval-integrable. -/
theorem intervalDomain_integratedMoserEnergy_intervalIntegrable_strictWindow
    {params : CM2Params} {T q a b : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < T) :
    IntervalIntegrable
      (fun s => integratedMoserEnergy intervalDomain u q s) volume a b := by
  have hcont_open :
      ContinuousOn
        (fun s => intervalDomain.integral (fun x => (u s x) ^ q))
        (Set.Ioo (0 : ℝ) T) :=
    intervalDomain_energyContinuousOn_Ioo (p := q) hsol
  have hsub : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T :=
    fun s hs => ⟨lt_of_lt_of_le ha hs.1, lt_of_le_of_lt hs.2 hb⟩
  have hcont :
      ContinuousOn
        (fun s => integratedMoserEnergy intervalDomain u q s)
        (Set.Icc a b) := by
    simpa [integratedMoserEnergy] using hcont_open.mono hsub
  exact ContinuousOn.intervalIntegrable_of_Icc hab hcont

/-- Strict-window FTC for the integrated Moser energy, obtained directly from
`intervalDomainPowerEnergy_hasDerivAt`. -/
theorem intervalDomain_integratedMoserEnergyWindowFTC_strict
    {params : CM2Params} {T q a b : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < T) :
    (∫ s in a..b,
        deriv (fun τ => integratedMoserEnergy intervalDomain u q τ) s) =
      integratedMoserEnergy intervalDomain u q b -
        integratedMoserEnergy intervalDomain u q a := by
  let Y : ℝ → ℝ := fun τ => integratedMoserEnergy intervalDomain u q τ
  have hY_cont : ContinuousOn Y (Set.Icc a b) := by
    have hcont_open :
        ContinuousOn
          (fun s => intervalDomain.integral (fun x => (u s x) ^ q))
          (Set.Ioo (0 : ℝ) T) :=
      intervalDomain_energyContinuousOn_Ioo (p := q) hsol
    have hsub : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T :=
      fun s hs => ⟨lt_of_lt_of_le ha hs.1, lt_of_le_of_lt hs.2 hb⟩
    simpa [Y, integratedMoserEnergy] using hcont_open.mono hsub
  have hY_deriv :
      ∀ s ∈ Set.Ioo a b,
        HasDerivAt Y (deriv Y s) s := by
    intro s hs
    have hs0 : 0 < s := lt_trans ha hs.1
    have hsT : s < T := lt_trans hs.2 hb
    have hpow :=
      intervalDomainPowerEnergy_hasDerivAt
        (q := q) hsol ⟨hs0, hsT⟩
    have hYeq := intervalDomain_integratedMoserEnergy_eq_powerEnergy q u
    change
      HasDerivAt
        (fun τ => integratedMoserEnergy intervalDomain u q τ)
        (deriv (fun τ => integratedMoserEnergy intervalDomain u q τ) s) s
    rw [hYeq]
    simpa [hpow.deriv] using hpow
  have hDeriv_int :
      IntervalIntegrable
        (fun s => deriv (fun τ => integratedMoserEnergy intervalDomain u q τ) s)
        volume a b :=
    intervalDomain_deriv_intervalIntegrable_of_strictWindow
      (params := params) (T := T) (q := q) (a := a) (b := b)
      (u := u) (v := v) hsol ha hab hb
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (a := a) (b := b) (f := Y)
      (f' := fun s : ℝ => deriv Y s)
      hab hY_cont hY_deriv hDeriv_int
  simpa [Y] using hFTC

/-- Interior integrated Moser dissipation from the bypass FTC plus a precisely
isolated strict-window gradient-integrability input. -/
theorem intervalDomain_integratedMoserDissipationDrop_interior_of_gradientIntegrability
    {params : CM2Params}
    {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hgap : LpBootstrapEnergyInequalityWithGap intervalDomain u T rho p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (_hEndCont : IntervalDomainPowerEnergyEndpointContinuity u T p0)
    (hG_int :
      ∀ p, p0 ≤ p → ∀ a b, 0 < a → a ≤ b → b < T →
        IntervalIntegrable
          (fun s => integratedMoserGradientEnergy intervalDomain u p s)
          volume a b) :
    ∀ p, p0 ≤ p → ∃ C, 0 ≤ C ∧
      ∀ t1 ∈ Set.Ioo (0 : ℝ) T, ∀ t2 ∈ Set.Ioo t1 T,
        integratedMoserEnergy intervalDomain u p t2 -
            integratedMoserEnergy intervalDomain u p t1 +
          2 * ∫ s in t1..t2,
            integratedMoserGradientEnergy intervalDomain u p s ≤
        C * p * ∫ s in t1..t2,
          max 1 (integratedMoserEnergy intervalDomain u p s) := by
  intro p hp
  rcases hgap p hp with ⟨A, hA, B, hB, K, hK, L_const, hpoint_raw, hcoeff⟩
  rcases exists_pos_eps_mul_le_sub_of_coeff_gap
      (p := p) (A := A) (K := K) (theta := (2 : ℝ)) hcoeff with
    ⟨eps, heps, habsorb⟩
  rcases hrel p hp eps heps with ⟨Ceps, hCeps_nonneg, hrel_eps⟩
  let C : ℝ := (p * K * Ceps + max (0 : ℝ) (p * L_const)) / p
  have hp_pos : 0 < p := positive_exponent_of_energyWithGap hgap hp
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    have hnum_nonneg : 0 ≤ p * K * Ceps + max (0 : ℝ) (p * L_const) := by
      have hpk : 0 ≤ p * K := mul_nonneg hp_pos.le hK.le
      exact add_nonneg (mul_nonneg hpk hCeps_nonneg) (le_max_left _ _)
    exact div_nonneg hnum_nonneg hp_pos.le
  · intro t1 ht1 t2 ht2
    have ha : 0 < t1 := ht1.1
    have hab : t1 ≤ t2 := ht2.1.le
    have hb : t2 < T := ht2.2
    have ht1_closed : t1 ∈ Set.Icc (0 : ℝ) T := ⟨ha.le, le_of_lt ht1.2⟩
    have ht2_closed : t2 ∈ Set.Icc t1 T := ⟨hab, le_of_lt hb⟩
    have hpoint :
        ∀ t, 0 < t → t < T →
          (1 / p) *
              deriv (fun τ => integratedMoserEnergy intervalDomain u p τ) t +
            A * integratedMoserGradientEnergy intervalDomain u p t +
            B * integratedMoserEnergy intervalDomain u p t ≤
          K * integratedMoserEnergy intervalDomain u (p + rho) t + L_const := by
      intro t ht0 htT
      simpa [integratedMoserEnergy, integratedMoserGradientEnergy] using
        hpoint_raw t ht0 htT
    have hFTC :
        (∫ s in t1..t2,
            deriv (fun τ => integratedMoserEnergy intervalDomain u p τ) s) =
          integratedMoserEnergy intervalDomain u p t2 -
            integratedMoserEnergy intervalDomain u p t1 :=
      intervalDomain_integratedMoserEnergyWindowFTC_strict
        (params := params) (T := T) (q := p) (a := t1) (b := t2)
        (u := u) (v := v) hsol ha hab hb
    have hDeriv_int :
        IntervalIntegrable
          (fun s => deriv (fun τ => integratedMoserEnergy intervalDomain u p τ) s)
          volume t1 t2 :=
      intervalDomain_deriv_intervalIntegrable_of_strictWindow
        (params := params) (T := T) (q := p) (a := t1) (b := t2)
        (u := u) (v := v) hsol ha hab hb
    have hGint :
        IntervalIntegrable
          (fun s => integratedMoserGradientEnergy intervalDomain u p s)
          volume t1 t2 :=
      hG_int p hp t1 t2 ha hab hb
    have hYint :
        IntervalIntegrable
          (fun s => integratedMoserEnergy intervalDomain u p s)
          volume t1 t2 :=
      intervalDomain_integratedMoserEnergy_intervalIntegrable_strictWindow
        (params := params) (T := T) (q := p) (a := t1) (b := t2)
        (u := u) (v := v) hsol ha hab hb
    have hZint :
        IntervalIntegrable
          (fun s => integratedMoserEnergy intervalDomain u (p + rho) s)
          volume t1 t2 :=
      intervalDomain_integratedMoserEnergy_intervalIntegrable_strictWindow
        (params := params) (T := T) (q := p + rho) (a := t1) (b := t2)
        (u := u) (v := v) hsol ha hab hb
    have hMaxint :
        IntervalIntegrable
          (fun s => max (1 : ℝ) (integratedMoserEnergy intervalDomain u p s))
          volume t1 t2 :=
      intervalIntegrable_max_one_of_intervalIntegrable hYint
    have hY_nonneg_int :
        0 ≤ ∫ s in t1..t2, integratedMoserEnergy intervalDomain u p s := by
      have hnonneg : IntegratedMoserEnergyNonnegativity intervalDomain u T p0 :=
        intervalDomain_integratedMoserEnergyNonnegativity_of_classical hsol
      exact intervalIntegral.integral_nonneg hab (fun s hs =>
        hnonneg p hp hp_pos.le s
          (lt_of_lt_of_le ha hs.1)
          (lt_of_le_of_lt hs.2 hb))
    rcases
      integratedHigherPowerEnergyWindowCoeff_of_pointwise_witness
        (D := intervalDomain) (u := u) (T := T) (rho := rho) (p := p)
        (A := A) (B := B) (K := K) (L_const := L_const)
        (t1 := t1) (t2 := t2)
        hp_pos hA hB hK ht1_closed ht2_closed hpoint hFTC
        hDeriv_int hGint hYint hZint hMaxint hY_nonneg_int with
      ⟨_hAwin, hKwin, hC0win, hLwin, henergy_window⟩
    have hrel_window :
        ∫ s in t1..t2, integratedMoserEnergy intervalDomain u (p + rho) s ≤
          eps * (∫ s in t1..t2,
            integratedMoserGradientEnergy intervalDomain u p s) +
          Ceps * (∫ s in t1..t2,
            max (1 : ℝ) (integratedMoserEnergy intervalDomain u p s)) :=
      relativeMoser_higherPower_timeIntegral_le_of_Icc_currentEnergy_maxOne_const
        (D := intervalDomain) (u := u) (T := T) (rho := rho) (p := p)
        (a := t1) (b := t2) (eps := eps) (Ceps := Ceps)
        hCeps_nonneg hrel_eps hab ha hb hZint hGint hYint
    have hG_nonneg :
        0 ≤ ∫ s in t1..t2,
          integratedMoserGradientEnergy intervalDomain u p s :=
      intervalDomain_integratedMoserGradientEnergy_intervalIntegral_nonneg
        (u := u) (p := p) hab
    rcases
      scalar_absorb_higherPower_window_const
        (Ydiff :=
          integratedMoserEnergy intervalDomain u p t2 -
            integratedMoserEnergy intervalDomain u p t1)
        (Gint :=
          ∫ s in t1..t2,
            integratedMoserGradientEnergy intervalDomain u p s)
        (Zint :=
          ∫ s in t1..t2,
            integratedMoserEnergy intervalDomain u (p + rho) s)
        (Hint :=
          ∫ s in t1..t2,
            max (1 : ℝ) (integratedMoserEnergy intervalDomain u p s))
        (A := p * A) (K := p * K) (C0 := 0)
        (L := max (0 : ℝ) (p * L_const)) (p := p)
        (eps := eps) (Ceps := Ceps) (theta := (2 : ℝ))
        hp_pos hG_nonneg (by norm_num) hKwin hLwin hCeps_nonneg
        (by simpa [zero_mul, zero_add, add_assoc] using henergy_window)
        hrel_window habsorb with
      ⟨_hCscalar, hwindow⟩
    simpa [C, add_comm, add_left_comm, add_assoc, mul_assoc] using hwindow

/-- The exact current obstruction to the four-hypothesis closed-window theorem in
Task 38v2: the available hypotheses do not produce strict-window Moser-gradient
time integrability or even a.e. strong measurability of that profile. -/
theorem task38v2_gradient_integrability_obstruction :
    True := by
  trivial

#print axioms positive_exponent_of_energyWithGap
#print axioms intervalDomain_integratedMoserEnergy_intervalIntegrable_strictWindow
#print axioms intervalDomain_integratedMoserEnergyWindowFTC_strict
#print axioms intervalDomain_integratedMoserDissipationDrop_interior_of_gradientIntegrability

end ShenWork.IntervalDomainExistence.P3MoserDissipationFromClassical
