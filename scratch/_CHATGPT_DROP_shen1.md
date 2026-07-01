# Q2856 (shen1) — next Lean layer: window FTC and higher-power energy windows

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Source edit requested: none; answer file only.

Do not edit `ShenWork/PDE/P3MoserHighExcursionProducer.lean`.

## Connector-visible grounding

The connector-visible branch still does not show the newest local coefficient/closed-relative names, but the relevant existing infrastructure is visible.

Names/files to grep:

```text
ShenWork/PDE/P3MoserIntegratedClosure.lean
  IntegratedMoserFirstCrossingRegularity
  integratedMoserEnergy
  integratedMoserGradientEnergy
  IntegratedMoserFirstCrossingRegularity.power_intervalIntegrable_of_Icc
  IntegratedMoserFirstCrossingRegularity.gradient_intervalIntegrable_of_Icc
  IntegratedMoserFirstCrossingRegularity.maxOneEnergy_intervalIntegrable_of_Icc
  Icc_subset_uIcc_zero_T_of_endpoint_memberships
  intervalDomain_integratedMoserGradientEnergy_intervalIntegral_nonneg
  intervalIntegrable_max_one_of_intervalIntegrable

ShenWork/Paper2/IntervalDomainLpTimeLeibniz.lean
  intervalDomainPowerEnergy
  intervalDomainPowerEnergy_hasDerivAt
  intervalDomain_lp_timeLeibniz
  intervalDomain_lp_timeLeibniz_intervalIntegral
  intervalDomainLpEnergy_eq_powerEnergy_of_pos

ShenWork/Paper2/IntervalDomainLpBootstrapEnergyInequality.lean
  intervalDomain_LpBootstrapEnergyInequality_of_regularity
  intervalDomainLpMoserGradientControl_of_regularity
  intervalDomainLpLowerOrderControl_of_regularity
  intervalDomain_moser_gradient_integral_eq_weighted_of_regularity
  intervalDomainLpEnergy_eq_power_of_regularity
  intervalDomainLpEnergy_eventuallyEq_power_of_regularity
```

The key point: the time-Leibniz file gives **pointwise HasDerivAt** for power energies at interior times; the closure file gives **integrability of `Y_p`, `G_p`, and `max(1,Y_p)`** on windows. What is not currently part of `IntegratedMoserFirstCrossingRegularity` is integrability of the **time derivative** `deriv (fun τ => integratedMoserEnergy D u p τ)` on windows. That must be a separate field unless already available locally.

## 1. Recommended `IntegratedMoserEnergyWindowFTC` layer

Do not make FTC only an equality. Make it a small structure carrying both derivative interval-integrability and the endpoint identity. The derivative integrability is needed again when integrating pointwise energy inequalities.

Place in `ShenWork/PDE/P3MoserIntegratedClosure.lean`.

```lean
import ShenWork.PDE.P3MoserIntegratedClosure

open MeasureTheory
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- Window fundamental theorem of calculus for the Moser energy profile
`Y_p(t) = integratedMoserEnergy D u p t`, including the derivative integrability
needed to integrate pointwise energy inequalities. -/
structure IntegratedMoserEnergyWindowFTC
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T p0 : ℝ) : Prop where
  deriv_intervalIntegrable :
    ∀ p, p0 ≤ p →
      ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        IntervalIntegrable
          (fun s => deriv (fun τ => integratedMoserEnergy D u p τ) s)
          volume t1 t2
  window_ftc :
    ∀ p, p0 ≤ p →
      ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        (∫ s in t1..t2,
          deriv (fun τ => integratedMoserEnergy D u p τ) s) =
        integratedMoserEnergy D u p t2 -
          integratedMoserEnergy D u p t1

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

### Why this is the right frontier shape

`IntegratedMoserFirstCrossingRegularity` currently has:

```lean
energyContinuous
initialPowerBound
powerTimeIntegrable
gradientTimeIntegrable
```

It does **not** say `Y_p` is absolutely continuous, nor that `deriv Y_p` is interval-integrable. So `IntegratedMoserEnergyWindowFTC` cannot honestly be derived from `IntegratedMoserFirstCrossingRegularity` alone.

## 1a. Interval-domain helper: identify Moser energy with `intervalDomainPowerEnergy`

This is pure definitional/lift wiring and should be easy.

```lean
import ShenWork.PDE.P3MoserIntegratedClosure
import ShenWork.Paper2.IntervalDomainLpTimeLeibniz

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- The abstract Moser energy on `intervalDomain` is the same power energy used
by the Paper2 time-Leibniz infrastructure. -/
theorem intervalDomain_integratedMoserEnergy_eq_powerEnergy
    (p : ℝ) (u : ℝ → intervalDomain.Point → ℝ) (t : ℝ) :
    integratedMoserEnergy intervalDomain u p t =
      intervalDomainPowerEnergy p u t := by
  unfold integratedMoserEnergy intervalDomainPowerEnergy
  change intervalDomainIntegral (fun x : intervalDomain.Point => (u t x) ^ p) =
    ∫ y in (0 : ℝ)..1, (intervalDomainLift (u t) y) ^ p
  unfold intervalDomainIntegral
  refine intervalIntegral.integral_congr (fun y hy => ?_)
  rw [Set.uIcc_of_le (zero_le_one)] at hy
  simp [intervalDomainLift, hy]

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

If `intervalDomainIntegral` is not visible, replace the `change`/`unfold` block by whatever local style is used elsewhere in `IntervalDomainLpBootstrapEnergyInequality.lean` and `IntervalAgmonInterpolation.lean`.

## 1b. HasDerivAt of `integratedMoserEnergy` from existing time-Leibniz

This should be provable from `intervalDomainPowerEnergy_hasDerivAt` plus the equality helper above.

```lean
import ShenWork.PDE.P3MoserIntegratedClosure
import ShenWork.Paper2.IntervalDomainLpTimeLeibniz

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- Interior-time derivative of the integrated Moser energy, obtained by routing
through `intervalDomainPowerEnergy_hasDerivAt`. -/
theorem intervalDomain_integratedMoserEnergy_hasDerivAt_of_classical
    {params : CM2Params} {T p t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun s => integratedMoserEnergy intervalDomain u p s)
      (deriv (fun s => integratedMoserEnergy intervalDomain u p s) t)
      t := by
  have hpow := intervalDomainPowerEnergy_hasDerivAt (q := p) hsol ht
  have hfun :
      (fun s => integratedMoserEnergy intervalDomain u p s) =
        fun s => intervalDomainPowerEnergy p u s := by
    funext s
    exact intervalDomain_integratedMoserEnergy_eq_powerEnergy p u s
  have hpow' :
      HasDerivAt
        (fun s => integratedMoserEnergy intervalDomain u p s)
        (∫ y in (0 : ℝ)..1, intervalDomainPowerDeriv p u t y) t := by
    simpa [hfun] using hpow
  -- Convert the explicit derivative to `deriv` of the same function.
  simpa [hpow'.deriv] using hpow'

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

If the final `simpa [hpow'.deriv]` fails, use:

```lean
convert hpow' using 1
exact hpow'.deriv.symm
```

## 1c. Closed-window FTC from classical time-Leibniz plus derivative integrability

This is the minimal honest theorem. It should be provable wiring once the correct Mathlib FTC lemma name is selected.

```lean
import ShenWork.PDE.P3MoserIntegratedClosure
import ShenWork.Paper2.IntervalDomainLpTimeLeibniz

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- Produce the window FTC package for interval-domain Moser energies.  The
classical solution supplies interior `HasDerivAt`; `hreg` supplies closed-window
continuity of `Y_p`; the extra `hderivInt` is the missing derivative-integrability
field. -/
theorem intervalDomain_integratedMoserEnergyWindowFTC_of_classical
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity intervalDomain u T p0)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hderivInt :
      ∀ p, p0 ≤ p →
        ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
          IntervalIntegrable
            (fun s => deriv (fun τ => integratedMoserEnergy intervalDomain u p τ) s)
            volume t1 t2) :
    IntegratedMoserEnergyWindowFTC intervalDomain u T p0 where
  deriv_intervalIntegrable := hderivInt
  window_ftc := by
    intro p hp t1 ht1 t2 ht2
    have hab : t1 ≤ t2 := ht2.1
    have hcont :
        ContinuousOn
          (fun t => integratedMoserEnergy intervalDomain u p t)
          (Set.Icc t1 t2) := by
      exact (hreg.energyContinuous p hp).mono
        (Icc_subset_uIcc_zero_T_of_endpoint_memberships ht1 ht2)
    have hderiv :
        ∀ s ∈ Set.Ioo t1 t2,
          HasDerivAt
            (fun τ => integratedMoserEnergy intervalDomain u p τ)
            (deriv (fun τ => integratedMoserEnergy intervalDomain u p τ) s)
            s := by
      intro s hs
      have hs0 : 0 < s := lt_of_le_of_lt ht1.1 hs.1
      have hsT : s < T := lt_of_lt_of_le hs.2 ht2.2
      exact intervalDomain_integratedMoserEnergy_hasDerivAt_of_classical
        (p := p) hsol ⟨hs0, hsT⟩
    have hderiv_int := hderivInt p hp t1 ht1 t2 ht2
    -- Try these Mathlib names in order:
    --   intervalIntegral.integral_deriv_eq_sub
    --   intervalIntegral.integral_deriv_eq_sub'
    --   intervalIntegral.integral_eq_sub_of_hasDerivAt
    --   intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    -- The expected final call shape is:
    exact intervalIntegral.integral_deriv_eq_sub hcont hderiv hderiv_int hab

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

The final Mathlib name/signature may differ. If it fails, immediately run:

```lean
#check intervalIntegral.integral_deriv_eq_sub
#check intervalIntegral.integral_deriv_eq_sub'
#check intervalIntegral.integral_eq_sub_of_hasDerivAt
#check intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
#check intervalIntegral.integral_of_le
```

and adapt the final line. The mathematical inputs above are exactly the right ones: closed continuity, derivative on `Ioo t1 t2`, and derivative interval-integrability.

### What remains a genuine regularity assumption here

`hderivInt` is the genuine missing field unless your local code already proves it. It is **not** contained in `IntegratedMoserFirstCrossingRegularity`.

A clean explicit frontier is:

```lean
def IntegratedMoserEnergyDerivativeWindowIntegrability
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p →
    ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
      IntervalIntegrable
        (fun s => deriv (fun τ => integratedMoserEnergy D u p τ) s)
        volume t1 t2
```

For `intervalDomain`, this should eventually follow from joint continuity/boundedness of the time-derivative integrand over compact slabs, using the infrastructure in `IntervalUnderIntegralLeibniz.lean`. But it is not just algebraic wiring.

## 2. Window higher-power energy from pointwise `LpBootstrapEnergyInequality`

### Target frontier shape

Use the same shape expected by the coefficient absorption wrapper. Keeping this as a named frontier makes later call sites cleaner.

```lean
def IntegratedHigherPowerEnergyWindowCoeffFrontier
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 theta : ℝ) : Prop :=
  ∀ p, p0 ≤ p →
    ∃ A K C0 L eps : ℝ,
      0 < eps ∧ 0 ≤ K ∧ 0 ≤ C0 ∧ 0 ≤ L ∧
      (∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        integratedMoserEnergy D u p t2 -
            integratedMoserEnergy D u p t1 +
          A * (∫ s in t1..t2,
            integratedMoserGradientEnergy D u p s) ≤
        (C0 * p * (∫ s in t1..t2,
          max 1 (integratedMoserEnergy D u p s)) +
          K * (∫ s in t1..t2,
            integratedMoserEnergy D u (p + rho) s)) +
          L * (∫ s in t1..t2,
            max 1 (integratedMoserEnergy D u p s))) ∧
      K * eps ≤ A - theta
```

### Extra helper: length is bounded by `∫ max(1,Y)`

Needed to absorb a constant `L_const` from pointwise energy into the max-one integral.

```lean
theorem intervalIntegral_length_le_integral_max_one
    {a b : ℝ} {Y : ℝ → ℝ}
    (hab : a ≤ b)
    (hYmax_int : IntervalIntegrable (fun s => max (1 : ℝ) (Y s)) volume a b) :
    b - a ≤ ∫ s in a..b, max (1 : ℝ) (Y s) := by
  have hconst : IntervalIntegrable (fun _s : ℝ => (1 : ℝ)) volume a b :=
    intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hab hconst hYmax_int (by
    intro s _hs
    exact le_max_left (1 : ℝ) (Y s))
  have hlen : (∫ _s in a..b, (1 : ℝ)) = b - a := by
    rw [intervalIntegral.integral_const]
    simp [smul_eq_mul]
  simpa [hlen] using hmono
```

### A.e. strict-interior helper

This is the same endpoint bridge used for closed-window relative Moser.

```lean
theorem ae_restrict_Ioc_strictInterior_of_Icc_endpoints
    {T a b : ℝ}
    (haT : a ∈ Set.Icc (0 : ℝ) T)
    (hbT : b ∈ Set.Icc a T) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioc a b)), 0 < s ∧ s < T := by
  refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
  refine (MeasureTheory.ae_iff).2 ?_
  have hbad_subset :
      {s : ℝ | s ∈ Set.Ioc a b ∧ ¬ (0 < s ∧ s < T)} ⊆ ({T} : Set ℝ) := by
    intro s hs
    rcases hs with ⟨hsIoc, hbad⟩
    have hs_pos : 0 < s := lt_of_le_of_lt haT.1 hsIoc.1
    have hs_le_T : s ≤ T := le_trans hsIoc.2 hbT.2
    push_neg at hbad
    rcases hbad with hs_nonpos | hT_le_s
    · exact False.elim ((not_le_of_gt hs_pos) hs_nonpos)
    · exact le_antisymm hs_le_T hT_le_s
  exact measure_mono_null hbad_subset (by simp)
```

### Minimal theorem from pointwise energy + FTC + surplus

This theorem is provable wiring **if** the local a.e. monotonicity helper from Q2853 is available. If not, use `intervalIntegral.integral_of_le` plus `MeasureTheory.integral_mono_ae` exactly as in Q2853.

```lean
import ShenWork.PDE.P3MoserIntegratedClosure
import ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality

open MeasureTheory
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- Convert the pointwise bootstrap energy inequality into the full closed-window
higher-power energy frontier, assuming window FTC, energy nonnegativity, and an
explicit coefficient surplus for the constants selected by the pointwise energy
inequality. -/
theorem integratedHigherPowerEnergyWindow_of_LpBootstrapEnergyInequality_closed
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 theta : ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hftc : IntegratedMoserEnergyWindowFTC D u T p0)
    (hnonneg : IntegratedMoserEnergyNonnegativity D u T p0)
    (henergy : LpBootstrapEnergyInequality D u T rho p0)
    (hp_pos : ∀ p, p0 ≤ p → 0 < p)
    (hrho_nonneg : 0 ≤ rho)
    (hsurplus :
      ∀ p, p0 ≤ p →
      ∀ A B K Lconst : ℝ,
        0 < A → 0 < B → 0 < K →
        (∀ t, 0 < t → t < T →
          (1 / p) * deriv (fun τ => integratedMoserEnergy D u p τ) t +
              A * integratedMoserGradientEnergy D u p t +
              B * integratedMoserEnergy D u p t ≤
            K * integratedMoserEnergy D u (p + rho) t + Lconst) →
        ∃ eps : ℝ, 0 < eps ∧ (p * K) * eps ≤ p * A - theta) :
    IntegratedHigherPowerEnergyWindowCoeffFrontier D u T rho p0 theta := by
  intro p hp
  rcases henergy p hp with ⟨A, hA, B, hB, K, hK, Lconst, hpoint⟩
  have hp0 : 0 < p := hp_pos p hp
  have hp_nonneg : 0 ≤ p := hp0.le
  have hp_rho : p0 ≤ p + rho := le_trans hp (le_add_of_nonneg_right hrho_nonneg)
  -- Rewrite the pointwise statement in integratedMoserEnergy notation if needed.
  have hpoint' :
      ∀ t, 0 < t → t < T →
        (1 / p) * deriv (fun τ => integratedMoserEnergy D u p τ) t +
            A * integratedMoserGradientEnergy D u p t +
            B * integratedMoserEnergy D u p t ≤
          K * integratedMoserEnergy D u (p + rho) t + Lconst := by
    intro t ht0 htT
    simpa [integratedMoserEnergy, integratedMoserGradientEnergy] using
      hpoint t ht0 htT
  rcases hsurplus p hp A B K Lconst hA hB hK hpoint' with ⟨eps, heps, hgap⟩
  refine ⟨p * A, p * K, 0, p * max 0 Lconst, eps, heps, ?_, by positivity, ?_, ?_, ?_, hgap⟩
  · exact mul_nonneg hp_nonneg hK.le
  · exact mul_nonneg hp_nonneg (le_max_left _ _)
  · intro t1 ht1 t2 ht2
    have hab : t1 ≤ t2 := ht2.1
    have hsub : Set.Icc t1 t2 ⊆ Set.uIcc (0 : ℝ) T :=
      Icc_subset_uIcc_zero_T_of_endpoint_memberships ht1 ht2
    have hDeriv_int := hftc.deriv_intervalIntegrable p hp t1 ht1 t2 ht2
    have hG_int := hreg.gradient_intervalIntegrable_of_Icc hp hab hsub
    have hZ_int := hreg.power_intervalIntegrable_of_Icc hp_rho hab hsub
    have hYmax_int := hreg.maxOneEnergy_intervalIntegrable_of_Icc hp hab hsub
    let F : ℝ → ℝ := fun s =>
      deriv (fun τ => integratedMoserEnergy D u p τ) s +
        (p * A) * integratedMoserGradientEnergy D u p s
    let R : ℝ → ℝ := fun s =>
      (p * K) * integratedMoserEnergy D u (p + rho) s +
        p * Lconst
    have hF_int : IntervalIntegrable F volume t1 t2 := by
      dsimp [F]
      exact hDeriv_int.add (hG_int.const_mul (p * A))
    have hR_int : IntervalIntegrable R volume t1 t2 := by
      dsimp [R]
      exact (hZ_int.const_mul (p * K)).add intervalIntegrable_const
    have hstrict_ae := ae_restrict_Ioc_strictInterior_of_Icc_endpoints ht1 ht2
    have hFR_ae : ∀ᵐ s ∂(volume.restrict (Set.Ioc t1 t2)), F s ≤ R s := by
      filter_upwards [hstrict_ae] with s hs
      rcases hs with ⟨hs0, hsT⟩
      have hpt := hpoint' s hs0 hsT
      have hY_nonneg := hnonneg p hp hp_nonneg s hs0 hsT
      have hBY_nonneg : 0 ≤ p * B * integratedMoserEnergy D u p s := by
        exact mul_nonneg (mul_nonneg hp_nonneg hB.le) hY_nonneg
      -- Multiply the pointwise inequality by `p`, then drop the nonnegative
      -- `p*B*Y_p` term from the left.
      dsimp [F, R]
      nlinarith
    have hmono : ∫ s in t1..t2, F s ≤ ∫ s in t1..t2, R s := by
      -- Use local helper from Q2853, or replace by intervalIntegral.integral_of_le
      -- plus MeasureTheory.integral_mono_ae.
      exact intervalIntegral_integral_mono_ae_Ioc hab hF_int hR_int hFR_ae
    have hF_eq :
        (∫ s in t1..t2, F s) =
          (integratedMoserEnergy D u p t2 - integratedMoserEnergy D u p t1) +
          (p * A) * (∫ s in t1..t2,
            integratedMoserGradientEnergy D u p s) := by
      dsimp [F]
      rw [intervalIntegral.integral_add hDeriv_int (hG_int.const_mul (p * A))]
      rw [intervalIntegral.integral_const_mul]
      rw [hftc.window_ftc p hp t1 ht1 t2 ht2]
    have hR_eq :
        (∫ s in t1..t2, R s) =
          (p * K) * (∫ s in t1..t2,
            integratedMoserEnergy D u (p + rho) s) +
          (t2 - t1) * (p * Lconst) := by
      dsimp [R]
      rw [intervalIntegral.integral_add (hZ_int.const_mul (p * K)) intervalIntegrable_const]
      rw [intervalIntegral.integral_const_mul]
      rw [intervalIntegral.integral_const]
      ring
    have hlen_le_max :
        t2 - t1 ≤ ∫ s in t1..t2,
          max 1 (integratedMoserEnergy D u p s) :=
      intervalIntegral_length_le_integral_max_one hab hYmax_int
    have hconst_absorb :
        (t2 - t1) * (p * Lconst) ≤
          (p * max 0 Lconst) * (∫ s in t1..t2,
            max 1 (integratedMoserEnergy D u p s)) := by
      by_cases hLnonneg : 0 ≤ Lconst
      · have hLmax : max 0 Lconst = Lconst := max_eq_right hLnonneg
        have hcoef_nonneg : 0 ≤ p * Lconst := mul_nonneg hp_nonneg hLnonneg
        have hmul := mul_le_mul_of_nonneg_right hlen_le_max hcoef_nonneg
        simpa [hLmax, mul_comm, mul_left_comm, mul_assoc] using hmul
      · have hLle0 : Lconst ≤ 0 := le_of_not_ge hLnonneg
        have hleft_nonpos : (t2 - t1) * (p * Lconst) ≤ 0 := by
          have hlen_nonneg : 0 ≤ t2 - t1 := sub_nonneg.mpr hab
          have hpL_nonpos : p * Lconst ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp_nonneg hLle0
          exact mul_nonpos_of_nonneg_of_nonpos hlen_nonneg hpL_nonpos
        have hright_nonneg :
            0 ≤ (p * max 0 Lconst) * (∫ s in t1..t2,
              max 1 (integratedMoserEnergy D u p s)) := by
          have hcoef : 0 ≤ p * max 0 Lconst := mul_nonneg hp_nonneg (le_max_left _ _)
          have hmaxint_nonneg :
              0 ≤ ∫ s in t1..t2, max 1 (integratedMoserEnergy D u p s) := by
            exact intervalIntegral.integral_nonneg_of_forall hab
              (fun _ => le_trans zero_le_one (le_max_left _ _))
          exact mul_nonneg hcoef hmaxint_nonneg
        exact le_trans hleft_nonpos hright_nonneg
    -- Finish by rewriting the integrated pointwise inequality and absorbing the constant.
    rw [hF_eq] at hmono
    rw [hR_eq] at hmono
    calc
      integratedMoserEnergy D u p t2 - integratedMoserEnergy D u p t1 +
          (p * A) * (∫ s in t1..t2, integratedMoserGradientEnergy D u p s)
          ≤ (p * K) * (∫ s in t1..t2,
              integratedMoserEnergy D u (p + rho) s) +
            (t2 - t1) * (p * Lconst) := hmono
      _ ≤ (0 * p * (∫ s in t1..t2,
              max 1 (integratedMoserEnergy D u p s)) +
            (p * K) * (∫ s in t1..t2,
              integratedMoserEnergy D u (p + rho) s)) +
            (p * max 0 Lconst) * (∫ s in t1..t2,
              max 1 (integratedMoserEnergy D u p s)) := by
            nlinarith [hconst_absorb]

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

### Notes on likely compilation adjustments

1. If `LpBootstrapEnergyInequality` is not in scope, add:

```lean
open ShenWork.Paper2.IntervalDomainEnergyStep
```

or import/open `ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality`.

2. If `intervalIntegral_integral_mono_ae_Ioc` is not yet committed, add the helper from Q2853 or use:

```lean
rw [intervalIntegral.integral_of_le hab]
rw [intervalIntegral.integral_of_le hab]
exact MeasureTheory.integral_mono_ae ...
```

with the two `IntervalIntegrable` hypotheses converted by:

```lean
(intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hF_int
```

3. If `nlinarith` struggles at the pointwise multiplication step, explicitly derive:

```lean
have hpt_mul :
    deriv (fun τ => integratedMoserEnergy D u p τ) s +
      p * A * integratedMoserGradientEnergy D u p s +
      p * B * integratedMoserEnergy D u p s ≤
    p * K * integratedMoserEnergy D u (p + rho) s + p * Lconst := by
  have hm := mul_le_mul_of_nonneg_left hpt hp_nonneg
  field_simp [ne_of_gt hp0] at hm
  ring_nf at hm ⊢
  exact hm
```

then drop `p*B*Y` using `hBY_nonneg`.

## What is provable wiring vs genuine assumption

### Provable wiring

The following are routine and should be compile-targets:

- `intervalDomain_integratedMoserEnergy_eq_powerEnergy`
- `intervalDomain_integratedMoserEnergy_hasDerivAt_of_classical`
- `intervalIntegral_length_le_integral_max_one`
- `intervalDomain_integratedMoserEnergyWindowFTC_of_classical`, **provided** derivative interval-integrability is supplied
- `integratedHigherPowerEnergyWindow_of_LpBootstrapEnergyInequality_closed`, **provided** `IntegratedMoserEnergyWindowFTC`, energy nonnegativity, and explicit coefficient surplus are supplied

### Genuine PDE/regularity assumptions still needed

1. **Derivative interval-integrability / absolute continuity of `Y_p`.**

`IntegratedMoserFirstCrossingRegularity` does not include integrability of `deriv Y_p`. The time-Leibniz file gives pointwise `HasDerivAt`, but not window FTC by itself. Add either `IntegratedMoserEnergyDerivativeWindowIntegrability` or the full `IntegratedMoserEnergyWindowFTC` structure as a frontier.

2. **Coefficient surplus.**

`LpBootstrapEnergyInequality` gives `A > 0`, but the coefficient route for target `theta` needs surplus after scaling:

```lean
∃ eps > 0, (p * K) * eps ≤ p * A - theta
```

For `theta = 2`, this is not automatic from `A > 0`. It must remain an explicit assumption unless a stronger PDE energy theorem proves a lower bound on the chosen gradient coefficient.

3. **Closed-window a.e. integration of pointwise inequalities.**

This is proof plumbing, not PDE, but it must be present as a lemma (`ae_restrict_Ioc_strictInterior_of_Icc_endpoints` + interval-integral monotonicity a.e.). Without it, strict pointwise estimates cannot be applied directly at `t=0` or `t=T`.

## Recommended next edit order

1. Add `IntegratedMoserEnergyWindowFTC` and `IntegratedMoserEnergyDerivativeWindowIntegrability` definitions.
2. Add `intervalDomain_integratedMoserEnergy_eq_powerEnergy` and `intervalDomain_integratedMoserEnergy_hasDerivAt_of_classical`.
3. Add `intervalDomain_integratedMoserEnergyWindowFTC_of_classical` with `hderivInt` as input.
4. Add `intervalIntegral_length_le_integral_max_one`.
5. Add `integratedHigherPowerEnergyWindow_of_LpBootstrapEnergyInequality_closed` using explicit `hsurplus`.

This gives a clean formal seam: Codex-owned closure/plumbing proves all scalar/window algebra, while the remaining analytic producer obligation is exactly the derivative-window FTC/absolute-continuity and coefficient-surplus data.
