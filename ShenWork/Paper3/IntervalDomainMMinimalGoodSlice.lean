import ShenWork.Paper3.IntervalDomainMMinimalEntropy
import ShenWork.Paper3.IntervalDomainMEntropyBasinEntry
import ShenWork.Paper3.IntervalDomainEntropyStrong2Dynamics
import ShenWork.Paper2.IntervalDomainMWeightedGradient
import ShenWork.PDE.SignalSaturationFactor

/-!
# General-`m` entropy good slices in the minimal model

For the faithful interval equation with `a = b = 0`, the general-`m` entropy
retains half of its negative-power gradient dissipation.  The elliptic
log-gradient estimate and the sharp scalar signal-saturation factor give the
parameter-only remainder

`χ₀² μ (signalSaturationFactor β)²`.

Consequently the negative-power gradient dissipation has liminf no larger
than this number, without any eventual upper box and for every `m ≥ 1`.
-/

open Filter MeasureTheory Set Topology
open scoped Topology Interval

namespace ShenWork.Paper3

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainEnergyStep

noncomputable section

/-- Parameter-only floor in the minimal entropy good-slice estimate. -/
def minimalMGoodSliceDissipationFloor (p : CM2Params) : ℝ :=
  p.χ₀ ^ 2 * p.μ * signalSaturationFactor p.β ^ 2

/-- The weighted signal-gradient integral is bounded by the sharp saturation
factor.  This is the integrated form of
`|vₓ|/(1+v)^β ≤ √μ · signalSaturationFactor β`. -/
theorem intervalDomainM_weightedSignalGradient_le_mu_signalSaturationFactor_sq
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) (hbeta : 1 ≤ p.β) :
    (∫ y in (0 : ℝ)..1,
        (deriv (intervalDomainLift (v t)) y) ^ 2 *
          (1 + intervalDomainLift (v t) y) ^ (-2 * p.β)) ≤
      p.μ * signalSaturationFactor p.β ^ 2 := by
  let V : ℝ → ℝ := intervalDomainLift (v t)
  have ht : t ∈ Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hV2 : ContDiffOn ℝ 2 V (Icc (0 : ℝ) 1) := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.1
  have hVxcont : ContinuousOn (deriv V) (Icc (0 : ℝ) 1) := by
    simpa [V] using deriv_v_continuousOn_Icc hsol ht0 htT
  have hVnonneg : ∀ y ∈ Icc (0 : ℝ) 1, 0 ≤ V y := by
    intro y hy
    simpa [V, intervalDomainLift, hy] using
      hsol.v_nonneg (x := (⟨y, hy⟩ : intervalDomainPoint)) ht0 htT
  have hlog : ∀ y ∈ Icc (0 : ℝ) 1,
      |deriv V y| ≤ Real.sqrt p.μ * V y := by
    simpa [V] using elliptic_log_gradient_bound hsol ht0 htT
  have hfactorPos : 0 < signalSaturationFactor p.β :=
    signalSaturationFactor_pos hbeta
  have hint : IntervalIntegrable
      (fun y => (deriv V y) ^ 2 * (1 + V y) ^ (-2 * p.β))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (hVxcont.pow 2).mul
      ((continuousOn_const.add hV2.continuousOn).rpow_const
        (fun y hy => Or.inl (by
          simpa only [Pi.add_apply] using
            ne_of_gt (show 0 < 1 + V y by linarith [hVnonneg y hy]))))
  have hpoint : ∀ y ∈ Icc (0 : ℝ) 1,
      (deriv V y) ^ 2 * (1 + V y) ^ (-2 * p.β) ≤
        p.μ * signalSaturationFactor p.β ^ 2 := by
    intro y hy
    have hbase : 0 < 1 + V y := by linarith [hVnonneg y hy]
    let w : ℝ := (1 + V y) ^ (-p.β)
    have hw : 0 ≤ w := Real.rpow_nonneg hbase.le _
    have hsat :
        V y * w ≤ signalSaturationFactor p.β := by
      simpa [w] using
        signal_mul_one_add_rpow_neg_le_factor hbeta (hVnonneg y hy)
    have habsWeighted :
        |deriv V y| * w ≤
          Real.sqrt p.μ * signalSaturationFactor p.β := by
      calc
        |deriv V y| * w ≤ (Real.sqrt p.μ * V y) * w :=
          mul_le_mul_of_nonneg_right (hlog y hy) hw
        _ = Real.sqrt p.μ * (V y * w) := by ring
        _ ≤ Real.sqrt p.μ * signalSaturationFactor p.β :=
          mul_le_mul_of_nonneg_left hsat (Real.sqrt_nonneg _)
    have hleftNonneg : 0 ≤ |deriv V y| * w :=
      mul_nonneg (abs_nonneg _) hw
    have hrightNonneg :
        0 ≤ Real.sqrt p.μ * signalSaturationFactor p.β :=
      mul_nonneg (Real.sqrt_nonneg _) hfactorPos.le
    have hsq :
        (|deriv V y| * w) ^ 2 ≤
          (Real.sqrt p.μ * signalSaturationFactor p.β) ^ 2 := by
      simpa [pow_two] using
        mul_self_le_mul_self hleftNonneg habsWeighted
    have hwSq : w ^ 2 = (1 + V y) ^ (-2 * p.β) := by
      dsimp [w]
      rw [sq, ← Real.rpow_add hbase]
      congr 1
      ring
    have hsqrtSq : Real.sqrt p.μ ^ 2 = p.μ :=
      Real.sq_sqrt p.hμ.le
    calc
      (deriv V y) ^ 2 * (1 + V y) ^ (-2 * p.β) =
          (|deriv V y| * w) ^ 2 := by
        rw [mul_pow, sq_abs, hwSq]
      _ ≤ (Real.sqrt p.μ * signalSaturationFactor p.β) ^ 2 := hsq
      _ = p.μ * signalSaturationFactor p.β ^ 2 := by
        rw [mul_pow, hsqrtSq]
  change (∫ y in (0 : ℝ)..1,
      (deriv V y) ^ 2 * (1 + V y) ^ (-2 * p.β)) ≤ _
  calc
    (∫ y in (0 : ℝ)..1,
        (deriv V y) ^ 2 * (1 + V y) ^ (-2 * p.β)) ≤
        ∫ _y in (0 : ℝ)..1,
          p.μ * signalSaturationFactor p.β ^ 2 :=
      intervalIntegral.integral_mono_on (by norm_num) hint
        intervalIntegrable_const hpoint
    _ = p.μ * signalSaturationFactor p.β ^ 2 := by
      rw [intervalIntegral.integral_const]
      norm_num [smul_eq_mul]

/-- Minimal entropy slope with the parameter-only good-slice floor exposed.
The physical equation contributes the exact dissipation
`∫ u⁻²ᵐ uₓ²`; half is retained by Young's inequality. -/
theorem intervalDomainM_minimal_entropySlope_le_goodSliceFloor
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hm : 1 ≤ p.m) (hb0 : p.b = 0) (hbeta : 1 ≤ p.β)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (heq : Paper3ConstantEquilibrium p uStar vStar) :
    intervalDomain.integral (fun x =>
        chemotaxisEntropyIntegrand p.m uStar (u t x) *
          intervalDomain.timeDeriv u t x) ≤
      -(((2 * p.m - 1) * uStar ^ (2 * p.m - 1)) / 2) *
        (intervalDomainLpWeightedGradientDissipation
            (2 - 2 * p.m) u t -
          minimalMGoodSliceDissipationFloor p) := by
  let c : ℝ := (2 * p.m - 1) * uStar ^ (2 * p.m - 1)
  have hc : 0 ≤ c := by
    exact mul_nonneg (by linarith) (Real.rpow_pos_of_pos heq.u_pos _).le
  let G : ℝ :=
    intervalDomainLpWeightedGradientDissipation (2 - 2 * p.m) u t
  let X : ℝ :=
    ShenWork.Paper2.IntervalDomainM.lpSignedCrossIntegralM
      p (2 - 2 * p.m) u v t
  let W : ℝ := ∫ y in (0 : ℝ)..1,
    (deriv (intervalDomainLift (v t)) y) ^ 2 *
      (1 + intervalDomainLift (v t) y) ^ (-2 * p.β)
  have hid := intervalDomainM_entropySlope_le_of_classical
    hm hsol ht0 htT heq
  have hyoung := intervalDomainM_entropyDiffusionChemotaxis_half_young
    (c := c) hc hsol ht0 htT
  have hW := intervalDomainM_weightedSignalGradient_le_mu_signalSaturationFactor_sq
    hsol ht0 htT hbeta
  change W ≤ p.μ * signalSaturationFactor p.β ^ 2 at hW
  have hscale : 0 ≤ p.χ₀ ^ 2 * c / 2 :=
    div_nonneg (mul_nonneg (sq_nonneg _) hc) (by norm_num)
  have hWscaled := mul_le_mul_of_nonneg_left hW hscale
  change
    -c * G + p.χ₀ * c * X ≤
      -(c / 2) * G + p.χ₀ ^ 2 * c / 2 * W at hyoung
  calc
    intervalDomain.integral (fun x =>
        chemotaxisEntropyIntegrand p.m uStar (u t x) *
          intervalDomain.timeDeriv u t x) ≤
        -c * G + p.χ₀ * c * X -
          p.b * chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
      simpa [c, G, X] using hid
    _ = -c * G + p.χ₀ * c * X := by rw [hb0]; ring
    _ ≤ -(c / 2) * G + p.χ₀ ^ 2 * c / 2 * W := hyoung
    _ ≤ -(c / 2) * G +
        p.χ₀ ^ 2 * c / 2 *
          (p.μ * signalSaturationFactor p.β ^ 2) := by
      linarith
    _ = -(c / 2) *
        (G - minimalMGoodSliceDissipationFloor p) := by
      unfold minimalMGoodSliceDissipationFloor
      ring
    _ = -(((2 * p.m - 1) * uStar ^ (2 * p.m - 1)) / 2) *
        (intervalDomainLpWeightedGradientDissipation
            (2 - 2 * p.m) u t -
          minimalMGoodSliceDissipationFloor p) := by
      rfl

/-- Arbitrarily late good slices: the negative-power gradient dissipation is
within any positive error of its sharp parameter-only floor. -/
theorem intervalDomainM_minimal_exists_late_goodSlice
    (p : CM2Params) (hm : 1 < p.m)
    {uStar vStar : ℝ}
    (hb0 : p.b = 0) (hbeta : 1 ≤ p.β)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
    {T eps : ℝ} (hT : 0 < T) (heps : 0 < eps) :
    ∃ t, T ≤ t ∧
      intervalDomainLpWeightedGradientDissipation
          (2 - 2 * p.m) u t <
        minimalMGoodSliceDissipationFloor p + eps := by
  let c : ℝ := ((2 * p.m - 1) * uStar ^ (2 * p.m - 1)) / 2
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos
      (mul_pos (by linarith) (Real.rpow_pos_of_pos heq.u_pos _))
      (by norm_num)
  obtain ⟨t, ht, htGood⟩ :=
    exists_late_dissipation_lt_of_nonnegative_energy_on_Ici
      (E := fun s => chemotaxisEntropyFunctional intervalDomain p.m uStar u s)
      (D := fun s =>
        intervalDomainLpWeightedGradientDissipation
            (2 - 2 * p.m) u s -
          minimalMGoodSliceDissipationFloor p)
      (slope := fun s => intervalDomain.integral (fun x =>
        chemotaxisEntropyIntegrand p.m uStar (u s x) *
          intervalDomain.timeDeriv u s x))
      hc hT heps
      (fun s hs =>
        intervalDomain_chemotaxisEntropyFunctional_nonneg_of_inside_pos
          (by linarith : (1 / 2 : ℝ) ≤ p.m) heq.u_pos
          (fun x hx => huv.pos (t := s) (x := x) hs hx))
      (intervalDomainM_strongMEntropy_hasDerivAt p heq huv)
      (fun s hs => by
        have hs0 : 0 < s := lt_of_lt_of_le hT hs
        have hH : 0 < s + 1 := by linarith
        simpa [c] using
          intervalDomainM_minimal_entropySlope_le_goodSliceFloor
            hm.le hb0 hbeta (huv.classical (s + 1) hH)
              hs0 (by linarith) heq)
  exact ⟨t, ht, by linarith⟩

/-- Liminf form of the general-`m` good-slice estimate:

`liminf_{t→∞} ∫ u(t)⁻²ᵐ uₓ(t)² ≤ χ₀² μ σ_β²`. -/
theorem intervalDomainM_minimal_goodSlice_liminf_le
    (p : CM2Params) (hm : 1 < p.m)
    {uStar vStar : ℝ}
    (hb0 : p.b = 0) (hbeta : 1 ≤ p.β)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v) :
    Filter.liminf
        (fun t => intervalDomainLpWeightedGradientDissipation
          (2 - 2 * p.m) u t) atTop ≤
      minimalMGoodSliceDissipationFloor p := by
  let D : ℝ → ℝ := fun t =>
    intervalDomainLpWeightedGradientDissipation (2 - 2 * p.m) u t
  have hDnonneg : ∀ᶠ t : ℝ in atTop, 0 ≤ D t := by
    refine eventually_atTop.2 ⟨1, fun t ht => ?_⟩
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
    have hH : 0 < t + 1 := by linarith
    let hsol := huv.classical (t + 1) hH
    rw [show D t =
        ∫ y in (0 : ℝ)..1,
          (intervalDomainLift (u t) y) ^ ((2 - 2 * p.m) - 2) *
            (deriv (intervalDomainLift (u t)) y) ^ 2 by
      simpa [D] using intervalDomainM_lpGradient_eq_integral
        (q := 2 - 2 * p.m) hsol ht0 (by linarith)]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro y hy
    have hupos : 0 < intervalDomainLift (u t) y :=
      solution_lift_pos_Icc hsol ⟨ht0, by linarith⟩ y hy
    exact mul_nonneg (Real.rpow_nonneg hupos.le _) (sq_nonneg _)
  have hbounded :
      IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop D :=
    isBoundedUnder_of_eventually_ge hDnonneg
  refine Filter.liminf_le_of_le (hf := hbounded) ?_
  intro b hb
  by_contra hnot
  have hfloor_lt_b : minimalMGoodSliceDissipationFloor p < b :=
    lt_of_not_ge hnot
  rcases eventually_atTop.1 hb with ⟨Tb, hTb⟩
  let T : ℝ := max Tb 1
  let eps : ℝ := (b - minimalMGoodSliceDissipationFloor p) / 2
  have hT : 0 < T := lt_of_lt_of_le one_pos (le_max_right _ _)
  have heps : 0 < eps := by dsimp [eps]; linarith
  obtain ⟨t, ht, hgood⟩ :=
    intervalDomainM_minimal_exists_late_goodSlice
      p hm hb0 hbeta heq huv hT heps
  have hbD : b ≤ D t :=
    hTb t ((le_max_left Tb (1 : ℝ)).trans ht)
  have hDb : D t < b := by
    dsimp [eps] at hgood
    change D t < _ at hgood
    linarith
  exact (not_lt_of_ge hbD) hDb

#print axioms
  intervalDomainM_weightedSignalGradient_le_mu_signalSaturationFactor_sq
#print axioms intervalDomainM_minimal_entropySlope_le_goodSliceFloor
#print axioms intervalDomainM_minimal_exists_late_goodSlice
#print axioms intervalDomainM_minimal_goodSlice_liminf_le

end

end ShenWork.Paper3
