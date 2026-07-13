import ShenWork.Paper3.IntervalDomainEntropyEllipticWeight
import ShenWork.Paper2.IntervalDomainMWeightedGradient

/-!
# The weighted elliptic estimate used by Paper 3 entropy dissipation

This file proves the Neumann multiplier estimate on the actual unit interval.
It first establishes a static `C²` estimate and then discharges every static
hypothesis from a classical solution of the faithful interval model.  No
`Paper3Constants`, compactness, persistence, or stability package is used.
-/

open MeasureTheory Set
open scoped Topology Interval
open ShenWork.IntervalDomain
open ShenWork.IntervalEllipticCharacterization

namespace ShenWork.Paper3

noncomputable section

/-- Weighted scalar Young inequality with the exact coefficient used in the
elliptic multiplier estimate. -/
theorem entropyElliptic_source_young
    {mu nu H w weight : ℝ}
    (hmu : 0 < mu) (hweight : 0 ≤ weight) :
    nu * H * w * weight ≤
      mu * w ^ 2 * weight + nu ^ 2 / (4 * mu) * H ^ 2 * weight := by
  rw [← sub_nonneg]
  have hden : 0 ≤ 1 / (4 * mu) := by positivity
  have hsquare : 0 ≤ weight * (2 * mu * w - nu * H) ^ 2 :=
    mul_nonneg hweight (sq_nonneg _)
  have hprod : 0 ≤ 1 / (4 * mu) *
      (weight * (2 * mu * w - nu * H) ^ 2) :=
    mul_nonneg hden hsquare
  convert hprod using 1 <;> field_simp [ne_of_gt hmu] <;> ring

/-- Static weighted Neumann multiplier estimate.  Its hypotheses are exactly
the regularity, positivity, elliptic equation, and boundary conditions of one
positive classical slice. -/
theorem interval_entropyElliptic_gradient_estimate
    {mu nu beta gamma uStar vStar : ℝ}
    (hmu : 0 < mu) (hnu : 0 < nu)
    (hbeta : 0 ≤ beta) (_hgamma : 0 < gamma)
    (_huStar : 0 < uStar) (hvStar : 0 ≤ vStar)
    {U V : ℝ → ℝ}
    (hUcont : ContinuousOn U (Set.Icc (0 : ℝ) 1))
    (hUpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < U x)
    (hV2 : ContDiffOn ℝ 2 V (Set.Icc (0 : ℝ) 1))
    (hdVcont : ContinuousOn (deriv V) (Set.Icc (0 : ℝ) 1))
    (hVnonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ V x)
    (hVxx : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      deriv (deriv V) x = mu * V x - nu * U x ^ gamma)
    (hNeu0 : deriv V 0 = 0) (hNeu1 : deriv V 1 = 0)
    (heq : mu * vStar = nu * uStar ^ gamma) :
    (1 + betaTilde beta * vStar) *
        (∫ x in (0 : ℝ)..1,
          (deriv V x) ^ 2 * (1 + V x) ^ (-2 * beta)) ≤
      nu ^ 2 / (4 * mu) *
        (∫ x in (0 : ℝ)..1, (U x ^ gamma - uStar ^ gamma) ^ 2) := by
  let eta : ℝ := betaTilde beta
  let B : ℝ → ℝ := fun x => (1 + V x) ^ (-eta)
  let W : ℝ → ℝ := fun x => (V x - vStar) * B x
  let W' : ℝ → ℝ := fun x =>
    entropyEllipticWeight beta vStar (V x) * deriv V x
  let H : ℝ → ℝ := fun x => U x ^ gamma - uStar ^ gamma
  have hVcont : ContinuousOn V (Set.Icc (0 : ℝ) 1) := hV2.continuousOn
  have hbase_pos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < 1 + V x := by
    intro x hx
    linarith [hVnonneg x hx]
  have hBcont : ContinuousOn B (Set.Icc (0 : ℝ) 1) := by
    dsimp [B]
    exact (continuousOn_const.add hVcont).rpow_const
      (fun x hx => Or.inl (ne_of_gt (hbase_pos x hx)))
  have htailcont : ContinuousOn
      (fun x => (1 + V x) ^ (-eta - 1)) (Set.Icc (0 : ℝ) 1) :=
    (continuousOn_const.add hVcont).rpow_const
      (fun x hx => Or.inl (ne_of_gt (hbase_pos x hx)))
  have hWcont : ContinuousOn W (Set.Icc (0 : ℝ) 1) := by
    exact (hVcont.sub continuousOn_const).mul hBcont
  have hweightcont : ContinuousOn
      (fun x => entropyEllipticWeight beta vStar (V x))
      (Set.Icc (0 : ℝ) 1) := by
    unfold entropyEllipticWeight
    exact hBcont.sub
      (((continuousOn_const.mul (hVcont.sub continuousOn_const))).mul htailcont)
  have hW'cont : ContinuousOn W' (Set.Icc (0 : ℝ) 1) :=
    hweightcont.mul hdVcont
  have hWderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt W (W' x) x := by
    intro x hx
    have hxIcc := Set.Ioo_subset_Icc_self hx
    have hVderiv :=
      (ShenWork.MinPersistenceAtoms.contDiffOn_two_hasDerivAt_pair
        isOpen_Ioo (hV2.mono Set.Ioo_subset_Icc_self) hx).1
    have hbaseDeriv : HasDerivAt (fun y => 1 + V y) (deriv V x) x := by
      convert (hasDerivAt_const x (1 : ℝ)).add hVderiv using 1 <;> ring
    have hpowDeriv := hbaseDeriv.rpow_const (p := -eta)
      (Or.inl (ne_of_gt (hbase_pos x hxIcc)))
    convert (hVderiv.sub_const vStar).mul hpowDeriv using 1 <;>
      dsimp [W, W', B, eta, entropyEllipticWeight] <;> ring
  have hV2deriv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (deriv V) (deriv (deriv V) x) x := by
    intro x hx
    exact (ShenWork.MinPersistenceAtoms.contDiffOn_two_hasDerivAt_pair
      isOpen_Ioo (hV2.mono Set.Ioo_subset_Icc_self) hx).2
  have hW'int : IntervalIntegrable W' volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le zero_le_one] using hW'cont
  have hV2int : IntervalIntegrable (deriv (deriv V)) volume 0 1 :=
    intervalIntegrable_deriv_deriv_of_contDiffOn_two hV2
  have hWV2int : IntervalIntegrable
      (fun x => W x * deriv (deriv V) x) volume 0 1 :=
    hV2int.continuousOn_mul (by
      simpa [Set.uIcc_of_le zero_le_one] using hWcont)
  have hW'dVint : IntervalIntegrable
      (fun x => W' x * deriv V x) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact hW'cont.mul hdVcont
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (u := W) (v := deriv V)
    (u' := W') (v' := deriv (deriv V))
    (by simpa [Set.uIcc_of_le zero_le_one] using hWcont)
    (by simpa [Set.uIcc_of_le zero_le_one] using hdVcont)
    (by simpa using hWderiv) (by simpa using hV2deriv) hW'int hV2int
  have hIBPzero :
      (∫ x in (0 : ℝ)..1, W x * deriv (deriv V) x) =
        -∫ x in (0 : ℝ)..1, W' x * deriv V x := by
    rw [hNeu0, hNeu1] at hIBP
    linarith
  have hHcont : ContinuousOn H (Set.Icc (0 : ℝ) 1) := by
    dsimp [H]
    exact (hUcont.rpow_const
      (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))).sub continuousOn_const
  have hQcont : ContinuousOn
      (fun x => (V x - vStar) ^ 2 * B x) (Set.Icc (0 : ℝ) 1) :=
    (hVcont.sub continuousOn_const).pow 2 |>.mul hBcont
  have hRcont : ContinuousOn
      (fun x => H x * (V x - vStar) * B x) (Set.Icc (0 : ℝ) 1) :=
    (hHcont.mul (hVcont.sub continuousOn_const)).mul hBcont
  have hQint : IntervalIntegrable
      (fun x => (V x - vStar) ^ 2 * B x) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le zero_le_one] using hQcont
  have hRint : IntervalIntegrable
      (fun x => H x * (V x - vStar) * B x) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le zero_le_one] using hRcont
  have hPDEint :
      (∫ x in (0 : ℝ)..1, W x * deriv (deriv V) x) =
        mu * (∫ x in (0 : ℝ)..1, (V x - vStar) ^ 2 * B x) -
          nu * (∫ x in (0 : ℝ)..1, H x * (V x - vStar) * B x) := by
    calc
      _ = ∫ x in (0 : ℝ)..1,
          mu * ((V x - vStar) ^ 2 * B x) -
            nu * (H x * (V x - vStar) * B x) := by
        apply intervalIntegral.integral_congr_ae
        have hne1 : ∀ᵐ x ∂volume, x ≠ (1 : ℝ) := by
          have hs : {x : ℝ | ¬ x ≠ 1} = ({1} : Set ℝ) := by
            ext x
            simp
          rw [MeasureTheory.ae_iff, hs]
          exact Real.volume_singleton
        filter_upwards [hne1] with x hxne hxmem
        rw [Set.uIoc_of_le zero_le_one] at hxmem
        have hx : x ∈ Set.Ioo (0 : ℝ) 1 :=
          ⟨hxmem.1, lt_of_le_of_ne hxmem.2 hxne⟩
        have hpde := hVxx x hx
        have hpde' : deriv (deriv V) x =
            mu * (V x - vStar) - nu * H x := by
          dsimp [H]
          linarith
        dsimp [W]
        rw [hpde']
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub (hQint.const_mul mu)
            (hRint.const_mul nu),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  have hbalance :
      (∫ x in (0 : ℝ)..1, W' x * deriv V x) +
          mu * (∫ x in (0 : ℝ)..1, (V x - vStar) ^ 2 * B x) =
        nu * (∫ x in (0 : ℝ)..1, H x * (V x - vStar) * B x) := by
    linarith [hIBPzero, hPDEint]
  have hBnonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ B x := by
    intro x hx
    exact Real.rpow_nonneg (hbase_pos x hx).le _
  have hH2Bcont : ContinuousOn (fun x => H x ^ 2 * B x)
      (Set.Icc (0 : ℝ) 1) := hHcont.pow 2 |>.mul hBcont
  have hH2Bint : IntervalIntegrable (fun x => H x ^ 2 * B x) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le zero_le_one] using hH2Bcont
  have hYoungInt :
      nu * (∫ x in (0 : ℝ)..1, H x * (V x - vStar) * B x) ≤
        mu * (∫ x in (0 : ℝ)..1, (V x - vStar) ^ 2 * B x) +
          nu ^ 2 / (4 * mu) *
            (∫ x in (0 : ℝ)..1, H x ^ 2 * B x) := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_add (hQint.const_mul mu)
      (hH2Bint.const_mul (nu ^ 2 / (4 * mu)))]
    exact intervalIntegral.integral_mono_on (by norm_num)
      (hRint.const_mul nu)
      ((hQint.const_mul mu).add
        (hH2Bint.const_mul (nu ^ 2 / (4 * mu))))
      (fun x hx => by
        simpa [mul_assoc] using
          entropyElliptic_source_young (mu := mu) (nu := nu)
            (H := H x) (w := V x - vStar) (weight := B x)
            hmu (hBnonneg x hx))
  have hAupper :
      (∫ x in (0 : ℝ)..1, W' x * deriv V x) ≤
        nu ^ 2 / (4 * mu) *
          (∫ x in (0 : ℝ)..1, H x ^ 2 * B x) := by
    linarith [hbalance, hYoungInt]
  have hB_le_one : ∀ x ∈ Set.Icc (0 : ℝ) 1, B x ≤ 1 := by
    intro x hx
    dsimp [B, eta]
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by linarith [hVnonneg x hx]) (neg_nonpos.mpr (betaTilde_nonneg beta))
  have hH2int : IntervalIntegrable (fun x => H x ^ 2) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le zero_le_one] using hHcont.pow 2
  have hsourceUpper :
      (∫ x in (0 : ℝ)..1, H x ^ 2 * B x) ≤
        ∫ x in (0 : ℝ)..1, H x ^ 2 := by
    exact intervalIntegral.integral_mono_on (by norm_num) hH2Bint hH2int
      (fun x hx => by
        have hsquare := sq_nonneg (H x)
        nlinarith [mul_le_mul_of_nonneg_left (hB_le_one x hx) hsquare])
  have hcoef_nonneg : 0 ≤ nu ^ 2 / (4 * mu) := by positivity
  have hAupper' :
      (∫ x in (0 : ℝ)..1, W' x * deriv V x) ≤
        nu ^ 2 / (4 * mu) *
          (∫ x in (0 : ℝ)..1, H x ^ 2) :=
    hAupper.trans (mul_le_mul_of_nonneg_left hsourceUpper hcoef_nonneg)
  have hGradCont : ContinuousOn
      (fun x => (deriv V x) ^ 2 * (1 + V x) ^ (-2 * beta))
      (Set.Icc (0 : ℝ) 1) :=
    (hdVcont.pow 2).mul
      ((continuousOn_const.add hVcont).rpow_const
        (fun x hx => Or.inl (ne_of_gt (hbase_pos x hx))))
  have hGradInt : IntervalIntegrable
      (fun x => (deriv V x) ^ 2 * (1 + V x) ^ (-2 * beta))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le zero_le_one] using hGradCont
  have hAlower :
      (1 + betaTilde beta * vStar) *
          (∫ x in (0 : ℝ)..1,
            (deriv V x) ^ 2 * (1 + V x) ^ (-2 * beta)) ≤
        ∫ x in (0 : ℝ)..1, W' x * deriv V x := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on (by norm_num)
      (hGradInt.const_mul (1 + betaTilde beta * vStar)) hW'dVint
      (fun x hx => by
        have hw := entropyEllipticWeight_lower hbeta hvStar (hVnonneg x hx)
        have hsquare : 0 ≤ (deriv V x) ^ 2 := sq_nonneg _
        dsimp [W']
        nlinarith [mul_le_mul_of_nonneg_right hw hsquare])
  simpa [H] using hAlower.trans hAupper'

/-- The weighted elliptic gradient estimate for one positive classical slice
of the faithful interval equation. -/
theorem intervalDomain_entropyElliptic_gradient_estimate_of_classical
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : ShenWork.Paper2.IsPaper2ClassicalSolution
      intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (heq : Paper3ConstantEquilibrium p uStar vStar) :
    (1 + betaTilde p.β * vStar) *
        (∫ x in (0 : ℝ)..1,
          (deriv (intervalDomainLift (v t)) x) ^ 2 *
            (1 + intervalDomainLift (v t) x) ^ (-2 * p.β)) ≤
      p.ν ^ 2 / (4 * p.μ) *
        (∫ x in (0 : ℝ)..1,
          (intervalDomainLift (u t) x ^ p.γ - uStar ^ p.γ) ^ 2) := by
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let V : ℝ → ℝ := intervalDomainLift (v t)
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hUcont : ContinuousOn U (Set.Icc (0 : ℝ) 1) := by
    simpa [U] using
      ShenWork.Paper2.IntervalDomainM.solution_lift_continuousOn_Icc hsol ht
  have hUpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < U x := by
    intro x hx
    simpa [U] using
      ShenWork.Paper2.IntervalDomainM.solution_lift_pos_Icc hsol ht x hx
  have hV2 : ContDiffOn ℝ 2 V (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.1
  have hdVcont : ContinuousOn (deriv V) (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using
      ShenWork.Paper2.IntervalDomainM.deriv_v_continuousOn_Icc hsol ht0 htT
  have hVnonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ V x := by
    intro x hx
    simpa [V, intervalDomainLift, hx] using
      hsol.v_nonneg (x := (⟨x, hx⟩ : intervalDomain.Point)) ht0 htT
  have hVxx : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      deriv (deriv V) x = p.μ * V x - p.ν * U x ^ p.γ := by
    intro x hx
    simpa [V, U] using
      ShenWork.Paper2.IntervalDomainM.v_xx_eq_reaction_lift
        hsol ht0 htT hx.1 hx.2
  have hNeu0 : deriv V 0 = 0 := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.2.1
  have hNeu1 : deriv V 1 = 0 := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.2.2
  simpa [U, V] using
    interval_entropyElliptic_gradient_estimate
      p.hμ p.hν p.hβ p.hγ heq.u_pos heq.v_nonneg
      hUcont hUpos hV2 hdVcont hVnonneg hVxx hNeu0 hNeu1
      heq.elliptic_relation

#print axioms entropyElliptic_source_young
#print axioms interval_entropyElliptic_gradient_estimate
#print axioms intervalDomain_entropyElliptic_gradient_estimate_of_classical

end

end ShenWork.Paper3
