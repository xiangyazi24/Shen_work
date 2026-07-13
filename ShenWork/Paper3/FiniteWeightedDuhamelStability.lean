/- Weighted quadratic Duhamel closure before a finite maximal horizon. -/
import ShenWork.Paper3.WeightedDuhamelStability

namespace ShenWork.Paper3

open MeasureTheory Set Real

noncomputable section

/-- Finite-horizon first-exit closure.  No endpoint value at `H` is required;
this is the form needed on a putative finite maximal classical branch. -/
theorem weightedTail_bound_of_bootstrap_before
    {z : ℝ → ℝ} {R B H : ℝ}
    (_hR : 0 < R) (hB : B < R)
    (hcont : ContinuousOn z (Set.Ico (0 : ℝ) H))
    (hz0 : z 0 < R)
    (hstep : ∀ t, 0 ≤ t → t < H →
      (∀ s ∈ Set.Icc (0 : ℝ) t, z s ≤ R) → z t ≤ B) :
    ∀ t, 0 ≤ t → t < H → z t ≤ R := by
  intro t ht htH
  by_contra hnot
  have hzt : R < z t := lt_of_not_ge hnot
  have h0t : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, ht⟩
  have htt : t ∈ Set.Icc (0 : ℝ) t := ⟨ht, le_rfl⟩
  have hcont0t : ContinuousOn z (Set.Icc (0 : ℝ) t) :=
    hcont.mono (fun _x hx => ⟨hx.1, lt_of_le_of_lt hx.2 htH⟩)
  let Z : Set ℝ := {s | s ∈ Set.Icc (0 : ℝ) t ∧ z s = R}
  have hZ_nonempty : Z.Nonempty := by
    have hRmem : R ∈ Set.Icc (z 0) (z t) :=
      ⟨le_of_lt hz0, le_of_lt hzt⟩
    rcases isPreconnected_Icc.intermediate_value h0t htt hcont0t hRmem with
      ⟨s, hsI, hsR⟩
    exact ⟨s, hsI, hsR⟩
  have hZ_compact : IsCompact Z := by
    have hclosed : IsClosed
        (Set.Icc (0 : ℝ) t ∩ z ⁻¹' ({R} : Set ℝ)) :=
      hcont0t.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    have hc : IsCompact
        (Set.Icc (0 : ℝ) t ∩ z ⁻¹' ({R} : Set ℝ)) :=
      IsCompact.of_isClosed_subset isCompact_Icc hclosed (fun _x hx => hx.1)
    simpa [Z, Set.setOf_and] using hc
  obtain ⟨tau, htauZ, htaumin⟩ :=
    hZ_compact.exists_isMinOn hZ_nonempty continuousOn_id
  have htauI : tau ∈ Set.Icc (0 : ℝ) t := htauZ.1
  have hztau : z tau = R := htauZ.2
  have htau0 : 0 < tau := by
    rcases eq_or_lt_of_le htauI.1 with heq | hlt
    · subst tau
      linarith
    · exact hlt
  have hpast : ∀ s ∈ Set.Icc (0 : ℝ) tau, z s ≤ R := by
    intro s hs
    by_contra hsnot
    have hRlt : R < z s := lt_of_not_ge hsnot
    have hspos : 0 < s := by
      rcases eq_or_lt_of_le hs.1 with heq | hlt
      · subst s
        linarith
      · exact hlt
    have hcont0s : ContinuousOn z (Set.Icc (0 : ℝ) s) :=
      hcont.mono (fun _x hx =>
        ⟨hx.1, lt_of_le_of_lt (hx.2.trans hs.2 |>.trans htauI.2) htH⟩)
    have h0s : (0 : ℝ) ∈ Set.Icc (0 : ℝ) s :=
      ⟨le_rfl, hspos.le⟩
    have hss : s ∈ Set.Icc (0 : ℝ) s := ⟨hspos.le, le_rfl⟩
    have hRmem : R ∈ Set.Icc (z 0) (z s) :=
      ⟨le_of_lt hz0, le_of_lt hRlt⟩
    rcases isPreconnected_Icc.intermediate_value h0s hss hcont0s hRmem with
      ⟨q, hqI, hzq⟩
    have hqZ : q ∈ Z := by
      refine ⟨⟨hqI.1, le_trans hqI.2 (le_trans hs.2 htauI.2)⟩, hzq⟩
    have htauleq : tau ≤ q := htaumin hqZ
    have htaus : tau ≤ s := le_trans htauleq hqI.2
    have hseq : s = tau := le_antisymm hs.2 htaus
    subst s
    linarith
  have himprove := hstep tau htauI.1
    (lt_of_le_of_lt htauI.2 htH) hpast
  rw [hztau] at himprove
  linarith

/-- Scalar norm data on the open finite horizon `[0,H)`. -/
structure FiniteWeightedQuadraticDuhamelData (size : ℝ → ℝ) where
  horizon : ℝ
  theta : ℝ
  smoothingRate : ℝ
  delta : ℝ
  rate : ℝ
  linearConst : ℝ
  nonlinearConst : ℝ
  datum : ℝ
  radius : ℝ
  positivityRadius : ℝ
  horizon_pos : 0 < horizon
  theta_pos : 0 < theta
  theta_lt_one : theta < 1
  rate_pos : 0 < rate
  rate_lt_smoothingRate : rate < smoothingRate
  rate_le_delta : rate ≤ delta
  linearConst_nonneg : 0 ≤ linearConst
  nonlinearConst_nonneg : 0 ≤ nonlinearConst
  datum_nonneg : 0 ≤ datum
  radius_pos : 0 < radius
  positivityRadius_pos : 0 < positivityRadius
  radius_le_positivityRadius : radius ≤ positivityRadius
  size_nonneg : ∀ t, 0 ≤ t → t < horizon → 0 ≤ size t
  size_continuous : ContinuousOn size (Set.Ico (0 : ℝ) horizon)
  source_integrable : ∀ t, 0 ≤ t → t < horizon →
    IntervalIntegrable
      (fun s : ℝ =>
        (t - s) ^ (-theta) * Real.exp (-smoothingRate * (t - s)) *
          size s ^ 2) volume 0 t
  size_zero_le : size 0 ≤ linearConst * datum
  duhamel_bound : ∀ t, 0 ≤ t → t < horizon →
    (∀ s ∈ Set.Icc (0 : ℝ) t, size s ≤ positivityRadius) →
      size t ≤
        linearConst * Real.exp (-delta * t) * datum +
          nonlinearConst * (∫ s in (0 : ℝ)..t,
            (t - s) ^ (-theta) * Real.exp (-smoothingRate * (t - s)) *
              size s ^ 2)
  datum_small : linearConst * datum ≤ radius / 2
  quadratic_small :
    nonlinearConst * radius ^ 2 *
      reservedSingularKernelMass theta (smoothingRate - rate) ≤ radius / 4

/-- Exponential closure up to, but not including, the finite horizon. -/
theorem FiniteWeightedQuadraticDuhamelData.exponential_bound
    {size : ℝ → ℝ} (H : FiniteWeightedQuadraticDuhamelData size) :
    ∀ t, 0 ≤ t → t < H.horizon →
      size t ≤ H.radius * Real.exp (-H.rate * t) := by
  let z : ℝ → ℝ := fun t => Real.exp (H.rate * t) * size t
  let B : ℝ := H.radius / 2 + H.radius / 4
  have hB : B < H.radius := by
    dsimp [B]
    linarith [H.radius_pos]
  have hzcont : ContinuousOn z (Set.Ico (0 : ℝ) H.horizon) :=
    (Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).continuousOn.mul H.size_continuous
  have hz0 : z 0 < H.radius := by
    have hsmall0 : size 0 < H.radius :=
      lt_of_le_of_lt (H.size_zero_le.trans H.datum_small) (by
        linarith [H.radius_pos])
    simpa [z] using hsmall0
  have hstep : ∀ t, 0 ≤ t → t < H.horizon →
      (∀ s ∈ Set.Icc (0 : ℝ) t, z s ≤ H.radius) → z t ≤ B := by
    intro t ht htH hpast
    have hlocal : ∀ s ∈ Set.Icc (0 : ℝ) t,
        size s ≤ H.positivityRadius := by
      intro s hs
      have hweighted := hpast s hs
      have hsize : size s ≤ H.radius * Real.exp (-H.rate * s) := by
        have hexppos : 0 < Real.exp (H.rate * s) := Real.exp_pos _
        apply (mul_le_mul_iff_of_pos_left hexppos).mp
        rw [show Real.exp (H.rate * s) *
            (H.radius * Real.exp (-H.rate * s)) = H.radius by
          calc
            Real.exp (H.rate * s) *
                (H.radius * Real.exp (-H.rate * s)) =
              H.radius * (Real.exp (H.rate * s) *
                Real.exp (-H.rate * s)) := by ring
            _ = H.radius * Real.exp 0 := by
              rw [← Real.exp_add]
              congr 2
              ring
            _ = H.radius := by simp]
        exact hweighted
      have hexple : Real.exp (-H.rate * s) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (mul_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr H.rate_pos.le) hs.1)
      exact hsize.trans <| (mul_le_mul_of_nonneg_left hexple H.radius_pos.le).trans <| by
        simpa using H.radius_le_positivityRadius
    let source : ℝ → ℝ := fun s =>
      (t - s) ^ (-H.theta) *
        Real.exp (-H.smoothingRate * (t - s)) * size s ^ 2
    let major : ℝ → ℝ := fun s =>
      H.radius ^ 2 *
        ((t - s) ^ (-H.theta) *
          Real.exp (-H.smoothingRate * (t - s)) *
          Real.exp (-2 * H.rate * s))
    have hsourceInt : IntervalIntegrable source volume 0 t := by
      simpa [source] using H.source_integrable t ht htH
    have hbaseInt :=
      weighted_singular_quadratic_convolution_intervalIntegrable
        H.theta_pos H.theta_lt_one H.rate_pos
          H.rate_lt_smoothingRate ht
    have hmajorInt : IntervalIntegrable major volume 0 t := by
      simpa [major, mul_assoc] using hbaseInt.const_mul (H.radius ^ 2)
    have hpoint : ∀ s ∈ Set.Icc (0 : ℝ) t, source s ≤ major s := by
      intro s hs
      have hweighted := hpast s hs
      have hsize : size s ≤ H.radius * Real.exp (-H.rate * s) := by
        have hexppos : 0 < Real.exp (H.rate * s) := Real.exp_pos _
        apply (mul_le_mul_iff_of_pos_left hexppos).mp
        rw [show Real.exp (H.rate * s) *
            (H.radius * Real.exp (-H.rate * s)) = H.radius by
          calc
            Real.exp (H.rate * s) *
                (H.radius * Real.exp (-H.rate * s)) =
              H.radius * (Real.exp (H.rate * s) *
                Real.exp (-H.rate * s)) := by ring
            _ = H.radius * Real.exp 0 := by
              rw [← Real.exp_add]
              congr 2
              ring
            _ = H.radius := by simp]
        exact hweighted
      have hsize0 := H.size_nonneg s hs.1 (lt_of_le_of_lt hs.2 htH)
      have hsquare : size s ^ 2 ≤
          H.radius ^ 2 * Real.exp (-2 * H.rate * s) := by
        have hsq := mul_self_le_mul_self hsize0 hsize
        calc
          size s ^ 2 ≤ (H.radius * Real.exp (-H.rate * s)) ^ 2 := by
            simpa [pow_two] using hsq
          _ = H.radius ^ 2 * Real.exp (-2 * H.rate * s) := by
            rw [mul_pow, ← Real.exp_nat_mul]
            congr 2
            ring
      have hkernel0 : 0 ≤
          (t - s) ^ (-H.theta) *
            Real.exp (-H.smoothingRate * (t - s)) :=
        mul_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _)
          (Real.exp_nonneg _)
      dsimp [source, major]
      calc
        (t - s) ^ (-H.theta) *
            Real.exp (-H.smoothingRate * (t - s)) * size s ^ 2 ≤
          ((t - s) ^ (-H.theta) *
              Real.exp (-H.smoothingRate * (t - s))) *
            (H.radius ^ 2 * Real.exp (-2 * H.rate * s)) :=
              mul_le_mul_of_nonneg_left hsquare hkernel0
        _ = H.radius ^ 2 *
            ((t - s) ^ (-H.theta) *
                Real.exp (-H.smoothingRate * (t - s)) *
              Real.exp (-2 * H.rate * s)) := by ring
    have hintegral : (∫ s in (0 : ℝ)..t, source s) ≤
        ∫ s in (0 : ℝ)..t, major s :=
      intervalIntegral.integral_mono_on ht hsourceInt hmajorInt hpoint
    have hconv := weighted_singular_quadratic_convolution_le
      H.theta_pos H.theta_lt_one H.rate_pos
        H.rate_lt_smoothingRate ht
    have hmajorBound : (∫ s in (0 : ℝ)..t, major s) ≤
        H.radius ^ 2 * (Real.exp (-H.rate * t) *
          reservedSingularKernelMass H.theta
            (H.smoothingRate - H.rate)) := by
      dsimp [major]
      rw [intervalIntegral.integral_const_mul]
      exact mul_le_mul_of_nonneg_left hconv (sq_nonneg H.radius)
    have hsourceBound : (∫ s in (0 : ℝ)..t, source s) ≤
        H.radius ^ 2 * (Real.exp (-H.rate * t) *
          reservedSingularKernelMass H.theta
            (H.smoothingRate - H.rate)) := hintegral.trans hmajorBound
    have hlinearExp :
        Real.exp (H.rate * t) * Real.exp (-H.delta * t) ≤ 1 := by
      rw [← Real.exp_add, ← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have hcoef : H.rate - H.delta ≤ 0 := sub_nonpos.mpr H.rate_le_delta
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hcoef ht]
    have hduh := H.duhamel_bound t ht htH hlocal
    have hweightedDuh := mul_le_mul_of_nonneg_left hduh
      (Real.exp_nonneg (H.rate * t))
    dsimp [z, B]
    calc
      Real.exp (H.rate * t) * size t ≤
          Real.exp (H.rate * t) *
            (H.linearConst * Real.exp (-H.delta * t) * H.datum +
              H.nonlinearConst * (∫ s in (0 : ℝ)..t, source s)) := by
            simpa [source] using hweightedDuh
      _ ≤ H.linearConst * H.datum +
          H.nonlinearConst * H.radius ^ 2 *
            reservedSingularKernelMass H.theta
              (H.smoothingRate - H.rate) := by
        have hlin0 : 0 ≤ H.linearConst * H.datum :=
          mul_nonneg H.linearConst_nonneg H.datum_nonneg
        have hlinTerm :
            (Real.exp (H.rate * t) * Real.exp (-H.delta * t)) *
                (H.linearConst * H.datum) ≤ H.linearConst * H.datum := by
          simpa using mul_le_mul_of_nonneg_right hlinearExp hlin0
        have hsourceMul := mul_le_mul_of_nonneg_left
          hsourceBound H.nonlinearConst_nonneg
        have hsourceWeighted := mul_le_mul_of_nonneg_left
          hsourceMul (Real.exp_nonneg (H.rate * t))
        have hcancel : Real.exp (H.rate * t) * Real.exp (-H.rate * t) = 1 := by
          rw [← Real.exp_add]
          simp
        have hsourceTerm :
            Real.exp (H.rate * t) *
                (H.nonlinearConst * (∫ s in (0 : ℝ)..t, source s)) ≤
              H.nonlinearConst * H.radius ^ 2 *
                reservedSingularKernelMass H.theta
                  (H.smoothingRate - H.rate) := by
          calc
            _ ≤ Real.exp (H.rate * t) *
                (H.nonlinearConst * (H.radius ^ 2 *
                  (Real.exp (-H.rate * t) *
                    reservedSingularKernelMass H.theta
                      (H.smoothingRate - H.rate)))) := hsourceWeighted
            _ = (Real.exp (H.rate * t) * Real.exp (-H.rate * t)) *
                (H.nonlinearConst * H.radius ^ 2 *
                  reservedSingularKernelMass H.theta
                    (H.smoothingRate - H.rate)) := by ring
            _ = _ := by rw [hcancel, one_mul]
        calc
          Real.exp (H.rate * t) *
              (H.linearConst * Real.exp (-H.delta * t) * H.datum +
                H.nonlinearConst * (∫ s in (0 : ℝ)..t, source s)) =
            (Real.exp (H.rate * t) * Real.exp (-H.delta * t)) *
                (H.linearConst * H.datum) +
              Real.exp (H.rate * t) *
                (H.nonlinearConst * (∫ s in (0 : ℝ)..t, source s)) := by ring
          _ ≤ _ := add_le_add hlinTerm hsourceTerm
      _ ≤ H.radius / 2 + H.radius / 4 :=
        add_le_add H.datum_small H.quadratic_small
  have hzbound := weightedTail_bound_of_bootstrap_before
    H.radius_pos hB hzcont hz0 hstep
  intro t ht htH
  have hz := hzbound t ht htH
  dsimp [z] at hz
  have hexppos : 0 < Real.exp (H.rate * t) := Real.exp_pos _
  apply (mul_le_mul_iff_of_pos_left hexppos).mp
  rw [show Real.exp (H.rate * t) *
      (H.radius * Real.exp (-H.rate * t)) = H.radius by
    calc
      Real.exp (H.rate * t) *
          (H.radius * Real.exp (-H.rate * t)) =
        H.radius * (Real.exp (H.rate * t) *
          Real.exp (-H.rate * t)) := by ring
      _ = H.radius * Real.exp 0 := by
        rw [← Real.exp_add]
        congr 2
        ring
      _ = H.radius := by simp]
  exact hz

#print axioms weightedTail_bound_of_bootstrap_before
#print axioms FiniteWeightedQuadraticDuhamelData.exponential_bound

end

end ShenWork.Paper3
