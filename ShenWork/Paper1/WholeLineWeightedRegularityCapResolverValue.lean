import ShenWork.Paper1.WholeLineWeightedRegularityCap

open Filter MeasureTheory Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Cap-weighted frozen-resolver value estimate

The cap infrastructure previously controlled only the resolver gradient.
The flux-derivative recurrence also contains the resolver value itself.  The
same two-point weight ratio gives a cap-radius-independent Schur estimate for
that value term.
-/

/-- A positive weight whose two-point ratio grows at most like
`exp (k * |x-y|)` conjugates the Green value kernel to an `L²` operator
of norm at most `1 / (1-k)`. -/
theorem weighted_resolver_value_of_ratio_bound
    {a s : ℝ → ℝ} {k : ℝ}
    (hk1 : k < 1)
    (ha : Continuous a) (ha_pos : ∀ x, 0 < a x)
    (hratio : ∀ x y, a x ≤ Real.exp (k * |x - y|) * a y)
    (hs : IsCUnifBdd s)
    (hsource : Integrable (fun y => (a y * s y) ^ 2)) :
    Integrable (fun x => (a x * Psi s 1 1 x) ^ 2) ∧
      (∫ x : ℝ, (a x * Psi s 1 1 x) ^ 2) ≤
        (1 / (1 - k)) ^ 2 * ∫ y : ℝ, (a y * s y) ^ 2 := by
  let q : ℝ → ℝ := fun y => a y * s y
  let T : ℝ → ℝ := fun x => ∫ y : ℝ,
    laplaceMarkovKernel (1 - k) x y * |q y|
  have hgap : 0 < 1 - k := by linarith
  have hq_meas : Measurable q := (ha.mul hs.1).measurable
  have hT := laplaceMarkovKernel_l2_contraction hgap hq_meas hsource
  have hc : 0 ≤ 1 / (1 - k) := one_div_nonneg.mpr hgap.le
  have hpointKernel : ∀ x y,
      a x * ((1 / 2 : ℝ) * Real.exp (-|x - y|) * |s y|) ≤
        (1 / (1 - k)) *
          (laplaceMarkovKernel (1 - k) x y * |q y|) := by
    intro x y
    have hfac : 0 ≤
        (1 / 2 : ℝ) * Real.exp (-|x - y|) * |s y| := by positivity
    have hmul := mul_le_mul_of_nonneg_right (hratio x y) hfac
    have hay : |a y| = a y := abs_of_pos (ha_pos y)
    have hqabs : |q y| = a y * |s y| := by
      dsimp [q]
      rw [abs_mul, hay]
    calc
      a x * ((1 / 2 : ℝ) * Real.exp (-|x - y|) * |s y|) ≤
          (Real.exp (k * |x - y|) * a y) *
            ((1 / 2 : ℝ) * Real.exp (-|x - y|) * |s y|) := hmul
      _ = (1 / (1 - k)) *
          (laplaceMarkovKernel (1 - k) x y * |q y|) := by
        rw [hqabs]
        unfold laplaceMarkovKernel
        have hexp :
            Real.exp (k * |x - y|) * Real.exp (-|x - y|) =
              Real.exp (-(1 - k) * |x - y|) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [show Real.exp (k * |x - y|) * a y *
            ((1 / 2 : ℝ) * Real.exp (-|x - y|) * |s y|) =
            (1 / 2 : ℝ) *
              (Real.exp (k * |x - y|) * Real.exp (-|x - y|)) *
                (a y * |s y|) by ring,
          hexp]
        have hne : 1 - k ≠ 0 := ne_of_gt hgap
        field_simp [hne]
  have hpoint : ∀ x,
      |a x * Psi s 1 1 x| ≤ (1 / (1 - k)) * T x := by
    intro x
    have hsource_int : Integrable
        (fun y : ℝ => Real.exp (-|x - y|) * s y) := by
      simpa [Real.sqrt_one] using
        (Psi_kernel_integrable_of_isCUnifBdd (l := 1) one_pos hs x)
    have hsource_abs_int : Integrable
        (fun y : ℝ => Real.exp (-|x - y|) * |s y|) := by
      have h := hsource_int.norm
      simpa [Real.norm_eq_abs, abs_mul,
        abs_of_pos (Real.exp_pos _)] using h
    have habsIntegral :
        |∫ y : ℝ, Real.exp (-|x - y|) * s y| ≤
          ∫ y : ℝ, Real.exp (-|x - y|) * |s y| := by
      calc
        |∫ y : ℝ, Real.exp (-|x - y|) * s y| =
            ‖∫ y : ℝ, Real.exp (-|x - y|) * s y‖ :=
          (Real.norm_eq_abs _).symm
        _ ≤ ∫ y : ℝ, ‖Real.exp (-|x - y|) * s y‖ :=
          norm_integral_le_integral_norm _
        _ = ∫ y : ℝ, Real.exp (-|x - y|) * |s y| := by
          apply integral_congr_ae
          filter_upwards with y
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      |a x * Psi s 1 1 x| =
          a x * ((1 / 2 : ℝ) *
            |∫ y : ℝ, Real.exp (-|x - y|) * s y|) := by
        unfold Psi
        simp only [Real.sqrt_one, mul_one, neg_one_mul]
        rw [abs_mul, abs_of_pos (ha_pos x), abs_mul,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      _ ≤ a x * ((1 / 2 : ℝ) *
          ∫ y : ℝ, Real.exp (-|x - y|) * |s y|) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left habsIntegral (by norm_num))
          (ha_pos x).le
      _ = (a x * (1 / 2 : ℝ)) *
          ∫ y : ℝ, Real.exp (-|x - y|) * |s y| := by ring
      _ = ∫ y : ℝ,
          (a x * (1 / 2 : ℝ)) *
            (Real.exp (-|x - y|) * |s y|) := by
        rw [integral_const_mul]
      _ = ∫ y : ℝ,
          a x * ((1 / 2 : ℝ) * Real.exp (-|x - y|) * |s y|) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by ring
      _ ≤ ∫ y : ℝ, (1 / (1 - k)) *
          (laplaceMarkovKernel (1 - k) x y * |q y|) := by
        apply integral_mono
        · simpa [mul_assoc] using
            (hsource_abs_int.const_mul (1 / 2)).const_mul (a x)
        · exact (laplaceMarkovKernel_mul_abs_integrable
            hgap hq_meas hsource x).const_mul (1 / (1 - k))
        · exact hpointKernel x
      _ = (1 / (1 - k)) * T x := by
        dsimp [T]
        rw [integral_const_mul]
  have hvalueCont : Continuous (fun x => Psi s 1 1 x) :=
    Psi_continuous one_pos one_pos hs
  have hdom : Integrable (fun x => (1 / (1 - k)) ^ 2 * T x ^ 2) :=
    hT.1.const_mul _
  have hpointSq : ∀ x,
      (a x * Psi s 1 1 x) ^ 2 ≤
        (1 / (1 - k)) ^ 2 * T x ^ 2 := by
    intro x
    have hT0 : 0 ≤ T x := by
      dsimp [T]
      exact integral_nonneg fun y => mul_nonneg
        (laplaceMarkovKernel_nonneg hgap.le x y) (abs_nonneg _)
    have hsquare := (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg hc hT0)).mpr (hpoint x)
    simpa [sq_abs, mul_pow] using hsquare
  have hout : Integrable (fun x => (a x * Psi s 1 1 x) ^ 2) := by
    refine Integrable.mono' hdom
      ((ha.mul hvalueCont).pow 2).aestronglyMeasurable ?_
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpointSq x
  refine ⟨hout, ?_⟩
  calc
    (∫ x : ℝ, (a x * Psi s 1 1 x) ^ 2) ≤
        ∫ x : ℝ, (1 / (1 - k)) ^ 2 * T x ^ 2 :=
      integral_mono hout hdom hpointSq
    _ = (1 / (1 - k)) ^ 2 * ∫ x : ℝ, T x ^ 2 := by
      rw [integral_const_mul]
    _ ≤ (1 / (1 - k)) ^ 2 * ∫ y : ℝ, (a y * s y) ^ 2 :=
      mul_le_mul_of_nonneg_left hT.2 (sq_nonneg _)

/-- Cap-weighted `L²` control of a frozen elliptic value difference.  The
constant is uniform in the cap radius `R`. -/
theorem capWeight_frozenElliptic_value_difference_l2_bounded
    (p : CMParams) {M eta R : ℝ}
    (hM : 0 ≤ M) (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    {u1 u2 : ℝ → ℝ}
    (hu1 : IsCUnifBdd u1) (hu2 : IsCUnifBdd u2)
    (hu1_mem : ∀ x, u1 x ∈ Set.Icc (0 : ℝ) M)
    (hu2_mem : ∀ x, u2 x ∈ Set.Icc (0 : ℝ) M)
    (hclose : Integrable (fun x =>
      capWeight eta R x * |u2 x - u1 x| ^ 2)) :
    Integrable (fun x => capWeight eta R x *
        |frozenElliptic p u2 x - frozenElliptic p u1 x| ^ 2) ∧
      (∫ x : ℝ, capWeight eta R x *
          |frozenElliptic p u2 x - frozenElliptic p u1 x| ^ 2) ≤
        ((1 / (1 - eta)) * (p.γ * M ^ (p.γ - 1))) ^ 2 *
          ∫ x : ℝ, capWeight eta R x * |u2 x - u1 x| ^ 2 := by
  have hclose' : Integrable (fun x =>
      (capWeightSqrt eta R x * (u2 x - u1 x)) ^ 2) := by
    refine hclose.congr (Eventually.of_forall fun x => ?_)
    change capWeight eta R x * |u2 x - u1 x| ^ 2 =
      (capWeightSqrt eta R x * (u2 x - u1 x)) ^ 2
    exact (capWeightSqrt_mul_sq_eq eta R x (u2 x - u1 x)).symm
  let s : ℝ → ℝ := fun x => u2 x ^ p.γ - u1 x ^ p.γ
  let L : ℝ := p.γ * M ^ (p.γ - 1)
  have hs : IsCUnifBdd s := by
    dsimp [s]
    exact rpow_difference_isCUnifBdd p.hγ hu1 hu2 hu1_mem hu2_mem
  have hL0 : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg (zero_le_one.trans p.hγ)
      (Real.rpow_nonneg hM _)
  have hsourcePoint : ∀ x,
      (capWeightSqrt eta R x * s x) ^ 2 ≤
        L ^ 2 * (capWeightSqrt eta R x * (u2 x - u1 x)) ^ 2 := by
    intro x
    have hp := abs_rpow_sub_rpow_le_of_mem_Icc
      p.hγ hM (hu2_mem x) (hu1_mem x)
    have ha0 : 0 ≤ capWeightSqrt eta R x :=
      (capWeightSqrt_pos eta R x).le
    have habs : |capWeightSqrt eta R x * s x| ≤
        L * |capWeightSqrt eta R x * (u2 x - u1 x)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha0]
      dsimp [s, L]
      calc
        capWeightSqrt eta R x * |u2 x ^ p.γ - u1 x ^ p.γ| ≤
            capWeightSqrt eta R x *
              (p.γ * M ^ (p.γ - 1) * |u2 x - u1 x|) :=
          mul_le_mul_of_nonneg_left hp ha0
        _ = p.γ * M ^ (p.γ - 1) *
            (capWeightSqrt eta R x * |u2 x - u1 x|) := by ring
    have hsq := (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg hL0 (abs_nonneg _))).2 habs
    simpa [sq_abs, mul_pow] using hsq
  have hsourceDom : Integrable (fun x =>
      L ^ 2 * (capWeightSqrt eta R x * (u2 x - u1 x)) ^ 2) :=
    hclose'.const_mul _
  have hsourceInt : Integrable (fun x =>
      (capWeightSqrt eta R x * s x) ^ 2) := by
    refine Integrable.mono' hsourceDom
      (((capWeightSqrt_continuous eta R).mul hs.1).pow 2).aestronglyMeasurable ?_
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hsourcePoint x
  have hsourceBound :
      (∫ x : ℝ, (capWeightSqrt eta R x * s x) ^ 2) ≤
        L ^ 2 * ∫ x : ℝ,
          (capWeightSqrt eta R x * (u2 x - u1 x)) ^ 2 := by
    calc
      (∫ x : ℝ, (capWeightSqrt eta R x * s x) ^ 2) ≤
          ∫ x : ℝ,
            L ^ 2 * (capWeightSqrt eta R x * (u2 x - u1 x)) ^ 2 :=
        integral_mono hsourceInt hsourceDom hsourcePoint
      _ = L ^ 2 * ∫ x : ℝ,
          (capWeightSqrt eta R x * (u2 x - u1 x)) ^ 2 := by
        rw [integral_const_mul]
  have hvalue := weighted_resolver_value_of_ratio_bound
    heta1
    (capWeightSqrt_continuous eta R)
    (capWeightSqrt_pos eta R)
    (capWeightSqrt_le_exp_abs_mul heta0 R)
    hs hsourceInt
  have hpow1 : IsCUnifBdd (fun x => u1 x ^ p.γ) :=
    rpow_cunif_bdd_of_nonneg p hu1 (fun x => (hu1_mem x).1)
  have hpow2 : IsCUnifBdd (fun x => u2 x ^ p.γ) :=
    rpow_cunif_bdd_of_nonneg p hu2 (fun x => (hu2_mem x).1)
  have hdiff : ∀ x,
      frozenElliptic p u2 x - frozenElliptic p u1 x = Psi s 1 1 x := by
    intro x
    dsimp [s]
    unfold frozenElliptic
    exact (Psi_sub x
      (by simpa [Real.sqrt_one] using
        (Psi_kernel_integrable_of_isCUnifBdd one_pos hpow2 x))
      (by simpa [Real.sqrt_one] using
        (Psi_kernel_integrable_of_isCUnifBdd one_pos hpow1 x))).symm
  have hout : Integrable (fun x => capWeight eta R x *
      |frozenElliptic p u2 x - frozenElliptic p u1 x| ^ 2) := by
    refine hvalue.1.congr (Eventually.of_forall fun x => ?_)
    change (capWeightSqrt eta R x * Psi s 1 1 x) ^ 2 =
      capWeight eta R x *
        |frozenElliptic p u2 x - frozenElliptic p u1 x| ^ 2
    rw [← hdiff x]
    exact capWeightSqrt_mul_sq_eq eta R x
      (frozenElliptic p u2 x - frozenElliptic p u1 x)
  refine ⟨hout, ?_⟩
  calc
    (∫ x : ℝ, capWeight eta R x *
        |frozenElliptic p u2 x - frozenElliptic p u1 x| ^ 2) =
      ∫ x : ℝ,
        (capWeightSqrt eta R x * Psi s 1 1 x) ^ 2 := by
      apply integral_congr_ae
      filter_upwards with x
      rw [← hdiff x, capWeightSqrt_mul_sq_eq eta R x
        (frozenElliptic p u2 x - frozenElliptic p u1 x)]
    _ ≤ (1 / (1 - eta)) ^ 2 *
        ∫ x : ℝ, (capWeightSqrt eta R x * s x) ^ 2 := hvalue.2
    _ ≤ (1 / (1 - eta)) ^ 2 *
        (L ^ 2 * ∫ x : ℝ,
          (capWeightSqrt eta R x * (u2 x - u1 x)) ^ 2) := by
      apply mul_le_mul_of_nonneg_left hsourceBound
      exact sq_nonneg _
    _ = ((1 / (1 - eta)) * (p.γ * M ^ (p.γ - 1))) ^ 2 *
        ∫ x : ℝ, capWeight eta R x * |u2 x - u1 x| ^ 2 := by
      dsimp [L]
      rw [show (∫ x : ℝ,
          (capWeightSqrt eta R x * (u2 x - u1 x)) ^ 2) =
          ∫ x : ℝ, capWeight eta R x * |u2 x - u1 x| ^ 2 by
        apply integral_congr_ae
        filter_upwards with x
        rw [capWeightSqrt_mul_sq_eq eta R x (u2 x - u1 x)]]
      ring

end ShenWork.Paper1

#print axioms ShenWork.Paper1.weighted_resolver_value_of_ratio_bound
#print axioms
  ShenWork.Paper1.capWeight_frozenElliptic_value_difference_l2_bounded
