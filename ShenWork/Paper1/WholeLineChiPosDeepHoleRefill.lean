import ShenWork.Paper1.ReactionPlateauCoercive
import ShenWork.Paper1.LeftFloorProducer
import ShenWork.Paper1.NoSmallLeftPocket
import ShenWork.Paper1.WaveFrozenEllipticDep

/-!
# Deep-hole refill for the normalized positive-sensitivity equation

For the normalized `m = γ = α = 1` equation, expansion at a spatial minimum
gives the local growth coefficient

`g(q,V) = 1 - χ V + (χ - 1) q`.

If `q ≤ ε` throughout `[x-K,x+K]`, `0 ≤ q ≤ M` globally, and the Green-kernel
tail satisfies `M exp(-K) ≤ ε`, the normalized resolver obeys

`Psi q 1 1 x ≤ ε + M exp(-K) ≤ 2ε`.

Consequently, under the explicit budget
`(2χ + |χ-1|) ε ≤ 1/2`, one has `g(q,V) ≥ 1/2`.
At a spatial minimum, diffusion is nonnegative and drift vanishes, so
`q_t ≥ q/2`: a sufficiently wide deep hole is self-refilling.

The final two bridge lemmas reuse the landed positive-plateau reaction
coercivity and the no-small-pocket/left-floor mechanism.  They do not turn a
time slice into a stationary profile; their hypotheses keep that distinction
explicit.
-/

open MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-- The normalized deep-hole growth coefficient after expanding the
chemotactic flux at `m = γ = α = 1`. -/
def deepHoleGrowthCoefficient (chi q V : ℝ) : ℝ :=
  1 - chi * V + (chi - 1) * q

/-- A local ceiling on a symmetric interval and a global ceiling give the
sharp elementary Green-kernel estimate
`Psi q 1 1 x ≤ ε + M exp(-K)`. -/
theorem Psi_le_of_symmetric_deepHole
    {q : ℝ → ℝ} (hq : IsCUnifBdd q)
    (_hq_nonneg : ∀ y, 0 ≤ q y)
    {M eps K x : ℝ}
    (hM : 0 ≤ M) (heps : 0 ≤ eps) (hK : 0 ≤ K)
    (hglobal : ∀ y, q y ≤ M)
    (hhole : ∀ y ∈ Set.Icc (x - K) (x + K), q y ≤ eps) :
    Psi q 1 1 x ≤ eps + M * Real.exp (-K) := by
  let ker : ℝ → ℝ := fun y => Real.exp (-|x - y|)
  let left : Set ℝ := Set.Iic (x - K)
  let right : Set ℝ := Set.Ici (x + K)
  let rhs : ℝ → ℝ := fun y =>
    ker y * eps +
      left.indicator (fun z => ker z * M) y +
      right.indicator (fun z => ker z * M) y
  have hker_int : Integrable ker := by
    simpa only [ker] using
      ShenWork.Paper1.exp_neg_abs_sub_integrable x
  have hsource_int : Integrable (fun y => ker y * q y) := by
    have hraw :=
      Psi_kernel_integrable_of_isCUnifBdd
        (u := q) (l := 1) one_pos hq x
    simpa only [ker, Real.sqrt_one, one_mul, neg_mul] using hraw
  have hnear_int : Integrable (fun y => ker y * eps) :=
    hker_int.mul_const eps
  have hleft_int :
      Integrable (left.indicator (fun y => ker y * M)) :=
    (hker_int.mul_const M).indicator measurableSet_Iic
  have hright_int :
      Integrable (right.indicator (fun y => ker y * M)) :=
    (hker_int.mul_const M).indicator measurableSet_Ici
  have hrhs_int : Integrable rhs := by
    exact (hnear_int.add hleft_int).add hright_int
  have hpoint : ∀ y, ker y * q y ≤ rhs y := by
    intro y
    have hker0 : 0 ≤ ker y := Real.exp_nonneg _
    have hnear0 : 0 ≤ ker y * eps := mul_nonneg hker0 heps
    by_cases hy : y ∈ Set.Icc (x - K) (x + K)
    · have hlocal :=
        mul_le_mul_of_nonneg_left (hhole y hy) hker0
      have hl0 :
          0 ≤ left.indicator (fun z => ker z * M) y := by
        simp only [Set.indicator_apply]
        split <;> positivity
      have hr0 :
          0 ≤ right.indicator (fun z => ker z * M) y := by
        simp only [Set.indicator_apply]
        split <;> positivity
      dsimp only [rhs]
      linarith
    · have hout : y < x - K ∨ x + K < y := by
        simpa only [Set.mem_Icc, not_and_or, not_le] using hy
      rcases hout with hyleft | hyright
      · have hmem : y ∈ left := by
          exact le_of_lt hyleft
        have hglobal_mul :=
          mul_le_mul_of_nonneg_left (hglobal y) hker0
        have hr0 :
            0 ≤ right.indicator (fun z => ker z * M) y := by
          simp only [Set.indicator_apply]
          split <;> positivity
        dsimp only [rhs]
        rw [Set.indicator_of_mem hmem]
        linarith
      · have hmem : y ∈ right := by
          exact le_of_lt hyright
        have hglobal_mul :=
          mul_le_mul_of_nonneg_left (hglobal y) hker0
        have hl0 :
            0 ≤ left.indicator (fun z => ker z * M) y := by
          simp only [Set.indicator_apply]
          split <;> positivity
        dsimp only [rhs]
        rw [Set.indicator_of_mem hmem]
        linarith
  have hintegral :
      (∫ y, ker y * q y) ≤ ∫ y, rhs y :=
    MeasureTheory.integral_mono hsource_int hrhs_int hpoint
  have hleft_tail :
      (∫ y in Set.Iic (x - K), ker y) ≤ Real.exp (-K) := by
    have hraw :=
      ShenWork.Paper1.exp_neg_abs_sub_Iic_le
        (x := x) (R' := K - x) (by linarith)
    have hcut : -(K - x) = x - K := by ring
    rw [hcut] at hraw
    have hexp :
        Real.exp (-x) * Real.exp (x - K) =
          Real.exp (-K) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp] at hraw
    simpa only [ker] using hraw
  have hright_tail :
      (∫ y in Set.Ici (x + K), ker y) ≤ Real.exp (-K) := by
    have hraw :=
      ShenWork.Paper1.exp_neg_abs_sub_Ici_le
        (x := x) (R' := x + K) (by linarith)
    have hexp :
        Real.exp x * Real.exp (-(x + K)) =
          Real.exp (-K) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simpa only [ker, hexp] using hraw
  have hrhs_eq :
      (∫ y, rhs y) =
        (∫ y, ker y) * eps +
          (∫ y in Set.Iic (x - K), ker y) * M +
          (∫ y in Set.Ici (x + K), ker y) * M := by
    change
      (∫ y,
        ((fun z => ker z * eps) +
          left.indicator (fun z => ker z * M) +
          right.indicator (fun z => ker z * M)) y) = _
    calc
      (∫ y,
          ((fun z => ker z * eps) +
            left.indicator (fun z => ker z * M) +
            right.indicator (fun z => ker z * M)) y) =
          (∫ y,
            ((fun z => ker z * eps) +
              left.indicator (fun z => ker z * M)) y) +
            ∫ y, right.indicator (fun z => ker z * M) y :=
        MeasureTheory.integral_add
          (hnear_int.add hleft_int) hright_int
      _ =
          ((∫ y, ker y * eps) +
            ∫ y, left.indicator (fun z => ker z * M) y) +
            ∫ y, right.indicator (fun z => ker z * M) y := by
        exact congrArg
          (fun value =>
            value + ∫ y, right.indicator (fun z => ker z * M) y)
          (MeasureTheory.integral_add hnear_int hleft_int)
      _ = _ := by
        rw [MeasureTheory.integral_mul_const,
          MeasureTheory.integral_indicator measurableSet_Iic,
          MeasureTheory.integral_mul_const,
          MeasureTheory.integral_indicator measurableSet_Ici,
          MeasureTheory.integral_mul_const]
  have hrhs_bound :
      (∫ y, rhs y) ≤ 2 * eps + 2 * M * Real.exp (-K) := by
    rw [hrhs_eq,
      show (∫ y, ker y) = 2 by
        simpa only [ker] using
          ShenWork.Paper1.exp_neg_abs_sub_integral_eq x]
    have hleft_scaled :=
      mul_le_mul_of_nonneg_right hleft_tail hM
    have hright_scaled :=
      mul_le_mul_of_nonneg_right hright_tail hM
    nlinarith
  have hsource_bound :
      (∫ y, ker y * q y) ≤
        2 * eps + 2 * M * Real.exp (-K) :=
    hintegral.trans hrhs_bound
  unfold Psi
  simpa only [Real.sqrt_one, one_mul, neg_mul, ker] using
    (show
      (1 / (2 * 1) : ℝ) * (∫ y, ker y * q y) ≤
        eps + M * Real.exp (-K) by
      nlinarith)

/-- If the kernel tail budget is at most the local ceiling, then the resolver
at the center of the deep hole is at most `2ε`. -/
theorem Psi_le_two_eps_of_symmetric_deepHole
    {q : ℝ → ℝ} (hq : IsCUnifBdd q)
    (hq_nonneg : ∀ y, 0 ≤ q y)
    {M eps K x : ℝ}
    (hM : 0 ≤ M) (heps : 0 ≤ eps) (hK : 0 ≤ K)
    (hglobal : ∀ y, q y ≤ M)
    (hhole : ∀ y ∈ Set.Icc (x - K) (x + K), q y ≤ eps)
    (htail : M * Real.exp (-K) ≤ eps) :
    Psi q 1 1 x ≤ 2 * eps := by
  have hresolver :=
    ShenWork.Paper1.Psi_le_of_symmetric_deepHole
      hq hq_nonneg hM heps hK hglobal hhole
  linarith

/-- The explicit deep-hole budget forces the normalized growth coefficient
to be at least `1/2`. -/
theorem deepHoleGrowthCoefficient_ge_half
    {chi q V eps : ℝ}
    (hchi : 0 ≤ chi) (hq0 : 0 ≤ q) (hqeps : q ≤ eps)
    (hVeps : V ≤ 2 * eps)
    (hbudget : (2 * chi + |chi - 1|) * eps ≤ 1 / 2) :
    1 / 2 ≤ deepHoleGrowthCoefficient chi q V := by
  have heps : 0 ≤ eps := hq0.trans hqeps
  have hchem :
      chi * V ≤ 2 * chi * eps := by
    have := mul_le_mul_of_nonneg_left hVeps hchi
    nlinarith
  have habsq : |q| ≤ eps := by
    rw [abs_of_nonneg hq0]
    exact hqeps
  have hamplitude :
      |(chi - 1) * q| ≤ |chi - 1| * eps := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left habsq (abs_nonneg _)
  have hamplitude_lower :=
    (abs_le.mp hamplitude).1
  unfold deepHoleGrowthCoefficient
  nlinarith

/-- At a spatial minimum, the normalized deep-hole equation has the KPP refill
rate `q_t ≥ q/2`.  The hypotheses state the expanded PDE exactly. -/
theorem deepHole_minimum_refill_rate
    {chi q V eps b qx qxx qt : ℝ}
    (hchi : 0 ≤ chi) (hq0 : 0 ≤ q) (hqeps : q ≤ eps)
    (hVeps : V ≤ 2 * eps)
    (hbudget : (2 * chi + |chi - 1|) * eps ≤ 1 / 2)
    (hqx : qx = 0) (hqxx : 0 ≤ qxx)
    (hpde : qt =
      qxx + b * qx + q * deepHoleGrowthCoefficient chi q V) :
    q / 2 ≤ qt := by
  have hg :=
    ShenWork.Paper1.deepHoleGrowthCoefficient_ge_half
      hchi hq0 hqeps hVeps hbudget
  have hqg : q / 2 ≤ q * deepHoleGrowthCoefficient chi q V := by
    nlinarith [mul_le_mul_of_nonneg_left hg hq0]
  rw [hqx, mul_zero, add_zero] at hpde
  nlinarith

/-- Complete deep-hole certificate: a symmetric local ceiling, an exponentially
small Green tail, and a spatial minimum imply `q_t ≥ q/2`. -/
theorem deepHole_minimum_refill_of_local_ceiling
    {q : ℝ → ℝ} (hq : IsCUnifBdd q)
    (hq_nonneg : ∀ y, 0 ≤ q y)
    {chi M eps K x b qx qxx qt : ℝ}
    (hchi : 0 ≤ chi)
    (hM : 0 ≤ M) (heps : 0 ≤ eps) (hK : 0 ≤ K)
    (hglobal : ∀ y, q y ≤ M)
    (hhole : ∀ y ∈ Set.Icc (x - K) (x + K), q y ≤ eps)
    (htail : M * Real.exp (-K) ≤ eps)
    (hbudget : (2 * chi + |chi - 1|) * eps ≤ 1 / 2)
    (hqx : qx = 0) (hqxx : 0 ≤ qxx)
    (hpde : qt =
      qxx + b * qx +
        q x * deepHoleGrowthCoefficient chi (q x) (Psi q 1 1 x)) :
    q x / 2 ≤ qt := by
  have hxmem : x ∈ Set.Icc (x - K) (x + K) := by
    constructor <;> linarith
  have hqxeps := hhole x hxmem
  have hVeps :=
    ShenWork.Paper1.Psi_le_two_eps_of_symmetric_deepHole
      hq hq_nonneg hM heps hK hglobal hhole htail
  exact ShenWork.Paper1.deepHole_minimum_refill_rate
    hchi (hq_nonneg x) hqxeps hVeps hbudget hqx hqxx hpde

/-- Once refill has returned a profile to a fixed positive plateau, reuse the
landed reaction coercivity estimate there. -/
theorem deepHole_rejoined_plateau_coercive
    (u alpha a b : ℝ) (halpha : 1 ≤ alpha) (ha : 0 < a)
    (hau : a ≤ u) (hub : u ≤ b) (ha1 : a ≤ 1) :
    u * (u - 1) * (u ^ alpha - 1) ≥
      alpha * a ^ alpha * (u - 1) ^ 2 := by
  exact ShenWork.Paper1.reaction_plateau_coercive
    u alpha a b halpha ha hau hub ha1

/-- The landed maximum-principle brick excludes a small interior pocket under
the explicit stationary small-density coercivity hypotheses. -/
theorem deepHole_noSmallInteriorPocket
    {U B Q : ℝ → ℝ} {eta b0 q0 kappa eps z : ℝ}
    (hUdiff : Differentiable ℝ U)
    (hUdiff2 : Differentiable ℝ (deriv U))
    (hcoer : SmallDensityCoercive U B Q eta b0 q0)
    (hkappa_pos : 0 < kappa) (hkappa_b0 : kappa < b0)
    (heps_pos : 0 < eps)
    (hUz_pos : 0 < U z) (hUz_le : U z ≤ eta)
    (hmin :
      IsLocalMin (fun x => U x + eps * Real.exp (-kappa * x)) z) :
    False := by
  exact ShenWork.Paper1.noSmallInteriorMin
    hUdiff hUdiff2 hcoer hkappa_pos hkappa_b0 heps_pos
      hUz_pos hUz_le hmin

/-- The complete landed producer/no-small-pocket mechanism turns a stationary
small-density coercive profile with an anchor into a strict left floor. -/
theorem deepHole_static_leftFloor
    {U B Q : ℝ → ℝ} {eta b0 q0 A : ℝ}
    (hUcont : Continuous U)
    (hUdiff : Differentiable ℝ U)
    (hUdiff2 : Differentiable ℝ (deriv U))
    (hUpos : ∀ x, 0 < U x)
    (hcoer : SmallDensityCoercive U B Q eta b0 q0)
    (hanchor : eta < U A) :
    StrictlyPositiveAtLeft U := by
  exact ShenWork.Paper1.strictlyPositiveAtLeft_of_coercive_anchor
    hUcont hUdiff hUdiff2 hUpos hcoer hanchor

section AxiomAudit

#print axioms Psi_le_of_symmetric_deepHole
#print axioms Psi_le_two_eps_of_symmetric_deepHole
#print axioms deepHoleGrowthCoefficient_ge_half
#print axioms deepHole_minimum_refill_rate
#print axioms deepHole_minimum_refill_of_local_ceiling
#print axioms deepHole_rejoined_plateau_coercive
#print axioms deepHole_noSmallInteriorPocket
#print axioms deepHole_static_leftFloor

end AxiomAudit

end ShenWork.Paper1
