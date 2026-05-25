/-
  ShenWork/Paper2/IntervalDomainLpMonotonicity.lean

  Finite-interval Lp monotonicity used by the Moser closure.

  On a finite-measure domain, L^q control implies L^p control for 1 < p ≤ q
  once the solution is nonnegative and the relevant powers are integrable.
  This file proves the concrete `[0,1]` intervalDomain version needed to turn
  the arithmetic Moser exponent chain into all exponents p > 1.
-/
import ShenWork.Paper2.IntervalDomainMoserClosure

open ShenWork.Paper2
open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainLpMonotonicity

lemma rpow_le_one_add_rpow_of_nonneg_of_le
    {a p q : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpq : p ≤ q) :
    a ^ p ≤ a ^ q + 1 := by
  by_cases ha_le_one : a ≤ 1
  · have hle_one : a ^ p ≤ 1 := Real.rpow_le_one ha ha_le_one hp
    have hq_nonneg : 0 ≤ a ^ q := Real.rpow_nonneg ha q
    linarith
  · have hone_le : 1 ≤ a := le_of_not_ge ha_le_one
    have hpq_pow : a ^ p ≤ a ^ q :=
      Real.rpow_le_rpow_of_exponent_le hone_le hpq
    linarith

/-- On `intervalDomain = [0,1]`, an L^q power bound gives an L^p power bound
for `1 < p ≤ q`, provided the solution is nonnegative and the two power traces
are interval-integrable on each time slice. -/
theorem intervalDomain_LpPowerBoundedBefore_mono_of_integrable_nonneg
    {u : ℝ → intervalDomain.Point → ℝ} {T p q : ℝ}
    (hp : 1 < p) (hpq : p ≤ q)
    (hu_nonneg :
      ∀ t, 0 < t → t < T → ∀ x : intervalDomain.Point, 0 ≤ u t x)
    (hp_int :
      ∀ t, 0 < t → t < T →
        IntervalIntegrable
          (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ p))
          MeasureTheory.volume 0 1)
    (hq_int :
      ∀ t, 0 < t → t < T →
        IntervalIntegrable
          (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ q))
          MeasureTheory.volume 0 1)
    (hq_bound : LpPowerBoundedBefore intervalDomain q T u) :
    LpPowerBoundedBefore intervalDomain p T u := by
  rcases hq_bound with ⟨Cq, hCq⟩
  refine ⟨Cq + 1, ?_⟩
  intro t ht0 htT
  have hp_nonneg : 0 ≤ p := le_trans zero_le_one hp.le
  have hpoint :
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ p) x ≤
          intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ q) x + 1 := by
    intro x hx
    simp only [intervalDomainLift, dif_pos hx]
    exact rpow_le_one_add_rpow_of_nonneg_of_le
      (hu_nonneg t ht0 htT ⟨x, hx⟩) hp_nonneg hpq
  have hmono :
      (∫ x in (0 : ℝ)..1,
          intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ p) x) ≤
        (∫ x in (0 : ℝ)..1,
          intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ q) x) + 1 := by
    have hle :=
      intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
        (hp_int t ht0 htT)
        ((hq_int t ht0 htT).add intervalIntegrable_const)
        hpoint
    have hadd :
        ∫ x in (0 : ℝ)..1,
            (intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ q) x + 1) =
          (∫ x in (0 : ℝ)..1,
            intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ q) x) + 1 := by
      rw [intervalIntegral.integral_add (hq_int t ht0 htT) intervalIntegrable_const,
        intervalIntegral.integral_const]
      norm_num [smul_eq_mul]
    simpa [hadd] using hle
  have hq_t : intervalDomain.integral (fun x => (u t x) ^ q) ≤ Cq :=
    hCq t ht0 htT
  have hq_t_int :
      (∫ x in (0 : ℝ)..1,
          intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ q) x) ≤ Cq := by
    simpa [intervalDomain, intervalDomainIntegral] using hq_t
  have htarget :
      (∫ x in (0 : ℝ)..1,
          intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ q) x) + 1 ≤
        Cq + 1 := by
    linarith
  change
    (∫ x in (0 : ℝ)..1,
        intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ p) x) ≤ Cq + 1
  exact le_trans hmono htarget

/-- Interior-nonnegative version of
`intervalDomain_LpPowerBoundedBefore_mono_of_integrable_nonneg`.

The interval integral is over `(0,1)` up to endpoints of measure zero, so the
pointwise comparison only needs nonnegativity on `intervalDomain.inside`. -/
theorem intervalDomain_LpPowerBoundedBefore_mono_of_integrable_inside_nonneg
    {u : ℝ → intervalDomain.Point → ℝ} {T p q : ℝ}
    (hp : 1 < p) (hpq : p ≤ q)
    (hu_nonneg :
      ∀ t, 0 < t → t < T →
        ∀ x : intervalDomain.Point, x ∈ intervalDomain.inside → 0 ≤ u t x)
    (hp_int :
      ∀ t, 0 < t → t < T →
        IntervalIntegrable
          (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ p))
          MeasureTheory.volume 0 1)
    (hq_int :
      ∀ t, 0 < t → t < T →
        IntervalIntegrable
          (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ q))
          MeasureTheory.volume 0 1)
    (hq_bound : LpPowerBoundedBefore intervalDomain q T u) :
    LpPowerBoundedBefore intervalDomain p T u := by
  rcases hq_bound with ⟨Cq, hCq⟩
  refine ⟨Cq + 1, ?_⟩
  intro t ht0 htT
  have hp_nonneg : 0 ≤ p := le_trans zero_le_one hp.le
  have hpoint :
      ∀ x ∈ Set.Ioo (0 : ℝ) 1,
        intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ p) x ≤
          intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ q) x + 1 := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    have hx_inside : (⟨x, hxIcc⟩ : intervalDomain.Point) ∈ intervalDomain.inside := by
      simpa [intervalDomain] using hx
    simp only [intervalDomainLift, dif_pos hxIcc]
    exact rpow_le_one_add_rpow_of_nonneg_of_le
      (hu_nonneg t ht0 htT ⟨x, hxIcc⟩ hx_inside) hp_nonneg hpq
  have hmono :
      (∫ x in (0 : ℝ)..1,
          intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ p) x) ≤
        (∫ x in (0 : ℝ)..1,
          intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ q) x) + 1 := by
    have hle :=
      intervalIntegral.integral_mono_on_of_le_Ioo
        (by norm_num : (0 : ℝ) ≤ 1)
        (hp_int t ht0 htT)
        ((hq_int t ht0 htT).add intervalIntegrable_const)
        hpoint
    have hadd :
        ∫ x in (0 : ℝ)..1,
            (intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ q) x + 1) =
          (∫ x in (0 : ℝ)..1,
            intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ q) x) + 1 := by
      rw [intervalIntegral.integral_add (hq_int t ht0 htT) intervalIntegrable_const,
        intervalIntegral.integral_const]
      norm_num [smul_eq_mul]
    simpa [hadd] using hle
  have hq_t : intervalDomain.integral (fun x => (u t x) ^ q) ≤ Cq :=
    hCq t ht0 htT
  have hq_t_int :
      (∫ x in (0 : ℝ)..1,
          intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ q) x) ≤ Cq := by
    simpa [intervalDomain, intervalDomainIntegral] using hq_t
  have htarget :
      (∫ x in (0 : ℝ)..1,
          intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ q) x) + 1 ≤
        Cq + 1 := by
    linarith
  change
    (∫ x in (0 : ℝ)..1,
        intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ p) x) ≤ Cq + 1
  exact le_trans hmono htarget

/-- Interval-domain Moser chain closure with the concrete finite-interval Lp
monotonicity lemma above.  The remaining hypotheses are the standard PDE
regularity facts: nonnegativity and integrability of all time-slice powers. -/
theorem intervalDomain_all_exponents_of_moser_iteration_chain
    {u : ℝ → intervalDomain.Point → ℝ} {T p0 rho : ℝ}
    (hrho : 0 < rho)
    (hbase : LpPowerBoundedBefore intervalDomain p0 T u)
    (hstep : ∀ p, p0 ≤ p →
      ∃ A > 0, ∃ K > 0, ∃ L_const,
        (∀ t, 0 < t → t < T →
          A * intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) ≤
          K * intervalDomain.integral (fun x => (u t x) ^ (p + rho)) + L_const) ∧
        (∀ eps > 0, ∃ Ceps, ∀ t, 0 < t → t < T →
          intervalDomain.integral (fun x => (u t x) ^ (p + rho)) ≤
            eps * intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
            Ceps))
    (hu_nonneg :
      ∀ t, 0 < t → t < T → ∀ x : intervalDomain.Point, 0 ≤ u t x)
    (hpow_int :
      ∀ pExp : ℝ, 1 < pExp → ∀ t, 0 < t → t < T →
        IntervalIntegrable
          (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ pExp))
          MeasureTheory.volume 0 1) :
    ∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u := by
  exact IntervalDomainMoserClosure.all_exponents_of_moser_iteration_chain
    hrho hbase hstep (fun {p q} hp hpq hq_bound =>
      intervalDomain_LpPowerBoundedBefore_mono_of_integrable_nonneg
        (p := p) (q := q) hp hpq hu_nonneg
        (hpow_int p hp)
        (hpow_int q (lt_of_lt_of_le hp hpq))
        hq_bound)

/-- Same Moser closure, with nonnegativity only required on the open interval
where the interval integral lives. -/
theorem intervalDomain_all_exponents_of_moser_iteration_chain_inside_nonneg
    {u : ℝ → intervalDomain.Point → ℝ} {T p0 rho : ℝ}
    (hrho : 0 < rho)
    (hbase : LpPowerBoundedBefore intervalDomain p0 T u)
    (hstep : ∀ p, p0 ≤ p →
      ∃ A > 0, ∃ K > 0, ∃ L_const,
        (∀ t, 0 < t → t < T →
          A * intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) ≤
          K * intervalDomain.integral (fun x => (u t x) ^ (p + rho)) + L_const) ∧
        (∀ eps > 0, ∃ Ceps, ∀ t, 0 < t → t < T →
          intervalDomain.integral (fun x => (u t x) ^ (p + rho)) ≤
            eps * intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
            Ceps))
    (hu_nonneg :
      ∀ t, 0 < t → t < T →
        ∀ x : intervalDomain.Point, x ∈ intervalDomain.inside → 0 ≤ u t x)
    (hpow_int :
      ∀ pExp : ℝ, 1 < pExp → ∀ t, 0 < t → t < T →
        IntervalIntegrable
          (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ pExp))
          MeasureTheory.volume 0 1) :
    ∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u := by
  exact IntervalDomainMoserClosure.all_exponents_of_moser_iteration_chain
    hrho hbase hstep (fun {p q} hp hpq hq_bound =>
      intervalDomain_LpPowerBoundedBefore_mono_of_integrable_inside_nonneg
        (p := p) (q := q) hp hpq hu_nonneg
        (hpow_int p hp)
        (hpow_int q (lt_of_lt_of_le hp hpq))
        hq_bound)

end ShenWork.Paper2.IntervalDomainLpMonotonicity

end
