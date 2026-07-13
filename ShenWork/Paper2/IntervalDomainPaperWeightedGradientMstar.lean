import ShenWork.Paper2.IntervalDomainTheorem13CriticalConstants
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Paper-exact weighted gradient constant on the interval

This file proves Proposition 2.2 with the literal `M*` from (1.18).  The
earlier elementary interval estimate has a different coefficient and cannot
be used in the critical thresholds (1.24)--(1.25).
-/

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainPaperWeightedGradientMstar

open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainTheorem13CriticalConstants

/-- The first Young split in (2.37), with the exact coefficient that survives
after absorbing half of the weighted gradient integral. -/
theorem weighted_split_young
    {q X Y : ℝ} (hq : 1 < q) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    (1 / (q - 1)) * X ^ ((q - 1) / q) * Y ≤
      (1 / 2 : ℝ) * X +
        ((2 : ℝ) ^ (q - 1) / ((q - 1) * q ^ q)) * Y ^ q := by
  let pH : ℝ := q / (q - 1)
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hqm1 : 0 < q - 1 := sub_pos.mpr hq
  have hpH : 1 < pH := by
    dsimp [pH]
    rw [one_lt_div hqm1]
    linarith
  have hpH0 : 0 < pH := zero_lt_one.trans hpH
  have hconj : pH.HolderConjugate q := by
    rw [Real.holderConjugate_iff]
    refine ⟨hpH, ?_⟩
    dsimp [pH]
    field_simp [hq0.ne', hqm1.ne']
    ring
  let scale : ℝ := ((1 / 2 : ℝ) * pH) ^ (1 / pH)
  have hscale : 0 < scale := by
    dsimp [scale]
    exact Real.rpow_pos_of_pos (mul_pos (by norm_num) hpH0) _
  have ha0 : 0 ≤ scale * X ^ ((q - 1) / q) :=
    mul_nonneg hscale.le (Real.rpow_nonneg hX _)
  have hb0 : 0 ≤ Y / ((q - 1) * scale) :=
    div_nonneg hY (mul_nonneg hqm1.le hscale.le)
  have hy := Real.young_inequality_of_nonneg
    (a := scale * X ^ ((q - 1) / q))
    (b := Y / ((q - 1) * scale)) ha0 hb0 hconj
  have hprod :
      (scale * X ^ ((q - 1) / q)) * (Y / ((q - 1) * scale)) =
        (1 / (q - 1)) * X ^ ((q - 1) / q) * Y := by
    field_simp [hqm1.ne', hscale.ne']
  have hscalePH : scale ^ pH = (1 / 2 : ℝ) * pH := by
    dsimp [scale]
    rw [← Real.rpow_mul (mul_pos (by norm_num) hpH0).le]
    have hone : (1 / pH) * pH = 1 := by field_simp [hpH0.ne']
    rw [hone, Real.rpow_one]
  have hXpow : (X ^ ((q - 1) / q)) ^ pH = X := by
    rw [← Real.rpow_mul hX]
    dsimp [pH]
    have he : ((q - 1) / q) * (q / (q - 1)) = 1 := by
      field_simp [hq0.ne', hqm1.ne']
    rw [he, Real.rpow_one]
  have htermA :
      (scale * X ^ ((q - 1) / q)) ^ pH / pH = (1 / 2 : ℝ) * X := by
    rw [Real.mul_rpow hscale.le (Real.rpow_nonneg hX _), hscalePH, hXpow]
    field_simp [hpH0.ne']
  have hscaleQ :
      scale ^ q = (q / (2 * (q - 1))) ^ (q - 1) := by
    have hbase : (1 / 2 : ℝ) * pH = q / (2 * (q - 1)) := by
      dsimp [pH]
      field_simp [hqm1.ne']
    have hexp : 1 / pH = (q - 1) / q := by
      dsimp [pH]
      field_simp [hq0.ne', hqm1.ne']
    dsimp [scale]
    rw [hbase, hexp, ← Real.rpow_mul (by positivity : 0 ≤ q / (2 * (q - 1)))]
    congr 1
    field_simp [hq0.ne']
  have htermB :
      (Y / ((q - 1) * scale)) ^ q / q =
        ((2 : ℝ) ^ (q - 1) / ((q - 1) * q ^ q)) * Y ^ q := by
    rw [Real.div_rpow hY (mul_nonneg hqm1.le hscale.le),
      Real.mul_rpow hqm1.le hscale.le, hscaleQ]
    rw [Real.div_rpow hq0.le (by positivity : 0 ≤ 2 * (q - 1))]
    have hqsplit : q = (q - 1) + 1 := by ring
    have hqpow : q ^ q = q ^ (q - 1) * q := by
      calc
        q ^ q = q ^ ((q - 1) + 1) := by congr 1 <;> ring
        _ = q ^ (q - 1) * q ^ (1 : ℝ) := Real.rpow_add hq0 _ _
        _ = q ^ (q - 1) * q := by rw [Real.rpow_one]
    have hqmpow : (q - 1) ^ q = (q - 1) ^ (q - 1) * (q - 1) := by
      calc
        (q - 1) ^ q = (q - 1) ^ ((q - 1) + 1) := by congr 1 <;> ring
        _ = (q - 1) ^ (q - 1) * (q - 1) ^ (1 : ℝ) :=
          Real.rpow_add hqm1 _ _
        _ = (q - 1) ^ (q - 1) * (q - 1) := by rw [Real.rpow_one]
    have htwopow :
        (2 * (q - 1)) ^ (q - 1) =
          (2 : ℝ) ^ (q - 1) * (q - 1) ^ (q - 1) := by
      rw [Real.mul_rpow (by norm_num) hqm1.le]
    rw [hqpow, hqmpow, htwopow]
    have hqpowpos : 0 < q ^ (q - 1) := Real.rpow_pos_of_pos hq0 _
    have hqmpowpos : 0 < (q - 1) ^ (q - 1) :=
      Real.rpow_pos_of_pos hqm1 _
    have htwopowpos : 0 < (2 : ℝ) ^ (q - 1) :=
      Real.rpow_pos_of_pos (by norm_num) _
    field_simp [hq0.ne', hqm1.ne', hqpowpos.ne', hqmpowpos.ne',
      htwopowpos.ne']
  rw [hprod] at hy
  simpa [htermA, htermB] using hy

/-- The explicit Young coefficient used to bound the elliptic `L^q` norm.
It is deliberately exposed, unlike the earlier choice-based coefficient. -/
def paperEllipticSourceYoungConstant (p : CM2Params) (q : ℝ) : ℝ :=
  let pH : ℝ := q / (q - 1)
  let scale : ℝ := ((p.μ / 2) * pH) ^ (1 / pH)
  (p.ν / scale) ^ q / q

lemma paperEllipticSourceYoungConstant_pos
    (p : CM2Params) {q : ℝ} (hq : 1 < q) :
    0 < paperEllipticSourceYoungConstant p q := by
  let pH : ℝ := q / (q - 1)
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hqm1 : 0 < q - 1 := sub_pos.mpr hq
  have hpH : 0 < pH := by
    dsimp [pH]
    positivity
  let scale : ℝ := ((p.μ / 2) * pH) ^ (1 / pH)
  have hscale : 0 < scale := by
    dsimp [scale]
    exact Real.rpow_pos_of_pos (mul_pos (div_pos p.hμ (by norm_num)) hpH) _
  dsimp [paperEllipticSourceYoungConstant, pH, scale]
  exact div_pos (Real.rpow_pos_of_pos (div_pos p.hν hscale) _) hq0

/-- Explicit source Young inequality, with no choice-valued constant. -/
lemma paperEllipticSourceYoungConstant_bound
    (p : CM2Params) {q : ℝ} (hq : 1 < q) :
    ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      p.ν * A * B ^ (q - 1) ≤
        p.μ / 2 * B ^ q + paperEllipticSourceYoungConstant p q * A ^ q := by
  intro A B hA hB
  let pH : ℝ := q / (q - 1)
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hqm1 : 0 < q - 1 := sub_pos.mpr hq
  have hpH : 1 < pH := by
    dsimp [pH]
    rw [one_lt_div hqm1]
    linarith
  have hpH0 : 0 < pH := zero_lt_one.trans hpH
  have hpHne : pH ≠ 0 := hpH0.ne'
  have hconj : pH.HolderConjugate q := by
    rw [Real.holderConjugate_iff]
    refine ⟨hpH, ?_⟩
    dsimp [pH]
    field_simp [hq0.ne', hqm1.ne']
    ring
  let scale : ℝ := ((p.μ / 2) * pH) ^ (1 / pH)
  have hscale : 0 < scale := by
    dsimp [scale]
    exact Real.rpow_pos_of_pos
      (mul_pos (div_pos p.hμ (by norm_num)) hpH0) _
  have hleft : 0 ≤ scale * B ^ (q - 1) :=
    mul_nonneg hscale.le (Real.rpow_nonneg hB _)
  have hright : 0 ≤ p.ν * A / scale :=
    div_nonneg (mul_nonneg p.hν.le hA) hscale.le
  have hY := Real.young_inequality_of_nonneg
    (a := scale * B ^ (q - 1)) (b := p.ν * A / scale)
    hleft hright hconj
  have hprod :
      (scale * B ^ (q - 1)) * (p.ν * A / scale) =
        p.ν * A * B ^ (q - 1) := by
    field_simp [hscale.ne']
  have hscalePow : scale ^ pH = (p.μ / 2) * pH := by
    dsimp [scale]
    rw [← Real.rpow_mul (mul_pos (div_pos p.hμ (by norm_num)) hpH0).le]
    have hone : (1 / pH) * pH = 1 := by field_simp [hpHne]
    rw [hone, Real.rpow_one]
  have hBpow : (B ^ (q - 1)) ^ pH = B ^ q := by
    rw [← Real.rpow_mul hB]
    dsimp [pH]
    have he : (q - 1) * (q / (q - 1)) = q := by
      field_simp [hqm1.ne']
    rw [he]
  have hterm1 :
      (scale * B ^ (q - 1)) ^ pH / pH = p.μ / 2 * B ^ q := by
    rw [Real.mul_rpow hscale.le (Real.rpow_nonneg hB _), hscalePow, hBpow]
    field_simp [hpHne]
  have hterm2 :
      (p.ν * A / scale) ^ q / q =
        paperEllipticSourceYoungConstant p q * A ^ q := by
    have hbase : p.ν * A / scale = (p.ν / scale) * A := by ring
    rw [hbase, Real.mul_rpow (div_nonneg p.hν.le hscale.le) hA]
    dsimp [paperEllipticSourceYoungConstant, pH, scale]
    ring
  calc
    p.ν * A * B ^ (q - 1) =
        (scale * B ^ (q - 1)) * (p.ν * A / scale) := hprod.symm
    _ ≤ (scale * B ^ (q - 1)) ^ pH / pH +
        (p.ν * A / scale) ^ q / q := hY
    _ = p.μ / 2 * B ^ q +
        paperEllipticSourceYoungConstant p q * A ^ q := by
      rw [hterm1, hterm2]

/-- The stronger one-dimensional log-gradient route yields this coefficient
before it is enlarged to the literal paper constant (1.18). -/
def intervalLogGradientMstar (p : CM2Params) (q : ℝ) : ℝ :=
  p.μ ^ q * (2 * paperEllipticSourceYoungConstant p q / p.μ)

lemma intervalLogGradientMstar_pos
    (p : CM2Params) {q : ℝ} (hq : 1 < q) :
    0 < intervalLogGradientMstar p q := by
  exact mul_pos (Real.rpow_pos_of_pos p.hμ _)
    (div_pos (mul_pos (by norm_num) (paperEllipticSourceYoungConstant_pos p hq))
      p.hμ)

lemma intervalLogGradientMstar_eq
    (p : CM2Params) {q : ℝ} (hq : 1 < q) :
    intervalLogGradientMstar p q =
      p.ν ^ q * ((2 / q) * (2 * (q - 1) / q) ^ (q - 1)) := by
  let pH : ℝ := q / (q - 1)
  let scale : ℝ := ((p.μ / 2) * pH) ^ (1 / pH)
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hqm1 : 0 < q - 1 := sub_pos.mpr hq
  have hpH : 0 < pH := by dsimp [pH]; positivity
  have hscale : 0 < scale := by
    dsimp [scale]
    exact Real.rpow_pos_of_pos
      (mul_pos (div_pos p.hμ (by norm_num)) hpH) _
  have hscaleq :
      scale ^ q =
        p.μ ^ (q - 1) * (q / (2 * (q - 1))) ^ (q - 1) := by
    have hbase : (p.μ / 2) * pH = p.μ * (q / (2 * (q - 1))) := by
      dsimp [pH]
      field_simp [hqm1.ne']
    have hexp : 1 / pH = (q - 1) / q := by
      dsimp [pH]
      field_simp [hq0.ne', hqm1.ne']
    dsimp [scale]
    have hratio0 : 0 ≤ q / (2 * (q - 1)) := by positivity
    rw [hbase, hexp, ← Real.rpow_mul (mul_nonneg p.hμ.le hratio0)]
    have he : (q - 1) / q * q = q - 1 := by field_simp [hq0.ne']
    rw [he, Real.mul_rpow p.hμ.le (by positivity : 0 ≤ q / (2 * (q - 1)))]
  have hmupow : p.μ ^ q = p.μ ^ (q - 1) * p.μ := by
    calc
      p.μ ^ q = p.μ ^ ((q - 1) + 1) := by congr 1 <;> ring
      _ = p.μ ^ (q - 1) * p.μ ^ (1 : ℝ) := Real.rpow_add p.hμ _ _
      _ = p.μ ^ (q - 1) * p.μ := by rw [Real.rpow_one]
  have hratioInv :
      ((q / (2 * (q - 1))) ^ (q - 1))⁻¹ =
        (2 * (q - 1) / q) ^ (q - 1) := by
    have hratio0 : 0 ≤ q / (2 * (q - 1)) := by positivity
    rw [← Real.inv_rpow hratio0]
    congr 2
    field_simp [hq0.ne', hqm1.ne']
  have hmupowpos : 0 < p.μ ^ (q - 1) := Real.rpow_pos_of_pos p.hμ _
  have hratioPos : 0 < (q / (2 * (q - 1))) ^ (q - 1) :=
    Real.rpow_pos_of_pos (by positivity) _
  unfold intervalLogGradientMstar paperEllipticSourceYoungConstant
  dsimp [pH, scale]
  change p.μ ^ q *
      (2 * ((p.ν / scale) ^ q / q) / p.μ) = _
  rw [Real.div_rpow p.hν.le hscale.le, hscaleq, hmupow]
  rw [show p.ν ^ q /
        (p.μ ^ (q - 1) * (q / (2 * (q - 1))) ^ (q - 1)) =
      p.ν ^ q *
        (p.μ ^ (q - 1) * (q / (2 * (q - 1))) ^ (q - 1))⁻¹ by
      rw [div_eq_mul_inv],
    show (p.μ ^ (q - 1) * (q / (2 * (q - 1))) ^ (q - 1))⁻¹ =
        (p.μ ^ (q - 1))⁻¹ *
          ((q / (2 * (q - 1))) ^ (q - 1))⁻¹ by rw [mul_inv],
    hratioInv]
  simp only [div_eq_mul_inv]
  field_simp [p.hμ.ne', hq0.ne', hmupowpos.ne', hratioPos.ne']

lemma intervalLogGradientMstar_le_paperMstar
    (p : CM2Params) {q : ℝ} (hq : 1 < q) :
    intervalLogGradientMstar p q ≤ intervalPaperMstar p q := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hqm1 : 0 ≤ q - 1 := (sub_pos.mpr hq).le
  let r : ℝ := 2 * (q - 1) / q
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr2 : r ≤ 2 := by
    dsimp [r]
    apply (div_le_iff₀ hq0).2
    nlinarith
  have hrpow : r ^ (q - 1) ≤ (2 : ℝ) ^ (q - 1) :=
    Real.rpow_le_rpow hr0 hr2 hqm1
  have hcoef :
      (2 / q) * r ^ (q - 1) ≤ (2 : ℝ) ^ q / q := by
    have hfac : 0 ≤ 2 / q := by positivity
    calc
      (2 / q) * r ^ (q - 1) ≤
          (2 / q) * (2 : ℝ) ^ (q - 1) :=
        mul_le_mul_of_nonneg_left hrpow hfac
      _ = (2 : ℝ) ^ q / q := by
        have hpow : (2 : ℝ) ^ q = (2 : ℝ) ^ (q - 1) * 2 := by
          calc
            (2 : ℝ) ^ q = (2 : ℝ) ^ ((q - 1) + 1) := by congr 1 <;> ring
            _ = (2 : ℝ) ^ (q - 1) * (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_add (by norm_num) _ _
            _ = (2 : ℝ) ^ (q - 1) * 2 := by rw [Real.rpow_one]
        rw [hpow]
        ring
  have h8 : 1 ≤ (8 : ℝ) ^ q :=
    Real.one_le_rpow (by norm_num) hq0.le
  have h2q0 : 0 ≤ (2 : ℝ) ^ q := Real.rpow_nonneg (by norm_num) _
  have hmuq0 : 0 ≤ p.μ ^ q := Real.rpow_nonneg p.hμ.le _
  have hmupos : 0 < p.μ ^ q := Real.rpow_pos_of_pos p.hμ _
  have hfirst :
      (2 : ℝ) ^ q / q ≤
        ((8 : ℝ) ^ q / q) *
          ((2 : ℝ) ^ q + 1 / p.μ ^ q) := by
    have ha : 1 / q ≤ (8 : ℝ) ^ q / q :=
      div_le_div_of_nonneg_right h8 hq0.le
    have hb : (2 : ℝ) ^ q ≤ (2 : ℝ) ^ q + 1 / p.μ ^ q := by
      exact le_add_of_nonneg_right (one_div_nonneg.mpr hmuq0)
    have hmul := mul_le_mul ha hb h2q0 (by positivity : 0 ≤ (8 : ℝ) ^ q / q)
    calc
      (2 : ℝ) ^ q / q = (1 / q) * (2 : ℝ) ^ q := by ring
      _ ≤ ((8 : ℝ) ^ q / q) *
          ((2 : ℝ) ^ q + 1 / p.μ ^ q) := hmul
  have hsecond :
      0 ≤ (2 : ℝ) ^ (2 * q) / ((q - 1) * q ^ q) := by
    positivity
  have hbracket :
      (2 : ℝ) ^ q / q ≤
        ((8 : ℝ) ^ q / q) * intervalHessianOptimalConstant q *
            ((2 : ℝ) ^ q + 1 / p.μ ^ q) +
          (2 : ℝ) ^ (2 * q) / ((q - 1) * q ^ q) := by
    rw [intervalHessianOptimalConstant_eq_one, mul_one]
    exact hfirst.trans (le_add_of_nonneg_right hsecond)
  rw [intervalLogGradientMstar_eq p hq]
  unfold intervalPaperMstar
  exact mul_le_mul_of_nonneg_left (hcoef.trans hbracket)
    (Real.rpow_nonneg p.hν.le q)

/-- The two lift-level estimates with the stronger logarithmic-gradient
coefficient.  This is the analytic core of the paper-exact realization. -/
theorem intervalLogGradientEstimate_lift
    {p : CM2Params} {T q beta : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hq : 1 < q) (hbeta : 0 ≤ beta) :
    ∀ t, 0 < t → t < T →
      (∫ x in (0 : ℝ)..1,
          |deriv (intervalDomainLift (v t)) x| ^ (2 * q) /
            intervalDomainLift (v t) x ^ q) ≤
        intervalLogGradientMstar p q *
          (∫ x in (0 : ℝ)..1,
            intervalDomainLift (u t) x ^ (p.γ * q)) ∧
      (∫ x in (0 : ℝ)..1,
          |deriv (intervalDomainLift (v t)) x| ^ (2 * q) /
            (1 + intervalDomainLift (v t) x) ^ ((1 + beta) * q)) ≤
        (Theta_beta beta) ^ q * intervalLogGradientMstar p q *
          (∫ x in (0 : ℝ)..1,
            intervalDomainLift (u t) x ^ (p.γ * q)) := by
  intro t ht0 htT
  let V : ℝ → ℝ := intervalDomainLift (v t)
  let U : ℝ → ℝ := intervalDomainLift (u t)
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hVpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < V x := by
    simpa [V] using solution_lift_v_pos_Icc hsol ht0 htT
  have hVcont : ContinuousOn V (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.1.continuousOn
  have hdVcont : ContinuousOn (deriv V) (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using deriv_v_continuousOn_Icc hsol ht0 htT
  have hlog : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv V x| ≤ Real.sqrt p.μ * V x := by
    simpa [V] using elliptic_log_gradient_bound hsol ht0 htT
  have hVqcont : ContinuousOn (fun x => V x ^ q) (Set.Icc (0 : ℝ) 1) :=
    hVcont.rpow_const (fun x hx => Or.inl (ne_of_gt (hVpos x hx)))
  have hVqint : IntervalIntegrable (fun x => V x ^ q) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le zero_le_one] using hVqcont
  have hnumcont : ContinuousOn (fun x => |deriv V x| ^ (2 * q))
      (Set.Icc (0 : ℝ) 1) :=
    hdVcont.abs.rpow_const (fun _ _ => Or.inr (by linarith))
  have hfirstCont : ContinuousOn
      (fun x => |deriv V x| ^ (2 * q) / V x ^ q) (Set.Icc (0 : ℝ) 1) :=
    hnumcont.div hVqcont
      (fun x hx => ne_of_gt (Real.rpow_pos_of_pos (hVpos x hx) q))
  have hfirstInt : IntervalIntegrable
      (fun x => |deriv V x| ^ (2 * q) / V x ^ q) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le zero_le_one] using hfirstCont
  have hfirstRaw :
      (∫ x in (0 : ℝ)..1, |deriv V x| ^ (2 * q) / V x ^ q) ≤
        p.μ ^ q * (∫ x in (0 : ℝ)..1, V x ^ q) := by
    calc
      _ ≤ ∫ x in (0 : ℝ)..1, p.μ ^ q * V x ^ q :=
        intervalIntegral.integral_mono_on (by norm_num) hfirstInt
          (hVqint.const_mul (p.μ ^ q))
          (fun x hx => elliptic_log_weight_pointwise
            p.hμ hq (hVpos x hx) (hlog x hx))
      _ = p.μ ^ q * (∫ x in (0 : ℝ)..1, V x ^ q) := by
        rw [intervalIntegral.integral_const_mul]
  have hpower := elliptic_power_estimate_of_young hsol ht0 htT hq
    (paperEllipticSourceYoungConstant_bound p hq)
  have hfirstFinal :
      (∫ x in (0 : ℝ)..1, |deriv V x| ^ (2 * q) / V x ^ q) ≤
        intervalLogGradientMstar p q *
          (∫ x in (0 : ℝ)..1, U x ^ (p.γ * q)) := by
    calc
      _ ≤ p.μ ^ q * (∫ x in (0 : ℝ)..1, V x ^ q) := hfirstRaw
      _ ≤ p.μ ^ q *
          ((2 * paperEllipticSourceYoungConstant p q / p.μ) *
            (∫ x in (0 : ℝ)..1, U x ^ (p.γ * q))) :=
        mul_le_mul_of_nonneg_left (by simpa [V, U] using hpower)
          (Real.rpow_nonneg p.hμ.le q)
      _ = intervalLogGradientMstar p q *
          (∫ x in (0 : ℝ)..1, U x ^ (p.γ * q)) := by
        unfold intervalLogGradientMstar
        ring
  have hbaseCont : ContinuousOn (fun x => 1 + V x) (Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.add hVcont
  have hdenCont : ContinuousOn
      (fun x => (1 + V x) ^ ((1 + beta) * q)) (Set.Icc (0 : ℝ) 1) :=
    hbaseCont.rpow_const (fun x hx => Or.inl (by
      have := hVpos x hx
      positivity))
  have hsecondCont : ContinuousOn
      (fun x => |deriv V x| ^ (2 * q) /
        (1 + V x) ^ ((1 + beta) * q)) (Set.Icc (0 : ℝ) 1) :=
    hnumcont.div hdenCont (fun x hx => ne_of_gt
      (Real.rpow_pos_of_pos (by have := hVpos x hx; linarith) _))
  have hsecondInt : IntervalIntegrable
      (fun x => |deriv V x| ^ (2 * q) /
        (1 + V x) ^ ((1 + beta) * q)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le zero_le_one] using hsecondCont
  have htheta0 : 0 ≤ Theta_beta beta ^ q :=
    Real.rpow_nonneg (Theta_beta_pos_of_nonneg hbeta).le _
  have hsecondRaw :
      (∫ x in (0 : ℝ)..1,
          |deriv V x| ^ (2 * q) / (1 + V x) ^ ((1 + beta) * q)) ≤
        (Theta_beta beta) ^ q *
          (p.μ ^ q * (∫ x in (0 : ℝ)..1, V x ^ q)) := by
    calc
      _ ≤ ∫ x in (0 : ℝ)..1,
          (Theta_beta beta) ^ q * (p.μ ^ q * V x ^ q) :=
        intervalIntegral.integral_mono_on (by norm_num) hsecondInt
          (by simpa [mul_assoc] using
            hVqint.const_mul ((Theta_beta beta) ^ q * p.μ ^ q))
          (fun x hx => by
            simpa [mul_assoc] using elliptic_denominator_weight_pointwise
              p.hμ hbeta hq (hVpos x hx) (hlog x hx))
      _ = (Theta_beta beta) ^ q *
          (p.μ ^ q * (∫ x in (0 : ℝ)..1, V x ^ q)) := by
        rw [show (fun x => (Theta_beta beta) ^ q * (p.μ ^ q * V x ^ q)) =
            fun x => ((Theta_beta beta) ^ q * p.μ ^ q) * V x ^ q by
              funext x; ring,
          intervalIntegral.integral_const_mul]
        ring
  have hsecondFinal :
      (∫ x in (0 : ℝ)..1,
          |deriv V x| ^ (2 * q) / (1 + V x) ^ ((1 + beta) * q)) ≤
        (Theta_beta beta) ^ q * intervalLogGradientMstar p q *
          (∫ x in (0 : ℝ)..1, U x ^ (p.γ * q)) := by
    calc
      _ ≤ (Theta_beta beta) ^ q *
          (p.μ ^ q * (∫ x in (0 : ℝ)..1, V x ^ q)) := hsecondRaw
      _ ≤ (Theta_beta beta) ^ q *
          (p.μ ^ q *
            ((2 * paperEllipticSourceYoungConstant p q / p.μ) *
              (∫ x in (0 : ℝ)..1, U x ^ (p.γ * q)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (by simpa [V, U] using hpower)
            (Real.rpow_nonneg p.hμ.le q)) htheta0
      _ = (Theta_beta beta) ^ q * intervalLogGradientMstar p q *
          (∫ x in (0 : ℝ)..1, U x ^ (p.γ * q)) := by
        unfold intervalLogGradientMstar
        ring
  exact ⟨by simpa [V, U] using hfirstFinal,
    by simpa [V, U] using hsecondFinal⟩

lemma intervalDomainM_weighted_v_integral_lift
    {f : intervalDomainPoint → ℝ} {q : ℝ} :
    intervalDomainM.integral
        (fun x => intervalDomainM.gradNorm f x ^ (2 * q) / f x ^ q) =
      ∫ y in (0 : ℝ)..1,
        |deriv (intervalDomainLift f) y| ^ (2 * q) /
          intervalDomainLift f y ^ q := by
  simpa [intervalDomainM, intervalDomain] using
    (intervalDomain_weighted_v_integral_lift (f := f) (q := q))

lemma intervalDomainM_weighted_one_add_v_integral_lift
    {f : intervalDomainPoint → ℝ} {q beta : ℝ} :
    intervalDomainM.integral
        (fun x => intervalDomainM.gradNorm f x ^ (2 * q) /
          (1 + f x) ^ ((1 + beta) * q)) =
      ∫ y in (0 : ℝ)..1,
        |deriv (intervalDomainLift f) y| ^ (2 * q) /
          (1 + intervalDomainLift f y) ^ ((1 + beta) * q) := by
  simpa [intervalDomainM, intervalDomain] using
    (intervalDomain_weighted_one_add_v_integral_lift
      (f := f) (q := q) (beta := beta))

lemma intervalDomainM_power_integral_lift
    {f : intervalDomainPoint → ℝ} {q : ℝ} :
    intervalDomainM.integral (fun x => f x ^ q) =
      ∫ y in (0 : ℝ)..1, intervalDomainLift f y ^ q := by
  simpa [intervalDomainM, intervalDomain] using
    (intervalDomain_power_integral_lift' (f := f) (q := q))

/-- Paper 2, Proposition 2.2 on the faithful general-`m` interval model,
with the literal coefficient `M*` from (1.18). -/
theorem intervalDomainM_weightedGradientEstimate_paperMstar
    {p : CM2Params} {T q beta : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hq : 1 < q) (hbeta : 0 ≤ beta) :
    WeightedGradientEstimate intervalDomainM q beta p.γ
      (intervalPaperMstar p q) T u v := by
  intro t ht0 htT
  have hsmall := intervalLogGradientEstimate_lift hsol hq hbeta t ht0 htT
  have hM := intervalLogGradientMstar_le_paperMstar p hq
  have hU0 : 0 ≤ ∫ x in (0 : ℝ)..1,
      intervalDomainLift (u t) x ^ (p.γ * q) := by
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx =>
      Real.rpow_nonneg
        (solution_lift_pos_Icc hsol ⟨ht0, htT⟩ x hx).le _)
  constructor
  · have hscale := mul_le_mul_of_nonneg_right hM hU0
    rw [intervalDomainM_weighted_v_integral_lift,
      intervalDomainM_power_integral_lift]
    exact hsmall.1.trans hscale
  · have htheta0 : 0 ≤ Theta_beta beta ^ q :=
      Real.rpow_nonneg (Theta_beta_pos_of_nonneg hbeta).le _
    have hscale :
        Theta_beta beta ^ q * intervalLogGradientMstar p q *
            (∫ x in (0 : ℝ)..1,
              intervalDomainLift (u t) x ^ (p.γ * q)) ≤
          Theta_beta beta ^ q * intervalPaperMstar p q *
            (∫ x in (0 : ℝ)..1,
              intervalDomainLift (u t) x ^ (p.γ * q)) := by
      calc
        _ = Theta_beta beta ^ q *
            (intervalLogGradientMstar p q *
              (∫ x in (0 : ℝ)..1,
                intervalDomainLift (u t) x ^ (p.γ * q))) := by ring
        _ ≤ Theta_beta beta ^ q *
            (intervalPaperMstar p q *
              (∫ x in (0 : ℝ)..1,
                intervalDomainLift (u t) x ^ (p.γ * q))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hM hU0) htheta0
        _ = _ := by ring
    rw [intervalDomainM_weighted_one_add_v_integral_lift,
      intervalDomainM_power_integral_lift]
    exact hsmall.2.trans hscale

#print axioms intervalDomainM_weightedGradientEstimate_paperMstar

#print axioms weighted_split_young

end ShenWork.Paper2.IntervalDomainPaperWeightedGradientMstar
