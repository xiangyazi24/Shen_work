import ShenWork.Paper1.WaveLocalStepConstruction
import ShenWork.Paper1.WaveSuperBarrierPos

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
## The paper-expanded upper barrier in the attraction regime

The positive branch evolves the paper-expanded cross-frozen equation.  Its
upper comparison therefore needs `paperWaveOperator`, not merely the frozen
divergence-form operator.  The only delicate region is the exponential branch.
There the exact one-sided Green formula gives

`κ m V' - V ≤ ((κ m - 1)₊ / (2 (1 + γ κ))) exp (-γ κ x)`.

The definition of `chiStar` is precisely the scalar budget which absorbs this
term when `κ m > 1`.  No spatial monotonicity of the frozen profile is used.
-/

/-- The right-hand Green tail estimate used in the positive paper
super-barrier.  Unlike the two-sided estimate, it has no `γ κ < 1`
restriction. -/
theorem setIntegral_Ioi_exp_le_of_rpow_le_positive
    {κ : ℝ} {u : ℝ → ℝ} {γ : ℝ}
    (hκ : 0 < κ) (hγ : 0 < γ)
    (hu_exp : ∀ y, (u y) ^ γ ≤ Real.exp (-(γ * κ) * y))
    (x : ℝ)
    (hint : IntegrableOn
      (fun y => Real.exp (-1 * y) * (u y) ^ γ) (Set.Ioi x)) :
    ∫ y in Set.Ioi x, Real.exp (-1 * y) * (u y) ^ γ ≤
      Real.exp (-(1 + γ * κ) * x) / (1 + γ * κ) := by
  have hden : 0 < 1 + γ * κ := by positivity
  have hneg : -(1 + γ * κ) < 0 := by linarith
  have hint_exp : IntegrableOn
      (fun y => Real.exp (-(1 + γ * κ) * y)) (Set.Ioi x) :=
    integrableOn_exp_mul_Ioi hneg x
  calc
    ∫ y in Set.Ioi x, Real.exp (-1 * y) * (u y) ^ γ
        ≤ ∫ y in Set.Ioi x, Real.exp (-(1 + γ * κ) * y) := by
          apply MeasureTheory.setIntegral_mono hint hint_exp
          intro y
          calc
            Real.exp (-1 * y) * (u y) ^ γ
                ≤ Real.exp (-1 * y) * Real.exp (-(γ * κ) * y) :=
              mul_le_mul_of_nonneg_left (hu_exp y) (Real.exp_nonneg _)
            _ = Real.exp (-(1 + γ * κ) * y) := by
              rw [← Real.exp_add]
              congr 1
              ring
    _ = -Real.exp (-(1 + γ * κ) * x) / (-(1 + γ * κ)) :=
      integral_exp_mul_Ioi hneg x
    _ = Real.exp (-(1 + γ * κ) * x) / (1 + γ * κ) := by
      field_simp

/-- When `κ m ≤ 1`, the positive paper transport combination is favorable. -/
theorem positivePaper_transport_nonpos_of_mkappa_le_one
    (p : CMParams) {κ M : ℝ} {u : ℝ → ℝ}
    (hκ : 0 ≤ κ) (hmκ : κ * p.m ≤ 1)
    (hu : InWaveTrapSet κ M u) (x : ℝ) :
    κ * p.m * deriv (frozenElliptic p u) x -
        frozenElliptic p u x ≤ 0 := by
  have hV0 : 0 ≤ frozenElliptic p u x :=
    frozenElliptic_nonneg p hu.nonneg x
  have hVx : deriv (frozenElliptic p u) x ≤ frozenElliptic p u x :=
    (le_abs_self _).trans
      (frozenElliptic_deriv_abs_le p hu.cunif_bdd hu.nonneg x)
  have hmk0 : 0 ≤ κ * p.m :=
    mul_nonneg hκ (le_trans zero_le_one p.hm)
  have hmul : κ * p.m * deriv (frozenElliptic p u) x ≤
      κ * p.m * frozenElliptic p u x :=
    mul_le_mul_of_nonneg_left hVx hmk0
  have hscale : κ * p.m * frozenElliptic p u x ≤
      frozenElliptic p u x := by
    simpa using mul_le_of_le_one_left hV0 hmκ
  linarith

/-- Exact positive-part Green bound for `κ m V' - V` in the regime
`1 < κ m`. -/
theorem positivePaper_transport_le_of_one_lt_mkappa
    (p : CMParams) {κ M : ℝ} {u : ℝ → ℝ}
    (hκ : 0 < κ) (hmκ : 1 < κ * p.m)
    (hu : InWaveTrapSet κ M u) (x : ℝ) :
    κ * p.m * deriv (frozenElliptic p u) x -
        frozenElliptic p u x ≤
      (κ * p.m - 1) / (2 * (1 + p.γ * κ)) *
        Real.exp (-(p.γ * κ) * x) := by
  have hγ : 0 < p.γ := lt_of_lt_of_le zero_lt_one p.hγ
  have hden : 0 < 1 + p.γ * κ := by positivity
  let f : ℝ → ℝ := fun y => (u y) ^ p.γ
  have hf0 : ∀ y, 0 ≤ f y := fun y => Real.rpow_nonneg (hu.nonneg y) _
  have hfC : IsCUnifBdd f :=
    rpow_cunif_bdd_of_nonneg p hu.cunif_bdd hu.nonneg
  have hVx := Psi_derivative_formula_general
    (l := 1) (mu := 1) one_pos one_pos hfC x
  let L : ℝ := ∫ y in Set.Iic x, Real.exp (1 * y) * f y
  let R : ℝ := ∫ y in Set.Ioi x, Real.exp (-1 * y) * f y
  have hV' : deriv (frozenElliptic p u) x =
      -(1 / 2) * Real.exp (-1 * x) * L +
        (1 / 2) * Real.exp (1 * x) * R := by
    simp only [Real.sqrt_one] at hVx
    have heq : (fun z => frozenElliptic p u z) =
        fun z => Psi f 1 1 z := rfl
    rw [show deriv (frozenElliptic p u) x =
        deriv (fun z => Psi f 1 1 z) x from
      congrArg (fun g => deriv g x) heq, hVx]
  have hV : frozenElliptic p u x =
      1 / 2 * (Real.exp (-1 * x) * L + Real.exp (1 * x) * R) := by
    exact Psi_kernel_splitting hfC hf0 x
  have hcomb :
      κ * p.m * deriv (frozenElliptic p u) x -
          frozenElliptic p u x =
        -(1 / 2) * (κ * p.m + 1) * (Real.exp (-1 * x) * L) +
          (1 / 2) * (κ * p.m - 1) * (Real.exp (1 * x) * R) := by
    rw [hV', hV]
    ring
  have hL0 : 0 ≤ L := by
    apply MeasureTheory.setIntegral_nonneg measurableSet_Iic
    intro y _hy
    exact mul_nonneg (Real.exp_nonneg _) (hf0 y)
  have hRint : IntegrableOn
      (fun y => Real.exp (-1 * y) * f y) (Set.Ioi x) := by
    have hdom : IntegrableOn
        (fun y => Real.exp (-(1 + p.γ * κ) * y)) (Set.Ioi x) :=
      integrableOn_exp_mul_Ioi (by linarith) x
    refine hdom.mono' ?_ (Eventually.of_forall fun y => ?_)
    · have hc : Continuous (fun y => Real.exp (-1 * y) * f y) :=
        (Real.continuous_exp.comp
          (continuous_const.mul continuous_id)).mul hfC.1
      exact hc.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (Real.exp_nonneg _) (hf0 y))]
      have hpow : f y ≤ Real.exp (-(p.γ * κ) * y) := by
        dsimp [f]
        calc
          (u y) ^ p.γ ≤ (Real.exp (-κ * y)) ^ p.γ :=
            Real.rpow_le_rpow (hu.nonneg y) (hu.le_exp y) hγ.le
          _ = Real.exp (-(p.γ * κ) * y) := by
            rw [← Real.exp_mul]
            congr 1
            ring
      calc
        Real.exp (-1 * y) * f y
            ≤ Real.exp (-1 * y) * Real.exp (-(p.γ * κ) * y) :=
          mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _)
        _ = Real.exp (-(1 + p.γ * κ) * y) := by
          rw [← Real.exp_add]
          congr 1
          ring
  have hpow : ∀ y, f y ≤ Real.exp (-(p.γ * κ) * y) := by
    intro y
    dsimp [f]
    calc
      (u y) ^ p.γ ≤ (Real.exp (-κ * y)) ^ p.γ :=
        Real.rpow_le_rpow (hu.nonneg y) (hu.le_exp y) hγ.le
      _ = Real.exp (-(p.γ * κ) * y) := by
        rw [← Real.exp_mul]
        congr 1
        ring
  have hR := setIntegral_Ioi_exp_le_of_rpow_le_positive
    hκ hγ hpow x hRint
  have hR0 : 0 ≤ R := by
    apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    intro y _hy
    exact mul_nonneg (Real.exp_nonneg _) (hf0 y)
  have hleft :
      -(1 / 2) * (κ * p.m + 1) * (Real.exp (-1 * x) * L) ≤ 0 := by
    have hcoef : -(1 / 2) * (κ * p.m + 1) ≤ 0 := by
      have : 0 ≤ κ * p.m :=
        mul_nonneg hκ.le (le_trans zero_le_one p.hm)
      nlinarith
    exact mul_nonpos_of_nonpos_of_nonneg hcoef
      (mul_nonneg (Real.exp_nonneg _) hL0)
  have hcoef0 : 0 ≤ (1 / 2) * (κ * p.m - 1) := by linarith
  have hright :
      (1 / 2) * (κ * p.m - 1) * (Real.exp (1 * x) * R) ≤
        (κ * p.m - 1) / (2 * (1 + p.γ * κ)) *
          Real.exp (-(p.γ * κ) * x) := by
    have hexp :
        Real.exp (1 * x) *
            (Real.exp (-(1 + p.γ * κ) * x) /
              (1 + p.γ * κ)) =
          Real.exp (-(p.γ * κ) * x) /
            (1 + p.γ * κ) := by
      field_simp [ne_of_gt hden]
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      (1 / 2) * (κ * p.m - 1) * (Real.exp (1 * x) * R)
          ≤ (1 / 2) * (κ * p.m - 1) *
              (Real.exp (1 * x) *
                (Real.exp (-(1 + p.γ * κ) * x) /
                  (1 + p.γ * κ))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hR (Real.exp_nonneg _)) hcoef0
      _ = (1 / 2) * (κ * p.m - 1) *
          (Real.exp (-(p.γ * κ) * x) / (1 + p.γ * κ)) := by
        rw [hexp]
      _ = (κ * p.m - 1) / (2 * (1 + p.γ * κ)) *
          Real.exp (-(p.γ * κ) * x) := by
        field_simp [ne_of_gt hden]
  rw [hcomb]
  linarith

/-- The `chiStar` budget absorbs the positive Green-tail coefficient in the
`1 < κ m` branch. -/
theorem chi_mul_one_add_positivePaper_coeff_lt_one
    (p : CMParams) {κ : ℝ}
    (hχ0 : 0 ≤ p.χ) (hχ : p.χ < chiStar p)
    (hκ1 : κ < 1) (hmκ : 1 < κ * p.m) :
    p.χ * (1 + (κ * p.m - 1) /
      (2 * (1 + p.γ * κ))) < 1 := by
  have hm : 0 < p.m := lt_of_lt_of_le zero_lt_one p.hm
  have hγ : 0 < p.γ := lt_of_lt_of_le zero_lt_one p.hγ
  have hκ : 0 < κ := by
    by_contra hk
    have hk0 : κ ≤ 0 := le_of_not_gt hk
    have : κ * p.m ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hk0 hm.le
    linarith
  have hnum0 : 0 ≤ κ * p.m - 1 := by linarith
  have hm1 : 0 ≤ p.m - 1 := sub_nonneg.mpr p.hm
  have hden : 0 < 2 * (1 + p.γ * κ) := by positivity
  have hden0 : 0 < 2 * (1 + p.γ / p.m) := by positivity
  have hnum_le : κ * p.m - 1 ≤ p.m - 1 := by
    nlinarith [mul_lt_mul_of_pos_right hκ1 hm]
  have hk_inv : 1 / p.m < κ := by
    rw [div_lt_iff₀ hm]
    simpa [one_mul, mul_comm] using hmκ
  have hgamma_div : p.γ / p.m ≤ p.γ * κ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left
      (by simpa [one_div] using hk_inv.le) hγ.le
  have hden_le : 2 * (1 + p.γ / p.m) ≤
      2 * (1 + p.γ * κ) := by
    nlinarith
  have hfrac1 :
      (κ * p.m - 1) / (2 * (1 + p.γ * κ)) ≤
        (p.m - 1) / (2 * (1 + p.γ * κ)) :=
    div_le_div_of_nonneg_right hnum_le hden.le
  have hfrac2 :
      (p.m - 1) / (2 * (1 + p.γ * κ)) ≤
        (p.m - 1) / (2 * (1 + p.γ / p.m)) := by
    exact div_le_div_of_nonneg_left hm1 hden0 hden_le
  let q : ℝ := (p.m - 1) / (2 * (1 + p.γ / p.m))
  have hcoeff :
      (κ * p.m - 1) / (2 * (1 + p.γ * κ)) ≤ q :=
    hfrac1.trans hfrac2
  have hfactor : 0 < 1 + q := by
    dsimp [q]
    positivity
  have hχratio :
      p.χ < (2 * p.m + 2 * p.γ) /
        (p.m ^ 2 + p.m + 2 * p.γ) :=
    hχ.trans_le (chiStar_le_ratio p)
  have hidentity :
      ((2 * p.m + 2 * p.γ) /
          (p.m ^ 2 + p.m + 2 * p.γ)) * (1 + q) = 1 := by
    dsimp [q]
    field_simp [ne_of_gt hm]
    ring
  have hbudget : p.χ * (1 + q) < 1 := by
    have hmul := mul_lt_mul_of_pos_right hχratio hfactor
    rwa [hidentity] at hmul
  have hscale :
      p.χ * (1 + (κ * p.m - 1) /
          (2 * (1 + p.γ * κ))) ≤ p.χ * (1 + q) :=
    mul_le_mul_of_nonneg_left
      (by simpa [add_comm] using add_le_add_left hcoeff 1) hχ0
  exact hscale.trans_lt hbudget

/-- Exponential branch of the positive paper-expanded super-barrier. -/
theorem paperWaveOperator_upperBarrier_exp_region_nonpos_pos
    (p : CMParams) {c κ M : ℝ} {u : ℝ → ℝ}
    (hχ0 : 0 ≤ p.χ) (hχ : p.χ < chiStar p)
    (hα : p.α = p.m + p.γ - 1)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hc : c = κ + κ⁻¹)
    (hu : InWaveTrapSet κ M u) {x : ℝ}
    (hx : Real.exp (-κ * x) < M) :
    paperWaveOperator p c u (upperBarrier κ M) x ≤ 0 := by
  let E : ℝ := expDecay κ x
  let V : ℝ := frozenElliptic p u x
  let Vx : ℝ := deriv (frozenElliptic p u) x
  have hE : 0 < E := expDecay_pos κ x
  have hχ1 : p.χ < 1 := hχ.trans_le (chiStar_le_one p)
  have hm0 : 0 ≤ p.m := le_trans zero_le_one p.hm
  have hEm : 0 ≤ E ^ p.m := Real.rpow_nonneg hE.le _
  have hEγ : 0 ≤ E ^ p.γ := Real.rpow_nonneg hE.le _
  have hpow_mγ : E ^ p.m * E ^ p.γ = E * E ^ p.α := by
    calc
      E ^ p.m * E ^ p.γ = E ^ (p.m + p.γ) := by
        rw [Real.rpow_add hE]
      _ = E ^ (1 + p.α) := by
        rw [hα]
        congr 1
        ring
      _ = E ^ (1 : ℝ) * E ^ p.α := by
        rw [Real.rpow_add hE]
      _ = E * E ^ p.α := by rw [Real.rpow_one]
  have hchem_eq :
      -p.χ * p.m * E ^ (p.m - 1) * Vx * (-κ * E) +
          E * (-p.χ * E ^ (p.m - 1) * V +
            p.χ * E ^ (p.m + p.γ - 1)) =
        p.χ * E ^ p.m * (κ * p.m * Vx - V + E ^ p.γ) := by
    have hpow_m : E ^ (p.m - 1) * E = E ^ p.m := by
      calc
        E ^ (p.m - 1) * E = E ^ (p.m - 1) * E ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = E ^ ((p.m - 1) + 1) := by rw [Real.rpow_add hE]
        _ = E ^ p.m := by congr 1 <;> ring
    have hpow_mγ' : E * E ^ (p.m + p.γ - 1) =
        E ^ p.m * E ^ p.γ := by
      calc
        E * E ^ (p.m + p.γ - 1) =
            E ^ (1 : ℝ) * E ^ (p.m + p.γ - 1) := by
          rw [Real.rpow_one]
        _ = E ^ (1 + (p.m + p.γ - 1)) := by rw [Real.rpow_add hE]
        _ = E ^ (p.m + p.γ) := by congr 1 <;> ring
        _ = E ^ p.m * E ^ p.γ := by rw [← Real.rpow_add hE]
    calc
      -p.χ * p.m * E ^ (p.m - 1) * Vx * (-κ * E) +
            E * (-p.χ * E ^ (p.m - 1) * V +
              p.χ * E ^ (p.m + p.γ - 1)) =
          p.χ * (E ^ (p.m - 1) * E) *
              (κ * p.m * Vx - V) +
            p.χ * (E * E ^ (p.m + p.γ - 1)) := by ring
      _ = p.χ * E ^ p.m * (κ * p.m * Vx - V) +
            p.χ * (E ^ p.m * E ^ p.γ) := by
        rw [hpow_m, hpow_mγ']
      _ = p.χ * E ^ p.m * (κ * p.m * Vx - V + E ^ p.γ) := by
        ring
  have hchem :
      p.χ * E ^ p.m * (κ * p.m * Vx - V + E ^ p.γ) ≤
        E * E ^ p.α := by
    by_cases hmk : κ * p.m ≤ 1
    · have ht := positivePaper_transport_nonpos_of_mkappa_le_one
        p hκ.le hmk hu x
      have hbracket : κ * p.m * Vx - V + E ^ p.γ ≤ E ^ p.γ := by
        dsimp [V, Vx] at ht ⊢
        linarith
      have hcoef0 : 0 ≤ p.χ * E ^ p.m := mul_nonneg hχ0 hEm
      calc
        p.χ * E ^ p.m * (κ * p.m * Vx - V + E ^ p.γ)
            ≤ p.χ * E ^ p.m * E ^ p.γ :=
          mul_le_mul_of_nonneg_left hbracket hcoef0
        _ = p.χ * (E * E ^ p.α) := by
          calc
            p.χ * E ^ p.m * E ^ p.γ =
                p.χ * (E ^ p.m * E ^ p.γ) := by ring
            _ = p.χ * (E * E ^ p.α) := by rw [hpow_mγ]
        _ ≤ E * E ^ p.α := by
          exact mul_le_of_le_one_left
            (mul_nonneg hE.le (Real.rpow_nonneg hE.le _)) hχ1.le
    · have hmk' : 1 < κ * p.m := lt_of_not_ge hmk
      let q : ℝ := (κ * p.m - 1) / (2 * (1 + p.γ * κ))
      have ht := positivePaper_transport_le_of_one_lt_mkappa
        p hκ hmk' hu x
      have hEγexp : E ^ p.γ = Real.exp (-(p.γ * κ) * x) := by
        dsimp [E]
        rw [expDecay_rpow_eq]
        unfold expDecay
        congr 1
        ring
      have ht' : κ * p.m * Vx - V ≤ q * E ^ p.γ := by
        simpa [q, hEγexp, V, Vx] using ht
      have hbracket : κ * p.m * Vx - V + E ^ p.γ ≤
          (1 + q) * E ^ p.γ := by
        linarith
      have hcoef0 : 0 ≤ p.χ * E ^ p.m := mul_nonneg hχ0 hEm
      have hbudget := chi_mul_one_add_positivePaper_coeff_lt_one
        p hχ0 hχ hκ1 hmk'
      calc
        p.χ * E ^ p.m * (κ * p.m * Vx - V + E ^ p.γ)
            ≤ p.χ * E ^ p.m * ((1 + q) * E ^ p.γ) :=
          mul_le_mul_of_nonneg_left hbracket hcoef0
        _ = (p.χ * (1 + q)) * (E ^ p.m * E ^ p.γ) := by ring
        _ = (p.χ * (1 + q)) * (E * E ^ p.α) := by rw [hpow_mγ]
        _ ≤ E * E ^ p.α := by
          exact mul_le_of_le_one_left
            (mul_nonneg hE.le (Real.rpow_nonneg hE.le _)) hbudget.le
  rw [paperWaveOperator_upperBarrier_exp_region_eq_of_kappa_speed
    p (ne_of_gt hκ) hc hx]
  dsimp [E, V, Vx] at hchem hchem_eq
  calc
    -expDecay κ x * (expDecay κ x) ^ p.α -
          p.χ * p.m * (expDecay κ x) ^ (p.m - 1) *
            deriv (frozenElliptic p u) x * (-κ * expDecay κ x) +
        expDecay κ x *
          (-p.χ * (expDecay κ x) ^ (p.m - 1) *
              frozenElliptic p u x +
            p.χ * (expDecay κ x) ^ (p.m + p.γ - 1)) =
      -expDecay κ x * (expDecay κ x) ^ p.α +
        (-p.χ * p.m * (expDecay κ x) ^ (p.m - 1) *
            deriv (frozenElliptic p u) x * (-κ * expDecay κ x) +
          expDecay κ x *
            (-p.χ * (expDecay κ x) ^ (p.m - 1) *
                frozenElliptic p u x +
              p.χ * (expDecay κ x) ^ (p.m + p.γ - 1))) := by ring
    _ = -expDecay κ x * (expDecay κ x) ^ p.α +
        p.χ * (expDecay κ x) ^ p.m *
          (κ * p.m * deriv (frozenElliptic p u) x -
            frozenElliptic p u x + (expDecay κ x) ^ p.γ) := by
      rw [hchem_eq]
    _ ≤ 0 := by linarith

/-- Interface branch for the positive paper-expanded upper barrier. -/
theorem paperWaveOperator_upperBarrier_interface_nonpos_pos
    (p : CMParams) {c κ M : ℝ} {u : ℝ → ℝ}
    (hχ0 : 0 ≤ p.χ) (hχ : p.χ < chiStar p)
    (hα : p.α = p.m + p.γ - 1)
    (hκ : 0 < κ) (hM : 1 ≤ M)
    (hMχ : (1 / (1 - p.χ)) ^ (1 / p.α) ≤ M)
    (hu : InWaveTrapSet κ M u) {x : ℝ}
    (hx : Real.exp (-κ * x) = M) :
    paperWaveOperator p c u (upperBarrier κ M) x ≤ 0 := by
  have hconst := paperWaveOperator_const_nonpos_pos
    p (c := c) hχ0 hχ hα hM hMχ hu x
  rw [paperWaveOperator_const_eq p hu.cunif_bdd hu.nonneg x] at hconst
  rw [paperWaveOperator_upperBarrier_interface_eq p hκ
    (lt_of_lt_of_le zero_lt_one hM) hx]
  exact hconst

/-- Whole-line paper-expanded super-barrier in the positive headline regime.
This is the barrier consumed by the genuine paper Green step. -/
theorem paperWaveOperator_super_barrier_pos
    (p : CMParams) {c κ M : ℝ}
    (hχ0 : 0 ≤ p.χ) (hχ : p.χ < chiStar p)
    (hα : p.α = p.m + p.γ - 1)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hM : 1 ≤ M)
    (hMχ : (1 / (1 - p.χ)) ^ (1 / p.α) ≤ M)
    (hc : c = κ + κ⁻¹) {u : ℝ → ℝ}
    (hu : InWaveTrapSet κ M u) :
    ∀ x, paperWaveOperator p c u (upperBarrier κ M) x ≤ 0 := by
  intro x
  rcases lt_trichotomy (Real.exp (-κ * x)) M with hx | hx | hx
  · exact paperWaveOperator_upperBarrier_exp_region_nonpos_pos
      p hχ0 hχ hα hκ hκ1 hc hu hx
  · exact paperWaveOperator_upperBarrier_interface_nonpos_pos
      p hχ0 hχ hα hκ hM hMχ hu hx
  · exact paperWaveOperator_upperBarrier_const_region_nonpos_pos
      p hχ0 hχ hα hM hMχ hu hx

section AxiomAudit

#print axioms positivePaper_transport_le_of_one_lt_mkappa
#print axioms chi_mul_one_add_positivePaper_coeff_lt_one
#print axioms paperWaveOperator_upperBarrier_exp_region_nonpos_pos
#print axioms paperWaveOperator_super_barrier_pos

end AxiomAudit

end ShenWork.Paper1
