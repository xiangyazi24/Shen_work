import ShenWork.Paper1.WholeLineChiPosEquilibriumRoot
import ShenWork.Paper1.WholeLineChiPosSupercriticalLongTimeBound

/-!
# Descent to the exact positive-sensitivity equilibrium ceiling

For `q := m + γ - 1 < α`, the exact scalar equilibrium supports the same
positive exponential relaxation rate `α - q` as the crude parameter ceiling.
The quantitative power gap proved for the supercritical branch pays for this
rate all the way down to the exact root.
-/

open Filter Topology Function MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-- The relaxing ceiling based at the exact positive-sensitivity equilibrium. -/
def wholeLineCauchyChiPosEquilibriumDescent
    (p : CMParams) (C t : ℝ) : ℝ :=
  chiPosEquilibriumCeiling p +
    (C - chiPosEquilibriumCeiling p) *
      Real.exp (-wholeLineCauchyChiPosSupercriticalRate p * t)

theorem wholeLineCauchyChiPosEquilibriumDescent_zero
    (p : CMParams) (C : ℝ) :
    wholeLineCauchyChiPosEquilibriumDescent p C 0 = C := by
  simp [wholeLineCauchyChiPosEquilibriumDescent]

theorem wholeLineCauchyChiPosEquilibriumDescent_hasDerivAt
    (p : CMParams) (C t : ℝ) :
    HasDerivAt (wholeLineCauchyChiPosEquilibriumDescent p C)
      (-wholeLineCauchyChiPosSupercriticalRate p *
        ((C - chiPosEquilibriumCeiling p) *
          Real.exp (-wholeLineCauchyChiPosSupercriticalRate p * t))) t := by
  have hlin : HasDerivAt
      (fun s : ℝ => -wholeLineCauchyChiPosSupercriticalRate p * s)
      (-wholeLineCauchyChiPosSupercriticalRate p) t := by
    simpa using (hasDerivAt_id t).const_mul
      (-wholeLineCauchyChiPosSupercriticalRate p)
  have hexp := hlin.exp
  have hderiv :=
    (hexp.const_mul (C - chiPosEquilibriumCeiling p)).const_add
      (chiPosEquilibriumCeiling p)
  convert hderiv using 1
  ring

theorem wholeLineCauchyChiPosEquilibriumDescent_base_le
    {p : CMParams} {C : ℝ}
    (hC : chiPosEquilibriumCeiling p ≤ C) (t : ℝ) :
    chiPosEquilibriumCeiling p ≤
      wholeLineCauchyChiPosEquilibriumDescent p C t := by
  unfold wholeLineCauchyChiPosEquilibriumDescent
  have hexp : 0 < Real.exp
      (-wholeLineCauchyChiPosSupercriticalRate p * t) := Real.exp_pos _
  nlinarith [sub_nonneg.mpr hC, hexp.le]

theorem wholeLineCauchyChiPosEquilibriumDescent_le
    {p : CMParams} {C t : ℝ}
    (hC : chiPosEquilibriumCeiling p ≤ C)
    (hsuper : p.m + p.γ - 1 < p.α) (ht : 0 ≤ t) :
    wholeLineCauchyChiPosEquilibriumDescent p C t ≤ C := by
  unfold wholeLineCauchyChiPosEquilibriumDescent
  have hrate := wholeLineCauchyChiPosSupercriticalRate_pos hsuper
  have hexp_le : Real.exp
      (-wholeLineCauchyChiPosSupercriticalRate p * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  nlinarith [sub_nonneg.mpr hC]

theorem wholeLineCauchyChiPosEquilibriumDescent_restart
    (p : CMParams) (C a s : ℝ) :
    wholeLineCauchyChiPosEquilibriumDescent p
        (wholeLineCauchyChiPosEquilibriumDescent p C a) s =
      wholeLineCauchyChiPosEquilibriumDescent p C (a + s) := by
  unfold wholeLineCauchyChiPosEquilibriumDescent
  have hexp : Real.exp (-wholeLineCauchyChiPosSupercriticalRate p * a) *
      Real.exp (-wholeLineCauchyChiPosSupercriticalRate p * s) =
      Real.exp (-wholeLineCauchyChiPosSupercriticalRate p * (a + s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← hexp]
  ring

/-- The exact equilibrium supports the positive rate `α - (m + γ - 1)` for
every ceiling height above it. -/
theorem chiPosEquilibriumDescent_supersolution
    {p : CMParams} (hχ : 0 ≤ p.χ)
    (hsuper : p.m + p.γ - 1 < p.α)
    {B : ℝ} (hB : chiPosEquilibriumCeiling p ≤ B) :
    p.χ * B ^ (p.m + p.γ) + reactionFun p.α B +
        wholeLineCauchyChiPosSupercriticalRate p *
          (B - chiPosEquilibriumCeiling p) ≤ 0 := by
  let q : ℝ := p.m + p.γ - 1
  let d : ℝ := p.α - q
  let M : ℝ := chiPosEquilibriumCeiling p
  have hq0 : (0 : ℝ) ≤ q := by
    dsimp [q]
    linarith [p.hm, p.hγ]
  have hd : 0 < d := by
    dsimp [d, q]
    linarith
  have hM1 : (1 : ℝ) ≤ M := by
    dsimp [M]
    exact chiPosEquilibriumCeiling_one_le p hχ hsuper
  have hM0 : (0 : ℝ) < M := zero_lt_one.trans_le hM1
  have hB0 : (0 : ℝ) < B := hM0.trans_le hB
  have hBM : 0 ≤ B - M := sub_nonneg.mpr hB
  have heq : chiPosEquilibriumEq p M = 0 := by
    dsimp [M]
    exact chiPosEquilibriumCeiling_eq_zero p hχ hsuper
  have hgap := rpow_supercritical_scaled_gap hM0 hB hq0 hd
  have hMpow1 : (1 : ℝ) ≤ M ^ (q + d) :=
    Real.one_le_rpow hM1 (add_nonneg hq0 hd.le)
  have hrateGap :
      d * (B - M) ≤ B ^ (q + 1) * (B ^ d - M ^ d) := by
    calc
      d * (B - M) ≤ d * M ^ (q + d) * (B - M) := by
        nlinarith [mul_nonneg hd.le hBM]
      _ ≤ B ^ (q + 1) * (B ^ d - M ^ d) := hgap
  have hMsplit : M ^ p.α = M ^ q * M ^ d := by
    rw [← Real.rpow_add hM0]
    congr 1
    dsimp [d, q]
    ring
  have hrootProduct : M ^ q * (M ^ d - p.χ) = 1 := by
    unfold chiPosEquilibriumEq at heq
    rw [hMsplit] at heq
    nlinarith
  have hrootGapPos : 0 < M ^ d - p.χ := by
    have hMqPos : 0 < M ^ q := Real.rpow_pos_of_pos hM0 q
    nlinarith
  have hBq : M ^ q ≤ B ^ q :=
    Real.rpow_le_rpow hM0.le hB hq0
  have hBqOne : B ^ (q + 1) = B ^ q * B := by
    rw [Real.rpow_add hB0, Real.rpow_one]
  have hpay : B ≤ B ^ (q + 1) * (M ^ d - p.χ) := by
    rw [hBqOne]
    calc
      B = (M ^ q * (M ^ d - p.χ)) * B := by rw [hrootProduct]; ring
      _ ≤ (B ^ q * (M ^ d - p.χ)) * B := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hBq hrootGapPos.le) hB0.le
      _ = B ^ q * B * (M ^ d - p.χ) := by ring
  have hbudget :
      B ^ (q + 1) * (B ^ d - M ^ d) ≤
        B ^ (q + 1) * (B ^ d - p.χ) - B := by
    nlinarith [hpay]
  have hchemExp : q + 1 = p.m + p.γ := by
    dsimp [q]
    ring
  have htotalExp : q + 1 + d = p.α + 1 := by
    dsimp [d, q]
    ring
  have htotalPow : B ^ (q + 1) * B ^ d = B ^ (p.α + 1) := by
    rw [← Real.rpow_add hB0, htotalExp]
  have hreactionPow : B * B ^ p.α = B ^ (p.α + 1) := by
    calc
      B * B ^ p.α = B ^ (1 : ℝ) * B ^ p.α := by rw [Real.rpow_one]
      _ = B ^ ((1 : ℝ) + p.α) := by rw [← Real.rpow_add hB0]
      _ = B ^ (p.α + 1) := by ring_nf
  have hreaction : reactionFun p.α B = B - B ^ (p.α + 1) := by
    unfold reactionFun
    rw [mul_sub, mul_one, hreactionPow]
  have hfield :
      B ^ (q + 1) * (B ^ d - p.χ) - B =
        -(p.χ * B ^ (p.m + p.γ) + reactionFun p.α B) := by
    rw [mul_sub, htotalPow, hchemExp, hreaction]
    ring
  have hrateDef : wholeLineCauchyChiPosSupercriticalRate p = d := by
    rfl
  rw [hrateDef]
  linarith [hrateGap, hbudget, hfield]

/-! ### Slab maximum principle -/

/-- A nonnegative solution of the expanded resolver PDE stays below the
supercritical relaxing ceiling on a bounded time slab. -/
theorem wholeLineSlab_le_chiPosEquilibriumDescent_of_positive_resolver_pde
    (p : CMParams) (hχ_pos : 0 < p.χ)
    (hsuper : p.m + p.γ - 1 < p.α)
    {T C A : ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0 < T) (hC : chiPosEquilibriumCeiling p ≤ C)
    (hcont : Continuous (fun q : ℝ × ℝ => u q.1 q.2))
    (hnonneg : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 ≤ u t x)
    (hupper : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, u t x ≤ A)
    (hinit : ∀ x, u 0 x ≤ C)
    (htime : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => u s x)
        (deriv (fun s : ℝ => u s x) t) t)
    (hspace1 : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => u t y)
        (deriv (fun y : ℝ => u t y) x) x)
    (hspace2 : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => u t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => u t z) y) x) x)
    (hpde : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      deriv (fun s : ℝ => u s x) t =
        deriv (fun y : ℝ => deriv (fun z : ℝ => u t z) y) x -
          p.χ *
            (p.m * (u t x) ^ (p.m - 1) *
                deriv (fun y : ℝ => u t y) x *
                deriv (frozenElliptic p (u t)) x +
              (u t x) ^ p.m *
                (frozenElliptic p (u t) x - (u t x) ^ p.γ)) +
          reactionFun p.α (u t x)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      u t x ≤ wholeLineCauchyChiPosEquilibriumDescent p C t := by
  let B : ℝ → ℝ := wholeLineCauchyChiPosEquilibriumDescent p C
  let w : ℝ → ℝ → ℝ := fun t x => u t x - B t
  have hA0 : 0 ≤ A := by
    linarith [hnonneg 0 ⟨le_rfl, hT.le⟩ 0,
      hupper 0 ⟨le_rfl, hT.le⟩ 0]
  have hrate_pos : 0 < wholeLineCauchyChiPosSupercriticalRate p :=
    wholeLineCauchyChiPosSupercriticalRate_pos hsuper
  have hbase_one : 1 ≤ chiPosEquilibriumCeiling p :=
    chiPosEquilibriumCeiling_one_le p hχ_pos.le hsuper
  have hbase_pos : 0 < chiPosEquilibriumCeiling p :=
    zero_lt_one.trans_le hbase_one
  have hC0 : 0 ≤ C := hbase_pos.le.trans hC
  have hBbase : ∀ t, chiPosEquilibriumCeiling p ≤ B t := fun t =>
    wholeLineCauchyChiPosEquilibriumDescent_base_le hC t
  have hBC : ∀ t ∈ Set.Icc (0 : ℝ) T, B t ≤ C := by
    intro t ht
    exact wholeLineCauchyChiPosEquilibriumDescent_le hC hsuper ht.1
  have hcontw : Continuous (fun q : ℝ × ℝ => w q.1 q.2) := by
    have hBcont : Continuous B := by
      change Continuous fun t =>
        chiPosEquilibriumCeiling p +
          (C - chiPosEquilibriumCeiling p) *
            Real.exp (-wholeLineCauchyChiPosSupercriticalRate p * t)
      fun_prop
    exact hcont.sub (hBcont.comp continuous_fst)
  have hupperw : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, w t x ≤ A := by
    intro t ht x
    dsimp [w]
    linarith [hupper t ht x, hBbase t, hbase_pos]
  have hinitw : ∀ x, w 0 x ≤ 0 := by
    intro x
    simpa [w, B, wholeLineCauchyChiPosEquilibriumDescent_zero] using hinit x
  have hBderiv : ∀ t, HasDerivAt B
      (-wholeLineCauchyChiPosSupercriticalRate p *
        (B t - chiPosEquilibriumCeiling p)) t := by
    intro t
    have hderiv := wholeLineCauchyChiPosEquilibriumDescent_hasDerivAt p C t
    convert hderiv using 1
    simp [B, wholeLineCauchyChiPosEquilibriumDescent]
  have hdtw : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => w s x)
        (deriv (fun s : ℝ => u s x) t +
          wholeLineCauchyChiPosSupercriticalRate p *
            (B t - chiPosEquilibriumCeiling p)) t := by
    intro t x ht
    dsimp [w]
    convert (htime ht).sub (hBderiv t) using 1
    ring
  have htimew : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => w s x)
        (deriv (fun s : ℝ => w s x) t) t := by
    intro t x ht
    exact (hdtw ht).differentiableAt.hasDerivAt
  have hspace1w : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => w t y)
        (deriv (fun y : ℝ => w t y) x) x := by
    intro t x ht
    have hd := (hspace1 (t := t) (x := x) ht).sub_const (B t)
    simpa [w] using hd.differentiableAt.hasDerivAt
  have hderivw : ∀ t,
      (fun y : ℝ => deriv (fun z : ℝ => w t z) y) =
        fun y : ℝ => deriv (fun z : ℝ => u t z) y := by
    intro t
    funext y
    simp [w, deriv_sub_const]
  have hspace2w : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => w t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => w t z) y) x) x := by
    intro t x ht
    rw [hderivw]
    exact hspace2 ht
  let L : ℝ := wholeLineSlabSup T w
  let K : ℝ := p.χ * p.m * A ^ (p.m - 1) * A ^ p.γ
  let R : ℝ := max C A
  have hR0 : 0 ≤ R := le_max_of_le_left hC0
  let Kreact : ℝ := effectiveReactionLip p R
  let G : ℝ → ℝ := fun r =>
    Kreact * max (-r) 0 -
      wholeLineCauchyChiPosSupercriticalRate p * max r 0
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (mul_nonneg hχ_pos.le
      (zero_le_one.trans p.hm)) (Real.rpow_nonneg hA0 _))
      (Real.rpow_nonneg hA0 _)
  have hKreact : 0 ≤ Kreact := effectiveReactionLip_nonneg hR0
  have hGcont : Continuous G := by
    dsimp [G]
    fun_prop
  have hGstrict : 0 < wholeLineSlabSup T w →
      G (wholeLineSlabSup T w) < 0 := by
    intro hL
    have hL0 : 0 ≤ L := hL.le
    have hnegL : -L ≤ 0 := neg_nonpos.mpr hL0
    dsimp [G]
    rw [max_eq_right hnegL, max_eq_left hL0]
    simpa only [mul_zero, zero_sub, neg_lt_zero] using
      mul_pos hrate_pos hL
  have hpdew : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      deriv (fun s : ℝ => w s x) t ≤
        deriv (fun y : ℝ => deriv (fun z : ℝ => w t z) y) x +
          K * |deriv (fun y : ℝ => w t y) x| + G (w t x) := by
    intro t x ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
    have hu0 : 0 ≤ u t x := hnonneg t htIcc x
    have huA : u t x ≤ A := hupper t htIcc x
    have hwL : w t x ≤ L := le_wholeLineSlabSup hT.le hupperw htIcc x
    have hsliceCont : Continuous (u t) :=
      hcont.comp (continuous_const.prodMk continuous_id)
    have hvxA : |deriv (frozenElliptic p (u t)) x| ≤ A ^ p.γ := by
      have hvA : frozenElliptic p (u t) x ≤ A ^ p.γ :=
        frozenElliptic_le_of_rpow_le p (Real.rpow_nonneg hA0 _) hsliceCont
          (hnonneg t htIcc) (fun y => Real.rpow_le_rpow (hnonneg t htIcc y)
            (hupper t htIcc y) (zero_le_one.trans p.hγ)) x
      exact (frozenElliptic_deriv_abs_le p
        ⟨hsliceCont, ⟨A, fun y => by
          rw [abs_of_nonneg (hnonneg t htIcc y)]
          exact hupper t htIcc y⟩⟩
        (hnonneg t htIcc) x).trans hvA
    have humA : (u t x) ^ (p.m - 1) ≤ A ^ (p.m - 1) :=
      Real.rpow_le_rpow hu0 huA (sub_nonneg.mpr p.hm)
    have hdrift :
        -(p.χ * (p.m * (u t x) ^ (p.m - 1) *
            deriv (fun y : ℝ => u t y) x *
            deriv (frozenElliptic p (u t)) x)) ≤
          K * |deriv (fun y : ℝ => u t y) x| := by
      calc
        -(p.χ * (p.m * (u t x) ^ (p.m - 1) *
              deriv (fun y : ℝ => u t y) x *
              deriv (frozenElliptic p (u t)) x))
            ≤ |p.χ * (p.m * (u t x) ^ (p.m - 1) *
              deriv (fun y : ℝ => u t y) x *
              deriv (frozenElliptic p (u t)) x)| :=
              (le_abs_self _).trans_eq (abs_neg _)
        _ = p.χ * p.m * (u t x) ^ (p.m - 1) *
              |deriv (fun y : ℝ => u t y) x| *
              |deriv (frozenElliptic p (u t)) x| := by
              rw [abs_mul, abs_mul, abs_mul, abs_mul,
                abs_of_pos hχ_pos,
                abs_of_nonneg (zero_le_one.trans p.hm),
                abs_of_nonneg (Real.rpow_nonneg hu0 _)]
              ring
        _ ≤ K * |deriv (fun y : ℝ => u t y) x| := by
              dsimp [K]
              have hux0 : 0 ≤ |deriv (fun y : ℝ => u t y) x| := abs_nonneg _
              have huv :
                  (u t x) ^ (p.m - 1) *
                      |deriv (frozenElliptic p (u t)) x| ≤
                    A ^ (p.m - 1) * A ^ p.γ :=
                mul_le_mul humA hvxA (abs_nonneg _)
                  (Real.rpow_nonneg hA0 _)
              have hcoef : 0 ≤ p.χ * p.m :=
                mul_nonneg hχ_pos.le (zero_le_one.trans p.hm)
              calc
                p.χ * p.m * (u t x) ^ (p.m - 1) *
                      |deriv (fun y : ℝ => u t y) x| *
                      |deriv (frozenElliptic p (u t)) x|
                    = (p.χ * p.m) *
                        |deriv (fun y : ℝ => u t y) x| *
                        ((u t x) ^ (p.m - 1) *
                          |deriv (frozenElliptic p (u t)) x|) := by ring
                _ ≤ (p.χ * p.m) *
                        |deriv (fun y : ℝ => u t y) x| *
                        (A ^ (p.m - 1) * A ^ p.γ) :=
                  mul_le_mul_of_nonneg_left huv (mul_nonneg hcoef hux0)
                _ = p.χ * p.m * A ^ (p.m - 1) * A ^ p.γ *
                      |deriv (fun y : ℝ => u t y) x| := by ring
    have hv_nonneg : 0 ≤ frozenElliptic p (u t) x :=
      frozenElliptic_nonneg p (hnonneg t htIcc) x
    have hchem_favorable :
        -(p.χ * ((u t x) ^ p.m *
            (frozenElliptic p (u t) x - (u t x) ^ p.γ))) ≤
          p.χ * (u t x) ^ p.m * (u t x) ^ p.γ := by
      have hum : 0 ≤ (u t x) ^ p.m := Real.rpow_nonneg hu0 _
      have hnonneg_term :
          0 ≤ p.χ * (u t x) ^ p.m * frozenElliptic p (u t) x :=
        mul_nonneg (mul_nonneg hχ_pos.le hum) hv_nonneg
      nlinarith
    have humγ :
        (u t x) ^ p.m * (u t x) ^ p.γ = (u t x) ^ (p.m + p.γ) := by
      by_cases hu00 : u t x = 0
      · simp only [hu00, Real.zero_rpow (by linarith [p.hm] : p.m ≠ 0),
          Real.zero_rpow (by linarith [p.hγ] : p.γ ≠ 0),
          Real.zero_rpow (by linarith [p.hm, p.hγ] : p.m + p.γ ≠ 0),
          zero_mul]
      · exact (Real.rpow_add
          (lt_of_le_of_ne hu0 (Ne.symm hu00)) p.m p.γ).symm
    have heff_react :
        p.χ * (u t x) ^ p.m * (u t x) ^ p.γ +
            reactionFun p.α (u t x) =
          supercriticalEffectiveReaction p (u t x) := by
      rw [mul_assoc, humγ]
      rfl
    have hreaction :
        supercriticalEffectiveReaction p (u t x) +
          wholeLineCauchyChiPosSupercriticalRate p *
            (B t - chiPosEquilibriumCeiling p) ≤ G (w t x) := by
      by_cases hw0 : 0 ≤ w t x
      · have huBase : chiPosEquilibriumCeiling p ≤ u t x := by
          dsimp [w] at hw0
          linarith [hBbase t]
        have hsuper_u :=
          chiPosEquilibriumDescent_supersolution hχ_pos.le hsuper huBase
        have hsuper_u' :
            supercriticalEffectiveReaction p (u t x) +
                wholeLineCauchyChiPosSupercriticalRate p *
                  (u t x - chiPosEquilibriumCeiling p) ≤ 0 := by
          simpa [supercriticalEffectiveReaction] using hsuper_u
        have hcalc :
            supercriticalEffectiveReaction p (u t x) +
                wholeLineCauchyChiPosSupercriticalRate p *
                  (B t - chiPosEquilibriumCeiling p) =
              (supercriticalEffectiveReaction p (u t x) +
                wholeLineCauchyChiPosSupercriticalRate p *
                  (u t x - chiPosEquilibriumCeiling p)) -
                wholeLineCauchyChiPosSupercriticalRate p *
                  (u t x - B t) := by ring
        dsimp [G]
        rw [max_eq_right (neg_nonpos.mpr hw0), max_eq_left hw0]
        dsimp [w] at hw0 ⊢
        linarith [hcalc]
      · have hwneg : w t x < 0 := lt_of_not_ge hw0
        have huB : u t x ≤ B t := by
          dsimp [w] at hwneg
          linarith
        have hBtR : B t ≤ R :=
          (hBC t htIcc).trans (le_max_left C A)
        have hsuper_B :=
          chiPosEquilibriumDescent_supersolution hχ_pos.le hsuper (hBbase t)
        have hsuper_B' :
            supercriticalEffectiveReaction p (B t) +
                wholeLineCauchyChiPosSupercriticalRate p *
                  (B t - chiPosEquilibriumCeiling p) ≤ 0 := by
          simpa [supercriticalEffectiveReaction] using hsuper_B
        have hLip := supercriticalEffectiveReaction_sub_le
          hχ_pos.le hu0 huB hBtR hR0
        dsimp [G]
        rw [max_eq_left (neg_nonneg.mpr hwneg.le),
          max_eq_right hwneg.le]
        dsimp [w] at hwneg ⊢
        linarith
    have hdt : deriv (fun s : ℝ => w s x) t =
        deriv (fun s : ℝ => u s x) t +
          wholeLineCauchyChiPosSupercriticalRate p *
            (B t - chiPosEquilibriumCeiling p) := (hdtw ht).deriv
    have hd1 : deriv (fun y : ℝ => w t y) x =
        deriv (fun y : ℝ => u t y) x := by
      simp [w, deriv_sub_const]
    have hd2 : deriv (fun y : ℝ => deriv (fun z : ℝ => w t z) y) x =
        deriv (fun y : ℝ => deriv (fun z : ℝ => u t z) y) x := by
      rw [hderivw]
    rw [hdt, hpde ht, hd1, hd2]
    dsimp [G] at hreaction ⊢
    have hkey :
        -(p.χ * (p.m * (u t x) ^ (p.m - 1) *
            deriv (fun y : ℝ => u t y) x *
            deriv (frozenElliptic p (u t)) x +
          (u t x) ^ p.m *
            (frozenElliptic p (u t) x - (u t x) ^ p.γ))) +
        reactionFun p.α (u t x) +
          wholeLineCauchyChiPosSupercriticalRate p *
            (B t - chiPosEquilibriumCeiling p) ≤
          K * |deriv (fun y : ℝ => u t y) x| + G (w t x) := by
      have hsplit :
          -(p.χ * (p.m * (u t x) ^ (p.m - 1) *
              deriv (fun y : ℝ => u t y) x *
              deriv (frozenElliptic p (u t)) x +
            (u t x) ^ p.m *
              (frozenElliptic p (u t) x - (u t x) ^ p.γ)))
          = -(p.χ * (p.m * (u t x) ^ (p.m - 1) *
              deriv (fun y : ℝ => u t y) x *
              deriv (frozenElliptic p (u t)) x)) +
            -(p.χ * ((u t x) ^ p.m *
              (frozenElliptic p (u t) x - (u t x) ^ p.γ))) := by ring
      rw [hsplit]
      have h1 := hdrift
      have h2 := hchem_favorable
      have h3 : p.χ * (u t x) ^ p.m * (u t x) ^ p.γ +
          reactionFun p.α (u t x) +
            wholeLineCauchyChiPosSupercriticalRate p *
              (B t - chiPosEquilibriumCeiling p) ≤
          G (w t x) := by
        rw [heff_react]
        exact hreaction
      linarith
    linarith
  have hwslab : wholeLineSlabSup T w ≤ 0 :=
    wholeLineSlabSup_le_of_scalar_pde hT hK hcontw hupperw hinitw
      hGcont hGstrict htimew hspace1w hspace2w hpdew
  intro t ht x
  have hwle : w t x ≤ wholeLineSlabSup T w :=
    le_wholeLineSlabSup hT.le hupperw ht x
  dsimp [w, B] at hwle ⊢
  linarith

/-! ### Segment-level ceiling propagation -/

/-- One mild fixed-point segment satisfies the supercritical ceiling on the
half-open construction interval. -/
theorem wholeLineCauchyBUCMildFixedPoint_chiPosEquilibriumDescent_Ico
    (p : CMParams) (hχ_pos : 0 < p.χ)
    (hsuper : p.m + p.γ - 1 < p.α)
    {M T C : ℝ} (hM : 0 ≤ M) (hT : 0 < T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M)
    (hC : chiPosEquilibriumCeiling p ≤ C)
    (hinit : ∀ x, u₀.1 x ≤ C) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x,
      (wholeLineBUCTrajectoryExtend hT.le
        (wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall) t).1 x ≤
          wholeLineCauchyChiPosEquilibriumDescent p C t := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall
  let ue : ℝ → ℝ → ℝ := fun t x =>
    (wholeLineBUCTrajectoryExtend hT.le U t).1 x
  have hjoint : Continuous (fun q : ℝ × ℝ => ue q.1 q.2) := by
    have hmap : Continuous
        (fun q : ℝ × ℝ => (Set.projIcc 0 T hT.le q.1, q.2)) :=
      (continuous_projIcc.comp continuous_fst).prodMk continuous_snd
    simpa [ue, wholeLineBUCTrajectoryExtend] using
      (wholeLineBUCTrajectory_jointContinuous U).comp hmap
  intro t ht x
  by_cases ht0 : t = 0
  · subst t
    have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
    have hext0 : wholeLineBUCTrajectoryExtend hT.le U 0 = U ⟨0, hzero⟩ :=
      wholeLineBUCTrajectoryExtend_eq hT.le U hzero
    have hU0 : U ⟨0, hzero⟩ = u₀ := by
      simpa [U] using wholeLineCauchyBUCMildFixedPoint_initial
        p hM hT.le u₀ hsmall hzero
    change (wholeLineBUCTrajectoryExtend hT.le U 0).1 x ≤
      wholeLineCauchyChiPosEquilibriumDescent p C 0
    rw [hext0, hU0, wholeLineCauchyChiPosEquilibriumDescent_zero]
    exact hinit x
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  let S : ℝ := (t + T) / 2
  have hSpos : 0 < S := by
    dsimp [S]
    linarith
  have hST : S < T := by
    dsimp [S]
    linarith [ht.2]
  have htS : t ≤ S := by
    dsimp [S]
    linarith [ht.2]
  have hclosedStrip : ∀ s ∈ Set.Icc (0 : ℝ) S, ∀ y,
      ue s y ∈ Set.Icc (0 : ℝ) M := by
    intro s hs y
    have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans hST.le⟩
    have hext : wholeLineBUCTrajectoryExtend hT.le U s = U ⟨s, hsT⟩ :=
      wholeLineBUCTrajectoryExtend_eq hT.le U hsT
    simpa [ue, hext, U] using hstrip ⟨s, hsT⟩ y
  have hbarrier :=
    wholeLineSlab_le_chiPosEquilibriumDescent_of_positive_resolver_pde
      p hχ_pos hsuper hSpos hC hjoint
      (fun s hs y => (hclosedStrip s hs y).1)
      (fun s hs y => (hclosedStrip s hs y).2)
      (by
        intro y
        have hzeroT : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
        have hext0 : wholeLineBUCTrajectoryExtend hT.le U 0 = U ⟨0, hzeroT⟩ :=
          wholeLineBUCTrajectoryExtend_eq hT.le U hzeroT
        have hU0 : U ⟨0, hzeroT⟩ = u₀ := by
          simpa [U] using wholeLineCauchyBUCMildFixedPoint_initial
            p hM hT.le u₀ hsmall hzeroT
        simpa [ue, hext0, hU0] using hinit y)
      (by
        intro s y hs
        have hsT : s < T := hs.2.trans_lt hST
        simpa [ue, U] using
          (wholeLineCauchyBUCMildFixedPoint_physical_pde_hasDerivAt
            p (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
            hM hT.le u₀ hsmall hs.1 hsT
            (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) hstrip y).differentiableAt.hasDerivAt)
      (by
        intro s y hs
        have hsT : s ∈ Set.Icc (0 : ℝ) T :=
          ⟨hs.1.le, hs.2.trans hST.le⟩
        let zs : Set.Icc (0 : ℝ) T := ⟨s, hsT⟩
        have hext : wholeLineBUCTrajectoryExtend hT.le U s = U zs :=
          wholeLineBUCTrajectoryExtend_eq hT.le U hsT
        change HasDerivAt (fun q : ℝ =>
          (wholeLineBUCTrajectoryExtend hT.le U s).1 q)
          (deriv (fun q : ℝ =>
            (wholeLineBUCTrajectoryExtend hT.le U s).1 q) y) y
        rw [hext]
        simpa [U, zs] using
          (wholeLineCauchyBUCMildFixedPoint_spatial_hasDerivAt_positive
            p hM hT.le u₀ hsmall zs hs.1 y).differentiableAt.hasDerivAt)
      (by
        intro s y hs
        have hsT : s ∈ Set.Icc (0 : ℝ) T :=
          ⟨hs.1.le, hs.2.trans hST.le⟩
        let zs : Set.Icc (0 : ℝ) T := ⟨s, hsT⟩
        have hext : wholeLineBUCTrajectoryExtend hT.le U s = U zs :=
          wholeLineBUCTrajectoryExtend_eq hT.le U hsT
        have hwindow : ∀ r ∈ Set.Icc (s / 2) s, ∀ q,
            (wholeLineBUCTrajectoryExtend hT.le
              (wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall) r).1 q ∈
                Set.Icc (0 : ℝ) M := by
          intro r _hr q
          exact hstrip (Set.projIcc 0 T hT.le r) q
        change HasDerivAt
          (fun q : ℝ => deriv (fun r : ℝ =>
            (wholeLineBUCTrajectoryExtend hT.le U s).1 r) q)
          (deriv (fun q : ℝ => deriv (fun r : ℝ =>
            (wholeLineBUCTrajectoryExtend hT.le U s).1 r) q) y) y
        rw [hext]
        simpa [U, zs] using
          (wholeLineCauchyBUCMildFixedPoint_spatial_second_hasDerivAt_positive
            (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
            p hM hT.le u₀ hsmall zs hs.1
            (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) hwindow y).differentiableAt.hasDerivAt)
      (by
        intro s y hs
        have hsTlt : s < T := hs.2.trans_lt hST
        have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1.le, hsTlt.le⟩
        let zs : Set.Icc (0 : ℝ) T := ⟨s, hsT⟩
        have hext : wholeLineBUCTrajectoryExtend hT.le U s = U zs :=
          wholeLineBUCTrajectoryExtend_eq hT.le U hsT
        have htime :=
          (wholeLineCauchyBUCMildFixedPoint_physical_pde_hasDerivAt
            p (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
            hM hT.le u₀ hsmall hs.1 hsTlt
            (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) hstrip y).deriv
        have hux :=
          (wholeLineCauchyBUCMildFixedPoint_spatial_hasDerivAt_positive
            p hM hT.le u₀ hsmall zs hs.1 y).differentiableAt.hasDerivAt
        have hflux := (wholeLineChemotaxisFlux_hasDerivAt p
          (WholeLineBUC.isCUnifBdd (U zs))
          (fun q => (hstrip zs q).1) hux).deriv
        rw [hflux] at htime
        simpa [ue, U, hext, wholeLineLogisticSource, reactionFun] using htime)
  simpa [ue, U] using hbarrier t ⟨htpos.le, htS⟩ x

/-- Time continuity passes the supercritical ceiling estimate to the closed
construction endpoint. -/
theorem wholeLineCauchyBUCMildFixedPoint_chiPosEquilibriumDescent_Icc
    (p : CMParams) (hχ_pos : 0 < p.χ)
    (hsuper : p.m + p.γ - 1 < p.α)
    {M T C : ℝ} (hM : 0 ≤ M) (hT : 0 < T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M)
    (hC : chiPosEquilibriumCeiling p ≤ C)
    (hinit : ∀ x, u₀.1 x ≤ C) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineBUCTrajectoryExtend hT.le
        (wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall) t).1 x ≤
          wholeLineCauchyChiPosEquilibriumDescent p C t := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall
  have hIco :=
    wholeLineCauchyBUCMildFixedPoint_chiPosEquilibriumDescent_Ico
      p hχ_pos hsuper hM hT u₀ hsmall hstrip hC hinit
  have hjoint : Continuous (fun q : ℝ × ℝ =>
      (wholeLineBUCTrajectoryExtend hT.le U q.1).1 q.2) := by
    have hmap : Continuous
        (fun q : ℝ × ℝ => (Set.projIcc 0 T hT.le q.1, q.2)) :=
      (continuous_projIcc.comp continuous_fst).prodMk continuous_snd
    simpa [wholeLineBUCTrajectoryExtend] using
      (wholeLineBUCTrajectory_jointContinuous U).comp hmap
  intro t ht x
  by_cases htT : t < T
  · simpa [U] using hIco t ⟨ht.1, htT⟩ x
  have hteq : t = T := by linarith [ht.2]
  subst t
  let f : ℝ → ℝ := fun s =>
    (wholeLineBUCTrajectoryExtend hT.le U s).1 x -
      wholeLineCauchyChiPosEquilibriumDescent p C s
  have hfcont : Continuous f := by
    have hucont : Continuous (fun s =>
        (wholeLineBUCTrajectoryExtend hT.le U s).1 x) :=
      hjoint.comp (continuous_id.prodMk continuous_const)
    have hbcont : Continuous
        (wholeLineCauchyChiPosEquilibriumDescent p C) := by
      change Continuous fun t =>
        chiPosEquilibriumCeiling p +
          (C - chiPosEquilibriumCeiling p) *
            Real.exp (-wholeLineCauchyChiPosSupercriticalRate p * t)
      fun_prop
    exact hucont.sub hbcont
  have hlim : Tendsto f (𝓝[<] T) (𝓝 (f T)) :=
    hfcont.continuousAt.tendsto.mono_left inf_le_left
  have hleft : ∀ᶠ s in 𝓝[<] T, s < T := self_mem_nhdsWithin
  have hposNhds : ∀ᶠ s in 𝓝 T, 0 < s := Ioi_mem_nhds hT
  have hpos : ∀ᶠ s in 𝓝[<] T, 0 < s :=
    hposNhds.filter_mono inf_le_left
  have hbound : ∀ᶠ s in 𝓝[<] T, f s ∈ Set.Iic 0 := by
    filter_upwards [hleft, hpos] with s hsT hs0
    exact sub_nonpos.mpr (by
      simpa [U] using hIco s ⟨hs0.le, hsT⟩ x)
  have hfT : f T ≤ 0 := Set.mem_Iic.mp
    (isClosed_Iic.mem_of_tendsto hlim hbound)
  have hfinal := sub_nonpos.mp hfT
  simpa [f, U] using hfinal

/-! ### Step ceiling -/

/-- The supercritical ceiling evaluated at the canonical restart times. -/
def wholeLineCauchyStepChiPosEquilibriumDescent
    (p : CMParams) (u₀ : WholeLineBUC) (C : ℝ) (n : ℕ) : ℝ :=
  wholeLineCauchyChiPosEquilibriumDescent p C
    ((n : ℝ) * wholeLineCauchyGlobalStep p u₀)

theorem wholeLineCauchyStepChiPosEquilibriumDescent_base_le
    (p : CMParams) (u₀ : WholeLineBUC) {C : ℝ}
    (hC : chiPosEquilibriumCeiling p ≤ C) (n : ℕ) :
    chiPosEquilibriumCeiling p ≤
      wholeLineCauchyStepChiPosEquilibriumDescent p u₀ C n :=
  wholeLineCauchyChiPosEquilibriumDescent_base_le hC _

theorem wholeLineCauchyStepChiPosEquilibriumDescent_succ
    (p : CMParams) (u₀ : WholeLineBUC) (C : ℝ) (n : ℕ) :
    wholeLineCauchyChiPosEquilibriumDescent p
        (wholeLineCauchyStepChiPosEquilibriumDescent p u₀ C n)
        (wholeLineCauchyGlobalStep p u₀) =
      wholeLineCauchyStepChiPosEquilibriumDescent p u₀ C (n + 1) := by
  rw [wholeLineCauchyStepChiPosEquilibriumDescent,
    wholeLineCauchyChiPosEquilibriumDescent_restart]
  unfold wholeLineCauchyStepChiPosEquilibriumDescent
  congr 1
  push_cast [Nat.cast_add, Nat.cast_one]
  ring

/-! ### Global propagation -/

/-- The supercritical ceiling propagates through every recursive restart datum
and every complete canonical segment. -/
theorem wholeLineCauchyGlobalDatum_segment_le_chiPosEquilibriumDescent
    (p : CMParams) (hχ_pos : 0 < p.χ)
    (hsuper : p.m + p.γ - 1 < p.α)
    (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (C : ℝ) (hC : chiPosEquilibriumCeiling p ≤ C)
    (hinit : ∀ x, u₀.1 x ≤ C) :
    ∀ n,
      (∀ x, (wholeLineCauchyGlobalDatum p u₀ n).1 x ≤
        wholeLineCauchyStepChiPosEquilibriumDescent p u₀ C n) ∧
      (∀ z x, (wholeLineCauchyGlobalSegment p u₀ n z).1 x ≤
        wholeLineCauchyChiPosEquilibriumDescent p
          (wholeLineCauchyStepChiPosEquilibriumDescent p u₀ C n) z.1) := by
  intro n
  induction n with
  | zero =>
      have hdatum : ∀ x,
          (wholeLineCauchyGlobalDatum p u₀ 0).1 x ≤
            wholeLineCauchyStepChiPosEquilibriumDescent p u₀ C 0 := by
        intro x
        simpa [wholeLineCauchyGlobalDatum,
          wholeLineCauchyStepChiPosEquilibriumDescent,
          wholeLineCauchyChiPosEquilibriumDescent_zero] using hinit x
      refine ⟨hdatum, ?_⟩
      intro z x
      have hstrip :=
        (wholeLineCauchyGlobalDatum_segment_bounds
          p hregime u₀ hu₀ 0).2.1
      have hclosed :=
        wholeLineCauchyBUCMildFixedPoint_chiPosEquilibriumDescent_Icc
          p hχ_pos hsuper
          (wholeLineCauchyGlobalClamp_pos p u₀).le
          (wholeLineCauchyGlobalSegmentTime_pos p u₀)
          (wholeLineCauchyGlobalDatum p u₀ 0)
          (wholeLineCauchyGlobalSegmentTime_rate p u₀)
          (by simpa [wholeLineCauchyGlobalSegment] using hstrip)
          (wholeLineCauchyStepChiPosEquilibriumDescent_base_le
            p u₀ hC 0)
          hdatum
      have hext := wholeLineBUCTrajectoryExtend_eq
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
        (wholeLineCauchyGlobalSegment p u₀ 0) z.2
      rw [← hext]
      simpa [wholeLineCauchyGlobalSegment] using hclosed z.1 z.2 x
  | succ n ih =>
      let δ := wholeLineCauchyGlobalStep p u₀
      let zδ : Set.Icc (0 : ℝ) (wholeLineCauchyGlobalSegmentTime p u₀) :=
        ⟨δ, (wholeLineCauchyGlobalStep_pos p u₀).le,
          by
            dsimp [δ, wholeLineCauchyGlobalStep]
            linarith [wholeLineCauchyGlobalSegmentTime_pos p u₀]⟩
      have hdatum : ∀ x,
          (wholeLineCauchyGlobalDatum p u₀ (n + 1)).1 x ≤
            wholeLineCauchyStepChiPosEquilibriumDescent p u₀ C (n + 1) := by
        intro x
        rw [← wholeLineCauchyStepChiPosEquilibriumDescent_succ p u₀ C n]
        simpa [wholeLineCauchyGlobalDatum, wholeLineCauchyGlobalSegment,
          zδ, δ] using ih.2 zδ x
      refine ⟨by simpa [Nat.succ_eq_add_one] using hdatum, ?_⟩
      intro z x
      have hstrip :=
        (wholeLineCauchyGlobalDatum_segment_bounds
          p hregime u₀ hu₀ (n + 1)).2.1
      have hclosed :=
        wholeLineCauchyBUCMildFixedPoint_chiPosEquilibriumDescent_Icc
          p hχ_pos hsuper
          (wholeLineCauchyGlobalClamp_pos p u₀).le
          (wholeLineCauchyGlobalSegmentTime_pos p u₀)
          (wholeLineCauchyGlobalDatum p u₀ (n + 1))
          (wholeLineCauchyGlobalSegmentTime_rate p u₀)
          (by simpa [wholeLineCauchyGlobalSegment] using hstrip)
          (wholeLineCauchyStepChiPosEquilibriumDescent_base_le
            p u₀ hC (n + 1))
          hdatum
      have hext := wholeLineBUCTrajectoryExtend_eq
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
        (wholeLineCauchyGlobalSegment p u₀ (n + 1)) z.2
      rw [← hext]
      simpa [wholeLineCauchyGlobalSegment] using hclosed z.1 z.2 x

/-- Quantitative global decay of the canonical solution toward the
supercritical parameter ceiling. -/
theorem wholeLineCauchyGlobal_le_chiPosEquilibriumDescent_of_chi_pos
    (p : CMParams) (hχ_pos : 0 < p.χ)
    (hsuper : p.m + p.γ - 1 < p.α)
    (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (C : ℝ) (hC : chiPosEquilibriumCeiling p ≤ C)
    (hinit : ∀ x, u₀.1 x ≤ C)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    wholeLineCauchyGlobalU p u₀ t x ≤
      wholeLineCauchyChiPosEquilibriumDescent p C t := by
  let n := wholeLineCauchyGlobalIndex p u₀ t
  let q := wholeLineCauchyGlobalLocalTime p u₀ t
  let δ := wholeLineCauchyGlobalStep p u₀
  let z : Set.Icc (0 : ℝ) (wholeLineCauchyGlobalSegmentTime p u₀) :=
    ⟨q, wholeLineCauchyGlobalLocalTime_nonneg p u₀ ht,
      (wholeLineCauchyGlobalLocalTime_lt_segmentTime p u₀ ht).le⟩
  have hbound :=
    (wholeLineCauchyGlobalDatum_segment_le_chiPosEquilibriumDescent
      p hχ_pos hsuper hregime u₀ hu₀ C hC hinit n).2 z x
  have heq := congrArg (fun w : WholeLineBUC => w.1 x)
    (wholeLineCauchyGlobalBUC_eq_segment p u₀ ht)
  have heq' : (wholeLineCauchyGlobalBUC p u₀ t).1 x =
      (wholeLineCauchyGlobalSegment p u₀ n z).1 x := by
    simpa [n, q, z] using heq
  have hrestart := wholeLineCauchyChiPosEquilibriumDescent_restart p C
    ((n : ℝ) * δ) q
  change (wholeLineCauchyGlobalBUC p u₀ t).1 x ≤
    wholeLineCauchyChiPosEquilibriumDescent p C t
  rw [heq']
  calc
    (wholeLineCauchyGlobalSegment p u₀ n z).1 x
        ≤ wholeLineCauchyChiPosEquilibriumDescent p
            (wholeLineCauchyStepChiPosEquilibriumDescent p u₀ C n) q :=
      hbound
    _ = wholeLineCauchyChiPosEquilibriumDescent p C
        (((n : ℝ) * δ) + q) := by
      simpa [wholeLineCauchyStepChiPosEquilibriumDescent, δ] using hrestart
    _ = wholeLineCauchyChiPosEquilibriumDescent p C t := by
      congr 1
      dsimp [q, n, δ, wholeLineCauchyGlobalLocalTime]
      ring

/-- The uniform limsup of the canonical solution is at most the explicit
parameter ceiling in the positive-sensitivity supercritical branch. -/
theorem wholeLineCauchyGlobal_uniformLimsupLe_equilibriumCeiling_of_chi_pos_supercritical
    (p : CMParams) (hχ_pos : 0 < p.χ)
    (hsuper : p.m + p.γ - 1 < p.α)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x) :
    UniformLimsupLe (wholeLineCauchyGlobalU p u₀)
      (chiPosEquilibriumCeiling p) := by
  let hregime : WholeLineCauchyCeilingRegime p :=
    Or.inr ⟨hχ_pos.le, Or.inl hsuper⟩
  let C : ℝ := max (chiPosEquilibriumCeiling p) ‖u₀‖
  have hC : chiPosEquilibriumCeiling p ≤ C := le_max_left _ _
  have hinit : ∀ x, u₀.1 x ≤ C := by
    intro x
    exact (WholeLineBUC.apply_le_norm u₀ x).trans (le_max_right _ _)
  have hrate_pos : 0 < wholeLineCauchyChiPosSupercriticalRate p :=
    wholeLineCauchyChiPosSupercriticalRate_pos hsuper
  have hdecay : Tendsto (fun t : ℝ =>
      (C - chiPosEquilibriumCeiling p) *
        Real.exp (-wholeLineCauchyChiPosSupercriticalRate p * t))
      atTop (𝓝 0) := by
    have hexp : Tendsto (fun t : ℝ =>
        Real.exp (-wholeLineCauchyChiPosSupercriticalRate p * t))
        atTop (𝓝 0) := by
      have hcomp : (fun t : ℝ =>
          Real.exp (-wholeLineCauchyChiPosSupercriticalRate p * t)) =
          (fun t : ℝ => Real.exp (-t)) ∘
            (fun t : ℝ => wholeLineCauchyChiPosSupercriticalRate p * t) := by
        ext t
        simp [mul_comm (wholeLineCauchyChiPosSupercriticalRate p) t]
      rw [hcomp]
      exact Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (Filter.tendsto_atTop_atTop_of_monotone
          (fun a b hab => by nlinarith)
          (fun b =>
            ⟨b / wholeLineCauchyChiPosSupercriticalRate p,
              le_of_eq (by field_simp)⟩))
    simpa using tendsto_const_nhds.mul hexp
  intro ε hε
  have hepsNhds : Set.Iio ε ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds hε
  have hsmall : ∀ᶠ t : ℝ in atTop,
      (C - chiPosEquilibriumCeiling p) *
          Real.exp (-wholeLineCauchyChiPosSupercriticalRate p * t) < ε :=
    hdecay.eventually hepsNhds
  filter_upwards [hsmall, eventually_ge_atTop (0 : ℝ)] with t htε ht0
  intro x
  have hbound :=
    wholeLineCauchyGlobal_le_chiPosEquilibriumDescent_of_chi_pos
      p hχ_pos hsuper hregime u₀ hu₀ C hC hinit ht0 x
  dsimp [wholeLineCauchyChiPosEquilibriumDescent] at hbound
  linarith

/-- The canonical global solution is bounded by the larger of the explicit
supercritical parameter ceiling and the norm of its initial datum. -/
theorem wholeLineCauchyGlobal_le_max_equilibriumCeiling_of_chi_pos_supercritical
    (p : CMParams) (hχ_pos : 0 < p.χ)
    (hsuper : p.m + p.γ - 1 < p.α)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    wholeLineCauchyGlobalU p u₀ t x ≤
      max (chiPosEquilibriumCeiling p) ‖u₀‖ := by
  let hregime : WholeLineCauchyCeilingRegime p :=
    Or.inr ⟨hχ_pos.le, Or.inl hsuper⟩
  let C : ℝ := max (chiPosEquilibriumCeiling p) ‖u₀‖
  have hC : chiPosEquilibriumCeiling p ≤ C := by
    dsimp [C]
    exact le_max_left _ _
  have hinit : ∀ y, u₀.1 y ≤ C := by
    intro y
    exact (WholeLineBUC.apply_le_norm u₀ y).trans (le_max_right _ _)
  exact
    (wholeLineCauchyGlobal_le_chiPosEquilibriumDescent_of_chi_pos
      p hχ_pos hsuper hregime u₀ hu₀ C hC hinit ht x).trans
      (wholeLineCauchyChiPosEquilibriumDescent_le hC hsuper ht)


section AxiomAudit

#print axioms chiPosEquilibriumDescent_supersolution
#print axioms wholeLineSlab_le_chiPosEquilibriumDescent_of_positive_resolver_pde
#print axioms wholeLineCauchyGlobal_uniformLimsupLe_equilibriumCeiling_of_chi_pos_supercritical

end AxiomAudit

end ShenWork.Paper1
