import ShenWork.Paper1.UniformTwoSidedConvergence

open Filter Topology MeasureTheory Real Set Function
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section

namespace ShenWork.Paper1

/-!
# Exponentially relaxing floor for nonpositive sensitivity

The floor uses a rate independent of its level.  The slab argument applies the
existing whole-line approximate-maximum principle to an exponentially weighted
positive part of `wholeLineCauchyExpFloor C lam t - u t x`.
-/

set_option maxHeartbeats 800000 in
/-- Moving-floor comparison on a bounded classical slab. -/
theorem wholeLineSlab_ge_expFloor_of_nonpositive_resolver_pde
    (p : CMParams) (hχ : p.χ ≤ 0)
    {T C lam A : ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0 < T) (hlam : 0 < lam) (hlamC : lam ≤ C)
    (hC1 : C ≤ 1) (hα : 1 ≤ p.α)
    (hcont : Continuous (fun q : ℝ × ℝ => u q.1 q.2))
    (hnonneg : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 ≤ u t x)
    (hupper : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, u t x ≤ A)
    (hinit : ∀ x, C ≤ u 0 x)
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
      wholeLineCauchyExpFloor C lam t ≤ u t x := by
  let B : ℝ → ℝ := wholeLineCauchyExpFloor C lam
  have hA0 : 0 ≤ A := by
    linarith [hnonneg 0 ⟨le_rfl, hT.le⟩ 0,
      hupper 0 ⟨le_rfl, hT.le⟩ 0]
  let R : ℝ := A + 1
  have hR0 : 0 ≤ R := by dsimp [R]; linarith
  let Kreact : ℝ := reactionLip p.α R
  have hKreact : 0 ≤ Kreact := reactionLip_nonneg p.hα hR0
  let D : ℝ := Kreact + 1
  have hD : 0 < D := by dsimp [D]; linarith
  let E : ℝ → ℝ := fun t => Real.exp (-(D * t))
  let F : ℝ → ℝ := fun t => Real.exp (D * t)
  let q : ℝ → ℝ → ℝ := fun t x => E t * (B t - u t x)
  have hBge : ∀ t ∈ Set.Icc (0 : ℝ) T, C ≤ B t := by
    intro t ht
    exact wholeLineCauchyExpFloor_ge hC1 hlam.le ht.1
  have hB1 : ∀ t, B t ≤ 1 := by
    intro t
    exact wholeLineCauchyExpFloor_le_one hC1 t
  have hB0 : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 < B t := by
    intro t ht
    exact wholeLineCauchyExpFloor_pos
      (lt_of_lt_of_le hlam hlamC) hC1 hlam.le ht.1
  have hE0 : ∀ t, 0 < E t := fun t => Real.exp_pos _
  have hEF : ∀ t, E t * F t = 1 := by
    intro t
    dsimp [E, F]
    rw [← Real.exp_add]
    ring_nf
    simp
  have hFq : ∀ t x, F t * q t x = B t - u t x := by
    intro t x
    dsimp [q]
    rw [← mul_assoc, mul_comm (F t) (E t), hEF]
    simp
  have hcontq : Continuous (fun z : ℝ × ℝ => q z.1 z.2) := by
    have hBcont : Continuous B := by
      simpa [B, wholeLineCauchyExpFloor] using
        continuous_const.add
          (continuous_const.mul
            (Real.continuous_exp.comp
              (continuous_const.mul continuous_id).neg))
    have hEcont : Continuous E := by
      dsimp [E]
      fun_prop
    exact (hEcont.comp continuous_fst).mul
      ((hBcont.comp continuous_fst).sub hcont)
  have hupperq : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, q t x ≤ 1 := by
    intro t ht x
    have hEt : E t ≤ 1 := by
      dsimp [E]
      simpa using Real.exp_le_one_iff.mpr
        (neg_nonpos.mpr (mul_nonneg hD.le ht.1))
    have hw1 : B t - u t x ≤ 1 := by
      linarith [hB1 t, hnonneg t ht x]
    calc
      q t x = E t * (B t - u t x) := rfl
      _ ≤ E t * 1 := mul_le_mul_of_nonneg_left hw1 (hE0 t).le
      _ ≤ 1 := by simpa using hEt
  have hinitq : ∀ x, q 0 x ≤ 0 := by
    intro x
    simpa [q, E, B, wholeLineCauchyExpFloor_zero] using
      sub_nonpos.mpr (hinit x)
  have hBderiv : ∀ t, HasDerivAt B (lam * (1 - B t)) t := by
    intro t
    convert wholeLineCauchyExpFloor_hasDerivAt C lam t using 1
    all_goals (simp [B, wholeLineCauchyExpFloor]; ring)
  have hEderiv : ∀ t, HasDerivAt E (-D * E t) t := by
    intro t
    have hlin : HasDerivAt (fun s : ℝ => -(D * s)) (-D) t := by
      simpa using ((hasDerivAt_id t).const_mul D).neg
    simpa [E, mul_comm] using hlin.exp
  have hdtq : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => q s x)
        (E t * (lam * (1 - B t) - deriv (fun s : ℝ => u s x) t) -
          D * q t x) t := by
    intro t x ht
    have hw := (hBderiv t).sub (htime (t := t) (x := x) ht)
    convert (hEderiv t).mul hw using 1
    all_goals (dsimp [q]; ring)
  have htimeq : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => q s x)
        (deriv (fun s : ℝ => q s x) t) t := by
    intro t x ht
    exact (hdtq ht).differentiableAt.hasDerivAt
  have hspace1q : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => q t y)
        (deriv (fun y : ℝ => q t y) x) x := by
    intro t x ht
    have hd :=
      ((hspace1 (t := t) (x := x) ht).const_sub (B t)).const_mul (E t)
    simpa [q] using hd.differentiableAt.hasDerivAt
  have hderivq : ∀ t,
      (fun y : ℝ => deriv (fun z : ℝ => q t z) y) =
        fun y : ℝ => -E t * deriv (fun z : ℝ => u t z) y := by
    intro t
    funext y
    simp [q, deriv_const_sub]
  have hspace2q : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => q t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x) x := by
    intro t x ht
    rw [hderivq]
    exact ((hspace2 (t := t) (x := x) ht).const_mul
      (-E t)).differentiableAt.hasDerivAt
  let L : ℝ := wholeLineSlabSup T q
  let K : ℝ := |p.χ| * p.m * A ^ (p.m - 1) * A ^ p.γ
  let Kchem : ℝ := (-p.χ) * A ^ p.m * rpowLip p.γ A
  let G : ℝ → ℝ := fun r =>
    Kchem * (L - r) + (Kreact + D) * max (-r) 0 - max r 0
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (abs_nonneg _) (zero_le_one.trans p.hm))
        (Real.rpow_nonneg hA0 _))
      (Real.rpow_nonneg hA0 _)
  have hKchem : 0 ≤ Kchem := by
    dsimp [Kchem]
    exact mul_nonneg
      (mul_nonneg (by linarith) (Real.rpow_nonneg hA0 _))
      (rpowLip_nonneg p.hγ hA0)
  have hGcont : Continuous G := by
    dsimp [G]
    fun_prop
  have hGstrict : 0 < wholeLineSlabSup T q →
      G (wholeLineSlabSup T q) < 0 := by
    intro hL
    have hL0 : 0 ≤ L := hL.le
    have hnegL : -L ≤ 0 := neg_nonpos.mpr hL0
    dsimp [G]
    rw [max_eq_right hnegL, max_eq_left hL0]
    simp [L]
    simpa [L] using (neg_neg_iff_pos.mpr hL)
  have hpdeq : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      deriv (fun s : ℝ => q s x) t ≤
        deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x +
          K * |deriv (fun y : ℝ => q t y) x| + G (q t x) := by
    intro t x ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
    have hu0 : 0 ≤ u t x := hnonneg t htIcc x
    have huA : u t x ≤ A := hupper t htIcc x
    have hEt0 : 0 < E t := hE0 t
    have hFt0 : 0 < F t := Real.exp_pos _
    have hqL : q t x ≤ L :=
      le_wholeLineSlabSup hT.le hupperq htIcc x
    have hLq0 : 0 ≤ L - q t x := sub_nonneg.mpr hqL
    have hsliceCont : Continuous (u t) :=
      hcont.comp (continuous_const.prodMk continuous_id)
    have hsliceC : IsCUnifBdd (u t) := by
      refine ⟨hsliceCont, ⟨A, ?_⟩⟩
      intro y
      rw [abs_of_nonneg (hnonneg t htIcc y)]
      exact hupper t htIcc y
    have hvA : frozenElliptic p (u t) x ≤ A ^ p.γ := by
      apply frozenElliptic_le_of_rpow_le p
        (Real.rpow_nonneg hA0 p.γ) hsliceCont (hnonneg t htIcc)
      intro y
      exact Real.rpow_le_rpow (hnonneg t htIcc y) (hupper t htIcc y)
        (zero_le_one.trans p.hγ)
    have hvxA : |deriv (frozenElliptic p (u t)) x| ≤ A ^ p.γ :=
      (frozenElliptic_deriv_abs_le p hsliceC (hnonneg t htIcc) x).trans hvA
    have humA : (u t x) ^ (p.m - 1) ≤ A ^ (p.m - 1) :=
      Real.rpow_le_rpow hu0 huA (sub_nonneg.mpr p.hm)
    have hd1 : deriv (fun y : ℝ => q t y) x =
        -E t * deriv (fun y : ℝ => u t y) x := by
      change (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x = _
      rw [hderivq]
    have hd1abs : |deriv (fun y : ℝ => q t y) x| =
        E t * |deriv (fun y : ℝ => u t y) x| := by
      rw [hd1, abs_mul, abs_neg, abs_of_pos hEt0]
    have hdrift :
        E t * (p.χ * (p.m * (u t x) ^ (p.m - 1) *
            deriv (fun y : ℝ => u t y) x *
            deriv (frozenElliptic p (u t)) x)) ≤
          K * |deriv (fun y : ℝ => q t y) x| := by
      calc
        E t * (p.χ * (p.m * (u t x) ^ (p.m - 1) *
              deriv (fun y : ℝ => u t y) x *
              deriv (frozenElliptic p (u t)) x))
            ≤ |E t * (p.χ * (p.m * (u t x) ^ (p.m - 1) *
              deriv (fun y : ℝ => u t y) x *
              deriv (frozenElliptic p (u t)) x))| := le_abs_self _
        _ = |p.χ| * p.m * (u t x) ^ (p.m - 1) *
              |deriv (fun y : ℝ => q t y) x| *
              |deriv (frozenElliptic p (u t)) x| := by
          rw [hd1abs, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul,
            abs_of_pos hEt0,
            abs_of_nonneg (zero_le_one.trans p.hm),
            abs_of_nonneg (Real.rpow_nonneg hu0 _)]
          ring
        _ ≤ K * |deriv (fun y : ℝ => q t y) x| := by
          have hcoef0 : 0 ≤ |p.χ| * p.m :=
            mul_nonneg (abs_nonneg _) (zero_le_one.trans p.hm)
          have hqx0 : 0 ≤ |deriv (fun y : ℝ => q t y) x| := abs_nonneg _
          have huv :
              (u t x) ^ (p.m - 1) *
                  |deriv (frozenElliptic p (u t)) x| ≤
                A ^ (p.m - 1) * A ^ p.γ :=
            mul_le_mul humA hvxA (abs_nonneg _)
              (Real.rpow_nonneg hA0 _)
          dsimp [K]
          calc
            |p.χ| * p.m * (u t x) ^ (p.m - 1) *
                  |deriv (fun y : ℝ => q t y) x| *
                  |deriv (frozenElliptic p (u t)) x|
                = (|p.χ| * p.m) *
                    |deriv (fun y : ℝ => q t y) x| *
                    ((u t x) ^ (p.m - 1) *
                      |deriv (frozenElliptic p (u t)) x|) := by ring
            _ ≤ (|p.χ| * p.m) *
                    |deriv (fun y : ℝ => q t y) x| *
                    (A ^ (p.m - 1) * A ^ p.γ) :=
              mul_le_mul_of_nonneg_left huv (mul_nonneg hcoef0 hqx0)
            _ = |p.χ| * p.m * A ^ (p.m - 1) * A ^ p.γ *
                    |deriv (fun y : ℝ => q t y) x| := by ring
    let a : ℝ := max (B t - F t * L) 0
    have ha0 : 0 ≤ a := by dsimp [a]; exact le_max_right _ _
    have hau : ∀ y, a ≤ u t y := by
      intro y
      have hqyL : q t y ≤ L :=
        le_wholeLineSlabSup hT.le hupperq htIcc y
      have hFqy : F t * q t y ≤ F t * L :=
        mul_le_mul_of_nonneg_left hqyL hFt0.le
      have hbase : B t - F t * L ≤ u t y := by
        rw [hFq] at hFqy
        linarith
      exact max_le hbase (hnonneg t htIcc y)
    have haA : a ≤ A := (hau 0).trans (hupper t htIcc 0)
    have hva : a ^ p.γ ≤ frozenElliptic p (u t) x := by
      apply frozenElliptic_ge_of_rpow_ge p
        (Real.rpow_nonneg hA0 p.γ) (Real.rpow_nonneg ha0 p.γ)
        hsliceCont (hnonneg t htIcc)
      · intro y
        exact Real.rpow_le_rpow (hnonneg t htIcc y) (hupper t htIcc y)
          (zero_le_one.trans p.hγ)
      · intro y
        exact Real.rpow_le_rpow ha0 (hau y) (zero_le_one.trans p.hγ)
    have hua : u t x - a ≤ F t * (L - q t x) := by
      have hbase : B t - F t * L ≤ a := by
        dsimp [a]
        exact le_max_left _ _
      have hx := hFq t x
      linarith
    have hpowdiff : (u t x) ^ p.γ - a ^ p.γ ≤
        rpowLip p.γ A * (F t * (L - q t x)) := by
      have hpoword : a ^ p.γ ≤ (u t x) ^ p.γ :=
        Real.rpow_le_rpow ha0 (hau x) (zero_le_one.trans p.hγ)
      have hLip := (rpow_m_lipschitz_on_Icc
        (m := p.γ) (M := A) p.hγ hA0).dist_le_mul
          (u t x) ⟨hu0, huA⟩ a ⟨ha0, haA⟩
      rw [Real.coe_toNNReal _ (rpowLip_nonneg p.hγ hA0)] at hLip
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hpoword),
        Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hau x))] at hLip
      exact hLip.trans (mul_le_mul_of_nonneg_left hua
        (rpowLip_nonneg p.hγ hA0))
    have humpA : (u t x) ^ p.m ≤ A ^ p.m :=
      Real.rpow_le_rpow hu0 huA (zero_le_one.trans p.hm)
    have hchem :
        E t * (p.χ * ((u t x) ^ p.m *
            (frozenElliptic p (u t) x - (u t x) ^ p.γ))) ≤
          Kchem * (L - q t x) := by
      have hcoef0 : 0 ≤ (-p.χ) * (u t x) ^ p.m :=
        mul_nonneg (by linarith) (Real.rpow_nonneg hu0 _)
      have hpow0 : 0 ≤ (u t x) ^ p.γ - a ^ p.γ :=
        sub_nonneg.mpr (Real.rpow_le_rpow ha0 (hau x)
          (zero_le_one.trans p.hγ))
      have hLip0 : 0 ≤ rpowLip p.γ A := rpowLip_nonneg p.hγ hA0
      calc
        E t * (p.χ * ((u t x) ^ p.m *
              (frozenElliptic p (u t) x - (u t x) ^ p.γ)))
            = E t * (((-p.χ) * (u t x) ^ p.m) *
                ((u t x) ^ p.γ - frozenElliptic p (u t) x)) := by ring
        _ ≤ E t * (((-p.χ) * (u t x) ^ p.m) *
                ((u t x) ^ p.γ - a ^ p.γ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (sub_le_sub_left hva _) hcoef0)
            hEt0.le
        _ ≤ E t * (((-p.χ) * A ^ p.m) *
                ((u t x) ^ p.γ - a ^ p.γ)) := by
          have hcoefA : (-p.χ) * (u t x) ^ p.m ≤
              (-p.χ) * A ^ p.m :=
            mul_le_mul_of_nonneg_left humpA (by linarith)
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hcoefA hpow0) hEt0.le
        _ ≤ E t * (((-p.χ) * A ^ p.m) *
                (rpowLip p.γ A * (F t * (L - q t x)))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hpowdiff
              (mul_nonneg (by linarith) (Real.rpow_nonneg hA0 _)))
            hEt0.le
        _ = Kchem * (L - q t x) := by
          dsimp [Kchem]
          calc
            E t * (-p.χ * A ^ p.m *
                (rpowLip p.γ A * (F t * (L - q t x)))) =
                (E t * F t) *
                  ((-p.χ) * A ^ p.m * rpowLip p.γ A *
                    (L - q t x)) := by ring
            _ = (-p.χ) * A ^ p.m * rpowLip p.γ A *
                  (L - q t x) := by rw [hEF]; ring
    have hBsub : lam * (1 - B t) ≤ reactionFun p.α (B t) := by
      simpa [reactionFun] using expFloor_reaction_dominates hα hlam hlamC
        (hBge t htIcc) (hB1 t)
    have hBtR : B t ≤ R := (hB1 t).trans (by dsimp [R]; linarith)
    have huR : u t x ≤ R := huA.trans (by dsimp [R]; linarith)
    have hLip := (reaction_lipschitz_on_Icc
      (a := p.α) (M := R) p.hα hR0).dist_le_mul
        (B t) ⟨(hB0 t htIcc).le, hBtR⟩ (u t x) ⟨hu0, huR⟩
    rw [Real.coe_toNNReal _ (reactionLip_nonneg p.hα hR0)] at hLip
    have hreaction0 :
        E t * (lam * (1 - B t) - reactionFun p.α (u t x)) ≤
          Kreact * |q t x| := by
      have hdiff : reactionFun p.α (B t) - reactionFun p.α (u t x) ≤
          Kreact * |B t - u t x| := by
        have habs := (le_abs_self
          (reactionFun p.α (B t) - reactionFun p.α (u t x))).trans hLip
        simpa [Real.dist_eq, Kreact] using habs
      have hraw : lam * (1 - B t) - reactionFun p.α (u t x) ≤
          Kreact * |B t - u t x| := by linarith
      have hscaled := mul_le_mul_of_nonneg_left hraw hEt0.le
      have habsq : |q t x| = E t * |B t - u t x| := by
        rw [show q t x = E t * (B t - u t x) from rfl,
          abs_mul, abs_of_pos hEt0]
      rw [habsq]
      nlinarith
    have hreaction :
        E t * (lam * (1 - B t) - reactionFun p.α (u t x)) -
            D * q t x ≤
          (Kreact + D) * max (-(q t x)) 0 - max (q t x) 0 := by
      by_cases hq0 : 0 ≤ q t x
      · rw [max_eq_right (neg_nonpos.mpr hq0), max_eq_left hq0]
        rw [abs_of_nonneg hq0] at hreaction0
        dsimp [D] at hreaction0 ⊢
        linarith
      · have hqneg : q t x < 0 := lt_of_not_ge hq0
        rw [max_eq_left (neg_nonneg.mpr hqneg.le), max_eq_right hqneg.le]
        rw [abs_of_nonpos hqneg.le] at hreaction0
        linarith
    have hdt : deriv (fun s : ℝ => q s x) t =
        E t * (lam * (1 - B t) - deriv (fun s : ℝ => u s x) t) -
          D * q t x := (hdtq ht).deriv
    have hd2 : deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x =
        -E t * deriv (fun y : ℝ => deriv (fun z : ℝ => u t z) y) x := by
      rw [hderivq]
      simp
    rw [hd1] at hdrift
    rw [hdt, hpde ht, hd1, hd2]
    dsimp [G]
    nlinarith [hdrift, hchem, hreaction]
  have hqslab : wholeLineSlabSup T q ≤ 0 :=
    wholeLineSlabSup_le_of_scalar_pde hT hK hcontq hupperq hinitq
      hGcont hGstrict htimeq hspace1q hspace2q hpdeq
  intro t ht x
  have hqle : q t x ≤ wholeLineSlabSup T q :=
    le_wholeLineSlabSup hT.le hupperq ht x
  have hEnonneg : 0 ≤ E t := (hE0 t).le
  dsimp [q, B] at hqle ⊢
  have : E t * (wholeLineCauchyExpFloor C lam t - u t x) ≤ 0 :=
    hqle.trans hqslab
  have hmul :
      (wholeLineCauchyExpFloor C lam t - u t x) * E t ≤ 0 := by
    simpa [mul_comm] using this
  exact sub_nonpos.mp (nonpos_of_mul_nonpos_left hmul (hE0 t))

/-- The moving floor on the strict-interior part of one canonical fixed-point
segment. -/
theorem wholeLineCauchyBUCMildFixedPoint_exp_floor_Ico
    (p : CMParams) (hχ : p.χ ≤ 0)
    {M T C lam : ℝ} (hM : 0 ≤ M) (hT : 0 < T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M)
    (hlam : 0 < lam) (hlamC : lam ≤ C) (hC1 : C ≤ 1)
    (hα : 1 ≤ p.α) (hinit : ∀ x, C ≤ u₀.1 x) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x,
      wholeLineCauchyExpFloor C lam t ≤
        (wholeLineBUCTrajectoryExtend hT.le
          (wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall) t).1 x := by
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
    change wholeLineCauchyExpFloor C lam 0 ≤
      (wholeLineBUCTrajectoryExtend hT.le U 0).1 x
    rw [hext0, hU0, wholeLineCauchyExpFloor_zero]
    exact hinit x
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  let S : ℝ := (t + T) / 2
  have hSpos : 0 < S := by dsimp [S]; linarith
  have hST : S < T := by dsimp [S]; linarith [ht.2]
  have htS : t ≤ S := by dsimp [S]; linarith [ht.2]
  have hclosedStrip : ∀ s ∈ Set.Icc (0 : ℝ) S, ∀ y,
      ue s y ∈ Set.Icc (0 : ℝ) M := by
    intro s hs y
    have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans hST.le⟩
    have hext : wholeLineBUCTrajectoryExtend hT.le U s = U ⟨s, hsT⟩ :=
      wholeLineBUCTrajectoryExtend_eq hT.le U hsT
    simpa [ue, hext, U] using hstrip ⟨s, hsT⟩ y
  have hbarrier := wholeLineSlab_ge_expFloor_of_nonpositive_resolver_pde
    p hχ hSpos hlam hlamC hC1 hα hjoint
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

/-- Time continuity passes the moving floor to the closed construction
endpoint. -/
theorem wholeLineCauchyBUCMildFixedPoint_exp_floor_Icc
    (p : CMParams) (hχ : p.χ ≤ 0)
    {M T C lam : ℝ} (hM : 0 ≤ M) (hT : 0 < T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M)
    (hlam : 0 < lam) (hlamC : lam ≤ C) (hC1 : C ≤ 1)
    (hα : 1 ≤ p.α) (hinit : ∀ x, C ≤ u₀.1 x) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      wholeLineCauchyExpFloor C lam t ≤
        (wholeLineBUCTrajectoryExtend hT.le
          (wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall) t).1 x := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall
  have hIco := wholeLineCauchyBUCMildFixedPoint_exp_floor_Ico
    p hχ hM hT u₀ hsmall hstrip hlam hlamC hC1 hα hinit
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
    wholeLineCauchyExpFloor C lam s -
      (wholeLineBUCTrajectoryExtend hT.le U s).1 x
  have hfcont : Continuous f := by
    have hucont : Continuous (fun s =>
        (wholeLineBUCTrajectoryExtend hT.le U s).1 x) :=
      hjoint.comp (continuous_id.prodMk continuous_const)
    have hbcont : Continuous (wholeLineCauchyExpFloor C lam) := by
      unfold wholeLineCauchyExpFloor
      fun_prop
    exact hbcont.sub hucont
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

def wholeLineCauchyStepExpFloor
    (p : CMParams) (u₀ : WholeLineBUC) (C lam : ℝ) (n : ℕ) : ℝ :=
  wholeLineCauchyExpFloor C lam
    ((n : ℝ) * wholeLineCauchyGlobalStep p u₀)

theorem wholeLineCauchyStepExpFloor_le_one
    (p : CMParams) (u₀ : WholeLineBUC) {C lam : ℝ}
    (hC : C ≤ 1) (n : ℕ) :
    wholeLineCauchyStepExpFloor p u₀ C lam n ≤ 1 :=
  wholeLineCauchyExpFloor_le_one hC _

theorem wholeLineCauchyStepExpFloor_ge
    (p : CMParams) (u₀ : WholeLineBUC) {C lam : ℝ}
    (hC : C ≤ 1) (hlam : 0 ≤ lam) (n : ℕ) :
    C ≤ wholeLineCauchyStepExpFloor p u₀ C lam n := by
  apply wholeLineCauchyExpFloor_ge hC hlam
  exact mul_nonneg (Nat.cast_nonneg n)
    (wholeLineCauchyGlobalStep_pos p u₀).le

theorem wholeLineCauchyStepExpFloor_rate_le
    (p : CMParams) (u₀ : WholeLineBUC) {C lam : ℝ}
    (hlamC : lam ≤ C) (hC : C ≤ 1) (hlam : 0 ≤ lam) (n : ℕ) :
    lam ≤ wholeLineCauchyStepExpFloor p u₀ C lam n :=
  hlamC.trans (wholeLineCauchyStepExpFloor_ge p u₀ hC hlam n)

theorem wholeLineCauchyStepExpFloor_succ
    (p : CMParams) (u₀ : WholeLineBUC) (C lam : ℝ) (n : ℕ) :
    wholeLineCauchyExpFloor
        (wholeLineCauchyStepExpFloor p u₀ C lam n) lam
        (wholeLineCauchyGlobalStep p u₀) =
      wholeLineCauchyStepExpFloor p u₀ C lam (n + 1) := by
  rw [wholeLineCauchyStepExpFloor, wholeLineCauchyExpFloor_restart]
  unfold wholeLineCauchyStepExpFloor
  congr 1
  norm_num [Nat.cast_add, Nat.cast_one]
  ring

/-- The exponential floor propagates through every recursive restart datum
and every complete canonical segment. -/
theorem wholeLineCauchyGlobalDatum_segment_ge_expFloor
    (p : CMParams) (hχ : p.χ ≤ 0)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (C lam : ℝ) (hlam : 0 < lam) (hlamC : lam ≤ C)
    (hC1 : C ≤ 1) (hα : 1 ≤ p.α) (hinit : ∀ x, C ≤ u₀.1 x) :
    ∀ n,
      (∀ x, wholeLineCauchyStepExpFloor p u₀ C lam n ≤
        (wholeLineCauchyGlobalDatum p u₀ n).1 x) ∧
      (∀ z x, wholeLineCauchyExpFloor
          (wholeLineCauchyStepExpFloor p u₀ C lam n) lam z.1 ≤
        (wholeLineCauchyGlobalSegment p u₀ n z).1 x) := by
  let hregime : WholeLineCauchyCeilingRegime p :=
    WholeLineCauchyCeilingRegime.of_nonpositive hχ
  intro n
  induction n with
  | zero =>
      have hdatum : ∀ x,
          wholeLineCauchyStepExpFloor p u₀ C lam 0 ≤
            (wholeLineCauchyGlobalDatum p u₀ 0).1 x := by
        intro x
        simpa [wholeLineCauchyGlobalDatum, wholeLineCauchyStepExpFloor,
          wholeLineCauchyExpFloor_zero] using hinit x
      refine ⟨hdatum, ?_⟩
      intro z x
      have hstrip :=
        (wholeLineCauchyGlobalDatum_segment_bounds
          p hregime u₀ hu₀ 0).2.1
      have hclosed := wholeLineCauchyBUCMildFixedPoint_exp_floor_Icc
        p hχ (wholeLineCauchyGlobalClamp_pos p u₀).le
        (wholeLineCauchyGlobalSegmentTime_pos p u₀)
        (wholeLineCauchyGlobalDatum p u₀ 0)
        (wholeLineCauchyGlobalSegmentTime_rate p u₀)
        (by simpa [wholeLineCauchyGlobalSegment] using hstrip)
        hlam
        (wholeLineCauchyStepExpFloor_rate_le p u₀ hlamC hC1 hlam.le 0)
        (wholeLineCauchyStepExpFloor_le_one p u₀ hC1 0)
        hα hdatum
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
          wholeLineCauchyStepExpFloor p u₀ C lam (n + 1) ≤
            (wholeLineCauchyGlobalDatum p u₀ (n + 1)).1 x := by
        intro x
        rw [← wholeLineCauchyStepExpFloor_succ p u₀ C lam n]
        simpa [wholeLineCauchyGlobalDatum, wholeLineCauchyGlobalSegment,
          zδ, δ] using ih.2 zδ x
      refine ⟨by simpa [Nat.succ_eq_add_one] using hdatum, ?_⟩
      intro z x
      have hstrip :=
        (wholeLineCauchyGlobalDatum_segment_bounds
          p hregime u₀ hu₀ (n + 1)).2.1
      have hclosed := wholeLineCauchyBUCMildFixedPoint_exp_floor_Icc
        p hχ (wholeLineCauchyGlobalClamp_pos p u₀).le
        (wholeLineCauchyGlobalSegmentTime_pos p u₀)
        (wholeLineCauchyGlobalDatum p u₀ (n + 1))
        (wholeLineCauchyGlobalSegmentTime_rate p u₀)
        (by simpa [wholeLineCauchyGlobalSegment] using hstrip)
        hlam
        (wholeLineCauchyStepExpFloor_rate_le
          p u₀ hlamC hC1 hlam.le (n + 1))
        (wholeLineCauchyStepExpFloor_le_one p u₀ hC1 (n + 1))
        hα hdatum
      have hext := wholeLineBUCTrajectoryExtend_eq
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
        (wholeLineCauchyGlobalSegment p u₀ (n + 1)) z.2
      rw [← hext]
      simpa [wholeLineCauchyGlobalSegment] using hclosed z.1 z.2 x

/-- Quantitative global rise of a uniformly positive canonical solution
toward the carrying-capacity floor `1`. -/
theorem wholeLineCauchyGlobal_ge_expFloor_of_chi_nonpos
    (p : CMParams) (hχ : p.χ ≤ 0)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) (hinit : ∀ x, c ≤ u₀.1 x)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    wholeLineCauchyExpFloor c c t ≤ wholeLineCauchyGlobalU p u₀ t x := by
  let n := wholeLineCauchyGlobalIndex p u₀ t
  let q := wholeLineCauchyGlobalLocalTime p u₀ t
  let δ := wholeLineCauchyGlobalStep p u₀
  let z : Set.Icc (0 : ℝ) (wholeLineCauchyGlobalSegmentTime p u₀) :=
    ⟨q, wholeLineCauchyGlobalLocalTime_nonneg p u₀ ht,
      (wholeLineCauchyGlobalLocalTime_lt_segmentTime p u₀ ht).le⟩
  have hbound :=
    (wholeLineCauchyGlobalDatum_segment_ge_expFloor
      p hχ u₀ hu₀ c c hc0 le_rfl hc1 p.hα hinit n).2 z x
  have heq := congrArg (fun w : WholeLineBUC => w.1 x)
    (wholeLineCauchyGlobalBUC_eq_segment p u₀ ht)
  have heq' : (wholeLineCauchyGlobalBUC p u₀ t).1 x =
      (wholeLineCauchyGlobalSegment p u₀ n z).1 x := by
    simpa [n, q, z] using heq
  have hrestart := wholeLineCauchyExpFloor_restart c c
    ((n : ℝ) * δ) q
  change wholeLineCauchyExpFloor c c t ≤
    (wholeLineCauchyGlobalBUC p u₀ t).1 x
  rw [heq']
  calc
    wholeLineCauchyExpFloor c c t =
        wholeLineCauchyExpFloor c c (((n : ℝ) * δ) + q) := by
      congr 1
      dsimp [q, n, δ, wholeLineCauchyGlobalLocalTime]
      ring
    _ = wholeLineCauchyExpFloor
          (wholeLineCauchyStepExpFloor p u₀ c c n) c q := by
      simpa [wholeLineCauchyStepExpFloor, δ] using hrestart.symm
    _ ≤ (wholeLineCauchyGlobalSegment p u₀ n z).1 x := hbound

theorem wholeLineCauchyGlobal_uniformLiminfGe_one_of_chi_nonpos
    (p : CMParams) (hχ : p.χ ≤ 0)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hinit : ∀ x, c ≤ u₀.1 x) :
    UniformLiminfGe (wholeLineCauchyGlobalU p u₀) 1 := by
  intro ε hε
  have hfloor := wholeLineCauchyExpFloor_eventually_ge
    (c := c) (lam := c) hc0 ε hε
  filter_upwards [hfloor, eventually_ge_atTop (0 : ℝ)] with t htFloor ht0
  intro x
  exact htFloor.trans (wholeLineCauchyGlobal_ge_expFloor_of_chi_nonpos
    p hχ u₀ hu₀ c hc0 hc1 hinit ht0 x)

/-- The canonical nonpositive-sensitivity solution converges uniformly to
the carrying capacity from two one-sided envelopes. -/
theorem wholeLineCauchyGlobal_uniformConvergesToConstant_one_of_chi_nonpos
    (p : CMParams) (hχ : p.χ ≤ 0)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hinit : ∀ x, c ≤ u₀.1 x) :
    UniformConvergesToConstant (wholeLineCauchyGlobalU p u₀) 1 :=
  uniformConvergesToConstant_of_limsupLe_liminfGe
    (wholeLineCauchyGlobal_uniformLimsupLe_one_of_chi_nonpos p hχ u₀ hu₀)
    (wholeLineCauchyGlobal_uniformLiminfGe_one_of_chi_nonpos
      p hχ u₀ hu₀ c hc0 hc1 hinit)

end ShenWork.Paper1
