import ShenWork.Paper1.WholeLineWeightedRegularityHalfLineMaximumNatural
import ShenWork.Paper1.WholeLineWeightedRegularityChiZeroKPPFloorNatural

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-!
# Scalar KPP comparison on a fixed left half-line

This file turns the left-half-line maximum principle into the order theorem
needed at zero sensitivity.  Both the initial ordering and the fixed lateral
ordering are explicit.  No whole-line positive floor is assumed.
-/

/-- A time-only scalar reaction subsolution remains below a classical scalar
reaction-diffusion supersolution on `(-infinity,z0]`, provided it is below on
the initial slice and at the fixed lateral boundary. -/
theorem leftHalfLine_ge_of_reaction_subsolution
    {alpha T z₀ c M : ℝ} {q : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (halpha : 1 ≤ alpha) (hT : 0 < T) (hM : 0 ≤ M)
    (hcontq : Continuous (fun p : ℝ × ℝ => q p.1 p.2))
    (hcontb : Continuous b)
    (hqrange : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Iic z₀,
      q t x ∈ Set.Icc (0 : ℝ) M)
    (hbrange : ∀ t ∈ Set.Icc (0 : ℝ) T, b t ∈ Set.Icc (0 : ℝ) M)
    (hinit : ∀ x ∈ Set.Iic z₀, b 0 ≤ q 0 x)
    (hboundary : ∀ t ∈ Set.Icc (0 : ℝ) T, b t ≤ q t z₀)
    (htimeq : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => q s x)
        (deriv (fun s : ℝ => q s x) t) t)
    (hspace1q : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => q t y)
        (deriv (fun y : ℝ => q t y) x) x)
    (hspace2q : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => q t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x) x)
    (htimeb : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt b (deriv b t) t)
    (hpdeq : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T → x < z₀ →
      deriv (fun s : ℝ => q s x) t ≥
        deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x +
          c * deriv (fun y : ℝ => q t y) x + reactionFun alpha (q t x))
    (hpdeb : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      deriv b t ≤ reactionFun alpha (b t)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Iic z₀, b t ≤ q t x := by
  let Kreact : ℝ := reactionLip alpha M
  let D : ℝ := Kreact + 1
  let E : ℝ → ℝ := fun t => Real.exp (-(D * t))
  let r : ℝ → ℝ → ℝ := fun t x => E t * (b t - q t x)
  let G : ℝ → ℝ := fun a => Kreact * |a| - D * a
  have hKreact : 0 ≤ Kreact := reactionLip_nonneg halpha hM
  have hD : 0 < D := by dsimp [D]; linarith
  have hE0 : ∀ t, 0 < E t := fun t => Real.exp_pos _
  have hEone : ∀ t ∈ Set.Icc (0 : ℝ) T, E t ≤ 1 := by
    intro t ht
    dsimp [E]
    simpa using Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (mul_nonneg hD.le ht.1))
  have hcontr : Continuous (fun p : ℝ × ℝ => r p.1 p.2) := by
    have hEcont : Continuous E := by
      dsimp [E]
      fun_prop
    dsimp [r]
    exact (hEcont.comp continuous_fst).mul
      ((hcontb.comp continuous_fst).sub hcontq)
  have hupperr : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Iic z₀,
      r t x ≤ M := by
    intro t ht x hx
    have hdiff : b t - q t x ≤ M := by
      linarith [(hbrange t ht).2, (hqrange t ht x hx).1]
    calc
      r t x = E t * (b t - q t x) := rfl
      _ ≤ E t * M := mul_le_mul_of_nonneg_left hdiff (hE0 t).le
      _ ≤ 1 * M := mul_le_mul_of_nonneg_right (hEone t ht) hM
      _ = M := one_mul _
  have hinitr : ∀ x ∈ Set.Iic z₀, r 0 x ≤ 0 := by
    intro x hx
    simpa [r, E] using sub_nonpos.mpr (hinit x hx)
  have hboundaryr : ∀ t ∈ Set.Icc (0 : ℝ) T, r t z₀ ≤ 0 := by
    intro t ht
    exact mul_nonpos_of_nonneg_of_nonpos (hE0 t).le
      (sub_nonpos.mpr (hboundary t ht))
  have hEderiv : ∀ t, HasDerivAt E (-D * E t) t := by
    intro t
    have hlin : HasDerivAt (fun s : ℝ => -(D * s)) (-D) t := by
      simpa using ((hasDerivAt_id t).const_mul D).neg
    simpa [E, mul_comm] using hlin.exp
  have htimer : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => r s x)
        (deriv (fun s : ℝ => r s x) t) t := by
    intro t x ht
    have hraw := (hEderiv t).mul
      ((htimeb ht).sub (htimeq (t := t) (x := x) ht))
    simpa [r] using hraw.differentiableAt.hasDerivAt
  have hspace1r : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => r t y)
        (deriv (fun y : ℝ => r t y) x) x := by
    intro t x ht
    have hraw := ((hspace1q (t := t) (x := x) ht).const_sub (b t)).const_mul
      (E t)
    simpa [r] using hraw.differentiableAt.hasDerivAt
  have hderivr : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T → ∀ y,
      deriv (fun z : ℝ => r t z) y =
        -E t * deriv (fun z : ℝ => q t z) y := by
    intro t ht y
    have hraw := ((hspace1q (t := t) (x := y) ht).const_sub (b t)).const_mul
      (E t)
    simpa [r] using hraw.deriv
  have hspace2r : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => r t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => r t z) y) x) x := by
    intro t x ht
    have hfun : (fun y : ℝ => deriv (fun z : ℝ => r t z) y) =
        fun y => -E t * deriv (fun z : ℝ => q t z) y := by
      funext y
      exact hderivr ht y
    rw [hfun]
    exact ((hspace2q (t := t) (x := x) ht).const_mul
      (-E t)).differentiableAt.hasDerivAt
  have hGcont : Continuous G := by
    dsimp [G]
    fun_prop
  have hGstrict : 0 < leftHalfLineSlabSup T z₀ r →
      G (leftHalfLineSlabSup T z₀ r) < 0 := by
    intro hL
    have hL0 := hL.le
    dsimp [G, D]
    rw [abs_of_nonneg hL0]
    linarith
  have hpder : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T → x < z₀ →
      deriv (fun s : ℝ => r s x) t ≤
        deriv (fun y : ℝ => deriv (fun z : ℝ => r t z) y) x +
          |c| * |deriv (fun y : ℝ => r t y) x| + G (r t x) := by
    intro t x ht hx
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
    have hq := hqrange t htIcc x (Set.mem_Iic.mpr hx.le)
    have hb := hbrange t htIcc
    have hLip := (reaction_lipschitz_on_Icc
      (a := alpha) (M := M) halpha hM).dist_le_mul
        (b t) hb (q t x) hq
    rw [Real.coe_toNNReal _ hKreact] at hLip
    have hreact : E t *
        (reactionFun alpha (b t) - reactionFun alpha (q t x)) ≤
      Kreact * |r t x| := by
      have hraw : reactionFun alpha (b t) - reactionFun alpha (q t x) ≤
          Kreact * |b t - q t x| := by
        exact (le_abs_self _).trans (by simpa [Real.dist_eq] using hLip)
      have hscaled := mul_le_mul_of_nonneg_left hraw (hE0 t).le
      have habs : |r t x| = E t * |b t - q t x| := by
        rw [show r t x = E t * (b t - q t x) from rfl,
          abs_mul, abs_of_pos (hE0 t)]
      rw [habs]
      nlinarith
    have hrt : deriv (fun s : ℝ => r s x) t =
        -D * E t * (b t - q t x) +
          E t * (deriv b t - deriv (fun s : ℝ => q s x) t) := by
      have hraw := (hEderiv t).mul
        ((htimeb ht).sub (htimeq (t := t) (x := x) ht))
      simpa [r] using hraw.deriv
    have hrx : deriv (fun y : ℝ => r t y) x =
        -E t * deriv (fun y : ℝ => q t y) x := hderivr ht x
    have hfun : (fun y : ℝ => deriv (fun z : ℝ => r t z) y) =
        fun y => -E t * deriv (fun z : ℝ => q t z) y := by
      funext y
      exact hderivr ht y
    have hrxx : deriv (fun y : ℝ => deriv (fun z : ℝ => r t z) y) x =
        -E t *
          deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x := by
      rw [hfun]
      exact ((hspace2q (t := t) (x := x) ht).const_mul (-E t)).deriv
    have hbase : deriv b t - deriv (fun s : ℝ => q s x) t ≤
        -(deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x) -
          c * deriv (fun y : ℝ => q t y) x +
            (reactionFun alpha (b t) - reactionFun alpha (q t x)) := by
      linarith [hpdeb ht, hpdeq ht hx]
    have hscaled := mul_le_mul_of_nonneg_left hbase (hE0 t).le
    have hscaled' : E t *
          (deriv b t - deriv (fun s : ℝ => q s x) t) ≤
        deriv (fun y : ℝ => deriv (fun z : ℝ => r t z) y) x +
          c * deriv (fun y : ℝ => r t y) x +
            E t *
              (reactionFun alpha (b t) - reactionFun alpha (q t x)) := by
      rw [hrxx, hrx]
      linarith
    have hdrift : c * deriv (fun y : ℝ => r t y) x ≤
        |c| * |deriv (fun y : ℝ => r t y) x| := by
      exact (le_abs_self _).trans (by rw [abs_mul])
    rw [hrt]
    dsimp [G]
    have hrid : E t * (b t - q t x) = r t x := rfl
    calc
      -D * E t * (b t - q t x) +
            E t * (deriv b t - deriv (fun s : ℝ => q s x) t)
          ≤ -D * r t x +
              (deriv (fun y : ℝ => deriv (fun z : ℝ => r t z) y) x +
                c * deriv (fun y : ℝ => r t y) x +
                  E t *
                    (reactionFun alpha (b t) - reactionFun alpha (q t x))) := by
            rw [← hrid]
            linarith
      _ ≤ deriv (fun y : ℝ => deriv (fun z : ℝ => r t z) y) x +
              |c| * |deriv (fun y : ℝ => r t y) x| +
                (Kreact * |r t x| - D * r t x) := by
            linarith
  have hsup : leftHalfLineSlabSup T z₀ r ≤ 0 :=
    leftHalfLineSlabSup_le_of_scalar_pde hT (abs_nonneg c) hcontr
      hupperr hinitr hboundaryr hGcont hGstrict
      htimer hspace1r hspace2r hpder
  intro t ht x hx
  have hrle : r t x ≤ leftHalfLineSlabSup T z₀ r :=
    le_leftHalfLineSlabSup hT.le hupperr ht hx
  have hr0 : r t x ≤ 0 := hrle.trans hsup
  dsimp [r] at hr0
  have hEt := hE0 t
  nlinarith

section AxiomAudit

#print axioms leftHalfLine_ge_of_reaction_subsolution

end AxiomAudit

end ShenWork.Paper1
