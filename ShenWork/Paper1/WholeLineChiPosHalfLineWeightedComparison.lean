import ShenWork.Paper1.WholeLineChiPosWholeLineComparisonNatural

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-!
# Weighted buffered half-line comparisons for positive sensitivity

The scalar contact budgets in this module retain the barrier-value factors
`b ^ m` and `a ^ m`.  The comparison is performed in the co-moving frame, so
the drift `c * q_z` is kept in the first-order part of the half-line maximum
principle.
-/

/-- Exponential damping closes a left-half-line scalar comparison with an
absolute-value zeroth-order error. -/
private theorem leftHalfLine_nonpos_of_linear_abs_pde
    {T x₀ A K L : ℝ} {d : ℝ → ℝ → ℝ}
    (hT : 0 < T) (hA : 0 ≤ A) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hcont : Continuous (fun z : ℝ × ℝ => d z.1 z.2))
    (hupper : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Iic x₀, d t x ≤ A)
    (hinit : ∀ x ∈ Set.Iic x₀, d 0 x ≤ 0)
    (hboundary : ∀ t ∈ Set.Icc (0 : ℝ) T, d t x₀ ≤ 0)
    (htime : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => d s x)
        (deriv (fun s : ℝ => d s x) t) t)
    (hspace1 : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => d t y)
        (deriv (fun y : ℝ => d t y) x) x)
    (hspace2 : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => d t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => d t z) y) x) x)
    (hpde : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T → x < x₀ →
      deriv (fun s : ℝ => d s x) t ≤
        deriv (fun y : ℝ => deriv (fun z : ℝ => d t z) y) x +
          K * |deriv (fun y : ℝ => d t y) x| + L * |d t x|) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Iic x₀, d t x ≤ 0 := by
  let D : ℝ := L + 1
  let E : ℝ → ℝ := fun t => Real.exp (-(D * t))
  let r : ℝ → ℝ → ℝ := fun t x => E t * d t x
  let F : ℝ → ℝ := fun s => L * |s| - D * s
  have hD : 0 < D := by dsimp [D]; linarith
  have hE0 : ∀ t, 0 < E t := fun t => Real.exp_pos _
  have hEone : ∀ t ∈ Set.Icc (0 : ℝ) T, E t ≤ 1 := by
    intro t ht
    dsimp [E]
    simpa using Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (mul_nonneg hD.le ht.1))
  have hcontr : Continuous (fun z : ℝ × ℝ => r z.1 z.2) := by
    have hEcont : Continuous E := by
      dsimp [E]
      fun_prop
    exact (hEcont.comp continuous_fst).mul hcont
  have hupperr : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Iic x₀,
      r t x ≤ A := by
    intro t ht x hx
    calc
      r t x = E t * d t x := rfl
      _ ≤ E t * A := mul_le_mul_of_nonneg_left (hupper t ht x hx) (hE0 t).le
      _ ≤ 1 * A := mul_le_mul_of_nonneg_right (hEone t ht) hA
      _ = A := one_mul _
  have hinitr : ∀ x ∈ Set.Iic x₀, r 0 x ≤ 0 := by
    intro x hx
    simpa [r, E] using hinit x hx
  have hboundaryr : ∀ t ∈ Set.Icc (0 : ℝ) T, r t x₀ ≤ 0 := by
    intro t ht
    exact mul_nonpos_of_nonneg_of_nonpos (hE0 t).le (hboundary t ht)
  have hEderiv : ∀ t, HasDerivAt E (-D * E t) t := by
    intro t
    have hlin : HasDerivAt (fun s : ℝ => -(D * s)) (-D) t := by
      simpa using ((hasDerivAt_id t).const_mul D).neg
    simpa [E, mul_comm] using hlin.exp
  have htimer : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => r s x)
        (deriv (fun s : ℝ => r s x) t) t := by
    intro t x ht
    have hraw := (hEderiv t).mul (htime (t := t) (x := x) ht)
    simpa [r] using hraw.differentiableAt.hasDerivAt
  have hspace1r : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => r t y)
        (deriv (fun y : ℝ => r t y) x) x := by
    intro t x ht
    have hraw := (hspace1 (t := t) (x := x) ht).const_mul (E t)
    simpa [r] using hraw.differentiableAt.hasDerivAt
  have hderivr : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T → ∀ y,
      deriv (fun z : ℝ => r t z) y =
        E t * deriv (fun z : ℝ => d t z) y := by
    intro t ht y
    have hraw := (hspace1 (t := t) (x := y) ht).const_mul (E t)
    simpa [r] using hraw.deriv
  have hspace2r : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => r t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => r t z) y) x) x := by
    intro t x ht
    have hfun : (fun y : ℝ => deriv (fun z : ℝ => r t z) y) =
        fun y => E t * deriv (fun z : ℝ => d t z) y := by
      funext y
      exact hderivr ht y
    rw [hfun]
    exact ((hspace2 (t := t) (x := x) ht).const_mul
      (E t)).differentiableAt.hasDerivAt
  have hFcont : Continuous F := by
    dsimp [F]
    fun_prop
  have hFstrict : 0 < leftHalfLineSlabSup T x₀ r →
      F (leftHalfLineSlabSup T x₀ r) < 0 := by
    intro hsup
    dsimp [F, D]
    rw [abs_of_pos hsup]
    linarith
  have hpder : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T → x < x₀ →
      deriv (fun s : ℝ => r s x) t ≤
        deriv (fun y : ℝ => deriv (fun z : ℝ => r t z) y) x +
          K * |deriv (fun y : ℝ => r t y) x| + F (r t x) := by
    intro t x ht hx
    have hEt0 : 0 < E t := hE0 t
    have hrt : deriv (fun s : ℝ => r s x) t =
        -D * r t x + E t * deriv (fun s : ℝ => d s x) t := by
      have hraw := (hEderiv t).mul (htime (t := t) (x := x) ht)
      convert hraw.deriv using 1 <;> dsimp [r] <;> ring
    have hrx : deriv (fun y : ℝ => r t y) x =
        E t * deriv (fun y : ℝ => d t y) x := hderivr ht x
    have hrxabs : |deriv (fun y : ℝ => r t y) x| =
        E t * |deriv (fun y : ℝ => d t y) x| := by
      rw [hrx, abs_mul, abs_of_pos hEt0]
    have hfun : (fun y : ℝ => deriv (fun z : ℝ => r t z) y) =
        fun y => E t * deriv (fun z : ℝ => d t z) y := by
      funext y
      exact hderivr ht y
    have hrxx : deriv (fun y : ℝ => deriv (fun z : ℝ => r t z) y) x =
        E t * deriv (fun y : ℝ => deriv (fun z : ℝ => d t z) y) x := by
      rw [hfun]
      exact ((hspace2 (t := t) (x := x) ht).const_mul (E t)).deriv
    have hrabs : |r t x| = E t * |d t x| := by
      rw [show r t x = E t * d t x from rfl, abs_mul, abs_of_pos hEt0]
    have hscaled := mul_le_mul_of_nonneg_left (hpde ht hx) hEt0.le
    rw [hrt, hrxx, hrxabs]
    dsimp [F]
    rw [hrabs]
    nlinarith
  have hrsup : leftHalfLineSlabSup T x₀ r ≤ 0 :=
    leftHalfLineSlabSup_le_of_scalar_pde hT hK hcontr hupperr hinitr
      hboundaryr hFcont hFstrict htimer hspace1r hspace2r hpder
  intro t ht x hx
  have hrle : r t x ≤ leftHalfLineSlabSup T x₀ r :=
    le_leftHalfLineSlabSup hT.le hupperr ht hx
  have hr0 : r t x ≤ 0 := hrle.trans hrsup
  dsimp [r] at hr0
  exact nonpos_of_mul_nonpos_left (by simpa [mul_comm] using hr0) (hE0 t)

set_option maxHeartbeats 1600000 in
/-- A reaction subsolution remains below a positive-sensitivity solution on a
whole-line slab when the full resolver gap is budgeted at the barrier value.
-/
theorem leftHalfLine_ge_of_coupled_resolver_reaction_subsolution
    (p : CMParams) (hchi_pos : 0 < p.χ)
    {T x₀ c M G Dup : ℝ} {q : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hT : 0 < T) (hM : 0 ≤ M) (hMG : M ≤ G)
    (hcontq : Continuous (fun z : ℝ × ℝ => q z.1 z.2))
    (hcontb : Continuous b)
    (hqglobal : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      q t x ∈ Set.Icc (0 : ℝ) G)
    (hqleft : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Iic x₀,
      q t x ∈ Set.Icc (0 : ℝ) M)
    (hbrange : ∀ t ∈ Set.Icc (0 : ℝ) T,
      b t ∈ Set.Icc (0 : ℝ) M)
    (hinit : ∀ x ∈ Set.Iic x₀, b 0 ≤ q 0 x)
    (hboundary : ∀ t ∈ Set.Icc (0 : ℝ) T, b t ≤ q t x₀)
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
    (hpdeq : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T → x < x₀ →
      deriv (fun s : ℝ => q s x) t =
        deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x +
          c * deriv (fun y : ℝ => q t y) x -
          p.χ *
            (p.m * (q t x) ^ (p.m - 1) *
                deriv (fun y : ℝ => q t y) x *
                deriv (frozenElliptic p (q t)) x +
              (q t x) ^ p.m *
                (frozenElliptic p (q t) x - (q t x) ^ p.γ)) +
          reactionFun p.α (q t x))
    (hresolver : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T → x < x₀ →
      frozenElliptic p (q t) x ≤ Dup)
    (hpdeb : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      deriv b t + p.χ * (b t) ^ p.m * (Dup - (b t) ^ p.γ) ≤
        reactionFun p.α (b t)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Iic x₀, b t ≤ q t x := by
  let d : ℝ → ℝ → ℝ := fun t x => b t - q t x
  let Kbase : ℝ := reactionLip p.α M
  let Kpow : ℝ := p.χ *
    (Dup * rpowLip p.m M + rpowLip (p.m + p.γ) M)
  let Ksource : ℝ := Kbase + Kpow
  let Kgrad : ℝ :=
    |p.χ| * p.m * M ^ (p.m - 1) * G ^ p.γ
  let K : ℝ := |c| + Kgrad
  have hG : 0 ≤ G := hM.trans hMG
  have hKbase : 0 ≤ Kbase := reactionLip_nonneg p.hα hM
  have hDup0 : 0 ≤ Dup := by
    let t₀ : ℝ := T / 2
    have ht₀ : t₀ ∈ Set.Ioc (0 : ℝ) T := by
      dsimp [t₀]
      constructor <;> linarith
    let y₀ : ℝ := x₀ - 1
    have ht₀Icc : t₀ ∈ Set.Icc (0 : ℝ) T := ⟨ht₀.1.le, ht₀.2⟩
    have hy₀ : y₀ < x₀ := by dsimp [y₀]; linarith
    exact (frozenElliptic_nonneg p
      (fun y => (hqglobal t₀ ht₀Icc y).1) y₀).trans
        (hresolver (t := t₀) (x := y₀) ht₀ hy₀)
  have hKpow : 0 ≤ Kpow := by
    dsimp [Kpow]
    exact mul_nonneg hchi_pos.le (add_nonneg
      (mul_nonneg hDup0 (rpowLip_nonneg p.hm hM))
      (rpowLip_nonneg (by linarith [p.hm, p.hγ]) hM))
  have hKsource : 0 ≤ Ksource := add_nonneg hKbase hKpow
  have hKgrad : 0 ≤ Kgrad := by
    dsimp [Kgrad]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (abs_nonneg _) (zero_le_one.trans p.hm))
          (Real.rpow_nonneg hM _))
      (Real.rpow_nonneg hG _)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hcontd : Continuous (fun z : ℝ × ℝ => d z.1 z.2) := by
    exact (hcontb.comp continuous_fst).sub hcontq
  have hupperd : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Iic x₀,
      d t x ≤ M := by
    intro t ht x hx
    dsimp [d]
    linarith [(hbrange t ht).2, (hqleft t ht x hx).1]
  have hinitd : ∀ x ∈ Set.Iic x₀, d 0 x ≤ 0 := by
    intro x hx
    exact sub_nonpos.mpr (hinit x hx)
  have hboundaryd : ∀ t ∈ Set.Icc (0 : ℝ) T, d t x₀ ≤ 0 := by
    intro t ht
    exact sub_nonpos.mpr (hboundary t ht)
  have htimed : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => d s x)
        (deriv (fun s : ℝ => d s x) t) t := by
    intro t x ht
    have hraw := (htimeb ht).sub (htimeq (t := t) (x := x) ht)
    simpa [d] using hraw.differentiableAt.hasDerivAt
  have hspace1d : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => d t y)
        (deriv (fun y : ℝ => d t y) x) x := by
    intro t x ht
    have hraw := (hspace1q (t := t) (x := x) ht).const_sub (b t)
    simpa [d] using hraw.differentiableAt.hasDerivAt
  have hderivd : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T → ∀ y,
      deriv (fun z : ℝ => d t z) y =
        -deriv (fun z : ℝ => q t z) y := by
    intro t ht y
    have hraw := (hspace1q (t := t) (x := y) ht).const_sub (b t)
    simpa [d] using hraw.deriv
  have hspace2d : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => d t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => d t z) y) x) x := by
    intro t x ht
    have hfun : (fun y : ℝ => deriv (fun z : ℝ => d t z) y) =
        fun y => -deriv (fun z : ℝ => q t z) y := by
      funext y
      exact hderivd ht y
    rw [hfun]
    exact (hspace2q (t := t) (x := x) ht).neg.differentiableAt.hasDerivAt
  have hpderd : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T → x < x₀ →
      deriv (fun s : ℝ => d s x) t ≤
        deriv (fun y : ℝ => deriv (fun z : ℝ => d t z) y) x +
          K * |deriv (fun y : ℝ => d t y) x| +
            Ksource * |d t x| := by
    intro t x ht hx
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
    have hqx := hqleft t htIcc x (Set.mem_Iic.mpr hx.le)
    have hb := hbrange t htIcc
    have hsliceCont : Continuous (q t) :=
      hcontq.comp (continuous_const.prodMk continuous_id)
    have hsliceC : IsCUnifBdd (q t) := by
      refine ⟨hsliceCont, ⟨G, ?_⟩⟩
      intro y
      rw [abs_of_nonneg (hqglobal t htIcc y).1]
      exact (hqglobal t htIcc y).2
    have hvG : frozenElliptic p (q t) x ≤ G ^ p.γ := by
      apply frozenElliptic_le_of_rpow_le p
        (Real.rpow_nonneg hG p.γ) hsliceCont
        (fun y => (hqglobal t htIcc y).1)
      intro y
      exact Real.rpow_le_rpow (hqglobal t htIcc y).1
        (hqglobal t htIcc y).2 (zero_le_one.trans p.hγ)
    have hvxG : |deriv (frozenElliptic p (q t)) x| ≤ G ^ p.γ :=
      (frozenElliptic_deriv_abs_le p hsliceC
        (fun y => (hqglobal t htIcc y).1) x).trans hvG
    have hqmM : (q t x) ^ (p.m - 1) ≤ M ^ (p.m - 1) :=
      Real.rpow_le_rpow hqx.1 hqx.2 (sub_nonneg.mpr p.hm)
    have hdx : deriv (fun y : ℝ => d t y) x =
        -deriv (fun y : ℝ => q t y) x := hderivd ht x
    have hdxabs : |deriv (fun y : ℝ => d t y) x| =
        |deriv (fun y : ℝ => q t y) x| := by
      rw [hdx, abs_neg]
    have hchemGrad :
        p.χ * (p.m * (q t x) ^ (p.m - 1) *
            deriv (fun y : ℝ => q t y) x *
            deriv (frozenElliptic p (q t)) x) ≤
          Kgrad * |deriv (fun y : ℝ => d t y) x| := by
      calc
        p.χ * (p.m * (q t x) ^ (p.m - 1) *
              deriv (fun y : ℝ => q t y) x *
              deriv (frozenElliptic p (q t)) x)
            ≤ |p.χ * (p.m * (q t x) ^ (p.m - 1) *
              deriv (fun y : ℝ => q t y) x *
              deriv (frozenElliptic p (q t)) x)| := le_abs_self _
        _ = |p.χ| * p.m * (q t x) ^ (p.m - 1) *
              |deriv (fun y : ℝ => d t y) x| *
              |deriv (frozenElliptic p (q t)) x| := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul,
            abs_of_nonneg (zero_le_one.trans p.hm),
            abs_of_nonneg (Real.rpow_nonneg hqx.1 _), hdxabs]
          ring
        _ ≤ Kgrad * |deriv (fun y : ℝ => d t y) x| := by
          have hcoef0 : 0 ≤ |p.χ| * p.m :=
            mul_nonneg (abs_nonneg _) (zero_le_one.trans p.hm)
          have hdx0 : 0 ≤ |deriv (fun y : ℝ => d t y) x| := abs_nonneg _
          have hpowV :
              (q t x) ^ (p.m - 1) *
                  |deriv (frozenElliptic p (q t)) x| ≤
                M ^ (p.m - 1) * G ^ p.γ :=
            mul_le_mul hqmM hvxG (abs_nonneg _)
              (Real.rpow_nonneg hM _)
          dsimp [Kgrad]
          calc
            |p.χ| * p.m * (q t x) ^ (p.m - 1) *
                  |deriv (fun y : ℝ => d t y) x| *
                  |deriv (frozenElliptic p (q t)) x| =
                (|p.χ| * p.m) * |deriv (fun y : ℝ => d t y) x| *
                  ((q t x) ^ (p.m - 1) *
                    |deriv (frozenElliptic p (q t)) x|) := by ring
            _ ≤ (|p.χ| * p.m) * |deriv (fun y : ℝ => d t y) x| *
                  (M ^ (p.m - 1) * G ^ p.γ) :=
              mul_le_mul_of_nonneg_left hpowV (mul_nonneg hcoef0 hdx0)
            _ = |p.χ| * p.m * M ^ (p.m - 1) * G ^ p.γ *
                  |deriv (fun y : ℝ => d t y) x| := by ring
    have habsd : |d t x| = |q t x - b t| := by
      dsimp [d]
      rw [abs_sub_comm]
    have hpowAdd : ∀ {z : ℝ}, 0 ≤ z →
        z ^ p.m * z ^ p.γ = z ^ (p.m + p.γ) := by
      intro z hz
      by_cases hz0 : z = 0
      · subst z
        rw [Real.zero_rpow (by linarith [p.hm] : p.m ≠ 0),
          Real.zero_rpow (by linarith [p.hγ] : p.γ ≠ 0),
          Real.zero_rpow (by linarith [p.hm, p.hγ] : p.m + p.γ ≠ 0)]
        ring
      · exact (Real.rpow_add (lt_of_le_of_ne hz (Ne.symm hz0)) p.m p.γ).symm
    have hpowMLip := (rpow_m_lipschitz_on_Icc
      (m := p.m) (M := M) p.hm hM).dist_le_mul
        (q t x) hqx (b t) hb
    rw [Real.coe_toNNReal _ (rpowLip_nonneg p.hm hM)] at hpowMLip
    have hpowMAbs : |(q t x) ^ p.m - (b t) ^ p.m| ≤
        rpowLip p.m M * |q t x - b t| := by
      simpa [Real.dist_eq] using hpowMLip
    have hmγ : 1 ≤ p.m + p.γ := by linarith [p.hm, p.hγ]
    have hpowMγLip := (rpow_m_lipschitz_on_Icc
      (m := p.m + p.γ) (M := M) hmγ hM).dist_le_mul
        (q t x) hqx (b t) hb
    rw [Real.coe_toNNReal _ (rpowLip_nonneg hmγ hM)] at hpowMγLip
    have hpowMγAbs :
        |(q t x) ^ (p.m + p.γ) - (b t) ^ (p.m + p.γ)| ≤
          rpowLip (p.m + p.γ) M * |q t x - b t| := by
      simpa [Real.dist_eq] using hpowMγLip
    have hcore :
        Dup * ((q t x) ^ p.m - (b t) ^ p.m) -
            ((q t x) ^ (p.m + p.γ) - (b t) ^ (p.m + p.γ)) ≤
          (Dup * rpowLip p.m M + rpowLip (p.m + p.γ) M) *
            |q t x - b t| := by
      have hfirst := mul_le_mul_of_nonneg_left hpowMAbs hDup0
      have hfirst' :
          Dup * ((q t x) ^ p.m - (b t) ^ p.m) ≤
            Dup * |(q t x) ^ p.m - (b t) ^ p.m| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hDup0
      have hsecond :
          -((q t x) ^ (p.m + p.γ) - (b t) ^ (p.m + p.γ)) ≤
            |(q t x) ^ (p.m + p.γ) - (b t) ^ (p.m + p.γ)| :=
        neg_le_abs _
      calc
        Dup * ((q t x) ^ p.m - (b t) ^ p.m) -
              ((q t x) ^ (p.m + p.γ) - (b t) ^ (p.m + p.γ)) ≤
            Dup * |(q t x) ^ p.m - (b t) ^ p.m| +
              |(q t x) ^ (p.m + p.γ) - (b t) ^ (p.m + p.γ)| :=
          add_le_add hfirst' hsecond
        _ ≤ Dup * (rpowLip p.m M * |q t x - b t|) +
              rpowLip (p.m + p.γ) M * |q t x - b t| :=
          add_le_add hfirst hpowMγAbs
        _ = (Dup * rpowLip p.m M + rpowLip (p.m + p.γ) M) *
              |q t x - b t| := by ring
    have hcoupledDiff :
        p.χ * (q t x) ^ p.m * (Dup - (q t x) ^ p.γ) -
            p.χ * (b t) ^ p.m * (Dup - (b t) ^ p.γ) ≤
          Kpow * |d t x| := by
      calc
        p.χ * (q t x) ^ p.m * (Dup - (q t x) ^ p.γ) -
              p.χ * (b t) ^ p.m * (Dup - (b t) ^ p.γ) =
            p.χ *
              (Dup * ((q t x) ^ p.m - (b t) ^ p.m) -
                ((q t x) ^ (p.m + p.γ) - (b t) ^ (p.m + p.γ))) := by
          rw [← hpowAdd hqx.1, ← hpowAdd hb.1]
          ring
        _ ≤ p.χ *
              ((Dup * rpowLip p.m M + rpowLip (p.m + p.γ) M) *
                |q t x - b t|) :=
          mul_le_mul_of_nonneg_left hcore hchi_pos.le
        _ = Kpow * |d t x| := by
          rw [habsd]
          dsimp [Kpow]
          ring
    have hchemResolver :
        p.χ * (q t x) ^ p.m *
            (frozenElliptic p (q t) x - (q t x) ^ p.γ) ≤
          p.χ * (q t x) ^ p.m * (Dup - (q t x) ^ p.γ) := by
      exact mul_le_mul_of_nonneg_left
        (sub_le_sub_right (hresolver (t := t) (x := x) ht hx) ((q t x) ^ p.γ))
        (mul_nonneg hchi_pos.le (Real.rpow_nonneg hqx.1 _))
    have hLip := (reaction_lipschitz_on_Icc
      (a := p.α) (M := M) p.hα hM).dist_le_mul
        (b t) hb (q t x) hqx
    rw [Real.coe_toNNReal _ hKbase] at hLip
    have hreaction :
        deriv b t - reactionFun p.α (q t x) ≤
          Kbase * |d t x| -
            p.χ * (b t) ^ p.m * (Dup - (b t) ^ p.γ) := by
      have hdiff : reactionFun p.α (b t) - reactionFun p.α (q t x) ≤
          Kbase * |b t - q t x| := by
        exact (le_abs_self _).trans (by simpa [Real.dist_eq] using hLip)
      have hraw : deriv b t - reactionFun p.α (q t x) ≤
          reactionFun p.α (b t) - reactionFun p.α (q t x) -
            p.χ * (b t) ^ p.m * (Dup - (b t) ^ p.γ) := by
        linarith [hpdeb ht]
      dsimp [d]
      exact hraw.trans (sub_le_sub_right hdiff
        (p.χ * (b t) ^ p.m * (Dup - (b t) ^ p.γ)))
    have hsource :
        p.χ * (q t x) ^ p.m *
              (frozenElliptic p (q t) x - (q t x) ^ p.γ) +
            (deriv b t - reactionFun p.α (q t x)) ≤
          Ksource * |d t x| := by
      dsimp [Ksource]
      nlinarith [hchemResolver, hcoupledDiff, hreaction]
    have hdt : deriv (fun s : ℝ => d s x) t =
        deriv b t - deriv (fun s : ℝ => q s x) t := by
      exact ((htimeb ht).sub (htimeq (t := t) (x := x) ht)).deriv
    have hfun : (fun y : ℝ => deriv (fun z : ℝ => d t z) y) =
        fun y => -deriv (fun z : ℝ => q t z) y := by
      funext y
      exact hderivd ht y
    have hdxx : deriv (fun y : ℝ => deriv (fun z : ℝ => d t z) y) x =
        -deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x := by
      rw [hfun]
      simpa using (hspace2q (t := t) (x := x) ht).neg.deriv
    have hcdrift : c * deriv (fun y : ℝ => d t y) x ≤
        |c| * |deriv (fun y : ℝ => d t y) x| := by
      exact (le_abs_self _).trans (by rw [abs_mul])
    have hcEq : -(c * deriv (fun y : ℝ => q t y) x) =
        c * deriv (fun y : ℝ => d t y) x := by
      rw [hdx]
      ring
    rw [hdt, hpdeq ht hx, hdxx]
    dsimp [K]
    nlinarith [hchemGrad, hsource, hcdrift, hcEq]
  have hdnonpos := leftHalfLine_nonpos_of_linear_abs_pde
    hT hM hK hKsource hcontd hupperd hinitd hboundaryd htimed hspace1d
      hspace2d hpderd
  intro t ht x hx
  exact sub_nonpos.mp (hdnonpos t ht x hx)

set_option maxHeartbeats 1600000 in
/-- A reaction supersolution remains above a positive-sensitivity solution on
a whole-line slab when the resolver lower bound is coupled to the barrier
value. -/
theorem leftHalfLine_le_of_weighted_resolver_reaction_supersolution
    (p : CMParams) (hchi_pos : 0 < p.χ)
    {T x₀ c M G Dlo : ℝ} {q : ℝ → ℝ → ℝ} {a : ℝ → ℝ}
    (hT : 0 < T) (hM : 0 ≤ M) (hMG : M ≤ G)
    (hcontq : Continuous (fun z : ℝ × ℝ => q z.1 z.2))
    (hconta : Continuous a)
    (hqglobal : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      q t x ∈ Set.Icc (0 : ℝ) G)
    (hqleft : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Iic x₀,
      q t x ∈ Set.Icc (0 : ℝ) M)
    (harange : ∀ t ∈ Set.Icc (0 : ℝ) T,
      a t ∈ Set.Icc (0 : ℝ) M)
    (hinit : ∀ x ∈ Set.Iic x₀, q 0 x ≤ a 0)
    (hboundary : ∀ t ∈ Set.Icc (0 : ℝ) T, q t x₀ ≤ a t)
    (htimeq : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => q s x)
        (deriv (fun s : ℝ => q s x) t) t)
    (hspace1q : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => q t y)
        (deriv (fun y : ℝ => q t y) x) x)
    (hspace2q : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => q t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x) x)
    (htimea : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt a (deriv a t) t)
    (hpdeq : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T → x < x₀ →
      deriv (fun s : ℝ => q s x) t =
        deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x +
          c * deriv (fun y : ℝ => q t y) x -
          p.χ *
            (p.m * (q t x) ^ (p.m - 1) *
                deriv (fun y : ℝ => q t y) x *
                deriv (frozenElliptic p (q t)) x +
              (q t x) ^ p.m *
                (frozenElliptic p (q t) x - (q t x) ^ p.γ)) +
          reactionFun p.α (q t x))
    (hresolver : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T → x < x₀ →
      Dlo ≤ frozenElliptic p (q t) x)
    (hpdea : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      reactionFun p.α (a t) +
          p.χ * (a t) ^ p.m * ((a t) ^ p.γ - Dlo) ≤
        deriv a t) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Iic x₀, q t x ≤ a t := by
  let d : ℝ → ℝ → ℝ := fun t x => q t x - a t
  let Kbase : ℝ := reactionLip p.α M
  let Kpow : ℝ := p.χ *
    (rpowLip (p.m + p.γ) M + |Dlo| * rpowLip p.m M)
  let Ksource : ℝ := Kbase + Kpow
  let Kgrad : ℝ :=
    |p.χ| * p.m * M ^ (p.m - 1) * G ^ p.γ
  let K : ℝ := |c| + Kgrad
  have hG : 0 ≤ G := hM.trans hMG
  have hmγ : 1 ≤ p.m + p.γ := by linarith [p.hm, p.hγ]
  have hKbase : 0 ≤ Kbase := reactionLip_nonneg p.hα hM
  have hKpow : 0 ≤ Kpow := by
    dsimp [Kpow]
    exact mul_nonneg hchi_pos.le (add_nonneg
      (rpowLip_nonneg hmγ hM)
      (mul_nonneg (abs_nonneg _) (rpowLip_nonneg p.hm hM)))
  have hKsource : 0 ≤ Ksource := add_nonneg hKbase hKpow
  have hKgrad : 0 ≤ Kgrad := by
    dsimp [Kgrad]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (abs_nonneg _) (zero_le_one.trans p.hm))
          (Real.rpow_nonneg hM _))
      (Real.rpow_nonneg hG _)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hcontd : Continuous (fun z : ℝ × ℝ => d z.1 z.2) := by
    exact hcontq.sub (hconta.comp continuous_fst)
  have hupperd : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Iic x₀,
      d t x ≤ M := by
    intro t ht x hx
    dsimp [d]
    linarith [(hqleft t ht x hx).2, (harange t ht).1]
  have hinitd : ∀ x ∈ Set.Iic x₀, d 0 x ≤ 0 := by
    intro x hx
    exact sub_nonpos.mpr (hinit x hx)
  have hboundaryd : ∀ t ∈ Set.Icc (0 : ℝ) T, d t x₀ ≤ 0 := by
    intro t ht
    exact sub_nonpos.mpr (hboundary t ht)
  have htimed : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => d s x)
        (deriv (fun s : ℝ => d s x) t) t := by
    intro t x ht
    have hraw := (htimeq (t := t) (x := x) ht).sub (htimea ht)
    simpa [d] using hraw.differentiableAt.hasDerivAt
  have hspace1d : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => d t y)
        (deriv (fun y : ℝ => d t y) x) x := by
    intro t x ht
    have hraw := (hspace1q (t := t) (x := x) ht).sub_const (a t)
    simpa [d] using hraw.differentiableAt.hasDerivAt
  have hderivd : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T → ∀ y,
      deriv (fun z : ℝ => d t z) y =
        deriv (fun z : ℝ => q t z) y := by
    intro t ht y
    have hraw := (hspace1q (t := t) (x := y) ht).sub_const (a t)
    simpa [d] using hraw.deriv
  have hspace2d : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => d t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => d t z) y) x) x := by
    intro t x ht
    have hfun : (fun y : ℝ => deriv (fun z : ℝ => d t z) y) =
        fun y => deriv (fun z : ℝ => q t z) y := by
      funext y
      exact hderivd ht y
    rw [hfun]
    exact hspace2q ht
  have hpderd : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T → x < x₀ →
      deriv (fun s : ℝ => d s x) t ≤
        deriv (fun y : ℝ => deriv (fun z : ℝ => d t z) y) x +
          K * |deriv (fun y : ℝ => d t y) x| +
            Ksource * |d t x| := by
    intro t x ht hx
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
    have hqx := hqleft t htIcc x (Set.mem_Iic.mpr hx.le)
    have ha := harange t htIcc
    have hsliceCont : Continuous (q t) :=
      hcontq.comp (continuous_const.prodMk continuous_id)
    have hsliceC : IsCUnifBdd (q t) := by
      refine ⟨hsliceCont, ⟨G, ?_⟩⟩
      intro y
      rw [abs_of_nonneg (hqglobal t htIcc y).1]
      exact (hqglobal t htIcc y).2
    have hvG : frozenElliptic p (q t) x ≤ G ^ p.γ := by
      apply frozenElliptic_le_of_rpow_le p
        (Real.rpow_nonneg hG p.γ) hsliceCont
        (fun y => (hqglobal t htIcc y).1)
      intro y
      exact Real.rpow_le_rpow (hqglobal t htIcc y).1
        (hqglobal t htIcc y).2 (zero_le_one.trans p.hγ)
    have hvxG : |deriv (frozenElliptic p (q t)) x| ≤ G ^ p.γ :=
      (frozenElliptic_deriv_abs_le p hsliceC
        (fun y => (hqglobal t htIcc y).1) x).trans hvG
    have hqmM : (q t x) ^ (p.m - 1) ≤ M ^ (p.m - 1) :=
      Real.rpow_le_rpow hqx.1 hqx.2 (sub_nonneg.mpr p.hm)
    have hdx : deriv (fun y : ℝ => d t y) x =
        deriv (fun y : ℝ => q t y) x := hderivd ht x
    have hchemGrad :
        -(p.χ * (p.m * (q t x) ^ (p.m - 1) *
            deriv (fun y : ℝ => q t y) x *
            deriv (frozenElliptic p (q t)) x)) ≤
          Kgrad * |deriv (fun y : ℝ => d t y) x| := by
      calc
        -(p.χ * (p.m * (q t x) ^ (p.m - 1) *
              deriv (fun y : ℝ => q t y) x *
              deriv (frozenElliptic p (q t)) x))
            ≤ |p.χ * (p.m * (q t x) ^ (p.m - 1) *
              deriv (fun y : ℝ => q t y) x *
              deriv (frozenElliptic p (q t)) x)| :=
          (le_abs_self _).trans_eq (abs_neg _)
        _ = |p.χ| * p.m * (q t x) ^ (p.m - 1) *
              |deriv (fun y : ℝ => d t y) x| *
              |deriv (frozenElliptic p (q t)) x| := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul,
            abs_of_nonneg (zero_le_one.trans p.hm),
            abs_of_nonneg (Real.rpow_nonneg hqx.1 _), hdx]
          ring
        _ ≤ Kgrad * |deriv (fun y : ℝ => d t y) x| := by
          have hcoef0 : 0 ≤ |p.χ| * p.m :=
            mul_nonneg (abs_nonneg _) (zero_le_one.trans p.hm)
          have hdx0 : 0 ≤ |deriv (fun y : ℝ => d t y) x| := abs_nonneg _
          have hpowV :
              (q t x) ^ (p.m - 1) *
                  |deriv (frozenElliptic p (q t)) x| ≤
                M ^ (p.m - 1) * G ^ p.γ :=
            mul_le_mul hqmM hvxG (abs_nonneg _)
              (Real.rpow_nonneg hM _)
          dsimp [Kgrad]
          calc
            |p.χ| * p.m * (q t x) ^ (p.m - 1) *
                  |deriv (fun y : ℝ => d t y) x| *
                  |deriv (frozenElliptic p (q t)) x| =
                (|p.χ| * p.m) * |deriv (fun y : ℝ => d t y) x| *
                  ((q t x) ^ (p.m - 1) *
                    |deriv (frozenElliptic p (q t)) x|) := by ring
            _ ≤ (|p.χ| * p.m) * |deriv (fun y : ℝ => d t y) x| *
                  (M ^ (p.m - 1) * G ^ p.γ) :=
              mul_le_mul_of_nonneg_left hpowV (mul_nonneg hcoef0 hdx0)
            _ = |p.χ| * p.m * M ^ (p.m - 1) * G ^ p.γ *
                  |deriv (fun y : ℝ => d t y) x| := by ring
    have habsd : |d t x| = |q t x - a t| := rfl
    have hpowAdd : ∀ {z : ℝ}, 0 ≤ z →
        z ^ p.m * z ^ p.γ = z ^ (p.m + p.γ) := by
      intro z hz
      by_cases hz0 : z = 0
      · subst z
        rw [Real.zero_rpow (by linarith [p.hm] : p.m ≠ 0),
          Real.zero_rpow (by linarith [p.hγ] : p.γ ≠ 0),
          Real.zero_rpow (by linarith [p.hm, p.hγ] : p.m + p.γ ≠ 0)]
        ring
      · exact (Real.rpow_add (lt_of_le_of_ne hz (Ne.symm hz0)) p.m p.γ).symm
    have hpowMLip := (rpow_m_lipschitz_on_Icc
      (m := p.m) (M := M) p.hm hM).dist_le_mul
        (q t x) hqx (a t) ha
    rw [Real.coe_toNNReal _ (rpowLip_nonneg p.hm hM)] at hpowMLip
    have hpowMAbs : |(q t x) ^ p.m - (a t) ^ p.m| ≤
        rpowLip p.m M * |q t x - a t| := by
      simpa [Real.dist_eq] using hpowMLip
    have hpowMγLip := (rpow_m_lipschitz_on_Icc
      (m := p.m + p.γ) (M := M) hmγ hM).dist_le_mul
        (q t x) hqx (a t) ha
    rw [Real.coe_toNNReal _ (rpowLip_nonneg hmγ hM)] at hpowMγLip
    have hpowMγAbs :
        |(q t x) ^ (p.m + p.γ) - (a t) ^ (p.m + p.γ)| ≤
          rpowLip (p.m + p.γ) M * |q t x - a t| := by
      simpa [Real.dist_eq] using hpowMγLip
    have hDloTerm :
        -(Dlo * ((q t x) ^ p.m - (a t) ^ p.m)) ≤
          |Dlo| * |(q t x) ^ p.m - (a t) ^ p.m| := by
      calc
        -(Dlo * ((q t x) ^ p.m - (a t) ^ p.m)) ≤
            |-(Dlo * ((q t x) ^ p.m - (a t) ^ p.m))| := le_abs_self _
        _ = |Dlo| * |(q t x) ^ p.m - (a t) ^ p.m| := by
          rw [abs_neg, abs_mul]
    have hcore :
        ((q t x) ^ (p.m + p.γ) - (a t) ^ (p.m + p.γ)) -
            Dlo * ((q t x) ^ p.m - (a t) ^ p.m) ≤
          (rpowLip (p.m + p.γ) M + |Dlo| * rpowLip p.m M) *
            |q t x - a t| := by
      have hDloBound := mul_le_mul_of_nonneg_left hpowMAbs (abs_nonneg Dlo)
      calc
        ((q t x) ^ (p.m + p.γ) - (a t) ^ (p.m + p.γ)) -
              Dlo * ((q t x) ^ p.m - (a t) ^ p.m) ≤
            |(q t x) ^ (p.m + p.γ) - (a t) ^ (p.m + p.γ)| +
              |Dlo| * |(q t x) ^ p.m - (a t) ^ p.m| :=
          add_le_add (le_abs_self _) hDloTerm
        _ ≤ rpowLip (p.m + p.γ) M * |q t x - a t| +
              |Dlo| * (rpowLip p.m M * |q t x - a t|) :=
          add_le_add hpowMγAbs hDloBound
        _ = (rpowLip (p.m + p.γ) M + |Dlo| * rpowLip p.m M) *
              |q t x - a t| := by ring
    have hcoupledDiff :
        p.χ * (q t x) ^ p.m * ((q t x) ^ p.γ - Dlo) -
            p.χ * (a t) ^ p.m * ((a t) ^ p.γ - Dlo) ≤
          Kpow * |d t x| := by
      calc
        p.χ * (q t x) ^ p.m * ((q t x) ^ p.γ - Dlo) -
              p.χ * (a t) ^ p.m * ((a t) ^ p.γ - Dlo) =
            p.χ *
              (((q t x) ^ (p.m + p.γ) - (a t) ^ (p.m + p.γ)) -
                Dlo * ((q t x) ^ p.m - (a t) ^ p.m)) := by
          rw [← hpowAdd hqx.1, ← hpowAdd ha.1]
          ring
        _ ≤ p.χ *
              ((rpowLip (p.m + p.γ) M + |Dlo| * rpowLip p.m M) *
                |q t x - a t|) :=
          mul_le_mul_of_nonneg_left hcore hchi_pos.le
        _ = Kpow * |d t x| := by
          rw [habsd]
          dsimp [Kpow]
          ring
    have hchemResolver :
        p.χ * (q t x) ^ p.m *
            ((q t x) ^ p.γ - frozenElliptic p (q t) x) ≤
          p.χ * (q t x) ^ p.m * ((q t x) ^ p.γ - Dlo) := by
      exact mul_le_mul_of_nonneg_left
        (sub_le_sub_left (hresolver (t := t) (x := x) ht hx) ((q t x) ^ p.γ))
        (mul_nonneg hchi_pos.le (Real.rpow_nonneg hqx.1 _))
    have hLip := (reaction_lipschitz_on_Icc
      (a := p.α) (M := M) p.hα hM).dist_le_mul
        (q t x) hqx (a t) ha
    rw [Real.coe_toNNReal _ hKbase] at hLip
    have hreaction :
        reactionFun p.α (q t x) - reactionFun p.α (a t) ≤
          Kbase * |d t x| := by
      exact (le_abs_self _).trans (by simpa [d, Real.dist_eq] using hLip)
    have hsource :
        p.χ * (q t x) ^ p.m *
              ((q t x) ^ p.γ - frozenElliptic p (q t) x) +
            reactionFun p.α (q t x) - deriv a t ≤
          Ksource * |d t x| := by
      dsimp [Ksource]
      nlinarith [hchemResolver, hcoupledDiff, hreaction, hpdea ht]
    have hdt : deriv (fun s : ℝ => d s x) t =
        deriv (fun s : ℝ => q s x) t - deriv a t := by
      exact ((htimeq (t := t) (x := x) ht).sub (htimea ht)).deriv
    have hfun : (fun y : ℝ => deriv (fun z : ℝ => d t z) y) =
        fun y => deriv (fun z : ℝ => q t z) y := by
      funext y
      exact hderivd ht y
    have hdxx : deriv (fun y : ℝ => deriv (fun z : ℝ => d t z) y) x =
        deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x := by
      rw [hfun]
    have hcdrift : c * deriv (fun y : ℝ => d t y) x ≤
        |c| * |deriv (fun y : ℝ => d t y) x| := by
      exact (le_abs_self _).trans (by rw [abs_mul])
    have hcEq : c * deriv (fun y : ℝ => q t y) x =
        c * deriv (fun y : ℝ => d t y) x := by
      rw [hdx]
    rw [hdt, hpdeq ht hx, hdxx]
    dsimp [K]
    nlinarith [hchemGrad, hsource, hcdrift, hcEq]
  have hdnonpos := leftHalfLine_nonpos_of_linear_abs_pde
    hT hM hK hKsource hcontd hupperd hinitd hboundaryd htimed hspace1d
      hspace2d hpderd
  intro t ht x hx
  exact sub_nonpos.mp (hdnonpos t ht x hx)


/-- A weighted scalar floor stays below a positive-sensitivity solution on a
buffered left half-line.  The resolver tail is charged at the barrier value
`b ^ m`; in particular, no constant-in-`b` defect is introduced. -/
theorem leftHalfLine_ge_of_weighted_buffered_chiPos_floor
    (p : CMParams) (hchi_pos : 0 < p.χ)
    {T x₀ R c ell M G : ℝ} {q : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hT : 0 < T) (hR : 0 ≤ R)
    (hell : 0 ≤ ell) (hM : 0 ≤ M) (_hellM : ell ≤ M) (hMG : M ≤ G)
    (hcontq : Continuous (fun z : ℝ × ℝ => q z.1 z.2))
    (hcontb : Continuous b)
    (hqglobal : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      q t x ∈ Set.Icc (0 : ℝ) G)
    (hqlocal : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      x ≤ x₀ + R → q t x ∈ Set.Icc ell M)
    (hbrange : ∀ t ∈ Set.Icc (0 : ℝ) T,
      b t ∈ Set.Icc (0 : ℝ) M)
    (hinit : ∀ x ∈ Set.Iic x₀, b 0 ≤ q 0 x)
    (hbuffer : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ x ∈ Set.Icc x₀ (x₀ + R), b t ≤ q t x)
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
    (hpdeq : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T → x < x₀ →
      deriv (fun s : ℝ => q s x) t =
        deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x +
          c * deriv (fun y : ℝ => q t y) x -
          p.χ *
            (p.m * (q t x) ^ (p.m - 1) *
                deriv (fun y : ℝ => q t y) x *
                deriv (frozenElliptic p (q t)) x +
              (q t x) ^ p.m *
                (frozenElliptic p (q t) x - (q t x) ^ p.γ)) +
          reactionFun p.α (q t x))
    (hpdeb : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      deriv b t ≤
        b t * (1 - (b t) ^ p.α) -
          p.χ * (b t) ^ p.m * (M ^ p.γ - (b t) ^ p.γ) -
          p.χ * (b t) ^ p.m * (Real.exp (-R) / 2) * G ^ p.γ) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Iic x₀, b t ≤ q t x := by
  let tau : ℝ := Real.exp (-R) / 2
  let Dup : ℝ := (1 - tau) * M ^ p.γ + tau * G ^ p.γ
  have hG : 0 ≤ G := hM.trans hMG
  have htau : 0 ≤ tau := by
    dsimp [tau]
    positivity
  refine leftHalfLine_ge_of_coupled_resolver_reaction_subsolution
    p hchi_pos (T := T) (x₀ := x₀) (c := c) (M := M) (G := G)
      (Dup := Dup) (q := q) (b := b) hT hM hMG hcontq hcontb hqglobal
      ?_ hbrange hinit ?_ htimeq hspace1q hspace2q htimeb hpdeq ?_ ?_
  · intro t ht x hx
    have hxR : x ≤ x₀ + R := hx.trans (by linarith)
    have hlocal := hqlocal t ht x hxR
    exact ⟨hell.trans hlocal.1, hlocal.2⟩
  · intro t ht
    exact hbuffer t ht x₀ ⟨le_rfl, by linarith⟩
  · intro t x ht hx
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
    have hsliceCont : Continuous (q t) :=
      hcontq.comp (continuous_const.prodMk continuous_id)
    have hsliceC : IsCUnifBdd (q t) := by
      refine ⟨hsliceCont, ⟨G, ?_⟩⟩
      intro y
      rw [abs_of_nonneg (hqglobal t htIcc y).1]
      exact (hqglobal t htIcc y).2
    dsimp [Dup, tau]
    apply frozenElliptic_upper_of_left_halfLine_ceiling
      p hsliceC (fun y => (hqglobal t htIcc y).1) hM hMG
      (fun y => (hqglobal t htIcc y).2)
      (fun y hy => (hqlocal t htIcc y hy).2) hR
    linarith
  · intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
    have hb0 : 0 ≤ b t := (hbrange t htIcc).1
    have hMpow : 0 ≤ M ^ p.γ := Real.rpow_nonneg hM _
    have hgap : Dup - (b t) ^ p.γ ≤
        (M ^ p.γ - (b t) ^ p.γ) + tau * G ^ p.γ := by
      dsimp [Dup]
      nlinarith [mul_nonneg htau hMpow]
    have hcoeff : 0 ≤ p.χ * (b t) ^ p.m :=
      mul_nonneg hchi_pos.le (Real.rpow_nonneg hb0 _)
    have hweighted := mul_le_mul_of_nonneg_left hgap hcoeff
    have hbudget := hpdeb ht
    rw [show b t * (1 - (b t) ^ p.α) = reactionFun p.α (b t) by rfl]
      at hbudget
    dsimp [tau] at hbudget hweighted
    nlinarith

/-- A weighted scalar ceiling stays above a positive-sensitivity solution on
a buffered left half-line.  The lower resolver estimate gives the exact
`a ^ m`-weighted tail budget. -/
theorem leftHalfLine_le_of_weighted_buffered_chiPos_ceiling
    (p : CMParams) (hchi_pos : 0 < p.χ)
    {T x₀ R c Lhat M G : ℝ} {q : ℝ → ℝ → ℝ} {a : ℝ → ℝ}
    (hT : 0 < T) (hR : 0 ≤ R)
    (hLhat : 0 ≤ Lhat) (hM : 0 ≤ M) (hLhatM : Lhat ≤ M) (hMG : M ≤ G)
    (hcontq : Continuous (fun z : ℝ × ℝ => q z.1 z.2))
    (hconta : Continuous a)
    (hqglobal : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      q t x ∈ Set.Icc (0 : ℝ) G)
    (hqlocal : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      x ≤ x₀ + R → q t x ∈ Set.Icc Lhat M)
    (harange : ∀ t ∈ Set.Icc (0 : ℝ) T,
      a t ∈ Set.Icc (0 : ℝ) M)
    (hinit : ∀ x ∈ Set.Iic x₀, q 0 x ≤ a 0)
    (hbuffer : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ x ∈ Set.Icc x₀ (x₀ + R), q t x ≤ a t)
    (htimeq : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => q s x)
        (deriv (fun s : ℝ => q s x) t) t)
    (hspace1q : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => q t y)
        (deriv (fun y : ℝ => q t y) x) x)
    (hspace2q : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => q t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x) x)
    (htimea : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt a (deriv a t) t)
    (hpdeq : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T → x < x₀ →
      deriv (fun s : ℝ => q s x) t =
        deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x +
          c * deriv (fun y : ℝ => q t y) x -
          p.χ *
            (p.m * (q t x) ^ (p.m - 1) *
                deriv (fun y : ℝ => q t y) x *
                deriv (frozenElliptic p (q t)) x +
              (q t x) ^ p.m *
                (frozenElliptic p (q t) x - (q t x) ^ p.γ)) +
          reactionFun p.α (q t x))
    (hpdea : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      a t * (1 - (a t) ^ p.α) +
          p.χ * (a t) ^ p.m * ((a t) ^ p.γ - Lhat ^ p.γ) +
          p.χ * (a t) ^ p.m * (Real.exp (-R) / 2) * Lhat ^ p.γ ≤
        deriv a t) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Iic x₀, q t x ≤ a t := by
  let tau : ℝ := Real.exp (-R) / 2
  let Dlo : ℝ := (1 - tau) * Lhat ^ p.γ
  refine leftHalfLine_le_of_weighted_resolver_reaction_supersolution
    p hchi_pos (T := T) (x₀ := x₀) (c := c) (M := M) (G := G)
      (Dlo := Dlo) (q := q) (a := a) hT hM hMG hcontq hconta hqglobal
      ?_ harange hinit ?_ htimeq hspace1q hspace2q htimea hpdeq ?_ ?_
  · intro t ht x hx
    have hxR : x ≤ x₀ + R := hx.trans (by linarith)
    have hlocal := hqlocal t ht x hxR
    exact ⟨hLhat.trans hlocal.1, hlocal.2⟩
  · intro t ht
    exact hbuffer t ht x₀ ⟨le_rfl, by linarith⟩
  · intro t x ht hx
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
    have hsliceCont : Continuous (q t) :=
      hcontq.comp (continuous_const.prodMk continuous_id)
    have hsliceC : IsCUnifBdd (q t) := by
      refine ⟨hsliceCont, ⟨G, ?_⟩⟩
      intro y
      rw [abs_of_nonneg (hqglobal t htIcc y).1]
      exact (hqglobal t htIcc y).2
    dsimp [Dlo, tau]
    apply frozenElliptic_lower_of_left_halfLine_floor
      p hsliceC (fun y => (hqglobal t htIcc y).1) hLhat
      (fun y hy => (hqlocal t htIcc y hy).1) hR
    linarith
  · intro t ht
    have hbudget := hpdea ht
    rw [show a t * (1 - (a t) ^ p.α) = reactionFun p.α (a t) by rfl]
      at hbudget
    dsimp [Dlo, tau]
    nlinarith

section AxiomAudit

#print axioms leftHalfLine_ge_of_weighted_buffered_chiPos_floor
#print axioms leftHalfLine_le_of_weighted_buffered_chiPos_ceiling

end AxiomAudit

end ShenWork.Paper1
