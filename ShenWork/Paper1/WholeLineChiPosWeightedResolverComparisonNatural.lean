import ShenWork.Paper1.WholeLineChiPosBufferedComparisonNatural

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-!
# Weighted positive-sensitivity resolver comparison

At a lower contact the positive-sensitivity resolver loss carries the same
`b ^ m` factor as the scalar barrier.  Away from contact, the Lipschitz bound
for `s \mapsto s ^ m` absorbs the discrepancy into the scalar maximum-principle
error term.
-/

set_option maxHeartbeats 1600000 in
/-- A scalar reaction subsolution remains below a positive-sensitivity
solution when the resolver loss is budgeted with the barrier weight `b ^ m`.
-/
theorem leftHalfLine_ge_of_weighted_resolver_reaction_subsolution
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
      deriv b t + p.χ * (b t) ^ p.m * Dup ≤
        reactionFun p.α (b t)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Iic x₀, b t ≤ q t x := by
  let Kbase : ℝ := reactionLip p.α M
  have hKbase : 0 ≤ Kbase := reactionLip_nonneg p.hα hM
  have hDup0 : 0 ≤ Dup := by
    let t₀ : ℝ := T / 2
    let y₀ : ℝ := x₀ - 1
    have ht₀ : t₀ ∈ Set.Ioc (0 : ℝ) T := by
      dsimp [t₀]
      constructor <;> linarith
    have ht₀' : t₀ ∈ Set.Icc (0 : ℝ) T := ⟨ht₀.1.le, ht₀.2⟩
    have hy₀ : y₀ < x₀ := by dsimp [y₀]; linarith
    exact (frozenElliptic_nonneg p
      (fun y => (hqglobal t₀ ht₀' y).1) y₀).trans (hresolver ht₀ hy₀)
  let Kpow : ℝ := p.χ * Dup * rpowLip p.m M
  have hKpow : 0 ≤ Kpow := by
    dsimp [Kpow]
    exact mul_nonneg (mul_nonneg hchi_pos.le hDup0)
      (rpowLip_nonneg p.hm hM)
  let Kreact : ℝ := Kbase + Kpow
  let D : ℝ := Kreact + 1
  let E : ℝ → ℝ := fun t => Real.exp (-(D * t))
  let r : ℝ → ℝ → ℝ := fun t x => E t * (b t - q t x)
  let Kgrad : ℝ :=
    |p.χ| * p.m * M ^ (p.m - 1) * G ^ p.γ
  let K : ℝ := |c| + Kgrad
  let F : ℝ → ℝ := fun a => Kreact * |a| - D * a
  have hG0 : 0 ≤ G := hM.trans hMG
  have hKreact : 0 ≤ Kreact := add_nonneg hKbase hKpow
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
    dsimp [r]
    exact (hEcont.comp continuous_fst).mul
      ((hcontb.comp continuous_fst).sub hcontq)
  have hupperr : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Iic x₀,
      r t x ≤ M := by
    intro t ht x hx
    have hdiff : b t - q t x ≤ M := by
      linarith [(hbrange t ht).2, (hqleft t ht x hx).1]
    calc
      r t x = E t * (b t - q t x) := rfl
      _ ≤ E t * M := mul_le_mul_of_nonneg_left hdiff (hE0 t).le
      _ ≤ 1 * M := mul_le_mul_of_nonneg_right (hEone t ht) hM
      _ = M := one_mul _
  have hinitr : ∀ x ∈ Set.Iic x₀, r 0 x ≤ 0 := by
    intro x hx
    simpa [r, E] using sub_nonpos.mpr (hinit x hx)
  have hboundaryr : ∀ t ∈ Set.Icc (0 : ℝ) T, r t x₀ ≤ 0 := by
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
  have hKgrad : 0 ≤ Kgrad := by
    dsimp [Kgrad]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (abs_nonneg _) (zero_le_one.trans p.hm))
          (Real.rpow_nonneg hM _))
      (Real.rpow_nonneg hG0 _)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hFcont : Continuous F := by
    dsimp [F]
    fun_prop
  have hFstrict : 0 < leftHalfLineSlabSup T x₀ r →
      F (leftHalfLineSlabSup T x₀ r) < 0 := by
    intro hL
    have hL0 := hL.le
    dsimp [F, D]
    rw [abs_of_nonneg hL0]
    linarith
  have hpder : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T → x < x₀ →
      deriv (fun s : ℝ => r s x) t ≤
        deriv (fun y : ℝ => deriv (fun z : ℝ => r t z) y) x +
          K * |deriv (fun y : ℝ => r t y) x| + F (r t x) := by
    intro t x ht hx
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
    have hqx := hqleft t htIcc x (Set.mem_Iic.mpr hx.le)
    have hb := hbrange t htIcc
    have hEt0 : 0 < E t := hE0 t
    have hsliceCont : Continuous (q t) :=
      hcontq.comp (continuous_const.prodMk continuous_id)
    have hsliceC : IsCUnifBdd (q t) := by
      refine ⟨hsliceCont, ⟨G, ?_⟩⟩
      intro y
      rw [abs_of_nonneg (hqglobal t htIcc y).1]
      exact (hqglobal t htIcc y).2
    have hvG : frozenElliptic p (q t) x ≤ G ^ p.γ := by
      apply frozenElliptic_le_of_rpow_le p
        (Real.rpow_nonneg hG0 p.γ) hsliceCont
        (fun y => (hqglobal t htIcc y).1)
      intro y
      exact Real.rpow_le_rpow (hqglobal t htIcc y).1
        (hqglobal t htIcc y).2 (zero_le_one.trans p.hγ)
    have hvxG : |deriv (frozenElliptic p (q t)) x| ≤ G ^ p.γ :=
      (frozenElliptic_deriv_abs_le p hsliceC
        (fun y => (hqglobal t htIcc y).1) x).trans hvG
    have hqmM : (q t x) ^ (p.m - 1) ≤ M ^ (p.m - 1) :=
      Real.rpow_le_rpow hqx.1 hqx.2 (sub_nonneg.mpr p.hm)
    have hrx : deriv (fun y : ℝ => r t y) x =
        -E t * deriv (fun y : ℝ => q t y) x := hderivr ht x
    have hrxabs : |deriv (fun y : ℝ => r t y) x| =
        E t * |deriv (fun y : ℝ => q t y) x| := by
      rw [hrx, abs_mul, abs_neg, abs_of_pos hEt0]
    have hchemGrad :
        E t * (p.χ * (p.m * (q t x) ^ (p.m - 1) *
            deriv (fun y : ℝ => q t y) x *
            deriv (frozenElliptic p (q t)) x)) ≤
          Kgrad * |deriv (fun y : ℝ => r t y) x| := by
      calc
        E t * (p.χ * (p.m * (q t x) ^ (p.m - 1) *
              deriv (fun y : ℝ => q t y) x *
              deriv (frozenElliptic p (q t)) x))
            ≤ |E t * (p.χ * (p.m * (q t x) ^ (p.m - 1) *
              deriv (fun y : ℝ => q t y) x *
              deriv (frozenElliptic p (q t)) x))| := le_abs_self _
        _ = |p.χ| * p.m * (q t x) ^ (p.m - 1) *
              |deriv (fun y : ℝ => r t y) x| *
              |deriv (frozenElliptic p (q t)) x| := by
          rw [hrxabs, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul,
            abs_of_pos hEt0, abs_of_nonneg (zero_le_one.trans p.hm),
            abs_of_nonneg (Real.rpow_nonneg hqx.1 _)]
          ring
        _ ≤ Kgrad * |deriv (fun y : ℝ => r t y) x| := by
          have hcoef0 : 0 ≤ |p.χ| * p.m :=
            mul_nonneg (abs_nonneg _) (zero_le_one.trans p.hm)
          have hrx0 : 0 ≤ |deriv (fun y : ℝ => r t y) x| := abs_nonneg _
          have hpowV :
              (q t x) ^ (p.m - 1) *
                  |deriv (frozenElliptic p (q t)) x| ≤
                M ^ (p.m - 1) * G ^ p.γ :=
            mul_le_mul hqmM hvxG (abs_nonneg _)
              (Real.rpow_nonneg hM _)
          dsimp [Kgrad]
          calc
            |p.χ| * p.m * (q t x) ^ (p.m - 1) *
                  |deriv (fun y : ℝ => r t y) x| *
                  |deriv (frozenElliptic p (q t)) x| =
                (|p.χ| * p.m) * |deriv (fun y : ℝ => r t y) x| *
                  ((q t x) ^ (p.m - 1) *
                    |deriv (frozenElliptic p (q t)) x|) := by ring
            _ ≤ (|p.χ| * p.m) * |deriv (fun y : ℝ => r t y) x| *
                  (M ^ (p.m - 1) * G ^ p.γ) :=
              mul_le_mul_of_nonneg_left hpowV (mul_nonneg hcoef0 hrx0)
            _ = |p.χ| * p.m * M ^ (p.m - 1) * G ^ p.γ *
                  |deriv (fun y : ℝ => r t y) x| := by ring
    have hpowLip := (rpow_m_lipschitz_on_Icc
      (m := p.m) (M := M) p.hm hM).dist_le_mul
        (q t x) hqx (b t) hb
    rw [Real.coe_toNNReal _ (rpowLip_nonneg p.hm hM)] at hpowLip
    have hpowAbs : |(q t x) ^ p.m - (b t) ^ p.m| ≤
        rpowLip p.m M * |q t x - b t| := by
      simpa [Real.dist_eq] using hpowLip
    have hpowUpper : (q t x) ^ p.m ≤
        (b t) ^ p.m + rpowLip p.m M * |q t x - b t| := by
      linarith [le_abs_self ((q t x) ^ p.m - (b t) ^ p.m)]
    have hresolverGap :
        frozenElliptic p (q t) x - (q t x) ^ p.γ ≤ Dup := by
      have hqγ0 : 0 ≤ (q t x) ^ p.γ := Real.rpow_nonneg hqx.1 _
      linarith [hresolver ht hx]
    have habsr : |r t x| = E t * |q t x - b t| := by
      rw [show r t x = E t * (b t - q t x) from rfl,
        abs_mul, abs_of_pos hEt0, abs_sub_comm]
    have hchemZero :
        E t * (p.χ * (q t x) ^ p.m *
          (frozenElliptic p (q t) x - (q t x) ^ p.γ)) ≤
            Kpow * |r t x| +
              E t * (p.χ * (b t) ^ p.m * Dup) := by
      calc
        E t * (p.χ * (q t x) ^ p.m *
            (frozenElliptic p (q t) x - (q t x) ^ p.γ)) ≤
          E t * (p.χ * (q t x) ^ p.m * Dup) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hresolverGap
                (mul_nonneg hchi_pos.le (Real.rpow_nonneg hqx.1 _)))
              hEt0.le
        _ ≤ E t * (p.χ *
            ((b t) ^ p.m + rpowLip p.m M * |q t x - b t|) * Dup) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpowUpper hchi_pos.le) hDup0)
            hEt0.le
        _ = Kpow * |r t x| +
              E t * (p.χ * (b t) ^ p.m * Dup) := by
          rw [habsr]
          dsimp [Kpow]
          ring
    have hLip := (reaction_lipschitz_on_Icc
      (a := p.α) (M := M) p.hα hM).dist_le_mul
        (b t) hb (q t x) hqx
    rw [Real.coe_toNNReal _ hKbase] at hLip
    have hreaction :
        E t * (deriv b t - reactionFun p.α (q t x)) ≤
          Kbase * |r t x| -
            E t * (p.χ * (b t) ^ p.m * Dup) := by
      have hdiff : reactionFun p.α (b t) - reactionFun p.α (q t x) ≤
          Kbase * |b t - q t x| := by
        exact (le_abs_self _).trans (by simpa [Real.dist_eq] using hLip)
      have hraw : deriv b t - reactionFun p.α (q t x) ≤
          reactionFun p.α (b t) - reactionFun p.α (q t x) -
            p.χ * (b t) ^ p.m * Dup := by
        linarith [hpdeb ht]
      have hscaled := mul_le_mul_of_nonneg_left
        (hraw.trans (sub_le_sub_right hdiff
          (p.χ * (b t) ^ p.m * Dup))) hEt0.le
      have habs : |r t x| = E t * |b t - q t x| := by
        rw [show r t x = E t * (b t - q t x) from rfl,
          abs_mul, abs_of_pos hEt0]
      rw [habs]
      nlinarith
    have hrt : deriv (fun s : ℝ => r s x) t =
        -D * E t * (b t - q t x) +
          E t * (deriv b t - deriv (fun s : ℝ => q s x) t) := by
      have hraw := (hEderiv t).mul
        ((htimeb ht).sub (htimeq (t := t) (x := x) ht))
      simpa [r] using hraw.deriv
    have hfun : (fun y : ℝ => deriv (fun z : ℝ => r t z) y) =
        fun y => -E t * deriv (fun z : ℝ => q t z) y := by
      funext y
      exact hderivr ht y
    have hrxx : deriv (fun y : ℝ => deriv (fun z : ℝ => r t z) y) x =
        -E t * deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x := by
      rw [hfun]
      exact ((hspace2q (t := t) (x := x) ht).const_mul (-E t)).deriv
    have hcdrift : c * deriv (fun y : ℝ => r t y) x ≤
        |c| * |deriv (fun y : ℝ => r t y) x| := by
      exact (le_abs_self _).trans (by rw [abs_mul])
    have hsum :
        c * deriv (fun y : ℝ => r t y) x +
            E t * (p.χ * (p.m * (q t x) ^ (p.m - 1) *
              deriv (fun y : ℝ => q t y) x *
              deriv (frozenElliptic p (q t)) x)) +
            E t * (p.χ * (q t x) ^ p.m *
              (frozenElliptic p (q t) x - (q t x) ^ p.γ)) +
            E t * (deriv b t - reactionFun p.α (q t x)) ≤
          (|c| + Kgrad) * |deriv (fun y : ℝ => r t y) x| +
            Kreact * |r t x| := by
      dsimp [Kreact]
      nlinarith [hcdrift, hchemGrad, hchemZero, hreaction]
    have hrt' : deriv (fun s : ℝ => r s x) t =
        -D * r t x +
          E t * (deriv b t - deriv (fun s : ℝ => q s x) t) := by
      rw [hrt]
      dsimp only [r]
      ring
    have hcEq :
        -(E t * (c * deriv (fun y : ℝ => q t y) x)) =
          c * deriv (fun y : ℝ => r t y) x := by
      rw [hrx]
      ring
    rw [hrt', hpdeq ht hx, hrxx]
    dsimp [F, K]
    nlinarith [hsum, hcEq]
  have hsup : leftHalfLineSlabSup T x₀ r ≤ 0 :=
    leftHalfLineSlabSup_le_of_scalar_pde hT hK hcontr hupperr hinitr
      hboundaryr hFcont hFstrict htimer hspace1r hspace2r hpder
  intro t ht x hx
  have hrle : r t x ≤ leftHalfLineSlabSup T x₀ r :=
    le_leftHalfLineSlabSup hT.le hupperr ht hx
  have hr0 : r t x ≤ 0 := hrle.trans hsup
  dsimp [r] at hr0
  have hEt := hE0 t
  nlinarith

section AxiomAudit

#print axioms leftHalfLine_ge_of_weighted_resolver_reaction_subsolution

end AxiomAudit

end ShenWork.Paper1
