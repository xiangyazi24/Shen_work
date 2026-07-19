import ShenWork.Paper1.WholeLineChiPosWeightedResolverComparisonNatural

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-!
# Whole-line comparisons for positive sensitivity

On the whole line there is no lateral boundary.  A scalar barrier can
therefore be compared on a complete classical slab as soon as the frozen
resolver is controlled throughout that slab.  The lower comparison retains
the barrier's `b ^ m` weight in the resolver loss.  The upper comparison below
will similarly retain the coupled term at the barrier value.
-/

/-- Exponential damping closes a whole-line scalar comparison with an
absolute-value zeroth-order error. -/
private theorem wholeLine_nonpos_of_linear_abs_pde
    {T A K L : ℝ} {d : ℝ → ℝ → ℝ}
    (hT : 0 < T) (hA : 0 ≤ A) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hcont : Continuous (fun z : ℝ × ℝ => d z.1 z.2))
    (hupper : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, d t x ≤ A)
    (hinit : ∀ x, d 0 x ≤ 0)
    (htime : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => d s x)
        (deriv (fun s : ℝ => d s x) t) t)
    (hspace1 : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => d t y)
        (deriv (fun y : ℝ => d t y) x) x)
    (hspace2 : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => d t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => d t z) y) x) x)
    (hpde : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      deriv (fun s : ℝ => d s x) t ≤
        deriv (fun y : ℝ => deriv (fun z : ℝ => d t z) y) x +
          K * |deriv (fun y : ℝ => d t y) x| + L * |d t x|) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, d t x ≤ 0 := by
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
  have hupperr : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, r t x ≤ A := by
    intro t ht x
    calc
      r t x = E t * d t x := rfl
      _ ≤ E t * A := mul_le_mul_of_nonneg_left (hupper t ht x) (hE0 t).le
      _ ≤ 1 * A := mul_le_mul_of_nonneg_right (hEone t ht) hA
      _ = A := one_mul _
  have hinitr : ∀ x, r 0 x ≤ 0 := by
    intro x
    simpa [r, E] using hinit x
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
  have hFstrict : 0 < wholeLineSlabSup T r →
      F (wholeLineSlabSup T r) < 0 := by
    intro hsup
    dsimp [F, D]
    rw [abs_of_pos hsup]
    linarith
  have hpder : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      deriv (fun s : ℝ => r s x) t ≤
        deriv (fun y : ℝ => deriv (fun z : ℝ => r t z) y) x +
          K * |deriv (fun y : ℝ => r t y) x| + F (r t x) := by
    intro t x ht
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
    have hscaled := mul_le_mul_of_nonneg_left
      (hpde (t := t) (x := x) ht) hEt0.le
    rw [hrt, hrxx, hrxabs]
    dsimp [F]
    rw [hrabs]
    nlinarith
  have hrsup : wholeLineSlabSup T r ≤ 0 :=
    wholeLineSlabSup_le_of_scalar_pde hT hK hcontr hupperr hinitr
      hFcont hFstrict htimer hspace1r hspace2r hpder
  intro t ht x
  have hrle : r t x ≤ wholeLineSlabSup T r :=
    le_wholeLineSlabSup hT.le hupperr ht x
  have hr0 : r t x ≤ 0 := hrle.trans hrsup
  dsimp [r] at hr0
  exact nonpos_of_mul_nonpos_left (by simpa [mul_comm] using hr0) (hE0 t)

set_option maxHeartbeats 1600000 in
/-- A reaction subsolution remains below a positive-sensitivity solution on a
whole-line slab when the full resolver gap is budgeted at the barrier value.
-/
theorem wholeLine_ge_of_coupled_resolver_reaction_subsolution
    (p : CMParams) (hchi_pos : 0 < p.χ)
    {T G Dup : ℝ} {q : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hT : 0 < T) (hG : 0 ≤ G)
    (hcontq : Continuous (fun z : ℝ × ℝ => q z.1 z.2))
    (hcontb : Continuous b)
    (hqrange : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      q t x ∈ Set.Icc (0 : ℝ) G)
    (hbrange : ∀ t ∈ Set.Icc (0 : ℝ) T,
      b t ∈ Set.Icc (0 : ℝ) G)
    (hinit : ∀ x, b 0 ≤ q 0 x)
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
    (hpdeq : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      deriv (fun s : ℝ => q s x) t =
        deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x -
          p.χ *
            (p.m * (q t x) ^ (p.m - 1) *
                deriv (fun y : ℝ => q t y) x *
                deriv (frozenElliptic p (q t)) x +
              (q t x) ^ p.m *
                (frozenElliptic p (q t) x - (q t x) ^ p.γ)) +
          reactionFun p.α (q t x))
    (hresolver : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      frozenElliptic p (q t) x ≤ Dup)
    (hpdeb : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      deriv b t + p.χ * (b t) ^ p.m * (Dup - (b t) ^ p.γ) ≤
        reactionFun p.α (b t)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, b t ≤ q t x := by
  let d : ℝ → ℝ → ℝ := fun t x => b t - q t x
  let Kbase : ℝ := reactionLip p.α G
  let Kpow : ℝ := p.χ *
    (Dup * rpowLip p.m G + rpowLip (p.m + p.γ) G)
  let Ksource : ℝ := Kbase + Kpow
  let Kgrad : ℝ :=
    |p.χ| * p.m * G ^ (p.m - 1) * G ^ p.γ
  have hKbase : 0 ≤ Kbase := reactionLip_nonneg p.hα hG
  have hDup0 : 0 ≤ Dup := by
    let t₀ : ℝ := T / 2
    have ht₀ : t₀ ∈ Set.Ioc (0 : ℝ) T := by
      dsimp [t₀]
      constructor <;> linarith
    have ht₀Icc : t₀ ∈ Set.Icc (0 : ℝ) T := ⟨ht₀.1.le, ht₀.2⟩
    exact (frozenElliptic_nonneg p
      (fun y => (hqrange t₀ ht₀Icc y).1) 0).trans
        (hresolver (t := t₀) (x := 0) ht₀)
  have hKpow : 0 ≤ Kpow := by
    dsimp [Kpow]
    exact mul_nonneg hchi_pos.le (add_nonneg
      (mul_nonneg hDup0 (rpowLip_nonneg p.hm hG))
      (rpowLip_nonneg (by linarith [p.hm, p.hγ]) hG))
  have hKsource : 0 ≤ Ksource := add_nonneg hKbase hKpow
  have hKgrad : 0 ≤ Kgrad := by
    dsimp [Kgrad]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (abs_nonneg _) (zero_le_one.trans p.hm))
          (Real.rpow_nonneg hG _))
      (Real.rpow_nonneg hG _)
  have hcontd : Continuous (fun z : ℝ × ℝ => d z.1 z.2) := by
    exact (hcontb.comp continuous_fst).sub hcontq
  have hupperd : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, d t x ≤ G := by
    intro t ht x
    dsimp [d]
    linarith [(hbrange t ht).2, (hqrange t ht x).1]
  have hinitd : ∀ x, d 0 x ≤ 0 := by
    intro x
    exact sub_nonpos.mpr (hinit x)
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
  have hpderd : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      deriv (fun s : ℝ => d s x) t ≤
        deriv (fun y : ℝ => deriv (fun z : ℝ => d t z) y) x +
          Kgrad * |deriv (fun y : ℝ => d t y) x| +
            Ksource * |d t x| := by
    intro t x ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
    have hqx := hqrange t htIcc x
    have hb := hbrange t htIcc
    have hsliceCont : Continuous (q t) :=
      hcontq.comp (continuous_const.prodMk continuous_id)
    have hsliceC : IsCUnifBdd (q t) := by
      refine ⟨hsliceCont, ⟨G, ?_⟩⟩
      intro y
      rw [abs_of_nonneg (hqrange t htIcc y).1]
      exact (hqrange t htIcc y).2
    have hvG : frozenElliptic p (q t) x ≤ G ^ p.γ := by
      apply frozenElliptic_le_of_rpow_le p
        (Real.rpow_nonneg hG p.γ) hsliceCont
        (fun y => (hqrange t htIcc y).1)
      intro y
      exact Real.rpow_le_rpow (hqrange t htIcc y).1
        (hqrange t htIcc y).2 (zero_le_one.trans p.hγ)
    have hvxG : |deriv (frozenElliptic p (q t)) x| ≤ G ^ p.γ :=
      (frozenElliptic_deriv_abs_le p hsliceC
        (fun y => (hqrange t htIcc y).1) x).trans hvG
    have hqmG : (q t x) ^ (p.m - 1) ≤ G ^ (p.m - 1) :=
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
                G ^ (p.m - 1) * G ^ p.γ :=
            mul_le_mul hqmG hvxG (abs_nonneg _)
              (Real.rpow_nonneg hG _)
          dsimp [Kgrad]
          calc
            |p.χ| * p.m * (q t x) ^ (p.m - 1) *
                  |deriv (fun y : ℝ => d t y) x| *
                  |deriv (frozenElliptic p (q t)) x| =
                (|p.χ| * p.m) * |deriv (fun y : ℝ => d t y) x| *
                  ((q t x) ^ (p.m - 1) *
                    |deriv (frozenElliptic p (q t)) x|) := by ring
            _ ≤ (|p.χ| * p.m) * |deriv (fun y : ℝ => d t y) x| *
                  (G ^ (p.m - 1) * G ^ p.γ) :=
              mul_le_mul_of_nonneg_left hpowV (mul_nonneg hcoef0 hdx0)
            _ = |p.χ| * p.m * G ^ (p.m - 1) * G ^ p.γ *
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
      (m := p.m) (M := G) p.hm hG).dist_le_mul
        (q t x) hqx (b t) hb
    rw [Real.coe_toNNReal _ (rpowLip_nonneg p.hm hG)] at hpowMLip
    have hpowMAbs : |(q t x) ^ p.m - (b t) ^ p.m| ≤
        rpowLip p.m G * |q t x - b t| := by
      simpa [Real.dist_eq] using hpowMLip
    have hmγ : 1 ≤ p.m + p.γ := by linarith [p.hm, p.hγ]
    have hpowMγLip := (rpow_m_lipschitz_on_Icc
      (m := p.m + p.γ) (M := G) hmγ hG).dist_le_mul
        (q t x) hqx (b t) hb
    rw [Real.coe_toNNReal _ (rpowLip_nonneg hmγ hG)] at hpowMγLip
    have hpowMγAbs :
        |(q t x) ^ (p.m + p.γ) - (b t) ^ (p.m + p.γ)| ≤
          rpowLip (p.m + p.γ) G * |q t x - b t| := by
      simpa [Real.dist_eq] using hpowMγLip
    have hcore :
        Dup * ((q t x) ^ p.m - (b t) ^ p.m) -
            ((q t x) ^ (p.m + p.γ) - (b t) ^ (p.m + p.γ)) ≤
          (Dup * rpowLip p.m G + rpowLip (p.m + p.γ) G) *
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
        _ ≤ Dup * (rpowLip p.m G * |q t x - b t|) +
              rpowLip (p.m + p.γ) G * |q t x - b t| :=
          add_le_add hfirst hpowMγAbs
        _ = (Dup * rpowLip p.m G + rpowLip (p.m + p.γ) G) *
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
              ((Dup * rpowLip p.m G + rpowLip (p.m + p.γ) G) *
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
        (sub_le_sub_right (hresolver (t := t) (x := x) ht) ((q t x) ^ p.γ))
        (mul_nonneg hchi_pos.le (Real.rpow_nonneg hqx.1 _))
    have hLip := (reaction_lipschitz_on_Icc
      (a := p.α) (M := G) p.hα hG).dist_le_mul
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
    rw [hdt, hpdeq ht, hdxx]
    nlinarith [hchemGrad, hsource]
  have hdnonpos := wholeLine_nonpos_of_linear_abs_pde
    hT hG hKgrad hKsource hcontd hupperd hinitd htimed hspace1d
      hspace2d hpderd
  intro t ht x
  exact sub_nonpos.mp (hdnonpos t ht x)

/-- The item-0 style whole-line lower comparison, with the nonnegative
`q ^ γ` part discarded from the resolver gap. -/
theorem wholeLine_ge_of_weighted_resolver_reaction_subsolution
    (p : CMParams) (hchi_pos : 0 < p.χ)
    {T G Dup : ℝ} {q : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hT : 0 < T) (hG : 0 ≤ G)
    (hcontq : Continuous (fun z : ℝ × ℝ => q z.1 z.2))
    (hcontb : Continuous b)
    (hqrange : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      q t x ∈ Set.Icc (0 : ℝ) G)
    (hbrange : ∀ t ∈ Set.Icc (0 : ℝ) T,
      b t ∈ Set.Icc (0 : ℝ) G)
    (hinit : ∀ x, b 0 ≤ q 0 x)
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
    (hpdeq : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      deriv (fun s : ℝ => q s x) t =
        deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x -
          p.χ *
            (p.m * (q t x) ^ (p.m - 1) *
                deriv (fun y : ℝ => q t y) x *
                deriv (frozenElliptic p (q t)) x +
              (q t x) ^ p.m *
                (frozenElliptic p (q t) x - (q t x) ^ p.γ)) +
          reactionFun p.α (q t x))
    (hresolver : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      frozenElliptic p (q t) x ≤ Dup)
    (hpdeb : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      deriv b t + p.χ * (b t) ^ p.m * Dup ≤
        reactionFun p.α (b t)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, b t ≤ q t x := by
  refine wholeLine_ge_of_coupled_resolver_reaction_subsolution
    p hchi_pos hT hG hcontq hcontb hqrange hbrange hinit htimeq
      hspace1q hspace2q htimeb hpdeq hresolver ?_
  intro t ht
  have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
  have hb0 : 0 ≤ b t := (hbrange t htIcc).1
  have hgap : Dup - (b t) ^ p.γ ≤ Dup := by
    linarith [Real.rpow_nonneg hb0 p.γ]
  have hcoeff : 0 ≤ p.χ * (b t) ^ p.m :=
    mul_nonneg hchi_pos.le (Real.rpow_nonneg hb0 _)
  have hterm := mul_le_mul_of_nonneg_left hgap hcoeff
  calc
    deriv b t + p.χ * (b t) ^ p.m * (Dup - (b t) ^ p.γ) ≤
        deriv b t + p.χ * (b t) ^ p.m * Dup := by
      nlinarith
    _ ≤ reactionFun p.α (b t) := hpdeb ht

set_option maxHeartbeats 1600000 in
/-- A reaction supersolution remains above a positive-sensitivity solution on
a whole-line slab when the resolver lower bound is coupled to the barrier
value. -/
theorem wholeLine_le_of_weighted_resolver_reaction_supersolution
    (p : CMParams) (hchi_pos : 0 < p.χ)
    {T G Dlo : ℝ} {q : ℝ → ℝ → ℝ} {a : ℝ → ℝ}
    (hT : 0 < T) (hG : 0 ≤ G)
    (hcontq : Continuous (fun z : ℝ × ℝ => q z.1 z.2))
    (hconta : Continuous a)
    (hqrange : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      q t x ∈ Set.Icc (0 : ℝ) G)
    (harange : ∀ t ∈ Set.Icc (0 : ℝ) T,
      a t ∈ Set.Icc (0 : ℝ) G)
    (hinit : ∀ x, q 0 x ≤ a 0)
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
    (hpdeq : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      deriv (fun s : ℝ => q s x) t =
        deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x -
          p.χ *
            (p.m * (q t x) ^ (p.m - 1) *
                deriv (fun y : ℝ => q t y) x *
                deriv (frozenElliptic p (q t)) x +
              (q t x) ^ p.m *
                (frozenElliptic p (q t) x - (q t x) ^ p.γ)) +
          reactionFun p.α (q t x))
    (hresolver : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      Dlo ≤ frozenElliptic p (q t) x)
    (hpdea : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      reactionFun p.α (a t) +
          p.χ * (a t) ^ p.m * ((a t) ^ p.γ - Dlo) ≤
        deriv a t) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, q t x ≤ a t := by
  let d : ℝ → ℝ → ℝ := fun t x => q t x - a t
  let Kbase : ℝ := reactionLip p.α G
  let Kpow : ℝ := p.χ *
    (rpowLip (p.m + p.γ) G + |Dlo| * rpowLip p.m G)
  let Ksource : ℝ := Kbase + Kpow
  let Kgrad : ℝ :=
    |p.χ| * p.m * G ^ (p.m - 1) * G ^ p.γ
  have hmγ : 1 ≤ p.m + p.γ := by linarith [p.hm, p.hγ]
  have hKbase : 0 ≤ Kbase := reactionLip_nonneg p.hα hG
  have hKpow : 0 ≤ Kpow := by
    dsimp [Kpow]
    exact mul_nonneg hchi_pos.le (add_nonneg
      (rpowLip_nonneg hmγ hG)
      (mul_nonneg (abs_nonneg _) (rpowLip_nonneg p.hm hG)))
  have hKsource : 0 ≤ Ksource := add_nonneg hKbase hKpow
  have hKgrad : 0 ≤ Kgrad := by
    dsimp [Kgrad]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (abs_nonneg _) (zero_le_one.trans p.hm))
          (Real.rpow_nonneg hG _))
      (Real.rpow_nonneg hG _)
  have hcontd : Continuous (fun z : ℝ × ℝ => d z.1 z.2) := by
    exact hcontq.sub (hconta.comp continuous_fst)
  have hupperd : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, d t x ≤ G := by
    intro t ht x
    dsimp [d]
    linarith [(hqrange t ht x).2, (harange t ht).1]
  have hinitd : ∀ x, d 0 x ≤ 0 := by
    intro x
    exact sub_nonpos.mpr (hinit x)
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
  have hpderd : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      deriv (fun s : ℝ => d s x) t ≤
        deriv (fun y : ℝ => deriv (fun z : ℝ => d t z) y) x +
          Kgrad * |deriv (fun y : ℝ => d t y) x| +
            Ksource * |d t x| := by
    intro t x ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
    have hqx := hqrange t htIcc x
    have ha := harange t htIcc
    have hsliceCont : Continuous (q t) :=
      hcontq.comp (continuous_const.prodMk continuous_id)
    have hsliceC : IsCUnifBdd (q t) := by
      refine ⟨hsliceCont, ⟨G, ?_⟩⟩
      intro y
      rw [abs_of_nonneg (hqrange t htIcc y).1]
      exact (hqrange t htIcc y).2
    have hvG : frozenElliptic p (q t) x ≤ G ^ p.γ := by
      apply frozenElliptic_le_of_rpow_le p
        (Real.rpow_nonneg hG p.γ) hsliceCont
        (fun y => (hqrange t htIcc y).1)
      intro y
      exact Real.rpow_le_rpow (hqrange t htIcc y).1
        (hqrange t htIcc y).2 (zero_le_one.trans p.hγ)
    have hvxG : |deriv (frozenElliptic p (q t)) x| ≤ G ^ p.γ :=
      (frozenElliptic_deriv_abs_le p hsliceC
        (fun y => (hqrange t htIcc y).1) x).trans hvG
    have hqmG : (q t x) ^ (p.m - 1) ≤ G ^ (p.m - 1) :=
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
                G ^ (p.m - 1) * G ^ p.γ :=
            mul_le_mul hqmG hvxG (abs_nonneg _)
              (Real.rpow_nonneg hG _)
          dsimp [Kgrad]
          calc
            |p.χ| * p.m * (q t x) ^ (p.m - 1) *
                  |deriv (fun y : ℝ => d t y) x| *
                  |deriv (frozenElliptic p (q t)) x| =
                (|p.χ| * p.m) * |deriv (fun y : ℝ => d t y) x| *
                  ((q t x) ^ (p.m - 1) *
                    |deriv (frozenElliptic p (q t)) x|) := by ring
            _ ≤ (|p.χ| * p.m) * |deriv (fun y : ℝ => d t y) x| *
                  (G ^ (p.m - 1) * G ^ p.γ) :=
              mul_le_mul_of_nonneg_left hpowV (mul_nonneg hcoef0 hdx0)
            _ = |p.χ| * p.m * G ^ (p.m - 1) * G ^ p.γ *
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
      (m := p.m) (M := G) p.hm hG).dist_le_mul
        (q t x) hqx (a t) ha
    rw [Real.coe_toNNReal _ (rpowLip_nonneg p.hm hG)] at hpowMLip
    have hpowMAbs : |(q t x) ^ p.m - (a t) ^ p.m| ≤
        rpowLip p.m G * |q t x - a t| := by
      simpa [Real.dist_eq] using hpowMLip
    have hpowMγLip := (rpow_m_lipschitz_on_Icc
      (m := p.m + p.γ) (M := G) hmγ hG).dist_le_mul
        (q t x) hqx (a t) ha
    rw [Real.coe_toNNReal _ (rpowLip_nonneg hmγ hG)] at hpowMγLip
    have hpowMγAbs :
        |(q t x) ^ (p.m + p.γ) - (a t) ^ (p.m + p.γ)| ≤
          rpowLip (p.m + p.γ) G * |q t x - a t| := by
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
          (rpowLip (p.m + p.γ) G + |Dlo| * rpowLip p.m G) *
            |q t x - a t| := by
      have hDloBound := mul_le_mul_of_nonneg_left hpowMAbs (abs_nonneg Dlo)
      calc
        ((q t x) ^ (p.m + p.γ) - (a t) ^ (p.m + p.γ)) -
              Dlo * ((q t x) ^ p.m - (a t) ^ p.m) ≤
            |(q t x) ^ (p.m + p.γ) - (a t) ^ (p.m + p.γ)| +
              |Dlo| * |(q t x) ^ p.m - (a t) ^ p.m| :=
          add_le_add (le_abs_self _) hDloTerm
        _ ≤ rpowLip (p.m + p.γ) G * |q t x - a t| +
              |Dlo| * (rpowLip p.m G * |q t x - a t|) :=
          add_le_add hpowMγAbs hDloBound
        _ = (rpowLip (p.m + p.γ) G + |Dlo| * rpowLip p.m G) *
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
              ((rpowLip (p.m + p.γ) G + |Dlo| * rpowLip p.m G) *
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
        (sub_le_sub_left (hresolver (t := t) (x := x) ht) ((q t x) ^ p.γ))
        (mul_nonneg hchi_pos.le (Real.rpow_nonneg hqx.1 _))
    have hLip := (reaction_lipschitz_on_Icc
      (a := p.α) (M := G) p.hα hG).dist_le_mul
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
    rw [hdt, hpdeq ht, hdxx]
    nlinarith [hchemGrad, hsource]
  have hdnonpos := wholeLine_nonpos_of_linear_abs_pde
    hT hG hKgrad hKsource hcontd hupperd hinitd htimed hspace1d
      hspace2d hpderd
  intro t ht x
  exact sub_nonpos.mp (hdnonpos t ht x)

section AxiomAudit

#print axioms wholeLine_ge_of_coupled_resolver_reaction_subsolution
#print axioms wholeLine_ge_of_weighted_resolver_reaction_subsolution
#print axioms wholeLine_le_of_weighted_resolver_reaction_supersolution

end AxiomAudit

end ShenWork.Paper1
