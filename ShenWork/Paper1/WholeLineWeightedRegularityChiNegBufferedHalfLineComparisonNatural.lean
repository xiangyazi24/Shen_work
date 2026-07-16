import ShenWork.Paper1.WholeLineWeightedRegularityHalfLineMaximumNatural
import ShenWork.Paper1.WholeLineWeightedRegularityHalfLineResolverLowerNatural
import ShenWork.Paper1.WholeLineWeightedRegularityChiNegKPPFloorNatural

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-!
# Buffered left-half-line comparison for nonpositive sensitivity

A lower comparison on a left half-line does not by itself give a global
floor for the elliptic resolver.  A finite buffer to the right of the
lateral boundary supplies the missing kernel mass.  The exponentially small
right-tail loss is reserved as a fixed defect in the scalar reaction
subsolution.
-/

set_option maxHeartbeats 1600000 in
-- The approximate-contact fencing calculation expands several nonlinear bounds.
/-- A scalar reaction subsolution with defect `H` remains below a classical
nonpositive-sensitivity solution on a left half-line.  The ordering on the
finite buffer `[x₀, x₀ + R]` is used only to lower-bound the nonlocal
resolver; no whole-line population floor is assumed. -/
theorem leftHalfLine_ge_of_buffered_nonpositive_resolver_reaction_subsolution
    (p : CMParams) (hchi : p.χ ≤ 0)
    {T x₀ R c M H : ℝ} {q : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hT : 0 < T) (hR : 0 ≤ R) (hM : 0 ≤ M) (_hH : 0 ≤ H)
    (hdefect :
      (-p.χ) * M ^ p.m * (Real.exp (-R) / 2 * M ^ p.γ) ≤ H)
    (hcontq : Continuous (fun z : ℝ × ℝ => q z.1 z.2))
    (hcontb : Continuous b)
    (hqrange : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      q t x ∈ Set.Icc (0 : ℝ) M)
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
      deriv b t + H ≤ reactionFun p.α (b t)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Iic x₀, b t ≤ q t x := by
  let Kreact : ℝ := reactionLip p.α M
  let D : ℝ := Kreact + 1
  let E : ℝ → ℝ := fun t => Real.exp (-(D * t))
  let F : ℝ → ℝ := fun t => Real.exp (D * t)
  let r : ℝ → ℝ → ℝ := fun t x => E t * (b t - q t x)
  let L : ℝ := leftHalfLineSlabSup T x₀ r
  let Lplus : ℝ := max L 0
  let Kgrad : ℝ :=
    |p.χ| * p.m * M ^ (p.m - 1) * M ^ p.γ
  let Kchem : ℝ := (-p.χ) * M ^ p.m * rpowLip p.γ M
  let K : ℝ := |c| + Kgrad
  let G : ℝ → ℝ := fun s =>
    Kchem * (Lplus - s) + Kreact * |s| - D * s
  have hKreact : 0 ≤ Kreact := reactionLip_nonneg p.hα hM
  have hD : 0 < D := by dsimp [D]; linarith
  have hE0 : ∀ t, 0 < E t := fun t => Real.exp_pos _
  have hF0 : ∀ t, 0 < F t := fun t => Real.exp_pos _
  have hEF : ∀ t, E t * F t = 1 := by
    intro t
    dsimp [E, F]
    rw [← Real.exp_add]
    ring_nf
    simp
  have hFr : ∀ t x, F t * r t x = b t - q t x := by
    intro t x
    dsimp [r]
    rw [← mul_assoc, mul_comm (F t) (E t), hEF]
    simp
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
    intro t ht x _hx
    have hdiff : b t - q t x ≤ M := by
      linarith [(hbrange t ht).2, (hqrange t ht x).1]
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
    have hbuffer0 := hbuffer t ht x₀ ⟨le_rfl, by linarith⟩
    exact mul_nonpos_of_nonneg_of_nonpos (hE0 t).le
      (sub_nonpos.mpr hbuffer0)
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
      (Real.rpow_nonneg hM _)
  have hKchem : 0 ≤ Kchem := by
    dsimp [Kchem]
    exact mul_nonneg
      (mul_nonneg (by linarith) (Real.rpow_nonneg hM _))
      (rpowLip_nonneg p.hγ hM)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hGcont : Continuous G := by
    dsimp [G]
    fun_prop
  have hGstrict : 0 < leftHalfLineSlabSup T x₀ r →
      G (leftHalfLineSlabSup T x₀ r) < 0 := by
    intro hL
    have hL0 : 0 ≤ L := hL.le
    have hLplus : Lplus = L := max_eq_left hL0
    dsimp [G]
    rw [show leftHalfLineSlabSup T x₀ r = L from rfl,
      hLplus, abs_of_nonneg hL0]
    dsimp [D]
    linarith
  have hpder : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T → x < x₀ →
      deriv (fun s : ℝ => r s x) t ≤
        deriv (fun y : ℝ => deriv (fun z : ℝ => r t z) y) x +
          K * |deriv (fun y : ℝ => r t y) x| + G (r t x) := by
    intro t x ht hx
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
    have hqt := hqrange t htIcc
    have hqx := hqt x
    have hb := hbrange t htIcc
    have hEt0 : 0 < E t := hE0 t
    have hFt0 : 0 < F t := hF0 t
    have hrL : r t x ≤ L := by
      exact le_leftHalfLineSlabSup hT.le hupperr htIcc
        (Set.mem_Iic.mpr hx.le)
    have hrLplus : r t x ≤ Lplus :=
      hrL.trans (le_max_left L 0)
    have hLplus0 : 0 ≤ Lplus := le_max_right L 0
    have hsliceCont : Continuous (q t) :=
      hcontq.comp (continuous_const.prodMk continuous_id)
    have hsliceC : IsCUnifBdd (q t) := by
      refine ⟨hsliceCont, ⟨M, ?_⟩⟩
      intro y
      rw [abs_of_nonneg (hqt y).1]
      exact (hqt y).2
    have hvM : frozenElliptic p (q t) x ≤ M ^ p.γ := by
      apply frozenElliptic_le_of_rpow_le p
        (Real.rpow_nonneg hM p.γ) hsliceCont (fun y => (hqt y).1)
      intro y
      exact Real.rpow_le_rpow (hqt y).1 (hqt y).2
        (zero_le_one.trans p.hγ)
    have hvxM : |deriv (frozenElliptic p (q t)) x| ≤ M ^ p.γ :=
      (frozenElliptic_deriv_abs_le p hsliceC (fun y => (hqt y).1) x).trans hvM
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
            abs_of_pos hEt0,
            abs_of_nonneg (zero_le_one.trans p.hm),
            abs_of_nonneg (Real.rpow_nonneg hqx.1 _)]
          ring
        _ ≤ Kgrad * |deriv (fun y : ℝ => r t y) x| := by
          have hcoef0 : 0 ≤ |p.χ| * p.m :=
            mul_nonneg (abs_nonneg _) (zero_le_one.trans p.hm)
          have hrx0 : 0 ≤ |deriv (fun y : ℝ => r t y) x| := abs_nonneg _
          have hpowV :
              (q t x) ^ (p.m - 1) *
                  |deriv (frozenElliptic p (q t)) x| ≤
                M ^ (p.m - 1) * M ^ p.γ :=
            mul_le_mul hqmM hvxM (abs_nonneg _)
              (Real.rpow_nonneg hM _)
          dsimp [Kgrad]
          calc
            |p.χ| * p.m * (q t x) ^ (p.m - 1) *
                  |deriv (fun y : ℝ => r t y) x| *
                  |deriv (frozenElliptic p (q t)) x| =
                (|p.χ| * p.m) *
                  |deriv (fun y : ℝ => r t y) x| *
                  ((q t x) ^ (p.m - 1) *
                    |deriv (frozenElliptic p (q t)) x|) := by ring
            _ ≤ (|p.χ| * p.m) *
                  |deriv (fun y : ℝ => r t y) x| *
                  (M ^ (p.m - 1) * M ^ p.γ) :=
              mul_le_mul_of_nonneg_left hpowV (mul_nonneg hcoef0 hrx0)
            _ = |p.χ| * p.m * M ^ (p.m - 1) * M ^ p.γ *
                  |deriv (fun y : ℝ => r t y) x| := by ring
    let a : ℝ := max (b t - F t * Lplus) 0
    have ha0 : 0 ≤ a := by dsimp [a]; exact le_max_right _ _
    have hab : a ≤ b t := by
      apply max_le
      · exact sub_le_self _ (mul_nonneg hFt0.le hLplus0)
      · exact hb.1
    have haM : a ≤ M := hab.trans hb.2
    have hafloorLeft : ∀ y, y ≤ x₀ → a ≤ q t y := by
      intro y hy
      have hryL : r t y ≤ L :=
        le_leftHalfLineSlabSup hT.le hupperr htIcc (Set.mem_Iic.mpr hy)
      have hryLplus : r t y ≤ Lplus := hryL.trans (le_max_left L 0)
      have hscaled : F t * r t y ≤ F t * Lplus :=
        mul_le_mul_of_nonneg_left hryLplus hFt0.le
      have hbase : b t - F t * Lplus ≤ q t y := by
        rw [hFr] at hscaled
        linarith
      exact max_le hbase (hqt y).1
    have hafloorBuffer : ∀ y, y ∈ Set.Icc x₀ (x₀ + R) → a ≤ q t y := by
      intro y hy
      exact hab.trans (hbuffer t htIcc y hy)
    have hafloor : ∀ y, y ≤ x₀ + R → a ≤ q t y := by
      intro y hy
      by_cases hy0 : y ≤ x₀
      · exact hafloorLeft y hy0
      · exact hafloorBuffer y ⟨le_of_not_ge hy0, hy⟩
    have hvaLower :
        (1 - Real.exp (-R) / 2) * a ^ p.γ ≤
          frozenElliptic p (q t) x := by
      apply frozenElliptic_lower_of_left_halfLine_floor p hsliceC
        (fun y => (hqt y).1) ha0 hafloor hR
      linarith
    have htail : a ^ p.γ - frozenElliptic p (q t) x ≤
        Real.exp (-R) / 2 * M ^ p.γ := by
      have haPowM : a ^ p.γ ≤ M ^ p.γ :=
        Real.rpow_le_rpow ha0 haM (zero_le_one.trans p.hγ)
      have hexp0 : 0 ≤ Real.exp (-R) / 2 := by positivity
      have hscaled := mul_le_mul_of_nonneg_left haPowM hexp0
      nlinarith
    have hqa : q t x - a ≤ F t * (Lplus - r t x) := by
      have hbase : b t - F t * Lplus ≤ a := by
        dsimp [a]
        exact le_max_left _ _
      have hxid := hFr t x
      linarith
    have hpowdiff : (q t x) ^ p.γ - a ^ p.γ ≤
        rpowLip p.γ M * (F t * (Lplus - r t x)) := by
      have hpoword : a ^ p.γ ≤ (q t x) ^ p.γ :=
        Real.rpow_le_rpow ha0 (hafloorLeft x hx.le)
          (zero_le_one.trans p.hγ)
      have hLip := (rpow_m_lipschitz_on_Icc
        (m := p.γ) (M := M) p.hγ hM).dist_le_mul
          (q t x) hqx a ⟨ha0, haM⟩
      rw [Real.coe_toNNReal _ (rpowLip_nonneg p.hγ hM)] at hLip
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hpoword),
        Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hafloorLeft x hx.le))]
        at hLip
      exact hLip.trans (mul_le_mul_of_nonneg_left hqa
        (rpowLip_nonneg p.hγ hM))
    have hqmPow : (q t x) ^ p.m ≤ M ^ p.m :=
      Real.rpow_le_rpow hqx.1 hqx.2 (zero_le_one.trans p.hm)
    have hchemZero :
        E t * (p.χ * ((q t x) ^ p.m *
            (frozenElliptic p (q t) x - (q t x) ^ p.γ))) ≤
          Kchem * (Lplus - r t x) + E t * H := by
      have hcoef0 : 0 ≤ (-p.χ) * (q t x) ^ p.m :=
        mul_nonneg (by linarith) (Real.rpow_nonneg hqx.1 _)
      have hcoefM : (-p.χ) * (q t x) ^ p.m ≤
          (-p.χ) * M ^ p.m :=
        mul_le_mul_of_nonneg_left hqmPow (by linarith)
      have hpowdiff0 : 0 ≤ (q t x) ^ p.γ - a ^ p.γ :=
        sub_nonneg.mpr (Real.rpow_le_rpow ha0 (hafloorLeft x hx.le)
          (zero_le_one.trans p.hγ))
      have hgap0 : 0 ≤ Lplus - r t x := sub_nonneg.mpr hrLplus
      have hmain :
          E t * (((-p.χ) * (q t x) ^ p.m) *
              ((q t x) ^ p.γ - a ^ p.γ)) ≤
            Kchem * (Lplus - r t x) := by
        calc
          E t * (((-p.χ) * (q t x) ^ p.m) *
                ((q t x) ^ p.γ - a ^ p.γ)) ≤
              E t * (((-p.χ) * M ^ p.m) *
                ((q t x) ^ p.γ - a ^ p.γ)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hcoefM hpowdiff0) hEt0.le
          _ ≤ E t * (((-p.χ) * M ^ p.m) *
                (rpowLip p.γ M * (F t * (Lplus - r t x)))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hpowdiff
                (mul_nonneg (by linarith) (Real.rpow_nonneg hM _)))
              hEt0.le
          _ = Kchem * (Lplus - r t x) := by
            dsimp [Kchem]
            calc
              E t * ((-p.χ * M ^ p.m) *
                  (rpowLip p.γ M * (F t * (Lplus - r t x)))) =
                  (E t * F t) *
                    ((-p.χ) * M ^ p.m * rpowLip p.γ M *
                      (Lplus - r t x)) := by ring
              _ = (-p.χ) * M ^ p.m * rpowLip p.γ M *
                    (Lplus - r t x) := by rw [hEF]; ring
      have htailScaled :
          E t * (((-p.χ) * (q t x) ^ p.m) *
              (a ^ p.γ - frozenElliptic p (q t) x)) ≤ E t * H := by
        calc
          E t * (((-p.χ) * (q t x) ^ p.m) *
                (a ^ p.γ - frozenElliptic p (q t) x)) ≤
              E t * (((-p.χ) * (q t x) ^ p.m) *
                (Real.exp (-R) / 2 * M ^ p.γ)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left htail hcoef0) hEt0.le
          _ ≤ E t * (((-p.χ) * M ^ p.m) *
                (Real.exp (-R) / 2 * M ^ p.γ)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hcoefM (by positivity)) hEt0.le
          _ ≤ E t * H := mul_le_mul_of_nonneg_left hdefect hEt0.le
      calc
        E t * (p.χ * ((q t x) ^ p.m *
              (frozenElliptic p (q t) x - (q t x) ^ p.γ))) =
            E t * (((-p.χ) * (q t x) ^ p.m) *
              (((q t x) ^ p.γ - a ^ p.γ) +
                (a ^ p.γ - frozenElliptic p (q t) x))) := by ring
        _ = E t * (((-p.χ) * (q t x) ^ p.m) *
              ((q t x) ^ p.γ - a ^ p.γ)) +
            E t * (((-p.χ) * (q t x) ^ p.m) *
              (a ^ p.γ - frozenElliptic p (q t) x)) := by ring
        _ ≤ Kchem * (Lplus - r t x) + E t * H :=
          add_le_add hmain htailScaled
    have hLip := (reaction_lipschitz_on_Icc
      (a := p.α) (M := M) p.hα hM).dist_le_mul
        (b t) hb (q t x) hqx
    rw [Real.coe_toNNReal _ hKreact] at hLip
    have hreaction :
        E t * (deriv b t - reactionFun p.α (q t x)) ≤
          Kreact * |r t x| - E t * H := by
      have hdiff : reactionFun p.α (b t) - reactionFun p.α (q t x) ≤
          Kreact * |b t - q t x| := by
        exact (le_abs_self _).trans (by simpa [Real.dist_eq] using hLip)
      have hraw : deriv b t - reactionFun p.α (q t x) ≤
          reactionFun p.α (b t) - reactionFun p.α (q t x) - H := by
        linarith [hpdeb ht]
      have hscaled := mul_le_mul_of_nonneg_left
        (hraw.trans (sub_le_sub_right hdiff H)) hEt0.le
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
            E t * (p.χ * ((q t x) ^ p.m *
              (frozenElliptic p (q t) x - (q t x) ^ p.γ))) +
            E t * (deriv b t - reactionFun p.α (q t x)) ≤
          (|c| + Kgrad) * |deriv (fun y : ℝ => r t y) x| +
            Kchem * (Lplus - r t x) + Kreact * |r t x| := by
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
    dsimp [G, K]
    nlinarith [hsum, hcEq]
  have hsup : leftHalfLineSlabSup T x₀ r ≤ 0 :=
    leftHalfLineSlabSup_le_of_scalar_pde hT hK hcontr hupperr hinitr
      hboundaryr hGcont hGstrict htimer hspace1r hspace2r hpder
  intro t ht x hx
  have hrle : r t x ≤ leftHalfLineSlabSup T x₀ r :=
    le_leftHalfLineSlabSup hT.le hupperr ht hx
  have hr0 : r t x ≤ 0 := hrle.trans hsup
  dsimp [r] at hr0
  have hEt := hE0 t
  nlinarith

/-- The explicit target-capped floor is a finite-slab lower barrier for the
nonpositive-sensitivity equation whenever the exponentially small resolver
tail defect fits inside its reserved reaction budget. -/
theorem leftHalfLine_ge_chiNegKPPFloor_of_buffer
    (p : CMParams) (hchi : p.χ ≤ 0)
    {T x₀ R c M C L : ℝ} {q : ℝ → ℝ → ℝ}
    (hT : 0 < T) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hC : 0 < C) (hCL : C < L) (hL1 : L < 1) (hLM : L ≤ M)
    (hdefectSmall :
      (-p.χ) * M ^ p.m * (Real.exp (-R) / 2 * M ^ p.γ) <
        C * (1 - L ^ p.α))
    (hcontq : Continuous (fun z : ℝ × ℝ => q z.1 z.2))
    (hqrange : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      q t x ∈ Set.Icc (0 : ℝ) M)
    (hinit : ∀ x ∈ Set.Iic x₀, C ≤ q 0 x)
    (hbuffer : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ x ∈ Set.Icc x₀ (x₀ + R), L ≤ q t x)
    (htimeq : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => q s x)
        (deriv (fun s : ℝ => q s x) t) t)
    (hspace1q : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => q t y)
        (deriv (fun y : ℝ => q t y) x) x)
    (hspace2q : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => q t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x) x)
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
          reactionFun p.α (q t x)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Iic x₀,
      chiZeroKPPFloor C L
        (chiNegKPPFloorRate p.α C L
          ((-p.χ) * M ^ p.m * (Real.exp (-R) / 2 * M ^ p.γ))) t ≤
        q t x := by
  let H : ℝ :=
    (-p.χ) * M ^ p.m * (Real.exp (-R) / 2 * M ^ p.γ)
  let lam : ℝ := chiNegKPPFloorRate p.α C L H
  have hH : 0 ≤ H := by
    dsimp [H]
    exact mul_nonneg
      (mul_nonneg (by linarith) (Real.rpow_nonneg hM _))
      (mul_nonneg (by positivity) (Real.rpow_nonneg hM _))
  have hlam : 0 < lam := by
    exact chiNegKPPFloorRate_pos hCL (by simpa [H] using hdefectSmall)
  have hHsmall : H < C * (1 - L ^ p.α) := by
    simpa only [H] using hdefectSmall
  apply leftHalfLine_ge_of_buffered_nonpositive_resolver_reaction_subsolution
      p hchi hT hR hM hH (by exact le_rfl) hcontq
      (b := chiZeroKPPFloor C L lam)
  · unfold chiZeroKPPFloor
    fun_prop
  · exact hqrange
  · intro t ht
    constructor
    · exact hC.le.trans (chiZeroKPPFloor_ge_start hCL.le hlam.le ht.1)
    · exact (chiZeroKPPFloor_le_target hCL.le).trans hLM
  · simpa [lam, H] using hinit
  · intro t ht x hx
    exact (chiZeroKPPFloor_le_target hCL.le).trans (hbuffer t ht x hx)
  · exact htimeq
  · exact hspace1q
  · exact hspace2q
  · intro t ht
    exact (chiZeroKPPFloor_hasDerivAt C L lam t).differentiableAt.hasDerivAt
  · exact hpdeq
  · intro t ht
    simpa only [lam] using
      chiNegKPPFloor_deriv_add_defect_le_reaction
        p.hα hC hCL hL1 hHsmall ht.1.le

section AxiomAudit

#print axioms
  leftHalfLine_ge_of_buffered_nonpositive_resolver_reaction_subsolution
#print axioms leftHalfLine_ge_chiNegKPPFloor_of_buffer

end AxiomAudit

end ShenWork.Paper1
