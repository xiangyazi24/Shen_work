import ShenWork.Paper1.WholeLineWeightedRegularityHalfLineMaximumNatural
import ShenWork.Paper1.WholeLineHalfLineResolverUpperNatural
import ShenWork.Paper1.WholeLineWeightedRegularityChiNegKPPFloorNatural
import ShenWork.Paper1.WholeLineChiPosTargetCeilingNatural

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-!
# Buffered left-half-line comparisons for positive sensitivity

For positive sensitivity the nondivergence-form chemotaxis reaction is
`χ q^m (q^γ - V)`.  At a lower contact the comparison equation instead sees
`χ q^m (V - q^γ)`, controlled by the upper half-line resolver estimate.  At an
upper contact it sees `χ q^m (q^γ - V)`, controlled by the lower resolver
estimate.  The fixed losses are reserved in the scalar floor and ceiling rates.
-/

set_option maxHeartbeats 1600000 in
/-- Abstract lower comparison after the positive-sensitivity resolver loss has
been bounded by a fixed scalar `H`. -/
theorem leftHalfLine_ge_of_positive_resolver_reaction_subsolution
    (p : CMParams) (_hchi_pos : 0 < p.χ)
    {T x₀ c M G H : ℝ} {q : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
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
    (hchem : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T → x < x₀ →
      p.χ * (q t x) ^ p.m *
        (frozenElliptic p (q t) x - (q t x) ^ p.γ) ≤ H)
    (hpdeb : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      deriv b t + H ≤ reactionFun p.α (b t)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Iic x₀, b t ≤ q t x := by
  let Kreact : ℝ := reactionLip p.α M
  let D : ℝ := Kreact + 1
  let E : ℝ → ℝ := fun t => Real.exp (-(D * t))
  let r : ℝ → ℝ → ℝ := fun t x => E t * (b t - q t x)
  let Kgrad : ℝ :=
    |p.χ| * p.m * M ^ (p.m - 1) * G ^ p.γ
  let K : ℝ := |c| + Kgrad
  let F : ℝ → ℝ := fun a => Kreact * |a| - D * a
  have hG0 : 0 ≤ G := hM.trans hMG
  have hKreact : 0 ≤ Kreact := reactionLip_nonneg p.hα hM
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
    have hchemZero :
        E t * (p.χ * (q t x) ^ p.m *
          (frozenElliptic p (q t) x - (q t x) ^ p.γ)) ≤ E t * H :=
      mul_le_mul_of_nonneg_left (hchem ht hx) hEt0.le
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
            E t * (p.χ * (q t x) ^ p.m *
              (frozenElliptic p (q t) x - (q t x) ^ p.γ)) +
            E t * (deriv b t - reactionFun p.α (q t x)) ≤
          (|c| + Kgrad) * |deriv (fun y : ℝ => r t y) x| +
            Kreact * |r t x| := by
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

set_option maxHeartbeats 1600000 in
/-- Abstract upper comparison after the positive-sensitivity resolver excess
has been bounded by a fixed scalar `H`. -/
theorem leftHalfLine_le_of_positive_resolver_reaction_supersolution
    (p : CMParams) (_hchi_pos : 0 < p.χ)
    {T x₀ c M G H : ℝ} {q : ℝ → ℝ → ℝ} {a : ℝ → ℝ}
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
    (hchem : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T → x < x₀ →
      p.χ * (q t x) ^ p.m *
        ((q t x) ^ p.γ - frozenElliptic p (q t) x) ≤ H)
    (hpdea : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      reactionFun p.α (a t) + H ≤ deriv a t) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Iic x₀, q t x ≤ a t := by
  let Kreact : ℝ := reactionLip p.α M
  let D : ℝ := Kreact + 1
  let E : ℝ → ℝ := fun t => Real.exp (-(D * t))
  let r : ℝ → ℝ → ℝ := fun t x => E t * (q t x - a t)
  let Kgrad : ℝ :=
    |p.χ| * p.m * M ^ (p.m - 1) * G ^ p.γ
  let K : ℝ := |c| + Kgrad
  let F : ℝ → ℝ := fun s => Kreact * |s| - D * s
  have hG0 : 0 ≤ G := hM.trans hMG
  have hKreact : 0 ≤ Kreact := reactionLip_nonneg p.hα hM
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
      (hcontq.sub (hconta.comp continuous_fst))
  have hupperr : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Iic x₀,
      r t x ≤ M := by
    intro t ht x hx
    have hdiff : q t x - a t ≤ M := by
      linarith [(hqleft t ht x hx).2, (harange t ht).1]
    calc
      r t x = E t * (q t x - a t) := rfl
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
      ((htimeq (t := t) (x := x) ht).sub (htimea ht))
    simpa [r] using hraw.differentiableAt.hasDerivAt
  have hspace1r : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => r t y)
        (deriv (fun y : ℝ => r t y) x) x := by
    intro t x ht
    have hraw := ((hspace1q (t := t) (x := x) ht).sub_const (a t)).const_mul
      (E t)
    simpa [r] using hraw.differentiableAt.hasDerivAt
  have hderivr : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T → ∀ y,
      deriv (fun z : ℝ => r t z) y =
        E t * deriv (fun z : ℝ => q t z) y := by
    intro t ht y
    have hraw := ((hspace1q (t := t) (x := y) ht).sub_const (a t)).const_mul
      (E t)
    simpa [r] using hraw.deriv
  have hspace2r : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => r t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => r t z) y) x) x := by
    intro t x ht
    have hfun : (fun y : ℝ => deriv (fun z : ℝ => r t z) y) =
        fun y => E t * deriv (fun z : ℝ => q t z) y := by
      funext y
      exact hderivr ht y
    rw [hfun]
    exact ((hspace2q (t := t) (x := x) ht).const_mul
      (E t)).differentiableAt.hasDerivAt
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
    have ha := harange t htIcc
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
        E t * deriv (fun y : ℝ => q t y) x := hderivr ht x
    have hrxabs : |deriv (fun y : ℝ => r t y) x| =
        E t * |deriv (fun y : ℝ => q t y) x| := by
      rw [hrx, abs_mul, abs_of_pos hEt0]
    have hchemGrad :
        E t * (-p.χ * (p.m * (q t x) ^ (p.m - 1) *
            deriv (fun y : ℝ => q t y) x *
            deriv (frozenElliptic p (q t)) x)) ≤
          Kgrad * |deriv (fun y : ℝ => r t y) x| := by
      calc
        E t * (-p.χ * (p.m * (q t x) ^ (p.m - 1) *
              deriv (fun y : ℝ => q t y) x *
              deriv (frozenElliptic p (q t)) x))
            ≤ |E t * (-p.χ * (p.m * (q t x) ^ (p.m - 1) *
              deriv (fun y : ℝ => q t y) x *
              deriv (frozenElliptic p (q t)) x))| := le_abs_self _
        _ = |p.χ| * p.m * (q t x) ^ (p.m - 1) *
              |deriv (fun y : ℝ => r t y) x| *
              |deriv (frozenElliptic p (q t)) x| := by
          rw [hrxabs, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul,
            abs_neg, abs_of_pos hEt0,
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
    have hchemZero :
        E t * (p.χ * (q t x) ^ p.m *
          ((q t x) ^ p.γ - frozenElliptic p (q t) x)) ≤ E t * H :=
      mul_le_mul_of_nonneg_left (hchem ht hx) hEt0.le
    have hLip := (reaction_lipschitz_on_Icc
      (a := p.α) (M := M) p.hα hM).dist_le_mul
        (q t x) hqx (a t) ha
    rw [Real.coe_toNNReal _ hKreact] at hLip
    have hreaction :
        E t * (reactionFun p.α (q t x) - deriv a t) ≤
          Kreact * |r t x| - E t * H := by
      have hdiff : reactionFun p.α (q t x) - reactionFun p.α (a t) ≤
          Kreact * |q t x - a t| := by
        exact (le_abs_self _).trans (by simpa [Real.dist_eq] using hLip)
      have hraw : reactionFun p.α (q t x) - deriv a t ≤
          reactionFun p.α (q t x) - reactionFun p.α (a t) - H := by
        linarith [hpdea ht]
      have hscaled := mul_le_mul_of_nonneg_left
        (hraw.trans (sub_le_sub_right hdiff H)) hEt0.le
      have habs : |r t x| = E t * |q t x - a t| := by
        rw [show r t x = E t * (q t x - a t) from rfl,
          abs_mul, abs_of_pos hEt0]
      rw [habs]
      nlinarith
    have hrt : deriv (fun s : ℝ => r s x) t =
        -D * E t * (q t x - a t) +
          E t * (deriv (fun s : ℝ => q s x) t - deriv a t) := by
      have hraw := (hEderiv t).mul
        ((htimeq (t := t) (x := x) ht).sub (htimea ht))
      simpa [r] using hraw.deriv
    have hfun : (fun y : ℝ => deriv (fun z : ℝ => r t z) y) =
        fun y => E t * deriv (fun z : ℝ => q t z) y := by
      funext y
      exact hderivr ht y
    have hrxx : deriv (fun y : ℝ => deriv (fun z : ℝ => r t z) y) x =
        E t * deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x := by
      rw [hfun]
      exact ((hspace2q (t := t) (x := x) ht).const_mul (E t)).deriv
    have hcdrift : c * deriv (fun y : ℝ => r t y) x ≤
        |c| * |deriv (fun y : ℝ => r t y) x| := by
      exact (le_abs_self _).trans (by rw [abs_mul])
    have hsum :
        c * deriv (fun y : ℝ => r t y) x +
            E t * (-p.χ * (p.m * (q t x) ^ (p.m - 1) *
              deriv (fun y : ℝ => q t y) x *
              deriv (frozenElliptic p (q t)) x)) +
            E t * (p.χ * (q t x) ^ p.m *
              ((q t x) ^ p.γ - frozenElliptic p (q t) x)) +
            E t * (reactionFun p.α (q t x) - deriv a t) ≤
          (|c| + Kgrad) * |deriv (fun y : ℝ => r t y) x| +
            Kreact * |r t x| := by
      nlinarith [hcdrift, hchemGrad, hchemZero, hreaction]
    have hrt' : deriv (fun s : ℝ => r s x) t =
        -D * r t x +
          E t * (deriv (fun s : ℝ => q s x) t - deriv a t) := by
      rw [hrt]
      dsimp only [r]
      ring
    have hcEq :
        E t * (c * deriv (fun y : ℝ => q t y) x) =
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

/-- A target-capped KPP floor stays below a positive-sensitivity solution on a
buffered left half-line.  The upper resolver estimate supplies the lower-contact
defect budget. -/
theorem leftHalfLine_ge_of_buffered_chiPos_floor
    (p : CMParams) (hchi_pos : 0 < p.χ)
    {T x₀ R c ell L M G : ℝ} {q : ℝ → ℝ → ℝ}
    (hT : 0 < T) (hR : 0 ≤ R)
    (hell : 0 < ell) (hellL : ell < L) (hL1 : L < 1)
    (hLM : L ≤ M) (hMG : M ≤ G)
    (hdefectSmall :
      p.χ * M ^ p.m *
          ((M ^ p.γ - ell ^ p.γ) +
            (Real.exp (-R) / 2) * (G ^ p.γ - M ^ p.γ)) <
        ell * (1 - L ^ p.α))
    (hcontq : Continuous (fun z : ℝ × ℝ => q z.1 z.2))
    (hqglobal : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      q t x ∈ Set.Icc (0 : ℝ) G)
    (hqlocal : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      x ≤ x₀ + R → q t x ∈ Set.Icc ell M)
    (hinit : ∀ x ∈ Set.Iic x₀, ell ≤ q 0 x)
    (hbuffer : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ x ∈ Set.Icc x₀ (x₀ + R),
        chiZeroKPPFloor ell L
          (chiNegKPPFloorRate p.α ell L
            (p.χ * M ^ p.m *
              ((M ^ p.γ - ell ^ p.γ) +
                (Real.exp (-R) / 2) * (G ^ p.γ - M ^ p.γ)))) t ≤ q t x)
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
      chiZeroKPPFloor ell L
        (chiNegKPPFloorRate p.α ell L
          (p.χ * M ^ p.m *
            ((M ^ p.γ - ell ^ p.γ) +
              (Real.exp (-R) / 2) * (G ^ p.γ - M ^ p.γ)))) t ≤ q t x := by
  let H : ℝ := p.χ * M ^ p.m *
    ((M ^ p.γ - ell ^ p.γ) +
      (Real.exp (-R) / 2) * (G ^ p.γ - M ^ p.γ))
  let lam : ℝ := chiNegKPPFloorRate p.α ell L H
  have hM : 0 ≤ M := hell.le.trans (hellL.le.trans hLM)
  have hG : 0 ≤ G := hM.trans hMG
  have hHsmall : H < ell * (1 - L ^ p.α) := by
    simpa only [H] using hdefectSmall
  have hlam : 0 < lam := chiNegKPPFloorRate_pos hellL hHsmall
  have hchem : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T → x < x₀ →
      p.χ * (q t x) ^ p.m *
        (frozenElliptic p (q t) x - (q t x) ^ p.γ) ≤ H := by
    intro t x ht hx
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
    have hxlocal : x ≤ x₀ + R := by linarith
    have hqx := hqlocal t htIcc x hxlocal
    have hsliceCont : Continuous (q t) :=
      hcontq.comp (continuous_const.prodMk continuous_id)
    have hsliceC : IsCUnifBdd (q t) := by
      refine ⟨hsliceCont, ⟨G, ?_⟩⟩
      intro y
      rw [abs_of_nonneg (hqglobal t htIcc y).1]
      exact (hqglobal t htIcc y).2
    have hVupper : frozenElliptic p (q t) x ≤
        (1 - Real.exp (-R) / 2) * M ^ p.γ +
          (Real.exp (-R) / 2) * G ^ p.γ := by
      apply frozenElliptic_upper_of_left_halfLine_ceiling
        p hsliceC (fun y => (hqglobal t htIcc y).1) hM hMG
        (fun y => (hqglobal t htIcc y).2)
        (fun y hy => (hqlocal t htIcc y hy).2) hR
      linarith
    have hgamma0 : 0 ≤ p.γ := zero_le_one.trans p.hγ
    have hellM : ell ≤ M := hellL.le.trans hLM
    have hellPowM : ell ^ p.γ ≤ M ^ p.γ :=
      Real.rpow_le_rpow hell.le hellM hgamma0
    have hMPowG : M ^ p.γ ≤ G ^ p.γ :=
      Real.rpow_le_rpow hM hMG hgamma0
    have hqPowLower : ell ^ p.γ ≤ (q t x) ^ p.γ :=
      Real.rpow_le_rpow hell.le hqx.1 hgamma0
    have htau0 : 0 ≤ Real.exp (-R) / 2 := by positivity
    have hgap0 : 0 ≤
        (M ^ p.γ - ell ^ p.γ) +
          (Real.exp (-R) / 2) * (G ^ p.γ - M ^ p.γ) := by
      exact add_nonneg (sub_nonneg.mpr hellPowM)
        (mul_nonneg htau0 (sub_nonneg.mpr hMPowG))
    have hresolverGap : frozenElliptic p (q t) x - (q t x) ^ p.γ ≤
        (M ^ p.γ - ell ^ p.γ) +
          (Real.exp (-R) / 2) * (G ^ p.γ - M ^ p.γ) := by
      nlinarith [hVupper, hqPowLower]
    have hqmM : (q t x) ^ p.m ≤ M ^ p.m :=
      Real.rpow_le_rpow (hell.le.trans hqx.1) hqx.2
        (zero_le_one.trans p.hm)
    calc
      p.χ * (q t x) ^ p.m *
            (frozenElliptic p (q t) x - (q t x) ^ p.γ) ≤
          p.χ * (q t x) ^ p.m *
            ((M ^ p.γ - ell ^ p.γ) +
              (Real.exp (-R) / 2) * (G ^ p.γ - M ^ p.γ)) :=
        mul_le_mul_of_nonneg_left hresolverGap
          (mul_nonneg hchi_pos.le
            (Real.rpow_nonneg (hell.le.trans hqx.1) _))
      _ ≤ p.χ * M ^ p.m *
            ((M ^ p.γ - ell ^ p.γ) +
              (Real.exp (-R) / 2) * (G ^ p.γ - M ^ p.γ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hqmM hchi_pos.le) hgap0
      _ = H := rfl
  have hcompare := leftHalfLine_ge_of_positive_resolver_reaction_subsolution
    p hchi_pos (T := T) (x₀ := x₀) (c := c) (M := M) (G := G) (H := H)
      (q := q) (b := chiZeroKPPFloor ell L lam)
      hT hM hMG hcontq (by unfold chiZeroKPPFloor; fun_prop) hqglobal
      (by
        intro t ht x hx
        have hxR : x ≤ x₀ + R := hx.trans (by linarith [hR])
        have hlocal := hqlocal t ht x hxR
        exact ⟨hell.le.trans hlocal.1, hlocal.2⟩)
      (by
        intro t ht
        exact ⟨hell.le.trans (chiZeroKPPFloor_ge_start hellL.le hlam.le ht.1),
          (chiZeroKPPFloor_le_target hellL.le).trans hLM⟩)
      (by simpa [lam, H] using hinit)
      (by
        intro t ht
        simpa [lam, H] using hbuffer t ht x₀ ⟨le_rfl, by linarith [hR]⟩)
      htimeq hspace1q hspace2q
      (by
        intro t _ht
        exact (chiZeroKPPFloor_hasDerivAt ell L lam t).differentiableAt.hasDerivAt)
      hpdeq hchem
      (by
        intro t ht
        simpa [lam] using
          chiNegKPPFloor_deriv_add_defect_le_reaction
            p.hα hell hellL hL1 hHsmall ht.1.le)
  simpa [lam, H] using hcompare

/-- A target-capped ceiling stays above a positive-sensitivity solution on a
buffered left half-line.  The lower resolver estimate supplies the upper-contact
defect budget. -/
theorem leftHalfLine_le_of_buffered_chiPos_ceiling
    (p : CMParams) (hchi_pos : 0 < p.χ)
    {T x₀ R c ell Ahat D M G : ℝ} {q : ℝ → ℝ → ℝ}
    (hT : 0 < T) (hR : 0 ≤ R)
    (hell : 0 ≤ ell) (hellM : ell ≤ M)
    (hA1 : 1 < Ahat) (hAD : Ahat ≤ D) (hDM : D ≤ M) (hMG : M ≤ G)
    (hdefectSmall :
      p.χ * M ^ p.m *
          ((M ^ p.γ - ell ^ p.γ) +
            (Real.exp (-R) / 2) * ell ^ p.γ) <
        Ahat * (Ahat ^ p.α - 1))
    (hcontq : Continuous (fun z : ℝ × ℝ => q z.1 z.2))
    (hqglobal : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      q t x ∈ Set.Icc (0 : ℝ) G)
    (hqlocal : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      x ≤ x₀ + R → q t x ∈ Set.Icc ell M)
    (hinit : ∀ x ∈ Set.Iic x₀, q 0 x ≤ D)
    (hbuffer : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ x ∈ Set.Icc x₀ (x₀ + R),
        q t x ≤ chiPosTargetCeiling Ahat D
          (chiPosTargetCeilingRate p.α Ahat D
            (p.χ * M ^ p.m *
              ((M ^ p.γ - ell ^ p.γ) +
                (Real.exp (-R) / 2) * ell ^ p.γ))) t)
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
      q t x ≤ chiPosTargetCeiling Ahat D
        (chiPosTargetCeilingRate p.α Ahat D
          (p.χ * M ^ p.m *
            ((M ^ p.γ - ell ^ p.γ) +
              (Real.exp (-R) / 2) * ell ^ p.γ))) t := by
  let H : ℝ := p.χ * M ^ p.m *
    ((M ^ p.γ - ell ^ p.γ) +
      (Real.exp (-R) / 2) * ell ^ p.γ)
  let lam : ℝ := chiPosTargetCeilingRate p.α Ahat D H
  have hA0 : 0 ≤ Ahat := zero_le_one.trans hA1.le
  have hM : 0 ≤ M := hA0.trans (hAD.trans (hDM))
  have hG : 0 ≤ G := hM.trans hMG
  have hHsmall : H < Ahat * (Ahat ^ p.α - 1) := by
    simpa only [H] using hdefectSmall
  have hlam : 0 < lam := chiPosTargetCeilingRate_pos hAD hHsmall
  have hchem : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T → x < x₀ →
      p.χ * (q t x) ^ p.m *
        ((q t x) ^ p.γ - frozenElliptic p (q t) x) ≤ H := by
    intro t x ht hx
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
    have hxlocal : x ≤ x₀ + R := by linarith
    have hqx := hqlocal t htIcc x hxlocal
    have hsliceCont : Continuous (q t) :=
      hcontq.comp (continuous_const.prodMk continuous_id)
    have hsliceC : IsCUnifBdd (q t) := by
      refine ⟨hsliceCont, ⟨G, ?_⟩⟩
      intro y
      rw [abs_of_nonneg (hqglobal t htIcc y).1]
      exact (hqglobal t htIcc y).2
    have hVlower :
        (1 - Real.exp (-R) / 2) * ell ^ p.γ ≤
          frozenElliptic p (q t) x := by
      apply frozenElliptic_lower_of_left_halfLine_floor
        p hsliceC (fun y => (hqglobal t htIcc y).1) hell
        (fun y hy => (hqlocal t htIcc y hy).1) hR
      linarith
    have hgamma0 : 0 ≤ p.γ := zero_le_one.trans p.hγ
    have hellPowM : ell ^ p.γ ≤ M ^ p.γ :=
      Real.rpow_le_rpow hell hellM hgamma0
    have hqPowUpper : (q t x) ^ p.γ ≤ M ^ p.γ :=
      Real.rpow_le_rpow (hell.trans hqx.1) hqx.2 hgamma0
    have htau0 : 0 ≤ Real.exp (-R) / 2 := by positivity
    have hgap0 : 0 ≤
        (M ^ p.γ - ell ^ p.γ) +
          (Real.exp (-R) / 2) * ell ^ p.γ := by
      exact add_nonneg (sub_nonneg.mpr hellPowM)
        (mul_nonneg htau0 (Real.rpow_nonneg hell _))
    have hresolverGap :
        (q t x) ^ p.γ - frozenElliptic p (q t) x ≤
          (M ^ p.γ - ell ^ p.γ) +
            (Real.exp (-R) / 2) * ell ^ p.γ := by
      nlinarith [hVlower, hqPowUpper]
    have hqmM : (q t x) ^ p.m ≤ M ^ p.m :=
      Real.rpow_le_rpow (hell.trans hqx.1) hqx.2
        (zero_le_one.trans p.hm)
    calc
      p.χ * (q t x) ^ p.m *
            ((q t x) ^ p.γ - frozenElliptic p (q t) x) ≤
          p.χ * (q t x) ^ p.m *
            ((M ^ p.γ - ell ^ p.γ) +
              (Real.exp (-R) / 2) * ell ^ p.γ) :=
        mul_le_mul_of_nonneg_left hresolverGap
          (mul_nonneg hchi_pos.le
            (Real.rpow_nonneg (hell.trans hqx.1) _))
      _ ≤ p.χ * M ^ p.m *
            ((M ^ p.γ - ell ^ p.γ) +
              (Real.exp (-R) / 2) * ell ^ p.γ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hqmM hchi_pos.le) hgap0
      _ = H := rfl
  have hcompare := leftHalfLine_le_of_positive_resolver_reaction_supersolution
    p hchi_pos (T := T) (x₀ := x₀) (c := c) (M := M) (G := G) (H := H)
      (q := q) (a := chiPosTargetCeiling Ahat D lam)
      hT hM hMG hcontq (by unfold chiPosTargetCeiling; fun_prop) hqglobal
      (by
        intro t ht x hx
        have hxR : x ≤ x₀ + R := hx.trans (by linarith [hR])
        have hlocal := hqlocal t ht x hxR
        exact ⟨hell.trans hlocal.1, hlocal.2⟩)
      (by
        intro t ht
        exact ⟨hA0.trans (chiPosTargetCeiling_ge_target hAD),
          (chiPosTargetCeiling_le_start hAD hlam.le ht.1).trans hDM⟩)
      (by simpa [lam, H] using hinit)
      (by
        intro t ht
        simpa [lam, H] using hbuffer t ht x₀ ⟨le_rfl, by linarith [hR]⟩)
      htimeq hspace1q hspace2q
      (by
        intro t _ht
        exact (chiPosTargetCeiling_hasDerivAt Ahat D lam t).differentiableAt.hasDerivAt)
      hpdeq hchem
      (by
        intro t ht
        simpa [lam] using
          chiPosTargetCeiling_deriv_ge_reaction_add_defect
            p.hα hA1 hAD hHsmall ht.1.le)
  simpa [lam, H] using hcompare

section AxiomAudit

#print axioms leftHalfLine_ge_of_positive_resolver_reaction_subsolution
#print axioms leftHalfLine_le_of_positive_resolver_reaction_supersolution
#print axioms leftHalfLine_ge_of_buffered_chiPos_floor
#print axioms leftHalfLine_le_of_buffered_chiPos_ceiling

end AxiomAudit

end ShenWork.Paper1
