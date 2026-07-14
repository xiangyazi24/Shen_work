import ShenWork.Paper1.WholeLineCauchySharpBound

open Filter Topology MeasureTheory Real Set Function
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section

namespace ShenWork.Paper1

/-!
# Exponentially relaxing ceiling for nonpositive sensitivity

For `chi <= 0`, the spatially constant function

`B_C(t) = 1 + (C - 1) exp(-t)`

is a supersolution whenever `C >= 1`.  At a spatial almost-maximum of
`u - B_C`, the elliptic resolver is bounded by the corresponding power of
the almost-supremum.  The nonlocal zeroth-order term is therefore favorable;
the remaining drift is absorbed by the existing whole-line approximate-
maximum theorem.  This yields a quantitative version of Proposition 1.1,
equation (1.9), without a time-translate compactness argument.
-/

def wholeLineCauchyExpCeiling (C t : ℝ) : ℝ :=
  1 + (C - 1) * Real.exp (-t)

theorem wholeLineCauchyExpCeiling_zero (C : ℝ) :
    wholeLineCauchyExpCeiling C 0 = C := by
  simp [wholeLineCauchyExpCeiling]

theorem wholeLineCauchyExpCeiling_hasDerivAt (C t : ℝ) :
    HasDerivAt (wholeLineCauchyExpCeiling C)
      (-((C - 1) * Real.exp (-t))) t := by
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-s))
      (-Real.exp (-t)) t := by
    simpa using (hasDerivAt_id t).neg.exp
  convert (hasDerivAt_const t (1 : ℝ)).add
    (hexp.const_mul (C - 1)) using 1 <;> ring

theorem wholeLineCauchyExpCeiling_deriv_eq_sub
    (C t : ℝ) :
    deriv (wholeLineCauchyExpCeiling C) t =
      -(wholeLineCauchyExpCeiling C t - 1) := by
  rw [(wholeLineCauchyExpCeiling_hasDerivAt C t).deriv]
  simp [wholeLineCauchyExpCeiling]

theorem wholeLineCauchyExpCeiling_one_le
    {C t : ℝ} (hC : 1 ≤ C) :
    1 ≤ wholeLineCauchyExpCeiling C t := by
  unfold wholeLineCauchyExpCeiling
  have hmul : 0 ≤ (C - 1) * Real.exp (-t) :=
    mul_nonneg (sub_nonneg.mpr hC) (Real.exp_nonneg _)
  linarith

theorem wholeLineCauchyExpCeiling_le
    {C t : ℝ} (hC : 1 ≤ C) (ht : 0 ≤ t) :
    wholeLineCauchyExpCeiling C t ≤ C := by
  have hexp : Real.exp (-t) ≤ 1 := by
    simpa using Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
  unfold wholeLineCauchyExpCeiling
  nlinarith [sub_nonneg.mpr hC, Real.exp_pos (-t)]

theorem wholeLineCauchyExpCeiling_restart (C a s : ℝ) :
    wholeLineCauchyExpCeiling (wholeLineCauchyExpCeiling C a) s =
      wholeLineCauchyExpCeiling C (a + s) := by
  unfold wholeLineCauchyExpCeiling
  rw [Real.exp_neg, Real.exp_neg, Real.exp_neg, Real.exp_add]
  field_simp
  ring

/-- Abstract moving-barrier maximum principle for the expanded resolver PDE.
The scalar function is only assumed bounded on the slab; spatial maxima need
not be attained. -/
theorem wholeLineSlab_le_expCeiling_of_nonpositive_resolver_pde
    (p : CMParams) (hχ : p.χ ≤ 0)
    {T C A : ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0 < T) (hC : 1 ≤ C)
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
      u t x ≤ wholeLineCauchyExpCeiling C t := by
  let B : ℝ → ℝ := wholeLineCauchyExpCeiling C
  let w : ℝ → ℝ → ℝ := fun t x => u t x - B t
  have hA0 : 0 ≤ A := by
    linarith [hnonneg 0 ⟨le_rfl, hT.le⟩ 0,
      hupper 0 ⟨le_rfl, hT.le⟩ 0]
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hB1 : ∀ t, 1 ≤ B t := by
    intro t
    exact wholeLineCauchyExpCeiling_one_le hC
  have hBC : ∀ t ∈ Set.Icc (0 : ℝ) T, B t ≤ C := by
    intro t ht
    exact wholeLineCauchyExpCeiling_le hC ht.1
  have hcontw : Continuous (fun q : ℝ × ℝ => w q.1 q.2) := by
    have hBcont : Continuous B := by
      simpa [B, wholeLineCauchyExpCeiling] using
        continuous_const.add
          (continuous_const.mul (Real.continuous_exp.comp continuous_id.neg))
    exact hcont.sub (hBcont.comp continuous_fst)
  have hupperw : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, w t x ≤ A := by
    intro t ht x
    dsimp [w]
    linarith [hupper t ht x, hB1 t]
  have hinitw : ∀ x, w 0 x ≤ 0 := by
    intro x
    simpa [w, B, wholeLineCauchyExpCeiling_zero] using hinit x
  have hBderiv : ∀ t, HasDerivAt B (-(B t - 1)) t := by
    intro t
    convert wholeLineCauchyExpCeiling_hasDerivAt C t using 1 <;>
      simp [B, wholeLineCauchyExpCeiling] <;> ring
  have hdtw : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => w s x)
        (deriv (fun s : ℝ => u s x) t + (B t - 1)) t := by
    intro t x ht
    dsimp [w]
    convert (htime ht).sub (hBderiv t) using 1 <;> ring
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
  let R : ℝ := C + A
  let K : ℝ := |p.χ| * p.m * A ^ (p.m - 1) * A ^ p.γ
  let Kchem : ℝ := (-p.χ) * A ^ p.m * rpowLip p.γ R
  let Kreact : ℝ := reactionLip p.α R
  let G : ℝ → ℝ := fun r =>
    Kchem * (L - r) + Kreact * max (-r) 0 - max r 0
  have hR0 : 0 ≤ R := by dsimp [R]; linarith
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
      (rpowLip_nonneg p.hγ hR0)
  have hKreact : 0 ≤ Kreact := by
    exact reactionLip_nonneg p.hα hR0
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
    simp [L]
    simpa [L] using (neg_neg_iff_pos.mpr hL)
  have hLA : L ≤ A := wholeLineSlabSup_le hT.le hupperw
  have hpdew : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      deriv (fun s : ℝ => w s x) t ≤
        deriv (fun y : ℝ => deriv (fun z : ℝ => w t z) y) x +
          K * |deriv (fun y : ℝ => w t y) x| + G (w t x) := by
    intro t x ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
    have hu0 : 0 ≤ u t x := hnonneg t htIcc x
    have huA : u t x ≤ A := hupper t htIcc x
    have hBt1 : 1 ≤ B t := hB1 t
    have hBtC : B t ≤ C := hBC t htIcc
    have hwL : w t x ≤ L :=
      le_wholeLineSlabSup hT.le hupperw htIcc x
    have hLw0 : 0 ≤ L - w t x := sub_nonneg.mpr hwL
    have hsliceCont : Continuous (u t) :=
      hcont.comp (continuous_const.prodMk continuous_id)
    have hsliceC : IsCUnifBdd (u t) := by
      refine ⟨hsliceCont, ⟨A, ?_⟩⟩
      intro y
      rw [abs_of_nonneg (hnonneg t htIcc y)]
      exact hupper t htIcc y
    have hBL0 : 0 ≤ B t + L := by
      have := add_le_add_left hwL (B t)
      dsimp [w] at this
      linarith
    have huBL : ∀ y, u t y ≤ B t + L := by
      intro y
      have hwy := le_wholeLineSlabSup hT.le hupperw htIcc y
      dsimp [w] at hwy
      linarith
    have hvBL : frozenElliptic p (u t) x ≤ (B t + L) ^ p.γ := by
      apply frozenElliptic_le_of_rpow_le p
        (Real.rpow_nonneg hBL0 p.γ) hsliceCont (hnonneg t htIcc)
      intro y
      exact Real.rpow_le_rpow (hnonneg t htIcc y) (huBL y)
        (zero_le_one.trans p.hγ)
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
    have hdrift :
        -p.χ * (p.m * (u t x) ^ (p.m - 1) *
            deriv (fun y : ℝ => u t y) x *
            deriv (frozenElliptic p (u t)) x) ≤
          K * |deriv (fun y : ℝ => u t y) x| := by
      calc
        -p.χ * (p.m * (u t x) ^ (p.m - 1) *
              deriv (fun y : ℝ => u t y) x *
              deriv (frozenElliptic p (u t)) x)
            ≤ |-p.χ * (p.m * (u t x) ^ (p.m - 1) *
              deriv (fun y : ℝ => u t y) x *
              deriv (frozenElliptic p (u t)) x)| := le_abs_self _
        _ = |p.χ| * p.m * (u t x) ^ (p.m - 1) *
              |deriv (fun y : ℝ => u t y) x| *
              |deriv (frozenElliptic p (u t)) x| := by
              rw [abs_mul, abs_neg, abs_mul, abs_mul, abs_mul,
                abs_of_nonneg (zero_le_one.trans p.hm),
                abs_of_nonneg (Real.rpow_nonneg hu0 _)]
              ring
        _ ≤ K * |deriv (fun y : ℝ => u t y) x| := by
              have hcoef0 : 0 ≤ |p.χ| * p.m :=
                mul_nonneg (abs_nonneg _) (zero_le_one.trans p.hm)
              have hux0 : 0 ≤ |deriv (fun y : ℝ => u t y) x| := abs_nonneg _
              have huv :
                  (u t x) ^ (p.m - 1) *
                      |deriv (frozenElliptic p (u t)) x| ≤
                    A ^ (p.m - 1) * A ^ p.γ :=
                mul_le_mul humA hvxA (abs_nonneg _)
                  (Real.rpow_nonneg hA0 _)
              dsimp [K]
              calc
                |p.χ| * p.m * (u t x) ^ (p.m - 1) *
                      |deriv (fun y : ℝ => u t y) x| *
                      |deriv (frozenElliptic p (u t)) x|
                    = (|p.χ| * p.m) *
                        |deriv (fun y : ℝ => u t y) x| *
                        ((u t x) ^ (p.m - 1) *
                          |deriv (frozenElliptic p (u t)) x|) := by ring
                _ ≤ (|p.χ| * p.m) *
                        |deriv (fun y : ℝ => u t y) x| *
                        (A ^ (p.m - 1) * A ^ p.γ) :=
                  mul_le_mul_of_nonneg_left huv (mul_nonneg hcoef0 hux0)
                _ = |p.χ| * p.m * A ^ (p.m - 1) * A ^ p.γ *
                      |deriv (fun y : ℝ => u t y) x| := by ring
    have hBLR : B t + L ≤ R := by
      dsimp [R]
      linarith
    have huR : u t x ≤ R := huA.trans (by dsimp [R]; linarith)
    have hpowLip := (rpow_m_lipschitz_on_Icc
      (m := p.γ) (M := R) p.hγ hR0).dist_le_mul
        (B t + L) ⟨hBL0, hBLR⟩ (u t x) ⟨hu0, huR⟩
    have hpowdiff :
        (B t + L) ^ p.γ - (u t x) ^ p.γ ≤
          rpowLip p.γ R * (L - w t x) := by
      have hpoword : (u t x) ^ p.γ ≤ (B t + L) ^ p.γ :=
        Real.rpow_le_rpow hu0 (huBL x) (zero_le_one.trans p.hγ)
      rw [Real.coe_toNNReal _ (rpowLip_nonneg p.hγ hR0)] at hpowLip
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hpoword),
        Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (huBL x))] at hpowLip
      dsimp [w] at hpowLip ⊢
      convert hpowLip using 1 <;> ring
    have humpA : (u t x) ^ p.m ≤ A ^ p.m :=
      Real.rpow_le_rpow hu0 huA (zero_le_one.trans p.hm)
    have hchem :
        -p.χ * ((u t x) ^ p.m *
            (frozenElliptic p (u t) x - (u t x) ^ p.γ)) ≤
          Kchem * (L - w t x) := by
      have hcoef0 : 0 ≤ (-p.χ) * (u t x) ^ p.m :=
        mul_nonneg (by linarith) (Real.rpow_nonneg hu0 _)
      have hLip0 : 0 ≤ rpowLip p.γ R := rpowLip_nonneg p.hγ hR0
      calc
        -p.χ * ((u t x) ^ p.m *
              (frozenElliptic p (u t) x - (u t x) ^ p.γ))
            = ((-p.χ) * (u t x) ^ p.m) *
                (frozenElliptic p (u t) x - (u t x) ^ p.γ) := by ring
        _ ≤ ((-p.χ) * (u t x) ^ p.m) *
                ((B t + L) ^ p.γ - (u t x) ^ p.γ) :=
          mul_le_mul_of_nonneg_left (sub_le_sub_right hvBL _) hcoef0
        _ ≤ ((-p.χ) * (u t x) ^ p.m) *
                (rpowLip p.γ R * (L - w t x)) :=
          mul_le_mul_of_nonneg_left hpowdiff hcoef0
        _ ≤ ((-p.χ) * A ^ p.m) *
                (rpowLip p.γ R * (L - w t x)) := by
          have hright0 : 0 ≤ rpowLip p.γ R * (L - w t x) :=
            mul_nonneg hLip0 hLw0
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left humpA (by linarith)) hright0
        _ = Kchem * (L - w t x) := by
          dsimp [Kchem]
          ring
    have hBpow : B t ≤ (B t) ^ p.α := by
      simpa using Real.rpow_le_rpow_of_exponent_le hBt1 p.hα
    have hBsuper : reactionFun p.α (B t) ≤ -(B t - 1) := by
      dsimp [reactionFun]
      nlinarith
    have hreaction :
        reactionFun p.α (u t x) + (B t - 1) ≤
          Kreact * max (-(w t x)) 0 - max (w t x) 0 := by
      by_cases hw0 : 0 ≤ w t x
      · have hu1 : 1 ≤ u t x := by
          dsimp [w] at hw0
          linarith
        have hupow : u t x ≤ (u t x) ^ p.α := by
          simpa using Real.rpow_le_rpow_of_exponent_le hu1 p.hα
        rw [max_eq_right (neg_nonpos.mpr hw0), max_eq_left hw0]
        dsimp [reactionFun, w] at hupow ⊢
        nlinarith
      · have hwneg : w t x < 0 := lt_of_not_ge hw0
        have hBtR : B t ≤ R := hBtC.trans (by dsimp [R]; linarith)
        have hLip := (reaction_lipschitz_on_Icc
          (a := p.α) (M := R) p.hα hR0).dist_le_mul
            (u t x) ⟨hu0, huR⟩ (B t) ⟨by linarith, hBtR⟩
        rw [Real.coe_toNNReal _ (reactionLip_nonneg p.hα hR0)] at hLip
        have habs : |reactionFun p.α (u t x) - reactionFun p.α (B t)| ≤
            Kreact * |u t x - B t| := by
          simpa [Real.dist_eq, Kreact] using hLip
        rw [max_eq_left (neg_nonneg.mpr hwneg.le),
          max_eq_right hwneg.le]
        have hdiff :
            reactionFun p.α (u t x) - reactionFun p.α (B t) ≤
              Kreact * (-(w t x)) := by
          have hle := (le_abs_self
            (reactionFun p.α (u t x) - reactionFun p.α (B t))).trans habs
          rw [abs_of_nonpos] at hle
          · simpa [w] using hle
          · simpa [w] using hwneg.le
        linarith
    have hdt : deriv (fun s : ℝ => w s x) t =
        deriv (fun s : ℝ => u s x) t + (B t - 1) := (hdtw ht).deriv
    have hd1 : deriv (fun y : ℝ => w t y) x =
        deriv (fun y : ℝ => u t y) x := by
      simp [w, deriv_sub_const]
    have hd2 : deriv (fun y : ℝ => deriv (fun z : ℝ => w t z) y) x =
        deriv (fun y : ℝ => deriv (fun z : ℝ => u t z) y) x := by
      rw [hderivw]
    rw [hdt, hpde ht, hd1, hd2]
    dsimp [G]
    linarith
  have hwslab : wholeLineSlabSup T w ≤ 0 :=
    wholeLineSlabSup_le_of_scalar_pde hT hK hcontw hupperw hinitw
      hGcont hGstrict htimew hspace1w hspace2w hpdew
  intro t ht x
  have hwle : w t x ≤ wholeLineSlabSup T w :=
    le_wholeLineSlabSup hT.le hupperw ht x
  dsimp [w, B] at hwle ⊢
  linarith

/-- The moving barrier on the strict-interior part of one canonical fixed
point segment.  A shorter auxiliary slab avoids asking for a time derivative
at the construction endpoint. -/
theorem wholeLineCauchyBUCMildFixedPoint_exp_ceiling_Ico
    (p : CMParams) (hχ : p.χ ≤ 0)
    {M T C : ℝ} (hM : 0 ≤ M) (hT : 0 < T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M)
    (hC : 1 ≤ C) (hinit : ∀ x, u₀.1 x ≤ C) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x,
      (wholeLineBUCTrajectoryExtend hT.le
        (wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall) t).1 x ≤
          wholeLineCauchyExpCeiling C t := by
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
      wholeLineCauchyExpCeiling C 0
    rw [hext0, hU0, wholeLineCauchyExpCeiling_zero]
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
  have hbarrier := wholeLineSlab_le_expCeiling_of_nonpositive_resolver_pde
    p hχ hSpos hC hjoint
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

/-- Time continuity passes the moving ceiling to the closed construction
endpoint. -/
theorem wholeLineCauchyBUCMildFixedPoint_exp_ceiling_Icc
    (p : CMParams) (hχ : p.χ ≤ 0)
    {M T C : ℝ} (hM : 0 ≤ M) (hT : 0 < T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M)
    (hC : 1 ≤ C) (hinit : ∀ x, u₀.1 x ≤ C) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineBUCTrajectoryExtend hT.le
        (wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall) t).1 x ≤
          wholeLineCauchyExpCeiling C t := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall
  have hIco := wholeLineCauchyBUCMildFixedPoint_exp_ceiling_Ico
    p hχ hM hT u₀ hsmall hstrip hC hinit
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
      wholeLineCauchyExpCeiling C s
  have hfcont : Continuous f := by
    have hucont : Continuous (fun s =>
        (wholeLineBUCTrajectoryExtend hT.le U s).1 x) :=
      hjoint.comp (continuous_id.prodMk continuous_const)
    have hbcont : Continuous (wholeLineCauchyExpCeiling C) := by
      unfold wholeLineCauchyExpCeiling
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

def wholeLineCauchyStepExpCeiling
    (p : CMParams) (u₀ : WholeLineBUC) (C : ℝ) (n : ℕ) : ℝ :=
  wholeLineCauchyExpCeiling C
    ((n : ℝ) * wholeLineCauchyGlobalStep p u₀)

theorem wholeLineCauchyStepExpCeiling_one_le
    (p : CMParams) (u₀ : WholeLineBUC) {C : ℝ} (hC : 1 ≤ C) (n : ℕ) :
    1 ≤ wholeLineCauchyStepExpCeiling p u₀ C n :=
  wholeLineCauchyExpCeiling_one_le hC

theorem wholeLineCauchyStepExpCeiling_succ
    (p : CMParams) (u₀ : WholeLineBUC) (C : ℝ) (n : ℕ) :
    wholeLineCauchyExpCeiling
        (wholeLineCauchyStepExpCeiling p u₀ C n)
        (wholeLineCauchyGlobalStep p u₀) =
      wholeLineCauchyStepExpCeiling p u₀ C (n + 1) := by
  rw [wholeLineCauchyStepExpCeiling, wholeLineCauchyExpCeiling_restart]
  unfold wholeLineCauchyStepExpCeiling
  congr 1
  norm_num [Nat.cast_add, Nat.cast_one]
  ring

/-- The exponential ceiling is propagated through every recursive restart
datum and every complete canonical segment. -/
theorem wholeLineCauchyGlobalDatum_segment_le_expCeiling
    (p : CMParams) (hχ : p.χ ≤ 0)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (C : ℝ) (hC : 1 ≤ C) (hinit : ∀ x, u₀.1 x ≤ C) :
    ∀ n,
      (∀ x, (wholeLineCauchyGlobalDatum p u₀ n).1 x ≤
        wholeLineCauchyStepExpCeiling p u₀ C n) ∧
      (∀ z x, (wholeLineCauchyGlobalSegment p u₀ n z).1 x ≤
        wholeLineCauchyExpCeiling
          (wholeLineCauchyStepExpCeiling p u₀ C n) z.1) := by
  let hregime : WholeLineCauchyCeilingRegime p :=
    WholeLineCauchyCeilingRegime.of_nonpositive hχ
  intro n
  induction n with
  | zero =>
      have hdatum : ∀ x,
          (wholeLineCauchyGlobalDatum p u₀ 0).1 x ≤
            wholeLineCauchyStepExpCeiling p u₀ C 0 := by
        intro x
        simpa [wholeLineCauchyGlobalDatum, wholeLineCauchyStepExpCeiling,
          wholeLineCauchyExpCeiling_zero] using
          hinit x
      refine ⟨hdatum, ?_⟩
      intro z x
      have hstrip :=
        (wholeLineCauchyGlobalDatum_segment_bounds
          p hregime u₀ hu₀ 0).2.1
      have hclosed := wholeLineCauchyBUCMildFixedPoint_exp_ceiling_Icc
        p hχ (wholeLineCauchyGlobalClamp_pos p u₀).le
        (wholeLineCauchyGlobalSegmentTime_pos p u₀)
        (wholeLineCauchyGlobalDatum p u₀ 0)
        (wholeLineCauchyGlobalSegmentTime_rate p u₀)
        (by simpa [wholeLineCauchyGlobalSegment] using hstrip)
        (wholeLineCauchyStepExpCeiling_one_le p u₀ hC 0) hdatum
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
            wholeLineCauchyStepExpCeiling p u₀ C (n + 1) := by
        intro x
        rw [← wholeLineCauchyStepExpCeiling_succ p u₀ C n]
        simpa [wholeLineCauchyGlobalDatum, wholeLineCauchyGlobalSegment,
          zδ, δ] using ih.2 zδ x
      refine ⟨by simpa [Nat.succ_eq_add_one] using hdatum, ?_⟩
      intro z x
      have hstrip :=
        (wholeLineCauchyGlobalDatum_segment_bounds
          p hregime u₀ hu₀ (n + 1)).2.1
      have hclosed := wholeLineCauchyBUCMildFixedPoint_exp_ceiling_Icc
        p hχ (wholeLineCauchyGlobalClamp_pos p u₀).le
        (wholeLineCauchyGlobalSegmentTime_pos p u₀)
        (wholeLineCauchyGlobalDatum p u₀ (n + 1))
        (wholeLineCauchyGlobalSegmentTime_rate p u₀)
        (by simpa [wholeLineCauchyGlobalSegment] using hstrip)
        (wholeLineCauchyStepExpCeiling_one_le p u₀ hC (n + 1)) hdatum
      have hext := wholeLineBUCTrajectoryExtend_eq
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
        (wholeLineCauchyGlobalSegment p u₀ (n + 1)) z.2
      rw [← hext]
      simpa [wholeLineCauchyGlobalSegment] using hclosed z.1 z.2 x

/-- Quantitative global decay of the canonical solution toward the carrying
capacity ceiling `1`. -/
theorem wholeLineCauchyGlobal_le_expCeiling_of_chi_nonpos
    (p : CMParams) (hχ : p.χ ≤ 0)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (C : ℝ) (hC : 1 ≤ C) (hinit : ∀ x, u₀.1 x ≤ C)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    wholeLineCauchyGlobalU p u₀ t x ≤ wholeLineCauchyExpCeiling C t := by
  let n := wholeLineCauchyGlobalIndex p u₀ t
  let q := wholeLineCauchyGlobalLocalTime p u₀ t
  let δ := wholeLineCauchyGlobalStep p u₀
  let z : Set.Icc (0 : ℝ) (wholeLineCauchyGlobalSegmentTime p u₀) :=
    ⟨q, wholeLineCauchyGlobalLocalTime_nonneg p u₀ ht,
      (wholeLineCauchyGlobalLocalTime_lt_segmentTime p u₀ ht).le⟩
  have hbound :=
    (wholeLineCauchyGlobalDatum_segment_le_expCeiling
      p hχ u₀ hu₀ C hC hinit n).2 z x
  have heq := congrArg (fun w : WholeLineBUC => w.1 x)
    (wholeLineCauchyGlobalBUC_eq_segment p u₀ ht)
  have heq' : (wholeLineCauchyGlobalBUC p u₀ t).1 x =
      (wholeLineCauchyGlobalSegment p u₀ n z).1 x := by
    simpa [n, q, z] using heq
  have hrestart := wholeLineCauchyExpCeiling_restart C
    ((n : ℝ) * δ) q
  change (wholeLineCauchyGlobalBUC p u₀ t).1 x ≤
    wholeLineCauchyExpCeiling C t
  rw [heq']
  calc
    (wholeLineCauchyGlobalSegment p u₀ n z).1 x
        ≤ wholeLineCauchyExpCeiling
            (wholeLineCauchyStepExpCeiling p u₀ C n) q := hbound
    _ = wholeLineCauchyExpCeiling C (((n : ℝ) * δ) + q) := by
      simpa [wholeLineCauchyStepExpCeiling, δ] using hrestart
    _ = wholeLineCauchyExpCeiling C t := by
      congr 1
      dsimp [q, n, δ, wholeLineCauchyGlobalLocalTime]
      ring

theorem wholeLineCauchyGlobal_uniformLimsupLe_one_of_chi_nonpos
    (p : CMParams) (hχ : p.χ ≤ 0)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x) :
    UniformLimsupLe (wholeLineCauchyGlobalU p u₀) 1 := by
  let C : ℝ := max 1 ‖u₀‖
  have hC : 1 ≤ C := le_max_left _ _
  have hinit : ∀ x, u₀.1 x ≤ C := by
    intro x
    exact (WholeLineBUC.apply_le_norm u₀ x).trans (le_max_right _ _)
  have hdecay : Tendsto (fun t : ℝ =>
      (C - 1) * Real.exp (-t)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul Real.tendsto_exp_neg_atTop_nhds_zero
  intro ε hε
  have hepsNhds : Set.Iio ε ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds hε
  have hsmall : ∀ᶠ t : ℝ in atTop, (C - 1) * Real.exp (-t) < ε :=
    hdecay.eventually hepsNhds
  filter_upwards [hsmall, eventually_ge_atTop (0 : ℝ)] with t htε ht0
  intro x
  have hbound := wholeLineCauchyGlobal_le_expCeiling_of_chi_nonpos
    p hχ u₀ hu₀ C hC hinit ht0 x
  dsimp [wholeLineCauchyExpCeiling] at hbound
  linarith

/-- The full nonpositive-sensitivity branch of Proposition 1.1, including
global existence, the sharp maximum estimate (1.8), and the long-time bound
(1.9). -/
theorem Proposition_1_1_negative_branch
    (p : CMParams) (hχ : p.χ ≤ 0)
    (u₀ : ℝ → ℝ) (hu₀ : PaperNonnegativeInitialDatum u₀) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalNonnegativeCauchySolutionFrom p u₀ u v ∧
      (∀ M, (∀ x, u₀ x ≤ M) →
        ∀ t x, 0 ≤ t → u t x ≤ max 1 M) ∧
      UniformLimsupLe u 1 := by
  let w : WholeLineBUC := wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1
  have hw0 : ∀ x, 0 ≤ w.1 x := by
    intro x
    simpa [w] using hu₀.2 x
  let hregime : WholeLineCauchyCeilingRegime p :=
    WholeLineCauchyCeilingRegime.of_nonpositive hχ
  refine ⟨wholeLineCauchyGlobalU p w, wholeLineCauchyGlobalV p w,
    ?_, ?_, wholeLineCauchyGlobal_uniformLimsupLe_one_of_chi_nonpos
      p hχ w hw0⟩
  · simpa [w] using
      wholeLineCauchyGlobal_isGlobalNonnegativeCauchySolutionFrom
        p hregime w hw0
  · intro M hM t x ht
    exact wholeLineCauchyGlobal_le_max_one_of_chi_nonpos
      p hχ w hw0 M (by simpa [w] using hM) ht x

section WholeLineCauchyLongTimeBarrierAxiomAudit

#print axioms wholeLineCauchyExpCeiling_restart
#print axioms wholeLineSlab_le_expCeiling_of_nonpositive_resolver_pde
#print axioms wholeLineCauchyBUCMildFixedPoint_exp_ceiling_Icc
#print axioms wholeLineCauchyGlobalDatum_segment_le_expCeiling
#print axioms wholeLineCauchyGlobal_le_expCeiling_of_chi_nonpos
#print axioms wholeLineCauchyGlobal_uniformLimsupLe_one_of_chi_nonpos
#print axioms Proposition_1_1_negative_branch

end WholeLineCauchyLongTimeBarrierAxiomAudit

end ShenWork.Paper1
