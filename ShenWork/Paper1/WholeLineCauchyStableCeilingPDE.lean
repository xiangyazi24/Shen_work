import ShenWork.Paper1.WholeLineCauchySpaceTimeMaximum
import ShenWork.Paper1.WholeLineCauchyGlobalBounds

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Stable-regime nonlocal Cauchy ceiling

At a space-time almost-maximum the frozen resolver is bounded by the power of
the true slab supremum.  The expanded chemotaxis drift is harmless because
the first spatial derivative is arbitrarily small.  The remaining scalar
term is strictly negative above the stable ceiling.
-/

set_option maxHeartbeats 800000 in
-- Each sign branch expands the resolver equation and several real powers;
-- the enlarged budget is for deterministic elaboration of those identities.
/-- The stable scalar margin closes the full nonlocal PDE maximum principle on
a bounded classical slab. -/
theorem wholeLineSlabSup_le_of_stable_resolver_pde
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    {T C A : ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0 < T) (hC1 : 1 ≤ C)
    (hmargin : 1 + max p.χ 0 * C ^ (p.m + p.γ - 1) ≤ C ^ p.α)
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
          u t x * (1 - (u t x) ^ p.α)) :
    wholeLineSlabSup T u ≤ C := by
  let L : ℝ := wholeLineSlabSup T u
  have hA0 : 0 ≤ A := by
    have := hupper 0 ⟨le_rfl, hT.le⟩ 0
    linarith [hnonneg 0 ⟨le_rfl, hT.le⟩ 0]
  let K : ℝ := |p.χ| * p.m * A ^ (p.m - 1) * A ^ p.γ
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (abs_nonneg _) (le_trans zero_le_one p.hm))
        (Real.rpow_nonneg hA0 _))
      (Real.rpow_nonneg hA0 _)
  have hstrictMargin : ∀ r, C < r →
      1 + max p.χ 0 * r ^ (p.m + p.γ - 1) < r ^ p.α :=
    fun r hr => wholeLineCauchyCeiling_strict_margin_above
      hregime hC1 hmargin hr
  rcases hregime with hχ | hpos
  · let G : ℝ → ℝ := fun r =>
      (-p.χ) * r ^ p.m * (L ^ p.γ - r ^ p.γ) +
        r * (1 - r ^ p.α)
    have hGcont : Continuous G := by
      have hm0 : 0 ≤ p.m := le_trans zero_le_one p.hm
      have hγ0 : 0 ≤ p.γ := le_trans zero_le_one p.hγ
      have hα0 : 0 ≤ p.α := le_trans zero_le_one p.hα
      dsimp [G]
      fun_prop (disch := assumption)
    have hGstrict : C < wholeLineSlabSup T u →
        G (wholeLineSlabSup T u) < 0 := by
      intro hCL
      have hL1 : 1 < L := hC1.trans_lt (by simpa [L] using hCL)
      have hLpos : 0 < L := zero_lt_one.trans hL1
      have hLpow : 1 < L ^ p.α :=
        Real.one_lt_rpow hL1 (by linarith [p.hα])
      change G L < 0
      dsimp [G]
      rw [sub_self, mul_zero, zero_add]
      exact mul_neg_of_pos_of_neg hLpos (sub_neg.mpr hLpow)
    apply wholeLineSlabSup_le_of_scalar_pde hT hK hcont hupper hinit
      hGcont hGstrict htime hspace1 hspace2
    intro t x ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
    have hu0 : 0 ≤ u t x := hnonneg t htIcc x
    have huA : u t x ≤ A := hupper t htIcc x
    have hLA : L ≤ A := wholeLineSlabSup_le hT.le hupper
    have hL0 : 0 ≤ L := le_trans hu0
      (le_wholeLineSlabSup hT.le hupper htIcc x)
    have huL : u t x ≤ L :=
      le_wholeLineSlabSup hT.le hupper htIcc x
    have hsliceCont : Continuous (u t) :=
      hcont.comp (continuous_const.prodMk continuous_id)
    have hsliceC : IsCUnifBdd (u t) := by
      refine ⟨hsliceCont, ⟨A, ?_⟩⟩
      intro y
      rw [abs_of_nonneg (hnonneg t htIcc y)]
      exact hupper t htIcc y
    have hv0 : 0 ≤ frozenElliptic p (u t) x :=
      frozenElliptic_nonneg p (hnonneg t htIcc) x
    have hvL : frozenElliptic p (u t) x ≤ L ^ p.γ := by
      apply frozenElliptic_le_of_rpow_le p
        (Real.rpow_nonneg hL0 p.γ) hsliceCont (hnonneg t htIcc)
      intro y
      exact Real.rpow_le_rpow (hnonneg t htIcc y)
        (le_wholeLineSlabSup hT.le hupper htIcc y)
        (zero_le_one.trans p.hγ)
    have hvxL : |deriv (frozenElliptic p (u t)) x| ≤ L ^ p.γ :=
      (frozenElliptic_deriv_abs_le p hsliceC (hnonneg t htIcc) x).trans hvL
    have hvxA : |deriv (frozenElliptic p (u t)) x| ≤ A ^ p.γ :=
      hvxL.trans (Real.rpow_le_rpow hL0 hLA (zero_le_one.trans p.hγ))
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
                abs_of_nonneg (by linarith [p.hm] : 0 ≤ p.m),
                abs_of_nonneg (Real.rpow_nonneg hu0 _)]
              ring
        _ ≤ K * |deriv (fun y : ℝ => u t y) x| := by
              have hcoef0 : 0 ≤ |p.χ| * p.m :=
                mul_nonneg (abs_nonneg _) (le_trans zero_le_one p.hm)
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
    have hum0 : 0 ≤ (u t x) ^ p.m := Real.rpow_nonneg hu0 _
    have hchem0 :
        -p.χ * ((u t x) ^ p.m *
            (frozenElliptic p (u t) x - (u t x) ^ p.γ)) ≤
          (-p.χ) * (u t x) ^ p.m *
            (L ^ p.γ - (u t x) ^ p.γ) := by
      have hcoef : 0 ≤ (-p.χ) * (u t x) ^ p.m :=
        mul_nonneg (by linarith [hχ]) hum0
      calc
        -p.χ * ((u t x) ^ p.m *
              (frozenElliptic p (u t) x - (u t x) ^ p.γ))
            = ((-p.χ) * (u t x) ^ p.m) *
                (frozenElliptic p (u t) x - (u t x) ^ p.γ) := by ring
        _ ≤ ((-p.χ) * (u t x) ^ p.m) *
                (L ^ p.γ - (u t x) ^ p.γ) :=
          mul_le_mul_of_nonneg_left (sub_le_sub_right hvL _) hcoef
        _ = (-p.χ) * (u t x) ^ p.m *
                (L ^ p.γ - (u t x) ^ p.γ) := by ring
    rw [hpde ht]
    dsimp [G]
    linarith
  · let G : ℝ → ℝ := fun r =>
      p.χ * r ^ (p.m + p.γ) + r * (1 - r ^ p.α)
    have hGcont : Continuous G := by
      have hsum0 : 0 ≤ p.m + p.γ := by linarith [p.hm, p.hγ]
      have hα0 : 0 ≤ p.α := le_trans zero_le_one p.hα
      dsimp [G]
      fun_prop (disch := assumption)
    have hGstrict : C < wholeLineSlabSup T u →
        G (wholeLineSlabSup T u) < 0 := by
      intro hCL
      have hL1 : 1 < L := hC1.trans_lt (by simpa [L] using hCL)
      have hLpos : 0 < L := zero_lt_one.trans hL1
      have hstrict := hstrictMargin L (by simpa [L] using hCL)
      rw [max_eq_left hpos.1] at hstrict
      change G L < 0
      dsimp [G]
      rw [show p.m + p.γ = 1 + (p.m + p.γ - 1) by ring,
        Real.rpow_add hLpos, Real.rpow_one]
      have hprod :
          L * (1 + p.χ * L ^ (p.m + p.γ - 1) - L ^ p.α) < 0 :=
        mul_neg_of_pos_of_neg hLpos (sub_neg.mpr hstrict)
      nlinarith
    apply wholeLineSlabSup_le_of_scalar_pde hT hK hcont hupper hinit
      hGcont hGstrict htime hspace1 hspace2
    intro t x ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
    have hu0 : 0 ≤ u t x := hnonneg t htIcc x
    have huA : u t x ≤ A := hupper t htIcc x
    have hL0 : 0 ≤ L := le_trans hu0
      (le_wholeLineSlabSup hT.le hupper htIcc x)
    have hLA : L ≤ A := wholeLineSlabSup_le hT.le hupper
    have hsliceCont : Continuous (u t) :=
      hcont.comp (continuous_const.prodMk continuous_id)
    have hsliceC : IsCUnifBdd (u t) := by
      refine ⟨hsliceCont, ⟨A, ?_⟩⟩
      intro y
      rw [abs_of_nonneg (hnonneg t htIcc y)]
      exact hupper t htIcc y
    have hv0 : 0 ≤ frozenElliptic p (u t) x :=
      frozenElliptic_nonneg p (hnonneg t htIcc) x
    have hvL : frozenElliptic p (u t) x ≤ L ^ p.γ := by
      apply frozenElliptic_le_of_rpow_le p
        (Real.rpow_nonneg hL0 p.γ) hsliceCont (hnonneg t htIcc)
      intro y
      exact Real.rpow_le_rpow (hnonneg t htIcc y)
        (le_wholeLineSlabSup hT.le hupper htIcc y)
        (zero_le_one.trans p.hγ)
    have hvxA : |deriv (frozenElliptic p (u t)) x| ≤ A ^ p.γ :=
      (frozenElliptic_deriv_abs_le p hsliceC (hnonneg t htIcc) x).trans
        (hvL.trans (Real.rpow_le_rpow hL0 hLA (zero_le_one.trans p.hγ)))
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
                abs_of_nonneg (by linarith [p.hm] : 0 ≤ p.m),
                abs_of_nonneg (Real.rpow_nonneg hu0 _)]
              ring
        _ ≤ K * |deriv (fun y : ℝ => u t y) x| := by
              have hcoef0 : 0 ≤ |p.χ| * p.m :=
                mul_nonneg (abs_nonneg _) (le_trans zero_le_one p.hm)
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
    have hchem0 :
        -p.χ * ((u t x) ^ p.m *
            (frozenElliptic p (u t) x - (u t x) ^ p.γ)) ≤
          p.χ * (u t x) ^ (p.m + p.γ) := by
      rw [Real.rpow_add_of_nonneg hu0 (zero_le_one.trans p.hm)
        (zero_le_one.trans p.hγ)]
      have hnonpos : -p.χ * (u t x) ^ p.m *
          frozenElliptic p (u t) x ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hpos.1)
            (Real.rpow_nonneg hu0 _)) hv0
      calc
        -p.χ * ((u t x) ^ p.m *
              (frozenElliptic p (u t) x - (u t x) ^ p.γ))
            = (-p.χ * (u t x) ^ p.m * frozenElliptic p (u t) x) +
                p.χ * ((u t x) ^ p.m * (u t x) ^ p.γ) := by ring
        _ ≤ p.χ * ((u t x) ^ p.m * (u t x) ^ p.γ) :=
          add_le_of_nonpos_left hnonpos
    rw [hpde ht]
    dsimp [G]
    linarith

section WholeLineCauchyStableCeilingPDEAxiomAudit

#print axioms wholeLineSlabSup_le_of_stable_resolver_pde

end WholeLineCauchyStableCeilingPDEAxiomAudit

end ShenWork.Paper1
