import Mathlib
import ShenWork.Wiener.WeightedL1Eval
import ShenWork.Wiener.WeightedL1CosineAdapter
import ShenWork.PDE.CosineParsevalBridge
import ShenWork.PDE.CosineSpectrum

/-!
# Wiener synthesis of even cosine coefficients = the committed cosine series — brick 6b

The 合龙 basis seam.  For real cosine coefficients `c : ℕ → ℝ` with `ℓ¹` summability,
the Wiener synthesis (`evalC`) of the even ℤ-bilateral embedding `ofCosineCoeffs c`
(brick 6a) evaluated at a real point `x` equals the committed cosine series
`∑_{k≥0} c k · cosineMode k x`, cast to `ℂ`.

The proof is the pointwise mirror of `wNorm_ofCosineCoeffs` (6a): a genuine ℤ-split via
`tsum_of_add_one_of_neg_add_one`, with the `n = 0` term giving `c 0` (since `fourier 0 = 1`),
and each `±(m+1)` pair collapsed by the committed bridge
`unitIntervalCosine_eq_fourier_pair` — `cos(nπx) = ½(fourier n x + fourier (−n) x)`.
The ½ from each `ofCosineCoeffs` coefficient times the 2 from the cos-pair equals 1.
-/

open scoped BigOperators

namespace ShenWork.Wiener

open ShenWork.CosineSpectrum ShenWork.CosineParsevalBridge

/-- The `n = 0` synthesis term equals `c 0 · cosineMode 0 x` (both `= c 0`). -/
private theorem evalCos_zero (c : ℕ → ℝ) (x : ℝ) :
    (ofCosineCoeffs c 0) • fourier (T := (2:ℝ)) 0 (x : AddCircle (2:ℝ))
      = ((c 0 : ℝ) : ℂ) * cosineMode 0 x := by
  rw [fourier_zero, ofCosineCoeffs]
  simp only [↓reduceIte]
  rw [cosineMode]; simp

/-- The paired `±(m+1)` synthesis terms collapse to `c (m+1) · cosineMode (m+1) x`
via the committed cos-pair bridge.  The ½ in each coefficient times the 2 in the
cos-pair gives the bare `c (m+1)`. -/
private theorem evalCos_pair (c : ℕ → ℝ) (x : ℝ) (m : ℕ) :
    (ofCosineCoeffs c ((m:ℤ)+1)) • fourier (T := (2:ℝ)) ((m:ℤ)+1) (x : AddCircle (2:ℝ))
      + (ofCosineCoeffs c (-((m:ℤ)+1))) • fourier (T := (2:ℝ)) (-((m:ℤ)+1))
          (x : AddCircle (2:ℝ))
      = ((c (m+1) : ℝ) : ℂ) * cosineMode (m+1) x := by
  rw [ofCosineCoeffs_neg]
  have hval : ofCosineCoeffs c ((m:ℤ)+1) = ((c (m+1) : ℝ) / 2 : ℂ) := by
    unfold ofCosineCoeffs; rw [if_neg (by omega)]
    have : ((m:ℤ)+1).natAbs = m+1 := by omega
    rw [this]
  rw [hval, smul_eq_mul, smul_eq_mul]
  have hbridge := unitIntervalCosine_eq_fourier_pair (m+1) x
  rw [cosineMode]
  have hcast : ((m:ℤ)+1 : ℤ) = ((m+1 : ℕ) : ℤ) := by push_cast; ring
  rw [hcast, hbridge]; push_cast; ring

open WA in
/-- **The basis-match (合龙 seam).** The Wiener synthesis of the even embedding of real
cosine coefficients equals the committed cosine series, pointwise. -/
theorem evalC_ofCosineCoeffs (c : ℕ → ℝ) (hc : Summable (fun k => |c k|))
    (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    WA.evalC (⟨ofCosineCoeffs c, memW_ofCosineCoeffs (r := 0) (by simpa using hc)⟩ : WA 0)
        (x : AddCircle (2:ℝ))
      = ((∑' k : ℕ, c k * cosineMode k x : ℝ) : ℂ) := by
  set a : WA 0 := ⟨ofCosineCoeffs c, memW_ofCosineCoeffs (r := 0) (by simpa using hc)⟩ with ha
  -- term family at the point x
  set g : ℤ → ℂ := fun n => (ofCosineCoeffs c n) • fourier (T := (2:ℝ)) n
      (x : AddCircle (2:ℝ)) with hg
  -- 1. reduce evalC a x to the ℤ-tsum ∑' n, g n
  have hLHS : WA.evalC a (x : AddCircle (2:ℝ)) = ∑' n : ℤ, g n := by
    rw [WA.evalC_apply, WA.evalLin_apply, WA.evalFun,
      ← ContinuousMap.tsum_apply (WA.summable_evalTerm a)]
    exact tsum_congr (fun n => rfl)
  rw [hLHS]
  -- 2. pointwise summability of g (norm comparison)
  have hgsum : Summable g := by
    apply Summable.of_norm
    refine (WA.summable_norm_toFun a).of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    calc ‖g n‖ = ‖(WA.evalTerm a n) (x : AddCircle (2:ℝ))‖ := rfl
      _ ≤ ‖WA.evalTerm a n‖ := (WA.evalTerm a n).norm_coe_le_norm _
      _ = ‖a.toFun n‖ := WA.norm_evalTerm a n
  -- pos / neg ℕ tails of g
  have hipos : Function.Injective (fun m : ℕ => (m:ℤ)+1) := by
    intro p q hpq; simpa using hpq
  have hineg : Function.Injective (fun m : ℕ => -((m:ℤ)+1)) := by
    intro p q hpq; simp only [neg_inj, add_left_inj] at hpq; exact_mod_cast hpq
  have hpos : Summable (fun m : ℕ => g ((m:ℤ)+1)) := hgsum.comp_injective hipos
  have hneg : Summable (fun m : ℕ => g (-((m:ℤ)+1))) := hgsum.comp_injective hineg
  -- 3. ℤ-split
  have hsplit : (∑' n : ℤ, g n)
      = (∑' m : ℕ, g ((m:ℤ)+1)) + g 0 + ∑' m : ℕ, g (-((m:ℤ)+1)) := by
    have := tsum_of_add_one_of_neg_add_one hpos hneg
    simpa using this
  rw [hsplit]
  -- combine the two ℕ tails into one (pos + neg = the cos pair)
  have hpairsum : (∑' m : ℕ, g ((m:ℤ)+1)) + ∑' m : ℕ, g (-((m:ℤ)+1))
      = ∑' m : ℕ, ((c (m+1) : ℝ) : ℂ) * cosineMode (m+1) x := by
    rw [← hpos.tsum_add hneg]
    exact tsum_congr (fun m => evalCos_pair c x m)
  -- regroup: zero term + pair tail
  have hg0 : g 0 = ((c 0 : ℝ) : ℂ) * cosineMode 0 x := evalCos_zero c x
  rw [show (∑' m : ℕ, g ((m:ℤ)+1)) + g 0 + ∑' m : ℕ, g (-((m:ℤ)+1))
        = ((∑' m : ℕ, g ((m:ℤ)+1)) + ∑' m : ℕ, g (-((m:ℤ)+1))) + g 0 by ring,
      hpairsum, hg0]
  -- 4. RHS: ℕ cosine series, split off k = 0
  have hcs : Summable (fun k : ℕ => ((c k : ℝ) : ℂ) * cosineMode k x) := by
    apply Summable.of_norm
    refine (hc.mul_right 1).of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    rw [norm_mul, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hcos : ‖((cosineMode k x : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, cosineMode]; exact Real.abs_cos_le_one _
    calc |c k| * ‖((cosineMode k x : ℝ) : ℂ)‖ ≤ |c k| * 1 :=
          mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
      _ = |c k| := by ring
  have hRHS : ((∑' k : ℕ, c k * cosineMode k x : ℝ) : ℂ)
      = ∑' k : ℕ, ((c k : ℝ) : ℂ) * cosineMode k x := by
    rw [Complex.ofReal_tsum]
    exact tsum_congr (fun k => by push_cast; ring)
  rw [hRHS, hcs.tsum_eq_zero_add]
  ring

end ShenWork.Wiener
