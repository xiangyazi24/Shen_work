import Mathlib
import ShenWork.Wiener.WeightedL1Convolution
import ShenWork.Wiener.WeightedL1Eval
import ShenWork.PDE.CosineSpectrum

/-!
# The sine ↔ ℤ-bilateral adapter (algebraic core + synthesis) — the SINE mirror

This is the odd/sine mirror of the committed cosine adapter
(`WeightedL1CosineAdapter` / `WeightedL1CosineEval`).  A real `f` on `[0,1]` with a
Dirichlet/sine expansion `f(x) = ∑_{k≥1} (c k) · sin(k π x)` is transported into the
exponential basis `e^{i n π x}` (`n ∈ ℤ`).  Since
`sin(k π x) = (e^{i k π x} − e^{-i k π x}) / (2i)`, the ℤ-bilateral coefficient is the
ODD (purely imaginary) embedding
`a₀ = 0`, `a_k = −i·c_{|k|}/2` (`k>0`), `a_{−k} = i·c_{|k|}/2` (`k>0`).
Thus `a_{−n} = −a_n` (oddness), mirroring the cosine adapter's evenness.

We prove the sine analogues of `ofCosineCoeffs_neg`, `memW_ofCosineCoeffs`,
`wNorm_ofCosineCoeffs`, and the synthesis seam `evalC_ofCosineCoeffs`.  The sine
pairing `sin(nπx) = (fourier n x − fourier (−n) x)/(2i)` is derived inline from
`Complex.two_sin` and `fourier_coe_apply` (no committed sine-pairing lemma exists).
This synthesis identity is stated for ALL real `x` (the pairing is unrestricted).
-/

open scoped BigOperators

namespace ShenWork.Wiener

open ShenWork.CosineSpectrum

/-- The sine mode on the ambient real line: `sineMode n x = sin(n π x)`.  The
odd analogue of the committed `cosineMode`. -/
noncomputable def sineMode (n : ℕ) (x : ℝ) : ℝ :=
  Real.sin ((n : ℝ) * Real.pi * x)

/-- The odd ℤ-bilateral embedding of real sine coefficients:
`a₀ = 0`, `a_k = −i·c_{|k|}/2` for `k > 0`, and `a_k = i·c_{|k|}/2` for `k < 0`. -/
noncomputable def ofSineCoeffs (c : ℕ → ℝ) : ℤ → ℂ :=
  fun n =>
    if n = 0 then 0
    else if 0 < n then (-(Complex.I) * (c n.natAbs : ℝ) / 2)
    else ((Complex.I) * (c n.natAbs : ℝ) / 2)

/-- Oddness: `ofSineCoeffs c (-n) = - ofSineCoeffs c n`. -/
theorem ofSineCoeffs_neg (c : ℕ → ℝ) (n : ℤ) :
    ofSineCoeffs c (-n) = - ofSineCoeffs c n := by
  unfold ofSineCoeffs
  rcases lt_trichotomy n 0 with hlt | heq | hgt
  · have h1 : (-n) ≠ 0 := by omega
    have h2 : n ≠ 0 := by omega
    have h3 : (0 : ℤ) < -n := by omega
    have h4 : ¬ (0 : ℤ) < n := by omega
    rw [if_neg h1, if_neg h2, if_pos h3, if_neg h4, Int.natAbs_neg]
    ring
  · simp [heq]
  · have h1 : (-n) ≠ 0 := by omega
    have h2 : n ≠ 0 := by omega
    have h3 : ¬ (0 : ℤ) < -n := by omega
    have h4 : (0 : ℤ) < n := by omega
    rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4, Int.natAbs_neg]
    ring

/-- The norm of a coefficient: `if n = 0 then 0 else |c_{|n|}|/2`. -/
theorem norm_ofSineCoeffs (c : ℕ → ℝ) (n : ℤ) :
    ‖ofSineCoeffs c n‖ = if n = 0 then 0 else |c n.natAbs| / 2 := by
  unfold ofSineCoeffs
  by_cases h : n = 0
  · simp [h]
  · rcases lt_or_gt_of_ne h with hlt | hgt
    · have h4 : ¬ (0 : ℤ) < n := by omega
      rw [if_neg h, if_neg h, if_neg h4]
      rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, Complex.norm_ofNat]
    · have h4 : (0 : ℤ) < n := by omega
      rw [if_neg h, if_neg h, if_pos h4]
      rw [norm_div, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, Complex.norm_ofNat]

/-- The weighted ℓ¹ summand for `ofSineCoeffs`. -/
private noncomputable def wterm (r : ℕ) (c : ℕ → ℝ) (n : ℤ) : ℝ :=
  wWeight r n * ‖ofSineCoeffs c n‖

/-- The target (sine-side) summand. -/
private def cterm (r : ℕ) (c : ℕ → ℝ) (k : ℕ) : ℝ := (1 + (k : ℝ)) ^ r * |c k|

/-- At `0` the weighted summand vanishes (the sine `n = 0` mode is absent). -/
private theorem wterm_zero (r : ℕ) (c : ℕ → ℝ) : wterm r c 0 = 0 := by
  unfold wterm wWeight
  rw [norm_ofSineCoeffs]; simp

/-- On the positive half, the weighted summand is half the sine summand at `k+1`. -/
private theorem wterm_succ (r : ℕ) (c : ℕ → ℝ) (m : ℕ) :
    wterm r c ((m : ℤ) + 1) = cterm r c (m + 1) / 2 := by
  unfold wterm cterm wWeight
  rw [norm_ofSineCoeffs (n := ((m : ℤ) + 1))]
  have hne : ((m : ℤ) + 1) ≠ 0 := by omega
  rw [if_neg hne]
  have hcast : |(((m : ℤ) + 1 : ℤ) : ℝ)| = 1 + (m : ℝ) := by
    push_cast; rw [abs_of_nonneg (by positivity)]; ring
  have hnat : ((m : ℤ) + 1).natAbs = m + 1 := by omega
  rw [hcast, hnat]; push_cast; ring

/-- On the negative half, the weighted summand is also half the sine summand at `k+1`. -/
private theorem wterm_neg_succ (r : ℕ) (c : ℕ → ℝ) (m : ℕ) :
    wterm r c (-((m : ℤ) + 1)) = cterm r c (m + 1) / 2 := by
  unfold wterm cterm wWeight
  rw [norm_ofSineCoeffs (n := (-((m : ℤ) + 1)))]
  have hne : (-((m : ℤ) + 1)) ≠ 0 := by omega
  rw [if_neg hne]
  have hcast : |((-((m : ℤ) + 1) : ℤ) : ℝ)| = 1 + (m : ℝ) := by
    push_cast; rw [abs_neg, abs_of_nonneg (by positivity)]; ring
  have hnat : (-((m : ℤ) + 1)).natAbs = m + 1 := by omega
  rw [hcast, hnat]; push_cast; ring

/-- Summability of the sine summand at shifted index `k+1`. -/
private theorem summable_cterm_succ {r : ℕ} {c : ℕ → ℝ}
    (hc : Summable (cterm r c)) : Summable (fun m : ℕ => cterm r c (m + 1)) :=
  (summable_nat_add_iff 1).2 hc

/-- Membership of the embedded coefficients in the weighted ℓ¹ space. -/
theorem memW_ofSineCoeffs {r : ℕ} {c : ℕ → ℝ}
    (hc : Summable (fun k : ℕ => (1 + (k : ℝ)) ^ r * |c k|)) :
    MemW r (ofSineCoeffs c) := by
  have hc' : Summable (cterm r c) := hc
  have hpos : Summable (fun m : ℕ => wterm r c ((m : ℤ) + 1)) :=
    ((summable_cterm_succ hc').div_const 2).congr (fun m => (wterm_succ r c m).symm)
  have hneg : Summable (fun m : ℕ => wterm r c (-((m : ℤ) + 1))) :=
    ((summable_cterm_succ hc').div_const 2).congr (fun m => (wterm_neg_succ r c m).symm)
  exact (hpos.of_add_one_of_neg_add_one hneg)

/-- **The adapter norm identity**: the weighted ℓ¹ norm of the embedded sine
coefficients equals the sine-side weighted ℓ¹ norm `∑_{k≥0} (1+k)^r |c k|`.  The
`k = 0` term contributes nothing on the WA side (`a₀ = 0`); on the sine side it
contributes `(1+0)^r |c 0| = |c 0|` — exactly the `c 0` slot, which a true sine
series ignores.  We therefore state the identity against the FULL `ℕ`-sum of the
embedded magnitudes shifted by one, i.e. the genuine `∑_{k≥1}` mass. -/
theorem wNorm_ofSineCoeffs {r : ℕ} {c : ℕ → ℝ}
    (hc : Summable (fun k : ℕ => (1 + (k : ℝ)) ^ r * |c k|)) :
    wNorm r (ofSineCoeffs c) = ∑' k : ℕ, (1 + ((k : ℝ) + 1)) ^ r * |c (k + 1)| := by
  have hc' : Summable (cterm r c) := hc
  have hcs := summable_cterm_succ hc'
  have hpos : Summable (fun m : ℕ => wterm r c ((m : ℤ) + 1)) :=
    (hcs.div_const 2).congr (fun m => (wterm_succ r c m).symm)
  have hneg : Summable (fun m : ℕ => wterm r c (-((m : ℤ) + 1))) :=
    (hcs.div_const 2).congr (fun m => (wterm_neg_succ r c m).symm)
  have hsplit : (∑' n : ℤ, wterm r c n)
      = (∑' m : ℕ, wterm r c ((m : ℤ) + 1)) + wterm r c 0
        + ∑' m : ℕ, wterm r c (-((m : ℤ) + 1)) :=
    tsum_of_add_one_of_neg_add_one hpos hneg
  have hposval : (∑' m : ℕ, wterm r c ((m : ℤ) + 1))
      = ∑' m : ℕ, cterm r c (m + 1) / 2 :=
    tsum_congr (fun m => wterm_succ r c m)
  have hnegval : (∑' m : ℕ, wterm r c (-((m : ℤ) + 1)))
      = ∑' m : ℕ, cterm r c (m + 1) / 2 :=
    tsum_congr (fun m => wterm_neg_succ r c m)
  have hwNorm : wNorm r (ofSineCoeffs c) = ∑' n : ℤ, wterm r c n := rfl
  rw [hwNorm, hsplit, hposval, hnegval, wterm_zero]
  rw [show (∑' m : ℕ, cterm r c (m + 1) / 2) = (∑' m : ℕ, cterm r c (m + 1)) / 2 from
    tsum_div_const]
  have htgt : (∑' k : ℕ, (1 + ((k : ℝ) + 1)) ^ r * |c (k + 1)|)
      = ∑' m : ℕ, cterm r c (m + 1) := by
    apply tsum_congr; intro m; unfold cterm; push_cast; ring
  rw [htgt]; ring

/-! ### Synthesis seam: the WA synthesis of `ofSineCoeffs` is the sine series. -/

open WA

/-- The inline sine pairing: `sin(nπx) = (fourier n x − fourier (−n) x)/(2i)`.
Derived from `Complex.two_sin` and `fourier_coe_apply`.  Unrestricted in `x`. -/
private theorem unitIntervalSine_eq_fourier_pair (n : ℕ) (x : ℝ) :
    ((Real.sin ((n : ℝ) * Real.pi * x) : ℂ)) =
      (-(Complex.I) / 2) *
        (fourier (T := (2 : ℝ)) (n : ℤ) (x : AddCircle (2 : ℝ)) -
          fourier (T := (2 : ℝ)) (-(n : ℤ)) (x : AddCircle (2 : ℝ))) := by
  let θ : ℂ := ((n : ℝ) * Real.pi * x : ℝ)
  have hpos :
      fourier (T := (2 : ℝ)) (n : ℤ) (x : AddCircle (2 : ℝ)) =
        Complex.exp (θ * Complex.I) := by
    rw [fourier_coe_apply]; congr 1; dsimp [θ]; norm_num; ring
  have hneg :
      fourier (T := (2 : ℝ)) (-(n : ℤ)) (x : AddCircle (2 : ℝ)) =
        Complex.exp (-θ * Complex.I) := by
    rw [fourier_coe_apply]; congr 1; dsimp [θ]; norm_num; ring
  rw [hpos, hneg]
  have htwo : 2 * Complex.sin θ = (Complex.exp (-θ * Complex.I)
      - Complex.exp (θ * Complex.I)) * Complex.I := Complex.two_sin θ
  have hsin : ((Real.sin ((n : ℝ) * Real.pi * x) : ℝ) : ℂ) = Complex.sin θ := by
    dsimp [θ]; rw [Complex.ofReal_sin]
  rw [hsin]
  have hkey : Complex.sin θ
      = (-(Complex.I) / 2) * (Complex.exp (θ * Complex.I)
          - Complex.exp (-θ * Complex.I)) := by
    have hsin2 : Complex.sin θ = ((Complex.exp (-θ * Complex.I)
        - Complex.exp (θ * Complex.I)) * Complex.I) / 2 := by
      linear_combination htwo / 2
    rw [hsin2]; ring
  rw [hkey]

/-- The `n = 0` synthesis term is zero (the sine series has no constant mode). -/
private theorem evalSin_zero (c : ℕ → ℝ) (x : ℝ) :
    (ofSineCoeffs c 0) • fourier (T := (2:ℝ)) 0 (x : AddCircle (2:ℝ)) = 0 := by
  rw [ofSineCoeffs]; simp

/-- The paired `±(m+1)` synthesis terms collapse to `c (m+1) · sineMode (m+1) x`
via the inline sine-pair bridge.  The `−i/2` in each coefficient times the
`(fourier n − fourier (−n))` difference (with the `+i/2` on the negative slot)
reassembles `(fourier n − fourier (−n))·(−i/2)`, i.e. the bare `c (m+1)·sin`. -/
private theorem evalSin_pair (c : ℕ → ℝ) (x : ℝ) (m : ℕ) :
    (ofSineCoeffs c ((m:ℤ)+1)) • fourier (T := (2:ℝ)) ((m:ℤ)+1) (x : AddCircle (2:ℝ))
      + (ofSineCoeffs c (-((m:ℤ)+1))) • fourier (T := (2:ℝ)) (-((m:ℤ)+1))
          (x : AddCircle (2:ℝ))
      = ((c (m+1) : ℝ) : ℂ) * sineMode (m+1) x := by
  rw [ofSineCoeffs_neg]
  have hval : ofSineCoeffs c ((m:ℤ)+1) = (-(Complex.I) * (c (m+1) : ℝ) / 2 : ℂ) := by
    unfold ofSineCoeffs
    rw [if_neg (by omega), if_pos (by omega)]
    have : ((m:ℤ)+1).natAbs = m+1 := by omega
    rw [this]
  rw [hval, smul_eq_mul, neg_smul, smul_eq_mul]
  have hbridge := unitIntervalSine_eq_fourier_pair (m+1) x
  rw [sineMode]
  have hcast : ((m:ℤ)+1 : ℤ) = ((m+1 : ℕ) : ℤ) := by push_cast; ring
  rw [hcast, hbridge]; push_cast; ring

open WA in
/-- **The basis-match (sine seam).** The Wiener synthesis of the odd embedding of
real sine coefficients equals the committed-style sine series, pointwise, for ALL
real `x`. -/
theorem evalC_ofSineCoeffs (c : ℕ → ℝ) (hc : Summable (fun k => |c k|))
    (x : ℝ) :
    WA.evalC (⟨ofSineCoeffs c, memW_ofSineCoeffs (r := 0) (by simpa using hc)⟩ : WA 0)
        (x : AddCircle (2:ℝ))
      = ((∑' k : ℕ, c k * sineMode k x : ℝ) : ℂ) := by
  set a : WA 0 := ⟨ofSineCoeffs c, memW_ofSineCoeffs (r := 0) (by simpa using hc)⟩ with ha
  set g : ℤ → ℂ := fun n => (ofSineCoeffs c n) • fourier (T := (2:ℝ)) n
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
  -- combine the two ℕ tails into one (pos + neg = the sine pair)
  have hpairsum : (∑' m : ℕ, g ((m:ℤ)+1)) + ∑' m : ℕ, g (-((m:ℤ)+1))
      = ∑' m : ℕ, ((c (m+1) : ℝ) : ℂ) * sineMode (m+1) x := by
    rw [← hpos.tsum_add hneg]
    exact tsum_congr (fun m => evalSin_pair c x m)
  -- regroup: zero term + pair tail
  have hg0 : g 0 = 0 := evalSin_zero c x
  rw [show (∑' m : ℕ, g ((m:ℤ)+1)) + g 0 + ∑' m : ℕ, g (-((m:ℤ)+1))
        = ((∑' m : ℕ, g ((m:ℤ)+1)) + ∑' m : ℕ, g (-((m:ℤ)+1))) + g 0 by ring,
      hpairsum, hg0, add_zero]
  -- 4. RHS: ℕ sine series, split off k = 0 (which is 0 since sineMode 0 x = 0)
  have hcs : Summable (fun k : ℕ => ((c k : ℝ) : ℂ) * sineMode k x) := by
    apply Summable.of_norm
    refine (hc.mul_right 1).of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    rw [norm_mul, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hsin : ‖((sineMode k x : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, sineMode]; exact Real.abs_sin_le_one _
    calc |c k| * ‖((sineMode k x : ℝ) : ℂ)‖ ≤ |c k| * 1 :=
          mul_le_mul_of_nonneg_left hsin (abs_nonneg _)
      _ = |c k| := by ring
  have hRHS : ((∑' k : ℕ, c k * sineMode k x : ℝ) : ℂ)
      = ∑' k : ℕ, ((c k : ℝ) : ℂ) * sineMode k x := by
    rw [Complex.ofReal_tsum]
    exact tsum_congr (fun k => by push_cast; ring)
  rw [hRHS, hcs.tsum_eq_zero_add]
  have hzero : ((c 0 : ℝ) : ℂ) * sineMode 0 x = 0 := by
    rw [sineMode]; simp
  rw [hzero, zero_add]

end ShenWork.Wiener
