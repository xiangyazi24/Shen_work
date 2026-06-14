import ShenWork.Wiener.GWA.Operators
import ShenWork.Wiener.WeightedL1CosineAdapter
import ShenWork.Wiener.WeightedL1SineAdapter

/-!
# Sequence-parity atoms for the weighted Wiener convolution algebra — brick (parity)

Pure `ℤ → ℂ` sequence parity, feeding the Phase C endgame parity propagation (the
chemotaxis source's evenness).  Nothing here touches realization, evaluation, or the
PDE layer: these are bookkeeping facts about how the bilateral convolution `gConv`
and the diagonal `iπn` multiplier interact with even/odd sequences.

`IsEvenSeq a : a(-n) = a n`, `IsOddSeq a : a(-n) = -a n`.

Delivered:
* `gConv_even_even / gConv_even_odd / gConv_odd_odd / gConv_odd_even` — the parity
  multiplication table of bilateral convolution.  The single subtlety is the
  reindex `m ↦ -m` inside the `tsum`; we use `(Equiv.neg ℤ).tsum_eq` (the
  unconditional `Equiv.tsum_eq`, no summability side-goal — the same pattern the
  committed `IntervalFullSemigroupNeumann` uses).
* `gDeriv_symbol_odd_of_even / gDeriv_symbol_even_of_odd` — the diagonal `iπn`
  symbol flips parity (the `iπ(-n) = -iπn` sign flip; at `n = 0` the term is `0`).
  Stated both for the raw symbol-multiplied sequence and for the `gDeriv … .toFun`
  form via `scalarMultiplier_toFun`.
* `ofCosineCoeffs_isEven`, `ofSineCoeffs_isOdd` — the adapter embeddings have the
  expected parity (from the committed `ofCosineCoeffs_neg` / `ofSineCoeffs_neg`).
-/

open scoped BigOperators

namespace ShenWork.EWA

open ShenWork.GWA

/-- An even ℤ-indexed `ℂ`-sequence: `a(-n) = a n`. -/
def IsEvenSeq (a : ℤ → ℂ) : Prop := ∀ n, a (-n) = a n

/-- An odd ℤ-indexed `ℂ`-sequence: `a(-n) = -a n`. -/
def IsOddSeq (a : ℤ → ℂ) : Prop := ∀ n, a (-n) = -a n

/-! ### The convolution parity multiplication table. -/

section Conv

variable {a b : ℤ → ℂ}

/-- **The reindexed convolution at `-n`.**  `gConv a b (-n) = ∑' m, a(-m)·b(-(n-m))`,
the single fiddly step: the `m ↦ -m` reindex of the bilateral `tsum`, done with the
unconditional `(Equiv.neg ℤ).tsum_eq` (no summability side-goal). -/
private theorem gConv_neg_reindex (a b : ℤ → ℂ) (n : ℤ) :
    gConv a b (-n) = ∑' m : ℤ, a (-m) * b (-(n - m)) := by
  change (∑' m : ℤ, a m * b (-n - m)) = ∑' m : ℤ, a (-m) * b (-(n - m))
  rw [← (Equiv.neg ℤ).tsum_eq (fun m => a m * b (-n - m))]
  refine tsum_congr (fun m => ?_)
  simp only [Equiv.neg_apply]
  congr 2
  ring

/-- **Even ⋆ even = even.** -/
theorem gConv_even_even (ha : IsEvenSeq a) (hb : IsEvenSeq b) :
    IsEvenSeq (gConv a b) := by
  intro n
  rw [gConv_neg_reindex a b n]
  change (∑' m : ℤ, a (-m) * b (-(n - m))) = ∑' m : ℤ, a m * b (n - m)
  refine tsum_congr (fun m => ?_)
  rw [ha m, hb (n - m)]

/-- **Even ⋆ odd = odd.** -/
theorem gConv_even_odd (ha : IsEvenSeq a) (hb : IsOddSeq b) :
    IsOddSeq (gConv a b) := by
  intro n
  rw [gConv_neg_reindex a b n]
  change (∑' m : ℤ, a (-m) * b (-(n - m))) = -∑' m : ℤ, a m * b (n - m)
  rw [← tsum_neg]
  refine tsum_congr (fun m => ?_)
  rw [ha m, hb (n - m)]
  ring

/-- **Odd ⋆ odd = even.** -/
theorem gConv_odd_odd (ha : IsOddSeq a) (hb : IsOddSeq b) :
    IsEvenSeq (gConv a b) := by
  intro n
  rw [gConv_neg_reindex a b n]
  change (∑' m : ℤ, a (-m) * b (-(n - m))) = ∑' m : ℤ, a m * b (n - m)
  refine tsum_congr (fun m => ?_)
  rw [ha m, hb (n - m)]
  ring

/-- **Odd ⋆ even = odd.** -/
theorem gConv_odd_even (ha : IsOddSeq a) (hb : IsEvenSeq b) :
    IsOddSeq (gConv a b) := by
  intro n
  rw [gConv_neg_reindex a b n]
  change (∑' m : ℤ, a (-m) * b (-(n - m))) = -∑' m : ℤ, a m * b (n - m)
  rw [← tsum_neg]
  refine tsum_congr (fun m => ?_)
  rw [ha m, hb (n - m)]
  ring

end Conv

/-! ### The `iπn` diagonal multiplier flips parity. -/

section Deriv

variable {a : ℤ → ℂ}

/-- The diagonal Fourier-derivative symbol `iπn`. -/
private noncomputable def iPiSym (n : ℤ) : ℂ := Complex.I * Real.pi * (n : ℂ)

/-- `iπ(-n) = -iπn` (the sign flip that drives the parity reversal). -/
private theorem iPiSym_neg (n : ℤ) : iPiSym (-n) = -iPiSym n := by
  unfold iPiSym; push_cast; ring

/-- **Raw symbol parity: even ↦ odd.**  Multiplying an even sequence by the diagonal
`iπn` symbol yields an odd sequence (the `n = 0` term being `0` is automatic). -/
theorem gDeriv_symbol_odd_of_even (ha : IsEvenSeq a) :
    IsOddSeq (fun n : ℤ => Complex.I * Real.pi * (n : ℂ) * a n) := by
  intro n
  change iPiSym (-n) * a (-n) = -(iPiSym n * a n)
  rw [iPiSym_neg, ha n]
  ring

/-- **Raw symbol parity: odd ↦ even.** -/
theorem gDeriv_symbol_even_of_odd (ha : IsOddSeq a) :
    IsEvenSeq (fun n : ℤ => Complex.I * Real.pi * (n : ℂ) * a n) := by
  intro n
  change iPiSym (-n) * a (-n) = iPiSym n * a n
  rw [iPiSym_neg, ha n]
  ring

/-- **`gDeriv` parity (even ↦ odd), `.toFun` form.**  The output sequence of `gDeriv`
on an even input is odd.  Bridges through `scalarMultiplier_toFun` to the raw symbol
parity above (`K = ℂ`). -/
theorem gDeriv_toFun_odd_of_even {r : ℕ} (x : GWA.GWA ℂ (r + 1))
    (hx : IsEvenSeq x.toFun) :
    IsOddSeq (fun n => (GWA.gDeriv (K := ℂ) (r := r) x).toFun n) := by
  have hsym : (fun n => (GWA.gDeriv (K := ℂ) (r := r) x).toFun n)
      = fun n : ℤ => Complex.I * Real.pi * (n : ℂ) * x.toFun n := by
    funext n
    rw [GWA.gDeriv, GWA.scalarMultiplier_toFun, smul_eq_mul]
  rw [hsym]
  exact gDeriv_symbol_odd_of_even hx

/-- **`gDeriv` parity (odd ↦ even), `.toFun` form.** -/
theorem gDeriv_toFun_even_of_odd {r : ℕ} (x : GWA.GWA ℂ (r + 1))
    (hx : IsOddSeq x.toFun) :
    IsEvenSeq (fun n => (GWA.gDeriv (K := ℂ) (r := r) x).toFun n) := by
  have hsym : (fun n => (GWA.gDeriv (K := ℂ) (r := r) x).toFun n)
      = fun n : ℤ => Complex.I * Real.pi * (n : ℂ) * x.toFun n := by
    funext n
    rw [GWA.gDeriv, GWA.scalarMultiplier_toFun, smul_eq_mul]
  rw [hsym]
  exact gDeriv_symbol_even_of_odd hx

end Deriv

/-! ### Adapter-embedding parity (from the committed neg lemmas). -/

/-- The cosine embedding is even. -/
theorem ofCosineCoeffs_isEven (c : ℕ → ℝ) :
    IsEvenSeq (ShenWork.Wiener.ofCosineCoeffs c) :=
  fun n => ShenWork.Wiener.ofCosineCoeffs_neg c n

/-- The sine embedding is odd. -/
theorem ofSineCoeffs_isOdd (c : ℕ → ℝ) :
    IsOddSeq (ShenWork.Wiener.ofSineCoeffs c) :=
  fun n => ShenWork.Wiener.ofSineCoeffs_neg c n

end ShenWork.EWA
