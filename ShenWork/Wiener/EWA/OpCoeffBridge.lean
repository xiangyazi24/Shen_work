import Mathlib
import ShenWork.Wiener.GWA.Operators
import ShenWork.Wiener.WeightedL1CosineAdapter
import ShenWork.Wiener.WeightedL1SineAdapter

/-!
# EWA brick — the operator-coefficient bridge (Phase C eval-bridge foundation)

This file is **pure coefficient algebra**.  It computes the action of the three
Fourier-multiplier operators on `GWA ℂ r`
(`ShenWork.GWA.GWA.gResolver`, `gDeriv`, the composite `gDeriv ∘ gResolver`) on the
even/odd cosine/sine embeddings of real coefficient families
(`ofCosineCoeffs`, `ofSineCoeffs` from the committed adapters).

Three bridges, all at the level of `.toFun : ℤ → ℂ`:

1. `gResolver_ofCosineCoeffs` — the elliptic resolver is **even-preserving**:
   `R_μ` sends `ofCosineCoeffs c` to `ofCosineCoeffs (k ↦ c_k/(μ+(kπ)²))`.
   The multiplier `1/(μ+(nπ)²)` is even in `n` (depends on `(nπ)²`), matching the
   evenness of `ofCosineCoeffs`.

2. `gDeriv_ofCosineCoeffs` — the derivative maps **even → odd**:
   `∂ₓ` sends `ofCosineCoeffs c` to `ofSineCoeffs (k ↦ -(kπ)·c_k)`.
   The multiplier `iπn` is odd in `n`; the `-i` in the `k>0` sine slot supplies the
   bookkeeping (`-i·(-kπ·c_k)/2 = i·kπ·c_k/2 = iπk·(c_k/2)`).

3. `gDerivResolver_ofCosineCoeffs` — the composite `∂ₓ R_μ`, the resolver gradient:
   `ofSineCoeffs (k ↦ -(kπ)·(c_k/(μ+(kπ)²)))`, obtained by composing 1 and 2.

No eval/realization, no PDE bricks: only the coefficient identities that the eval
bridge (B5) consumes.

## The i-arithmetic for the even→odd `gDeriv` case (the prime defect risk)
For `n = k > 0`: `gDeriv` multiplier is `I·π·k`, `ofCosineCoeffs c k = c_k/2`, so the
output coefficient is `I·π·k·(c_k/2)`.  The target `ofSineCoeffs (-kπ·c) k`
(`k > 0` slot is `-I·(·)/2`) is `-I·((-kπ)·c_k)/2 = I·(kπ·c_k)/2 = I·π·k·(c_k/2)`. ✓
For `n = -k < 0`: multiplier `I·π·(-k)`, `ofCosineCoeffs c (-k) = c_k/2`, output
`-I·π·k·(c_k/2)`.  Target `ofSineCoeffs (-kπ·c) (-k)` (`<0` slot is `+I·(·)/2`) is
`I·((-kπ)·c_k)/2 = -I·(kπ·c_k)/2 = -I·π·k·(c_k/2)`. ✓
The `natAbs` of `±k` is `k`, so both reference the same real coefficient `c_k`.
-/

open scoped BigOperators

namespace ShenWork.EWA

open ShenWork.Wiener ShenWork.GWA ShenWork.GWA.GWA

/-! ### The even cosine embedding as a `GWA ℂ r` element.

`MemW r a` and `GMemW r a` are definitionally equal (`wWeight = gWeight` share the
same body `(1+|n|)^r`, and both `MemW`/`GMemW` are `Summable (weight·‖·‖)`), so the
committed `memW_ofCosineCoeffs` directly supplies the `GMemW` witness. -/

variable {r : ℕ} {c : ℕ → ℝ}

/-- The even cosine embedding bundled as a `GWA ℂ r` element. -/
noncomputable def cosG (r : ℕ) (c : ℕ → ℝ)
    (hc : Summable (fun k : ℕ => (1 + (k : ℝ)) ^ r * |c k|)) : GWA ℂ r :=
  ⟨ofCosineCoeffs c, memW_ofCosineCoeffs (r := r) hc⟩

@[simp] theorem cosG_toFun (hc : Summable (fun k : ℕ => (1 + (k : ℝ)) ^ r * |c k|)) :
    (cosG r c hc).toFun = ofCosineCoeffs c := rfl

/-! ### 1. The resolver is even-preserving on cosine coefficients. -/

/-- **Resolver on cosine coefficients (even → even).**  The elliptic resolver
`R_μ` sends the even embedding of `c` to the even embedding of
`k ↦ c_k/(μ+(kπ)²)`.  The multiplier `1/(μ+(nπ)²)` depends only on `(nπ)²`, hence
is even, matching the evenness of `ofCosineCoeffs`. -/
theorem gResolver_ofCosineCoeffs (μ : ℝ) (hμ : 0 < μ)
    (hc : Summable (fun k : ℕ => (1 + (k : ℝ)) ^ r * |c k|)) :
    (gResolver (K := ℂ) μ hμ (cosG r c hc)).toFun
      = ofCosineCoeffs (fun k => c k / (μ + ((k : ℝ) * Real.pi) ^ 2)) := by
  funext n
  unfold gResolver
  rw [scalarMultiplier_toFun, cosG_toFun]
  -- LHS: (1/(μ+(nπ)²)) • ofCosineCoeffs c n  ;  RHS: ofCosineCoeffs (c/(μ+λ)) n
  have hμne : (μ : ℝ) ≠ 0 := ne_of_gt hμ
  rcases lt_trichotomy n 0 with hlt | heq | hgt
  · -- n = -k, k > 0
    obtain ⟨k, hk, hkpos⟩ : ∃ k : ℕ, n = -(k : ℤ) ∧ 0 < k :=
      ⟨n.natAbs, by omega, by omega⟩
    subst hk
    have hne : (-(k : ℤ)) ≠ 0 := by omega
    have hnat : (-(k : ℤ)).natAbs = k := by simp
    have hd : (μ + ((k : ℝ) * Real.pi) ^ 2) ≠ 0 := by positivity
    unfold ofCosineCoeffs
    rw [if_neg hne, if_neg hne, hnat, smul_eq_mul]
    push_cast
    rw [show ((-(k : ℂ)) * (Real.pi : ℂ)) ^ 2 = ((k : ℂ) * (Real.pi : ℂ)) ^ 2 by ring]
    field_simp
  · subst heq
    unfold ofCosineCoeffs
    rw [if_pos rfl, if_pos rfl, smul_eq_mul]
    push_cast
    field_simp
  · -- n = k, k > 0
    obtain ⟨k, hk, hkpos⟩ : ∃ k : ℕ, n = (k : ℤ) ∧ 0 < k :=
      ⟨n.natAbs, by omega, by omega⟩
    subst hk
    have hne : ((k : ℤ)) ≠ 0 := by omega
    have hnat : ((k : ℤ)).natAbs = k := by simp
    have hd : (μ + ((k : ℝ) * Real.pi) ^ 2) ≠ 0 := by positivity
    unfold ofCosineCoeffs
    rw [if_neg hne, if_neg hne, hnat, smul_eq_mul]
    push_cast
    field_simp

/-! ### 2. The derivative maps cosine (even) → sine (odd) coefficients. -/

/-- **Derivative on cosine coefficients (even → odd).**  `∂ₓ` sends the even
embedding of `c` to the odd embedding of `k ↦ -(kπ)·c_k`.  The multiplier `iπn` is
odd in `n`; the i-arithmetic in the sine slots (`-i/2` for `k>0`, `+i/2` for `k<0`)
exactly reassembles `iπn·(c_{|n|}/2)`. -/
theorem gDeriv_ofCosineCoeffs
    (hc : Summable (fun k : ℕ => (1 + (k : ℝ)) ^ (r + 1) * |c k|)) :
    (gDeriv (K := ℂ) (r := r) (cosG (r + 1) c hc)).toFun
      = ofSineCoeffs (fun k => -((k : ℝ) * Real.pi) * c k) := by
  funext n
  unfold gDeriv
  rw [scalarMultiplier_toFun, cosG_toFun]
  rcases lt_trichotomy n 0 with hlt | heq | hgt
  · -- n = -k, k > 0 : multiplier I·π·(-k), cos coeff c_k/2 ; sine <0 slot is +I·(·)/2
    obtain ⟨k, hk, hkpos⟩ : ∃ k : ℕ, n = -(k : ℤ) ∧ 0 < k :=
      ⟨n.natAbs, by omega, by omega⟩
    subst hk
    have hne : (-(k : ℤ)) ≠ 0 := by omega
    have hnpos : ¬ (0 : ℤ) < -(k : ℤ) := by omega
    have hnat : (-(k : ℤ)).natAbs = k := by simp
    unfold ofCosineCoeffs ofSineCoeffs
    rw [if_neg hne, if_neg hne, if_neg hnpos, hnat, smul_eq_mul]
    push_cast
    ring
  · subst heq
    unfold ofCosineCoeffs ofSineCoeffs
    rw [if_pos rfl, if_pos rfl, smul_eq_mul]
    push_cast
    ring
  · -- n = k, k > 0 : multiplier I·π·k, cos coeff c_k/2 ; sine >0 slot is -I·(·)/2
    obtain ⟨k, hk, hkpos⟩ : ∃ k : ℕ, n = (k : ℤ) ∧ 0 < k :=
      ⟨n.natAbs, by omega, by omega⟩
    subst hk
    have hne : ((k : ℤ)) ≠ 0 := by omega
    have hnpos : (0 : ℤ) < (k : ℤ) := by omega
    have hnat : ((k : ℤ)).natAbs = k := by simp
    unfold ofCosineCoeffs ofSineCoeffs
    rw [if_neg hne, if_neg hne, if_pos hnpos, hnat, smul_eq_mul]
    push_cast
    ring

/-! ### 3. The composite resolver-gradient. -/

/-- **Derivative of resolver on cosine coefficients (the resolver gradient).**
Composing 1 then 2: `∂ₓ R_μ` sends the even embedding of `c` to the odd embedding
of `k ↦ -(kπ)·(c_k/(μ+(kπ)²))` — exactly the `resolverGradReal` coefficient shape
`v̂_k·(-kπ)` with `v̂_k = c_k/(μ+(kπ)²)`. -/
theorem gDerivResolver_ofCosineCoeffs (μ : ℝ) (hμ : 0 < μ)
    (hc : Summable (fun k : ℕ => (1 + (k : ℝ)) ^ r * |c k|)) :
    (gDeriv (K := ℂ) (r := r + 1)
        (gResolver (K := ℂ) μ hμ (cosG r c hc))).toFun
      = ofSineCoeffs (fun k => -((k : ℝ) * Real.pi)
          * (c k / (μ + ((k : ℝ) * Real.pi) ^ 2))) := by
  have hres := gResolver_ofCosineCoeffs (r := r) μ hμ hc
  funext n
  -- rewrite the resolver-then-deriv coefficient using scalarMultiplier twice
  unfold gDeriv
  rw [scalarMultiplier_toFun, hres]
  -- now LHS = (iπn) • ofCosineCoeffs d n ; identical to gDeriv_ofCosineCoeffs body
  rcases lt_trichotomy n 0 with hlt | heq | hgt
  · obtain ⟨k, hk, hkpos⟩ : ∃ k : ℕ, n = -(k : ℤ) ∧ 0 < k :=
      ⟨n.natAbs, by omega, by omega⟩
    subst hk
    have hne : (-(k : ℤ)) ≠ 0 := by omega
    have hnpos : ¬ (0 : ℤ) < -(k : ℤ) := by omega
    have hnat : (-(k : ℤ)).natAbs = k := by simp
    unfold ofCosineCoeffs ofSineCoeffs
    rw [if_neg hne, if_neg hne, if_neg hnpos, hnat, smul_eq_mul]
    push_cast
    ring
  · subst heq
    unfold ofCosineCoeffs ofSineCoeffs
    rw [if_pos rfl, if_pos rfl, smul_eq_mul]
    push_cast
    ring
  · obtain ⟨k, hk, hkpos⟩ : ∃ k : ℕ, n = (k : ℤ) ∧ 0 < k :=
      ⟨n.natAbs, by omega, by omega⟩
    subst hk
    have hne : ((k : ℤ)) ≠ 0 := by omega
    have hnpos : (0 : ℤ) < (k : ℤ) := by omega
    have hnat : ((k : ℤ)).natAbs = k := by simp
    unfold ofCosineCoeffs ofSineCoeffs
    rw [if_neg hne, if_neg hne, if_pos hnpos, hnat, smul_eq_mul]
    push_cast
    ring

end ShenWork.EWA
