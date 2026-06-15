import ShenWork.Wiener.EWA.SourceFixedPointClean

/-!
# χ₀<0 datum-uniform lifespan extraction (atom (a))

The `ChiNegDatumUniformConstruction` residual
(`ShenWork.EWA.SourceChiNegTheorem11`) quantifies in the order
`∀ M, ∃ δ, ∀ u₀ (|u₀| ≤ M), …` — ONE shared lifespan `δ(M)` good for every
admissible datum with sup-norm `≤ M`.

The per-datum EWA fixed-point engine `picardEWA_clean_fixedPoint`
(`ShenWork.EWA.SourceFixedPointClean`) instead chooses its horizon `T` *after*
seeing the datum, via the two-smallness time chooser `exists_small_two_conditions`
with the constants

* contraction:  `A = |χ₀|·C₀·L_Q`,  `B = L_G`,
* self-map:     `A' = |χ₀|·C₀·M_Q`, `B' = M_G`.

All four constants `L_Q, L_G, M_Q, M_G` are **`T`-independent** (see
`picardEWA_clean_fixedPoint`); they depend on the datum ONLY through

* the radius  `R = ‖u₀E‖ + δ_floor/2`  (Wiener norm of the cosine embedding), and
* the positivity floor `δ_floor` with `u₀ ≥ δ_floor > 0`,

through the `negNormConst`/`negLipConst` Γ-combinations, which are monotone
(nondecreasing) in `R` and in `1/δ_floor`.

This file isolates the bookkeeping step that lifts per-datum → datum-uniform:
the chosen time `T = 1/(A + B + 1)²` is **monotone decreasing** in the four
constants, so a single uniform UPPER bound on `(A, B, A', B')` — equivalently a
uniform bound on `(L_Q, L_G, M_Q, M_G)` — yields a single `δ` that works for the
whole family.  We prove this monotone-lifespan fact as a clean, datum-independent
lemma.

The two *genuine* missing controls — surfaced here as the hypotheses of the
uniform-bound lemma, NOT silently assumed — are exactly what the sup-norm class
`|u₀| ≤ M` does NOT supply on the open interval `(0,1)`:

1. **uniform Wiener-norm bound**: `‖u₀E‖ ≤ W(M)`.  The sup bound `|u₀| ≤ M`
   controls the `L∞` norm, but `‖u₀E‖ = Σ |cosineCoeffs u₀ k|·gWeight` is the
   stronger absolutely-summable (Wiener/ℓ¹) norm; it is NOT bounded by `M`.

2. **uniform positivity floor**: `δ_floor ≥ φ(M) > 0`.  `PositiveInitialDatum`
   gives only pointwise `0 < u₀ x` on the OPEN `inside = (0,1)`; a continuous
   datum positive on `(0,1)` may have `inf = 0` (vanishing at the endpoints),
   so no floor — let alone a uniform one — is available.

Hence the headline obligation that remains for χ₀<0 hQuant is precisely these two
controls; the lifespan extraction itself is the monotone bookkeeping proved here.

No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/

open scoped BigOperators
open ShenWork.IntervalChemFluxLipschitz (exists_small_contraction_time)

noncomputable section

namespace ShenWork.EWA

/-! ### Monotonicity of the explicit small-contraction time. -/

/-- The explicit two-smallness time `T = 1/(c²)` with `c = max(A+B, A'+B') + 1`
works simultaneously for the contraction `A·√T + B·T < 1` and the self-map
smallness `A'·√T + B'·T ≤ ρ`, PROVIDED `1 ≤ ρ` is NOT required — it works for the
contraction unconditionally and for the self-map under the stated bound.  This is
the datum-independent core: the chosen time depends only on the constant data
`(A, B, A', B')` and is monotone decreasing in each.

We package it as: given a uniform UPPER bound `Ā, B̄, Ā', B̄'` on the constants and
`0 < ρ`, there is a single `δ > 0` such that for EVERY constant tuple dominated by
the bounds, both smallness conditions hold at that `δ`. -/
theorem exists_uniform_small_two_conditions
    {Abar Bbar Abar' Bbar' ρ : ℝ} (hAbar : 0 ≤ Abar) (hBbar : 0 ≤ Bbar)
    (hAbar' : 0 ≤ Abar') (hBbar' : 0 ≤ Bbar') (hρ : 0 < ρ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {A B A' B' : ℝ}, 0 ≤ A → 0 ≤ B → 0 ≤ A' → 0 ≤ B' →
        A ≤ Abar → B ≤ Bbar → A' ≤ Abar' → B' ≤ Bbar' →
        A * Real.sqrt δ + B * δ < 1 ∧ A' * Real.sqrt δ + B' * δ ≤ ρ := by
  -- Choose the time for the WORST tuple (Abar, Bbar, Abar', Bbar'); any dominated
  -- tuple is then automatically fine since `x ↦ x·√δ + y·δ` is monotone in (x, y).
  obtain ⟨δ, hδpos, hcontr, hself⟩ :=
    exists_small_two_conditions hAbar hBbar hAbar' hBbar' hρ
  refine ⟨δ, hδpos, ?_⟩
  intro A B A' B' hA hB hA' hB' hAle hBle hA'le hB'le
  have hsqrt_nn : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg δ
  have hδ_nn : 0 ≤ δ := hδpos.le
  constructor
  · -- contraction: monotone in `(A, B)` upward, dominated by the worst tuple.
    have h1 : A * Real.sqrt δ ≤ Abar * Real.sqrt δ :=
      mul_le_mul_of_nonneg_right hAle hsqrt_nn
    have h2 : B * δ ≤ Bbar * δ := mul_le_mul_of_nonneg_right hBle hδ_nn
    linarith
  · -- self-map: same monotone domination.
    have h1 : A' * Real.sqrt δ ≤ Abar' * Real.sqrt δ :=
      mul_le_mul_of_nonneg_right hA'le hsqrt_nn
    have h2 : B' * δ ≤ Bbar' * δ := mul_le_mul_of_nonneg_right hB'le hδ_nn
    linarith

/-! ### Specialization to the EWA contraction/self-map constants.

The four constants `(A, B, A', B') = (|χ₀|·C₀·L_Q, L_G, |χ₀|·C₀·M_Q, M_G)` are the
exact arguments fed to `exists_small_two_conditions` inside
`picardEWA_clean_fixedPoint`.  Given uniform upper bounds on `(L_Q, L_G, M_Q, M_G)`
over an admissible datum family, `exists_uniform_small_two_conditions` supplies a
single `δ` making both the contraction `hK` and the self-map smallness `hsmall`
hold at that `δ` for EVERY member of the family — which is exactly the
datum-uniform lifespan needed to reorder `∀ u₀, ∃ T` into `∃ T, ∀ u₀`. -/
theorem exists_uniform_EWA_lifespan
    {χ₀ LQbar LGbar MQbar MGbar ρ : ℝ}
    (hLQbar : 0 ≤ LQbar) (hLGbar : 0 ≤ LGbar) (hMQbar : 0 ≤ MQbar)
    (hMGbar : 0 ≤ MGbar) (hρ : 0 < ρ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {L_Q L_G M_Q M_G : ℝ}, 0 ≤ L_Q → 0 ≤ L_G → 0 ≤ M_Q → 0 ≤ M_G →
        L_Q ≤ LQbar → L_G ≤ LGbar → M_Q ≤ MQbar → M_G ≤ MGbar →
        (|χ₀| * C₀ * L_Q) * Real.sqrt δ + L_G * δ < 1 ∧
        (|χ₀| * C₀ * M_Q) * Real.sqrt δ + M_G * δ ≤ ρ := by
  have hC₀ : (0 : ℝ) ≤ C₀ := C₀_nonneg
  have hχ : (0 : ℝ) ≤ |χ₀| := abs_nonneg _
  obtain ⟨δ, hδpos, hbody⟩ :=
    exists_uniform_small_two_conditions
      (Abar := |χ₀| * C₀ * LQbar) (Bbar := LGbar)
      (Abar' := |χ₀| * C₀ * MQbar) (Bbar' := MGbar)
      (by positivity) hLGbar (by positivity) hMGbar hρ
  refine ⟨δ, hδpos, ?_⟩
  intro L_Q L_G M_Q M_G hLQ hLG hMQ hMG hLQle hLGle hMQle hMGle
  exact hbody
    (A := |χ₀| * C₀ * L_Q) (B := L_G)
    (A' := |χ₀| * C₀ * M_Q) (B' := M_G)
    (by positivity) hLG (by positivity) hMG
    (by
      have : |χ₀| * C₀ * L_Q ≤ |χ₀| * C₀ * LQbar :=
        mul_le_mul_of_nonneg_left hLQle (by positivity)
      exact this)
    hLGle
    (by
      have : |χ₀| * C₀ * M_Q ≤ |χ₀| * C₀ * MQbar :=
        mul_le_mul_of_nonneg_left hMQle (by positivity)
      exact this)
    hMGle

end ShenWork.EWA

#print axioms ShenWork.EWA.exists_uniform_small_two_conditions
#print axioms ShenWork.EWA.exists_uniform_EWA_lifespan
