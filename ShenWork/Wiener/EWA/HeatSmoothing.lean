import ShenWork.Wiener.EWA.SobolevEmbedding

/-!
  # Heat-semigroup smoothing `L² → H^θ` on cosine coefficients.

  This file supplies the first leg of the `A³` bootstrap seed: the heat
  semigroup `S(t)`, acting diagonally on cosine coefficients by
  `(S(t) f)_k = e^{-t λ_k} f_k`, maps `ℓ²` data into every fractional Sobolev
  space `H^θ` for `t > 0`.  The per-mode multiplier
  `(1+λ_k)^θ e^{-2 t λ_k}` is uniformly bounded by a finite constant `M`
  (`heat_smoothing_mode_sup`), because the polynomial growth `(1+x)^θ` is
  dominated by the exponential decay `e^{-2tx}` for every `t > 0`.  Hence the
  `H^θ` energy `Σ_k (1+λ_k)^θ (S(t) f)_k²` is bounded termwise by `M·(f_k)²`,
  which is summable from `ℓ²` membership of `f`.

  Composing with `memWNorm_of_memHSob` (`H^θ ↪ A⁰` for `θ > 1/2`) gives the
  full `L² → H^θ → A⁰` smoothing seed (`heat_L2_to_memWNorm`).

  Contents:
  * `MemL2`                    — `ℓ²` membership of a coefficient sequence.
  * `heatCoeff`                — the diagonal heat-semigroup action `S(t)`.
  * `heat_smoothing_mode_sup`  — the finite per-mode multiplier sup.
  * `heat_L2_to_memHSob`       — the smoothing `L² → H^θ`.
  * `heat_L2_to_memWNorm`      — the composed `L² → A⁰` seed (`θ > 1/2`).
-/

noncomputable section

open scoped BigOperators Topology
open Filter
open ShenWork.Paper2.HSigmaScale

namespace ShenWork.Wiener.EWA

/-- `ℓ²` membership: the squared coefficient series `Σ_k (a_k)²` converges. -/
def MemL2 (a : ℕ → ℝ) : Prop := Summable (fun k : ℕ => (a k) ^ 2)

/-- The heat semigroup `S(t)` acting diagonally on cosine coefficients:
`(S(t) f)_k = e^{-t λ_k} f_k`. -/
def heatCoeff (t : ℝ) (f : ℕ → ℝ) : ℕ → ℝ :=
  fun k => Real.exp (-(t * lam k)) * f k

/-- The per-mode heat multiplier `(1+x)^θ e^{-2tx}` is uniformly bounded over
`x ≥ 0` for every `t > 0`: polynomial growth is dominated by exponential decay.
We exhibit a finite `M` with `0 ≤ M`. -/
theorem heat_smoothing_mode_sup {θ t : ℝ} (hθ : 0 ≤ θ) (ht : 0 < t) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ x : ℝ, 0 ≤ x → (1 + x) ^ θ * Real.exp (-(2 * t * x)) ≤ M := by
  classical
  -- The smoothing profile `g x = (1+x)^θ e^{-2tx}`, continuous on `ℝ`.
  set g : ℝ → ℝ := fun x => (1 + x) ^ θ * Real.exp (-(2 * t * x)) with hg
  have hgcont : Continuous g := by
    have h1 : Continuous (fun x : ℝ => (1 + x) ^ θ) :=
      (Real.continuous_rpow_const hθ).comp (continuous_const.add continuous_id)
    have h2 : Continuous (fun x : ℝ => Real.exp (-(2 * t * x))) :=
      Real.continuous_exp.comp (by continuity)
    exact h1.mul h2
  -- `g x → 0` as `x → +∞`, via the standard `rpow·exp` decay after the shift `u = 1+x`.
  have hbpos : (0 : ℝ) < 2 * t := by linarith
  have hdecay : Tendsto (fun u : ℝ => u ^ θ * Real.exp (-(2 * t) * u)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero θ (2 * t) hbpos
  -- Shift `x ↦ x + 1` tends to `atTop`, so the composite decays too.
  have hshift : Tendsto (fun x : ℝ => x + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_id
  have hcomp :
      Tendsto (fun x : ℝ => (x + 1) ^ θ * Real.exp (-(2 * t) * (x + 1))) atTop (𝓝 0) :=
    hdecay.comp hshift
  -- `g x = e^{2t} · (x+1)^θ e^{-2t(x+1)}`, so `g → e^{2t}·0 = 0`.
  have hglim : Tendsto g atTop (𝓝 0) := by
    have hscaled :
        Tendsto (fun x : ℝ => Real.exp (2 * t) *
            ((x + 1) ^ θ * Real.exp (-(2 * t) * (x + 1)))) atTop (𝓝 (Real.exp (2 * t) * 0)) :=
      hcomp.const_mul (Real.exp (2 * t))
    rw [mul_zero] at hscaled
    refine hscaled.congr (fun x => ?_)
    simp only [hg]
    rw [show (1 + x) = (x + 1) by ring, mul_left_comm, ← Real.exp_add]
    congr 1
    ring
  -- Eventually `g x ≤ 1`; pick a threshold `N` past which the bound holds.
  have hev : ∀ᶠ x in atTop, g x ≤ 1 := by
    have := hglim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
    exact this
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hev)
  -- On the compact slice `[0, max N 0]`, `g` is bounded above.
  set b : ℝ := max N 0 with hb
  have hcompact : IsCompact (Set.Icc (0 : ℝ) b) := isCompact_Icc
  have hbdd : BddAbove (g '' Set.Icc (0 : ℝ) b) :=
    hcompact.bddAbove_image hgcont.continuousOn
  obtain ⟨C, hC⟩ := hbdd
  -- `M = max C 1` dominates both the compact part and the tail.
  refine ⟨max C 1, le_trans zero_le_one (le_max_right _ _), fun x hx => ?_⟩
  by_cases hxb : x ≤ b
  · -- Compact part: `g x ≤ C ≤ max C 1`.
    have hmem : g x ∈ g '' Set.Icc (0 : ℝ) b :=
      ⟨x, ⟨hx, hxb⟩, rfl⟩
    exact le_trans (hC hmem) (le_max_left _ _)
  · -- Tail part: `x > b ≥ N`, so `g x ≤ 1 ≤ max C 1`.
    have hxN : N ≤ x := le_trans (le_max_left N 0) (le_of_lt (lt_of_not_ge hxb))
    exact le_trans (hN x hxN) (le_max_right _ _)

/-- Heat smoothing `L² → H^θ`: for `t > 0` and `θ ≥ 0`, if `f ∈ ℓ²` then the
heat-smoothed coefficients `S(t) f` lie in the fractional Sobolev space `H^θ`.
The `H^θ` energy term is `(1+λ_k)^θ e^{-2 t λ_k} (f_k)² ≤ M·(f_k)²`, summable. -/
theorem heat_L2_to_memHSob {θ t : ℝ} (hθ : 0 ≤ θ) (ht : 0 < t) {f : ℕ → ℝ}
    (hf : MemL2 f) : MemHSob θ (heatCoeff t f) := by
  classical
  obtain ⟨M, hM0, hMbd⟩ := heat_smoothing_mode_sup hθ ht
  -- The comparison series `M · (f_k)²` is summable from `ℓ²`.
  have hdom : Summable (fun k : ℕ => M * (f k) ^ 2) := hf.mul_left M
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hdom
  · -- Termwise nonnegativity of the `H^θ` energy.
    have hw : (0 : ℝ) ≤ (1 + lam k) ^ θ := Real.rpow_nonneg (one_add_lam_pos k).le _
    positivity
  · -- Termwise bound `(1+λ_k)^θ (S(t)f)_k² ≤ M (f_k)²`.
    have hlam : (0 : ℝ) ≤ lam k := lam_nonneg k
    -- `(S(t)f)_k² = e^{-2 t λ_k} (f_k)²`.
    have hsq : (heatCoeff t f k) ^ 2 = Real.exp (-(2 * t * lam k)) * (f k) ^ 2 := by
      rw [heatCoeff, mul_pow, ← Real.exp_nat_mul]
      congr 2
      · push_cast; ring
    rw [hsq]
    -- Regroup the weight and the exponential into the per-mode multiplier.
    have hmul := hMbd (lam k) hlam
    have hfsq : (0 : ℝ) ≤ (f k) ^ 2 := sq_nonneg _
    calc (1 + lam k) ^ θ * (Real.exp (-(2 * t * lam k)) * (f k) ^ 2)
        = ((1 + lam k) ^ θ * Real.exp (-(2 * t * lam k))) * (f k) ^ 2 := by ring
      _ ≤ M * (f k) ^ 2 := by
            exact mul_le_mul_of_nonneg_right hmul hfsq

/-- The full `L² → A⁰` heat-smoothing seed: for `t > 0` and `θ > 1/2`, `ℓ²`
data is smoothed by `S(t)` into the Wiener algebra `A⁰ = MemWNorm 0`.
Composition of `heat_L2_to_memHSob` (`L² → H^θ`) with `memWNorm_of_memHSob`
(`H^θ ↪ A⁰`, needing `0 + 1/2 < θ`). -/
theorem heat_L2_to_memWNorm {θ t : ℝ} (hθ : (1 / 2 : ℝ) < θ) (ht : 0 < t) {f : ℕ → ℝ}
    (hf : MemL2 f) : MemWNorm 0 (heatCoeff t f) := by
  have hθ0 : (0 : ℝ) ≤ θ := le_of_lt (lt_trans (by norm_num) hθ)
  have hsob : MemHSob θ (heatCoeff t f) := heat_L2_to_memHSob hθ0 ht hf
  exact memWNorm_of_memHSob (by linarith) hsob

end ShenWork.Wiener.EWA
