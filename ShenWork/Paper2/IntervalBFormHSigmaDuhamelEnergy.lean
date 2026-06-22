import ShenWork.Paper2.IntervalBFormHSigmaDuhamelMode

/-!
  Brick 3 (operator level) — the `H^σ` energy bound for the divergence-Duhamel
  map, assembled from the landed per-mode bound `hSigma_mode_duhamel_bound`.

  Given a Neumann-cosine source `F : ℕ → ℝ → ℝ` with, for each mode `k`, a
  pointwise-in-time bound `|F k τ| ≤ Msup k` on `[0,s]`, the per-mode Duhamel
  coefficients `B_k(s) = duhamelModeCoeff d (lam k) (F k) s` satisfy

      hSigmaEnergy σ (fun k => B_k s)
        = ∑_k (1+λ_k)^σ B_k(s)²
        ≤ C_σ² · R(s)² · ∑_k (Msup k)²,    R(s) = s^{(1−σ)/2}/((1−σ)/2),

  provided the per-mode sup bounds are `ℓ²`-summable (`Summable (Msup²)`).  This
  is the weighted-source operator estimate.  (The sharp `L∞_t L²_x` constant
  `M∞² = sup_τ ∑_k F_k(τ)²` would require the genuine `ℓ²`-Minkowski
  integral-triangle; the `∑_k (Msup k)²` form proved here is the clean,
  fully-scalar consequence of the per-mode bound and is what the chemotaxis
  flux bootstrap consumes when the source's per-mode sup envelope is `ℓ²`.)

  Axiom-clean: only the landed per-mode scalar bound + `tsum` algebra.
-/

noncomputable section

namespace ShenWork.Paper2.BFormHSigmaDuhamelEnergy

open ShenWork.Paper2.BFormHSigmaDuhamelMode
open ShenWork.Paper2.BFormHSigmaLinftyMultiplier
open ShenWork.Paper2.HSigmaScale
open Real

/-- The Duhamel-map spectral coefficients `B_k(s)` for a multi-mode source. -/
def duhamelEnergyCoeff (d : ℝ) (F : ℕ → ℝ → ℝ) (s : ℝ) (k : ℕ) : ℝ :=
  duhamelModeCoeff d (lam k) (F k) s

/-- Per-mode squared `H^σ`-weight bound: `(1+λ_k)^σ B_k(s)² ≤ C² R(s)² (Msup k)²`.
Obtained by squaring the per-mode `hSigma_mode_duhamel_bound`. -/
theorem hSigma_mode_sq_bound {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    {d : ℝ} (hd : 0 < d) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {F : ℕ → ℝ → ℝ} (hFcont : ∀ k, Continuous (F k))
    {Msup : ℕ → ℝ} (hMsup0 : ∀ k, 0 ≤ Msup k)
    (hFbd : ∀ k, ∀ τ ∈ Set.Icc (0:ℝ) s, |F k τ| ≤ Msup k) (k : ℕ) :
    (1 + lam k) ^ σ * (duhamelEnergyCoeff d F s k) ^ 2 ≤
      (Classical.choose (linfty_multiplier_bound hσ0 hσ1 d hd)) ^ 2
        * (s ^ ((1 - σ)/2) / ((1 - σ)/2)) ^ 2 * (Msup k) ^ 2 := by
  set C := Classical.choose (linfty_multiplier_bound hσ0 hσ1 d hd) with hCdef
  have hCpos := (Classical.choose_spec (linfty_multiplier_bound hσ0 hσ1 d hd)).1
  -- per-mode bound on the weighted absolute coefficient
  have hbound := hSigma_mode_duhamel_bound hσ0 hσ1 hd hs hs1 (lam_nonneg k)
    (hFcont k) (hMsup0 k) (hFbd k)
  -- hbound : (1+λ_k)^{σ/2} * |B_k| ≤ C * Msup k * R(s)
  set B := duhamelEnergyCoeff d F s k with hBdef
  set R := s ^ ((1 - σ)/2) / ((1 - σ)/2) with hRdef
  have hweight : (1 + lam k) ^ σ = ((1 + lam k) ^ (σ/2)) ^ 2 := by
    rw [← Real.rpow_natCast ((1 + lam k) ^ (σ/2)) 2, ← Real.rpow_mul (one_add_lam_pos k).le]
    norm_num
  -- LHS = ((1+λ)^{σ/2} * |B|)²
  have hLHS : (1 + lam k) ^ σ * B ^ 2 = ((1 + lam k) ^ (σ/2) * |B|) ^ 2 := by
    rw [hweight]; rw [mul_pow, sq_abs]
  rw [hLHS]
  -- nonneg of the weighted abs coeff and of the RHS factor
  have hnonneg : 0 ≤ (1 + lam k) ^ (σ/2) * |B| := by
    have := Real.rpow_nonneg (one_add_lam_pos k).le (σ/2); positivity
  have hRHSfac_nonneg : 0 ≤ C * Msup k * R := by
    have hRnonneg : 0 ≤ R := by
      rw [hRdef]
      apply div_nonneg (Real.rpow_nonneg hs.le _)
      linarith
    have := hMsup0 k; positivity
  -- square the inequality
  have hsq : ((1 + lam k) ^ (σ/2) * |B|) ^ 2 ≤ (C * Msup k * R) ^ 2 :=
    pow_le_pow_left₀ hnonneg hbound 2
  calc ((1 + lam k) ^ (σ/2) * |B|) ^ 2
      ≤ (C * Msup k * R) ^ 2 := hsq
    _ = C ^ 2 * R ^ 2 * (Msup k) ^ 2 := by ring

/-- **Operator-level `H^σ` energy bound for the divergence-Duhamel map.**

If the per-mode source sup envelope `Msup` is `ℓ²`-summable, then the Duhamel
coefficients lie in `H^σ`, and

    hSigmaEnergy σ (duhamelEnergyCoeff d F s)
        ≤ C_σ² · (s^{(1−σ)/2}/((1−σ)/2))² · ∑_k (Msup k)². -/
theorem hSigmaEnergy_duhamel_bound {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    {d : ℝ} (hd : 0 < d) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {F : ℕ → ℝ → ℝ} (hFcont : ∀ k, Continuous (F k))
    {Msup : ℕ → ℝ} (hMsup0 : ∀ k, 0 ≤ Msup k)
    (hFbd : ∀ k, ∀ τ ∈ Set.Icc (0:ℝ) s, |F k τ| ≤ Msup k)
    (hMsq : Summable fun k => (Msup k) ^ 2) :
    MemHSigma σ (duhamelEnergyCoeff d F s) ∧
      hSigmaEnergy σ (duhamelEnergyCoeff d F s) ≤
        (Classical.choose (linfty_multiplier_bound hσ0 hσ1 d hd)) ^ 2
          * (s ^ ((1 - σ)/2) / ((1 - σ)/2)) ^ 2
          * ∑' k, (Msup k) ^ 2 := by
  set C := Classical.choose (linfty_multiplier_bound hσ0 hσ1 d hd) with hCdef
  set R := s ^ ((1 - σ)/2) / ((1 - σ)/2) with hRdef
  set K := C ^ 2 * R ^ 2 with hKdef
  -- per-mode domination
  have hdom : ∀ k, (1 + lam k) ^ σ * (duhamelEnergyCoeff d F s k) ^ 2
      ≤ K * (Msup k) ^ 2 := by
    intro k
    have := hSigma_mode_sq_bound hσ0 hσ1 hd hs hs1 hFcont hMsup0 hFbd k
    rwa [← hKdef] at this
  have hnonneg : ∀ k, 0 ≤ (1 + lam k) ^ σ * (duhamelEnergyCoeff d F s k) ^ 2 := by
    intro k
    have := Real.rpow_nonneg (one_add_lam_pos k).le σ; positivity
  have hKMsq : Summable fun k => K * (Msup k) ^ 2 := hMsq.mul_left K
  have hmem : MemHSigma σ (duhamelEnergyCoeff d F s) :=
    Summable.of_nonneg_of_le hnonneg hdom hKMsq
  refine ⟨hmem, ?_⟩
  unfold hSigmaEnergy
  calc ∑' k, (1 + lam k) ^ σ * (duhamelEnergyCoeff d F s k) ^ 2
      ≤ ∑' k, K * (Msup k) ^ 2 := hmem.tsum_le_tsum hdom hKMsq
    _ = K * ∑' k, (Msup k) ^ 2 := hMsq.tsum_mul_left K
    _ = C ^ 2 * R ^ 2 * ∑' k, (Msup k) ^ 2 := by rw [hKdef]

#print axioms hSigma_mode_sq_bound
#print axioms hSigmaEnergy_duhamel_bound

end ShenWork.Paper2.BFormHSigmaDuhamelEnergy
