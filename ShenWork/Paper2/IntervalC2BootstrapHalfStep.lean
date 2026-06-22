import ShenWork.Paper2.IntervalBFormHSigmaDuhamelEnergy

/-!
# `IntervalC2Bootstrap` — the higher-rung (shifted) `H^r → H^{r+α}` divergence-Duhamel half-step

This file lands the genuine **iterable** linear engine rung of the parabolic
`C²`-regularity bootstrap for the gradient mild solution
`u(t)=S(t)u₀ − χ₀∫₀ᵗ∂ₓS(t−s)Q(u(s))ds + ∫₀ᵗS(t−s)L(u(s))ds`.

The landed `hSigmaEnergy_duhamel_bound` is the **base rung** `r = 0`: it maps an
`L∞_t ℓ²_x` *source envelope* into `H^α` (`α < 1`) output.  To iterate the
`σ`-ladder `H^0 → H^{1/2} → H^1 → …` one needs the **shifted** rung

    (source per-mode time-sup envelope `Msup` with `(1+λ_k)^{r/2}·Msup k ∈ ℓ²`,
     i.e. the source already in `H^r`)
        ⟹  the divergence-Duhamel coefficients lie in `H^{r+α}` (`α < 1`),

with the same smoothing constant and the `s^{(1−α)/2}` rate.  This is exactly the
`hSigmaEnergy_duhamel_heat_bound_shifted` rung.

The proof weights the landed per-mode square bound `hSigma_mode_sq_bound`
(`(1+λ_k)^α B_k² ≤ C² R² (Msup k)²`) by `(1+λ_k)^r`, turning it into
`(1+λ_k)^{r+α} B_k² ≤ C² R² · ((1+λ_k)^{r/2} Msup k)²`, then dominates by the
`H^r`-weighted source envelope.

This is the KEY BRICK (half-step #2): a single, fully axiom-clean, iterable
`H^r → H^{r+α}` divergence-Duhamel energy gain.  It uses ONLY the heat kernel
(the landed multiplier/per-mode estimates) + the source's `H^r` envelope — no
source-package, no resolver-`C²`/FAC field.  The remaining (genuinely missing)
content to close the full ladder to `H^{5/2}⊂C²` is the NONLINEAR source-regularity
estimate `Q,L : H^r → H^r` (Moser/product in the cosine scale) and the spectral
`MemHSigma → ContDiffOn ℝ 2` reconstruction bridge — neither is in the repo; see
the report.

No `sorry`, no `axiom`, no `native_decide`, no `admit`.
-/

noncomputable section

namespace ShenWork.IntervalC2Bootstrap

open ShenWork.Paper2.BFormHSigmaDuhamelEnergy
open ShenWork.Paper2.BFormHSigmaLinftyMultiplier
open ShenWork.Paper2.HSigmaScale
open Real

/-- The `H^r`-weighted per-mode source envelope: `(1+λ_k)^{r/2}·Msup k`.  Its
square is the `H^r`-energy summand of the envelope, so its `ℓ²`-summability is
exactly "the source envelope lies in `H^r`". -/
def weightedEnvelope (r : ℝ) (Msup : ℕ → ℝ) (k : ℕ) : ℝ :=
  (1 + lam k) ^ (r / 2) * Msup k

theorem weightedEnvelope_nonneg {r : ℝ} {Msup : ℕ → ℝ}
    (hMsup0 : ∀ k, 0 ≤ Msup k) (k : ℕ) : 0 ≤ weightedEnvelope r Msup k := by
  unfold weightedEnvelope
  have := Real.rpow_nonneg (one_add_lam_pos k).le (r / 2)
  have := hMsup0 k; positivity

/-- The square of the `H^r`-weighted envelope equals `(1+λ_k)^r · (Msup k)²`. -/
theorem weightedEnvelope_sq (r : ℝ) (Msup : ℕ → ℝ) (k : ℕ) :
    (weightedEnvelope r Msup k) ^ 2 = (1 + lam k) ^ r * (Msup k) ^ 2 := by
  unfold weightedEnvelope
  rw [mul_pow, ← Real.rpow_natCast ((1 + lam k) ^ (r / 2)) 2,
    ← Real.rpow_mul (one_add_lam_pos k).le]
  norm_num

/-- **Per-mode shifted square bound.**  Weighting the landed base square bound
`hSigma_mode_sq_bound` (at level `α`) by `(1+λ_k)^r` yields the `H^{r+α}` summand
controlled by the `H^r`-weighted envelope square. -/
theorem hSigma_mode_sq_bound_shifted {r α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    {d : ℝ} (hd : 0 < d) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {F : ℕ → ℝ → ℝ} (hFcont : ∀ k, Continuous (F k))
    {Msup : ℕ → ℝ} (hMsup0 : ∀ k, 0 ≤ Msup k)
    (hFbd : ∀ k, ∀ τ ∈ Set.Icc (0 : ℝ) s, |F k τ| ≤ Msup k) (k : ℕ) :
    (1 + lam k) ^ (r + α) * (duhamelEnergyCoeff d F s k) ^ 2 ≤
      (Classical.choose (linfty_multiplier_bound hα0 hα1 d hd)) ^ 2
        * (s ^ ((1 - α)/2) / ((1 - α)/2)) ^ 2
        * (weightedEnvelope r Msup k) ^ 2 := by
  have hbase := hSigma_mode_sq_bound hα0 hα1 hd hs hs1 hFcont hMsup0 hFbd k
  set C := Classical.choose (linfty_multiplier_bound hα0 hα1 d hd) with hCdef
  set R := s ^ ((1 - α)/2) / ((1 - α)/2) with hRdef
  set w : ℝ := (1 + lam k) ^ r with hwdef
  have hw0 : 0 ≤ w := Real.rpow_nonneg (one_add_lam_pos k).le r
  -- multiply the base bound by w ≥ 0
  have hmul : w * ((1 + lam k) ^ α * (duhamelEnergyCoeff d F s k) ^ 2)
      ≤ w * (C ^ 2 * R ^ 2 * (Msup k) ^ 2) :=
    mul_le_mul_of_nonneg_left hbase hw0
  -- LHS: w * (1+λ)^α = (1+λ)^{r+α}
  have hLHS : w * ((1 + lam k) ^ α * (duhamelEnergyCoeff d F s k) ^ 2)
      = (1 + lam k) ^ (r + α) * (duhamelEnergyCoeff d F s k) ^ 2 := by
    rw [hwdef, ← mul_assoc, ← Real.rpow_add (one_add_lam_pos k)]
  -- RHS: w * (C²R²Msup²) = C²R² * ((1+λ)^r Msup²) = C²R² * weightedEnvelope²
  have hRHS : w * (C ^ 2 * R ^ 2 * (Msup k) ^ 2)
      = C ^ 2 * R ^ 2 * (weightedEnvelope r Msup k) ^ 2 := by
    rw [weightedEnvelope_sq, hwdef]; ring
  rw [hLHS, hRHS] at hmul
  exact hmul

/-- **THE KEY BRICK — shifted (`H^r → H^{r+α}`) divergence-Duhamel energy bound.**

If the source's per-mode time-sup envelope `Msup` lies in `H^r`
(`Summable (fun k => (1+λ_k)^r (Msup k)²)`, equivalently the weighted envelope is
`ℓ²`), then for `0 ≤ α < 1`, `d > 0`, `0 < s ≤ 1` the divergence-Duhamel
coefficients lie in `H^{r+α}`, with

    hSigmaEnergy (r+α) (duhamelEnergyCoeff d F s)
      ≤ C_α² · (s^{(1−α)/2}/((1−α)/2))² · Σ_k (1+λ_k)^r (Msup k)².

This is the genuinely iterable engine rung: starting from a source already in
`H^r`, the divergence-Duhamel term gains `α < 1` derivatives.  Axiom-clean. -/
theorem hSigmaEnergy_duhamel_bound_shifted {r α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    {d : ℝ} (hd : 0 < d) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {F : ℕ → ℝ → ℝ} (hFcont : ∀ k, Continuous (F k))
    {Msup : ℕ → ℝ} (hMsup0 : ∀ k, 0 ≤ Msup k)
    (hFbd : ∀ k, ∀ τ ∈ Set.Icc (0 : ℝ) s, |F k τ| ≤ Msup k)
    (hMsq : Summable fun k => (1 + lam k) ^ r * (Msup k) ^ 2) :
    MemHSigma (r + α) (duhamelEnergyCoeff d F s) ∧
      hSigmaEnergy (r + α) (duhamelEnergyCoeff d F s) ≤
        (Classical.choose (linfty_multiplier_bound hα0 hα1 d hd)) ^ 2
          * (s ^ ((1 - α)/2) / ((1 - α)/2)) ^ 2
          * ∑' k, (1 + lam k) ^ r * (Msup k) ^ 2 := by
  set C := Classical.choose (linfty_multiplier_bound hα0 hα1 d hd) with hCdef
  set R := s ^ ((1 - α)/2) / ((1 - α)/2) with hRdef
  set K := C ^ 2 * R ^ 2 with hKdef
  -- envelope-square summability ⇔ weighted-envelope ℓ²
  have hWsq : Summable fun k => (weightedEnvelope r Msup k) ^ 2 := by
    refine (summable_congr ?_).mpr hMsq
    intro k; exact weightedEnvelope_sq r Msup k
  -- per-mode domination by K · weightedEnvelope²
  have hdom : ∀ k, (1 + lam k) ^ (r + α) * (duhamelEnergyCoeff d F s k) ^ 2
      ≤ K * (weightedEnvelope r Msup k) ^ 2 := by
    intro k
    have := hSigma_mode_sq_bound_shifted (r := r) hα0 hα1 hd hs hs1 hFcont hMsup0 hFbd k
    rwa [← hKdef] at this
  have hnonneg : ∀ k, 0 ≤ (1 + lam k) ^ (r + α) * (duhamelEnergyCoeff d F s k) ^ 2 := by
    intro k
    have := Real.rpow_nonneg (one_add_lam_pos k).le (r + α); positivity
  have hKW : Summable fun k => K * (weightedEnvelope r Msup k) ^ 2 := hWsq.mul_left K
  have hmem : MemHSigma (r + α) (duhamelEnergyCoeff d F s) :=
    Summable.of_nonneg_of_le hnonneg hdom hKW
  refine ⟨hmem, ?_⟩
  unfold hSigmaEnergy
  calc ∑' k, (1 + lam k) ^ (r + α) * (duhamelEnergyCoeff d F s k) ^ 2
      ≤ ∑' k, K * (weightedEnvelope r Msup k) ^ 2 := hmem.tsum_le_tsum hdom hKW
    _ = K * ∑' k, (weightedEnvelope r Msup k) ^ 2 := hWsq.tsum_mul_left K
    _ = K * ∑' k, (1 + lam k) ^ r * (Msup k) ^ 2 := by
        congr 1; exact tsum_congr (fun k => weightedEnvelope_sq r Msup k)
    _ = C ^ 2 * R ^ 2 * ∑' k, (1 + lam k) ^ r * (Msup k) ^ 2 := by rw [hKdef]

end ShenWork.IntervalC2Bootstrap

open ShenWork.IntervalC2Bootstrap in
#print axioms hSigma_mode_sq_bound_shifted
open ShenWork.IntervalC2Bootstrap in
#print axioms hSigmaEnergy_duhamel_bound_shifted
