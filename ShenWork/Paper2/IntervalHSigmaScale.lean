import ShenWork.PDE.HeatSemigroup
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
  Brick 2 + Brick 4 of the two-step parabolic-smoothing bootstrap (Paper 2).

  * Brick 2: the fractional cosine Sobolev scale `H^σ` on the unit interval,
    `‖a‖²_{H^σ} = Σ_k (1+λ_k)^σ (a_k)²`, with `λ_k = (kπ)²`, together with the
    membership predicate (squared-`H^σ`-energy summable).

  * Brick 4: the elliptic resolver gains exactly two derivatives in the cosine
    scale.  For `v̂_k = ĝ_k / (μ + λ_k)`, the multiplier `(1+λ_k)/(μ+λ_k)` is
    uniformly bounded (by `max 1 (1/μ)`), so the `H^{σ+2}` energy of `v` is
    controlled by the `H^σ` energy of `g`.
-/

noncomputable section

namespace ShenWork.Paper2.HSigmaScale

/-- The Neumann cosine eigenvalue `λ_k = (kπ)²`, reused from `HeatSemigroup`. -/
abbrev lam (k : ℕ) : ℝ := unitIntervalCosineEigenvalue k

theorem lam_nonneg (k : ℕ) : 0 ≤ lam k := by
  unfold lam unitIntervalCosineEigenvalue; positivity

theorem one_add_lam_pos (k : ℕ) : 0 < 1 + lam k := by
  have := lam_nonneg k; linarith

/-- The fractional `H^σ` cosine energy: `Σ_k (1+λ_k)^σ (a_k)²`. -/
def hSigmaEnergy (σ : ℝ) (a : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, (1 + lam k) ^ σ * (a k) ^ 2

/-- Membership in the fractional cosine `H^σ`: the `H^σ` energy series is
summable (i.e. converges). -/
def MemHSigma (σ : ℝ) (a : ℕ → ℝ) : Prop :=
  Summable fun k : ℕ => (1 + lam k) ^ σ * (a k) ^ 2

theorem hSigmaEnergy_nonneg (σ : ℝ) (a : ℕ → ℝ) : 0 ≤ hSigmaEnergy σ a := by
  unfold hSigmaEnergy
  apply tsum_nonneg
  intro k
  have := one_add_lam_pos k
  positivity

/-- `σ ≤ 0`: `H^σ` membership is weaker than `L²` (here we record the simple
fact `MemHSigma 0 a ↔ Summable (a²)`). -/
theorem memHSigma_zero (a : ℕ → ℝ) :
    MemHSigma 0 a ↔ Summable fun k : ℕ => (a k) ^ 2 := by
  unfold MemHSigma
  constructor <;> intro h
  · refine h.congr ?_; intro k; simp [Real.rpow_zero]
  · refine h.congr ?_; intro k; simp [Real.rpow_zero]

/-! ## Brick 4: elliptic resolver `H^σ → H^{σ+2}` gain (coefficient form). -/

/-- The elliptic Neumann resolver coefficient (real, source form):
`v_k = g_k / (μ + λ_k)`. -/
def resolverCoeff (μ : ℝ) (g : ℕ → ℝ) (k : ℕ) : ℝ :=
  g k / (μ + lam k)

/-- Uniform bound on the elliptic multiplier `(1+λ_k)/(μ+λ_k)`.

For `μ > 0`: if `μ ≤ 1` then `(1+λ)/(μ+λ) ≤ 1/μ`; if `μ ≥ 1` then it is `≤ 1`.
A clean uniform bound is `max 1 (1/μ)`. -/
theorem elliptic_multiplier_le {μ : ℝ} (hμ : 0 < μ) (k : ℕ) :
    (1 + lam k) / (μ + lam k) ≤ max 1 (1 / μ) := by
  have hlamk := lam_nonneg k
  have hden : 0 < μ + lam k := by linarith
  rcases le_or_gt 1 μ with hμ1 | hμ1
  · -- μ ≥ 1 : numerator ≤ denominator, quotient ≤ 1 ≤ max.
    have hle : 1 + lam k ≤ μ + lam k := by linarith
    have : (1 + lam k) / (μ + lam k) ≤ 1 :=
      (div_le_one hden).2 hle
    exact le_trans this (le_max_left _ _)
  · -- μ < 1 : (1+λ)/(μ+λ) ≤ 1/μ since μ(1+λ) ≤ (μ+λ).
    have hμpos : 0 < μ := hμ
    have hkey : μ * (1 + lam k) ≤ μ + lam k := by nlinarith [hlamk, hμ1.le, hμpos]
    have hquot : (1 + lam k) / (μ + lam k) ≤ 1 / μ := by
      rw [div_le_div_iff₀ hden hμpos]
      nlinarith [hkey]
    exact le_trans hquot (le_max_right _ _)

/-- Per-mode `H^{σ+2}` weight bound for the resolver: the `(σ+2)`-weighted
square of `v_k` is bounded by `(max 1 (1/μ))² · (1+λ_k)^σ (g_k)²`.

Uses `(1+λ_k)^{σ+2} = (1+λ_k)^σ · (1+λ_k)²` and the multiplier bound. -/
theorem resolver_hSigmaPlus2_mode_le {μ σ : ℝ} (hμ : 0 < μ) (g : ℕ → ℝ) (k : ℕ) :
    (1 + lam k) ^ (σ + 2) * (resolverCoeff μ g k) ^ 2 ≤
      (max 1 (1 / μ)) ^ 2 * ((1 + lam k) ^ σ * (g k) ^ 2) := by
  have hlamk := lam_nonneg k
  have h1pos := one_add_lam_pos k
  have hden : 0 < μ + lam k := by linarith
  have hM : (0 : ℝ) ≤ max 1 (1 / μ) := le_trans zero_le_one (le_max_left _ _)
  -- rewrite (1+λ)^{σ+2} = (1+λ)^σ * (1+λ)^2
  have hpow : (1 + lam k) ^ (σ + 2) = (1 + lam k) ^ σ * (1 + lam k) ^ (2 : ℝ) := by
    rw [← Real.rpow_add h1pos]
  have hsq : (1 + lam k) ^ (2 : ℝ) = (1 + lam k) ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  -- v_k^2 = g_k^2 / (μ+λ)^2
  have hv2 : (resolverCoeff μ g k) ^ 2 = (g k) ^ 2 / (μ + lam k) ^ 2 := by
    unfold resolverCoeff; rw [div_pow]
  rw [hpow, hsq, hv2]
  -- Goal: (1+λ)^σ * (1+λ)^2 * (g^2/(μ+λ)^2) ≤ M^2 * ((1+λ)^σ * g^2)
  -- Group: = (1+λ)^σ g^2 * ((1+λ)/(μ+λ))^2 ≤ (1+λ)^σ g^2 * M^2.
  have hmult := elliptic_multiplier_le hμ k
  have hmultsq : ((1 + lam k) / (μ + lam k)) ^ 2 ≤ (max 1 (1 / μ)) ^ 2 := by
    have hquot_nonneg : 0 ≤ (1 + lam k) / (μ + lam k) :=
      div_nonneg h1pos.le hden.le
    exact pow_le_pow_left₀ hquot_nonneg hmult 2
  have hcoef_nonneg : 0 ≤ (1 + lam k) ^ σ * (g k) ^ 2 := by
    have := Real.rpow_nonneg h1pos.le σ; positivity
  have hratio_sq : (1 + lam k) ^ 2 * ((g k) ^ 2 / (μ + lam k) ^ 2)
      = (g k) ^ 2 * ((1 + lam k) / (μ + lam k)) ^ 2 := by
    rw [div_pow]; field_simp
  calc
    (1 + lam k) ^ σ * (1 + lam k) ^ 2 * ((g k) ^ 2 / (μ + lam k) ^ 2)
        = ((1 + lam k) ^ σ * (g k) ^ 2) * ((1 + lam k) / (μ + lam k)) ^ 2 := by
          rw [mul_assoc, hratio_sq]; ring
    _ ≤ ((1 + lam k) ^ σ * (g k) ^ 2) * (max 1 (1 / μ)) ^ 2 :=
          mul_le_mul_of_nonneg_left hmultsq hcoef_nonneg
    _ = (max 1 (1 / μ)) ^ 2 * ((1 + lam k) ^ σ * (g k) ^ 2) := by ring

/-- **Brick 4: elliptic `H^σ → H^{σ+2}` gain.**  If the source `g ∈ H^σ`, then
the resolver `v_k = g_k/(μ+λ_k)` lies in `H^{σ+2}`, and the `H^{σ+2}` energy is
bounded by `(max 1 (1/μ))²` times the `H^σ` energy of `g`. -/
theorem resolver_memHSigmaPlus2_of_memHSigma {μ σ : ℝ} (hμ : 0 < μ) {g : ℕ → ℝ}
    (hg : MemHSigma σ g) :
    MemHSigma (σ + 2) (resolverCoeff μ g) ∧
      hSigmaEnergy (σ + 2) (resolverCoeff μ g) ≤
        (max 1 (1 / μ)) ^ 2 * hSigmaEnergy σ g := by
  have hnonneg : ∀ k, 0 ≤ (1 + lam k) ^ (σ + 2) * (resolverCoeff μ g k) ^ 2 := by
    intro k
    have := Real.rpow_nonneg (one_add_lam_pos k).le (σ + 2); positivity
  have hdom : ∀ k, (1 + lam k) ^ (σ + 2) * (resolverCoeff μ g k) ^ 2 ≤
      (max 1 (1 / μ)) ^ 2 * ((1 + lam k) ^ σ * (g k) ^ 2) :=
    fun k => resolver_hSigmaPlus2_mode_le hμ g k
  have hsummable : MemHSigma (σ + 2) (resolverCoeff μ g) :=
    Summable.of_nonneg_of_le hnonneg hdom (hg.mul_left _)
  refine ⟨hsummable, ?_⟩
  unfold hSigmaEnergy
  calc
    ∑' k, (1 + lam k) ^ (σ + 2) * (resolverCoeff μ g k) ^ 2
        ≤ ∑' k, (max 1 (1 / μ)) ^ 2 * ((1 + lam k) ^ σ * (g k) ^ 2) :=
          hsummable.tsum_le_tsum hdom (hg.mul_left _)
    _ = (max 1 (1 / μ)) ^ 2 * ∑' k, (1 + lam k) ^ σ * (g k) ^ 2 :=
          (Summable.tsum_mul_left _ hg)

#print axioms hSigmaEnergy_nonneg
#print axioms memHSigma_zero
#print axioms elliptic_multiplier_le
#print axioms resolver_memHSigmaPlus2_of_memHSigma

end ShenWork.Paper2.HSigmaScale
