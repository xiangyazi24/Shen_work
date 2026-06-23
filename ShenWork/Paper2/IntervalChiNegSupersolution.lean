/-
  # χ₀<0: the supersolution H^σ residual `hEhatH` — TWO-WAY AUDIT RESULT.

  The single remaining residual of the χ₀<0 UNCONDITIONAL route
  (`trajEnvelope_chiNeg_gw`, IntervalChiNegGwInvariance.lean) is
  `hEhatH : MemHSigma σ (gwInflatedBase E Gden)` where (for `k ≥ 1`)

      gwInflatedBase E Gden k = trueCosProd (gW E Gden) (sineEnv E) k · (1+λ_k)/√λ_k .

  The supersolution construction in `/tmp/shen_super.md` claims the outer
  multiplier `(1+λ_k)/√λ_k` "re-inflates" the `√λ/(1+λ)` deflation of `sineEnv E`,
  leaving the product at the H^σ scale (no derivative loss).  **This is FALSE.**

  `trueCosProd` is a genuine CONVOLUTION (Cauchy/correlation sums, `cosProd =
  ½(addConv + diffConv)`, `corr1 a b k = Σ' n, a (n+k) b n`).  The `sineEnv E`
  deflation `√λ/(1+λ)` lives at the INNER summation index; the inflation
  `(1+λ_k)/√λ_k` lives at the OUTPUT index `k`.  In a convolution these are
  DIFFERENT indices, so they do NOT cancel.

  This file proves the obstruction RIGOROUSLY and axiom-clean:

  * `gwInflatedBase_weight_lower` — the SHARP per-mode lower bound
    `(1+λ_k)^{σ+1}·(flux k)² ≤ (1+λ_k)^σ·(gwInflatedBase k)²` for `k ≥ 1`,
    because `((1+λ_k)/√λ_k)² = (1+λ_k)²/λ_k ≥ (1+λ_k)`.  The output multiplier
    costs EXACTLY ONE FULL derivative of H^σ energy (two-sided `Θ(1+λ_k)`).

  * `memHSigma_flux_succ_of_hEhatH` — the DECISIVE obstruction:
    `MemHSigma σ (gwInflatedBase E Gden) → MemHSigma (σ+1) (flux convolution)`.
    Closing `hEhatH` at H^σ would FORCE the convolution
    `trueCosProd (gW E Gden) (sineEnv E)` to live a FULL derivative higher.

  The only landed product estimate (`memHSigma_trueCosProd_of_gt_half`, σ>1/2)
  delivers the convolution at H^σ; the Duhamel heat-smoothing engine
  (`chemDuhamel_memHSigma_succ`) gains only `α < 1` derivatives.  Neither supplies
  the full `+1` derivative.  Hence `hEhatH` is NOT provable at the H^σ scale of
  the flux factors `E, Gden, sineEnv E` — this is the genuine PDE crux.

  STATUS: PARTIAL/STALL on `hEhatH`.  The obstruction (full-derivative loss) is
  DERIVED and verified here.  No `sorry`/`admit`/`native_decide`/custom axiom.
-/
import ShenWork.Paper2.IntervalChiNegGwInvariance

open scoped Topology NNReal

noncomputable section

open Real Set
open ShenWork.Paper2.HSigmaScale (lam lam_nonneg one_add_lam_pos MemHSigma)
open ShenWork.Paper2.IntervalFluxFactorEnvelope (sineEnv)
open ShenWork.Paper2.IntervalGWProductEnvelope (gW)
open ShenWork.Paper2.IntervalWienerAlgebra (trueCosProd memHSigma_congr_except)
open ShenWork.Paper2.IntervalChiNegGwInvariance (gwInflatedBase gwInflatedBase_zero)

namespace ShenWork.Paper2.IntervalChiNegSupersolution

/-! ## 1. The Neumann eigenvalue is strictly positive off mode `0`. -/

/-- `λ_k = (kπ)² > 0` for `k ≥ 1`. -/
theorem lam_pos_of_pos {k : ℕ} (hk : 0 < k) : 0 < lam k := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hpi : 0 < Real.pi := Real.pi_pos
  change 0 < unitIntervalCosineEigenvalue k
  unfold unitIntervalCosineEigenvalue
  have : 0 < (k : ℝ) * Real.pi := by positivity
  positivity

/-! ## 2. The SHARP full-derivative lower bound (the obstruction witness). -/

/-- **SHARP per-mode lower bound (k ≥ 1).**  The H^σ weight of `gwInflatedBase`
dominates the H^{σ+1} weight of the flux convolution, because the output
multiplier squared is `((1+λ_k)/√λ_k)² = (1+λ_k)²/λ_k ≥ (1+λ_k)`.  The inflation
costs EXACTLY ONE FULL derivative — it does NOT cancel `sineEnv`'s deflation
(which sits at the inner convolution index, not the output index `k`). -/
theorem gwInflatedBase_weight_lower {σ : ℝ} (E Gden : ℕ → ℝ) {k : ℕ} (hk : 0 < k) :
    (1 + lam k) ^ (σ + 1) * (trueCosProd (gW E Gden) (sineEnv E) k) ^ 2
      ≤ (1 + lam k) ^ σ * (gwInflatedBase E Gden k) ^ 2 := by
  have hkne : k ≠ 0 := hk.ne'
  have hlam : 0 < lam k := lam_pos_of_pos hk
  have h1l : 0 < 1 + lam k := one_add_lam_pos k
  set f := trueCosProd (gW E Gden) (sineEnv E) k with hf
  have hbase : gwInflatedBase E Gden k = f * ((1 + lam k) / Real.sqrt (lam k)) := by
    simp only [gwInflatedBase, if_neg hkne, hf]
  rw [hbase]
  have hsqrt : (Real.sqrt (lam k)) ^ 2 = lam k := Real.sq_sqrt hlam.le
  have hmulsq : ((1 + lam k) / Real.sqrt (lam k)) ^ 2 = (1 + lam k) ^ 2 / lam k := by
    rw [div_pow, hsqrt]
  have hgeq : (1 + lam k) ≤ (1 + lam k) ^ 2 / lam k := by
    rw [le_div_iff₀ hlam]; nlinarith [sq_nonneg (1 + lam k), h1l, hlam]
  have hrpow : (0 : ℝ) < (1 + lam k) ^ σ := Real.rpow_pos_of_pos h1l σ
  have hrpow1 : (1 + lam k) ^ (σ + 1) = (1 + lam k) ^ σ * (1 + lam k) := by
    rw [Real.rpow_add h1l, Real.rpow_one]
  rw [hrpow1, mul_pow, hmulsq]
  have hfac : (1 + lam k) * f ^ 2 ≤ f ^ 2 * ((1 + lam k) ^ 2 / lam k) := by
    nlinarith [mul_le_mul_of_nonneg_right hgeq (sq_nonneg f)]
  calc (1 + lam k) ^ σ * (1 + lam k) * f ^ 2
      = (1 + lam k) ^ σ * ((1 + lam k) * f ^ 2) := by ring
    _ ≤ (1 + lam k) ^ σ * (f ^ 2 * ((1 + lam k) ^ 2 / lam k)) :=
        mul_le_mul_of_nonneg_left hfac hrpow.le

/-! ## 3. The DECISIVE obstruction: `hEhatH` forces a FULL extra derivative. -/

/-- **THE OBSTRUCTION (DERIVED).**  If the residual `hEhatH : MemHSigma σ
(gwInflatedBase E Gden)` held, then the flux convolution
`trueCosProd (gW E Gden) (sineEnv E)` would lie in `H^{σ+1}` — a FULL derivative
above the H^σ Banach algebra that produces it.  The landed product estimate
`memHSigma_trueCosProd_of_gt_half` (σ>1/2) delivers only H^σ, and the Duhamel
heat-smoothing engine `chemDuhamel_memHSigma_succ` gains only `α<1` derivatives.
So `hEhatH` is NOT provable at the flux scale: the supersolution map `T` maps
H^σ OUT of H^σ.  This is the genuine PDE crux; `χ₀<0` is NOT closed by this route
at the H^σ scale of `E, Gden, sineEnv E`. -/
theorem memHSigma_flux_succ_of_hEhatH {σ : ℝ} {E Gden : ℕ → ℝ}
    (hEhatH : MemHSigma σ (gwInflatedBase E Gden)) :
    MemHSigma (σ + 1) (trueCosProd (gW E Gden) (sineEnv E)) := by
  -- The flux with mode 0 zeroed; dominated everywhere by the gwInflatedBase weight.
  set flux := trueCosProd (gW E Gden) (sineEnv E) with hflux
  set flux0 : ℕ → ℝ := fun k => if k = 0 then 0 else flux k with hflux0
  have hdom : MemHSigma (σ + 1) flux0 := by
    unfold MemHSigma
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hEhatH
    · have := one_add_lam_pos k; positivity
    · rcases Nat.eq_zero_or_pos k with hk0 | hk
      · simp [hflux0, hk0, gwInflatedBase_zero]
      · have hkne : k ≠ 0 := hk.ne'
        simp only [hflux0, if_neg hkne]
        exact gwInflatedBase_weight_lower E Gden hk
  -- flux and flux0 agree off mode 0, so H^{σ+1} membership transfers back.
  exact memHSigma_congr_except 0 (fun k hk => by simp [hflux0, hk]) hdom

/-! ## AxiomAudit -/

section AxiomAudit
#print axioms lam_pos_of_pos
#print axioms gwInflatedBase_weight_lower
#print axioms memHSigma_flux_succ_of_hEhatH
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegSupersolution
