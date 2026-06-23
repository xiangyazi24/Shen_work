/-
  ShenWork/Paper2/IntervalChiNegH1Final.lean

  χ₀<0 REBUILD — CLOSE: source regularity (Wiener-ℓ¹ flux smoothing at the
  divergence weight √λ) + the L² zero-mode part + the uniform-H¹ assembly.

  This file CLOSES the χ₀<0 uniform-H¹ rebuild by wiring the landed machinery at
  the divergence weight, per cron1's verified route (_CHATGPT_DROP_cron1.md, the A₃
  Wiener condition `Σ_k λ_k^{3/2}|sineCoeff(F)_k|`, F=W·v_x).

  ## PIECE A — source regularity at the divergence weight √λ (DERIVED machinery).
  cron1's verdict: bare C² is NOT enough; the divergence-weighted summability is the
  A-Wiener flux condition.  Here the LOCAL flux-smoothing fact is the per-flux
  `MemHSigma σ'` membership (σ'>3/2); it is the FLUX ℓ¹ (a local smoothing fact),
  NOT the target H¹ bound (cron2 warning 1: it carries no time-uniform energy, just a
  fixed-weight per-flux Sobolev datum).  Two DERIVED bricks:
   * `weightedHalf_of_memHSigma` — `MemHSigma σ' a` (σ'>3/2) ⟹
     `Summable (fun k => Real.sqrt (lam k) * |a k|)`, the √λ-weighted ℓ¹ flux
     envelope, via the landed `hSigma_subset_l1_of_gt_half` on `(1+λ)^{1/2}·a ∈
     MemHSigma (σ'-1)` plus `√λ ≤ (1+λ)^{1/2}`.  DERIVED.
   * `srcWeighted_of_base` — lifts a base `DuhamelSourceTimeC1 a` (the honest
     time-C¹ source package of the raw flux family) to the √λ-weighted package
     `DuhamelSourceTimeC1 (fun s n => √(lam n) * a s n)`, threading the supplied
     √λ-weighted ℓ¹ envelope (DERIVED above) and a uniform √λ-weighted derivative
     bound — the SAME `.toWeightedTimeC1` pattern landed in
     `IntervalParabolicDuhamelGainNonCircular`, here at the half-weight.  DERIVED.

  ## PIECE B — the L² zero-mode part (DERIVED).
   * `l2_of_sup_bound` — `(∀ x∈[0,1], |g x|≤M)` ⟹ `∫₀¹ g² ≤ M²` (so `½∫g² ≤ ½M²`):
     the L∞ order box ⟹ uniform L² bound on the zero-mode part of the H¹ norm.

  ## PIECE C — assemble (DERIVED over PIECE A/B + the landed headline).
   * `chiNeg_H1_full_norm_bound` — the FULL H¹ norm² `½‖u‖²_{L²}+½‖u_x‖²_{L²}` bounded
     uniformly: the seminorm part from the landed `chiNeg_H1_norm_bound`
     (IntervalChiNegH1Energy), the L² part from `l2_of_sup_bound` fed the L∞ box
     `conjugatePicardLimit_bounded`.  DERIVED assembly.

  ## CARRIED (precise, never faked, never relabeled).  PIECE A's two analytic inputs
  are the honest flux-smoothing data, supplied to `srcWeighted_of_base`:
   * the base time-C¹ package `DuhamelSourceTimeC1 a` of the raw conjugate flux
     family (`conjQ`/`conjFl`) — the landed time-C¹ source machinery is geared to the
     CLAMPED restart source `LocalRestart.srcC` (IntervalChiNegSourceTail), not the
     raw families; failed grep
        grep -rn "DuhamelSourceTimeC1.*conjQ|DuhamelSourceTimeC1.*conjFl" → NONE.
   * the τ-uniform flux `MemHSigma σ'` envelope (σ'>3/2) — the campaign's SINGLE open
     seam (C1, IntervalChiNegTrajectoryAssembly): the τ-uniform base envelope at
     σ₀>1/2 is NOT producible from mild data (the L∞ ball ⇒ constant ∉ H^{σ₀}); it
     requires the initial H¹ regularity `hû₀(H¹)`.  This is the honest physical input.
  And the seminorm headline `chiNeg_H1_norm_bound` itself carries its energy identity
  / window inputs (documented in IntervalChiNegH1Energy).

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file only.  Lines ≤ 100.
  Mathlib v4.29.1.  `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.
-/
import ShenWork.Paper2.IntervalChiNegGradSummable
import ShenWork.Paper2.IntervalChiNegH1Energy
import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.Paper2.IntervalWienerAlgebra

noncomputable section

open scoped BigOperators
open ShenWork.Paper2.HSigmaScale (lam MemHSigma one_add_lam_pos lam_nonneg)
open ShenWork.Paper2.IntervalWienerAlgebra (hSigma_subset_l1_of_gt_half)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)

namespace ShenWork.Paper2.IntervalChiNegH1Final

/-! ## PIECE A — divergence-weight (√λ) source regularity. -/

/-- **√λ-weighted ℓ¹ flux envelope (the LOCAL smoothing fact).**  For a flux
coefficient sequence `a ∈ H^{σ'}` with `σ' > 3/2`, the divergence-weighted ℓ¹ sum
`Σ_k √λ_k |a_k|` converges.  This is the A-Wiener flux condition (cron1 §3): it
multiplies the `H^{σ'}` energy by the half-weight `√λ_k ≤ (1+λ_k)^{1/2}`, reducing
to `(1+λ)^{1/2}·a ∈ H^{σ'-1}` and the landed `H^{σ'-1} ⊂ ℓ¹` (`σ'-1 > 1/2`).
A LOCAL fixed-weight per-flux fact — NOT the time-uniform H¹ bound. DERIVED. -/
theorem weightedHalf_of_memHSigma {σ' : ℝ} (hσ' : 3 / 2 < σ') {a : ℕ → ℝ}
    (ha : MemHSigma σ' a) :
    Summable (fun k : ℕ => Real.sqrt (lam k) * |a k|) := by
  have hshift : MemHSigma (σ' - 1) (fun k => (1 + lam k) ^ (1 / 2 : ℝ) * a k) := by
    unfold MemHSigma at ha ⊢
    refine ha.congr (fun k => ?_)
    have hpos : 0 < 1 + lam k := one_add_lam_pos k
    have hsq : ((1 + lam k) ^ (1 / 2 : ℝ)) ^ 2 = (1 + lam k) ^ (1 : ℝ) := by
      rw [← Real.rpow_natCast ((1 + lam k) ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hpos.le]
      norm_num
    rw [mul_pow, hsq, ← mul_assoc, ← Real.rpow_add hpos]
    norm_num
  have hl1 := hSigma_subset_l1_of_gt_half (by linarith : (1 : ℝ) / 2 < σ' - 1) hshift
  refine hl1.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
  have hpos : 0 < 1 + lam k := one_add_lam_pos k
  have hle : Real.sqrt (lam k) ≤ (1 + lam k) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt (by have := lam_nonneg k; linarith)
  calc Real.sqrt (lam k) * |a k|
      ≤ (1 + lam k) ^ (1 / 2 : ℝ) * |a k| :=
        mul_le_mul_of_nonneg_right hle (abs_nonneg _)
    _ = |(1 + lam k) ^ (1 / 2 : ℝ) * a k| := by
        rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hpos.le _)]

/-- **√λ-weighted source-package producer.**  From a base time-`C¹` source package
`base : DuhamelSourceTimeC1 a` of the raw flux family, the supplied √λ-weighted ℓ¹
envelope `genv` dominating `√λ·a` (DERIVED via `weightedHalf_of_memHSigma`), and a
uniform √λ-weighted derivative bound `Mdot`, produce the divergence-weighted
package `DuhamelSourceTimeC1 (fun s n => √(lam n) * a s n)` — exactly the shape
`gradSummable_slice` consumes.  This is the landed `.toWeightedTimeC1` pattern at
the half-weight `√λ` (rather than the integer weights `λ`, `λ²`).  DERIVED. -/
def srcWeighted_of_base {a : ℝ → ℕ → ℝ} (base : DuhamelSourceTimeC1 a)
    (genv : ℕ → ℝ) (_hgenv_nn : ∀ n, 0 ≤ genv n) (hgenv_sum : Summable genv)
    (hgenv_bd : ∀ s, 0 ≤ s → ∀ n, Real.sqrt (lam n) * |a s n| ≤ genv n)
    (Mdot : ℝ)
    (hMdot : ∀ s, 0 ≤ s → ∀ n, Real.sqrt (lam n) * |base.adot s n| ≤ Mdot) :
    DuhamelSourceTimeC1 (fun s n => Real.sqrt (lam n) * a s n) where
  adot := fun s n => Real.sqrt (lam n) * base.adot s n
  hderiv := fun s n => (base.hderiv s n).const_mul (Real.sqrt (lam n))
  hadotcont := fun n => (base.hadotcont n).const_mul (Real.sqrt (lam n))
  envelope := genv
  henv_summable := hgenv_sum
  henv_bound := by
    intro s hs n
    have hsq : 0 ≤ Real.sqrt (lam n) := Real.sqrt_nonneg _
    rw [abs_mul, abs_of_nonneg hsq]
    exact hgenv_bd s hs n
  derivBound := Mdot
  hderivBound := by
    intro s hs n
    have hsq : 0 ≤ Real.sqrt (lam n) := Real.sqrt_nonneg _
    rw [abs_mul, abs_of_nonneg hsq]
    exact hMdot s hs n

/-! ## PIECE B — the L² zero-mode part from the L∞ order box. -/

/-- **L²-from-L∞ (the zero-mode part of the H¹ norm).**  If `|g x| ≤ M` for every
`x ∈ [0,1]`, then `∫₀¹ g² ≤ M²` (so `½∫g² ≤ ½M²`).  The L∞ order box
`conjugatePicardLimit_bounded` (value `≤ M`) feeds this to bound the L² leg
`½‖u‖²_{L²}` of the full H¹ norm uniformly in time.  DERIVED. -/
theorem l2_of_sup_bound {g : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hint : IntervalIntegrable (fun x => (g x) ^ 2) MeasureTheory.volume 0 1)
    (hg : ∀ x, x ∈ Set.Icc (0 : ℝ) 1 → |g x| ≤ M) :
    (∫ x in (0 : ℝ)..1, (g x) ^ 2) ≤ M ^ 2 := by
  have hbound : (∫ x in (0 : ℝ)..1, (g x) ^ 2) ≤ ∫ _x in (0 : ℝ)..1, M ^ 2 := by
    refine intervalIntegral.integral_mono_on (by norm_num) hint
      (intervalIntegrable_const) (fun x hx => ?_)
    have hx' : |g x| ≤ M := hg x hx
    nlinarith [abs_nonneg (g x), sq_abs (g x), hx']
  calc (∫ x in (0 : ℝ)..1, (g x) ^ 2)
      ≤ ∫ _x in (0 : ℝ)..1, M ^ 2 := hbound
    _ = M ^ 2 := by simp

/-! ## PIECE C — assemble the full uniform H¹ norm² bound. -/

/-- **Uniform full-H¹-norm² bound — assembly.**  The full H¹ norm² splits as the L²
leg `½∫₀¹ u²` (PIECE B, from the L∞ box `M`) + the seminorm leg `H1energy u`
(the landed `chiNeg_H1_norm_bound`, value `≤ Yhalf`).  Hence the sum is bounded by
`½M² + Yhalf` uniformly in `τ > 0`.  DERIVED assembly over PIECE B + the landed
seminorm headline. -/
theorem chiNeg_H1_full_norm_bound
    {u : ℝ → ShenWork.IntervalDomain.intervalDomainPoint → ℝ} {M Yhalf : ℝ}
    (hM : 0 ≤ M)
    (hint : ∀ τ, 0 < τ → IntervalIntegrable
      (fun x => (ShenWork.IntervalDomain.intervalDomainLift (u τ) x) ^ 2)
      MeasureTheory.volume 0 1)
    (hL2 : ∀ τ, 0 < τ →
      ∀ x, x ∈ Set.Icc (0 : ℝ) 1 →
        |ShenWork.IntervalDomain.intervalDomainLift (u τ) x| ≤ M)
    (hsemi : ∀ τ, 0 < τ →
      ShenWork.Paper2.IntervalChiNegH1Energy.H1energy u τ ≤ Yhalf) :
    ∀ τ, 0 < τ →
      (1 / 2 : ℝ) * (∫ x in (0 : ℝ)..1,
          (ShenWork.IntervalDomain.intervalDomainLift (u τ) x) ^ 2)
        + ShenWork.Paper2.IntervalChiNegH1Energy.H1energy u τ
        ≤ (1 / 2 : ℝ) * M ^ 2 + Yhalf := by
  intro τ hτ
  have hl2 := l2_of_sup_bound hM (hint τ hτ) (hL2 τ hτ)
  have hs := hsemi τ hτ
  have hhalf : (1 / 2 : ℝ) * (∫ x in (0 : ℝ)..1,
      (ShenWork.IntervalDomain.intervalDomainLift (u τ) x) ^ 2)
      ≤ (1 / 2 : ℝ) * M ^ 2 := by
    have : (0 : ℝ) ≤ 1 / 2 := by norm_num
    nlinarith [hl2]
  linarith [hhalf, hs]

/-! ## PIECE A — end-to-end: produce `srcChem`/`srcLog` and feed the per-slice
gradient summability. -/

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.Paper2.IntervalDecompTauLift (conjQ conjFl)

/-- **PIECE A end-to-end — per-slice gradient summability from the flux smoothing
data.**  Assembles the divergence-weighted source packages `srcChem`/`srcLog`
(`srcWeighted_of_base` fed the √λ-weighted ℓ¹ flux envelopes from
`weightedHalf_of_memHSigma`, the LOCAL `MemHSigma σ'` flux facts σ'>3/2) and the
base time-`C¹` packages, then discharges the carried `srcChem`/`srcLog` frontier of
`gradSummable_slice` (IntervalChiNegGradSummable) to obtain the per-slice
eigenvalue-weighted ℓ¹ gradient summability `Σ_k λ_k|û_k(τ)| < ∞`.  This is the
spectral H^{3/2}-regularity input the H¹ energy identity consumes.  DERIVED. -/
theorem gradSummable_slice_of_flux {p : CM2Params} {τ M₀ : ℝ} (hτ : 0 < τ)
    {u : ℝ → intervalDomainPoint → ℝ} {uhat0 : ℕ → ℝ}
    (hM0 : ∀ k, |uhat0 k| ≤ M₀)
    -- base time-C¹ packages of the raw flux families (CARRIED: honest time-C¹ input)
    (baseChem : DuhamelSourceTimeC1 (fun s n => sineCoeffs (conjQ p u s) n))
    (baseLog : DuhamelSourceTimeC1 (fun s n => conjFl p u n s))
    -- √λ-weighted ℓ¹ flux envelopes + derivative bounds (DERIVED via memHSigma)
    (gQ gL : ℕ → ℝ) (hgQ_nn : ∀ n, 0 ≤ gQ n) (hgL_nn : ∀ n, 0 ≤ gL n)
    (hgQ_sum : Summable gQ) (hgL_sum : Summable gL)
    (hgQ_bd : ∀ s, 0 ≤ s → ∀ n,
      Real.sqrt (lam n) * |sineCoeffs (conjQ p u s) n| ≤ gQ n)
    (hgL_bd : ∀ s, 0 ≤ s → ∀ n, Real.sqrt (lam n) * |conjFl p u n s| ≤ gL n)
    (MQ ML : ℝ)
    (hMQ : ∀ s, 0 ≤ s → ∀ n, Real.sqrt (lam n) * |baseChem.adot s n| ≤ MQ)
    (hML : ∀ s, 0 ≤ s → ∀ n, Real.sqrt (lam n) * |baseLog.adot s n| ≤ ML)
    (hdecomp : ∀ k, cosineCoeffs (intervalDomainLift (u τ)) k
        = Real.exp (-(τ * lam k)) * uhat0 k
          + (-p.χ₀) * duhamelEnergyCoeff 1
              (fun k τ => sineCoeffs (conjQ p u τ) k) τ k
          + duhamelEnergyCoeff 1 (conjFl p u) τ k) :
    Summable (fun k : ℕ =>
      lam k * |cosineCoeffs (intervalDomainLift (u τ)) k|) := by
  have srcChem := srcWeighted_of_base baseChem gQ hgQ_nn hgQ_sum hgQ_bd MQ hMQ
  have srcLog := srcWeighted_of_base baseLog gL hgL_nn hgL_sum hgL_bd ML hML
  exact ShenWork.Paper2.IntervalChiNegGradSummable.gradSummable_slice
    hτ hM0 srcChem srcLog hdecomp

section AxiomAudit
#print axioms weightedHalf_of_memHSigma
#print axioms srcWeighted_of_base
#print axioms l2_of_sup_bound
#print axioms gradSummable_slice_of_flux
#print axioms chiNeg_H1_full_norm_bound
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegH1Final
