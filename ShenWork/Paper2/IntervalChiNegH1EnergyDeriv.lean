/-
  ShenWork/Paper2/IntervalChiNegH1EnergyDeriv.lean

  χ₀<0 REBUILD — the LAST piece: the H¹ ENERGY DERIVATIVE via the SPECTRAL route
  (ROUTE A), avoiding the missing mixed gradient regularity `u_xt = ∂ₜ∂ₓ(lift u)`.

  ## The idea (design ROUTE A).
  Parseval rewrites the spatial H¹ seminorm energy `y(τ)=½∫₀¹(∂ₓ lift(u τ))²` as the
  SPECTRAL energy `specH1energy u τ = ½·Σ_k λ_k·û_k(τ)²` with `λ_k=(kπ)²` and
  `û_k(τ)=cosineCoeffs (lift (u τ)) k`.  Differentiating term-by-term gives
  `y'(τ)=Σ_k λ_k·û_k·û_k'` with `û_k'(τ)=cosineCoeffs (∂ₜ lift (u τ)) k` — the
  VALUE-field time-derivative, which IS in the regularity record (conj. 8), so the
  route never touches the gradient time-derivative `u_xt`.  The spectral PDE
  `û_k' = −λ_k û_k + cosineCoeffs(−χ₀·flux + reaction)_k` (from `pde_u` + the
  eigenfunction Laplacian IBP `cosineCoeffs(u_xx)_k = −λ_k û_k`) then yields the
  energy identity `y' = −Σλ_k²û_k² + cross = −‖u_xx‖² + cross` — the H1EnergyIdentity
  shape, with `‖u_xx‖² = Σλ_k²û_k²` by Parseval again.

  ## WHAT LANDS (DERIVED, axiom-clean, no `sorry`):
   * `specH1energy`               — the spectral H¹ energy `½Σλ_k û_k²`.
   * `specH1energy_nonneg`        — `0 ≤ specH1energy`.
   * `specTermDeriv`              — the per-mode derivative `λ_k û_k û_k'` value.
   * `specH1_term_hasDerivAt`     — per-mode `HasDerivAt (½λ_k û_k²) (λ_k û_k û_k')`
       by the chain rule, from the per-mode coeff time-derivative (conj.-8 datum).
   * `specH1_hasDerivAt_of_majorant` — the term-by-term `hasDerivAt_tsum` ENGINE:
       given the supplied uniform majorant `umaj` (Σ-summable, dominating every
       per-mode derivative on a τ-ball) and the per-mode derivatives, the spectral
       energy has derivative `Σ_k λ_k û_k û_k'`.  DERIVED wrapper of Mathlib
       `hasDerivAt_tsum`; the majorant is the SUPPLIED `ℓ¹`-weighted data.
   * `lapCoeff_eq_neg_lam_coeff` — `cosineCoeffs(u_xx)_k = −λ_k·û_k` from the landed
       eigenfunction Laplacian IBP `intervalCosineLaplacianCoeff_eq_of_contDiffOn`
       (record conj. 7).  DERIVED.
   * `specPDE_mode`               — the spectral PDE per mode
       `û_k' = −λ_k û_k + cosineCoeffs(srcField)_k`, from `pde_u` rearranged +
       `lapCoeff_eq_neg_lam_coeff` + `cosineCoeffs` ℝ-linearity.  DERIVED.
   * `H1EnergyIdentity_of_spectral` — assembles the spectral derivative + the
       Parseval bridges (`hParsevalGrad`, `hParsevalLap`) into the scaffold
       `H1EnergyIdentity` shape.  DERIVED rewrite.

  ## CARRIED — the ONE genuine analytic frontier (the spectral analogue of the
  missing `u_xt`), with the precise missing lemma and the failed greps:
   * `gradL2_eq_spectral` (the Parseval bridge `H1energy = specH1energy`) and the
     uniform tsum majorant both require the EIGENVALUE-WEIGHTED `ℓ¹` summability of
     the classical solution's cosine coefficients, `Σ_k λ_k·|û_k(τ)| < ∞`
     (a Wiener-algebra-of-the-GRADIENT / `H^{three-halves}` regularity), PLUS the cosine
     RECONSTRUCTION `lift (u τ) = Σ_k û_k cos(kπ·)` pointwise.  The record carries
     only spatial `C²` (conj. 1,7) and the value-field `∂ₜ` joint continuity
     (conj. 8); NEITHER the weighted-`ℓ¹` spectral summability NOR the cosine
     reconstruction identity for a GENERAL classical solution is present.  Failed
     greps (the reconstruction/weighted-summability for the bare record):
        grep -rn "Summable.*eigenvalue.*cosineCoeffs.*lift"      ShenWork → NONE
        grep -rn "intervalDomainLift.*= ∑.*cosineCoeffs.*cos"    ShenWork → NONE
        grep -rn "f x = ∑.*sineCoeffs.*sin|reconstruct.*sine"    ShenWork → NONE
        grep -rn "gradL2_eq_spectral|spectral.*gradient.*Parseval" ShenWork → NONE
     The landed `cosineCoeffSeries_grad_hasDerivAt`/`sineSeries_l2_sq` ARE the
     engines, but they CONSUME exactly this `Summable (λ_n·|b_n|)` hypothesis — the
     spectral analogue of the missing `u_xt` parabolic regularity.  Carried below as
     the named hypotheses `hParsevalGrad`/`hParsevalLap` (Parseval bridges) and
     `hmaj`/`hcoeffDeriv` (the weighted-`ℓ¹` uniform majorant + per-mode derivative).

  ## TWO-WAY AUDIT.  DERIVED: `specH1energy(_nonneg)`, `specH1_term_hasDerivAt`,
  `specH1_hasDerivAt_of_majorant` (the tsum engine over the supplied majorant),
  `lapCoeff_eq_neg_lam_coeff`, `specPDE_mode`, `H1EnergyIdentity_of_spectral`.
  CARRIED: the two Parseval bridges + the uniform weighted-`ℓ¹` majorant — each the
  precise named obligation reducing to the spectral `H^{three-halves}` regularity of the
  classical solution (the spectral analogue of `u_xt`), with its failed grep, never
  faked, never relabeled.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file only.  Lines ≤ 100.
  Mathlib v4.29.1.  `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.
-/
import ShenWork.Paper2.IntervalChiNegH1EnergyCore
import ShenWork.Paper2.IntervalDivergenceModeIdentity
import ShenWork.PDE.IntervalEllipticCharacterization

noncomputable section

open scoped BigOperators Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalDomain)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2 (IsPaper2ClassicalSolution)
open ShenWork.IntervalEllipticCharacterization
  (intervalCosineLaplacianCoeff_eq_of_contDiffOn)

namespace ShenWork.Paper2.IntervalChiNegH1EnergyDeriv

/-- The spectral cosine coefficient `û_k(τ) = cosineCoeffs (lift (u τ)) k`. -/
def uhat (u : ℝ → intervalDomainPoint → ℝ) (τ : ℝ) (k : ℕ) : ℝ :=
  cosineCoeffs (intervalDomainLift (u τ)) k

/-- The spectral H¹ energy `½·Σ_k λ_k·û_k(τ)²` (`λ_k = (kπ)²`). -/
def specH1energy (u : ℝ → intervalDomainPoint → ℝ) (τ : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑' k : ℕ, unitIntervalCosineEigenvalue k * (uhat u τ k) ^ 2

/-- The per-mode energy-derivative value `λ_k·û_k(τ)·û_k'(τ)`. -/
def specTermDeriv (u : ℝ → intervalDomainPoint → ℝ) (uhatT : ℝ → ℕ → ℝ)
    (τ : ℝ) (k : ℕ) : ℝ :=
  unitIntervalCosineEigenvalue k * (uhat u τ k * uhatT τ k)

/-- **`0 ≤ specH1energy`** — a half-sum of `λ_k·û_k² ≥ 0`. -/
theorem specH1energy_nonneg (u : ℝ → intervalDomainPoint → ℝ) (τ : ℝ) :
    0 ≤ specH1energy u τ := by
  unfold specH1energy
  have h : (0 : ℝ) ≤ ∑' k : ℕ, unitIntervalCosineEigenvalue k * (uhat u τ k) ^ 2 :=
    tsum_nonneg (fun k => by
      have : (0 : ℝ) ≤ unitIntervalCosineEigenvalue k := by
        unfold unitIntervalCosineEigenvalue; positivity
      positivity)
  linarith

/-- **Per-mode `HasDerivAt`** of the term `τ ↦ ½·λ_k·û_k(τ)²` with value
`λ_k·û_k(τ)·û_k'(τ)`, GIVEN the per-mode coefficient time-derivative
`hd : HasDerivAt (fun s => uhat u s k) (uhatT τ k) τ` (the conj.-8 value-field
datum: `û_k` is a fixed linear integral functional of `lift (u s)`).  Chain rule;
DERIVED. -/
theorem specH1_term_hasDerivAt {u : ℝ → intervalDomainPoint → ℝ} {uhatT : ℝ → ℕ → ℝ}
    {τ : ℝ} (k : ℕ) (hd : HasDerivAt (fun s => uhat u s k) (uhatT τ k) τ) :
    HasDerivAt (fun s => (1 / 2 : ℝ) * unitIntervalCosineEigenvalue k * (uhat u s k) ^ 2)
      (specTermDeriv u uhatT τ k) τ := by
  have hsq : HasDerivAt (fun s => (uhat u s k) ^ 2)
      (2 * uhat u τ k * uhatT τ k) τ := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hd.pow 2
  have hc := hsq.const_mul ((1 / 2 : ℝ) * unitIntervalCosineEigenvalue k)
  refine hc.congr_deriv ?_
  unfold specTermDeriv; ring

/-- **The term-by-term `hasDerivAt_tsum` ENGINE.**  Given a Σ-summable uniform
majorant `umaj` dominating every per-mode derivative on all of `ℝ`
(`hbound : ∀ k s, ‖specTermDeriv u uhatT s k‖ ≤ umaj k`), the per-mode coefficient
derivatives `hcoeffDeriv` (∀ k s, the value-field datum), and the value-summability
`hval : Summable (fun k => ½·λ_k·û_k(τ)²)`, the spectral energy has derivative
`Σ_k specTermDeriv = Σ_k λ_k û_k û_k'`.  DERIVED wrapper of Mathlib `hasDerivAt_tsum`;
the SUPPLIED majorant is the weighted-`ℓ¹` data (carried — see header). -/
theorem specH1_hasDerivAt_of_majorant {u : ℝ → intervalDomainPoint → ℝ}
    {uhatT : ℝ → ℕ → ℝ} {umaj : ℕ → ℝ} {τ : ℝ}
    (hmaj : Summable umaj)
    (hcoeffDeriv : ∀ (k : ℕ) (s : ℝ), HasDerivAt (fun r => uhat u r k) (uhatT s k) s)
    (hbound : ∀ (k : ℕ) (s : ℝ), ‖specTermDeriv u uhatT s k‖ ≤ umaj k)
    (hval : Summable (fun k : ℕ =>
      (1 / 2 : ℝ) * unitIntervalCosineEigenvalue k * (uhat u τ k) ^ 2)) :
    HasDerivAt (specH1energy u) (∑' k : ℕ, specTermDeriv u uhatT τ k) τ := by
  have hterm : ∀ (k : ℕ) (s : ℝ),
      HasDerivAt (fun r => (1 / 2 : ℝ) * unitIntervalCosineEigenvalue k * (uhat u r k) ^ 2)
        (specTermDeriv u uhatT s k) s :=
    fun k s => specH1_term_hasDerivAt k (hcoeffDeriv k s)
  have hEeq : specH1energy u
      = fun s => ∑' k : ℕ,
          (1 / 2 : ℝ) * unitIntervalCosineEigenvalue k * (uhat u s k) ^ 2 := by
    funext s; unfold specH1energy; rw [← tsum_mul_left]
    refine tsum_congr (fun k => by ring)
  rw [hEeq]
  exact hasDerivAt_tsum (𝕜 := ℝ) (u := umaj) hmaj hterm hbound hval τ

/-- **Eigenfunction Laplacian coefficient identity** `cosineCoeffs(u_xx)_k = −λ_k·û_k`.
For the spatial slice `g = lift (u τ)`, the closed-`Icc` `C²` (record conj. 7) +
endpoint Neumann (tendsto + value `0`) give, via the landed
`intervalCosineLaplacianCoeff_eq_of_contDiffOn`, `cosineCoeffs(∂ₓ²g)_k = −λ_k·û_k`
for `k ≥ 1` (the `k=0` mode `cosineCoeffs(∂ₓ²g)_0 = ∂ₓg|₀¹ = 0 = −λ_0·û_0`).  DERIVED.
This is the per-mode `−Σλ²û²` engine of the H¹ identity. -/
theorem lapCoeff_eq_neg_lam_coeff {u : ℝ → intervalDomainPoint → ℝ} {τ : ℝ} (k : ℕ)
    (hg : ContDiffOn ℝ 2 (intervalDomainLift (u τ)) (Set.Icc (0 : ℝ) 1))
    (htend0 : Filter.Tendsto (deriv (intervalDomainLift (u τ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htend1 : Filter.Tendsto (deriv (intervalDomainLift (u τ)))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0))
    (hbc0 : deriv (intervalDomainLift (u τ)) 0 = 0)
    (hbc1 : deriv (intervalDomainLift (u τ)) 1 = 0) :
    cosineCoeffs (fun y => deriv (fun z => deriv (intervalDomainLift (u τ)) z) y) k
      = -(unitIntervalCosineEigenvalue k) * uhat u τ k := by
  have hibp := intervalCosineLaplacianCoeff_eq_of_contDiffOn
    k hg htend0 htend1 hbc0 hbc1
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- `k = 0`: both `cosineCoeffs` use the `c(0)=1` factor; `λ_0 = 0`.
    rw [ShenWork.IntervalMildPicardRegularity.cosineCoeffs_zero_eq_integral,
      uhat, ShenWork.IntervalMildPicardRegularity.cosineCoeffs_zero_eq_integral]
    simp only [unitIntervalCosineEigenvalue, Nat.cast_zero, zero_mul] at hibp ⊢
    simp only [Real.cos_zero, one_mul] at hibp
    simpa using hibp
  · have hkne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
    rw [ShenWork.IntervalMildPicardRegularity.cosineCoeffs_pos_eq_integral hkne,
      uhat, ShenWork.IntervalMildPicardRegularity.cosineCoeffs_pos_eq_integral hkne,
      hibp, unitIntervalCosineEigenvalue]
    ring

/-- **The spectral PDE per mode** `û_k'(τ) = −λ_k·û_k(τ) + cosineCoeffs(srcField τ)_k`.
GIVEN the value-field coefficient time-derivative `hd : û_k'(τ) = cosineCoeffs(∂ₜ lift)_k`
(conj.-8 datum, `û_k` linear in the value field) and the linear-decomposition datum
`hsrc : cosineCoeffs(∂ₜ lift (u τ))_k = cosineCoeffs(u_xx)_k + srcCoeff` (the cosine
functional of `pde_u`'s RHS, split by `cosineCoeffs_sub_eq` ℝ-linearity into the
Laplacian mode + the flux+reaction modes `srcCoeff`), substituting
`lapCoeff_eq_neg_lam_coeff` gives the diagonal spectral PDE.  DERIVED rewrite. -/
theorem specPDE_mode {u : ℝ → intervalDomainPoint → ℝ} {τ uhatTk srcCoeff : ℝ} (k : ℕ)
    (hg : ContDiffOn ℝ 2 (intervalDomainLift (u τ)) (Set.Icc (0 : ℝ) 1))
    (htend0 : Filter.Tendsto (deriv (intervalDomainLift (u τ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htend1 : Filter.Tendsto (deriv (intervalDomainLift (u τ)))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0))
    (hbc0 : deriv (intervalDomainLift (u τ)) 0 = 0)
    (hbc1 : deriv (intervalDomainLift (u τ)) 1 = 0)
    (hsrc : uhatTk =
      cosineCoeffs (fun y => deriv (fun z => deriv (intervalDomainLift (u τ)) z) y) k
        + srcCoeff) :
    uhatTk = -(unitIntervalCosineEigenvalue k) * uhat u τ k + srcCoeff := by
  rw [hsrc, lapCoeff_eq_neg_lam_coeff k hg htend0 htend1 hbc0 hbc1]

/-- **Assembly into the scaffold `H1EnergyIdentity` shape.**
GIVEN the spectral-energy derivative `hder` (`specH1_hasDerivAt_of_majorant`'s
output, value `D := Σ_k λ_k û_k û_k'`), the Parseval GRADIENT bridge
`hParsevalGrad : H1energy u = specH1energy u` (the carried frontier, see header) and
the value identity `hval : Σ_k specTermDeriv = −lapL2sq u τ + (−χ₀)·taxisX
+ (−χ₀)·uvxx + reactX` (the post-PDE sorting: `Σλ_k û_k·(−λ_k û_k) = −Σλ_k²û_k²
= −‖u_xx‖²` by `hParsevalLap`, plus the flux/reaction cross modes), this is exactly
`H1EnergyIdentity p u τ taxisX uvxx reactX`.  DERIVED rewrite of `hder` along the
two bridges. -/
theorem H1EnergyIdentity_of_spectral
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {uhatT : ℝ → ℕ → ℝ}
    {τ taxisX uvxx reactX : ℝ}
    (hParsevalGrad : ShenWork.Paper2.IntervalChiNegH1Energy.H1energy u = specH1energy u)
    (hder : HasDerivAt (specH1energy u) (∑' k : ℕ, specTermDeriv u uhatT τ k) τ)
    (hval : (∑' k : ℕ, specTermDeriv u uhatT τ k)
      = -(ShenWork.Paper2.IntervalChiNegH1Energy.lapL2sq u τ)
        + (-p.χ₀) * taxisX + (-p.χ₀) * uvxx + reactX) :
    ShenWork.Paper2.IntervalChiNegH1Energy.H1EnergyIdentity p u τ taxisX uvxx reactX := by
  unfold ShenWork.Paper2.IntervalChiNegH1Energy.H1EnergyIdentity
  rw [hParsevalGrad, ← hval]; exact hder

section AxiomAudit
#print axioms specH1energy_nonneg
#print axioms specH1_term_hasDerivAt
#print axioms specH1_hasDerivAt_of_majorant
#print axioms lapCoeff_eq_neg_lam_coeff
#print axioms specPDE_mode
#print axioms H1EnergyIdentity_of_spectral
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegH1EnergyDeriv
