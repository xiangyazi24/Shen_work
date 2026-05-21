/-
  Statement layer for Chen-Ruau-Shen,
  "Chemotaxis models with signal-dependent sensitivity and a logistic-type
  source, II: Persistence and stabilization".

  The paper's main results are Theorems 2.1--2.5.  They are stated here against
  the non-toy bounded-domain PDE interface from `Paper2/Statements.lean`.
-/
import ShenWork.Paper2.Statements
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

open Filter Topology

namespace ShenWork.Paper3

open ShenWork.Paper2

noncomputable section

abbrev BoundedDomainData := ShenWork.Paper2.BoundedDomainData

def positiveEquilibrium (p : CM2Params) (_hab : 0 < p.a ∧ 0 < p.b) : ℝ × ℝ :=
  ((p.a / p.b) ^ (1 / p.α),
    p.ν / p.μ * ((p.a / p.b) ^ (1 / p.α)) ^ p.γ)

def minimalEquilibrium (p : CM2Params) (uStar : ℝ) : ℝ × ℝ :=
  (uStar, p.ν / p.μ * uStar ^ p.γ)

lemma positiveEquilibrium_fst_pos
    (p : CM2Params) (hab : 0 < p.a ∧ 0 < p.b) :
    0 < (positiveEquilibrium p hab).1 := by
  change 0 < (p.a / p.b) ^ (1 / p.α)
  exact Real.rpow_pos_of_pos (div_pos hab.1 hab.2) _

lemma positiveEquilibrium_snd_pos
    (p : CM2Params) (hab : 0 < p.a ∧ 0 < p.b) :
    0 < (positiveEquilibrium p hab).2 := by
  change 0 < p.ν / p.μ * ((p.a / p.b) ^ (1 / p.α)) ^ p.γ
  exact mul_pos (div_pos p.hν p.hμ)
    (Real.rpow_pos_of_pos
      (Real.rpow_pos_of_pos (div_pos hab.1 hab.2) _) _)

lemma positiveEquilibrium_fst_rpow_alpha
    (p : CM2Params) (hab : 0 < p.a ∧ 0 < p.b) :
    (positiveEquilibrium p hab).1 ^ p.α = p.a / p.b := by
  change ((p.a / p.b) ^ (1 / p.α)) ^ p.α = p.a / p.b
  rw [← Real.rpow_mul (div_pos hab.1 hab.2).le]
  have hα_ne : p.α ≠ 0 := ne_of_gt p.hα
  field_simp [hα_ne]
  rw [Real.rpow_one]

lemma positiveEquilibrium_fst_eq_one
    (p : CM2Params) (hab : 0 < p.a ∧ 0 < p.b) (hab_eq : p.a = p.b) :
    (positiveEquilibrium p hab).1 = 1 := by
  change (p.a / p.b) ^ (1 / p.α) = 1
  rw [hab_eq, div_self (ne_of_gt hab.2)]
  exact Real.one_rpow _

lemma positiveEquilibrium_snd_eq_nu_div_mu
    (p : CM2Params) (hab : 0 < p.a ∧ 0 < p.b)
    (hab_eq : p.a = p.b) (hγ : p.γ = 1) :
    (positiveEquilibrium p hab).2 = p.ν / p.μ := by
  change p.ν / p.μ * ((p.a / p.b) ^ (1 / p.α)) ^ p.γ = p.ν / p.μ
  rw [hab_eq, div_self (ne_of_gt hab.2), hγ]
  simp

lemma positiveEquilibrium_logistic_zero
    (p : CM2Params) (hab : 0 < p.a ∧ 0 < p.b) :
    p.a - p.b * (positiveEquilibrium p hab).1 ^ p.α = 0 := by
  rw [positiveEquilibrium_fst_rpow_alpha p hab]
  field_simp [ne_of_gt hab.2]
  ring

lemma positiveEquilibrium_reaction_zero
    (p : CM2Params) (hab : 0 < p.a ∧ 0 < p.b) :
    (positiveEquilibrium p hab).1 *
      (p.a - p.b * (positiveEquilibrium p hab).1 ^ p.α) = 0 := by
  rw [positiveEquilibrium_logistic_zero p hab]
  ring

lemma positiveEquilibrium_elliptic_relation
    (p : CM2Params) (hab : 0 < p.a ∧ 0 < p.b) :
    p.μ * (positiveEquilibrium p hab).2 =
      p.ν * (positiveEquilibrium p hab).1 ^ p.γ := by
  change p.μ * (p.ν / p.μ * ((p.a / p.b) ^ (1 / p.α)) ^ p.γ) =
    p.ν * ((p.a / p.b) ^ (1 / p.α)) ^ p.γ
  field_simp [ne_of_gt p.hμ]

lemma minimalEquilibrium_fst_eq (p : CM2Params) (uStar : ℝ) :
    (minimalEquilibrium p uStar).1 = uStar := by
  rfl

lemma minimalEquilibrium_snd_eq_nu_div_mu_mul_uStar
    (p : CM2Params) (uStar : ℝ) (hγ : p.γ = 1) :
    (minimalEquilibrium p uStar).2 = p.ν / p.μ * uStar := by
  change p.ν / p.μ * uStar ^ p.γ = p.ν / p.μ * uStar
  rw [hγ, Real.rpow_one]

lemma minimalEquilibrium_snd_pos
    (p : CM2Params) {uStar : ℝ} (huStar : 0 < uStar) :
    0 < (minimalEquilibrium p uStar).2 := by
  change 0 < p.ν / p.μ * uStar ^ p.γ
  exact mul_pos (div_pos p.hν p.hμ) (Real.rpow_pos_of_pos huStar _)

lemma minimalEquilibrium_elliptic_relation
    (p : CM2Params) (uStar : ℝ) :
    p.μ * (minimalEquilibrium p uStar).2 =
      p.ν * (minimalEquilibrium p uStar).1 ^ p.γ := by
  change p.μ * (p.ν / p.μ * uStar ^ p.γ) = p.ν * uStar ^ p.γ
  field_simp [ne_of_gt p.hμ]

lemma minimalEquilibrium_reaction_zero_of_a_b_zero
    (p : CM2Params) (uStar : ℝ) (ha : p.a = 0) (hb : p.b = 0) :
    (minimalEquilibrium p uStar).1 *
      (p.a - p.b * (minimalEquilibrium p uStar).1 ^ p.α) = 0 := by
  simp [minimalEquilibrium, ha, hb]

def PositiveGlobalBoundedSolution
    (D : BoundedDomainData) (p : CM2Params)
    (u v : ℝ → D.Point → ℝ) : Prop :=
  IsPaper2GlobalClassicalSolution D p u v ∧
    IsPaper2Bounded D u ∧
    ∀ t x, 0 < t → x ∈ D.inside → 0 < u t x

lemma PositiveGlobalBoundedSolution.of_global_bounded
    {D : BoundedDomainData} {p : CM2Params} {u v : ℝ → D.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution D p u v)
    (hbdd : IsPaper2Bounded D u) :
    PositiveGlobalBoundedSolution D p u v :=
  ⟨hglobal, hbdd, fun t x ht hx => hglobal.u_pos (t := t) (x := x) ht hx⟩

def EventuallyLowerBound
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ) (δ : ℝ) : Prop :=
  0 < δ ∧ ∀ᶠ t in atTop, δ ≤ D.infValue (u t)

def UniformConvergesInSup
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ) (a : ℝ) : Prop :=
  Tendsto (fun t => D.supNorm (fun x => u t x - a)) atTop (𝓝 0)

def HasInitialMass
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ) (uStar : ℝ) : Prop :=
  D.integral (u 0) = D.volume * uStar

def ThetaMomentConvergesToZero
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (uStar theta : ℝ) : Prop :=
  Tendsto
    (fun t => D.integral
      (fun x => (u t x - uStar) * ((u t x) ^ theta - uStar ^ theta)))
    atTop (𝓝 0)

lemma PositiveGlobalBoundedSolution.classical
    {D : BoundedDomainData} {p : CM2Params} {u v : ℝ → D.Point → ℝ}
    (h : PositiveGlobalBoundedSolution D p u v) :
    IsPaper2GlobalClassicalSolution D p u v :=
  h.1

lemma PositiveGlobalBoundedSolution.bounded
    {D : BoundedDomainData} {p : CM2Params} {u v : ℝ → D.Point → ℝ}
    (h : PositiveGlobalBoundedSolution D p u v) :
    IsPaper2Bounded D u :=
  h.2.1

lemma PositiveGlobalBoundedSolution.regularity
    {D : BoundedDomainData} {p : CM2Params} {T : ℝ}
    {u v : ℝ → D.Point → ℝ}
    (h : PositiveGlobalBoundedSolution D p u v) (hT : 0 < T) :
    D.classicalRegularity T u v :=
  h.classical.regularity hT

lemma PositiveGlobalBoundedSolution.pos
    {D : BoundedDomainData} {p : CM2Params} {u v : ℝ → D.Point → ℝ}
    (h : PositiveGlobalBoundedSolution D p u v)
    {t : ℝ} {x : D.Point} (ht : 0 < t) (hx : x ∈ D.inside) :
    0 < u t x :=
  h.2.2 t x ht hx

lemma PositiveGlobalBoundedSolution.pde_u
    {D : BoundedDomainData} {p : CM2Params} {t : ℝ}
    {u v : ℝ → D.Point → ℝ} {x : D.Point}
    (h : PositiveGlobalBoundedSolution D p u v)
    (ht0 : 0 < t) (hx : x ∈ D.inside) :
    D.timeDeriv u t x =
      D.laplacian (u t) x
        - p.χ₀ * D.chemotaxisDiv p (u t) (v t) x
        + u t x * (p.a - p.b * (u t x) ^ p.α) :=
  h.classical.pde_u ht0 hx

lemma PositiveGlobalBoundedSolution.pde_v
    {D : BoundedDomainData} {p : CM2Params} {t : ℝ}
    {u v : ℝ → D.Point → ℝ} {x : D.Point}
    (h : PositiveGlobalBoundedSolution D p u v)
    (ht0 : 0 < t) (hx : x ∈ D.inside) :
    0 = D.laplacian (v t) x - p.μ * v t x + p.ν * (u t x) ^ p.γ :=
  h.classical.pde_v ht0 hx

lemma PositiveGlobalBoundedSolution.neumann
    {D : BoundedDomainData} {p : CM2Params} {t : ℝ}
    {u v : ℝ → D.Point → ℝ} {x : D.Point}
    (h : PositiveGlobalBoundedSolution D p u v)
    (ht0 : 0 < t) (hx : x ∈ D.boundary) :
    D.normalDeriv (u t) x = 0 ∧ D.normalDeriv (v t) x = 0 :=
  h.classical.neumann ht0 hx

lemma EventuallyLowerBound.delta_pos
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {δ : ℝ}
    (h : EventuallyLowerBound D u δ) :
    0 < δ :=
  h.1

lemma EventuallyLowerBound.eventually
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {δ : ℝ}
    (h : EventuallyLowerBound D u δ) :
    ∀ᶠ t in atTop, δ ≤ D.infValue (u t) :=
  h.2

lemma UniformConvergesInSup.tendsto
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {a : ℝ}
    (h : UniformConvergesInSup D u a) :
    Tendsto (fun t => D.supNorm (fun x => u t x - a)) atTop (𝓝 0) :=
  h

lemma HasInitialMass.eq
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {uStar : ℝ}
    (h : HasInitialMass D u uStar) :
    D.integral (u 0) = D.volume * uStar :=
  h

lemma ThetaMomentConvergesToZero.tendsto
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {uStar theta : ℝ}
    (h : ThetaMomentConvergesToZero D u uStar theta) :
    Tendsto
      (fun t => D.integral
        (fun x => (u t x - uStar) * ((u t x) ^ theta - uStar ^ theta)))
      atTop (𝓝 0) :=
  h

structure SpectralData where
  eigenvalue : ℕ → ℝ
  firstNonzero : ℝ

structure HasNeumannSpectrum (S : SpectralData) : Prop where
  zero_eigenvalue : S.eigenvalue 0 = 0
  eigenvalue_nonneg : ∀ n : ℕ, 0 ≤ S.eigenvalue n
  eigenvalue_pos_of_ne_zero : ∀ n : ℕ, n ≠ 0 → 0 < S.eigenvalue n
  firstNonzero_pos : 0 < S.firstNonzero
  firstNonzero_le_eigenvalue : ∀ n : ℕ, n ≠ 0 → S.firstNonzero ≤ S.eigenvalue n

lemma HasNeumannSpectrum.eigenvalue_nonneg_of_ne_zero
    {S : SpectralData} (H : HasNeumannSpectrum S) {n : ℕ} (_hn : n ≠ 0) :
    0 ≤ S.eigenvalue n :=
  H.eigenvalue_nonneg n

/-- The one-dimensional Neumann spectrum on the unit interval:
`λ_n = n^2 π^2`, with first nonzero mode `π^2`. -/
def unitIntervalNeumannSpectrum : SpectralData where
  eigenvalue := fun n => (n : ℝ) ^ 2 * Real.pi ^ 2
  firstNonzero := Real.pi ^ 2

/-- The concrete unit-interval spectrum satisfies the spectral positivity and
first-mode lower-bound interface used by the Paper3 linear theory. -/
lemma unitIntervalNeumannSpectrum_hasNeumannSpectrum :
    HasNeumannSpectrum unitIntervalNeumannSpectrum := by
  refine
    { zero_eigenvalue := ?_
      eigenvalue_nonneg := ?_
      eigenvalue_pos_of_ne_zero := ?_
      firstNonzero_pos := ?_
      firstNonzero_le_eigenvalue := ?_ }
  · simp [unitIntervalNeumannSpectrum]
  · intro n
    exact mul_nonneg (sq_nonneg (n : ℝ)) (sq_nonneg Real.pi)
  · intro n hn
    have hn_real_ne : (n : ℝ) ≠ 0 := by
      exact_mod_cast hn
    exact mul_pos (sq_pos_of_ne_zero hn_real_ne)
      (sq_pos_of_ne_zero (ne_of_gt Real.pi_pos))
  · exact sq_pos_of_ne_zero (ne_of_gt Real.pi_pos)
  · intro n hn
    have hn_nat : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
    have hn_real : (1 : ℝ) ≤ n := by
      exact_mod_cast hn_nat
    have hn_sq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
    calc
      unitIntervalNeumannSpectrum.firstNonzero
          = (1 : ℝ) * Real.pi ^ 2 := by
            simp [unitIntervalNeumannSpectrum]
      _ ≤ (n : ℝ) ^ 2 * Real.pi ^ 2 :=
            mul_le_mul_of_nonneg_right hn_sq (sq_nonneg Real.pi)
      _ = unitIntervalNeumannSpectrum.eigenvalue n := by
            simp [unitIntervalNeumannSpectrum]

def sigma
    (p : CM2Params) (uStar vStar lambdaN : ℝ) : ℝ :=
  -lambdaN +
    p.χ₀ * p.ν * p.γ *
      (uStar ^ (p.m + p.γ - 1) * lambdaN) /
        ((1 + vStar) ^ p.β * (p.μ + lambdaN)) -
    p.a * p.α

def sigmaBase (p : CM2Params) (lambdaN : ℝ) : ℝ :=
  -lambdaN - p.a * p.α

def sigmaChemCoefficient
    (p : CM2Params) (uStar vStar lambdaN : ℝ) : ℝ :=
  p.ν * p.γ *
    (uStar ^ (p.m + p.γ - 1) * lambdaN) /
      ((1 + vStar) ^ p.β * (p.μ + lambdaN))

def sigmaCriticalChi
    (p : CM2Params) (uStar vStar lambdaN : ℝ) : ℝ :=
  (lambdaN + p.a * p.α) /
    sigmaChemCoefficient p uStar vStar lambdaN

/-- The explicit per-mode factor appearing inside the paper's critical
sensitivity threshold `(2.10)`.  The paper's `χ*` is the infimum of these
quantities over the nonzero Neumann modes. -/
def sigmaCriticalChiPaperFormula
    (p : CM2Params) (uStar vStar lambdaN : ℝ) : ℝ :=
  ((1 + vStar) ^ p.β /
      (p.ν * p.γ * uStar ^ (p.m + p.γ - 1))) *
    ((lambdaN + p.a * p.α) * (p.μ + lambdaN) / lambdaN)

/-- The nonzero-mode values whose infimum is the paper's critical sensitivity
threshold `(2.10)`. -/
def paperCriticalSensitivitySet
    (S : SpectralData) (p : CM2Params) (uStar vStar : ℝ) : Set ℝ :=
  {χ | ∃ n : ℕ, n ≠ 0 ∧
    χ = sigmaCriticalChiPaperFormula p uStar vStar (S.eigenvalue n)}

/-- Paper3's critical sensitivity threshold `χ*`, represented as the infimum
of the explicit nonzero-mode values in `(2.10)`. -/
def paperCriticalSensitivity
    (S : SpectralData) (p : CM2Params) (uStar vStar : ℝ) : ℝ :=
  sInf (paperCriticalSensitivitySet S p uStar vStar)

lemma paperCriticalSensitivitySet_nonempty
    (S : SpectralData) (p : CM2Params) (uStar vStar : ℝ) :
    (paperCriticalSensitivitySet S p uStar vStar).Nonempty := by
  refine ⟨sigmaCriticalChiPaperFormula p uStar vStar (S.eigenvalue 1), ?_⟩
  exact ⟨1, by norm_num, rfl⟩

lemma sigma_eq_base_add_chi_coeff
    (p : CM2Params) (uStar vStar lambdaN : ℝ) :
    sigma p uStar vStar lambdaN =
      sigmaBase p lambdaN +
        p.χ₀ * sigmaChemCoefficient p uStar vStar lambdaN := by
  unfold sigma sigmaBase sigmaChemCoefficient
  ring

lemma sigmaChemCoefficient_nonneg
    (p : CM2Params) {uStar vStar lambdaN : ℝ}
    (huStar : 0 ≤ uStar) (hvStar : 0 ≤ vStar) (hlambda : 0 ≤ lambdaN) :
    0 ≤ sigmaChemCoefficient p uStar vStar lambdaN := by
  unfold sigmaChemCoefficient
  have hden_pos :
      0 < (1 + vStar) ^ p.β * (p.μ + lambdaN) := by
    exact mul_pos
      (Real.rpow_pos_of_pos (by linarith : 0 < 1 + vStar) _)
      (by linarith [p.hμ])
  have hnum_nonneg :
      0 ≤ p.ν * p.γ * (uStar ^ (p.m + p.γ - 1) * lambdaN) := by
    exact mul_nonneg (mul_pos p.hν p.hγ).le
      (mul_nonneg (Real.rpow_nonneg huStar _) hlambda)
  exact div_nonneg hnum_nonneg hden_pos.le

lemma sigmaChemCoefficient_pos
    (p : CM2Params) {uStar vStar lambdaN : ℝ}
    (huStar : 0 < uStar) (hvStar : 0 ≤ vStar) (hlambda : 0 < lambdaN) :
    0 < sigmaChemCoefficient p uStar vStar lambdaN := by
  unfold sigmaChemCoefficient
  have hden_pos :
      0 < (1 + vStar) ^ p.β * (p.μ + lambdaN) := by
    exact mul_pos
      (Real.rpow_pos_of_pos (by linarith : 0 < 1 + vStar) _)
      (by linarith [p.hμ])
  have hnum_pos :
      0 < p.ν * p.γ * (uStar ^ (p.m + p.γ - 1) * lambdaN) := by
    exact mul_pos (mul_pos p.hν p.hγ)
      (mul_pos (Real.rpow_pos_of_pos huStar _) hlambda)
  exact div_pos hnum_pos hden_pos

lemma sigmaCriticalChi_pos
    (p : CM2Params) {uStar vStar lambdaN : ℝ}
    (huStar : 0 < uStar) (hvStar : 0 ≤ vStar) (hlambda : 0 < lambdaN) :
    0 < sigmaCriticalChi p uStar vStar lambdaN := by
  unfold sigmaCriticalChi
  have hnum : 0 < lambdaN + p.a * p.α := by
    nlinarith [hlambda, p.ha, p.hα]
  have hden : 0 < sigmaChemCoefficient p uStar vStar lambdaN :=
    sigmaChemCoefficient_pos p huStar hvStar hlambda
  exact div_pos hnum hden

lemma sigmaCriticalChi_eq_paperFormula
    (p : CM2Params) {uStar vStar lambdaN : ℝ}
    (huStar : 0 < uStar) (hvStar : 0 ≤ vStar) (hlambda : 0 < lambdaN) :
    sigmaCriticalChi p uStar vStar lambdaN =
      sigmaCriticalChiPaperFormula p uStar vStar lambdaN := by
  unfold sigmaCriticalChi sigmaChemCoefficient sigmaCriticalChiPaperFormula
  have hvpos : 0 < 1 + vStar := by linarith
  have hpowv : (1 + vStar) ^ p.β ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hvpos _)
  have hpowu : uStar ^ (p.m + p.γ - 1) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos huStar _)
  have hmulcoeff :
      p.ν * p.γ * uStar ^ (p.m + p.γ - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (ne_of_gt p.hν) (ne_of_gt p.hγ)) hpowu
  have hmulden :
      (1 + vStar) ^ p.β * (p.μ + lambdaN) ≠ 0 :=
    mul_ne_zero hpowv (ne_of_gt (by linarith [p.hμ, hlambda]))
  field_simp [hmulcoeff, hmulden, hpowv, hpowu, ne_of_gt hlambda,
    ne_of_gt p.hν, ne_of_gt p.hγ]

lemma sigmaCriticalChiPaperFormula_pos
    (p : CM2Params) {uStar vStar lambdaN : ℝ}
    (huStar : 0 < uStar) (hvStar : 0 ≤ vStar) (hlambda : 0 < lambdaN) :
    0 < sigmaCriticalChiPaperFormula p uStar vStar lambdaN := by
  rw [← sigmaCriticalChi_eq_paperFormula p huStar hvStar hlambda]
  exact sigmaCriticalChi_pos p huStar hvStar hlambda

lemma paperCriticalSensitivitySet_bddBelow
    (S : SpectralData) (p : CM2Params) (H : HasNeumannSpectrum S)
    {uStar vStar : ℝ} (huStar : 0 < uStar) (hvStar : 0 ≤ vStar) :
    BddBelow (paperCriticalSensitivitySet S p uStar vStar) := by
  refine ⟨0, ?_⟩
  rintro χ ⟨n, hn, rfl⟩
  exact (sigmaCriticalChiPaperFormula_pos p huStar hvStar
    (H.eigenvalue_pos_of_ne_zero n hn)).le

lemma sigmaCriticalChiPaperFormula_mode_one_mem
    (S : SpectralData) (p : CM2Params) (uStar vStar : ℝ) :
    sigmaCriticalChiPaperFormula p uStar vStar (S.eigenvalue 1) ∈
      paperCriticalSensitivitySet S p uStar vStar :=
  ⟨1, by norm_num, rfl⟩

lemma paperCriticalSensitivity_le_mode_one
    (S : SpectralData) (p : CM2Params) (H : HasNeumannSpectrum S)
    {uStar vStar : ℝ} (huStar : 0 < uStar) (hvStar : 0 ≤ vStar) :
    paperCriticalSensitivity S p uStar vStar ≤
      sigmaCriticalChiPaperFormula p uStar vStar (S.eigenvalue 1) := by
  unfold paperCriticalSensitivity
  exact csInf_le (paperCriticalSensitivitySet_bddBelow S p H huStar hvStar)
    (sigmaCriticalChiPaperFormula_mode_one_mem S p uStar vStar)

lemma paperCriticalSensitivity_positiveEquilibrium_le_mode_one
    (S : SpectralData) (p : CM2Params) (H : HasNeumannSpectrum S)
    (ha : 0 < p.a) (hb : 0 < p.b) :
    paperCriticalSensitivity S p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 ≤
      sigmaCriticalChiPaperFormula p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2
        (S.eigenvalue 1) :=
  paperCriticalSensitivity_le_mode_one S p H
    (positiveEquilibrium_fst_pos p ⟨ha, hb⟩)
    (positiveEquilibrium_snd_pos p ⟨ha, hb⟩).le

lemma paperCriticalSensitivity_minimalEquilibrium_le_mode_one
    (S : SpectralData) (p : CM2Params) (H : HasNeumannSpectrum S)
    {uStar : ℝ} (huStar : 0 < uStar) :
    paperCriticalSensitivity S p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 ≤
      sigmaCriticalChiPaperFormula p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2
        (S.eigenvalue 1) :=
  paperCriticalSensitivity_le_mode_one S p H
    (by simpa [minimalEquilibrium_fst_eq] using huStar)
    (minimalEquilibrium_snd_pos p huStar).le

lemma paperCriticalSensitivity_lt_chi_of_mode_one_lt_chi
    (S : SpectralData) (p : CM2Params) (H : HasNeumannSpectrum S)
    {uStar vStar : ℝ} (huStar : 0 < uStar) (hvStar : 0 ≤ vStar)
    (hχ :
      sigmaCriticalChiPaperFormula p uStar vStar (S.eigenvalue 1) < p.χ₀) :
    paperCriticalSensitivity S p uStar vStar < p.χ₀ :=
  lt_of_le_of_lt
    (paperCriticalSensitivity_le_mode_one S p H huStar hvStar) hχ

lemma paperCriticalSensitivity_positiveEquilibrium_lt_chi_of_mode_one_lt_chi
    (S : SpectralData) (p : CM2Params) (H : HasNeumannSpectrum S)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ :
      sigmaCriticalChiPaperFormula p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2
          (S.eigenvalue 1) <
        p.χ₀) :
    paperCriticalSensitivity S p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 <
      p.χ₀ :=
  paperCriticalSensitivity_lt_chi_of_mode_one_lt_chi S p H
    (positiveEquilibrium_fst_pos p ⟨ha, hb⟩)
    (positiveEquilibrium_snd_pos p ⟨ha, hb⟩).le hχ

lemma paperCriticalSensitivity_minimalEquilibrium_lt_chi_of_mode_one_lt_chi
    (S : SpectralData) (p : CM2Params) (H : HasNeumannSpectrum S)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hχ :
      sigmaCriticalChiPaperFormula p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2
          (S.eigenvalue 1) <
        p.χ₀) :
    paperCriticalSensitivity S p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 <
      p.χ₀ :=
  paperCriticalSensitivity_lt_chi_of_mode_one_lt_chi S p H
    (by simpa [minimalEquilibrium_fst_eq] using huStar)
    (minimalEquilibrium_snd_pos p huStar).le hχ

lemma paperCriticalSensitivity_nonneg
    (S : SpectralData) (p : CM2Params) (H : HasNeumannSpectrum S)
    {uStar vStar : ℝ} (huStar : 0 < uStar) (hvStar : 0 ≤ vStar) :
    0 ≤ paperCriticalSensitivity S p uStar vStar := by
  unfold paperCriticalSensitivity
  refine le_csInf (paperCriticalSensitivitySet_nonempty S p uStar vStar) ?_
  rintro χ ⟨n, hn, rfl⟩
  exact (sigmaCriticalChiPaperFormula_pos p huStar hvStar
    (H.eigenvalue_pos_of_ne_zero n hn)).le

lemma sigmaCriticalChiPaperFormula_ge_firstNonzero_lower
    (S : SpectralData) (p : CM2Params)
    {uStar vStar : ℝ} (huStar : 0 < uStar) (hvStar : 0 ≤ vStar)
    {lambdaN : ℝ} (hlambda : 0 < lambdaN)
    (hfirst_le : S.firstNonzero ≤ lambdaN) :
    ((1 + vStar) ^ p.β /
        (p.ν * p.γ * uStar ^ (p.m + p.γ - 1))) *
      (p.μ + S.firstNonzero) ≤
        sigmaCriticalChiPaperFormula p uStar vStar lambdaN := by
  unfold sigmaCriticalChiPaperFormula
  let A :=
    (1 + vStar) ^ p.β /
      (p.ν * p.γ * uStar ^ (p.m + p.γ - 1))
  have hA_pos : 0 < A := by
    dsimp [A]
    exact div_pos
      (Real.rpow_pos_of_pos (by linarith : 0 < 1 + vStar) _)
      (mul_pos (mul_pos p.hν p.hγ)
        (Real.rpow_pos_of_pos huStar _))
  have hquad :
      p.μ + S.firstNonzero ≤
        ((lambdaN + p.a * p.α) * (p.μ + lambdaN) / lambdaN) := by
    rw [le_div_iff₀ hlambda]
    have haα_nonneg : 0 ≤ p.a * p.α :=
      mul_nonneg p.ha p.hα.le
    have hmul_left_nonneg : 0 ≤ p.μ + lambdaN := by linarith [p.hμ, hlambda]
    have hleft :
        (p.μ + S.firstNonzero) * lambdaN ≤
          (p.μ + lambdaN) * lambdaN := by
      nlinarith [hfirst_le, hlambda]
    have hright :
        (p.μ + lambdaN) * lambdaN ≤
          (p.μ + lambdaN) * (lambdaN + p.a * p.α) := by
      exact mul_le_mul_of_nonneg_left (by nlinarith [haα_nonneg]) hmul_left_nonneg
    nlinarith [hleft, hright]
  change A * (p.μ + S.firstNonzero) ≤
    A * ((lambdaN + p.a * p.α) * (p.μ + lambdaN) / lambdaN)
  exact mul_le_mul_of_nonneg_left hquad hA_pos.le

/-- The paper critical sensitivity is bounded below by the first nonzero
Neumann mode contribution.  This is the explicit estimate used to prove
positivity of `χ*`, exposed as a reusable theorem rather than hidden inside a
constants package field. -/
lemma paperCriticalSensitivity_ge_firstNonzero_lower
    (S : SpectralData) (p : CM2Params) (H : HasNeumannSpectrum S)
    {uStar vStar : ℝ} (huStar : 0 < uStar) (hvStar : 0 ≤ vStar) :
    ((1 + vStar) ^ p.β /
        (p.ν * p.γ * uStar ^ (p.m + p.γ - 1))) *
      (p.μ + S.firstNonzero) ≤
        paperCriticalSensitivity S p uStar vStar := by
  unfold paperCriticalSensitivity
  refine le_csInf (paperCriticalSensitivitySet_nonempty S p uStar vStar) ?_
  rintro χ ⟨n, hn, rfl⟩
  exact sigmaCriticalChiPaperFormula_ge_firstNonzero_lower
    S p huStar hvStar
    (H.eigenvalue_pos_of_ne_zero n hn)
    (H.firstNonzero_le_eigenvalue n hn)

/-- First-mode lower bound for the critical sensitivity at the positive
constant equilibrium. -/
lemma paperCriticalSensitivity_positiveEquilibrium_ge_firstNonzero_lower
    (S : SpectralData) (p : CM2Params) (H : HasNeumannSpectrum S)
    (ha : 0 < p.a) (hb : 0 < p.b) :
    ((1 + (positiveEquilibrium p ⟨ha, hb⟩).2) ^ p.β /
        (p.ν * p.γ *
          (positiveEquilibrium p ⟨ha, hb⟩).1 ^ (p.m + p.γ - 1))) *
      (p.μ + S.firstNonzero) ≤
        paperCriticalSensitivity S p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  paperCriticalSensitivity_ge_firstNonzero_lower S p H
    (positiveEquilibrium_fst_pos p ⟨ha, hb⟩)
    (positiveEquilibrium_snd_pos p ⟨ha, hb⟩).le

/-- First-mode lower bound for the critical sensitivity at the minimal
constant equilibrium. -/
lemma paperCriticalSensitivity_minimalEquilibrium_ge_firstNonzero_lower
    (S : SpectralData) (p : CM2Params) (H : HasNeumannSpectrum S)
    {uStar : ℝ} (huStar : 0 < uStar) :
    ((1 + (minimalEquilibrium p uStar).2) ^ p.β /
        (p.ν * p.γ *
          (minimalEquilibrium p uStar).1 ^ (p.m + p.γ - 1))) *
      (p.μ + S.firstNonzero) ≤
        paperCriticalSensitivity S p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2 :=
  paperCriticalSensitivity_ge_firstNonzero_lower S p H
    (by simpa [minimalEquilibrium_fst_eq] using huStar)
    (minimalEquilibrium_snd_pos p huStar).le

lemma paperCriticalSensitivity_pos
    (S : SpectralData) (p : CM2Params) (H : HasNeumannSpectrum S)
    {uStar vStar : ℝ} (huStar : 0 < uStar) (hvStar : 0 ≤ vStar) :
    0 < paperCriticalSensitivity S p uStar vStar := by
  let lower :=
    ((1 + vStar) ^ p.β /
      (p.ν * p.γ * uStar ^ (p.m + p.γ - 1))) *
      (p.μ + S.firstNonzero)
  have hlower_pos : 0 < lower := by
    dsimp [lower]
    exact mul_pos
      (div_pos
        (Real.rpow_pos_of_pos (by linarith : 0 < 1 + vStar) _)
        (mul_pos (mul_pos p.hν p.hγ)
          (Real.rpow_pos_of_pos huStar _)))
      (by linarith [p.hμ, H.firstNonzero_pos])
  have hlower_le : lower ≤ paperCriticalSensitivity S p uStar vStar := by
    exact paperCriticalSensitivity_ge_firstNonzero_lower S p H huStar hvStar
  exact lt_of_lt_of_le hlower_pos hlower_le

/-- Positivity of the paper critical sensitivity at the positive constant
equilibrium, proved from the explicit spectral formula. -/
lemma paperCriticalSensitivity_positiveEquilibrium_pos
    (S : SpectralData) (p : CM2Params) (H : HasNeumannSpectrum S)
    (ha : 0 < p.a) (hb : 0 < p.b) :
    0 < paperCriticalSensitivity S p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  paperCriticalSensitivity_pos S p H
    (positiveEquilibrium_fst_pos p ⟨ha, hb⟩)
    (positiveEquilibrium_snd_pos p ⟨ha, hb⟩).le

/-- Nonnegativity of the paper critical sensitivity at the positive constant
equilibrium. -/
lemma paperCriticalSensitivity_positiveEquilibrium_nonneg
    (S : SpectralData) (p : CM2Params) (H : HasNeumannSpectrum S)
    (ha : 0 < p.a) (hb : 0 < p.b) :
    0 ≤ paperCriticalSensitivity S p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  (paperCriticalSensitivity_positiveEquilibrium_pos S p H ha hb).le

/-- Positivity of the paper critical sensitivity at the minimal constant
equilibrium, proved from the explicit spectral formula. -/
lemma paperCriticalSensitivity_minimalEquilibrium_pos
    (S : SpectralData) (p : CM2Params) (H : HasNeumannSpectrum S)
    {uStar : ℝ} (huStar : 0 < uStar) :
    0 < paperCriticalSensitivity S p
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 :=
  paperCriticalSensitivity_pos S p H
    (by simpa [minimalEquilibrium_fst_eq] using huStar)
    (minimalEquilibrium_snd_pos p huStar).le

/-- Nonnegativity of the paper critical sensitivity at the minimal constant
equilibrium. -/
lemma paperCriticalSensitivity_minimalEquilibrium_nonneg
    (S : SpectralData) (p : CM2Params) (H : HasNeumannSpectrum S)
    {uStar : ℝ} (huStar : 0 < uStar) :
    0 ≤ paperCriticalSensitivity S p
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 :=
  (paperCriticalSensitivity_minimalEquilibrium_pos S p H huStar).le

lemma sigma_eq_chi_sub_critical_mul_coeff
    (p : CM2Params) (uStar vStar lambdaN : ℝ)
    (hcoeff :
      sigmaChemCoefficient p uStar vStar lambdaN ≠ 0) :
    sigma p uStar vStar lambdaN =
      (p.χ₀ - sigmaCriticalChi p uStar vStar lambdaN) *
        sigmaChemCoefficient p uStar vStar lambdaN := by
  rw [sigma_eq_base_add_chi_coeff]
  unfold sigmaBase sigmaCriticalChi
  field_simp [hcoeff]
  ring

lemma sigma_pos_of_sigmaCriticalChi_lt_chi
    (p : CM2Params) {uStar vStar lambdaN : ℝ}
    (hcoeff : 0 < sigmaChemCoefficient p uStar vStar lambdaN)
    (hχ : sigmaCriticalChi p uStar vStar lambdaN < p.χ₀) :
    0 < sigma p uStar vStar lambdaN := by
  rw [sigma_eq_chi_sub_critical_mul_coeff p uStar vStar lambdaN
    (ne_of_gt hcoeff)]
  exact mul_pos (sub_pos.mpr hχ) hcoeff

lemma sigma_neg_of_chi_lt_sigmaCriticalChi
    (p : CM2Params) {uStar vStar lambdaN : ℝ}
    (hcoeff : 0 < sigmaChemCoefficient p uStar vStar lambdaN)
    (hχ : p.χ₀ < sigmaCriticalChi p uStar vStar lambdaN) :
    sigma p uStar vStar lambdaN < 0 := by
  rw [sigma_eq_chi_sub_critical_mul_coeff p uStar vStar lambdaN
    (ne_of_gt hcoeff)]
  exact mul_neg_of_neg_of_pos (sub_neg.mpr hχ) hcoeff

def LinearlyStable
    (S : SpectralData) (p : CM2Params) (uStar vStar : ℝ) : Prop :=
  ∀ n : ℕ, n ≠ 0 → sigma p uStar vStar (S.eigenvalue n) < 0

def LinearlyUnstable
    (S : SpectralData) (p : CM2Params) (uStar vStar : ℝ) : Prop :=
  ∃ n : ℕ, n ≠ 0 ∧ 0 < sigma p uStar vStar (S.eigenvalue n)

/-- The sensitivity is below every nonzero-mode linear critical threshold. -/
def BelowAllLinearCriticalThresholds
    (S : SpectralData) (p : CM2Params) (uStar vStar : ℝ) : Prop :=
  ∀ n : ℕ, n ≠ 0 →
    p.χ₀ < sigmaCriticalChi p uStar vStar (S.eigenvalue n)

/-- The sensitivity is above at least one nonzero-mode linear critical threshold. -/
def AboveSomeLinearCriticalThreshold
    (S : SpectralData) (p : CM2Params) (uStar vStar : ℝ) : Prop :=
  ∃ n : ℕ, n ≠ 0 ∧
    sigmaCriticalChi p uStar vStar (S.eigenvalue n) < p.χ₀

lemma LinearlyStable.at
    {S : SpectralData} {p : CM2Params} {uStar vStar : ℝ}
    (hstable : LinearlyStable S p uStar vStar)
    {n : ℕ} (hn : n ≠ 0) :
    sigma p uStar vStar (S.eigenvalue n) < 0 :=
  hstable n hn

lemma LinearlyUnstable.exists_mode
    {S : SpectralData} {p : CM2Params} {uStar vStar : ℝ}
    (hunstable : LinearlyUnstable S p uStar vStar) :
    ∃ n : ℕ, n ≠ 0 ∧ 0 < sigma p uStar vStar (S.eigenvalue n) :=
  hunstable

lemma BelowAllLinearCriticalThresholds.at
    {S : SpectralData} {p : CM2Params} {uStar vStar : ℝ}
    (hbelow : BelowAllLinearCriticalThresholds S p uStar vStar)
    {n : ℕ} (hn : n ≠ 0) :
    p.χ₀ < sigmaCriticalChi p uStar vStar (S.eigenvalue n) :=
  hbelow n hn

lemma AboveSomeLinearCriticalThreshold.exists_mode
    {S : SpectralData} {p : CM2Params} {uStar vStar : ℝ}
    (habove : AboveSomeLinearCriticalThreshold S p uStar vStar) :
    ∃ n : ℕ, n ≠ 0 ∧
      sigmaCriticalChi p uStar vStar (S.eigenvalue n) < p.χ₀ :=
  habove

lemma LinearlyStable.not_linearlyUnstable
    {S : SpectralData} {p : CM2Params} {uStar vStar : ℝ}
    (hstable : LinearlyStable S p uStar vStar) :
    ¬ LinearlyUnstable S p uStar vStar := by
  rintro ⟨n, hn, hpos⟩
  have hneg := hstable n hn
  linarith

lemma LinearlyUnstable.not_linearlyStable
    {S : SpectralData} {p : CM2Params} {uStar vStar : ℝ}
    (hunstable : LinearlyUnstable S p uStar vStar) :
    ¬ LinearlyStable S p uStar vStar := by
  intro hstable
  exact hstable.not_linearlyUnstable hunstable

lemma AboveSomeLinearCriticalThreshold.not_belowAll
    {S : SpectralData} {p : CM2Params} {uStar vStar : ℝ}
    (habove : AboveSomeLinearCriticalThreshold S p uStar vStar) :
    ¬ BelowAllLinearCriticalThresholds S p uStar vStar := by
  rintro hbelow
  rcases habove with ⟨n, hn, habove_n⟩
  have hbelow_n := hbelow n hn
  linarith

lemma BelowAllLinearCriticalThresholds.not_aboveSome
    {S : SpectralData} {p : CM2Params} {uStar vStar : ℝ}
    (hbelow : BelowAllLinearCriticalThresholds S p uStar vStar) :
    ¬ AboveSomeLinearCriticalThreshold S p uStar vStar := by
  intro habove
  exact habove.not_belowAll hbelow

lemma BelowAllLinearCriticalThresholds_of_chi_nonpos
    (S : SpectralData) (p : CM2Params) (H : HasNeumannSpectrum S)
    {uStar vStar : ℝ}
    (hχ : p.χ₀ ≤ 0) (huStar : 0 < uStar) (hvStar : 0 ≤ vStar) :
    BelowAllLinearCriticalThresholds S p uStar vStar := by
  intro n hn
  have hcrit : 0 < sigmaCriticalChi p uStar vStar (S.eigenvalue n) :=
    sigmaCriticalChi_pos p huStar hvStar
      (H.eigenvalue_pos_of_ne_zero n hn)
  exact lt_of_le_of_lt hχ hcrit

lemma BelowAllLinearCriticalThresholds_of_chi_lt_paperCriticalSensitivity
    (S : SpectralData) (p : CM2Params) (H : HasNeumannSpectrum S)
    {uStar vStar : ℝ}
    (hχ : p.χ₀ < paperCriticalSensitivity S p uStar vStar)
    (huStar : 0 < uStar) (hvStar : 0 ≤ vStar) :
    BelowAllLinearCriticalThresholds S p uStar vStar := by
  intro n hn
  have hbdd :
      BddBelow (paperCriticalSensitivitySet S p uStar vStar) :=
    paperCriticalSensitivitySet_bddBelow S p H huStar hvStar
  have hmem :
      sigmaCriticalChiPaperFormula p uStar vStar (S.eigenvalue n) ∈
        paperCriticalSensitivitySet S p uStar vStar :=
    ⟨n, hn, rfl⟩
  have hinf_le :
      paperCriticalSensitivity S p uStar vStar ≤
        sigmaCriticalChiPaperFormula p uStar vStar (S.eigenvalue n) := by
    unfold paperCriticalSensitivity
    exact csInf_le hbdd hmem
  have hχ_mode :
      p.χ₀ <
        sigmaCriticalChiPaperFormula p uStar vStar (S.eigenvalue n) :=
    lt_of_lt_of_le hχ hinf_le
  rw [sigmaCriticalChi_eq_paperFormula p huStar hvStar
    (H.eigenvalue_pos_of_ne_zero n hn)]
  exact hχ_mode

lemma AboveSomeLinearCriticalThreshold_of_paperCriticalSensitivity_lt_chi
    (S : SpectralData) (p : CM2Params) (H : HasNeumannSpectrum S)
    {uStar vStar : ℝ}
    (hχ : paperCriticalSensitivity S p uStar vStar < p.χ₀)
    (huStar : 0 < uStar) (hvStar : 0 ≤ vStar) :
    AboveSomeLinearCriticalThreshold S p uStar vStar := by
  have hbdd :
      BddBelow (paperCriticalSensitivitySet S p uStar vStar) :=
    paperCriticalSensitivitySet_bddBelow S p H huStar hvStar
  have hne :
      (paperCriticalSensitivitySet S p uStar vStar).Nonempty :=
    paperCriticalSensitivitySet_nonempty S p uStar vStar
  unfold paperCriticalSensitivity at hχ
  rcases (csInf_lt_iff hbdd hne).mp hχ with
    ⟨χmode, ⟨n, hn, hχmode_eq⟩, hχmode_lt⟩
  refine ⟨n, hn, ?_⟩
  rw [sigmaCriticalChi_eq_paperFormula p huStar hvStar
    (H.eigenvalue_pos_of_ne_zero n hn)]
  rwa [hχmode_eq] at hχmode_lt

structure StabilityNorms (D : BoundedDomainData) where
  c1Distance : (D.Point → ℝ) → (D.Point → ℝ) → ℝ
  xpSigmaDistance : ℝ → ℝ → (D.Point → ℝ) → (D.Point → ℝ) → ℝ
  initialContinuity :
    ∀ p : CM2Params, ∀ uConst > 0,
      ∀ sigma pNorm eps, 1 / 2 < sigma → 1 < pNorm → 0 < eps →
        ∃ delta > 0, ∃ T0 > 0, ∃ T > T0,
          ∀ u₀ : D.Point → ℝ,
          ∀ u v uConstSol vConstSol : ℝ → D.Point → ℝ,
            PositiveInitialDatum D u₀ →
            PositiveInitialDatum D (fun _ : D.Point => uConst) →
            D.supNorm (fun x => u₀ x - uConst) ≤ delta →
            IsPaper2ClassicalSolution D p T u v →
            InitialTrace D u₀ u →
            IsPaper2ClassicalSolution D p T uConstSol vConstSol →
            InitialTrace D (fun _ : D.Point => uConst) uConstSol →
              xpSigmaDistance sigma pNorm (u T0) (uConstSol T0) ≤ eps
  sectorialLocalExponential :
    ∀ p : CM2Params, ∀ S : SpectralData,
      ∀ sigma pNorm uStar vStar,
        1 / 2 < sigma → sigma < 1 → 1 < pNorm →
        LinearlyStable S p uStar vStar →
          ∃ eps > 0, ∃ C > 0, ∃ rate > 0,
            ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
              xpSigmaDistance sigma pNorm u₀ (fun _ => uStar) ≤ eps →
                ∀ u v : ℝ → D.Point → ℝ,
                  IsPaper2GlobalClassicalSolution D p u v →
                  InitialTrace D u₀ u →
                    ∀ t, 0 ≤ t →
                      c1Distance (u t) (fun _ => uStar) +
                        c1Distance (v t) (fun _ => vStar) ≤
                          C * Real.exp (-rate * t)
  negativeSensitivityGlobalStability :
    ∀ p : CM2Params, p.χ₀ ≤ 0 → 1 ≤ p.m →
      (∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        (∀ u v : ℝ → D.Point → ℝ,
          PositiveGlobalBoundedSolution D p u v →
            UniformConvergesInSup D u eq.1) ∧
        ∃ A > 0, ∃ rate > 0,
          ∀ u v : ℝ → D.Point → ℝ,
            PositiveGlobalBoundedSolution D p u v →
              ∀ t, 0 ≤ t →
                c1Distance (u t) (fun _ => eq.1) +
                  c1Distance (v t) (fun _ => eq.2) ≤
                    A * Real.exp (-rate * t)) ∧
      (p.a = 0 → p.b = 0 →
        ∀ uStar > 0,
          let eq := minimalEquilibrium p uStar
          (∀ u v : ℝ → D.Point → ℝ,
            PositiveGlobalBoundedSolution D p u v →
            HasInitialMass D u uStar →
              UniformConvergesInSup D u eq.1) ∧
          ∃ A > 0, ∃ rate > 0,
            ∀ u v : ℝ → D.Point → ℝ,
              PositiveGlobalBoundedSolution D p u v →
              HasInitialMass D u uStar →
                ∀ t, 0 ≤ t →
                  c1Distance (u t) (fun _ => eq.1) +
                    c1Distance (v t) (fun _ => eq.2) ≤
                      A * Real.exp (-rate * t))

structure CompactnessData (D : BoundedDomainData) where
  locallyConverges :
    (ℕ → ℝ → D.Point → ℝ) → (ℝ → D.Point → ℝ) → Prop
  upperEnvelope : (D.Point → ℝ) → ℝ
  timeTranslateCompactness :
    ∀ p : CM2Params, 1 ≤ p.m → 0 < p.γ →
      ∀ u v : ℝ → D.Point → ℝ,
        PositiveGlobalBoundedSolution D p u v →
          ∀ times : ℕ → ℝ, Tendsto times atTop atTop →
            ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
            ∃ uInf vInf : ℝ → D.Point → ℝ,
              locallyConverges (fun n t x => u (t + times (subseq n)) x) uInf ∧
              locallyConverges (fun n t x => v (t + times (subseq n)) x) vInf ∧
              ∀ T > 0, IsPaper2ClassicalSolution D p T
                (fun t x => uInf (t - T / 2) x)
                (fun t x => vInf (t - T / 2) x)
  upperEnvelopeMonotonicity :
    ∀ p : CM2Params, ∀ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v →
        (p.χ₀ ≤ 0 → 0 < p.a → 0 < p.b →
          ∀ t₀, 0 < t₀ →
            (p.a / p.b) ^ (1 / p.α) < upperEnvelope (u t₀) →
            ∀ t₁ t₂, 0 < t₁ → t₁ ≤ t₂ → t₂ ≤ t₀ →
              upperEnvelope (u t₂) ≤ upperEnvelope (u t₁)) ∧
        (p.χ₀ ≤ 0 → p.a = 0 → p.b = 0 →
          ∀ t₁ t₂, 0 < t₁ → t₁ ≤ t₂ →
            upperEnvelope (u t₂) ≤ upperEnvelope (u t₁))
  neumannResolventGradientBound :
    (mu nu : ℝ) → (D.Point → ℝ) → ℝ → Prop
  neumannResolventGradientBound_exists :
    ∃ M0 > 0, ∀ mu nu : ℝ, ∀ f : D.Point → ℝ,
      0 < mu → 0 < nu →
        neumannResolventGradientBound mu nu f M0

def EntireClassicalSolution
    (D : BoundedDomainData) (p : CM2Params)
    (u v : ℝ → D.Point → ℝ) : Prop :=
  ∀ T > 0, IsPaper2ClassicalSolution D p T
    (fun t x => u (t - T / 2) x)
    (fun t x => v (t - T / 2) x)

def UniformRegularityConclusion
    (D : BoundedDomainData) (_p : CM2Params)
    (u v : ℝ → D.Point → ℝ) : Prop :=
  ∀ T > 0, D.classicalRegularity T u v

lemma EntireClassicalSolution.on_window
    {D : BoundedDomainData} {p : CM2Params}
    {u v : ℝ → D.Point → ℝ}
    (h : EntireClassicalSolution D p u v)
    {T : ℝ} (hT : 0 < T) :
    IsPaper2ClassicalSolution D p T
      (fun t x => u (t - T / 2) x)
      (fun t x => v (t - T / 2) x) :=
  h T hT

lemma UniformRegularityConclusion.regular
    {D : BoundedDomainData} {p : CM2Params}
    {u v : ℝ → D.Point → ℝ}
    (h : UniformRegularityConclusion D p u v)
    {T : ℝ} (hT : 0 < T) :
    D.classicalRegularity T u v :=
  h T hT

def TimeTranslateCompactnessConclusion
    (D : BoundedDomainData) (p : CM2Params) (K : CompactnessData D)
    (u v : ℝ → D.Point → ℝ) : Prop :=
  ∀ times : ℕ → ℝ, Tendsto times atTop atTop →
    ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
    ∃ uInf vInf : ℝ → D.Point → ℝ,
      K.locallyConverges (fun n t x => u (t + times (subseq n)) x) uInf ∧
      K.locallyConverges (fun n t x => v (t + times (subseq n)) x) vInf ∧
      EntireClassicalSolution D p uInf vInf

lemma TimeTranslateCompactnessConclusion.subsequence
    {D : BoundedDomainData} {p : CM2Params} {K : CompactnessData D}
    {u v : ℝ → D.Point → ℝ}
    (h : TimeTranslateCompactnessConclusion D p K u v)
    {times : ℕ → ℝ} (htimes : Tendsto times atTop atTop) :
    ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
    ∃ uInf vInf : ℝ → D.Point → ℝ,
      K.locallyConverges (fun n t x => u (t + times (subseq n)) x) uInf ∧
      K.locallyConverges (fun n t x => v (t + times (subseq n)) x) vInf ∧
      EntireClassicalSolution D p uInf vInf :=
  h times htimes

lemma TimeTranslateCompactnessConclusion.entire_limit
    {D : BoundedDomainData} {p : CM2Params} {K : CompactnessData D}
    {u v : ℝ → D.Point → ℝ}
    (h : TimeTranslateCompactnessConclusion D p K u v)
    {times : ℕ → ℝ} (htimes : Tendsto times atTop atTop) :
    ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
    ∃ uInf vInf : ℝ → D.Point → ℝ,
      EntireClassicalSolution D p uInf vInf :=
  by
    rcases h.subsequence htimes with
      ⟨subseq, hsubseq, uInf, vInf, _hu, _hv, hentire⟩
    exact ⟨subseq, hsubseq, uInf, vInf, hentire⟩

def InitialContinuityConclusion
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (uConst : ℝ) : Prop :=
  ∀ sigma pNorm eps, 1 / 2 < sigma → 1 < pNorm → 0 < eps →
    ∃ delta > 0, ∃ T0 > 0, ∃ T > T0,
      ∀ u₀ : D.Point → ℝ,
      ∀ u v uConstSol vConstSol : ℝ → D.Point → ℝ,
        PositiveInitialDatum D u₀ →
        PositiveInitialDatum D (fun _ : D.Point => uConst) →
        D.supNorm (fun x => u₀ x - uConst) ≤ delta →
        IsPaper2ClassicalSolution D p T u v →
        InitialTrace D u₀ u →
        IsPaper2ClassicalSolution D p T uConstSol vConstSol →
        InitialTrace D (fun _ : D.Point => uConst) uConstSol →
          N.xpSigmaDistance sigma pNorm (u T0) (uConstSol T0) ≤ eps

lemma InitialContinuityConclusion.data
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {uConst sigma pNorm eps : ℝ}
    (h : InitialContinuityConclusion D p N uConst)
    (hsigma : 1 / 2 < sigma) (hpNorm : 1 < pNorm) (heps : 0 < eps) :
    ∃ delta > 0, ∃ T0 > 0, ∃ T > T0,
      ∀ u₀ : D.Point → ℝ,
      ∀ u v uConstSol vConstSol : ℝ → D.Point → ℝ,
        PositiveInitialDatum D u₀ →
        PositiveInitialDatum D (fun _ : D.Point => uConst) →
        D.supNorm (fun x => u₀ x - uConst) ≤ delta →
        IsPaper2ClassicalSolution D p T u v →
        InitialTrace D u₀ u →
        IsPaper2ClassicalSolution D p T uConstSol vConstSol →
        InitialTrace D (fun _ : D.Point => uConst) uConstSol →
          N.xpSigmaDistance sigma pNorm (u T0) (uConstSol T0) ≤ eps :=
  h sigma pNorm eps hsigma hpNorm heps

def UpperEnvelopeMonotonicityConclusion
    (D : BoundedDomainData) (p : CM2Params) (K : CompactnessData D)
    (u : ℝ → D.Point → ℝ) : Prop :=
  (p.χ₀ ≤ 0 → 0 < p.a → 0 < p.b →
    ∀ t₀, 0 < t₀ →
      (p.a / p.b) ^ (1 / p.α) < K.upperEnvelope (u t₀) →
      ∀ t₁ t₂, 0 < t₁ → t₁ ≤ t₂ → t₂ ≤ t₀ →
        K.upperEnvelope (u t₂) ≤ K.upperEnvelope (u t₁)) ∧
  (p.χ₀ ≤ 0 → p.a = 0 → p.b = 0 →
    ∀ t₁ t₂, 0 < t₁ → t₁ ≤ t₂ →
      K.upperEnvelope (u t₂) ≤ K.upperEnvelope (u t₁))

lemma UpperEnvelopeMonotonicityConclusion.nonminimal_bound
    {D : BoundedDomainData} {p : CM2Params} {K : CompactnessData D}
    {u : ℝ → D.Point → ℝ}
    (h : UpperEnvelopeMonotonicityConclusion D p K u)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    {t₀ t₁ t₂ : ℝ}
    (ht₀ : 0 < t₀)
    (hlarge : (p.a / p.b) ^ (1 / p.α) < K.upperEnvelope (u t₀))
    (ht₁ : 0 < t₁) (h12 : t₁ ≤ t₂) (h2₀ : t₂ ≤ t₀) :
    K.upperEnvelope (u t₂) ≤ K.upperEnvelope (u t₁) :=
  h.1 hχ ha hb t₀ ht₀ hlarge t₁ t₂ ht₁ h12 h2₀

lemma UpperEnvelopeMonotonicityConclusion.minimal_bound
    {D : BoundedDomainData} {p : CM2Params} {K : CompactnessData D}
    {u : ℝ → D.Point → ℝ}
    (h : UpperEnvelopeMonotonicityConclusion D p K u)
    (hχ : p.χ₀ ≤ 0) (ha : p.a = 0) (hb : p.b = 0)
    {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (h12 : t₁ ≤ t₂) :
    K.upperEnvelope (u t₂) ≤ K.upperEnvelope (u t₁) :=
  h.2 hχ ha hb t₁ t₂ ht₁ h12

def ExponentialC1Convergence
    (D : BoundedDomainData) (N : StabilityNorms D)
    (u v : ℝ → D.Point → ℝ) (uStar vStar : ℝ) : Prop :=
  ∃ C > 0, ∃ rate > 0, ∀ t, 0 ≤ t →
    N.c1Distance (u t) (fun _ => uStar) +
      N.c1Distance (v t) (fun _ => vStar) ≤ C * Real.exp (-rate * t)

def ExponentialC1ConvergenceWith
    (D : BoundedDomainData) (N : StabilityNorms D)
    (u v : ℝ → D.Point → ℝ) (uStar vStar C rate : ℝ) : Prop :=
  ∀ t, 0 ≤ t →
    N.c1Distance (u t) (fun _ => uStar) +
      N.c1Distance (v t) (fun _ => vStar) ≤ C * Real.exp (-rate * t)

lemma ExponentialC1ConvergenceWith.bound_at
    {D : BoundedDomainData} {N : StabilityNorms D}
    {u v : ℝ → D.Point → ℝ} {uStar vStar C rate : ℝ}
    (h : ExponentialC1ConvergenceWith D N u v uStar vStar C rate)
    {t : ℝ} (ht : 0 ≤ t) :
    N.c1Distance (u t) (fun _ => uStar) +
      N.c1Distance (v t) (fun _ => vStar) ≤ C * Real.exp (-rate * t) :=
  h t ht

lemma ExponentialC1Convergence.bound
    {D : BoundedDomainData} {N : StabilityNorms D}
    {u v : ℝ → D.Point → ℝ} {uStar vStar : ℝ}
    (h : ExponentialC1Convergence D N u v uStar vStar) :
    ∃ C > 0, ∃ rate > 0,
      ExponentialC1ConvergenceWith D N u v uStar vStar C rate :=
  h

lemma ExponentialC1ConvergenceWith.exists
    {D : BoundedDomainData} {N : StabilityNorms D}
    {u v : ℝ → D.Point → ℝ} {uStar vStar C rate : ℝ}
    (hC : 0 < C) (hrate : 0 < rate)
    (h :
      ExponentialC1ConvergenceWith D N u v uStar vStar C rate) :
    ExponentialC1Convergence D N u v uStar vStar :=
  ⟨C, hC, rate, hrate, h⟩

def SupCloseToConstant
    (D : BoundedDomainData) (u₀ : D.Point → ℝ) (uStar δ : ℝ) : Prop :=
  D.supNorm (fun x => u₀ x - uStar) < δ

lemma SupCloseToConstant.lt
    {D : BoundedDomainData} {u₀ : D.Point → ℝ} {uStar δ : ℝ}
    (h : SupCloseToConstant D u₀ uStar δ) :
    D.supNorm (fun x => u₀ x - uStar) < δ :=
  h

/-- Local exponential stability from small perturbations in the sup norm.

This is the nonminimal stability package in Paper3 Theorem 2.2. -/
def LocallyExponentiallyStableFromSup
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (uStar vStar : ℝ) : Prop :=
  ∃ δ > 0, ∃ A > 0, ∃ rate > 0,
    ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
      SupCloseToConstant D u₀ uStar δ →
        ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2GlobalClassicalSolution D p u v ∧
          InitialTrace D u₀ u ∧
          ExponentialC1ConvergenceWith D N u v uStar vStar A rate

/-- Local exponential stability for the minimal model, where the perturbation
must preserve the prescribed mass. -/
def MassConstrainedLocallyExponentiallyStableFromSup
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (uStar vStar : ℝ) : Prop :=
  ∃ δ > 0, ∃ A > 0, ∃ rate > 0,
    ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
      SupCloseToConstant D u₀ uStar δ →
      D.integral u₀ = D.volume * uStar →
        ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2GlobalClassicalSolution D p u v ∧
          InitialTrace D u₀ u ∧
          ExponentialC1ConvergenceWith D N u v uStar vStar A rate

lemma LocallyExponentiallyStableFromSup.solution
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {uStar vStar : ℝ}
    (h : LocallyExponentiallyStableFromSup D p N uStar vStar) :
    ∃ δ > 0, ∃ A > 0, ∃ rate > 0,
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        SupCloseToConstant D u₀ uStar δ →
          ∃ u v : ℝ → D.Point → ℝ,
            IsPaper2GlobalClassicalSolution D p u v ∧
            InitialTrace D u₀ u ∧
            ExponentialC1ConvergenceWith D N u v uStar vStar A rate :=
  h

lemma LocallyExponentiallyStableFromSup.exponential_convergence
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {uStar vStar : ℝ}
    (h : LocallyExponentiallyStableFromSup D p N uStar vStar) :
    ∃ δ > 0,
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        SupCloseToConstant D u₀ uStar δ →
          ∃ u v : ℝ → D.Point → ℝ,
            IsPaper2GlobalClassicalSolution D p u v ∧
            InitialTrace D u₀ u ∧
            ExponentialC1Convergence D N u v uStar vStar := by
  rcases h with ⟨δ, hδ, A, hA, rate, hrate, hsol⟩
  refine ⟨δ, hδ, ?_⟩
  intro u₀ hu₀ hclose
  rcases hsol u₀ hu₀ hclose with ⟨u, v, huv, htrace, hexp⟩
  exact ⟨u, v, huv, htrace,
    ExponentialC1ConvergenceWith.exists hA hrate hexp⟩

lemma MassConstrainedLocallyExponentiallyStableFromSup.solution
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {uStar vStar : ℝ}
    (h : MassConstrainedLocallyExponentiallyStableFromSup D p N uStar vStar) :
    ∃ δ > 0, ∃ A > 0, ∃ rate > 0,
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        SupCloseToConstant D u₀ uStar δ →
        D.integral u₀ = D.volume * uStar →
          ∃ u v : ℝ → D.Point → ℝ,
            IsPaper2GlobalClassicalSolution D p u v ∧
            InitialTrace D u₀ u ∧
            ExponentialC1ConvergenceWith D N u v uStar vStar A rate :=
  h

lemma MassConstrainedLocallyExponentiallyStableFromSup.exponential_convergence
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {uStar vStar : ℝ}
    (h : MassConstrainedLocallyExponentiallyStableFromSup D p N uStar vStar) :
    ∃ δ > 0,
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        SupCloseToConstant D u₀ uStar δ →
        D.integral u₀ = D.volume * uStar →
          ∃ u v : ℝ → D.Point → ℝ,
            IsPaper2GlobalClassicalSolution D p u v ∧
            InitialTrace D u₀ u ∧
            ExponentialC1Convergence D N u v uStar vStar := by
  rcases h with ⟨δ, hδ, A, hA, rate, hrate, hsol⟩
  refine ⟨δ, hδ, ?_⟩
  intro u₀ hu₀ hclose hmass
  rcases hsol u₀ hu₀ hclose hmass with ⟨u, v, huv, htrace, hexp⟩
  exact ⟨u, v, huv, htrace,
    ExponentialC1ConvergenceWith.exists hA hrate hexp⟩

def Proposition_1_1 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  Paper2.Proposition_1_1 D p

lemma Proposition_1_1.paper2
    {D : BoundedDomainData} {p : CM2Params}
    (h : Proposition_1_1 D p) :
    Paper2.Proposition_1_1 D p :=
  h

lemma Proposition_1_1.solution
    {D : BoundedDomainData} {p : CM2Params}
    (h : Proposition_1_1 D p)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p Tmax u v ∧
      InitialTrace D u₀ u ∧
      FiniteHorizonAlternative D Tmax u ∧
      (1 ≤ p.m → MGeOneFiniteHorizonAlternative D Tmax u) :=
  h.paper2.solution hu₀

def Proposition_1_2 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  p.χ₀ ≤ 0 → 1 ≤ p.m →
    ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
      ∃ u v : ℝ → D.Point → ℝ,
        IsPaper2GlobalClassicalSolution D p u v ∧
        InitialTrace D u₀ u ∧
        IsPaper2Bounded D u

lemma Proposition_1_2.global_solution
    {D : BoundedDomainData} {p : CM2Params}
    (h : Proposition_1_2 D p)
    (hχ : p.χ₀ ≤ 0) (hm : 1 ≤ p.m)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2Bounded D u :=
  h hχ hm u₀ hu₀

lemma Proposition_1_2.positive_global_solution
    {D : BoundedDomainData} {p : CM2Params}
    (h : Proposition_1_2 D p)
    (hχ : p.χ₀ ≤ 0) (hm : 1 ≤ p.m)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v ∧
      InitialTrace D u₀ u := by
  rcases h.global_solution hχ hm hu₀ with ⟨u, v, hglobal, htrace, hbdd⟩
  exact ⟨u, v,
    PositiveGlobalBoundedSolution.of_global_bounded hglobal hbdd, htrace⟩

lemma Proposition_1_2_of_negativeSensitivityGlobalEventualBound
    (D : BoundedDomainData) (p : CM2Params)
    (h :
      p.χ₀ ≤ 0 → 1 ≤ p.m →
        ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
          ∃ u v : ℝ → D.Point → ℝ,
            IsPaper2GlobalClassicalSolution D p u v ∧
            InitialTrace D u₀ u ∧
            ∃ M : ℝ, ∀ᶠ t in atTop, D.supNorm (u t) ≤ M) :
    Proposition_1_2 D p := by
  intro hχ hm u₀ hu₀
  rcases h hχ hm u₀ hu₀ with ⟨u, v, hglobal, htrace, M, hM⟩
  exact ⟨u, v, hglobal, htrace, ⟨M, hM⟩⟩

def NegativeSensitivityGlobalEventualBound
    (D : BoundedDomainData) (p : CM2Params) : Prop :=
  p.χ₀ ≤ 0 → 1 ≤ p.m →
    ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
      ∃ u v : ℝ → D.Point → ℝ,
        IsPaper2GlobalClassicalSolution D p u v ∧
        InitialTrace D u₀ u ∧
        ∃ M : ℝ, ∀ᶠ t in atTop, D.supNorm (u t) ≤ M

lemma Proposition_1_2.nonminimal_global_bounded_before_solution_of_paper2_theorem_1_1
    {D : BoundedDomainData} {p : CM2Params}
    (h : Paper2.Theorem_1_1 D p)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b) (hm : 1 ≤ p.m)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2BoundedBefore D Tmax u :=
  h.nonminimal_global_bounded_before_solution hχ ha hb hm hu₀

lemma Proposition_1_2.minimal_global_bounded_before_solution_of_paper2_theorem_1_1
    {D : BoundedDomainData} {p : CM2Params}
    (h : Paper2.Theorem_1_1 D p)
    (hχ : p.χ₀ ≤ 0) (ha : p.a = 0) (hb : p.b = 0) (hm : 1 ≤ p.m)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2BoundedBefore D Tmax u :=
  h.minimal_global_bounded_before_solution hχ ha hb hm hu₀

/-- A one-point abstract domain used to show that Paper2 Theorem 1.1's
finite-`Tmax` bound is not enough, under the current abstract API, to imply the
eventual-in-time boundedness required by recalled Paper3 Proposition 1.2. -/
def proposition12CounterDomain : BoundedDomainData where
  Point := Unit
  inside := ∅
  boundary := ∅
  volume := 1
  supNorm := fun f => f ()
  infValue := fun f => f ()
  integral := fun f => f ()
  gradNorm := fun _ _ => 0
  timeDeriv := fun _ _ _ => 0
  laplacian := fun _ _ => 0
  chemotaxisDiv := fun _ _ _ _ => 0
  crossDiffusionEnergyTerm := fun _ _ _ _ => 0
  normalDeriv := fun _ _ => 0
  initialAdmissible := fun u₀ => u₀ () = 0
  classicalRegularity :=
    fun _T u _v => ∀ t, 0 < t → t < _T →
      u t () = if t < 1 then 0 else t

def proposition12CounterParams : CM2Params where
  N := 1
  hN := by norm_num
  α := 1
  γ := 1
  m := 1
  μ := 1
  ν := 1
  χ₀ := 0
  a := 0
  b := 0
  β := 0
  hα := by norm_num
  hγ := by norm_num
  hm := by norm_num
  hμ := by norm_num
  hν := by norm_num
  ha := by norm_num
  hb := by norm_num
  hβ := by norm_num

def proposition12CounterU : ℝ → proposition12CounterDomain.Point → ℝ :=
  fun t _ => if t < 1 then 0 else t

def proposition12CounterV : ℝ → proposition12CounterDomain.Point → ℝ :=
  fun _ _ => 0

lemma proposition12Counter_classical (T : ℝ) (hT : 0 < T) :
    IsPaper2ClassicalSolution proposition12CounterDomain
      proposition12CounterParams T proposition12CounterU proposition12CounterV := by
  refine IsPaper2ClassicalSolution.of_components hT ?_ ?_ ?_ ?_ ?_
  · intro t ht0 htT
    simp [proposition12CounterU]
  · intro t x ht0 htT hx
    cases hx
  · intro t x ht0 htT hx
    cases hx
  · intro t x ht0 htT hx
    cases hx
  · intro t x ht0 htT hx
    cases hx

lemma proposition12Counter_initialTrace
    {u₀ : proposition12CounterDomain.Point → ℝ}
    (hu₀ : PositiveInitialDatum proposition12CounterDomain u₀) :
    InitialTrace proposition12CounterDomain u₀ proposition12CounterU := by
  intro ε hε
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro t ht0 htδ
  have ht1 : t < 1 := by nlinarith
  have hu0 : u₀ () = 0 := hu₀.1
  simp [proposition12CounterDomain, proposition12CounterU, ht1, hu0, hε]

lemma proposition12Counter_paper2_theorem_1_1 :
    Paper2.Theorem_1_1 proposition12CounterDomain
      proposition12CounterParams := by
  intro _hχ
  constructor
  · intro ha _hb
    norm_num [proposition12CounterParams] at ha
  · intro _ha _hb u₀ hu₀
    refine ⟨1 / 2, by norm_num, proposition12CounterU,
      proposition12CounterV, ?_, ?_, ?_, ?_⟩
    · exact proposition12Counter_classical (1 / 2) (by norm_num)
    · exact proposition12Counter_initialTrace hu₀
    · intro t ht0 htT
      have ht1 : t < 1 := by nlinarith
      have hu0 : u₀ () = 0 := hu₀.1
      simp [proposition12CounterDomain, proposition12CounterU, ht1, hu0]
    · intro _hm T hT
      exact proposition12Counter_classical T hT

theorem not_paper2_theorem_1_1_implies_paper3_proposition_1_2 :
    ¬ (∀ D : BoundedDomainData, ∀ p : CM2Params,
        Paper2.Theorem_1_1 D p → Proposition_1_2 D p) := by
  intro h
  have hprop :
      Proposition_1_2 proposition12CounterDomain
        proposition12CounterParams :=
    h proposition12CounterDomain proposition12CounterParams
      proposition12Counter_paper2_theorem_1_1
  have hu₀ :
      PositiveInitialDatum proposition12CounterDomain (fun _ => 0) := by
    constructor
    · rfl
    · intro x hx
      cases hx
  rcases hprop (by norm_num [proposition12CounterParams])
      (by norm_num [proposition12CounterParams]) (fun _ => 0) hu₀ with
    ⟨u, v, hglobal, _htrace, hbdd⟩
  rcases hbdd with ⟨M, hM⟩
  rcases eventually_atTop.mp hM with ⟨T, hT⟩
  let t : ℝ := max T (max M 1) + 1
  have htT : T ≤ t := by
    dsimp [t]
    exact le_trans (le_max_left T (max M 1)) (by linarith)
  have hMt : M < t := by
    dsimp [t]
    have hMmax : M ≤ max M 1 := le_max_left M 1
    have hmax : max M 1 ≤ max T (max M 1) := le_max_right T (max M 1)
    linarith
  have ht0 : 0 < t := by
    dsimp [t]
    have h1max : (1 : ℝ) ≤ max M 1 := le_max_right M 1
    have hmax : max M 1 ≤ max T (max M 1) := le_max_right T (max M 1)
    linarith
  have ht_not_lt_one : ¬ t < 1 := by
    dsimp [t]
    have h1max : (1 : ℝ) ≤ max M 1 := le_max_right M 1
    have hmax : max M 1 ≤ max T (max M 1) := le_max_right T (max M 1)
    linarith
  have hbound : proposition12CounterDomain.supNorm (u t) ≤ M :=
    hT t htT
  have hreg :
      proposition12CounterDomain.classicalRegularity (t + 1) u v :=
    (hglobal.classical (by linarith)).regularity
  have hprofile_raw : u t () = if t < 1 then 0 else t :=
    hreg t ht0 (by linarith)
  have hprofile : u t () = t := by
    simpa [ht_not_lt_one] using hprofile_raw
  have ht_le_M : t ≤ M := by
    simpa [proposition12CounterDomain, hprofile] using hbound
  linarith

def Proposition_1_3
    (D : BoundedDomainData) (p : CM2Params) (C : Paper2Constants p) : Prop :=
  0 < p.a → 0 < p.b → 1 ≤ p.m → StrongLogisticCondition p C →
    ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
      ∃ u v : ℝ → D.Point → ℝ,
        IsPaper2GlobalClassicalSolution D p u v ∧
        InitialTrace D u₀ u ∧
        IsPaper2Bounded D u

lemma Proposition_1_3.global_solution
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Proposition_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hm : 1 ≤ p.m)
    (hcond : StrongLogisticCondition p C)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2Bounded D u :=
  h ha hb hm hcond u₀ hu₀

lemma Proposition_1_3.positive_global_solution
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Proposition_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hm : 1 ≤ p.m)
    (hcond : StrongLogisticCondition p C)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v ∧
      InitialTrace D u₀ u := by
  rcases h.global_solution ha hb hm hcond hu₀ with
    ⟨u, v, hglobal, htrace, hbdd⟩
  exact ⟨u, v,
    PositiveGlobalBoundedSolution.of_global_bounded hglobal hbdd, htrace⟩

lemma Proposition_1_3.of_paper2_theorem_1_3
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Paper2.Theorem_1_3 D p C) :
    Proposition_1_3 D p C := by
  intro ha hb hm hcond u₀ hu₀
  exact h.global_solution ha hb p.hm hcond hm hu₀

lemma Proposition_1_3.global_solution_of_alpha_gt_m_add_gamma_sub_one
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Paper2.Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hm : 1 ≤ p.m)
    (hβ : 0 ≤ p.β) (hα : p.m + p.γ - 1 < p.α)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2Bounded D u :=
  h.global_solution_of_alpha_gt_m_add_gamma_sub_one
    ha hb p.hm hm hβ hα hu₀

lemma Proposition_1_3.global_solution_of_alpha_gt_two_mul_m_add_gamma_sub_two
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Paper2.Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hm : 1 ≤ p.m)
    (hβ : (1 / 2 : ℝ) ≤ p.β)
    (hα : 2 * p.m + p.γ - 2 < p.α)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2Bounded D u :=
  h.global_solution_of_alpha_gt_two_mul_m_add_gamma_sub_two
    ha hb p.hm hm hβ hα hu₀

lemma Proposition_1_3.global_solution_of_critical_m_add_gamma_sub_one_low_dimension
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Paper2.Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hm : 1 ≤ p.m)
    (hβ : 0 ≤ p.β) (hα : p.α = p.m + p.γ - 1)
    (hdim : (p.N : ℝ) * p.α ≤ 2)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2Bounded D u :=
  h.global_solution_of_critical_m_add_gamma_sub_one_low_dimension
    ha hb p.hm hm hβ hα hdim hu₀

lemma Proposition_1_3.global_solution_of_critical_two_mul_m_add_gamma_sub_two_low_dimension
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Paper2.Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hm : 1 ≤ p.m)
    (hβ : (1 / 2 : ℝ) ≤ p.β)
    (hα : p.α = 2 * p.m + p.γ - 2)
    (hdim : (p.N : ℝ) * p.α ≤ 2)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2Bounded D u :=
  h.global_solution_of_critical_two_mul_m_add_gamma_sub_two_low_dimension
    ha hb p.hm hm hβ hα hdim hu₀

lemma Proposition_1_3.global_solution_of_critical_m_add_gamma_sub_one
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Paper2.Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hm : 1 ≤ p.m)
    (hβ : 0 ≤ p.β) (hα : p.α = p.m + p.γ - 1)
    (hχ :
      positivePart ((p.N : ℝ) * p.α - 2) = 0 ∨
        p.χ₀ <
          ((positivePart ((p.N : ℝ) * p.α - 2) + 2 * p.m) * p.b) /
            (positivePart ((p.N : ℝ) * p.α - 2) *
              (p.ν + Psi_beta p.β * C.K)))
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2Bounded D u :=
  h.global_solution_of_critical_m_add_gamma_sub_one
    ha hb p.hm hm hβ hα hχ hu₀

lemma Proposition_1_3.global_solution_of_critical_two_mul_m_add_gamma_sub_two
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Paper2.Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hm : 1 ≤ p.m)
    (hβ : (1 / 2 : ℝ) ≤ p.β)
    (hα : p.α = 2 * p.m + p.γ - 2)
    (hχ :
      positivePart ((p.N : ℝ) * p.α - 2) = 0 ∨
        p.χ₀ <
          Real.sqrt
            (8 * p.b /
              (positivePart ((p.N : ℝ) * p.α - 2) *
                Theta_beta (2 * p.β - 1) * C.K)))
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2Bounded D u :=
  h.global_solution_of_critical_two_mul_m_add_gamma_sub_two
    ha hb p.hm hm hβ hα hχ hu₀

lemma Proposition_1_3.global_solution_of_remark16_chiStar1
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Paper2.Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hβ : 1 ≤ p.β) (hm : p.m = 1) (hα : p.α = p.γ)
    (hdim : 2 < (p.N : ℝ) * p.γ)
    (hχ : p.χ₀ < remark16ChiStar1 p C)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2Bounded D u :=
  h.global_solution_of_remark16_chiStar1
    ha hb hβ hm hα hdim hχ hu₀

lemma Proposition_1_3.global_solution_of_remark16_chiStar2
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Paper2.Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hβ : 1 ≤ p.β) (hm : p.m = 1) (hα : p.α = p.γ)
    (hdim : 2 < (p.N : ℝ) * p.γ)
    (hχ : p.χ₀ < remark16ChiStar2 p C)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2Bounded D u :=
  h.global_solution_of_remark16_chiStar2
    ha hb hβ hm hα hdim hχ hu₀

lemma Proposition_1_3.global_solution_of_remark16_min_chiStar12
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Paper2.Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hβ : 1 ≤ p.β) (hm : p.m = 1) (hα : p.α = p.γ)
    (hdim : 2 < (p.N : ℝ) * p.γ)
    (hχ : p.χ₀ < min (remark16ChiStar1 p C) (remark16ChiStar2 p C))
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2Bounded D u :=
  h.global_solution_of_remark16_min_chiStar12
    ha hb hβ hm hα hdim hχ hu₀

lemma Proposition_1_3.positive_global_solution_of_paper2_theorem_1_3
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Paper2.Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hm : 1 ≤ p.m)
    (hcond : StrongLogisticCondition p C)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v ∧
      InitialTrace D u₀ u :=
  (Proposition_1_3.of_paper2_theorem_1_3 h).positive_global_solution
    ha hb hm hcond hu₀

lemma Proposition_1_3.positive_global_solution_of_alpha_gt_m_add_gamma_sub_one
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Paper2.Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m) (hβ : 0 ≤ p.β)
    (hα : p.m + p.γ - 1 < p.α)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v ∧
      InitialTrace D u₀ u :=
  Proposition_1_3.positive_global_solution_of_paper2_theorem_1_3 h ha hb hm
    (StrongLogisticCondition.of_alpha_gt_m_add_gamma_sub_one hβ hα) hu₀

lemma Proposition_1_3.positive_global_solution_of_alpha_gt_two_mul_m_add_gamma_sub_two
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Paper2.Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m) (hβ : (1 / 2 : ℝ) ≤ p.β)
    (hα : 2 * p.m + p.γ - 2 < p.α)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v ∧
      InitialTrace D u₀ u :=
  Proposition_1_3.positive_global_solution_of_paper2_theorem_1_3 h ha hb hm
    (StrongLogisticCondition.of_alpha_gt_two_mul_m_add_gamma_sub_two hβ hα)
    hu₀

lemma Proposition_1_3.positive_global_solution_of_critical_m_add_gamma_sub_one_low_dimension
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Paper2.Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m)
    (hβ : 0 ≤ p.β) (hα : p.α = p.m + p.γ - 1)
    (hdim : (p.N : ℝ) * p.α ≤ 2)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v ∧
      InitialTrace D u₀ u :=
  Proposition_1_3.positive_global_solution_of_paper2_theorem_1_3 h ha hb hm
    (StrongLogisticCondition.of_critical_m_add_gamma_sub_one_low_dimension
      hβ hα hdim)
    hu₀

lemma Proposition_1_3.positive_global_solution_of_critical_two_mul_m_add_gamma_sub_two_low_dimension
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Paper2.Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m)
    (hβ : (1 / 2 : ℝ) ≤ p.β)
    (hα : p.α = 2 * p.m + p.γ - 2)
    (hdim : (p.N : ℝ) * p.α ≤ 2)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v ∧
      InitialTrace D u₀ u :=
  Proposition_1_3.positive_global_solution_of_paper2_theorem_1_3 h ha hb hm
    (StrongLogisticCondition.of_critical_two_mul_m_add_gamma_sub_two_low_dimension
      hβ hα hdim)
    hu₀

lemma Proposition_1_3.positive_global_solution_of_critical_m_add_gamma_sub_one
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Paper2.Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m)
    (hβ : 0 ≤ p.β) (hα : p.α = p.m + p.γ - 1)
    (hχ :
      positivePart ((p.N : ℝ) * p.α - 2) = 0 ∨
        p.χ₀ <
          ((positivePart ((p.N : ℝ) * p.α - 2) + 2 * p.m) * p.b) /
            (positivePart ((p.N : ℝ) * p.α - 2) *
              (p.ν + Psi_beta p.β * C.K)))
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v ∧
      InitialTrace D u₀ u :=
  Proposition_1_3.positive_global_solution_of_paper2_theorem_1_3 h ha hb hm
    (StrongLogisticCondition.of_critical_m_add_gamma_sub_one hβ hα hχ) hu₀

lemma Proposition_1_3.positive_global_solution_of_critical_two_mul_m_add_gamma_sub_two
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Paper2.Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m)
    (hβ : (1 / 2 : ℝ) ≤ p.β)
    (hα : p.α = 2 * p.m + p.γ - 2)
    (hχ :
      positivePart ((p.N : ℝ) * p.α - 2) = 0 ∨
        p.χ₀ <
          Real.sqrt
            (8 * p.b /
              (positivePart ((p.N : ℝ) * p.α - 2) *
                Theta_beta (2 * p.β - 1) * C.K)))
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v ∧
      InitialTrace D u₀ u :=
  Proposition_1_3.positive_global_solution_of_paper2_theorem_1_3 h ha hb hm
    (StrongLogisticCondition.of_critical_two_mul_m_add_gamma_sub_two hβ hα hχ)
    hu₀

lemma Proposition_1_3.positive_global_solution_of_remark16_min_chiStar12
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Paper2.Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hβ : 1 ≤ p.β) (hm : p.m = 1) (hα : p.α = p.γ)
    (hdim : 2 < (p.N : ℝ) * p.γ)
    (hχ : p.χ₀ < min (remark16ChiStar1 p C) (remark16ChiStar2 p C))
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v ∧
      InitialTrace D u₀ u := by
  have hm_ge : 1 ≤ p.m := by
    rw [hm]
  exact Proposition_1_3.positive_global_solution_of_paper2_theorem_1_3 h ha hb hm_ge
    (StrongLogisticCondition.of_remark16_min_chiStar12 hβ hm hα hdim hχ)
    hu₀

def proposition13NoRegularityParams : CM2Params :=
  { N := 1
    hN := by norm_num
    α := 3
    γ := 1
    m := 1
    μ := 1
    ν := 1
    χ₀ := 0
    a := 1
    b := 1
    β := 0
    hα := by norm_num
    hγ := by norm_num
    hm := by norm_num
    hμ := by norm_num
    hν := by norm_num
    ha := by norm_num
    hb := by norm_num
    hβ := by norm_num }

def proposition13NoRegularityConstants :
    Paper2Constants proposition13NoRegularityParams :=
  { K := 0
    K_nonneg := by norm_num }

lemma not_forall_Proposition_1_3 :
    ¬ (∀ D : BoundedDomainData, ∀ p : CM2Params,
        ∀ C : Paper2Constants p, Proposition_1_3 D p C) := by
  intro h
  let D := proposition11NoRegularityDomain
  let p := proposition13NoRegularityParams
  let C := proposition13NoRegularityConstants
  let u₀ : D.Point → ℝ := fun _ => 1
  have hu₀ : PositiveInitialDatum D u₀ := by
    constructor
    · trivial
    · intro x hx
      exact False.elim (by simpa [D, proposition11NoRegularityDomain] using hx)
  have hcond : StrongLogisticCondition p C := by
    exact StrongLogisticCondition.of_alpha_gt_m_add_gamma_sub_one
      (by norm_num [p, proposition13NoRegularityParams])
      (by norm_num [p, proposition13NoRegularityParams])
  rcases h D p C
      (by norm_num [p, proposition13NoRegularityParams])
      (by norm_num [p, proposition13NoRegularityParams])
      (by norm_num [p, proposition13NoRegularityParams])
      hcond u₀ hu₀ with
    ⟨u, v, hglobal, _htrace, _hbdd⟩
  have hreg := (hglobal.classical (by norm_num : (0 : ℝ) < 1)).regularity
  change False at hreg
  exact hreg

def Proposition_1_4 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  p.m = 1 → 1 ≤ p.β →
    ((p.a = 0 ∧ p.b = 0) ∨ (0 ≤ p.a ∧ 0 < p.b)) →
      p.χ₀ < chiBeta p →
        ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
          ∃ u v : ℝ → D.Point → ℝ,
            IsPaper2GlobalClassicalSolution D p u v ∧
            InitialTrace D u₀ u ∧
            IsPaper2Bounded D u

lemma Proposition_1_4.global_solution
    {D : BoundedDomainData} {p : CM2Params}
    (h : Proposition_1_4 D p)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hab : (p.a = 0 ∧ p.b = 0) ∨ (0 ≤ p.a ∧ 0 < p.b))
    (hχ : p.χ₀ < chiBeta p)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2Bounded D u :=
  h hm hβ hab hχ u₀ hu₀

lemma Proposition_1_4.positive_global_solution
    {D : BoundedDomainData} {p : CM2Params}
    (h : Proposition_1_4 D p)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hab : (p.a = 0 ∧ p.b = 0) ∨ (0 ≤ p.a ∧ 0 < p.b))
    (hχ : p.χ₀ < chiBeta p)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v ∧
      InitialTrace D u₀ u := by
  rcases h.global_solution hm hβ hab hχ hu₀ with
    ⟨u, v, hglobal, htrace, hbdd⟩
  exact ⟨u, v,
    PositiveGlobalBoundedSolution.of_global_bounded hglobal hbdd, htrace⟩

lemma Proposition_1_4.global_solution_minimal
    {D : BoundedDomainData} {p : CM2Params}
    (h : Proposition_1_4 D p)
    (ha : p.a = 0) (hb : p.b = 0)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < chiBeta p)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2Bounded D u :=
  h.global_solution hm hβ (Or.inl ⟨ha, hb⟩) hχ hu₀

lemma Proposition_1_4.positive_global_solution_minimal
    {D : BoundedDomainData} {p : CM2Params}
    (h : Proposition_1_4 D p)
    (ha : p.a = 0) (hb : p.b = 0)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < chiBeta p)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v ∧
      InitialTrace D u₀ u :=
  h.positive_global_solution hm hβ (Or.inl ⟨ha, hb⟩) hχ hu₀

lemma Proposition_1_4.global_solution_nonminimal
    {D : BoundedDomainData} {p : CM2Params}
    (h : Proposition_1_4 D p)
    (ha : 0 ≤ p.a) (hb : 0 < p.b)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < chiBeta p)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2Bounded D u :=
  h.global_solution hm hβ (Or.inr ⟨ha, hb⟩) hχ hu₀

lemma Proposition_1_4.positive_global_solution_nonminimal
    {D : BoundedDomainData} {p : CM2Params}
    (h : Proposition_1_4 D p)
    (ha : 0 ≤ p.a) (hb : 0 < p.b)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < chiBeta p)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v ∧
      InitialTrace D u₀ u :=
  h.positive_global_solution hm hβ (Or.inr ⟨ha, hb⟩) hχ hu₀

lemma Proposition_1_4.of_paper2_theorem_1_2
    {D : BoundedDomainData} {p : CM2Params}
    (h : Paper2.Theorem_1_2 D p) :
    Proposition_1_4 D p := by
  intro hm hβ _hab hχ u₀ hu₀
  exact h.linear_solution p.ha p.hb hβ hm hχ hu₀

lemma Proposition_1_4.global_solution_of_min_half_sqrt
    {D : BoundedDomainData} {p : CM2Params}
    (h : Paper2.Theorem_1_2 D p)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < min (chiBeta p / 2) (Real.sqrt (chiBeta p)))
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2Bounded D u :=
  h.linear_solution_of_min_half_sqrt p.ha p.hb hβ hm hχ hu₀

lemma Proposition_1_4.positive_global_solution_of_min_half_sqrt
    {D : BoundedDomainData} {p : CM2Params}
    (h : Paper2.Theorem_1_2 D p)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < min (chiBeta p / 2) (Real.sqrt (chiBeta p)))
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v ∧
      InitialTrace D u₀ u := by
  rcases h.linear_solution_of_min_half_sqrt p.ha p.hb hβ hm hχ hu₀ with
    ⟨u, v, hglobal, htrace, hbdd⟩
  exact ⟨u, v,
    PositiveGlobalBoundedSolution.of_global_bounded hglobal hbdd, htrace⟩

lemma Proposition_1_4.global_solution_of_remark16_weak
    {D : BoundedDomainData} {p : CM2Params}
    (h : Paper2.Theorem_1_2 D p)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < remark16ChiStarWeak p)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2Bounded D u :=
  h.linear_solution_of_remark16_weak p.ha p.hb hβ hm hχ hu₀

lemma Proposition_1_4.positive_global_solution_of_remark16_weak
    {D : BoundedDomainData} {p : CM2Params}
    (h : Paper2.Theorem_1_2 D p)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < remark16ChiStarWeak p)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v ∧
      InitialTrace D u₀ u := by
  rcases h.linear_solution_of_remark16_weak p.ha p.hb hβ hm hχ hu₀ with
    ⟨u, v, hglobal, htrace, hbdd⟩
  exact ⟨u, v,
    PositiveGlobalBoundedSolution.of_global_bounded hglobal hbdd, htrace⟩

def proposition14NoRegularityParams : CM2Params :=
  { N := 1
    hN := by norm_num
    α := 1
    γ := 1
    m := 1
    μ := 1
    ν := 1
    χ₀ := 0
    a := 0
    b := 0
    β := 1
    hα := by norm_num
    hγ := by norm_num
    hm := by norm_num
    hμ := by norm_num
    hν := by norm_num
    ha := by norm_num
    hb := by norm_num
    hβ := by norm_num }

lemma not_forall_Proposition_1_4 :
    ¬ (∀ D : BoundedDomainData, ∀ p : CM2Params, Proposition_1_4 D p) := by
  intro h
  let D := proposition11NoRegularityDomain
  let p := proposition14NoRegularityParams
  let u₀ : D.Point → ℝ := fun _ => 1
  have hu₀ : PositiveInitialDatum D u₀ := by
    constructor
    · trivial
    · intro x hx
      exact False.elim (by simpa [D, proposition11NoRegularityDomain] using hx)
  have hχ : p.χ₀ < chiBeta p := by
    norm_num [p, proposition14NoRegularityParams, chiBeta]
  rcases h D p
      (by norm_num [p, proposition14NoRegularityParams])
      (by norm_num [p, proposition14NoRegularityParams])
      (Or.inl
        ⟨by norm_num [p, proposition14NoRegularityParams],
          by norm_num [p, proposition14NoRegularityParams]⟩)
      hχ u₀ hu₀ with
    ⟨u, v, hglobal, _htrace, _hbdd⟩
  have hreg := (hglobal.classical (by norm_num : (0 : ℝ) < 1)).regularity
  change False at hreg
  exact hreg

lemma sigma_zero (p : CM2Params) (uStar vStar : ℝ) :
    sigma p uStar vStar 0 = -p.a * p.α := by
  simp [sigma]

lemma sigma_zero_neg_of_a_pos
    (p : CM2Params) (uStar vStar : ℝ) (ha : 0 < p.a) :
    sigma p uStar vStar 0 < 0 := by
  rw [sigma_zero]
  nlinarith [mul_pos ha p.hα]

lemma sigma_zero_eq_zero_of_a_eq_zero
    (p : CM2Params) (uStar vStar : ℝ) (ha : p.a = 0) :
    sigma p uStar vStar 0 = 0 := by
  simp [sigma_zero, ha]

lemma sigma_neg_of_chi_nonpos_a_pos
    (p : CM2Params) {uStar vStar lambdaN : ℝ}
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a)
    (huStar : 0 ≤ uStar) (hvStar : 0 ≤ vStar) (hlambda : 0 ≤ lambdaN) :
    sigma p uStar vStar lambdaN < 0 := by
  have hden_pos :
      0 < (1 + vStar) ^ p.β * (p.μ + lambdaN) := by
    exact mul_pos
      (Real.rpow_pos_of_pos (by linarith : 0 < 1 + vStar) _)
      (by linarith [p.hμ])
  have hfrac_nonneg :
      0 ≤
        (uStar ^ (p.m + p.γ - 1) * lambdaN) /
          ((1 + vStar) ^ p.β * (p.μ + lambdaN)) := by
    exact div_nonneg
      (mul_nonneg (Real.rpow_nonneg huStar _) hlambda)
      hden_pos.le
  have hchem_nonpos :
      p.χ₀ * p.ν * p.γ *
        ((uStar ^ (p.m + p.γ - 1) * lambdaN) /
          ((1 + vStar) ^ p.β * (p.μ + lambdaN))) ≤ 0 := by
    have hcoef_nonneg :
        0 ≤ p.ν * p.γ *
          ((uStar ^ (p.m + p.γ - 1) * lambdaN) /
            ((1 + vStar) ^ p.β * (p.μ + lambdaN))) := by
      exact mul_nonneg (mul_pos p.hν p.hγ).le hfrac_nonneg
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hχ hcoef_nonneg]
  have hchem_nonpos' :
      p.χ₀ * p.ν * p.γ * (uStar ^ (p.m + p.γ - 1) * lambdaN) /
          ((1 + vStar) ^ p.β * (p.μ + lambdaN)) ≤ 0 := by
    convert hchem_nonpos using 1
    ring
  unfold sigma
  nlinarith [mul_pos ha p.hα, hlambda, hchem_nonpos']

lemma LinearlyStable_of_chi_nonpos_a_pos
    (S : SpectralData) (p : CM2Params) {uStar vStar : ℝ}
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a)
    (huStar : 0 ≤ uStar) (hvStar : 0 ≤ vStar)
    (heig_nonneg : ∀ n : ℕ, n ≠ 0 → 0 ≤ S.eigenvalue n) :
    LinearlyStable S p uStar vStar := by
  intro n hn
  exact sigma_neg_of_chi_nonpos_a_pos p hχ ha huStar hvStar (heig_nonneg n hn)

lemma sigma_neg_of_chi_nonpos_lambda_pos
    (p : CM2Params) {uStar vStar lambdaN : ℝ}
    (hχ : p.χ₀ ≤ 0) (ha : 0 ≤ p.a)
    (huStar : 0 ≤ uStar) (hvStar : 0 ≤ vStar) (hlambda : 0 < lambdaN) :
    sigma p uStar vStar lambdaN < 0 := by
  have hden_pos :
      0 < (1 + vStar) ^ p.β * (p.μ + lambdaN) := by
    exact mul_pos
      (Real.rpow_pos_of_pos (by linarith : 0 < 1 + vStar) _)
      (by linarith [p.hμ])
  have hfrac_nonneg :
      0 ≤
        (uStar ^ (p.m + p.γ - 1) * lambdaN) /
          ((1 + vStar) ^ p.β * (p.μ + lambdaN)) := by
    exact div_nonneg
      (mul_nonneg (Real.rpow_nonneg huStar _) hlambda.le)
      hden_pos.le
  have hchem_nonpos :
      p.χ₀ * p.ν * p.γ *
        ((uStar ^ (p.m + p.γ - 1) * lambdaN) /
          ((1 + vStar) ^ p.β * (p.μ + lambdaN))) ≤ 0 := by
    have hcoef_nonneg :
        0 ≤ p.ν * p.γ *
          ((uStar ^ (p.m + p.γ - 1) * lambdaN) /
            ((1 + vStar) ^ p.β * (p.μ + lambdaN))) := by
      exact mul_nonneg (mul_pos p.hν p.hγ).le hfrac_nonneg
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hχ hcoef_nonneg]
  have hchem_nonpos' :
      p.χ₀ * p.ν * p.γ * (uStar ^ (p.m + p.γ - 1) * lambdaN) /
          ((1 + vStar) ^ p.β * (p.μ + lambdaN)) ≤ 0 := by
    convert hchem_nonpos using 1
    ring
  unfold sigma
  nlinarith [mul_nonneg ha p.hα.le, hlambda, hchem_nonpos']

lemma LinearlyStable_of_chi_nonpos_a_nonneg_eigen_pos
    (S : SpectralData) (p : CM2Params) {uStar vStar : ℝ}
    (hχ : p.χ₀ ≤ 0) (ha : 0 ≤ p.a)
    (huStar : 0 ≤ uStar) (hvStar : 0 ≤ vStar)
    (heig_pos : ∀ n : ℕ, n ≠ 0 → 0 < S.eigenvalue n) :
    LinearlyStable S p uStar vStar := by
  intro n hn
  exact sigma_neg_of_chi_nonpos_lambda_pos p hχ ha huStar hvStar (heig_pos n hn)

lemma LinearlyStable_of_chi_lt_sigmaCriticalChi
    (S : SpectralData) (p : CM2Params) {uStar vStar : ℝ}
    (H : HasNeumannSpectrum S)
    (huStar : 0 < uStar) (hvStar : 0 ≤ vStar)
    (hχ :
      ∀ n : ℕ, n ≠ 0 →
        p.χ₀ < sigmaCriticalChi p uStar vStar (S.eigenvalue n)) :
    LinearlyStable S p uStar vStar := by
  intro n hn
  have hcoeff :
      0 < sigmaChemCoefficient p uStar vStar (S.eigenvalue n) :=
    sigmaChemCoefficient_pos p huStar hvStar
      (H.eigenvalue_pos_of_ne_zero n hn)
  exact sigma_neg_of_chi_lt_sigmaCriticalChi p hcoeff (hχ n hn)

lemma BelowAllLinearCriticalThresholds.linearlyStable
    {S : SpectralData} {p : CM2Params} {uStar vStar : ℝ}
    (hbelow : BelowAllLinearCriticalThresholds S p uStar vStar)
    (H : HasNeumannSpectrum S)
    (huStar : 0 < uStar) (hvStar : 0 ≤ vStar) :
    LinearlyStable S p uStar vStar :=
  LinearlyStable_of_chi_lt_sigmaCriticalChi S p H huStar hvStar hbelow

lemma LinearlyUnstable_of_sigmaCriticalChi_lt_chi
    (S : SpectralData) (p : CM2Params) {uStar vStar : ℝ}
    (H : HasNeumannSpectrum S)
    (huStar : 0 < uStar) (hvStar : 0 ≤ vStar)
    {n : ℕ} (hn : n ≠ 0)
    (hχ : sigmaCriticalChi p uStar vStar (S.eigenvalue n) < p.χ₀) :
    LinearlyUnstable S p uStar vStar := by
  have hcoeff :
      0 < sigmaChemCoefficient p uStar vStar (S.eigenvalue n) :=
    sigmaChemCoefficient_pos p huStar hvStar
      (H.eigenvalue_pos_of_ne_zero n hn)
  exact ⟨n, hn, sigma_pos_of_sigmaCriticalChi_lt_chi p hcoeff hχ⟩

lemma AboveSomeLinearCriticalThreshold.linearlyUnstable
    {S : SpectralData} {p : CM2Params} {uStar vStar : ℝ}
    (habove : AboveSomeLinearCriticalThreshold S p uStar vStar)
    (H : HasNeumannSpectrum S)
    (huStar : 0 < uStar) (hvStar : 0 ≤ vStar) :
    LinearlyUnstable S p uStar vStar := by
  rcases habove with ⟨n, hn, hχ⟩
  exact LinearlyUnstable_of_sigmaCriticalChi_lt_chi S p H huStar hvStar hn hχ

lemma positiveEquilibrium_linearlyStable_of_chi_nonpos
    (S : SpectralData) (p : CM2Params)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (heig_nonneg : ∀ n : ℕ, n ≠ 0 → 0 ≤ S.eigenvalue n) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    LinearlyStable S p eq.1 eq.2 := by
  dsimp
  exact LinearlyStable_of_chi_nonpos_a_pos S p hχ ha
    (positiveEquilibrium_fst_pos p ⟨ha, hb⟩).le
    (positiveEquilibrium_snd_pos p ⟨ha, hb⟩).le
    heig_nonneg

lemma positiveEquilibrium_linearlyStable_of_chi_nonpos_neumann
    (S : SpectralData) (p : CM2Params)
    (H : HasNeumannSpectrum S)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    LinearlyStable S p eq.1 eq.2 := by
  exact positiveEquilibrium_linearlyStable_of_chi_nonpos S p hχ ha hb
    (fun n hn => H.eigenvalue_nonneg_of_ne_zero hn)

lemma positiveEquilibrium_belowAllLinearCriticalThresholds_of_chi_nonpos
    (S : SpectralData) (p : CM2Params)
    (H : HasNeumannSpectrum S)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    BelowAllLinearCriticalThresholds S p eq.1 eq.2 := by
  dsimp
  exact BelowAllLinearCriticalThresholds_of_chi_nonpos S p H hχ
    (positiveEquilibrium_fst_pos p ⟨ha, hb⟩)
    (positiveEquilibrium_snd_pos p ⟨ha, hb⟩).le

lemma positiveEquilibrium_linearlyStable_of_chi_lt_sigmaCriticalChi_neumann
    (S : SpectralData) (p : CM2Params)
    (H : HasNeumannSpectrum S) (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ :
      ∀ n : ℕ, n ≠ 0 →
        p.χ₀ <
          sigmaCriticalChi p
            (positiveEquilibrium p ⟨ha, hb⟩).1
            (positiveEquilibrium p ⟨ha, hb⟩).2
            (S.eigenvalue n)) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    LinearlyStable S p eq.1 eq.2 := by
  dsimp
  exact LinearlyStable_of_chi_lt_sigmaCriticalChi S p H
    (positiveEquilibrium_fst_pos p ⟨ha, hb⟩)
    (positiveEquilibrium_snd_pos p ⟨ha, hb⟩).le
    hχ

lemma positiveEquilibrium_linearlyStable_of_belowAll_neumann
    (S : SpectralData) (p : CM2Params)
    (H : HasNeumannSpectrum S) (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ :
      BelowAllLinearCriticalThresholds S p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    LinearlyStable S p eq.1 eq.2 := by
  exact positiveEquilibrium_linearlyStable_of_chi_lt_sigmaCriticalChi_neumann
    S p H ha hb hχ

lemma positiveEquilibrium_belowAllLinearCriticalThresholds_of_chi_lt_paperCriticalSensitivity
    (S : SpectralData) (p : CM2Params)
    (H : HasNeumannSpectrum S) (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity S p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    BelowAllLinearCriticalThresholds S p eq.1 eq.2 := by
  dsimp
  exact BelowAllLinearCriticalThresholds_of_chi_lt_paperCriticalSensitivity
    S p H hχ
    (positiveEquilibrium_fst_pos p ⟨ha, hb⟩)
    (positiveEquilibrium_snd_pos p ⟨ha, hb⟩).le

lemma positiveEquilibrium_linearlyStable_of_chi_lt_paperCriticalSensitivity_neumann
    (S : SpectralData) (p : CM2Params)
    (H : HasNeumannSpectrum S) (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity S p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    LinearlyStable S p eq.1 eq.2 := by
  exact positiveEquilibrium_linearlyStable_of_belowAll_neumann S p H ha hb
    (positiveEquilibrium_belowAllLinearCriticalThresholds_of_chi_lt_paperCriticalSensitivity
      S p H ha hb hχ)

lemma positiveEquilibrium_linearlyUnstable_of_sigmaCriticalChi_lt_chi_neumann
    (S : SpectralData) (p : CM2Params)
    (H : HasNeumannSpectrum S) (ha : 0 < p.a) (hb : 0 < p.b)
    {n : ℕ} (hn : n ≠ 0)
    (hχ :
      sigmaCriticalChi p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2
        (S.eigenvalue n) < p.χ₀) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    LinearlyUnstable S p eq.1 eq.2 := by
  dsimp
  exact LinearlyUnstable_of_sigmaCriticalChi_lt_chi S p H
    (positiveEquilibrium_fst_pos p ⟨ha, hb⟩)
    (positiveEquilibrium_snd_pos p ⟨ha, hb⟩).le
    hn hχ

lemma positiveEquilibrium_linearlyUnstable_of_mode_one_paperFormula_lt_chi_neumann
    (S : SpectralData) (p : CM2Params)
    (H : HasNeumannSpectrum S) (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ :
      sigmaCriticalChiPaperFormula p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2
          (S.eigenvalue 1) <
        p.χ₀) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    LinearlyUnstable S p eq.1 eq.2 := by
  have hχ' :
      sigmaCriticalChi p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2
          (S.eigenvalue 1) <
        p.χ₀ := by
    rw [sigmaCriticalChi_eq_paperFormula p
      (positiveEquilibrium_fst_pos p ⟨ha, hb⟩)
      (positiveEquilibrium_snd_pos p ⟨ha, hb⟩).le
      (H.eigenvalue_pos_of_ne_zero 1 (by norm_num))]
    exact hχ
  exact positiveEquilibrium_linearlyUnstable_of_sigmaCriticalChi_lt_chi_neumann
    S p H ha hb (n := 1) (by norm_num) hχ'

lemma positiveEquilibrium_linearlyUnstable_of_aboveSome_neumann
    (S : SpectralData) (p : CM2Params)
    (H : HasNeumannSpectrum S) (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ :
      AboveSomeLinearCriticalThreshold S p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    LinearlyUnstable S p eq.1 eq.2 := by
  dsimp
  exact hχ.linearlyUnstable H
    (positiveEquilibrium_fst_pos p ⟨ha, hb⟩)
    (positiveEquilibrium_snd_pos p ⟨ha, hb⟩).le

lemma positiveEquilibrium_linearlyUnstable_of_paperCriticalSensitivity_lt_chi_neumann
    (S : SpectralData) (p : CM2Params)
    (H : HasNeumannSpectrum S) (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ :
      paperCriticalSensitivity S p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 < p.χ₀) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    LinearlyUnstable S p eq.1 eq.2 := by
  have habove :
      AboveSomeLinearCriticalThreshold S p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 :=
    AboveSomeLinearCriticalThreshold_of_paperCriticalSensitivity_lt_chi
      S p H hχ
      (positiveEquilibrium_fst_pos p ⟨ha, hb⟩)
      (positiveEquilibrium_snd_pos p ⟨ha, hb⟩).le
  exact positiveEquilibrium_linearlyUnstable_of_aboveSome_neumann
    S p H ha hb habove

lemma minimalEquilibrium_linearlyStable_of_chi_nonpos
    (S : SpectralData) (p : CM2Params) {uStar : ℝ}
    (hχ : p.χ₀ ≤ 0) (ha : 0 ≤ p.a) (huStar : 0 < uStar)
    (heig_pos : ∀ n : ℕ, n ≠ 0 → 0 < S.eigenvalue n) :
    let eq := minimalEquilibrium p uStar
    LinearlyStable S p eq.1 eq.2 := by
  dsimp
  exact LinearlyStable_of_chi_nonpos_a_nonneg_eigen_pos S p hχ ha
    huStar.le
    (minimalEquilibrium_snd_pos p huStar).le
    heig_pos

lemma minimalEquilibrium_linearlyStable_of_chi_nonpos_a_eq_zero
    (S : SpectralData) (p : CM2Params) {uStar : ℝ}
    (hχ : p.χ₀ ≤ 0) (ha : p.a = 0) (huStar : 0 < uStar)
    (heig_pos : ∀ n : ℕ, n ≠ 0 → 0 < S.eigenvalue n) :
    let eq := minimalEquilibrium p uStar
    LinearlyStable S p eq.1 eq.2 := by
  exact minimalEquilibrium_linearlyStable_of_chi_nonpos S p hχ
    (by rw [ha]) huStar heig_pos

lemma minimalEquilibrium_linearlyStable_of_chi_nonpos_neumann
    (S : SpectralData) (p : CM2Params) {uStar : ℝ}
    (H : HasNeumannSpectrum S)
    (hχ : p.χ₀ ≤ 0) (ha : 0 ≤ p.a) (huStar : 0 < uStar) :
    let eq := minimalEquilibrium p uStar
    LinearlyStable S p eq.1 eq.2 := by
  exact minimalEquilibrium_linearlyStable_of_chi_nonpos S p hχ ha huStar
    H.eigenvalue_pos_of_ne_zero

lemma minimalEquilibrium_linearlyStable_of_chi_nonpos_a_eq_zero_neumann
    (S : SpectralData) (p : CM2Params) {uStar : ℝ}
    (H : HasNeumannSpectrum S)
    (hχ : p.χ₀ ≤ 0) (ha : p.a = 0) (huStar : 0 < uStar) :
    let eq := minimalEquilibrium p uStar
    LinearlyStable S p eq.1 eq.2 := by
  exact minimalEquilibrium_linearlyStable_of_chi_nonpos_a_eq_zero S p hχ ha huStar
    H.eigenvalue_pos_of_ne_zero

lemma minimalEquilibrium_belowAllLinearCriticalThresholds_of_chi_nonpos
    (S : SpectralData) (p : CM2Params) {uStar : ℝ}
    (H : HasNeumannSpectrum S)
    (hχ : p.χ₀ ≤ 0) (huStar : 0 < uStar) :
    let eq := minimalEquilibrium p uStar
    BelowAllLinearCriticalThresholds S p eq.1 eq.2 := by
  dsimp
  exact BelowAllLinearCriticalThresholds_of_chi_nonpos S p H hχ
    huStar
    (minimalEquilibrium_snd_pos p huStar).le

lemma minimalEquilibrium_linearlyStable_of_chi_lt_sigmaCriticalChi_neumann
    (S : SpectralData) (p : CM2Params) {uStar : ℝ}
    (H : HasNeumannSpectrum S) (huStar : 0 < uStar)
    (hχ :
      ∀ n : ℕ, n ≠ 0 →
        p.χ₀ <
          sigmaCriticalChi p
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2
            (S.eigenvalue n)) :
    let eq := minimalEquilibrium p uStar
    LinearlyStable S p eq.1 eq.2 := by
  dsimp
  exact LinearlyStable_of_chi_lt_sigmaCriticalChi S p H
    huStar
    (minimalEquilibrium_snd_pos p huStar).le
    hχ

lemma minimalEquilibrium_linearlyStable_of_belowAll_neumann
    (S : SpectralData) (p : CM2Params) {uStar : ℝ}
    (H : HasNeumannSpectrum S) (huStar : 0 < uStar)
    (hχ :
      BelowAllLinearCriticalThresholds S p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2) :
    let eq := minimalEquilibrium p uStar
    LinearlyStable S p eq.1 eq.2 := by
  exact minimalEquilibrium_linearlyStable_of_chi_lt_sigmaCriticalChi_neumann
    S p H huStar hχ

lemma minimalEquilibrium_belowAllLinearCriticalThresholds_of_chi_lt_paperCriticalSensitivity
    (S : SpectralData) (p : CM2Params) {uStar : ℝ}
    (H : HasNeumannSpectrum S) (huStar : 0 < uStar)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity S p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2) :
    let eq := minimalEquilibrium p uStar
    BelowAllLinearCriticalThresholds S p eq.1 eq.2 := by
  dsimp
  exact BelowAllLinearCriticalThresholds_of_chi_lt_paperCriticalSensitivity
    S p H hχ huStar
    (minimalEquilibrium_snd_pos p huStar).le

lemma minimalEquilibrium_linearlyStable_of_chi_lt_paperCriticalSensitivity_neumann
    (S : SpectralData) (p : CM2Params) {uStar : ℝ}
    (H : HasNeumannSpectrum S) (huStar : 0 < uStar)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity S p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2) :
    let eq := minimalEquilibrium p uStar
    LinearlyStable S p eq.1 eq.2 := by
  exact minimalEquilibrium_linearlyStable_of_belowAll_neumann S p H huStar
    (minimalEquilibrium_belowAllLinearCriticalThresholds_of_chi_lt_paperCriticalSensitivity
      S p H huStar hχ)

lemma minimalEquilibrium_linearlyUnstable_of_sigmaCriticalChi_lt_chi_neumann
    (S : SpectralData) (p : CM2Params) {uStar : ℝ}
    (H : HasNeumannSpectrum S) (huStar : 0 < uStar)
    {n : ℕ} (hn : n ≠ 0)
    (hχ :
      sigmaCriticalChi p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2
        (S.eigenvalue n) < p.χ₀) :
    let eq := minimalEquilibrium p uStar
    LinearlyUnstable S p eq.1 eq.2 := by
  dsimp
  exact LinearlyUnstable_of_sigmaCriticalChi_lt_chi S p H
    huStar
    (minimalEquilibrium_snd_pos p huStar).le
    hn hχ

lemma minimalEquilibrium_linearlyUnstable_of_mode_one_paperFormula_lt_chi_neumann
    (S : SpectralData) (p : CM2Params) {uStar : ℝ}
    (H : HasNeumannSpectrum S) (huStar : 0 < uStar)
    (hχ :
      sigmaCriticalChiPaperFormula p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2
          (S.eigenvalue 1) <
        p.χ₀) :
    let eq := minimalEquilibrium p uStar
    LinearlyUnstable S p eq.1 eq.2 := by
  have hχ' :
      sigmaCriticalChi p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2
          (S.eigenvalue 1) <
        p.χ₀ := by
    change
      sigmaCriticalChi p uStar (p.ν / p.μ * uStar ^ p.γ)
          (S.eigenvalue 1) <
        p.χ₀
    rw [sigmaCriticalChi_eq_paperFormula (p := p) (uStar := uStar)
      (vStar := p.ν / p.μ * uStar ^ p.γ)
      (lambdaN := S.eigenvalue 1)
      huStar
      (by
        exact (mul_pos (div_pos p.hν p.hμ)
          (Real.rpow_pos_of_pos huStar _)).le)
      (H.eigenvalue_pos_of_ne_zero 1 (by norm_num))]
    simpa [minimalEquilibrium] using hχ
  exact minimalEquilibrium_linearlyUnstable_of_sigmaCriticalChi_lt_chi_neumann
    S p H huStar (n := 1) (by norm_num) hχ'

lemma minimalEquilibrium_linearlyUnstable_of_aboveSome_neumann
    (S : SpectralData) (p : CM2Params) {uStar : ℝ}
    (H : HasNeumannSpectrum S) (huStar : 0 < uStar)
    (hχ :
      AboveSomeLinearCriticalThreshold S p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2) :
    let eq := minimalEquilibrium p uStar
    LinearlyUnstable S p eq.1 eq.2 := by
  dsimp
  exact hχ.linearlyUnstable H huStar
    (minimalEquilibrium_snd_pos p huStar).le

lemma minimalEquilibrium_linearlyUnstable_of_paperCriticalSensitivity_lt_chi_neumann
    (S : SpectralData) (p : CM2Params) {uStar : ℝ}
    (H : HasNeumannSpectrum S) (huStar : 0 < uStar)
    (hχ :
      paperCriticalSensitivity S p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 < p.χ₀) :
    let eq := minimalEquilibrium p uStar
    LinearlyUnstable S p eq.1 eq.2 := by
  have habove :
      AboveSomeLinearCriticalThreshold S p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 :=
    AboveSomeLinearCriticalThreshold_of_paperCriticalSensitivity_lt_chi
      S p H hχ huStar
      (minimalEquilibrium_snd_pos p huStar).le
  exact minimalEquilibrium_linearlyUnstable_of_aboveSome_neumann
    S p H huStar habove

/-! ### Concrete unit-interval spectral branches

These branches instantiate the abstract Neumann spectrum with the actual
one-dimensional unit-interval eigenvalues `n^2 π^2`, removing the fakeable
`SpectralData` parameter from the linear-stability hypotheses.
-/

lemma unitInterval_positiveEquilibrium_linearlyStable_of_chi_nonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 := by
  exact positiveEquilibrium_linearlyStable_of_chi_nonpos_neumann
    unitIntervalNeumannSpectrum p unitIntervalNeumannSpectrum_hasNeumannSpectrum
    hχ ha hb

lemma unitInterval_positiveEquilibrium_linearlyStable_of_chi_lt_critical
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 := by
  exact positiveEquilibrium_linearlyStable_of_chi_lt_paperCriticalSensitivity_neumann
    unitIntervalNeumannSpectrum p unitIntervalNeumannSpectrum_hasNeumannSpectrum
    ha hb hχ

lemma unitInterval_positiveEquilibrium_linearlyUnstable_of_critical_lt_chi
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ :
      paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2 <
        p.χ₀) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    LinearlyUnstable unitIntervalNeumannSpectrum p eq.1 eq.2 := by
  exact positiveEquilibrium_linearlyUnstable_of_paperCriticalSensitivity_lt_chi_neumann
    unitIntervalNeumannSpectrum p unitIntervalNeumannSpectrum_hasNeumannSpectrum
    ha hb hχ

lemma unitInterval_positiveEquilibrium_linearlyUnstable_of_first_mode_formula_lt_chi
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ :
      sigmaCriticalChiPaperFormula p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2
          (Real.pi ^ 2) <
        p.χ₀) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    LinearlyUnstable unitIntervalNeumannSpectrum p eq.1 eq.2 := by
  have hχ' :
      sigmaCriticalChi p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2
          (unitIntervalNeumannSpectrum.eigenvalue 1) <
        p.χ₀ := by
    rw [sigmaCriticalChi_eq_paperFormula p
      (positiveEquilibrium_fst_pos p ⟨ha, hb⟩)
      (positiveEquilibrium_snd_pos p ⟨ha, hb⟩).le
      (unitIntervalNeumannSpectrum_hasNeumannSpectrum.eigenvalue_pos_of_ne_zero
        1 (by norm_num))]
    simpa [unitIntervalNeumannSpectrum] using hχ
  exact positiveEquilibrium_linearlyUnstable_of_sigmaCriticalChi_lt_chi_neumann
    unitIntervalNeumannSpectrum p unitIntervalNeumannSpectrum_hasNeumannSpectrum
    ha hb (n := 1) (by norm_num) hχ'

lemma unitInterval_minimalEquilibrium_linearlyStable_of_chi_nonpos
    (p : CM2Params) {uStar : ℝ}
    (hχ : p.χ₀ ≤ 0) (ha : p.a = 0) (huStar : 0 < uStar) :
    let eq := minimalEquilibrium p uStar
    LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 := by
  exact minimalEquilibrium_linearlyStable_of_chi_nonpos_a_eq_zero_neumann
    unitIntervalNeumannSpectrum p unitIntervalNeumannSpectrum_hasNeumannSpectrum
    hχ ha huStar

lemma unitInterval_minimalEquilibrium_linearlyStable_of_chi_lt_critical
    (p : CM2Params) {uStar : ℝ} (huStar : 0 < uStar)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2) :
    let eq := minimalEquilibrium p uStar
    LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 := by
  exact minimalEquilibrium_linearlyStable_of_chi_lt_paperCriticalSensitivity_neumann
    unitIntervalNeumannSpectrum p unitIntervalNeumannSpectrum_hasNeumannSpectrum
    huStar hχ

lemma unitInterval_minimalEquilibrium_linearlyUnstable_of_critical_lt_chi
    (p : CM2Params) {uStar : ℝ} (huStar : 0 < uStar)
    (hχ :
      paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2 <
        p.χ₀) :
    let eq := minimalEquilibrium p uStar
    LinearlyUnstable unitIntervalNeumannSpectrum p eq.1 eq.2 := by
  exact minimalEquilibrium_linearlyUnstable_of_paperCriticalSensitivity_lt_chi_neumann
    unitIntervalNeumannSpectrum p unitIntervalNeumannSpectrum_hasNeumannSpectrum
    huStar hχ

lemma unitInterval_minimalEquilibrium_linearlyUnstable_of_first_mode_formula_lt_chi
    (p : CM2Params) {uStar : ℝ} (huStar : 0 < uStar)
    (hχ :
      sigmaCriticalChiPaperFormula p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2
          (Real.pi ^ 2) <
        p.χ₀) :
    let eq := minimalEquilibrium p uStar
    LinearlyUnstable unitIntervalNeumannSpectrum p eq.1 eq.2 := by
  have hχ' :
      sigmaCriticalChi p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2
          (unitIntervalNeumannSpectrum.eigenvalue 1) <
        p.χ₀ := by
    change
      sigmaCriticalChi p uStar (p.ν / p.μ * uStar ^ p.γ)
          (unitIntervalNeumannSpectrum.eigenvalue 1) <
        p.χ₀
    rw [sigmaCriticalChi_eq_paperFormula (p := p) (uStar := uStar)
      (vStar := p.ν / p.μ * uStar ^ p.γ)
      (lambdaN := unitIntervalNeumannSpectrum.eigenvalue 1)
      huStar
      (by
        exact (mul_pos (div_pos p.hν p.hμ)
          (Real.rpow_pos_of_pos huStar _)).le)
      (unitIntervalNeumannSpectrum_hasNeumannSpectrum.eigenvalue_pos_of_ne_zero
        1 (by norm_num))]
    simpa [unitIntervalNeumannSpectrum, minimalEquilibrium] using hχ
  exact minimalEquilibrium_linearlyUnstable_of_sigmaCriticalChi_lt_chi_neumann
    unitIntervalNeumannSpectrum p unitIntervalNeumannSpectrum_hasNeumannSpectrum
    huStar (n := 1) (by norm_num) hχ'

def GloballyAsymptoticallyStableNonminimal
    (D : BoundedDomainData) (p : CM2Params) (uStar _vStar : ℝ) : Prop :=
  ∀ u v : ℝ → D.Point → ℝ,
    PositiveGlobalBoundedSolution D p u v →
      UniformConvergesInSup D u uStar

def GloballyAsymptoticallyStableMinimal
    (D : BoundedDomainData) (p : CM2Params) (uStar _vStar : ℝ) : Prop :=
  ∀ u v : ℝ → D.Point → ℝ,
    PositiveGlobalBoundedSolution D p u v →
    HasInitialMass D u uStar →
      UniformConvergesInSup D u uStar

lemma GloballyAsymptoticallyStableNonminimal.convergence
    {D : BoundedDomainData} {p : CM2Params} {uStar vStar : ℝ}
    (h : GloballyAsymptoticallyStableNonminimal D p uStar vStar)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v) :
    UniformConvergesInSup D u uStar :=
  h u v huv

lemma GloballyAsymptoticallyStableMinimal.convergence
    {D : BoundedDomainData} {p : CM2Params} {uStar vStar : ℝ}
    (h : GloballyAsymptoticallyStableMinimal D p uStar vStar)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hmass : HasInitialMass D u uStar) :
    UniformConvergesInSup D u uStar :=
  h u v huv hmass

structure Paper3Constants (D : BoundedDomainData) (p : CM2Params) where
  chiCritical : ℝ → ℝ
  chiStrong1 : ℝ → ℝ
  chiStrong2 : ℝ → ℝ
  chiStrong3 : ℝ → ℝ
  chiStrong4 : ℝ → ℝ
  chiMinimal1 : ℝ → ℝ
  chiMinimal2 : ℝ → ℝ
  eventualMinimalUBound : ℝ → ℝ
  gaussianLowerConst : ℝ
  gaussianLowerConst_pos : 0 < gaussianLowerConst
  eventualMinimalUpperBound :
    p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
      0 < p.χ₀ → p.χ₀ < min (chiBeta p / 2) (Real.sqrt (chiBeta p)) →
        ∀ u v : ℝ → D.Point → ℝ,
          PositiveGlobalBoundedSolution D p u v →
            ∀ uStar > 0, HasInitialMass D u uStar →
              ∀ᶠ t in atTop, D.supNorm (u t) ≤ eventualMinimalUBound uStar
  uniformPersistencePart1 :
    1 ≤ p.m →
      ∀ u v : ℝ → D.Point → ℝ,
        PositiveGlobalBoundedSolution D p u v →
          ∃ δu > 0, EventuallyLowerBound D u δu ∧
            EventuallyLowerBound D v (p.ν / p.μ * δu ^ p.γ)
  uniformPersistencePart2 :
    0 < p.a → 0 < p.b → 0 < p.χ₀ → p.m = 1 → 1 ≤ p.β →
      p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)) →
        ∀ u v : ℝ → D.Point → ℝ,
          PositiveGlobalBoundedSolution D p u v →
            let lowerU :=
              ((p.a - p.χ₀ * p.μ * Theta_beta (p.β - 1)) / p.b) ^ (1 / p.α)
            EventuallyLowerBound D u lowerU ∧
              EventuallyLowerBound D v (p.ν / p.μ * lowerU ^ p.γ)
  uniformPersistencePart3 :
    0 < p.a → 0 < p.b → 0 < p.χ₀ → 1 < p.m → 1 ≤ p.β →
      ∀ u v : ℝ → D.Point → ℝ,
        PositiveGlobalBoundedSolution D p u v →
          let lowerU :=
            min 1 (p.a / (p.b + p.χ₀ * p.μ * Theta_beta (p.β - 1))) ^
              max (1 / (p.m - 1)) (1 / p.α)
          EventuallyLowerBound D u lowerU ∧
            EventuallyLowerBound D v (p.ν / p.μ * lowerU ^ p.γ)
  uniformPersistencePart4 :
    p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
      0 < p.χ₀ → p.χ₀ < min (chiBeta p / 2) (Real.sqrt (chiBeta p)) →
        ∀ uStar > 0, ∀ u v : ℝ → D.Point → ℝ,
          PositiveGlobalBoundedSolution D p u v →
          HasInitialMass D u uStar →
            EventuallyLowerBound D v
              (gaussianLowerConst *
                if p.γ ≤ 1 then
                  uStar * (eventualMinimalUBound uStar) ^ (p.γ - 1)
                else
                  uStar ^ p.γ)
  convergenceToExponential :
    ∀ N : StabilityNorms D, 1 ≤ p.m →
      (∀ (uStar _vStar theta : ℝ), 0 < theta →
        ∀ u v : ℝ → D.Point → ℝ,
          PositiveGlobalBoundedSolution D p u v →
          ThetaMomentConvergesToZero D u uStar theta →
            UniformConvergesInSup D u uStar) ∧
      (∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        p.χ₀ < chiCritical eq.1 →
          ∀ u v : ℝ → D.Point → ℝ,
            PositiveGlobalBoundedSolution D p u v →
            UniformConvergesInSup D u eq.1 →
              ExponentialC1Convergence D N u v eq.1 eq.2) ∧
      (p.a = 0 → p.b = 0 →
        ∀ uStar > 0,
          let eq := minimalEquilibrium p uStar
          p.χ₀ < chiCritical uStar →
            ∀ u v : ℝ → D.Point → ℝ,
              PositiveGlobalBoundedSolution D p u v →
              HasInitialMass D u uStar →
              UniformConvergesInSup D u eq.1 →
                ExponentialC1Convergence D N u v eq.1 eq.2)
  nonminimalGlobalStability :
    ∀ N : StabilityNorms D,
      0 < p.a → 0 < p.b → 0 ≤ p.β → 0 < p.α → 0 < p.γ →
        ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        ((1 ≤ p.m ∧ p.α + 1 ≥ 2 * p.γ ∧
            0 < p.χ₀ ∧ p.χ₀ < chiStrong1 eq.1) ∨
          (1 ≤ p.m ∧ 1 ≤ p.β ∧ p.α + 1 ≥ 2 * p.γ ∧
            0 < p.χ₀ ∧ p.χ₀ < chiStrong2 eq.1) ∨
          (1 ≤ p.m ∧ 1 ≤ p.γ ∧
            p.α + 1 ≥ p.m + p.γ + (if p.β = 0 then 0 else p.γ) ∧
            p.χ₀ < chiStrong3 eq.1) ∨
          (1 ≤ p.m ∧ 1 ≤ p.β ∧ 1 ≤ p.γ ∧
            p.α + 1 ≥ p.m + 2 * p.γ ∧
            p.χ₀ < chiStrong4 eq.1)) →
          (∀ u v : ℝ → D.Point → ℝ,
            PositiveGlobalBoundedSolution D p u v →
              UniformConvergesInSup D u eq.1) ∧
          ∃ A > 0, ∃ rate > 0,
            ∀ u v : ℝ → D.Point → ℝ,
              PositiveGlobalBoundedSolution D p u v →
                ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate
  minimalGlobalStability :
    ∀ N : StabilityNorms D,
      p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
        ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        ((0 < p.χ₀ ∧ p.χ₀ < chiMinimal1 uStar) ∨
          (p.γ = 1 ∧ 0 < p.χ₀ ∧ p.χ₀ < chiMinimal2 uStar)) →
          (∀ u v : ℝ → D.Point → ℝ,
            PositiveGlobalBoundedSolution D p u v →
            HasInitialMass D u uStar →
              UniformConvergesInSup D u eq.1) ∧
          ∃ A > 0, ∃ rate > 0,
            ∀ u v : ℝ → D.Point → ℝ,
              PositiveGlobalBoundedSolution D p u v →
              HasInitialMass D u uStar →
                ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate
  linearStabilityInstability :
    ∀ S : SpectralData, ∀ N : StabilityNorms D,
      (∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        p.χ₀ < chiCritical eq.1 →
          LinearlyStable S p eq.1 eq.2 ∧
          LocallyExponentiallyStableFromSup D p N eq.1 eq.2) ∧
      (∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        chiCritical eq.1 < p.χ₀ →
          LinearlyUnstable S p eq.1 eq.2) ∧
      (p.a = 0 → p.b = 0 →
        ∀ uStar > 0,
          let eq := minimalEquilibrium p uStar
          p.χ₀ < chiCritical uStar →
            LinearlyStable S p eq.1 eq.2 ∧
            MassConstrainedLocallyExponentiallyStableFromSup D p N eq.1 eq.2) ∧
      (p.a = 0 → p.b = 0 →
        ∀ uStar > 0,
          let eq := minimalEquilibrium p uStar
          chiCritical uStar < p.χ₀ →
            LinearlyUnstable S p eq.1 eq.2)
  chiStrong1_le_chiCritical :
    0 ≤ p.β → 1 ≤ p.m →
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        p.α + 1 ≥ 2 * p.γ →
          chiStrong1 (positiveEquilibrium p ⟨ha, hb⟩).1 ≤
            chiCritical (positiveEquilibrium p ⟨ha, hb⟩).1
  chiStrong2_le_chiCritical :
    0 ≤ p.β → 1 ≤ p.m →
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        1 ≤ p.β → p.α + 1 ≥ 2 * p.γ →
          chiStrong2 (positiveEquilibrium p ⟨ha, hb⟩).1 ≤
            chiCritical (positiveEquilibrium p ⟨ha, hb⟩).1
  chiStrong3_le_chiCritical :
    0 ≤ p.β → 1 ≤ p.m →
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        1 ≤ p.γ → p.α + 1 ≥ p.m + p.γ →
          chiStrong3 (positiveEquilibrium p ⟨ha, hb⟩).1 ≤
            chiCritical (positiveEquilibrium p ⟨ha, hb⟩).1
  chiStrong4_le_chiCritical :
    0 ≤ p.β → 1 ≤ p.m →
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        1 ≤ p.β → 1 ≤ p.γ → p.α + 1 ≥ p.m + 2 * p.γ →
          chiStrong4 (positiveEquilibrium p ⟨ha, hb⟩).1 ≤
            chiCritical (positiveEquilibrium p ⟨ha, hb⟩).1
  chiMinimal1_le_chiCritical :
    p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
      ∀ uStar > 0,
        0 < p.γ → chiMinimal1 uStar ≤ chiCritical uStar
  chiMinimal2_le_chiCritical :
    p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
      ∀ uStar > 0,
        p.γ = 1 → chiMinimal2 uStar ≤ chiCritical uStar

/-- The constants package uses the paper's concrete spectral formula `(2.10)`
for the linear critical sensitivity. -/
def Paper3ConstantsUsesCriticalSpectrum
    (S : SpectralData) (p : CM2Params) {D : BoundedDomainData}
    (C : Paper3Constants D p) : Prop :=
  ∀ uStar : ℝ, 0 < uStar →
    C.chiCritical uStar =
      paperCriticalSensitivity S p uStar (p.ν / p.μ * uStar ^ p.γ)

lemma Paper3ConstantsUsesCriticalSpectrum.chiCritical_positiveEquilibrium
    {D : BoundedDomainData} {S : SpectralData} {p : CM2Params}
    {C : Paper3Constants D p}
    (hC : Paper3ConstantsUsesCriticalSpectrum S p C)
    (ha : 0 < p.a) (hb : 0 < p.b) :
    C.chiCritical (positiveEquilibrium p ⟨ha, hb⟩).1 =
      paperCriticalSensitivity S p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  dsimp [positiveEquilibrium]
  exact hC ((p.a / p.b) ^ (1 / p.α))
    (positiveEquilibrium_fst_pos p ⟨ha, hb⟩)

lemma Paper3ConstantsUsesCriticalSpectrum.chiCritical_minimalEquilibrium
    {D : BoundedDomainData} {S : SpectralData} {p : CM2Params}
    {C : Paper3Constants D p} {uStar : ℝ}
    (hC : Paper3ConstantsUsesCriticalSpectrum S p C)
    (huStar : 0 < uStar) :
    C.chiCritical uStar =
      paperCriticalSensitivity S p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 := by
  dsimp [minimalEquilibrium]
  exact hC uStar huStar

lemma Paper3ConstantsUsesCriticalSpectrum.chiCritical_nonneg
    {D : BoundedDomainData} {S : SpectralData} {p : CM2Params}
    {C : Paper3Constants D p}
    (hC : Paper3ConstantsUsesCriticalSpectrum S p C)
    (H : HasNeumannSpectrum S) {uStar : ℝ} (huStar : 0 < uStar) :
    0 ≤ C.chiCritical uStar := by
  rw [hC uStar huStar]
  have hvStar : 0 ≤ p.ν / p.μ * uStar ^ p.γ := by
    exact mul_nonneg (div_pos p.hν p.hμ).le
      (Real.rpow_nonneg huStar.le _)
  exact paperCriticalSensitivity_nonneg S p H huStar hvStar

lemma Paper3ConstantsUsesCriticalSpectrum.chiCritical_pos
    {D : BoundedDomainData} {S : SpectralData} {p : CM2Params}
    {C : Paper3Constants D p}
    (hC : Paper3ConstantsUsesCriticalSpectrum S p C)
    (H : HasNeumannSpectrum S) {uStar : ℝ} (huStar : 0 < uStar) :
    0 < C.chiCritical uStar := by
  rw [hC uStar huStar]
  have hvStar : 0 ≤ p.ν / p.μ * uStar ^ p.γ := by
    exact mul_nonneg (div_pos p.hν p.hμ).le
      (Real.rpow_nonneg huStar.le _)
  exact paperCriticalSensitivity_pos S p H huStar hvStar

lemma Paper3ConstantsUsesCriticalSpectrum.chiCritical_positiveEquilibrium_nonneg
    {D : BoundedDomainData} {S : SpectralData} {p : CM2Params}
    {C : Paper3Constants D p}
    (hC : Paper3ConstantsUsesCriticalSpectrum S p C)
    (H : HasNeumannSpectrum S) (ha : 0 < p.a) (hb : 0 < p.b) :
    0 ≤ C.chiCritical (positiveEquilibrium p ⟨ha, hb⟩).1 := by
  rw [hC.chiCritical_positiveEquilibrium ha hb]
  exact paperCriticalSensitivity_positiveEquilibrium_nonneg S p H ha hb

lemma Paper3ConstantsUsesCriticalSpectrum.chiCritical_positiveEquilibrium_pos
    {D : BoundedDomainData} {S : SpectralData} {p : CM2Params}
    {C : Paper3Constants D p}
    (hC : Paper3ConstantsUsesCriticalSpectrum S p C)
    (H : HasNeumannSpectrum S) (ha : 0 < p.a) (hb : 0 < p.b) :
    0 < C.chiCritical (positiveEquilibrium p ⟨ha, hb⟩).1 := by
  rw [hC.chiCritical_positiveEquilibrium ha hb]
  exact paperCriticalSensitivity_positiveEquilibrium_pos S p H ha hb

lemma Paper3ConstantsUsesCriticalSpectrum.chiCritical_minimalEquilibrium_nonneg
    {D : BoundedDomainData} {S : SpectralData} {p : CM2Params}
    {C : Paper3Constants D p} {uStar : ℝ}
    (hC : Paper3ConstantsUsesCriticalSpectrum S p C)
    (H : HasNeumannSpectrum S) (huStar : 0 < uStar) :
    0 ≤ C.chiCritical uStar := by
  rw [hC.chiCritical_minimalEquilibrium huStar]
  exact paperCriticalSensitivity_minimalEquilibrium_nonneg S p H huStar

lemma Paper3ConstantsUsesCriticalSpectrum.chiCritical_minimalEquilibrium_pos
    {D : BoundedDomainData} {S : SpectralData} {p : CM2Params}
    {C : Paper3Constants D p} {uStar : ℝ}
    (hC : Paper3ConstantsUsesCriticalSpectrum S p C)
    (H : HasNeumannSpectrum S) (huStar : 0 < uStar) :
    0 < C.chiCritical uStar := by
  rw [hC.chiCritical_minimalEquilibrium huStar]
  exact paperCriticalSensitivity_minimalEquilibrium_pos S p H huStar

lemma Paper3ConstantsUsesCriticalSpectrum.positiveEquilibrium_linearlyStable
    {D : BoundedDomainData} {S : SpectralData} {p : CM2Params}
    {C : Paper3Constants D p}
    (hC : Paper3ConstantsUsesCriticalSpectrum S p C)
    (H : HasNeumannSpectrum S) (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ : p.χ₀ < C.chiCritical (positiveEquilibrium p ⟨ha, hb⟩).1) :
    LinearlyStable S p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  exact
    positiveEquilibrium_linearlyStable_of_chi_lt_paperCriticalSensitivity_neumann
      S p H ha hb
      (by
        simpa [hC.chiCritical_positiveEquilibrium ha hb] using hχ)

lemma Paper3ConstantsUsesCriticalSpectrum.positiveEquilibrium_linearlyUnstable
    {D : BoundedDomainData} {S : SpectralData} {p : CM2Params}
    {C : Paper3Constants D p}
    (hC : Paper3ConstantsUsesCriticalSpectrum S p C)
    (H : HasNeumannSpectrum S) (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ : C.chiCritical (positiveEquilibrium p ⟨ha, hb⟩).1 < p.χ₀) :
    LinearlyUnstable S p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  exact
    positiveEquilibrium_linearlyUnstable_of_paperCriticalSensitivity_lt_chi_neumann
      S p H ha hb
      (by
        simpa [hC.chiCritical_positiveEquilibrium ha hb] using hχ)

lemma Paper3ConstantsUsesCriticalSpectrum.minimalEquilibrium_linearlyStable
    {D : BoundedDomainData} {S : SpectralData} {p : CM2Params}
    {C : Paper3Constants D p} {uStar : ℝ}
    (hC : Paper3ConstantsUsesCriticalSpectrum S p C)
    (H : HasNeumannSpectrum S) (huStar : 0 < uStar)
    (hχ : p.χ₀ < C.chiCritical uStar) :
    LinearlyStable S p
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 := by
  exact
    minimalEquilibrium_linearlyStable_of_chi_lt_paperCriticalSensitivity_neumann
      S p H huStar
      (by
        simpa [hC.chiCritical_minimalEquilibrium huStar] using hχ)

lemma Paper3ConstantsUsesCriticalSpectrum.minimalEquilibrium_linearlyUnstable
    {D : BoundedDomainData} {S : SpectralData} {p : CM2Params}
    {C : Paper3Constants D p} {uStar : ℝ}
    (hC : Paper3ConstantsUsesCriticalSpectrum S p C)
    (H : HasNeumannSpectrum S) (huStar : 0 < uStar)
    (hχ : C.chiCritical uStar < p.χ₀) :
    LinearlyUnstable S p
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 := by
  exact
    minimalEquilibrium_linearlyUnstable_of_paperCriticalSensitivity_lt_chi_neumann
      S p H huStar
      (by
        simpa [hC.chiCritical_minimalEquilibrium huStar] using hχ)

lemma Paper3ConstantsUsesCriticalSpectrum.chi_pos_of_chiCritical_lt
    {D : BoundedDomainData} {S : SpectralData} {p : CM2Params}
    {C : Paper3Constants D p}
    (hC : Paper3ConstantsUsesCriticalSpectrum S p C)
    (H : HasNeumannSpectrum S) {uStar : ℝ} (huStar : 0 < uStar)
    (hχ : C.chiCritical uStar < p.χ₀) :
    0 < p.χ₀ :=
  lt_of_le_of_lt (hC.chiCritical_nonneg H huStar) hχ

lemma Paper3ConstantsUsesCriticalSpectrum.chi_pos_of_positiveEquilibrium_chiCritical_lt
    {D : BoundedDomainData} {S : SpectralData} {p : CM2Params}
    {C : Paper3Constants D p}
    (hC : Paper3ConstantsUsesCriticalSpectrum S p C)
    (H : HasNeumannSpectrum S) (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ : C.chiCritical (positiveEquilibrium p ⟨ha, hb⟩).1 < p.χ₀) :
    0 < p.χ₀ :=
  lt_of_le_of_lt
    (hC.chiCritical_positiveEquilibrium_nonneg H ha hb) hχ

def betaTilde (beta : ℝ) : ℝ :=
  positivePart (min 1 (2 * beta - 1))

def CAlphaGamma (alpha gamma : ℝ) : ℝ :=
  if alpha < 1 then
    (alpha + 1) ^ 2 / (4 * alpha)
  else if gamma ≤ 1 then
    1
  else
    gamma ^ 2 / (2 * gamma - 1)

lemma betaTilde_nonneg (beta : ℝ) :
    0 ≤ betaTilde beta := by
  unfold betaTilde
  exact positivePart_nonneg _

lemma betaTilde_le_one (beta : ℝ) :
    betaTilde beta ≤ 1 := by
  unfold betaTilde
  by_cases hnonneg : 0 ≤ min (1 : ℝ) (2 * beta - 1)
  · rw [positivePart_eq_self_of_nonneg hnonneg]
    exact min_le_left _ _
  · rw [positivePart_eq_zero_of_nonpos (le_of_not_ge hnonneg)]
    norm_num

lemma betaTilde_mem_Icc_zero_one (beta : ℝ) :
    betaTilde beta ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨betaTilde_nonneg beta, betaTilde_le_one beta⟩

lemma betaTilde_eq_zero_of_beta_le_half {beta : ℝ}
    (hbeta : beta ≤ (1 / 2 : ℝ)) :
    betaTilde beta = 0 := by
  unfold betaTilde
  apply positivePart_eq_zero_of_nonpos
  exact le_trans (min_le_right _ _) (by linarith)

lemma betaTilde_eq_two_mul_sub_one_of_mem_Icc {beta : ℝ}
    (hbeta : beta ∈ Set.Icc (1 / 2 : ℝ) 1) :
    betaTilde beta = 2 * beta - 1 := by
  unfold betaTilde
  have hnonneg : 0 ≤ 2 * beta - 1 := by linarith [hbeta.1]
  have hle_one : 2 * beta - 1 ≤ 1 := by linarith [hbeta.2]
  rw [min_eq_right hle_one]
  exact positivePart_eq_self_of_nonneg hnonneg

lemma betaTilde_eq_one_of_one_le_beta {beta : ℝ}
    (hbeta : 1 ≤ beta) :
    betaTilde beta = 1 := by
  unfold betaTilde
  have hone_le : 1 ≤ 2 * beta - 1 := by linarith
  rw [min_eq_left hone_le]
  exact positivePart_eq_self_of_nonneg zero_le_one

lemma betaTilde_le_two_mul {beta : ℝ} (hbeta : 0 ≤ beta) :
    betaTilde beta ≤ 2 * beta := by
  unfold betaTilde
  by_cases hhalf : beta ≤ (1 / 2 : ℝ)
  · rw [positivePart_eq_zero_of_nonpos]
    · nlinarith
    · exact le_trans (min_le_right _ _) (by linarith)
  · have hpos : 0 ≤ min (1 : ℝ) (2 * beta - 1) := by
      exact le_min (by norm_num) (by linarith)
    rw [positivePart_eq_self_of_nonneg hpos]
    exact le_trans (min_le_right _ _) (by linarith)

lemma one_add_betaTilde_mul_le_one_add_rpow
    {beta v : ℝ} (hbeta : 0 ≤ beta) (hv : 0 ≤ v) :
    1 + betaTilde beta * v ≤ (1 + v) ^ (2 * beta) := by
  by_cases hhalf : beta < (1 / 2 : ℝ)
  · have htilde : betaTilde beta = 0 :=
      betaTilde_eq_zero_of_beta_le_half (le_of_lt hhalf)
    rw [htilde, zero_mul, add_zero]
    exact Real.one_le_rpow (by linarith : 1 ≤ 1 + v) (by nlinarith)
  · have hpow : 1 ≤ 2 * beta := by linarith
    have hbern :
        1 + (2 * beta) * v ≤ (1 + v) ^ (2 * beta) := by
      exact one_add_mul_self_le_rpow_one_add (s := v)
        (by linarith : -1 ≤ v) hpow
    have hcoef : betaTilde beta * v ≤ (2 * beta) * v := by
      exact mul_le_mul_of_nonneg_right
        (betaTilde_le_two_mul hbeta) hv
    have hstep :
        1 + betaTilde beta * v ≤ 1 + (2 * beta) * v :=
      by simpa [add_comm] using add_le_add_left hcoef 1
    exact hstep.trans hbern

lemma CAlphaGamma_pos {alpha gamma : ℝ}
    (halpha : 0 < alpha) (_hgamma : 0 < gamma) :
    0 < CAlphaGamma alpha gamma := by
  unfold CAlphaGamma
  by_cases halpha_lt : alpha < 1
  · rw [if_pos halpha_lt]
    exact div_pos
      (sq_pos_of_ne_zero (by linarith : alpha + 1 ≠ 0))
      (by positivity)
  · rw [if_neg halpha_lt]
    by_cases hgamma_le : gamma ≤ 1
    · rw [if_pos hgamma_le]
      norm_num
    · rw [if_neg hgamma_le]
      have hgamma_gt : 1 < gamma := lt_of_not_ge hgamma_le
      exact div_pos
        (sq_pos_of_ne_zero (by linarith : gamma ≠ 0))
        (by linarith)

lemma one_le_CAlphaGamma_mul_alpha_div_gamma_sq
    {alpha gamma : ℝ} (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hrel : 2 * gamma ≤ alpha + 1) :
    1 ≤ CAlphaGamma alpha gamma * alpha / gamma ^ 2 := by
  unfold CAlphaGamma
  by_cases halpha_lt : alpha < 1
  · rw [if_pos halpha_lt]
    have hgamma_le : gamma ≤ (alpha + 1) / 2 := by linarith
    have hsq : gamma ^ 2 ≤ (alpha + 1) ^ 2 / 4 := by
      nlinarith [sq_nonneg ((alpha + 1) / 2 - gamma)]
    rw [le_div_iff₀ (by positivity : 0 < gamma ^ 2)]
    calc
      1 * gamma ^ 2 = gamma ^ 2 := by ring
      _ ≤ (alpha + 1) ^ 2 / 4 := hsq
      _ = ((alpha + 1) ^ 2 / (4 * alpha)) * alpha := by
        field_simp [ne_of_gt halpha]
  · rw [if_neg halpha_lt]
    have halpha_ge : 1 ≤ alpha := le_of_not_gt halpha_lt
    by_cases hgamma_le : gamma ≤ 1
    · rw [if_pos hgamma_le]
      rw [le_div_iff₀ (by positivity : 0 < gamma ^ 2)]
      nlinarith [sq_nonneg (gamma - 1)]
    · rw [if_neg hgamma_le]
      have hgamma_gt : 1 < gamma := lt_of_not_ge hgamma_le
      rw [le_div_iff₀ (by positivity : 0 < gamma ^ 2)]
      have hden_pos : 0 < 2 * gamma - 1 := by linarith
      rw [div_mul_eq_mul_div]
      rw [le_div_iff₀ hden_pos]
      nlinarith

lemma power_difference_normalized_of_one_le_alpha_of_gamma_le_one
    {alpha gamma t : ℝ}
    (halpha : 1 ≤ alpha) (hgamma_pos : 0 < gamma) (hgamma_le : gamma ≤ 1)
    (ht : 0 < t) :
    (t ^ gamma - 1) ^ 2 ≤ (t - 1) * (t ^ alpha - 1) := by
  have hgamma_nonneg : 0 ≤ gamma := hgamma_pos.le
  have hgamma_le_alpha : gamma ≤ alpha := hgamma_le.trans halpha
  by_cases ht_ge : 1 ≤ t
  · have htγ_ge_one : 1 ≤ t ^ gamma := Real.one_le_rpow ht_ge hgamma_nonneg
    have htγ_le_t : t ^ gamma ≤ t := Real.rpow_le_self_of_one_le ht_ge hgamma_le
    have htγ_le_tα : t ^ gamma ≤ t ^ alpha :=
      Real.rpow_le_rpow_of_exponent_le ht_ge hgamma_le_alpha
    have hA_nonneg : 0 ≤ t ^ gamma - 1 := sub_nonneg.mpr htγ_ge_one
    have hB_nonneg : 0 ≤ t - 1 := sub_nonneg.mpr ht_ge
    have hA_le_B : t ^ gamma - 1 ≤ t - 1 := sub_le_sub_right htγ_le_t 1
    have hA_le_C : t ^ gamma - 1 ≤ t ^ alpha - 1 :=
      sub_le_sub_right htγ_le_tα 1
    have hmul :
        (t ^ gamma - 1) * (t ^ gamma - 1) ≤
          (t - 1) * (t ^ alpha - 1) :=
      mul_le_mul hA_le_B hA_le_C hA_nonneg hB_nonneg
    simpa [sq] using hmul
  · have ht_le : t ≤ 1 := le_of_not_ge ht_ge
    have htγ_le_one : t ^ gamma ≤ 1 := Real.rpow_le_one ht.le ht_le hgamma_nonneg
    have ht_le_tγ : t ≤ t ^ gamma := Real.self_le_rpow_of_le_one ht.le ht_le hgamma_le
    have htα_le_tγ : t ^ alpha ≤ t ^ gamma :=
      Real.rpow_le_rpow_of_exponent_ge ht ht_le hgamma_le_alpha
    have hA_nonneg : 0 ≤ 1 - t ^ gamma := sub_nonneg.mpr htγ_le_one
    have hB_nonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht_le
    have hA_le_B : 1 - t ^ gamma ≤ 1 - t := sub_le_sub_left ht_le_tγ 1
    have hA_le_C : 1 - t ^ gamma ≤ 1 - t ^ alpha := sub_le_sub_left htα_le_tγ 1
    have hmul :
        (1 - t ^ gamma) * (1 - t ^ gamma) ≤
          (1 - t) * (1 - t ^ alpha) :=
      mul_le_mul hA_le_B hA_le_C hA_nonneg hB_nonneg
    nlinarith

lemma sinh_mul_le_mul_sinh_of_mem_Icc
    {a x : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx : 0 ≤ x) :
    Real.sinh (a * x) ≤ a * Real.sinh x := by
  let F : ℝ → ℝ := fun y => a * Real.sinh y - Real.sinh (a * y)
  have hcont : ContinuousOn F (Set.Icc 0 x) := by
    dsimp [F]
    exact ((Real.continuous_sinh.const_mul a).sub
      (Real.continuous_sinh.comp (continuous_const.mul continuous_id))).continuousOn
  have hdiff : DifferentiableOn ℝ F (interior (Set.Icc 0 x)) := by
    intro y hy
    dsimp [F]
    exact (((Real.differentiableAt_sinh.const_mul a).sub
      (Real.differentiableAt_sinh.comp y
        ((differentiableAt_const (c := a)).mul differentiableAt_id))).differentiableWithinAt)
  have hderiv_nonneg :
      ∀ y ∈ interior (Set.Icc 0 x), (0 : ℝ) ≤ deriv F y := by
    intro y hy
    rw [interior_Icc] at hy
    have hy_nonneg : 0 ≤ y := hy.1.le
    have hay_abs : |a * y| ≤ |y| := by
      rw [abs_of_nonneg hy_nonneg]
      rw [abs_of_nonneg (mul_nonneg ha0 hy_nonneg)]
      nlinarith
    have hcosh : Real.cosh (a * y) ≤ Real.cosh y :=
      Real.cosh_le_cosh.2 hay_abs
    have hderiv : deriv F y = a * Real.cosh y - a * Real.cosh (a * y) := by
      have hA : HasDerivAt (fun y : ℝ => a * Real.sinh y) (a * Real.cosh y) y := by
        simpa [mul_comm] using (Real.hasDerivAt_sinh y).const_mul a
      have hB : HasDerivAt (fun y : ℝ => Real.sinh (a * y)) (a * Real.cosh (a * y)) y := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (Real.hasDerivAt_sinh (a * y)).comp y ((hasDerivAt_id y).const_mul a)
      exact (hA.sub hB).deriv
    rw [hderiv]
    exact sub_nonneg.mpr (mul_le_mul_of_nonneg_left hcosh ha0)
  have hmain :=
    (convex_Icc (0 : ℝ) x).mul_sub_le_image_sub_of_le_deriv
      hcont hdiff hderiv_nonneg (x := 0) (y := x)
      (by exact ⟨le_rfl, hx⟩) (by exact ⟨hx, le_rfl⟩) hx
  dsimp [F] at hmain
  simpa using hmain

lemma sinh_sq_mid_le_const_mul_sinh_mul_sinh
    {alpha x : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hx : 0 ≤ x) :
    Real.sinh (((alpha + 1) / 2) * x) ^ 2 ≤
      ((alpha + 1) ^ 2 / (4 * alpha)) *
        (Real.sinh x * Real.sinh (alpha * x)) := by
  let m : ℝ := ((alpha + 1) / 2) * x
  let d : ℝ := ((1 - alpha) / 2) * x
  let k : ℝ := (1 - alpha) / (alpha + 1)
  have hm_nonneg : 0 ≤ m := by
    dsimp [m]
    exact mul_nonneg (by positivity) hx
  have hk_nonneg : 0 ≤ k := by
    dsimp [k]
    exact div_nonneg (by linarith) (by linarith)
  have hk_le_one : k ≤ 1 := by
    dsimp [k]
    rw [div_le_iff₀ (by linarith : 0 < alpha + 1)]
    linarith
  have hd_eq : d = k * m := by
    dsimp [d, k, m]
    have ha1_ne : alpha + 1 ≠ 0 := by linarith
    field_simp [ha1_ne]
  have hsinh_d_le : Real.sinh d ≤ k * Real.sinh m := by
    rw [hd_eq]
    exact sinh_mul_le_mul_sinh_of_mem_Icc hk_nonneg hk_le_one hm_nonneg
  have hsinh_d_nonneg : 0 ≤ Real.sinh d := by
    rw [Real.sinh_nonneg_iff]
    dsimp [d]
    exact mul_nonneg (by linarith) hx
  have hsinh_m_nonneg : 0 ≤ Real.sinh m := by
    rw [Real.sinh_nonneg_iff]
    exact hm_nonneg
  have hd_sq_le : Real.sinh d ^ 2 ≤ k ^ 2 * Real.sinh m ^ 2 := by
    have h := mul_le_mul hsinh_d_le hsinh_d_le hsinh_d_nonneg
      (mul_nonneg hk_nonneg hsinh_m_nonneg)
    nlinarith
  have hx_eq : x = m + d := by
    dsimp [m, d]
    ring
  have hax_eq : alpha * x = m - d := by
    dsimp [m, d]
    ring
  have hprod :
        Real.sinh x * Real.sinh (alpha * x) =
        Real.sinh m ^ 2 - Real.sinh d ^ 2 := by
    rw [hax_eq, hx_eq, Real.sinh_add, Real.sinh_sub]
    ring_nf
    rw [Real.cosh_sq', Real.cosh_sq']
    ring
  have hmain :
      (1 - k ^ 2) * Real.sinh m ^ 2 ≤
        Real.sinh x * Real.sinh (alpha * x) := by
    rw [hprod]
    nlinarith
  have hcoef_pos : 0 < (alpha + 1) ^ 2 / (4 * alpha) := by
    positivity
  have hcoef :
      ((alpha + 1) ^ 2 / (4 * alpha)) * (1 - k ^ 2) = 1 := by
    dsimp [k]
    have ha_ne : alpha ≠ 0 := ne_of_gt halpha0
    have ha1_ne : alpha + 1 ≠ 0 := by linarith
    field_simp [ha_ne, ha1_ne]
    ring
  have hscaled := mul_le_mul_of_nonneg_left hmain hcoef_pos.le
  calc
    Real.sinh (((alpha + 1) / 2) * x) ^ 2 =
        Real.sinh m ^ 2 := by rfl
    _ = ((alpha + 1) ^ 2 / (4 * alpha)) *
          ((1 - k ^ 2) * Real.sinh m ^ 2) := by
        rw [← mul_assoc, hcoef, one_mul]
    _ ≤ ((alpha + 1) ^ 2 / (4 * alpha)) *
        (Real.sinh x * Real.sinh (alpha * x)) := hscaled

lemma rpow_sub_one_eq_two_mul_rpow_half_mul_sinh
    {t p : ℝ} (ht : 0 < t) :
    t ^ p - 1 = 2 * t ^ (p / 2) * Real.sinh ((p * Real.log t) / 2) := by
  rw [Real.rpow_def_of_pos ht, Real.rpow_def_of_pos ht]
  rw [Real.sinh_eq]
  ring_nf
  rw [← Real.exp_add (Real.log t * p * (1 / 2)) (Real.log t * p * (-1 / 2))]
  rw [show Real.log t * p * (1 / 2) + Real.log t * p * (-1 / 2) = 0 by ring]
  rw [Real.exp_zero, sq, ← Real.exp_add]
  rw [show Real.log t * p * (1 / 2) + Real.log t * p * (1 / 2) =
    Real.log t * p by ring]

lemma power_difference_midpoint_normalized_of_one_le
    {alpha t : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (ht : 1 ≤ t) :
    (t ^ ((alpha + 1) / 2) - 1) ^ 2 ≤
      ((alpha + 1) ^ 2 / (4 * alpha)) * ((t - 1) * (t ^ alpha - 1)) := by
  let delta : ℝ := (alpha + 1) / 2
  let x : ℝ := Real.log t / 2
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg (Real.log_nonneg ht) (by norm_num)
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    positivity
  have hpow_half_sq (p : ℝ) :
      (t ^ (p / 2)) ^ 2 = t ^ p := by
    rw [sq, ← Real.rpow_add ht_pos]
    congr 1
    ring
  have hpow_half_mul :
      t ^ ((1 : ℝ) / 2) * t ^ (alpha / 2) = t ^ delta := by
    rw [← Real.rpow_add ht_pos]
    congr 1
    dsimp [delta]
    ring
  have hdelta_arg :
      ((delta * Real.log t) / 2) = delta * x := by
    dsimp [x]
    ring
  have halpha_arg :
      ((alpha * Real.log t) / 2) = alpha * x := by
    dsimp [x]
    ring
  have hone_arg :
      (((1 : ℝ) * Real.log t) / 2) = x := by
    dsimp [x]
    ring
  have hsub_delta :
      t ^ delta - 1 = 2 * t ^ (delta / 2) * Real.sinh (delta * x) := by
    simpa [hdelta_arg] using
      (rpow_sub_one_eq_two_mul_rpow_half_mul_sinh (t := t) (p := delta) ht_pos)
  have hsub_alpha :
      t ^ alpha - 1 = 2 * t ^ (alpha / 2) * Real.sinh (alpha * x) := by
    simpa [halpha_arg] using
      (rpow_sub_one_eq_two_mul_rpow_half_mul_sinh (t := t) (p := alpha) ht_pos)
  have hsub_one :
      t - 1 = 2 * t ^ ((1 : ℝ) / 2) * Real.sinh x := by
    simpa [hone_arg, Real.rpow_one] using
      (rpow_sub_one_eq_two_mul_rpow_half_mul_sinh (t := t) (p := (1 : ℝ)) ht_pos)
  have hsinh :
      Real.sinh (delta * x) ^ 2 ≤
        ((alpha + 1) ^ 2 / (4 * alpha)) *
          (Real.sinh x * Real.sinh (alpha * x)) := by
    dsimp [delta]
    exact sinh_sq_mid_le_const_mul_sinh_mul_sinh halpha0 halpha1 hx_nonneg
  have hfactor_nonneg : 0 ≤ 4 * t ^ delta := by
    positivity
  have hscaled :
      4 * t ^ delta * Real.sinh (delta * x) ^ 2 ≤
        4 * t ^ delta *
          (((alpha + 1) ^ 2 / (4 * alpha)) *
            (Real.sinh x * Real.sinh (alpha * x))) :=
    mul_le_mul_of_nonneg_left hsinh hfactor_nonneg
  calc
    (t ^ ((alpha + 1) / 2) - 1) ^ 2 =
        4 * t ^ delta * Real.sinh (delta * x) ^ 2 := by
      dsimp [delta] at hsub_delta ⊢
      rw [hsub_delta]
      rw [show (2 * t ^ (((alpha + 1) / 2 / 2)) *
          Real.sinh (((alpha + 1) / 2 * x))) ^ 2 =
          4 * (t ^ (((alpha + 1) / 2 / 2))) ^ 2 *
            Real.sinh (((alpha + 1) / 2 * x)) ^ 2 by ring]
      rw [hpow_half_sq]
    _ ≤ 4 * t ^ delta *
          (((alpha + 1) ^ 2 / (4 * alpha)) *
            (Real.sinh x * Real.sinh (alpha * x))) := hscaled
    _ = ((alpha + 1) ^ 2 / (4 * alpha)) * ((t - 1) * (t ^ alpha - 1)) := by
      rw [hsub_one, hsub_alpha]
      rw [show (2 * t ^ ((1 : ℝ) / 2) * Real.sinh x) *
          (2 * t ^ (alpha / 2) * Real.sinh (alpha * x)) =
          4 * (t ^ ((1 : ℝ) / 2) * t ^ (alpha / 2)) *
            (Real.sinh x * Real.sinh (alpha * x)) by ring]
      rw [hpow_half_mul]
      ring

lemma power_difference_midpoint_normalized_of_le_one
    {alpha t : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (ht_pos : 0 < t) (ht : t ≤ 1) :
    (t ^ ((alpha + 1) / 2) - 1) ^ 2 ≤
      ((alpha + 1) ^ 2 / (4 * alpha)) * ((t - 1) * (t ^ alpha - 1)) := by
  let delta : ℝ := (alpha + 1) / 2
  let x : ℝ := -Real.log t / 2
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg (neg_nonneg.mpr (Real.log_nonpos ht_pos.le ht)) (by norm_num)
  have hpow_half_sq (p : ℝ) :
      (t ^ (p / 2)) ^ 2 = t ^ p := by
    rw [sq, ← Real.rpow_add ht_pos]
    congr 1
    ring
  have hpow_half_mul :
      t ^ ((1 : ℝ) / 2) * t ^ (alpha / 2) = t ^ delta := by
    rw [← Real.rpow_add ht_pos]
    congr 1
    dsimp [delta]
    ring
  have hdelta_arg :
      ((delta * Real.log t) / 2) = -(delta * x) := by
    dsimp [x]
    ring
  have halpha_arg :
      ((alpha * Real.log t) / 2) = -(alpha * x) := by
    dsimp [x]
    ring
  have hone_arg :
      (((1 : ℝ) * Real.log t) / 2) = -x := by
    dsimp [x]
    ring
  have hsub_delta :
      t ^ delta - 1 = -(2 * t ^ (delta / 2) * Real.sinh (delta * x)) := by
    rw [rpow_sub_one_eq_two_mul_rpow_half_mul_sinh (t := t) (p := delta) ht_pos]
    rw [hdelta_arg, Real.sinh_neg]
    ring
  have hsub_alpha :
      t ^ alpha - 1 = -(2 * t ^ (alpha / 2) * Real.sinh (alpha * x)) := by
    rw [rpow_sub_one_eq_two_mul_rpow_half_mul_sinh (t := t) (p := alpha) ht_pos]
    rw [halpha_arg, Real.sinh_neg]
    ring
  have hsub_one :
      t - 1 = -(2 * t ^ ((1 : ℝ) / 2) * Real.sinh x) := by
    rw [show t - 1 = t ^ (1 : ℝ) - 1 by rw [Real.rpow_one]]
    rw [rpow_sub_one_eq_two_mul_rpow_half_mul_sinh (t := t) (p := (1 : ℝ)) ht_pos]
    rw [hone_arg, Real.sinh_neg]
    ring
  have hsinh :
      Real.sinh (delta * x) ^ 2 ≤
        ((alpha + 1) ^ 2 / (4 * alpha)) *
          (Real.sinh x * Real.sinh (alpha * x)) := by
    dsimp [delta]
    exact sinh_sq_mid_le_const_mul_sinh_mul_sinh halpha0 halpha1 hx_nonneg
  have hfactor_nonneg : 0 ≤ 4 * t ^ delta := by
    positivity
  have hscaled :
      4 * t ^ delta * Real.sinh (delta * x) ^ 2 ≤
        4 * t ^ delta *
          (((alpha + 1) ^ 2 / (4 * alpha)) *
            (Real.sinh x * Real.sinh (alpha * x))) :=
    mul_le_mul_of_nonneg_left hsinh hfactor_nonneg
  calc
    (t ^ ((alpha + 1) / 2) - 1) ^ 2 =
        4 * t ^ delta * Real.sinh (delta * x) ^ 2 := by
      dsimp [delta] at hsub_delta ⊢
      rw [hsub_delta]
      rw [show (-(2 * t ^ (((alpha + 1) / 2 / 2)) *
          Real.sinh (((alpha + 1) / 2 * x)))) ^ 2 =
          4 * (t ^ (((alpha + 1) / 2 / 2))) ^ 2 *
            Real.sinh (((alpha + 1) / 2 * x)) ^ 2 by ring]
      rw [hpow_half_sq]
    _ ≤ 4 * t ^ delta *
          (((alpha + 1) ^ 2 / (4 * alpha)) *
            (Real.sinh x * Real.sinh (alpha * x))) := hscaled
    _ = ((alpha + 1) ^ 2 / (4 * alpha)) * ((t - 1) * (t ^ alpha - 1)) := by
      rw [hsub_one, hsub_alpha]
      rw [show (-(2 * t ^ ((1 : ℝ) / 2) * Real.sinh x)) *
          (-(2 * t ^ (alpha / 2) * Real.sinh (alpha * x))) =
          4 * (t ^ ((1 : ℝ) / 2) * t ^ (alpha / 2)) *
            (Real.sinh x * Real.sinh (alpha * x)) by ring]
      rw [hpow_half_mul]
      ring

lemma power_difference_midpoint_normalized_of_lt_alpha
    {alpha t : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (ht : 0 < t) :
    (t ^ ((alpha + 1) / 2) - 1) ^ 2 ≤
      ((alpha + 1) ^ 2 / (4 * alpha)) * ((t - 1) * (t ^ alpha - 1)) := by
  by_cases ht_ge : 1 ≤ t
  · exact power_difference_midpoint_normalized_of_one_le halpha0 halpha1 ht_ge
  · exact power_difference_midpoint_normalized_of_le_one halpha0 halpha1 ht
      (le_of_not_ge ht_ge)

lemma power_difference_midpoint_normalized
    {beta t : ℝ} (hbeta0 : 0 < beta) (ht : 0 < t) :
    (t ^ ((beta + 1) / 2) - 1) ^ 2 ≤
      ((beta + 1) ^ 2 / (4 * beta)) * ((t - 1) * (t ^ beta - 1)) := by
  by_cases hbeta_lt : beta < 1
  · exact power_difference_midpoint_normalized_of_lt_alpha hbeta0 hbeta_lt ht
  · by_cases hbeta_eq : beta = 1
    · subst beta
      simp [Real.rpow_one]
      ring_nf
      exact le_rfl
    · have hbeta_gt : 1 < beta := lt_of_le_of_ne (le_of_not_gt hbeta_lt)
        (fun h : 1 = beta => hbeta_eq h.symm)
      let a : ℝ := 1 / beta
      let s : ℝ := t ^ beta
      have ha0 : 0 < a := by
        dsimp [a]
        positivity
      have ha1 : a < 1 := by
        dsimp [a]
        rw [div_lt_one₀ hbeta0]
        exact hbeta_gt
      have hs_pos : 0 < s := by
        dsimp [s]
        exact Real.rpow_pos_of_pos ht beta
      have hbase :
          (s ^ ((a + 1) / 2) - 1) ^ 2 ≤
            ((a + 1) ^ 2 / (4 * a)) * ((s - 1) * (s ^ a - 1)) :=
        power_difference_midpoint_normalized_of_lt_alpha ha0 ha1 hs_pos
      have hs_a : s ^ a = t := by
        dsimp [s, a]
        rw [← Real.rpow_mul ht.le]
        have hbeta_ne : beta ≠ 0 := ne_of_gt hbeta0
        rw [mul_one_div_cancel hbeta_ne, Real.rpow_one]
      have hs_mid : s ^ ((a + 1) / 2) = t ^ ((beta + 1) / 2) := by
        dsimp [s, a]
        rw [← Real.rpow_mul ht.le]
        congr 1
        have hbeta_ne : beta ≠ 0 := ne_of_gt hbeta0
        field_simp [hbeta_ne]
        ring
      have hcoef :
          (a + 1) ^ 2 / (4 * a) = (beta + 1) ^ 2 / (4 * beta) := by
        dsimp [a]
        have hbeta_ne : beta ≠ 0 := ne_of_gt hbeta0
        field_simp [hbeta_ne]
        ring
      have hprod :
          (s - 1) * (s ^ a - 1) = (t - 1) * (t ^ beta - 1) := by
        rw [hs_a]
        dsimp [s]
        ring
      calc
        (t ^ ((beta + 1) / 2) - 1) ^ 2 =
            (s ^ ((a + 1) / 2) - 1) ^ 2 := by rw [hs_mid]
        _ ≤ ((a + 1) ^ 2 / (4 * a)) * ((s - 1) * (s ^ a - 1)) := hbase
        _ = ((beta + 1) ^ 2 / (4 * beta)) *
              ((t - 1) * (t ^ beta - 1)) := by
            rw [hcoef, hprod]

lemma power_difference_normalized_of_lt_alpha
    {alpha gamma t : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hgamma_pos : 0 < gamma) (hrel : 2 * gamma ≤ alpha + 1)
    (ht : 0 < t) :
    (t ^ gamma - 1) ^ 2 ≤
      ((alpha + 1) ^ 2 / (4 * alpha)) * ((t - 1) * (t ^ alpha - 1)) := by
  let delta : ℝ := (alpha + 1) / 2
  have hgamma_le_delta : gamma ≤ delta := by
    dsimp [delta]
    linarith
  have hdelta_nonneg : 0 ≤ delta := by
    dsimp [delta]
    positivity
  have hgamma_nonneg : 0 ≤ gamma := hgamma_pos.le
  have hmid :
      (t ^ delta - 1) ^ 2 ≤
        ((alpha + 1) ^ 2 / (4 * alpha)) * ((t - 1) * (t ^ alpha - 1)) := by
    dsimp [delta]
    exact power_difference_midpoint_normalized_of_lt_alpha halpha0 halpha1 ht
  by_cases ht_ge : 1 ≤ t
  · have hγ_ge_one : 1 ≤ t ^ gamma := Real.one_le_rpow ht_ge hgamma_nonneg
    have hδ_ge_one : 1 ≤ t ^ delta := Real.one_le_rpow ht_ge hdelta_nonneg
    have hγ_le_δ : t ^ gamma ≤ t ^ delta :=
      Real.rpow_le_rpow_of_exponent_le ht_ge hgamma_le_delta
    have hdiff_le : t ^ gamma - 1 ≤ t ^ delta - 1 :=
      sub_le_sub_right hγ_le_δ 1
    have hsq_le : (t ^ gamma - 1) ^ 2 ≤ (t ^ delta - 1) ^ 2 := by
      have hmul := mul_le_mul hdiff_le hdiff_le
        (sub_nonneg.mpr hγ_ge_one) (sub_nonneg.mpr hδ_ge_one)
      simpa [sq] using hmul
    exact hsq_le.trans hmid
  · have ht_le : t ≤ 1 := le_of_not_ge ht_ge
    have hγ_le_one : t ^ gamma ≤ 1 :=
      Real.rpow_le_one ht.le ht_le hgamma_nonneg
    have hδ_le_one : t ^ delta ≤ 1 :=
      Real.rpow_le_one ht.le ht_le hdelta_nonneg
    have hδ_le_γ : t ^ delta ≤ t ^ gamma :=
      Real.rpow_le_rpow_of_exponent_ge ht ht_le hgamma_le_delta
    have hdiff_le : 1 - t ^ gamma ≤ 1 - t ^ delta :=
      sub_le_sub_left hδ_le_γ 1
    have hsq_le : (t ^ gamma - 1) ^ 2 ≤ (t ^ delta - 1) ^ 2 := by
      have hsq : (1 - t ^ gamma) ^ 2 ≤ (1 - t ^ delta) ^ 2 :=
        by
          have hmul := mul_le_mul hdiff_le hdiff_le
            (sub_nonneg.mpr hγ_le_one) (sub_nonneg.mpr hδ_le_one)
          simpa [sq] using hmul
      nlinarith
    exact hsq_le.trans hmid

lemma power_difference_normalized_of_one_le_alpha_of_one_lt_gamma
    {alpha gamma t : ℝ}
    (_halpha : 1 ≤ alpha) (hgamma : 1 < gamma)
    (hrel : 2 * gamma ≤ alpha + 1) (ht : 0 < t) :
    (t ^ gamma - 1) ^ 2 ≤
      (gamma ^ 2 / (2 * gamma - 1)) * ((t - 1) * (t ^ alpha - 1)) := by
  let beta : ℝ := 2 * gamma - 1
  have hbeta0 : 0 < beta := by
    dsimp [beta]
    linarith
  have hbeta_le_alpha : beta ≤ alpha := by
    dsimp [beta]
    linarith
  have hgamma_eq : gamma = (beta + 1) / 2 := by
    dsimp [beta]
    ring
  have hcoef :
      (beta + 1) ^ 2 / (4 * beta) = gamma ^ 2 / (2 * gamma - 1) := by
    dsimp [beta]
    have hden_ne : 2 * gamma - 1 ≠ 0 := by linarith
    field_simp [hden_ne]
    ring
  have hmid :
      (t ^ gamma - 1) ^ 2 ≤
        (gamma ^ 2 / (2 * gamma - 1)) * ((t - 1) * (t ^ beta - 1)) := by
    simpa [hgamma_eq, hcoef] using
      power_difference_midpoint_normalized (beta := beta) (t := t) hbeta0 ht
  have hprod :
      (t - 1) * (t ^ beta - 1) ≤ (t - 1) * (t ^ alpha - 1) := by
    by_cases ht_ge : 1 ≤ t
    · have hpow : t ^ beta ≤ t ^ alpha :=
        Real.rpow_le_rpow_of_exponent_le ht_ge hbeta_le_alpha
      exact mul_le_mul_of_nonneg_left (sub_le_sub_right hpow 1)
        (sub_nonneg.mpr ht_ge)
    · have ht_le : t ≤ 1 := le_of_not_ge ht_ge
      have hpow : t ^ alpha ≤ t ^ beta :=
        Real.rpow_le_rpow_of_exponent_ge ht ht_le hbeta_le_alpha
      exact mul_le_mul_of_nonpos_left (sub_le_sub_right hpow 1)
        (sub_nonpos.mpr ht_le)
  have hcoef_nonneg : 0 ≤ gamma ^ 2 / (2 * gamma - 1) := by
    positivity
  exact hmid.trans (mul_le_mul_of_nonneg_left hprod hcoef_nonneg)

def chiStrong1Formula (p : CM2Params) (uStar vStar : ℝ) : ℝ :=
  Real.sqrt
    (p.b *
      (16 * (1 + betaTilde p.β * vStar) * p.μ /
        ((2 * p.m - 1) * p.ν ^ 2 * CAlphaGamma p.α p.γ *
          uStar ^ (2 * p.γ - p.α + 2 * p.m - 2))))

def chiBarFormula (p : CM2Params) : ℝ :=
  if p.m = 1 then
    p.a / (2 * p.μ * Theta_beta (p.β - 1))
  else
    p.b / (p.μ * Theta_beta (p.β - 1))

def vABLowerFormula (p : CM2Params) : ℝ :=
  if p.m = 1 then
    p.ν / p.μ * (p.a / (2 * p.b)) ^ (p.γ / p.α)
  else
    p.ν / p.μ *
      (min 1
        ((p.a / (2 * p.b)) ^
          max (1 / (p.m - 1)) (1 / p.α))) ^ p.γ

def chiStrong2Formula (p : CM2Params) (uStar : ℝ) : ℝ :=
  min (chiBarFormula p)
    (Real.sqrt
      (p.b *
        (16 * (1 + vABLowerFormula p) ^ (2 * p.β) * p.μ /
          ((2 * p.m - 1) * p.ν ^ 2 * CAlphaGamma p.α p.γ *
            uStar ^ (2 * p.γ - p.α + 2 * p.m - 2)))))

def chiStrong3Formula (p : CM2Params) (M0 uStar vStar : ℝ) : ℝ :=
  p.a / (p.ν * uStar ^ (p.m + p.γ - 1)) *
    (1 / (2 + p.β * vStar * M0 ^ 2))

def chiStrong4Formula (p : CM2Params) (M0 uStar : ℝ) : ℝ :=
  min (chiBarFormula p)
    ((1 + vABLowerFormula p) ^ p.β *
      chiStrong3Formula p M0 uStar
        (p.ν / p.μ * uStar ^ p.γ))

lemma chiStrong1Formula_nonneg (p : CM2Params) (uStar vStar : ℝ) :
    0 ≤ chiStrong1Formula p uStar vStar := by
  unfold chiStrong1Formula
  exact Real.sqrt_nonneg _

lemma chiStrong1Formula_pos
    (p : CM2Params) {uStar vStar : ℝ}
    (hb : 0 < p.b) (hm : 1 ≤ p.m)
    (huStar : 0 < uStar) (hvStar : 0 ≤ vStar) :
    0 < chiStrong1Formula p uStar vStar := by
  unfold chiStrong1Formula
  apply Real.sqrt_pos.mpr
  apply mul_pos hb
  apply div_pos
  · have hfactor : 0 < 1 + betaTilde p.β * vStar := by
      have hmul : 0 ≤ betaTilde p.β * vStar :=
        mul_nonneg (betaTilde_nonneg p.β) hvStar
      linarith
    exact mul_pos (mul_pos (by norm_num) hfactor) p.hμ
  · have hmpos : 0 < 2 * p.m - 1 := by linarith
    have hνsq : 0 < p.ν ^ 2 := sq_pos_of_ne_zero (ne_of_gt p.hν)
    have hC : 0 < CAlphaGamma p.α p.γ := CAlphaGamma_pos p.hα p.hγ
    have hupow : 0 < uStar ^ (2 * p.γ - p.α + 2 * p.m - 2) :=
      Real.rpow_pos_of_pos huStar _
    exact mul_pos (mul_pos (mul_pos hmpos hνsq) hC) hupow

lemma chiStrong3Formula_pos
    (p : CM2Params) {M0 uStar vStar : ℝ}
    (ha : 0 < p.a) (huStar : 0 < uStar)
    (hvStar : 0 ≤ vStar) :
    0 < chiStrong3Formula p M0 uStar vStar := by
  unfold chiStrong3Formula
  apply mul_pos
  · exact div_pos ha (mul_pos p.hν (Real.rpow_pos_of_pos huStar _))
  · apply div_pos zero_lt_one
    have hnonneg : 0 ≤ p.β * vStar * M0 ^ 2 := by
      exact mul_nonneg (mul_nonneg p.hβ hvStar) (sq_nonneg M0)
    linarith

lemma chiStrong3Formula_nonneg
    (p : CM2Params) {M0 uStar vStar : ℝ}
    (huStar : 0 < uStar) (hvStar : 0 ≤ vStar) :
    0 ≤ chiStrong3Formula p M0 uStar vStar := by
  unfold chiStrong3Formula
  apply mul_nonneg
  · exact div_nonneg p.ha
      (mul_pos p.hν (Real.rpow_pos_of_pos huStar _)).le
  · apply div_nonneg zero_le_one
    have hnonneg : 0 ≤ p.β * vStar * M0 ^ 2 := by
      exact mul_nonneg (mul_nonneg p.hβ hvStar) (sq_nonneg M0)
    linarith

lemma chiBarFormula_pos
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b)
    (hβ : 1 ≤ p.β) :
    0 < chiBarFormula p := by
  unfold chiBarFormula
  by_cases hm_eq : p.m = 1
  · rw [if_pos hm_eq]
    apply div_pos ha
    exact mul_pos (mul_pos (by norm_num) p.hμ)
      (Theta_beta_pos_of_nonneg (by linarith))
  · rw [if_neg hm_eq]
    apply div_pos hb
    exact mul_pos p.hμ (Theta_beta_pos_of_nonneg (by linarith))

lemma chiBarFormula_nonneg
    (p : CM2Params) (hβ : 1 ≤ p.β) :
    0 ≤ chiBarFormula p := by
  unfold chiBarFormula
  by_cases hm_eq : p.m = 1
  · rw [if_pos hm_eq]
    apply div_nonneg p.ha
    exact (mul_pos (mul_pos (by norm_num) p.hμ)
      (Theta_beta_pos_of_nonneg (by linarith))).le
  · rw [if_neg hm_eq]
    apply div_nonneg p.hb
    exact (mul_pos p.hμ (Theta_beta_pos_of_nonneg (by linarith))).le

lemma vABLowerFormula_pos
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m) :
    0 < vABLowerFormula p := by
  unfold vABLowerFormula
  by_cases hm_eq : p.m = 1
  · rw [if_pos hm_eq]
    exact mul_pos (div_pos p.hν p.hμ)
      (Real.rpow_pos_of_pos (div_pos ha (mul_pos (by norm_num) hb)) _)
  · rw [if_neg hm_eq]
    have hm_gt : 1 < p.m := lt_of_le_of_ne hm (fun h => hm_eq h.symm)
    have hbase : 0 < p.a / (2 * p.b) :=
      div_pos ha (mul_pos (by norm_num) hb)
    have hpow :
        0 <
          (p.a / (2 * p.b)) ^
            max (1 / (p.m - 1)) (1 / p.α) :=
      Real.rpow_pos_of_pos hbase _
    have hmin :
        0 <
          min 1
            ((p.a / (2 * p.b)) ^
              max (1 / (p.m - 1)) (1 / p.α)) :=
      lt_min zero_lt_one hpow
    exact mul_pos (div_pos p.hν p.hμ)
      (Real.rpow_pos_of_pos hmin _)

lemma chiStrong2Formula_pos
    (p : CM2Params) {uStar : ℝ}
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m) (hβ : 1 ≤ p.β) (huStar : 0 < uStar) :
    0 < chiStrong2Formula p uStar := by
  unfold chiStrong2Formula
  apply lt_min
  · exact chiBarFormula_pos p ha hb hβ
  · apply Real.sqrt_pos.mpr
    apply mul_pos hb
    apply div_pos
    · have hvpos : 0 < 1 + vABLowerFormula p :=
        by linarith [vABLowerFormula_pos p ha hb hm]
      exact mul_pos (mul_pos (by norm_num)
        (Real.rpow_pos_of_pos hvpos _)) p.hμ
    · have hmpos : 0 < 2 * p.m - 1 := by linarith
      have hνsq : 0 < p.ν ^ 2 := sq_pos_of_ne_zero (ne_of_gt p.hν)
      have hC : 0 < CAlphaGamma p.α p.γ := CAlphaGamma_pos p.hα p.hγ
      have hupow : 0 < uStar ^ (2 * p.γ - p.α + 2 * p.m - 2) :=
        Real.rpow_pos_of_pos huStar _
      exact mul_pos (mul_pos (mul_pos hmpos hνsq) hC) hupow

lemma chiStrong4Formula_pos
    (p : CM2Params) {M0 uStar : ℝ}
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m) (hβ : 1 ≤ p.β) (huStar : 0 < uStar) :
    0 < chiStrong4Formula p M0 uStar := by
  unfold chiStrong4Formula
  apply lt_min
  · exact chiBarFormula_pos p ha hb hβ
  · have hvpos : 0 < 1 + vABLowerFormula p :=
      by linarith [vABLowerFormula_pos p ha hb hm]
    have hveq_nonneg : 0 ≤ p.ν / p.μ * uStar ^ p.γ := by
      exact (mul_pos (div_pos p.hν p.hμ)
        (Real.rpow_pos_of_pos huStar _)).le
    exact mul_pos
      (Real.rpow_pos_of_pos hvpos _)
      (chiStrong3Formula_pos p ha huStar hveq_nonneg)

lemma chiStrong2Formula_nonneg
    (p : CM2Params) (uStar : ℝ) (hβ : 1 ≤ p.β) :
    0 ≤ chiStrong2Formula p uStar := by
  unfold chiStrong2Formula
  exact le_min (chiBarFormula_nonneg p hβ) (Real.sqrt_nonneg _)

lemma chiStrong4Formula_nonneg
    (p : CM2Params) {M0 uStar : ℝ}
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m) (hβ : 1 ≤ p.β) (huStar : 0 < uStar) :
    0 ≤ chiStrong4Formula p M0 uStar := by
  exact (chiStrong4Formula_pos p ha hb hm hβ huStar).le

lemma chiStrong2Formula_le_chiBarFormula
    (p : CM2Params) (uStar : ℝ) :
    chiStrong2Formula p uStar ≤ chiBarFormula p := by
  unfold chiStrong2Formula
  exact min_le_left _ _

lemma chiStrong4Formula_le_chiBarFormula
    (p : CM2Params) (M0 uStar : ℝ) :
    chiStrong4Formula p M0 uStar ≤ chiBarFormula p := by
  unfold chiStrong4Formula
  exact min_le_left _ _

lemma chi_lt_chiBarFormula_of_lt_chiStrong2Formula
    (p : CM2Params) {chi uStar : ℝ}
    (hchi : chi < chiStrong2Formula p uStar) :
    chi < chiBarFormula p :=
  lt_of_lt_of_le hchi (chiStrong2Formula_le_chiBarFormula p uStar)

lemma chi_lt_chiBarFormula_of_lt_chiStrong4Formula
    (p : CM2Params) {chi M0 uStar : ℝ}
    (hchi : chi < chiStrong4Formula p M0 uStar) :
    chi < chiBarFormula p :=
  lt_of_lt_of_le hchi (chiStrong4Formula_le_chiBarFormula p M0 uStar)

def minimalUpperBoundFormula (CN qPrime qDoublePrime uStar : ℝ) : ℝ :=
  CN * (uStar ^ qPrime + uStar ^ qDoublePrime)

def minimalVLowerFormula
    (COmega gamma uStar uBar : ℝ) : ℝ :=
  COmega *
    if gamma ≤ 1 then
      uStar * uBar ^ (gamma - 1)
    else
      uStar ^ gamma

def GammaMinimalFormula
    (gamma uStar uBar : ℝ) : ℝ :=
  if gamma ≤ 1 then
    uStar ^ (gamma - 1) * uBar
  else
    gamma * uBar ^ gamma

def chiMinimal1Formula
    (p : CM2Params) (lambdaStar uStar uBar vLower : ℝ) : ℝ :=
  min (min (chiBeta p / 2) (Real.sqrt (chiBeta p)))
    (2 * Real.sqrt (p.μ * lambdaStar) * (1 + vLower) ^ p.β /
      (p.ν * GammaMinimalFormula p.γ uStar uBar))

def chiMinimal2Formula
    (p : CM2Params) (uBar vLower : ℝ) : ℝ :=
  min (min (chiBeta p / 2) (Real.sqrt (chiBeta p)))
    (p.μ * (1 + vLower) ^ p.β / (p.ν * uBar))

lemma minimalUpperBoundFormula_pos
    {CN qPrime qDoublePrime uStar : ℝ}
    (hCN : 0 < CN) (huStar : 0 < uStar) :
    0 < minimalUpperBoundFormula CN qPrime qDoublePrime uStar := by
  unfold minimalUpperBoundFormula
  exact mul_pos hCN
    (add_pos
      (Real.rpow_pos_of_pos huStar _)
      (Real.rpow_pos_of_pos huStar _))

lemma minimalVLowerFormula_pos
    {COmega gamma uStar uBar : ℝ}
    (hCOmega : 0 < COmega) (huStar : 0 < uStar) (huBar : 0 < uBar) :
    0 < minimalVLowerFormula COmega gamma uStar uBar := by
  unfold minimalVLowerFormula
  apply mul_pos hCOmega
  by_cases hle : gamma ≤ 1
  · rw [if_pos hle]
    exact mul_pos huStar (Real.rpow_pos_of_pos huBar _)
  · rw [if_neg hle]
    exact Real.rpow_pos_of_pos huStar _

lemma Paper3Constants.minimalVLower_pos
    {D : BoundedDomainData} {p : CM2Params} (C : Paper3Constants D p)
    {uStar : ℝ}
    (huStar : 0 < uStar)
    (hUpper : 0 < C.eventualMinimalUBound uStar) :
    0 <
      minimalVLowerFormula
        C.gaussianLowerConst p.γ uStar (C.eventualMinimalUBound uStar) :=
  minimalVLowerFormula_pos C.gaussianLowerConst_pos huStar hUpper

lemma GammaMinimalFormula_pos
    {gamma uStar uBar : ℝ}
    (hgamma : 0 < gamma) (huStar : 0 < uStar) (huBar : 0 < uBar) :
    0 < GammaMinimalFormula gamma uStar uBar := by
  unfold GammaMinimalFormula
  by_cases hle : gamma ≤ 1
  · rw [if_pos hle]
    exact mul_pos (Real.rpow_pos_of_pos huStar _) huBar
  · rw [if_neg hle]
    exact mul_pos hgamma (Real.rpow_pos_of_pos huBar _)

lemma chiMinimal1Formula_pos
    (p : CM2Params) {lambdaStar uStar uBar vLower : ℝ}
    (hβ : 1 ≤ p.β) (hlambda : 0 < lambdaStar)
    (huStar : 0 < uStar) (huBar : 0 < uBar) (hvLower : 0 ≤ vLower) :
    0 < chiMinimal1Formula p lambdaStar uStar uBar vLower := by
  unfold chiMinimal1Formula
  apply lt_min
  · exact min_chiBeta_half_sqrt_pos_of_one_le_beta p hβ
  · apply div_pos
    · exact mul_pos
        (mul_pos (by norm_num)
          (Real.sqrt_pos.mpr (mul_pos p.hμ hlambda)))
        (Real.rpow_pos_of_pos (by linarith : 0 < 1 + vLower) _)
    · exact mul_pos p.hν
        (GammaMinimalFormula_pos p.hγ huStar huBar)

lemma chiMinimal2Formula_pos
    (p : CM2Params) {uBar vLower : ℝ}
    (hβ : 1 ≤ p.β) (huBar : 0 < uBar) (hvLower : 0 ≤ vLower) :
    0 < chiMinimal2Formula p uBar vLower := by
  unfold chiMinimal2Formula
  apply lt_min
  · exact min_chiBeta_half_sqrt_pos_of_one_le_beta p hβ
  · apply div_pos
    · exact mul_pos p.hμ
        (Real.rpow_pos_of_pos (by linarith : 0 < 1 + vLower) _)
    · exact mul_pos p.hν huBar

lemma chiMinimal1Formula_le_min_half_sqrt
    (p : CM2Params) (lambdaStar uStar uBar vLower : ℝ) :
    chiMinimal1Formula p lambdaStar uStar uBar vLower ≤
      min (chiBeta p / 2) (Real.sqrt (chiBeta p)) := by
  unfold chiMinimal1Formula
  exact min_le_left _ _

lemma chiMinimal2Formula_le_min_half_sqrt
    (p : CM2Params) (uBar vLower : ℝ) :
    chiMinimal2Formula p uBar vLower ≤
      min (chiBeta p / 2) (Real.sqrt (chiBeta p)) := by
  unfold chiMinimal2Formula
  exact min_le_left _ _

lemma chi_lt_chiBeta_of_lt_chiMinimal1Formula
    (p : CM2Params) {chi lambdaStar uStar uBar vLower : ℝ}
    (hβ : 1 ≤ p.β)
    (hchi : chi < chiMinimal1Formula p lambdaStar uStar uBar vLower) :
    chi < chiBeta p :=
  lt_chiBeta_of_lt_min_half_sqrt p hβ
    (lt_of_lt_of_le hchi
      (chiMinimal1Formula_le_min_half_sqrt p lambdaStar uStar uBar vLower))

lemma chi_lt_chiBeta_of_lt_chiMinimal2Formula
    (p : CM2Params) {chi uBar vLower : ℝ}
    (hβ : 1 ≤ p.β)
    (hchi : chi < chiMinimal2Formula p uBar vLower) :
    chi < chiBeta p :=
  lt_chiBeta_of_lt_min_half_sqrt p hβ
    (lt_of_lt_of_le hchi
      (chiMinimal2Formula_le_min_half_sqrt p uBar vLower))

def EventuallyUpperBoundMinimalConclusion
    (D : BoundedDomainData) (p : CM2Params) (C : Paper3Constants D p)
    (u : ℝ → D.Point → ℝ) : Prop :=
  ∀ uStar > 0, HasInitialMass D u uStar →
    ∀ᶠ t in atTop, D.supNorm (u t) ≤ C.eventualMinimalUBound uStar

lemma EventuallyUpperBoundMinimalConclusion.bound
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    {u : ℝ → D.Point → ℝ}
    (h : EventuallyUpperBoundMinimalConclusion D p C u)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hmass : HasInitialMass D u uStar) :
    ∀ᶠ t in atTop, D.supNorm (u t) ≤ C.eventualMinimalUBound uStar :=
  h uStar huStar hmass

def NonminimalGlobalStabilityCondition
    (D : BoundedDomainData) (p : CM2Params) (C : Paper3Constants D p)
    (uStar : ℝ) : Prop :=
  (1 ≤ p.m ∧ p.α + 1 ≥ 2 * p.γ ∧
      0 < p.χ₀ ∧ p.χ₀ < C.chiStrong1 uStar) ∨
    (1 ≤ p.m ∧ 1 ≤ p.β ∧ p.α + 1 ≥ 2 * p.γ ∧
      0 < p.χ₀ ∧ p.χ₀ < C.chiStrong2 uStar) ∨
    (1 ≤ p.m ∧ 1 ≤ p.γ ∧
      p.α + 1 ≥ p.m + p.γ + (if p.β = 0 then 0 else p.γ) ∧
      p.χ₀ < C.chiStrong3 uStar) ∨
    (1 ≤ p.m ∧ 1 ≤ p.β ∧ 1 ≤ p.γ ∧
      p.α + 1 ≥ p.m + 2 * p.γ ∧
      p.χ₀ < C.chiStrong4 uStar)

lemma NonminimalGlobalStabilityCondition.as_disjunction
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    {uStar : ℝ}
    (h : NonminimalGlobalStabilityCondition D p C uStar) :
    (1 ≤ p.m ∧ p.α + 1 ≥ 2 * p.γ ∧
        0 < p.χ₀ ∧ p.χ₀ < C.chiStrong1 uStar) ∨
      (1 ≤ p.m ∧ 1 ≤ p.β ∧ p.α + 1 ≥ 2 * p.γ ∧
        0 < p.χ₀ ∧ p.χ₀ < C.chiStrong2 uStar) ∨
      (1 ≤ p.m ∧ 1 ≤ p.γ ∧
        p.α + 1 ≥ p.m + p.γ + (if p.β = 0 then 0 else p.γ) ∧
        p.χ₀ < C.chiStrong3 uStar) ∨
      (1 ≤ p.m ∧ 1 ≤ p.β ∧ 1 ≤ p.γ ∧
        p.α + 1 ≥ p.m + 2 * p.γ ∧
        p.χ₀ < C.chiStrong4 uStar) :=
  h

lemma NonminimalGlobalStabilityCondition.of_chiStrong1
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    {uStar : ℝ}
    (hm : 1 ≤ p.m) (hαγ : 2 * p.γ ≤ p.α + 1)
    (hχ0 : 0 < p.χ₀) (hχ : p.χ₀ < C.chiStrong1 uStar) :
    NonminimalGlobalStabilityCondition D p C uStar := by
  exact Or.inl ⟨hm, hαγ, hχ0, hχ⟩

lemma NonminimalGlobalStabilityCondition.of_chiStrong2
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    {uStar : ℝ}
    (hm : 1 ≤ p.m) (hβ : 1 ≤ p.β) (hαγ : 2 * p.γ ≤ p.α + 1)
    (hχ0 : 0 < p.χ₀) (hχ : p.χ₀ < C.chiStrong2 uStar) :
    NonminimalGlobalStabilityCondition D p C uStar := by
  exact Or.inr (Or.inl ⟨hm, hβ, hαγ, hχ0, hχ⟩)

lemma NonminimalGlobalStabilityCondition.of_chiStrong3
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    {uStar : ℝ}
    (hm : 1 ≤ p.m) (hγ : 1 ≤ p.γ)
    (hαγ :
      p.m + p.γ + (if p.β = 0 then 0 else p.γ) ≤ p.α + 1)
    (hχ : p.χ₀ < C.chiStrong3 uStar) :
    NonminimalGlobalStabilityCondition D p C uStar := by
  exact Or.inr (Or.inr (Or.inl ⟨hm, hγ, hαγ, hχ⟩))

lemma NonminimalGlobalStabilityCondition.of_chiStrong4
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    {uStar : ℝ}
    (hm : 1 ≤ p.m) (hβ : 1 ≤ p.β) (hγ : 1 ≤ p.γ)
    (hαγ : p.m + 2 * p.γ ≤ p.α + 1)
    (hχ : p.χ₀ < C.chiStrong4 uStar) :
    NonminimalGlobalStabilityCondition D p C uStar := by
  exact Or.inr (Or.inr (Or.inr ⟨hm, hβ, hγ, hαγ, hχ⟩))

lemma NonminimalGlobalStabilityCondition.m_ge_one
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    {uStar : ℝ}
    (h : NonminimalGlobalStabilityCondition D p C uStar) :
    1 ≤ p.m := by
  rcases h with h | h | h | h
  · exact h.1
  · exact h.1
  · exact h.1
  · exact h.1

lemma NonminimalGlobalStabilityCondition.chi_lt_max_threshold
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    {uStar : ℝ}
    (h : NonminimalGlobalStabilityCondition D p C uStar) :
    p.χ₀ <
      max (max (C.chiStrong1 uStar) (C.chiStrong2 uStar))
        (max (C.chiStrong3 uStar) (C.chiStrong4 uStar)) := by
  rcases h with h | h | h | h
  · exact lt_of_lt_of_le h.2.2.2
      (le_trans (le_max_left _ _) (le_max_left _ _))
  · exact lt_of_lt_of_le h.2.2.2.2
      (le_trans (le_max_right _ _) (le_max_left _ _))
  · exact lt_of_lt_of_le h.2.2.2
      (le_trans (le_max_left _ _) (le_max_right _ _))
  · exact lt_of_lt_of_le h.2.2.2.2
      (le_trans (le_max_right _ _) (le_max_right _ _))

/-- Nonminimal stability condition written directly with the explicit strong
threshold formulas, instead of the `Paper3Constants` threshold fields. -/
def NonminimalGlobalStabilityFormulaCondition
    (p : CM2Params) (uStar vStar M0 : ℝ) : Prop :=
  (1 ≤ p.m ∧ p.α + 1 ≥ 2 * p.γ ∧
      0 < p.χ₀ ∧ p.χ₀ < chiStrong1Formula p uStar vStar) ∨
    (1 ≤ p.m ∧ 1 ≤ p.β ∧ p.α + 1 ≥ 2 * p.γ ∧
      0 < p.χ₀ ∧ p.χ₀ < chiStrong2Formula p uStar) ∨
    (1 ≤ p.m ∧ 1 ≤ p.γ ∧
      p.α + 1 ≥ p.m + p.γ + (if p.β = 0 then 0 else p.γ) ∧
      p.χ₀ < chiStrong3Formula p M0 uStar vStar) ∨
    (1 ≤ p.m ∧ 1 ≤ p.β ∧ 1 ≤ p.γ ∧
      p.α + 1 ≥ p.m + 2 * p.γ ∧
      p.χ₀ < chiStrong4Formula p M0 uStar)

lemma NonminimalGlobalStabilityFormulaCondition.chi_lt_max_threshold
    {p : CM2Params} {uStar vStar M0 : ℝ}
    (h : NonminimalGlobalStabilityFormulaCondition p uStar vStar M0) :
    p.χ₀ <
      max (max (chiStrong1Formula p uStar vStar)
          (chiStrong2Formula p uStar))
        (max (chiStrong3Formula p M0 uStar vStar)
          (chiStrong4Formula p M0 uStar)) := by
  rcases h with h | h | h | h
  · exact lt_of_lt_of_le h.2.2.2
      (le_trans (le_max_left _ _) (le_max_left _ _))
  · exact lt_of_lt_of_le h.2.2.2.2
      (le_trans (le_max_right _ _) (le_max_left _ _))
  · exact lt_of_lt_of_le h.2.2.2
      (le_trans (le_max_left _ _) (le_max_right _ _))
  · exact lt_of_lt_of_le h.2.2.2.2
      (le_trans (le_max_right _ _) (le_max_right _ _))

lemma NonminimalGlobalStabilityFormulaCondition.linearlyStable_of_max_threshold_le_critical
    (S : SpectralData) (p : CM2Params) (H : HasNeumannSpectrum S)
    (ha : 0 < p.a) (hb : 0 < p.b) {M0 : ℝ}
    (hcritical :
      max
          (max
            (chiStrong1Formula p
              (positiveEquilibrium p ⟨ha, hb⟩).1
              (positiveEquilibrium p ⟨ha, hb⟩).2)
            (chiStrong2Formula p
              (positiveEquilibrium p ⟨ha, hb⟩).1))
          (max
            (chiStrong3Formula p M0
              (positiveEquilibrium p ⟨ha, hb⟩).1
              (positiveEquilibrium p ⟨ha, hb⟩).2)
            (chiStrong4Formula p M0
              (positiveEquilibrium p ⟨ha, hb⟩).1)) ≤
        paperCriticalSensitivity S p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2)
    (h :
      NonminimalGlobalStabilityFormulaCondition p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 M0) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    LinearlyStable S p eq.1 eq.2 := by
  exact positiveEquilibrium_linearlyStable_of_chi_lt_paperCriticalSensitivity_neumann
    S p H ha hb
    (lt_of_lt_of_le (h.chi_lt_max_threshold) hcritical)

lemma NonminimalGlobalStabilityFormulaCondition.linearlyStable_of_firstNonzero_lower
    (S : SpectralData) (p : CM2Params) (H : HasNeumannSpectrum S)
    (ha : 0 < p.a) (hb : 0 < p.b) {M0 : ℝ}
    (hfirst :
      max
          (max
            (chiStrong1Formula p
              (positiveEquilibrium p ⟨ha, hb⟩).1
              (positiveEquilibrium p ⟨ha, hb⟩).2)
            (chiStrong2Formula p
              (positiveEquilibrium p ⟨ha, hb⟩).1))
          (max
            (chiStrong3Formula p M0
              (positiveEquilibrium p ⟨ha, hb⟩).1
              (positiveEquilibrium p ⟨ha, hb⟩).2)
            (chiStrong4Formula p M0
              (positiveEquilibrium p ⟨ha, hb⟩).1)) ≤
        ((1 + (positiveEquilibrium p ⟨ha, hb⟩).2) ^ p.β /
            (p.ν * p.γ *
              (positiveEquilibrium p ⟨ha, hb⟩).1 ^ (p.m + p.γ - 1))) *
          (p.μ + S.firstNonzero))
    (h :
      NonminimalGlobalStabilityFormulaCondition p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 M0) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    LinearlyStable S p eq.1 eq.2 := by
  exact h.linearlyStable_of_max_threshold_le_critical S p H ha hb
    (le_trans hfirst
      (paperCriticalSensitivity_positiveEquilibrium_ge_firstNonzero_lower
        S p H ha hb))

def MinimalGlobalStabilityCondition
    (D : BoundedDomainData) (p : CM2Params) (C : Paper3Constants D p)
    (uStar : ℝ) : Prop :=
  (0 < p.χ₀ ∧ p.χ₀ < C.chiMinimal1 uStar) ∨
    (p.γ = 1 ∧ 0 < p.χ₀ ∧ p.χ₀ < C.chiMinimal2 uStar)

lemma MinimalGlobalStabilityCondition.as_disjunction
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    {uStar : ℝ}
    (h : MinimalGlobalStabilityCondition D p C uStar) :
    (0 < p.χ₀ ∧ p.χ₀ < C.chiMinimal1 uStar) ∨
      (p.γ = 1 ∧ 0 < p.χ₀ ∧ p.χ₀ < C.chiMinimal2 uStar) :=
  h

lemma MinimalGlobalStabilityCondition.of_chiMinimal1
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    {uStar : ℝ}
    (hχ0 : 0 < p.χ₀) (hχ : p.χ₀ < C.chiMinimal1 uStar) :
    MinimalGlobalStabilityCondition D p C uStar := by
  exact Or.inl ⟨hχ0, hχ⟩

lemma MinimalGlobalStabilityCondition.of_chiMinimal2
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    {uStar : ℝ}
    (hγ : p.γ = 1) (hχ0 : 0 < p.χ₀)
    (hχ : p.χ₀ < C.chiMinimal2 uStar) :
    MinimalGlobalStabilityCondition D p C uStar := by
  exact Or.inr ⟨hγ, hχ0, hχ⟩

lemma MinimalGlobalStabilityCondition.chi_pos
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    {uStar : ℝ}
    (h : MinimalGlobalStabilityCondition D p C uStar) :
    0 < p.χ₀ := by
  rcases h with h | h
  · exact h.1
  · exact h.2.1

lemma MinimalGlobalStabilityCondition.chi_lt_max_threshold
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    {uStar : ℝ}
    (h : MinimalGlobalStabilityCondition D p C uStar) :
    p.χ₀ < max (C.chiMinimal1 uStar) (C.chiMinimal2 uStar) := by
  rcases h with h | h
  · exact lt_of_lt_of_le h.2 (le_max_left _ _)
  · exact lt_of_lt_of_le h.2.2 (le_max_right _ _)

lemma MinimalGlobalStabilityCondition.chi_lt_chiBeta
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    {uStar uBar vLower : ℝ}
    (hβ : 1 ≤ p.β)
    (hC1 :
      C.chiMinimal1 uStar =
        chiMinimal1Formula p 1 uStar uBar vLower)
    (hC2 :
      C.chiMinimal2 uStar =
        chiMinimal2Formula p uBar vLower)
    (h : MinimalGlobalStabilityCondition D p C uStar) :
    p.χ₀ < chiBeta p := by
  rcases h with h | h
  · exact chi_lt_chiBeta_of_lt_chiMinimal1Formula p hβ
      (by simpa [hC1] using h.2)
  · exact chi_lt_chiBeta_of_lt_chiMinimal2Formula p hβ
      (by simpa [hC2] using h.2.2)

/-- Minimal-model stability condition written directly with the explicit
threshold formulas, instead of the `Paper3Constants` threshold fields. -/
def MinimalGlobalStabilityFormulaCondition
    (p : CM2Params) (uStar uBar vLower : ℝ) : Prop :=
  (0 < p.χ₀ ∧
      p.χ₀ < chiMinimal1Formula p 1 uStar uBar vLower) ∨
    (p.γ = 1 ∧ 0 < p.χ₀ ∧
      p.χ₀ < chiMinimal2Formula p uBar vLower)

lemma MinimalGlobalStabilityFormulaCondition.chi_lt_chiBeta
    {p : CM2Params} {uStar uBar vLower : ℝ}
    (hβ : 1 ≤ p.β)
    (h : MinimalGlobalStabilityFormulaCondition p uStar uBar vLower) :
    p.χ₀ < chiBeta p := by
  rcases h with h | h
  · exact chi_lt_chiBeta_of_lt_chiMinimal1Formula p hβ h.2
  · exact chi_lt_chiBeta_of_lt_chiMinimal2Formula p hβ h.2.2

lemma MinimalGlobalStabilityFormulaCondition.linearlyStable_of_chiBeta_le_critical
    (S : SpectralData) (p : CM2Params) {uStar uBar vLower : ℝ}
    (H : HasNeumannSpectrum S) (hβ : 1 ≤ p.β) (huStar : 0 < uStar)
    (hcritical :
      chiBeta p ≤
        paperCriticalSensitivity S p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2)
    (h : MinimalGlobalStabilityFormulaCondition p uStar uBar vLower) :
    let eq := minimalEquilibrium p uStar
    LinearlyStable S p eq.1 eq.2 := by
  exact minimalEquilibrium_linearlyStable_of_chi_lt_paperCriticalSensitivity_neumann
    S p H huStar
    (lt_of_lt_of_le (h.chi_lt_chiBeta hβ) hcritical)

lemma MinimalGlobalStabilityFormulaCondition.linearlyStable_of_firstNonzero_lower
    (S : SpectralData) (p : CM2Params) {uStar uBar vLower : ℝ}
    (H : HasNeumannSpectrum S) (hβ : 1 ≤ p.β) (huStar : 0 < uStar)
    (hfirst :
      chiBeta p ≤
        ((1 + (minimalEquilibrium p uStar).2) ^ p.β /
            (p.ν * p.γ *
              (minimalEquilibrium p uStar).1 ^ (p.m + p.γ - 1))) *
          (p.μ + S.firstNonzero))
    (h : MinimalGlobalStabilityFormulaCondition p uStar uBar vLower) :
    let eq := minimalEquilibrium p uStar
    LinearlyStable S p eq.1 eq.2 := by
  exact h.linearlyStable_of_chiBeta_le_critical S p H hβ huStar
    (le_trans hfirst
      (paperCriticalSensitivity_minimalEquilibrium_ge_firstNonzero_lower
        S p H huStar))

def Theorem_2_1_part1 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  1 ≤ p.m →
    ∀ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v →
        ∃ δu > 0, EventuallyLowerBound D u δu ∧
          EventuallyLowerBound D v (p.ν / p.μ * δu ^ p.γ)

lemma Theorem_2_1_part1.persistence
    {D : BoundedDomainData} {p : CM2Params}
    (h : Theorem_2_1_part1 D p) (hm : 1 ≤ p.m)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v) :
    ∃ δu > 0, EventuallyLowerBound D u δu ∧
      EventuallyLowerBound D v (p.ν / p.μ * δu ^ p.γ) :=
  h hm u v huv

/-- A degenerate bounded-domain API showing that Paper3 Theorem 2.1(1)
cannot be proved from the current abstract `BoundedDomainData` interface alone.
The PDE side admits the positive constant solution `u = v = 1`, but the
abstract lower-envelope functional is identically zero. -/
def theorem21Part1NoLowerEnvelopeDomain : BoundedDomainData where
  Point := Unit
  inside := Set.univ
  boundary := ∅
  volume := 1
  supNorm := fun _ => 1
  infValue := fun _ => 0
  integral := fun _ => 1
  gradNorm := fun _ _ => 0
  timeDeriv := fun _ _ _ => 0
  laplacian := fun _ _ => 0
  chemotaxisDiv := fun _ _ _ _ => 0
  crossDiffusionEnergyTerm := fun _ _ _ _ => 0
  normalDeriv := fun _ _ => 0
  initialAdmissible := fun _ => True
  classicalRegularity := fun _ _ _ => True

def theorem21Part1CounterParams : CM2Params :=
  { N := 1
    hN := by norm_num
    α := 1
    γ := 1
    m := 1
    μ := 1
    ν := 1
    χ₀ := 0
    a := 1
    b := 1
    β := 1
    hα := by norm_num
    hγ := by norm_num
    hm := by norm_num
    hμ := by norm_num
    hν := by norm_num
    ha := by norm_num
    hb := by norm_num
    hβ := by norm_num }

lemma theorem21Part1Counter_classical (T : ℝ) (hT : 0 < T) :
    IsPaper2ClassicalSolution theorem21Part1NoLowerEnvelopeDomain
      theorem21Part1CounterParams T
      (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) := by
  refine ⟨hT, trivial, ?_, ?_, ?_, ?_⟩
  · intro t x ht0 htT hx
    norm_num
  · intro t x ht0 htT hx
    change (0 : ℝ) =
      0 - theorem21Part1CounterParams.χ₀ * 0 +
        1 * (theorem21Part1CounterParams.a -
          theorem21Part1CounterParams.b * (1 : ℝ) ^ theorem21Part1CounterParams.α)
    norm_num [theorem21Part1CounterParams]
  · intro t x ht0 htT hx
    change (0 : ℝ) =
      0 - theorem21Part1CounterParams.μ * 1 +
        theorem21Part1CounterParams.ν * (1 : ℝ) ^ theorem21Part1CounterParams.γ
    norm_num [theorem21Part1CounterParams]
  · intro t x ht0 htT hx
    cases hx

lemma theorem21Part1Counter_positiveGlobalBounded :
    PositiveGlobalBoundedSolution theorem21Part1NoLowerEnvelopeDomain
      theorem21Part1CounterParams
      (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro T hT
    exact theorem21Part1Counter_classical T hT
  · exact ⟨1, Eventually.of_forall fun _t => le_rfl⟩
  · intro t x ht hx
    norm_num

/-- Raw version of the `StabilityNorms.initialContinuity` field, with the
distance functional exposed rather than hidden inside a package. -/
def InitialContinuityRaw
    (D : BoundedDomainData) (p : CM2Params)
    (xpSigmaDistance : ℝ → ℝ → (D.Point → ℝ) → (D.Point → ℝ) → ℝ)
    (uConst : ℝ) : Prop :=
  ∀ sigma pNorm eps, 1 / 2 < sigma → 1 < pNorm → 0 < eps →
    ∃ delta > 0, ∃ T0 > 0, ∃ T > T0,
      ∀ u₀ : D.Point → ℝ,
      ∀ u v uConstSol vConstSol : ℝ → D.Point → ℝ,
        PositiveInitialDatum D u₀ →
        PositiveInitialDatum D (fun _ : D.Point => uConst) →
        D.supNorm (fun x => u₀ x - uConst) ≤ delta →
        IsPaper2ClassicalSolution D p T u v →
        InitialTrace D u₀ u →
        IsPaper2ClassicalSolution D p T uConstSol vConstSol →
        InitialTrace D (fun _ : D.Point => uConst) uConstSol →
          xpSigmaDistance sigma pNorm (u T0) (uConstSol T0) ≤ eps

/-- A fake one-point domain whose `supNorm` is identically zero.  It makes every
initial trace and every initial perturbation look arbitrarily small, so a
completely unrelated `X^σ_p` distance cannot be controlled from this API. -/
def initialContinuityNoDistanceControlDomain : BoundedDomainData where
  Point := Unit
  inside := Set.univ
  boundary := ∅
  volume := 1
  supNorm := fun _ => 0
  infValue := fun _ => 1
  integral := fun _ => 1
  gradNorm := fun _ _ => 0
  timeDeriv := fun _ _ _ => 0
  laplacian := fun _ _ => 0
  chemotaxisDiv := fun _ _ _ _ => 0
  crossDiffusionEnergyTerm := fun _ _ _ _ => 0
  normalDeriv := fun _ _ => 0
  initialAdmissible := fun _ => True
  classicalRegularity := fun _ _ _ => True

lemma initialContinuityNoDistanceControl_constant_one_classical
    (T : ℝ) (hT : 0 < T) :
    IsPaper2ClassicalSolution initialContinuityNoDistanceControlDomain
      theorem21Part1CounterParams T
      (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) := by
  refine ⟨hT, trivial, ?_, ?_, ?_, ?_⟩
  · intro t x ht0 htT hx
    norm_num
  · intro t x ht0 htT hx
    change (0 : ℝ) =
      0 - theorem21Part1CounterParams.χ₀ * 0 +
        1 * (theorem21Part1CounterParams.a -
          theorem21Part1CounterParams.b * (1 : ℝ) ^ theorem21Part1CounterParams.α)
    norm_num [theorem21Part1CounterParams]
  · intro t x ht0 htT hx
    change (0 : ℝ) =
      0 - theorem21Part1CounterParams.μ * 1 +
        theorem21Part1CounterParams.ν * (1 : ℝ) ^ theorem21Part1CounterParams.γ
    norm_num [theorem21Part1CounterParams]
  · intro t x ht0 htT hx
    cases hx

lemma initialContinuityNoDistanceControl_trace_one :
    InitialTrace initialContinuityNoDistanceControlDomain
      (fun _ : Unit => (1 : ℝ)) (fun _ _ => (1 : ℝ)) := by
  intro ε hε
  refine ⟨1, by norm_num, ?_⟩
  intro t ht0 ht
  simpa [initialContinuityNoDistanceControlDomain] using hε

/-- Field-level obstruction for `StabilityNorms.initialContinuity`: without a
real relation between the sup norm and `X^σ_p`, the raw statement is false.
Here `supNorm ≡ 0`, while the exposed `xpSigmaDistance` is constantly `1`. -/
lemma not_InitialContinuityRaw_constant_xpSigmaDistance :
    ¬ InitialContinuityRaw initialContinuityNoDistanceControlDomain
      theorem21Part1CounterParams
      (fun _ _ _ _ => (1 : ℝ)) 1 := by
  intro h
  rcases h 1 2 (1 / 2)
      (by norm_num) (by norm_num) (by norm_num) with
    ⟨delta, hdelta_pos, T0, hT0_pos, T, hT_gt, hmain⟩
  have hpos :
      PositiveInitialDatum initialContinuityNoDistanceControlDomain
        (fun _ : Unit => (1 : ℝ)) := by
    constructor
    · trivial
    · intro x hx
      norm_num
  have hclose :
      initialContinuityNoDistanceControlDomain.supNorm
        (fun x : Unit => (fun _ : Unit => (1 : ℝ)) x - 1) ≤ delta := by
    simpa [initialContinuityNoDistanceControlDomain] using hdelta_pos.le
  have hT_pos : 0 < T := lt_trans hT0_pos hT_gt
  have hclassical :
      IsPaper2ClassicalSolution initialContinuityNoDistanceControlDomain
        theorem21Part1CounterParams T
        (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) :=
    initialContinuityNoDistanceControl_constant_one_classical T hT_pos
  have hle :=
    hmain (fun _ : Unit => (1 : ℝ))
      (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ))
      (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ))
      hpos hpos hclose hclassical initialContinuityNoDistanceControl_trace_one
      hclassical initialContinuityNoDistanceControl_trace_one
  norm_num at hle

/-- Raw version of `StabilityNorms.negativeSensitivityGlobalStability`,
exposing only the `C¹` distance rather than a full norm package. -/
def NegativeSensitivityGlobalStabilityRaw
    (D : BoundedDomainData) (p : CM2Params)
    (c1Distance : (D.Point → ℝ) → (D.Point → ℝ) → ℝ) : Prop :=
  p.χ₀ ≤ 0 → 1 ≤ p.m →
    (∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      (∀ u v : ℝ → D.Point → ℝ,
        PositiveGlobalBoundedSolution D p u v →
          UniformConvergesInSup D u eq.1) ∧
      ∃ A > 0, ∃ rate > 0,
        ∀ u v : ℝ → D.Point → ℝ,
          PositiveGlobalBoundedSolution D p u v →
            ∀ t, 0 ≤ t →
              c1Distance (u t) (fun _ => eq.1) +
                c1Distance (v t) (fun _ => eq.2) ≤
                  A * Real.exp (-rate * t)) ∧
    (p.a = 0 → p.b = 0 →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        (∀ u v : ℝ → D.Point → ℝ,
          PositiveGlobalBoundedSolution D p u v →
          HasInitialMass D u uStar →
            UniformConvergesInSup D u eq.1) ∧
        ∃ A > 0, ∃ rate > 0,
          ∀ u v : ℝ → D.Point → ℝ,
            PositiveGlobalBoundedSolution D p u v →
            HasInitialMass D u uStar →
              ∀ t, 0 ≤ t →
                c1Distance (u t) (fun _ => eq.1) +
                  c1Distance (v t) (fun _ => eq.2) ≤
                    A * Real.exp (-rate * t))

/-- Raw obstruction for the negative-sensitivity global-stability package
field: an unrelated constant `C¹` distance cannot satisfy the asserted
exponential convergence estimate, even for the constant equilibrium solution. -/
lemma not_NegativeSensitivityGlobalStabilityRaw_constant_c1Distance :
    ¬ NegativeSensitivityGlobalStabilityRaw theorem21Part1NoLowerEnvelopeDomain
      theorem21Part1CounterParams (fun _ _ => (1 : ℝ)) := by
  intro h
  let D := theorem21Part1NoLowerEnvelopeDomain
  let p := theorem21Part1CounterParams
  have hχ : p.χ₀ ≤ 0 := by
    norm_num [p, theorem21Part1CounterParams]
  have hm : 1 ≤ p.m := by
    norm_num [p, theorem21Part1CounterParams]
  have ha : 0 < p.a := by
    norm_num [p, theorem21Part1CounterParams]
  have hb : 0 < p.b := by
    norm_num [p, theorem21Part1CounterParams]
  rcases (h hχ hm).1 ha hb with
    ⟨_hconv, A, hA_pos, rate, hrate_pos, hbound⟩
  have hmul : Tendsto (fun t : ℝ => rate * t) atTop atTop :=
    (Filter.tendsto_id.atTop_mul_const hrate_pos).congr
      (fun t => mul_comm t rate)
  have hneg : Tendsto (fun t : ℝ => -(rate * t)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hmul
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(rate * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have hlim :
      Tendsto (fun t : ℝ => A * Real.exp (-rate * t)) atTop (𝓝 0) := by
    convert tendsto_const_nhds.mul hexp using 1
    · ext t
      ring_nf
    · simp
  have hevent :
      ∀ᶠ t : ℝ in atTop, A * Real.exp (-rate * t) < (2 : ℝ) :=
    hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 2))
  rcases eventually_atTop.1 hevent with ⟨T, hT⟩
  let t : ℝ := max T 0
  have ht0 : 0 ≤ t := le_max_right T 0
  have hTle : T ≤ t := le_max_left T 0
  have hsmall_rhs : A * Real.exp (-rate * t) < (2 : ℝ) := hT t hTle
  have hlarge_rhs : (2 : ℝ) ≤ A * Real.exp (-rate * t) := by
    have htmp :=
      hbound (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ))
        theorem21Part1Counter_positiveGlobalBounded t ht0
    norm_num at htmp
    simpa [t] using htmp
  linarith

/-- Raw version of `StabilityNorms.sectorialLocalExponential`, with the two
distance functionals exposed. -/
def SectorialLocalExponentialRaw
    (D : BoundedDomainData) (p : CM2Params) (S : SpectralData)
    (c1Distance : (D.Point → ℝ) → (D.Point → ℝ) → ℝ)
    (xpSigmaDistance : ℝ → ℝ → (D.Point → ℝ) → (D.Point → ℝ) → ℝ) : Prop :=
  ∀ sigma pNorm uStar vStar,
    1 / 2 < sigma → sigma < 1 → 1 < pNorm →
    LinearlyStable S p uStar vStar →
      ∃ eps > 0, ∃ C > 0, ∃ rate > 0,
        ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
          xpSigmaDistance sigma pNorm u₀ (fun _ => uStar) ≤ eps →
            ∀ u v : ℝ → D.Point → ℝ,
              IsPaper2GlobalClassicalSolution D p u v →
              InitialTrace D u₀ u →
                ∀ t, 0 ≤ t →
                  c1Distance (u t) (fun _ => uStar) +
                    c1Distance (v t) (fun _ => vStar) ≤
                      C * Real.exp (-rate * t)

lemma SectorialLocalExponentialRaw.local_exponential_stability
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {c1Distance : (D.Point → ℝ) → (D.Point → ℝ) → ℝ}
    {xpSigmaDistance : ℝ → ℝ → (D.Point → ℝ) → (D.Point → ℝ) → ℝ}
    (h : SectorialLocalExponentialRaw D p S c1Distance xpSigmaDistance)
    {sigma pNorm uStar vStar : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (hstable : LinearlyStable S p uStar vStar) :
    ∃ eps > 0, ∃ C > 0, ∃ rate > 0,
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        xpSigmaDistance sigma pNorm u₀ (fun _ => uStar) ≤ eps →
          ∀ u v : ℝ → D.Point → ℝ,
            IsPaper2GlobalClassicalSolution D p u v →
            InitialTrace D u₀ u →
              ∀ t, 0 ≤ t →
                c1Distance (u t) (fun _ => uStar) +
                  c1Distance (v t) (fun _ => vStar) ≤
                    C * Real.exp (-rate * t) :=
  h sigma pNorm uStar vStar hsigma_low hsigma_high hpNorm hstable

def sectorialLocalExponentialCounterSpectralData : SpectralData where
  eigenvalue := fun n => if n = 0 then 0 else 1
  firstNonzero := 1

lemma sectorialLocalExponentialCounter_linearlyStable :
    LinearlyStable sectorialLocalExponentialCounterSpectralData
      theorem21Part1CounterParams 1 1 := by
  intro n hn
  simp [sectorialLocalExponentialCounterSpectralData,
    sigma, theorem21Part1CounterParams, hn]

lemma initialContinuityNoDistanceControl_constant_one_global :
    IsPaper2GlobalClassicalSolution initialContinuityNoDistanceControlDomain
      theorem21Part1CounterParams
      (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) := by
  intro T hT
  exact initialContinuityNoDistanceControl_constant_one_classical T hT

lemma initialContinuityNoDistanceControl_constant_one_positiveGlobalBounded :
    PositiveGlobalBoundedSolution initialContinuityNoDistanceControlDomain
      theorem21Part1CounterParams
      (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) := by
  refine ⟨initialContinuityNoDistanceControl_constant_one_global, ?_, ?_⟩
  · exact ⟨0, Eventually.of_forall fun _t => le_rfl⟩
  · intro t x ht hx
    norm_num

/-- Raw obstruction for `StabilityNorms.sectorialLocalExponential`: if the
`C¹` distance is unrelated to the dynamics and is constantly `1`, the claimed
exponential decay forces `2 ≤ C exp(-rate t)` for all `t`, impossible as the
right-hand side tends to `0`. -/
lemma not_SectorialLocalExponentialRaw_constant_c1Distance :
    ¬ SectorialLocalExponentialRaw initialContinuityNoDistanceControlDomain
      theorem21Part1CounterParams sectorialLocalExponentialCounterSpectralData
      (fun _ _ => (1 : ℝ)) (fun _ _ _ _ => (0 : ℝ)) := by
  intro h
  rcases h (3 / 4) 2 1 1
      (by norm_num) (by norm_num) (by norm_num)
      sectorialLocalExponentialCounter_linearlyStable with
    ⟨eps, heps_pos, C, hC_pos, rate, hrate_pos, hmain⟩
  have hpos :
      PositiveInitialDatum initialContinuityNoDistanceControlDomain
        (fun _ : Unit => (1 : ℝ)) := by
    constructor
    · trivial
    · intro x hx
      norm_num
  have hsmall :
      (fun _ _ _ _ => (0 : ℝ)) (3 / 4) 2
        (fun _ : Unit => (1 : ℝ)) (fun _ : Unit => (1 : ℝ)) ≤ eps := by
    simpa using heps_pos.le
  have hbound :=
    hmain (fun _ : Unit => (1 : ℝ)) hpos hsmall
      (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ))
      initialContinuityNoDistanceControl_constant_one_global
      initialContinuityNoDistanceControl_trace_one
  have hmul : Tendsto (fun t : ℝ => rate * t) atTop atTop :=
    (Filter.tendsto_id.atTop_mul_const hrate_pos).congr
      (fun t => mul_comm t rate)
  have hneg : Tendsto (fun t : ℝ => -(rate * t)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hmul
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(rate * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have hlim :
      Tendsto (fun t : ℝ => C * Real.exp (-rate * t)) atTop (𝓝 0) := by
    convert tendsto_const_nhds.mul hexp using 1
    · ext t
      ring_nf
    · simp
  have hevent :
      ∀ᶠ t : ℝ in atTop, C * Real.exp (-rate * t) < (2 : ℝ) :=
    hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 2))
  rcases eventually_atTop.1 hevent with ⟨T, hT⟩
  let t : ℝ := max T 0
  have ht0 : 0 ≤ t := by
    exact le_max_right T 0
  have hTle : T ≤ t := by
    exact le_max_left T 0
  have hsmall_rhs : C * Real.exp (-rate * t) < (2 : ℝ) := hT t hTle
  have hlarge_rhs : (2 : ℝ) ≤ C * Real.exp (-rate * t) := by
    have htmp := hbound t ht0
    norm_num at htmp
    simpa [t] using htmp
  linarith

/-- Nonminimal exponential-upgrade branch of
`Paper3Constants.convergenceToExponential`, with the `C¹` distance and critical
threshold exposed. -/
def ConvergenceToExponentialNonminimalRaw
    (D : BoundedDomainData) (p : CM2Params)
    (c1Distance : (D.Point → ℝ) → (D.Point → ℝ) → ℝ)
    (chiCritical : ℝ → ℝ) : Prop :=
  1 ≤ p.m →
    ∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      p.χ₀ < chiCritical eq.1 →
        ∀ u v : ℝ → D.Point → ℝ,
          PositiveGlobalBoundedSolution D p u v →
          UniformConvergesInSup D u eq.1 →
            ∃ C > 0, ∃ rate > 0, ∀ t, 0 ≤ t →
              c1Distance (u t) (fun _ => eq.1) +
                c1Distance (v t) (fun _ => eq.2) ≤
                  C * Real.exp (-rate * t)

/-- Raw minimal exponential-upgrade branch of
`Paper3Constants.convergenceToExponential`, with the `C¹` distance and
critical threshold exposed. -/
def ConvergenceToExponentialMinimalRaw
    (D : BoundedDomainData) (p : CM2Params)
    (c1Distance : (D.Point → ℝ) → (D.Point → ℝ) → ℝ)
    (chiCritical : ℝ → ℝ) : Prop :=
  1 ≤ p.m → p.a = 0 → p.b = 0 →
    ∀ uStar > 0,
      let eq := minimalEquilibrium p uStar
      p.χ₀ < chiCritical uStar →
        ∀ u v : ℝ → D.Point → ℝ,
          PositiveGlobalBoundedSolution D p u v →
          HasInitialMass D u uStar →
          UniformConvergesInSup D u eq.1 →
            ∃ C > 0, ∃ rate > 0, ∀ t, 0 ≤ t →
              c1Distance (u t) (fun _ => eq.1) +
                c1Distance (v t) (fun _ => eq.2) ≤
                  C * Real.exp (-rate * t)

/-- Raw first branch of `Paper3Constants.convergenceToExponential`: theta
moment convergence is exposed as an assumption and the sup convergence
conclusion is not hidden inside the constants package. -/
def MomentConvergenceToUniformRaw
    (D : BoundedDomainData) (p : CM2Params) : Prop :=
  1 ≤ p.m →
    ∀ (uStar _vStar theta : ℝ), 0 < theta →
      ∀ u v : ℝ → D.Point → ℝ,
        PositiveGlobalBoundedSolution D p u v →
        ThetaMomentConvergesToZero D u uStar theta →
          UniformConvergesInSup D u uStar

/-- A fake domain where the moment functional is identically zero, but the
sup-norm functional is identically one.  It separates the first convergence
branch from any genuine compactness or norm-control argument. -/
def momentConvergenceNoUniformDomain : BoundedDomainData where
  Point := Unit
  inside := Set.univ
  boundary := ∅
  volume := 1
  supNorm := fun _ => 1
  infValue := fun _ => 1
  integral := fun _ => 0
  gradNorm := fun _ _ => 0
  timeDeriv := fun _ _ _ => 0
  laplacian := fun _ _ => 0
  chemotaxisDiv := fun _ _ _ _ => 0
  crossDiffusionEnergyTerm := fun _ _ _ _ => 0
  normalDeriv := fun _ _ => 0
  initialAdmissible := fun _ => True
  classicalRegularity := fun _ _ _ => True

lemma momentConvergenceNoUniform_constant_one_classical
    (T : ℝ) (hT : 0 < T) :
    IsPaper2ClassicalSolution momentConvergenceNoUniformDomain
      theorem21Part1CounterParams T
      (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) := by
  refine ⟨hT, trivial, ?_, ?_, ?_, ?_⟩
  · intro t x ht0 htT hx
    norm_num
  · intro t x ht0 htT hx
    change (0 : ℝ) =
      0 - theorem21Part1CounterParams.χ₀ * 0 +
        1 * (theorem21Part1CounterParams.a -
          theorem21Part1CounterParams.b * (1 : ℝ) ^ theorem21Part1CounterParams.α)
    norm_num [theorem21Part1CounterParams]
  · intro t x ht0 htT hx
    change (0 : ℝ) =
      0 - theorem21Part1CounterParams.μ * 1 +
        theorem21Part1CounterParams.ν * (1 : ℝ) ^ theorem21Part1CounterParams.γ
    norm_num [theorem21Part1CounterParams]
  · intro t x ht0 htT hx
    cases hx

lemma momentConvergenceNoUniform_constant_one_positiveGlobalBounded :
    PositiveGlobalBoundedSolution momentConvergenceNoUniformDomain
      theorem21Part1CounterParams
      (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro T hT
    exact momentConvergenceNoUniform_constant_one_classical T hT
  · exact ⟨1, Eventually.of_forall fun _t => le_rfl⟩
  · intro t x ht hx
    norm_num

lemma momentConvergenceNoUniform_constant_one_thetaMoment :
    ThetaMomentConvergesToZero momentConvergenceNoUniformDomain
      (fun _ _ => (1 : ℝ)) 1 1 := by
  simp [ThetaMomentConvergesToZero, momentConvergenceNoUniformDomain]

/-- Raw obstruction for the moment-to-uniform convergence branch: the current
abstract domain API permits a zero moment functional unrelated to the exposed
sup norm. -/
lemma not_MomentConvergenceToUniformRaw_no_norm_control :
    ¬ MomentConvergenceToUniformRaw momentConvergenceNoUniformDomain
      theorem21Part1CounterParams := by
  intro h
  let D := momentConvergenceNoUniformDomain
  let p := theorem21Part1CounterParams
  have hm : 1 ≤ p.m := by
    norm_num [p, theorem21Part1CounterParams]
  have hconv :
      UniformConvergesInSup D (fun _ _ => (1 : ℝ)) 1 :=
    h hm 1 1 1 (by norm_num) (fun _ _ => (1 : ℝ))
      (fun _ _ => (1 : ℝ))
      momentConvergenceNoUniform_constant_one_positiveGlobalBounded
      momentConvergenceNoUniform_constant_one_thetaMoment
  have hlim_zero : Tendsto (fun _t : ℝ => (1 : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simp [UniformConvergesInSup, D, momentConvergenceNoUniformDomain] at hconv
  have hlim_one : Tendsto (fun _t : ℝ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) :=
    tendsto_const_nhds
  have hone_eq_zero : (1 : ℝ) = 0 :=
    tendsto_nhds_unique hlim_one hlim_zero
  norm_num at hone_eq_zero

/-- Raw obstruction for the convergence-to-exponential upgrade: uniform
convergence in a fake `supNorm` does not imply exponential convergence in an
unrelated `C¹` distance. -/
lemma not_ConvergenceToExponentialNonminimalRaw_constant_c1Distance :
    ¬ ConvergenceToExponentialNonminimalRaw initialContinuityNoDistanceControlDomain
      theorem21Part1CounterParams (fun _ _ => (1 : ℝ)) (fun _ => (1 : ℝ)) := by
  intro h
  let D := initialContinuityNoDistanceControlDomain
  let p := theorem21Part1CounterParams
  have hm : 1 ≤ p.m := by
    norm_num [p, theorem21Part1CounterParams]
  have ha : 0 < p.a := by
    norm_num [p, theorem21Part1CounterParams]
  have hb : 0 < p.b := by
    norm_num [p, theorem21Part1CounterParams]
  have hχ : p.χ₀ < (fun _ => (1 : ℝ)) (positiveEquilibrium p ⟨ha, hb⟩).1 := by
    norm_num [p, theorem21Part1CounterParams]
  have hconv :
      UniformConvergesInSup D (fun _ _ => (1 : ℝ))
        (positiveEquilibrium p ⟨ha, hb⟩).1 := by
    simp [UniformConvergesInSup, D, initialContinuityNoDistanceControlDomain]
  rcases h hm ha hb hχ (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ))
      initialContinuityNoDistanceControl_constant_one_positiveGlobalBounded
      hconv with
    ⟨C, hC_pos, rate, hrate_pos, hbound⟩
  have hmul : Tendsto (fun t : ℝ => rate * t) atTop atTop :=
    (Filter.tendsto_id.atTop_mul_const hrate_pos).congr
      (fun t => mul_comm t rate)
  have hneg : Tendsto (fun t : ℝ => -(rate * t)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hmul
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(rate * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have hlim :
      Tendsto (fun t : ℝ => C * Real.exp (-rate * t)) atTop (𝓝 0) := by
    convert tendsto_const_nhds.mul hexp using 1
    · ext t
      ring_nf
    · simp
  have hevent :
      ∀ᶠ t : ℝ in atTop, C * Real.exp (-rate * t) < (2 : ℝ) :=
    hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 2))
  rcases eventually_atTop.1 hevent with ⟨T, hT⟩
  let t : ℝ := max T 0
  have ht0 : 0 ≤ t := by
    exact le_max_right T 0
  have hTle : T ≤ t := by
    exact le_max_left T 0
  have hsmall_rhs : C * Real.exp (-rate * t) < (2 : ℝ) := hT t hTle
  have hlarge_rhs : (2 : ℝ) ≤ C * Real.exp (-rate * t) := by
    have htmp := hbound t ht0
    norm_num at htmp
    simpa [t] using htmp
  linarith

def nonminimalGlobalStabilityCounterParams : CM2Params :=
  { N := 1
    hN := by norm_num
    α := 1
    γ := 1
    m := 1
    μ := 1
    ν := 1
    χ₀ := 0
    a := 1
    b := 1
    β := 0
    hα := by norm_num
    hγ := by norm_num
    hm := by norm_num
    hμ := by norm_num
    hν := by norm_num
    ha := by norm_num
    hb := by norm_num
    hβ := by norm_num }

lemma initialContinuityNoDistanceControl_nonminimalCounter_classical
    (T : ℝ) (hT : 0 < T) :
    IsPaper2ClassicalSolution initialContinuityNoDistanceControlDomain
      nonminimalGlobalStabilityCounterParams T
      (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) := by
  refine ⟨hT, trivial, ?_, ?_, ?_, ?_⟩
  · intro t x ht0 htT hx
    norm_num
  · intro t x ht0 htT hx
    change (0 : ℝ) =
      0 - nonminimalGlobalStabilityCounterParams.χ₀ * 0 +
        1 * (nonminimalGlobalStabilityCounterParams.a -
          nonminimalGlobalStabilityCounterParams.b *
            (1 : ℝ) ^ nonminimalGlobalStabilityCounterParams.α)
    norm_num [nonminimalGlobalStabilityCounterParams]
  · intro t x ht0 htT hx
    change (0 : ℝ) =
      0 - nonminimalGlobalStabilityCounterParams.μ * 1 +
        nonminimalGlobalStabilityCounterParams.ν *
          (1 : ℝ) ^ nonminimalGlobalStabilityCounterParams.γ
    norm_num [nonminimalGlobalStabilityCounterParams]
  · intro t x ht0 htT hx
    cases hx

lemma initialContinuityNoDistanceControl_nonminimalCounter_global :
    IsPaper2GlobalClassicalSolution initialContinuityNoDistanceControlDomain
      nonminimalGlobalStabilityCounterParams
      (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) := by
  intro T hT
  exact initialContinuityNoDistanceControl_nonminimalCounter_classical T hT

lemma initialContinuityNoDistanceControl_nonminimalCounter_positiveGlobalBounded :
    PositiveGlobalBoundedSolution initialContinuityNoDistanceControlDomain
      nonminimalGlobalStabilityCounterParams
      (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) := by
  refine ⟨initialContinuityNoDistanceControl_nonminimalCounter_global, ?_, ?_⟩
  · exact ⟨0, Eventually.of_forall fun _t => le_rfl⟩
  · intro t x ht hx
    norm_num

/-- Raw nonminimal global-stability branch, exposing only the metric and the
threshold needed for the third strong-logistic alternative. -/
def NonminimalGlobalStabilityRaw
    (D : BoundedDomainData) (p : CM2Params)
    (c1Distance : (D.Point → ℝ) → (D.Point → ℝ) → ℝ)
    (chiStrong3 : ℝ → ℝ) : Prop :=
  0 < p.a → 0 < p.b → 0 ≤ p.β → 0 < p.α → 0 < p.γ →
    ∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      (1 ≤ p.m ∧ 1 ≤ p.γ ∧
        p.α + 1 ≥ p.m + p.γ + (if p.β = 0 then 0 else p.γ) ∧
        p.χ₀ < chiStrong3 eq.1) →
        (∀ u v : ℝ → D.Point → ℝ,
          PositiveGlobalBoundedSolution D p u v →
            UniformConvergesInSup D u eq.1) ∧
        ∃ A > 0, ∃ rate > 0,
          ∀ u v : ℝ → D.Point → ℝ,
            PositiveGlobalBoundedSolution D p u v →
              ∀ t, 0 ≤ t →
                c1Distance (u t) (fun _ => eq.1) +
                  c1Distance (v t) (fun _ => eq.2) ≤
                    A * Real.exp (-rate * t)

/-- Raw obstruction for the nonminimal global-stability package field.  The
third strong-logistic branch can be satisfied algebraically, but an unrelated
constant `C¹` distance cannot decay exponentially. -/
lemma not_NonminimalGlobalStabilityRaw_constant_c1Distance :
    ¬ NonminimalGlobalStabilityRaw initialContinuityNoDistanceControlDomain
      nonminimalGlobalStabilityCounterParams
      (fun _ _ => (1 : ℝ)) (fun _ => (1 : ℝ)) := by
  intro h
  let D := initialContinuityNoDistanceControlDomain
  let p := nonminimalGlobalStabilityCounterParams
  have ha : 0 < p.a := by
    norm_num [p, nonminimalGlobalStabilityCounterParams]
  have hb : 0 < p.b := by
    norm_num [p, nonminimalGlobalStabilityCounterParams]
  have hcond :
      1 ≤ p.m ∧ 1 ≤ p.γ ∧
        p.α + 1 ≥ p.m + p.γ + (if p.β = 0 then 0 else p.γ) ∧
        p.χ₀ < (fun _ => (1 : ℝ)) (positiveEquilibrium p ⟨ha, hb⟩).1 := by
    norm_num [p, nonminimalGlobalStabilityCounterParams]
  rcases (h
      (by norm_num [p, nonminimalGlobalStabilityCounterParams])
      (by norm_num [p, nonminimalGlobalStabilityCounterParams])
      (by norm_num [p, nonminimalGlobalStabilityCounterParams])
      (by norm_num [p, nonminimalGlobalStabilityCounterParams])
      (by norm_num [p, nonminimalGlobalStabilityCounterParams])
      ha hb hcond).2 with
    ⟨A, hA_pos, rate, hrate_pos, hbound⟩
  have hmul : Tendsto (fun t : ℝ => rate * t) atTop atTop :=
    (Filter.tendsto_id.atTop_mul_const hrate_pos).congr
      (fun t => mul_comm t rate)
  have hneg : Tendsto (fun t : ℝ => -(rate * t)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hmul
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(rate * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have hlim :
      Tendsto (fun t : ℝ => A * Real.exp (-rate * t)) atTop (𝓝 0) := by
    convert tendsto_const_nhds.mul hexp using 1
    · ext t
      ring_nf
    · simp
  have hevent :
      ∀ᶠ t : ℝ in atTop, A * Real.exp (-rate * t) < (2 : ℝ) :=
    hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 2))
  rcases eventually_atTop.1 hevent with ⟨T, hT⟩
  let t : ℝ := max T 0
  have ht0 : 0 ≤ t := by
    exact le_max_right T 0
  have hTle : T ≤ t := by
    exact le_max_left T 0
  have hsmall_rhs : A * Real.exp (-rate * t) < (2 : ℝ) := hT t hTle
  have hlarge_rhs : (2 : ℝ) ≤ A * Real.exp (-rate * t) := by
    have htmp :=
      hbound (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ))
        initialContinuityNoDistanceControl_nonminimalCounter_positiveGlobalBounded
        t ht0
    norm_num at htmp
    simpa [t] using htmp
  linarith

def minimalGlobalStabilityCounterParams : CM2Params :=
  { N := 1
    hN := by norm_num
    α := 1
    γ := 1
    m := 1
    μ := 1
    ν := 1
    χ₀ := 1 / 2
    a := 0
    b := 0
    β := 1
    hα := by norm_num
    hγ := by norm_num
    hm := by norm_num
    hμ := by norm_num
    hν := by norm_num
    ha := by norm_num
    hb := by norm_num
    hβ := by norm_num }

lemma initialContinuityNoDistanceControl_minimalCounter_classical
    (T : ℝ) (hT : 0 < T) :
    IsPaper2ClassicalSolution initialContinuityNoDistanceControlDomain
      minimalGlobalStabilityCounterParams T
      (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) := by
  refine ⟨hT, trivial, ?_, ?_, ?_, ?_⟩
  · intro t x ht0 htT hx
    norm_num
  · intro t x ht0 htT hx
    change (0 : ℝ) =
      0 - minimalGlobalStabilityCounterParams.χ₀ * 0 +
        1 * (minimalGlobalStabilityCounterParams.a -
          minimalGlobalStabilityCounterParams.b *
            (1 : ℝ) ^ minimalGlobalStabilityCounterParams.α)
    norm_num [minimalGlobalStabilityCounterParams]
  · intro t x ht0 htT hx
    change (0 : ℝ) =
      0 - minimalGlobalStabilityCounterParams.μ * 1 +
        minimalGlobalStabilityCounterParams.ν *
          (1 : ℝ) ^ minimalGlobalStabilityCounterParams.γ
    norm_num [minimalGlobalStabilityCounterParams]
  · intro t x ht0 htT hx
    cases hx

lemma initialContinuityNoDistanceControl_minimalCounter_global :
    IsPaper2GlobalClassicalSolution initialContinuityNoDistanceControlDomain
      minimalGlobalStabilityCounterParams
      (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) := by
  intro T hT
  exact initialContinuityNoDistanceControl_minimalCounter_classical T hT

lemma initialContinuityNoDistanceControl_minimalCounter_positiveGlobalBounded :
    PositiveGlobalBoundedSolution initialContinuityNoDistanceControlDomain
      minimalGlobalStabilityCounterParams
      (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) := by
  refine ⟨initialContinuityNoDistanceControl_minimalCounter_global, ?_, ?_⟩
  · exact ⟨0, Eventually.of_forall fun _t => le_rfl⟩
  · intro t x ht hx
    norm_num

lemma initialContinuityNoDistanceControl_minimalCounter_mass_one :
    HasInitialMass initialContinuityNoDistanceControlDomain
      (fun _ _ => (1 : ℝ)) 1 := by
  unfold HasInitialMass
  dsimp [initialContinuityNoDistanceControlDomain]
  norm_num

/-- Raw minimal-model global-stability branch, exposing the metric and the two
minimal thresholds instead of hiding them inside `Paper3Constants`. -/
def MinimalGlobalStabilityRaw
    (D : BoundedDomainData) (p : CM2Params)
    (c1Distance : (D.Point → ℝ) → (D.Point → ℝ) → ℝ)
    (chiMinimal1 chiMinimal2 : ℝ → ℝ) : Prop :=
  p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
    ∀ uStar > 0,
    let eq := minimalEquilibrium p uStar
    ((0 < p.χ₀ ∧ p.χ₀ < chiMinimal1 uStar) ∨
      (p.γ = 1 ∧ 0 < p.χ₀ ∧ p.χ₀ < chiMinimal2 uStar)) →
      (∀ u v : ℝ → D.Point → ℝ,
        PositiveGlobalBoundedSolution D p u v →
        HasInitialMass D u uStar →
          UniformConvergesInSup D u eq.1) ∧
      ∃ A > 0, ∃ rate > 0,
        ∀ u v : ℝ → D.Point → ℝ,
          PositiveGlobalBoundedSolution D p u v →
          HasInitialMass D u uStar →
            ∀ t, 0 ≤ t →
              c1Distance (u t) (fun _ => eq.1) +
                c1Distance (v t) (fun _ => eq.2) ≤
                  A * Real.exp (-rate * t)

/-- Raw obstruction for the minimal global-stability package field.  Even with
the mass constraint and the first minimal-threshold branch satisfied by
concrete parameters, an unrelated constant `C¹` distance cannot decay
exponentially. -/
lemma not_MinimalGlobalStabilityRaw_constant_c1Distance :
    ¬ MinimalGlobalStabilityRaw initialContinuityNoDistanceControlDomain
      minimalGlobalStabilityCounterParams
      (fun _ _ => (1 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) := by
  intro h
  let D := initialContinuityNoDistanceControlDomain
  let p := minimalGlobalStabilityCounterParams
  have huStar : (0 : ℝ) < 1 := by norm_num
  have hcond :
      (0 < p.χ₀ ∧ p.χ₀ < (fun _ => (1 : ℝ)) 1) ∨
        (p.γ = 1 ∧ 0 < p.χ₀ ∧ p.χ₀ < (fun _ => (1 : ℝ)) 1) := by
    left
    norm_num [p, minimalGlobalStabilityCounterParams]
  rcases (h
      (by norm_num [p, minimalGlobalStabilityCounterParams])
      (by norm_num [p, minimalGlobalStabilityCounterParams])
      (by norm_num [p, minimalGlobalStabilityCounterParams])
      (by norm_num [p, minimalGlobalStabilityCounterParams])
      1 huStar hcond).2 with
    ⟨A, hA_pos, rate, hrate_pos, hbound⟩
  have hmul : Tendsto (fun t : ℝ => rate * t) atTop atTop :=
    (Filter.tendsto_id.atTop_mul_const hrate_pos).congr
      (fun t => mul_comm t rate)
  have hneg : Tendsto (fun t : ℝ => -(rate * t)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hmul
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(rate * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have hlim :
      Tendsto (fun t : ℝ => A * Real.exp (-rate * t)) atTop (𝓝 0) := by
    convert tendsto_const_nhds.mul hexp using 1
    · ext t
      ring_nf
    · simp
  have hevent :
      ∀ᶠ t : ℝ in atTop, A * Real.exp (-rate * t) < (2 : ℝ) :=
    hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 2))
  rcases eventually_atTop.1 hevent with ⟨T, hT⟩
  let t : ℝ := max T 0
  have ht0 : 0 ≤ t := by
    exact le_max_right T 0
  have hTle : T ≤ t := by
    exact le_max_left T 0
  have hsmall_rhs : A * Real.exp (-rate * t) < (2 : ℝ) := hT t hTle
  have hlarge_rhs : (2 : ℝ) ≤ A * Real.exp (-rate * t) := by
    have htmp :=
      hbound (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ))
        initialContinuityNoDistanceControl_minimalCounter_positiveGlobalBounded
        initialContinuityNoDistanceControl_minimalCounter_mass_one t ht0
    norm_num at htmp
    simpa [t] using htmp
  linarith

/-- Raw obstruction for the minimal convergence-to-exponential upgrade:
uniform convergence in the fake `supNorm`, even with the mass constraint, does
not imply exponential convergence in an unrelated constant `C¹` distance. -/
lemma not_ConvergenceToExponentialMinimalRaw_constant_c1Distance :
    ¬ ConvergenceToExponentialMinimalRaw initialContinuityNoDistanceControlDomain
      minimalGlobalStabilityCounterParams (fun _ _ => (1 : ℝ))
      (fun _ => (1 : ℝ)) := by
  intro h
  let D := initialContinuityNoDistanceControlDomain
  let p := minimalGlobalStabilityCounterParams
  have hm : 1 ≤ p.m := by
    norm_num [p, minimalGlobalStabilityCounterParams]
  have ha : p.a = 0 := by
    norm_num [p, minimalGlobalStabilityCounterParams]
  have hb : p.b = 0 := by
    norm_num [p, minimalGlobalStabilityCounterParams]
  have huStar : (0 : ℝ) < 1 := by norm_num
  have hχ : p.χ₀ < (fun _ => (1 : ℝ)) 1 := by
    norm_num [p, minimalGlobalStabilityCounterParams]
  have hconv :
      UniformConvergesInSup D (fun _ _ => (1 : ℝ))
        (minimalEquilibrium p 1).1 := by
    simp [UniformConvergesInSup, D, p, initialContinuityNoDistanceControlDomain,
      minimalGlobalStabilityCounterParams, minimalEquilibrium]
  rcases h hm ha hb 1 huStar hχ (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ))
      initialContinuityNoDistanceControl_minimalCounter_positiveGlobalBounded
      initialContinuityNoDistanceControl_minimalCounter_mass_one hconv with
    ⟨A, hA_pos, rate, hrate_pos, hbound⟩
  have hmul : Tendsto (fun t : ℝ => rate * t) atTop atTop :=
    (Filter.tendsto_id.atTop_mul_const hrate_pos).congr
      (fun t => mul_comm t rate)
  have hneg : Tendsto (fun t : ℝ => -(rate * t)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hmul
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(rate * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have hlim :
      Tendsto (fun t : ℝ => A * Real.exp (-rate * t)) atTop (𝓝 0) := by
    convert tendsto_const_nhds.mul hexp using 1
    · ext t
      ring_nf
    · simp
  have hevent :
      ∀ᶠ t : ℝ in atTop, A * Real.exp (-rate * t) < (2 : ℝ) :=
    hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 2))
  rcases eventually_atTop.1 hevent with ⟨T, hT⟩
  let t : ℝ := max T 0
  have ht0 : 0 ≤ t := by
    exact le_max_right T 0
  have hTle : T ≤ t := by
    exact le_max_left T 0
  have hsmall_rhs : A * Real.exp (-rate * t) < (2 : ℝ) := hT t hTle
  have hlarge_rhs : (2 : ℝ) ≤ A * Real.exp (-rate * t) := by
    have htmp := hbound t ht0
    norm_num at htmp
    simpa [t] using htmp
  linarith

/-- Raw nonminimal local-stability branch of
`Paper3Constants.linearStabilityInstability`, exposing the `C¹` distance. -/
def LinearStabilityInstabilityNonminimalRaw
    (D : BoundedDomainData) (p : CM2Params) (S : SpectralData)
    (c1Distance : (D.Point → ℝ) → (D.Point → ℝ) → ℝ)
    (chiCritical : ℝ → ℝ) : Prop :=
  ∀ (ha : 0 < p.a) (hb : 0 < p.b),
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    p.χ₀ < chiCritical eq.1 →
      LinearlyStable S p eq.1 eq.2 ∧
      ∃ δ > 0, ∃ A > 0, ∃ rate > 0,
        ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
          SupCloseToConstant D u₀ eq.1 δ →
            ∃ u v : ℝ → D.Point → ℝ,
              IsPaper2GlobalClassicalSolution D p u v ∧
              InitialTrace D u₀ u ∧
              ∀ t, 0 ≤ t →
                c1Distance (u t) (fun _ => eq.1) +
                  c1Distance (v t) (fun _ => eq.2) ≤
                    A * Real.exp (-rate * t)

/-- Raw obstruction for the local-stability part of
`Paper3Constants.linearStabilityInstability`: fake sup-norm closeness can make
the initial datum admissibly small, but an unrelated constant `C¹` distance
prevents every asserted exponential convergence estimate. -/
lemma not_LinearStabilityInstabilityNonminimalRaw_constant_c1Distance :
    ¬ LinearStabilityInstabilityNonminimalRaw
      initialContinuityNoDistanceControlDomain theorem21Part1CounterParams
      sectorialLocalExponentialCounterSpectralData
      (fun _ _ => (1 : ℝ)) (fun _ => (1 : ℝ)) := by
  intro h
  let D := initialContinuityNoDistanceControlDomain
  let p := theorem21Part1CounterParams
  have ha : 0 < p.a := by
    norm_num [p, theorem21Part1CounterParams]
  have hb : 0 < p.b := by
    norm_num [p, theorem21Part1CounterParams]
  have hχ :
      p.χ₀ < (fun _ => (1 : ℝ)) (positiveEquilibrium p ⟨ha, hb⟩).1 := by
    norm_num [p, theorem21Part1CounterParams]
  rcases (h ha hb hχ).2 with
    ⟨δ, hδ_pos, A, hA_pos, rate, hrate_pos, hloc⟩
  have hpos :
      PositiveInitialDatum D (fun _ : Unit => (1 : ℝ)) := by
    constructor
    · trivial
    · intro x hx
      norm_num
  have hclose :
      SupCloseToConstant D (fun _ : Unit => (1 : ℝ))
        (positiveEquilibrium p ⟨ha, hb⟩).1 δ := by
    simp [SupCloseToConstant, D, initialContinuityNoDistanceControlDomain,
      hδ_pos]
  rcases hloc (fun _ : Unit => (1 : ℝ)) hpos hclose with
    ⟨u, v, _hglobal, _htrace, hbound⟩
  have hmul : Tendsto (fun t : ℝ => rate * t) atTop atTop :=
    (Filter.tendsto_id.atTop_mul_const hrate_pos).congr
      (fun t => mul_comm t rate)
  have hneg : Tendsto (fun t : ℝ => -(rate * t)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hmul
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(rate * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have hlim :
      Tendsto (fun t : ℝ => A * Real.exp (-rate * t)) atTop (𝓝 0) := by
    convert tendsto_const_nhds.mul hexp using 1
    · ext t
      ring_nf
    · simp
  have hevent :
      ∀ᶠ t : ℝ in atTop, A * Real.exp (-rate * t) < (2 : ℝ) :=
    hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 2))
  rcases eventually_atTop.1 hevent with ⟨T, hT⟩
  let t : ℝ := max T 0
  have ht0 : 0 ≤ t := by
    exact le_max_right T 0
  have hTle : T ≤ t := by
    exact le_max_left T 0
  have hsmall_rhs : A * Real.exp (-rate * t) < (2 : ℝ) := hT t hTle
  have hlarge_rhs : (2 : ℝ) ≤ A * Real.exp (-rate * t) := by
    have htmp := hbound t ht0
    norm_num at htmp
    simpa [t] using htmp
  linarith

/-- Raw minimal local-stability branch of
`Paper3Constants.linearStabilityInstability`, exposing the `C¹` distance and
mass constraint. -/
def LinearStabilityInstabilityMinimalRaw
    (D : BoundedDomainData) (p : CM2Params) (S : SpectralData)
    (c1Distance : (D.Point → ℝ) → (D.Point → ℝ) → ℝ)
    (chiCritical : ℝ → ℝ) : Prop :=
  p.a = 0 → p.b = 0 →
    ∀ uStar > 0,
      let eq := minimalEquilibrium p uStar
      p.χ₀ < chiCritical uStar →
        LinearlyStable S p eq.1 eq.2 ∧
        ∃ δ > 0, ∃ A > 0, ∃ rate > 0,
          ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
            SupCloseToConstant D u₀ eq.1 δ →
            D.integral u₀ = D.volume * uStar →
              ∃ u v : ℝ → D.Point → ℝ,
                IsPaper2GlobalClassicalSolution D p u v ∧
                InitialTrace D u₀ u ∧
                ∀ t, 0 ≤ t →
                  c1Distance (u t) (fun _ => eq.1) +
                    c1Distance (v t) (fun _ => eq.2) ≤
                      A * Real.exp (-rate * t)

/-- Raw obstruction for the minimal local-stability part of
`Paper3Constants.linearStabilityInstability`: fake sup-norm closeness and the
fake mass functional can both be satisfied, while an unrelated constant `C¹`
distance prevents the asserted exponential estimate. -/
lemma not_LinearStabilityInstabilityMinimalRaw_constant_c1Distance :
    ¬ LinearStabilityInstabilityMinimalRaw
      initialContinuityNoDistanceControlDomain minimalGlobalStabilityCounterParams
      sectorialLocalExponentialCounterSpectralData
      (fun _ _ => (1 : ℝ)) (fun _ => (1 : ℝ)) := by
  intro h
  let D := initialContinuityNoDistanceControlDomain
  let p := minimalGlobalStabilityCounterParams
  have ha : p.a = 0 := by
    norm_num [p, minimalGlobalStabilityCounterParams]
  have hb : p.b = 0 := by
    norm_num [p, minimalGlobalStabilityCounterParams]
  have huStar : (0 : ℝ) < 1 := by norm_num
  have hχ : p.χ₀ < (fun _ => (1 : ℝ)) 1 := by
    norm_num [p, minimalGlobalStabilityCounterParams]
  rcases (h ha hb 1 huStar hχ).2 with
    ⟨δ, hδ_pos, A, hA_pos, rate, hrate_pos, hloc⟩
  have hpos :
      PositiveInitialDatum D (fun _ : Unit => (1 : ℝ)) := by
    constructor
    · trivial
    · intro x hx
      norm_num
  have hclose :
      SupCloseToConstant D (fun _ : Unit => (1 : ℝ))
        (minimalEquilibrium p 1).1 δ := by
    simp [SupCloseToConstant, D, p, initialContinuityNoDistanceControlDomain,
      minimalGlobalStabilityCounterParams, minimalEquilibrium, hδ_pos]
  have hmass :
      D.integral (fun _ : Unit => (1 : ℝ)) = D.volume * 1 := by
    simp [D, initialContinuityNoDistanceControlDomain]
  rcases hloc (fun _ : Unit => (1 : ℝ)) hpos hclose hmass with
    ⟨u, v, _hglobal, _htrace, hbound⟩
  have hmul : Tendsto (fun t : ℝ => rate * t) atTop atTop :=
    (Filter.tendsto_id.atTop_mul_const hrate_pos).congr
      (fun t => mul_comm t rate)
  have hneg : Tendsto (fun t : ℝ => -(rate * t)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hmul
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(rate * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have hlim :
      Tendsto (fun t : ℝ => A * Real.exp (-rate * t)) atTop (𝓝 0) := by
    convert tendsto_const_nhds.mul hexp using 1
    · ext t
      ring_nf
    · simp
  have hevent :
      ∀ᶠ t : ℝ in atTop, A * Real.exp (-rate * t) < (2 : ℝ) :=
    hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 2))
  rcases eventually_atTop.1 hevent with ⟨T, hT⟩
  let t : ℝ := max T 0
  have ht0 : 0 ≤ t := by
    exact le_max_right T 0
  have hTle : T ≤ t := by
    exact le_max_left T 0
  have hsmall_rhs : A * Real.exp (-rate * t) < (2 : ℝ) := hT t hTle
  have hlarge_rhs : (2 : ℝ) ≤ A * Real.exp (-rate * t) := by
    have htmp := hbound t ht0
    norm_num at htmp
    simpa [t] using htmp
  linarith

/-- Raw nonminimal instability branch of
`Paper3Constants.linearStabilityInstability`, with the critical threshold
exposed instead of hidden inside a constants package. -/
def LinearInstabilityNonminimalRaw
    (p : CM2Params) (S : SpectralData) (chiCritical : ℝ → ℝ) : Prop :=
  ∀ (ha : 0 < p.a) (hb : 0 < p.b),
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    chiCritical eq.1 < p.χ₀ →
      LinearlyUnstable S p eq.1 eq.2

/-- Formula-level proof of the nonminimal raw instability branch when the
critical threshold is the actual spectral infimum. -/
lemma LinearInstabilityNonminimalRaw_paperCriticalSensitivity
    (S : SpectralData) (p : CM2Params) (H : HasNeumannSpectrum S) :
    LinearInstabilityNonminimalRaw p S
      (fun u => paperCriticalSensitivity S p u (p.ν / p.μ * u ^ p.γ)) := by
  intro ha hb
  dsimp
  intro hχ
  exact positiveEquilibrium_linearlyUnstable_of_paperCriticalSensitivity_lt_chi_neumann
    S p H ha hb (by
      simpa [positiveEquilibrium] using hχ)

/-- Raw nonminimal instability obstruction: an arbitrary critical-threshold
function can make the threshold hypothesis true even when the chosen spectral
data are linearly stable in every nonzero mode. -/
lemma not_LinearInstabilityNonminimalRaw_arbitrary_threshold :
    ¬ LinearInstabilityNonminimalRaw theorem21Part1CounterParams
      sectorialLocalExponentialCounterSpectralData (fun _ => (-1 : ℝ)) := by
  intro h
  let p := theorem21Part1CounterParams
  let S := sectorialLocalExponentialCounterSpectralData
  have ha : 0 < p.a := by
    norm_num [p, theorem21Part1CounterParams]
  have hb : 0 < p.b := by
    norm_num [p, theorem21Part1CounterParams]
  have hχ :
      (fun _ => (-1 : ℝ)) (positiveEquilibrium p ⟨ha, hb⟩).1 < p.χ₀ := by
    norm_num [p, theorem21Part1CounterParams]
  have hstable :
      LinearlyStable S p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 := by
    simpa [S, p, theorem21Part1CounterParams, positiveEquilibrium] using
      sectorialLocalExponentialCounter_linearlyStable
  rcases h ha hb hχ with ⟨n, hn, hpos⟩
  have hneg := hstable n hn
  linarith

/-- Raw minimal instability branch of
`Paper3Constants.linearStabilityInstability`, with the critical threshold
exposed instead of hidden inside a constants package. -/
def LinearInstabilityMinimalRaw
    (p : CM2Params) (S : SpectralData) (chiCritical : ℝ → ℝ) : Prop :=
  p.a = 0 → p.b = 0 →
    ∀ uStar > 0,
      let eq := minimalEquilibrium p uStar
      chiCritical uStar < p.χ₀ →
        LinearlyUnstable S p eq.1 eq.2

/-- Formula-level proof of the minimal raw instability branch when the critical
threshold is the actual spectral infimum. -/
lemma LinearInstabilityMinimalRaw_paperCriticalSensitivity
    (S : SpectralData) (p : CM2Params) (H : HasNeumannSpectrum S) :
    LinearInstabilityMinimalRaw p S
      (fun u => paperCriticalSensitivity S p u (p.ν / p.μ * u ^ p.γ)) := by
  intro _ha _hb uStar huStar
  dsimp
  intro hχ
  exact minimalEquilibrium_linearlyUnstable_of_paperCriticalSensitivity_lt_chi_neumann
    S p H huStar (by
      simpa [minimalEquilibrium] using hχ)

/-- Raw minimal instability obstruction: an arbitrary critical-threshold
function can make the threshold hypothesis true even though the concrete
minimal counter-parameters are linearly stable for the helper spectrum at
`uStar = 1`. -/
lemma not_LinearInstabilityMinimalRaw_arbitrary_threshold :
    ¬ LinearInstabilityMinimalRaw minimalGlobalStabilityCounterParams
      sectorialLocalExponentialCounterSpectralData (fun _ => (0 : ℝ)) := by
  intro h
  let p := minimalGlobalStabilityCounterParams
  let S := sectorialLocalExponentialCounterSpectralData
  have ha : p.a = 0 := by
    norm_num [p, minimalGlobalStabilityCounterParams]
  have hb : p.b = 0 := by
    norm_num [p, minimalGlobalStabilityCounterParams]
  have huStar : (0 : ℝ) < 1 := by norm_num
  have hχ : (fun _ => (0 : ℝ)) 1 < p.χ₀ := by
    norm_num [p, minimalGlobalStabilityCounterParams]
  have hstable :
      LinearlyStable S p (minimalEquilibrium p 1).1
        (minimalEquilibrium p 1).2 := by
    intro n hn
    simp [S, p, sectorialLocalExponentialCounterSpectralData,
      minimalGlobalStabilityCounterParams, minimalEquilibrium, sigma, hn]
    norm_num
  rcases h ha hb 1 huStar hχ with ⟨n, hn, hpos⟩
  have hneg := hstable n hn
  linarith

/-- Raw version of `CompactnessData.upperEnvelopeMonotonicity`, exposing the
upper-envelope functional instead of hiding it inside a compactness package. -/
def UpperEnvelopeMonotonicityRaw
    (D : BoundedDomainData) (p : CM2Params)
    (upperEnvelope : (D.Point → ℝ) → ℝ) : Prop :=
  ∀ u v : ℝ → D.Point → ℝ,
    PositiveGlobalBoundedSolution D p u v →
      (p.χ₀ ≤ 0 → 0 < p.a → 0 < p.b →
        ∀ t₀, 0 < t₀ →
          (p.a / p.b) ^ (1 / p.α) < upperEnvelope (u t₀) →
          ∀ t₁ t₂, 0 < t₁ → t₁ ≤ t₂ → t₂ ≤ t₀ →
            upperEnvelope (u t₂) ≤ upperEnvelope (u t₁)) ∧
      (p.χ₀ ≤ 0 → p.a = 0 → p.b = 0 →
        ∀ t₁ t₂, 0 < t₁ → t₁ ≤ t₂ →
          upperEnvelope (u t₂) ≤ upperEnvelope (u t₁))

lemma initialContinuityNoDistanceControl_increasing_minimal_classical
    (T : ℝ) (hT : 0 < T) :
    IsPaper2ClassicalSolution initialContinuityNoDistanceControlDomain
      proposition14NoRegularityParams T
      (fun t _ => t + 1) (fun t _ => t + 1) := by
  refine ⟨hT, trivial, ?_, ?_, ?_, ?_⟩
  · intro t x ht0 htT hx
    linarith
  · intro t x ht0 htT hx
    change (0 : ℝ) =
      0 - proposition14NoRegularityParams.χ₀ * 0 +
        (t + 1) * (proposition14NoRegularityParams.a -
          proposition14NoRegularityParams.b *
            (t + 1) ^ proposition14NoRegularityParams.α)
    norm_num [proposition14NoRegularityParams]
  · intro t x ht0 htT hx
    change (0 : ℝ) =
      0 - proposition14NoRegularityParams.μ * (t + 1) +
        proposition14NoRegularityParams.ν *
          (t + 1) ^ proposition14NoRegularityParams.γ
    norm_num [proposition14NoRegularityParams]
  · intro t x ht0 htT hx
    cases hx

lemma initialContinuityNoDistanceControl_increasing_minimal_global :
    IsPaper2GlobalClassicalSolution initialContinuityNoDistanceControlDomain
      proposition14NoRegularityParams
      (fun t _ => t + 1) (fun t _ => t + 1) := by
  intro T hT
  exact initialContinuityNoDistanceControl_increasing_minimal_classical T hT

lemma initialContinuityNoDistanceControl_increasing_minimal_positiveGlobalBounded :
    PositiveGlobalBoundedSolution initialContinuityNoDistanceControlDomain
      proposition14NoRegularityParams
      (fun t _ => t + 1) (fun t _ => t + 1) := by
  refine ⟨initialContinuityNoDistanceControl_increasing_minimal_global, ?_, ?_⟩
  · exact ⟨0, Eventually.of_forall fun _t => le_rfl⟩
  · intro t x ht hx
    linarith

/-- Raw obstruction for `CompactnessData.upperEnvelopeMonotonicity`.  The
current abstract PDE interface can declare the increasing profile `u(t)=t+1`
to be a positive global bounded solution by making the time derivative and
sup-norm fields fake; the point-value upper envelope then violates the claimed
monotonicity. -/
lemma not_UpperEnvelopeMonotonicityRaw_eval_increasing_solution :
    ¬ UpperEnvelopeMonotonicityRaw initialContinuityNoDistanceControlDomain
      proposition14NoRegularityParams (fun f => f ()) := by
  intro h
  let u : ℝ → Unit → ℝ := fun t _ => t + 1
  have hmono :=
    (h u u
      initialContinuityNoDistanceControl_increasing_minimal_positiveGlobalBounded).2
      (by norm_num [proposition14NoRegularityParams])
      (by norm_num [proposition14NoRegularityParams])
      (by norm_num [proposition14NoRegularityParams])
      1 2 (by norm_num) (by norm_num)
  norm_num [u] at hmono

/-- Raw version of `CompactnessData.timeTranslateCompactness`, exposing the
local convergence predicate instead of hiding it inside a compactness package. -/
def TimeTranslateCompactnessRaw
    (D : BoundedDomainData) (p : CM2Params)
    (locallyConverges :
      (ℕ → ℝ → D.Point → ℝ) → (ℝ → D.Point → ℝ) → Prop) : Prop :=
  1 ≤ p.m → 0 < p.γ →
    ∀ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v →
        ∀ times : ℕ → ℝ, Tendsto times atTop atTop →
          ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
          ∃ uInf vInf : ℝ → D.Point → ℝ,
            locallyConverges (fun n t x => u (t + times (subseq n)) x) uInf ∧
            locallyConverges (fun n t x => v (t + times (subseq n)) x) vInf ∧
            ∀ T > 0, IsPaper2ClassicalSolution D p T
              (fun t x => uInf (t - T / 2) x)
              (fun t x => vInf (t - T / 2) x)

/-- Raw obstruction for `CompactnessData.timeTranslateCompactness`: without a
real local-convergence semantics, the compactness conclusion is just an
assumption.  Taking `locallyConverges` to be identically false refutes the raw
shape even for the positive constant solution. -/
lemma not_TimeTranslateCompactnessRaw_false_locallyConverges :
    ¬ TimeTranslateCompactnessRaw initialContinuityNoDistanceControlDomain
      theorem21Part1CounterParams (fun _ _ => False) := by
  intro h
  have htimes : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  rcases h
      (by norm_num [theorem21Part1CounterParams])
      (by norm_num [theorem21Part1CounterParams])
      (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ))
      initialContinuityNoDistanceControl_constant_one_positiveGlobalBounded
      (fun n : ℕ => (n : ℝ)) htimes with
    ⟨subseq, hsubseq, uInf, vInf, hloc_u, _hloc_v, _hclassical⟩
  exact hloc_u

/-- Raw version of `CompactnessData.neumannResolventGradientBound_exists`,
with the bound predicate exposed. -/
def NeumannResolventGradientBoundExistsRaw
    (D : BoundedDomainData)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (D.Point → ℝ) → ℝ → Prop) : Prop :=
  ∃ M0 > 0, ∀ mu nu : ℝ, ∀ f : D.Point → ℝ,
    0 < mu → 0 < nu →
      neumannResolventGradientBound mu nu f M0

/-- Raw obstruction for `CompactnessData.neumannResolventGradientBound_exists`:
if the exposed resolvent-gradient predicate is unrelated to analysis and is
identically false, no uniform bound witness can exist. -/
lemma not_NeumannResolventGradientBoundExistsRaw_false_bound :
    ¬ NeumannResolventGradientBoundExistsRaw initialContinuityNoDistanceControlDomain
      (fun _ _ _ _ => False) := by
  rintro ⟨M0, hM0_pos, hbound⟩
  exact hbound 1 1 (fun _ : Unit => (0 : ℝ)) (by norm_num) (by norm_num)

/-- Raw version of `Paper3Constants.uniformPersistencePart1`, with no
constants package. -/
def UniformPersistencePart1Raw
    (D : BoundedDomainData) (p : CM2Params) : Prop :=
  1 ≤ p.m →
    ∀ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v →
        ∃ δu > 0, EventuallyLowerBound D u δu ∧
          EventuallyLowerBound D v (p.ν / p.μ * δu ^ p.γ)

/-- Raw obstruction for `uniformPersistencePart1`: on the fake lower-envelope
domain the positive constant solution exists, but `infValue` is identically
zero, so no positive eventual lower bound can hold. -/
lemma not_UniformPersistencePart1Raw_no_lower_envelope :
    ¬ UniformPersistencePart1Raw theorem21Part1NoLowerEnvelopeDomain
      theorem21Part1CounterParams := by
  intro h
  let D := theorem21Part1NoLowerEnvelopeDomain
  let p := theorem21Part1CounterParams
  have hm : 1 ≤ p.m := by
    norm_num [p, theorem21Part1CounterParams]
  rcases h hm (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ))
      theorem21Part1Counter_positiveGlobalBounded with
    ⟨δu, hδu_pos, hlowerU, _hlowerV⟩
  rcases hlowerU with ⟨_hδu_pos', hlower_eventually⟩
  have heventually_nonpos :
      ∀ᶠ t : ℝ in atTop, δu ≤ (0 : ℝ) := by
    simpa [D, theorem21Part1NoLowerEnvelopeDomain] using hlower_eventually
  rcases eventually_atTop.1 heventually_nonpos with ⟨T, hT⟩
  have hnonpos : δu ≤ 0 := hT T le_rfl
  linarith

/-- The abstract `StabilityNorms` package cannot be instantiated on an arbitrary
`BoundedDomainData`.  On the fake lower-envelope domain the PDE admits the
positive constant solution `u = v = 1`, but `supNorm` is identically `1`, so the
negative-sensitivity global-stability field would force the constant function
`1` to tend to `0`. -/
lemma not_exists_StabilityNorms_no_supNorm_convergence :
    ¬ Nonempty (StabilityNorms theorem21Part1NoLowerEnvelopeDomain) := by
  rintro ⟨N⟩
  let D := theorem21Part1NoLowerEnvelopeDomain
  let p := theorem21Part1CounterParams
  have ha : 0 < p.a := by
    norm_num [p, theorem21Part1CounterParams]
  have hb : 0 < p.b := by
    norm_num [p, theorem21Part1CounterParams]
  have hχ : p.χ₀ ≤ 0 := by
    norm_num [p, theorem21Part1CounterParams]
  have hm : 1 ≤ p.m := by
    norm_num [p, theorem21Part1CounterParams]
  have hbranch := (N.negativeSensitivityGlobalStability p hχ hm).1 ha hb
  have hconv :
      UniformConvergesInSup D (fun _ _ => (1 : ℝ))
        (positiveEquilibrium p ⟨ha, hb⟩).1 :=
    hbranch.1 (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ))
      theorem21Part1Counter_positiveGlobalBounded
  have hlim_zero : Tendsto (fun _t : ℝ => (1 : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simp [UniformConvergesInSup, D, theorem21Part1NoLowerEnvelopeDomain] at hconv
  have hlim_one : Tendsto (fun _t : ℝ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) :=
    tendsto_const_nhds
  have hone_eq_zero : (1 : ℝ) = 0 :=
    tendsto_nhds_unique hlim_one hlim_zero
  norm_num at hone_eq_zero

/-- The same fake lower-envelope domain also rules out a `Paper3Constants`
package for the Part (1) persistence parameters.  The
`uniformPersistencePart1` field would give a positive eventual lower bound for
`u = 1`, but `infValue` is identically zero. -/
lemma not_exists_Paper3Constants_theorem21_part1_counterdomain :
    ¬ Nonempty
      (Paper3Constants theorem21Part1NoLowerEnvelopeDomain
        theorem21Part1CounterParams) := by
  rintro ⟨C⟩
  let D := theorem21Part1NoLowerEnvelopeDomain
  let p := theorem21Part1CounterParams
  have hm : 1 ≤ p.m := by
    norm_num [p, theorem21Part1CounterParams]
  rcases C.uniformPersistencePart1 hm
      (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ))
      theorem21Part1Counter_positiveGlobalBounded with
    ⟨δu, hδu_pos, hlowerU, _hlowerV⟩
  rcases hlowerU with ⟨_hδu_pos', hlower_eventually⟩
  have heventually_nonpos :
      ∀ᶠ t : ℝ in atTop, δu ≤ (0 : ℝ) := by
    simpa [D, theorem21Part1NoLowerEnvelopeDomain] using hlower_eventually
  rcases eventually_atTop.1 heventually_nonpos with ⟨T, hT⟩
  have hnonpos : δu ≤ 0 := hT T le_rfl
  linarith

lemma not_forall_Theorem_2_1_part1 :
    ¬ (∀ D : BoundedDomainData, ∀ p : CM2Params, Theorem_2_1_part1 D p) := by
  intro h
  let D := theorem21Part1NoLowerEnvelopeDomain
  let p := theorem21Part1CounterParams
  have hpart := h D p
  rcases hpart (by norm_num [p, theorem21Part1CounterParams])
      (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ))
      theorem21Part1Counter_positiveGlobalBounded with
    ⟨δu, hδu_pos, hδu_lower, _hv_lower⟩
  rcases hδu_lower with ⟨_hδu_pos', hlower_eventually⟩
  have heventually_nonpos :
      ∀ᶠ t : ℝ in atTop, δu ≤ (0 : ℝ) := by
    simpa [D, theorem21Part1NoLowerEnvelopeDomain] using hlower_eventually
  rcases eventually_atTop.1 heventually_nonpos with ⟨T, hT⟩
  have hnonpos : δu ≤ 0 := hT T le_rfl
  linarith

lemma theorem21NoLowerEnvelope_constant_one_classical
    (p : CM2Params) (ha : p.a = 1) (hb : p.b = 1)
    (hmu : p.μ = 1) (hnu : p.ν = 1)
    (T : ℝ) (hT : 0 < T) :
    IsPaper2ClassicalSolution theorem21Part1NoLowerEnvelopeDomain p T
      (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) := by
  refine ⟨hT, trivial, ?_, ?_, ?_, ?_⟩
  · intro t x ht0 htT hx
    norm_num
  · intro t x ht0 htT hx
    change (0 : ℝ) =
      0 - p.χ₀ * 0 + 1 * (p.a - p.b * (1 : ℝ) ^ p.α)
    rw [Real.one_rpow, ha, hb]
    ring
  · intro t x ht0 htT hx
    change (0 : ℝ) = 0 - p.μ * 1 + p.ν * (1 : ℝ) ^ p.γ
    rw [Real.one_rpow, hmu, hnu]
    ring
  · intro t x ht0 htT hx
    cases hx

lemma theorem21NoLowerEnvelope_constant_one_positiveGlobalBounded
    (p : CM2Params) (ha : p.a = 1) (hb : p.b = 1)
    (hmu : p.μ = 1) (hnu : p.ν = 1) :
    PositiveGlobalBoundedSolution theorem21Part1NoLowerEnvelopeDomain p
      (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro T hT
    exact theorem21NoLowerEnvelope_constant_one_classical p ha hb hmu hnu T hT
  · exact ⟨1, Eventually.of_forall fun _t => le_rfl⟩
  · intro t x ht hx
    norm_num

def theorem21Part2CounterParams : CM2Params :=
  { N := 1
    hN := by norm_num
    α := 1
    γ := 1
    m := 1
    μ := 1
    ν := 1
    χ₀ := 1 / 2
    a := 1
    b := 1
    β := 1
    hα := by norm_num
    hγ := by norm_num
    hm := by norm_num
    hμ := by norm_num
    hν := by norm_num
    ha := by norm_num
    hb := by norm_num
    hβ := by norm_num }

def Theorem_2_1_part2 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  0 < p.a → 0 < p.b → 0 < p.χ₀ → p.m = 1 → 1 ≤ p.β →
    p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)) →
      ∀ u v : ℝ → D.Point → ℝ,
        PositiveGlobalBoundedSolution D p u v →
          let lowerU :=
            ((p.a - p.χ₀ * p.μ * Theta_beta (p.β - 1)) / p.b) ^ (1 / p.α)
          EventuallyLowerBound D u lowerU ∧
            EventuallyLowerBound D v (p.ν / p.μ * lowerU ^ p.γ)

/-- Raw version of `Paper3Constants.uniformPersistencePart2`, with no
constants package. -/
def UniformPersistencePart2Raw
    (D : BoundedDomainData) (p : CM2Params) : Prop :=
  0 < p.a → 0 < p.b → 0 < p.χ₀ → p.m = 1 → 1 ≤ p.β →
    p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)) →
      ∀ u v : ℝ → D.Point → ℝ,
        PositiveGlobalBoundedSolution D p u v →
          let lowerU :=
            ((p.a - p.χ₀ * p.μ * Theta_beta (p.β - 1)) / p.b) ^ (1 / p.α)
          EventuallyLowerBound D u lowerU ∧
            EventuallyLowerBound D v (p.ν / p.μ * lowerU ^ p.γ)

lemma Theorem_2_1_part2.lower_bounds
    {D : BoundedDomainData} {p : CM2Params}
    (h : Theorem_2_1_part2 D p)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v) :
    let lowerU :=
      ((p.a - p.χ₀ * p.μ * Theta_beta (p.β - 1)) / p.b) ^ (1 / p.α)
    EventuallyLowerBound D u lowerU ∧
      EventuallyLowerBound D v (p.ν / p.μ * lowerU ^ p.γ) :=
  h ha hb hχ0 hm hβ hχ u v huv

lemma not_forall_Theorem_2_1_part2 :
    ¬ (∀ D : BoundedDomainData, ∀ p : CM2Params, Theorem_2_1_part2 D p) := by
  intro h
  let D := theorem21Part1NoLowerEnvelopeDomain
  let p := theorem21Part2CounterParams
  have hpart := h D p
  have hχ :
      p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)) := by
    norm_num [p, theorem21Part2CounterParams, Theta_beta_zero]
  have huv :
      PositiveGlobalBoundedSolution D p
        (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) := by
    exact theorem21NoLowerEnvelope_constant_one_positiveGlobalBounded p
      (by norm_num [p, theorem21Part2CounterParams])
      (by norm_num [p, theorem21Part2CounterParams])
      (by norm_num [p, theorem21Part2CounterParams])
      (by norm_num [p, theorem21Part2CounterParams])
  rcases hpart
      (by norm_num [p, theorem21Part2CounterParams])
      (by norm_num [p, theorem21Part2CounterParams])
      (by norm_num [p, theorem21Part2CounterParams])
      (by norm_num [p, theorem21Part2CounterParams])
      (by norm_num [p, theorem21Part2CounterParams])
      hχ (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) huv with
    ⟨hlowerU, _hlowerV⟩
  rcases hlowerU with ⟨hlowerU_pos, hlowerU_eventually⟩
  have heventually_nonpos :
      ∀ᶠ t : ℝ in atTop,
        ((p.a - p.χ₀ * p.μ * Theta_beta (p.β - 1)) / p.b) ^
            (1 / p.α) ≤ (0 : ℝ) := by
    simpa [D, theorem21Part1NoLowerEnvelopeDomain] using hlowerU_eventually
  rcases eventually_atTop.1 heventually_nonpos with ⟨T, hT⟩
  have hnonpos :
      ((p.a - p.χ₀ * p.μ * Theta_beta (p.β - 1)) / p.b) ^
          (1 / p.α) ≤ (0 : ℝ) := hT T le_rfl
  linarith

/-- Raw obstruction for `uniformPersistencePart2`: on the fake lower-envelope
domain the positive constant solution exists, but `infValue` is identically
zero, contradicting the positive lower bound forced by the field. -/
lemma not_UniformPersistencePart2Raw_no_lower_envelope :
    ¬ UniformPersistencePart2Raw theorem21Part1NoLowerEnvelopeDomain
      theorem21Part2CounterParams := by
  intro h
  let D := theorem21Part1NoLowerEnvelopeDomain
  let p := theorem21Part2CounterParams
  have hχ :
      p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)) := by
    norm_num [p, theorem21Part2CounterParams, Theta_beta_zero]
  have huv :
      PositiveGlobalBoundedSolution D p
        (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) := by
    exact theorem21NoLowerEnvelope_constant_one_positiveGlobalBounded p
      (by norm_num [p, theorem21Part2CounterParams])
      (by norm_num [p, theorem21Part2CounterParams])
      (by norm_num [p, theorem21Part2CounterParams])
      (by norm_num [p, theorem21Part2CounterParams])
  rcases h
      (by norm_num [p, theorem21Part2CounterParams])
      (by norm_num [p, theorem21Part2CounterParams])
      (by norm_num [p, theorem21Part2CounterParams])
      (by norm_num [p, theorem21Part2CounterParams])
      (by norm_num [p, theorem21Part2CounterParams])
      hχ (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) huv with
    ⟨hlowerU, _hlowerV⟩
  rcases hlowerU with ⟨_hlowerU_pos, hlowerU_eventually⟩
  have heventually_nonpos :
      ∀ᶠ t : ℝ in atTop,
        ((p.a - p.χ₀ * p.μ * Theta_beta (p.β - 1)) / p.b) ^
            (1 / p.α) ≤ (0 : ℝ) := by
    simpa [D, theorem21Part1NoLowerEnvelopeDomain] using hlowerU_eventually
  rcases eventually_atTop.1 heventually_nonpos with ⟨T, hT⟩
  have hnonpos :
      ((p.a - p.χ₀ * p.μ * Theta_beta (p.β - 1)) / p.b) ^
          (1 / p.α) ≤ (0 : ℝ) := hT T le_rfl
  linarith

/-- Package-level version of the Part (2) lower-envelope obstruction.  The
`uniformPersistencePart2` field of `Paper3Constants` would force a positive
eventual lower bound, contradicting `infValue ≡ 0` on the fake domain. -/
lemma not_exists_Paper3Constants_theorem21_part2_counterdomain :
    ¬ Nonempty
      (Paper3Constants theorem21Part1NoLowerEnvelopeDomain
        theorem21Part2CounterParams) := by
  rintro ⟨C⟩
  let D := theorem21Part1NoLowerEnvelopeDomain
  let p := theorem21Part2CounterParams
  have hχ :
      p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)) := by
    norm_num [p, theorem21Part2CounterParams, Theta_beta_zero]
  have huv :
      PositiveGlobalBoundedSolution D p
        (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) := by
    exact theorem21NoLowerEnvelope_constant_one_positiveGlobalBounded p
      (by norm_num [p, theorem21Part2CounterParams])
      (by norm_num [p, theorem21Part2CounterParams])
      (by norm_num [p, theorem21Part2CounterParams])
      (by norm_num [p, theorem21Part2CounterParams])
  rcases C.uniformPersistencePart2
      (by norm_num [p, theorem21Part2CounterParams])
      (by norm_num [p, theorem21Part2CounterParams])
      (by norm_num [p, theorem21Part2CounterParams])
      (by norm_num [p, theorem21Part2CounterParams])
      (by norm_num [p, theorem21Part2CounterParams])
      hχ (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) huv with
    ⟨hlowerU, _hlowerV⟩
  rcases hlowerU with ⟨hlowerU_pos, hlowerU_eventually⟩
  have heventually_nonpos :
      ∀ᶠ t : ℝ in atTop,
        ((p.a - p.χ₀ * p.μ * Theta_beta (p.β - 1)) / p.b) ^
            (1 / p.α) ≤ (0 : ℝ) := by
    simpa [D, theorem21Part1NoLowerEnvelopeDomain] using hlowerU_eventually
  rcases eventually_atTop.1 heventually_nonpos with ⟨T, hT⟩
  have hnonpos :
      ((p.a - p.χ₀ * p.μ * Theta_beta (p.β - 1)) / p.b) ^
          (1 / p.α) ≤ (0 : ℝ) := hT T le_rfl
  linarith

def Theorem_2_1_part3 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  0 < p.a → 0 < p.b → 0 < p.χ₀ → 1 < p.m → 1 ≤ p.β →
    ∀ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v →
        let lowerU :=
          min 1 (p.a / (p.b + p.χ₀ * p.μ * Theta_beta (p.β - 1))) ^
            max (1 / (p.m - 1)) (1 / p.α)
        EventuallyLowerBound D u lowerU ∧
          EventuallyLowerBound D v (p.ν / p.μ * lowerU ^ p.γ)

/-- Raw version of `Paper3Constants.uniformPersistencePart3`, with no
constants package. -/
def UniformPersistencePart3Raw
    (D : BoundedDomainData) (p : CM2Params) : Prop :=
  0 < p.a → 0 < p.b → 0 < p.χ₀ → 1 < p.m → 1 ≤ p.β →
    ∀ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v →
        let lowerU :=
          min 1 (p.a / (p.b + p.χ₀ * p.μ * Theta_beta (p.β - 1))) ^
            max (1 / (p.m - 1)) (1 / p.α)
        EventuallyLowerBound D u lowerU ∧
          EventuallyLowerBound D v (p.ν / p.μ * lowerU ^ p.γ)

lemma Theorem_2_1_part3.lower_bounds
    {D : BoundedDomainData} {p : CM2Params}
    (h : Theorem_2_1_part3 D p)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : 1 < p.m) (hβ : 1 ≤ p.β)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v) :
    let lowerU :=
      min 1 (p.a / (p.b + p.χ₀ * p.μ * Theta_beta (p.β - 1))) ^
        max (1 / (p.m - 1)) (1 / p.α)
    EventuallyLowerBound D u lowerU ∧
      EventuallyLowerBound D v (p.ν / p.μ * lowerU ^ p.γ) :=
  h ha hb hχ0 hm hβ u v huv

def theorem21Part3CounterParams : CM2Params :=
  { N := 1
    hN := by norm_num
    α := 1
    γ := 1
    m := 2
    μ := 1
    ν := 1
    χ₀ := 1
    a := 1
    b := 1
    β := 1
    hα := by norm_num
    hγ := by norm_num
    hm := by norm_num
    hμ := by norm_num
    hν := by norm_num
    ha := by norm_num
    hb := by norm_num
    hβ := by norm_num }

lemma not_forall_Theorem_2_1_part3 :
    ¬ (∀ D : BoundedDomainData, ∀ p : CM2Params, Theorem_2_1_part3 D p) := by
  intro h
  let D := theorem21Part1NoLowerEnvelopeDomain
  let p := theorem21Part3CounterParams
  have hpart := h D p
  have huv :
      PositiveGlobalBoundedSolution D p
        (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) := by
    exact theorem21NoLowerEnvelope_constant_one_positiveGlobalBounded p
      (by norm_num [p, theorem21Part3CounterParams])
      (by norm_num [p, theorem21Part3CounterParams])
      (by norm_num [p, theorem21Part3CounterParams])
      (by norm_num [p, theorem21Part3CounterParams])
  rcases hpart
      (by norm_num [p, theorem21Part3CounterParams])
      (by norm_num [p, theorem21Part3CounterParams])
      (by norm_num [p, theorem21Part3CounterParams])
      (by norm_num [p, theorem21Part3CounterParams])
      (by norm_num [p, theorem21Part3CounterParams])
      (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) huv with
    ⟨hlowerU, _hlowerV⟩
  rcases hlowerU with ⟨hlowerU_pos, hlowerU_eventually⟩
  have heventually_nonpos :
      ∀ᶠ t : ℝ in atTop,
        (min 1
            (p.a / (p.b + p.χ₀ * p.μ * Theta_beta (p.β - 1))) ^
          max (1 / (p.m - 1)) (1 / p.α)) ≤ (0 : ℝ) := by
    simpa [D, theorem21Part1NoLowerEnvelopeDomain] using hlowerU_eventually
  rcases eventually_atTop.1 heventually_nonpos with ⟨T, hT⟩
  have hnonpos :
      (min 1
          (p.a / (p.b + p.χ₀ * p.μ * Theta_beta (p.β - 1))) ^
        max (1 / (p.m - 1)) (1 / p.α)) ≤ (0 : ℝ) := hT T le_rfl
  linarith

/-- Raw obstruction for `uniformPersistencePart3`: the fake lower-envelope
domain again refutes the asserted positive lower bound. -/
lemma not_UniformPersistencePart3Raw_no_lower_envelope :
    ¬ UniformPersistencePart3Raw theorem21Part1NoLowerEnvelopeDomain
      theorem21Part3CounterParams := by
  intro h
  let D := theorem21Part1NoLowerEnvelopeDomain
  let p := theorem21Part3CounterParams
  have huv :
      PositiveGlobalBoundedSolution D p
        (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) := by
    exact theorem21NoLowerEnvelope_constant_one_positiveGlobalBounded p
      (by norm_num [p, theorem21Part3CounterParams])
      (by norm_num [p, theorem21Part3CounterParams])
      (by norm_num [p, theorem21Part3CounterParams])
      (by norm_num [p, theorem21Part3CounterParams])
  rcases h
      (by norm_num [p, theorem21Part3CounterParams])
      (by norm_num [p, theorem21Part3CounterParams])
      (by norm_num [p, theorem21Part3CounterParams])
      (by norm_num [p, theorem21Part3CounterParams])
      (by norm_num [p, theorem21Part3CounterParams])
      (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) huv with
    ⟨hlowerU, _hlowerV⟩
  rcases hlowerU with ⟨_hlowerU_pos, hlowerU_eventually⟩
  have heventually_nonpos :
      ∀ᶠ t : ℝ in atTop,
        (min 1
            (p.a / (p.b + p.χ₀ * p.μ * Theta_beta (p.β - 1))) ^
          max (1 / (p.m - 1)) (1 / p.α)) ≤ (0 : ℝ) := by
    simpa [D, theorem21Part1NoLowerEnvelopeDomain] using hlowerU_eventually
  rcases eventually_atTop.1 heventually_nonpos with ⟨T, hT⟩
  have hnonpos :
      (min 1
          (p.a / (p.b + p.χ₀ * p.μ * Theta_beta (p.β - 1))) ^
        max (1 / (p.m - 1)) (1 / p.α)) ≤ (0 : ℝ) := hT T le_rfl
  linarith

/-- Package-level version of the Part (3) lower-envelope obstruction. -/
lemma not_exists_Paper3Constants_theorem21_part3_counterdomain :
    ¬ Nonempty
      (Paper3Constants theorem21Part1NoLowerEnvelopeDomain
        theorem21Part3CounterParams) := by
  rintro ⟨C⟩
  let D := theorem21Part1NoLowerEnvelopeDomain
  let p := theorem21Part3CounterParams
  have huv :
      PositiveGlobalBoundedSolution D p
        (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) := by
    exact theorem21NoLowerEnvelope_constant_one_positiveGlobalBounded p
      (by norm_num [p, theorem21Part3CounterParams])
      (by norm_num [p, theorem21Part3CounterParams])
      (by norm_num [p, theorem21Part3CounterParams])
      (by norm_num [p, theorem21Part3CounterParams])
  rcases C.uniformPersistencePart3
      (by norm_num [p, theorem21Part3CounterParams])
      (by norm_num [p, theorem21Part3CounterParams])
      (by norm_num [p, theorem21Part3CounterParams])
      (by norm_num [p, theorem21Part3CounterParams])
      (by norm_num [p, theorem21Part3CounterParams])
      (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) huv with
    ⟨hlowerU, _hlowerV⟩
  rcases hlowerU with ⟨hlowerU_pos, hlowerU_eventually⟩
  have heventually_nonpos :
      ∀ᶠ t : ℝ in atTop,
        (min 1
            (p.a / (p.b + p.χ₀ * p.μ * Theta_beta (p.β - 1))) ^
          max (1 / (p.m - 1)) (1 / p.α)) ≤ (0 : ℝ) := by
    simpa [D, theorem21Part1NoLowerEnvelopeDomain] using hlowerU_eventually
  rcases eventually_atTop.1 heventually_nonpos with ⟨T, hT⟩
  have hnonpos :
      (min 1
          (p.a / (p.b + p.χ₀ * p.μ * Theta_beta (p.β - 1))) ^
        max (1 / (p.m - 1)) (1 / p.α)) ≤ (0 : ℝ) := hT T le_rfl
  linarith

/-- Parameters for the minimal-model lower-bound obstruction in Theorem 2.1(4).
The fake bounded-domain API still admits the positive constant solution
`u = v = 1`, but its `infValue` functional is identically zero. -/
def theorem21Part4CounterParams : CM2Params :=
  { N := 1
    hN := by norm_num
    α := 1
    γ := 1
    m := 1
    μ := 1
    ν := 1
    χ₀ := 1 / 4
    a := 0
    b := 0
    β := 1
    hα := by norm_num
    hγ := by norm_num
    hm := by norm_num
    hμ := by norm_num
    hν := by norm_num
    ha := by norm_num
    hb := by norm_num
    hβ := by norm_num }

lemma theorem21Part4Counter_classical (T : ℝ) (hT : 0 < T) :
    IsPaper2ClassicalSolution theorem21Part1NoLowerEnvelopeDomain
      theorem21Part4CounterParams T
      (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) := by
  refine ⟨hT, trivial, ?_, ?_, ?_, ?_⟩
  · intro t x ht0 htT hx
    norm_num
  · intro t x ht0 htT hx
    change (0 : ℝ) =
      0 - theorem21Part4CounterParams.χ₀ * 0 +
        1 * (theorem21Part4CounterParams.a -
          theorem21Part4CounterParams.b * (1 : ℝ) ^ theorem21Part4CounterParams.α)
    norm_num [theorem21Part4CounterParams]
  · intro t x ht0 htT hx
    change (0 : ℝ) =
      0 - theorem21Part4CounterParams.μ * 1 +
        theorem21Part4CounterParams.ν * (1 : ℝ) ^ theorem21Part4CounterParams.γ
    norm_num [theorem21Part4CounterParams]
  · intro t x ht0 htT hx
    cases hx

lemma theorem21Part4Counter_positiveGlobalBounded :
    PositiveGlobalBoundedSolution theorem21Part1NoLowerEnvelopeDomain
      theorem21Part4CounterParams
      (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro T hT
    exact theorem21Part4Counter_classical T hT
  · exact ⟨1, Eventually.of_forall fun _t => le_rfl⟩
  · intro t x ht hx
    norm_num

lemma theorem21Part4Counter_initialMass :
    HasInitialMass theorem21Part1NoLowerEnvelopeDomain
      (fun _ _ => (1 : ℝ)) 1 := by
  unfold HasInitialMass
  change (1 : ℝ) = 1 * 1
  norm_num

/-- Raw version of `Paper3Constants.eventualMinimalUpperBound`, with the
eventual upper-bound function exposed. -/
def EventualMinimalUpperBoundRaw
    (D : BoundedDomainData) (p : CM2Params)
    (eventualMinimalUBound : ℝ → ℝ) : Prop :=
  p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
    0 < p.χ₀ → p.χ₀ < min (chiBeta p / 2) (Real.sqrt (chiBeta p)) →
      ∀ u v : ℝ → D.Point → ℝ,
        PositiveGlobalBoundedSolution D p u v →
          ∀ uStar > 0, HasInitialMass D u uStar →
            ∀ᶠ t in atTop, D.supNorm (u t) ≤ eventualMinimalUBound uStar

/-- Raw obstruction for `Paper3Constants.eventualMinimalUpperBound`: if the
exposed bound is unrelated to the fake `supNorm`, the claimed eventual upper
bound can be false even for the positive constant solution. -/
lemma not_EventualMinimalUpperBoundRaw_zero_bound :
    ¬ EventualMinimalUpperBoundRaw theorem21Part1NoLowerEnvelopeDomain
      theorem21Part4CounterParams (fun _ => (0 : ℝ)) := by
  intro h
  let D := theorem21Part1NoLowerEnvelopeDomain
  let p := theorem21Part4CounterParams
  have hχ :
      p.χ₀ < min (chiBeta p / 2) (Real.sqrt (chiBeta p)) := by
    norm_num [p, theorem21Part4CounterParams, chiBeta]
  have hupper :
      ∀ᶠ t : ℝ in atTop,
        D.supNorm (((fun _ : ℝ => fun _ : Unit => (1 : ℝ)) t)) ≤
          (fun _ => (0 : ℝ)) 1 := by
    exact h
      (by norm_num [p, theorem21Part4CounterParams])
      (by norm_num [p, theorem21Part4CounterParams])
      (by norm_num [p, theorem21Part4CounterParams])
      (by norm_num [p, theorem21Part4CounterParams])
      (by norm_num [p, theorem21Part4CounterParams])
      hχ (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ))
      theorem21Part4Counter_positiveGlobalBounded 1 (by norm_num)
      theorem21Part4Counter_initialMass
  have heventually_nonpos :
      ∀ᶠ t : ℝ in atTop, (1 : ℝ) ≤ 0 := by
    simpa [D, theorem21Part1NoLowerEnvelopeDomain] using hupper
  rcases eventually_atTop.1 heventually_nonpos with ⟨T, hT⟩
  have hbad : (1 : ℝ) ≤ 0 := hT T le_rfl
  norm_num at hbad

/-- Raw version of `Paper3Constants.uniformPersistencePart4`, with the
eventual upper-bound function and Gaussian lower constant exposed. -/
def UniformPersistencePart4Raw
    (D : BoundedDomainData) (p : CM2Params)
    (eventualMinimalUBound : ℝ → ℝ) (gaussianLowerConst : ℝ) : Prop :=
  0 < gaussianLowerConst →
    p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
      0 < p.χ₀ → p.χ₀ < min (chiBeta p / 2) (Real.sqrt (chiBeta p)) →
        ∀ uStar > 0, ∀ u v : ℝ → D.Point → ℝ,
          PositiveGlobalBoundedSolution D p u v →
          HasInitialMass D u uStar →
            EventuallyLowerBound D v
              (gaussianLowerConst *
                if p.γ ≤ 1 then
                  uStar * (eventualMinimalUBound uStar) ^ (p.γ - 1)
                else
                  uStar ^ p.γ)

/-- Raw obstruction for `uniformPersistencePart4`: the fake lower-envelope
domain refutes the positive eventual lower bound even for the positive
constant minimal-model solution. -/
lemma not_UniformPersistencePart4Raw_no_lower_envelope :
    ¬ UniformPersistencePart4Raw theorem21Part1NoLowerEnvelopeDomain
      theorem21Part4CounterParams (fun _ => (1 : ℝ)) 1 := by
  intro h
  let D := theorem21Part1NoLowerEnvelopeDomain
  let p := theorem21Part4CounterParams
  have huv :
      PositiveGlobalBoundedSolution D p
        (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) := by
    simpa [D, p] using theorem21Part4Counter_positiveGlobalBounded
  have hmass :
      HasInitialMass D (fun _ _ => (1 : ℝ)) 1 := by
    simpa [D] using theorem21Part4Counter_initialMass
  have hχ :
      p.χ₀ < min (chiBeta p / 2) (Real.sqrt (chiBeta p)) := by
    norm_num [p, theorem21Part4CounterParams, chiBeta]
  have hlower :
      EventuallyLowerBound D (fun _ _ => (1 : ℝ))
        ((1 : ℝ) *
          if p.γ ≤ 1 then
            (1 : ℝ) * ((fun _ => (1 : ℝ)) 1) ^ (p.γ - 1)
          else
            (1 : ℝ) ^ p.γ) := by
    exact h
      (by norm_num)
      (by norm_num [p, theorem21Part4CounterParams])
      (by norm_num [p, theorem21Part4CounterParams])
      (by norm_num [p, theorem21Part4CounterParams])
      (by norm_num [p, theorem21Part4CounterParams])
      (by norm_num [p, theorem21Part4CounterParams])
      hχ 1 (by norm_num) (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ))
      huv hmass
  rcases hlower with ⟨hlower_pos, hlower_eventually⟩
  have heventually_nonpos :
      ∀ᶠ t : ℝ in atTop,
        ((1 : ℝ) *
          (if p.γ ≤ 1 then
            (1 : ℝ) * ((fun _ => (1 : ℝ)) 1) ^ (p.γ - 1)
          else
            (1 : ℝ) ^ p.γ)) ≤ (0 : ℝ) := by
    simpa [D, theorem21Part1NoLowerEnvelopeDomain] using hlower_eventually
  rcases eventually_atTop.1 heventually_nonpos with ⟨T, hT⟩
  have hnonpos :
      ((1 : ℝ) *
        (if p.γ ≤ 1 then
          (1 : ℝ) * ((fun _ => (1 : ℝ)) 1) ^ (p.γ - 1)
        else
          (1 : ℝ) ^ p.γ)) ≤ (0 : ℝ) := hT T le_rfl
  linarith

/-- Raw version of the Lemma A.7 threshold comparisons, with the four strong
threshold functions and the critical threshold exposed instead of packaged as
fields of `Paper3Constants`. -/
def LemmaA7ThresholdComparisonsRaw
    (p : CM2Params)
    (chiCritical chiStrong1 chiStrong2 chiStrong3 chiStrong4 : ℝ → ℝ) :
    Prop :=
  0 ≤ p.β → 1 ≤ p.m →
    ∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      (p.α + 1 ≥ 2 * p.γ →
        chiStrong1 eq.1 ≤ chiCritical eq.1) ∧
      (1 ≤ p.β → p.α + 1 ≥ 2 * p.γ →
        chiStrong2 eq.1 ≤ chiCritical eq.1) ∧
      (1 ≤ p.γ → p.α + 1 ≥ p.m + p.γ →
        chiStrong3 eq.1 ≤ chiCritical eq.1) ∧
      (1 ≤ p.β → 1 ≤ p.γ → p.α + 1 ≥ p.m + 2 * p.γ →
        chiStrong4 eq.1 ≤ chiCritical eq.1)

/-- Formula-level raw Lemma A.7 threshold comparison.  The only threshold
input is the explicit domination of the maximum strong threshold by the chosen
critical threshold. -/
lemma LemmaA7ThresholdComparisonsRaw_of_max_le_critical
    (p : CM2Params) (M0 : ℝ) (chiCritical : ℝ → ℝ)
    (hcritical :
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        max
            (max (chiStrong1Formula p eq.1 eq.2)
              (chiStrong2Formula p eq.1))
            (max (chiStrong3Formula p M0 eq.1 eq.2)
              (chiStrong4Formula p M0 eq.1)) ≤
          chiCritical eq.1) :
    LemmaA7ThresholdComparisonsRaw p chiCritical
      (fun u => chiStrong1Formula p u (p.ν / p.μ * u ^ p.γ))
      (fun u => chiStrong2Formula p u)
      (fun u => chiStrong3Formula p M0 u (p.ν / p.μ * u ^ p.γ))
      (fun u => chiStrong4Formula p M0 u) := by
  intro _hβ _hm ha hb
  dsimp
  have hmax := hcritical ha hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _hαγ
    exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hmax
  · intro _hβ1 _hαγ
    exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hmax
  · intro _hγ _hαγ
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hmax
  · intro _hβ1 _hγ _hαγ
    exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hmax

/-- Formula-level raw Lemma A.7 threshold comparison from the first nonzero
Neumann eigenvalue lower bound. -/
lemma LemmaA7ThresholdComparisonsRaw_of_firstNonzero_lower
    (S : SpectralData) (p : CM2Params) (M0 : ℝ)
    (H : HasNeumannSpectrum S)
    (hfirst :
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        max
            (max (chiStrong1Formula p eq.1 eq.2)
              (chiStrong2Formula p eq.1))
            (max (chiStrong3Formula p M0 eq.1 eq.2)
              (chiStrong4Formula p M0 eq.1)) ≤
          ((1 + eq.2) ^ p.β /
              (p.ν * p.γ * eq.1 ^ (p.m + p.γ - 1))) *
            (p.μ + S.firstNonzero)) :
    LemmaA7ThresholdComparisonsRaw p
      (fun u => paperCriticalSensitivity S p u (p.ν / p.μ * u ^ p.γ))
      (fun u => chiStrong1Formula p u (p.ν / p.μ * u ^ p.γ))
      (fun u => chiStrong2Formula p u)
      (fun u => chiStrong3Formula p M0 u (p.ν / p.μ * u ^ p.γ))
      (fun u => chiStrong4Formula p M0 u) := by
  apply LemmaA7ThresholdComparisonsRaw_of_max_le_critical
  intro ha hb
  dsimp
  exact le_trans (hfirst ha hb) (by
    simpa [positiveEquilibrium] using
      paperCriticalSensitivity_positiveEquilibrium_ge_firstNonzero_lower
        S p H ha hb)

/-- Raw obstruction for Lemma A.7-style threshold comparisons: the comparison
is not a consequence of the parameter hypotheses alone when the threshold
functions are exposed as arbitrary data. -/
lemma not_LemmaA7ThresholdComparisonsRaw_arbitrary_thresholds :
    ¬ LemmaA7ThresholdComparisonsRaw theorem21Part1CounterParams
      (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
      (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) := by
  intro h
  have hle : (1 : ℝ) ≤ 0 := by
    simpa using
      ((h (by norm_num [theorem21Part1CounterParams])
          (by norm_num [theorem21Part1CounterParams])
          (by norm_num [theorem21Part1CounterParams])
          (by norm_num [theorem21Part1CounterParams])).1
        (by norm_num [theorem21Part1CounterParams]))
  norm_num at hle

/-- Raw version of the Lemma A.8 minimal-model threshold comparisons, with the
minimal and critical threshold functions exposed. -/
def LemmaA8ThresholdComparisonsRaw
    (p : CM2Params)
    (chiCritical chiMinimal1 chiMinimal2 : ℝ → ℝ) : Prop :=
  p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
    ∀ uStar > 0,
      (0 < p.γ → chiMinimal1 uStar ≤ chiCritical uStar) ∧
      (p.γ = 1 → chiMinimal2 uStar ≤ chiCritical uStar)

/-- The first explicit minimal threshold is bounded by `chiBeta`. -/
lemma chiMinimal1Formula_le_chiBeta_of_one_le_beta
    (p : CM2Params) (hβ : 1 ≤ p.β)
    (lambdaStar uStar uBar vLower : ℝ) :
    chiMinimal1Formula p lambdaStar uStar uBar vLower ≤ chiBeta p := by
  have hmin :
      chiMinimal1Formula p lambdaStar uStar uBar vLower ≤
        min (chiBeta p / 2) (Real.sqrt (chiBeta p)) :=
    chiMinimal1Formula_le_min_half_sqrt p lambdaStar uStar uBar vLower
  have hhalf : chiBeta p / 2 ≤ chiBeta p := by
    have hpos : 0 < chiBeta p := chiBeta_pos_of_one_le_beta p hβ
    linarith
  exact le_trans hmin (le_trans (min_le_left _ _) hhalf)

/-- The second explicit minimal threshold is bounded by `chiBeta`. -/
lemma chiMinimal2Formula_le_chiBeta_of_one_le_beta
    (p : CM2Params) (hβ : 1 ≤ p.β) (uBar vLower : ℝ) :
    chiMinimal2Formula p uBar vLower ≤ chiBeta p := by
  have hmin :
      chiMinimal2Formula p uBar vLower ≤
        min (chiBeta p / 2) (Real.sqrt (chiBeta p)) :=
    chiMinimal2Formula_le_min_half_sqrt p uBar vLower
  have hhalf : chiBeta p / 2 ≤ chiBeta p := by
    have hpos : 0 < chiBeta p := chiBeta_pos_of_one_le_beta p hβ
    linarith
  exact le_trans hmin (le_trans (min_le_left _ _) hhalf)

/-- Formula-level raw Lemma A.8 threshold comparison.  It replaces the
`Paper3Constants` comparison fields by the explicit `chiBeta` domination
condition. -/
lemma LemmaA8ThresholdComparisonsRaw_of_chiBeta_le_critical
    (p : CM2Params) (uBar vLower : ℝ) (chiCritical : ℝ → ℝ)
    (hcritical : ∀ uStar > 0, chiBeta p ≤ chiCritical uStar) :
    LemmaA8ThresholdComparisonsRaw p chiCritical
      (fun uStar => chiMinimal1Formula p 1 uStar uBar vLower)
      (fun _uStar => chiMinimal2Formula p uBar vLower) := by
  intro _ha _hb _hm hβ uStar huStar
  refine ⟨?_, ?_⟩
  · intro _hγ
    exact le_trans
      (chiMinimal1Formula_le_chiBeta_of_one_le_beta p hβ 1 uStar uBar vLower)
      (hcritical uStar huStar)
  · intro _hγ
    exact le_trans
      (chiMinimal2Formula_le_chiBeta_of_one_le_beta p hβ uBar vLower)
      (hcritical uStar huStar)

/-- Formula-level raw Lemma A.8 threshold comparison from the first nonzero
Neumann eigenvalue lower bound. -/
lemma LemmaA8ThresholdComparisonsRaw_of_firstNonzero_lower
    (S : SpectralData) (p : CM2Params) (uBar vLower : ℝ)
    (H : HasNeumannSpectrum S)
    (hfirst :
      ∀ uStar > 0,
        chiBeta p ≤
          ((1 + (minimalEquilibrium p uStar).2) ^ p.β /
              (p.ν * p.γ *
                (minimalEquilibrium p uStar).1 ^ (p.m + p.γ - 1))) *
            (p.μ + S.firstNonzero)) :
    LemmaA8ThresholdComparisonsRaw p
      (fun u => paperCriticalSensitivity S p u (p.ν / p.μ * u ^ p.γ))
      (fun uStar => chiMinimal1Formula p 1 uStar uBar vLower)
      (fun _uStar => chiMinimal2Formula p uBar vLower) := by
  apply LemmaA8ThresholdComparisonsRaw_of_chiBeta_le_critical
  intro uStar huStar
  exact le_trans (hfirst uStar huStar) (by
    simpa [minimalEquilibrium] using
      paperCriticalSensitivity_minimalEquilibrium_ge_firstNonzero_lower
        S p H huStar)

/-- Raw obstruction for Lemma A.8-style threshold comparisons: without the
exact threshold formulas, the minimal comparison fields are arbitrary data. -/
lemma not_LemmaA8ThresholdComparisonsRaw_arbitrary_thresholds :
    ¬ LemmaA8ThresholdComparisonsRaw theorem21Part4CounterParams
      (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) := by
  intro h
  have hle : (1 : ℝ) ≤ 0 := by
    simpa using
      ((h (by norm_num [theorem21Part4CounterParams])
          (by norm_num [theorem21Part4CounterParams])
          (by norm_num [theorem21Part4CounterParams])
          (by norm_num [theorem21Part4CounterParams])
          1 (by norm_num)).1
        (by norm_num [theorem21Part4CounterParams]))
  norm_num at hle

lemma not_exists_Paper3Constants_theorem21_part4_counterdomain :
    ¬ Nonempty
      (Paper3Constants theorem21Part1NoLowerEnvelopeDomain
        theorem21Part4CounterParams) := by
  rintro ⟨C⟩
  let D := theorem21Part1NoLowerEnvelopeDomain
  let p := theorem21Part4CounterParams
  have huv :
      PositiveGlobalBoundedSolution D p
        (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) := by
    simpa [D, p] using theorem21Part4Counter_positiveGlobalBounded
  have hmass :
      HasInitialMass D (fun _ _ => (1 : ℝ)) 1 := by
    simpa [D] using theorem21Part4Counter_initialMass
  have hχ :
      p.χ₀ < min (chiBeta p / 2) (Real.sqrt (chiBeta p)) := by
    norm_num [p, theorem21Part4CounterParams, chiBeta]
  have hlower :
      EventuallyLowerBound D (fun _ _ => (1 : ℝ))
        (C.gaussianLowerConst *
          if p.γ ≤ 1 then
            (1 : ℝ) * (C.eventualMinimalUBound 1) ^ (p.γ - 1)
          else
            (1 : ℝ) ^ p.γ) := by
    exact C.uniformPersistencePart4
      (by norm_num [p, theorem21Part4CounterParams])
      (by norm_num [p, theorem21Part4CounterParams])
      (by norm_num [p, theorem21Part4CounterParams])
      (by norm_num [p, theorem21Part4CounterParams])
      (by norm_num [p, theorem21Part4CounterParams])
      hχ 1 (by norm_num) (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ))
      huv hmass
  rcases hlower with ⟨hlower_pos, hlower_eventually⟩
  have heventually_nonpos :
      ∀ᶠ t : ℝ in atTop,
        C.gaussianLowerConst *
          (if p.γ ≤ 1 then
            (1 : ℝ) * (C.eventualMinimalUBound 1) ^ (p.γ - 1)
          else
            (1 : ℝ) ^ p.γ) ≤ (0 : ℝ) := by
    simpa [D, theorem21Part1NoLowerEnvelopeDomain] using hlower_eventually
  rcases eventually_atTop.1 heventually_nonpos with ⟨T, hT⟩
  have hnonpos :
      C.gaussianLowerConst *
        (if p.γ ≤ 1 then
          (1 : ℝ) * (C.eventualMinimalUBound 1) ^ (p.γ - 1)
        else
          (1 : ℝ) ^ p.γ) ≤ (0 : ℝ) := hT T le_rfl
  linarith

lemma theorem_2_1_part2_lowerU_pos
    (p : CM2Params)
    (_ha : 0 < p.a) (hb : 0 < p.b) (_hχ0 : 0 < p.χ₀)
    (_hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1))) :
    0 <
      ((p.a - p.χ₀ * p.μ * Theta_beta (p.β - 1)) / p.b) ^
        (1 / p.α) := by
  have hTheta : 0 < Theta_beta (p.β - 1) :=
    Theta_beta_pos_of_nonneg (by linarith)
  have hden : 0 < p.μ * Theta_beta (p.β - 1) :=
    mul_pos p.hμ hTheta
  have hχmul : p.χ₀ * (p.μ * Theta_beta (p.β - 1)) < p.a := by
    rw [lt_div_iff₀ hden] at hχ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hχ
  have hbase :
      0 < (p.a - p.χ₀ * p.μ * Theta_beta (p.β - 1)) / p.b := by
    apply div_pos
    · nlinarith
    · exact hb
  exact Real.rpow_pos_of_pos hbase _

lemma theorem_2_1_part3_lowerU_pos
    (p : CM2Params)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (_hm : 1 < p.m) (hβ : 1 ≤ p.β) :
    0 <
      min 1 (p.a / (p.b + p.χ₀ * p.μ * Theta_beta (p.β - 1))) ^
        max (1 / (p.m - 1)) (1 / p.α) := by
  have hTheta : 0 < Theta_beta (p.β - 1) :=
    Theta_beta_pos_of_nonneg (by linarith)
  have hden : 0 < p.b + p.χ₀ * p.μ * Theta_beta (p.β - 1) := by
    have hterm : 0 < p.χ₀ * p.μ * Theta_beta (p.β - 1) := by
      exact mul_pos (mul_pos hχ0 p.hμ) hTheta
    linarith
  have hratio : 0 < p.a / (p.b + p.χ₀ * p.μ * Theta_beta (p.β - 1)) :=
    div_pos ha hden
  have hbase :
      0 < min 1 (p.a / (p.b + p.χ₀ * p.μ * Theta_beta (p.β - 1))) :=
    lt_min zero_lt_one hratio
  exact Real.rpow_pos_of_pos hbase _

lemma theorem_2_1_part2_lowerV_pos
    (p : CM2Params)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1))) :
    0 <
      p.ν / p.μ *
        (((p.a - p.χ₀ * p.μ * Theta_beta (p.β - 1)) / p.b) ^
          (1 / p.α)) ^ p.γ := by
  have hU :
      0 <
        ((p.a - p.χ₀ * p.μ * Theta_beta (p.β - 1)) / p.b) ^
          (1 / p.α) :=
    theorem_2_1_part2_lowerU_pos p ha hb hχ0 hm hβ hχ
  exact mul_pos (div_pos p.hν p.hμ) (Real.rpow_pos_of_pos hU _)

lemma theorem_2_1_part3_lowerV_pos
    (p : CM2Params)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : 1 < p.m) (hβ : 1 ≤ p.β) :
    0 <
      p.ν / p.μ *
        (min 1 (p.a / (p.b + p.χ₀ * p.μ * Theta_beta (p.β - 1))) ^
          max (1 / (p.m - 1)) (1 / p.α)) ^ p.γ := by
  have hU :
      0 <
        min 1 (p.a / (p.b + p.χ₀ * p.μ * Theta_beta (p.β - 1))) ^
          max (1 / (p.m - 1)) (1 / p.α) :=
    theorem_2_1_part3_lowerU_pos p ha hb hχ0 hm hβ
  exact mul_pos (div_pos p.hν p.hμ) (Real.rpow_pos_of_pos hU _)

def Theorem_2_1_part4
    (D : BoundedDomainData) (p : CM2Params) (C : Paper3Constants D p) : Prop :=
  p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
    0 < p.χ₀ → p.χ₀ < min (chiBeta p / 2) (Real.sqrt (chiBeta p)) →
      ∀ uStar > 0, ∀ u v : ℝ → D.Point → ℝ,
        PositiveGlobalBoundedSolution D p u v →
        HasInitialMass D u uStar →
          EventuallyLowerBound D v
            (minimalVLowerFormula
              C.gaussianLowerConst p.γ uStar (C.eventualMinimalUBound uStar))

lemma Theorem_2_1_part4.minimal_v_lower_bound
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (h : Theorem_2_1_part4 D p C)
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ0 : 0 < p.χ₀)
    (hχ : p.χ₀ < min (chiBeta p / 2) (Real.sqrt (chiBeta p)))
    {uStar : ℝ} (huStar : 0 < uStar)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hmass : HasInitialMass D u uStar) :
    EventuallyLowerBound D v
      (minimalVLowerFormula
        C.gaussianLowerConst p.γ uStar (C.eventualMinimalUBound uStar)) :=
  h ha hb hm hβ hχ0 hχ uStar huStar u v huv hmass

/-- Paper3 Theorem 2.1: uniform persistence. -/
def Theorem_2_1 (D : BoundedDomainData) (p : CM2Params) (C : Paper3Constants D p) : Prop :=
  Theorem_2_1_part1 D p ∧
    Theorem_2_1_part2 D p ∧
    Theorem_2_1_part3 D p ∧
    Theorem_2_1_part4 D p C

lemma Theorem_2_1.part1
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (h : Theorem_2_1 D p C) :
    Theorem_2_1_part1 D p :=
  h.1

lemma Theorem_2_1.part2
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (h : Theorem_2_1 D p C) :
    Theorem_2_1_part2 D p :=
  h.2.1

lemma Theorem_2_1.part3
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (h : Theorem_2_1 D p C) :
    Theorem_2_1_part3 D p :=
  h.2.2.1

lemma Theorem_2_1.part4
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (h : Theorem_2_1 D p C) :
    Theorem_2_1_part4 D p C :=
  h.2.2.2

lemma Theorem_2_1.persistence
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (h : Theorem_2_1 D p C) (hm : 1 ≤ p.m)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v) :
    ∃ δu > 0, EventuallyLowerBound D u δu ∧
      EventuallyLowerBound D v (p.ν / p.μ * δu ^ p.γ) :=
  h.part1 hm u v huv

lemma Theorem_2_1.part2_positive_lower_bounds
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (h : Theorem_2_1 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v) :
    ∃ δu > 0, ∃ δv > 0,
      EventuallyLowerBound D u δu ∧ EventuallyLowerBound D v δv := by
  let lowerU :=
    ((p.a - p.χ₀ * p.μ * Theta_beta (p.β - 1)) / p.b) ^ (1 / p.α)
  have hbounds :
      EventuallyLowerBound D u lowerU ∧
        EventuallyLowerBound D v (p.ν / p.μ * lowerU ^ p.γ) :=
    h.part2 ha hb hχ0 hm hβ hχ u v huv
  refine ⟨lowerU, ?_, p.ν / p.μ * lowerU ^ p.γ, ?_, hbounds⟩
  · exact theorem_2_1_part2_lowerU_pos p ha hb hχ0 hm hβ hχ
  · exact theorem_2_1_part2_lowerV_pos p ha hb hχ0 hm hβ hχ

lemma Theorem_2_1.part3_positive_lower_bounds
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (h : Theorem_2_1 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : 1 < p.m) (hβ : 1 ≤ p.β)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v) :
    ∃ δu > 0, ∃ δv > 0,
      EventuallyLowerBound D u δu ∧ EventuallyLowerBound D v δv := by
  let lowerU :=
    min 1 (p.a / (p.b + p.χ₀ * p.μ * Theta_beta (p.β - 1))) ^
      max (1 / (p.m - 1)) (1 / p.α)
  have hbounds :
      EventuallyLowerBound D u lowerU ∧
        EventuallyLowerBound D v (p.ν / p.μ * lowerU ^ p.γ) :=
    h.part3 ha hb hχ0 hm hβ u v huv
  refine ⟨lowerU, ?_, p.ν / p.μ * lowerU ^ p.γ, ?_, hbounds⟩
  · exact theorem_2_1_part3_lowerU_pos p ha hb hχ0 hm hβ
  · exact theorem_2_1_part3_lowerV_pos p ha hb hχ0 hm hβ

lemma Theorem_2_1.part4_minimal_v_lower_bound
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (h : Theorem_2_1 D p C)
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ0 : 0 < p.χ₀)
    (hχ : p.χ₀ < min (chiBeta p / 2) (Real.sqrt (chiBeta p)))
    {uStar : ℝ} (huStar : 0 < uStar)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hmass : HasInitialMass D u uStar) :
    EventuallyLowerBound D v
      (minimalVLowerFormula
        C.gaussianLowerConst p.γ uStar (C.eventualMinimalUBound uStar)) :=
  h.part4 ha hb hm hβ hχ0 hχ uStar huStar u v huv hmass

lemma Theorem_2_1.part4_minimal_v_positive_lower_bound
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (h : Theorem_2_1 D p C)
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ0 : 0 < p.χ₀)
    (hχ : p.χ₀ < min (chiBeta p / 2) (Real.sqrt (chiBeta p)))
    {uStar : ℝ} (huStar : 0 < uStar)
    (hUpper : 0 < C.eventualMinimalUBound uStar)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hmass : HasInitialMass D u uStar) :
    ∃ δv > 0, EventuallyLowerBound D v δv := by
  let δv :=
    minimalVLowerFormula
      C.gaussianLowerConst p.γ uStar (C.eventualMinimalUBound uStar)
  exact
    ⟨δv, C.minimalVLower_pos huStar hUpper,
      h.part4_minimal_v_lower_bound ha hb hm hβ hχ0 hχ huStar huv hmass⟩

/-- Paper3 Theorem 2.2: linear stability/instability and local exponential stability. -/
def Theorem_2_2
    (D : BoundedDomainData) (p : CM2Params) (S : SpectralData)
    (N : StabilityNorms D) (C : Paper3Constants D p) : Prop :=
  (∀ (ha : 0 < p.a) (hb : 0 < p.b),
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    p.χ₀ < C.chiCritical eq.1 →
      LinearlyStable S p eq.1 eq.2 ∧
      ∃ δ > 0, ∃ A > 0, ∃ rate > 0,
        ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
          SupCloseToConstant D u₀ eq.1 δ →
            ∃ u v : ℝ → D.Point → ℝ,
              IsPaper2GlobalClassicalSolution D p u v ∧
              InitialTrace D u₀ u ∧
              ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate) ∧
  (∀ (ha : 0 < p.a) (hb : 0 < p.b),
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    C.chiCritical eq.1 < p.χ₀ →
      LinearlyUnstable S p eq.1 eq.2) ∧
  (p.a = 0 → p.b = 0 →
    ∀ uStar > 0,
      let eq := minimalEquilibrium p uStar
      p.χ₀ < C.chiCritical uStar →
        LinearlyStable S p eq.1 eq.2 ∧
        ∃ δ > 0, ∃ A > 0, ∃ rate > 0,
          ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
            SupCloseToConstant D u₀ eq.1 δ →
            D.integral u₀ = D.volume * uStar →
              ∃ u v : ℝ → D.Point → ℝ,
                IsPaper2GlobalClassicalSolution D p u v ∧
                InitialTrace D u₀ u ∧
                ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate) ∧
  (p.a = 0 → p.b = 0 →
    ∀ uStar > 0,
      let eq := minimalEquilibrium p uStar
      C.chiCritical uStar < p.χ₀ →
        LinearlyUnstable S p eq.1 eq.2)

/-- Direct linear-stability branch of Paper3 Theorem 2.2 at nonpositive
sensitivity.  This proves only the spectral linear-stability conclusions; the
local exponential stability assertions still belong to the analytic stability
package. -/
def Theorem_2_2_linear_stability_chi_nonpos_branch : Prop :=
  ∀ S : SpectralData, ∀ p : CM2Params,
    HasNeumannSpectrum S → p.χ₀ ≤ 0 →
      (∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        LinearlyStable S p eq.1 eq.2) ∧
      (p.a = 0 → p.b = 0 →
        ∀ uStar > 0,
          let eq := minimalEquilibrium p uStar
          LinearlyStable S p eq.1 eq.2)

lemma Theorem_2_2_linear_stability_chi_nonpos_branch_proved :
    Theorem_2_2_linear_stability_chi_nonpos_branch := by
  intro S p H hχ
  refine ⟨?_, ?_⟩
  · intro ha hb
    exact positiveEquilibrium_linearlyStable_of_chi_nonpos_neumann
      S p H hχ ha hb
  · intro ha _hb uStar huStar
    exact minimalEquilibrium_linearlyStable_of_chi_nonpos_a_eq_zero_neumann
      S p H hχ ha huStar

/-- Direct theorem-shaped version of the nonpositive-sensitivity linear
stability branch of Paper3 Theorem 2.2.  This avoids routing the result
through a theorem-shaped `Prop` wrapper. -/
theorem Theorem_2_2_linear_stability_chi_nonpos_branch_direct
    (S : SpectralData) (p : CM2Params)
    (H : HasNeumannSpectrum S) (hχ : p.χ₀ ≤ 0) :
    (∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      LinearlyStable S p eq.1 eq.2) ∧
    (p.a = 0 → p.b = 0 →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        LinearlyStable S p eq.1 eq.2) := by
  refine ⟨?_, ?_⟩
  · intro ha hb
    exact positiveEquilibrium_linearlyStable_of_chi_nonpos_neumann
      S p H hχ ha hb
  · intro ha _hb uStar huStar
    exact minimalEquilibrium_linearlyStable_of_chi_nonpos_a_eq_zero_neumann
      S p H hχ ha huStar

lemma Theorem_2_2_linear_stability_chi_nonpos_unitInterval
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) :
    (∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2) ∧
    (p.a = 0 → p.b = 0 →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2) := by
  refine ⟨?_, ?_⟩
  · intro ha hb
    exact unitInterval_positiveEquilibrium_linearlyStable_of_chi_nonpos
      p hχ ha hb
  · intro ha _hb uStar huStar
    exact unitInterval_minimalEquilibrium_linearlyStable_of_chi_nonpos
      p hχ ha huStar

/-- Direct spectral-threshold branch of Paper3 Theorem 2.2.  The threshold is
the paper's explicit nonzero-mode infimum `paperCriticalSensitivity`; this
closes the linear stable/unstable part without using
`Paper3Constants.linearStabilityInstability`. -/
def Theorem_2_2_linear_threshold_branch : Prop :=
  ∀ S : SpectralData, ∀ p : CM2Params,
    HasNeumannSpectrum S →
      (∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        (p.χ₀ < paperCriticalSensitivity S p eq.1 eq.2 →
          LinearlyStable S p eq.1 eq.2) ∧
        (paperCriticalSensitivity S p eq.1 eq.2 < p.χ₀ →
          LinearlyUnstable S p eq.1 eq.2)) ∧
      (p.a = 0 → p.b = 0 →
        ∀ uStar > 0,
          let eq := minimalEquilibrium p uStar
          (p.χ₀ < paperCriticalSensitivity S p eq.1 eq.2 →
            LinearlyStable S p eq.1 eq.2) ∧
          (paperCriticalSensitivity S p eq.1 eq.2 < p.χ₀ →
            LinearlyUnstable S p eq.1 eq.2))

lemma Theorem_2_2_linear_threshold_branch_proved :
    Theorem_2_2_linear_threshold_branch := by
  intro S p H
  refine ⟨?_, ?_⟩
  · intro ha hb
    exact
      ⟨positiveEquilibrium_linearlyStable_of_chi_lt_paperCriticalSensitivity_neumann
          S p H ha hb,
        positiveEquilibrium_linearlyUnstable_of_paperCriticalSensitivity_lt_chi_neumann
          S p H ha hb⟩
  · intro _ha _hb uStar huStar
    exact
      ⟨minimalEquilibrium_linearlyStable_of_chi_lt_paperCriticalSensitivity_neumann
          S p H huStar,
        minimalEquilibrium_linearlyUnstable_of_paperCriticalSensitivity_lt_chi_neumann
          S p H huStar⟩

lemma Theorem_2_2_linear_threshold_unitInterval
    (p : CM2Params) :
    (∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      (p.χ₀ < paperCriticalSensitivity unitIntervalNeumannSpectrum p eq.1 eq.2 →
        LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2) ∧
      (paperCriticalSensitivity unitIntervalNeumannSpectrum p eq.1 eq.2 < p.χ₀ →
        LinearlyUnstable unitIntervalNeumannSpectrum p eq.1 eq.2)) ∧
    (p.a = 0 → p.b = 0 →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        (p.χ₀ <
            paperCriticalSensitivity unitIntervalNeumannSpectrum p eq.1 eq.2 →
          LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2) ∧
        (paperCriticalSensitivity unitIntervalNeumannSpectrum p eq.1 eq.2 <
            p.χ₀ →
          LinearlyUnstable unitIntervalNeumannSpectrum p eq.1 eq.2)) := by
  refine ⟨?_, ?_⟩
  · intro ha hb
    exact
      ⟨unitInterval_positiveEquilibrium_linearlyStable_of_chi_lt_critical
          p ha hb,
        unitInterval_positiveEquilibrium_linearlyUnstable_of_critical_lt_chi
          p ha hb⟩
  · intro _ha _hb uStar huStar
    exact
      ⟨unitInterval_minimalEquilibrium_linearlyStable_of_chi_lt_critical
          p huStar,
        unitInterval_minimalEquilibrium_linearlyUnstable_of_critical_lt_chi
          p huStar⟩

/-- Direct mode-one instability branch of Paper3 Theorem 2.2.  This is weaker
than the full `paperCriticalSensitivity < χ₀` branch, but it uses one explicit
paper formula value and does not touch `Paper3Constants`. -/
def Theorem_2_2_linear_mode_one_instability_branch : Prop :=
  ∀ S : SpectralData, ∀ p : CM2Params,
    HasNeumannSpectrum S →
      (∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        sigmaCriticalChiPaperFormula p eq.1 eq.2 (S.eigenvalue 1) < p.χ₀ →
          LinearlyUnstable S p eq.1 eq.2) ∧
      (p.a = 0 → p.b = 0 →
        ∀ uStar > 0,
          let eq := minimalEquilibrium p uStar
          sigmaCriticalChiPaperFormula p eq.1 eq.2 (S.eigenvalue 1) < p.χ₀ →
            LinearlyUnstable S p eq.1 eq.2)

lemma Theorem_2_2_linear_mode_one_instability_branch_proved :
    Theorem_2_2_linear_mode_one_instability_branch := by
  intro S p H
  refine ⟨?_, ?_⟩
  · intro ha hb
    exact
      positiveEquilibrium_linearlyUnstable_of_mode_one_paperFormula_lt_chi_neumann
        S p H ha hb
  · intro _ha _hb uStar huStar
    exact
      minimalEquilibrium_linearlyUnstable_of_mode_one_paperFormula_lt_chi_neumann
        S p H huStar

lemma Theorem_2_2_linear_mode_one_instability_unitInterval
    (p : CM2Params) :
    (∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      sigmaCriticalChiPaperFormula p eq.1 eq.2 (Real.pi ^ 2) < p.χ₀ →
        LinearlyUnstable unitIntervalNeumannSpectrum p eq.1 eq.2) ∧
    (p.a = 0 → p.b = 0 →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        sigmaCriticalChiPaperFormula p eq.1 eq.2 (Real.pi ^ 2) < p.χ₀ →
          LinearlyUnstable unitIntervalNeumannSpectrum p eq.1 eq.2) := by
  refine ⟨?_, ?_⟩
  · intro ha hb
    exact unitInterval_positiveEquilibrium_linearlyUnstable_of_first_mode_formula_lt_chi
      p ha hb
  · intro _ha _hb uStar huStar
    exact unitInterval_minimalEquilibrium_linearlyUnstable_of_first_mode_formula_lt_chi
      p huStar

/-- Direct linear part of Paper3 Theorem 2.2 using the constants package's
critical-sensitivity field, once that field is identified with the paper's
spectral infimum.  This intentionally does not include local exponential
stability. -/
def Theorem_2_2_linear_critical_spectrum_branch : Prop :=
  ∀ (D : BoundedDomainData) (S : SpectralData) (p : CM2Params)
    (C : Paper3Constants D p),
    HasNeumannSpectrum S → Paper3ConstantsUsesCriticalSpectrum S p C →
      (∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        (p.χ₀ < C.chiCritical eq.1 →
          LinearlyStable S p eq.1 eq.2) ∧
        (C.chiCritical eq.1 < p.χ₀ →
          LinearlyUnstable S p eq.1 eq.2)) ∧
      (p.a = 0 → p.b = 0 →
        ∀ uStar > 0,
          let eq := minimalEquilibrium p uStar
          (p.χ₀ < C.chiCritical uStar →
            LinearlyStable S p eq.1 eq.2) ∧
          (C.chiCritical uStar < p.χ₀ →
            LinearlyUnstable S p eq.1 eq.2))

lemma Theorem_2_2_linear_critical_spectrum_branch_proved :
    Theorem_2_2_linear_critical_spectrum_branch := by
  intro D S p C H hC
  refine ⟨?_, ?_⟩
  · intro ha hb
    exact
      ⟨hC.positiveEquilibrium_linearlyStable H ha hb,
        hC.positiveEquilibrium_linearlyUnstable H ha hb⟩
  · intro _ha _hb uStar huStar
    exact
      ⟨hC.minimalEquilibrium_linearlyStable H huStar,
        hC.minimalEquilibrium_linearlyUnstable H huStar⟩

lemma Theorem_2_2.nonminimal_stable
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Theorem_2_2 D p S N C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ : p.χ₀ < C.chiCritical (positiveEquilibrium p ⟨ha, hb⟩).1) :
    LinearlyStable S p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  exact (h.1 ha hb hχ).1

lemma Theorem_2_2.nonminimal_local_exponential
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Theorem_2_2 D p S N C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ : p.χ₀ < C.chiCritical (positiveEquilibrium p ⟨ha, hb⟩).1) :
    LocallyExponentiallyStableFromSup D p N
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  exact (h.1 ha hb hχ).2

lemma Theorem_2_2.nonminimal_stability_conclusion
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Theorem_2_2 D p S N C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ : p.χ₀ < C.chiCritical (positiveEquilibrium p ⟨ha, hb⟩).1) :
    LinearlyStable S p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 ∧
    LocallyExponentiallyStableFromSup D p N
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  h.1 ha hb hχ

lemma Theorem_2_2.nonminimal_stability_conclusion_of_chi_lt_paperCriticalSensitivity
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Theorem_2_2 D p S N C)
    (hC : Paper3ConstantsUsesCriticalSpectrum S p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity S p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2) :
    LinearlyStable S p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 ∧
    LocallyExponentiallyStableFromSup D p N
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  exact h.nonminimal_stability_conclusion ha hb
    (by
      rwa [hC.chiCritical_positiveEquilibrium ha hb])

lemma Theorem_2_2.nonminimal_exponential_convergence
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Theorem_2_2 D p S N C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ : p.χ₀ < C.chiCritical (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ∃ δ > 0,
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        SupCloseToConstant D u₀ (positiveEquilibrium p ⟨ha, hb⟩).1 δ →
          ∃ u v : ℝ → D.Point → ℝ,
            IsPaper2GlobalClassicalSolution D p u v ∧
            InitialTrace D u₀ u ∧
            ExponentialC1Convergence D N u v
              (positiveEquilibrium p ⟨ha, hb⟩).1
              (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  (h.nonminimal_local_exponential ha hb hχ).exponential_convergence

lemma Theorem_2_2.nonminimal_exponential_convergence_of_chi_lt_paperCriticalSensitivity
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Theorem_2_2 D p S N C)
    (hC : Paper3ConstantsUsesCriticalSpectrum S p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity S p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2) :
    ∃ δ > 0,
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        SupCloseToConstant D u₀ (positiveEquilibrium p ⟨ha, hb⟩).1 δ →
          ∃ u v : ℝ → D.Point → ℝ,
            IsPaper2GlobalClassicalSolution D p u v ∧
            InitialTrace D u₀ u ∧
            ExponentialC1Convergence D N u v
              (positiveEquilibrium p ⟨ha, hb⟩).1
              (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  exact h.nonminimal_exponential_convergence ha hb
    (by
      rwa [hC.chiCritical_positiveEquilibrium ha hb])

lemma Theorem_2_2.nonminimal_unstable
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Theorem_2_2 D p S N C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ : C.chiCritical (positiveEquilibrium p ⟨ha, hb⟩).1 < p.χ₀) :
    LinearlyUnstable S p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  exact h.2.1 ha hb hχ

lemma Theorem_2_2.nonminimal_unstable_of_paperCriticalSensitivity_lt_chi
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Theorem_2_2 D p S N C)
    (hC : Paper3ConstantsUsesCriticalSpectrum S p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ :
      paperCriticalSensitivity S p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 < p.χ₀) :
    LinearlyUnstable S p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  exact h.nonminimal_unstable ha hb
    (by
      rwa [hC.chiCritical_positiveEquilibrium ha hb])

lemma Theorem_2_2.minimal_stable
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Theorem_2_2 D p S N C)
    (ha : p.a = 0) (hb : p.b = 0) {uStar : ℝ} (huStar : 0 < uStar)
    (hχ : p.χ₀ < C.chiCritical uStar) :
    LinearlyStable S p
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 := by
  exact (h.2.2.1 ha hb uStar huStar hχ).1

lemma Theorem_2_2.minimal_local_exponential
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Theorem_2_2 D p S N C)
    (ha : p.a = 0) (hb : p.b = 0) {uStar : ℝ} (huStar : 0 < uStar)
    (hχ : p.χ₀ < C.chiCritical uStar) :
    MassConstrainedLocallyExponentiallyStableFromSup D p N
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 := by
  exact (h.2.2.1 ha hb uStar huStar hχ).2

lemma Theorem_2_2.minimal_stability_conclusion
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Theorem_2_2 D p S N C)
    (ha : p.a = 0) (hb : p.b = 0) {uStar : ℝ} (huStar : 0 < uStar)
    (hχ : p.χ₀ < C.chiCritical uStar) :
    LinearlyStable S p
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 ∧
    MassConstrainedLocallyExponentiallyStableFromSup D p N
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 :=
  h.2.2.1 ha hb uStar huStar hχ

lemma Theorem_2_2.minimal_stability_conclusion_of_chi_lt_paperCriticalSensitivity
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Theorem_2_2 D p S N C)
    (hC : Paper3ConstantsUsesCriticalSpectrum S p C)
    (ha : p.a = 0) (hb : p.b = 0) {uStar : ℝ} (huStar : 0 < uStar)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity S p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2) :
    LinearlyStable S p
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 ∧
    MassConstrainedLocallyExponentiallyStableFromSup D p N
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 := by
  exact h.minimal_stability_conclusion ha hb huStar
    (by
      rwa [hC.chiCritical_minimalEquilibrium huStar])

lemma Theorem_2_2.minimal_exponential_convergence
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Theorem_2_2 D p S N C)
    (ha : p.a = 0) (hb : p.b = 0) {uStar : ℝ} (huStar : 0 < uStar)
    (hχ : p.χ₀ < C.chiCritical uStar) :
    ∃ δ > 0,
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        SupCloseToConstant D u₀ (minimalEquilibrium p uStar).1 δ →
        D.integral u₀ = D.volume * uStar →
          ∃ u v : ℝ → D.Point → ℝ,
            IsPaper2GlobalClassicalSolution D p u v ∧
            InitialTrace D u₀ u ∧
            ExponentialC1Convergence D N u v
              (minimalEquilibrium p uStar).1
              (minimalEquilibrium p uStar).2 :=
  (h.minimal_local_exponential ha hb huStar hχ).exponential_convergence

lemma Theorem_2_2.minimal_exponential_convergence_of_chi_lt_paperCriticalSensitivity
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Theorem_2_2 D p S N C)
    (hC : Paper3ConstantsUsesCriticalSpectrum S p C)
    (ha : p.a = 0) (hb : p.b = 0) {uStar : ℝ} (huStar : 0 < uStar)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity S p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2) :
    ∃ δ > 0,
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        SupCloseToConstant D u₀ (minimalEquilibrium p uStar).1 δ →
        D.integral u₀ = D.volume * uStar →
          ∃ u v : ℝ → D.Point → ℝ,
            IsPaper2GlobalClassicalSolution D p u v ∧
            InitialTrace D u₀ u ∧
            ExponentialC1Convergence D N u v
              (minimalEquilibrium p uStar).1
              (minimalEquilibrium p uStar).2 := by
  exact h.minimal_exponential_convergence ha hb huStar
    (by
      rwa [hC.chiCritical_minimalEquilibrium huStar])

lemma Theorem_2_2.minimal_unstable
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Theorem_2_2 D p S N C)
    (ha : p.a = 0) (hb : p.b = 0) {uStar : ℝ} (huStar : 0 < uStar)
    (hχ : C.chiCritical uStar < p.χ₀) :
    LinearlyUnstable S p
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 := by
  exact h.2.2.2 ha hb uStar huStar hχ

lemma Theorem_2_2.minimal_unstable_of_paperCriticalSensitivity_lt_chi
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Theorem_2_2 D p S N C)
    (hC : Paper3ConstantsUsesCriticalSpectrum S p C)
    (ha : p.a = 0) (hb : p.b = 0) {uStar : ℝ} (huStar : 0 < uStar)
    (hχ :
      paperCriticalSensitivity S p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 < p.χ₀) :
    LinearlyUnstable S p
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 := by
  exact h.minimal_unstable ha hb huStar
    (by
      rwa [hC.chiCritical_minimalEquilibrium huStar])

/-- Paper3 Theorem 2.3: global stability for negative sensitivity. -/
def Theorem_2_3
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D) : Prop :=
  p.χ₀ ≤ 0 → 1 ≤ p.m →
    (∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      GloballyAsymptoticallyStableNonminimal D p eq.1 eq.2 ∧
      ∃ A > 0, ∃ rate > 0,
        ∀ u v : ℝ → D.Point → ℝ,
          PositiveGlobalBoundedSolution D p u v →
            ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate) ∧
    (p.a = 0 → p.b = 0 →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        GloballyAsymptoticallyStableMinimal D p eq.1 eq.2 ∧
        ∃ A > 0, ∃ rate > 0,
          ∀ u v : ℝ → D.Point → ℝ,
            PositiveGlobalBoundedSolution D p u v →
            HasInitialMass D u uStar →
              ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate)

lemma Theorem_2_3.nonminimal_stability
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    (h : Theorem_2_3 D p N)
    (hχ : p.χ₀ ≤ 0) (hm : 1 ≤ p.m) (ha : 0 < p.a) (hb : 0 < p.b) :
    GloballyAsymptoticallyStableNonminimal D p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  exact ((h hχ hm).1 ha hb).1

lemma Theorem_2_3.nonminimal_exponential
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    (h : Theorem_2_3 D p N)
    (hχ : p.χ₀ ≤ 0) (hm : 1 ≤ p.m) (ha : 0 < p.a) (hb : 0 < p.b) :
    ∃ A > 0, ∃ rate > 0,
      ∀ u v : ℝ → D.Point → ℝ,
        PositiveGlobalBoundedSolution D p u v →
          ExponentialC1ConvergenceWith D N u v
            (positiveEquilibrium p ⟨ha, hb⟩).1
            (positiveEquilibrium p ⟨ha, hb⟩).2 A rate := by
  exact ((h hχ hm).1 ha hb).2

lemma Theorem_2_3.nonminimal_exponential_convergence
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    (h : Theorem_2_3 D p N)
    (hχ : p.χ₀ ≤ 0) (hm : 1 ≤ p.m) (ha : 0 < p.a) (hb : 0 < p.b)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v) :
    ExponentialC1Convergence D N u v
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  rcases h.nonminimal_exponential hχ hm ha hb with
    ⟨A, hA, rate, hrate, hexp⟩
  exact ExponentialC1ConvergenceWith.exists hA hrate (hexp u v huv)

lemma Theorem_2_3.minimal_stability
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    (h : Theorem_2_3 D p N)
    (hχ : p.χ₀ ≤ 0) (hm : 1 ≤ p.m) (ha : p.a = 0) (hb : p.b = 0)
    {uStar : ℝ} (huStar : 0 < uStar) :
    GloballyAsymptoticallyStableMinimal D p
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 := by
  exact ((h hχ hm).2 ha hb uStar huStar).1

lemma Theorem_2_3.minimal_exponential
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    (h : Theorem_2_3 D p N)
    (hχ : p.χ₀ ≤ 0) (hm : 1 ≤ p.m) (ha : p.a = 0) (hb : p.b = 0)
    {uStar : ℝ} (huStar : 0 < uStar) :
    ∃ A > 0, ∃ rate > 0,
      ∀ u v : ℝ → D.Point → ℝ,
        PositiveGlobalBoundedSolution D p u v →
        HasInitialMass D u uStar →
          ExponentialC1ConvergenceWith D N u v
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2 A rate := by
  exact ((h hχ hm).2 ha hb uStar huStar).2

lemma Theorem_2_3.minimal_exponential_convergence
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    (h : Theorem_2_3 D p N)
    (hχ : p.χ₀ ≤ 0) (hm : 1 ≤ p.m) (ha : p.a = 0) (hb : p.b = 0)
    {uStar : ℝ} (huStar : 0 < uStar)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hmass : HasInitialMass D u uStar) :
    ExponentialC1Convergence D N u v
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 := by
  rcases h.minimal_exponential hχ hm ha hb huStar with
    ⟨A, hA, rate, hrate, hexp⟩
  exact ExponentialC1ConvergenceWith.exists hA hrate (hexp u v huv hmass)

/-- Paper3 Theorem 2.4: global stability under relatively strong logistic source. -/
def Theorem_2_4
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (C : Paper3Constants D p) : Prop :=
  0 < p.a → 0 < p.b → 0 ≤ p.β → 0 < p.α → 0 < p.γ →
    ∀ (ha : 0 < p.a) (hb : 0 < p.b),
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    NonminimalGlobalStabilityCondition D p C eq.1 →
      GloballyAsymptoticallyStableNonminimal D p eq.1 eq.2 ∧
      ∃ A > 0, ∃ rate > 0,
        ∀ u v : ℝ → D.Point → ℝ,
          PositiveGlobalBoundedSolution D p u v →
            ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate

lemma Theorem_2_4.stability
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {C : Paper3Constants D p}
    (h : Theorem_2_4 D p N C)
    (ha0 : 0 < p.a) (hb0 : 0 < p.b) (hβ : 0 ≤ p.β)
    (hα : 0 < p.α) (hγ : 0 < p.γ)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hcond : NonminimalGlobalStabilityCondition D p C
      (positiveEquilibrium p ⟨ha, hb⟩).1) :
    GloballyAsymptoticallyStableNonminimal D p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  exact (h ha0 hb0 hβ hα hγ ha hb hcond).1

lemma Theorem_2_4.exponential
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {C : Paper3Constants D p}
    (h : Theorem_2_4 D p N C)
    (ha0 : 0 < p.a) (hb0 : 0 < p.b) (hβ : 0 ≤ p.β)
    (hα : 0 < p.α) (hγ : 0 < p.γ)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hcond : NonminimalGlobalStabilityCondition D p C
      (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ∃ A > 0, ∃ rate > 0,
      ∀ u v : ℝ → D.Point → ℝ,
        PositiveGlobalBoundedSolution D p u v →
          ExponentialC1ConvergenceWith D N u v
            (positiveEquilibrium p ⟨ha, hb⟩).1
            (positiveEquilibrium p ⟨ha, hb⟩).2 A rate := by
  exact (h ha0 hb0 hβ hα hγ ha hb hcond).2

lemma Theorem_2_4.exponential_convergence
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {C : Paper3Constants D p}
    (h : Theorem_2_4 D p N C)
    (ha0 : 0 < p.a) (hb0 : 0 < p.b) (hβ : 0 ≤ p.β)
    (hα : 0 < p.α) (hγ : 0 < p.γ)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hcond : NonminimalGlobalStabilityCondition D p C
      (positiveEquilibrium p ⟨ha, hb⟩).1)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v) :
    ExponentialC1Convergence D N u v
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  rcases h.exponential ha0 hb0 hβ hα hγ ha hb hcond with
    ⟨A, hA, rate, hrate, hexp⟩
  exact ExponentialC1ConvergenceWith.exists hA hrate (hexp u v huv)

lemma Theorem_2_4.stability_of_chiStrong1
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {C : Paper3Constants D p}
    (h : Theorem_2_4 D p N C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hβ : 0 ≤ p.β)
    (hm : 1 ≤ p.m) (hαγ : 2 * p.γ ≤ p.α + 1)
    (hχ0 : 0 < p.χ₀)
    (hχ : p.χ₀ < C.chiStrong1 (positiveEquilibrium p ⟨ha, hb⟩).1) :
    GloballyAsymptoticallyStableNonminimal D p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  h.stability ha hb hβ p.hα p.hγ ha hb
    (NonminimalGlobalStabilityCondition.of_chiStrong1 hm hαγ hχ0 hχ)

lemma Theorem_2_4.exponential_of_chiStrong1
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {C : Paper3Constants D p}
    (h : Theorem_2_4 D p N C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hβ : 0 ≤ p.β)
    (hm : 1 ≤ p.m) (hαγ : 2 * p.γ ≤ p.α + 1)
    (hχ0 : 0 < p.χ₀)
    (hχ : p.χ₀ < C.chiStrong1 (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ∃ A > 0, ∃ rate > 0,
      ∀ u v : ℝ → D.Point → ℝ,
        PositiveGlobalBoundedSolution D p u v →
          ExponentialC1ConvergenceWith D N u v
            (positiveEquilibrium p ⟨ha, hb⟩).1
            (positiveEquilibrium p ⟨ha, hb⟩).2 A rate :=
  h.exponential ha hb hβ p.hα p.hγ ha hb
    (NonminimalGlobalStabilityCondition.of_chiStrong1 hm hαγ hχ0 hχ)

lemma Theorem_2_4.exponential_convergence_of_chiStrong1
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {C : Paper3Constants D p}
    (h : Theorem_2_4 D p N C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hβ : 0 ≤ p.β)
    (hm : 1 ≤ p.m) (hαγ : 2 * p.γ ≤ p.α + 1)
    (hχ0 : 0 < p.χ₀)
    (hχ : p.χ₀ < C.chiStrong1 (positiveEquilibrium p ⟨ha, hb⟩).1)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v) :
    ExponentialC1Convergence D N u v
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  h.exponential_convergence ha hb hβ p.hα p.hγ ha hb
    (NonminimalGlobalStabilityCondition.of_chiStrong1 hm hαγ hχ0 hχ) huv

lemma Theorem_2_4.stability_of_chiStrong2
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {C : Paper3Constants D p}
    (h : Theorem_2_4 D p N C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m) (hβ : 1 ≤ p.β)
    (hαγ : 2 * p.γ ≤ p.α + 1)
    (hχ0 : 0 < p.χ₀)
    (hχ : p.χ₀ < C.chiStrong2 (positiveEquilibrium p ⟨ha, hb⟩).1) :
    GloballyAsymptoticallyStableNonminimal D p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  h.stability ha hb (by linarith : 0 ≤ p.β) p.hα p.hγ ha hb
    (NonminimalGlobalStabilityCondition.of_chiStrong2 hm hβ hαγ hχ0 hχ)

lemma Theorem_2_4.exponential_of_chiStrong2
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {C : Paper3Constants D p}
    (h : Theorem_2_4 D p N C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m) (hβ : 1 ≤ p.β)
    (hαγ : 2 * p.γ ≤ p.α + 1)
    (hχ0 : 0 < p.χ₀)
    (hχ : p.χ₀ < C.chiStrong2 (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ∃ A > 0, ∃ rate > 0,
      ∀ u v : ℝ → D.Point → ℝ,
        PositiveGlobalBoundedSolution D p u v →
          ExponentialC1ConvergenceWith D N u v
            (positiveEquilibrium p ⟨ha, hb⟩).1
            (positiveEquilibrium p ⟨ha, hb⟩).2 A rate :=
  h.exponential ha hb (by linarith : 0 ≤ p.β) p.hα p.hγ ha hb
    (NonminimalGlobalStabilityCondition.of_chiStrong2 hm hβ hαγ hχ0 hχ)

lemma Theorem_2_4.exponential_convergence_of_chiStrong2
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {C : Paper3Constants D p}
    (h : Theorem_2_4 D p N C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m) (hβ : 1 ≤ p.β)
    (hαγ : 2 * p.γ ≤ p.α + 1)
    (hχ0 : 0 < p.χ₀)
    (hχ : p.χ₀ < C.chiStrong2 (positiveEquilibrium p ⟨ha, hb⟩).1)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v) :
    ExponentialC1Convergence D N u v
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  h.exponential_convergence ha hb (by linarith : 0 ≤ p.β) p.hα p.hγ ha hb
    (NonminimalGlobalStabilityCondition.of_chiStrong2 hm hβ hαγ hχ0 hχ) huv

lemma Theorem_2_4.stability_of_chiStrong3
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {C : Paper3Constants D p}
    (h : Theorem_2_4 D p N C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hβ : 0 ≤ p.β)
    (hm : 1 ≤ p.m) (hγ : 1 ≤ p.γ)
    (hαγ :
      p.m + p.γ + (if p.β = 0 then 0 else p.γ) ≤ p.α + 1)
    (hχ : p.χ₀ < C.chiStrong3 (positiveEquilibrium p ⟨ha, hb⟩).1) :
    GloballyAsymptoticallyStableNonminimal D p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  h.stability ha hb hβ p.hα p.hγ ha hb
    (NonminimalGlobalStabilityCondition.of_chiStrong3 hm hγ hαγ hχ)

lemma Theorem_2_4.exponential_of_chiStrong3
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {C : Paper3Constants D p}
    (h : Theorem_2_4 D p N C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hβ : 0 ≤ p.β)
    (hm : 1 ≤ p.m) (hγ : 1 ≤ p.γ)
    (hαγ :
      p.m + p.γ + (if p.β = 0 then 0 else p.γ) ≤ p.α + 1)
    (hχ : p.χ₀ < C.chiStrong3 (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ∃ A > 0, ∃ rate > 0,
      ∀ u v : ℝ → D.Point → ℝ,
        PositiveGlobalBoundedSolution D p u v →
          ExponentialC1ConvergenceWith D N u v
            (positiveEquilibrium p ⟨ha, hb⟩).1
            (positiveEquilibrium p ⟨ha, hb⟩).2 A rate :=
  h.exponential ha hb hβ p.hα p.hγ ha hb
    (NonminimalGlobalStabilityCondition.of_chiStrong3 hm hγ hαγ hχ)

lemma Theorem_2_4.exponential_convergence_of_chiStrong3
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {C : Paper3Constants D p}
    (h : Theorem_2_4 D p N C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hβ : 0 ≤ p.β)
    (hm : 1 ≤ p.m) (hγ : 1 ≤ p.γ)
    (hαγ :
      p.m + p.γ + (if p.β = 0 then 0 else p.γ) ≤ p.α + 1)
    (hχ : p.χ₀ < C.chiStrong3 (positiveEquilibrium p ⟨ha, hb⟩).1)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v) :
    ExponentialC1Convergence D N u v
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  h.exponential_convergence ha hb hβ p.hα p.hγ ha hb
    (NonminimalGlobalStabilityCondition.of_chiStrong3 hm hγ hαγ hχ) huv

lemma Theorem_2_4.stability_of_chiStrong4
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {C : Paper3Constants D p}
    (h : Theorem_2_4 D p N C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m) (hβ : 1 ≤ p.β) (hγ : 1 ≤ p.γ)
    (hαγ : p.m + 2 * p.γ ≤ p.α + 1)
    (hχ : p.χ₀ < C.chiStrong4 (positiveEquilibrium p ⟨ha, hb⟩).1) :
    GloballyAsymptoticallyStableNonminimal D p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  h.stability ha hb (by linarith : 0 ≤ p.β) p.hα p.hγ ha hb
    (NonminimalGlobalStabilityCondition.of_chiStrong4 hm hβ hγ hαγ hχ)

lemma Theorem_2_4.exponential_of_chiStrong4
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {C : Paper3Constants D p}
    (h : Theorem_2_4 D p N C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m) (hβ : 1 ≤ p.β) (hγ : 1 ≤ p.γ)
    (hαγ : p.m + 2 * p.γ ≤ p.α + 1)
    (hχ : p.χ₀ < C.chiStrong4 (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ∃ A > 0, ∃ rate > 0,
      ∀ u v : ℝ → D.Point → ℝ,
        PositiveGlobalBoundedSolution D p u v →
          ExponentialC1ConvergenceWith D N u v
            (positiveEquilibrium p ⟨ha, hb⟩).1
            (positiveEquilibrium p ⟨ha, hb⟩).2 A rate :=
  h.exponential ha hb (by linarith : 0 ≤ p.β) p.hα p.hγ ha hb
    (NonminimalGlobalStabilityCondition.of_chiStrong4 hm hβ hγ hαγ hχ)

lemma Theorem_2_4.exponential_convergence_of_chiStrong4
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {C : Paper3Constants D p}
    (h : Theorem_2_4 D p N C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m) (hβ : 1 ≤ p.β) (hγ : 1 ≤ p.γ)
    (hαγ : p.m + 2 * p.γ ≤ p.α + 1)
    (hχ : p.χ₀ < C.chiStrong4 (positiveEquilibrium p ⟨ha, hb⟩).1)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v) :
    ExponentialC1Convergence D N u v
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  h.exponential_convergence ha hb (by linarith : 0 ≤ p.β) p.hα p.hγ ha hb
    (NonminimalGlobalStabilityCondition.of_chiStrong4 hm hβ hγ hαγ hχ) huv

/-- Paper3 Theorem 2.5: global stability in the minimal model. -/
def Theorem_2_5
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (C : Paper3Constants D p) : Prop :=
  p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
    ∀ uStar > 0,
      let eq := minimalEquilibrium p uStar
      MinimalGlobalStabilityCondition D p C uStar →
        GloballyAsymptoticallyStableMinimal D p eq.1 eq.2 ∧
        ∃ A > 0, ∃ rate > 0,
          ∀ u v : ℝ → D.Point → ℝ,
            PositiveGlobalBoundedSolution D p u v →
            HasInitialMass D u uStar →
              ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate

lemma Theorem_2_5.stability
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {C : Paper3Constants D p}
    (h : Theorem_2_5 D p N C)
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hcond : MinimalGlobalStabilityCondition D p C uStar) :
    GloballyAsymptoticallyStableMinimal D p
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 := by
  exact (h ha hb hm hβ uStar huStar hcond).1

lemma Theorem_2_5.exponential
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {C : Paper3Constants D p}
    (h : Theorem_2_5 D p N C)
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hcond : MinimalGlobalStabilityCondition D p C uStar) :
    ∃ A > 0, ∃ rate > 0,
      ∀ u v : ℝ → D.Point → ℝ,
        PositiveGlobalBoundedSolution D p u v →
        HasInitialMass D u uStar →
          ExponentialC1ConvergenceWith D N u v
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2 A rate := by
  exact (h ha hb hm hβ uStar huStar hcond).2

lemma Theorem_2_5.exponential_convergence
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {C : Paper3Constants D p}
    (h : Theorem_2_5 D p N C)
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hcond : MinimalGlobalStabilityCondition D p C uStar)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hmass : HasInitialMass D u uStar) :
    ExponentialC1Convergence D N u v
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 := by
  rcases h.exponential ha hb hm hβ huStar hcond with
    ⟨A, hA, rate, hrate, hexp⟩
  exact ExponentialC1ConvergenceWith.exists hA hrate (hexp u v huv hmass)

lemma Theorem_2_5.stability_of_chiMinimal1
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {C : Paper3Constants D p}
    (h : Theorem_2_5 D p N C)
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hχ0 : 0 < p.χ₀) (hχ : p.χ₀ < C.chiMinimal1 uStar) :
    GloballyAsymptoticallyStableMinimal D p
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 :=
  h.stability ha hb hm hβ huStar
    (MinimalGlobalStabilityCondition.of_chiMinimal1 hχ0 hχ)

lemma Theorem_2_5.exponential_of_chiMinimal1
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {C : Paper3Constants D p}
    (h : Theorem_2_5 D p N C)
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hχ0 : 0 < p.χ₀) (hχ : p.χ₀ < C.chiMinimal1 uStar) :
    ∃ A > 0, ∃ rate > 0,
      ∀ u v : ℝ → D.Point → ℝ,
        PositiveGlobalBoundedSolution D p u v →
        HasInitialMass D u uStar →
          ExponentialC1ConvergenceWith D N u v
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2 A rate :=
  h.exponential ha hb hm hβ huStar
    (MinimalGlobalStabilityCondition.of_chiMinimal1 hχ0 hχ)

lemma Theorem_2_5.exponential_convergence_of_chiMinimal1
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {C : Paper3Constants D p}
    (h : Theorem_2_5 D p N C)
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hχ0 : 0 < p.χ₀) (hχ : p.χ₀ < C.chiMinimal1 uStar)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hmass : HasInitialMass D u uStar) :
    ExponentialC1Convergence D N u v
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 :=
  h.exponential_convergence ha hb hm hβ huStar
    (MinimalGlobalStabilityCondition.of_chiMinimal1 hχ0 hχ) huv hmass

lemma Theorem_2_5.stability_of_chiMinimal2
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {C : Paper3Constants D p}
    (h : Theorem_2_5 D p N C)
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hγ : p.γ = 1) (hχ0 : 0 < p.χ₀)
    (hχ : p.χ₀ < C.chiMinimal2 uStar) :
    GloballyAsymptoticallyStableMinimal D p
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 :=
  h.stability ha hb hm hβ huStar
    (MinimalGlobalStabilityCondition.of_chiMinimal2 hγ hχ0 hχ)

lemma Theorem_2_5.exponential_of_chiMinimal2
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {C : Paper3Constants D p}
    (h : Theorem_2_5 D p N C)
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hγ : p.γ = 1) (hχ0 : 0 < p.χ₀)
    (hχ : p.χ₀ < C.chiMinimal2 uStar) :
    ∃ A > 0, ∃ rate > 0,
      ∀ u v : ℝ → D.Point → ℝ,
        PositiveGlobalBoundedSolution D p u v →
        HasInitialMass D u uStar →
          ExponentialC1ConvergenceWith D N u v
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2 A rate :=
  h.exponential ha hb hm hβ huStar
    (MinimalGlobalStabilityCondition.of_chiMinimal2 hγ hχ0 hχ)

lemma Theorem_2_5.exponential_convergence_of_chiMinimal2
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {C : Paper3Constants D p}
    (h : Theorem_2_5 D p N C)
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hγ : p.γ = 1) (hχ0 : 0 < p.χ₀)
    (hχ : p.χ₀ < C.chiMinimal2 uStar)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hmass : HasInitialMass D u uStar) :
    ExponentialC1Convergence D N u v
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 :=
  h.exponential_convergence ha hb hm hβ huStar
    (MinimalGlobalStabilityCondition.of_chiMinimal2 hγ hχ0 hχ) huv hmass

def Lemma_3_1 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ u v : ℝ → D.Point → ℝ,
    PositiveGlobalBoundedSolution D p u v →
      UniformRegularityConclusion D p u v

lemma Lemma_3_1.regularity
    {D : BoundedDomainData} {p : CM2Params}
    (h : Lemma_3_1 D p)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v) :
    UniformRegularityConclusion D p u v :=
  h u v huv

/- This is an accessor from the regularity component already present in
`PositiveGlobalBoundedSolution`, not an end-to-end proof of the analytic
regularity estimate.  The name deliberately avoids `_proved`. -/
lemma Lemma_3_1_from_global_solution_regular_components
    (D : BoundedDomainData) (p : CM2Params) :
    Lemma_3_1 D p := by
  intro u v huv T hT
  exact huv.regularity hT

def Lemma_3_2
    (D : BoundedDomainData) (p : CM2Params) (K : CompactnessData D) : Prop :=
  1 ≤ p.m → 0 < p.γ →
    ∀ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v →
        TimeTranslateCompactnessConclusion D p K u v

lemma Lemma_3_2.compactness
    {D : BoundedDomainData} {p : CM2Params} {K : CompactnessData D}
    (h : Lemma_3_2 D p K) (hm : 1 ≤ p.m) (hγ : 0 < p.γ)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v) :
    TimeTranslateCompactnessConclusion D p K u v :=
  h hm hγ u v huv

def Lemma_3_3 (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D) : Prop :=
  ∀ uStar > 0, InitialContinuityConclusion D p N uStar

lemma Lemma_3_3.initial_continuity
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    (h : Lemma_3_3 D p N) {uStar : ℝ} (huStar : 0 < uStar) :
    InitialContinuityConclusion D p N uStar :=
  h uStar huStar

def Lemma_3_4
    (D : BoundedDomainData) (p : CM2Params) (K : CompactnessData D) : Prop :=
  ∀ u v : ℝ → D.Point → ℝ,
    PositiveGlobalBoundedSolution D p u v →
      UpperEnvelopeMonotonicityConclusion D p K u

lemma Lemma_3_4.upper_envelope
    {D : BoundedDomainData} {p : CM2Params} {K : CompactnessData D}
    (h : Lemma_3_4 D p K)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v) :
    UpperEnvelopeMonotonicityConclusion D p K u :=
  h u v huv

def Lemma_3_5
    (D : BoundedDomainData) (p : CM2Params) (C : Paper3Constants D p) : Prop :=
  p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
    0 < p.χ₀ → p.χ₀ < min (chiBeta p / 2) (Real.sqrt (chiBeta p)) →
      ∀ u v : ℝ → D.Point → ℝ,
        PositiveGlobalBoundedSolution D p u v →
          EventuallyUpperBoundMinimalConclusion D p C u

lemma Lemma_3_5.eventual_upper_bound
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (h : Lemma_3_5 D p C)
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ_pos : 0 < p.χ₀)
    (hχ_small : p.χ₀ < min (chiBeta p / 2) (Real.sqrt (chiBeta p)))
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v) :
    EventuallyUpperBoundMinimalConclusion D p C u :=
  h ha hb hm hβ hχ_pos hχ_small u v huv

lemma Lemma_3_1_2.regularity_and_compactness
    {D : BoundedDomainData} {p : CM2Params} {K : CompactnessData D}
    (hreg : Lemma_3_1 D p) (hcompact : Lemma_3_2 D p K)
    (hm : 1 ≤ p.m) (hγ : 0 < p.γ)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v) :
    UniformRegularityConclusion D p u v ∧
      TimeTranslateCompactnessConclusion D p K u v :=
  ⟨hreg.regularity huv, hcompact.compactness hm hγ huv⟩

lemma Lemma_3_1_2_4.dynamical_compactness_conclusion
    {D : BoundedDomainData} {p : CM2Params} {K : CompactnessData D}
    (hreg : Lemma_3_1 D p) (hcompact : Lemma_3_2 D p K)
    (henvelope : Lemma_3_4 D p K)
    (hm : 1 ≤ p.m) (hγ : 0 < p.γ)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v) :
    UniformRegularityConclusion D p u v ∧
      TimeTranslateCompactnessConclusion D p K u v ∧
      UpperEnvelopeMonotonicityConclusion D p K u :=
  ⟨hreg.regularity huv, hcompact.compactness hm hγ huv,
    henvelope.upper_envelope huv⟩

lemma Lemma_3_1_2_4.eventual_entire_limit
    {D : BoundedDomainData} {p : CM2Params} {K : CompactnessData D}
    (hcompact : Lemma_3_2 D p K)
    (hm : 1 ≤ p.m) (hγ : 0 < p.γ)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    {times : ℕ → ℝ} (htimes : Tendsto times atTop atTop) :
    ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
    ∃ uInf vInf : ℝ → D.Point → ℝ,
      EntireClassicalSolution D p uInf vInf :=
  (hcompact.compactness hm hγ huv).entire_limit htimes

lemma Lemma_3_5.eventual_upper_bound_at_mass
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (h : Lemma_3_5 D p C)
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ_pos : 0 < p.χ₀)
    (hχ_small : p.χ₀ < min (chiBeta p / 2) (Real.sqrt (chiBeta p)))
    {uStar : ℝ} (huStar : 0 < uStar)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hmass : HasInitialMass D u uStar) :
    ∀ᶠ t in atTop, D.supNorm (u t) ≤ C.eventualMinimalUBound uStar :=
  (h.eventual_upper_bound ha hb hm hβ hχ_pos hχ_small huv).bound
    huStar hmass

def Corollary_5_1
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (C : Paper3Constants D p) : Prop :=
  1 ≤ p.m →
    (∀ (uStar _vStar theta : ℝ), 0 < theta →
      ∀ u v : ℝ → D.Point → ℝ,
        PositiveGlobalBoundedSolution D p u v →
        ThetaMomentConvergesToZero D u uStar theta →
          UniformConvergesInSup D u uStar) ∧
    (∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      p.χ₀ < C.chiCritical eq.1 →
        ∀ u v : ℝ → D.Point → ℝ,
          PositiveGlobalBoundedSolution D p u v →
          UniformConvergesInSup D u eq.1 →
            ExponentialC1Convergence D N u v eq.1 eq.2) ∧
    (p.a = 0 → p.b = 0 →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        p.χ₀ < C.chiCritical uStar →
          ∀ u v : ℝ → D.Point → ℝ,
            PositiveGlobalBoundedSolution D p u v →
            HasInitialMass D u uStar →
            UniformConvergesInSup D u eq.1 →
              ExponentialC1Convergence D N u v eq.1 eq.2)

lemma Corollary_5_1.uniform_convergence_of_theta
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {C : Paper3Constants D p}
    (h : Corollary_5_1 D p N C) (hm : 1 ≤ p.m)
    {uStar vStar theta : ℝ} (htheta : 0 < theta)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hthetaConv : ThetaMomentConvergesToZero D u uStar theta) :
    UniformConvergesInSup D u uStar :=
  (h hm).1 uStar vStar theta htheta u v huv hthetaConv

lemma Corollary_5_1.nonminimal_exponential
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {C : Paper3Constants D p}
    (h : Corollary_5_1 D p N C) (hm : 1 ≤ p.m)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ : p.χ₀ < C.chiCritical (positiveEquilibrium p ⟨ha, hb⟩).1)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hconv : UniformConvergesInSup D u (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ExponentialC1Convergence D N u v
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  (h hm).2.1 ha hb hχ u v huv hconv

lemma Corollary_5_1.minimal_exponential
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {C : Paper3Constants D p}
    (h : Corollary_5_1 D p N C) (hm : 1 ≤ p.m)
    (ha : p.a = 0) (hb : p.b = 0)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hχ : p.χ₀ < C.chiCritical uStar)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hmass : HasInitialMass D u uStar)
    (hconv : UniformConvergesInSup D u (minimalEquilibrium p uStar).1) :
    ExponentialC1Convergence D N u v
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 :=
  (h hm).2.2 ha hb uStar huStar hχ u v huv hmass hconv

/-- Formula-level nonminimal exponential upgrade for Corollary 5.1.  The
critical threshold is the concrete spectral formula, and the analytic upgrade
is supplied as the raw `ConvergenceToExponentialNonminimalRaw` hypothesis
rather than through `Paper3Constants.convergenceToExponential`. -/
lemma Corollary_5_1_nonminimal_exponential_formula_branch
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D}
    (hraw :
      ConvergenceToExponentialNonminimalRaw D p N.c1Distance
        (fun uStar =>
          paperCriticalSensitivity S p uStar
            (p.ν / p.μ * uStar ^ p.γ)))
    (hm : 1 ≤ p.m) (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity S p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hconv : UniformConvergesInSup D u (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ExponentialC1Convergence D N u v
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  have hχraw :
      p.χ₀ <
        (fun uStar =>
          paperCriticalSensitivity S p uStar
            (p.ν / p.μ * uStar ^ p.γ))
          (positiveEquilibrium p ⟨ha, hb⟩).1 := by
    simpa [positiveEquilibrium] using hχ
  rcases hraw hm ha hb hχraw u v huv hconv with
    ⟨A, hA, rate, hrate, hdecay⟩
  exact ExponentialC1ConvergenceWith.exists hA hrate hdecay

lemma Corollary_5_1_nonminimal_exponential_formula_unitInterval
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    (hraw :
      ConvergenceToExponentialNonminimalRaw D p N.c1Distance
        (fun uStar =>
          paperCriticalSensitivity unitIntervalNeumannSpectrum p uStar
            (p.ν / p.μ * uStar ^ p.γ)))
    (hm : 1 ≤ p.m) (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hconv : UniformConvergesInSup D u (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ExponentialC1Convergence D N u v
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  Corollary_5_1_nonminimal_exponential_formula_branch
    (S := unitIntervalNeumannSpectrum) hraw hm ha hb hχ huv hconv

/-- Formula-level minimal exponential upgrade for Corollary 5.1. -/
lemma Corollary_5_1_minimal_exponential_formula_branch
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D}
    (hraw :
      ConvergenceToExponentialMinimalRaw D p N.c1Distance
        (fun uStar =>
          paperCriticalSensitivity S p uStar
            (p.ν / p.μ * uStar ^ p.γ)))
    (hm : 1 ≤ p.m) (ha : p.a = 0) (hb : p.b = 0)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity S p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hmass : HasInitialMass D u uStar)
    (hconv : UniformConvergesInSup D u (minimalEquilibrium p uStar).1) :
    ExponentialC1Convergence D N u v
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 := by
  have hχraw :
      p.χ₀ <
        (fun uStar =>
          paperCriticalSensitivity S p uStar
            (p.ν / p.μ * uStar ^ p.γ)) uStar := by
    simpa [minimalEquilibrium] using hχ
  rcases hraw hm ha hb uStar huStar hχraw u v huv hmass hconv with
    ⟨A, hA, rate, hrate, hdecay⟩
  exact ExponentialC1ConvergenceWith.exists hA hrate hdecay

lemma Corollary_5_1_minimal_exponential_formula_unitInterval
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    (hraw :
      ConvergenceToExponentialMinimalRaw D p N.c1Distance
        (fun uStar =>
          paperCriticalSensitivity unitIntervalNeumannSpectrum p uStar
            (p.ν / p.μ * uStar ^ p.γ)))
    (hm : 1 ≤ p.m) (ha : p.a = 0) (hb : p.b = 0)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hmass : HasInitialMass D u uStar)
    (hconv : UniformConvergesInSup D u (minimalEquilibrium p uStar).1) :
    ExponentialC1Convergence D N u v
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 :=
  Corollary_5_1_minimal_exponential_formula_branch
    (S := unitIntervalNeumannSpectrum) hraw hm ha hb huStar hχ
    huv hmass hconv

def Lemma_7_1 (D : BoundedDomainData) (K : CompactnessData D) : Prop :=
  ∃ M0 > 0, ∀ mu nu : ℝ, ∀ f : D.Point → ℝ,
    0 < mu → 0 < nu →
      K.neumannResolventGradientBound mu nu f M0

lemma Lemma_7_1.bound
    {D : BoundedDomainData} {K : CompactnessData D}
    (h : Lemma_7_1 D K) :
    ∃ M0 > 0, ∀ mu nu : ℝ, ∀ f : D.Point → ℝ,
      0 < mu → 0 < nu →
        K.neumannResolventGradientBound mu nu f M0 :=
  h

def Lemma_A_1
    (D : BoundedDomainData) (p : CM2Params) (S : SpectralData)
    (N : StabilityNorms D) : Prop :=
  ∀ sigma pNorm uStar vStar,
    1 / 2 < sigma → sigma < 1 → 1 < pNorm →
    LinearlyStable S p uStar vStar →
      ∃ eps > 0, ∃ C > 0, ∃ rate > 0,
        ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
          N.xpSigmaDistance sigma pNorm u₀ (fun _ => uStar) ≤ eps →
            ∀ u v : ℝ → D.Point → ℝ,
              IsPaper2GlobalClassicalSolution D p u v →
              InitialTrace D u₀ u →
                ∀ t, 0 ≤ t →
                  N.c1Distance (u t) (fun _ => uStar) +
                    N.c1Distance (v t) (fun _ => vStar) ≤
                      C * Real.exp (-rate * t)

lemma Lemma_A_1.local_exponential_stability
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D}
    (h : Lemma_A_1 D p S N)
    {sigma pNorm uStar vStar : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (hstable : LinearlyStable S p uStar vStar) :
    ∃ eps > 0, ∃ C > 0, ∃ rate > 0,
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        N.xpSigmaDistance sigma pNorm u₀ (fun _ => uStar) ≤ eps →
          ∀ u v : ℝ → D.Point → ℝ,
            IsPaper2GlobalClassicalSolution D p u v →
            InitialTrace D u₀ u →
              ∀ t, 0 ≤ t →
                N.c1Distance (u t) (fun _ => uStar) +
                  N.c1Distance (v t) (fun _ => vStar) ≤
                    C * Real.exp (-rate * t) :=
  h sigma pNorm uStar vStar hsigma_low hsigma_high hpNorm hstable

/-- The `X^σ_p` local exponential-decay part of Paper3 Theorem 2.2.  This is
weaker than `LocallyExponentiallyStableFromSup`: it assumes an existing global
solution with the required initial trace and asks for smallness in the
`xpSigmaDistance` norm directly.  Under those explicit inputs, the proof uses
only the spectral critical-sensitivity bridge and Lemma A.1, not the
`Paper3Constants.linearStabilityInstability` field. -/
def Theorem_2_2_xpSigma_local_exponential_branch : Prop :=
  ∀ (D : BoundedDomainData) (S : SpectralData) (p : CM2Params)
    (N : StabilityNorms D) (C : Paper3Constants D p),
    HasNeumannSpectrum S → Paper3ConstantsUsesCriticalSpectrum S p C →
      Lemma_A_1 D p S N →
        (∀ sigma pNorm, 1 / 2 < sigma → sigma < 1 → 1 < pNorm →
          ∀ (ha : 0 < p.a) (hb : 0 < p.b),
            let eq := positiveEquilibrium p ⟨ha, hb⟩
            p.χ₀ < C.chiCritical eq.1 →
              ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
                ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
                  N.xpSigmaDistance sigma pNorm u₀ (fun _ => eq.1) ≤ eps →
                    ∀ u v : ℝ → D.Point → ℝ,
                      IsPaper2GlobalClassicalSolution D p u v →
                      InitialTrace D u₀ u →
                        ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate) ∧
        (∀ sigma pNorm, 1 / 2 < sigma → sigma < 1 → 1 < pNorm →
          p.a = 0 → p.b = 0 →
            ∀ uStar > 0,
              let eq := minimalEquilibrium p uStar
              p.χ₀ < C.chiCritical uStar →
                ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
                  ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
                    N.xpSigmaDistance sigma pNorm u₀ (fun _ => eq.1) ≤ eps →
                      ∀ u v : ℝ → D.Point → ℝ,
                        IsPaper2GlobalClassicalSolution D p u v →
                        InitialTrace D u₀ u →
                          ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate)

lemma Theorem_2_2_xpSigma_local_exponential_branch_proved :
    Theorem_2_2_xpSigma_local_exponential_branch := by
  intro D S p N C H hC hA1
  refine ⟨?_, ?_⟩
  · intro sigma pNorm hsigma_low hsigma_high hpNorm ha hb
    dsimp
    intro hχ
    have hstable :=
      hC.positiveEquilibrium_linearlyStable H ha hb hχ
    rcases hA1.local_exponential_stability hsigma_low hsigma_high hpNorm hstable with
      ⟨eps, heps, A, hA, rate, hrate, hdecay⟩
    refine ⟨eps, heps, A, hA, rate, hrate, ?_⟩
    intro u₀ hu₀ hsmall u v huv htrace t ht
    exact hdecay u₀ hu₀ hsmall u v huv htrace t ht
  · intro sigma pNorm hsigma_low hsigma_high hpNorm ha hb uStar huStar
    dsimp
    intro hχ
    have hstable :=
      hC.minimalEquilibrium_linearlyStable H huStar hχ
    rcases hA1.local_exponential_stability hsigma_low hsigma_high hpNorm hstable with
      ⟨eps, heps, A, hA, rate, hrate, hdecay⟩
    refine ⟨eps, heps, A, hA, rate, hrate, ?_⟩
    intro u₀ hu₀ hsmall u v huv htrace t ht
    exact hdecay u₀ hu₀ hsmall u v huv htrace t ht

/-- Formula-level nonminimal `X^σ_p` local exponential branch.  The spectral
stability input is obtained from the explicit strong thresholds and the paper
critical-sensitivity infimum, not from `Paper3Constants`. -/
def Theorem_2_2_xpSigma_nonminimal_formula_branch : Prop :=
  ∀ (D : BoundedDomainData) (S : SpectralData) (p : CM2Params)
    (N : StabilityNorms D),
    HasNeumannSpectrum S → Lemma_A_1 D p S N →
      ∀ sigma pNorm, 1 / 2 < sigma → sigma < 1 → 1 < pNorm →
        ∀ (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ),
          let eq := positiveEquilibrium p ⟨ha, hb⟩
          max
              (max (chiStrong1Formula p eq.1 eq.2)
                (chiStrong2Formula p eq.1))
              (max (chiStrong3Formula p M0 eq.1 eq.2)
                (chiStrong4Formula p M0 eq.1)) ≤
            paperCriticalSensitivity S p eq.1 eq.2 →
            NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
              ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
                ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
                  N.xpSigmaDistance sigma pNorm u₀ (fun _ => eq.1) ≤ eps →
                    ∀ u v : ℝ → D.Point → ℝ,
                      IsPaper2GlobalClassicalSolution D p u v →
                      InitialTrace D u₀ u →
                        ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate

lemma Theorem_2_2_xpSigma_nonminimal_formula_branch_proved :
    Theorem_2_2_xpSigma_nonminimal_formula_branch := by
  intro D S p N H hA1 sigma pNorm hsigma_low hsigma_high hpNorm ha hb M0
  dsimp
  intro hcritical hcond
  have hstable :=
    hcond.linearlyStable_of_max_threshold_le_critical S p H ha hb hcritical
  rcases hA1.local_exponential_stability hsigma_low hsigma_high hpNorm hstable with
    ⟨eps, heps, A, hA, rate, hrate, hdecay⟩
  refine ⟨eps, heps, A, hA, rate, hrate, ?_⟩
  intro u₀ hu₀ hsmall u v huv htrace t ht
  exact hdecay u₀ hu₀ hsmall u v huv htrace t ht

/-- Formula-level minimal `X^σ_p` local exponential branch.  The spectral
stability input is obtained from the explicit minimal thresholds and the paper
critical-sensitivity infimum, not from `Paper3Constants`. -/
def Theorem_2_2_xpSigma_minimal_formula_branch : Prop :=
  ∀ (D : BoundedDomainData) (S : SpectralData) (p : CM2Params)
    (N : StabilityNorms D),
    HasNeumannSpectrum S → Lemma_A_1 D p S N →
      ∀ sigma pNorm, 1 / 2 < sigma → sigma < 1 → 1 < pNorm →
        p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
          ∀ uStar > 0, ∀ uBar vLower : ℝ,
            chiBeta p ≤
              paperCriticalSensitivity S p
                (minimalEquilibrium p uStar).1
                (minimalEquilibrium p uStar).2 →
              MinimalGlobalStabilityFormulaCondition p uStar uBar vLower →
                ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
                  ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
                    N.xpSigmaDistance sigma pNorm u₀
                        (fun _ => (minimalEquilibrium p uStar).1) ≤ eps →
                      ∀ u v : ℝ → D.Point → ℝ,
                        IsPaper2GlobalClassicalSolution D p u v →
                        InitialTrace D u₀ u →
                          ExponentialC1ConvergenceWith D N u v
                            (minimalEquilibrium p uStar).1
                            (minimalEquilibrium p uStar).2 A rate

lemma Theorem_2_2_xpSigma_minimal_formula_branch_proved :
    Theorem_2_2_xpSigma_minimal_formula_branch := by
  intro D S p N H hA1 sigma pNorm hsigma_low hsigma_high hpNorm
    _ha _hb _hm hβ uStar huStar uBar vLower hcritical hcond
  have hstable :=
    hcond.linearlyStable_of_chiBeta_le_critical S p H hβ huStar hcritical
  rcases hA1.local_exponential_stability hsigma_low hsigma_high hpNorm hstable with
    ⟨eps, heps, A, hA, rate, hrate, hdecay⟩
  refine ⟨eps, heps, A, hA, rate, hrate, ?_⟩
  intro u₀ hu₀ hsmall u v huv htrace t ht
  exact hdecay u₀ hu₀ hsmall u v huv htrace t ht

/-- First-mode sufficient version of the formula-level nonminimal `X^σ_p`
local exponential branch. -/
def Theorem_2_2_xpSigma_nonminimal_first_mode_branch : Prop :=
  ∀ (D : BoundedDomainData) (S : SpectralData) (p : CM2Params)
    (N : StabilityNorms D),
    HasNeumannSpectrum S → Lemma_A_1 D p S N →
      ∀ sigma pNorm, 1 / 2 < sigma → sigma < 1 → 1 < pNorm →
        ∀ (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ),
          let eq := positiveEquilibrium p ⟨ha, hb⟩
          max
              (max (chiStrong1Formula p eq.1 eq.2)
                (chiStrong2Formula p eq.1))
              (max (chiStrong3Formula p M0 eq.1 eq.2)
                (chiStrong4Formula p M0 eq.1)) ≤
            ((1 + eq.2) ^ p.β /
                (p.ν * p.γ * eq.1 ^ (p.m + p.γ - 1))) *
              (p.μ + S.firstNonzero) →
            NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
              ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
                ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
                  N.xpSigmaDistance sigma pNorm u₀ (fun _ => eq.1) ≤ eps →
                    ∀ u v : ℝ → D.Point → ℝ,
                      IsPaper2GlobalClassicalSolution D p u v →
                      InitialTrace D u₀ u →
                        ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate

lemma Theorem_2_2_xpSigma_nonminimal_first_mode_branch_proved :
    Theorem_2_2_xpSigma_nonminimal_first_mode_branch := by
  intro D S p N H hA1 sigma pNorm hsigma_low hsigma_high hpNorm ha hb M0
  dsimp
  intro hfirst hcond
  have hstable := hcond.linearlyStable_of_firstNonzero_lower S p H ha hb hfirst
  rcases hA1.local_exponential_stability hsigma_low hsigma_high hpNorm hstable with
    ⟨eps, heps, A, hA, rate, hrate, hdecay⟩
  refine ⟨eps, heps, A, hA, rate, hrate, ?_⟩
  intro u₀ hu₀ hsmall u v huv htrace t ht
  exact hdecay u₀ hu₀ hsmall u v huv htrace t ht

/-- First-mode sufficient version of the formula-level minimal `X^σ_p`
local exponential branch. -/
def Theorem_2_2_xpSigma_minimal_first_mode_branch : Prop :=
  ∀ (D : BoundedDomainData) (S : SpectralData) (p : CM2Params)
    (N : StabilityNorms D),
    HasNeumannSpectrum S → Lemma_A_1 D p S N →
      ∀ sigma pNorm, 1 / 2 < sigma → sigma < 1 → 1 < pNorm →
        p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
          ∀ uStar > 0, ∀ uBar vLower : ℝ,
            chiBeta p ≤
              ((1 + (minimalEquilibrium p uStar).2) ^ p.β /
                  (p.ν * p.γ *
                    (minimalEquilibrium p uStar).1 ^ (p.m + p.γ - 1))) *
                (p.μ + S.firstNonzero) →
              MinimalGlobalStabilityFormulaCondition p uStar uBar vLower →
                ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
                  ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
                    N.xpSigmaDistance sigma pNorm u₀
                        (fun _ => (minimalEquilibrium p uStar).1) ≤ eps →
                      ∀ u v : ℝ → D.Point → ℝ,
                        IsPaper2GlobalClassicalSolution D p u v →
                        InitialTrace D u₀ u →
                          ExponentialC1ConvergenceWith D N u v
                            (minimalEquilibrium p uStar).1
                            (minimalEquilibrium p uStar).2 A rate

lemma Theorem_2_2_xpSigma_minimal_first_mode_branch_proved :
    Theorem_2_2_xpSigma_minimal_first_mode_branch := by
  intro D S p N H hA1 sigma pNorm hsigma_low hsigma_high hpNorm
    _ha _hb _hm hβ uStar huStar uBar vLower hfirst hcond
  have hstable :=
    hcond.linearlyStable_of_firstNonzero_lower S p H hβ huStar hfirst
  rcases hA1.local_exponential_stability hsigma_low hsigma_high hpNorm hstable with
    ⟨eps, heps, A, hA, rate, hrate, hdecay⟩
  refine ⟨eps, heps, A, hA, rate, hrate, ?_⟩
  intro u₀ hu₀ hsmall u v huv htrace t ht
  exact hdecay u₀ hu₀ hsmall u v huv htrace t ht

lemma Theorem_2_2_xpSigma_nonminimal_formula_unitInterval
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hA1 : Lemma_A_1 D p unitIntervalNeumannSpectrum N)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    max
        (max (chiStrong1Formula p eq.1 eq.2)
          (chiStrong2Formula p eq.1))
        (max (chiStrong3Formula p M0 eq.1 eq.2)
          (chiStrong4Formula p M0 eq.1)) ≤
      paperCriticalSensitivity unitIntervalNeumannSpectrum p eq.1 eq.2 →
      NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
        ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
          ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
            N.xpSigmaDistance sigma pNorm u₀ (fun _ => eq.1) ≤ eps →
              ∀ u v : ℝ → D.Point → ℝ,
                IsPaper2GlobalClassicalSolution D p u v →
                InitialTrace D u₀ u →
                  ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate := by
  dsimp
  intro hcritical hcond
  have hstable :=
    hcond.linearlyStable_of_max_threshold_le_critical
      unitIntervalNeumannSpectrum p unitIntervalNeumannSpectrum_hasNeumannSpectrum
      ha hb hcritical
  rcases hA1.local_exponential_stability hsigma_low hsigma_high hpNorm hstable with
    ⟨eps, heps, A, hA, rate, hrate, hdecay⟩
  refine ⟨eps, heps, A, hA, rate, hrate, ?_⟩
  intro u₀ hu₀ hsmall u v huv htrace t ht
  exact hdecay u₀ hu₀ hsmall u v huv htrace t ht

lemma Theorem_2_2_xpSigma_nonminimal_first_mode_unitInterval
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hA1 : Lemma_A_1 D p unitIntervalNeumannSpectrum N)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    max
        (max (chiStrong1Formula p eq.1 eq.2)
          (chiStrong2Formula p eq.1))
        (max (chiStrong3Formula p M0 eq.1 eq.2)
          (chiStrong4Formula p M0 eq.1)) ≤
      ((1 + eq.2) ^ p.β /
          (p.ν * p.γ * eq.1 ^ (p.m + p.γ - 1))) *
        (p.μ + Real.pi ^ 2) →
      NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
        ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
          ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
            N.xpSigmaDistance sigma pNorm u₀ (fun _ => eq.1) ≤ eps →
              ∀ u v : ℝ → D.Point → ℝ,
                IsPaper2GlobalClassicalSolution D p u v →
                InitialTrace D u₀ u →
                  ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate := by
  dsimp
  intro hfirst hcond
  have hstable :=
    hcond.linearlyStable_of_firstNonzero_lower
      unitIntervalNeumannSpectrum p unitIntervalNeumannSpectrum_hasNeumannSpectrum
      ha hb hfirst
  rcases hA1.local_exponential_stability hsigma_low hsigma_high hpNorm hstable with
    ⟨eps, heps, A, hA, rate, hrate, hdecay⟩
  refine ⟨eps, heps, A, hA, rate, hrate, ?_⟩
  intro u₀ hu₀ hsmall u v huv htrace t ht
  exact hdecay u₀ hu₀ hsmall u v huv htrace t ht

lemma Theorem_2_2_xpSigma_minimal_formula_unitInterval
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hA1 : Lemma_A_1 D p unitIntervalNeumannSpectrum N)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (_ha : p.a = 0) (_hb : p.b = 0) (_hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar) (uBar vLower : ℝ) :
    chiBeta p ≤
      paperCriticalSensitivity unitIntervalNeumannSpectrum p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 →
      MinimalGlobalStabilityFormulaCondition p uStar uBar vLower →
        ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
          ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
            N.xpSigmaDistance sigma pNorm u₀
                (fun _ => (minimalEquilibrium p uStar).1) ≤ eps →
              ∀ u v : ℝ → D.Point → ℝ,
                IsPaper2GlobalClassicalSolution D p u v →
                InitialTrace D u₀ u →
                  ExponentialC1ConvergenceWith D N u v
                    (minimalEquilibrium p uStar).1
                    (minimalEquilibrium p uStar).2 A rate := by
  intro hcritical hcond
  have hstable :=
    hcond.linearlyStable_of_chiBeta_le_critical
      unitIntervalNeumannSpectrum p unitIntervalNeumannSpectrum_hasNeumannSpectrum
      hβ huStar hcritical
  rcases hA1.local_exponential_stability hsigma_low hsigma_high hpNorm hstable with
    ⟨eps, heps, A, hA, rate, hrate, hdecay⟩
  refine ⟨eps, heps, A, hA, rate, hrate, ?_⟩
  intro u₀ hu₀ hsmall u v huv htrace t ht
  exact hdecay u₀ hu₀ hsmall u v huv htrace t ht

lemma Theorem_2_2_xpSigma_minimal_first_mode_unitInterval
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hA1 : Lemma_A_1 D p unitIntervalNeumannSpectrum N)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (_ha : p.a = 0) (_hb : p.b = 0) (_hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar) (uBar vLower : ℝ) :
    chiBeta p ≤
      ((1 + (minimalEquilibrium p uStar).2) ^ p.β /
          (p.ν * p.γ *
            (minimalEquilibrium p uStar).1 ^ (p.m + p.γ - 1))) *
        (p.μ + Real.pi ^ 2) →
      MinimalGlobalStabilityFormulaCondition p uStar uBar vLower →
        ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
          ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
            N.xpSigmaDistance sigma pNorm u₀
                (fun _ => (minimalEquilibrium p uStar).1) ≤ eps →
              ∀ u v : ℝ → D.Point → ℝ,
                IsPaper2GlobalClassicalSolution D p u v →
                InitialTrace D u₀ u →
                  ExponentialC1ConvergenceWith D N u v
                    (minimalEquilibrium p uStar).1
                    (minimalEquilibrium p uStar).2 A rate := by
  intro hfirst hcond
  have hstable :=
    hcond.linearlyStable_of_firstNonzero_lower
      unitIntervalNeumannSpectrum p unitIntervalNeumannSpectrum_hasNeumannSpectrum
      hβ huStar hfirst
  rcases hA1.local_exponential_stability hsigma_low hsigma_high hpNorm hstable with
    ⟨eps, heps, A, hA, rate, hrate, hdecay⟩
  refine ⟨eps, heps, A, hA, rate, hrate, ?_⟩
  intro u₀ hu₀ hsmall u v huv htrace t ht
  exact hdecay u₀ hu₀ hsmall u v huv htrace t ht

/-- `X^σ_p` local exponential branch for nonpositive sensitivity.  This
uses the direct spectral stability theorem for `χ₀ ≤ 0` and Lemma A.1, with
no critical-sensitivity package and no `Paper3Constants` field. -/
lemma Theorem_2_2_xpSigma_chi_nonpos_branch
    (D : BoundedDomainData) (S : SpectralData) (p : CM2Params)
    (N : StabilityNorms D)
    (H : HasNeumannSpectrum S) (hA1 : Lemma_A_1 D p S N)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm) (hχ : p.χ₀ ≤ 0) :
    (∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
        ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
          N.xpSigmaDistance sigma pNorm u₀ (fun _ => eq.1) ≤ eps →
            ∀ u v : ℝ → D.Point → ℝ,
              IsPaper2GlobalClassicalSolution D p u v →
              InitialTrace D u₀ u →
                ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate) ∧
    (p.a = 0 → p.b = 0 →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
          ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
            N.xpSigmaDistance sigma pNorm u₀ (fun _ => eq.1) ≤ eps →
              ∀ u v : ℝ → D.Point → ℝ,
                IsPaper2GlobalClassicalSolution D p u v →
                InitialTrace D u₀ u →
                  ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate) := by
  refine ⟨?_, ?_⟩
  · intro ha hb
    dsimp
    have hstable :=
      positiveEquilibrium_linearlyStable_of_chi_nonpos_neumann
        S p H hχ ha hb
    rcases hA1.local_exponential_stability
        hsigma_low hsigma_high hpNorm hstable with
      ⟨eps, heps, A, hA, rate, hrate, hdecay⟩
    refine ⟨eps, heps, A, hA, rate, hrate, ?_⟩
    intro u₀ hu₀ hsmall u v huv htrace t ht
    exact hdecay u₀ hu₀ hsmall u v huv htrace t ht
  · intro ha _hb uStar huStar
    dsimp
    have hstable :=
      minimalEquilibrium_linearlyStable_of_chi_nonpos_a_eq_zero_neumann
        S p H hχ ha huStar
    rcases hA1.local_exponential_stability
        hsigma_low hsigma_high hpNorm hstable with
      ⟨eps, heps, A, hA, rate, hrate, hdecay⟩
    refine ⟨eps, heps, A, hA, rate, hrate, ?_⟩
    intro u₀ hu₀ hsmall u v huv htrace t ht
    exact hdecay u₀ hu₀ hsmall u v huv htrace t ht

/-- Unit-interval `X^σ_p` local exponential branch for nonpositive
sensitivity.  The spectral part is proved from `χ₀ ≤ 0`; the sectorial
local exponential estimate is exactly the explicit Lemma A.1 input, not a
`Paper3Constants` package field. -/
lemma Theorem_2_2_xpSigma_chi_nonpos_unitInterval
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hA1 : Lemma_A_1 D p unitIntervalNeumannSpectrum N)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm) (hχ : p.χ₀ ≤ 0) :
    (∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
        ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
          N.xpSigmaDistance sigma pNorm u₀ (fun _ => eq.1) ≤ eps →
            ∀ u v : ℝ → D.Point → ℝ,
              IsPaper2GlobalClassicalSolution D p u v →
              InitialTrace D u₀ u →
                ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate) ∧
    (p.a = 0 → p.b = 0 →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
          ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
            N.xpSigmaDistance sigma pNorm u₀ (fun _ => eq.1) ≤ eps →
              ∀ u v : ℝ → D.Point → ℝ,
                IsPaper2GlobalClassicalSolution D p u v →
                InitialTrace D u₀ u →
                  ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate) := by
  refine ⟨?_, ?_⟩
  · intro ha hb
    dsimp
    have hstable :=
      unitInterval_positiveEquilibrium_linearlyStable_of_chi_nonpos p hχ ha hb
    rcases hA1.local_exponential_stability
        hsigma_low hsigma_high hpNorm hstable with
      ⟨eps, heps, A, hA, rate, hrate, hdecay⟩
    refine ⟨eps, heps, A, hA, rate, hrate, ?_⟩
    intro u₀ hu₀ hsmall u v huv htrace t ht
    exact hdecay u₀ hu₀ hsmall u v huv htrace t ht
  · intro ha _hb uStar huStar
    dsimp
    have hstable :=
      unitInterval_minimalEquilibrium_linearlyStable_of_chi_nonpos
        p hχ ha huStar
    rcases hA1.local_exponential_stability
        hsigma_low hsigma_high hpNorm hstable with
      ⟨eps, heps, A, hA, rate, hrate, hdecay⟩
    refine ⟨eps, heps, A, hA, rate, hrate, ?_⟩
    intro u₀ hu₀ hsmall u v huv htrace t ht
    exact hdecay u₀ hu₀ hsmall u v huv htrace t ht

/-- Raw `X^σ_p` local exponential branch for nonpositive sensitivity.  This
version replaces the theorem-shaped `Lemma_A_1` hypothesis by the exposed
sectorial estimate `SectorialLocalExponentialRaw`. -/
lemma Theorem_2_2_xpSigma_chi_nonpos_raw_branch
    (D : BoundedDomainData) (S : SpectralData) (p : CM2Params)
    (N : StabilityNorms D)
    (H : HasNeumannSpectrum S)
    (hraw :
      SectorialLocalExponentialRaw D p S N.c1Distance N.xpSigmaDistance)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm) (hχ : p.χ₀ ≤ 0) :
    (∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
        ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
          N.xpSigmaDistance sigma pNorm u₀ (fun _ => eq.1) ≤ eps →
            ∀ u v : ℝ → D.Point → ℝ,
              IsPaper2GlobalClassicalSolution D p u v →
              InitialTrace D u₀ u →
                ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate) ∧
    (p.a = 0 → p.b = 0 →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
          ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
            N.xpSigmaDistance sigma pNorm u₀ (fun _ => eq.1) ≤ eps →
              ∀ u v : ℝ → D.Point → ℝ,
                IsPaper2GlobalClassicalSolution D p u v →
                InitialTrace D u₀ u →
                  ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate) := by
  refine ⟨?_, ?_⟩
  · intro ha hb
    dsimp
    have hstable :=
      positiveEquilibrium_linearlyStable_of_chi_nonpos_neumann
        S p H hχ ha hb
    rcases hraw.local_exponential_stability
        hsigma_low hsigma_high hpNorm hstable with
      ⟨eps, heps, A, hA, rate, hrate, hdecay⟩
    refine ⟨eps, heps, A, hA, rate, hrate, ?_⟩
    intro u₀ hu₀ hsmall u v huv htrace t ht
    exact hdecay u₀ hu₀ hsmall u v huv htrace t ht
  · intro ha _hb uStar huStar
    dsimp
    have hstable :=
      minimalEquilibrium_linearlyStable_of_chi_nonpos_a_eq_zero_neumann
        S p H hχ ha huStar
    rcases hraw.local_exponential_stability
        hsigma_low hsigma_high hpNorm hstable with
      ⟨eps, heps, A, hA, rate, hrate, hdecay⟩
    refine ⟨eps, heps, A, hA, rate, hrate, ?_⟩
    intro u₀ hu₀ hsmall u v huv htrace t ht
    exact hdecay u₀ hu₀ hsmall u v huv htrace t ht

/-- Unit-interval raw `X^σ_p` local exponential branch for nonpositive
sensitivity. -/
lemma Theorem_2_2_xpSigma_chi_nonpos_raw_unitInterval
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hraw :
      SectorialLocalExponentialRaw D p unitIntervalNeumannSpectrum
        N.c1Distance N.xpSigmaDistance)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm) (hχ : p.χ₀ ≤ 0) :
    (∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
        ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
          N.xpSigmaDistance sigma pNorm u₀ (fun _ => eq.1) ≤ eps →
            ∀ u v : ℝ → D.Point → ℝ,
              IsPaper2GlobalClassicalSolution D p u v →
              InitialTrace D u₀ u →
                ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate) ∧
    (p.a = 0 → p.b = 0 →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
          ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
            N.xpSigmaDistance sigma pNorm u₀ (fun _ => eq.1) ≤ eps →
              ∀ u v : ℝ → D.Point → ℝ,
                IsPaper2GlobalClassicalSolution D p u v →
                InitialTrace D u₀ u →
                  ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate) :=
  Theorem_2_2_xpSigma_chi_nonpos_raw_branch
    D unitIntervalNeumannSpectrum p N
    unitIntervalNeumannSpectrum_hasNeumannSpectrum hraw
    hsigma_low hsigma_high hpNorm hχ

/-- Raw formula-level nonminimal `X^σ_p` local exponential branch. -/
lemma Theorem_2_2_xpSigma_nonminimal_formula_raw_branch
    (D : BoundedDomainData) (S : SpectralData) (p : CM2Params)
    (N : StabilityNorms D)
    (H : HasNeumannSpectrum S)
    (hraw :
      SectorialLocalExponentialRaw D p S N.c1Distance N.xpSigmaDistance)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    max
        (max (chiStrong1Formula p eq.1 eq.2)
          (chiStrong2Formula p eq.1))
        (max (chiStrong3Formula p M0 eq.1 eq.2)
          (chiStrong4Formula p M0 eq.1)) ≤
      paperCriticalSensitivity S p eq.1 eq.2 →
      NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
        ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
          ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
            N.xpSigmaDistance sigma pNorm u₀ (fun _ => eq.1) ≤ eps →
              ∀ u v : ℝ → D.Point → ℝ,
                IsPaper2GlobalClassicalSolution D p u v →
                InitialTrace D u₀ u →
                  ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate := by
  dsimp
  intro hcritical hcond
  have hstable :=
    hcond.linearlyStable_of_max_threshold_le_critical S p H ha hb hcritical
  rcases hraw.local_exponential_stability
      hsigma_low hsigma_high hpNorm hstable with
    ⟨eps, heps, A, hA, rate, hrate, hdecay⟩
  refine ⟨eps, heps, A, hA, rate, hrate, ?_⟩
  intro u₀ hu₀ hsmall u v huv htrace t ht
  exact hdecay u₀ hu₀ hsmall u v huv htrace t ht

/-- Raw formula-level minimal `X^σ_p` local exponential branch. -/
lemma Theorem_2_2_xpSigma_minimal_formula_raw_branch
    (D : BoundedDomainData) (S : SpectralData) (p : CM2Params)
    (N : StabilityNorms D)
    (H : HasNeumannSpectrum S)
    (hraw :
      SectorialLocalExponentialRaw D p S N.c1Distance N.xpSigmaDistance)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (_ha : p.a = 0) (_hb : p.b = 0) (_hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar) (uBar vLower : ℝ) :
    chiBeta p ≤
      paperCriticalSensitivity S p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 →
      MinimalGlobalStabilityFormulaCondition p uStar uBar vLower →
        ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
          ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
            N.xpSigmaDistance sigma pNorm u₀
                (fun _ => (minimalEquilibrium p uStar).1) ≤ eps →
              ∀ u v : ℝ → D.Point → ℝ,
                IsPaper2GlobalClassicalSolution D p u v →
                InitialTrace D u₀ u →
                  ExponentialC1ConvergenceWith D N u v
                    (minimalEquilibrium p uStar).1
                    (minimalEquilibrium p uStar).2 A rate := by
  intro hcritical hcond
  have hstable :=
    hcond.linearlyStable_of_chiBeta_le_critical S p H hβ huStar hcritical
  rcases hraw.local_exponential_stability
      hsigma_low hsigma_high hpNorm hstable with
    ⟨eps, heps, A, hA, rate, hrate, hdecay⟩
  refine ⟨eps, heps, A, hA, rate, hrate, ?_⟩
  intro u₀ hu₀ hsmall u v huv htrace t ht
  exact hdecay u₀ hu₀ hsmall u v huv htrace t ht

/-- Raw first-mode sufficient version of the nonminimal `X^σ_p` local
exponential branch. -/
lemma Theorem_2_2_xpSigma_nonminimal_first_mode_raw_branch
    (D : BoundedDomainData) (S : SpectralData) (p : CM2Params)
    (N : StabilityNorms D)
    (H : HasNeumannSpectrum S)
    (hraw :
      SectorialLocalExponentialRaw D p S N.c1Distance N.xpSigmaDistance)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    max
        (max (chiStrong1Formula p eq.1 eq.2)
          (chiStrong2Formula p eq.1))
        (max (chiStrong3Formula p M0 eq.1 eq.2)
          (chiStrong4Formula p M0 eq.1)) ≤
      ((1 + eq.2) ^ p.β /
          (p.ν * p.γ * eq.1 ^ (p.m + p.γ - 1))) *
        (p.μ + S.firstNonzero) →
      NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
        ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
          ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
            N.xpSigmaDistance sigma pNorm u₀ (fun _ => eq.1) ≤ eps →
              ∀ u v : ℝ → D.Point → ℝ,
                IsPaper2GlobalClassicalSolution D p u v →
                InitialTrace D u₀ u →
                  ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate := by
  dsimp
  intro hfirst hcond
  have hstable := hcond.linearlyStable_of_firstNonzero_lower S p H ha hb hfirst
  rcases hraw.local_exponential_stability
      hsigma_low hsigma_high hpNorm hstable with
    ⟨eps, heps, A, hA, rate, hrate, hdecay⟩
  refine ⟨eps, heps, A, hA, rate, hrate, ?_⟩
  intro u₀ hu₀ hsmall u v huv htrace t ht
  exact hdecay u₀ hu₀ hsmall u v huv htrace t ht

/-- Raw first-mode sufficient version of the minimal `X^σ_p` local exponential
branch. -/
lemma Theorem_2_2_xpSigma_minimal_first_mode_raw_branch
    (D : BoundedDomainData) (S : SpectralData) (p : CM2Params)
    (N : StabilityNorms D)
    (H : HasNeumannSpectrum S)
    (hraw :
      SectorialLocalExponentialRaw D p S N.c1Distance N.xpSigmaDistance)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (_ha : p.a = 0) (_hb : p.b = 0) (_hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar) (uBar vLower : ℝ) :
    chiBeta p ≤
      ((1 + (minimalEquilibrium p uStar).2) ^ p.β /
          (p.ν * p.γ *
            (minimalEquilibrium p uStar).1 ^ (p.m + p.γ - 1))) *
        (p.μ + S.firstNonzero) →
      MinimalGlobalStabilityFormulaCondition p uStar uBar vLower →
        ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
          ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
            N.xpSigmaDistance sigma pNorm u₀
                (fun _ => (minimalEquilibrium p uStar).1) ≤ eps →
              ∀ u v : ℝ → D.Point → ℝ,
                IsPaper2GlobalClassicalSolution D p u v →
                InitialTrace D u₀ u →
                  ExponentialC1ConvergenceWith D N u v
                    (minimalEquilibrium p uStar).1
                    (minimalEquilibrium p uStar).2 A rate := by
  intro hfirst hcond
  have hstable :=
    hcond.linearlyStable_of_firstNonzero_lower S p H hβ huStar hfirst
  rcases hraw.local_exponential_stability
      hsigma_low hsigma_high hpNorm hstable with
    ⟨eps, heps, A, hA, rate, hrate, hdecay⟩
  refine ⟨eps, heps, A, hA, rate, hrate, ?_⟩
  intro u₀ hu₀ hsmall u v huv htrace t ht
  exact hdecay u₀ hu₀ hsmall u v huv htrace t ht

/-- Unit-interval raw formula-level nonminimal `X^σ_p` local exponential
branch. -/
lemma Theorem_2_2_xpSigma_nonminimal_formula_raw_unitInterval
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hraw :
      SectorialLocalExponentialRaw D p unitIntervalNeumannSpectrum
        N.c1Distance N.xpSigmaDistance)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    max
        (max (chiStrong1Formula p eq.1 eq.2)
          (chiStrong2Formula p eq.1))
        (max (chiStrong3Formula p M0 eq.1 eq.2)
          (chiStrong4Formula p M0 eq.1)) ≤
      paperCriticalSensitivity unitIntervalNeumannSpectrum p eq.1 eq.2 →
      NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
        ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
          ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
            N.xpSigmaDistance sigma pNorm u₀ (fun _ => eq.1) ≤ eps →
              ∀ u v : ℝ → D.Point → ℝ,
                IsPaper2GlobalClassicalSolution D p u v →
                InitialTrace D u₀ u →
                  ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate :=
  Theorem_2_2_xpSigma_nonminimal_formula_raw_branch
    D unitIntervalNeumannSpectrum p N
    unitIntervalNeumannSpectrum_hasNeumannSpectrum hraw
    hsigma_low hsigma_high hpNorm ha hb M0

/-- Unit-interval raw formula-level minimal `X^σ_p` local exponential
branch. -/
lemma Theorem_2_2_xpSigma_minimal_formula_raw_unitInterval
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hraw :
      SectorialLocalExponentialRaw D p unitIntervalNeumannSpectrum
        N.c1Distance N.xpSigmaDistance)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (_ha : p.a = 0) (_hb : p.b = 0) (_hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar) (uBar vLower : ℝ) :
    chiBeta p ≤
      paperCriticalSensitivity unitIntervalNeumannSpectrum p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 →
      MinimalGlobalStabilityFormulaCondition p uStar uBar vLower →
        ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
          ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
            N.xpSigmaDistance sigma pNorm u₀
                (fun _ => (minimalEquilibrium p uStar).1) ≤ eps →
              ∀ u v : ℝ → D.Point → ℝ,
                IsPaper2GlobalClassicalSolution D p u v →
                InitialTrace D u₀ u →
                  ExponentialC1ConvergenceWith D N u v
                    (minimalEquilibrium p uStar).1
                    (minimalEquilibrium p uStar).2 A rate :=
  Theorem_2_2_xpSigma_minimal_formula_raw_branch
    D unitIntervalNeumannSpectrum p N
    unitIntervalNeumannSpectrum_hasNeumannSpectrum hraw
    hsigma_low hsigma_high hpNorm _ha _hb _hm hβ huStar uBar vLower

/-- Unit-interval raw first-mode nonminimal `X^σ_p` local exponential branch. -/
lemma Theorem_2_2_xpSigma_nonminimal_first_mode_raw_unitInterval
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hraw :
      SectorialLocalExponentialRaw D p unitIntervalNeumannSpectrum
        N.c1Distance N.xpSigmaDistance)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    max
        (max (chiStrong1Formula p eq.1 eq.2)
          (chiStrong2Formula p eq.1))
        (max (chiStrong3Formula p M0 eq.1 eq.2)
          (chiStrong4Formula p M0 eq.1)) ≤
      ((1 + eq.2) ^ p.β /
          (p.ν * p.γ * eq.1 ^ (p.m + p.γ - 1))) *
        (p.μ + Real.pi ^ 2) →
      NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
        ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
          ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
            N.xpSigmaDistance sigma pNorm u₀ (fun _ => eq.1) ≤ eps →
              ∀ u v : ℝ → D.Point → ℝ,
                IsPaper2GlobalClassicalSolution D p u v →
                InitialTrace D u₀ u →
                  ExponentialC1ConvergenceWith D N u v eq.1 eq.2 A rate := by
  dsimp
  intro hfirst hcond
  exact
    Theorem_2_2_xpSigma_nonminimal_first_mode_raw_branch
      D unitIntervalNeumannSpectrum p N
      unitIntervalNeumannSpectrum_hasNeumannSpectrum hraw
      hsigma_low hsigma_high hpNorm ha hb M0 hfirst hcond

/-- Unit-interval raw first-mode minimal `X^σ_p` local exponential branch. -/
lemma Theorem_2_2_xpSigma_minimal_first_mode_raw_unitInterval
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hraw :
      SectorialLocalExponentialRaw D p unitIntervalNeumannSpectrum
        N.c1Distance N.xpSigmaDistance)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (_ha : p.a = 0) (_hb : p.b = 0) (_hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar) (uBar vLower : ℝ) :
    chiBeta p ≤
      ((1 + (minimalEquilibrium p uStar).2) ^ p.β /
          (p.ν * p.γ *
            (minimalEquilibrium p uStar).1 ^ (p.m + p.γ - 1))) *
        (p.μ + Real.pi ^ 2) →
      MinimalGlobalStabilityFormulaCondition p uStar uBar vLower →
        ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
          ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
            N.xpSigmaDistance sigma pNorm u₀
                (fun _ => (minimalEquilibrium p uStar).1) ≤ eps →
              ∀ u v : ℝ → D.Point → ℝ,
                IsPaper2GlobalClassicalSolution D p u v →
                InitialTrace D u₀ u →
                  ExponentialC1ConvergenceWith D N u v
                    (minimalEquilibrium p uStar).1
                    (minimalEquilibrium p uStar).2 A rate := by
  intro hfirst hcond
  exact
    Theorem_2_2_xpSigma_minimal_first_mode_raw_branch
      D unitIntervalNeumannSpectrum p N
      unitIntervalNeumannSpectrum_hasNeumannSpectrum hraw
      hsigma_low hsigma_high hpNorm _ha _hb _hm hβ huStar uBar vLower
      hfirst hcond

def Lemma_A_2
    (D : BoundedDomainData) (p : CM2Params)
    (S : SemigroupEstimateData D) : Prop :=
  Paper2.Lemma_2_1 D p S

lemma Lemma_A_2.paper2
    {D : BoundedDomainData} {p : CM2Params} {S : SemigroupEstimateData D}
    (h : Lemma_A_2 D p S) :
    Paper2.Lemma_2_1 D p S :=
  h

lemma Lemma_A_2_zero_output_branch
    (D : BoundedDomainData) (p : CM2Params) (S : SemigroupEstimateData D)
    (hlp_nonneg : ∀ q u, 0 ≤ S.lpNorm q u)
    (hfrac_nonneg : ∀ sigma q u, 0 ≤ S.fractionalNorm sigma q u)
    (hfrac_semigroup_zero :
      ∀ sigma q t u, S.fractionalNorm sigma q (S.semigroup t u) = 0)
    (hlp_difference_zero :
      ∀ t u, S.lpNorm 2 (fun x => S.semigroup t u x - u x) = 0) :
    Lemma_A_2 D p S := by
  simpa [Lemma_A_2] using
    ShenWork.Paper2.Lemma_2_1_zero_output_branch D p S
      hlp_nonneg hfrac_nonneg hfrac_semigroup_zero hlp_difference_zero

lemma Lemma_A_2_zero_data (D : BoundedDomainData) (p : CM2Params) :
    Lemma_A_2 D p (ShenWork.Paper2.zeroSemigroupEstimateData D) :=
  ShenWork.Paper2.Lemma_2_1_zero_data D p

lemma Lemma_A_2.fractional_decay
    {D : BoundedDomainData} {p : CM2Params} {S : SemigroupEstimateData D}
    (h : Lemma_A_2 D p S)
    {sigma q delta : ℝ}
    (hsigma : 0 ≤ sigma) (hq : 1 ≤ q)
    (hdelta_pos : 0 < delta) (hdelta_mu : delta < p.μ) :
    ∃ C > 0, ∀ t > 0, ∀ u : D.Point → ℝ,
      S.fractionalNorm sigma q (S.semigroup t u) ≤
        C * t ^ (-sigma) * Real.exp (-delta * t) * S.lpNorm q u :=
  h.paper2.fractional_decay hsigma hq hdelta_pos hdelta_mu

lemma Lemma_A_2.semigroup_continuity
    {D : BoundedDomainData} {p : CM2Params} {S : SemigroupEstimateData D}
    (h : Lemma_A_2 D p S)
    {sigma : ℝ} (hsigma_pos : 0 < sigma) (hsigma_one : sigma ≤ 1) :
    ∃ C > 0, ∀ t > 0, ∀ u : D.Point → ℝ,
      S.lpNorm 2 (fun x => S.semigroup t u x - u x) ≤
        C * t ^ sigma * S.fractionalNorm sigma 2 u :=
  h.paper2.semigroup_continuity hsigma_pos hsigma_one

def Lemma_A_3
    (D : BoundedDomainData) (S : SemigroupEstimateData D) : Prop :=
  Paper2.Lemma_2_2 D S

lemma Lemma_A_3.paper2
    {D : BoundedDomainData} {S : SemigroupEstimateData D}
    (h : Lemma_A_3 D S) :
    Paper2.Lemma_2_2 D S :=
  h

lemma Lemma_A_3_zero_embedding_branch
    (D : BoundedDomainData) (S : SemigroupEstimateData D)
    (hfrac_nonneg : ∀ sigma q u, 0 ≤ S.fractionalNorm sigma q u)
    (hembed_general_zero : ∀ k r sigma u, S.embeddingNorm k r sigma u = 0)
    (hembed_same_zero : ∀ theta q sigma u, S.embeddingNorm theta q sigma u = 0) :
    Lemma_A_3 D S := by
  simpa [Lemma_A_3] using
    ShenWork.Paper2.Lemma_2_2_zero_embedding_branch D S
      hfrac_nonneg hembed_general_zero hembed_same_zero

lemma Lemma_A_3_zero_data (D : BoundedDomainData) :
    Lemma_A_3 D (ShenWork.Paper2.zeroSemigroupEstimateData D) :=
  ShenWork.Paper2.Lemma_2_2_zero_data D

lemma Lemma_A_3.embedding_general
    {D : BoundedDomainData} {S : SemigroupEstimateData D}
    (h : Lemma_A_3 D S)
    {sigma q k r : ℝ}
    (hsigma : 0 ≤ sigma) (hq : 1 ≤ q) (hqr : q ≤ r)
    (hcond : k - (D.volume / r) < 2 * sigma - D.volume / q) :
    ∃ C > 0, ∀ u : D.Point → ℝ,
      S.embeddingNorm k r sigma u ≤ C * S.fractionalNorm sigma q u :=
  h.paper2.embedding_general hsigma hq hqr hcond

lemma Lemma_A_3.embedding_same_q
    {D : BoundedDomainData} {S : SemigroupEstimateData D}
    (h : Lemma_A_3 D S)
    {sigma q theta : ℝ}
    (htheta_nonneg : 0 ≤ theta)
    (hcond : theta < 2 * sigma - D.volume / q) :
    ∃ C > 0, ∀ u : D.Point → ℝ,
      S.embeddingNorm theta q sigma u ≤ C * S.fractionalNorm sigma q u :=
  h.paper2.embedding_same_q htheta_nonneg hcond

def Lemma_A_4
    (D : BoundedDomainData) (p : CM2Params)
    (S : SemigroupEstimateData D) : Prop :=
  Paper2.Lemma_2_3 D p S

lemma Lemma_A_4.paper2
    {D : BoundedDomainData} {p : CM2Params} {S : SemigroupEstimateData D}
    (h : Lemma_A_4 D p S) :
    Paper2.Lemma_2_3 D p S :=
  h

lemma Lemma_A_4_zero_divergence_branch
    (D : BoundedDomainData) (p : CM2Params) (S : SemigroupEstimateData D)
    (hvector_nonneg : ∀ q phi, 0 ≤ S.vectorLpNorm q phi)
    (hlp_div_zero : ∀ q t phi, S.lpNorm q (S.divergenceSemigroup t phi) = 0) :
    Lemma_A_4 D p S := by
  simpa [Lemma_A_4] using
    ShenWork.Paper2.Lemma_2_3_zero_divergence_branch D p S
      hvector_nonneg hlp_div_zero

lemma Lemma_A_4_zero_data (D : BoundedDomainData) (p : CM2Params) :
    Lemma_A_4 D p (ShenWork.Paper2.zeroSemigroupEstimateData D) :=
  ShenWork.Paper2.Lemma_2_3_zero_data D p

lemma Lemma_A_4.divergence_bound
    {D : BoundedDomainData} {p : CM2Params} {S : SemigroupEstimateData D}
    (h : Lemma_A_4 D p S) :
    ∃ C > 0, ∀ q > 1, ∀ t > 0, ∀ phi : D.Point → ℝ,
      S.lpNorm q (S.divergenceSemigroup t phi) ≤
        C * (1 + t ^ (-(1 / 2 : ℝ))) *
          Real.exp (-(p.μ) * t) * S.vectorLpNorm q phi :=
  h.paper2.divergence_bound

def Lemma_A_5
    (D : BoundedDomainData) (p : CM2Params)
    (S : SemigroupEstimateData D) : Prop :=
  Paper2.Lemma_2_4 D p S

lemma Lemma_A_5.paper2
    {D : BoundedDomainData} {p : CM2Params} {S : SemigroupEstimateData D}
    (h : Lemma_A_5 D p S) :
    Paper2.Lemma_2_4 D p S :=
  h

lemma Lemma_A_5_zero_fractional_divergence_branch
    (D : BoundedDomainData) (p : CM2Params) (S : SemigroupEstimateData D)
    (hvector_nonneg : ∀ q phi, 0 ≤ S.vectorLpNorm q phi)
    (hfrac_div_zero :
      ∀ sigma q t phi,
        S.fractionalNorm sigma q (S.divergenceSemigroup t phi) = 0) :
    Lemma_A_5 D p S := by
  simpa [Lemma_A_5] using
    ShenWork.Paper2.Lemma_2_4_zero_fractional_divergence_branch D p S
      hvector_nonneg hfrac_div_zero

lemma Lemma_A_5_zero_data (D : BoundedDomainData) (p : CM2Params) :
    Lemma_A_5 D p (ShenWork.Paper2.zeroSemigroupEstimateData D) :=
  ShenWork.Paper2.Lemma_2_4_zero_data D p

lemma Lemma_A_5.fractional_divergence_bound
    {D : BoundedDomainData} {p : CM2Params} {S : SemigroupEstimateData D}
    (h : Lemma_A_5 D p S)
    {sigma q : ℝ} (hsigma : 0 < sigma) (hq : 1 < q) :
    ∃ C > 0, ∀ t > 0, ∀ phi : D.Point → ℝ,
      S.fractionalNorm sigma q (S.divergenceSemigroup t phi) ≤
        C * t ^ (-sigma) * (1 + t ^ (-(1 / 2 : ℝ))) *
          Real.exp (-(p.μ / 2) * t) * S.vectorLpNorm q phi :=
  h.paper2.fractional_divergence_bound hsigma hq

def PowerDifferenceInequality
    (C alpha gamma uStar : ℝ) : Prop :=
  ∀ u > 0,
    (u ^ gamma - uStar ^ gamma) ^ 2 ≤
      C * uStar ^ (2 * gamma - alpha - 1) *
        ((u - uStar) * (u ^ alpha - uStar ^ alpha))

lemma PowerDifferenceInequality.apply
    {C alpha gamma uStar u : ℝ}
    (h : PowerDifferenceInequality C alpha gamma uStar)
    (hu : 0 < u) :
    (u ^ gamma - uStar ^ gamma) ^ 2 ≤
      C * uStar ^ (2 * gamma - alpha - 1) *
        ((u - uStar) * (u ^ alpha - uStar ^ alpha)) :=
  h u hu

lemma PowerDifferenceInequality.of_normalized
    {C alpha gamma uStar : ℝ}
    (hnorm : ∀ t > 0,
      (t ^ gamma - 1) ^ 2 ≤ C * ((t - 1) * (t ^ alpha - 1)))
    (huStar : 0 < uStar) :
    PowerDifferenceInequality C alpha gamma uStar := by
  intro u hu
  let t : ℝ := u / uStar
  have ht : 0 < t := div_pos hu huStar
  have hu_eq : u = uStar * t := by
    dsimp [t]
    field_simp [ne_of_gt huStar]
  have huStar_nonneg : 0 ≤ uStar := huStar.le
  have ht_nonneg : 0 ≤ t := ht.le
  have hnorm_t := hnorm t ht
  have hpow_u_gamma : u ^ gamma = uStar ^ gamma * t ^ gamma := by
    rw [hu_eq]
    exact Real.mul_rpow huStar_nonneg ht_nonneg
  have hpow_u_alpha : u ^ alpha = uStar ^ alpha * t ^ alpha := by
    rw [hu_eq]
    exact Real.mul_rpow huStar_nonneg ht_nonneg
  have hpow_gamma_sq : (uStar ^ gamma) * (uStar ^ gamma) = uStar ^ (2 * gamma) := by
    calc
      (uStar ^ gamma) * (uStar ^ gamma) = uStar ^ (gamma + gamma) := by
        rw [← Real.rpow_add huStar]
      _ = uStar ^ (2 * gamma) := by
        congr 1
        ring
  have hleft :
      (u ^ gamma - uStar ^ gamma) ^ 2 =
        uStar ^ (2 * gamma) * (t ^ gamma - 1) ^ 2 := by
    rw [hpow_u_gamma]
    calc
      (uStar ^ gamma * t ^ gamma - uStar ^ gamma) ^ 2 =
          ((uStar ^ gamma) * (t ^ gamma - 1)) ^ 2 := by ring
      _ = ((uStar ^ gamma) * (uStar ^ gamma)) * (t ^ gamma - 1) ^ 2 := by
          ring
      _ = uStar ^ (2 * gamma) * (t ^ gamma - 1) ^ 2 := by
          rw [hpow_gamma_sq]
  have hpow_alpha_one : uStar * uStar ^ alpha = uStar ^ (alpha + 1) := by
    calc
      uStar * uStar ^ alpha = uStar ^ (1 : ℝ) * uStar ^ alpha := by
        rw [Real.rpow_one]
      _ = uStar ^ (1 + alpha) := by
        rw [← Real.rpow_add huStar]
      _ = uStar ^ (alpha + 1) := by
        congr 1
        ring
  have hpow_total :
      uStar ^ (2 * gamma - alpha - 1) * (uStar * uStar ^ alpha) =
        uStar ^ (2 * gamma) := by
    rw [hpow_alpha_one]
    calc
      uStar ^ (2 * gamma - alpha - 1) * uStar ^ (alpha + 1) =
          uStar ^ ((2 * gamma - alpha - 1) + (alpha + 1)) := by
        rw [← Real.rpow_add huStar]
      _ = uStar ^ (2 * gamma) := by
        congr 1
        ring
  have hright :
      C * uStar ^ (2 * gamma - alpha - 1) *
          ((u - uStar) * (u ^ alpha - uStar ^ alpha)) =
        uStar ^ (2 * gamma) *
          (C * ((t - 1) * (t ^ alpha - 1))) := by
    rw [hpow_u_alpha, hu_eq]
    calc
      C * uStar ^ (2 * gamma - alpha - 1) *
          ((uStar * t - uStar) *
            (uStar ^ alpha * t ^ alpha - uStar ^ alpha)) =
        C * (uStar ^ (2 * gamma - alpha - 1) *
          ((uStar * (t - 1)) * (uStar ^ alpha * (t ^ alpha - 1)))) := by
          ring
      _ = C * ((uStar ^ (2 * gamma - alpha - 1) * (uStar * uStar ^ alpha)) *
          ((t - 1) * (t ^ alpha - 1))) := by
          ring
      _ = C * (uStar ^ (2 * gamma) * ((t - 1) * (t ^ alpha - 1))) := by
          rw [hpow_total]
      _ = uStar ^ (2 * gamma) *
          (C * ((t - 1) * (t ^ alpha - 1))) := by
          ring
  have hcoeff_nonneg : 0 ≤ uStar ^ (2 * gamma) :=
    Real.rpow_nonneg huStar_nonneg _
  have hscaled :
      uStar ^ (2 * gamma) * (t ^ gamma - 1) ^ 2 ≤
        uStar ^ (2 * gamma) *
          (C * ((t - 1) * (t ^ alpha - 1))) :=
    mul_le_mul_of_nonneg_left hnorm_t hcoeff_nonneg
  calc
    (u ^ gamma - uStar ^ gamma) ^ 2 =
        uStar ^ (2 * gamma) * (t ^ gamma - 1) ^ 2 := hleft
    _ ≤ uStar ^ (2 * gamma) *
          (C * ((t - 1) * (t ^ alpha - 1))) := hscaled
    _ = C * uStar ^ (2 * gamma - alpha - 1) *
          ((u - uStar) * (u ^ alpha - uStar ^ alpha)) := hright.symm

lemma PowerDifferenceInequality.of_one_le_alpha_of_gamma_le_one
    {alpha gamma uStar : ℝ}
    (halpha : 1 ≤ alpha) (hgamma_pos : 0 < gamma) (hgamma_le : gamma ≤ 1)
    (huStar : 0 < uStar) :
    PowerDifferenceInequality 1 alpha gamma uStar := by
  intro u hu
  let t : ℝ := u / uStar
  have ht : 0 < t := div_pos hu huStar
  have hu_eq : u = uStar * t := by
    dsimp [t]
    field_simp [ne_of_gt huStar]
  have huStar_nonneg : 0 ≤ uStar := huStar.le
  have ht_nonneg : 0 ≤ t := ht.le
  have hnorm :=
    power_difference_normalized_of_one_le_alpha_of_gamma_le_one
      halpha hgamma_pos hgamma_le ht
  have hpow_u_gamma : u ^ gamma = uStar ^ gamma * t ^ gamma := by
    rw [hu_eq]
    exact Real.mul_rpow huStar_nonneg ht_nonneg
  have hpow_u_alpha : u ^ alpha = uStar ^ alpha * t ^ alpha := by
    rw [hu_eq]
    exact Real.mul_rpow huStar_nonneg ht_nonneg
  have hpow_gamma_sq : (uStar ^ gamma) * (uStar ^ gamma) = uStar ^ (2 * gamma) := by
    calc
      (uStar ^ gamma) * (uStar ^ gamma) = uStar ^ (gamma + gamma) := by
        rw [← Real.rpow_add huStar]
      _ = uStar ^ (2 * gamma) := by
        congr 1
        ring
  have hleft :
      (u ^ gamma - uStar ^ gamma) ^ 2 =
        uStar ^ (2 * gamma) * (t ^ gamma - 1) ^ 2 := by
    rw [hpow_u_gamma]
    calc
      (uStar ^ gamma * t ^ gamma - uStar ^ gamma) ^ 2 =
          ((uStar ^ gamma) * (t ^ gamma - 1)) ^ 2 := by ring
      _ = ((uStar ^ gamma) * (uStar ^ gamma)) * (t ^ gamma - 1) ^ 2 := by
          ring
      _ = uStar ^ (2 * gamma) * (t ^ gamma - 1) ^ 2 := by
          rw [hpow_gamma_sq]
  have hpow_alpha_one : uStar * uStar ^ alpha = uStar ^ (alpha + 1) := by
    calc
      uStar * uStar ^ alpha = uStar ^ (1 : ℝ) * uStar ^ alpha := by
        rw [Real.rpow_one]
      _ = uStar ^ (1 + alpha) := by
        rw [← Real.rpow_add huStar]
      _ = uStar ^ (alpha + 1) := by
        congr 1
        ring
  have hpow_total :
      uStar ^ (2 * gamma - alpha - 1) * (uStar * uStar ^ alpha) =
        uStar ^ (2 * gamma) := by
    rw [hpow_alpha_one]
    calc
      uStar ^ (2 * gamma - alpha - 1) * uStar ^ (alpha + 1) =
          uStar ^ ((2 * gamma - alpha - 1) + (alpha + 1)) := by
        rw [← Real.rpow_add huStar]
      _ = uStar ^ (2 * gamma) := by
        congr 1
        ring
  have hright :
      1 * uStar ^ (2 * gamma - alpha - 1) *
          ((u - uStar) * (u ^ alpha - uStar ^ alpha)) =
        uStar ^ (2 * gamma) * ((t - 1) * (t ^ alpha - 1)) := by
    rw [hpow_u_alpha, hu_eq]
    calc
      1 * uStar ^ (2 * gamma - alpha - 1) *
          ((uStar * t - uStar) *
            (uStar ^ alpha * t ^ alpha - uStar ^ alpha)) =
        uStar ^ (2 * gamma - alpha - 1) *
          ((uStar * (t - 1)) * (uStar ^ alpha * (t ^ alpha - 1))) := by
          ring
      _ = (uStar ^ (2 * gamma - alpha - 1) * (uStar * uStar ^ alpha)) *
          ((t - 1) * (t ^ alpha - 1)) := by
          ring
      _ = uStar ^ (2 * gamma) * ((t - 1) * (t ^ alpha - 1)) := by
          rw [hpow_total]
  have hcoeff_nonneg : 0 ≤ uStar ^ (2 * gamma) :=
    Real.rpow_nonneg huStar_nonneg _
  have hscaled :
      uStar ^ (2 * gamma) * (t ^ gamma - 1) ^ 2 ≤
        uStar ^ (2 * gamma) * ((t - 1) * (t ^ alpha - 1)) :=
    mul_le_mul_of_nonneg_left hnorm hcoeff_nonneg
  calc
    (u ^ gamma - uStar ^ gamma) ^ 2 =
        uStar ^ (2 * gamma) * (t ^ gamma - 1) ^ 2 := hleft
    _ ≤ uStar ^ (2 * gamma) * ((t - 1) * (t ^ alpha - 1)) := hscaled
    _ = 1 * uStar ^ (2 * gamma - alpha - 1) *
          ((u - uStar) * (u ^ alpha - uStar ^ alpha)) := hright.symm

lemma PowerDifferenceInequality.CAlphaGamma_of_lt_alpha
    {alpha gamma uStar : ℝ}
    (halpha_pos : 0 < alpha) (halpha_lt : alpha < 1)
    (hgamma_pos : 0 < gamma) (hrel : 2 * gamma ≤ alpha + 1)
    (huStar : 0 < uStar) :
    PowerDifferenceInequality (CAlphaGamma alpha gamma) alpha gamma uStar := by
  intro u hu
  let C : ℝ := (alpha + 1) ^ 2 / (4 * alpha)
  let t : ℝ := u / uStar
  have hC_eq : CAlphaGamma alpha gamma = C := by
    unfold CAlphaGamma C
    rw [if_pos halpha_lt]
  have ht : 0 < t := div_pos hu huStar
  have hu_eq : u = uStar * t := by
    dsimp [t]
    field_simp [ne_of_gt huStar]
  have huStar_nonneg : 0 ≤ uStar := huStar.le
  have ht_nonneg : 0 ≤ t := ht.le
  have hnorm :
      (t ^ gamma - 1) ^ 2 ≤ C * ((t - 1) * (t ^ alpha - 1)) := by
    dsimp [C]
    exact power_difference_normalized_of_lt_alpha
      halpha_pos halpha_lt hgamma_pos hrel ht
  have hpow_u_gamma : u ^ gamma = uStar ^ gamma * t ^ gamma := by
    rw [hu_eq]
    exact Real.mul_rpow huStar_nonneg ht_nonneg
  have hpow_u_alpha : u ^ alpha = uStar ^ alpha * t ^ alpha := by
    rw [hu_eq]
    exact Real.mul_rpow huStar_nonneg ht_nonneg
  have hpow_gamma_sq : (uStar ^ gamma) * (uStar ^ gamma) = uStar ^ (2 * gamma) := by
    calc
      (uStar ^ gamma) * (uStar ^ gamma) = uStar ^ (gamma + gamma) := by
        rw [← Real.rpow_add huStar]
      _ = uStar ^ (2 * gamma) := by
        congr 1
        ring
  have hleft :
      (u ^ gamma - uStar ^ gamma) ^ 2 =
        uStar ^ (2 * gamma) * (t ^ gamma - 1) ^ 2 := by
    rw [hpow_u_gamma]
    calc
      (uStar ^ gamma * t ^ gamma - uStar ^ gamma) ^ 2 =
          ((uStar ^ gamma) * (t ^ gamma - 1)) ^ 2 := by ring
      _ = ((uStar ^ gamma) * (uStar ^ gamma)) * (t ^ gamma - 1) ^ 2 := by
          ring
      _ = uStar ^ (2 * gamma) * (t ^ gamma - 1) ^ 2 := by
          rw [hpow_gamma_sq]
  have hpow_alpha_one : uStar * uStar ^ alpha = uStar ^ (alpha + 1) := by
    calc
      uStar * uStar ^ alpha = uStar ^ (1 : ℝ) * uStar ^ alpha := by
        rw [Real.rpow_one]
      _ = uStar ^ (1 + alpha) := by
        rw [← Real.rpow_add huStar]
      _ = uStar ^ (alpha + 1) := by
        congr 1
        ring
  have hpow_total :
      uStar ^ (2 * gamma - alpha - 1) * (uStar * uStar ^ alpha) =
        uStar ^ (2 * gamma) := by
    rw [hpow_alpha_one]
    calc
      uStar ^ (2 * gamma - alpha - 1) * uStar ^ (alpha + 1) =
          uStar ^ ((2 * gamma - alpha - 1) + (alpha + 1)) := by
        rw [← Real.rpow_add huStar]
      _ = uStar ^ (2 * gamma) := by
        congr 1
        ring
  have hright :
      C * uStar ^ (2 * gamma - alpha - 1) *
          ((u - uStar) * (u ^ alpha - uStar ^ alpha)) =
        uStar ^ (2 * gamma) * (C * ((t - 1) * (t ^ alpha - 1))) := by
    rw [hpow_u_alpha, hu_eq]
    calc
      C * uStar ^ (2 * gamma - alpha - 1) *
          ((uStar * t - uStar) *
            (uStar ^ alpha * t ^ alpha - uStar ^ alpha)) =
        C * uStar ^ (2 * gamma - alpha - 1) *
          ((uStar * (t - 1)) * (uStar ^ alpha * (t ^ alpha - 1))) := by
          ring
      _ = C * (uStar ^ (2 * gamma - alpha - 1) *
            (uStar * uStar ^ alpha)) *
          ((t - 1) * (t ^ alpha - 1)) := by
          ring
      _ = uStar ^ (2 * gamma) * (C * ((t - 1) * (t ^ alpha - 1))) := by
          rw [hpow_total]
          ring
  have hcoeff_nonneg : 0 ≤ uStar ^ (2 * gamma) :=
    Real.rpow_nonneg huStar_nonneg _
  have hscaled :
      uStar ^ (2 * gamma) * (t ^ gamma - 1) ^ 2 ≤
        uStar ^ (2 * gamma) * (C * ((t - 1) * (t ^ alpha - 1))) :=
    mul_le_mul_of_nonneg_left hnorm hcoeff_nonneg
  calc
    (u ^ gamma - uStar ^ gamma) ^ 2 =
        uStar ^ (2 * gamma) * (t ^ gamma - 1) ^ 2 := hleft
    _ ≤ uStar ^ (2 * gamma) * (C * ((t - 1) * (t ^ alpha - 1))) := hscaled
    _ = C * uStar ^ (2 * gamma - alpha - 1) *
          ((u - uStar) * (u ^ alpha - uStar ^ alpha)) := hright.symm
    _ = CAlphaGamma alpha gamma * uStar ^ (2 * gamma - alpha - 1) *
          ((u - uStar) * (u ^ alpha - uStar ^ alpha)) := by rw [hC_eq]

lemma PowerDifferenceInequality.CAlphaGamma_of_one_le_alpha_of_gamma_le_one
    {alpha gamma uStar : ℝ}
    (halpha : 1 ≤ alpha) (hgamma_pos : 0 < gamma) (hgamma_le : gamma ≤ 1)
    (huStar : 0 < uStar) :
    PowerDifferenceInequality (CAlphaGamma alpha gamma) alpha gamma uStar := by
  have hC : CAlphaGamma alpha gamma = 1 := by
    unfold CAlphaGamma
    rw [if_neg (not_lt_of_ge halpha), if_pos hgamma_le]
  simpa [hC] using
    PowerDifferenceInequality.of_one_le_alpha_of_gamma_le_one
      halpha hgamma_pos hgamma_le huStar

lemma PowerDifferenceInequality.of_one_le_alpha_of_one_lt_gamma
    {alpha gamma uStar : ℝ}
    (halpha : 1 ≤ alpha) (hgamma : 1 < gamma)
    (hrel : 2 * gamma ≤ alpha + 1) (huStar : 0 < uStar) :
    PowerDifferenceInequality (gamma ^ 2 / (2 * gamma - 1))
      alpha gamma uStar := by
  exact PowerDifferenceInequality.of_normalized
    (fun t ht =>
      power_difference_normalized_of_one_le_alpha_of_one_lt_gamma
        halpha hgamma hrel ht)
    huStar

lemma PowerDifferenceInequality.CAlphaGamma_of_one_le_alpha_of_one_lt_gamma
    {alpha gamma uStar : ℝ}
    (halpha : 1 ≤ alpha) (hgamma : 1 < gamma)
    (hrel : 2 * gamma ≤ alpha + 1) (huStar : 0 < uStar) :
    PowerDifferenceInequality (CAlphaGamma alpha gamma) alpha gamma uStar := by
  have hC : CAlphaGamma alpha gamma = gamma ^ 2 / (2 * gamma - 1) := by
    unfold CAlphaGamma
    rw [if_neg (not_lt_of_ge halpha), if_neg (not_le_of_gt hgamma)]
  simpa [hC] using
    PowerDifferenceInequality.of_one_le_alpha_of_one_lt_gamma
      halpha hgamma hrel huStar

lemma PowerDifferenceInequality.of_alpha_lt_one
    {alpha gamma uStar : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hgamma0 : 0 < gamma) (hrel : 2 * gamma ≤ alpha + 1)
    (huStar : 0 < uStar) :
    PowerDifferenceInequality ((alpha + 1) ^ 2 / (4 * alpha))
      alpha gamma uStar := by
  exact PowerDifferenceInequality.of_normalized
    (fun t ht =>
      power_difference_normalized_of_lt_alpha
        halpha0 halpha1 hgamma0 hrel ht)
    huStar

lemma PowerDifferenceInequality.CAlphaGamma_of_alpha_lt_one
    {alpha gamma uStar : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hgamma0 : 0 < gamma) (hrel : 2 * gamma ≤ alpha + 1)
    (huStar : 0 < uStar) :
    PowerDifferenceInequality (CAlphaGamma alpha gamma) alpha gamma uStar := by
  have hC : CAlphaGamma alpha gamma = (alpha + 1) ^ 2 / (4 * alpha) := by
    unfold CAlphaGamma
    rw [if_pos halpha1]
  simpa [hC] using
    PowerDifferenceInequality.of_alpha_lt_one
      halpha0 halpha1 hgamma0 hrel huStar

def Lemma_A_6 : Prop :=
  ∀ alpha gamma,
    0 < alpha → 0 < gamma →
      2 * gamma ≤ alpha + 1 →
        ∀ uStar > 0,
          PowerDifferenceInequality (CAlphaGamma alpha gamma) alpha gamma uStar

lemma Lemma_A_6_proved : Lemma_A_6 := by
  intro alpha gamma halpha hgamma hrel uStar huStar
  by_cases halpha_lt : alpha < 1
  · exact PowerDifferenceInequality.CAlphaGamma_of_alpha_lt_one
      halpha halpha_lt hgamma hrel huStar
  · have halpha_ge : 1 ≤ alpha := le_of_not_gt halpha_lt
    by_cases hgamma_le : gamma ≤ 1
    · exact PowerDifferenceInequality.CAlphaGamma_of_one_le_alpha_of_gamma_le_one
        halpha_ge hgamma hgamma_le huStar
    · exact PowerDifferenceInequality.CAlphaGamma_of_one_le_alpha_of_one_lt_gamma
        halpha_ge (lt_of_not_ge hgamma_le) hrel huStar

lemma Lemma_A_6.alpha_lt_one_branch
    {alpha gamma uStar : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hgamma0 : 0 < gamma) (hrel : 2 * gamma ≤ alpha + 1)
    (huStar : 0 < uStar) :
    PowerDifferenceInequality (CAlphaGamma alpha gamma) alpha gamma uStar :=
  PowerDifferenceInequality.CAlphaGamma_of_alpha_lt_one
    halpha0 halpha1 hgamma0 hrel huStar

lemma Lemma_A_6.power_difference
    (h : Lemma_A_6)
    {alpha gamma uStar : ℝ}
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hrel : 2 * gamma ≤ alpha + 1) (huStar : 0 < uStar) :
    PowerDifferenceInequality (CAlphaGamma alpha gamma) alpha gamma uStar :=
  h alpha gamma halpha hgamma hrel uStar huStar

lemma Lemma_A_6.apply
    (h : Lemma_A_6)
    {alpha gamma uStar u : ℝ}
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hrel : 2 * gamma ≤ alpha + 1)
    (huStar : 0 < uStar) (hu : 0 < u) :
    (u ^ gamma - uStar ^ gamma) ^ 2 ≤
      CAlphaGamma alpha gamma * uStar ^ (2 * gamma - alpha - 1) *
        ((u - uStar) * (u ^ alpha - uStar ^ alpha)) :=
  (h.power_difference halpha hgamma hrel huStar).apply hu

def Lemma_A_7
    (D : BoundedDomainData) (p : CM2Params)
    (C : Paper3Constants D p) : Prop :=
  0 ≤ p.β → 1 ≤ p.m →
    ∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      (p.α + 1 ≥ 2 * p.γ →
        C.chiStrong1 eq.1 ≤ C.chiCritical eq.1) ∧
      (1 ≤ p.β → p.α + 1 ≥ 2 * p.γ →
        C.chiStrong2 eq.1 ≤ C.chiCritical eq.1) ∧
      (1 ≤ p.γ → p.α + 1 ≥ p.m + p.γ →
        C.chiStrong3 eq.1 ≤ C.chiCritical eq.1) ∧
      (1 ≤ p.β → 1 ≤ p.γ → p.α + 1 ≥ p.m + 2 * p.γ →
        C.chiStrong4 eq.1 ≤ C.chiCritical eq.1)

lemma Lemma_A_7.chiStrong1_le
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (h : Lemma_A_7 D p C)
    (hβ0 : 0 ≤ p.β) (hm : 1 ≤ p.m)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hαγ : p.α + 1 ≥ 2 * p.γ) :
    C.chiStrong1 (positiveEquilibrium p ⟨ha, hb⟩).1 ≤
      C.chiCritical (positiveEquilibrium p ⟨ha, hb⟩).1 :=
  ((h hβ0 hm ha hb).1 hαγ)

lemma Lemma_A_7.chiStrong2_le
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (h : Lemma_A_7 D p C)
    (hβ0 : 0 ≤ p.β) (hm : 1 ≤ p.m)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hβ1 : 1 ≤ p.β) (hαγ : p.α + 1 ≥ 2 * p.γ) :
    C.chiStrong2 (positiveEquilibrium p ⟨ha, hb⟩).1 ≤
      C.chiCritical (positiveEquilibrium p ⟨ha, hb⟩).1 :=
  ((h hβ0 hm ha hb).2.1 hβ1 hαγ)

lemma Lemma_A_7.chiStrong3_le
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (h : Lemma_A_7 D p C)
    (hβ0 : 0 ≤ p.β) (hm : 1 ≤ p.m)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ : 1 ≤ p.γ) (hαγ : p.α + 1 ≥ p.m + p.γ) :
    C.chiStrong3 (positiveEquilibrium p ⟨ha, hb⟩).1 ≤
      C.chiCritical (positiveEquilibrium p ⟨ha, hb⟩).1 :=
  ((h hβ0 hm ha hb).2.2.1 hγ hαγ)

lemma Lemma_A_7.chiStrong4_le
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (h : Lemma_A_7 D p C)
    (hβ0 : 0 ≤ p.β) (hm : 1 ≤ p.m)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hβ1 : 1 ≤ p.β) (hγ : 1 ≤ p.γ)
    (hαγ : p.α + 1 ≥ p.m + 2 * p.γ) :
    C.chiStrong4 (positiveEquilibrium p ⟨ha, hb⟩).1 ≤
      C.chiCritical (positiveEquilibrium p ⟨ha, hb⟩).1 :=
  ((h hβ0 hm ha hb).2.2.2 hβ1 hγ hαγ)

def Lemma_A_8
    (D : BoundedDomainData) (p : CM2Params)
    (C : Paper3Constants D p) : Prop :=
  p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
    ∀ uStar > 0,
      (0 < p.γ → C.chiMinimal1 uStar ≤ C.chiCritical uStar) ∧
      (p.γ = 1 → C.chiMinimal2 uStar ≤ C.chiCritical uStar)

lemma Lemma_A_8.chiMinimal1_le
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (h : Lemma_A_8 D p C)
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar) (hγ : 0 < p.γ) :
    C.chiMinimal1 uStar ≤ C.chiCritical uStar :=
  (h ha hb hm hβ uStar huStar).1 hγ

lemma Lemma_A_8.chiMinimal2_le
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (h : Lemma_A_8 D p C)
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar) (hγ : p.γ = 1) :
    C.chiMinimal2 uStar ≤ C.chiCritical uStar :=
  (h ha hb hm hβ uStar huStar).2 hγ

lemma Lemma_A_7.nonminimal_condition_chi_lt_critical
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (h : Lemma_A_7 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hcond :
      NonminimalGlobalStabilityCondition D p C
        (positiveEquilibrium p ⟨ha, hb⟩).1) :
    p.χ₀ < C.chiCritical (positiveEquilibrium p ⟨ha, hb⟩).1 := by
  rcases hcond with h1 | h2 | h3 | h4
  · rcases h1 with ⟨hm, hαγ, _hχ0, hχ⟩
    exact lt_of_lt_of_le hχ
      (h.chiStrong1_le p.hβ hm ha hb hαγ)
  · rcases h2 with ⟨hm, hβ, hαγ, _hχ0, hχ⟩
    exact lt_of_lt_of_le hχ
      (h.chiStrong2_le p.hβ hm ha hb hβ hαγ)
  · rcases h3 with ⟨hm, hγ, hαγ, hχ⟩
    have hbase :
        p.m + p.γ ≤
          p.m + p.γ + (if p.β = 0 then 0 else p.γ) := by
      by_cases hβzero : p.β = 0
      · rw [if_pos hβzero, add_zero]
      · rw [if_neg hβzero]
        exact le_add_of_nonneg_right p.hγ.le
    exact lt_of_lt_of_le hχ
      (h.chiStrong3_le p.hβ hm ha hb hγ (le_trans hbase hαγ))
  · rcases h4 with ⟨hm, hβ, hγ, hαγ, hχ⟩
    exact lt_of_lt_of_le hχ
      (h.chiStrong4_le p.hβ hm ha hb hβ hγ hαγ)

lemma Lemma_A_8.minimal_condition_chi_lt_critical
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    (h : Lemma_A_8 D p C)
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hcond : MinimalGlobalStabilityCondition D p C uStar) :
    p.χ₀ < C.chiCritical uStar := by
  rcases hcond with h1 | h2
  · exact lt_of_lt_of_le h1.2
      (h.chiMinimal1_le ha hb hm hβ huStar p.hγ)
  · exact lt_of_lt_of_le h2.2.2
      (h.chiMinimal2_le ha hb hm hβ huStar h2.1)

lemma Lemma_A_7.nonminimal_condition_linearlyStable_of_critical_spectrum
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    {S : SpectralData}
    (h : Lemma_A_7 D p C) (H : HasNeumannSpectrum S)
    (hC : Paper3ConstantsUsesCriticalSpectrum S p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hcond :
      NonminimalGlobalStabilityCondition D p C
        (positiveEquilibrium p ⟨ha, hb⟩).1) :
    LinearlyStable S p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  exact hC.positiveEquilibrium_linearlyStable H ha hb
    (h.nonminimal_condition_chi_lt_critical ha hb hcond)

lemma Lemma_A_8.minimal_condition_linearlyStable_of_critical_spectrum
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    {S : SpectralData}
    (h : Lemma_A_8 D p C) (H : HasNeumannSpectrum S)
    (hC : Paper3ConstantsUsesCriticalSpectrum S p C)
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hcond : MinimalGlobalStabilityCondition D p C uStar) :
    LinearlyStable S p
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 := by
  exact hC.minimalEquilibrium_linearlyStable H huStar
    (h.minimal_condition_chi_lt_critical ha hb hm hβ huStar hcond)

lemma Lemma_A_7.chiStrong1_linearlyStable_of_critical_spectrum
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    {S : SpectralData}
    (h : Lemma_A_7 D p C) (H : HasNeumannSpectrum S)
    (hC : Paper3ConstantsUsesCriticalSpectrum S p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m) (hαγ : 2 * p.γ ≤ p.α + 1)
    (hχ0 : 0 < p.χ₀)
    (hχ : p.χ₀ < C.chiStrong1 (positiveEquilibrium p ⟨ha, hb⟩).1) :
    LinearlyStable S p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  h.nonminimal_condition_linearlyStable_of_critical_spectrum H hC ha hb
    (NonminimalGlobalStabilityCondition.of_chiStrong1 hm hαγ hχ0 hχ)

lemma Lemma_A_7.chiStrong2_linearlyStable_of_critical_spectrum
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    {S : SpectralData}
    (h : Lemma_A_7 D p C) (H : HasNeumannSpectrum S)
    (hC : Paper3ConstantsUsesCriticalSpectrum S p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m) (hβ : 1 ≤ p.β)
    (hαγ : 2 * p.γ ≤ p.α + 1)
    (hχ0 : 0 < p.χ₀)
    (hχ : p.χ₀ < C.chiStrong2 (positiveEquilibrium p ⟨ha, hb⟩).1) :
    LinearlyStable S p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  h.nonminimal_condition_linearlyStable_of_critical_spectrum H hC ha hb
    (NonminimalGlobalStabilityCondition.of_chiStrong2 hm hβ hαγ hχ0 hχ)

lemma Lemma_A_7.chiStrong3_linearlyStable_of_critical_spectrum
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    {S : SpectralData}
    (h : Lemma_A_7 D p C) (H : HasNeumannSpectrum S)
    (hC : Paper3ConstantsUsesCriticalSpectrum S p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m) (hγ : 1 ≤ p.γ)
    (hαγ :
      p.m + p.γ + (if p.β = 0 then 0 else p.γ) ≤ p.α + 1)
    (hχ : p.χ₀ < C.chiStrong3 (positiveEquilibrium p ⟨ha, hb⟩).1) :
    LinearlyStable S p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  h.nonminimal_condition_linearlyStable_of_critical_spectrum H hC ha hb
    (NonminimalGlobalStabilityCondition.of_chiStrong3 hm hγ hαγ hχ)

lemma Lemma_A_7.chiStrong4_linearlyStable_of_critical_spectrum
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    {S : SpectralData}
    (h : Lemma_A_7 D p C) (H : HasNeumannSpectrum S)
    (hC : Paper3ConstantsUsesCriticalSpectrum S p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m) (hβ : 1 ≤ p.β) (hγ : 1 ≤ p.γ)
    (hαγ : p.m + 2 * p.γ ≤ p.α + 1)
    (hχ : p.χ₀ < C.chiStrong4 (positiveEquilibrium p ⟨ha, hb⟩).1) :
    LinearlyStable S p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  h.nonminimal_condition_linearlyStable_of_critical_spectrum H hC ha hb
    (NonminimalGlobalStabilityCondition.of_chiStrong4 hm hβ hγ hαγ hχ)

lemma Lemma_A_8.chiMinimal1_linearlyStable_of_critical_spectrum
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    {S : SpectralData}
    (h : Lemma_A_8 D p C) (H : HasNeumannSpectrum S)
    (hC : Paper3ConstantsUsesCriticalSpectrum S p C)
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hχ0 : 0 < p.χ₀) (hχ : p.χ₀ < C.chiMinimal1 uStar) :
    LinearlyStable S p
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 :=
  h.minimal_condition_linearlyStable_of_critical_spectrum H hC ha hb hm hβ
    huStar (MinimalGlobalStabilityCondition.of_chiMinimal1 hχ0 hχ)

lemma Lemma_A_8.chiMinimal2_linearlyStable_of_critical_spectrum
    {D : BoundedDomainData} {p : CM2Params} {C : Paper3Constants D p}
    {S : SpectralData}
    (h : Lemma_A_8 D p C) (H : HasNeumannSpectrum S)
    (hC : Paper3ConstantsUsesCriticalSpectrum S p C)
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hγ : p.γ = 1) (hχ0 : 0 < p.χ₀)
    (hχ : p.χ₀ < C.chiMinimal2 uStar) :
    LinearlyStable S p
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 :=
  h.minimal_condition_linearlyStable_of_critical_spectrum H hC ha hb hm hβ
    huStar (MinimalGlobalStabilityCondition.of_chiMinimal2 hγ hχ0 hχ)

/-- The linear-stability part of Paper3 Theorem 2.4, proved directly from the
A.7 threshold comparison and the critical-spectrum identification.  The global
stability and exponential convergence conclusions remain analytic package
fields. -/
def Theorem_2_4_linear_stability_branch : Prop :=
  ∀ (D : BoundedDomainData) (S : SpectralData) (p : CM2Params)
    (C : Paper3Constants D p),
    HasNeumannSpectrum S → Paper3ConstantsUsesCriticalSpectrum S p C →
      Lemma_A_7 D p C →
        ∀ (ha : 0 < p.a) (hb : 0 < p.b),
          let eq := positiveEquilibrium p ⟨ha, hb⟩
          NonminimalGlobalStabilityCondition D p C eq.1 →
            LinearlyStable S p eq.1 eq.2

lemma Theorem_2_4_linear_stability_branch_proved :
    Theorem_2_4_linear_stability_branch := by
  intro D S p C H hC hA7 ha hb
  dsimp
  intro hcond
  exact hA7.nonminimal_condition_linearlyStable_of_critical_spectrum
    H hC ha hb hcond

/-- The linear-stability part of Paper3 Theorem 2.5, proved directly from the
A.8 threshold comparison and the critical-spectrum identification.  The global
stability and exponential convergence conclusions remain analytic package
fields. -/
def Theorem_2_5_linear_stability_branch : Prop :=
  ∀ (D : BoundedDomainData) (S : SpectralData) (p : CM2Params)
    (C : Paper3Constants D p),
    HasNeumannSpectrum S → Paper3ConstantsUsesCriticalSpectrum S p C →
      Lemma_A_8 D p C →
        p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
          ∀ uStar > 0,
            MinimalGlobalStabilityCondition D p C uStar →
              LinearlyStable S p
                (minimalEquilibrium p uStar).1
                (minimalEquilibrium p uStar).2

lemma Theorem_2_5_linear_stability_branch_proved :
    Theorem_2_5_linear_stability_branch := by
  intro D S p C H hC hA8 ha hb hm hβ uStar huStar hcond
  exact hA8.minimal_condition_linearlyStable_of_critical_spectrum
    H hC ha hb hm hβ huStar hcond

/-- Formula-level linear-stability part of Paper3 Theorem 2.4.  This version
uses the explicit strong thresholds and the paper critical-sensitivity
infimum directly, with no `Paper3Constants` and no Lemma A.7 package field. -/
def Theorem_2_4_linear_stability_formula_branch : Prop :=
  ∀ (S : SpectralData) (p : CM2Params),
    HasNeumannSpectrum S →
      ∀ (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        max
            (max (chiStrong1Formula p eq.1 eq.2)
              (chiStrong2Formula p eq.1))
            (max (chiStrong3Formula p M0 eq.1 eq.2)
              (chiStrong4Formula p M0 eq.1)) ≤
          paperCriticalSensitivity S p eq.1 eq.2 →
          NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
            LinearlyStable S p eq.1 eq.2

lemma Theorem_2_4_linear_stability_formula_branch_proved :
    Theorem_2_4_linear_stability_formula_branch := by
  intro S p H ha hb M0
  dsimp
  intro hcritical hcond
  exact hcond.linearlyStable_of_max_threshold_le_critical S p H ha hb
    hcritical

/-- First-mode sufficient version of the formula-level Theorem 2.4 linear
stability branch. -/
def Theorem_2_4_linear_stability_first_mode_branch : Prop :=
  ∀ (S : SpectralData) (p : CM2Params),
    HasNeumannSpectrum S →
      ∀ (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        max
            (max (chiStrong1Formula p eq.1 eq.2)
              (chiStrong2Formula p eq.1))
            (max (chiStrong3Formula p M0 eq.1 eq.2)
              (chiStrong4Formula p M0 eq.1)) ≤
          ((1 + eq.2) ^ p.β /
              (p.ν * p.γ * eq.1 ^ (p.m + p.γ - 1))) *
            (p.μ + S.firstNonzero) →
          NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
            LinearlyStable S p eq.1 eq.2

lemma Theorem_2_4_linear_stability_first_mode_branch_proved :
    Theorem_2_4_linear_stability_first_mode_branch := by
  intro S p H ha hb M0
  dsimp
  intro hfirst hcond
  exact hcond.linearlyStable_of_firstNonzero_lower S p H ha hb hfirst

lemma Theorem_2_4_linear_stability_formula_unitInterval
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    max
        (max (chiStrong1Formula p eq.1 eq.2)
          (chiStrong2Formula p eq.1))
        (max (chiStrong3Formula p M0 eq.1 eq.2)
          (chiStrong4Formula p M0 eq.1)) ≤
      paperCriticalSensitivity unitIntervalNeumannSpectrum p eq.1 eq.2 →
      NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
        LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 := by
  dsimp
  intro hcritical hcond
  exact hcond.linearlyStable_of_max_threshold_le_critical
    unitIntervalNeumannSpectrum p unitIntervalNeumannSpectrum_hasNeumannSpectrum
    ha hb hcritical

lemma Theorem_2_4_linear_stability_first_mode_unitInterval
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    max
        (max (chiStrong1Formula p eq.1 eq.2)
          (chiStrong2Formula p eq.1))
        (max (chiStrong3Formula p M0 eq.1 eq.2)
          (chiStrong4Formula p M0 eq.1)) ≤
      ((1 + eq.2) ^ p.β /
          (p.ν * p.γ * eq.1 ^ (p.m + p.γ - 1))) *
        (p.μ + Real.pi ^ 2) →
      NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
        LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 := by
  dsimp
  intro hfirst hcond
  exact hcond.linearlyStable_of_firstNonzero_lower
    unitIntervalNeumannSpectrum p unitIntervalNeumannSpectrum_hasNeumannSpectrum
    ha hb hfirst

/-- Formula-level linear-stability part of Paper3 Theorem 2.5.  This version
uses the explicit minimal thresholds and the paper critical-sensitivity
infimum directly, with no `Paper3Constants` and no Lemma A.8 package field. -/
def Theorem_2_5_linear_stability_formula_branch : Prop :=
  ∀ (S : SpectralData) (p : CM2Params),
    HasNeumannSpectrum S →
      p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
        ∀ uStar > 0, ∀ uBar vLower : ℝ,
          chiBeta p ≤
            paperCriticalSensitivity S p
              (minimalEquilibrium p uStar).1
              (minimalEquilibrium p uStar).2 →
            MinimalGlobalStabilityFormulaCondition p uStar uBar vLower →
              LinearlyStable S p
                (minimalEquilibrium p uStar).1
                (minimalEquilibrium p uStar).2

lemma Theorem_2_5_linear_stability_formula_branch_proved :
    Theorem_2_5_linear_stability_formula_branch := by
  intro S p H _ha _hb _hm hβ uStar huStar uBar vLower hcritical hcond
  exact hcond.linearlyStable_of_chiBeta_le_critical S p H hβ huStar
    hcritical

/-- First-mode sufficient version of the formula-level Theorem 2.5 linear
stability branch. -/
def Theorem_2_5_linear_stability_first_mode_branch : Prop :=
  ∀ (S : SpectralData) (p : CM2Params),
    HasNeumannSpectrum S →
      p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
        ∀ uStar > 0, ∀ uBar vLower : ℝ,
          chiBeta p ≤
            ((1 + (minimalEquilibrium p uStar).2) ^ p.β /
                (p.ν * p.γ *
                  (minimalEquilibrium p uStar).1 ^ (p.m + p.γ - 1))) *
              (p.μ + S.firstNonzero) →
            MinimalGlobalStabilityFormulaCondition p uStar uBar vLower →
              LinearlyStable S p
                (minimalEquilibrium p uStar).1
                (minimalEquilibrium p uStar).2

lemma Theorem_2_5_linear_stability_first_mode_branch_proved :
    Theorem_2_5_linear_stability_first_mode_branch := by
  intro S p H _ha _hb _hm hβ uStar huStar uBar vLower hfirst hcond
  exact hcond.linearlyStable_of_firstNonzero_lower S p H hβ huStar hfirst

lemma Theorem_2_5_linear_stability_formula_unitInterval
    (p : CM2Params)
    (_ha : p.a = 0) (_hb : p.b = 0) (_hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar) (uBar vLower : ℝ) :
    chiBeta p ≤
      paperCriticalSensitivity unitIntervalNeumannSpectrum p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 →
      MinimalGlobalStabilityFormulaCondition p uStar uBar vLower →
        LinearlyStable unitIntervalNeumannSpectrum p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2 := by
  intro hcritical hcond
  exact hcond.linearlyStable_of_chiBeta_le_critical
    unitIntervalNeumannSpectrum p unitIntervalNeumannSpectrum_hasNeumannSpectrum
    hβ huStar hcritical

lemma Theorem_2_5_linear_stability_first_mode_unitInterval
    (p : CM2Params)
    (_ha : p.a = 0) (_hb : p.b = 0) (_hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar) (uBar vLower : ℝ) :
    chiBeta p ≤
      ((1 + (minimalEquilibrium p uStar).2) ^ p.β /
          (p.ν * p.γ *
            (minimalEquilibrium p uStar).1 ^ (p.m + p.γ - 1))) *
        (p.μ + Real.pi ^ 2) →
      MinimalGlobalStabilityFormulaCondition p uStar uBar vLower →
        LinearlyStable unitIntervalNeumannSpectrum p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2 := by
  intro hfirst hcond
  exact hcond.linearlyStable_of_firstNonzero_lower
    unitIntervalNeumannSpectrum p unitIntervalNeumannSpectrum_hasNeumannSpectrum
    hβ huStar hfirst

/-- Formula-level negative-sensitivity bridge for Paper3 Theorem 2.3 at the
positive equilibrium.  The spectral stability is direct from `χ₀ ≤ 0`; the
mass-constrained local exponential conclusion is an explicit sectorial-style
input, rather than a `Paper3Constants` package field. -/
def Theorem_2_3_negative_sensitivity_convergence_formula_branch : Prop :=
  ∀ (D : BoundedDomainData) (S : SpectralData) (p : CM2Params)
    (N : StabilityNorms D),
    HasNeumannSpectrum S → p.χ₀ ≤ 0 →
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        (LinearlyStable S p eq.1 eq.2 →
          MassConstrainedLocallyExponentiallyStableFromSup D p N eq.1 eq.2) →
          LinearlyStable S p eq.1 eq.2 ∧
          MassConstrainedLocallyExponentiallyStableFromSup D p N eq.1 eq.2

lemma Theorem_2_3_negative_sensitivity_convergence_formula_branch_proved :
    Theorem_2_3_negative_sensitivity_convergence_formula_branch := by
  intro D S p N H hχ ha hb
  dsimp
  intro hsectorial
  have hstable :
      LinearlyStable S p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 :=
    positiveEquilibrium_linearlyStable_of_chi_nonpos_neumann S p H hχ ha hb
  exact ⟨hstable, hsectorial hstable⟩

/-- Direct theorem-shaped version of the negative-sensitivity convergence
bridge for Paper3 Theorem 2.3.  The local exponential step remains the
explicit supplied consequence of the proved linear stability. -/
theorem Theorem_2_3_negative_sensitivity_convergence_formula_branch_direct
    (D : BoundedDomainData) (S : SpectralData) (p : CM2Params)
    (N : StabilityNorms D)
    (H : HasNeumannSpectrum S) (hχ : p.χ₀ ≤ 0)
    (ha : 0 < p.a) (hb : 0 < p.b) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    (LinearlyStable S p eq.1 eq.2 →
      MassConstrainedLocallyExponentiallyStableFromSup D p N eq.1 eq.2) →
      LinearlyStable S p eq.1 eq.2 ∧
      MassConstrainedLocallyExponentiallyStableFromSup D p N eq.1 eq.2 := by
  dsimp
  intro hsectorial
  have hstable :
      LinearlyStable S p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 :=
    positiveEquilibrium_linearlyStable_of_chi_nonpos_neumann S p H hχ ha hb
  exact ⟨hstable, hsectorial hstable⟩

lemma Theorem_2_3_negative_sensitivity_convergence_unitInterval
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    (LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 →
      MassConstrainedLocallyExponentiallyStableFromSup D p N eq.1 eq.2) →
      LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 ∧
      MassConstrainedLocallyExponentiallyStableFromSup D p N eq.1 eq.2 := by
  dsimp
  intro hsectorial
  have hstable :=
    unitInterval_positiveEquilibrium_linearlyStable_of_chi_nonpos p hχ ha hb
  exact ⟨hstable, hsectorial hstable⟩

/-- Formula-level full stability bridge for Paper3 Theorem 2.4.  The linear
part uses the explicit strong thresholds and `paperCriticalSensitivity`; the
local exponential part is supplied explicitly as a sectorial-style consequence
of the resulting linear stability. -/
def Theorem_2_4_full_stability_formula_branch : Prop :=
  ∀ (D : BoundedDomainData) (S : SpectralData) (p : CM2Params)
    (N : StabilityNorms D),
    HasNeumannSpectrum S →
      ∀ (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        max
            (max (chiStrong1Formula p eq.1 eq.2)
              (chiStrong2Formula p eq.1))
            (max (chiStrong3Formula p M0 eq.1 eq.2)
              (chiStrong4Formula p M0 eq.1)) ≤
          paperCriticalSensitivity S p eq.1 eq.2 →
          NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
            (LinearlyStable S p eq.1 eq.2 →
              MassConstrainedLocallyExponentiallyStableFromSup D p N eq.1 eq.2) →
              LinearlyStable S p eq.1 eq.2 ∧
              MassConstrainedLocallyExponentiallyStableFromSup D p N eq.1 eq.2

lemma Theorem_2_4_full_stability_formula_branch_proved :
    Theorem_2_4_full_stability_formula_branch := by
  intro D S p N H ha hb M0
  dsimp
  intro hcritical hcond hsectorial
  have hstable :=
    hcond.linearlyStable_of_max_threshold_le_critical S p H ha hb hcritical
  exact ⟨hstable, hsectorial hstable⟩

/-- Direct theorem-shaped version of the formula-level Theorem 2.4
full-stability bridge.  This is the same statement as
`Theorem_2_4_full_stability_formula_branch`, but not routed through a
theorem-shaped `Prop` wrapper. -/
theorem Theorem_2_4_full_stability_formula_branch_direct
    (D : BoundedDomainData) (S : SpectralData) (p : CM2Params)
    (N : StabilityNorms D) (H : HasNeumannSpectrum S)
    (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    max
        (max (chiStrong1Formula p eq.1 eq.2)
          (chiStrong2Formula p eq.1))
        (max (chiStrong3Formula p M0 eq.1 eq.2)
          (chiStrong4Formula p M0 eq.1)) ≤
      paperCriticalSensitivity S p eq.1 eq.2 →
      NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
        (LinearlyStable S p eq.1 eq.2 →
          MassConstrainedLocallyExponentiallyStableFromSup D p N eq.1 eq.2) →
          LinearlyStable S p eq.1 eq.2 ∧
          MassConstrainedLocallyExponentiallyStableFromSup D p N eq.1 eq.2 := by
  dsimp
  intro hcritical hcond hsectorial
  have hstable :=
    hcond.linearlyStable_of_max_threshold_le_critical S p H ha hb hcritical
  exact ⟨hstable, hsectorial hstable⟩

/-- General first-mode sufficient version of the formula-level Theorem 2.4
full-stability bridge.  This avoids `Paper3Constants`; the remaining local
exponential step is the explicit sectorial consequence supplied as an input. -/
lemma Theorem_2_4_full_stability_first_mode_branch
    (D : BoundedDomainData) (S : SpectralData) (p : CM2Params)
    (N : StabilityNorms D) (H : HasNeumannSpectrum S)
    (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    max
        (max (chiStrong1Formula p eq.1 eq.2)
          (chiStrong2Formula p eq.1))
        (max (chiStrong3Formula p M0 eq.1 eq.2)
          (chiStrong4Formula p M0 eq.1)) ≤
      ((1 + eq.2) ^ p.β /
          (p.ν * p.γ * eq.1 ^ (p.m + p.γ - 1))) *
        (p.μ + S.firstNonzero) →
      NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
        (LinearlyStable S p eq.1 eq.2 →
          MassConstrainedLocallyExponentiallyStableFromSup D p N eq.1 eq.2) →
          LinearlyStable S p eq.1 eq.2 ∧
          MassConstrainedLocallyExponentiallyStableFromSup D p N eq.1 eq.2 := by
  dsimp
  intro hfirst hcond hsectorial
  have hstable :=
    hcond.linearlyStable_of_firstNonzero_lower S p H ha hb hfirst
  exact ⟨hstable, hsectorial hstable⟩

lemma Theorem_2_4_full_stability_formula_unitInterval
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    max
        (max (chiStrong1Formula p eq.1 eq.2)
          (chiStrong2Formula p eq.1))
        (max (chiStrong3Formula p M0 eq.1 eq.2)
          (chiStrong4Formula p M0 eq.1)) ≤
      paperCriticalSensitivity unitIntervalNeumannSpectrum p eq.1 eq.2 →
      NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
        (LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 →
          MassConstrainedLocallyExponentiallyStableFromSup D p N eq.1 eq.2) →
          LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 ∧
          MassConstrainedLocallyExponentiallyStableFromSup D p N eq.1 eq.2 := by
  dsimp
  intro hcritical hcond hsectorial
  have hstable :=
    hcond.linearlyStable_of_max_threshold_le_critical
      unitIntervalNeumannSpectrum p unitIntervalNeumannSpectrum_hasNeumannSpectrum
      ha hb hcritical
  exact ⟨hstable, hsectorial hstable⟩

lemma Theorem_2_4_full_stability_first_mode_unitInterval
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    max
        (max (chiStrong1Formula p eq.1 eq.2)
          (chiStrong2Formula p eq.1))
        (max (chiStrong3Formula p M0 eq.1 eq.2)
          (chiStrong4Formula p M0 eq.1)) ≤
      ((1 + eq.2) ^ p.β /
          (p.ν * p.γ * eq.1 ^ (p.m + p.γ - 1))) *
        (p.μ + Real.pi ^ 2) →
      NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
        (LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 →
          MassConstrainedLocallyExponentiallyStableFromSup D p N eq.1 eq.2) →
          LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 ∧
          MassConstrainedLocallyExponentiallyStableFromSup D p N eq.1 eq.2 := by
  dsimp
  intro hfirst hcond hsectorial
  have hstable :=
    hcond.linearlyStable_of_firstNonzero_lower
      unitIntervalNeumannSpectrum p unitIntervalNeumannSpectrum_hasNeumannSpectrum
      ha hb hfirst
  exact ⟨hstable, hsectorial hstable⟩

/-- Formula-level full stability bridge for Paper3 Theorem 2.5.  This minimal
model version uses the explicit `chiBeta` threshold and
`paperCriticalSensitivity`; the local exponential part is supplied explicitly
as a sectorial-style consequence of linear stability. -/
def Theorem_2_5_full_stability_formula_branch : Prop :=
  ∀ (D : BoundedDomainData) (S : SpectralData) (p : CM2Params)
    (N : StabilityNorms D),
    HasNeumannSpectrum S →
      p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
        ∀ uStar > 0, ∀ uBar vLower : ℝ,
          chiBeta p ≤
            paperCriticalSensitivity S p
              (minimalEquilibrium p uStar).1
              (minimalEquilibrium p uStar).2 →
            MinimalGlobalStabilityFormulaCondition p uStar uBar vLower →
              (LinearlyStable S p
                  (minimalEquilibrium p uStar).1
                  (minimalEquilibrium p uStar).2 →
                MassConstrainedLocallyExponentiallyStableFromSup D p N
                  (minimalEquilibrium p uStar).1
                  (minimalEquilibrium p uStar).2) →
                LinearlyStable S p
                  (minimalEquilibrium p uStar).1
                  (minimalEquilibrium p uStar).2 ∧
                MassConstrainedLocallyExponentiallyStableFromSup D p N
                  (minimalEquilibrium p uStar).1
                  (minimalEquilibrium p uStar).2

lemma Theorem_2_5_full_stability_formula_branch_proved :
    Theorem_2_5_full_stability_formula_branch := by
  intro D S p N H _ha _hb _hm hβ uStar huStar uBar vLower
    hcritical hcond hsectorial
  have hstable :=
    hcond.linearlyStable_of_chiBeta_le_critical S p H hβ huStar hcritical
  exact ⟨hstable, hsectorial hstable⟩

/-- Direct theorem-shaped version of the formula-level Theorem 2.5
full-stability bridge, avoiding the theorem-shaped `Prop` wrapper. -/
theorem Theorem_2_5_full_stability_formula_branch_direct
    (D : BoundedDomainData) (S : SpectralData) (p : CM2Params)
    (N : StabilityNorms D) (H : HasNeumannSpectrum S)
    (_ha : p.a = 0) (_hb : p.b = 0) (_hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar) (uBar vLower : ℝ) :
    chiBeta p ≤
      paperCriticalSensitivity S p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 →
      MinimalGlobalStabilityFormulaCondition p uStar uBar vLower →
        (LinearlyStable S p
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2 →
          MassConstrainedLocallyExponentiallyStableFromSup D p N
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2) →
          LinearlyStable S p
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2 ∧
          MassConstrainedLocallyExponentiallyStableFromSup D p N
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2 := by
  intro hcritical hcond hsectorial
  have hstable :=
    hcond.linearlyStable_of_chiBeta_le_critical S p H hβ huStar hcritical
  exact ⟨hstable, hsectorial hstable⟩

/-- General first-mode sufficient version of the formula-level Theorem 2.5
full-stability bridge.  It uses the explicit first-nonzero eigenvalue lower
bound instead of a `Paper3Constants` critical-threshold field. -/
lemma Theorem_2_5_full_stability_first_mode_branch
    (D : BoundedDomainData) (S : SpectralData) (p : CM2Params)
    (N : StabilityNorms D) (H : HasNeumannSpectrum S)
    (_ha : p.a = 0) (_hb : p.b = 0) (_hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar) (uBar vLower : ℝ) :
    chiBeta p ≤
      ((1 + (minimalEquilibrium p uStar).2) ^ p.β /
          (p.ν * p.γ *
            (minimalEquilibrium p uStar).1 ^ (p.m + p.γ - 1))) *
        (p.μ + S.firstNonzero) →
      MinimalGlobalStabilityFormulaCondition p uStar uBar vLower →
        (LinearlyStable S p
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2 →
          MassConstrainedLocallyExponentiallyStableFromSup D p N
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2) →
          LinearlyStable S p
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2 ∧
          MassConstrainedLocallyExponentiallyStableFromSup D p N
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2 := by
  intro hfirst hcond hsectorial
  have hstable :=
    hcond.linearlyStable_of_firstNonzero_lower S p H hβ huStar hfirst
  exact ⟨hstable, hsectorial hstable⟩

lemma Theorem_2_5_full_stability_formula_unitInterval
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (_ha : p.a = 0) (_hb : p.b = 0) (_hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar) (uBar vLower : ℝ) :
    chiBeta p ≤
      paperCriticalSensitivity unitIntervalNeumannSpectrum p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 →
      MinimalGlobalStabilityFormulaCondition p uStar uBar vLower →
        (LinearlyStable unitIntervalNeumannSpectrum p
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2 →
          MassConstrainedLocallyExponentiallyStableFromSup D p N
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2) →
          LinearlyStable unitIntervalNeumannSpectrum p
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2 ∧
          MassConstrainedLocallyExponentiallyStableFromSup D p N
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2 := by
  intro hcritical hcond hsectorial
  have hstable :=
    hcond.linearlyStable_of_chiBeta_le_critical
      unitIntervalNeumannSpectrum p unitIntervalNeumannSpectrum_hasNeumannSpectrum
      hβ huStar hcritical
  exact ⟨hstable, hsectorial hstable⟩

lemma Theorem_2_5_full_stability_first_mode_unitInterval
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (_ha : p.a = 0) (_hb : p.b = 0) (_hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar) (uBar vLower : ℝ) :
    chiBeta p ≤
      ((1 + (minimalEquilibrium p uStar).2) ^ p.β /
          (p.ν * p.γ *
            (minimalEquilibrium p uStar).1 ^ (p.m + p.γ - 1))) *
        (p.μ + Real.pi ^ 2) →
      MinimalGlobalStabilityFormulaCondition p uStar uBar vLower →
        (LinearlyStable unitIntervalNeumannSpectrum p
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2 →
          MassConstrainedLocallyExponentiallyStableFromSup D p N
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2) →
          LinearlyStable unitIntervalNeumannSpectrum p
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2 ∧
          MassConstrainedLocallyExponentiallyStableFromSup D p N
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2 := by
  intro hfirst hcond hsectorial
  have hstable :=
    hcond.linearlyStable_of_firstNonzero_lower
      unitIntervalNeumannSpectrum p unitIntervalNeumannSpectrum_hasNeumannSpectrum
      hβ huStar hfirst
  exact ⟨hstable, hsectorial hstable⟩

lemma Theorem_2_2.nonminimal_stability_conclusion_of_Lemma_A_7
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Theorem_2_2 D p S N C) (hA7 : Lemma_A_7 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hcond :
      NonminimalGlobalStabilityCondition D p C
        (positiveEquilibrium p ⟨ha, hb⟩).1) :
    LinearlyStable S p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 ∧
    LocallyExponentiallyStableFromSup D p N
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  exact h.nonminimal_stability_conclusion ha hb
    (hA7.nonminimal_condition_chi_lt_critical ha hb hcond)

lemma Theorem_2_2.nonminimal_stability_conclusion_of_chiStrong1_of_Lemma_A_7
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Theorem_2_2 D p S N C) (hA7 : Lemma_A_7 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m) (hαγ : 2 * p.γ ≤ p.α + 1)
    (hχ0 : 0 < p.χ₀)
    (hχ : p.χ₀ < C.chiStrong1 (positiveEquilibrium p ⟨ha, hb⟩).1) :
    LinearlyStable S p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 ∧
    LocallyExponentiallyStableFromSup D p N
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  h.nonminimal_stability_conclusion_of_Lemma_A_7 hA7 ha hb
    (NonminimalGlobalStabilityCondition.of_chiStrong1 hm hαγ hχ0 hχ)

lemma Theorem_2_2.nonminimal_stability_conclusion_of_chiStrong2_of_Lemma_A_7
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Theorem_2_2 D p S N C) (hA7 : Lemma_A_7 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m) (hβ : 1 ≤ p.β)
    (hαγ : 2 * p.γ ≤ p.α + 1)
    (hχ0 : 0 < p.χ₀)
    (hχ : p.χ₀ < C.chiStrong2 (positiveEquilibrium p ⟨ha, hb⟩).1) :
    LinearlyStable S p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 ∧
    LocallyExponentiallyStableFromSup D p N
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  h.nonminimal_stability_conclusion_of_Lemma_A_7 hA7 ha hb
    (NonminimalGlobalStabilityCondition.of_chiStrong2 hm hβ hαγ hχ0 hχ)

lemma Theorem_2_2.nonminimal_stability_conclusion_of_chiStrong3_of_Lemma_A_7
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Theorem_2_2 D p S N C) (hA7 : Lemma_A_7 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m) (hγ : 1 ≤ p.γ)
    (hαγ :
      p.m + p.γ + (if p.β = 0 then 0 else p.γ) ≤ p.α + 1)
    (hχ : p.χ₀ < C.chiStrong3 (positiveEquilibrium p ⟨ha, hb⟩).1) :
    LinearlyStable S p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 ∧
    LocallyExponentiallyStableFromSup D p N
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  h.nonminimal_stability_conclusion_of_Lemma_A_7 hA7 ha hb
    (NonminimalGlobalStabilityCondition.of_chiStrong3 hm hγ hαγ hχ)

lemma Theorem_2_2.nonminimal_stability_conclusion_of_chiStrong4_of_Lemma_A_7
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Theorem_2_2 D p S N C) (hA7 : Lemma_A_7 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m) (hβ : 1 ≤ p.β) (hγ : 1 ≤ p.γ)
    (hαγ : p.m + 2 * p.γ ≤ p.α + 1)
    (hχ : p.χ₀ < C.chiStrong4 (positiveEquilibrium p ⟨ha, hb⟩).1) :
    LinearlyStable S p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 ∧
    LocallyExponentiallyStableFromSup D p N
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  h.nonminimal_stability_conclusion_of_Lemma_A_7 hA7 ha hb
    (NonminimalGlobalStabilityCondition.of_chiStrong4 hm hβ hγ hαγ hχ)

lemma Theorem_2_2.nonminimal_exponential_convergence_of_Lemma_A_7
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Theorem_2_2 D p S N C) (hA7 : Lemma_A_7 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hcond :
      NonminimalGlobalStabilityCondition D p C
        (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ∃ δ > 0,
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        SupCloseToConstant D u₀ (positiveEquilibrium p ⟨ha, hb⟩).1 δ →
          ∃ u v : ℝ → D.Point → ℝ,
            IsPaper2GlobalClassicalSolution D p u v ∧
            InitialTrace D u₀ u ∧
            ExponentialC1Convergence D N u v
              (positiveEquilibrium p ⟨ha, hb⟩).1
              (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  exact h.nonminimal_exponential_convergence ha hb
    (hA7.nonminimal_condition_chi_lt_critical ha hb hcond)

lemma Theorem_2_2.nonminimal_exponential_convergence_of_chiStrong1_of_Lemma_A_7
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Theorem_2_2 D p S N C) (hA7 : Lemma_A_7 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m) (hαγ : 2 * p.γ ≤ p.α + 1)
    (hχ0 : 0 < p.χ₀)
    (hχ : p.χ₀ < C.chiStrong1 (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ∃ δ > 0,
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        SupCloseToConstant D u₀ (positiveEquilibrium p ⟨ha, hb⟩).1 δ →
          ∃ u v : ℝ → D.Point → ℝ,
            IsPaper2GlobalClassicalSolution D p u v ∧
            InitialTrace D u₀ u ∧
            ExponentialC1Convergence D N u v
              (positiveEquilibrium p ⟨ha, hb⟩).1
              (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  h.nonminimal_exponential_convergence_of_Lemma_A_7 hA7 ha hb
    (NonminimalGlobalStabilityCondition.of_chiStrong1 hm hαγ hχ0 hχ)

lemma Theorem_2_2.nonminimal_exponential_convergence_of_chiStrong2_of_Lemma_A_7
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Theorem_2_2 D p S N C) (hA7 : Lemma_A_7 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m) (hβ : 1 ≤ p.β)
    (hαγ : 2 * p.γ ≤ p.α + 1)
    (hχ0 : 0 < p.χ₀)
    (hχ : p.χ₀ < C.chiStrong2 (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ∃ δ > 0,
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        SupCloseToConstant D u₀ (positiveEquilibrium p ⟨ha, hb⟩).1 δ →
          ∃ u v : ℝ → D.Point → ℝ,
            IsPaper2GlobalClassicalSolution D p u v ∧
            InitialTrace D u₀ u ∧
            ExponentialC1Convergence D N u v
              (positiveEquilibrium p ⟨ha, hb⟩).1
              (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  h.nonminimal_exponential_convergence_of_Lemma_A_7 hA7 ha hb
    (NonminimalGlobalStabilityCondition.of_chiStrong2 hm hβ hαγ hχ0 hχ)

lemma Theorem_2_2.nonminimal_exponential_convergence_of_chiStrong3_of_Lemma_A_7
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Theorem_2_2 D p S N C) (hA7 : Lemma_A_7 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m) (hγ : 1 ≤ p.γ)
    (hαγ :
      p.m + p.γ + (if p.β = 0 then 0 else p.γ) ≤ p.α + 1)
    (hχ : p.χ₀ < C.chiStrong3 (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ∃ δ > 0,
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        SupCloseToConstant D u₀ (positiveEquilibrium p ⟨ha, hb⟩).1 δ →
          ∃ u v : ℝ → D.Point → ℝ,
            IsPaper2GlobalClassicalSolution D p u v ∧
            InitialTrace D u₀ u ∧
            ExponentialC1Convergence D N u v
              (positiveEquilibrium p ⟨ha, hb⟩).1
              (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  h.nonminimal_exponential_convergence_of_Lemma_A_7 hA7 ha hb
    (NonminimalGlobalStabilityCondition.of_chiStrong3 hm hγ hαγ hχ)

lemma Theorem_2_2.nonminimal_exponential_convergence_of_chiStrong4_of_Lemma_A_7
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Theorem_2_2 D p S N C) (hA7 : Lemma_A_7 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m) (hβ : 1 ≤ p.β) (hγ : 1 ≤ p.γ)
    (hαγ : p.m + 2 * p.γ ≤ p.α + 1)
    (hχ : p.χ₀ < C.chiStrong4 (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ∃ δ > 0,
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        SupCloseToConstant D u₀ (positiveEquilibrium p ⟨ha, hb⟩).1 δ →
          ∃ u v : ℝ → D.Point → ℝ,
            IsPaper2GlobalClassicalSolution D p u v ∧
            InitialTrace D u₀ u ∧
            ExponentialC1Convergence D N u v
              (positiveEquilibrium p ⟨ha, hb⟩).1
              (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  h.nonminimal_exponential_convergence_of_Lemma_A_7 hA7 ha hb
    (NonminimalGlobalStabilityCondition.of_chiStrong4 hm hβ hγ hαγ hχ)

lemma Theorem_2_2.minimal_stability_conclusion_of_Lemma_A_8
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Theorem_2_2 D p S N C) (hA8 : Lemma_A_8 D p C)
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hcond : MinimalGlobalStabilityCondition D p C uStar) :
    LinearlyStable S p
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 ∧
    MassConstrainedLocallyExponentiallyStableFromSup D p N
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 := by
  exact h.minimal_stability_conclusion ha hb huStar
    (hA8.minimal_condition_chi_lt_critical ha hb hm hβ huStar hcond)

lemma Theorem_2_2.minimal_stability_conclusion_of_chiMinimal1_of_Lemma_A_8
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Theorem_2_2 D p S N C) (hA8 : Lemma_A_8 D p C)
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hχ0 : 0 < p.χ₀) (hχ : p.χ₀ < C.chiMinimal1 uStar) :
    LinearlyStable S p
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 ∧
    MassConstrainedLocallyExponentiallyStableFromSup D p N
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 :=
  h.minimal_stability_conclusion_of_Lemma_A_8 hA8 ha hb hm hβ huStar
    (MinimalGlobalStabilityCondition.of_chiMinimal1 hχ0 hχ)

lemma Theorem_2_2.minimal_stability_conclusion_of_chiMinimal2_of_Lemma_A_8
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Theorem_2_2 D p S N C) (hA8 : Lemma_A_8 D p C)
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hγ : p.γ = 1) (hχ0 : 0 < p.χ₀)
    (hχ : p.χ₀ < C.chiMinimal2 uStar) :
    LinearlyStable S p
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 ∧
    MassConstrainedLocallyExponentiallyStableFromSup D p N
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 :=
  h.minimal_stability_conclusion_of_Lemma_A_8 hA8 ha hb hm hβ huStar
    (MinimalGlobalStabilityCondition.of_chiMinimal2 hγ hχ0 hχ)

lemma Theorem_2_2.minimal_exponential_convergence_of_Lemma_A_8
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Theorem_2_2 D p S N C) (hA8 : Lemma_A_8 D p C)
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hcond : MinimalGlobalStabilityCondition D p C uStar) :
    ∃ δ > 0,
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        SupCloseToConstant D u₀ (minimalEquilibrium p uStar).1 δ →
        D.integral u₀ = D.volume * uStar →
          ∃ u v : ℝ → D.Point → ℝ,
            IsPaper2GlobalClassicalSolution D p u v ∧
            InitialTrace D u₀ u ∧
            ExponentialC1Convergence D N u v
              (minimalEquilibrium p uStar).1
              (minimalEquilibrium p uStar).2 := by
  exact h.minimal_exponential_convergence ha hb huStar
    (hA8.minimal_condition_chi_lt_critical ha hb hm hβ huStar hcond)

lemma Theorem_2_2.minimal_exponential_convergence_of_chiMinimal1_of_Lemma_A_8
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Theorem_2_2 D p S N C) (hA8 : Lemma_A_8 D p C)
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hχ0 : 0 < p.χ₀) (hχ : p.χ₀ < C.chiMinimal1 uStar) :
    ∃ δ > 0,
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        SupCloseToConstant D u₀ (minimalEquilibrium p uStar).1 δ →
        D.integral u₀ = D.volume * uStar →
          ∃ u v : ℝ → D.Point → ℝ,
            IsPaper2GlobalClassicalSolution D p u v ∧
            InitialTrace D u₀ u ∧
            ExponentialC1Convergence D N u v
              (minimalEquilibrium p uStar).1
              (minimalEquilibrium p uStar).2 :=
  h.minimal_exponential_convergence_of_Lemma_A_8 hA8 ha hb hm hβ huStar
    (MinimalGlobalStabilityCondition.of_chiMinimal1 hχ0 hχ)

lemma Theorem_2_2.minimal_exponential_convergence_of_chiMinimal2_of_Lemma_A_8
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Theorem_2_2 D p S N C) (hA8 : Lemma_A_8 D p C)
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hγ : p.γ = 1) (hχ0 : 0 < p.χ₀)
    (hχ : p.χ₀ < C.chiMinimal2 uStar) :
    ∃ δ > 0,
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        SupCloseToConstant D u₀ (minimalEquilibrium p uStar).1 δ →
        D.integral u₀ = D.volume * uStar →
          ∃ u v : ℝ → D.Point → ℝ,
            IsPaper2GlobalClassicalSolution D p u v ∧
            InitialTrace D u₀ u ∧
            ExponentialC1Convergence D N u v
              (minimalEquilibrium p uStar).1
              (minimalEquilibrium p uStar).2 :=
  h.minimal_exponential_convergence_of_Lemma_A_8 hA8 ha hb hm hβ huStar
    (MinimalGlobalStabilityCondition.of_chiMinimal2 hγ hχ0 hχ)

lemma Corollary_5_1.nonminimal_exponential_of_chi_lt_paperCriticalSensitivity
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Corollary_5_1 D p N C)
    (hC : Paper3ConstantsUsesCriticalSpectrum S p C)
    (hm : 1 ≤ p.m) (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity S p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hconv : UniformConvergesInSup D u (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ExponentialC1Convergence D N u v
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  h.nonminimal_exponential hm ha hb
    (by
      rwa [hC.chiCritical_positiveEquilibrium ha hb])
    huv hconv

lemma Corollary_5_1.minimal_exponential_of_chi_lt_paperCriticalSensitivity
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Corollary_5_1 D p N C)
    (hC : Paper3ConstantsUsesCriticalSpectrum S p C)
    (hm : 1 ≤ p.m) (ha : p.a = 0) (hb : p.b = 0)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity S p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hmass : HasInitialMass D u uStar)
    (hconv : UniformConvergesInSup D u (minimalEquilibrium p uStar).1) :
    ExponentialC1Convergence D N u v
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 :=
  h.minimal_exponential hm ha hb huStar
    (by
      rwa [hC.chiCritical_minimalEquilibrium huStar])
    huv hmass hconv

lemma Corollary_5_1.nonminimal_exponential_unitInterval
    {D : BoundedDomainData} {p : CM2Params}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Corollary_5_1 D p N C)
    (hC : Paper3ConstantsUsesCriticalSpectrum unitIntervalNeumannSpectrum p C)
    (hm : 1 ≤ p.m) (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hconv : UniformConvergesInSup D u (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ExponentialC1Convergence D N u v
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  h.nonminimal_exponential_of_chi_lt_paperCriticalSensitivity hC
    hm ha hb hχ huv hconv

lemma Corollary_5_1.minimal_exponential_unitInterval
    {D : BoundedDomainData} {p : CM2Params}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Corollary_5_1 D p N C)
    (hC : Paper3ConstantsUsesCriticalSpectrum unitIntervalNeumannSpectrum p C)
    (hm : 1 ≤ p.m) (ha : p.a = 0) (hb : p.b = 0)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hmass : HasInitialMass D u uStar)
    (hconv : UniformConvergesInSup D u (minimalEquilibrium p uStar).1) :
    ExponentialC1Convergence D N u v
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 :=
  h.minimal_exponential_of_chi_lt_paperCriticalSensitivity hC
    hm ha hb huStar hχ huv hmass hconv

lemma Corollary_5_1.nonminimal_exponential_of_Lemma_A_7
    {D : BoundedDomainData} {p : CM2Params}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Corollary_5_1 D p N C) (hA7 : Lemma_A_7 D p C)
    (hm : 1 ≤ p.m) (ha : 0 < p.a) (hb : 0 < p.b)
    (hcond :
      NonminimalGlobalStabilityCondition D p C
        (positiveEquilibrium p ⟨ha, hb⟩).1)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hconv : UniformConvergesInSup D u (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ExponentialC1Convergence D N u v
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  h.nonminimal_exponential hm ha hb
    (hA7.nonminimal_condition_chi_lt_critical ha hb hcond)
    huv hconv

lemma Corollary_5_1.minimal_exponential_of_Lemma_A_8
    {D : BoundedDomainData} {p : CM2Params}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Corollary_5_1 D p N C) (hA8 : Lemma_A_8 D p C)
    (hm_le : 1 ≤ p.m) (ha : p.a = 0) (hb : p.b = 0)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hcond : MinimalGlobalStabilityCondition D p C uStar)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hmass : HasInitialMass D u uStar)
    (hconv : UniformConvergesInSup D u (minimalEquilibrium p uStar).1) :
    ExponentialC1Convergence D N u v
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 :=
  h.minimal_exponential hm_le ha hb huStar
    (hA8.minimal_condition_chi_lt_critical ha hb hm hβ huStar hcond)
    huv hmass hconv

lemma Corollary_5_1.nonminimal_exponential_of_chiStrong1_of_Lemma_A_7
    {D : BoundedDomainData} {p : CM2Params}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Corollary_5_1 D p N C) (hA7 : Lemma_A_7 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m) (hαγ : 2 * p.γ ≤ p.α + 1)
    (hχ0 : 0 < p.χ₀)
    (hχ : p.χ₀ < C.chiStrong1 (positiveEquilibrium p ⟨ha, hb⟩).1)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hconv : UniformConvergesInSup D u (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ExponentialC1Convergence D N u v
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  h.nonminimal_exponential_of_Lemma_A_7 hA7 hm ha hb
    (NonminimalGlobalStabilityCondition.of_chiStrong1 hm hαγ hχ0 hχ)
    huv hconv

lemma Corollary_5_1.nonminimal_exponential_of_chiStrong2_of_Lemma_A_7
    {D : BoundedDomainData} {p : CM2Params}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Corollary_5_1 D p N C) (hA7 : Lemma_A_7 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m) (hβ : 1 ≤ p.β)
    (hαγ : 2 * p.γ ≤ p.α + 1)
    (hχ0 : 0 < p.χ₀)
    (hχ : p.χ₀ < C.chiStrong2 (positiveEquilibrium p ⟨ha, hb⟩).1)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hconv : UniformConvergesInSup D u (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ExponentialC1Convergence D N u v
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  h.nonminimal_exponential_of_Lemma_A_7 hA7 hm ha hb
    (NonminimalGlobalStabilityCondition.of_chiStrong2 hm hβ hαγ hχ0 hχ)
    huv hconv

lemma Corollary_5_1.nonminimal_exponential_of_chiStrong3_of_Lemma_A_7
    {D : BoundedDomainData} {p : CM2Params}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Corollary_5_1 D p N C) (hA7 : Lemma_A_7 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m) (hγ : 1 ≤ p.γ)
    (hαγ :
      p.m + p.γ + (if p.β = 0 then 0 else p.γ) ≤ p.α + 1)
    (hχ : p.χ₀ < C.chiStrong3 (positiveEquilibrium p ⟨ha, hb⟩).1)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hconv : UniformConvergesInSup D u (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ExponentialC1Convergence D N u v
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  h.nonminimal_exponential_of_Lemma_A_7 hA7 hm ha hb
    (NonminimalGlobalStabilityCondition.of_chiStrong3 hm hγ hαγ hχ)
    huv hconv

lemma Corollary_5_1.nonminimal_exponential_of_chiStrong4_of_Lemma_A_7
    {D : BoundedDomainData} {p : CM2Params}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Corollary_5_1 D p N C) (hA7 : Lemma_A_7 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m) (hβ : 1 ≤ p.β) (hγ : 1 ≤ p.γ)
    (hαγ : p.m + 2 * p.γ ≤ p.α + 1)
    (hχ : p.χ₀ < C.chiStrong4 (positiveEquilibrium p ⟨ha, hb⟩).1)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hconv : UniformConvergesInSup D u (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ExponentialC1Convergence D N u v
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  h.nonminimal_exponential_of_Lemma_A_7 hA7 hm ha hb
    (NonminimalGlobalStabilityCondition.of_chiStrong4 hm hβ hγ hαγ hχ)
    huv hconv

lemma Corollary_5_1.minimal_exponential_of_chiMinimal1_of_Lemma_A_8
    {D : BoundedDomainData} {p : CM2Params}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Corollary_5_1 D p N C) (hA8 : Lemma_A_8 D p C)
    (hm_le : 1 ≤ p.m) (ha : p.a = 0) (hb : p.b = 0)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hχ0 : 0 < p.χ₀) (hχ : p.χ₀ < C.chiMinimal1 uStar)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hmass : HasInitialMass D u uStar)
    (hconv : UniformConvergesInSup D u (minimalEquilibrium p uStar).1) :
    ExponentialC1Convergence D N u v
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 :=
  h.minimal_exponential_of_Lemma_A_8 hA8 hm_le ha hb hm hβ huStar
    (MinimalGlobalStabilityCondition.of_chiMinimal1 hχ0 hχ) huv hmass hconv

lemma Corollary_5_1.minimal_exponential_of_chiMinimal2_of_Lemma_A_8
    {D : BoundedDomainData} {p : CM2Params}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (h : Corollary_5_1 D p N C) (hA8 : Lemma_A_8 D p C)
    (hm_le : 1 ≤ p.m) (ha : p.a = 0) (hb : p.b = 0)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hγ : p.γ = 1) (hχ0 : 0 < p.χ₀)
    (hχ : p.χ₀ < C.chiMinimal2 uStar)
    {u v : ℝ → D.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution D p u v)
    (hmass : HasInitialMass D u uStar)
    (hconv : UniformConvergesInSup D u (minimalEquilibrium p uStar).1) :
    ExponentialC1Convergence D N u v
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 :=
  h.minimal_exponential_of_Lemma_A_8 hA8 hm_le ha hb hm hβ huStar
    (MinimalGlobalStabilityCondition.of_chiMinimal2 hγ hχ0 hχ) huv hmass hconv

end

end ShenWork.Paper3
