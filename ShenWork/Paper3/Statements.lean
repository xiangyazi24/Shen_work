/-
  Statement layer for Chen-Ruau-Shen,
  "Chemotaxis models with signal-dependent sensitivity and a logistic-type
  source, II: Persistence and stabilization".

  The paper's main results are Theorems 2.1--2.5.  They are stated here against
  the non-toy bounded-domain PDE interface from `Paper2/Statements.lean`.
-/
import ShenWork.Paper2.Statements

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

lemma positiveEquilibrium_logistic_zero
    (p : CM2Params) (hab : 0 < p.a ∧ 0 < p.b) :
    p.a - p.b * (positiveEquilibrium p hab).1 ^ p.α = 0 := by
  rw [positiveEquilibrium_fst_rpow_alpha p hab]
  field_simp [ne_of_gt hab.2]
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

def PositiveGlobalBoundedSolution
    (D : BoundedDomainData) (p : CM2Params)
    (u v : ℝ → D.Point → ℝ) : Prop :=
  IsPaper2GlobalClassicalSolution D p u v ∧
    IsPaper2Bounded D u ∧
    ∀ t x, 0 < t → x ∈ D.inside → 0 < u t x

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

structure StabilityNorms (D : BoundedDomainData) where
  c1Distance : (D.Point → ℝ) → (D.Point → ℝ) → ℝ
  xpSigmaDistance : ℝ → ℝ → (D.Point → ℝ) → (D.Point → ℝ) → ℝ

structure CompactnessData (D : BoundedDomainData) where
  locallyConverges :
    (ℕ → ℝ → D.Point → ℝ) → (ℝ → D.Point → ℝ) → Prop
  upperEnvelope : (D.Point → ℝ) → ℝ
  neumannResolventGradientBound :
    (mu nu : ℝ) → (D.Point → ℝ) → ℝ → Prop

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

def TimeTranslateCompactnessConclusion
    (D : BoundedDomainData) (p : CM2Params) (K : CompactnessData D)
    (u v : ℝ → D.Point → ℝ) : Prop :=
  ∀ times : ℕ → ℝ, Tendsto times atTop atTop →
    ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
    ∃ uInf vInf : ℝ → D.Point → ℝ,
      K.locallyConverges (fun n t x => u (t + times (subseq n)) x) uInf ∧
      K.locallyConverges (fun n t x => v (t + times (subseq n)) x) vInf ∧
      EntireClassicalSolution D p uInf vInf

def InitialContinuityConclusion
    (D : BoundedDomainData) (N : StabilityNorms D)
    (uConst : ℝ) : Prop :=
  ∀ sigma pNorm eps, 1 / 2 < sigma → 1 < pNorm → 0 < eps →
    ∃ delta > 0, ∃ T0 > 0, ∀ u₀ u : D.Point → ℝ,
      D.supNorm (fun x => u₀ x - uConst) ≤ delta →
      N.xpSigmaDistance sigma pNorm u (fun _ => uConst) ≤ eps

def UpperEnvelopeMonotonicityConclusion
    (D : BoundedDomainData) (p : CM2Params) (K : CompactnessData D)
    (u : ℝ → D.Point → ℝ) : Prop :=
  (p.χ₀ ≤ 0 → 0 < p.a → 0 < p.b →
    ∀ t₀, 0 < t₀ →
      (p.a / p.b) ^ (1 / p.α) < K.upperEnvelope (u t₀) →
      ∀ t, 0 < t → t ≤ t₀ → K.upperEnvelope (u t) ≤ K.upperEnvelope (u t₀)) ∧
  (p.χ₀ ≤ 0 → p.a = 0 → p.b = 0 →
    ∀ t₁ t₂, 0 < t₁ → t₁ ≤ t₂ →
      K.upperEnvelope (u t₂) ≤ K.upperEnvelope (u t₁))

def ExponentialC1Convergence
    (D : BoundedDomainData) (N : StabilityNorms D)
    (u v : ℝ → D.Point → ℝ) (uStar vStar : ℝ) : Prop :=
  ∃ C > 0, ∃ rate > 0, ∀ t, 0 ≤ t →
    N.c1Distance (u t) (fun _ => uStar) +
      N.c1Distance (v t) (fun _ => vStar) ≤ C * Real.exp (-rate * t)

def Proposition_1_1 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  Paper2.Proposition_1_1 D p

def Proposition_1_2 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  p.χ₀ ≤ 0 → 1 ≤ p.m →
    ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
      ∃ u v : ℝ → D.Point → ℝ,
        IsPaper2GlobalClassicalSolution D p u v ∧
        InitialTrace D u₀ u ∧
        IsPaper2Bounded D u

def Proposition_1_3
    (D : BoundedDomainData) (p : CM2Params) (C : Paper2Constants p) : Prop :=
  0 < p.a → 0 < p.b → 1 ≤ p.m → StrongLogisticCondition p C →
    ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
      ∃ u v : ℝ → D.Point → ℝ,
        IsPaper2GlobalClassicalSolution D p u v ∧
        InitialTrace D u₀ u ∧
        IsPaper2Bounded D u

def Proposition_1_4 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  p.m = 1 → 1 ≤ p.β →
    ((p.a = 0 ∧ p.b = 0) ∨ (0 ≤ p.a ∧ 0 < p.b)) →
      p.χ₀ < chiBeta p →
        ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
          ∃ u v : ℝ → D.Point → ℝ,
            IsPaper2GlobalClassicalSolution D p u v ∧
            InitialTrace D u₀ u ∧
            IsPaper2Bounded D u

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

structure Paper3Constants (D : BoundedDomainData) (p : CM2Params) where
  chiCritical : ℝ → ℝ
  chiStrong1 : ℝ → ℝ
  chiStrong2 : ℝ → ℝ
  chiStrong3 : ℝ → ℝ
  chiStrong4 : ℝ → ℝ
  chiMinimal1 : ℝ → ℝ
  chiMinimal2 : ℝ → ℝ
  eventualMinimalUBound : ℝ → ℝ
  eventualMinimalVLower : ℝ → ℝ

def EventuallyUpperBoundMinimalConclusion
    (D : BoundedDomainData) (p : CM2Params) (C : Paper3Constants D p)
    (u : ℝ → D.Point → ℝ) : Prop :=
  ∀ uStar > 0, HasInitialMass D u uStar →
    ∀ᶠ t in atTop, D.supNorm (u t) ≤ C.eventualMinimalUBound uStar

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

def Theorem_2_1_part1 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  1 ≤ p.m →
    ∀ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v →
        ∃ δu > 0, EventuallyLowerBound D u δu ∧
          EventuallyLowerBound D v (p.ν / p.μ * δu ^ p.γ)

def Theorem_2_1_part2 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  0 < p.a → 0 < p.b → 0 < p.χ₀ → p.m = 1 → 1 ≤ p.β →
    p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)) →
      ∀ u v : ℝ → D.Point → ℝ,
        PositiveGlobalBoundedSolution D p u v →
          let lowerU :=
            ((p.a - p.χ₀ * p.μ * Theta_beta (p.β - 1)) / p.b) ^ (1 / p.α)
          EventuallyLowerBound D u lowerU ∧
            EventuallyLowerBound D v (p.ν / p.μ * lowerU ^ p.γ)

def Theorem_2_1_part3 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  0 < p.a → 0 < p.b → 0 < p.χ₀ → 1 < p.m → 1 ≤ p.β →
    ∀ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v →
        let lowerU :=
          min 1 (p.a / (p.b + p.χ₀ * p.μ * Theta_beta (p.β - 1))) ^
            max (1 / (p.m - 1)) (1 / p.α)
        EventuallyLowerBound D u lowerU ∧
          EventuallyLowerBound D v (p.ν / p.μ * lowerU ^ p.γ)

def Theorem_2_1_part4
    (D : BoundedDomainData) (p : CM2Params) (C : Paper3Constants D p) : Prop :=
  p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
    0 < p.χ₀ → p.χ₀ < min (p.χ₀ / (2 * p.β)) (chiBeta p) →
      ∀ uStar > 0, ∀ u v : ℝ → D.Point → ℝ,
        PositiveGlobalBoundedSolution D p u v →
        HasInitialMass D u uStar →
          EventuallyLowerBound D v (C.eventualMinimalVLower uStar)

/-- Paper3 Theorem 2.1: uniform persistence. -/
def Theorem_2_1 (D : BoundedDomainData) (p : CM2Params) (C : Paper3Constants D p) : Prop :=
  Theorem_2_1_part1 D p ∧
    Theorem_2_1_part2 D p ∧
    Theorem_2_1_part3 D p ∧
    Theorem_2_1_part4 D p C

/-- Paper3 Theorem 2.2: linear stability/instability and local exponential stability. -/
def Theorem_2_2
    (D : BoundedDomainData) (p : CM2Params) (S : SpectralData)
    (N : StabilityNorms D) (C : Paper3Constants D p) : Prop :=
  (∀ (ha : 0 < p.a) (hb : 0 < p.b),
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    p.χ₀ < C.chiCritical eq.1 →
      LinearlyStable S p eq.1 eq.2 ∧
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2GlobalClassicalSolution D p u v ∧
          InitialTrace D u₀ u ∧
          ExponentialC1Convergence D N u v eq.1 eq.2) ∧
  (∀ (ha : 0 < p.a) (hb : 0 < p.b),
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    C.chiCritical eq.1 < p.χ₀ →
      LinearlyUnstable S p eq.1 eq.2) ∧
  (p.a = 0 → p.b = 0 →
    ∀ uStar > 0,
      let eq := minimalEquilibrium p uStar
      p.χ₀ < C.chiCritical uStar →
        LinearlyStable S p eq.1 eq.2) ∧
  (p.a = 0 → p.b = 0 →
    ∀ uStar > 0,
      let eq := minimalEquilibrium p uStar
      C.chiCritical uStar < p.χ₀ →
        LinearlyUnstable S p eq.1 eq.2)

/-- Paper3 Theorem 2.3: global stability for negative sensitivity. -/
def Theorem_2_3
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D) : Prop :=
  p.χ₀ ≤ 0 → 1 ≤ p.m →
    (∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      GloballyAsymptoticallyStableNonminimal D p eq.1 eq.2 ∧
      ∀ u v : ℝ → D.Point → ℝ,
        PositiveGlobalBoundedSolution D p u v →
          ExponentialC1Convergence D N u v eq.1 eq.2) ∧
    (p.a = 0 → p.b = 0 →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        GloballyAsymptoticallyStableMinimal D p eq.1 eq.2 ∧
        ∀ u v : ℝ → D.Point → ℝ,
          PositiveGlobalBoundedSolution D p u v →
          HasInitialMass D u uStar →
            ExponentialC1Convergence D N u v eq.1 eq.2)

/-- Paper3 Theorem 2.4: global stability under relatively strong logistic source. -/
def Theorem_2_4
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (C : Paper3Constants D p) : Prop :=
  0 < p.a → 0 < p.b → 0 ≤ p.β → 0 < p.α → 0 < p.γ →
    ∀ (ha : 0 < p.a) (hb : 0 < p.b),
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    NonminimalGlobalStabilityCondition D p C eq.1 →
      GloballyAsymptoticallyStableNonminimal D p eq.1 eq.2 ∧
      ∀ u v : ℝ → D.Point → ℝ,
        PositiveGlobalBoundedSolution D p u v →
          ExponentialC1Convergence D N u v eq.1 eq.2

/-- Paper3 Theorem 2.5: global stability in the minimal model. -/
def Theorem_2_5
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (C : Paper3Constants D p) : Prop :=
  p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
    ∀ uStar > 0,
      let eq := minimalEquilibrium p uStar
      ((0 < p.χ₀ ∧ p.χ₀ < C.chiMinimal1 uStar) ∨
        (p.γ = 1 ∧ 0 < p.χ₀ ∧ p.χ₀ < C.chiMinimal2 uStar)) →
        GloballyAsymptoticallyStableMinimal D p eq.1 eq.2 ∧
        ∀ u v : ℝ → D.Point → ℝ,
          PositiveGlobalBoundedSolution D p u v →
          HasInitialMass D u uStar →
            ExponentialC1Convergence D N u v eq.1 eq.2

def Lemma_3_1 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ u v : ℝ → D.Point → ℝ,
    PositiveGlobalBoundedSolution D p u v →
      UniformRegularityConclusion D p u v

def Lemma_3_2
    (D : BoundedDomainData) (p : CM2Params) (K : CompactnessData D) : Prop :=
  1 ≤ p.m → 0 < p.γ →
    ∀ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v →
        TimeTranslateCompactnessConclusion D p K u v

def Lemma_3_3 (D : BoundedDomainData) (N : StabilityNorms D) : Prop :=
  ∀ uStar > 0, InitialContinuityConclusion D N uStar

def Lemma_3_4
    (D : BoundedDomainData) (p : CM2Params) (K : CompactnessData D) : Prop :=
  ∀ u v : ℝ → D.Point → ℝ,
    PositiveGlobalBoundedSolution D p u v →
      UpperEnvelopeMonotonicityConclusion D p K u

def Lemma_3_5
    (D : BoundedDomainData) (p : CM2Params) (C : Paper3Constants D p) : Prop :=
  p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
    0 < p.χ₀ → p.χ₀ < min (p.χ₀ / (2 * p.β)) (chiBeta p) →
      ∀ u v : ℝ → D.Point → ℝ,
        PositiveGlobalBoundedSolution D p u v →
          EventuallyUpperBoundMinimalConclusion D p C u

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

def Lemma_7_1 (D : BoundedDomainData) (K : CompactnessData D) : Prop :=
  ∃ M0 > 0, ∀ mu nu : ℝ, ∀ f : D.Point → ℝ,
    0 < mu → 0 < nu →
      K.neumannResolventGradientBound mu nu f M0

end

end ShenWork.Paper3
