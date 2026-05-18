/-
  Statement layer for Chen-Ruau-Shen,
  "Chemotaxis models with signal-dependent sensitivity and a logistic-type
  source, II: Persistence and stabilization".

  The paper's main results are Theorems 2.1--2.5.  They are stated here against
  the non-toy bounded-domain PDE interface from `Paper2/Statements.lean`.
-/
import ShenWork.Paper2.Statements
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

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
  gaussianLowerConst : ℝ
  gaussianLowerConst_pos : 0 < gaussianLowerConst

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
    (hβ : 1 < p.β) :
    0 < chiBarFormula p := by
  unfold chiBarFormula
  by_cases hm_eq : p.m = 1
  · rw [if_pos hm_eq]
    apply div_pos ha
    exact mul_pos (mul_pos (by norm_num) p.hμ)
      (Theta_beta_pos (by linarith))
  · rw [if_neg hm_eq]
    apply div_pos hb
    exact mul_pos p.hμ (Theta_beta_pos (by linarith))

lemma chiBarFormula_nonneg
    (p : CM2Params) (hβ : 1 < p.β) :
    0 ≤ chiBarFormula p := by
  unfold chiBarFormula
  by_cases hm_eq : p.m = 1
  · rw [if_pos hm_eq]
    apply div_nonneg p.ha
    exact (mul_pos (mul_pos (by norm_num) p.hμ)
      (Theta_beta_pos (by linarith))).le
  · rw [if_neg hm_eq]
    apply div_nonneg p.hb
    exact (mul_pos p.hμ (Theta_beta_pos (by linarith))).le

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
    (hm : 1 ≤ p.m) (hβ : 1 < p.β) (huStar : 0 < uStar) :
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
    (hm : 1 ≤ p.m) (hβ : 1 < p.β) (huStar : 0 < uStar) :
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
    (p : CM2Params) (uStar : ℝ) (hβ : 1 < p.β) :
    0 ≤ chiStrong2Formula p uStar := by
  unfold chiStrong2Formula
  exact le_min (chiBarFormula_nonneg p hβ) (Real.sqrt_nonneg _)

lemma chiStrong4Formula_nonneg
    (p : CM2Params) {M0 uStar : ℝ}
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m) (hβ : 1 < p.β) (huStar : 0 < uStar) :
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

def MinimalGlobalStabilityCondition
    (D : BoundedDomainData) (p : CM2Params) (C : Paper3Constants D p)
    (uStar : ℝ) : Prop :=
  (0 < p.χ₀ ∧ p.χ₀ < C.chiMinimal1 uStar) ∨
    (p.γ = 1 ∧ 0 < p.χ₀ ∧ p.χ₀ < C.chiMinimal2 uStar)

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
    0 < p.χ₀ → p.χ₀ < min (chiBeta p / 2) (Real.sqrt (chiBeta p)) →
      ∀ uStar > 0, ∀ u v : ℝ → D.Point → ℝ,
        PositiveGlobalBoundedSolution D p u v →
        HasInitialMass D u uStar →
          EventuallyLowerBound D v
            (minimalVLowerFormula
              C.gaussianLowerConst p.γ uStar (C.eventualMinimalUBound uStar))

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

def Lemma_A_2
    (D : BoundedDomainData) (p : CM2Params)
    (S : SemigroupEstimateData D) : Prop :=
  Paper2.Lemma_2_1 D p S

lemma Lemma_A_2.paper2
    {D : BoundedDomainData} {p : CM2Params} {S : SemigroupEstimateData D}
    (h : Lemma_A_2 D p S) :
    Paper2.Lemma_2_1 D p S :=
  h

def Lemma_A_3
    (D : BoundedDomainData) (S : SemigroupEstimateData D) : Prop :=
  Paper2.Lemma_2_2 D S

lemma Lemma_A_3.paper2
    {D : BoundedDomainData} {S : SemigroupEstimateData D}
    (h : Lemma_A_3 D S) :
    Paper2.Lemma_2_2 D S :=
  h

def Lemma_A_4
    (D : BoundedDomainData) (p : CM2Params)
    (S : SemigroupEstimateData D) : Prop :=
  Paper2.Lemma_2_3 D p S

lemma Lemma_A_4.paper2
    {D : BoundedDomainData} {p : CM2Params} {S : SemigroupEstimateData D}
    (h : Lemma_A_4 D p S) :
    Paper2.Lemma_2_3 D p S :=
  h

def Lemma_A_5
    (D : BoundedDomainData) (p : CM2Params)
    (S : SemigroupEstimateData D) : Prop :=
  Paper2.Lemma_2_4 D p S

lemma Lemma_A_5.paper2
    {D : BoundedDomainData} {p : CM2Params} {S : SemigroupEstimateData D}
    (h : Lemma_A_5 D p S) :
    Paper2.Lemma_2_4 D p S :=
  h

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

def Lemma_A_6 : Prop :=
  ∀ alpha gamma,
    0 < alpha → 0 < gamma →
      2 * gamma ≤ alpha + 1 →
        ∀ uStar > 0,
          PowerDifferenceInequality (CAlphaGamma alpha gamma) alpha gamma uStar

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

end

end ShenWork.Paper3
