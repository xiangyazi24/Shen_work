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

def sigma
    (p : CM2Params) (uStar vStar lambdaN : ℝ) : ℝ :=
  -lambdaN +
    p.χ₀ * p.ν * p.γ *
      (uStar ^ (p.m + p.γ - 1) * lambdaN) /
        ((1 + vStar) ^ p.β * (p.μ + lambdaN)) -
    p.a * p.α

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
