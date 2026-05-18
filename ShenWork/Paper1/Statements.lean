/-
  Statement layer for Shen,
  "Existence, uniqueness, stability, and monotonicity of traveling waves for
  repulsion/attraction chemotaxis models with logistic type source".

  The declarations below formalize the paper-level targets as propositions.
  They are not proofs of the paper theorems.
-/
import ShenWork.Defs

open Filter Topology MeasureTheory

namespace ShenWork.Paper1

noncomputable section

def NonnegativeInitialDatum (u₀ : ℝ → ℝ) : Prop :=
  IsCUnifBdd u₀ ∧ ∀ x, 0 ≤ u₀ x

def StrictlyPositiveAtLeft (u₀ : ℝ → ℝ) : Prop :=
  ∃ δ > 0, ∀ x, δ ≤ u₀ x

def HasInitialDatum (u : ℝ → ℝ → ℝ) (u₀ : ℝ → ℝ) : Prop :=
  ∀ x, u 0 x = u₀ x

def IsGlobalCauchySolutionFrom
    (p : CMParams) (u₀ : ℝ → ℝ) (u v : ℝ → ℝ → ℝ) : Prop :=
  IsGlobalClassicalSolution p u v ∧
    HasInitialDatum u u₀ ∧
    ∀ t x, 0 ≤ t → 0 < u t x

def UniformEventuallyBounded (u : ℝ → ℝ → ℝ) : Prop :=
  ∃ M, ∀ᶠ t in atTop, ∀ x, |u t x| ≤ M

def UniformLimsupLe (u : ℝ → ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ t in atTop, ∀ x, u t x ≤ L + ε

def UniformConvergesToConstant (u : ℝ → ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ T, ∀ t x, T ≤ t → |u t x - a| < ε

def HasWaveRightTailAsymptotic (c κ₁ : ℝ) (U : ℝ → ℝ) : Prop :=
  Tendsto
    (fun x => Real.exp ((κ₁ - kappa c) * x) *
      (U x / Real.exp (-(kappa c) * x) - 1))
    atTop (𝓝 0)

def ShenUpperBoundNegative (c : ℝ) (U : ℝ → ℝ) : Prop :=
  ∀ x, 0 < U x ∧ U x < max 1 (Real.exp (-(kappa c) * x))

def ShenUpperBoundPositive (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop :=
  ∀ x, 0 < U x ∧
    U x < min ((1 / (1 - p.χ)) ^ (1 / p.α)) (Real.exp (-(kappa c) * x))

def WeightedL2InitialCloseness (η : ℝ) (u₀ U : ℝ → ℝ) : Prop :=
  Integrable (fun x : ℝ => Real.exp (2 * η * x) * |u₀ x - U x| ^ 2)

def WeightedL2MovingFrameConvergence
    (η c : ℝ) (u : ℝ → ℝ → ℝ) (U : ℝ → ℝ) : Prop :=
  Tendsto
    (fun t : ℝ =>
      ∫ x : ℝ, Real.exp (2 * η * x) * |u t x - U (x - c * t)| ^ 2)
    atTop (𝓝 0)

def UniformMovingFrameConvergence
    (c : ℝ) (u : ℝ → ℝ → ℝ) (U : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ T, ∀ t x, T ≤ t → |u t x - U (x - c * t)| < ε

structure HeatSemigroupEstimateData where
  lpNorm : ℝ → (ℝ → ℝ) → ℝ
  lqNorm : ℝ → (ℝ → ℝ) → ℝ
  linftyNorm : (ℝ → ℝ) → ℝ
  gradientNorm : ℝ → (ℝ → ℝ) → ℝ
  semigroup : ℝ → (ℝ → ℝ) → ℝ → ℝ
  divergenceSemigroup : ℝ → (ℝ → ℝ) → ℝ → ℝ

def Lemma_2_1 (S : HeatSemigroupEstimateData) : Prop :=
  ∀ p q : ℝ, 1 < p → p ≤ q →
    (∃ Cpq > 0, ∀ t > 0, ∀ u : ℝ → ℝ,
      S.lqNorm q (S.semigroup t u) ≤
        Cpq * t ^ (-(1 / 2 : ℝ) * (1 / p - 1 / q)) *
          Real.exp (-t) * S.lpNorm p u) ∧
    (∃ Cpq > 0, ∀ t > 0, ∀ u : ℝ → ℝ,
      S.gradientNorm q (S.semigroup t u) ≤
        Cpq * t ^ (-(1 / 2 : ℝ) - (1 / 2 : ℝ) * (1 / p - 1 / q)) *
          Real.exp (-t) * S.lpNorm p u) ∧
    (∃ Cp > 0, ∀ t > 0, ∀ u : ℝ → ℝ,
      S.linftyNorm (S.divergenceSemigroup t u) ≤
        Cp * t ^ (-(1 / 2 : ℝ) - (1 / (2 * p))) *
          Real.exp (-t) * S.lpNorm p u)

def PsiDerivativeFormula (u : ℝ → ℝ) (l mu : ℝ) : Prop :=
  ∀ x,
    deriv (fun z => Psi u l mu z) x =
      -(mu / 2) * Real.exp (-Real.sqrt l * x) *
          ∫ y in Set.Iic x, Real.exp (Real.sqrt l * y) * u y
        + (mu / 2) * Real.exp (Real.sqrt l * x) *
          ∫ y in Set.Ioi x, Real.exp (-Real.sqrt l * y) * u y

def Lemma_2_2 : Prop :=
  ∀ u : ℝ → ℝ, ∀ l mu : ℝ, 0 < l → 0 < mu → IsCUnifBdd u →
    (∀ x,
      Psi u l mu x =
        mu / (2 * Real.sqrt l) *
          ∫ y : ℝ, Real.exp (-Real.sqrt l * |x - y|) * u y) ∧
    PsiDerivativeFormula u l mu

def Lemma_2_3 : Prop :=
  ∀ u : ℝ → ℝ, ∀ l mu : ℝ, 0 < l → 0 < mu → IsCUnifBdd u →
    (∀ x, 0 ≤ u x) →
      ∀ x, |deriv (fun z => Psi u l mu z) x| ≤ Real.sqrt l * Psi u l mu x

def Lemma_2_4 : Prop :=
  ∀ M k : ℝ, 1 ≤ M → 0 < k → k < 1 →
    ∀ u : ℝ → ℝ, IsCUnifBdd u →
      (∀ x, 0 ≤ u x) →
      (∀ x, u x ≤ min M (Real.exp (-k * x))) →
        ∀ x, Psi u 1 1 x ≤ min M (1 / (1 - k ^ 2) * Real.exp (-k * x))

structure ExponentialWeight where
  weight : ℝ → ℝ
  smooth : ContDiff ℝ 2 weight
  pos : ∀ x, 0 < weight x
  decay : ∃ k > 0, ∀ x, weight x ≤ Real.exp (-k * |x|)
  deriv_abs_le : ∃ k > 0, ∀ x, |deriv weight x| ≤ k * weight x
  second_deriv_abs_le : ∃ k > 0, ∀ x, |iteratedDeriv 2 weight x| ≤ k * weight x

def Lemma_2_5 : Prop :=
  ∀ pExp gamma l mu : ℝ, 1 < pExp → 0 < gamma → 0 < l → 0 < mu →
    ∃ C > 0, ∀ u : ℝ → ℝ, ∀ psi : ExponentialWeight,
      Integrable (fun x => (u x) ^ (gamma * pExp) * psi.weight x) →
        Integrable
          (fun x =>
            |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp *
              psi.weight x) ∧
        ∫ x : ℝ,
            |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp *
              psi.weight x
          ≤ C * ∫ x : ℝ, (u x) ^ (gamma * pExp) * psi.weight x

/-- Paper1 Proposition 1.1: global existence and boundedness of Cauchy solutions. -/
def Proposition_1_1 : Prop :=
  (∀ p : CMParams, p.χ ≤ 0 →
    ∀ u₀ : ℝ → ℝ, NonnegativeInitialDatum u₀ →
      ∃ u v : ℝ → ℝ → ℝ,
        IsGlobalCauchySolutionFrom p u₀ u v ∧
        (∀ M, (∀ x, u₀ x ≤ M) →
          ∀ t x, 0 ≤ t → u t x ≤ max 1 M) ∧
        UniformLimsupLe u 1) ∧
  (∀ p : CMParams,
    (0 < p.χ ∧ p.α > p.m + p.γ - 1) ∨
      (0 < p.χ ∧
        p.χ < min
          ((p.m + p.γ - 1) / (2 * p.m - 1))
          ((p.m + p.γ - 1) / (p.γ - 1)) ∧
        p.α = p.m + p.γ - 1) →
    ∀ u₀ : ℝ → ℝ, NonnegativeInitialDatum u₀ →
      ∃ u v : ℝ → ℝ → ℝ,
        IsGlobalCauchySolutionFrom p u₀ u v ∧
        UniformEventuallyBounded u ∧
        (0 < p.χ → p.χ < 1 → UniformLimsupLe u ((1 / (1 - p.χ)) ^ (1 / p.α))))

/-- Paper1 Proposition 1.2: stability of the positive constant solution. -/
def Proposition_1_2 : Prop :=
  (∀ p : CMParams, p.χ ≤ 0 →
    ∀ u₀ : ℝ → ℝ, NonnegativeInitialDatum u₀ → StrictlyPositiveAtLeft u₀ →
      ∃ u v : ℝ → ℝ → ℝ,
        IsGlobalCauchySolutionFrom p u₀ u v ∧
        UniformConvergesToConstant u 1) ∧
  (∀ p : CMParams, 0 < p.χ → p.χ < (1 / 2 : ℝ) →
    p.m + p.γ - 1 ≤ p.α →
    ∀ u₀ : ℝ → ℝ, NonnegativeInitialDatum u₀ → StrictlyPositiveAtLeft u₀ →
      ∃ u v : ℝ → ℝ → ℝ,
        IsGlobalCauchySolutionFrom p u₀ u v ∧
        UniformConvergesToConstant u 1)

/-- Paper1 Theorem 1.1: existence of traveling waves. -/
def Theorem_1_1 : Prop :=
  (∀ p : CMParams, p.α ≤ p.m + p.γ - 1 → p.χ ≤ 0 →
    ∀ c : ℝ, cStarLower p < c →
      ∃ U V : ℝ → ℝ,
        IsMonotoneTravelingWave p c U V ∧
        ShenUpperBoundNegative c U ∧
        ∀ κ₁, kappa c < κ₁ →
          κ₁ < min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1) →
          HasWaveRightTailAsymptotic c κ₁ U) ∧
  (∀ p : CMParams, p.α = p.m + p.γ - 1 →
    0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
    ∀ c : ℝ, 2 < c →
      ∃ U V : ℝ → ℝ,
        IsTravelingWave p c U V ∧
        ShenUpperBoundPositive p c U ∧
        ∀ κ₁, kappa c < κ₁ →
          κ₁ < min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1) →
          HasWaveRightTailAsymptotic c κ₁ U)

def StableWaveParameterRegime (p : CMParams) : Prop :=
  (p.χ < 0 ∧ p.α ≤ p.m + p.γ - 1) ∨
    (0 ≤ p.χ ∧ p.χ < chiStar p ∧ p.α = p.m + p.γ - 1)

/-- Paper1 Theorem 1.2: weighted stability of traveling waves. -/
def Theorem_1_2 : Prop :=
  ∀ p : CMParams, StableWaveParameterRegime p →
    ∃ cStarStar > 0, ∀ c : ℝ, cStarStar < c →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        ∀ η : ℝ, kappa c < η → η < 1 / (1 + |p.χ| ^ (1 / 6)) →
          ∀ u₀ : ℝ → ℝ,
            NonnegativeInitialDatum u₀ →
            StrictlyPositiveAtLeft u₀ →
            WeightedL2InitialCloseness η u₀ U →
            ∃ u v : ℝ → ℝ → ℝ,
              IsGlobalCauchySolutionFrom p u₀ u v ∧
              WeightedL2MovingFrameConvergence η c u U ∧
              UniformMovingFrameConvergence c u U

/-- Paper1 Theorem 1.3: uniqueness of traveling waves with the prescribed right tail. -/
def Theorem_1_3 : Prop :=
  ∀ p : CMParams, StableWaveParameterRegime p →
    ∃ cStarStar > 0, ∀ c : ℝ, cStarStar < c →
      ∀ U₁ V₁ U₂ V₂ : ℝ → ℝ,
        IsTravelingWave p c U₁ V₁ →
        IsTravelingWave p c U₂ V₂ →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧
          HasWaveRightTailAsymptotic c κ₁ U₁ ∧
          HasWaveRightTailAsymptotic c κ₁ U₂) →
        (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x)

end

end ShenWork.Paper1
