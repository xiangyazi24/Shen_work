/-
  Statement layer for Chen-Ruau-Shen,
  "Chemotaxis models with signal-dependent sensitivity and a logistic-type
  source, I: Boundedness and global existence".

  This file introduces a bounded-domain PDE interface and states the paper's
  main results against that interface.  It deliberately does not reuse the toy
  predicates in `Paper2/Defs.lean`.
-/
import ShenWork.Paper2.Defs

open Filter Topology

namespace ShenWork.Paper2

noncomputable section

def positivePart (r : ℝ) : ℝ := max r 0

/--
Abstract data for the smooth bounded Neumann domain used in Paper2.

The differential operators are intentionally bundled here: the statement layer
can express the paper PDE now, while later analytic work can instantiate these
fields for a concrete smooth bounded domain in `ℝ^N`.
-/
structure BoundedDomainData where
  Point : Type
  inside : Set Point
  boundary : Set Point
  volume : ℝ
  supNorm : (Point → ℝ) → ℝ
  infValue : (Point → ℝ) → ℝ
  integral : (Point → ℝ) → ℝ
  timeDeriv : (ℝ → Point → ℝ) → ℝ → Point → ℝ
  laplacian : (Point → ℝ) → Point → ℝ
  chemotaxisDiv : CM2Params → (Point → ℝ) → (Point → ℝ) → Point → ℝ
  normalDeriv : (Point → ℝ) → Point → ℝ
  initialAdmissible : (Point → ℝ) → Prop
  classicalRegularity : ℝ → (ℝ → Point → ℝ) → (ℝ → Point → ℝ) → Prop

def IsPaper2ClassicalSolution
    (D : BoundedDomainData) (p : CM2Params) (T : ℝ)
    (u v : ℝ → D.Point → ℝ) : Prop :=
  0 < T ∧
    D.classicalRegularity T u v ∧
    (∀ t x, 0 < t → t < T → x ∈ D.inside → 0 < u t x) ∧
    (∀ t x, 0 < t → t < T → x ∈ D.inside →
      D.timeDeriv u t x =
        D.laplacian (u t) x
          - p.χ₀ * D.chemotaxisDiv p (u t) (v t) x
          + u t x * (p.a - p.b * (u t x) ^ p.α)) ∧
    (∀ t x, 0 < t → t < T → x ∈ D.inside →
      0 = D.laplacian (v t) x - p.μ * v t x + p.ν * (u t x) ^ p.γ) ∧
    (∀ t x, 0 < t → t < T → x ∈ D.boundary →
      D.normalDeriv (u t) x = 0 ∧ D.normalDeriv (v t) x = 0)

def IsPaper2GlobalClassicalSolution
    (D : BoundedDomainData) (p : CM2Params)
    (u v : ℝ → D.Point → ℝ) : Prop :=
  ∀ T > 0, IsPaper2ClassicalSolution D p T u v

def InitialTrace
    (D : BoundedDomainData) (u₀ : D.Point → ℝ) (u : ℝ → D.Point → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
    D.supNorm (fun x => u t x - u₀ x) < ε

def PositiveInitialDatum (D : BoundedDomainData) (u₀ : D.Point → ℝ) : Prop :=
  D.initialAdmissible u₀ ∧ ∀ x, x ∈ D.inside → 0 < u₀ x

def IsPaper2Bounded (D : BoundedDomainData) (u : ℝ → D.Point → ℝ) : Prop :=
  ∃ M, ∀ᶠ t in atTop, D.supNorm (u t) ≤ M

def FiniteHorizonAlternative
    (D : BoundedDomainData) (Tmax : ℝ) (u : ℝ → D.Point → ℝ) : Prop :=
  (∀ M, ∃ t x, 0 < t ∧ t < Tmax ∧ x ∈ D.inside ∧ M < u t x) ∨
    (∀ δ > 0, ∃ t x, 0 < t ∧ t < Tmax ∧ x ∈ D.inside ∧ u t x < δ)

def MGeOneFiniteHorizonAlternative
    (D : BoundedDomainData) (Tmax : ℝ) (u : ℝ → D.Point → ℝ) : Prop :=
  ∀ M, ∃ t x, 0 < t ∧ t < Tmax ∧ x ∈ D.inside ∧ M < u t x

def chiBeta (p : CM2Params) : ℝ :=
  2 * (2 * p.β - 1) / max 2 (p.γ * (p.N : ℝ))

structure Paper2Constants (p : CM2Params) where
  K : ℝ
  K_nonneg : 0 ≤ K

def StrongLogisticCondition (p : CM2Params) (C : Paper2Constants p) : Prop :=
  (p.β ≥ 0 ∧ p.α > p.m + p.γ - 1) ∨
    (p.β ≥ 1 / 2 ∧ p.α > 2 * p.m + p.γ - 2) ∨
    (p.β ≥ 0 ∧ p.α = p.m + p.γ - 1 ∧
      (positivePart ((p.N : ℝ) * p.α - 2) = 0 ∨
        p.χ₀ <
          ((positivePart ((p.N : ℝ) * p.α - 2) + 2 * p.m) * p.b) /
            (positivePart ((p.N : ℝ) * p.α - 2) *
              (p.ν + Psi_beta p.β * C.K)))) ∨
    (p.β ≥ 1 / 2 ∧ p.α = 2 * p.m + p.γ - 2 ∧
      (positivePart ((p.N : ℝ) * p.α - 2) = 0 ∨
        p.χ₀ <
          Real.sqrt
            (8 * p.b /
              (positivePart ((p.N : ℝ) * p.α - 2) *
                Theta_beta (2 * p.β - 1) * C.K))))

/-- Paper2 Proposition 1.1: local existence and blow-up alternative. -/
def Proposition_1_1 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
    ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p Tmax u v ∧
      InitialTrace D u₀ u ∧
      FiniteHorizonAlternative D Tmax u ∧
      (1 ≤ p.m → MGeOneFiniteHorizonAlternative D Tmax u)

/-- Paper2 Theorem 1.1: boundedness/global existence for negative sensitivity. -/
def Theorem_1_1 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  p.χ₀ ≤ 0 →
    (0 < p.a → 0 < p.b →
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2GlobalClassicalSolution D p u v ∧
          InitialTrace D u₀ u ∧
          ∀ t > 0, D.supNorm (u t) ≤ max (D.supNorm u₀) ((p.a / p.b) ^ (1 / p.α))) ∧
    (p.a = 0 → p.b = 0 →
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2GlobalClassicalSolution D p u v ∧
          InitialTrace D u₀ u ∧
          ∀ t > 0, D.supNorm (u t) ≤ D.supNorm u₀)

/-- Paper2 Theorem 1.2: boundedness/global existence for weak nonlinear cross diffusion. -/
def Theorem_1_2 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  0 ≤ p.a → 0 ≤ p.b → 1 ≤ p.β →
    ((0 < p.m → p.m < 1 →
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2ClassicalSolution D p Tmax u v ∧ IsPaper2Bounded D u) ∧
    (p.m = 1 → p.χ₀ < chiBeta p →
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2GlobalClassicalSolution D p u v ∧ IsPaper2Bounded D u))

/-- Paper2 Theorem 1.3: boundedness/global existence under a strong logistic source. -/
def Theorem_1_3 (D : BoundedDomainData) (p : CM2Params) (C : Paper2Constants p) : Prop :=
  0 < p.a → 0 < p.b → 0 < p.m → StrongLogisticCondition p C →
    (∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
      ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
        IsPaper2ClassicalSolution D p Tmax u v ∧ IsPaper2Bounded D u) ∧
    (1 ≤ p.m →
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2GlobalClassicalSolution D p u v ∧ IsPaper2Bounded D u)

end

end ShenWork.Paper2
