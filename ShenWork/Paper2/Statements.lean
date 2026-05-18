/-
  Statement layer for Chen-Ruau-Shen,
  "Chemotaxis models with signal-dependent sensitivity and a logistic-type
  source, I: Boundedness and global existence".

  This file introduces a bounded-domain PDE interface and states the paper's
  main results against that interface.  It deliberately does not reuse the toy
  predicates in `Paper2/Defs.lean`.
-/
import ShenWork.Paper2.Defs
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

open Filter Topology

namespace ShenWork.Paper2

noncomputable section

def positivePart (r : ℝ) : ℝ := max r 0

lemma positivePart_nonneg (r : ℝ) : 0 ≤ positivePart r := by
  exact le_max_right r 0

lemma le_positivePart (r : ℝ) : r ≤ positivePart r := by
  exact le_max_left r 0

lemma positivePart_eq_self_of_nonneg {r : ℝ} (hr : 0 ≤ r) :
    positivePart r = r := by
  simp [positivePart, hr]

lemma positivePart_eq_zero_of_nonpos {r : ℝ} (hr : r ≤ 0) :
    positivePart r = 0 := by
  simp [positivePart, hr]

lemma positivePart_eq_zero_iff {r : ℝ} :
    positivePart r = 0 ↔ r ≤ 0 := by
  constructor
  · intro h
    have hr : r ≤ positivePart r := le_positivePart r
    linarith
  · exact positivePart_eq_zero_of_nonpos

lemma positivePart_pos_iff {r : ℝ} :
    0 < positivePart r ↔ 0 < r := by
  constructor
  · intro h
    by_contra hn
    have hzero : positivePart r = 0 :=
      positivePart_eq_zero_of_nonpos (le_of_not_gt hn)
    linarith
  · intro hr
    have hle : r ≤ positivePart r := le_positivePart r
    linarith

lemma positivePart_eq_self_iff {r : ℝ} :
    positivePart r = r ↔ 0 ≤ r := by
  constructor
  · intro h
    rw [← h]
    exact positivePart_nonneg r
  · exact positivePart_eq_self_of_nonneg

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
  gradNorm : (Point → ℝ) → Point → ℝ
  timeDeriv : (ℝ → Point → ℝ) → ℝ → Point → ℝ
  laplacian : (Point → ℝ) → Point → ℝ
  chemotaxisDiv : CM2Params → (Point → ℝ) → (Point → ℝ) → Point → ℝ
  crossDiffusionEnergyTerm : CM2Params → ℝ → (Point → ℝ) → (Point → ℝ) → ℝ
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

def IsPaper2BoundedBefore
    (D : BoundedDomainData) (Tmax : ℝ) (u : ℝ → D.Point → ℝ) : Prop :=
  ∃ M, ∀ t, 0 < t → t < Tmax → D.supNorm (u t) ≤ M

lemma IsPaper2BoundedBefore.bound
    {D : BoundedDomainData} {Tmax : ℝ} {u : ℝ → D.Point → ℝ}
    (h : IsPaper2BoundedBefore D Tmax u)
    {t : ℝ} (ht0 : 0 < t) (htT : t < Tmax) :
    ∃ M, D.supNorm (u t) ≤ M := by
  rcases h with ⟨M, hM⟩
  exact ⟨M, hM t ht0 htT⟩

def LpPowerBoundedBefore
    (D : BoundedDomainData) (pExp Tmax : ℝ) (u : ℝ → D.Point → ℝ) : Prop :=
  ∃ C, ∀ t, 0 < t → t < Tmax →
    D.integral (fun x => (u t x) ^ pExp) ≤ C

lemma LpPowerBoundedBefore.bound
    {D : BoundedDomainData} {pExp Tmax : ℝ} {u : ℝ → D.Point → ℝ}
    (h : LpPowerBoundedBefore D pExp Tmax u)
    {t : ℝ} (ht0 : 0 < t) (htT : t < Tmax) :
    ∃ C, D.integral (fun x => (u t x) ^ pExp) ≤ C := by
  rcases h with ⟨C, hC⟩
  exact ⟨C, hC t ht0 htT⟩

def MassConservedBefore
    (D : BoundedDomainData) (Tmax : ℝ)
    (u₀ : D.Point → ℝ) (u : ℝ → D.Point → ℝ) : Prop :=
  ∀ t, 0 < t → t < Tmax → D.integral (u t) = D.integral u₀

lemma MassConservedBefore.eq
    {D : BoundedDomainData} {Tmax : ℝ}
    {u₀ : D.Point → ℝ} {u : ℝ → D.Point → ℝ}
    (h : MassConservedBefore D Tmax u₀ u)
    {t : ℝ} (ht0 : 0 < t) (htT : t < Tmax) :
    D.integral (u t) = D.integral u₀ :=
  h t ht0 htT

def LogisticMassUpperBoundBefore
    (D : BoundedDomainData) (p : CM2Params) (Tmax : ℝ)
    (u₀ : D.Point → ℝ) (u : ℝ → D.Point → ℝ) : Prop :=
  ∀ t, 0 < t → t < Tmax →
    D.integral (u t) ≤
      max (D.integral u₀) (((p.a / p.b) ^ (1 / p.α)) * D.volume)

lemma LogisticMassUpperBoundBefore.bound
    {D : BoundedDomainData} {p : CM2Params} {Tmax : ℝ}
    {u₀ : D.Point → ℝ} {u : ℝ → D.Point → ℝ}
    (h : LogisticMassUpperBoundBefore D p Tmax u₀ u)
    {t : ℝ} (ht0 : 0 < t) (htT : t < Tmax) :
    D.integral (u t) ≤
      max (D.integral u₀) (((p.a / p.b) ^ (1 / p.α)) * D.volume) :=
  h t ht0 htT

def SupNormNonincreasingOn
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ) (I : Set ℝ) : Prop :=
  ∀ t₁, t₁ ∈ I → ∀ t₂, t₂ ∈ I → t₁ ≤ t₂ →
    D.supNorm (u t₂) ≤ D.supNorm (u t₁)

def WeightedGradientEstimate
    (D : BoundedDomainData) (pExp beta gamma Mstar T : ℝ)
    (u v : ℝ → D.Point → ℝ) : Prop :=
  ∀ t, 0 < t → t < T →
    D.integral
        (fun x => (D.gradNorm (v t) x) ^ (2 * pExp) / (v t x) ^ pExp) ≤
      Mstar * D.integral (fun x => (u t x) ^ (gamma * pExp)) ∧
    D.integral
        (fun x =>
          (D.gradNorm (v t) x) ^ (2 * pExp) /
            (1 + v t x) ^ ((1 + beta) * pExp)) ≤
      (Theta_beta beta) ^ pExp * Mstar *
        D.integral (fun x => (u t x) ^ (gamma * pExp))

def WeightedSignalEstimate
    (D : BoundedDomainData) (pExp beta gamma eps Ceps T : ℝ)
    (u v : ℝ → D.Point → ℝ) : Prop :=
  ∀ t, 0 < t → t < T →
    D.integral (fun x => (v t x) ^ (pExp + 1) / (1 + v t x) ^ beta) ≤
      eps *
          D.integral
            (fun x => (u t x) ^ (gamma * (pExp + 1)) / (1 + v t x) ^ beta) +
        Ceps *
          (D.integral
            (fun x => v t x / (1 + v t x) ^ (beta / (pExp + 1)))) ^ (pExp + 1)

lemma WeightedGradientEstimate.first
    {D : BoundedDomainData} {pExp beta gamma Mstar T : ℝ}
    {u v : ℝ → D.Point → ℝ}
    (h : WeightedGradientEstimate D pExp beta gamma Mstar T u v)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    D.integral
        (fun x => (D.gradNorm (v t) x) ^ (2 * pExp) / (v t x) ^ pExp) ≤
      Mstar * D.integral (fun x => (u t x) ^ (gamma * pExp)) :=
  (h t ht0 htT).1

lemma WeightedGradientEstimate.second
    {D : BoundedDomainData} {pExp beta gamma Mstar T : ℝ}
    {u v : ℝ → D.Point → ℝ}
    (h : WeightedGradientEstimate D pExp beta gamma Mstar T u v)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    D.integral
        (fun x =>
          (D.gradNorm (v t) x) ^ (2 * pExp) /
            (1 + v t x) ^ ((1 + beta) * pExp)) ≤
      (Theta_beta beta) ^ pExp * Mstar *
        D.integral (fun x => (u t x) ^ (gamma * pExp)) :=
  (h t ht0 htT).2

lemma WeightedSignalEstimate.bound
    {D : BoundedDomainData} {pExp beta gamma eps Ceps T : ℝ}
    {u v : ℝ → D.Point → ℝ}
    (h : WeightedSignalEstimate D pExp beta gamma eps Ceps T u v)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    D.integral (fun x => (v t x) ^ (pExp + 1) / (1 + v t x) ^ beta) ≤
      eps *
          D.integral
            (fun x => (u t x) ^ (gamma * (pExp + 1)) / (1 + v t x) ^ beta) +
        Ceps *
          (D.integral
            (fun x => v t x / (1 + v t x) ^ (beta / (pExp + 1)))) ^ (pExp + 1) :=
  h t ht0 htT

def LpBootstrapEnergyInequality
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop :=
  ∀ pExp, p0 ≤ pExp →
    ∃ A > 0, ∃ B > 0, ∃ K > 0, ∃ L,
      ∀ t, 0 < t → t < T →
        (1 / pExp) *
            deriv (fun τ => D.integral (fun x => (u τ x) ^ pExp)) t +
          A *
            D.integral
              (fun x =>
                (D.gradNorm (fun y => (u t y) ^ (pExp / 2)) x) ^ 2) +
          B * D.integral (fun x => (u t x) ^ pExp) ≤
        K * D.integral (fun x => (u t x) ^ (pExp + rho)) + L

def CrossDiffusionBootstrapEstimate
    (D : BoundedDomainData) (p : CM2Params) (T rho : ℝ)
    (u v : ℝ → D.Point → ℝ) : Prop :=
  ∀ eps > 0, ∀ pExp > 1, ∃ Ceps,
    ∀ t, 0 < t → t < T →
      D.crossDiffusionEnergyTerm p pExp (u t) (v t) ≤
        eps *
            D.integral
              (fun x => (u t x) ^ (pExp - 2) * (D.gradNorm (u t) x) ^ 2) +
          Ceps * D.integral (fun x => (u t x) ^ (pExp + rho))

def LpMassGradientInterpolationEstimate
    (D : BoundedDomainData) (pExp eps Ceps T : ℝ)
    (u : ℝ → D.Point → ℝ) : Prop :=
  ∀ t, 0 < t → t < T →
    D.integral (fun x => (u t x) ^ pExp) ≤
      eps *
          D.integral
            (fun x => (u t x) ^ (pExp - 2) * (D.gradNorm (u t) x) ^ 2) +
        Ceps * (D.integral (u t)) ^ pExp

lemma LpMassGradientInterpolationEstimate.bound
    {D : BoundedDomainData} {pExp eps Ceps T : ℝ}
    {u : ℝ → D.Point → ℝ}
    (h : LpMassGradientInterpolationEstimate D pExp eps Ceps T u)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    D.integral (fun x => (u t x) ^ pExp) ≤
      eps *
          D.integral
            (fun x => (u t x) ^ (pExp - 2) * (D.gradNorm (u t) x) ^ 2) +
        Ceps * (D.integral (u t)) ^ pExp :=
  h t ht0 htT

lemma CrossDiffusionBootstrapEstimate.bound
    {D : BoundedDomainData} {p : CM2Params} {T rho : ℝ}
    {u v : ℝ → D.Point → ℝ}
    (h : CrossDiffusionBootstrapEstimate D p T rho u v)
    {eps pExp t : ℝ} (heps : 0 < eps) (hpExp : 1 < pExp)
    (ht0 : 0 < t) (htT : t < T) :
    ∃ Ceps,
      D.crossDiffusionEnergyTerm p pExp (u t) (v t) ≤
        eps *
            D.integral
              (fun x => (u t x) ^ (pExp - 2) * (D.gradNorm (u t) x) ^ 2) +
          Ceps * D.integral (fun x => (u t x) ^ (pExp + rho)) := by
  rcases h eps heps pExp hpExp with ⟨Ceps, hCeps⟩
  exact ⟨Ceps, hCeps t ht0 htT⟩

def FiniteHorizonAlternative
    (D : BoundedDomainData) (Tmax : ℝ) (u : ℝ → D.Point → ℝ) : Prop :=
  (∀ M, ∃ t x, 0 < t ∧ t < Tmax ∧ x ∈ D.inside ∧ M < u t x) ∨
    (∀ δ > 0, ∃ t x, 0 < t ∧ t < Tmax ∧ x ∈ D.inside ∧ u t x < δ)

def MGeOneFiniteHorizonAlternative
    (D : BoundedDomainData) (Tmax : ℝ) (u : ℝ → D.Point → ℝ) : Prop :=
  ∀ M, ∃ t x, 0 < t ∧ t < Tmax ∧ x ∈ D.inside ∧ M < u t x

def chiBeta (p : CM2Params) : ℝ :=
  2 * (2 * p.β - 1) / max 2 (p.γ * (p.N : ℝ))

lemma chiBeta_denom_pos (p : CM2Params) :
    0 < max (2 : ℝ) (p.γ * (p.N : ℝ)) :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)

lemma chiBeta_pos_of_one_le_beta (p : CM2Params) (hβ : 1 ≤ p.β) :
    0 < chiBeta p := by
  unfold chiBeta
  have hnum : 0 < 2 * (2 * p.β - 1) := by nlinarith
  exact div_pos hnum (chiBeta_denom_pos p)

lemma chiBeta_half_pos_of_one_le_beta (p : CM2Params) (hβ : 1 ≤ p.β) :
    0 < chiBeta p / 2 := by
  exact half_pos (chiBeta_pos_of_one_le_beta p hβ)

lemma sqrt_chiBeta_pos_of_one_le_beta (p : CM2Params) (hβ : 1 ≤ p.β) :
    0 < Real.sqrt (chiBeta p) := by
  exact Real.sqrt_pos.mpr (chiBeta_pos_of_one_le_beta p hβ)

lemma min_chiBeta_half_sqrt_pos_of_one_le_beta
    (p : CM2Params) (hβ : 1 ≤ p.β) :
    0 < min (chiBeta p / 2) (Real.sqrt (chiBeta p)) :=
  lt_min
    (chiBeta_half_pos_of_one_le_beta p hβ)
    (sqrt_chiBeta_pos_of_one_le_beta p hβ)

lemma lt_chiBeta_of_lt_min_half_sqrt
    (p : CM2Params) {chi : ℝ} (hβ : 1 ≤ p.β)
    (hchi : chi < min (chiBeta p / 2) (Real.sqrt (chiBeta p))) :
    chi < chiBeta p := by
  have hhalf : chi < chiBeta p / 2 := lt_of_lt_of_le hchi (min_le_left _ _)
  have hpos : 0 < chiBeta p := chiBeta_pos_of_one_le_beta p hβ
  nlinarith

lemma chiBeta_nonneg_of_half_le_beta (p : CM2Params) (hβ : (1 / 2 : ℝ) ≤ p.β) :
    0 ≤ chiBeta p := by
  unfold chiBeta
  apply div_nonneg
  · nlinarith
  · exact le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_max_left _ _)

lemma chiBeta_pos_of_half_lt_beta (p : CM2Params) (hβ : (1 / 2 : ℝ) < p.β) :
    0 < chiBeta p := by
  unfold chiBeta
  apply div_pos
  · nlinarith
  · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)

lemma chiBeta_le_two_beta_sub_one (p : CM2Params) (hβ : (1 / 2 : ℝ) ≤ p.β) :
    chiBeta p ≤ 2 * p.β - 1 := by
  unfold chiBeta
  have hnum_nonneg : 0 ≤ 2 * (2 * p.β - 1) := by nlinarith
  have hden_ge_two : (2 : ℝ) ≤ max 2 (p.γ * (p.N : ℝ)) := le_max_left _ _
  have hden_pos : 0 < max (2 : ℝ) (p.γ * (p.N : ℝ)) :=
    lt_of_lt_of_le (by norm_num) hden_ge_two
  have hmul :
      2 * (2 * p.β - 1) / max 2 (p.γ * (p.N : ℝ)) ≤
        2 * (2 * p.β - 1) / 2 := by
    exact div_le_div_of_nonneg_left hnum_nonneg (by norm_num) hden_ge_two
  nlinarith

lemma chiBeta_eq_two_beta_sub_one_of_gamma_mul_N_le_two
    (p : CM2Params) (hden : p.γ * (p.N : ℝ) ≤ 2) :
    chiBeta p = 2 * p.β - 1 := by
  unfold chiBeta
  rw [max_eq_left hden]
  ring

lemma chiBeta_lt_two_beta_sub_one_of_two_lt_denom
    (p : CM2Params) (hβ : (1 / 2 : ℝ) < p.β)
    (hden : (2 : ℝ) < max 2 (p.γ * (p.N : ℝ))) :
    chiBeta p < 2 * p.β - 1 := by
  unfold chiBeta
  have hnum_pos : 0 < 2 * (2 * p.β - 1) := by nlinarith
  calc
    2 * (2 * p.β - 1) / max 2 (p.γ * (p.N : ℝ))
        < 2 * (2 * p.β - 1) / 2 := by
          exact div_lt_div_of_pos_left hnum_pos (by norm_num) hden
    _ = 2 * p.β - 1 := by ring

lemma chiBeta_lt_of_lt_two_beta_sub_one
    (p : CM2Params) {chi : ℝ} (hβ : (1 / 2 : ℝ) < p.β)
    (hden : (2 : ℝ) < max 2 (p.γ * (p.N : ℝ)))
    (hchi : chi < chiBeta p) :
    chi < 2 * p.β - 1 :=
  lt_trans hchi (chiBeta_lt_two_beta_sub_one_of_two_lt_denom p hβ hden)

lemma chiBeta_lt_two_beta_sub_one_of_two_lt_gamma_mul_N
    (p : CM2Params) (hβ : (1 / 2 : ℝ) < p.β)
    (hden : (2 : ℝ) < p.γ * (p.N : ℝ)) :
    chiBeta p < 2 * p.β - 1 :=
  chiBeta_lt_two_beta_sub_one_of_two_lt_denom p hβ
    (by rwa [max_eq_right hden.le])

lemma chiBeta_lt_of_lt_two_beta_sub_one_gamma_mul_N
    (p : CM2Params) {chi : ℝ} (hβ : (1 / 2 : ℝ) < p.β)
    (hden : (2 : ℝ) < p.γ * (p.N : ℝ))
    (hchi : chi < chiBeta p) :
    chi < 2 * p.β - 1 :=
  lt_trans hchi (chiBeta_lt_two_beta_sub_one_of_two_lt_gamma_mul_N p hβ hden)

structure SemigroupEstimateData (D : BoundedDomainData) where
  lpNorm : ℝ → (D.Point → ℝ) → ℝ
  vectorLpNorm : ℝ → (D.Point → ℝ) → ℝ
  fractionalNorm : ℝ → ℝ → (D.Point → ℝ) → ℝ
  semigroup : ℝ → (D.Point → ℝ) → D.Point → ℝ
  divergenceSemigroup : ℝ → (D.Point → ℝ) → D.Point → ℝ
  embeddingNorm : ℝ → ℝ → ℝ → (D.Point → ℝ) → ℝ

def Lemma_2_1 (D : BoundedDomainData) (p : CM2Params)
    (S : SemigroupEstimateData D) : Prop :=
  (∀ sigma q delta, 0 ≤ sigma → 1 ≤ q → 0 < delta → delta < p.μ →
    ∃ C > 0, ∀ t > 0, ∀ u : D.Point → ℝ,
      S.fractionalNorm sigma q (S.semigroup t u) ≤
        C * t ^ (-sigma) * Real.exp (-delta * t) * S.lpNorm q u) ∧
  (∀ sigma, 0 < sigma → sigma ≤ 1 →
    ∃ C > 0, ∀ t > 0, ∀ u : D.Point → ℝ,
      S.lpNorm 2 (fun x => S.semigroup t u x - u x) ≤
        C * t ^ sigma * S.fractionalNorm sigma 2 u)

lemma Lemma_2_1.fractional_decay
    {D : BoundedDomainData} {p : CM2Params} {S : SemigroupEstimateData D}
    (h : Lemma_2_1 D p S)
    {sigma q delta : ℝ}
    (hsigma : 0 ≤ sigma) (hq : 1 ≤ q)
    (hdelta_pos : 0 < delta) (hdelta_mu : delta < p.μ) :
    ∃ C > 0, ∀ t > 0, ∀ u : D.Point → ℝ,
      S.fractionalNorm sigma q (S.semigroup t u) ≤
        C * t ^ (-sigma) * Real.exp (-delta * t) * S.lpNorm q u :=
  h.1 sigma q delta hsigma hq hdelta_pos hdelta_mu

lemma Lemma_2_1.semigroup_continuity
    {D : BoundedDomainData} {p : CM2Params} {S : SemigroupEstimateData D}
    (h : Lemma_2_1 D p S)
    {sigma : ℝ} (hsigma_pos : 0 < sigma) (hsigma_one : sigma ≤ 1) :
    ∃ C > 0, ∀ t > 0, ∀ u : D.Point → ℝ,
      S.lpNorm 2 (fun x => S.semigroup t u x - u x) ≤
        C * t ^ sigma * S.fractionalNorm sigma 2 u :=
  h.2 sigma hsigma_pos hsigma_one

def Lemma_2_2 (D : BoundedDomainData) (S : SemigroupEstimateData D) : Prop :=
  (∀ sigma q k r, 0 ≤ sigma → 1 ≤ q → q ≤ r →
    k - (D.volume / r) < 2 * sigma - D.volume / q →
      ∃ C > 0, ∀ u : D.Point → ℝ,
        S.embeddingNorm k r sigma u ≤ C * S.fractionalNorm sigma q u) ∧
  (∀ sigma q theta, 0 ≤ theta → theta < 2 * sigma - D.volume / q →
      ∃ C > 0, ∀ u : D.Point → ℝ,
        S.embeddingNorm theta q sigma u ≤ C * S.fractionalNorm sigma q u)

lemma Lemma_2_2.embedding_general
    {D : BoundedDomainData} {S : SemigroupEstimateData D}
    (h : Lemma_2_2 D S)
    {sigma q k r : ℝ}
    (hsigma : 0 ≤ sigma) (hq : 1 ≤ q) (hqr : q ≤ r)
    (hcond : k - (D.volume / r) < 2 * sigma - D.volume / q) :
    ∃ C > 0, ∀ u : D.Point → ℝ,
      S.embeddingNorm k r sigma u ≤ C * S.fractionalNorm sigma q u :=
  h.1 sigma q k r hsigma hq hqr hcond

lemma Lemma_2_2.embedding_same_q
    {D : BoundedDomainData} {S : SemigroupEstimateData D}
    (h : Lemma_2_2 D S)
    {sigma q theta : ℝ}
    (htheta_nonneg : 0 ≤ theta)
    (hcond : theta < 2 * sigma - D.volume / q) :
    ∃ C > 0, ∀ u : D.Point → ℝ,
      S.embeddingNorm theta q sigma u ≤ C * S.fractionalNorm sigma q u :=
  h.2 sigma q theta htheta_nonneg hcond

def Lemma_2_3 (D : BoundedDomainData) (p : CM2Params)
    (S : SemigroupEstimateData D) : Prop :=
  ∃ C > 0, ∀ q > 1, ∀ t > 0, ∀ phi : D.Point → ℝ,
    S.lpNorm q (S.divergenceSemigroup t phi) ≤
      C * (1 + t ^ (-(1 / 2 : ℝ))) *
        Real.exp (-(p.μ) * t) * S.vectorLpNorm q phi

lemma Lemma_2_3.divergence_bound
    {D : BoundedDomainData} {p : CM2Params} {S : SemigroupEstimateData D}
    (h : Lemma_2_3 D p S) :
    ∃ C > 0, ∀ q > 1, ∀ t > 0, ∀ phi : D.Point → ℝ,
      S.lpNorm q (S.divergenceSemigroup t phi) ≤
        C * (1 + t ^ (-(1 / 2 : ℝ))) *
          Real.exp (-(p.μ) * t) * S.vectorLpNorm q phi :=
  h

def Lemma_2_4 (D : BoundedDomainData) (p : CM2Params)
    (S : SemigroupEstimateData D) : Prop :=
  ∀ sigma q, 0 < sigma → 1 < q →
    ∃ C > 0, ∀ t > 0, ∀ phi : D.Point → ℝ,
      S.fractionalNorm sigma q (S.divergenceSemigroup t phi) ≤
        C * t ^ (-sigma) * (1 + t ^ (-(1 / 2 : ℝ))) *
          Real.exp (-(p.μ / 2) * t) * S.vectorLpNorm q phi

lemma Lemma_2_4.fractional_divergence_bound
    {D : BoundedDomainData} {p : CM2Params} {S : SemigroupEstimateData D}
    (h : Lemma_2_4 D p S)
    {sigma q : ℝ} (hsigma : 0 < sigma) (hq : 1 < q) :
    ∃ C > 0, ∀ t > 0, ∀ phi : D.Point → ℝ,
      S.fractionalNorm sigma q (S.divergenceSemigroup t phi) ≤
        C * t ^ (-sigma) * (1 + t ^ (-(1 / 2 : ℝ))) *
          Real.exp (-(p.μ / 2) * t) * S.vectorLpNorm q phi :=
  h sigma q hsigma hq

def Lemma_2_5 : Prop :=
  ∀ beta v : ℝ, 0 < beta → 0 < v →
    beta * v / (1 + v) ^ (1 + beta) ≤ Psi_beta beta

lemma Psi_beta_pos {beta : ℝ} (hbeta : 0 < beta) :
    0 < Psi_beta beta := by
  unfold Psi_beta
  positivity

lemma Psi_beta_nonneg {beta : ℝ} (hbeta : 0 ≤ beta) :
    0 ≤ Psi_beta beta := by
  unfold Psi_beta
  positivity

lemma Psi_beta_zero :
    Psi_beta 0 = 0 := by
  norm_num [Psi_beta]

lemma beta_div_one_add_beta_hasDerivAt {beta : ℝ} (hbeta : 0 < beta) :
    HasDerivAt (fun b : ℝ => b / (1 + b)) (1 / (1 + beta) ^ 2) beta := by
  have hden : 1 + beta ≠ 0 := by linarith
  have hden_deriv : HasDerivAt (fun b : ℝ => 1 + b) 1 beta := by
    simpa using ((hasDerivAt_const beta (1 : ℝ)).add (hasDerivAt_id beta))
  have hraw :
      HasDerivAt (fun b : ℝ => b / (1 + b))
        ((1 * (1 + beta) - beta * 1) / (1 + beta) ^ 2) beta := by
    simpa using (hasDerivAt_id beta).div hden_deriv hden
  convert hraw using 1
  field_simp [hden]
  ring_nf

lemma Psi_beta_hasDerivAt_raw {beta : ℝ} (hbeta : 0 < beta) :
    HasDerivAt Psi_beta
      ((1 / (1 + beta) ^ 2) * (1 + beta) *
          (beta / (1 + beta)) ^ ((1 + beta) - 1) +
        1 * (beta / (1 + beta)) ^ (1 + beta) *
          Real.log (beta / (1 + beta)))
      beta := by
  have hbase : 0 < beta / (1 + beta) := by positivity
  have hexp_deriv : HasDerivAt (fun b : ℝ => 1 + b) 1 beta := by
    simpa using ((hasDerivAt_const beta (1 : ℝ)).add (hasDerivAt_id beta))
  unfold Psi_beta
  exact (beta_div_one_add_beta_hasDerivAt hbeta).rpow
    hexp_deriv hbase

lemma Psi_beta_deriv_raw {beta : ℝ} (hbeta : 0 < beta) :
    deriv Psi_beta beta =
      (1 / (1 + beta) ^ 2) * (1 + beta) *
          (beta / (1 + beta)) ^ ((1 + beta) - 1) +
        1 * (beta / (1 + beta)) ^ (1 + beta) *
          Real.log (beta / (1 + beta)) :=
  (Psi_beta_hasDerivAt_raw hbeta).deriv

lemma Psi_beta_deriv_eq {beta : ℝ} (hbeta : 0 < beta) :
    deriv Psi_beta beta =
      Psi_beta beta * (1 / beta + Real.log (beta / (1 + beta))) := by
  have hden_pos : 0 < 1 + beta := by linarith
  have hq_pos : 0 < beta / (1 + beta) := div_pos hbeta hden_pos
  have hpow :
      (beta / (1 + beta)) ^ ((1 + beta) - 1) =
        (beta / (1 + beta)) ^ (1 + beta) / (beta / (1 + beta)) := by
    simpa using Real.rpow_sub hq_pos (1 + beta) 1
  rw [Psi_beta_deriv_raw hbeta]
  unfold Psi_beta
  rw [hpow]
  field_simp [ne_of_gt hbeta, ne_of_gt hden_pos, ne_of_gt hq_pos]

lemma Psi_beta_log_factor_pos {beta : ℝ} (hbeta : 0 < beta) :
    0 < 1 / beta + Real.log (beta / (1 + beta)) := by
  have hx_pos : 0 < 1 + 1 / beta := by positivity
  have hx_ne : 1 + 1 / beta ≠ 1 := by
    intro h
    have hinv_pos : 0 < 1 / beta := by positivity
    linarith
  have hlog_lt := Real.log_lt_sub_one_of_pos hx_pos hx_ne
  have hquot : beta / (1 + beta) = (1 + 1 / beta)⁻¹ := by
    field_simp [ne_of_gt hbeta, ne_of_gt (by linarith : 0 < 1 + beta)]
    ring
  rw [hquot, Real.log_inv]
  linarith

lemma Psi_beta_deriv_pos {beta : ℝ} (hbeta : 0 < beta) :
    0 < deriv Psi_beta beta := by
  rw [Psi_beta_deriv_eq hbeta]
  exact mul_pos (Psi_beta_pos hbeta) (Psi_beta_log_factor_pos hbeta)

lemma Psi_beta_strictMonoOn_Ioi :
    StrictMonoOn Psi_beta (Set.Ioi (0 : ℝ)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi (0 : ℝ)) ?_ ?_
  · intro beta hbeta
    exact (Psi_beta_hasDerivAt_raw hbeta).continuousAt.continuousWithinAt
  · intro beta hbeta
    exact Psi_beta_deriv_pos (by simpa using hbeta)

lemma Psi_beta_monotoneOn_Ici :
    MonotoneOn Psi_beta (Set.Ici (0 : ℝ)) := by
  intro beta hbeta gamma hgamma hle
  by_cases hbeta_zero : beta = 0
  · subst beta
    rw [Psi_beta_zero]
    exact Psi_beta_nonneg hgamma
  · have hbeta_pos : 0 < beta := lt_of_le_of_ne hbeta (Ne.symm hbeta_zero)
    by_cases h_eq : beta = gamma
    · subst gamma
      rfl
    · have hlt : beta < gamma := lt_of_le_of_ne hle h_eq
      have hgamma_pos : 0 < gamma := lt_trans hbeta_pos hlt
      exact le_of_lt (Psi_beta_strictMonoOn_Ioi hbeta_pos hgamma_pos hlt)

lemma Psi_beta_eq_zero_iff_of_nonneg {beta : ℝ} (hbeta : 0 ≤ beta) :
    Psi_beta beta = 0 ↔ beta = 0 := by
  constructor
  · intro h
    by_contra hne
    have hpos : 0 < beta := lt_of_le_of_ne hbeta (Ne.symm hne)
    have := Psi_beta_pos hpos
    linarith
  · intro h
    subst beta
    exact Psi_beta_zero

lemma Psi_beta_pos_iff_of_nonneg {beta : ℝ} (hbeta : 0 ≤ beta) :
    0 < Psi_beta beta ↔ 0 < beta := by
  constructor
  · intro h
    exact lt_of_le_of_ne hbeta
      (fun hzero => by
        subst beta
        rw [Psi_beta_zero] at h
        exact (lt_irrefl (0 : ℝ)) h)
  · exact Psi_beta_pos

lemma Psi_beta_lt_one {beta : ℝ} (hbeta : 0 < beta) :
    Psi_beta beta < 1 := by
  unfold Psi_beta
  have hbase_nonneg : 0 ≤ beta / (1 + beta) := by positivity
  have hbase_lt : beta / (1 + beta) < 1 := by
    rw [div_lt_one (by positivity : 0 < 1 + beta)]
    linarith
  exact Real.rpow_lt_one hbase_nonneg hbase_lt (by linarith : 0 < 1 + beta)

lemma Psi_beta_lt_self {beta : ℝ} (hbeta : 0 < beta) :
    Psi_beta beta < beta := by
  unfold Psi_beta
  have hden_pos : 0 < 1 + beta := by linarith
  have hbase_pos : 0 < beta / (1 + beta) := div_pos hbeta hden_pos
  have hbase_lt_one : beta / (1 + beta) < 1 := by
    rw [div_lt_one hden_pos]
    linarith
  calc
    (beta / (1 + beta)) ^ (1 + beta) < beta / (1 + beta) :=
      Real.rpow_lt_self_of_lt_one hbase_pos hbase_lt_one (by linarith)
    _ < beta := by
      rw [div_lt_iff₀ hden_pos]
      nlinarith

lemma Psi_beta_le_self {beta : ℝ} (hbeta : 0 ≤ beta) :
    Psi_beta beta ≤ beta := by
  by_cases hzero : beta = 0
  · subst beta
    rw [Psi_beta_zero]
  · exact le_of_lt (Psi_beta_lt_self (lt_of_le_of_ne hbeta (Ne.symm hzero)))

lemma Psi_beta_eq_at_inv {beta : ℝ} (hbeta : 0 < beta) :
    beta * (1 / beta) / (1 + 1 / beta) ^ (1 + beta) = Psi_beta beta := by
  have hbeta_ne : beta ≠ 0 := ne_of_gt hbeta
  have hden_pos : 0 < 1 + beta := by linarith
  have hbase :
      1 + 1 / beta = (1 + beta) / beta := by
    field_simp [hbeta_ne]
    ring
  have hquot :
      (1 + beta) / beta = (beta / (1 + beta))⁻¹ := by
    field_simp [hbeta_ne, ne_of_gt hden_pos]
  have hfrac_nonneg : 0 ≤ beta / (1 + beta) :=
    div_nonneg hbeta.le hden_pos.le
  unfold Psi_beta
  rw [show beta * (1 / beta) = 1 by field_simp [hbeta_ne]]
  rw [hbase, hquot, Real.inv_rpow hfrac_nonneg]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos (div_pos hbeta hden_pos) (1 + beta))]

lemma Psi_beta_le_one {beta : ℝ} (hbeta : 0 ≤ beta) :
    Psi_beta beta ≤ 1 := by
  by_cases hzero : beta = 0
  · subst beta
    norm_num [Psi_beta]
  · exact le_of_lt (Psi_beta_lt_one (lt_of_le_of_ne hbeta (Ne.symm hzero)))

lemma Psi_beta_mem_Icc_zero_one {beta : ℝ} (hbeta : 0 ≤ beta) :
    Psi_beta beta ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Psi_beta_nonneg hbeta, Psi_beta_le_one hbeta⟩

lemma one_add_inv_tendsto_one_atTop :
    Tendsto (fun beta : ℝ => 1 + 1 / beta) atTop (𝓝 1) := by
  have hinv : Tendsto (fun beta : ℝ => 1 / beta) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero
  simpa using tendsto_const_nhds.add hinv

lemma one_add_inv_rpow_one_add_tendsto_exp :
    Tendsto (fun beta : ℝ => (1 + 1 / beta) ^ (1 + beta)) atTop
      (𝓝 (Real.exp 1)) := by
  have hp : Tendsto (fun beta : ℝ => (1 + 1 / beta) ^ beta) atTop
      (𝓝 (Real.exp 1)) := by
    simpa [one_div] using Real.tendsto_one_add_div_rpow_exp 1
  have hbase : Tendsto (fun beta : ℝ => 1 + 1 / beta) atTop (𝓝 1) :=
    one_add_inv_tendsto_one_atTop
  have heq :
      (fun beta : ℝ => (1 + 1 / beta) ^ beta * (1 + 1 / beta)) =ᶠ[atTop]
        fun beta : ℝ => (1 + 1 / beta) ^ (1 + beta) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with beta hbeta
    have hbase_pos : 0 < 1 + 1 / beta := by positivity
    rw [show 1 + beta = beta + 1 by ring]
    rw [Real.rpow_add hbase_pos]
    rw [Real.rpow_one]
  simpa using (hp.mul hbase).congr' heq

lemma Psi_beta_tendsto_atTop :
    Tendsto Psi_beta atTop (𝓝 (Real.exp (-1))) := by
  have hlim :
      Tendsto (fun beta : ℝ => ((1 + 1 / beta) ^ (1 + beta))⁻¹)
        atTop (𝓝 ((Real.exp 1)⁻¹)) :=
    one_add_inv_rpow_one_add_tendsto_exp.inv₀ (by positivity)
  have heq :
      (fun beta : ℝ => Psi_beta beta) =ᶠ[atTop]
        fun beta : ℝ => ((1 + 1 / beta) ^ (1 + beta))⁻¹ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with beta hbeta
    have hbeta_ne : beta ≠ 0 := ne_of_gt hbeta
    have hbase_nonneg : 0 ≤ 1 + 1 / beta := by positivity
    have hquot : beta / (1 + beta) = (1 + 1 / beta)⁻¹ := by
      field_simp [hbeta_ne, ne_of_gt (by linarith : 0 < 1 + beta)]
      ring
    unfold Psi_beta
    rw [hquot, Real.inv_rpow hbase_nonneg]
  have hinv_exp : (Real.exp 1)⁻¹ = Real.exp (-1) := by
    rw [← Real.exp_neg]
  simpa [hinv_exp] using hlim.congr' heq.symm

lemma Psi_beta_le_exp_neg_one {beta : ℝ} (hbeta : 0 < beta) :
    Psi_beta beta ≤ Real.exp (-1) := by
  have hden_pos : 0 < 1 + beta := by linarith
  have hq_pos : 0 < beta / (1 + beta) := div_pos hbeta hden_pos
  have hx_pos : 0 < 1 + 1 / beta := by positivity
  have hquot : beta / (1 + beta) = (1 + 1 / beta)⁻¹ := by
    field_simp [ne_of_gt hbeta, ne_of_gt hden_pos]
    ring
  have hxinv :
      (1 + 1 / beta)⁻¹ = beta / (1 + beta) := hquot.symm
  have hlog_lower := Real.one_sub_inv_le_log_of_pos hx_pos
  rw [hxinv] at hlog_lower
  have hunit :
      1 - beta / (1 + beta) = 1 / (1 + beta) := by
    field_simp [ne_of_gt hden_pos]
    ring
  rw [hunit] at hlog_lower
  have hmul :
      1 ≤ (1 + beta) * Real.log (1 + 1 / beta) := by
    have hmul' := mul_le_mul_of_nonneg_left hlog_lower hden_pos.le
    have hone : (1 + beta) * (1 / (1 + beta)) = 1 := by
      field_simp [ne_of_gt hden_pos]
    nlinarith
  have hlog :
      Real.log (Psi_beta beta) ≤ Real.log (Real.exp (-1)) := by
    unfold Psi_beta
    rw [Real.log_rpow hq_pos, hquot, Real.log_inv]
    rw [Real.log_exp]
    nlinarith
  exact (Real.log_le_log_iff (Psi_beta_pos hbeta) (Real.exp_pos _)).mp hlog

lemma Psi_beta_lt_exp_neg_one {beta : ℝ} (hbeta : 0 < beta) :
    Psi_beta beta < Real.exp (-1) := by
  have hden_pos : 0 < 1 + beta := by linarith
  have hq_pos : 0 < beta / (1 + beta) := div_pos hbeta hden_pos
  have hq_ne_one : beta / (1 + beta) ≠ 1 := by
    have hq_lt_one : beta / (1 + beta) < 1 := by
      rw [div_lt_one hden_pos]
      linarith
    exact ne_of_lt hq_lt_one
  have hlog_q_lt : Real.log (beta / (1 + beta)) < beta / (1 + beta) - 1 :=
    Real.log_lt_sub_one_of_pos hq_pos hq_ne_one
  have hunit :
      (1 + beta) * (beta / (1 + beta) - 1) = -1 := by
    field_simp [ne_of_gt hden_pos]
    ring
  have hlog :
      Real.log (Psi_beta beta) < Real.log (Real.exp (-1)) := by
    unfold Psi_beta
    rw [Real.log_rpow hq_pos, Real.log_exp]
    calc
      (1 + beta) * Real.log (beta / (1 + beta))
          < (1 + beta) * (beta / (1 + beta) - 1) :=
            mul_lt_mul_of_pos_left hlog_q_lt hden_pos
      _ = -1 := hunit
  exact (Real.log_lt_log_iff (Psi_beta_pos hbeta) (Real.exp_pos _)).mp hlog

lemma Psi_beta_le_exp_neg_one_of_nonneg {beta : ℝ} (hbeta : 0 ≤ beta) :
    Psi_beta beta ≤ Real.exp (-1) := by
  by_cases hzero : beta = 0
  · subst beta
    rw [Psi_beta_zero]
    exact (Real.exp_pos _).le
  · exact le_of_lt (Psi_beta_lt_exp_neg_one (lt_of_le_of_ne hbeta (Ne.symm hzero)))

lemma Psi_beta_lt_exp_neg_one_of_nonneg {beta : ℝ} (hbeta : 0 ≤ beta) :
    Psi_beta beta < Real.exp (-1) := by
  by_cases hzero : beta = 0
  · subst beta
    rw [Psi_beta_zero]
    exact Real.exp_pos _
  · exact Psi_beta_lt_exp_neg_one (lt_of_le_of_ne hbeta (Ne.symm hzero))

lemma Theta_beta_pos {beta : ℝ} (hbeta : 0 < beta) :
    0 < Theta_beta beta := by
  unfold Theta_beta
  positivity

lemma Theta_beta_zero :
    Theta_beta 0 = 1 := by
  norm_num [Theta_beta]

lemma Theta_beta_pos_of_nonneg {beta : ℝ} (hbeta : 0 ≤ beta) :
    0 < Theta_beta beta := by
  by_cases hzero : beta = 0
  · subst beta
    rw [Theta_beta_zero]
    norm_num
  · exact Theta_beta_pos (lt_of_le_of_ne hbeta (Ne.symm hzero))

lemma Theta_beta_nonneg {beta : ℝ} (hbeta : 0 ≤ beta) :
    0 ≤ Theta_beta beta := by
  exact (Theta_beta_pos_of_nonneg hbeta).le

lemma Psi_beta_eq_beta_mul_Theta_beta {beta : ℝ} (hbeta : 0 < beta) :
    Psi_beta beta = beta * Theta_beta beta := by
  have hden_pos : 0 < 1 + beta := by linarith
  unfold Psi_beta Theta_beta
  rw [Real.div_rpow hbeta.le hden_pos.le]
  rw [show 1 + beta = beta + 1 by ring]
  rw [Real.rpow_add_one hbeta.ne' beta]
  have hden_nonneg : 0 ≤ beta + 1 := by linarith
  rw [Real.rpow_neg hden_nonneg]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos (by linarith : 0 < beta + 1) (beta + 1))]

lemma Theta_beta_lt_one {beta : ℝ} (hbeta : 0 < beta) :
    Theta_beta beta < 1 := by
  have h := Psi_beta_lt_self hbeta
  rw [Psi_beta_eq_beta_mul_Theta_beta hbeta] at h
  rw [← div_self (ne_of_gt hbeta)]
  rw [lt_div_iff₀ hbeta]
  rwa [mul_comm]

lemma Theta_beta_le_one {beta : ℝ} (hbeta : 0 ≤ beta) :
    Theta_beta beta ≤ 1 := by
  by_cases hzero : beta = 0
  · subst beta
    rw [Theta_beta_zero]
  · exact le_of_lt (Theta_beta_lt_one (lt_of_le_of_ne hbeta (Ne.symm hzero)))

lemma Theta_beta_eq_Psi_beta_div {beta : ℝ} (hbeta : 0 < beta) :
    Theta_beta beta = Psi_beta beta / beta := by
  rw [Psi_beta_eq_beta_mul_Theta_beta hbeta]
  field_simp [ne_of_gt hbeta]

lemma beta_mul_Theta_beta_lt_one {beta : ℝ} (hbeta : 0 < beta) :
    beta * Theta_beta beta < 1 := by
  rw [← Psi_beta_eq_beta_mul_Theta_beta hbeta]
  exact Psi_beta_lt_one hbeta

lemma beta_mul_Theta_beta_pos {beta : ℝ} (hbeta : 0 < beta) :
    0 < beta * Theta_beta beta := by
  rw [← Psi_beta_eq_beta_mul_Theta_beta hbeta]
  exact Psi_beta_pos hbeta

lemma beta_mul_Theta_beta_le_one {beta : ℝ} (hbeta : 0 < beta) :
    beta * Theta_beta beta ≤ 1 :=
  le_of_lt (beta_mul_Theta_beta_lt_one hbeta)

theorem Lemma_2_5_proved : Lemma_2_5 := by
  intro beta v hbeta hv
  have hden_pos : 0 < 1 + beta := by linarith
  have hvden_pos : 0 < 1 + v := by linarith
  have hweights : 1 / (1 + beta) + beta / (1 + beta) = 1 := by
    field_simp [ne_of_gt hden_pos]
  have hgm :=
    Real.geom_mean_le_arith_mean2_weighted
      (show 0 ≤ 1 / (1 + beta) by positivity)
      (show 0 ≤ beta / (1 + beta) by positivity)
      (mul_nonneg hbeta.le hv.le)
      (show 0 ≤ (1 : ℝ) by norm_num)
      hweights
      (p₁ := beta * v) (p₂ := 1)
  have hgm' :
      (beta * v) ^ (1 / (1 + beta)) ≤ beta * (1 + v) / (1 + beta) := by
    calc
      (beta * v) ^ (1 / (1 + beta))
          ≤ beta / (beta + 1) + (beta + 1)⁻¹ * (beta * v) := by
            simpa [Real.one_rpow, one_div, add_comm] using hgm
      _ = beta * (1 + v) / (1 + beta) := by
            field_simp [ne_of_gt hden_pos]
            ring
  have hpow :=
    Real.rpow_le_rpow
      (Real.rpow_nonneg (mul_nonneg hbeta.le hv.le) _)
      hgm' (show 0 ≤ 1 + beta by linarith)
  have hleft_eq :
      ((beta * v) ^ (1 / (1 + beta))) ^ (1 + beta) = beta * v := by
    rw [← Real.rpow_mul (mul_nonneg hbeta.le hv.le)]
    have hprod : 1 / (1 + beta) * (1 + beta) = 1 := by
      field_simp [ne_of_gt hden_pos]
    rw [hprod, Real.rpow_one]
  have hrhs_eq :
      (beta * (1 + v) / (1 + beta)) ^ (1 + beta) =
        Psi_beta beta * (1 + v) ^ (1 + beta) := by
    have hbase : beta * (1 + v) / (1 + beta) = (beta / (1 + beta)) * (1 + v) := by
      ring
    rw [hbase]
    rw [Real.mul_rpow (div_nonneg hbeta.le hden_pos.le) hvden_pos.le]
    rfl
  have hmain : beta * v ≤ Psi_beta beta * (1 + v) ^ (1 + beta) := by
    rw [hleft_eq, hrhs_eq] at hpow
    exact hpow
  have hden_rpow_pos : 0 < (1 + v) ^ (1 + beta) :=
    Real.rpow_pos_of_pos hvden_pos _
  exact (div_le_iff₀ hden_rpow_pos).mpr hmain

def AbstractLpBootstrapHypothesis
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (N T rho p0 : ℝ) : Prop :=
  0 < rho ∧
    0 < T ∧
    max 1 (rho * N / 2) < p0 ∧
    LpPowerBoundedBefore D p0 T u

def Lemma_2_6 (D : BoundedDomainData) : Prop :=
  ∀ N > 0, ∀ u : ℝ → D.Point → ℝ, ∀ T rho p0,
    AbstractLpBootstrapHypothesis D u N T rho p0 →
      LpBootstrapEnergyInequality D u T rho p0 →
        ∀ pExp > 1, LpPowerBoundedBefore D pExp T u

lemma Lemma_2_6.lp_bound
    {D : BoundedDomainData}
    (h : Lemma_2_6 D)
    {N : ℝ} (hN : 0 < N) {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (hhyp : AbstractLpBootstrapHypothesis D u N T rho p0)
    (henergy : LpBootstrapEnergyInequality D u T rho p0)
    {pExp : ℝ} (hpExp : 1 < pExp) :
    LpPowerBoundedBefore D pExp T u :=
  h N hN u T rho p0 hhyp henergy pExp hpExp

lemma AbstractLpBootstrapHypothesis.rho_pos
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {N T rho p0 : ℝ}
    (h : AbstractLpBootstrapHypothesis D u N T rho p0) :
    0 < rho :=
  h.1

lemma AbstractLpBootstrapHypothesis.T_pos
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {N T rho p0 : ℝ}
    (h : AbstractLpBootstrapHypothesis D u N T rho p0) :
    0 < T :=
  h.2.1

lemma AbstractLpBootstrapHypothesis.p0_gt_threshold
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {N T rho p0 : ℝ}
    (h : AbstractLpBootstrapHypothesis D u N T rho p0) :
    max 1 (rho * N / 2) < p0 :=
  h.2.2.1

lemma AbstractLpBootstrapHypothesis.initial_lp_bound
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {N T rho p0 : ℝ}
    (h : AbstractLpBootstrapHypothesis D u N T rho p0) :
    LpPowerBoundedBefore D p0 T u :=
  h.2.2.2

def Corollary_2_1 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ T > 0, ∀ u v : ℝ → D.Point → ℝ,
    IsPaper2ClassicalSolution D p T u v →
      (∃ rho > 0, CrossDiffusionBootstrapEstimate D p T rho u v ∧
        ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
          LpPowerBoundedBefore D p0 T u) →
      ∀ pExp > 1, LpPowerBoundedBefore D pExp T u

lemma Corollary_2_1.lp_bound
    {D : BoundedDomainData} {p : CM2Params}
    (h : Corollary_2_1 D p)
    {T : ℝ} (hT : 0 < T) {u v : ℝ → D.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution D p T u v)
    (hboot :
      ∃ rho > 0, CrossDiffusionBootstrapEstimate D p T rho u v ∧
        ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
          LpPowerBoundedBefore D p0 T u)
    {pExp : ℝ} (hpExp : 1 < pExp) :
    LpPowerBoundedBefore D pExp T u :=
  h T hT u v hsol hboot pExp hpExp

def Proposition_2_1
    (D : BoundedDomainData) (p : CM2Params)
    (S : SemigroupEstimateData D) : Prop :=
  ∀ T > 0, ∀ u v : ℝ → D.Point → ℝ,
    IsPaper2ClassicalSolution D p T u v →
      ∀ pExp, 1 ≤ pExp →
        ∀ t, 0 < t → t < T →
          S.lpNorm pExp (v t) ≤
            (p.ν / p.μ) * S.lpNorm pExp (fun x => (u t x) ^ p.γ)

lemma Proposition_2_1.signal_lp_bound
    {D : BoundedDomainData} {p : CM2Params} {S : SemigroupEstimateData D}
    (h : Proposition_2_1 D p S)
    {T : ℝ} (hT : 0 < T) {u v : ℝ → D.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution D p T u v)
    {pExp : ℝ} (hpExp : 1 ≤ pExp)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    S.lpNorm pExp (v t) ≤
      (p.ν / p.μ) * S.lpNorm pExp (fun x => (u t x) ^ p.γ) :=
  h T hT u v hsol pExp hpExp t ht0 htT

def Proposition_2_2 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ T > 0, ∀ u v : ℝ → D.Point → ℝ,
    IsPaper2ClassicalSolution D p T u v →
      ∀ pExp > 1, ∃ Mstar > 0,
        WeightedGradientEstimate D pExp p.β p.γ Mstar T u v

lemma Proposition_2_2.weighted_gradient
    {D : BoundedDomainData} {p : CM2Params}
    (h : Proposition_2_2 D p)
    {T : ℝ} (hT : 0 < T) {u v : ℝ → D.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution D p T u v)
    {pExp : ℝ} (hpExp : 1 < pExp) :
    ∃ Mstar > 0, WeightedGradientEstimate D pExp p.β p.γ Mstar T u v :=
  h T hT u v hsol pExp hpExp

def Proposition_2_3 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ T > 0, ∀ u v : ℝ → D.Point → ℝ,
    IsPaper2ClassicalSolution D p T u v →
      ∀ pExp, max 1 p.β < pExp →
        ∀ eps > 0, ∃ Ceps > 0,
          WeightedSignalEstimate D pExp p.β p.γ eps Ceps T u v

lemma Proposition_2_3.weighted_signal
    {D : BoundedDomainData} {p : CM2Params}
    (h : Proposition_2_3 D p)
    {T : ℝ} (hT : 0 < T) {u v : ℝ → D.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution D p T u v)
    {pExp eps : ℝ} (hpExp : max 1 p.β < pExp) (heps : 0 < eps) :
    ∃ Ceps > 0, WeightedSignalEstimate D pExp p.β p.γ eps Ceps T u v :=
  h T hT u v hsol pExp hpExp eps heps

def Proposition_2_4 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
    ∀ T > 0, ∀ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p T u v →
      InitialTrace D u₀ u →
        (p.a = 0 → p.b = 0 → MassConservedBefore D T u₀ u) ∧
          (0 < p.a → 0 < p.b → LogisticMassUpperBoundBefore D p T u₀ u)

lemma Proposition_2_4.mass_conserved
    {D : BoundedDomainData} {p : CM2Params}
    (h : Proposition_2_4 D p)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀)
    {T : ℝ} (hT : 0 < T) {u v : ℝ → D.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution D p T u v)
    (htrace : InitialTrace D u₀ u)
    (ha : p.a = 0) (hb : p.b = 0) :
    MassConservedBefore D T u₀ u :=
  (h u₀ hu₀ T hT u v hsol htrace).1 ha hb

lemma Proposition_2_4.logistic_mass_upper
    {D : BoundedDomainData} {p : CM2Params}
    (h : Proposition_2_4 D p)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀)
    {T : ℝ} (hT : 0 < T) {u v : ℝ → D.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution D p T u v)
    (htrace : InitialTrace D u₀ u)
    (ha : 0 < p.a) (hb : 0 < p.b) :
    LogisticMassUpperBoundBefore D p T u₀ u :=
  (h u₀ hu₀ T hT u v hsol htrace).2 ha hb

def Proposition_2_5 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
    ∀ Tmax > 0, ∀ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p Tmax u v →
      InitialTrace D u₀ u →
        ∀ pExp,
          max (p.N : ℝ) (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
            LpPowerBoundedBefore D pExp Tmax u →
              IsPaper2BoundedBefore D Tmax u

lemma Proposition_2_5.bounded_before
    {D : BoundedDomainData} {p : CM2Params}
    (h : Proposition_2_5 D p)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀)
    {Tmax : ℝ} (hTmax : 0 < Tmax) {u v : ℝ → D.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution D p Tmax u v)
    (htrace : InitialTrace D u₀ u)
    {pExp : ℝ}
    (hpExp :
      max (p.N : ℝ) (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp)
    (hLp : LpPowerBoundedBefore D pExp Tmax u) :
    IsPaper2BoundedBefore D Tmax u :=
  h u₀ hu₀ Tmax hTmax u v hsol htrace pExp hpExp hLp

def Lemma_2_7 (D : BoundedDomainData) : Prop :=
  ∀ u : ℝ → D.Point → ℝ, ∀ T pExp C1 C2 C3 C4 eps alpha,
    0 < T → 1 < pExp →
      0 ≤ C1 → 0 ≤ C2 → 0 ≤ C3 → 0 < C4 →
        0 < eps → eps ≤ alpha →
          (∀ t, 0 < t → t < T →
            deriv (fun τ => D.integral (fun x => (u τ x) ^ pExp)) t +
                C3 * D.integral (fun x => (u t x) ^ (pExp + alpha - eps)) ≤
              C1 + C2 * D.integral (fun x => (u t x) ^ pExp) -
                C4 * D.integral (fun x => (u t x) ^ (pExp + alpha))) →
            LpPowerBoundedBefore D pExp T u

lemma Lemma_2_7.lp_bound
    {D : BoundedDomainData}
    (h : Lemma_2_7 D)
    {u : ℝ → D.Point → ℝ} {T pExp C1 C2 C3 C4 eps alpha : ℝ}
    (hT : 0 < T) (hpExp : 1 < pExp)
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3) (hC4 : 0 < C4)
    (heps : 0 < eps) (heps_alpha : eps ≤ alpha)
    (hdiff :
      ∀ t, 0 < t → t < T →
        deriv (fun τ => D.integral (fun x => (u τ x) ^ pExp)) t +
            C3 * D.integral (fun x => (u t x) ^ (pExp + alpha - eps)) ≤
          C1 + C2 * D.integral (fun x => (u t x) ^ pExp) -
            C4 * D.integral (fun x => (u t x) ^ (pExp + alpha))) :
    LpPowerBoundedBefore D pExp T u :=
  h u T pExp C1 C2 C3 C4 eps alpha
    hT hpExp hC1 hC2 hC3 hC4 heps heps_alpha hdiff

def Lemma_3_1 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  p.χ₀ ≤ 0 →
    (0 < p.a → 0 < p.b →
      ∀ T > 0, ∀ u v : ℝ → D.Point → ℝ,
        IsPaper2ClassicalSolution D p T u v →
          ∀ t₀, 0 < t₀ → t₀ < T →
            (p.a / p.b) ^ (1 / p.α) < D.supNorm (u t₀) →
              SupNormNonincreasingOn D u (Set.Ioc (0 : ℝ) t₀)) ∧
    (p.a = 0 → p.b = 0 →
      ∀ T > 0, ∀ u v : ℝ → D.Point → ℝ,
        IsPaper2ClassicalSolution D p T u v →
          SupNormNonincreasingOn D u (Set.Ioo (0 : ℝ) T))

lemma Lemma_3_1.nonminimal_sup_norm_monotone
    {D : BoundedDomainData} {p : CM2Params}
    (h : Lemma_3_1 D p)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    {T : ℝ} (hT : 0 < T) {u v : ℝ → D.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution D p T u v)
    {t₀ : ℝ} (ht₀_pos : 0 < t₀) (ht₀_T : t₀ < T)
    (hsup : (p.a / p.b) ^ (1 / p.α) < D.supNorm (u t₀)) :
    SupNormNonincreasingOn D u (Set.Ioc (0 : ℝ) t₀) :=
  (h hχ).1 ha hb T hT u v hsol t₀ ht₀_pos ht₀_T hsup

lemma Lemma_3_1.minimal_sup_norm_monotone
    {D : BoundedDomainData} {p : CM2Params}
    (h : Lemma_3_1 D p)
    (hχ : p.χ₀ ≤ 0) (ha : p.a = 0) (hb : p.b = 0)
    {T : ℝ} (hT : 0 < T) {u v : ℝ → D.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution D p T u v) :
    SupNormNonincreasingOn D u (Set.Ioo (0 : ℝ) T) :=
  (h hχ).2 ha hb T hT u v hsol

def Lemma_4_1 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
  ∀ T > 0, ∀ u v : ℝ → D.Point → ℝ,
    IsPaper2ClassicalSolution D p T u v →
      InitialTrace D u₀ u →
        ∀ eps > 0, ∀ pExp > 1, ∃ Ceps > 0,
          LpMassGradientInterpolationEstimate D pExp eps Ceps T u

lemma Lemma_4_1.interpolation_estimate
    {D : BoundedDomainData} {p : CM2Params}
    (h : Lemma_4_1 D p)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀)
    {T : ℝ} (hT : 0 < T) {u v : ℝ → D.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution D p T u v)
    (htrace : InitialTrace D u₀ u)
    {eps pExp : ℝ} (heps : 0 < eps) (hpExp : 1 < pExp) :
    ∃ Ceps > 0, LpMassGradientInterpolationEstimate D pExp eps Ceps T u :=
  h u₀ hu₀ T hT u v hsol htrace eps heps pExp hpExp

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

lemma StrongLogisticCondition.of_alpha_gt_m_add_gamma_sub_one
    {p : CM2Params} {C : Paper2Constants p}
    (hβ : 0 ≤ p.β) (hα : p.m + p.γ - 1 < p.α) :
    StrongLogisticCondition p C := by
  exact Or.inl ⟨hβ, hα⟩

lemma StrongLogisticCondition.of_alpha_gt_two_mul_m_add_gamma_sub_two
    {p : CM2Params} {C : Paper2Constants p}
    (hβ : (1 / 2 : ℝ) ≤ p.β)
    (hα : 2 * p.m + p.γ - 2 < p.α) :
    StrongLogisticCondition p C := by
  exact Or.inr (Or.inl ⟨hβ, hα⟩)

lemma StrongLogisticCondition.of_critical_m_add_gamma_sub_one
    {p : CM2Params} {C : Paper2Constants p}
    (hβ : 0 ≤ p.β)
    (hα : p.α = p.m + p.γ - 1)
    (hχ :
      positivePart ((p.N : ℝ) * p.α - 2) = 0 ∨
        p.χ₀ <
          ((positivePart ((p.N : ℝ) * p.α - 2) + 2 * p.m) * p.b) /
            (positivePart ((p.N : ℝ) * p.α - 2) *
              (p.ν + Psi_beta p.β * C.K))) :
    StrongLogisticCondition p C := by
  exact Or.inr (Or.inr (Or.inl ⟨hβ, hα, hχ⟩))

lemma StrongLogisticCondition.of_critical_two_mul_m_add_gamma_sub_two
    {p : CM2Params} {C : Paper2Constants p}
    (hβ : (1 / 2 : ℝ) ≤ p.β)
    (hα : p.α = 2 * p.m + p.γ - 2)
    (hχ :
      positivePart ((p.N : ℝ) * p.α - 2) = 0 ∨
        p.χ₀ <
          Real.sqrt
            (8 * p.b /
              (positivePart ((p.N : ℝ) * p.α - 2) *
                Theta_beta (2 * p.β - 1) * C.K))) :
    StrongLogisticCondition p C := by
  exact Or.inr (Or.inr (Or.inr ⟨hβ, hα, hχ⟩))

lemma StrongLogisticCondition.of_critical_m_add_gamma_sub_one_low_dimension
    {p : CM2Params} {C : Paper2Constants p}
    (hβ : 0 ≤ p.β)
    (hα : p.α = p.m + p.γ - 1)
    (hdim : (p.N : ℝ) * p.α ≤ 2) :
    StrongLogisticCondition p C := by
  exact
    StrongLogisticCondition.of_critical_m_add_gamma_sub_one hβ hα
      (Or.inl (positivePart_eq_zero_of_nonpos (by linarith)))

lemma StrongLogisticCondition.of_critical_two_mul_m_add_gamma_sub_two_low_dimension
    {p : CM2Params} {C : Paper2Constants p}
    (hβ : (1 / 2 : ℝ) ≤ p.β)
    (hα : p.α = 2 * p.m + p.γ - 2)
    (hdim : (p.N : ℝ) * p.α ≤ 2) :
    StrongLogisticCondition p C := by
  exact
    StrongLogisticCondition.of_critical_two_mul_m_add_gamma_sub_two hβ hα
      (Or.inl (positivePart_eq_zero_of_nonpos (by linarith)))

lemma StrongLogisticCondition.beta_nonneg
    {p : CM2Params} {C : Paper2Constants p}
    (h : StrongLogisticCondition p C) :
    0 ≤ p.β := by
  rcases h with h | h | h | h
  · exact h.1
  · linarith [h.1]
  · exact h.1
  · linarith [h.1]

lemma StrongLogisticCondition.alpha_ge_m_add_gamma_sub_one_of_m_ge_one
    {p : CM2Params} {C : Paper2Constants p}
    (hm : 1 ≤ p.m) (h : StrongLogisticCondition p C) :
    p.m + p.γ - 1 ≤ p.α := by
  rcases h with h | h | h | h
  · exact le_of_lt h.2
  · have hle : p.m + p.γ - 1 ≤ 2 * p.m + p.γ - 2 := by
      linarith
    exact le_trans hle (le_of_lt h.2)
  · linarith [h.2.1]
  · have hle : p.m + p.γ - 1 ≤ 2 * p.m + p.γ - 2 := by
      linarith
    linarith [hle, h.2.1]

lemma StrongLogisticCondition.alpha_ge_two_mul_m_add_gamma_sub_two_of_m_le_one
    {p : CM2Params} {C : Paper2Constants p}
    (hm : p.m ≤ 1) (h : StrongLogisticCondition p C) :
    2 * p.m + p.γ - 2 ≤ p.α := by
  rcases h with h | h | h | h
  · have hle : 2 * p.m + p.γ - 2 ≤ p.m + p.γ - 1 := by
      linarith
    exact le_trans hle (le_of_lt h.2)
  · exact le_of_lt h.2
  · have hle : 2 * p.m + p.γ - 2 ≤ p.m + p.γ - 1 := by
      linarith
    linarith [hle, h.2.1]
  · linarith [h.2.1]

/-- Paper2 Proposition 1.1: local existence and blow-up alternative. -/
def Proposition_1_1 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
    ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p Tmax u v ∧
      InitialTrace D u₀ u ∧
      FiniteHorizonAlternative D Tmax u ∧
      (1 ≤ p.m → MGeOneFiniteHorizonAlternative D Tmax u)

lemma Proposition_1_1.solution
    {D : BoundedDomainData} {p : CM2Params}
    (h : Proposition_1_1 D p)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p Tmax u v ∧
      InitialTrace D u₀ u ∧
      FiniteHorizonAlternative D Tmax u ∧
      (1 ≤ p.m → MGeOneFiniteHorizonAlternative D Tmax u) :=
  h u₀ hu₀

/-- Paper2 Theorem 1.1: boundedness/global existence for negative sensitivity. -/
def Theorem_1_1 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  p.χ₀ ≤ 0 →
    (0 < p.a → 0 < p.b →
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2ClassicalSolution D p Tmax u v ∧
          InitialTrace D u₀ u ∧
          (∀ t, 0 < t → t < Tmax →
            D.supNorm (u t) ≤ max (D.supNorm u₀) ((p.a / p.b) ^ (1 / p.α))) ∧
          (1 ≤ p.m → IsPaper2GlobalClassicalSolution D p u v)) ∧
    (p.a = 0 → p.b = 0 →
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2ClassicalSolution D p Tmax u v ∧
          InitialTrace D u₀ u ∧
          (∀ t, 0 < t → t < Tmax → D.supNorm (u t) ≤ D.supNorm u₀) ∧
          (1 ≤ p.m → IsPaper2GlobalClassicalSolution D p u v))

lemma Theorem_1_1.nonminimal_solution
    {D : BoundedDomainData} {p : CM2Params}
    (h : Theorem_1_1 D p)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p Tmax u v ∧
      InitialTrace D u₀ u ∧
      (∀ t, 0 < t → t < Tmax →
        D.supNorm (u t) ≤ max (D.supNorm u₀) ((p.a / p.b) ^ (1 / p.α))) ∧
      (1 ≤ p.m → IsPaper2GlobalClassicalSolution D p u v) :=
  (h hχ).1 ha hb u₀ hu₀

lemma Theorem_1_1.minimal_solution
    {D : BoundedDomainData} {p : CM2Params}
    (h : Theorem_1_1 D p)
    (hχ : p.χ₀ ≤ 0) (ha : p.a = 0) (hb : p.b = 0)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p Tmax u v ∧
      InitialTrace D u₀ u ∧
      (∀ t, 0 < t → t < Tmax → D.supNorm (u t) ≤ D.supNorm u₀) ∧
      (1 ≤ p.m → IsPaper2GlobalClassicalSolution D p u v) :=
  (h hχ).2 ha hb u₀ hu₀

/-- Paper2 Theorem 1.2: boundedness/global existence for weak nonlinear cross diffusion. -/
def Theorem_1_2 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  0 ≤ p.a → 0 ≤ p.b → 1 ≤ p.β →
    ((0 < p.m → p.m < 1 →
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2ClassicalSolution D p Tmax u v ∧
            InitialTrace D u₀ u ∧
            IsPaper2BoundedBefore D Tmax u) ∧
    (p.m = 1 → p.χ₀ < chiBeta p →
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2GlobalClassicalSolution D p u v ∧
            InitialTrace D u₀ u ∧
            IsPaper2Bounded D u))

lemma Theorem_1_2.sublinear_solution
    {D : BoundedDomainData} {p : CM2Params}
    (h : Theorem_1_2 D p)
    (ha : 0 ≤ p.a) (hb : 0 ≤ p.b) (hβ : 1 ≤ p.β)
    (hm_pos : 0 < p.m) (hm_lt : p.m < 1)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p Tmax u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2BoundedBefore D Tmax u :=
  (h ha hb hβ).1 hm_pos hm_lt u₀ hu₀

lemma Theorem_1_2.linear_solution
    {D : BoundedDomainData} {p : CM2Params}
    (h : Theorem_1_2 D p)
    (ha : 0 ≤ p.a) (hb : 0 ≤ p.b) (hβ : 1 ≤ p.β)
    (hm : p.m = 1) (hχ : p.χ₀ < chiBeta p)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2Bounded D u :=
  (h ha hb hβ).2 hm hχ u₀ hu₀

/-- Paper2 Theorem 1.3: boundedness/global existence under a strong logistic source. -/
def Theorem_1_3 (D : BoundedDomainData) (p : CM2Params) (C : Paper2Constants p) : Prop :=
  0 < p.a → 0 < p.b → 0 < p.m → StrongLogisticCondition p C →
    (∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
      ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
        IsPaper2ClassicalSolution D p Tmax u v ∧
          InitialTrace D u₀ u ∧
          IsPaper2BoundedBefore D Tmax u) ∧
    (1 ≤ p.m →
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2GlobalClassicalSolution D p u v ∧
            InitialTrace D u₀ u ∧
            IsPaper2Bounded D u)

lemma Theorem_1_3.finite_horizon_solution
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hm_pos : 0 < p.m)
    (hcond : StrongLogisticCondition p C)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p Tmax u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2BoundedBefore D Tmax u :=
  (h ha hb hm_pos hcond).1 u₀ hu₀

lemma Theorem_1_3.global_solution
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hm_pos : 0 < p.m)
    (hcond : StrongLogisticCondition p C) (hm : 1 ≤ p.m)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2Bounded D u :=
  (h ha hb hm_pos hcond).2 hm u₀ hu₀

end

end ShenWork.Paper2
