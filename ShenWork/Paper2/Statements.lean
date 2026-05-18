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

def IsPaper2BoundedBefore
    (D : BoundedDomainData) (Tmax : ℝ) (u : ℝ → D.Point → ℝ) : Prop :=
  ∃ M, ∀ t, 0 < t → t < Tmax → D.supNorm (u t) ≤ M

def LpPowerBoundedBefore
    (D : BoundedDomainData) (pExp Tmax : ℝ) (u : ℝ → D.Point → ℝ) : Prop :=
  ∃ C, ∀ t, 0 < t → t < Tmax →
    D.integral (fun x => (u t x) ^ pExp) ≤ C

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

def Lemma_2_2 (D : BoundedDomainData) (S : SemigroupEstimateData D) : Prop :=
  (∀ sigma q k r, 0 ≤ sigma → 1 ≤ q → q ≤ r →
    k - (D.volume / r) < 2 * sigma - D.volume / q →
      ∃ C > 0, ∀ u : D.Point → ℝ,
        S.embeddingNorm k r sigma u ≤ C * S.fractionalNorm sigma q u) ∧
  (∀ sigma q theta, 0 ≤ theta → theta < 2 * sigma - D.volume / q →
      ∃ C > 0, ∀ u : D.Point → ℝ,
        S.embeddingNorm theta q sigma u ≤ C * S.fractionalNorm sigma q u)

def Lemma_2_3 (D : BoundedDomainData) (p : CM2Params)
    (S : SemigroupEstimateData D) : Prop :=
  ∃ C > 0, ∀ q > 1, ∀ t > 0, ∀ phi : D.Point → ℝ,
    S.lpNorm q (S.divergenceSemigroup t phi) ≤
      C * (1 + t ^ (-(1 / 2 : ℝ))) *
        Real.exp (-(p.μ) * t) * S.vectorLpNorm q phi

def Lemma_2_4 (D : BoundedDomainData) (p : CM2Params)
    (S : SemigroupEstimateData D) : Prop :=
  ∀ sigma q, 0 < sigma → 1 < q →
    ∃ C > 0, ∀ t > 0, ∀ phi : D.Point → ℝ,
      S.fractionalNorm sigma q (S.divergenceSemigroup t phi) ≤
        C * t ^ (-sigma) * (1 + t ^ (-(1 / 2 : ℝ))) *
          Real.exp (-(p.μ / 2) * t) * S.vectorLpNorm q phi

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
    (T rho p0 : ℝ) : Prop :=
  0 < rho ∧
    0 < T ∧
    max 1 (rho * D.volume / 2) < p0 ∧
    (∃ C, ∀ t, 0 < t → t < T → D.integral (fun x => (u t x) ^ p0) ≤ C)

def Lemma_2_6 (D : BoundedDomainData) : Prop :=
  ∀ u : ℝ → D.Point → ℝ, ∀ T rho p0,
    AbstractLpBootstrapHypothesis D u T rho p0 →
      (∀ pExp, p0 ≤ pExp →
        ∃ A > 0, ∃ B > 0, ∃ K > 0, ∃ L,
          ∀ t, 0 < t → t < T →
            D.integral (fun x => (u t x) ^ pExp) ≤
              K * D.integral (fun x => (u t x) ^ (pExp + rho)) + L) →
      ∀ pExp > 1, ∃ C, ∀ t, 0 < t → t < T →
        D.integral (fun x => (u t x) ^ pExp) ≤ C

def Corollary_2_1 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ T > 0, ∀ u v : ℝ → D.Point → ℝ,
    IsPaper2ClassicalSolution D p T u v →
      (∃ rho > 0, ∃ p0 > max 1 (rho * D.volume / 2),
        ∃ C, ∀ t, 0 < t → t < T →
          D.integral (fun x => (u t x) ^ p0) ≤ C) →
      ∀ pExp > 1, ∃ C, ∀ t, 0 < t → t < T →
        D.integral (fun x => (u t x) ^ pExp) ≤ C

def Proposition_2_1
    (D : BoundedDomainData) (p : CM2Params)
    (S : SemigroupEstimateData D) : Prop :=
  ∀ T > 0, ∀ u v : ℝ → D.Point → ℝ,
    IsPaper2ClassicalSolution D p T u v →
      ∀ pExp, 1 ≤ pExp →
        ∀ t, 0 < t → t < T →
          S.lpNorm pExp (v t) ≤
            (p.ν / p.μ) * S.lpNorm pExp (fun x => (u t x) ^ p.γ)

def Proposition_2_2 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ T > 0, ∀ u v : ℝ → D.Point → ℝ,
    IsPaper2ClassicalSolution D p T u v →
      ∀ pExp > 1, ∃ C, ∀ t, 0 < t → t < T →
        D.integral (fun x => (u t x) ^ pExp) ≤ C

def Proposition_2_3 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ T > 0, ∀ u v : ℝ → D.Point → ℝ,
    IsPaper2ClassicalSolution D p T u v →
      ∀ pExp, max 1 p.β < pExp →
        ∀ eps > 0, ∃ Ceps, ∀ t, 0 < t → t < T →
          D.integral (fun x => (u t x) ^ pExp) ≤ Ceps

def Proposition_2_4 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ T > 0, ∀ u v : ℝ → D.Point → ℝ,
    IsPaper2ClassicalSolution D p T u v →
      IsPaper2BoundedBefore D T u

def Proposition_2_5 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
    ∀ Tmax > 0, ∀ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p Tmax u v →
      InitialTrace D u₀ u →
        ∀ pExp,
          max (p.N : ℝ) (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
            LpPowerBoundedBefore D pExp Tmax u →
              IsPaper2BoundedBefore D Tmax u

def Lemma_2_7 : Prop :=
  ∀ y : ℝ → ℝ, ∀ T C1 C2 C3 C4 eps alpha,
    0 < T → 0 ≤ C1 → 0 ≤ C2 → 0 ≤ C3 → 0 < C4 →
      0 < eps → eps ≤ alpha →
        (∀ t, 0 < t → t < T → y t ≤ C1 + C2 * y t - C4 * (y t) ^ (1 + eps) + C3) →
          ∃ C, ∀ t, 0 < t → t < T → y t ≤ C

def Lemma_3_1 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  p.χ₀ ≤ 0 →
    ∀ T > 0, ∀ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p T u v →
        ∀ t, 0 < t → t < T →
          D.supNorm (u t) ≤ D.supNorm (u 0)

def Lemma_4_1 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ T > 0, ∀ u v : ℝ → D.Point → ℝ,
    IsPaper2ClassicalSolution D p T u v →
      1 ≤ p.β →
        ∃ rho > 0, ∀ eps > 0, ∃ Ceps,
          ∀ t, 0 < t → t < T →
            D.integral (fun x => (u t x) ^ (p.m + rho)) ≤ Ceps

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

/-- Paper2 Theorem 1.2: boundedness/global existence for weak nonlinear cross diffusion. -/
def Theorem_1_2 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  0 ≤ p.a → 0 ≤ p.b → 1 ≤ p.β →
    ((0 < p.m → p.m < 1 →
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2ClassicalSolution D p Tmax u v ∧ IsPaper2BoundedBefore D Tmax u) ∧
    (p.m = 1 → p.χ₀ < chiBeta p →
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2GlobalClassicalSolution D p u v ∧ IsPaper2Bounded D u))

/-- Paper2 Theorem 1.3: boundedness/global existence under a strong logistic source. -/
def Theorem_1_3 (D : BoundedDomainData) (p : CM2Params) (C : Paper2Constants p) : Prop :=
  0 < p.a → 0 < p.b → 0 < p.m → StrongLogisticCondition p C →
    (∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
      ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
        IsPaper2ClassicalSolution D p Tmax u v ∧ IsPaper2BoundedBefore D Tmax u) ∧
    (1 ≤ p.m →
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2GlobalClassicalSolution D p u v ∧ IsPaper2Bounded D u)

end

end ShenWork.Paper2
