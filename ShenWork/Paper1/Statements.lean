/-
  Statement layer for Shen,
  "Existence, uniqueness, stability, and monotonicity of traveling waves for
  repulsion/attraction chemotaxis models with logistic type source".

  The declarations below formalize the paper-level targets as propositions.
  They are not proofs of the paper theorems.
-/
import ShenWork.PDE.LeibnizRule
import Mathlib.Analysis.Convex.Basic

open Filter Topology MeasureTheory

namespace ShenWork.Paper1

noncomputable section

def NonnegativeInitialDatum (u₀ : ℝ → ℝ) : Prop :=
  IsCUnifBdd u₀ ∧ ∀ x, 0 ≤ u₀ x

def UniformlyPositive (u₀ : ℝ → ℝ) : Prop :=
  ∃ δ > 0, ∀ x, δ ≤ u₀ x

def StrictlyPositiveAtLeft (u₀ : ℝ → ℝ) : Prop :=
  ∃ δ > 0, ∀ᶠ x in atBot, δ ≤ u₀ x

theorem UniformlyPositive.pos
    {u₀ : ℝ → ℝ} (h : UniformlyPositive u₀) :
    ∀ x, 0 < u₀ x := by
  rcases h with ⟨δ, hδ, hδle⟩
  intro x
  exact lt_of_lt_of_le hδ (hδle x)

theorem UniformlyPositive.strictlyPositiveAtLeft
    {u₀ : ℝ → ℝ} (h : UniformlyPositive u₀) :
    StrictlyPositiveAtLeft u₀ := by
  rcases h with ⟨δ, hδ, hδle⟩
  exact ⟨δ, hδ, Eventually.of_forall hδle⟩

theorem StrictlyPositiveAtLeft.eventually_pos
    {u₀ : ℝ → ℝ} (h : StrictlyPositiveAtLeft u₀) :
    ∀ᶠ x in atBot, 0 < u₀ x := by
  rcases h with ⟨δ, hδ, hδle⟩
  filter_upwards [hδle] with x hx
  exact lt_of_lt_of_le hδ hx

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

theorem UniformMovingFrameConvergence.profile_eq_of_movingFrame
    {c : ℝ} {U W : ℝ → ℝ}
    (h : UniformMovingFrameConvergence c (fun t x => W (x - c * t)) U) :
    ∀ x, W x = U x := by
  intro y
  by_contra hne
  have hdist_pos : 0 < |W y - U y| :=
    abs_pos.mpr (sub_ne_zero.mpr hne)
  rcases h (|W y - U y| / 2) (by positivity) with ⟨T, hT⟩
  let t : ℝ := T
  let x : ℝ := y + c * T
  have hx : x - c * t = y := by
    dsimp [x, t]
    ring
  have hlt := hT t x le_rfl
  simp [t, x, hx] at hlt
  linarith [abs_nonneg (W y - U y)]

theorem WeightedL2InitialCloseness.refl
    (η : ℝ) (U : ℝ → ℝ) :
    WeightedL2InitialCloseness η U U := by
  simp [WeightedL2InitialCloseness]

theorem WeightedL2InitialCloseness.symm
    {η : ℝ} {u₀ U : ℝ → ℝ}
    (h : WeightedL2InitialCloseness η u₀ U) :
    WeightedL2InitialCloseness η U u₀ := by
  unfold WeightedL2InitialCloseness at h ⊢
  convert h using 1
  ext x
  rw [abs_sub_comm]

theorem IsGlobalCauchySolutionFrom.classical
    {p : CMParams} {u₀ : ℝ → ℝ} {u v : ℝ → ℝ → ℝ}
    (h : IsGlobalCauchySolutionFrom p u₀ u v) :
    IsGlobalClassicalSolution p u v :=
  h.1

theorem IsGlobalCauchySolutionFrom.initial
    {p : CMParams} {u₀ : ℝ → ℝ} {u v : ℝ → ℝ → ℝ}
    (h : IsGlobalCauchySolutionFrom p u₀ u v) :
    HasInitialDatum u u₀ :=
  h.2.1

theorem IsGlobalCauchySolutionFrom.pos
    {p : CMParams} {u₀ : ℝ → ℝ} {u v : ℝ → ℝ → ℝ}
    (h : IsGlobalCauchySolutionFrom p u₀ u v) :
    ∀ t x, 0 ≤ t → 0 < u t x :=
  h.2.2

theorem IsGlobalCauchySolutionFrom.initial_pos
    {p : CMParams} {u₀ : ℝ → ℝ} {u v : ℝ → ℝ → ℝ}
    (h : IsGlobalCauchySolutionFrom p u₀ u v) (x : ℝ) :
    0 < u₀ x := by
  rw [← h.initial x]
  exact h.pos 0 x le_rfl

theorem IsTravelingWave.strictlyPositiveAtLeft
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V) :
    StrictlyPositiveAtLeft U := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  have hnhds : Set.Ioi (1 / 2 : ℝ) ∈ 𝓝 (1 : ℝ) :=
    Ioi_mem_nhds (by norm_num)
  filter_upwards [hTW.lim_neg_inf.1 hnhds] with x hx
  exact le_of_lt hx

theorem IsTravelingWave.nonnegativeInitialDatum
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V) (hU : IsCUnifBdd U) :
    NonnegativeInitialDatum U :=
  ⟨hU, fun x => (hTW.U_pos x).le⟩

theorem IsTravelingWave.to_globalCauchySolutionFrom
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hU_diff : ContDiff ℝ 2 U) (hV_diff : ContDiff ℝ 2 V) :
    IsGlobalCauchySolutionFrom p U
      (fun t x => U (x - c * t)) (fun t x => V (x - c * t)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact _root_.IsTravelingWave.to_movingFrame_global_classical_solution
      p hTW hU_diff hV_diff
  · intro x
    simp
  · intro t x _ht
    exact hTW.U_pos (x - c * t)

theorem IsTravelingWave.weightedL2MovingFrameConvergence_self
    {p : CMParams} {c η : ℝ} {U V : ℝ → ℝ}
    (_hTW : IsTravelingWave p c U V) :
    WeightedL2MovingFrameConvergence η c (fun t x => U (x - c * t)) U := by
  simp [WeightedL2MovingFrameConvergence]

theorem IsTravelingWave.uniformMovingFrameConvergence_self
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (_hTW : IsTravelingWave p c U V) :
    UniformMovingFrameConvergence c (fun t x => U (x - c * t)) U := by
  intro ε hε
  exact ⟨0, fun _t _x _ht => by simpa using hε⟩

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

theorem Lemma_2_1.semigroup_lp_lq
    {S : HeatSemigroupEstimateData}
    (h : Lemma_2_1 S)
    {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) :
    ∃ Cpq > 0, ∀ t > 0, ∀ u : ℝ → ℝ,
      S.lqNorm q (S.semigroup t u) ≤
        Cpq * t ^ (-(1 / 2 : ℝ) * (1 / p - 1 / q)) *
          Real.exp (-t) * S.lpNorm p u :=
  (h p q hp hpq).1

theorem Lemma_2_1.gradient_lp_lq
    {S : HeatSemigroupEstimateData}
    (h : Lemma_2_1 S)
    {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) :
    ∃ Cpq > 0, ∀ t > 0, ∀ u : ℝ → ℝ,
      S.gradientNorm q (S.semigroup t u) ≤
        Cpq * t ^ (-(1 / 2 : ℝ) - (1 / 2 : ℝ) * (1 / p - 1 / q)) *
          Real.exp (-t) * S.lpNorm p u :=
  (h p q hp hpq).2.1

theorem Lemma_2_1.divergence_linf
    {S : HeatSemigroupEstimateData}
    (h : Lemma_2_1 S)
    {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) :
    ∃ Cp > 0, ∀ t > 0, ∀ u : ℝ → ℝ,
      S.linftyNorm (S.divergenceSemigroup t u) ≤
        Cp * t ^ (-(1 / 2 : ℝ) - (1 / (2 * p))) *
          Real.exp (-t) * S.lpNorm p u :=
  (h p q hp hpq).2.2

def PsiDerivativeFormula (u : ℝ → ℝ) (l mu : ℝ) : Prop :=
  ∀ x,
    deriv (fun z => Psi u l mu z) x =
      (-(mu / 2) * Real.exp (-Real.sqrt l * x) *
          (∫ y in Set.Iic x, Real.exp (Real.sqrt l * y) * u y))
        + ((mu / 2) * Real.exp (Real.sqrt l * x) *
          (∫ y in Set.Ioi x, Real.exp (-Real.sqrt l * y) * u y))

def Lemma_2_2 : Prop :=
  ∀ u : ℝ → ℝ, ∀ l mu : ℝ, 0 < l → 0 < mu → IsCUnifBdd u →
    (∀ x,
      Psi u l mu x =
        mu / (2 * Real.sqrt l) *
          ∫ y : ℝ, Real.exp (-Real.sqrt l * |x - y|) * u y) ∧
    PsiDerivativeFormula u l mu

theorem Lemma_2_2.kernel_formula
    (h : Lemma_2_2)
    {u : ℝ → ℝ} {l mu : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hu : IsCUnifBdd u) :
    ∀ x,
      Psi u l mu x =
        mu / (2 * Real.sqrt l) *
          ∫ y : ℝ, Real.exp (-Real.sqrt l * |x - y|) * u y :=
  (h u l mu hl hmu hu).1

theorem Lemma_2_2.derivative_formula
    (h : Lemma_2_2)
    {u : ℝ → ℝ} {l mu : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hu : IsCUnifBdd u) :
    PsiDerivativeFormula u l mu :=
  (h u l mu hl hmu hu).2

theorem Psi_kernel_integrable_of_isCUnifBdd
    {u : ℝ → ℝ} {l : ℝ}
    (hl : 0 < l) (hu : IsCUnifBdd u) (x : ℝ) :
    Integrable
      (fun y : ℝ => Real.exp (-Real.sqrt l * |x - y|) * u y) := by
  rcases hu.2 with ⟨M, hM⟩
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg (u 0)) (hM 0)
  exact _root_.psi_kernel_mul_bounded_integrable hl hM_nonneg hM x
    hu.1.aestronglyMeasurable

theorem Lemma_2_2_kernel_formula_proved :
    ∀ u : ℝ → ℝ, ∀ l mu : ℝ, 0 < l → 0 < mu → IsCUnifBdd u →
      ∀ x,
        Psi u l mu x =
          mu / (2 * Real.sqrt l) *
            ∫ y : ℝ, Real.exp (-Real.sqrt l * |x - y|) * u y := by
  intro u l mu _hl _hmu _hu x
  rfl

theorem Lemma_2_2_derivative_formula_proved :
    ∀ u : ℝ → ℝ, ∀ l mu : ℝ, 0 < l → 0 < mu → IsCUnifBdd u →
      PsiDerivativeFormula u l mu := by
  intro u l mu hl hmu hu
  exact Psi_derivative_formula_general hl hmu hu

theorem Lemma_2_2_proved : Lemma_2_2 := by
  intro u l mu hl hmu hu
  exact
    ⟨Lemma_2_2_kernel_formula_proved u l mu hl hmu hu,
      Lemma_2_2_derivative_formula_proved u l mu hl hmu hu⟩

def Lemma_2_3 : Prop :=
  ∀ u : ℝ → ℝ, ∀ l mu : ℝ, 0 < l → 0 < mu → IsCUnifBdd u →
    (∀ x, 0 ≤ u x) →
      ∀ x, |deriv (fun z => Psi u l mu z) x| ≤ Real.sqrt l * Psi u l mu x

theorem Lemma_2_3.derivative_bound
    (h : Lemma_2_3)
    {u : ℝ → ℝ} {l mu : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hu : IsCUnifBdd u)
    (hu_nonneg : ∀ x, 0 ≤ u x) :
    ∀ x, |deriv (fun z => Psi u l mu z) x| ≤ Real.sqrt l * Psi u l mu x :=
  h u l mu hl hmu hu hu_nonneg

theorem Lemma_2_3_proved : Lemma_2_3 := by
  intro u l mu hl hmu hu hu_nonneg x
  exact Psi_deriv_abs_le_general hl hmu hu hu_nonneg x

theorem Lemma_2_3_of_Lemma_2_2 (h22 : Lemma_2_2) : Lemma_2_3 := by
  intro u l mu hl hmu hu hu_nonneg x
  let a : ℝ := Real.sqrt l
  have ha : 0 < a := by
    dsimp [a]
    exact Real.sqrt_pos.mpr hl
  let A : ℝ :=
    Real.exp (-a * x) * ∫ y in Set.Iic x, Real.exp (a * y) * u y
  let B : ℝ :=
    Real.exp (a * x) * ∫ y in Set.Ioi x, Real.exp (-a * y) * u y
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (Real.exp_nonneg _)
      (MeasureTheory.integral_nonneg
        (fun y => mul_nonneg (Real.exp_nonneg _) (hu_nonneg y)))
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (Real.exp_nonneg _)
      (MeasureTheory.integral_nonneg
        (fun y => mul_nonneg (Real.exp_nonneg _) (hu_nonneg y)))
  have hder :
      deriv (fun z => Psi u l mu z) x =
        -(mu / 2) * A + (mu / 2) * B := by
    have h := (h22.derivative_formula hl hmu hu) x
    simpa [A, B, a, mul_assoc, mul_left_comm, mul_comm] using h
  have habs :
      |deriv (fun z => Psi u l mu z) x| ≤ (mu / 2) * (A + B) := by
    rw [hder]
    have hmu2_nonneg : 0 ≤ mu / 2 := by positivity
    have htermA : |-(mu / 2) * A| = (mu / 2) * A := by
      rw [show -(mu / 2) * A = -((mu / 2) * A) by ring]
      rw [abs_neg, abs_of_nonneg (mul_nonneg hmu2_nonneg hA_nonneg)]
    have htermB : |(mu / 2) * B| = (mu / 2) * B := by
      rw [abs_of_nonneg (mul_nonneg hmu2_nonneg hB_nonneg)]
    calc
      |-(mu / 2) * A + (mu / 2) * B|
          ≤ |-(mu / 2) * A| + |(mu / 2) * B| := abs_add_le _ _
      _ = (mu / 2) * A + (mu / 2) * B := by
            rw [htermA, htermB]
      _ = (mu / 2) * (A + B) := by ring
  have hiu :
      Integrable
        (fun y : ℝ => Real.exp (-a * |x - y|) * u y) := by
    dsimp [a]
    simpa using Psi_kernel_integrable_of_isCUnifBdd hl hu x
  have hkernel_split :
      (∫ y : ℝ, Real.exp (-a * |x - y|) * u y) = A + B := by
    have hsplit :=
      MeasureTheory.integral_add_compl (s := Set.Iic x) measurableSet_Iic hiu
    simp only [Set.compl_Iic] at hsplit
    have hleft :
        ∫ y in Set.Iic x, Real.exp (-a * |x - y|) * u y = A := by
      have hleft_eq :
          Set.EqOn
            (fun y : ℝ => Real.exp (-a * |x - y|) * u y)
            (fun y : ℝ => Real.exp (-a * x) * (Real.exp (a * y) * u y))
            (Set.Iic x) := by
        intro y hy
        have hyx : y ≤ x := by simpa using hy
        change
          Real.exp (-a * |x - y|) * u y =
            Real.exp (-a * x) * (Real.exp (a * y) * u y)
        rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
        rw [show -a * (x - y) = -a * x + a * y by ring, Real.exp_add]
        ring_nf
      calc
        ∫ y in Set.Iic x, Real.exp (-a * |x - y|) * u y
            = ∫ y in Set.Iic x,
                Real.exp (-a * x) * (Real.exp (a * y) * u y) := by
              exact MeasureTheory.setIntegral_congr_fun measurableSet_Iic hleft_eq
        _ = Real.exp (-a * x) * ∫ y in Set.Iic x, Real.exp (a * y) * u y := by
              exact MeasureTheory.integral_const_mul _ _
        _ = A := by rfl
    have hright :
        ∫ y in Set.Ioi x, Real.exp (-a * |x - y|) * u y = B := by
      have hright_eq :
          Set.EqOn
            (fun y : ℝ => Real.exp (-a * |x - y|) * u y)
            (fun y : ℝ => Real.exp (a * x) * (Real.exp (-a * y) * u y))
            (Set.Ioi x) := by
        intro y hy
        have hxy : x < y := by simpa using hy
        change
          Real.exp (-a * |x - y|) * u y =
            Real.exp (a * x) * (Real.exp (-a * y) * u y)
        rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hxy))]
        rw [show -a * -(x - y) = a * x + -a * y by ring, Real.exp_add]
        ring_nf
      calc
        ∫ y in Set.Ioi x, Real.exp (-a * |x - y|) * u y
            = ∫ y in Set.Ioi x,
                Real.exp (a * x) * (Real.exp (-a * y) * u y) := by
              exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hright_eq
        _ = Real.exp (a * x) * ∫ y in Set.Ioi x, Real.exp (-a * y) * u y := by
              exact MeasureTheory.integral_const_mul _ _
        _ = B := by rfl
    calc
      ∫ y : ℝ, Real.exp (-a * |x - y|) * u y
          = (∫ y in Set.Iic x, Real.exp (-a * |x - y|) * u y) +
              (∫ y in Set.Ioi x, Real.exp (-a * |x - y|) * u y) := hsplit.symm
      _ = A + B := by rw [hleft, hright]
  have hpsi :
      Real.sqrt l * Psi u l mu x = (mu / 2) * (A + B) := by
    dsimp [a] at hkernel_split
    unfold Psi
    rw [hkernel_split]
    have hsqrt_pos : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl
    field_simp [ne_of_gt hsqrt_pos]
  exact le_trans habs (le_of_eq hpsi.symm)

def Lemma_2_3_unit : Prop :=
  ∀ u : ℝ → ℝ, IsCUnifBdd u →
    (∀ x, 0 ≤ u x) →
      ∀ x, |deriv (Psi u 1 1) x| ≤ Psi u 1 1 x

theorem Lemma_2_3_unit_proved : Lemma_2_3_unit := by
  intro u hu hu_nonneg x
  rcases hu.2 with ⟨M, hM⟩
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg (u 0)) (hM 0)
  have hint_raw :
      Integrable (fun y => Real.exp (-1 * |x - y|) * u y) :=
    kernel_mul_bounded_integrable u M hM_nonneg hM x hu.1.aestronglyMeasurable
  have hint :
      Integrable (fun y => Real.exp (-|x - y|) * u y) := by
    simpa using hint_raw
  exact Psi_deriv_abs_le' hu_nonneg x hint hu.1.aestronglyMeasurable

theorem Psi_one_mu_eq (u : ℝ → ℝ) (mu x : ℝ) :
    Psi u 1 mu x = mu * Psi u 1 1 x := by
  simp [Psi]
  ring

theorem Lemma_2_3_unit_mu_proved :
    ∀ u : ℝ → ℝ, ∀ mu : ℝ, 0 < mu → IsCUnifBdd u →
      (∀ x, 0 ≤ u x) →
        ∀ x, |deriv (Psi u 1 mu) x| ≤ Psi u 1 mu x := by
  intro u mu hmu hu hu_nonneg x
  have hderiv :
      deriv (Psi u 1 mu) x = mu * deriv (Psi u 1 1) x := by
    rw [show Psi u 1 mu = fun z => mu * Psi u 1 1 z from by
      ext z
      exact Psi_one_mu_eq u mu z]
    rw [deriv_const_mul_field]
  rw [hderiv, Psi_one_mu_eq u mu x]
  rw [abs_mul, abs_of_pos hmu]
  exact mul_le_mul_of_nonneg_left
    (Lemma_2_3_unit_proved u hu hu_nonneg x) hmu.le

def Lemma_2_4 : Prop :=
  ∀ M k : ℝ, 1 ≤ M → 0 < k → k < 1 →
    ∀ u : ℝ → ℝ, IsCUnifBdd u →
      (∀ x, 0 ≤ u x) →
      (∀ x, u x ≤ min M (Real.exp (-k * x))) →
        ∀ x, Psi u 1 1 x ≤ min M (1 / (1 - k ^ 2) * Real.exp (-k * x))

theorem Lemma_2_4_proved : Lemma_2_4 := by
  intro M k hM hk hk1 u hu hu_nonneg hu_bound x
  have hM_nonneg : 0 ≤ M := le_trans zero_le_one hM
  have huM : ∀ y, u y ≤ M := by
    intro y
    exact le_trans (hu_bound y) (min_le_left _ _)
  have huexp : ∀ y, u y ≤ Real.exp (-k * y) := by
    intro y
    exact le_trans (hu_bound y) (min_le_right _ _)
  exact
    Psi_le_min_const_exp_of_nonneg_le hM_nonneg hk hk1
      hu.1 hu_nonneg huM huexp x

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

theorem Lemma_2_5.weighted_resolvent_gradient
    (h : Lemma_2_5)
    {pExp gamma l mu : ℝ}
    (hpExp : 1 < pExp) (hgamma : 0 < gamma) (hl : 0 < l) (hmu : 0 < mu) :
    ∃ C > 0, ∀ u : ℝ → ℝ, ∀ psi : ExponentialWeight,
      Integrable (fun x => (u x) ^ (gamma * pExp) * psi.weight x) →
        Integrable
          (fun x =>
            |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp *
              psi.weight x) ∧
        ∫ x : ℝ,
            |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp *
              psi.weight x
          ≤ C * ∫ x : ℝ, (u x) ^ (gamma * pExp) * psi.weight x :=
  h pExp gamma l mu hpExp hgamma hl hmu

theorem Lemma_2_5.weighted_resolvent_gradient_unit
    (h : Lemma_2_5) (p : CMParams) {pExp : ℝ} (hpExp : 1 < pExp) :
    ∃ C > 0, ∀ u : ℝ → ℝ, ∀ psi : ExponentialWeight,
      Integrable (fun x => (u x) ^ (p.γ * pExp) * psi.weight x) →
        Integrable
          (fun x =>
            |deriv (fun z => Psi (fun y => (u y) ^ p.γ) 1 1 z) x| ^ pExp *
              psi.weight x) ∧
        ∫ x : ℝ,
            |deriv (fun z => Psi (fun y => (u y) ^ p.γ) 1 1 z) x| ^ pExp *
              psi.weight x
          ≤ C * ∫ x : ℝ, (u x) ^ (p.γ * pExp) * psi.weight x :=
  h.weighted_resolvent_gradient hpExp
    (lt_of_lt_of_le one_pos p.hγ) one_pos one_pos

theorem Lemma_2_5.weighted_resolvent_gradient_unit_L2
    (h : Lemma_2_5) (p : CMParams) :
    ∃ C > 0, ∀ u : ℝ → ℝ, ∀ psi : ExponentialWeight,
      Integrable (fun x => (u x) ^ (p.γ * (2 : ℝ)) * psi.weight x) →
        Integrable
          (fun x =>
            |deriv (fun z => Psi (fun y => (u y) ^ p.γ) 1 1 z) x| ^ (2 : ℝ) *
              psi.weight x) ∧
        ∫ x : ℝ,
            |deriv (fun z => Psi (fun y => (u y) ^ p.γ) 1 1 z) x| ^ (2 : ℝ) *
              psi.weight x
          ≤ C * ∫ x : ℝ, (u x) ^ (p.γ * (2 : ℝ)) * psi.weight x :=
  h.weighted_resolvent_gradient_unit p (by norm_num : (1 : ℝ) < 2)

def frozenElliptic (p : CMParams) (u : ℝ → ℝ) : ℝ → ℝ :=
  fun x => Psi (fun y => (u y) ^ p.γ) 1 1 x

theorem frozenElliptic_nonneg
    (p : CMParams) {u : ℝ → ℝ} (hu : ∀ x, 0 ≤ u x) (x : ℝ) :
    0 ≤ frozenElliptic p u x := by
  unfold frozenElliptic
  exact Psi_nonneg one_pos one_pos
    (fun y => Real.rpow_nonneg (hu y) p.γ) x

def frozenWaveOperator (p : CMParams) (c : ℝ) (u W : ℝ → ℝ) : ℝ → ℝ :=
  fun x =>
    iteratedDeriv 2 W x + c * deriv W x
      - p.χ *
        deriv (fun y => (W y) ^ p.m * deriv (frozenElliptic p u) y) x
      + W x * (1 - (W x) ^ p.α)

/-- Stationary profile obtained after the frozen auxiliary fixed-point step.
This is the exact bridge object needed before producing an `IsTravelingWave`.
The hard analytic work is to prove these fields for the Schauder fixed point. -/
structure FrozenStationaryWaveProfile
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop where
  hc : 0 < c
  U_pos : ∀ x, 0 < U x
  stationary_eq : ∀ x, frozenWaveOperator p c U U x = 0
  elliptic_eq :
    ∀ x,
      iteratedDeriv 2 (frozenElliptic p U) x -
          frozenElliptic p U x + (U x) ^ p.γ = 0
  lim_neg_inf :
    Tendsto U atBot (𝓝 1) ∧ Tendsto (frozenElliptic p U) atBot (𝓝 1)
  lim_pos_inf :
    Tendsto U atTop (𝓝 0) ∧ Tendsto (frozenElliptic p U) atTop (𝓝 0)

theorem FrozenStationaryWaveProfile.to_travelingWave
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : FrozenStationaryWaveProfile p c U) :
    IsTravelingWave p c U (frozenElliptic p U) := by
  refine
    { hc := h.hc
      U_pos := h.U_pos
      ode_U := ?_
      ode_V := h.elliptic_eq
      lim_neg_inf := h.lim_neg_inf
      lim_pos_inf := h.lim_pos_inf }
  intro x
  simpa [frozenWaveOperator] using h.stationary_eq x

theorem FrozenStationaryWaveProfile.to_monotoneTravelingWave
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : FrozenStationaryWaveProfile p c U)
    (hUmono : ∀ x, deriv U x ≤ 0)
    (hVmono : ∀ x, deriv (frozenElliptic p U) x ≤ 0) :
    IsMonotoneTravelingWave p c U (frozenElliptic p U) :=
  ⟨h.to_travelingWave, hUmono, hVmono⟩

def IsFrozenSuperSolution (p : CMParams) (c : ℝ) (u W : ℝ → ℝ) : Prop :=
  ∀ x, frozenWaveOperator p c u W x ≤ 0

def IsFrozenSubSolutionOn (p : CMParams) (c : ℝ) (u W : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, 0 ≤ frozenWaveOperator p c u W x

def expDecay (κ : ℝ) : ℝ → ℝ :=
  fun x => Real.exp (-(κ * x))

theorem expDecay_pos (κ x : ℝ) :
    0 < expDecay κ x := by
  exact Real.exp_pos _

theorem expDecay_antitone {κ : ℝ} (hκ : 0 ≤ κ) :
    Antitone (expDecay κ) := by
  intro x y hxy
  unfold expDecay
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hxy hκ]

theorem expDecay_tendsto_atTop {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (expDecay κ) atTop (𝓝 0) := by
  have hmul : Tendsto (fun x : ℝ => κ * x) atTop atTop :=
    (Filter.tendsto_id.atTop_mul_const hκ).congr (fun x => mul_comm x κ)
  have hneg : Tendsto (fun x : ℝ => -(κ * x)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hmul
  simpa [expDecay] using Real.tendsto_exp_atBot.comp hneg

theorem expDecay_tendsto_atBot {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (expDecay κ) atBot atTop := by
  have hmul : Tendsto (fun x : ℝ => κ * x) atBot atBot :=
    (Filter.tendsto_id.atBot_mul_const hκ).congr (fun x => mul_comm x κ)
  have hneg : Tendsto (fun x : ℝ => -(κ * x)) atBot atTop :=
    tendsto_neg_atBot_atTop.comp hmul
  simpa [expDecay] using Real.tendsto_exp_atTop.comp hneg

theorem expDecay_hasDerivAt (κ x : ℝ) :
    HasDerivAt (expDecay κ) (-κ * expDecay κ x) x := by
  have hlin : HasDerivAt (fun y : ℝ => -κ * y) (-κ) x :=
    by simpa using (hasDerivAt_id x).const_mul (-κ)
  change
    HasDerivAt (fun y : ℝ => Real.exp (-(κ * y)))
      (-κ * Real.exp (-(κ * x))) x
  simpa [expDecay, mul_comm, mul_left_comm, mul_assoc] using hlin.exp

theorem expDecay_deriv (κ x : ℝ) :
    deriv (expDecay κ) x = -κ * expDecay κ x :=
  (expDecay_hasDerivAt κ x).deriv

theorem expDecay_iteratedDeriv_two (κ x : ℝ) :
    iteratedDeriv 2 (expDecay κ) x = κ ^ 2 * expDecay κ x := by
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  change deriv (deriv (expDecay κ)) x = κ ^ 2 * expDecay κ x
  have hderiv :
      deriv (expDecay κ) = fun y => -κ * expDecay κ y := by
    ext y
    exact expDecay_deriv κ y
  rw [hderiv]
  have h :=
    ((expDecay_hasDerivAt κ x).const_mul (-κ)).deriv
  simpa [pow_two, mul_assoc] using h

theorem expDecay_linear_part_eq
    (κ c x : ℝ) :
    iteratedDeriv 2 (expDecay κ) x + c * deriv (expDecay κ) x +
        expDecay κ x =
      (κ ^ 2 - c * κ + 1) * expDecay κ x := by
  rw [expDecay_iteratedDeriv_two, expDecay_deriv]
  ring

theorem expDecay_linear_part_kappa_eq_zero
    {c : ℝ} (hc : 2 ≤ c) (x : ℝ) :
    iteratedDeriv 2 (expDecay (kappa c)) x +
        c * deriv (expDecay (kappa c)) x +
        expDecay (kappa c) x = 0 := by
  rw [expDecay_linear_part_eq]
  rw [kappa_quadratic_eq_zero hc]
  ring

def upperBarrier (κ M : ℝ) : ℝ → ℝ :=
  fun x => min M (Real.exp (-κ * x))

theorem upperBarrier_le_M (κ M x : ℝ) :
    upperBarrier κ M x ≤ M :=
  min_le_left _ _

theorem upperBarrier_le_exp (κ M x : ℝ) :
    upperBarrier κ M x ≤ Real.exp (-κ * x) :=
  min_le_right _ _

theorem upperBarrier_mono_M {κ M₁ M₂ : ℝ} (hM : M₁ ≤ M₂) (x : ℝ) :
    upperBarrier κ M₁ x ≤ upperBarrier κ M₂ x :=
  min_le_min hM le_rfl

theorem upperBarrier_eq_M_of_le_exp {κ M x : ℝ}
    (h : M ≤ Real.exp (-κ * x)) :
    upperBarrier κ M x = M := by
  exact min_eq_left h

theorem upperBarrier_eq_exp_of_exp_le {κ M x : ℝ}
    (h : Real.exp (-κ * x) ≤ M) :
    upperBarrier κ M x = Real.exp (-κ * x) := by
  exact min_eq_right h

theorem upperBarrier_nonneg {κ M : ℝ} (hM : 0 ≤ M) (x : ℝ) :
    0 ≤ upperBarrier κ M x :=
  le_min hM (Real.exp_pos _).le

theorem upperBarrier_pos {κ M : ℝ} (hM : 0 < M) (x : ℝ) :
    0 < upperBarrier κ M x :=
  lt_min hM (Real.exp_pos _)

theorem upperBarrier_continuous (κ M : ℝ) :
    Continuous (upperBarrier κ M) := by
  unfold upperBarrier
  exact continuous_const.min
    (Real.continuous_exp.comp (continuous_const.mul continuous_id))

theorem upperBarrier_isBddFun {κ M : ℝ} (hM : 0 ≤ M) :
    IsBddFun (upperBarrier κ M) := by
  refine ⟨M, ?_⟩
  intro x
  rw [abs_of_nonneg (upperBarrier_nonneg hM x)]
  exact upperBarrier_le_M κ M x

theorem upperBarrier_cunif_bdd {κ M : ℝ} (hM : 0 ≤ M) :
    IsCUnifBdd (upperBarrier κ M) :=
  ⟨upperBarrier_continuous κ M, upperBarrier_isBddFun hM⟩

theorem upperBarrier_rpow_le_M
    {κ M a : ℝ} (hM : 0 ≤ M) (ha : 0 ≤ a) (x : ℝ) :
    (upperBarrier κ M x) ^ a ≤ M ^ a :=
  Real.rpow_le_rpow (upperBarrier_nonneg hM x) (upperBarrier_le_M κ M x) ha

theorem upperBarrier_rpow_le_exp
    {κ M a : ℝ} (hM : 0 ≤ M) (ha : 0 ≤ a) (x : ℝ) :
    (upperBarrier κ M x) ^ a ≤ (Real.exp (-κ * x)) ^ a :=
  Real.rpow_le_rpow (upperBarrier_nonneg hM x) (upperBarrier_le_exp κ M x) ha

theorem upperBarrier_rpow_le_exp_mul
    {κ M a : ℝ} (hM : 0 ≤ M) (ha : 0 ≤ a) (x : ℝ) :
    (upperBarrier κ M x) ^ a ≤ Real.exp (-κ * a * x) := by
  calc
    (upperBarrier κ M x) ^ a ≤ (Real.exp (-κ * x)) ^ a :=
      upperBarrier_rpow_le_exp hM ha x
    _ = Real.exp (-κ * a * x) := by
      rw [← Real.exp_mul]
      congr 1
      ring

theorem upperBarrier_antitone {κ M : ℝ} (hκ : 0 ≤ κ) :
    Antitone (upperBarrier κ M) := by
  intro x₁ x₂ hx
  unfold upperBarrier
  exact min_le_min le_rfl
    (Real.exp_le_exp.mpr (by nlinarith))

def lowerBarrierRaw (κ κtilde D : ℝ) : ℝ → ℝ :=
  fun x => Real.exp (-κ * x) - D * Real.exp (-κtilde * x)

theorem lowerBarrierRaw_continuous (κ κtilde D : ℝ) :
    Continuous (lowerBarrierRaw κ κtilde D) := by
  have hlinκ : Continuous (fun x : ℝ => (-κ) * x) :=
    continuous_const.mul continuous_id
  have hlinκtilde : Continuous (fun x : ℝ => (-κtilde) * x) :=
    continuous_const.mul continuous_id
  have hκ : Continuous (fun x : ℝ => Real.exp ((-κ) * x)) :=
    Real.continuous_exp.comp hlinκ
  have hκtilde : Continuous (fun x : ℝ => Real.exp ((-κtilde) * x)) :=
    Real.continuous_exp.comp hlinκtilde
  have hD : Continuous (fun _ : ℝ => D) := continuous_const
  change Continuous
    (fun x : ℝ => Real.exp ((-κ) * x) - D * Real.exp ((-κtilde) * x))
  exact hκ.sub (hD.mul hκtilde)

theorem lowerBarrierRaw_hasDerivAt (κ κtilde D x : ℝ) :
    HasDerivAt (lowerBarrierRaw κ κtilde D)
      (-κ * Real.exp (-κ * x) + D * κtilde * Real.exp (-κtilde * x)) x := by
  unfold lowerBarrierRaw
  have hκ :
      HasDerivAt
        (fun y : ℝ => Real.exp (-κ * y))
        (-κ * Real.exp (-κ * x)) x := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id x).const_mul κ).neg.exp)
  have hκtilde :
      HasDerivAt
        (fun y : ℝ => D * Real.exp (-κtilde * y))
        (D * (-κtilde * Real.exp (-κtilde * x))) x := by
    have hbase :
        HasDerivAt
          (fun y : ℝ => Real.exp (-κtilde * y))
          (-κtilde * Real.exp (-κtilde * x)) x := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (((hasDerivAt_id x).const_mul κtilde).neg.exp)
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbase.const_mul D
  simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hκ.sub hκtilde

theorem lowerBarrierRaw_deriv (κ κtilde D x : ℝ) :
    deriv (lowerBarrierRaw κ κtilde D) x =
      -κ * Real.exp (-κ * x) + D * κtilde * Real.exp (-κtilde * x) := by
  exact (lowerBarrierRaw_hasDerivAt κ κtilde D x).deriv

theorem lowerBarrierRaw_second_deriv (κ κtilde D x : ℝ) :
    iteratedDeriv 2 (lowerBarrierRaw κ κtilde D) x =
      κ ^ 2 * Real.exp (-κ * x) - D * κtilde ^ 2 * Real.exp (-κtilde * x) := by
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  have hder_fun :
      deriv (lowerBarrierRaw κ κtilde D) =
        fun y : ℝ =>
          -κ * Real.exp (-κ * y) + D * κtilde * Real.exp (-κtilde * y) := by
    funext y
    exact lowerBarrierRaw_deriv κ κtilde D y
  rw [hder_fun]
  have hκbase :
      HasDerivAt
        (fun y : ℝ => Real.exp (-κ * y))
        (-κ * Real.exp (-κ * x)) x := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id x).const_mul κ).neg.exp)
  have hκ :
      HasDerivAt
        (fun y : ℝ => -κ * Real.exp (-κ * y))
        (κ ^ 2 * Real.exp (-κ * x)) x := by
    convert hκbase.const_mul (-κ) using 1
    ring
  have hκtilde_base :
      HasDerivAt
        (fun y : ℝ => Real.exp (-κtilde * y))
        (-κtilde * Real.exp (-κtilde * x)) x := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id x).const_mul κtilde).neg.exp)
  have hκtilde :
      HasDerivAt
        (fun y : ℝ => D * κtilde * Real.exp (-κtilde * y))
        (-(D * κtilde ^ 2 * Real.exp (-κtilde * x))) x := by
    convert hκtilde_base.const_mul (D * κtilde) using 1
    ring
  have hder := hκ.add hκtilde
  simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hder.deriv

theorem lowerBarrierRaw_linear_part_eq
    (κ κtilde D c x : ℝ) :
    iteratedDeriv 2 (lowerBarrierRaw κ κtilde D) x +
        c * deriv (lowerBarrierRaw κ κtilde D) x +
        lowerBarrierRaw κ κtilde D x =
      (κ ^ 2 - c * κ + 1) * Real.exp (-κ * x) -
        D * (κtilde ^ 2 - c * κtilde + 1) *
          Real.exp (-κtilde * x) := by
  rw [lowerBarrierRaw_second_deriv, lowerBarrierRaw_deriv]
  unfold lowerBarrierRaw
  ring

theorem lowerBarrierRaw_linear_part_eq_of_kappa_speed
    {κ κtilde D c x : ℝ} (hκ : κ ≠ 0) (hc : c = κ + κ⁻¹) :
    iteratedDeriv 2 (lowerBarrierRaw κ κtilde D) x +
        c * deriv (lowerBarrierRaw κ κtilde D) x +
        lowerBarrierRaw κ κtilde D x =
      -D * (κtilde ^ 2 - c * κtilde + 1) *
        Real.exp (-κtilde * x) := by
  rw [lowerBarrierRaw_linear_part_eq, hc]
  have hzero : κ ^ 2 - (κ + κ⁻¹) * κ + 1 = 0 := by
    field_simp [hκ]
    ring
  rw [hzero]
  ring

theorem lowerBarrierRaw_speed_coefficient_neg
    {κ κtilde c : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ < 1) (hgap : κ < κtilde)
    (hκtilde1 : κtilde ≤ 1) (hc : c = κ + κ⁻¹) :
    κtilde ^ 2 - c * κtilde + 1 < 0 := by
  have hinv_gt_one : 1 < κ⁻¹ := (one_lt_inv₀ hκ0).2 hκ1
  have hleft : 0 < κtilde - κ := sub_pos.mpr hgap
  have hright : κtilde - κ⁻¹ < 0 := sub_neg.mpr (lt_of_le_of_lt hκtilde1 hinv_gt_one)
  have hfactor :
      κtilde ^ 2 - c * κtilde + 1 =
        (κtilde - κ) * (κtilde - κ⁻¹) := by
    rw [hc]
    field_simp [ne_of_gt hκ0]
    ring
  rw [hfactor]
  exact mul_neg_of_pos_of_neg hleft hright

theorem lowerBarrierRaw_speed_denominator_pos
    {κ κtilde c : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ < 1) (hgap : κ < κtilde)
    (hκtilde1 : κtilde ≤ 1) (hc : c = κ + κ⁻¹) :
    0 < c * κtilde - κtilde ^ 2 - 1 := by
  have h :=
    lowerBarrierRaw_speed_coefficient_neg hκ0 hκ1 hgap hκtilde1 hc
  nlinarith

theorem lowerBarrierRaw_linear_part_pos_of_kappa_speed
    {κ κtilde D c x : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ < 1) (hgap : κ < κtilde)
    (hκtilde1 : κtilde ≤ 1) (hD : 0 < D) (hc : c = κ + κ⁻¹) :
    0 <
      iteratedDeriv 2 (lowerBarrierRaw κ κtilde D) x +
        c * deriv (lowerBarrierRaw κ κtilde D) x +
        lowerBarrierRaw κ κtilde D x := by
  rw [lowerBarrierRaw_linear_part_eq_of_kappa_speed (ne_of_gt hκ0) hc]
  apply mul_pos
  · exact mul_pos_of_neg_of_neg (neg_lt_zero.mpr hD)
      (lowerBarrierRaw_speed_coefficient_neg hκ0 hκ1 hgap hκtilde1 hc)
  · exact Real.exp_pos _

theorem lowerBarrierRaw_linear_part_pos_of_speed_gt_two
    {κtilde D c x : ℝ}
    (hc : 2 < c) (hgap : kappa c < κtilde)
    (hκtilde1 : κtilde ≤ 1) (hD : 0 < D) :
    0 <
      iteratedDeriv 2 (lowerBarrierRaw (kappa c) κtilde D) x +
        c * deriv (lowerBarrierRaw (kappa c) κtilde D) x +
        lowerBarrierRaw (kappa c) κtilde D x := by
  exact
    lowerBarrierRaw_linear_part_pos_of_kappa_speed
      (kappa_pos_of_two_lt hc)
      (kappa_lt_one_of_two_lt hc)
      hgap hκtilde1 hD
      (kappa_add_inv_eq_of_two_lt hc).symm

theorem lowerBarrierRaw_linear_part_pos_of_cStarLower_lt
    {p : CMParams} {κtilde D c x : ℝ}
    (hc : cStarLower p < c) (hgap : kappa c < κtilde)
    (hκtilde1 : κtilde ≤ 1) (hD : 0 < D) :
    0 <
      iteratedDeriv 2 (lowerBarrierRaw (kappa c) κtilde D) x +
        c * deriv (lowerBarrierRaw (kappa c) κtilde D) x +
        lowerBarrierRaw (kappa c) κtilde D x :=
  lowerBarrierRaw_linear_part_pos_of_speed_gt_two
    (two_lt_of_cStarLower_lt hc) hgap hκtilde1 hD

def lowerBarrierXMinus (κ κtilde D : ℝ) : ℝ :=
  Real.log D / (κtilde - κ)

theorem lowerBarrierRaw_eq_exp_mul (κ κtilde D x : ℝ) :
    lowerBarrierRaw κ κtilde D x =
      Real.exp (-κ * x) * (1 - D * Real.exp (-(κtilde - κ) * x)) := by
  unfold lowerBarrierRaw
  have hexp :
      Real.exp (-κtilde * x) =
        Real.exp (-κ * x) * Real.exp (-(κtilde - κ) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

theorem lowerBarrierRaw_le_exp {κ κtilde D x : ℝ} (hD : 0 ≤ D) :
    lowerBarrierRaw κ κtilde D x ≤ Real.exp (-κ * x) := by
  unfold lowerBarrierRaw
  have hnonneg : 0 ≤ D * Real.exp (-κtilde * x) :=
    mul_nonneg hD (Real.exp_pos _).le
  linarith

theorem lowerBarrierRaw_nonneg_of_xminus_le
    {κ κtilde D x : ℝ} (hgap : 0 < κtilde - κ) (hD : 0 < D)
    (hx : lowerBarrierXMinus κ κtilde D ≤ x) :
    0 ≤ lowerBarrierRaw κ κtilde D x := by
  rw [lowerBarrierRaw_eq_exp_mul]
  apply mul_nonneg (Real.exp_pos _).le
  have hlog_le : Real.log D ≤ (κtilde - κ) * x := by
    rw [lowerBarrierXMinus] at hx
    simpa [mul_comm] using (div_le_iff₀ hgap).mp hx
  have hexp_le :
      Real.exp (Real.log D + (-(κtilde - κ) * x)) ≤ Real.exp 0 :=
    Real.exp_le_exp.mpr (by linarith)
  have hDexp_le : D * Real.exp (-(κtilde - κ) * x) ≤ 1 := by
    simpa [Real.exp_add, Real.exp_log hD] using hexp_le
  linarith

theorem lowerBarrierRaw_pos_of_xminus_lt
    {κ κtilde D x : ℝ} (hgap : 0 < κtilde - κ) (hD : 0 < D)
    (hx : lowerBarrierXMinus κ κtilde D < x) :
    0 < lowerBarrierRaw κ κtilde D x := by
  rw [lowerBarrierRaw_eq_exp_mul]
  apply mul_pos (Real.exp_pos _)
  have hlog_lt : Real.log D < (κtilde - κ) * x := by
    rw [lowerBarrierXMinus] at hx
    simpa [mul_comm] using (div_lt_iff₀ hgap).mp hx
  have hexp_lt :
      Real.exp (Real.log D + (-(κtilde - κ) * x)) < Real.exp 0 :=
    Real.exp_lt_exp.mpr (by linarith)
  have hDexp_lt : D * Real.exp (-(κtilde - κ) * x) < 1 := by
    simpa [Real.exp_add, Real.exp_log hD] using hexp_lt
  linarith

theorem lowerBarrierRaw_eq_zero_at_xminus
    {κ κtilde D : ℝ} (hgap : 0 < κtilde - κ) (hD : 0 < D) :
    lowerBarrierRaw κ κtilde D (lowerBarrierXMinus κ κtilde D) = 0 := by
  rw [lowerBarrierRaw_eq_exp_mul]
  have hx :
      (κtilde - κ) * lowerBarrierXMinus κ κtilde D = Real.log D := by
    unfold lowerBarrierXMinus
    field_simp [ne_of_gt hgap]
  have hDexp :
      D * Real.exp (-(κtilde - κ) * lowerBarrierXMinus κ κtilde D) = 1 := by
    have hexp :
        Real.exp
          (Real.log D + (-(κtilde - κ) * lowerBarrierXMinus κ κtilde D)) =
          Real.exp 0 := by
      congr 1
      linarith
    simpa [Real.exp_add, Real.exp_log hD] using hexp
  rw [hDexp]
  ring

def lowerBarrierXPlus (κ κtilde D : ℝ) : ℝ :=
  Real.log (κtilde * D / κ) / (κtilde - κ)

theorem lowerBarrierXPlus_of_exp_choice
    {κ κtilde x : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ) :
    lowerBarrierXPlus κ κtilde
        (κ / κtilde * Real.exp ((κtilde - κ) * x)) = x := by
  have hκtilde : 0 < κtilde := by linarith
  unfold lowerBarrierXPlus
  have harg :
      κtilde * (κ / κtilde * Real.exp ((κtilde - κ) * x)) / κ =
        Real.exp ((κtilde - κ) * x) := by
    field_simp [ne_of_gt hκ, ne_of_gt hκtilde]
  rw [harg, Real.log_exp]
  field_simp [ne_of_gt hgap]

theorem lowerBarrierXPlus_mono_D
    {κ κtilde D₁ D₂ : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hD₁ : 0 < D₁) (hDle : D₁ ≤ D₂) :
    lowerBarrierXPlus κ κtilde D₁ ≤ lowerBarrierXPlus κ κtilde D₂ := by
  have hκtilde : 0 < κtilde := by linarith
  have harg₁ : 0 < κtilde * D₁ / κ := by positivity
  have hmul : κtilde * D₁ ≤ κtilde * D₂ :=
    mul_le_mul_of_nonneg_left hDle hκtilde.le
  have hargle : κtilde * D₁ / κ ≤ κtilde * D₂ / κ :=
    div_le_div_of_nonneg_right hmul hκ.le
  unfold lowerBarrierXPlus
  exact div_le_div_of_nonneg_right (Real.log_le_log harg₁ hargle) hgap.le

theorem lowerBarrierExpXPlus_antitone_D
    {κ κtilde D₁ D₂ : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hD₁ : 0 < D₁) (hDle : D₁ ≤ D₂) :
    Real.exp (-κ * lowerBarrierXPlus κ κtilde D₂) ≤
      Real.exp (-κ * lowerBarrierXPlus κ κtilde D₁) := by
  apply Real.exp_le_exp.mpr
  have hx :=
    lowerBarrierXPlus_mono_D hκ hgap hD₁ hDle
  nlinarith [mul_nonneg hκ.le (sub_nonneg.mpr hx)]

theorem exists_D_gt_with_exp_xplus_le
    {κ κtilde M B : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hM : 0 < M) :
    ∃ D > B, Real.exp (-κ * lowerBarrierXPlus κ κtilde D) ≤ M := by
  have hκtilde : 0 < κtilde := by linarith
  let x₀ : ℝ := max 0 (-(Real.log M) / κ)
  let Dneed : ℝ := κ / κtilde * Real.exp ((κtilde - κ) * x₀)
  let D : ℝ := max (B + 1) Dneed
  have hDneed_pos : 0 < Dneed := by
    dsimp [Dneed]
    positivity
  have hB_D : B < D := by
    have h : B < B + 1 := by linarith
    exact lt_of_lt_of_le h (le_max_left _ _)
  have hDneed_le_D : Dneed ≤ D := le_max_right _ _
  have hx₀_bound : Real.exp (-κ * x₀) ≤ M := by
    have hx₀_ge : -(Real.log M) / κ ≤ x₀ := le_max_right _ _
    have hmul : -κ * x₀ ≤ Real.log M := by
      rw [neg_mul]
      have hmul' := mul_le_mul_of_nonneg_left hx₀_ge hκ.le
      rw [mul_div_cancel₀ _ (ne_of_gt hκ)] at hmul'
      linarith
    calc
      Real.exp (-κ * x₀) ≤ Real.exp (Real.log M) :=
        Real.exp_le_exp.mpr hmul
      _ = M := Real.exp_log hM
  refine ⟨D, hB_D, ?_⟩
  calc
    Real.exp (-κ * lowerBarrierXPlus κ κtilde D) ≤
        Real.exp (-κ * lowerBarrierXPlus κ κtilde Dneed) :=
      lowerBarrierExpXPlus_antitone_D hκ hgap hDneed_pos hDneed_le_D
    _ = Real.exp (-κ * x₀) := by
      rw [lowerBarrierXPlus_of_exp_choice hκ hgap]
    _ ≤ M := hx₀_bound

theorem lowerBarrierXMinus_lt_xplus
    {κ κtilde D : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D) :
    lowerBarrierXMinus κ κtilde D < lowerBarrierXPlus κ κtilde D := by
  have harg_pos : 0 < κtilde * D / κ := by
    have hκtilde_pos : 0 < κtilde := by linarith
    positivity
  have hD_lt_arg : D < κtilde * D / κ := by
    rw [lt_div_iff₀ hκ]
    nlinarith
  unfold lowerBarrierXMinus lowerBarrierXPlus
  rw [div_lt_div_iff_of_pos_right hgap]
  exact Real.log_lt_log hD hD_lt_arg

theorem lowerBarrierRaw_deriv_eq_zero_at_xplus
    {κ κtilde D : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D) :
    deriv (lowerBarrierRaw κ κtilde D) (lowerBarrierXPlus κ κtilde D) = 0 := by
  have hκtilde_pos : 0 < κtilde := by linarith
  have harg_pos : 0 < κtilde * D / κ := by positivity
  have hx :
      (κtilde - κ) * lowerBarrierXPlus κ κtilde D =
        Real.log (κtilde * D / κ) := by
    unfold lowerBarrierXPlus
    field_simp [ne_of_gt hgap]
  have hargexp :
      (κtilde * D / κ) *
        Real.exp (-(κtilde - κ) * lowerBarrierXPlus κ κtilde D) = 1 := by
    have hexp :
        Real.exp
          (Real.log (κtilde * D / κ) +
            (-(κtilde - κ) * lowerBarrierXPlus κ κtilde D)) =
          Real.exp 0 := by
      congr 1
      linarith
    simpa [Real.exp_add, Real.exp_log harg_pos] using hexp
  have hcrit :
      D * κtilde *
        Real.exp (-(κtilde - κ) * lowerBarrierXPlus κ κtilde D) = κ := by
    have hκ_ne : κ ≠ 0 := ne_of_gt hκ
    field_simp [hκ_ne] at hargexp
    convert hargexp using 1
    ring_nf
  rw [lowerBarrierRaw_deriv]
  have hexp :
      Real.exp (-κtilde * lowerBarrierXPlus κ κtilde D) =
        Real.exp (-κ * lowerBarrierXPlus κ κtilde D) *
          Real.exp (-(κtilde - κ) * lowerBarrierXPlus κ κtilde D) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  nlinarith [Real.exp_pos (-κ * lowerBarrierXPlus κ κtilde D)]

theorem lowerBarrierRaw_deriv_nonpos_of_xplus_le
    {κ κtilde D x : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D)
    (hx : lowerBarrierXPlus κ κtilde D ≤ x) :
    deriv (lowerBarrierRaw κ κtilde D) x ≤ 0 := by
  have hκtilde_pos : 0 < κtilde := by linarith
  have harg_pos : 0 < κtilde * D / κ := by positivity
  have hlog_le : Real.log (κtilde * D / κ) ≤ (κtilde - κ) * x := by
    rw [lowerBarrierXPlus] at hx
    simpa [mul_comm] using (div_le_iff₀ hgap).mp hx
  have hexp_le :
      Real.exp (Real.log (κtilde * D / κ) + (-(κtilde - κ) * x)) ≤
        Real.exp 0 :=
    Real.exp_le_exp.mpr (by linarith)
  have hcrit_le :
      D * κtilde * Real.exp (-(κtilde - κ) * x) ≤ κ := by
    have hle :
        (κtilde * D / κ) * Real.exp (-(κtilde - κ) * x) ≤ 1 := by
      simpa [Real.exp_add, Real.exp_log harg_pos] using hexp_le
    have hκ_nonneg : 0 ≤ κ := hκ.le
    have hmul := mul_le_mul_of_nonneg_right hle hκ_nonneg
    have hκ_ne : κ ≠ 0 := ne_of_gt hκ
    field_simp [hκ_ne] at hmul
    convert hmul using 1
    ring_nf
  rw [lowerBarrierRaw_deriv]
  have hexp :
      Real.exp (-κtilde * x) =
        Real.exp (-κ * x) * Real.exp (-(κtilde - κ) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  nlinarith [Real.exp_pos (-κ * x)]

theorem lowerBarrierRaw_antitoneOn_Ici_xplus
    {κ κtilde D : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D) :
    AntitoneOn (lowerBarrierRaw κ κtilde D)
      (Set.Ici (lowerBarrierXPlus κ κtilde D)) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici _)
    (lowerBarrierRaw_continuous κ κtilde D).continuousOn ?_ ?_
  · intro x _hx
    exact (lowerBarrierRaw_hasDerivAt κ κtilde D x).differentiableAt.differentiableWithinAt
  · intro x hx
    exact lowerBarrierRaw_deriv_nonpos_of_xplus_le hκ hgap hD
      (by
        have hx' : lowerBarrierXPlus κ κtilde D < x := by
          simpa using hx
        exact hx'.le)

theorem lowerBarrierRaw_deriv_nonneg_of_le_xplus
    {κ κtilde D x : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D)
    (hx : x ≤ lowerBarrierXPlus κ κtilde D) :
    0 ≤ deriv (lowerBarrierRaw κ κtilde D) x := by
  have hκtilde_pos : 0 < κtilde := by linarith
  have harg_pos : 0 < κtilde * D / κ := by positivity
  have hlog_ge : Real.log (κtilde * D / κ) ≥ (κtilde - κ) * x := by
    rw [lowerBarrierXPlus] at hx
    simpa [mul_comm] using (le_div_iff₀ hgap).mp hx
  have hexp_ge :
      Real.exp 0 ≤
        Real.exp (Real.log (κtilde * D / κ) + (-(κtilde - κ) * x)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hcrit_ge :
      κ ≤ D * κtilde * Real.exp (-(κtilde - κ) * x) := by
    have hle :
        1 ≤ (κtilde * D / κ) * Real.exp (-(κtilde - κ) * x) := by
      simpa [Real.exp_add, Real.exp_log harg_pos] using hexp_ge
    have hκ_nonneg : 0 ≤ κ := hκ.le
    have hmul := mul_le_mul_of_nonneg_right hle hκ_nonneg
    have hκ_ne : κ ≠ 0 := ne_of_gt hκ
    field_simp [hκ_ne] at hmul
    convert hmul using 1
    ring_nf
  rw [lowerBarrierRaw_deriv]
  have hexp :
      Real.exp (-κtilde * x) =
        Real.exp (-κ * x) * Real.exp (-(κtilde - κ) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  nlinarith [Real.exp_pos (-κ * x)]

theorem lowerBarrierRaw_pos_at_xplus
    {κ κtilde D : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D) :
    0 < lowerBarrierRaw κ κtilde D (lowerBarrierXPlus κ κtilde D) :=
  lowerBarrierRaw_pos_of_xminus_lt hgap hD
    (lowerBarrierXMinus_lt_xplus hκ hgap hD)

def lowerBarrierPlateau (κ κtilde D : ℝ) : ℝ → ℝ :=
  fun x =>
    if x ≤ lowerBarrierXPlus κ κtilde D then
      lowerBarrierRaw κ κtilde D (lowerBarrierXPlus κ κtilde D)
    else
      lowerBarrierRaw κ κtilde D x

theorem lowerBarrierPlateau_eq_const_of_le
    {κ κtilde D x : ℝ} (hx : x ≤ lowerBarrierXPlus κ κtilde D) :
    lowerBarrierPlateau κ κtilde D x =
      lowerBarrierRaw κ κtilde D (lowerBarrierXPlus κ κtilde D) := by
  simp [lowerBarrierPlateau, hx]

theorem lowerBarrierPlateau_eq_raw_of_xplus_lt
    {κ κtilde D x : ℝ} (hx : lowerBarrierXPlus κ κtilde D < x) :
    lowerBarrierPlateau κ κtilde D x = lowerBarrierRaw κ κtilde D x := by
  simp [lowerBarrierPlateau, not_le.mpr hx]

theorem lowerBarrierPlateau_continuous (κ κtilde D : ℝ) :
    Continuous (lowerBarrierPlateau κ κtilde D) := by
  unfold lowerBarrierPlateau
  exact continuous_if_le continuous_id continuous_const
    continuous_const.continuousOn
    (lowerBarrierRaw_continuous κ κtilde D).continuousOn
    (fun x hx => by rw [hx])

theorem lowerBarrierPlateau_pos
    {κ κtilde D : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D)
    (x : ℝ) :
    0 < lowerBarrierPlateau κ κtilde D x := by
  by_cases hx : x ≤ lowerBarrierXPlus κ κtilde D
  · rw [lowerBarrierPlateau_eq_const_of_le hx]
    exact lowerBarrierRaw_pos_at_xplus hκ hgap hD
  · have hxlt : lowerBarrierXPlus κ κtilde D < x := lt_of_not_ge hx
    rw [lowerBarrierPlateau_eq_raw_of_xplus_lt hxlt]
    exact lowerBarrierRaw_pos_of_xminus_lt hgap hD
      (lt_trans (lowerBarrierXMinus_lt_xplus hκ hgap hD) hxlt)

theorem lowerBarrierPlateau_le_exp
    {κ κtilde D : ℝ} (hκ : 0 ≤ κ) (hD : 0 ≤ D) (x : ℝ) :
    lowerBarrierPlateau κ κtilde D x ≤ Real.exp (-κ * x) := by
  by_cases hx : x ≤ lowerBarrierXPlus κ κtilde D
  · rw [lowerBarrierPlateau_eq_const_of_le hx]
    have hraw_le :
        lowerBarrierRaw κ κtilde D (lowerBarrierXPlus κ κtilde D) ≤
          Real.exp (-κ * lowerBarrierXPlus κ κtilde D) :=
      lowerBarrierRaw_le_exp hD
    have hexp_le :
        Real.exp (-κ * lowerBarrierXPlus κ κtilde D) ≤ Real.exp (-κ * x) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hκ (sub_nonneg.mpr hx)]
    exact le_trans hraw_le hexp_le
  · have hxlt : lowerBarrierXPlus κ κtilde D < x := lt_of_not_ge hx
    rw [lowerBarrierPlateau_eq_raw_of_xplus_lt hxlt]
    exact lowerBarrierRaw_le_exp hD

theorem lowerBarrierPlateau_le_exp_xplus
    {κ κtilde D : ℝ} (hκ : 0 ≤ κ) (hD : 0 ≤ D) (x : ℝ) :
    lowerBarrierPlateau κ κtilde D x ≤
      Real.exp (-κ * lowerBarrierXPlus κ κtilde D) := by
  by_cases hx : x ≤ lowerBarrierXPlus κ κtilde D
  · rw [lowerBarrierPlateau_eq_const_of_le hx]
    exact lowerBarrierRaw_le_exp hD
  · have hxlt : lowerBarrierXPlus κ κtilde D < x := lt_of_not_ge hx
    calc
      lowerBarrierPlateau κ κtilde D x ≤ Real.exp (-κ * x) :=
        lowerBarrierPlateau_le_exp hκ hD x
      _ ≤ Real.exp (-κ * lowerBarrierXPlus κ κtilde D) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg hκ (sub_nonneg.mpr hxlt.le)]

theorem lowerBarrierPlateau_rpow_le_exp
    {κ κtilde D a : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hD : 0 < D) (ha : 0 ≤ a) (x : ℝ) :
    (lowerBarrierPlateau κ κtilde D x) ^ a ≤
      (Real.exp (-κ * x)) ^ a :=
  Real.rpow_le_rpow
    (lowerBarrierPlateau_pos hκ hgap hD x).le
    (lowerBarrierPlateau_le_exp hκ.le hD.le x) ha

theorem lowerBarrierPlateau_rpow_le_exp_mul
    {κ κtilde D a : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hD : 0 < D) (ha : 0 ≤ a) (x : ℝ) :
    (lowerBarrierPlateau κ κtilde D x) ^ a ≤ Real.exp (-κ * a * x) := by
  calc
    (lowerBarrierPlateau κ κtilde D x) ^ a ≤
        (Real.exp (-κ * x)) ^ a :=
      lowerBarrierPlateau_rpow_le_exp hκ hgap hD ha x
    _ = Real.exp (-κ * a * x) := by
      rw [← Real.exp_mul]
      congr 1
      ring

theorem lowerBarrierPlateau_rpow_le_exp_xplus
    {κ κtilde D a : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hD : 0 < D) (ha : 0 ≤ a) (x : ℝ) :
    (lowerBarrierPlateau κ κtilde D x) ^ a ≤
      (Real.exp (-κ * lowerBarrierXPlus κ κtilde D)) ^ a :=
  Real.rpow_le_rpow
    (lowerBarrierPlateau_pos hκ hgap hD x).le
    (lowerBarrierPlateau_le_exp_xplus hκ.le hD.le x) ha

theorem lowerBarrierPlateau_rpow_le_exp_xplus_mul
    {κ κtilde D a : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hD : 0 < D) (ha : 0 ≤ a) (x : ℝ) :
    (lowerBarrierPlateau κ κtilde D x) ^ a ≤
      Real.exp (-κ * a * lowerBarrierXPlus κ κtilde D) := by
  calc
    (lowerBarrierPlateau κ κtilde D x) ^ a ≤
        (Real.exp (-κ * lowerBarrierXPlus κ κtilde D)) ^ a :=
      lowerBarrierPlateau_rpow_le_exp_xplus hκ hgap hD ha x
    _ = Real.exp (-κ * a * lowerBarrierXPlus κ κtilde D) := by
      rw [← Real.exp_mul]
      congr 1
      ring

theorem lowerBarrierPlateau_isBddFun
    {κ κtilde D : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D) :
    IsBddFun (lowerBarrierPlateau κ κtilde D) := by
  refine ⟨Real.exp (-κ * lowerBarrierXPlus κ κtilde D), ?_⟩
  intro x
  rw [abs_of_nonneg (lowerBarrierPlateau_pos hκ hgap hD x).le]
  exact lowerBarrierPlateau_le_exp_xplus hκ.le hD.le x

theorem lowerBarrierPlateau_cunif_bdd
    {κ κtilde D : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D) :
    IsCUnifBdd (lowerBarrierPlateau κ κtilde D) :=
  ⟨lowerBarrierPlateau_continuous κ κtilde D,
    lowerBarrierPlateau_isBddFun hκ hgap hD⟩

theorem lowerBarrierPlateau_antitone
    {κ κtilde D : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D) :
    Antitone (lowerBarrierPlateau κ κtilde D) := by
  intro x y hxy
  by_cases hy : y ≤ lowerBarrierXPlus κ κtilde D
  · have hx : x ≤ lowerBarrierXPlus κ κtilde D := le_trans hxy hy
    rw [lowerBarrierPlateau_eq_const_of_le hx,
      lowerBarrierPlateau_eq_const_of_le hy]
  · have hylt : lowerBarrierXPlus κ κtilde D < y := lt_of_not_ge hy
    by_cases hx : x ≤ lowerBarrierXPlus κ κtilde D
    · rw [lowerBarrierPlateau_eq_const_of_le hx,
        lowerBarrierPlateau_eq_raw_of_xplus_lt hylt]
      exact lowerBarrierRaw_antitoneOn_Ici_xplus hκ hgap hD
        (le_rfl : lowerBarrierXPlus κ κtilde D ≤ lowerBarrierXPlus κ κtilde D)
        hylt.le hylt.le
    · have hxlt : lowerBarrierXPlus κ κtilde D < x := lt_of_not_ge hx
      rw [lowerBarrierPlateau_eq_raw_of_xplus_lt hxlt,
        lowerBarrierPlateau_eq_raw_of_xplus_lt hylt]
      exact lowerBarrierRaw_antitoneOn_Ici_xplus hκ hgap hD
        hxlt.le hylt.le hxy

def InWaveTrapSet (κ M : ℝ) (u : ℝ → ℝ) : Prop :=
  IsCUnifBdd u ∧ ∀ x, 0 ≤ u x ∧ u x ≤ upperBarrier κ M x

def NonincreasingProfile (u : ℝ → ℝ) : Prop :=
  Antitone u

def InMonotoneWaveTrapSet (κ M : ℝ) (u : ℝ → ℝ) : Prop :=
  InWaveTrapSet κ M u ∧ NonincreasingProfile u

def WaveTrapSet (κ M : ℝ) : Set (ℝ → ℝ) :=
  {u | InWaveTrapSet κ M u}

def MonotoneWaveTrapSet (κ M : ℝ) : Set (ℝ → ℝ) :=
  {u | InMonotoneWaveTrapSet κ M u}

theorem IsBddFun.convex_combo
    {u v : ℝ → ℝ} {θ : ℝ}
    (_hθ0 : 0 ≤ θ) (_hθ1 : θ ≤ 1)
    (hu : IsBddFun u) (hv : IsBddFun v) :
    IsBddFun (fun x => θ * u x + (1 - θ) * v x) := by
  rcases hu with ⟨Mu, hu⟩
  rcases hv with ⟨Mv, hv⟩
  refine ⟨|θ| * Mu + |1 - θ| * Mv, ?_⟩
  intro x
  calc
    |θ * u x + (1 - θ) * v x| ≤
        |θ * u x| + |(1 - θ) * v x| := abs_add_le _ _
    _ = |θ| * |u x| + |1 - θ| * |v x| := by rw [abs_mul, abs_mul]
    _ ≤ |θ| * Mu + |1 - θ| * Mv := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hu x) (abs_nonneg θ))
        (mul_le_mul_of_nonneg_left (hv x) (abs_nonneg (1 - θ)))

theorem IsCUnifBdd.convex_combo
    {u v : ℝ → ℝ} {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hu : IsCUnifBdd u) (hv : IsCUnifBdd v) :
    IsCUnifBdd (fun x => θ * u x + (1 - θ) * v x) := by
  constructor
  · exact (continuous_const.mul hu.1).add (continuous_const.mul hv.1)
  · exact IsBddFun.convex_combo hθ0 hθ1 hu.2 hv.2

theorem IsBddFun.zero :
    IsBddFun (fun _ : ℝ => (0 : ℝ)) := by
  exact ⟨0, by simp⟩

theorem IsCUnifBdd.zero :
    IsCUnifBdd (fun _ : ℝ => (0 : ℝ)) := by
  exact ⟨continuous_const, IsBddFun.zero⟩

theorem InWaveTrapSet.cunif_bdd {κ M : ℝ} {u : ℝ → ℝ}
    (h : InWaveTrapSet κ M u) :
    IsCUnifBdd u :=
  h.1

theorem InWaveTrapSet.nonneg {κ M : ℝ} {u : ℝ → ℝ}
    (h : InWaveTrapSet κ M u) (x : ℝ) :
    0 ≤ u x :=
  (h.2 x).1

theorem InWaveTrapSet.le_upperBarrier {κ M : ℝ} {u : ℝ → ℝ}
    (h : InWaveTrapSet κ M u) (x : ℝ) :
    u x ≤ upperBarrier κ M x :=
  (h.2 x).2

theorem InWaveTrapSet.le_M {κ M : ℝ} {u : ℝ → ℝ}
    (h : InWaveTrapSet κ M u) (x : ℝ) :
    u x ≤ M :=
  le_trans (h.le_upperBarrier x) (min_le_left _ _)

theorem InWaveTrapSet.le_exp {κ M : ℝ} {u : ℝ → ℝ}
    (h : InWaveTrapSet κ M u) (x : ℝ) :
    u x ≤ Real.exp (-κ * x) :=
  le_trans (h.le_upperBarrier x) (min_le_right _ _)

theorem InWaveTrapSet.le_one_of_M_le_one {κ M : ℝ} {u : ℝ → ℝ}
    (h : InWaveTrapSet κ M u) (hM : M ≤ 1) (x : ℝ) :
    u x ≤ 1 :=
  le_trans (h.le_M x) hM

theorem InWaveTrapSet.rpow_le_M
    {κ M : ℝ} {u : ℝ → ℝ} {a : ℝ}
    (h : InWaveTrapSet κ M u) (ha : 0 ≤ a) (x : ℝ) :
    (u x) ^ a ≤ M ^ a :=
  Real.rpow_le_rpow (h.nonneg x) (h.le_M x) ha

theorem InWaveTrapSet.rpow_le_exp
    {κ M : ℝ} {u : ℝ → ℝ} {a : ℝ}
    (h : InWaveTrapSet κ M u) (ha : 0 ≤ a) (x : ℝ) :
    (u x) ^ a ≤ (Real.exp (-κ * x)) ^ a :=
  Real.rpow_le_rpow (h.nonneg x) (h.le_exp x) ha

theorem InWaveTrapSet.rpow_le_exp_mul
    {κ M : ℝ} {u : ℝ → ℝ} {a : ℝ}
    (h : InWaveTrapSet κ M u) (ha : 0 ≤ a) (x : ℝ) :
    (u x) ^ a ≤ Real.exp (-κ * a * x) := by
  calc
    (u x) ^ a ≤ (Real.exp (-κ * x)) ^ a := h.rpow_le_exp ha x
    _ = Real.exp (-κ * a * x) := by
      rw [← Real.exp_mul]
      congr 1
      ring

theorem InWaveTrapSet.zero {κ M : ℝ} (hM : 0 ≤ M) :
    InWaveTrapSet κ M (fun _ : ℝ => (0 : ℝ)) := by
  refine ⟨IsCUnifBdd.zero, ?_⟩
  intro x
  exact ⟨le_rfl, upperBarrier_nonneg hM x⟩

theorem upperBarrier_mem_InWaveTrapSet {κ M : ℝ} (hM : 0 ≤ M) :
    InWaveTrapSet κ M (upperBarrier κ M) := by
  refine ⟨upperBarrier_cunif_bdd hM, ?_⟩
  intro x
  exact ⟨upperBarrier_nonneg hM x, le_rfl⟩

theorem lowerBarrierPlateau_mem_InWaveTrapSet_exp_xplus
    {κ κtilde D : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D) :
    InWaveTrapSet κ
      (Real.exp (-κ * lowerBarrierXPlus κ κtilde D))
      (lowerBarrierPlateau κ κtilde D) := by
  refine ⟨lowerBarrierPlateau_cunif_bdd hκ hgap hD, ?_⟩
  intro x
  refine ⟨(lowerBarrierPlateau_pos hκ hgap hD x).le, ?_⟩
  exact le_min
    (lowerBarrierPlateau_le_exp_xplus hκ.le hD.le x)
    (lowerBarrierPlateau_le_exp hκ.le hD.le x)

theorem InWaveTrapSet.convex_combo
    {κ M : ℝ} {u v : ℝ → ℝ} {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hu : InWaveTrapSet κ M u) (hv : InWaveTrapSet κ M v) :
    InWaveTrapSet κ M (fun x => θ * u x + (1 - θ) * v x) := by
  refine ⟨IsCUnifBdd.convex_combo hθ0 hθ1 hu.cunif_bdd hv.cunif_bdd, ?_⟩
  intro x
  constructor
  · exact add_nonneg
      (mul_nonneg hθ0 (hu.nonneg x))
      (mul_nonneg (sub_nonneg.mpr hθ1) (hv.nonneg x))
  · calc
      θ * u x + (1 - θ) * v x ≤
          θ * upperBarrier κ M x + (1 - θ) * upperBarrier κ M x :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hu.le_upperBarrier x) hθ0)
          (mul_le_mul_of_nonneg_left (hv.le_upperBarrier x) (sub_nonneg.mpr hθ1))
      _ = upperBarrier κ M x := by ring

theorem InWaveTrapSet.mono_M
    {κ M₁ M₂ : ℝ} {u : ℝ → ℝ}
    (hM : M₁ ≤ M₂) (h : InWaveTrapSet κ M₁ u) :
    InWaveTrapSet κ M₂ u := by
  refine ⟨h.cunif_bdd, ?_⟩
  intro x
  exact
    ⟨h.nonneg x,
      le_trans (h.le_upperBarrier x) (upperBarrier_mono_M hM x)⟩

theorem lowerBarrierPlateau_mem_InWaveTrapSet_of_exp_xplus_le
    {κ κtilde D M : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hD : 0 < D)
    (hM : Real.exp (-κ * lowerBarrierXPlus κ κtilde D) ≤ M) :
    InWaveTrapSet κ M (lowerBarrierPlateau κ κtilde D) :=
  InWaveTrapSet.mono_M hM
    (lowerBarrierPlateau_mem_InWaveTrapSet_exp_xplus hκ hgap hD)

theorem lowerBarrierPlateau_mem_InMonotoneWaveTrapSet_exp_xplus
    {κ κtilde D : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D) :
    InMonotoneWaveTrapSet κ
      (Real.exp (-κ * lowerBarrierXPlus κ κtilde D))
      (lowerBarrierPlateau κ κtilde D) :=
  ⟨lowerBarrierPlateau_mem_InWaveTrapSet_exp_xplus hκ hgap hD,
    lowerBarrierPlateau_antitone hκ hgap hD⟩

theorem lowerBarrierPlateau_mem_InMonotoneWaveTrapSet_of_exp_xplus_le
    {κ κtilde D M : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hD : 0 < D)
    (hM : Real.exp (-κ * lowerBarrierXPlus κ κtilde D) ≤ M) :
    InMonotoneWaveTrapSet κ M (lowerBarrierPlateau κ κtilde D) :=
  ⟨lowerBarrierPlateau_mem_InWaveTrapSet_of_exp_xplus_le hκ hgap hD hM,
    lowerBarrierPlateau_antitone hκ hgap hD⟩

theorem exists_D_gt_lowerBarrierPlateau_mem_InWaveTrapSet
    {κ κtilde M B : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hM : 0 < M) (hB : 0 ≤ B) :
    ∃ D > B, InWaveTrapSet κ M (lowerBarrierPlateau κ κtilde D) := by
  rcases exists_D_gt_with_exp_xplus_le (κ := κ) (κtilde := κtilde)
      (M := M) (B := B) hκ hgap hM with
    ⟨D, hBD, hheight⟩
  have hD : 0 < D := lt_of_le_of_lt hB hBD
  exact
    ⟨D, hBD,
      lowerBarrierPlateau_mem_InWaveTrapSet_of_exp_xplus_le
        hκ hgap hD hheight⟩

theorem exists_D_gt_lowerBarrierPlateau_mem_InMonotoneWaveTrapSet
    {κ κtilde M B : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hM : 0 < M) (hB : 0 ≤ B) :
    ∃ D > B, InMonotoneWaveTrapSet κ M (lowerBarrierPlateau κ κtilde D) := by
  rcases exists_D_gt_with_exp_xplus_le (κ := κ) (κtilde := κtilde)
      (M := M) (B := B) hκ hgap hM with
    ⟨D, hBD, hheight⟩
  have hD : 0 < D := lt_of_le_of_lt hB hBD
  exact
    ⟨D, hBD,
      lowerBarrierPlateau_mem_InMonotoneWaveTrapSet_of_exp_xplus_le
        hκ hgap hD hheight⟩

theorem WaveTrapSet_subset_of_M_le
    {κ M₁ M₂ : ℝ} (hM : M₁ ≤ M₂) :
    WaveTrapSet κ M₁ ⊆ WaveTrapSet κ M₂ := by
  intro u hu
  exact InWaveTrapSet.mono_M hM hu

theorem InWaveTrapSet.set_nonempty {κ M : ℝ} (hM : 0 ≤ M) :
    ({u : ℝ → ℝ | InWaveTrapSet κ M u}).Nonempty :=
  ⟨fun _ => 0, InWaveTrapSet.zero hM⟩

theorem WaveTrapSet_nonempty {κ M : ℝ} (hM : 0 ≤ M) :
    (WaveTrapSet κ M).Nonempty :=
  InWaveTrapSet.set_nonempty hM

theorem InWaveTrapSet.set_convex (κ M : ℝ) :
    Convex ℝ {u : ℝ → ℝ | InWaveTrapSet κ M u} := by
  rw [convex_iff_add_mem]
  intro u hu v hv a b ha hb hab
  have ha_le_one : a ≤ 1 := by nlinarith
  have hb_eq : b = 1 - a := by linarith
  convert InWaveTrapSet.convex_combo ha ha_le_one hu hv using 1
  ext x
  simp [hb_eq, smul_eq_mul]

theorem WaveTrapSet_convex (κ M : ℝ) :
    Convex ℝ (WaveTrapSet κ M) :=
  InWaveTrapSet.set_convex κ M

theorem InMonotoneWaveTrapSet.trap
    {κ M : ℝ} {u : ℝ → ℝ}
    (h : InMonotoneWaveTrapSet κ M u) :
    InWaveTrapSet κ M u :=
  h.1

theorem InMonotoneWaveTrapSet.antitone
    {κ M : ℝ} {u : ℝ → ℝ}
    (h : InMonotoneWaveTrapSet κ M u) :
    Antitone u :=
  h.2

theorem InMonotoneWaveTrapSet.deriv_nonpos
    {κ M : ℝ} {u : ℝ → ℝ}
    (h : InMonotoneWaveTrapSet κ M u) (x : ℝ) :
    deriv u x ≤ 0 :=
  h.antitone.deriv_nonpos

theorem InMonotoneWaveTrapSet.nonneg
    {κ M : ℝ} {u : ℝ → ℝ}
    (h : InMonotoneWaveTrapSet κ M u) (x : ℝ) :
    0 ≤ u x :=
  h.trap.nonneg x

theorem InMonotoneWaveTrapSet.le_upperBarrier
    {κ M : ℝ} {u : ℝ → ℝ}
    (h : InMonotoneWaveTrapSet κ M u) (x : ℝ) :
    u x ≤ upperBarrier κ M x :=
  h.trap.le_upperBarrier x

theorem InMonotoneWaveTrapSet.le_M
    {κ M : ℝ} {u : ℝ → ℝ}
    (h : InMonotoneWaveTrapSet κ M u) (x : ℝ) :
    u x ≤ M :=
  h.trap.le_M x

theorem InMonotoneWaveTrapSet.le_exp
    {κ M : ℝ} {u : ℝ → ℝ}
    (h : InMonotoneWaveTrapSet κ M u) (x : ℝ) :
    u x ≤ Real.exp (-κ * x) :=
  h.trap.le_exp x

theorem InMonotoneWaveTrapSet.le_one_of_M_le_one
    {κ M : ℝ} {u : ℝ → ℝ}
    (h : InMonotoneWaveTrapSet κ M u) (hM : M ≤ 1) (x : ℝ) :
    u x ≤ 1 :=
  h.trap.le_one_of_M_le_one hM x

theorem InMonotoneWaveTrapSet.rpow_le_M
    {κ M : ℝ} {u : ℝ → ℝ} {a : ℝ}
    (h : InMonotoneWaveTrapSet κ M u) (ha : 0 ≤ a) (x : ℝ) :
    (u x) ^ a ≤ M ^ a :=
  h.trap.rpow_le_M ha x

theorem InMonotoneWaveTrapSet.rpow_le_exp
    {κ M : ℝ} {u : ℝ → ℝ} {a : ℝ}
    (h : InMonotoneWaveTrapSet κ M u) (ha : 0 ≤ a) (x : ℝ) :
    (u x) ^ a ≤ (Real.exp (-κ * x)) ^ a :=
  h.trap.rpow_le_exp ha x

theorem InMonotoneWaveTrapSet.rpow_le_exp_mul
    {κ M : ℝ} {u : ℝ → ℝ} {a : ℝ}
    (h : InMonotoneWaveTrapSet κ M u) (ha : 0 ≤ a) (x : ℝ) :
    (u x) ^ a ≤ Real.exp (-κ * a * x) :=
  h.trap.rpow_le_exp_mul ha x

theorem InMonotoneWaveTrapSet.zero {κ M : ℝ} (hM : 0 ≤ M) :
    InMonotoneWaveTrapSet κ M (fun _ : ℝ => (0 : ℝ)) := by
  exact ⟨InWaveTrapSet.zero hM, antitone_const⟩

theorem upperBarrier_mem_InMonotoneWaveTrapSet
    {κ M : ℝ} (hκ : 0 ≤ κ) (hM : 0 ≤ M) :
    InMonotoneWaveTrapSet κ M (upperBarrier κ M) := by
  exact ⟨upperBarrier_mem_InWaveTrapSet hM, upperBarrier_antitone hκ⟩

theorem InMonotoneWaveTrapSet.convex_combo
    {κ M : ℝ} {u v : ℝ → ℝ} {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hu : InMonotoneWaveTrapSet κ M u)
    (hv : InMonotoneWaveTrapSet κ M v) :
    InMonotoneWaveTrapSet κ M
      (fun x => θ * u x + (1 - θ) * v x) := by
  refine
    ⟨InWaveTrapSet.convex_combo hθ0 hθ1 hu.trap hv.trap, ?_⟩
  intro x y hxy
  exact add_le_add
    (mul_le_mul_of_nonneg_left (hu.antitone hxy) hθ0)
    (mul_le_mul_of_nonneg_left (hv.antitone hxy) (sub_nonneg.mpr hθ1))

theorem InMonotoneWaveTrapSet.mono_M
    {κ M₁ M₂ : ℝ} {u : ℝ → ℝ}
    (hM : M₁ ≤ M₂) (h : InMonotoneWaveTrapSet κ M₁ u) :
    InMonotoneWaveTrapSet κ M₂ u :=
  ⟨InWaveTrapSet.mono_M hM h.trap, h.antitone⟩

theorem MonotoneWaveTrapSet_subset_of_M_le
    {κ M₁ M₂ : ℝ} (hM : M₁ ≤ M₂) :
    MonotoneWaveTrapSet κ M₁ ⊆ MonotoneWaveTrapSet κ M₂ := by
  intro u hu
  exact InMonotoneWaveTrapSet.mono_M hM hu

theorem InMonotoneWaveTrapSet.set_nonempty {κ M : ℝ} (hM : 0 ≤ M) :
    ({u : ℝ → ℝ | InMonotoneWaveTrapSet κ M u}).Nonempty :=
  ⟨fun _ => 0, InMonotoneWaveTrapSet.zero hM⟩

theorem MonotoneWaveTrapSet_nonempty {κ M : ℝ} (hM : 0 ≤ M) :
    (MonotoneWaveTrapSet κ M).Nonempty :=
  InMonotoneWaveTrapSet.set_nonempty hM

theorem InMonotoneWaveTrapSet.set_convex (κ M : ℝ) :
    Convex ℝ {u : ℝ → ℝ | InMonotoneWaveTrapSet κ M u} := by
  rw [convex_iff_add_mem]
  intro u hu v hv a b ha hb hab
  have ha_le_one : a ≤ 1 := by nlinarith
  have hb_eq : b = 1 - a := by linarith
  convert InMonotoneWaveTrapSet.convex_combo ha ha_le_one hu hv using 1
  ext x
  simp [hb_eq, smul_eq_mul]

theorem MonotoneWaveTrapSet_convex (κ M : ℝ) :
    Convex ℝ (MonotoneWaveTrapSet κ M) :=
  InMonotoneWaveTrapSet.set_convex κ M

/-- Local-uniform convergence on compact intervals of the line.  This is the
topology used in the Schauder step of the traveling-wave construction. -/
def LocallyUniformConverges
    (fs : ℕ → ℝ → ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ R > 0, ∀ ε > 0,
    ∀ᶠ n in atTop, ∀ x : ℝ, x ∈ Set.Icc (-R) R → |fs n x - f x| < ε

theorem LocallyUniformConverges.tendsto_at
    {fs : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (h : LocallyUniformConverges fs f) (x : ℝ) :
    Tendsto (fun n : ℕ => fs n x) atTop (𝓝 (f x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let R : ℝ := |x| + 1
  have hR : 0 < R := by
    dsimp [R]
    nlinarith [abs_nonneg x]
  have hxR : x ∈ Set.Icc (-R) R := by
    have hxabs : |x| ≤ R := by
      dsimp [R]
      nlinarith [abs_nonneg x]
    exact abs_le.mp hxabs
  rcases (eventually_atTop.1 (h R hR ε hε)) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  simpa [Real.dist_eq] using hN n hn x hxR

theorem LocallyUniformConverges.unique
    {fs : ℕ → ℝ → ℝ} {f g : ℝ → ℝ}
    (hf : LocallyUniformConverges fs f)
    (hg : LocallyUniformConverges fs g) :
    f = g := by
  funext x
  exact tendsto_nhds_unique (hf.tendsto_at x) (hg.tendsto_at x)

theorem LocallyUniformConverges.comp_strictMono
    {fs : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {subseq : ℕ → ℕ}
    (h : LocallyUniformConverges fs f) (hsubseq : StrictMono subseq) :
    LocallyUniformConverges (fun n => fs (subseq n)) f := by
  intro R hR ε hε
  exact hsubseq.tendsto_atTop.eventually (h R hR ε hε)

theorem LocallyUniformConverges.congr
    {fs gs : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hfg : ∀ᶠ n in atTop, fs n = gs n)
    (h : LocallyUniformConverges fs f) :
    LocallyUniformConverges gs f := by
  intro R hR ε hε
  filter_upwards [hfg, h R hR ε hε] with n hn hconv
  simpa [← hn] using hconv

/-- Sequential continuity of a wave map in the local-uniform topology, restricted
to a trapping set. -/
def LocalUniformContinuousOn
    (trap : (ℝ → ℝ) → Prop) (Tmap : (ℝ → ℝ) → ℝ → ℝ) : Prop :=
  ∀ (seq : ℕ → ℝ → ℝ) (u : ℝ → ℝ),
    (∀ n, trap (seq n)) →
      trap u →
        LocallyUniformConverges seq u →
          LocallyUniformConverges (fun n => Tmap (seq n)) (Tmap u)

theorem LocalUniformContinuousOn.fixed_of_approx_fixed
    {trap : (ℝ → ℝ) → Prop} {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hcont : LocalUniformContinuousOn trap Tmap)
    {seq : ℕ → ℝ → ℝ} {u : ℝ → ℝ}
    (hseq : ∀ n, trap (seq n)) (hu : trap u)
    (hconv : LocallyUniformConverges seq u)
    (hfix : ∀ n, Tmap (seq n) = seq n) :
    Tmap u = u := by
  have himage : LocallyUniformConverges (fun n => Tmap (seq n)) (Tmap u) :=
    hcont seq u hseq hu hconv
  have hsame : LocallyUniformConverges (fun n => Tmap (seq n)) u := by
    intro R hR ε hε
    filter_upwards [hconv R hR ε hε] with n hn
    simpa [hfix n] using hn
  exact himage.unique hsame

theorem LocalUniformContinuousOn.fixed_of_subseq_fixed_limit
    {trap : (ℝ → ℝ) → Prop} {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hcont : LocalUniformContinuousOn trap Tmap)
    {seq : ℕ → ℝ → ℝ} {u : ℝ → ℝ} {subseq : ℕ → ℕ}
    (_hsubseq : StrictMono subseq)
    (hseq : ∀ n, trap (seq n)) (hu : trap u)
    (hconv : LocallyUniformConverges (fun n => seq (subseq n)) u)
    (hfix : ∀ n, Tmap (seq n) = seq n) :
    Tmap u = u := by
  exact hcont.fixed_of_approx_fixed
    (seq := fun n => seq (subseq n)) (u := u)
    (fun n => hseq (subseq n)) hu hconv
    (fun n => hfix (subseq n))

theorem LocalUniformContinuousOn.comp_strictMono
    {trap : (ℝ → ℝ) → Prop} {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hcont : LocalUniformContinuousOn trap Tmap)
    {seq : ℕ → ℝ → ℝ} {u : ℝ → ℝ} {subseq : ℕ → ℕ}
    (_hsubseq : StrictMono subseq)
    (hseq : ∀ n, trap (seq n)) (hu : trap u)
    (hconv : LocallyUniformConverges (fun n => seq (subseq n)) u) :
    LocallyUniformConverges
      (fun n => Tmap (seq (subseq n))) (Tmap u) :=
  hcont (fun n => seq (subseq n)) u (fun n => hseq (subseq n)) hu hconv

/-- Sequential compactness of the range of a wave map in the local-uniform
topology, restricted to a trapping set. -/
def LocalUniformSequentiallyCompactRange
    (trap : (ℝ → ℝ) → Prop) (Tmap : (ℝ → ℝ) → ℝ → ℝ) : Prop :=
  ∀ seq : ℕ → ℝ → ℝ,
    (∀ n, trap (seq n)) →
      ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
        ∃ U : ℝ → ℝ,
          trap U ∧
            LocallyUniformConverges (fun n => Tmap (seq (subseq n))) U

theorem LocalUniformSequentiallyCompactRange.exists_fixed_subseq_limit
    {trap : (ℝ → ℝ) → Prop} {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hcompact : LocalUniformSequentiallyCompactRange trap Tmap)
    (hcont : LocalUniformContinuousOn trap Tmap)
    {seq : ℕ → ℝ → ℝ}
    (hseq : ∀ n, trap (seq n))
    (hfix : ∀ n, Tmap (seq n) = seq n) :
    ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
      ∃ U : ℝ → ℝ,
        trap U ∧
          LocallyUniformConverges (fun n => seq (subseq n)) U ∧
          Tmap U = U := by
  rcases hcompact seq hseq with ⟨subseq, hsubseq, U, hU, hconv_image⟩
  have hconv_seq :
      LocallyUniformConverges (fun n => seq (subseq n)) U := by
    intro R hR ε hε
    filter_upwards [hconv_image R hR ε hε] with n hn
    simpa [hfix (subseq n)] using hn
  exact
    ⟨subseq, hsubseq, U, hU, hconv_seq,
      hcont.fixed_of_subseq_fixed_limit hsubseq hseq hU hconv_seq hfix⟩

/-- The frozen auxiliary parabolic equation used in Section 4.2/4.3.
The frozen profile supplies the elliptic response; the orbit starts from the
upper barrier. -/
def FrozenAuxiliarySolutionFrom
    (p : CMParams) (c : ℝ) (frozen initial : ℝ → ℝ)
    (z : ℝ → ℝ → ℝ) : Prop :=
  (∀ x, z 0 x = initial x) ∧
    ∀ t x, 0 < t →
      deriv (fun τ : ℝ => z τ x) t =
        frozenWaveOperator p c frozen (z t) x

theorem FrozenAuxiliarySolutionFrom.initial_eq
    {p : CMParams} {c : ℝ} {frozen initial : ℝ → ℝ}
    {z : ℝ → ℝ → ℝ}
    (h : FrozenAuxiliarySolutionFrom p c frozen initial z) (x : ℝ) :
    z 0 x = initial x :=
  h.1 x

theorem FrozenAuxiliarySolutionFrom.evolution_eq
    {p : CMParams} {c : ℝ} {frozen initial : ℝ → ℝ}
    {z : ℝ → ℝ → ℝ}
    (h : FrozenAuxiliarySolutionFrom p c frozen initial z)
    {t x : ℝ} (ht : 0 < t) :
    deriv (fun τ : ℝ => z τ x) t =
      frozenWaveOperator p c frozen (z t) x :=
  h.2 t x ht

/-- Output of the auxiliary parabolic construction: the orbit stays in the
chosen trapping set, is monotone in time pointwise, and converges locally
pointwise to the profile `U`. -/
def FrozenAuxiliaryLimitOutput
    (p : CMParams) (c κ M : ℝ) (trap : (ℝ → ℝ) → Prop)
    (frozen U : ℝ → ℝ) : Prop :=
  ∃ z : ℝ → ℝ → ℝ,
    FrozenAuxiliarySolutionFrom p c frozen (upperBarrier κ M) z ∧
      (∀ t, 0 ≤ t → trap (z t)) ∧
      (∀ x, Antitone (fun t => z t x)) ∧
      ∀ x, Tendsto (fun t : ℝ => z t x) atTop (𝓝 (U x))

theorem FrozenAuxiliaryLimitOutput.exists_orbit
    {p : CMParams} {c κ M : ℝ} {trap : (ℝ → ℝ) → Prop}
    {frozen U : ℝ → ℝ}
    (h : FrozenAuxiliaryLimitOutput p c κ M trap frozen U) :
    ∃ z : ℝ → ℝ → ℝ,
      FrozenAuxiliarySolutionFrom p c frozen (upperBarrier κ M) z ∧
        (∀ t, 0 ≤ t → trap (z t)) ∧
        (∀ x, Antitone (fun t => z t x)) ∧
        ∀ x, Tendsto (fun t : ℝ => z t x) atTop (𝓝 (U x)) :=
  h

theorem FrozenAuxiliaryLimitOutput.solution_from
    {p : CMParams} {c κ M : ℝ} {trap : (ℝ → ℝ) → Prop}
    {frozen U : ℝ → ℝ}
    (h : FrozenAuxiliaryLimitOutput p c κ M trap frozen U) :
    ∃ z : ℝ → ℝ → ℝ,
      FrozenAuxiliarySolutionFrom p c frozen (upperBarrier κ M) z := by
  rcases h with ⟨z, hz, _htrap, _hanti, _htendsto⟩
  exact ⟨z, hz⟩

theorem FrozenAuxiliaryLimitOutput.exists_trapped_antitone_orbit
    {p : CMParams} {c κ M : ℝ} {trap : (ℝ → ℝ) → Prop}
    {frozen U : ℝ → ℝ}
    (h : FrozenAuxiliaryLimitOutput p c κ M trap frozen U) :
    ∃ z : ℝ → ℝ → ℝ,
      (∀ t, 0 ≤ t → trap (z t)) ∧
        (∀ x, Antitone (fun t => z t x)) ∧
        ∀ x, Tendsto (fun t : ℝ => z t x) atTop (𝓝 (U x)) := by
  rcases h with ⟨z, _hz, htrap, hanti, htendsto⟩
  exact ⟨z, htrap, hanti, htendsto⟩

/-- The Schauder-map statement target from the proof of Theorem 1.1: construct
a local-uniformly compact and continuous limit map on a trapping set, then get a
fixed point. -/
def FrozenWaveMapConstruction
    (p : CMParams) (c κ M : ℝ) (trap : (ℝ → ℝ) → Prop) : Prop :=
  ∃ Tmap : (ℝ → ℝ) → ℝ → ℝ,
    (∀ u, trap u → trap (Tmap u)) ∧
      (∀ u, trap u → FrozenAuxiliaryLimitOutput p c κ M trap u (Tmap u)) ∧
      LocalUniformContinuousOn trap Tmap ∧
      LocalUniformSequentiallyCompactRange trap Tmap ∧
      ∃ U : ℝ → ℝ, trap U ∧ Tmap U = U

theorem FrozenWaveMapConstruction.exists_fixed_limit
    {p : CMParams} {c κ M : ℝ} {trap : (ℝ → ℝ) → Prop}
    (h : FrozenWaveMapConstruction p c κ M trap) :
    ∃ U : ℝ → ℝ,
      trap U ∧ FrozenAuxiliaryLimitOutput p c κ M trap U U := by
  rcases h with ⟨Tmap, _hmap, hlimit, _hcont, _hcompact, U, hU, hfix⟩
  refine ⟨U, hU, ?_⟩
  have hUlimit := hlimit U hU
  rwa [hfix] at hUlimit

theorem FrozenWaveMapConstruction.exists_fixed_inWaveTrapSet_with_bounds
    {p : CMParams} {c κ M : ℝ}
    (h : FrozenWaveMapConstruction p c κ M (fun u => InWaveTrapSet κ M u)) :
    ∃ U : ℝ → ℝ,
      InWaveTrapSet κ M U ∧
        FrozenAuxiliaryLimitOutput p c κ M
          (fun u => InWaveTrapSet κ M u) U U ∧
        (∀ x, 0 ≤ U x) ∧
        (∀ x, U x ≤ M) ∧
        ∀ x, U x ≤ Real.exp (-κ * x) := by
  rcases h.exists_fixed_limit with ⟨U, hU, hlimit⟩
  exact ⟨U, hU, hlimit, hU.nonneg, hU.le_M, hU.le_exp⟩

theorem FrozenWaveMapConstruction.exists_fixed_inMonotoneWaveTrapSet_with_bounds
    {p : CMParams} {c κ M : ℝ}
    (h :
      FrozenWaveMapConstruction p c κ M
        (fun u => InMonotoneWaveTrapSet κ M u)) :
    ∃ U : ℝ → ℝ,
      InMonotoneWaveTrapSet κ M U ∧
        FrozenAuxiliaryLimitOutput p c κ M
          (fun u => InMonotoneWaveTrapSet κ M u) U U ∧
        Antitone U ∧
        (∀ x, 0 ≤ U x) ∧
        (∀ x, U x ≤ M) ∧
        ∀ x, U x ≤ Real.exp (-κ * x) := by
  rcases h.exists_fixed_limit with ⟨U, hU, hlimit⟩
  exact
    ⟨U, hU, hlimit, hU.antitone, hU.nonneg, hU.le_M, hU.le_exp⟩

def subsolutionK (M κ κtilde m gamma : ℝ) : ℝ :=
  let prefactor := m * (κtilde + κ) + 1
  if gamma * κ = 1 then
    prefactor * (M ^ gamma + 3 / 4)
  else if gamma * κ < 1 then
    prefactor * (1 / (1 - gamma ^ 2 * κ ^ 2))
  else
    prefactor *
      (M ^ gamma * (κ ^ 2 * gamma ^ 2 - 1 + gamma * κ) /
        (κ ^ 2 * gamma ^ 2 - 1))

def subsolutionDThreshold
    (χ M κ κtilde m gamma c : ℝ) : ℝ :=
  (1 + |χ| * subsolutionK M κ κtilde m gamma) /
    (c * κtilde - κtilde ^ 2 - 1)

def constantSubsolutionThreshold (χ κ κtilde D : ℝ) : ℝ :=
  min (1 / (1 + |χ|))
    ((κ / (κtilde * D)) ^ (κ / (κtilde - κ)) *
      (1 - κ / κtilde))

theorem subsolutionK_pos
    {M κ κtilde m gamma : ℝ} (hM : 0 < M) (hκ : 0 < κ)
    (hgap : 0 < κtilde - κ) (hm : 0 < m) (hgamma : 0 < gamma) :
    0 < subsolutionK M κ κtilde m gamma := by
  have hκtilde : 0 < κtilde := by linarith
  have hprefactor : 0 < m * (κtilde + κ) + 1 := by
    nlinarith [mul_pos hm (by linarith : 0 < κtilde + κ)]
  unfold subsolutionK
  by_cases heq : gamma * κ = 1
  · rw [if_pos heq]
    exact mul_pos hprefactor
      (add_pos (Real.rpow_pos_of_pos hM _) (by norm_num))
  · rw [if_neg heq]
    by_cases hlt : gamma * κ < 1
    · rw [if_pos hlt]
      apply mul_pos hprefactor
      apply div_pos one_pos
      nlinarith [mul_pos hgamma hκ]
    · rw [if_neg hlt]
      have hgt : 1 < gamma * κ := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
      apply mul_pos hprefactor
      apply div_pos
      · apply mul_pos (Real.rpow_pos_of_pos hM _)
        nlinarith
      · nlinarith

theorem subsolutionDThreshold_pos
    {χ M κ κtilde m gamma c : ℝ}
    (hM : 0 < M) (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hm : 0 < m) (hgamma : 0 < gamma)
    (hden : 0 < c * κtilde - κtilde ^ 2 - 1) :
    0 < subsolutionDThreshold χ M κ κtilde m gamma c := by
  unfold subsolutionDThreshold
  apply div_pos
  · exact add_pos_of_pos_of_nonneg one_pos
      (mul_nonneg (abs_nonneg χ)
        (subsolutionK_pos hM hκ hgap hm hgamma).le)
  · exact hden

theorem subsolutionDThreshold_pos_of_kappa_speed
    {χ M κ κtilde m gamma c : ℝ}
    (hM : 0 < M) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hgap : κ < κtilde) (hκtilde1 : κtilde ≤ 1)
    (hm : 0 < m) (hgamma : 0 < gamma) (hc : c = κ + κ⁻¹) :
    0 < subsolutionDThreshold χ M κ κtilde m gamma c :=
  subsolutionDThreshold_pos hM hκ0 (sub_pos.mpr hgap) hm hgamma
    (lowerBarrierRaw_speed_denominator_pos hκ0 hκ1 hgap hκtilde1 hc)

theorem subsolutionDThreshold_pos_of_speed_gt_two
    {χ M κtilde m gamma c : ℝ}
    (hM : 0 < M) (hc : 2 < c) (hgap : kappa c < κtilde)
    (hκtilde1 : κtilde ≤ 1) (hm : 0 < m) (hgamma : 0 < gamma) :
    0 < subsolutionDThreshold χ M (kappa c) κtilde m gamma c :=
  subsolutionDThreshold_pos_of_kappa_speed hM
    (kappa_pos_of_two_lt hc)
    (kappa_lt_one_of_two_lt hc)
    hgap hκtilde1 hm hgamma
    (kappa_add_inv_eq_of_two_lt hc).symm

theorem subsolutionDThreshold_pos_of_cStarLower_lt
    {p : CMParams} {M κtilde c : ℝ}
    (hM : 0 < M) (hc : cStarLower p < c)
    (hgap : kappa c < κtilde) (hκtilde1 : κtilde ≤ 1) :
    0 < subsolutionDThreshold p.χ M (kappa c) κtilde p.m p.γ c :=
  subsolutionDThreshold_pos_of_speed_gt_two hM
    (two_lt_of_cStarLower_lt hc) hgap hκtilde1
    (lt_of_lt_of_le one_pos p.hm)
    (lt_of_lt_of_le one_pos p.hγ)

theorem constantSubsolutionThreshold_pos
    {χ κ κtilde D : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hD : 0 < D) :
    0 < constantSubsolutionThreshold χ κ κtilde D := by
  have hκtilde : 0 < κtilde := by linarith
  unfold constantSubsolutionThreshold
  apply lt_min
  · exact div_pos one_pos (by positivity)
  · apply mul_pos
    · apply Real.rpow_pos_of_pos
      exact div_pos hκ (mul_pos hκtilde hD)
    · rw [sub_pos]
      exact (div_lt_one hκtilde).mpr (by linarith)

theorem exists_D_gt_subsolutionDThreshold_lowerBarrierPlateau_mem_InWaveTrapSet
    {χ M κ κtilde m gamma c : ℝ}
    (hM : 0 < M) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hgap : κ < κtilde) (hκtilde1 : κtilde ≤ 1)
    (hm : 0 < m) (hgamma : 0 < gamma) (hc : c = κ + κ⁻¹) :
    ∃ D > subsolutionDThreshold χ M κ κtilde m gamma c,
      InWaveTrapSet κ M (lowerBarrierPlateau κ κtilde D) := by
  exact
    exists_D_gt_lowerBarrierPlateau_mem_InWaveTrapSet
      hκ0 (sub_pos.mpr hgap) hM
      (subsolutionDThreshold_pos_of_kappa_speed hM hκ0 hκ1 hgap
        hκtilde1 hm hgamma hc).le

theorem exists_D_gt_subsolutionDThreshold_lowerBarrierPlateau_mem_InMonotoneWaveTrapSet
    {χ M κ κtilde m gamma c : ℝ}
    (hM : 0 < M) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hgap : κ < κtilde) (hκtilde1 : κtilde ≤ 1)
    (hm : 0 < m) (hgamma : 0 < gamma) (hc : c = κ + κ⁻¹) :
    ∃ D > subsolutionDThreshold χ M κ κtilde m gamma c,
      InMonotoneWaveTrapSet κ M (lowerBarrierPlateau κ κtilde D) := by
  exact
    exists_D_gt_lowerBarrierPlateau_mem_InMonotoneWaveTrapSet
      hκ0 (sub_pos.mpr hgap) hM
      (subsolutionDThreshold_pos_of_kappa_speed hM hκ0 hκ1 hgap
        hκtilde1 hm hgamma hc).le

theorem
    exists_D_gt_subsolutionDThreshold_lowerBarrierPlateau_mem_InMonotoneWaveTrapSet_of_cStarLower_lt
    {p : CMParams} {M κtilde c : ℝ}
    (hM : 0 < M) (hc : cStarLower p < c)
    (hgap : kappa c < κtilde) (hκtilde1 : κtilde ≤ 1) :
    ∃ D > subsolutionDThreshold p.χ M (kappa c) κtilde p.m p.γ c,
      InMonotoneWaveTrapSet (kappa c) M
        (lowerBarrierPlateau (kappa c) κtilde D) := by
  exact
    exists_D_gt_subsolutionDThreshold_lowerBarrierPlateau_mem_InMonotoneWaveTrapSet
      hM (kappa_pos_of_cStarLower_lt hc) (kappa_lt_one_of_cStarLower_lt hc)
      hgap hκtilde1
      (lt_of_lt_of_le one_pos p.hm)
      (lt_of_lt_of_le one_pos p.hγ)
      (kappa_add_inv_eq_of_cStarLower_lt hc).symm

theorem D_pos_of_subsolutionDThreshold_lt_of_kappa_speed
    {χ M κ κtilde m gamma c D : ℝ}
    (hM : 0 < M) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hgap : κ < κtilde) (hκtilde1 : κtilde ≤ 1)
    (hm : 0 < m) (hgamma : 0 < gamma) (hc : c = κ + κ⁻¹)
    (hD : subsolutionDThreshold χ M κ κtilde m gamma c < D) :
    0 < D :=
  lt_trans
    (subsolutionDThreshold_pos_of_kappa_speed hM hκ0 hκ1 hgap
      hκtilde1 hm hgamma hc)
    hD

theorem D_pos_of_subsolutionDThreshold_lt_of_cStarLower_lt
    {p : CMParams} {M κtilde c D : ℝ}
    (hM : 0 < M) (hc : cStarLower p < c)
    (hgap : kappa c < κtilde) (hκtilde1 : κtilde ≤ 1)
    (hD : subsolutionDThreshold p.χ M (kappa c) κtilde p.m p.γ c < D) :
    0 < D :=
  D_pos_of_subsolutionDThreshold_lt_of_kappa_speed
    hM (kappa_pos_of_cStarLower_lt hc) (kappa_lt_one_of_cStarLower_lt hc)
    hgap hκtilde1
    (lt_of_lt_of_le one_pos p.hm)
    (lt_of_lt_of_le one_pos p.hγ)
    (kappa_add_inv_eq_of_cStarLower_lt hc).symm
    hD

theorem exists_d_pos_le_constantSubsolutionThreshold
    {χ κ κtilde D : ℝ}
    (hκ : 0 < κ) (hgap : κ < κtilde) (hD : 0 < D) :
    ∃ d : ℝ, 0 < d ∧ d ≤ constantSubsolutionThreshold χ κ κtilde D := by
  let d := constantSubsolutionThreshold χ κ κtilde D / 2
  have hthr : 0 < constantSubsolutionThreshold χ κ κtilde D :=
    constantSubsolutionThreshold_pos hκ (sub_pos.mpr hgap) hD
  refine ⟨d, ?_, ?_⟩
  · dsimp [d]
    linarith
  · dsimp [d]
    linarith

theorem
    exists_d_pos_le_constantSubsolutionThreshold_of_subsolutionDThreshold_lt
    {χ M κ κtilde m gamma c D : ℝ}
    (hM : 0 < M) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hgap : κ < κtilde) (hκtilde1 : κtilde ≤ 1)
    (hm : 0 < m) (hgamma : 0 < gamma) (hc : c = κ + κ⁻¹)
    (hD : subsolutionDThreshold χ M κ κtilde m gamma c < D) :
    ∃ d : ℝ, 0 < d ∧ d ≤ constantSubsolutionThreshold χ κ κtilde D :=
  exists_d_pos_le_constantSubsolutionThreshold hκ0 hgap
    (D_pos_of_subsolutionDThreshold_lt_of_kappa_speed hM hκ0 hκ1 hgap
      hκtilde1 hm hgamma hc hD)

theorem
    exists_d_pos_le_constantSubsolutionThreshold_of_cStarLower_lt
    {p : CMParams} {M κtilde c D : ℝ}
    (hM : 0 < M) (hc : cStarLower p < c)
    (hgap : kappa c < κtilde) (hκtilde1 : κtilde ≤ 1)
    (hD : subsolutionDThreshold p.χ M (kappa c) κtilde p.m p.γ c < D) :
    ∃ d : ℝ, 0 < d ∧
      d ≤ constantSubsolutionThreshold p.χ (kappa c) κtilde D :=
  exists_d_pos_le_constantSubsolutionThreshold_of_subsolutionDThreshold_lt
    hM (kappa_pos_of_cStarLower_lt hc) (kappa_lt_one_of_cStarLower_lt hc)
    hgap hκtilde1
    (lt_of_lt_of_le one_pos p.hm)
    (lt_of_lt_of_le one_pos p.hγ)
    (kappa_add_inv_eq_of_cStarLower_lt hc).symm
    hD

theorem kappaTilde_pos_of_kappa_lt
    {κ κtilde : ℝ} (hκ : 0 < κ) (hgap : κ < κtilde) :
    0 < κtilde := by
  linarith

theorem kappaTilde_le_one_plus_alpha_mul_kappa_of_subsolution_range
    {alpha m κ κtilde : ℝ}
    (hrange :
      κtilde ≤ min ((1 + alpha) * κ) (min (m * κ + 1 / 2) 1)) :
    κtilde ≤ (1 + alpha) * κ :=
  le_trans hrange (min_le_left _ _)

theorem kappaTilde_le_m_mul_kappa_add_half_of_subsolution_range
    {alpha m κ κtilde : ℝ}
    (hrange :
      κtilde ≤ min ((1 + alpha) * κ) (min (m * κ + 1 / 2) 1)) :
    κtilde ≤ m * κ + 1 / 2 :=
  le_trans hrange (le_trans (min_le_right _ _) (min_le_left _ _))

theorem kappaTilde_le_one_of_subsolution_range
    {alpha m κ κtilde : ℝ}
    (hrange :
      κtilde ≤ min ((1 + alpha) * κ) (min (m * κ + 1 / 2) 1)) :
    κtilde ≤ 1 :=
  le_trans hrange (le_trans (min_le_right _ _) (min_le_right _ _))

theorem kappaTilde_lt_one_of_lt_subsolution_range
    {alpha m κ κtilde : ℝ}
    (hrange :
      κtilde < min ((1 + alpha) * κ) (min (m * κ + 1 / 2) 1)) :
    κtilde < 1 :=
  lt_of_lt_of_le hrange (le_trans (min_le_right _ _) (min_le_right _ _))

def Lemma_4_1 : Prop :=
  (∀ p : CMParams, p.χ ≤ 0 → p.α ≤ p.m + p.γ - 1 →
    ∀ κ M c : ℝ, 0 < κ → κ < 1 → 1 ≤ M → c = κ + κ⁻¹ →
      ∀ u : ℝ → ℝ, InWaveTrapSet κ M u →
        IsFrozenSuperSolution p c u (upperBarrier κ M)) ∧
  (∀ p : CMParams, 0 ≤ p.χ → p.χ < chiStar p →
    p.α = p.m + p.γ - 1 →
    ∀ κ M c : ℝ, 0 < κ → κ < 1 → 1 ≤ M →
      (1 / (1 - p.χ)) ^ (1 / p.α) ≤ M → c = κ + κ⁻¹ →
      ∀ u : ℝ → ℝ, InWaveTrapSet κ M u →
        IsFrozenSuperSolution p c u (upperBarrier κ M))

def Lemma_4_2 : Prop :=
  ∀ p : CMParams, ∀ κ κtilde M c : ℝ,
    0 < κ → κ < 1 →
      κ < κtilde →
      κtilde ≤ min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1) →
      1 ≤ M → c = κ + κ⁻¹ →
        ∀ D : ℝ,
          subsolutionDThreshold p.χ M κ κtilde p.m p.γ c < D →
            ∀ u : ℝ → ℝ, InWaveTrapSet κ M u →
              IsFrozenSubSolutionOn p c u (lowerBarrierRaw κ κtilde D)
                (Set.Ioi (lowerBarrierXMinus κ κtilde D)) ∧
              ∀ d : ℝ, 0 < d → d ≤ constantSubsolutionThreshold p.χ κ κtilde D →
                IsFrozenSubSolutionOn p c u (fun _ => d) Set.univ

def MChi (p : CMParams) : ℝ :=
  if p.χ ≤ 0 then 1 else (1 / (1 - p.χ)) ^ (1 / p.α)

theorem MChi_eq_one_of_chi_nonpos (p : CMParams) (hχ : p.χ ≤ 0) :
    MChi p = 1 := by
  simp [MChi, hχ]

theorem MChi_eq_rpow_of_chi_pos (p : CMParams) (hχ : 0 < p.χ) :
    MChi p = (1 / (1 - p.χ)) ^ (1 / p.α) := by
  simp [MChi, not_le.mpr hχ]

theorem MChi_eq_rpow_of_chi_nonneg_lt_one
    (p : CMParams) (hχ_nonneg : 0 ≤ p.χ) (_hχ_lt : p.χ < 1) :
    MChi p = (1 / (1 - p.χ)) ^ (1 / p.α) := by
  by_cases hχ_zero : p.χ = 0
  · have hχ_nonpos : p.χ ≤ 0 := by linarith
    simp [MChi_eq_one_of_chi_nonpos p hχ_nonpos, hχ_zero]
  · exact
      MChi_eq_rpow_of_chi_pos p
        (lt_of_le_of_ne hχ_nonneg (Ne.symm hχ_zero))

theorem MChi_pos_of_chi_lt_one (p : CMParams) (hχ : p.χ < 1) :
    0 < MChi p := by
  by_cases hχ_nonpos : p.χ ≤ 0
  · simp [MChi, hχ_nonpos]
  · have hχ_pos : 0 < p.χ := lt_of_not_ge hχ_nonpos
    have hden_pos : 0 < 1 - p.χ := by linarith
    rw [MChi_eq_rpow_of_chi_pos p hχ_pos]
    exact Real.rpow_pos_of_pos (div_pos one_pos hden_pos) _

theorem one_le_MChi_of_chi_nonneg_lt_one
    (p : CMParams) (hχ_nonneg : 0 ≤ p.χ) (hχ_lt : p.χ < 1) :
    1 ≤ MChi p := by
  by_cases hχ_zero : p.χ = 0
  · have hχ_nonpos : p.χ ≤ 0 := by linarith
    simp [MChi_eq_one_of_chi_nonpos p hχ_nonpos]
  · have hχ_pos : 0 < p.χ := lt_of_le_of_ne hχ_nonneg (Ne.symm hχ_zero)
    have hden_pos : 0 < 1 - p.χ := by linarith
    have hbase : 1 ≤ 1 / (1 - p.χ) := by
      rw [le_div_iff₀ hden_pos]
      linarith
    have hα_pos : 0 < p.α := lt_of_lt_of_le one_pos p.hα
    have hexp_nonneg : 0 ≤ 1 / p.α := by positivity
    rw [MChi_eq_rpow_of_chi_pos p hχ_pos]
    exact Real.one_le_rpow hbase hexp_nonneg

theorem MChi_pos_of_chi_lt_chiStar (p : CMParams) (hχ : p.χ < chiStar p) :
    0 < MChi p :=
  MChi_pos_of_chi_lt_one p (lt_of_lt_of_le hχ (chiStar_le_one p))

theorem MChi_nonneg_of_chi_lt_one (p : CMParams) (hχ : p.χ < 1) :
    0 ≤ MChi p :=
  (MChi_pos_of_chi_lt_one p hχ).le

theorem MChi_rpow_pos_of_chi_lt_one (p : CMParams) (hχ : p.χ < 1) (a : ℝ) :
    0 < (MChi p) ^ a :=
  Real.rpow_pos_of_pos (MChi_pos_of_chi_lt_one p hχ) a

theorem MChi_gamma_pos_of_chi_lt_one (p : CMParams) (hχ : p.χ < 1) :
    0 < (MChi p) ^ p.γ :=
  MChi_rpow_pos_of_chi_lt_one p hχ p.γ

/-- Section 4.2 fixed-point construction for negative sensitivity, before the
final conversion of the fixed point into a traveling wave. -/
def NegativeSensitivityWaveFixedPointConstruction
    (p : CMParams) (c κ₁ κtilde D : ℝ) : Prop :=
  p.χ < 0 ∧
    p.α ≤ p.m + p.γ - 1 ∧
    cStarLower p < c ∧
    kappa c < κ₁ ∧
    κ₁ < κtilde ∧
    κtilde ≤
      min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1) ∧
    subsolutionDThreshold p.χ 1 (kappa c) κtilde p.m p.γ c < D ∧
    FrozenWaveMapConstruction p c (kappa c) 1
      (fun u => InMonotoneWaveTrapSet (kappa c) 1 u)

/-- Section 4.3 fixed-point construction for positive sensitivity, before the
final conversion of the fixed point into a traveling wave. -/
def PositiveSensitivityWaveFixedPointConstruction
    (p : CMParams) (c κ₁ κtilde D : ℝ) : Prop :=
  0 ≤ p.χ ∧
    p.χ < min (1 / 2 : ℝ) (chiStar p) ∧
    p.α = p.m + p.γ - 1 ∧
    2 < c ∧
    kappa c < κ₁ ∧
    κ₁ < κtilde ∧
    κtilde ≤
      min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1) ∧
    subsolutionDThreshold p.χ (MChi p) (kappa c) κtilde p.m p.γ c < D ∧
    FrozenWaveMapConstruction p c (kappa c) (MChi p)
      (fun u => InWaveTrapSet (kappa c) (MChi p) u)

theorem NegativeSensitivityWaveFixedPointConstruction.chi_neg
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    p.χ < 0 :=
  h.1

theorem NegativeSensitivityWaveFixedPointConstruction.alpha_le
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    p.α ≤ p.m + p.γ - 1 :=
  h.2.1

theorem NegativeSensitivityWaveFixedPointConstruction.cStarLower_lt
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    cStarLower p < c :=
  h.2.2.1

theorem NegativeSensitivityWaveFixedPointConstruction.two_lt_c
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    2 < c :=
  two_lt_of_cStarLower_lt h.cStarLower_lt

theorem NegativeSensitivityWaveFixedPointConstruction.c_pos
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    0 < c :=
  lt_trans (by norm_num : (0 : ℝ) < 2) h.two_lt_c

theorem NegativeSensitivityWaveFixedPointConstruction.kappa_lt_kappaOne
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    kappa c < κ₁ :=
  h.2.2.2.1

theorem NegativeSensitivityWaveFixedPointConstruction.kappaOne_lt_kappaTilde
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    κ₁ < κtilde :=
  h.2.2.2.2.1

theorem NegativeSensitivityWaveFixedPointConstruction.kappaTilde_range
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    κtilde ≤
      min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1) :=
  h.2.2.2.2.2.1

theorem NegativeSensitivityWaveFixedPointConstruction.D_gt_threshold
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    subsolutionDThreshold p.χ 1 (kappa c) κtilde p.m p.γ c < D :=
  h.2.2.2.2.2.2.1

theorem NegativeSensitivityWaveFixedPointConstruction.map_construction
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    FrozenWaveMapConstruction p c (kappa c) 1
      (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) :=
  h.2.2.2.2.2.2.2

theorem NegativeSensitivityWaveFixedPointConstruction.kappa_pos
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    0 < kappa c :=
  kappa_pos_of_cStarLower_lt h.cStarLower_lt

theorem NegativeSensitivityWaveFixedPointConstruction.kappa_lt_one
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    kappa c < 1 :=
  kappa_lt_one_of_cStarLower_lt h.cStarLower_lt

theorem NegativeSensitivityWaveFixedPointConstruction.kappa_add_inv_eq
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    kappa c + (kappa c)⁻¹ = c :=
  kappa_add_inv_eq_of_cStarLower_lt h.cStarLower_lt

theorem NegativeSensitivityWaveFixedPointConstruction.kappa_lt_kappaTilde
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    kappa c < κtilde :=
  lt_trans h.kappa_lt_kappaOne h.kappaOne_lt_kappaTilde

theorem NegativeSensitivityWaveFixedPointConstruction.kappaTilde_pos
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    0 < κtilde :=
  kappaTilde_pos_of_kappa_lt h.kappa_pos h.kappa_lt_kappaTilde

theorem NegativeSensitivityWaveFixedPointConstruction.kappaTilde_le_one
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    κtilde ≤ 1 :=
  kappaTilde_le_one_of_subsolution_range h.kappaTilde_range

theorem NegativeSensitivityWaveFixedPointConstruction.kappaTilde_le_one_plus_alpha_mul_kappa
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    κtilde ≤ (1 + p.α) * kappa c :=
  kappaTilde_le_one_plus_alpha_mul_kappa_of_subsolution_range
    h.kappaTilde_range

theorem NegativeSensitivityWaveFixedPointConstruction.kappaTilde_le_m_mul_kappa_add_half
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    κtilde ≤ p.m * kappa c + 1 / 2 :=
  kappaTilde_le_m_mul_kappa_add_half_of_subsolution_range
    h.kappaTilde_range

theorem NegativeSensitivityWaveFixedPointConstruction.D_pos
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    0 < D :=
  D_pos_of_subsolutionDThreshold_lt_of_cStarLower_lt
    one_pos h.cStarLower_lt h.kappa_lt_kappaTilde h.kappaTilde_le_one
    h.D_gt_threshold

theorem NegativeSensitivityWaveFixedPointConstruction.exists_constant_subsolution
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    ∃ d : ℝ, 0 < d ∧
      d ≤ constantSubsolutionThreshold p.χ (kappa c) κtilde D :=
  exists_d_pos_le_constantSubsolutionThreshold_of_cStarLower_lt
    one_pos h.cStarLower_lt h.kappa_lt_kappaTilde h.kappaTilde_le_one
    h.D_gt_threshold

theorem NegativeSensitivityWaveFixedPointConstruction.MChi_eq_one
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    MChi p = 1 :=
  MChi_eq_one_of_chi_nonpos p (le_of_lt h.chi_neg)

theorem PositiveSensitivityWaveFixedPointConstruction.chi_nonneg
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    0 ≤ p.χ :=
  h.1

theorem PositiveSensitivityWaveFixedPointConstruction.chi_lt_min
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    p.χ < min (1 / 2 : ℝ) (chiStar p) :=
  h.2.1

theorem PositiveSensitivityWaveFixedPointConstruction.chi_lt_chiStar
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    p.χ < chiStar p :=
  lt_of_lt_of_le h.chi_lt_min (min_le_right _ _)

theorem PositiveSensitivityWaveFixedPointConstruction.alpha_eq
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    p.α = p.m + p.γ - 1 :=
  h.2.2.1

theorem PositiveSensitivityWaveFixedPointConstruction.two_lt_c
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    2 < c :=
  h.2.2.2.1

theorem PositiveSensitivityWaveFixedPointConstruction.c_pos
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    0 < c :=
  lt_trans (by norm_num : (0 : ℝ) < 2) h.two_lt_c

theorem PositiveSensitivityWaveFixedPointConstruction.kappa_lt_kappaOne
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    kappa c < κ₁ :=
  h.2.2.2.2.1

theorem PositiveSensitivityWaveFixedPointConstruction.kappaOne_lt_kappaTilde
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    κ₁ < κtilde :=
  h.2.2.2.2.2.1

theorem PositiveSensitivityWaveFixedPointConstruction.kappaTilde_range
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    κtilde ≤
      min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1) :=
  h.2.2.2.2.2.2.1

theorem PositiveSensitivityWaveFixedPointConstruction.D_gt_threshold
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    subsolutionDThreshold p.χ (MChi p) (kappa c) κtilde p.m p.γ c < D :=
  h.2.2.2.2.2.2.2.1

theorem PositiveSensitivityWaveFixedPointConstruction.map_construction
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    FrozenWaveMapConstruction p c (kappa c) (MChi p)
      (fun u => InWaveTrapSet (kappa c) (MChi p) u) :=
  h.2.2.2.2.2.2.2.2

theorem PositiveSensitivityWaveFixedPointConstruction.kappa_pos
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    0 < kappa c :=
  kappa_pos_of_two_lt h.two_lt_c

theorem PositiveSensitivityWaveFixedPointConstruction.kappa_lt_one
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    kappa c < 1 :=
  kappa_lt_one_of_two_lt h.two_lt_c

theorem PositiveSensitivityWaveFixedPointConstruction.kappa_add_inv_eq
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    kappa c + (kappa c)⁻¹ = c :=
  kappa_add_inv_eq_of_two_lt h.two_lt_c

theorem PositiveSensitivityWaveFixedPointConstruction.kappa_lt_kappaTilde
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    kappa c < κtilde :=
  lt_trans h.kappa_lt_kappaOne h.kappaOne_lt_kappaTilde

theorem PositiveSensitivityWaveFixedPointConstruction.kappaTilde_pos
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    0 < κtilde :=
  kappaTilde_pos_of_kappa_lt h.kappa_pos h.kappa_lt_kappaTilde

theorem PositiveSensitivityWaveFixedPointConstruction.kappaTilde_le_one
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    κtilde ≤ 1 :=
  kappaTilde_le_one_of_subsolution_range h.kappaTilde_range

theorem PositiveSensitivityWaveFixedPointConstruction.kappaTilde_le_one_plus_alpha_mul_kappa
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    κtilde ≤ (1 + p.α) * kappa c :=
  kappaTilde_le_one_plus_alpha_mul_kappa_of_subsolution_range
    h.kappaTilde_range

theorem PositiveSensitivityWaveFixedPointConstruction.kappaTilde_le_m_mul_kappa_add_half
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    κtilde ≤ p.m * kappa c + 1 / 2 :=
  kappaTilde_le_m_mul_kappa_add_half_of_subsolution_range
    h.kappaTilde_range

theorem PositiveSensitivityWaveFixedPointConstruction.MChi_pos
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    0 < MChi p :=
  MChi_pos_of_chi_lt_chiStar p h.chi_lt_chiStar

theorem PositiveSensitivityWaveFixedPointConstruction.D_pos
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    0 < D :=
  D_pos_of_subsolutionDThreshold_lt_of_kappa_speed h.MChi_pos
    h.kappa_pos h.kappa_lt_one h.kappa_lt_kappaTilde h.kappaTilde_le_one
    (lt_of_lt_of_le one_pos p.hm)
    (lt_of_lt_of_le one_pos p.hγ)
    (kappa_add_inv_eq_of_two_lt h.two_lt_c).symm
    h.D_gt_threshold

theorem PositiveSensitivityWaveFixedPointConstruction.exists_constant_subsolution
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    ∃ d : ℝ, 0 < d ∧
      d ≤ constantSubsolutionThreshold p.χ (kappa c) κtilde D :=
  exists_d_pos_le_constantSubsolutionThreshold h.kappa_pos
    h.kappa_lt_kappaTilde h.D_pos

theorem PositiveSensitivityWaveFixedPointConstruction.one_le_MChi
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    1 ≤ MChi p :=
  one_le_MChi_of_chi_nonneg_lt_one p h.chi_nonneg
    (lt_of_lt_of_le h.chi_lt_chiStar (chiStar_le_one p))

theorem NegativeSensitivityWaveFixedPointConstruction.exists_fixed_limit
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    ∃ U : ℝ → ℝ,
      InMonotoneWaveTrapSet (kappa c) 1 U ∧
        FrozenAuxiliaryLimitOutput p c (kappa c) 1
          (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U := by
  exact FrozenWaveMapConstruction.exists_fixed_limit h.map_construction

theorem NegativeSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_bounds
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    ∃ U : ℝ → ℝ,
      InMonotoneWaveTrapSet (kappa c) 1 U ∧
        FrozenAuxiliaryLimitOutput p c (kappa c) 1
          (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U ∧
        Antitone U ∧
        (∀ x, 0 ≤ U x) ∧
        (∀ x, U x ≤ 1) ∧
        ∀ x, U x ≤ Real.exp (-(kappa c) * x) := by
  exact h.map_construction.exists_fixed_inMonotoneWaveTrapSet_with_bounds

theorem PositiveSensitivityWaveFixedPointConstruction.exists_fixed_limit
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    ∃ U : ℝ → ℝ,
      InWaveTrapSet (kappa c) (MChi p) U ∧
        FrozenAuxiliaryLimitOutput p c (kappa c) (MChi p)
          (fun u => InWaveTrapSet (kappa c) (MChi p) u) U U := by
  exact FrozenWaveMapConstruction.exists_fixed_limit h.map_construction

theorem PositiveSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_bounds
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    ∃ U : ℝ → ℝ,
      InWaveTrapSet (kappa c) (MChi p) U ∧
        FrozenAuxiliaryLimitOutput p c (kappa c) (MChi p)
          (fun u => InWaveTrapSet (kappa c) (MChi p) u) U U ∧
        (∀ x, 0 ≤ U x) ∧
        (∀ x, U x ≤ MChi p) ∧
        ∀ x, U x ≤ Real.exp (-(kappa c) * x) := by
  exact h.map_construction.exists_fixed_inWaveTrapSet_with_bounds

theorem one_le_MChi_of_chi_nonneg_lt_chiStar
    (p : CMParams) (hχ_nonneg : 0 ≤ p.χ) (hχ : p.χ < chiStar p) :
    1 ≤ MChi p :=
  one_le_MChi_of_chi_nonneg_lt_one p hχ_nonneg
    (lt_of_lt_of_le hχ (chiStar_le_one p))

def HasWaveUpperTailBound (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop :=
  ∀ x, 0 < U x ∧ U x ≤ min (MChi p) (Real.exp (-(kappa c) * x))

def HasStrictWaveUpperTailBound (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop :=
  ∀ x, 0 < U x ∧ U x < min (MChi p) (Real.exp (-(kappa c) * x))

theorem HasStrictWaveUpperTailBound.hasWaveUpperTailBound
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasStrictWaveUpperTailBound p c U) :
    HasWaveUpperTailBound p c U := by
  intro x
  exact ⟨(h x).1, (h x).2.le⟩

theorem HasStrictWaveUpperTailBound.pos
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasStrictWaveUpperTailBound p c U) (x : ℝ) :
    0 < U x :=
  (h x).1

theorem HasStrictWaveUpperTailBound.lt_MChi
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasStrictWaveUpperTailBound p c U) (x : ℝ) :
    U x < MChi p :=
  lt_of_lt_of_le (h x).2 (min_le_left _ _)

theorem HasStrictWaveUpperTailBound.lt_exp
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasStrictWaveUpperTailBound p c U) (x : ℝ) :
    U x < Real.exp (-(kappa c) * x) :=
  lt_of_lt_of_le (h x).2 (min_le_right _ _)

theorem HasWaveUpperTailBound.pos {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasWaveUpperTailBound p c U) (x : ℝ) :
    0 < U x :=
  (h x).1

theorem HasWaveUpperTailBound.le_MChi {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasWaveUpperTailBound p c U) (x : ℝ) :
    U x ≤ MChi p :=
  le_trans (h x).2 (min_le_left _ _)

theorem HasWaveUpperTailBound.le_exp {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasWaveUpperTailBound p c U) (x : ℝ) :
    U x ≤ Real.exp (-(kappa c) * x) :=
  le_trans (h x).2 (min_le_right _ _)

theorem HasWaveUpperTailBound.inWaveTrapSet
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasWaveUpperTailBound p c U) (hU : IsCUnifBdd U) :
    InWaveTrapSet (kappa c) (MChi p) U := by
  refine ⟨hU, ?_⟩
  intro x
  exact ⟨(h.pos x).le, by simpa [upperBarrier] using (h x).2⟩

theorem HasWaveUpperTailBound.inMonotoneWaveTrapSet
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasWaveUpperTailBound p c U) (hU : IsCUnifBdd U)
    (hmono : NonincreasingProfile U) :
    InMonotoneWaveTrapSet (kappa c) (MChi p) U :=
  ⟨h.inWaveTrapSet hU, hmono⟩

theorem HasWaveUpperTailBound.rpow_le_MChi
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ} {a : ℝ}
    (h : HasWaveUpperTailBound p c U) (ha : 0 ≤ a) (x : ℝ) :
    (U x) ^ a ≤ (MChi p) ^ a :=
  Real.rpow_le_rpow (h.pos x).le (h.le_MChi x) ha

theorem HasWaveUpperTailBound.rpow_le_exp
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ} {a : ℝ}
    (h : HasWaveUpperTailBound p c U) (ha : 0 ≤ a) (x : ℝ) :
    (U x) ^ a ≤ (Real.exp (-(kappa c) * x)) ^ a :=
  Real.rpow_le_rpow (h.pos x).le (h.le_exp x) ha

theorem HasWaveUpperTailBound.rpow_le_exp_mul
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ} {a : ℝ}
    (h : HasWaveUpperTailBound p c U) (ha : 0 ≤ a) (x : ℝ) :
    (U x) ^ a ≤ Real.exp (-(kappa c) * a * x) := by
  calc
    (U x) ^ a ≤ (Real.exp (-(kappa c) * x)) ^ a := h.rpow_le_exp ha x
    _ = Real.exp (-(kappa c) * a * x) := by
      rw [← Real.exp_mul]
      congr 1
      ring

theorem HasWaveUpperTailBound.rpow_le_MChi_gamma
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasWaveUpperTailBound p c U) (x : ℝ) :
    (U x) ^ p.γ ≤ (MChi p) ^ p.γ :=
  h.rpow_le_MChi (le_trans zero_le_one p.hγ) x

theorem HasWaveUpperTailBound.rpow_le_exp_gamma
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasWaveUpperTailBound p c U) (x : ℝ) :
    (U x) ^ p.γ ≤ (Real.exp (-(kappa c) * x)) ^ p.γ :=
  h.rpow_le_exp (le_trans zero_le_one p.hγ) x

theorem HasWaveUpperTailBound.rpow_abs_le_MChi_gamma
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasWaveUpperTailBound p c U) (x : ℝ) :
    |(U x) ^ p.γ| ≤ (MChi p) ^ p.γ := by
  rw [abs_of_nonneg (Real.rpow_nonneg (h.pos x).le _)]
  exact h.rpow_le_MChi_gamma x

theorem ShenUpperBoundPositive.hasStrictWaveUpperTailBound
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : ShenUpperBoundPositive p c U)
    (hχ_nonneg : 0 ≤ p.χ) (hχ_lt : p.χ < 1) :
    HasStrictWaveUpperTailBound p c U := by
  intro x
  refine ⟨(h x).1, ?_⟩
  rw [MChi_eq_rpow_of_chi_nonneg_lt_one p hχ_nonneg hχ_lt]
  exact (h x).2

theorem ShenUpperBoundPositive.hasWaveUpperTailBound
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hχ_nonneg : 0 ≤ p.χ) (hχ_lt : p.χ < 1)
    (h : ShenUpperBoundPositive p c U) :
    HasWaveUpperTailBound p c U :=
  (h.hasStrictWaveUpperTailBound hχ_nonneg hχ_lt).hasWaveUpperTailBound

theorem ShenUpperBoundPositive.inWaveTrapSet
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hχ_nonneg : 0 ≤ p.χ) (hχ_lt : p.χ < 1)
    (h : ShenUpperBoundPositive p c U) (hU : IsCUnifBdd U) :
    InWaveTrapSet (kappa c) (MChi p) U :=
  (ShenUpperBoundPositive.hasWaveUpperTailBound hχ_nonneg hχ_lt h).inWaveTrapSet hU

def WaveDerivativeTendsZero (U : ℝ → ℝ) : Prop :=
  Tendsto (fun x => deriv U x) atBot (𝓝 0) ∧
    Tendsto (fun x => deriv U x) atTop (𝓝 0)

def Lemma_5_1 : Prop :=
  ∀ p : CMParams, ∀ c : ℝ, 2 < c →
    ∀ U V : ℝ → ℝ,
      IsTravelingWave p c U V →
      HasWaveUpperTailBound p c U →
        (∀ x, |V x| ≤ (MChi p) ^ p.γ ∧ |deriv V x| ≤ (MChi p) ^ p.γ) ∧
        (p.γ + p.γ⁻¹ < c →
          ∀ x,
            |V x| ≤
              min ((MChi p) ^ p.γ)
                ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
                  Real.exp (-(kappa c) * p.γ * x)) ∧
            |deriv V x| ≤
              min ((MChi p) ^ p.γ)
                ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
                  Real.exp (-(kappa c) * p.γ * x))) ∧
        WaveDerivativeTendsZero U ∧
        (c > p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) →
          ∃ B > 0, ∀ x, |deriv U x| ≤ B) ∧
        (c > max (p.γ + p.γ⁻¹) (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)) →
          ∃ B1 B2, ∀ x,
            |deriv U x| ≤
              B1 * Real.exp (-(kappa c) * x) +
                B2 * Real.exp (-(kappa c) * p.γ * x))

theorem Lemma_5_1.signal_bound
    (h : Lemma_5_1) {p : CMParams} {c : ℝ} (hc : 2 < c)
    {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U) :
    ∀ x, |V x| ≤ (MChi p) ^ p.γ ∧ |deriv V x| ≤ (MChi p) ^ p.γ :=
  (h p c hc U V hTW hbound).1

theorem Lemma_5_1.exponential_signal_bound
    (h : Lemma_5_1) {p : CMParams} {c : ℝ} (hc : 2 < c)
    {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hspeed : p.γ + p.γ⁻¹ < c) :
    ∀ x,
      |V x| ≤
        min ((MChi p) ^ p.γ)
          ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
            Real.exp (-(kappa c) * p.γ * x)) ∧
      |deriv V x| ≤
        min ((MChi p) ^ p.γ)
          ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
            Real.exp (-(kappa c) * p.γ * x)) :=
  (h p c hc U V hTW hbound).2.1 hspeed

theorem Lemma_5_1.wave_derivative_tends_zero
    (h : Lemma_5_1) {p : CMParams} {c : ℝ} (hc : 2 < c)
    {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U) :
    WaveDerivativeTendsZero U :=
  (h p c hc U V hTW hbound).2.2.1

theorem Lemma_5_1.wave_derivative_bounded
    (h : Lemma_5_1) {p : CMParams} {c : ℝ} (hc : 2 < c)
    {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hspeed : c > p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)) :
    ∃ B > 0, ∀ x, |deriv U x| ≤ B :=
  (h p c hc U V hTW hbound).2.2.2.1 hspeed

theorem Lemma_5_1.wave_derivative_exp_bound
    (h : Lemma_5_1) {p : CMParams} {c : ℝ} (hc : 2 < c)
    {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hspeed :
      c > max (p.γ + p.γ⁻¹) (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1))) :
    ∃ B1 B2, ∀ x,
      |deriv U x| ≤
        B1 * Real.exp (-(kappa c) * x) +
          B2 * Real.exp (-(kappa c) * p.γ * x) :=
  (h p c hc U V hTW hbound).2.2.2.2 hspeed

def Lemma_5_2 : Prop :=
  ∀ p : CMParams, ∀ c : ℝ,
    c > max (p.γ + p.γ⁻¹) (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)) →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
          ∃ B > 0, ∀ x, deriv U x / U x ≤ B

theorem Lemma_5_2.log_derivative_bound
    (h : Lemma_5_2) {p : CMParams} {c : ℝ}
    (hspeed :
      c > max (p.γ + p.γ⁻¹) (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)))
    {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U) :
    ∃ B > 0, ∀ x, deriv U x / U x ≤ B :=
  h p c hspeed U V hTW hbound

def Lemma_5_3 : Prop :=
  ∀ gamma M eta : ℝ,
    1 ≤ gamma → 1 ≤ M → 0 < eta → eta < 1 →
      ∀ u1 u2 : ℝ → ℝ,
        IsCUnifBdd u1 → IsCUnifBdd u2 →
        (∀ x, 0 ≤ u1 x ∧ u1 x ≤ M) →
        (∀ x, 0 ≤ u2 x ∧ u2 x ≤ M) →
        Integrable
          (fun x => Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2) →
          let v := Psi (fun x => u2 x ^ gamma - u1 x ^ gamma) 1 1
          let U := fun x => Real.exp (eta * x) * (u2 x - u1 x)
          let V := fun x => Real.exp (eta * x) * v x
          (∫ x : ℝ, |V x| ^ 2 ≤
              gamma ^ 2 * M ^ (2 * (gamma - 1)) / (1 - eta) ^ 2 *
                ∫ x : ℝ, |U x| ^ 2) ∧
            (∫ x : ℝ, |deriv V x| ^ 2 ≤
              gamma ^ 2 * M ^ (2 * (gamma - 1)) / (1 - eta ^ 2) *
                ∫ x : ℝ, |U x| ^ 2)

theorem Lemma_5_3.weighted_elliptic_perturbation
    (h : Lemma_5_3)
    {gamma M eta : ℝ}
    (hgamma : 1 ≤ gamma) (hM : 1 ≤ M) (heta_pos : 0 < eta) (heta_one : eta < 1)
    {u1 u2 : ℝ → ℝ}
    (hu1 : IsCUnifBdd u1) (hu2 : IsCUnifBdd u2)
    (hu1_bound : ∀ x, 0 ≤ u1 x ∧ u1 x ≤ M)
    (hu2_bound : ∀ x, 0 ≤ u2 x ∧ u2 x ≤ M)
    (hclose : Integrable
      (fun x => Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2)) :
    let v := Psi (fun x => u2 x ^ gamma - u1 x ^ gamma) 1 1
    let U := fun x => Real.exp (eta * x) * (u2 x - u1 x)
    let V := fun x => Real.exp (eta * x) * v x
    (∫ x : ℝ, |V x| ^ 2 ≤
        gamma ^ 2 * M ^ (2 * (gamma - 1)) / (1 - eta) ^ 2 *
          ∫ x : ℝ, |U x| ^ 2) ∧
      (∫ x : ℝ, |deriv V x| ^ 2 ≤
        gamma ^ 2 * M ^ (2 * (gamma - 1)) / (1 - eta ^ 2) *
          ∫ x : ℝ, |U x| ^ 2) :=
  h gamma M eta hgamma hM heta_pos heta_one
    u1 u2 hu1 hu2 hu1_bound hu2_bound hclose

theorem Lemma_5_3.weighted_elliptic_perturbation_CM
    (h : Lemma_5_3) (p : CMParams) {eta : ℝ}
    (hM : 1 ≤ MChi p) (heta_pos : 0 < eta) (heta_one : eta < 1)
    {u1 u2 : ℝ → ℝ}
    (hu1 : IsCUnifBdd u1) (hu2 : IsCUnifBdd u2)
    (hu1_bound : ∀ x, 0 ≤ u1 x ∧ u1 x ≤ MChi p)
    (hu2_bound : ∀ x, 0 ≤ u2 x ∧ u2 x ≤ MChi p)
    (hclose : Integrable
      (fun x => Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2)) :
    let v := Psi (fun x => u2 x ^ p.γ - u1 x ^ p.γ) 1 1
    let U := fun x => Real.exp (eta * x) * (u2 x - u1 x)
    let V := fun x => Real.exp (eta * x) * v x
    (∫ x : ℝ, |V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta) ^ 2 *
          ∫ x : ℝ, |U x| ^ 2) ∧
      (∫ x : ℝ, |deriv V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta ^ 2) *
          ∫ x : ℝ, |U x| ^ 2) :=
  h.weighted_elliptic_perturbation p.hγ hM heta_pos heta_one
    hu1 hu2 hu1_bound hu2_bound hclose

theorem Lemma_5_3.weighted_elliptic_perturbation_of_tail_bounds
    (h : Lemma_5_3) {p : CMParams} {c eta : ℝ}
    (hM : 1 ≤ MChi p) (heta_pos : 0 < eta) (heta_one : eta < 1)
    {u1 u2 : ℝ → ℝ}
    (hu1 : IsCUnifBdd u1) (hu2 : IsCUnifBdd u2)
    (hbound1 : HasWaveUpperTailBound p c u1)
    (hbound2 : HasWaveUpperTailBound p c u2)
    (hclose : Integrable
      (fun x => Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2)) :
    let v := Psi (fun x => u2 x ^ p.γ - u1 x ^ p.γ) 1 1
    let U := fun x => Real.exp (eta * x) * (u2 x - u1 x)
    let V := fun x => Real.exp (eta * x) * v x
    (∫ x : ℝ, |V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta) ^ 2 *
          ∫ x : ℝ, |U x| ^ 2) ∧
      (∫ x : ℝ, |deriv V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta ^ 2) *
          ∫ x : ℝ, |U x| ^ 2) :=
  h.weighted_elliptic_perturbation_CM p hM heta_pos heta_one
    hu1 hu2
    (fun x => ⟨(hbound1.pos x).le, hbound1.le_MChi x⟩)
    (fun x => ⟨(hbound2.pos x).le, hbound2.le_MChi x⟩)
    hclose

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

theorem Proposition_1_1.negative_solution
    (h : Proposition_1_1) {p : CMParams}
    (hχ : p.χ ≤ 0) {u₀ : ℝ → ℝ}
    (hu₀ : NonnegativeInitialDatum u₀) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalCauchySolutionFrom p u₀ u v ∧
      (∀ M, (∀ x, u₀ x ≤ M) →
        ∀ t x, 0 ≤ t → u t x ≤ max 1 M) ∧
      UniformLimsupLe u 1 :=
  h.1 p hχ u₀ hu₀

theorem Proposition_1_1.positive_solution
    (h : Proposition_1_1) {p : CMParams}
    (hparam :
      (0 < p.χ ∧ p.α > p.m + p.γ - 1) ∨
        (0 < p.χ ∧
          p.χ < min
            ((p.m + p.γ - 1) / (2 * p.m - 1))
            ((p.m + p.γ - 1) / (p.γ - 1)) ∧
          p.α = p.m + p.γ - 1))
    {u₀ : ℝ → ℝ} (hu₀ : NonnegativeInitialDatum u₀) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalCauchySolutionFrom p u₀ u v ∧
      UniformEventuallyBounded u ∧
      (0 < p.χ → p.χ < 1 → UniformLimsupLe u ((1 / (1 - p.χ)) ^ (1 / p.α))) :=
  h.2 p hparam u₀ hu₀

/-- Paper1 Proposition 1.2: stability of the positive constant solution. -/
def Proposition_1_2 : Prop :=
  (∀ p : CMParams, p.χ ≤ 0 →
    ∀ u₀ : ℝ → ℝ, NonnegativeInitialDatum u₀ → UniformlyPositive u₀ →
      ∃ u v : ℝ → ℝ → ℝ,
        IsGlobalCauchySolutionFrom p u₀ u v ∧
        UniformConvergesToConstant u 1) ∧
  (∀ p : CMParams, 0 < p.χ → p.χ < (1 / 2 : ℝ) →
    p.m + p.γ - 1 ≤ p.α →
    ∀ u₀ : ℝ → ℝ, NonnegativeInitialDatum u₀ → UniformlyPositive u₀ →
      ∃ u v : ℝ → ℝ → ℝ,
        IsGlobalCauchySolutionFrom p u₀ u v ∧
        UniformConvergesToConstant u 1)

theorem Proposition_1_2.negative_stability
    (h : Proposition_1_2) {p : CMParams}
    (hχ : p.χ ≤ 0) {u₀ : ℝ → ℝ}
    (hu₀_nonneg : NonnegativeInitialDatum u₀)
    (hu₀_pos : UniformlyPositive u₀) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalCauchySolutionFrom p u₀ u v ∧
      UniformConvergesToConstant u 1 :=
  h.1 p hχ u₀ hu₀_nonneg hu₀_pos

theorem Proposition_1_2.positive_stability
    (h : Proposition_1_2) {p : CMParams}
    (hχ_pos : 0 < p.χ) (hχ_small : p.χ < (1 / 2 : ℝ))
    (halpha : p.m + p.γ - 1 ≤ p.α)
    {u₀ : ℝ → ℝ}
    (hu₀_nonneg : NonnegativeInitialDatum u₀)
    (hu₀_pos : UniformlyPositive u₀) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalCauchySolutionFrom p u₀ u v ∧
      UniformConvergesToConstant u 1 :=
  h.2 p hχ_pos hχ_small halpha u₀ hu₀_nonneg hu₀_pos

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

theorem Theorem_1_1.negative_wave
    (h : Theorem_1_1) {p : CMParams}
    (halpha : p.α ≤ p.m + p.γ - 1) (hχ : p.χ ≤ 0)
    {c : ℝ} (hc : cStarLower p < c) :
    ∃ U V : ℝ → ℝ,
      IsMonotoneTravelingWave p c U V ∧
      ShenUpperBoundNegative c U ∧
      ∀ κ₁, kappa c < κ₁ →
        κ₁ < min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1) →
        HasWaveRightTailAsymptotic c κ₁ U :=
  h.1 p halpha hχ c hc

theorem Theorem_1_1.positive_wave
    (h : Theorem_1_1) {p : CMParams}
    (halpha : p.α = p.m + p.γ - 1)
    (hχ_nonneg : 0 ≤ p.χ) (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    {c : ℝ} (hc : 2 < c) :
    ∃ U V : ℝ → ℝ,
      IsTravelingWave p c U V ∧
      ShenUpperBoundPositive p c U ∧
      ∀ κ₁, kappa c < κ₁ →
        κ₁ < min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1) →
        HasWaveRightTailAsymptotic c κ₁ U :=
  h.2 p halpha hχ_nonneg hχ_small c hc

theorem Theorem_1_1.of_frozenStationaryProfile_branches
    (hneg :
      ∀ p : CMParams, p.α ≤ p.m + p.γ - 1 → p.χ ≤ 0 →
        ∀ c : ℝ, cStarLower p < c →
          ∃ U : ℝ → ℝ,
            FrozenStationaryWaveProfile p c U ∧
              (∀ x, deriv U x ≤ 0) ∧
              (∀ x, deriv (frozenElliptic p U) x ≤ 0) ∧
              ShenUpperBoundNegative c U ∧
              ∀ κ₁, kappa c < κ₁ →
                κ₁ <
                  min ((1 + p.α) * kappa c)
                    (min (p.m * kappa c + 1 / 2) 1) →
                HasWaveRightTailAsymptotic c κ₁ U)
    (hpos :
      ∀ p : CMParams, p.α = p.m + p.γ - 1 →
        0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
        ∀ c : ℝ, 2 < c →
          ∃ U : ℝ → ℝ,
            FrozenStationaryWaveProfile p c U ∧
              ShenUpperBoundPositive p c U ∧
              ∀ κ₁, kappa c < κ₁ →
                κ₁ <
                  min ((1 + p.α) * kappa c)
                    (min (p.m * kappa c + 1 / 2) 1) →
                HasWaveRightTailAsymptotic c κ₁ U) :
    Theorem_1_1 := by
  constructor
  · intro p halpha hχ c hc
    rcases hneg p halpha hχ c hc with
      ⟨U, hprofile, hUmono, hVmono, hupper, htail⟩
    exact
      ⟨U, frozenElliptic p U,
        hprofile.to_monotoneTravelingWave hUmono hVmono, hupper, htail⟩
  · intro p halpha hχ_nonneg hχ_small c hc
    rcases hpos p halpha hχ_nonneg hχ_small c hc with
      ⟨U, hprofile, hupper, htail⟩
    exact
      ⟨U, frozenElliptic p U,
        hprofile.to_travelingWave, hupper, htail⟩

theorem Theorem_1_1.of_frozenStationaryProfile_trap_branches
    (hneg :
      ∀ p : CMParams, p.α ≤ p.m + p.γ - 1 → p.χ ≤ 0 →
        ∀ c : ℝ, cStarLower p < c →
          ∃ U : ℝ → ℝ,
            InMonotoneWaveTrapSet (kappa c) 1 U ∧
              FrozenStationaryWaveProfile p c U ∧
              (∀ x, deriv (frozenElliptic p U) x ≤ 0) ∧
              ShenUpperBoundNegative c U ∧
              ∀ κ₁, kappa c < κ₁ →
                κ₁ <
                  min ((1 + p.α) * kappa c)
                    (min (p.m * kappa c + 1 / 2) 1) →
                HasWaveRightTailAsymptotic c κ₁ U)
    (hpos :
      ∀ p : CMParams, p.α = p.m + p.γ - 1 →
        0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
        ∀ c : ℝ, 2 < c →
          ∃ U : ℝ → ℝ,
            FrozenStationaryWaveProfile p c U ∧
              ShenUpperBoundPositive p c U ∧
              ∀ κ₁, kappa c < κ₁ →
                κ₁ <
                  min ((1 + p.α) * kappa c)
                    (min (p.m * kappa c + 1 / 2) 1) →
                HasWaveRightTailAsymptotic c κ₁ U) :
    Theorem_1_1 := by
  refine Theorem_1_1.of_frozenStationaryProfile_branches ?_ hpos
  intro p halpha hχ c hc
  rcases hneg p halpha hχ c hc with
    ⟨U, htrap, hprofile, hVmono, hupper, htail⟩
  exact
    ⟨U, hprofile, htrap.deriv_nonpos, hVmono, hupper, htail⟩

def StableWaveParameterRegime (p : CMParams) : Prop :=
  (p.χ < 0 ∧ p.α ≤ p.m + p.γ - 1) ∨
    (0 ≤ p.χ ∧ p.χ < chiStar p ∧ p.α = p.m + p.γ - 1)

theorem StableWaveParameterRegime.of_negative
    {p : CMParams} (hχ : p.χ < 0) (halpha : p.α ≤ p.m + p.γ - 1) :
    StableWaveParameterRegime p :=
  Or.inl ⟨hχ, halpha⟩

theorem StableWaveParameterRegime.of_positive
    {p : CMParams}
    (hχ_nonneg : 0 ≤ p.χ) (hχ_small : p.χ < chiStar p)
    (halpha : p.α = p.m + p.γ - 1) :
    StableWaveParameterRegime p :=
  Or.inr ⟨hχ_nonneg, hχ_small, halpha⟩

theorem StableWaveParameterRegime.alpha_le
    {p : CMParams} (h : StableWaveParameterRegime p) :
    p.α ≤ p.m + p.γ - 1 := by
  rcases h with hneg | hpos
  · exact hneg.2
  · exact le_of_eq hpos.2.2

theorem StableWaveParameterRegime.positive_branch_of_chi_nonneg
    {p : CMParams} (h : StableWaveParameterRegime p) (hχ_nonneg : 0 ≤ p.χ) :
    p.χ < chiStar p ∧ p.α = p.m + p.γ - 1 := by
  rcases h with hneg | hpos
  · linarith
  · exact ⟨hpos.2.1, hpos.2.2⟩

theorem StableWaveParameterRegime.MChi_eq_one_of_chi_neg
    {p : CMParams} (_h : StableWaveParameterRegime p) (hχ : p.χ < 0) :
    MChi p = 1 :=
  MChi_eq_one_of_chi_nonpos p (le_of_lt hχ)

def stabilitySpeedBaseline (p : CMParams) : ℝ :=
  1 + |p.χ| ^ (1 / 6 : ℝ) + (1 + |p.χ| ^ (1 / 6 : ℝ))⁻¹

/-- The paper's `c**_{χ,m,α,γ} - γ - γ⁻¹ = O(|χ|^{1/6})`
as `χ → 0`, represented by an explicit big-O bound for a threshold family. -/
def StabilitySpeedThresholdFamilyAsymptotic
    (p : CMParams) (cStarStar : ℝ → ℝ) : Prop :=
  ∃ A > 0, ∃ δ > 0, ∀ χ : ℝ, |χ| < δ →
    |cStarStar χ - (p.γ + p.γ⁻¹)| ≤ A * |χ| ^ (1 / 6 : ℝ)

lemma StabilitySpeedThresholdFamilyAsymptotic.bound
    {p : CMParams} {cStarStar : ℝ → ℝ}
    (h : StabilitySpeedThresholdFamilyAsymptotic p cStarStar) :
    ∃ A > 0, ∃ δ > 0, ∀ χ : ℝ, |χ| < δ →
      |cStarStar χ - (p.γ + p.γ⁻¹)| ≤ A * |χ| ^ (1 / 6 : ℝ) :=
  h

theorem stabilitySpeedBaseline_pos (p : CMParams) :
    0 < stabilitySpeedBaseline p := by
  unfold stabilitySpeedBaseline
  have hpow_nonneg : 0 ≤ |p.χ| ^ (1 / 6 : ℝ) :=
    Real.rpow_nonneg (abs_nonneg p.χ) _
  have hden_pos : 0 < 1 + |p.χ| ^ (1 / 6 : ℝ) := by
    linarith
  positivity

theorem one_lt_stabilitySpeedBaseline (p : CMParams) :
    1 < stabilitySpeedBaseline p := by
  unfold stabilitySpeedBaseline
  have hpow_nonneg : 0 ≤ |p.χ| ^ (1 / 6 : ℝ) :=
    Real.rpow_nonneg (abs_nonneg p.χ) _
  have hden_pos : 0 < 1 + |p.χ| ^ (1 / 6 : ℝ) := by
    linarith
  have hinv_pos : 0 < (1 + |p.χ| ^ (1 / 6 : ℝ))⁻¹ :=
    inv_pos.mpr hden_pos
  linarith

theorem stabilitySpeedBaseline_eq_cStarStar (p : CMParams) :
    stabilitySpeedBaseline p = cStarStar p := by
  simp [stabilitySpeedBaseline, cStarStar, one_div]

theorem two_le_stabilitySpeedBaseline (p : CMParams) :
    2 ≤ stabilitySpeedBaseline p := by
  rw [stabilitySpeedBaseline_eq_cStarStar]
  exact cStarStar_ge_two p

theorem two_lt_of_stabilitySpeedBaseline_lt
    {p : CMParams} {threshold : ℝ → ℝ} {c : ℝ}
    (hlower : stabilitySpeedBaseline p < threshold p.χ)
    (hc : threshold p.χ < c) :
    2 < c :=
  lt_of_le_of_lt (two_le_stabilitySpeedBaseline p) (lt_trans hlower hc)

theorem kappa_pos_of_stabilitySpeedBaseline_lt
    {p : CMParams} {threshold : ℝ → ℝ} {c : ℝ}
    (hlower : stabilitySpeedBaseline p < threshold p.χ)
    (hc : threshold p.χ < c) :
    0 < kappa c :=
  kappa_pos_of_two_lt (two_lt_of_stabilitySpeedBaseline_lt hlower hc)

theorem eta_pos_of_stability_weight_hypotheses
    {p : CMParams} {threshold : ℝ → ℝ} {c eta : ℝ}
    (hlower : stabilitySpeedBaseline p < threshold p.χ)
    (hc : threshold p.χ < c) (hketa : kappa c < eta) :
    0 < eta :=
  lt_trans (kappa_pos_of_stabilitySpeedBaseline_lt hlower hc) hketa

theorem eta_lt_one_of_stability_weight_upper_bound
    (p : CMParams) {eta : ℝ}
    (heta : eta < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ))) :
    eta < 1 := by
  have hpow_nonneg : 0 ≤ |p.χ| ^ (1 / 6 : ℝ) :=
    Real.rpow_nonneg (abs_nonneg p.χ) _
  have hden_one : 1 ≤ 1 + |p.χ| ^ (1 / 6 : ℝ) := by
    linarith
  have hbound :
      1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) ≤ (1 : ℝ) := by
    simpa [one_div] using inv_le_one_of_one_le₀ hden_one
  exact lt_of_lt_of_le heta hbound

theorem eta_mem_Ioo_zero_one_of_stability_weight_hypotheses
    {p : CMParams} {threshold : ℝ → ℝ} {c eta : ℝ}
    (hlower : stabilitySpeedBaseline p < threshold p.χ)
    (hc : threshold p.χ < c) (hketa : kappa c < eta)
    (heta_upper : eta < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ))) :
    eta ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨eta_pos_of_stability_weight_hypotheses hlower hc hketa,
    eta_lt_one_of_stability_weight_upper_bound p heta_upper⟩

theorem StableWaveParameterRegime.chi_lt_one
    {p : CMParams} (h : StableWaveParameterRegime p) :
    p.χ < 1 := by
  rcases h with h | h
  · linarith [h.1]
  · exact lt_of_lt_of_le h.2.1 (chiStar_le_one p)

theorem StableWaveParameterRegime.MChi_pos
    {p : CMParams} (h : StableWaveParameterRegime p) :
    0 < MChi p :=
  MChi_pos_of_chi_lt_one p h.chi_lt_one

theorem StableWaveParameterRegime.MChi_nonneg
    {p : CMParams} (h : StableWaveParameterRegime p) :
    0 ≤ MChi p :=
  h.MChi_pos.le

theorem StableWaveParameterRegime.one_le_MChi
    {p : CMParams} (h : StableWaveParameterRegime p) :
    1 ≤ MChi p := by
  rcases h with hneg | hpos
  · simp [MChi_eq_one_of_chi_nonpos p (le_of_lt hneg.1)]
  · exact one_le_MChi_of_chi_nonneg_lt_chiStar p hpos.1 hpos.2.1

theorem Lemma_5_3.weighted_elliptic_perturbation_of_stable_tail_bounds
    (h : Lemma_5_3) {p : CMParams} {c eta : ℝ}
    (hregime : StableWaveParameterRegime p)
    (heta_pos : 0 < eta) (heta_one : eta < 1)
    {u1 u2 : ℝ → ℝ}
    (hu1 : IsCUnifBdd u1) (hu2 : IsCUnifBdd u2)
    (hbound1 : HasWaveUpperTailBound p c u1)
    (hbound2 : HasWaveUpperTailBound p c u2)
    (hclose : Integrable
      (fun x => Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2)) :
    let v := Psi (fun x => u2 x ^ p.γ - u1 x ^ p.γ) 1 1
    let U := fun x => Real.exp (eta * x) * (u2 x - u1 x)
    let V := fun x => Real.exp (eta * x) * v x
    (∫ x : ℝ, |V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta) ^ 2 *
          ∫ x : ℝ, |U x| ^ 2) ∧
      (∫ x : ℝ, |deriv V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta ^ 2) *
          ∫ x : ℝ, |U x| ^ 2) :=
  h.weighted_elliptic_perturbation_of_tail_bounds
    hregime.one_le_MChi heta_pos heta_one hu1 hu2 hbound1 hbound2 hclose

theorem Lemma_5_3.weighted_elliptic_perturbation_of_stable_strict_tail_bounds
    (h : Lemma_5_3) {p : CMParams} {c eta : ℝ}
    (hregime : StableWaveParameterRegime p)
    (heta_pos : 0 < eta) (heta_one : eta < 1)
    {u1 u2 : ℝ → ℝ}
    (hu1 : IsCUnifBdd u1) (hu2 : IsCUnifBdd u2)
    (hbound1 : HasStrictWaveUpperTailBound p c u1)
    (hbound2 : HasStrictWaveUpperTailBound p c u2)
    (hclose : Integrable
      (fun x => Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2)) :
    let v := Psi (fun x => u2 x ^ p.γ - u1 x ^ p.γ) 1 1
    let U := fun x => Real.exp (eta * x) * (u2 x - u1 x)
    let V := fun x => Real.exp (eta * x) * v x
    (∫ x : ℝ, |V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta) ^ 2 *
          ∫ x : ℝ, |U x| ^ 2) ∧
      (∫ x : ℝ, |deriv V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta ^ 2) *
          ∫ x : ℝ, |U x| ^ 2) :=
  h.weighted_elliptic_perturbation_of_stable_tail_bounds hregime
    heta_pos heta_one hu1 hu2
    hbound1.hasWaveUpperTailBound hbound2.hasWaveUpperTailBound hclose

theorem Lemma_5_3.weighted_elliptic_perturbation_of_stability_hypotheses
    (h : Lemma_5_3) {p : CMParams} {threshold : ℝ → ℝ} {c eta : ℝ}
    (hregime : StableWaveParameterRegime p)
    (hlower : stabilitySpeedBaseline p < threshold p.χ)
    (hc : threshold p.χ < c) (hketa : kappa c < eta)
    (heta_upper : eta < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)))
    {u1 u2 : ℝ → ℝ}
    (hu1 : IsCUnifBdd u1) (hu2 : IsCUnifBdd u2)
    (hbound1 : HasStrictWaveUpperTailBound p c u1)
    (hbound2 : HasStrictWaveUpperTailBound p c u2)
    (hclose : Integrable
      (fun x => Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2)) :
    let v := Psi (fun x => u2 x ^ p.γ - u1 x ^ p.γ) 1 1
    let U := fun x => Real.exp (eta * x) * (u2 x - u1 x)
    let V := fun x => Real.exp (eta * x) * v x
    (∫ x : ℝ, |V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta) ^ 2 *
          ∫ x : ℝ, |U x| ^ 2) ∧
      (∫ x : ℝ, |deriv V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta ^ 2) *
          ∫ x : ℝ, |U x| ^ 2) :=
  h.weighted_elliptic_perturbation_of_stable_strict_tail_bounds hregime
    (eta_pos_of_stability_weight_hypotheses hlower hc hketa)
    (eta_lt_one_of_stability_weight_upper_bound p heta_upper)
    hu1 hu2 hbound1 hbound2 hclose

/-- Paper1 Theorem 1.2: weighted stability of traveling waves. -/
def Theorem_1_2 : Prop :=
  ∀ p : CMParams, StableWaveParameterRegime p →
    ∃ cStarStar : ℝ → ℝ,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p < cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
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

theorem Theorem_1_2.threshold_family
    (h : Theorem_1_2) {p : CMParams} (hp : StableWaveParameterRegime p) :
    ∃ cStarStar : ℝ → ℝ,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
        stabilitySpeedBaseline p < cStarStar p.χ := by
  rcases h p hp with ⟨cStarStar, hasymp, hlower, _hconcl⟩
  exact ⟨cStarStar, hasymp, hlower⟩

theorem Theorem_1_2.stability_package
    (h : Theorem_1_2) {p : CMParams} (hp : StableWaveParameterRegime p) :
    ∃ cStarStar : ℝ → ℝ,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p < cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        ∀ η : ℝ, kappa c < η → η < 1 / (1 + |p.χ| ^ (1 / 6)) →
          ∀ u₀ : ℝ → ℝ,
            NonnegativeInitialDatum u₀ →
            StrictlyPositiveAtLeft u₀ →
            WeightedL2InitialCloseness η u₀ U →
            ∃ u v : ℝ → ℝ → ℝ,
              IsGlobalCauchySolutionFrom p u₀ u v ∧
              WeightedL2MovingFrameConvergence η c u U ∧
              UniformMovingFrameConvergence c u U :=
  h p hp

theorem Theorem_1_2.stability_from_wave_initial_package
    (h : Theorem_1_2) {p : CMParams} (hp : StableWaveParameterRegime p) :
    ∃ cStarStar : ℝ → ℝ,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p < cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        IsCUnifBdd U →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        ∀ η : ℝ, kappa c < η → η < 1 / (1 + |p.χ| ^ (1 / 6)) →
          ∃ u v : ℝ → ℝ → ℝ,
            IsGlobalCauchySolutionFrom p U u v ∧
            WeightedL2MovingFrameConvergence η c u U ∧
            UniformMovingFrameConvergence c u U := by
  rcases h.stability_package hp with ⟨cStarStar, hasymp, hlower, hstable⟩
  refine ⟨cStarStar, hasymp, hlower, ?_⟩
  intro c hc U V hTW hU hbound htail η hketa heta
  exact hstable c hc U V hTW hbound htail η hketa heta U
    (IsTravelingWave.nonnegativeInitialDatum hTW hU)
    (IsTravelingWave.strictlyPositiveAtLeft hTW)
    (WeightedL2InitialCloseness.refl η U)

theorem Theorem_1_2.stability_from_second_wave_initial_package
    (h : Theorem_1_2) {p : CMParams} (hp : StableWaveParameterRegime p) :
    ∃ cStarStar : ℝ → ℝ,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p < cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
      ∀ U₁ V₁ U₂ V₂ : ℝ → ℝ,
        IsTravelingWave p c U₁ V₁ →
        IsTravelingWave p c U₂ V₂ →
        IsCUnifBdd U₂ →
        HasStrictWaveUpperTailBound p c U₁ →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U₁) →
        ∀ η : ℝ, kappa c < η → η < 1 / (1 + |p.χ| ^ (1 / 6)) →
          WeightedL2InitialCloseness η U₂ U₁ →
          ∃ u v : ℝ → ℝ → ℝ,
            IsGlobalCauchySolutionFrom p U₂ u v ∧
            WeightedL2MovingFrameConvergence η c u U₁ ∧
            UniformMovingFrameConvergence c u U₁ := by
  rcases h.stability_package hp with ⟨cStarStar, hasymp, hlower, hstable⟩
  refine ⟨cStarStar, hasymp, hlower, ?_⟩
  intro c hc U₁ V₁ U₂ V₂ hTW₁ hTW₂ hU₂ hbound₁ htail₁ η hketa heta hclose
  exact hstable c hc U₁ V₁ hTW₁ hbound₁ htail₁ η hketa heta U₂
    (IsTravelingWave.nonnegativeInitialDatum hTW₂ hU₂)
    (IsTravelingWave.strictlyPositiveAtLeft hTW₂)
    hclose

/-- Paper1 Theorem 1.3: uniqueness of traveling waves with the prescribed right tail. -/
def Theorem_1_3 : Prop :=
  ∀ p : CMParams, StableWaveParameterRegime p →
    ∃ cStarStar : ℝ → ℝ,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p < cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
      ∀ U₁ V₁ U₂ V₂ : ℝ → ℝ,
        IsTravelingWave p c U₁ V₁ →
        IsTravelingWave p c U₂ V₂ →
        HasStrictWaveUpperTailBound p c U₁ →
        HasStrictWaveUpperTailBound p c U₂ →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧
          HasWaveRightTailAsymptotic c κ₁ U₁ ∧
          HasWaveRightTailAsymptotic c κ₁ U₂) →
        (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x)

theorem Theorem_1_3.threshold_family
    (h : Theorem_1_3) {p : CMParams} (hp : StableWaveParameterRegime p) :
    ∃ cStarStar : ℝ → ℝ,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
        stabilitySpeedBaseline p < cStarStar p.χ := by
  rcases h p hp with ⟨cStarStar, hasymp, hlower, _hconcl⟩
  exact ⟨cStarStar, hasymp, hlower⟩

theorem Theorem_1_3.uniqueness_package
    (h : Theorem_1_3) {p : CMParams} (hp : StableWaveParameterRegime p) :
    ∃ cStarStar : ℝ → ℝ,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p < cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
      ∀ U₁ V₁ U₂ V₂ : ℝ → ℝ,
        IsTravelingWave p c U₁ V₁ →
        IsTravelingWave p c U₂ V₂ →
        HasStrictWaveUpperTailBound p c U₁ →
        HasStrictWaveUpperTailBound p c U₂ →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧
          HasWaveRightTailAsymptotic c κ₁ U₁ ∧
          HasWaveRightTailAsymptotic c κ₁ U₂) →
        (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x) :=
  h p hp

theorem Theorem_1_3.uniqueness_at_admissible_threshold
    {p : CMParams} {cStarStar : ℝ → ℝ}
    (hthreshold :
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p < cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
      ∀ U₁ V₁ U₂ V₂ : ℝ → ℝ,
        IsTravelingWave p c U₁ V₁ →
        IsTravelingWave p c U₂ V₂ →
        HasStrictWaveUpperTailBound p c U₁ →
        HasStrictWaveUpperTailBound p c U₂ →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧
          HasWaveRightTailAsymptotic c κ₁ U₁ ∧
          HasWaveRightTailAsymptotic c κ₁ U₂) →
        (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x))
    {c : ℝ} (hc : cStarStar p.χ < c)
    {U₁ V₁ U₂ V₂ : ℝ → ℝ}
    (hTW₁ : IsTravelingWave p c U₁ V₁)
    (hTW₂ : IsTravelingWave p c U₂ V₂)
    (hbound₁ : HasStrictWaveUpperTailBound p c U₁)
    (hbound₂ : HasStrictWaveUpperTailBound p c U₂)
    (htail :
      ∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧
        HasWaveRightTailAsymptotic c κ₁ U₁ ∧
        HasWaveRightTailAsymptotic c κ₁ U₂) :
    (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x) :=
  hthreshold.2.2 c hc U₁ V₁ U₂ V₂
    hTW₁ hTW₂ hbound₁ hbound₂ htail

theorem Theorem_1_3.exists_threshold_with_uniqueness_at_speed
    (h : Theorem_1_3) {p : CMParams} (hp : StableWaveParameterRegime p) :
    ∃ cStarStar : ℝ → ℝ,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p < cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
      ∀ U₁ V₁ U₂ V₂ : ℝ → ℝ,
        IsTravelingWave p c U₁ V₁ →
        IsTravelingWave p c U₂ V₂ →
        HasStrictWaveUpperTailBound p c U₁ →
        HasStrictWaveUpperTailBound p c U₂ →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧
          HasWaveRightTailAsymptotic c κ₁ U₁ ∧
          HasWaveRightTailAsymptotic c κ₁ U₂) →
        (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x) :=
  h.uniqueness_package hp

end

end ShenWork.Paper1
