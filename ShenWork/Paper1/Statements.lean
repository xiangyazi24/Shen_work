/-
  Statement layer for Shen,
  "Existence, uniqueness, stability, and monotonicity of traveling waves for
  repulsion/attraction chemotaxis models with logistic type source".

  The declarations below formalize the paper-level targets as propositions.
  They are not proofs of the paper theorems.
-/
import ShenWork.PDE.LeibnizRule

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

def frozenElliptic (p : CMParams) (u : ℝ → ℝ) : ℝ → ℝ :=
  fun x => Psi (fun y => (u y) ^ p.γ) 1 1 x

def frozenWaveOperator (p : CMParams) (c : ℝ) (u W : ℝ → ℝ) : ℝ → ℝ :=
  fun x =>
    iteratedDeriv 2 W x + c * deriv W x
      - p.χ *
        deriv (fun y => (W y) ^ p.m * deriv (frozenElliptic p u) y) x
      + W x * (1 - (W x) ^ p.α)

def IsFrozenSuperSolution (p : CMParams) (c : ℝ) (u W : ℝ → ℝ) : Prop :=
  ∀ x, frozenWaveOperator p c u W x ≤ 0

def IsFrozenSubSolutionOn (p : CMParams) (c : ℝ) (u W : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, 0 ≤ frozenWaveOperator p c u W x

def upperBarrier (κ M : ℝ) : ℝ → ℝ :=
  fun x => min M (Real.exp (-κ * x))

theorem upperBarrier_le_M (κ M x : ℝ) :
    upperBarrier κ M x ≤ M :=
  min_le_left _ _

theorem upperBarrier_le_exp (κ M x : ℝ) :
    upperBarrier κ M x ≤ Real.exp (-κ * x) :=
  min_le_right _ _

theorem upperBarrier_nonneg {κ M : ℝ} (hM : 0 ≤ M) (x : ℝ) :
    0 ≤ upperBarrier κ M x :=
  le_min hM (Real.exp_pos _).le

theorem upperBarrier_pos {κ M : ℝ} (hM : 0 < M) (x : ℝ) :
    0 < upperBarrier κ M x :=
  lt_min hM (Real.exp_pos _)

def lowerBarrierRaw (κ κtilde D : ℝ) : ℝ → ℝ :=
  fun x => Real.exp (-κ * x) - D * Real.exp (-κtilde * x)

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

def lowerBarrierPlateau (κ κtilde D : ℝ) : ℝ → ℝ :=
  fun x =>
    if x ≤ lowerBarrierXPlus κ κtilde D then
      lowerBarrierRaw κ κtilde D (lowerBarrierXPlus κ κtilde D)
    else
      lowerBarrierRaw κ κtilde D x

def InWaveTrapSet (κ M : ℝ) (u : ℝ → ℝ) : Prop :=
  IsCUnifBdd u ∧ ∀ x, 0 ≤ u x ∧ u x ≤ upperBarrier κ M x

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

structure SubsolutionConstants where
  K : ℝ
  D : ℝ
  d : ℝ
  K_pos : 0 < K
  D_pos : 0 < D
  d_pos : 0 < d

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
        ∃ C : SubsolutionConstants,
          ∀ D : ℝ, C.D < D →
            ∀ u : ℝ → ℝ, InWaveTrapSet κ M u →
              IsFrozenSubSolutionOn p c u (lowerBarrierRaw κ κtilde D)
                (Set.Ioi (lowerBarrierXMinus κ κtilde D)) ∧
              ∀ d : ℝ, 0 < d → d ≤ C.d →
                IsFrozenSubSolutionOn p c u (fun _ => d) Set.univ

def MChi (p : CMParams) : ℝ :=
  if p.χ ≤ 0 then 1 else (1 / (1 - p.χ)) ^ (1 / p.α)

theorem MChi_eq_one_of_chi_nonpos (p : CMParams) (hχ : p.χ ≤ 0) :
    MChi p = 1 := by
  simp [MChi, hχ]

theorem MChi_eq_rpow_of_chi_pos (p : CMParams) (hχ : 0 < p.χ) :
    MChi p = (1 / (1 - p.χ)) ^ (1 / p.α) := by
  simp [MChi, not_le.mpr hχ]

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

theorem one_le_MChi_of_chi_nonneg_lt_chiStar
    (p : CMParams) (hχ_nonneg : 0 ≤ p.χ) (hχ : p.χ < chiStar p) :
    1 ≤ MChi p :=
  one_le_MChi_of_chi_nonneg_lt_one p hχ_nonneg
    (lt_of_lt_of_le hχ (chiStar_le_one p))

def HasWaveUpperTailBound (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop :=
  ∀ x, 0 < U x ∧ U x ≤ min (MChi p) (Real.exp (-(kappa c) * x))

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

def Lemma_5_2 : Prop :=
  ∀ p : CMParams, ∀ c : ℝ,
    c > max (p.γ + p.γ⁻¹) (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)) →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
          ∃ B > 0, ∀ x, deriv U x / U x ≤ B

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
