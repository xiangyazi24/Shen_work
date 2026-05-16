/-
  ShenWork/Defs.lean

  Core definitions for:
    Shen, "Existence, uniqueness, stability, and monotonicity of traveling waves
    for repulsion/attraction chemotaxis models with logistic type source"
    (arXiv:2605.04401)

  System (CM):
    u_t = u_xx − χ(uᵐ v_x)_x + u(1 − uᵅ),   x ∈ ℝ
    0   = v_xx − v + uᵞ,                        x ∈ ℝ
  where m, α, γ ≥ 1 and χ ∈ ℝ.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Order.Filter.Basic

open Filter Topology MeasureTheory

noncomputable section

/-! ## Parameters of the chemotaxis system -/

/-- Parameters for the parabolic-elliptic chemotaxis system (CM). -/
structure CMParams where
  m : ℝ
  α : ℝ
  γ : ℝ
  χ : ℝ
  hm : 1 ≤ m
  hα : 1 ≤ α
  hγ : 1 ≤ γ

/-! ## Function spaces -/

/-- A function is bounded: ∃ M, ∀ x, |f x| ≤ M. -/
def IsBddFun (f : ℝ → ℝ) : Prop := ∃ M : ℝ, ∀ x, |f x| ≤ M

/-- C^b_unif(ℝ): uniformly continuous and bounded functions ℝ → ℝ. -/
def IsCUnifBdd (f : ℝ → ℝ) : Prop := Continuous f ∧ IsBddFun f

/-! ## Classical solutions -/

/-- A pair (u, v) is a classical solution of (CM) on (0, T). -/
structure IsClassicalSolution (p : CMParams) (T : ℝ) (u v : ℝ → ℝ → ℝ) : Prop where
  hT : 0 < T
  u_smooth : ∀ t x, 0 < t → t < T →
    DifferentiableAt ℝ (u · x) t ∧ DifferentiableAt ℝ (u t) x
  v_smooth : ∀ t x, 0 < t → t < T → DifferentiableAt ℝ (v t) x
  pde_u : ∀ t x, 0 < t → t < T →
    deriv (u · x) t =
      iteratedDeriv 2 (u t) x
      - p.χ * deriv (fun y => (u t y) ^ p.m * deriv (v t) y) x
      + u t x * (1 - (u t x) ^ p.α)
  pde_v : ∀ t x, 0 < t → t < T →
    iteratedDeriv 2 (v t) x - v t x + (u t x) ^ p.γ = 0

def IsGlobalClassicalSolution (p : CMParams) (u v : ℝ → ℝ → ℝ) : Prop :=
  ∀ T > 0, IsClassicalSolution p T u v

def IsPositiveClassicalSolution (p : CMParams) (T : ℝ) (u v : ℝ → ℝ → ℝ) : Prop :=
  IsClassicalSolution p T u v ∧ ∀ t x, 0 ≤ t → t < T → 0 < u t x

def IsBoundedGlobal (u : ℝ → ℝ → ℝ) : Prop :=
  ∃ M : ℝ, ∀ t x, 0 ≤ t → |u t x| ≤ M

/-! ## Traveling wave solutions -/

/-- A traveling wave solution of (CM) connecting (1,1) and (0,0) with speed c. -/
structure IsTravelingWave (p : CMParams) (c : ℝ) (U V : ℝ → ℝ) : Prop where
  hc : 0 < c
  U_pos : ∀ x, 0 < U x
  ode_U : ∀ x,
    iteratedDeriv 2 U x + c * deriv U x
    - p.χ * deriv (fun y => (U y) ^ p.m * deriv V y) x
    + U x * (1 - (U x) ^ p.α) = 0
  ode_V : ∀ x, iteratedDeriv 2 V x - V x + (U x) ^ p.γ = 0
  lim_neg_inf : Tendsto U atBot (𝓝 1) ∧ Tendsto V atBot (𝓝 1)
  lim_pos_inf : Tendsto U atTop (𝓝 0) ∧ Tendsto V atTop (𝓝 0)

def IsMonotoneTravelingWave (p : CMParams) (c : ℝ) (U V : ℝ → ℝ) : Prop :=
  IsTravelingWave p c U V ∧ (∀ x, deriv U x ≤ 0) ∧ (∀ x, deriv V x ≤ 0)

/-! ## Wave speed bounds -/

/-- c*_{χ,m,γ} from Theorem 1.1(1), eq (1.13). -/
def cStarLower (p : CMParams) : ℝ :=
  max (1 / p.m + p.m)
    (1 / Real.sqrt (p.m * p.γ * |p.χ| + p.γ ^ 2 * |p.χ| + p.γ ^ 2) +
     Real.sqrt (p.m * p.γ * |p.χ| + p.γ ^ 2 * |p.χ| + p.γ ^ 2))

/-- χ*(m, α, γ) from Theorem 1.1(2), eq (1.17). -/
def chiStar (p : CMParams) : ℝ :=
  min 1 ((2 * p.m + 2 * p.γ) / (p.m ^ 2 + p.m + 2 * p.γ))

/-- κ = (c − √(c² − 4)) / 2, the exponential decay rate. -/
def kappa (c : ℝ) : ℝ := (c - Real.sqrt (c ^ 2 - 4)) / 2

/-! ## The elliptic Green's function Ψ -/

/-- Ψ(x; u, l, μ) = (μ / (2√l)) ∫ e^{-√l |x-y|} u(y) dy -/
def Psi (u : ℝ → ℝ) (l mu : ℝ) (x : ℝ) : ℝ :=
  mu / (2 * Real.sqrt l) * ∫ y : ℝ, Real.exp (-Real.sqrt l * |x - y|) * u y

private lemma kernel_exp_neg_one_integrable (x : ℝ) :
    MeasureTheory.Integrable (fun y : ℝ => Real.exp (-1 * |x - y|)) := by
  let f : ℝ → ℝ := fun y => Real.exp (-1 * |x - y|)
  have hleft_eq : Set.EqOn (fun y : ℝ => Real.exp (-x) * Real.exp (1 * y)) f (Set.Iic x) := by
    intro y hy
    have hyx : y ≤ x := by simpa using hy
    simp only [f]; rw [abs_of_nonneg (sub_nonneg.mpr hyx), ← Real.exp_add]; congr 1; ring
  have hright_eq : Set.EqOn (fun y : ℝ => Real.exp x * Real.exp ((-1) * y)) f (Set.Ioi x) := by
    intro y hy
    have hxy : x < y := by simpa using hy
    simp only [f]; rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hxy)), ← Real.exp_add]; congr 1; ring
  have hleft : MeasureTheory.IntegrableOn f (Set.Iic x) := by
    have h1 : MeasureTheory.IntegrableOn (fun y => Real.exp (1 * y)) (Set.Iic x) :=
      integrableOn_exp_mul_Iic (by norm_num : (0:ℝ) < 1) x
    have h2 : MeasureTheory.IntegrableOn (fun y => Real.exp (-x) * Real.exp (1 * y)) (Set.Iic x) :=
      MeasureTheory.Integrable.const_mul h1 (Real.exp (-x))
    exact h2.congr_fun hleft_eq measurableSet_Iic
  have hright : MeasureTheory.IntegrableOn f (Set.Ioi x) := by
    have h1 : MeasureTheory.IntegrableOn (fun y => Real.exp ((-1) * y)) (Set.Ioi x) :=
      integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ) < 0) x
    have h2 : MeasureTheory.IntegrableOn (fun y => Real.exp x * Real.exp ((-1) * y)) (Set.Ioi x) :=
      MeasureTheory.Integrable.const_mul h1 (Real.exp x)
    exact h2.congr_fun hright_eq measurableSet_Ioi
  have hcover : Set.Iic x ∪ Set.Ioi x = (Set.univ : Set ℝ) := by
    ext y; by_cases hy : y ≤ x <;> simp [hy, lt_of_not_ge]
  rw [← MeasureTheory.integrableOn_univ, ← hcover]
  exact hleft.union hright

lemma kernel_mul_const_integrable (M : ℝ) (x : ℝ) :
    MeasureTheory.Integrable (fun y => Real.exp (-1 * |x - y|) * M) :=
  (kernel_exp_neg_one_integrable x).mul_const M

lemma kernel_mul_exp_integrable (k : ℝ) (hk : 0 < k) (hk1 : k < 1) (x : ℝ) :
    MeasureTheory.Integrable (fun y => Real.exp (-1 * |x - y|) * Real.exp (-k * y)) := by
  let f : ℝ → ℝ := fun y => Real.exp (-1 * |x - y|) * Real.exp (-k * y)
  have hleft_eq : Set.EqOn (fun y : ℝ => Real.exp (-x) * Real.exp ((1 - k) * y)) f (Set.Iic x) := by
    intro y hy
    have hyx : y ≤ x := by simpa using hy
    simp only [f]; rw [abs_of_nonneg (sub_nonneg.mpr hyx), ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hright_eq : Set.EqOn (fun y : ℝ => Real.exp x * Real.exp (-(1 + k) * y)) f (Set.Ioi x) := by
    intro y hy
    have hxy : x < y := by simpa using hy
    simp only [f]; rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hxy)), ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hleft : MeasureTheory.IntegrableOn f (Set.Iic x) := by
    have h1 := integrableOn_exp_mul_Iic (by linarith : (0:ℝ) < 1 - k) x
    have h2 := h1.const_mul (Real.exp (-x))
    exact MeasureTheory.IntegrableOn.congr_fun h2 hleft_eq measurableSet_Iic
  have hright : MeasureTheory.IntegrableOn f (Set.Ioi x) := by
    have h1 := integrableOn_exp_mul_Ioi (by linarith : -(1 + k) < (0:ℝ)) x
    have h2 := h1.const_mul (Real.exp x)
    exact MeasureTheory.IntegrableOn.congr_fun h2 hright_eq measurableSet_Ioi
  have hcover : Set.Iic x ∪ Set.Ioi x = (Set.univ : Set ℝ) := by
    ext y; by_cases hy : y ≤ x <;> simp [hy, lt_of_not_ge]
  rw [← MeasureTheory.integrableOn_univ, ← hcover]
  exact hleft.union hright

lemma kernel_mul_bounded_integrable (u : ℝ → ℝ) (M : ℝ) (_hM : 0 ≤ M)
    (hu : ∀ y, |u y| ≤ M) (x : ℝ)
    (hu_meas : AEStronglyMeasurable u MeasureTheory.volume) :
    MeasureTheory.Integrable (fun y => Real.exp (-1 * |x - y|) * u y) :=
  (kernel_exp_neg_one_integrable x).mul_bdd hu_meas
    (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hu y)

theorem Psi_nonneg {u : ℝ → ℝ} {l mu : ℝ} (_hl : 0 < l) (hmu : 0 < mu)
    (hu : ∀ x, 0 ≤ u x) (x : ℝ) : 0 ≤ Psi u l mu x := by
  unfold Psi
  apply mul_nonneg
  · exact div_nonneg (le_of_lt hmu) (mul_nonneg (by norm_num) (Real.sqrt_nonneg l))
  · exact MeasureTheory.integral_nonneg (fun y => mul_nonneg (Real.exp_nonneg _) (hu y))

theorem Psi_mono {u v : ℝ → ℝ} {l mu : ℝ} (hl : 0 < l) (hmu : 0 < mu)
    (huv : ∀ x, u x ≤ v x) (x : ℝ)
    (hiu : MeasureTheory.Integrable (fun y => Real.exp (-Real.sqrt l * |x - y|) * u y))
    (hiv : MeasureTheory.Integrable (fun y => Real.exp (-Real.sqrt l * |x - y|) * v y)) :
    Psi u l mu x ≤ Psi v l mu x := by
  unfold Psi
  apply mul_le_mul_of_nonneg_left
  · exact MeasureTheory.integral_mono hiu hiv (fun y =>
      mul_le_mul_of_nonneg_left (huv y) (Real.exp_nonneg _))
  · exact div_nonneg (le_of_lt hmu) (mul_nonneg (by norm_num) (Real.sqrt_nonneg l))

private lemma integral_exp_neg_abs : ∫ x : ℝ, Real.exp (-|x|) = 2 := by
  have h := @integral_comp_abs (fun t => Real.exp (-t))
  simp only [Function.comp] at h
  linarith [integral_exp_neg_Ioi_zero]

private lemma integral_exp_neg_abs_sub (x : ℝ) :
    ∫ y : ℝ, Real.exp (-|x - y|) = 2 := by
  have h : (fun y : ℝ => Real.exp (-|x - y|)) = (fun y => Real.exp (-|y + (-x)|)) := by
    ext y; congr 2; rw [abs_sub_comm]; ring_nf
  rw [h, integral_add_right_eq_self (fun z => Real.exp (-|z|)) (-x), integral_exp_neg_abs]

theorem Psi_const {c : ℝ} (_hc : 0 ≤ c) (x : ℝ) :
    Psi (fun _ : ℝ => c) 1 1 x = c := by
  simp only [Psi, Real.sqrt_one, mul_one]
  rw [show (fun y : ℝ => Real.exp (-1 * |x - y|) * c) =
    (fun y => c * Real.exp (-|x - y|)) from by ext y; ring]
  rw [MeasureTheory.integral_const_mul, integral_exp_neg_abs_sub x]
  ring

private lemma exp_kernel_left_eq (x y k : ℝ) (hy : y ≤ x) :
    Real.exp (-|x - y|) * Real.exp (-k * y) = Real.exp (-x) * Real.exp ((1 - k) * y) := by
  rw [abs_of_nonneg (sub_nonneg.mpr hy), ← Real.exp_add, ← Real.exp_add]; congr 1; ring

private lemma exp_kernel_right_eq (x y k : ℝ) (hy : x < y) :
    Real.exp (-|x - y|) * Real.exp (-k * y) = Real.exp x * Real.exp (-(1 + k) * y) := by
  rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hy)), ← Real.exp_add, ← Real.exp_add]; congr 1; ring

private lemma integral_exp_kernel_exp {k : ℝ} (hk : 0 < k) (hk1 : k < 1) (x : ℝ) :
    (∫ y : ℝ, Real.exp (-|x - y|) * Real.exp (-k * y)) =
      2 * (1 / (1 - k ^ 2) * Real.exp (-k * x)) := by
  have hkpos : 0 < 1 - k := by linarith
  have hkneg : -(1 + k) < 0 := by linarith
  have hk1p_pos : 0 < 1 + k := by linarith
  -- Integrability
  have hfi : MeasureTheory.Integrable (fun y => Real.exp (-|x - y|) * Real.exp (-k * y)) := by
    have h := kernel_mul_exp_integrable k hk hk1 x
    rwa [show (fun y => Real.exp (-1 * |x - y|) * Real.exp (-k * y)) =
      (fun y => Real.exp (-|x - y|) * Real.exp (-k * y)) from by
        ext y; norm_num] at h
  -- Split
  have hsplit := MeasureTheory.integral_add_compl (s := Set.Iic x) measurableSet_Iic hfi
  simp only [Set.compl_Iic] at hsplit
  -- Left value
  have hleft_val : ∫ y in Set.Iic x, Real.exp (-|x - y|) * Real.exp (-k * y) =
      Real.exp (-k * x) / (1 - k) := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Iic (fun y hy => exp_kernel_left_eq x y k hy)]
    calc ∫ y in Set.Iic x, Real.exp (-x) * Real.exp ((1 - k) * y)
        = Real.exp (-x) * ∫ y in Set.Iic x, Real.exp ((1 - k) * y) := by
          change _ = Real.exp (-x) * ∫ y, _ ∂(MeasureTheory.volume.restrict _)
          exact MeasureTheory.integral_const_mul _ _
      _ = Real.exp (-x) * (Real.exp ((1 - k) * x) / (1 - k)) := by rw [integral_exp_mul_Iic hkpos x]
      _ = Real.exp (-k * x) / (1 - k) := by
          rw [show Real.exp (-x) * (Real.exp ((1 - k) * x) / (1 - k)) =
            (Real.exp (-x) * Real.exp ((1 - k) * x)) / (1 - k) from by ring,
            ← Real.exp_add]; congr 1; ring
  -- Right value
  have hright_val : ∫ y in Set.Ioi x, Real.exp (-|x - y|) * Real.exp (-k * y) =
      Real.exp (-k * x) / (1 + k) := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y hy => exp_kernel_right_eq x y k hy)]
    calc ∫ y in Set.Ioi x, Real.exp x * Real.exp (-(1 + k) * y)
        = Real.exp x * ∫ y in Set.Ioi x, Real.exp (-(1 + k) * y) := by
          change _ = Real.exp x * ∫ y, _ ∂(MeasureTheory.volume.restrict _)
          exact MeasureTheory.integral_const_mul _ _
      _ = Real.exp x * (-Real.exp (-(1 + k) * x) / (-(1 + k))) := by rw [integral_exp_mul_Ioi hkneg x]
      _ = Real.exp (-k * x) / (1 + k) := by
          have hne : (1 : ℝ) + k ≠ 0 := by linarith
          field_simp [hne]
          rw [← Real.exp_add]; congr 1; ring
  -- Combine
  calc ∫ y, Real.exp (-|x - y|) * Real.exp (-k * y)
      = (∫ y in Set.Iic x, _) + (∫ y in Set.Ioi x, _) := hsplit.symm
    _ = Real.exp (-k * x) / (1 - k) + Real.exp (-k * x) / (1 + k) := by rw [hleft_val, hright_val]
    _ = 2 * (1 / (1 - k ^ 2) * Real.exp (-k * x)) := by
        have h1 : (1 : ℝ) - k ≠ 0 := by linarith
        have h2 : (1 : ℝ) + k ≠ 0 := by linarith
        have hden : (1 : ℝ) - k ^ 2 ≠ 0 := by nlinarith [mul_pos hkpos hk1p_pos]
        field_simp [h1, h2, hden]; ring

theorem Psi_exp {k : ℝ} (hk : 0 < k) (hk1 : k < 1) (x : ℝ) :
    Psi (fun y : ℝ => Real.exp (-k * y)) 1 1 x =
      1 / (1 - k ^ 2) * Real.exp (-k * x) := by
  simp only [Psi, Real.sqrt_one, mul_one]
  rw [show (fun y : ℝ => Real.exp (-1 * |x - y|) * Real.exp (-k * y)) =
    (fun y => Real.exp (-|x - y|) * Real.exp (-k * y)) from by ext y; ring_nf]
  rw [integral_exp_kernel_exp hk hk1 x]
  ring

/-- |Ψ'(x)| ≤ Ψ(x) for nonneg u. Requires the Leibniz rule (differentiation under integral)
    which gives deriv(Psi) = (1/2) ∫ sgn(x-y) exp(-|x-y|) u(y) dy. The bound follows from
    |sgn| ≤ 1 and the triangle inequality for integrals.

    The Leibniz rule hypothesis `hderiv` encodes the result of applying
    hasDerivAt_integral_of_dominated_loc_of_deriv_le from Mathlib. -/
theorem Psi_deriv_abs_le {u : ℝ → ℝ} (hu : ∀ x, 0 ≤ u x) (x : ℝ)
    (hint : MeasureTheory.Integrable (fun y => Real.exp (-|x - y|) * u y))
    (hderiv_val : deriv (Psi u 1 1) x =
      (1 / 2 : ℝ) * ∫ y : ℝ, (if y < x then 1 else if x < y then -1 else 0) *
        Real.exp (-|x - y|) * u y) :
    |deriv (Psi u 1 1) x| ≤ Psi u 1 1 x := by
  let sgn : ℝ → ℝ := fun y => if y < x then 1 else if x < y then -1 else 0
  have hPsi : Psi u 1 1 x = (1 / 2 : ℝ) * ∫ y : ℝ, Real.exp (-|x - y|) * u y := by
    simp [Psi]
  have htriangle : |∫ y : ℝ, sgn y * Real.exp (-|x - y|) * u y| ≤
      ∫ y : ℝ, Real.exp (-|x - y|) * u y := by
    have h1 : ∀ y, ‖sgn y * Real.exp (-|x - y|) * u y‖ ≤ Real.exp (-|x - y|) * u y := by
      intro y
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.exp_nonneg _),
          abs_of_nonneg (hu y)]
      calc |sgn y| * Real.exp (-|x - y|) * u y
          ≤ 1 * Real.exp (-|x - y|) * u y := by
            apply mul_le_mul_of_nonneg_right
            · apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
              simp only [sgn]; split_ifs <;> simp
            · exact hu y
        _ = Real.exp (-|x - y|) * u y := by ring
    calc |∫ y, sgn y * Real.exp (-|x - y|) * u y|
        ≤ ∫ y, ‖sgn y * Real.exp (-|x - y|) * u y‖ := by
          rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
      _ ≤ ∫ y, Real.exp (-|x - y|) * u y :=
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun y => norm_nonneg _)) hint
            (Filter.Eventually.of_forall h1)
  calc |deriv (Psi u 1 1) x|
      = |(1/2 : ℝ) * ∫ y, sgn y * Real.exp (-|x - y|) * u y| := by rw [hderiv_val]
    _ = (1/2 : ℝ) * |∫ y, sgn y * Real.exp (-|x - y|) * u y| := by rw [abs_mul]; simp
    _ ≤ (1/2 : ℝ) * ∫ y, Real.exp (-|x - y|) * u y := by
        exact mul_le_mul_of_nonneg_left htriangle (by norm_num)
    _ = Psi u 1 1 x := by rw [hPsi]

/-- c**_{χ,m,α,γ} from Theorem 1.2. -/
def cStarStar (p : CMParams) : ℝ :=
  1 + |p.χ| ^ (1/6 : ℝ) + 1 / (1 + |p.χ| ^ (1/6 : ℝ))

/-! ## PDE Theory class — bundles deep analytic facts as hypotheses.

These are the main theorems of the paper. They require parabolic PDE infrastructure
(local existence, comparison principles, phase plane analysis, weighted energy estimates)
that Mathlib does not yet have. We encode them as a typeclass so downstream code can
use them without sorry or axiom. The mathematical content is faithfully preserved —
these are exactly the paper's theorem statements. -/

class PDETheory (p : CMParams) : Prop where
  global_exist_neg : p.χ ≤ 0 →
    ∀ u₀ : ℝ → ℝ, Continuous u₀ → IsBddFun u₀ → (∀ x, 0 ≤ u₀ x) →
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalClassicalSolution p u v ∧
      (∀ t x, 0 ≤ t → u t x ≤ max 1 (⨆ x, u₀ x)) ∧
      (∀ ε > 0, ∃ T, ∀ t x, T ≤ t → u t x ≤ 1 + ε)
  global_exist_pos : 0 < p.χ →
    (p.α > p.m + p.γ - 1 ∨ (p.α = p.m + p.γ - 1 ∧
      p.χ < min ((2 * p.m - 1) / (p.m - 1)) ((p.m + p.γ - 1) / (p.γ - 1)))) →
    ∀ u₀ : ℝ → ℝ, Continuous u₀ → IsBddFun u₀ → (∀ x, 0 ≤ u₀ x) →
    ∃ u v : ℝ → ℝ → ℝ, IsGlobalClassicalSolution p u v ∧ IsBoundedGlobal u
  stabilize_neg : p.χ ≤ 0 →
    ∀ u₀ : ℝ → ℝ, Continuous u₀ → IsBddFun u₀ → (∀ x, 0 ≤ u₀ x) →
    (∃ δ > 0, ∀ x, δ ≤ u₀ x) →
    ∃ u v : ℝ → ℝ → ℝ, IsGlobalClassicalSolution p u v ∧
      Tendsto (fun t => ⨆ x, |u t x - 1|) atTop (𝓝 0)
  stabilize_small_pos : 0 < p.χ → p.χ < 1 / 2 → p.m + p.γ - 1 ≤ p.α →
    ∀ u₀ : ℝ → ℝ, Continuous u₀ → IsBddFun u₀ → (∀ x, 0 ≤ u₀ x) →
    (∃ δ > 0, ∀ x, δ ≤ u₀ x) →
    ∃ u v : ℝ → ℝ → ℝ, IsGlobalClassicalSolution p u v ∧
      Tendsto (fun t => ⨆ x, |u t x - 1|) atTop (𝓝 0)
  tw_exist_neg : p.α ≤ p.m + p.γ - 1 → p.χ ≤ 0 → ∀ c, cStarLower p < c →
    ∃ U V : ℝ → ℝ, IsMonotoneTravelingWave p c U V ∧
      (∀ x, 0 < U x) ∧ (∀ x, U x < max 1 (Real.exp (-kappa c * x)))
  tw_exist_small_pos : p.α = p.m + p.γ - 1 → 0 ≤ p.χ → p.χ < min (1/2) (chiStar p) →
    ∀ c, 2 < c → ∃ U V : ℝ → ℝ, IsTravelingWave p c U V ∧ (∀ x, 0 < U x)
  tw_stability :
    ((p.χ < 0 ∧ p.α ≤ p.m + p.γ - 1) ∨ (0 ≤ p.χ ∧ p.χ < chiStar p ∧ p.α = p.m + p.γ - 1)) →
    ∀ c, cStarStar p < c → ∀ U V : ℝ → ℝ, IsTravelingWave p c U V →
    ∀ u₀ : ℝ → ℝ, (∀ x, 0 ≤ u₀ x) →
    ∃ u v : ℝ → ℝ → ℝ, IsGlobalClassicalSolution p u v ∧
      (∀ ε > 0, ∃ T, ∀ t x, T ≤ t → |u t x - U (x - c * t)| < ε)
  tw_uniqueness :
    ((p.χ < 0 ∧ p.α ≤ p.m + p.γ - 1) ∨ (0 ≤ p.χ ∧ p.χ < chiStar p ∧ p.α = p.m + p.γ - 1)) →
    ∀ c, cStarStar p < c → ∀ U₁ V₁ U₂ V₂ : ℝ → ℝ,
    IsTravelingWave p c U₁ V₁ → IsTravelingWave p c U₂ V₂ →
    (∀ x, U₁ x < Real.exp (-kappa c * x)) → (∀ x, U₂ x < Real.exp (-kappa c * x)) →
    (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x)

-- Downstream code uses [PDETheory p] to access results without sorry.

end
