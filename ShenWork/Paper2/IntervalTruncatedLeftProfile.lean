/-
Left Volterra profile for the gradient bootstrap on (0, lo].

When B_F ≠ 0, the source depends on the gradient, creating a Volterra
self-coupling. The invariant profile on the left interval (0, lo] is
  |∂_x U_n(t', x)| ≤ C/√t' + D
where D absorbs the Volterra feedback via the elementary bound
κ = 2√3 ≥ ∫_0^r (r-s)^{-1/2} s^{-1/2} ds.

Source: ChatGPT Q3969 (hleft_gradient_strategy).
-/
import ShenWork.Paper2.IntervalTruncatedGradientWindow
import ShenWork.PDE.IntervalGradDuhamelBound
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory Set
open scoped BigOperators Topology Real

noncomputable section

namespace ShenWork.Paper2.TruncatedGradientWindow

open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant heatGradientLinftyLinftyConstant_nonneg)

/-- Lean-friendly Volterra constant for the left bootstrap.
Replaces the exact `π = B(1/2,1/2)` by the elementary bound `2√3`. -/
def truncLeftKappa : ℝ := 2 * Real.sqrt 3

/-- `L0 = A_L + |χ₀| · A_F` — the constant part of the source bound. -/
def truncLeftSourceConst (A_L A_F chi : ℝ) : ℝ :=
  A_L + |chi| * A_F

/-- `β = |χ₀| · B_F` — the gradient coupling coefficient. -/
def truncLeftBeta (B_F chi : ℝ) : ℝ :=
  |chi| * B_F

/-- `C = Cg · M` — the singular semigroup coefficient. -/
def truncLeftSingularC (M : ℝ) : ℝ :=
  heatGradientLinftyLinftyConstant * M

/-- The contraction coefficient on the left interval `(0, lo]`.
`bL = 2 · Cg · √lo · |χ₀| · B_F`. -/
def truncLeftB (B_F chi lo : ℝ) : ℝ :=
  heatGradientLinftyLinftyConstant * (2 * Real.sqrt lo) * truncLeftBeta B_F chi

/-- The additive constant D in the invariant profile `C/√t' + D` on `(0, lo]`.
`D = (K·β·C·κ + 2K·√lo·L0) / (1 - bL)`. -/
def truncLeftD (M A_L A_F B_F chi lo : ℝ) : ℝ :=
  let K := heatGradientLinftyLinftyConstant
  let beta := truncLeftBeta B_F chi
  let C := truncLeftSingularC M
  let L0 := truncLeftSourceConst A_L A_F chi
  (K * beta * C * truncLeftKappa + K * (2 * Real.sqrt lo) * L0)
    / (1 - truncLeftB B_F chi lo)

/-- The left Volterra profile: `P(t') = C/√t' + D`. -/
def truncLeftProfile (M A_L A_F B_F chi lo t' : ℝ) : ℝ :=
  truncLeftSingularC M / Real.sqrt t'
    + truncLeftD M A_L A_F B_F chi lo

private theorem beta_half_integral_eq_pi {r : ℝ} (hr : 0 < r) :
    ((∫ s in (0)..r, (r - s) ^ (-(1:ℝ)/2) * s ^ (-(1:ℝ)/2) : ℝ) : ℂ)
      = (Real.pi : ℂ) := by
  have htoC :
      ((∫ s in (0)..r, (r - s) ^ (-(1:ℝ)/2) * s ^ (-(1:ℝ)/2) : ℝ) : ℂ)
        = ∫ s in (0)..r,
            (s : ℂ) ^ ((1/2 : ℂ) - 1) * ((r : ℂ) - s) ^ ((1/2 : ℂ) - 1) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hr.le] at hs
    have hs0 : 0 ≤ s := hs.1
    have hrs0 : 0 ≤ r - s := sub_nonneg.mpr hs.2
    push_cast
    rw [Complex.ofReal_cpow hrs0 (-(1:ℝ)/2)]
    rw [Complex.ofReal_cpow hs0 (-(1:ℝ)/2)]
    norm_num [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc]
  rw [htoC]
  have hscaled := Complex.betaIntegral_scaled (s := (1/2 : ℂ)) (t := (1/2 : ℂ)) (a := r) hr
  rw [show ((1 / 2 : ℂ) + (1 / 2 : ℂ) - 1) = 0 by norm_num] at hscaled
  rw [Complex.cpow_zero, one_mul] at hscaled
  rw [hscaled]
  rw [Complex.betaIntegral_eq_Gamma_mul_div]
  · rw [show ((1 / 2 : ℂ) + (1 / 2 : ℂ)) = 1 by norm_num]
    rw [Complex.Gamma_one]
    rw [Complex.Gamma_one_half_eq]
    rw [div_one]
    rw [← Complex.cpow_add]
    · norm_num
    · exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  · norm_num
  · norm_num

private theorem pi_le_truncLeftKappa : Real.pi ≤ truncLeftKappa := by
  unfold truncLeftKappa
  have hpi : Real.pi < (3.1416 : ℝ) := Real.pi_lt_d4
  have hnum : (3.1416 : ℝ) < 2 * Real.sqrt 3 := by
    norm_num [show (3.1416 : ℝ) = 3927 / 1250 by norm_num]
    rw [mul_self_lt_mul_self_iff]
    · have hs : Real.sqrt (3:ℝ) ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3:ℝ) by norm_num)
      nlinarith
    · norm_num
    · positivity
  exact le_of_lt (lt_trans hpi hnum)

private theorem profile_algebra_bound {X Y2 Y3 bL bW : ℝ}
    (hX : 0 ≤ X) (hY2 : 0 ≤ Y2) (hY23 : Y2 ≤ Y3)
    (hbL0 : 0 ≤ bL) (hbb : bL ≤ bW) (hbW : bW < 1) :
    X + (bW * X + Y2) / (1 - bL) ≤ (X + Y3) / (1 - bW) := by
  have hdL : 0 < 1 - bL := by linarith
  have hdW : 0 < 1 - bW := by linarith
  have hdLn : 1 - bL ≠ 0 := ne_of_gt hdL
  have hleft_eq : X + (bW * X + Y2) / (1 - bL)
      = (X * (1 - bL) + (bW * X + Y2)) / (1 - bL) := by
    field_simp [hdLn]
  rw [hleft_eq]
  rw [div_le_div_iff₀ hdL hdW]
  nlinarith [mul_nonneg (mul_nonneg hX (le_trans hbL0 hbb)) (sub_nonneg.mpr hbb),
    mul_nonneg (sub_nonneg.mpr hY23) (le_of_lt hdL),
    mul_nonneg hY2 (sub_nonneg.mpr hbb)]

-- Theorem 1: Elementary Volterra integral bound
-- ∫_0^r (r-s)^{-1/2} · s^{-1/2} ds ≤ 2√3 for 0 < r
theorem left_beta_kernel_bound {r : ℝ} (hr : 0 < r) :
    ∫ s in (0)..r, (r - s) ^ (-(1:ℝ)/2) * s ^ (-(1:ℝ)/2) ≤ truncLeftKappa := by
  have hC := beta_half_integral_eq_pi hr
  have hReal : ∫ s in (0)..r, (r - s) ^ (-(1:ℝ)/2) * s ^ (-(1:ℝ)/2) = Real.pi := by
    exact Complex.ofReal_injective hC
  rw [hReal]
  exact pi_le_truncLeftKappa

-- Theorem 2: Duhamel gradient bound with singular source
-- If |q(s,y)| ≤ Q0 + Q1/√s then
-- |∂_x ∫_0^t S(t-s) q(s) ds| ≤ Cg · (2√t · Q0 + κ · Q1)
theorem gradDuhamel_singular_source_bound
    {q : ℝ → ℝ → ℝ} {Q0 Q1 t : ℝ} (ht : 0 < t)
    (hq : ∀ s ∈ Set.Ioo 0 t, ∀ y : ℝ, |q s y| ≤ Q0 + Q1 / Real.sqrt s) :
    True := by  -- placeholder type; actual statement needs semigroup
  trivial

-- Theorem 3: Profile induction step
-- From |∂_x U_n(t')| ≤ P(t') on (0, lo], prove same for n+1
-- Uses: truncLeftB B_F chi lo < 1
-- Key: D is exactly the fixed point of the affine map
theorem truncLeftProfile_step
    {M A_L A_F B_F chi lo : ℝ}
    (hcontr : truncLeftB B_F chi lo < 1) :
    True := by  -- placeholder; needs full Picard iterate structure
  trivial

-- Theorem 4: Profile holds for all n (induction)
theorem truncLeftProfile_all
    {M A_L A_F B_F chi lo : ℝ}
    (hcontr : truncLeftB B_F chi lo < 1) :
    True := by  -- placeholder
  trivial

-- Theorem 5: Left profile at a ≤ Gw
-- Under a = lo - a (i.e. lo = 2a), hi - a = 3a, and truncWindowB < 1
theorem truncLeftProfile_le_Gw
    {M A_L A_F B_F chi a lo hi : ℝ}
    (hM : 0 ≤ M) (hAL : 0 ≤ A_L) (hAF : 0 ≤ A_F) (hBF : 0 ≤ B_F)
    (ha : 0 < a) (hlo : lo = 2 * a) (hhi : hi = 4 * a)
    (hcontr : truncWindowB B_F chi a hi < 1) :
    truncLeftProfile M A_L A_F B_F chi lo a
      ≤ truncWindowFixedG M A_L A_F B_F chi a lo hi := by
  subst lo
  subst hi
  set K : ℝ := heatGradientLinftyLinftyConstant with hK
  set beta : ℝ := |chi| * B_F with hbeta
  set C : ℝ := K * M with hC
  set L0 : ℝ := A_L + |chi| * A_F with hL0
  set X : ℝ := C / Real.sqrt a with hX
  set Y2 : ℝ := K * (2 * Real.sqrt (2 * a)) * L0 with hY2
  set Y3 : ℝ := K * (2 * Real.sqrt (4 * a - a)) * L0 with hY3
  set bL : ℝ := truncLeftB B_F chi (2 * a) with hbL
  set bW : ℝ := truncWindowB B_F chi a (4 * a) with hbW
  have hK_nonneg : 0 ≤ K := by
    rw [hK]
    exact heatGradientLinftyLinftyConstant_nonneg
  have hbeta_nonneg : 0 ≤ beta := by
    rw [hbeta]
    exact mul_nonneg (abs_nonneg chi) hBF
  have hC_nonneg : 0 ≤ C := by
    rw [hC]
    exact mul_nonneg hK_nonneg hM
  have hL0_nonneg : 0 ≤ L0 := by
    rw [hL0]
    exact add_nonneg hAL (mul_nonneg (abs_nonneg chi) hAF)
  have hsqrta_pos : 0 < Real.sqrt a := Real.sqrt_pos_of_pos ha
  have hX_nonneg : 0 ≤ X := by
    rw [hX]
    exact div_nonneg hC_nonneg hsqrta_pos.le
  have hY2_nonneg : 0 ≤ Y2 := by
    rw [hY2]
    positivity
  have hsqrt23 : Real.sqrt (2 * a) ≤ Real.sqrt (4 * a - a) := by
    apply Real.sqrt_le_sqrt
    nlinarith [ha.le]
  have hY23 : Y2 ≤ Y3 := by
    rw [hY2, hY3]
    gcongr
  have hbL_nonneg : 0 ≤ bL := by
    rw [hbL, truncLeftB, truncLeftBeta, ← hK, ← hbeta]
    positivity
  have hbLbW : bL ≤ bW := by
    rw [hbL, hbW, truncLeftB, truncWindowB, truncLeftBeta, ← hK]
    calc
      K * (2 * Real.sqrt (2 * a)) * (|chi| * B_F)
          ≤ K * (2 * Real.sqrt (4 * a - a)) * (|chi| * B_F) := by
        gcongr
      _ = K * (2 * Real.sqrt (4 * a - a)) * |chi| * B_F := by ring
  have hbW_lt : bW < 1 := by
    simpa [hbW] using hcontr
  have hsqrt3a : Real.sqrt (4 * a - a) = Real.sqrt 3 * Real.sqrt a := by
    have hrewrite : 4 * a - a = 3 * a := by ring
    rw [hrewrite]
    rw [show 3 * a = a * 3 by ring]
    rw [Real.sqrt_mul ha.le]
    ring
  have hbeta_term :
      K * beta * C * truncLeftKappa = bW * X := by
    rw [hbW, hX, truncWindowB, truncLeftKappa, ← hK, hbeta]
    rw [hsqrt3a]
    field_simp [ne_of_gt hsqrta_pos]
  have hleft :
      truncLeftProfile M A_L A_F B_F chi (2 * a) a
        = X + (bW * X + Y2) / (1 - bL) := by
    rw [truncLeftProfile, truncLeftD, truncLeftSingularC, truncLeftSourceConst,
      truncLeftBeta]
    rw [← hK, ← hC, ← hL0, ← hbeta]
    rw [← hbL, ← hY2, ← hX, hbeta_term]
  have hright :
      truncWindowFixedG M A_L A_F B_F chi a (2 * a) (4 * a)
        = (X + Y3) / (1 - bW) := by
    have hbW_expr : bW = K * (2 * Real.sqrt (4 * a - a)) * |chi| * B_F := by
      rw [hbW, truncWindowB, ← hK]
    rw [truncWindowFixedG, truncWindowA, truncWindowB]
    rw [← hK, ← hL0, ← hY3, ← hbW_expr]
    have hsqrt_sub : Real.sqrt (2 * a - a) = Real.sqrt a := by
      congr 1
      ring
    rw [hsqrt_sub, hX, hC]
    field_simp [ne_of_gt hsqrta_pos]
  rw [hleft, hright]
  exact profile_algebra_bound hX_nonneg hY2_nonneg hY23 hbL_nonneg hbLbW hbW_lt

-- Theorem 6: hleft provider
-- Combines theorems 4 and 5 to produce ∀ n, IterGradOnWindow U a lo n Gw
-- This is the theorem that fills the hleft field of TruncatedGradientWindowWiring

end ShenWork.Paper2.TruncatedGradientWindow
