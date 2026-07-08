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

-- Theorem 1: Elementary Volterra integral bound
-- ∫_0^r (r-s)^{-1/2} · s^{-1/2} ds ≤ 2√3 for 0 < r
theorem left_beta_kernel_bound {r : ℝ} (hr : 0 < r) :
    ∫ s in (0)..r, (r - s) ^ (-(1:ℝ)/2) * s ^ (-(1:ℝ)/2) ≤ truncLeftKappa := by
  sorry

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
    (ha : 0 < a) (hlo : lo = 2 * a) (hhi : hi = 4 * a)
    (hcontr : truncWindowB B_F chi a hi < 1) :
    truncLeftProfile M A_L A_F B_F chi lo a
      ≤ truncWindowFixedG M A_L A_F B_F chi a lo hi := by
  sorry

-- Theorem 6: hleft provider
-- Combines theorems 4 and 5 to produce ∀ n, IterGradOnWindow U a lo n Gw
-- This is the theorem that fills the hleft field of TruncatedGradientWindowWiring

end ShenWork.Paper2.TruncatedGradientWindow
