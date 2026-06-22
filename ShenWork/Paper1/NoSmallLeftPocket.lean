/-
  No-small-left-pocket left-floor mechanism for Paper 1 traveling waves.

  Analytic unlock for `StrictlyPositiveAtLeft U`.  If `U` is positive, `C²`, and
  on the small-density region `{0 < U ≤ η}` the stationary profile equation is
  coercive (`U'' + B U' + Q U = 0`, `B ≥ b0 > 0`, `Q ≥ q0 > 0`), then a small
  interior local minimum of the perturbed barrier `h = U + ε e^{-κ x}`
  (`0 < κ < b0`) is impossible.  This is the maximum-principle heart of the
  non-monotone left-floor route (no integrating factors, no connected
  components): at such a minimum `h'(z)=0` gives `U'(z)=κε e^{-κz}>0`, the second
  derivative test gives `U''(z) ≥ -κ U'(z)`, hence
    `0 = U'' + B U' + Q U ≥ (b0-κ)U' + q0 U > 0`,
  a contradiction.

  The reusable pieces are:
  * `deriv_deriv_nonneg_of_isLocalMin`   (necessary second-derivative test),
  * `exists_interior_min_left`           (interior minimiser on a left half-line
                                           via coercivity at `-∞`),
  * `noSmallInteriorMin`                 (the maximum-principle contradiction),
  * `strictlyPositiveAtLeft_of_noSmallInteriorMin`
        (reduction of the floor to producing such an interior minimum from a
         floor violation — the remaining geometric brick).
-/
import ShenWork.Paper1.Statements
import Mathlib.Analysis.Calculus.DerivativeTest

namespace ShenWork.Paper1

noncomputable section

open Filter Topology Set

/-- On the small-density set `{0 < U ≤ η}`, `U` solves the linearised stationary
equation `U'' + B U' + Q U = 0` with positive drift `B ≥ b0` and positive
zeroth-order coefficient `Q ≥ q0`. -/
structure SmallDensityCoercive
    (U B Q : ℝ → ℝ) (η b0 q0 : ℝ) : Prop where
  hη : 0 < η
  hb0 : 0 < b0
  hq0 : 0 < q0
  eq_on : ∀ x, 0 < U x → U x ≤ η →
    deriv (deriv U) x + B x * deriv U x + Q x * U x = 0
  B_ge : ∀ x, 0 < U x → U x ≤ η → b0 ≤ B x
  Q_ge : ∀ x, 0 < U x → U x ≤ η → q0 ≤ Q x

/-- Barrier `ε e^{-κ y}` as a `HasDerivAt`. -/
private lemma bar_hasDerivAt (ε κ y : ℝ) :
    HasDerivAt (fun w => ε * Real.exp (-κ * w))
      (-(κ * ε) * Real.exp (-κ * y)) y := by
  have h1 : HasDerivAt (fun w => -κ * w) (-κ) y := by
    simpa using (hasDerivAt_id y).const_mul (-κ)
  have h2 : HasDerivAt (fun w => Real.exp (-κ * w))
      (Real.exp (-κ * y) * -κ) y := (Real.hasDerivAt_exp _).comp y h1
  have := h2.const_mul ε
  convert this using 1; ring

/-- Necessary second-derivative test: at a local minimum where the first
derivative vanishes, the second derivative is nonnegative. -/
lemma deriv_deriv_nonneg_of_isLocalMin
    {f : ℝ → ℝ} {z : ℝ} (hcont : ContinuousAt f z)
    (hmin : IsLocalMin f z) (hd : deriv f z = 0) :
    0 ≤ deriv (deriv f) z := by
  by_contra hlt
  rw [not_le] at hlt
  have hmax : IsLocalMax f z := isLocalMax_of_deriv_deriv_neg hlt hd hcont
  have hconst : ∀ᶠ x in 𝓝 z, f x = f z := by
    filter_upwards [hmin, hmax] with x hxmin hxmax
    exact le_antisymm hxmax hxmin
  have hderiv0 : ∀ᶠ x in 𝓝 z, deriv f x = 0 := by
    have hfconst : f =ᶠ[𝓝 z] (fun _ => f z) := hconst
    filter_upwards [hfconst.eventuallyEq_nhds] with x hx
    rw [hx.deriv_eq]; simp
  have heq : deriv (deriv f) z = deriv (fun _ => (0 : ℝ)) z :=
    Filter.EventuallyEq.deriv_eq hderiv0
  rw [heq] at hlt; simp at hlt

/-- Interior minimiser on a left half-line for a continuous function that is
coercive (`→ +∞`) at `-∞` and dominated at the right anchor by a strictly
smaller value somewhere to its left. -/
lemma exists_interior_min_left
    {h : ℝ → ℝ} {A z₀ : ℝ} (hcont : Continuous h)
    (hcoer : Tendsto h atBot atTop)
    (hz₀A : z₀ ≤ A) (hlt : h z₀ < h A) :
    ∃ z, z < A ∧ IsLocalMin h z ∧ (∀ y ≤ A, h z ≤ h y) := by
  have hev : ∀ᶠ y in atBot, h z₀ ≤ h y :=
    hcoer.eventually (eventually_ge_atTop (h z₀))
  rw [eventually_atBot] at hev
  obtain ⟨L, hL⟩ := hev
  set L' := min L z₀ with hL'
  have hL'_le : L' ≤ z₀ := min_le_right _ _
  have hL'_leL : L' ≤ L := min_le_left _ _
  have hL'A : L' ≤ A := le_trans hL'_le hz₀A
  obtain ⟨z, hzmem, hzmin⟩ :=
    (isCompact_Icc (a := L') (b := A)).exists_isMinOn
      (nonempty_Icc.mpr hL'A) hcont.continuousOn
  have hglobal : ∀ y ≤ A, h z ≤ h y := by
    intro y hy
    by_cases hyL' : L' ≤ y
    · exact hzmin ⟨hyL', hy⟩
    · rw [not_le] at hyL'
      have : h z₀ ≤ h y := hL y (le_trans hyL'.le hL'_leL)
      have hz_le_z₀ : h z ≤ h z₀ := hzmin ⟨hL'_le, hz₀A⟩
      linarith
  have hzA : z < A := by
    have hz_le_z₀ : h z ≤ h z₀ := hzmin ⟨hL'_le, hz₀A⟩
    have : h z < h A := lt_of_le_of_lt hz_le_z₀ hlt
    rcases lt_or_eq_of_le hzmem.2 with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ this) (lt_irrefl _)
  refine ⟨z, hzA, ?_, hglobal⟩
  -- IsLocalMin on the open neighbourhood `Iio A`
  have hmem : Iio A ∈ 𝓝 z := Iio_mem_nhds hzA
  show ∀ᶠ y in 𝓝 z, h z ≤ h y
  filter_upwards [hmem] with y hy
  exact hglobal y (le_of_lt hy)

/-- **No small interior minimum (maximum principle).**
Under small-density coercivity, the perturbed barrier `h = U + ε e^{-κ x}`
(`0 < κ < b0`, `ε > 0`) cannot have an interior local minimum `z` whose value
keeps `U` inside the small-density window `0 < U z ≤ η`. -/
theorem noSmallInteriorMin
    {U B Q : ℝ → ℝ} {η b0 q0 κ ε z : ℝ}
    (hUdiff : Differentiable ℝ U)
    (hUdiff2 : Differentiable ℝ (deriv U))
    (hcoer : SmallDensityCoercive U B Q η b0 q0)
    (hκpos : 0 < κ) (hκb0 : κ < b0) (hεpos : 0 < ε)
    (hUz_pos : 0 < U z) (hUz_le : U z ≤ η)
    (hmin : IsLocalMin (fun x => U x + ε * Real.exp (-κ * x)) z) :
    False := by
  obtain ⟨hη, hb0, hq0, heq, hB, hQ⟩ := hcoer
  set bar : ℝ → ℝ := fun x => ε * Real.exp (-κ * x) with hbardef
  set h : ℝ → ℝ := fun x => U x + bar x with hhdef
  -- derivatives of `h`
  have hbarHD : ∀ y, HasDerivAt bar (-(κ * ε) * Real.exp (-κ * y)) y :=
    fun y => bar_hasDerivAt ε κ y
  have hhderiv : ∀ y, deriv h y = deriv U y - (κ * ε) * Real.exp (-κ * y) := by
    intro y
    have hHD : HasDerivAt h
        (deriv U y + -(κ * ε) * Real.exp (-κ * y)) y :=
      (hUdiff y).hasDerivAt.add (hbarHD y)
    rw [hHD.deriv]; ring
  -- `h` continuous and differentiable (for the second-derivative test)
  have hbarcont : Continuous bar :=
    continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))
  have hhcontAt : ContinuousAt h z := (hUdiff.continuous.add hbarcont).continuousAt
  -- first-order condition: deriv h z = 0
  have hd1 : deriv h z = 0 := hmin.deriv_eq_zero
  have hUd1 : deriv U z = (κ * ε) * Real.exp (-κ * z) := by
    have := hhderiv z; rw [hd1] at this; linarith
  have hUd1_pos : 0 < deriv U z := by
    rw [hUd1]; positivity
  -- second-order condition: deriv (deriv h) z ≥ 0, and equals U'' + κ²ε e^{-κz}
  have hderiv_eq : deriv h =ᶠ[𝓝 z]
      (fun y => deriv U y - (κ * ε) * Real.exp (-κ * y)) :=
    Filter.Eventually.of_forall hhderiv
  have hdd_eq : deriv (deriv h) z
      = deriv (fun y => deriv U y - (κ * ε) * Real.exp (-κ * y)) z :=
    Filter.EventuallyEq.deriv_eq hderiv_eq
  have hdd_rhs : deriv (fun y => deriv U y - (κ * ε) * Real.exp (-κ * y)) z
      = deriv (deriv U) z + (κ * (κ * ε)) * Real.exp (-κ * z) := by
    have hsub : HasDerivAt (fun y => deriv U y - (κ * ε) * Real.exp (-κ * y))
        (deriv (deriv U) z + (κ * (κ * ε)) * Real.exp (-κ * z)) z := by
      have hsum := (hUdiff2 z).hasDerivAt.sub
        (bar_hasDerivAt (κ * ε) κ z)
      convert hsum using 1; ring
    rw [hsub.deriv]
  have hdd_nonneg : 0 ≤ deriv (deriv h) z :=
    deriv_deriv_nonneg_of_isLocalMin hhcontAt hmin hd1
  rw [hdd_eq, hdd_rhs] at hdd_nonneg
  -- so U''(z) ≥ -(κ·κε) e^{-κz} = -κ·U'(z)
  have hUdd_lb : -(κ * deriv U z) ≤ deriv (deriv U) z := by
    have hcollapse : (κ * (κ * ε)) * Real.exp (-κ * z) = κ * deriv U z := by
      rw [hUd1]; ring
    rw [hcollapse] at hdd_nonneg; linarith
  -- coercive equation at z
  have heqz := heq z hUz_pos hUz_le
  have hBz : b0 ≤ B z := hB z hUz_pos hUz_le
  have hQz : q0 ≤ Q z := hQ z hUz_pos hUz_le
  -- contradiction: 0 = U'' + B U' + Q U ≥ (b0-κ)U' + q0 U > 0
  have hBU : b0 * deriv U z ≤ B z * deriv U z :=
    mul_le_mul_of_nonneg_right hBz hUd1_pos.le
  have hQU : q0 * U z ≤ Q z * U z :=
    mul_le_mul_of_nonneg_right hQz (hUz_pos.le)
  have hpos : 0 < (b0 - κ) * deriv U z + q0 * U z := by
    have h1 : 0 < (b0 - κ) * deriv U z :=
      mul_pos (by linarith) hUd1_pos
    have h2 : 0 < q0 * U z := mul_pos hq0 hUz_pos
    linarith
  nlinarith [heqz, hUdd_lb, hBU, hQU, hpos]

/-- **Reduction of the left floor to a small interior minimum.**
`StrictlyPositiveAtLeft U` follows from small-density coercivity once one can
produce, from any floor violation, an interior local minimum of the perturbed
barrier `U + ε e^{-κ x}` staying in the small-density window.  The geometric
producer `hproduce` is the remaining brick (it is the analogue of choosing the
sublevel component / interior minimiser of the classical proof, packaged so the
maximum principle `noSmallInteriorMin` discharges it). -/
theorem strictlyPositiveAtLeft_of_noSmallInteriorMin
    {U B Q : ℝ → ℝ} {η b0 q0 : ℝ}
    (hUdiff : Differentiable ℝ U)
    (hUdiff2 : Differentiable ℝ (deriv U))
    (hcoer : SmallDensityCoercive U B Q η b0 q0)
    (hproduce : ¬ StrictlyPositiveAtLeft U →
      ∃ κ ε z : ℝ, 0 < κ ∧ κ < b0 ∧ 0 < ε ∧
        0 < U z ∧ U z ≤ η ∧
        IsLocalMin (fun x => U x + ε * Real.exp (-κ * x)) z) :
    StrictlyPositiveAtLeft U := by
  by_contra hviol
  obtain ⟨κ, ε, z, hκpos, hκb0, hεpos, hUz_pos, hUz_le, hmin⟩ := hproduce hviol
  exact noSmallInteriorMin hUdiff hUdiff2 hcoer hκpos hκb0 hεpos
    hUz_pos hUz_le hmin

/-! ## Coercivity for Paper 1's actual stationary equation

The Paper 1 profile equation is, in divergence form,
`U'' + c U' - χ ∂ₓ(Uᵐ V') + U(1 - Uᵃ) = 0`, which at the fixed point expands
(`paperWaveOperator`) into `U'' + B U' + Q U = 0` with
`B = c - χ m U^{m-1} V'` and `Q = 1 - χ U^{m-1}(V - U^γ) - U^α`.
On the trap `0 ≤ U ≤ 1` the elliptic resolver gives `|V'| ≤ 1` and
`|V - U^γ| ≤ 1`, hence `B ≥ c - |χ| m η^{m-1}` and `Q ≥ 1 - |χ| - η^α`
on `{0 < U ≤ η}`.  For `m ≥ 1` (Paper 1's `p.hm`) both floors are positive in
the Remark 1.3(2) regime (`c > 2`, `|χ| < 1`), so the coercivity holds. -/

/-- The drift coefficient `B` of the expanded profile operator. -/
def coercDrift (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : ℝ → ℝ :=
  fun x => c - p.χ * p.m * (U x) ^ (p.m - 1) * deriv (frozenElliptic p U) x

/-- The zeroth-order coefficient `Q` of the expanded profile operator. -/
def coercZero (p : CMParams) (U : ℝ → ℝ) : ℝ → ℝ :=
  fun x => 1 - p.χ * (U x) ^ (p.m - 1) * frozenElliptic p U x
    - (U x) ^ p.α + p.χ * (U x) ^ (p.m + p.γ - 1)

/-- The paper operator at the fixed point is `U'' + B U' + Q U`. -/
theorem paperWaveOperator_eq_coercForm
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) (x : ℝ) :
    paperWaveOperator p c U U x
      = deriv (deriv U) x + coercDrift p c U x * deriv U x
        + coercZero p U x * U x := by
  unfold paperWaveOperator coercDrift coercZero
  rw [iteratedDeriv_succ, iteratedDeriv_one]; ring

/-- Drift floor on the small-density window: `B ≥ c - |χ| m η^{m-1}`. -/
theorem coercDrift_lb
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) {η : ℝ} {x : ℝ}
    (hU_nonneg : 0 ≤ U x) (hU_le : U x ≤ η) (_hη1 : η ≤ 1) (hη0 : 0 ≤ η)
    (hV1 : |deriv (frozenElliptic p U) x| ≤ 1) :
    c - |p.χ| * p.m * η ^ (p.m - 1) ≤ coercDrift p c U x := by
  unfold coercDrift
  have hm1 : (0:ℝ) ≤ p.m - 1 := by linarith [p.hm]
  have hpow_le : (U x) ^ (p.m - 1) ≤ η ^ (p.m - 1) :=
    Real.rpow_le_rpow hU_nonneg hU_le hm1
  have hpow_nonneg : 0 ≤ (U x) ^ (p.m - 1) := Real.rpow_nonneg hU_nonneg _
  have hηpow_nonneg : 0 ≤ η ^ (p.m - 1) := Real.rpow_nonneg hη0 _
  have hm_nonneg : (0:ℝ) ≤ p.m := by linarith [p.hm]
  have hbound : |p.χ * p.m * (U x) ^ (p.m - 1) * deriv (frozenElliptic p U) x|
      ≤ |p.χ| * p.m * η ^ (p.m - 1) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hm_nonneg,
      abs_of_nonneg hpow_nonneg]
    have h1 : |p.χ| * p.m * (U x) ^ (p.m - 1)
        * |deriv (frozenElliptic p U) x|
        ≤ |p.χ| * p.m * η ^ (p.m - 1) * 1 := by gcongr
    simpa using h1
  have hab := abs_le.mp hbound
  linarith [hab.1, hab.2]

/-- Zeroth-order floor on the small-density window: `Q ≥ 1 - |χ| - η^α`. -/
theorem coercZero_lb
    (p : CMParams) (U : ℝ → ℝ) {η : ℝ} {x : ℝ}
    (hU_nonneg : 0 ≤ U x) (hU_le : U x ≤ η) (hη1 : η ≤ 1) (_hη0 : 0 ≤ η)
    (hV_nonneg : 0 ≤ frozenElliptic p U x)
    (hV_le1 : frozenElliptic p U x ≤ 1)
    (hUγ_le1 : (U x) ^ p.γ ≤ 1) :
    1 - |p.χ| - η ^ p.α ≤ coercZero p U x := by
  have hU_le1 : U x ≤ 1 := le_trans hU_le hη1
  unfold coercZero
  have hsplit : p.m + p.γ - 1 = (p.m - 1) + p.γ := by ring
  have hrw : (U x) ^ (p.m + p.γ - 1)
      = (U x) ^ (p.m - 1) * (U x) ^ p.γ := by
    rw [hsplit, Real.rpow_add' hU_nonneg]
    intro h; exfalso; nlinarith [p.hm, p.hγ]
  rw [hrw]
  have hpow_le1 : (U x) ^ (p.m - 1) ≤ 1 :=
    Real.rpow_le_one hU_nonneg hU_le1 (by linarith [p.hm])
  have hpow_nonneg : 0 ≤ (U x) ^ (p.m - 1) := Real.rpow_nonneg hU_nonneg _
  have hUγ_nonneg : 0 ≤ (U x) ^ p.γ := Real.rpow_nonneg hU_nonneg _
  have hUα_le : (U x) ^ p.α ≤ η ^ p.α :=
    Real.rpow_le_rpow hU_nonneg hU_le (by linarith [p.hα])
  have hdiff_abs : |frozenElliptic p U x - (U x) ^ p.γ| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  have hbound : |p.χ * (U x) ^ (p.m - 1)
      * (frozenElliptic p U x - (U x) ^ p.γ)| ≤ |p.χ| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hpow_nonneg]
    have h1 : |p.χ| * (U x) ^ (p.m - 1)
        * |frozenElliptic p U x - (U x) ^ p.γ| ≤ |p.χ| * 1 * 1 := by gcongr
    simpa using h1
  have hab := abs_le.mp hbound
  nlinarith [hab.1, hab.2, hUα_le]

/-- **Coercivity producer for Paper 1.**  From the paper stationary equation
`paperWaveOperator p c U U = 0`, the trap bounds (`0 ≤ U ≤ η ≤ 1`, elliptic
`0 ≤ V ≤ 1`, `|V'| ≤ 1`, `U^γ ≤ 1`), and the Remark 1.3(2) regime floors
`|χ| m η^{m-1} < c` and `|χ| + η^α < 1`, the equation is small-density coercive
with `B = coercDrift`, `Q = coercZero`, `b0 = c - |χ| m η^{m-1}`,
`q0 = 1 - |χ| - η^α`. -/
theorem smallDensityCoercive_paper
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) {η : ℝ}
    (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hU_nonneg : ∀ x, 0 ≤ U x)
    (hstat : ∀ x, paperWaveOperator p c U U x = 0)
    (hV_nonneg : ∀ x, 0 ≤ frozenElliptic p U x)
    (hV_le1 : ∀ x, frozenElliptic p U x ≤ 1)
    (hV1 : ∀ x, |deriv (frozenElliptic p U) x| ≤ 1)
    (hUγ_le1 : ∀ x, (U x) ^ p.γ ≤ 1)
    (hdrift : |p.χ| * p.m * η ^ (p.m - 1) < c)
    (hzero : |p.χ| + η ^ p.α < 1) :
    SmallDensityCoercive U (coercDrift p c U) (coercZero p U)
      η (c - |p.χ| * p.m * η ^ (p.m - 1)) (1 - |p.χ| - η ^ p.α) := by
  refine
    { hη := hη0
      hb0 := by linarith
      hq0 := by linarith
      eq_on := ?_
      B_ge := ?_
      Q_ge := ?_ }
  · intro x _ _
    have := paperWaveOperator_eq_coercForm p c U x
    have h0 := hstat x
    rw [this] at h0; linarith
  · intro x _ hUle
    exact coercDrift_lb p c U (hU_nonneg x) hUle hη1 hη0.le (hV1 x)
  · intro x _ hUle
    exact coercZero_lb p U (hU_nonneg x) hUle hη1 hη0.le
      (hV_nonneg x) (hV_le1 x) (hUγ_le1 x)

section NoSmallLeftPocketAxiomAudit
#print axioms deriv_deriv_nonneg_of_isLocalMin
#print axioms exists_interior_min_left
#print axioms noSmallInteriorMin
#print axioms strictlyPositiveAtLeft_of_noSmallInteriorMin
#print axioms paperWaveOperator_eq_coercForm
#print axioms coercDrift_lb
#print axioms coercZero_lb
#print axioms smallDensityCoercive_paper
end NoSmallLeftPocketAxiomAudit

end

end ShenWork.Paper1
