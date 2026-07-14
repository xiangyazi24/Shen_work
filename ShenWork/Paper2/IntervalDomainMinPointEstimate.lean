/-
  B2 core (MinPersistence): the min-point PDE estimate.

  At a fixed time `t`, let `x*` be a spatial argmin of `u(t,·)` (value
  `m := u(t,x*) ≥ 0`).  The parabolic PDE
    `u_t = u_xx − χ₀·chemDiv + u·(a − b·u^α)`
  at `x*`, together with
    - `u_xx(x*) ≥ 0`              (second-derivative test at an argmin, Phase A),
    - `chemDiv(x*) = m·G`         (the flux divergence at a spatial critical
                                   point `u_x(x*)=0`, with `|G| ≤ K₁` the
                                   B4 coefficient bound),
  forces the slab-independent lower slope
    `u_t(t,x*) ≥ −K·m`,    `K := |χ₀|·K₁ + b·M^α`.
  This is the pointwise inequality the Hamilton/Grönwall step
  (`hamilton_lower_bound`) integrates into `m(t) ≥ m(t₁)·e^{−K(t−t₁)}`.

  The lemma is stated over abstract reals so it is independent of the
  `IsPaper2ClassicalSolution` interface (the caller supplies the PDE value,
  the `u_xx ≥ 0` sign, and the critical-point flux expansion).

  No `sorry`/`admit`/custom `axiom`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

namespace ShenWork.MinPersistenceAtoms

/-- **Min-point PDE estimate retaining positive linear growth.**  Given the
parabolic PDE value at a spatial minimum, the time derivative retains the
whole `a * m` contribution while bounding only chemotaxis and logistic
damping by the supplied ceiling. -/
theorem min_point_estimate_allChi_with_growth
    {χ₀ a b α m M uxx cd G K₁ uT : ℝ}
    (hb : 0 ≤ b) (hα : 0 ≤ α)
    (hm_nonneg : 0 ≤ m) (hm_le : m ≤ M)
    (huxx : 0 ≤ uxx)
    (hcd : cd = m * G) (hG : |G| ≤ K₁)
    (hpde : uT = uxx - χ₀ * cd + m * (a - b * m ^ α)) :
    (a - (|χ₀| * K₁ + b * M ^ α)) * m ≤ uT := by
  have hM_nonneg : 0 ≤ M := le_trans hm_nonneg hm_le
  have hcd_lb : -(|χ₀| * K₁) * m ≤ -χ₀ * cd := by
    have hterm_abs : |-χ₀ * cd| ≤ |χ₀| * K₁ * m := by
      rw [hcd, abs_mul, abs_neg, abs_mul, abs_of_nonneg hm_nonneg]
      nlinarith [mul_nonneg (abs_nonneg χ₀) hm_nonneg,
        mul_nonneg (abs_nonneg χ₀) (abs_nonneg G)]
    nlinarith [(abs_le.mp hterm_abs).1]
  have hpow_le : m ^ α ≤ M ^ α :=
    Real.rpow_le_rpow hm_nonneg hm_le hα
  have hreact_lb : (a - b * M ^ α) * m ≤ m * (a - b * m ^ α) := by
    have h1 : b * m ^ α ≤ b * M ^ α :=
      mul_le_mul_of_nonneg_left hpow_le hb
    nlinarith [mul_nonneg hm_nonneg (sub_nonneg.mpr h1),
      Real.rpow_nonneg hM_nonneg α]
  rw [hpde]
  have hexpand : (a - (|χ₀| * K₁ + b * M ^ α)) * m =
      -(|χ₀| * K₁) * m + (a - b * M ^ α) * m := by ring
  rw [hexpand]
  linarith [hcd_lb, hreact_lb, huxx]

/-- **Min-point PDE estimate (abstract form).**  Given the parabolic PDE value
`uT = uxx − χ₀·cd + m·(a − b·m^α)` at a spatial argmin (so `uxx ≥ 0` and the
flux `cd = m·G` with `|G| ≤ K₁`), with `0 ≤ m ≤ M`, the time derivative obeys
`−(|χ₀|·K₁ + b·M^α)·m ≤ uT`. -/
theorem min_point_estimate_allChi
    {χ₀ a b α m M uxx cd G K₁ uT : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hα : 0 ≤ α)
    (hm_nonneg : 0 ≤ m) (hm_le : m ≤ M)
    (huxx : 0 ≤ uxx)
    (hcd : cd = m * G) (hG : |G| ≤ K₁)
    (hpde : uT = uxx - χ₀ * cd + m * (a - b * m ^ α)) :
    -(|χ₀| * K₁ + b * M ^ α) * m ≤ uT := by
  have hgrowth := min_point_estimate_allChi_with_growth hb hα hm_nonneg
    hm_le huxx hcd hG hpde
  nlinarith [mul_nonneg ha hm_nonneg]

/-- Compatibility form retaining the former nonpositive-sensitivity
hypothesis.  The estimate itself is sign-agnostic. -/
theorem min_point_estimate
    {χ₀ a b α m M uxx cd G K₁ uT : ℝ}
    (_hχ : χ₀ ≤ 0) (ha : 0 ≤ a) (hb : 0 ≤ b) (hα : 0 ≤ α)
    (hm_nonneg : 0 ≤ m) (hm_le : m ≤ M)
    (huxx : 0 ≤ uxx)
    (hcd : cd = m * G) (hG : |G| ≤ K₁)
    (hpde : uT = uxx - χ₀ * cd + m * (a - b * m ^ α)) :
    -(|χ₀| * K₁ + b * M ^ α) * m ≤ uT :=
  min_point_estimate_allChi ha hb hα hm_nonneg hm_le huxx hcd hG hpde

end ShenWork.MinPersistenceAtoms
