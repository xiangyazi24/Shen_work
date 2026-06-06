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

/-- **Min-point PDE estimate (abstract form).**  Given the parabolic PDE value
`uT = uxx − χ₀·cd + m·(a − b·m^α)` at a spatial argmin (so `uxx ≥ 0` and the
flux `cd = m·G` with `|G| ≤ K₁`), with `0 ≤ m ≤ M`, the time derivative obeys
`−(|χ₀|·K₁ + b·M^α)·m ≤ uT`. -/
theorem min_point_estimate
    {χ₀ a b α m M uxx cd G K₁ uT : ℝ}
    (hχ : χ₀ ≤ 0) (ha : 0 ≤ a) (hb : 0 ≤ b) (hα : 0 ≤ α)
    (hm_nonneg : 0 ≤ m) (hm_le : m ≤ M)
    (huxx : 0 ≤ uxx)
    (hcd : cd = m * G) (hG : |G| ≤ K₁)
    (hpde : uT = uxx - χ₀ * cd + m * (a - b * m ^ α)) :
    -(|χ₀| * K₁ + b * M ^ α) * m ≤ uT := by
  have hM_nonneg : 0 ≤ M := le_trans hm_nonneg hm_le
  -- Chemotaxis term: `−χ₀·cd = |χ₀|·m·G ≥ −|χ₀|·K₁·m`.
  have hχabs : |χ₀| = -χ₀ := abs_of_nonpos hχ
  have hcd_lb : -(|χ₀| * K₁) * m ≤ -χ₀ * cd := by
    rw [hcd, hχabs]
    -- `-χ₀·(m·G) = (-χ₀)·m·G ≥ (-χ₀)·m·(-K₁)`  since `G ≥ -K₁`, `(-χ₀)·m ≥ 0`.
    have hcoef_nonneg : 0 ≤ -χ₀ * m := mul_nonneg (by linarith) hm_nonneg
    have hG_lb : -K₁ ≤ G := by
      have := (abs_le.mp hG).1; linarith
    have : -χ₀ * m * (-K₁) ≤ -χ₀ * m * G :=
      mul_le_mul_of_nonneg_left hG_lb hcoef_nonneg
    calc -(-χ₀ * K₁) * m = -χ₀ * m * (-K₁) := by ring
      _ ≤ -χ₀ * m * G := this
      _ = -χ₀ * (m * G) := by ring
  -- Reaction term: `m·(a − b·m^α) ≥ −b·M^α·m`.
  have hpow_le : m ^ α ≤ M ^ α := Real.rpow_le_rpow hm_nonneg hm_le hα
  have hMpow_nonneg : 0 ≤ M ^ α := Real.rpow_nonneg hM_nonneg α
  have hreact_lb : -(b * M ^ α) * m ≤ m * (a - b * m ^ α) := by
    have h1 : b * m ^ α ≤ b * M ^ α := mul_le_mul_of_nonneg_left hpow_le hb
    -- `m·(a − b·m^α) = a·m − b·m^α·m ≥ −b·M^α·m`.
    have hmα_nonneg : 0 ≤ m ^ α := Real.rpow_nonneg hm_nonneg α
    nlinarith [mul_nonneg ha hm_nonneg, mul_nonneg hm_nonneg
      (sub_nonneg.mpr h1), mul_nonneg hb hmα_nonneg]
  -- Assemble.
  rw [hpde]
  have hexpand : -(|χ₀| * K₁ + b * M ^ α) * m
      = -(|χ₀| * K₁) * m + -(b * M ^ α) * m := by ring
  rw [hexpand]
  linarith [hcd_lb, hreact_lb, huxx]

end ShenWork.MinPersistenceAtoms
