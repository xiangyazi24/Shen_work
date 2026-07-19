import ShenWork.Paper1.WholeLineChiPosRectangleTargets

/-!
# The exact positive-sensitivity equilibrium ceiling

For the supercritical branch `q := m + γ - 1 < α` the crude parameter ceiling
`max 1 ((1+χ)^(1/(α-q)))` is far too large to seed a rectangle: at `m = 1` the
floor margin `1 - χ M ^ γ` is negative there whenever `α - q` is small.

The right ceiling is the exact scalar equilibrium `M` of

  `M ^ α = 1 + χ * M ^ q`,

towards which a ceiling-only barrier descends using nothing but `u ≥ 0` (so
`frozenElliptic ≥ 0`).  At that height the two rectangle margins are not merely
positive — the ceiling margin is an exact product:

  `chiPosCeilingGap p ℓ M = χ * M ^ (m-1) * ℓ ^ γ`,

and the floor margin is positive for small `ℓ` because `M ^ α < 2` whenever
`χ < 1/2` (proved below), which for `m = 1` is exactly `χ * M ^ γ < 1`.
-/

open Real

noncomputable section

namespace ShenWork.Paper1

/-- The scalar equilibrium equation of the positive branch. -/
def chiPosEquilibriumEq (p : CMParams) (M : ℝ) : ℝ :=
  M ^ p.α - p.χ * M ^ (p.m + p.γ - 1) - 1

/-- At `M = 1` the equilibrium function is `-χ ≤ 0`. -/
theorem chiPosEquilibriumEq_one (p : CMParams) :
    chiPosEquilibriumEq p 1 = -p.χ := by
  unfold chiPosEquilibriumEq
  simp

/-- The equilibrium function is eventually positive in the supercritical
branch: it grows like `M ^ α` against `χ M ^ q` with `q < α`. -/
theorem chiPosEquilibriumEq_pos_of_large
    (p : CMParams) (hχ : 0 ≤ p.χ) (hsuper : p.m + p.γ - 1 < p.α)
    {M : ℝ} (hM : 1 ≤ M)
    (hlarge : 1 + p.χ ≤ M ^ (p.α - (p.m + p.γ - 1))) :
    0 ≤ chiPosEquilibriumEq p M := by
  have hM0 : (0 : ℝ) < M := zero_lt_one.trans_le hM
  have hq0 : (0 : ℝ) ≤ p.m + p.γ - 1 := by linarith [p.hm, p.hγ]
  have hsplit : M ^ p.α =
      M ^ (p.m + p.γ - 1) * M ^ (p.α - (p.m + p.γ - 1)) := by
    rw [← Real.rpow_add hM0]
    congr 1
    ring
  have hq1 : (1 : ℝ) ≤ M ^ (p.m + p.γ - 1) := Real.one_le_rpow hM hq0
  unfold chiPosEquilibriumEq
  rw [hsplit]
  nlinarith [hq1, hlarge]

/-- Sharp bound on the equilibrium height: `M ^ α < 2` whenever `χ < 1/2` and
the exponent is supercritical.  This is what makes the floor margin positive at
the equilibrium (for `m = 1` it reads exactly `χ * M ^ γ < 1`). -/
theorem chiPos_equilibrium_rpow_alpha_lt_two
    (p : CMParams) (hχ0 : 0 ≤ p.χ) (hχ : p.χ < 1 / 2)
    (hsuper : p.m + p.γ - 1 < p.α)
    {M : ℝ} (hM : 1 ≤ M) (heq : chiPosEquilibriumEq p M = 0) :
    M ^ p.α < 2 := by
  have hM0 : (0 : ℝ) < M := zero_lt_one.trans_le hM
  have hq0 : (0 : ℝ) ≤ p.m + p.γ - 1 := by linarith [p.hm, p.hγ]
  have hα0 : (0 : ℝ) < p.α := lt_of_lt_of_le zero_lt_one p.hα
  have hkey : M ^ p.α = 1 + p.χ * M ^ (p.m + p.γ - 1) := by
    unfold chiPosEquilibriumEq at heq
    linarith
  by_contra hcon
  push_neg at hcon
  -- from `M ^ α ≥ 2` the equilibrium forces `χ ≥ (M ^ α) / (2 M ^ q)`
  have hq1 : (1 : ℝ) ≤ M ^ (p.m + p.γ - 1) := Real.one_le_rpow hM hq0
  have hqα : M ^ (p.m + p.γ - 1) < M ^ p.α ∨ M = 1 := by
    rcases eq_or_lt_of_le hM with h1 | h1
    · exact Or.inr h1.symm
    · exact Or.inl (Real.rpow_lt_rpow_of_exponent_lt h1 hsuper)
  rcases hqα with hlt | hone
  · -- `M > 1`: the equilibrium gives `χ M^q = M^α − 1 ≥ M^α/2 > M^q/2`
    have hhalf : M ^ p.α / 2 ≤ M ^ p.α - 1 := by linarith
    have hchain : p.χ * M ^ (p.m + p.γ - 1) ≥ M ^ p.α / 2 := by
      rw [hkey] at hhalf ⊢
      linarith
    have hpos : (0 : ℝ) < M ^ (p.m + p.γ - 1) := by linarith
    nlinarith [hchain, hlt, hpos]
  · -- `M = 1` contradicts `M ^ α ≥ 2`
    rw [hone] at hcon
    simp at hcon

/-- At the equilibrium height the ceiling margin is an exact positive product:
`chiPosCeilingGap p ℓ M = χ * M ^ (m-1) * ℓ ^ γ`. -/
theorem chiPosCeilingGap_at_equilibrium
    (p : CMParams) {M ℓ : ℝ} (hM : 0 < M)
    (heq : chiPosEquilibriumEq p M = 0) :
    chiPosCeilingGap p ℓ M = p.χ * (M ^ (p.m - 1) * ℓ ^ p.γ) := by
  have hsplit : M ^ (p.m - 1) * M ^ p.γ = M ^ (p.m + p.γ - 1) := by
    rw [← Real.rpow_add hM]
    congr 1
    ring
  have hkey : M ^ p.α = 1 + p.χ * M ^ (p.m + p.γ - 1) := by
    unfold chiPosEquilibriumEq at heq
    linarith
  unfold chiPosCeilingGap
  rw [hkey, mul_sub, hsplit]
  ring

/-- Consequently the ceiling margin at the equilibrium is strictly positive for
every positive floor. -/
theorem chiPosCeilingGap_pos_at_equilibrium
    (p : CMParams) {M ℓ : ℝ} (hM : 0 < M) (hχ : 0 < p.χ) (hℓ : 0 < ℓ)
    (heq : chiPosEquilibriumEq p M = 0) :
    0 < chiPosCeilingGap p ℓ M := by
  rw [chiPosCeilingGap_at_equilibrium p hM heq]
  have h1 : (0 : ℝ) < M ^ (p.m - 1) := Real.rpow_pos_of_pos hM _
  have h2 : (0 : ℝ) < ℓ ^ p.γ := Real.rpow_pos_of_pos hℓ _
  positivity

section AxiomAudit

#print axioms chiPosEquilibriumEq_one
#print axioms chiPosEquilibriumEq_pos_of_large
#print axioms chiPos_equilibrium_rpow_alpha_lt_two
#print axioms chiPosCeilingGap_at_equilibrium
#print axioms chiPosCeilingGap_pos_at_equilibrium

end AxiomAudit

end ShenWork.Paper1
