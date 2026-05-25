/-
  Interval-domain uniqueness handoff for classical Paper2 solutions.

  This file deliberately stays out of the Theorem 1.2 gluing file.  It proves
  the non-gluing part of the standard uniqueness argument: a Gronwall/energy
  certificate whose error vanishes at the initial edge forces two interval
  classical solutions to agree on their common positive time interval.
-/
import ShenWork.Paper2.Statements

open ShenWork.IntervalDomain

namespace ShenWork.Paper2

noncomputable section

/-- Pointwise error controlled by an energy functional for two interval-domain
classical solutions on a common horizon.

Point 17 status: this is an honest energy-method certificate, not a theorem
claiming that the certificate has already been derived from the PDE.  The
nontrivial analytic work still needed upstream is to construct such an `energy`
from the difference equation, comparison principle, or Gronwall estimate. -/
structure IntervalDomainClassicalOverlapEnergyCertificate
    (p : CM2Params) (T : ℝ)
    (u v U V : ℝ → intervalDomain.Point → ℝ) where
  left_solution : IsPaper2ClassicalSolution intervalDomain p T u v
  right_solution : IsPaper2ClassicalSolution intervalDomain p T U V
  energy : ℝ → ℝ
  energy_nonneg : ∀ t, 0 < t → t < T → 0 ≤ energy t
  controls_pointwise :
    ∀ t, 0 < t → t < T → ∀ x : intervalDomain.Point,
      |u t x - U t x| + |v t x - V t x| ≤ energy t
  gronwall_from_positive_times :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ s t, 0 < s → s ≤ t → t < T →
        energy t ≤ energy s * Real.exp (K * (t - s))
  initial_error_vanishes :
    ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → s < T →
      energy s < ε

private lemma intervalDomain_energy_eq_zero_of_gronwall
    {T : ℝ} {E : ℝ → ℝ}
    (hE_nonneg : ∀ t, 0 < t → t < T → 0 ≤ E t)
    (hgronwall :
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ s t, 0 < s → s ≤ t → t < T →
          E t ≤ E s * Real.exp (K * (t - s)))
    (hinit :
      ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → s < T →
        E s < ε) :
    ∀ t, 0 < t → t < T → E t = 0 := by
  intro t ht0 htT
  have hEt_nonneg : 0 ≤ E t := hE_nonneg t ht0 htT
  by_contra hEt_ne
  have hEt_pos : 0 < E t := lt_of_le_of_ne hEt_nonneg (Ne.symm hEt_ne)
  rcases hgronwall with ⟨K, hK_nonneg, hG⟩
  have hExp_pos : 0 < Real.exp (K * t) := Real.exp_pos _
  let ε : ℝ := E t / (2 * Real.exp (K * t))
  have hε_pos : 0 < ε := by
    exact div_pos hEt_pos (mul_pos (by norm_num) hExp_pos)
  rcases hinit ε hε_pos with ⟨δ, hδ_pos, hδ⟩
  let s : ℝ := min (δ / 2) (t / 2)
  have hs_pos : 0 < s := by
    exact lt_min (by linarith) (by linarith)
  have hs_lt_δ : s < δ := by
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hs_lt_t : s < t := by
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hs_le_t : s ≤ t := le_of_lt hs_lt_t
  have hsT : s < T := lt_trans hs_lt_t htT
  have hEs_nonneg : 0 ≤ E s := hE_nonneg s hs_pos hsT
  have hEs_lt : E s < ε := hδ s hs_pos hs_lt_δ hsT
  have hExp_le : Real.exp (K * (t - s)) ≤ Real.exp (K * t) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hK_nonneg, hs_pos]
  have hEt_le : E t ≤ E s * Real.exp (K * t) := by
    exact le_trans (hG s t hs_pos hs_le_t htT)
      (mul_le_mul_of_nonneg_left hExp_le hEs_nonneg)
  have hEs_mul_lt : E s * Real.exp (K * t) < ε * Real.exp (K * t) :=
    mul_lt_mul_of_pos_right hEs_lt hExp_pos
  have hε_mul : ε * Real.exp (K * t) = E t / 2 := by
    dsimp [ε]
    field_simp [ne_of_gt hExp_pos]
  have hEt_lt_half : E t < E t / 2 := lt_of_le_of_lt hEt_le (by
    simpa [hε_mul] using hEs_mul_lt)
  linarith

/-- Energy-certificate uniqueness on the overlap of two interval-domain
classical solutions.

The proof is pure Gronwall plus pointwise control: no gluing construction is
used here.  Downstream gluing files can instantiate the certificate for each
pair of finite reachable solutions. -/
theorem intervalDomain_classicalSolution_overlap_unique_of_energyCertificate
    {p : CM2Params} {T : ℝ}
    {u v U V : ℝ → intervalDomain.Point → ℝ}
    (hcert :
      IntervalDomainClassicalOverlapEnergyCertificate p T u v U V) :
    ∀ t, 0 < t → t < T →
      ∀ x : intervalDomain.Point, u t x = U t x ∧ v t x = V t x := by
  have hE_zero :
      ∀ t, 0 < t → t < T → hcert.energy t = 0 :=
    intervalDomain_energy_eq_zero_of_gronwall
      hcert.energy_nonneg hcert.gronwall_from_positive_times
      hcert.initial_error_vanishes
  intro t ht0 htT x
  have hcontrol := hcert.controls_pointwise t ht0 htT x
  have hEt_zero := hE_zero t ht0 htT
  have hsum_le_zero :
      |u t x - U t x| + |v t x - V t x| ≤ 0 := by
    simpa [hEt_zero] using hcontrol
  have hu_abs_zero : |u t x - U t x| = 0 := by
    apply le_antisymm
    · exact le_trans
        (le_add_of_nonneg_right (abs_nonneg (v t x - V t x)))
        hsum_le_zero
    · exact abs_nonneg _
  have hv_abs_zero : |v t x - V t x| = 0 := by
    apply le_antisymm
    · exact le_trans
        (le_add_of_nonneg_left (abs_nonneg (u t x - U t x)))
        hsum_le_zero
    · exact abs_nonneg _
  constructor
  · exact sub_eq_zero.mp (abs_eq_zero.mp hu_abs_zero)
  · exact sub_eq_zero.mp (abs_eq_zero.mp hv_abs_zero)

/-- The concrete L2 difference energy for two interval-domain solution pairs.

It is intentionally only a definition: the analytic work in an application is
to prove that this quantity satisfies the positive-time Gronwall estimate
below. -/
def intervalDomainClassicalL2DifferenceEnergy
    (u v U V : ℝ → intervalDomain.Point → ℝ) (t : ℝ) : ℝ :=
  intervalDomain.integral fun x =>
    (u t x - U t x) ^ 2 + (v t x - V t x) ^ 2

/-- L2-energy uniqueness certificate for two interval-domain classical
solutions on a common horizon.

Point 17 status: the Gronwall-to-zero part is proved below.  The remaining
upstream PDE obligations are exactly the displayed hypotheses: nonnegativity
of the L2 energy, the L2 Gronwall estimate for the difference equation, the
vanishing of the positive-time initial L2 error, and the standard
zero-L2-to-pointwise step under the needed spatial regularity. -/
structure IntervalDomainClassicalOverlapL2EnergyCertificate
    (p : CM2Params) (T : ℝ)
    (u v U V : ℝ → intervalDomain.Point → ℝ) where
  left_solution : IsPaper2ClassicalSolution intervalDomain p T u v
  right_solution : IsPaper2ClassicalSolution intervalDomain p T U V
  l2_energy_nonneg :
    ∀ t, 0 < t → t < T →
      0 ≤ intervalDomainClassicalL2DifferenceEnergy u v U V t
  l2_gronwall_from_positive_times :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ s t, 0 < s → s ≤ t → t < T →
        intervalDomainClassicalL2DifferenceEnergy u v U V t ≤
          intervalDomainClassicalL2DifferenceEnergy u v U V s *
            Real.exp (K * (t - s))
  l2_initial_error_vanishes :
    ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → s < T →
      intervalDomainClassicalL2DifferenceEnergy u v U V s < ε
  l2_zero_controls_pointwise :
    ∀ t, 0 < t → t < T →
      intervalDomainClassicalL2DifferenceEnergy u v U V t = 0 →
        ∀ x : intervalDomain.Point, u t x = U t x ∧ v t x = V t x

/-- L2-energy-certificate uniqueness on the overlap of two interval-domain
classical solutions.

This is the handoff theorem for gluing: once the actual PDE energy estimate has
been supplied, the overlap equality follows by a genuine Gronwall argument. -/
theorem intervalDomain_classicalSolution_overlap_unique_of_l2EnergyCertificate
    {p : CM2Params} {T : ℝ}
    {u v U V : ℝ → intervalDomain.Point → ℝ}
    (hcert :
      IntervalDomainClassicalOverlapL2EnergyCertificate p T u v U V) :
    ∀ t, 0 < t → t < T →
      ∀ x : intervalDomain.Point, u t x = U t x ∧ v t x = V t x := by
  have hE_zero :
      ∀ t, 0 < t → t < T →
        intervalDomainClassicalL2DifferenceEnergy u v U V t = 0 :=
    intervalDomain_energy_eq_zero_of_gronwall
      hcert.l2_energy_nonneg hcert.l2_gronwall_from_positive_times
      hcert.l2_initial_error_vanishes
  intro t ht0 htT x
  exact hcert.l2_zero_controls_pointwise t ht0 htT
    (hE_zero t ht0 htT) x

/-- Energy-method frontier for overlap uniqueness of interval-domain classical
solutions with the same initial `u` trace.

The certificate includes the missing analytic input that the `v`-difference is
also initially controlled, as would follow from a formal elliptic uniqueness
or trace theorem for the `v` equation.  This keeps the remaining gap explicit
instead of pretending that `InitialTrace` for `u` alone determines `v`. -/
structure IntervalDomainClassicalUniquenessEnergyMethod
    (p : CM2Params) where
  certificate :
    ∀ {u₀ : intervalDomain.Point → ℝ} {T₁ T₂ : ℝ}
      {u₁ v₁ u₂ v₂ : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
      IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
      InitialTrace intervalDomain u₀ u₁ →
      InitialTrace intervalDomain u₀ u₂ →
        IntervalDomainClassicalOverlapEnergyCertificate
          p (min T₁ T₂) u₁ v₁ u₂ v₂

/-- User-facing overlap uniqueness from a genuine energy-method certificate
builder.

This is the theorem intended for the Theorem 1.2 gluing file: instantiate
`hmethod` once, then apply this lemma to any two finite reachable witnesses
with the same initial trace. -/
theorem intervalDomain_classicalSolution_overlap_unique_of_energyMethod
    {p : CM2Params}
    (hmethod : IntervalDomainClassicalUniquenessEnergyMethod p)
    {u₀ : intervalDomain.Point → ℝ} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomain.Point → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    (htrace₁ : InitialTrace intervalDomain u₀ u₁)
    (htrace₂ : InitialTrace intervalDomain u₀ u₂) :
    ∀ t, 0 < t → t < min T₁ T₂ →
      ∀ x : intervalDomain.Point, u₁ t x = u₂ t x ∧ v₁ t x = v₂ t x :=
  intervalDomain_classicalSolution_overlap_unique_of_energyCertificate
    (hmethod.certificate hsol₁ hsol₂ htrace₁ htrace₂)

/-- L2-energy-method frontier for overlap uniqueness of interval-domain
classical solutions with the same initial `u` trace.

Compared with `IntervalDomainClassicalUniquenessEnergyMethod`, this pins the
energy to the actual interval integral of the squared `u` and `v` differences.
It is the intended interface for a PDE proof based on the usual L2 energy
identity plus Gronwall. -/
structure IntervalDomainClassicalUniquenessL2EnergyMethod
    (p : CM2Params) where
  certificate :
    ∀ {u₀ : intervalDomain.Point → ℝ} {T₁ T₂ : ℝ}
      {u₁ v₁ u₂ v₂ : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
      IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
      InitialTrace intervalDomain u₀ u₁ →
      InitialTrace intervalDomain u₀ u₂ →
        IntervalDomainClassicalOverlapL2EnergyCertificate
          p (min T₁ T₂) u₁ v₁ u₂ v₂

/-- User-facing overlap uniqueness from the concrete L2 energy-method
certificate builder. -/
theorem intervalDomain_classicalSolution_overlap_unique_of_l2EnergyMethod
    {p : CM2Params}
    (hmethod : IntervalDomainClassicalUniquenessL2EnergyMethod p)
    {u₀ : intervalDomain.Point → ℝ} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomain.Point → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    (htrace₁ : InitialTrace intervalDomain u₀ u₁)
    (htrace₂ : InitialTrace intervalDomain u₀ u₂) :
    ∀ t, 0 < t → t < min T₁ T₂ →
      ∀ x : intervalDomain.Point, u₁ t x = u₂ t x ∧ v₁ t x = v₂ t x :=
  intervalDomain_classicalSolution_overlap_unique_of_l2EnergyCertificate
    (hmethod.certificate hsol₁ hsol₂ htrace₁ htrace₂)

end

end ShenWork.Paper2
