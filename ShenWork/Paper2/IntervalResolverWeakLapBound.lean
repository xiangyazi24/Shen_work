/-
Non-circular M-ball bound for the resolver's physical second derivative.

Uses the elliptic identity R'' = μR - ρ(u) to bound |R''| ≤ μ·V_M + ν·M^γ
without requiring gradient bounds on u. This avoids the circularity in the
spectral route (resolverGrad2Real_bounded_of_sourceDecay needs SourceCoeffQuadraticDecay).

Source: ChatGPT Q3968 (resolver_H_M_bound), verified by structural analysis.
-/
import ShenWork.Paper2.IntervalResolverWeakBounds
import ShenWork.Paper2.Statements
import ShenWork.PDE.IntervalNeumannEllipticResolverR

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.PDE
open ShenWork.Paper2
open ShenWork.IntervalResolverWeakBounds
open scoped Topology BigOperators

noncomputable section

namespace ShenWork.IntervalResolverWeakBounds

def resolverPositiveSourceLifted (p : CM2Params)
    (u : intervalDomainPoint → ℝ) : ℝ → ℝ :=
  fun x => p.ν * (positivePart (intervalDomainLift u x)) ^ p.γ

def resolverLapPhysical (p : CM2Params)
    (u : intervalDomainPoint → ℝ) : intervalDomainPoint → ℝ :=
  fun y => p.μ * intervalNeumannResolverR p u y -
    resolverPositiveSourceLifted p u y.1

def resolverWeakValueBound (p : CM2Params) (M : ℝ) : ℝ :=
  Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) *
    (2 * (p.ν * M ^ p.γ))

def resolverWeakLapBound (p : CM2Params) (M : ℝ) : ℝ :=
  p.μ * resolverWeakValueBound p M + p.ν * M ^ p.γ

theorem resolverPositiveSourceLifted_abs_le_of_bounded
    (p : CM2Params) {u : intervalDomainPoint → ℝ} {M x : ℝ}
    (hlb : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift u y)
    (hub : ∀ y ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift u y ≤ M)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |resolverPositiveSourceLifted p u x| ≤ p.ν * M ^ p.γ := by
  have hux_nonneg : 0 ≤ intervalDomainLift u x := hlb x hx
  have hux_le : intervalDomainLift u x ≤ M := hub x hx
  have hpp_eq : positivePart (intervalDomainLift u x) = intervalDomainLift u x :=
    positivePart_eq_self_of_nonneg hux_nonneg
  have hpp_nonneg : 0 ≤ positivePart (intervalDomainLift u x) := positivePart_nonneg _
  have hpp_le : positivePart (intervalDomainLift u x) ≤ M := by
    simpa [hpp_eq] using hux_le
  have hpow_le :
      (positivePart (intervalDomainLift u x)) ^ p.γ ≤ M ^ p.γ := by
    exact Real.rpow_le_rpow hpp_nonneg hpp_le p.hγ.le
  have hsrc_nonneg :
      0 ≤ p.ν * (positivePart (intervalDomainLift u x)) ^ p.γ :=
    mul_nonneg p.hν.le (Real.rpow_nonneg hpp_nonneg _)
  calc
    |resolverPositiveSourceLifted p u x|
        = p.ν * (positivePart (intervalDomainLift u x)) ^ p.γ := by
          simp [resolverPositiveSourceLifted, abs_of_nonneg hsrc_nonneg]
    _ ≤ p.ν * M ^ p.γ :=
          mul_le_mul_of_nonneg_left hpow_le p.hν.le

theorem resolverLapPhysical_abs_le_of_bounded
    (p : CM2Params) {u : intervalDomainPoint → ℝ} {M : ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    (hlb : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift u y)
    (hub : ∀ y ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift u y ≤ M)
    (y : intervalDomainPoint) :
    |resolverLapPhysical p u y| ≤ resolverWeakLapBound p M := by
  have hR : |intervalNeumannResolverR p u y| ≤ resolverWeakValueBound p M := by
    simpa [resolverWeakValueBound] using
      resolverValue_sup_le_of_bounded p hUcont hlb hub y
  have hsrc : |resolverPositiveSourceLifted p u y.1| ≤ p.ν * M ^ p.γ :=
    resolverPositiveSourceLifted_abs_le_of_bounded p hlb hub y.2
  calc
    |resolverLapPhysical p u y|
        = |p.μ * intervalNeumannResolverR p u y -
            resolverPositiveSourceLifted p u y.1| := by
          rfl
    _ ≤ |p.μ * intervalNeumannResolverR p u y| +
          |resolverPositiveSourceLifted p u y.1| := abs_sub _ _
    _ = p.μ * |intervalNeumannResolverR p u y| +
          |resolverPositiveSourceLifted p u y.1| := by
          rw [abs_mul, abs_of_pos p.hμ]
    _ ≤ p.μ * resolverWeakValueBound p M + p.ν * M ^ p.γ := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hR p.hμ.le)
            hsrc
    _ = resolverWeakLapBound p M := by
          rfl

theorem exists_resolverLapPhysical_bound_of_bounded
    (p : CM2Params) {u : intervalDomainPoint → ℝ} {M : ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    (hlb : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift u y)
    (hub : ∀ y ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift u y ≤ M) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ y : intervalDomainPoint,
      |resolverLapPhysical p u y| ≤ H := by
  refine ⟨resolverWeakLapBound p M, ?_, ?_⟩
  · have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
    have hMnn : 0 ≤ M := (hlb 0 h0).trans (hub 0 h0)
    have hMpow : 0 ≤ M ^ p.γ := Real.rpow_nonneg hMnn _
    have hsrcB : 0 ≤ p.ν * M ^ p.γ := mul_nonneg p.hν.le hMpow
    have hV : 0 ≤ resolverWeakValueBound p M := by
      unfold resolverWeakValueBound
      exact mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (by norm_num) hsrcB)
    unfold resolverWeakLapBound
    exact add_nonneg (mul_nonneg p.hμ.le hV) hsrcB
  · intro y
    exact resolverLapPhysical_abs_le_of_bounded p hUcont hlb hub y

/-- Green/ODE regularity bridge: continuous source → resolver is C² → R'' = μR - ρ(u).
Uses the 1D Neumann Green kernel or weak-to-classical ODE regularity, NOT the spectral
R'' Fourier series (which requires SourceCoeffQuadraticDecay). -/
theorem resolverGradReal_hasDerivAt_physicalLap_of_continuousOn
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun z : ℝ => resolverGradReal p u z)
      (resolverLapPhysical p u ⟨x, Set.Ioo_subset_Icc_self hx⟩) x := by
  sorry

theorem deriv_resolverGradReal_abs_le_of_bounded
    (p : CM2Params) {u : intervalDomainPoint → ℝ} {M : ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    (hlb : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift u y)
    (hub : ∀ y ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift u y ≤ M)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    |deriv (fun z : ℝ => resolverGradReal p u z) x| ≤ resolverWeakLapBound p M := by
  have hder := resolverGradReal_hasDerivAt_physicalLap_of_continuousOn p hUcont hx
  rw [hder.deriv]
  exact resolverLapPhysical_abs_le_of_bounded p hUcont hlb hub
    ⟨x, Set.Ioo_subset_Icc_self hx⟩

end ShenWork.IntervalResolverWeakBounds
