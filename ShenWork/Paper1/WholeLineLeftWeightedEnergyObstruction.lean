import ShenWork.Paper1.WholeLineWeightedRegularityHCoreEnergyNatural

/-!
# Why the global left-growing mirror energy cannot be initialized

The right-weighted hcore uses `exp (2 * eta * x)`, which decays at the end not
controlled by the initial weighted norm.  Replacing it by
`exp (-2 * eta * x)` is not a harmless reflection: the hypotheses only give
`StrictlyPositiveAtLeft u₀`, not convergence of `u₀` to the equilibrium `1`.
Consequently the perturbation `u₀ - 1` may stay bounded away from zero along
the entire far-left tail.

The theorem below makes the obstruction independent of any PDE bookkeeping:
every such perturbation has infinite left-growing weighted `L²` mass.  Thus a
global exponential mirror (and likewise a two-sided weight) cannot be the
starting energy for the datum class of the whole-line Cauchy theorem.  A
translated localizing weight is finite, but its quadratic reaction
dissipation degenerates near the other equilibrium `u = 0`; it therefore
needs an independent persistent positive floor before a near-equilibrium
spectral estimate can start.
-/

open Filter MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-- A perturbation which is uniformly nonzero at the left end cannot belong
to the exponentially left-weighted `L²` space. -/
theorem not_integrable_leftGrowing_sq_of_eventually_abs_ge
    {eta d : ℝ} {w : ℝ → ℝ} (heta : 0 < eta) (hd : 0 < d)
    (hw : ∀ᶠ x : ℝ in atBot, d ≤ |w x|) :
    ¬ Integrable
      (fun x : ℝ => Real.exp (-2 * eta * x) * |w x| ^ 2) := by
  intro hInt
  obtain ⟨R, hR⟩ := eventually_atBot.1 hw
  let B : ℝ := min R 0
  have hBR : B ≤ R := min_le_left _ _
  have hB0 : B ≤ 0 := min_le_right _ _
  have hIntIic : IntegrableOn
      (fun x : ℝ => Real.exp (-2 * eta * x) * |w x| ^ 2)
      (Set.Iic B) := hInt.integrableOn
  have hconst : IntegrableOn (fun _ : ℝ => d ^ 2) (Set.Iic B) := by
    apply Integrable.mono hIntIic
    · fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
      have hxR : x ≤ R := hx.trans hBR
      have hx0 : x ≤ 0 := hx.trans hB0
      have hwd : d ≤ |w x| := hR x hxR
      have hexp : 1 ≤ Real.exp (-2 * eta * x) := by
        rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        nlinarith
      change |d ^ 2| ≤
        |Real.exp (-2 * eta * x) * |w x| ^ 2|
      rw [abs_of_pos (sq_pos_of_pos hd),
        abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
      have hsq : d ^ 2 ≤ |w x| ^ 2 := by
        nlinarith [abs_nonneg (w x)]
      have hnonneg : 0 ≤ |w x| ^ 2 := sq_nonneg _
      have hprod : |w x| ^ 2 ≤
          Real.exp (-2 * eta * x) * |w x| ^ 2 := by
        nlinarith
      exact hsq.trans hprod
  have hconstCriterion :=
    (integrableOn_const_iff (C := d ^ 2)).mp hconst
  rcases hconstCriterion with hzero | hfinite
  · have hne : d ^ 2 ≠ 0 := pow_ne_zero 2 hd.ne'
    exact hne (by simpa using hzero)
  · rw [Real.volume_Iic] at hfinite
    exact (not_lt_of_ge le_rfl) hfinite

/-- In particular, a profile with a non-unit far-left limit cannot initialize
the proposed mirror energy for its perturbation from `1`. -/
theorem not_integrable_leftGrowing_equilibrium_error_of_tendsto
    {eta a : ℝ} {u : ℝ → ℝ} (heta : 0 < eta) (ha : a ≠ 1)
    (hu : Tendsto u atBot (nhds a)) :
    ¬ Integrable
      (fun x : ℝ => Real.exp (-2 * eta * x) * |u x - 1| ^ 2) := by
  let d : ℝ := |a - 1| / 2
  have haabs : 0 < |a - 1| := abs_pos.mpr (sub_ne_zero.mpr ha)
  have hd : 0 < d := half_pos haabs
  have hball : Metric.ball a d ∈ nhds a := Metric.ball_mem_nhds _ hd
  have hevent := hu hball
  have htail : ∀ᶠ x : ℝ in atBot, d ≤ |u x - 1| := by
    filter_upwards [hevent] with x hx
    have hx' : |u x - a| < d := by
      simpa [Metric.mem_ball, Real.dist_eq] using hx
    have htri : |a - 1| ≤ |a - u x| + |u x - 1| := by
      calc
        |a - 1| = |(a - u x) + (u x - 1)| := by ring_nf
        _ ≤ |a - u x| + |u x - 1| := abs_add_le _ _
    rw [abs_sub_comm a (u x)] at htri
    dsimp only [d] at hx' ⊢
    linarith
  exact not_integrable_leftGrowing_sq_of_eventually_abs_ge heta hd htail

section AxiomAudit

#print axioms not_integrable_leftGrowing_sq_of_eventually_abs_ge
#print axioms not_integrable_leftGrowing_equilibrium_error_of_tendsto

end AxiomAudit

end ShenWork.Paper1
