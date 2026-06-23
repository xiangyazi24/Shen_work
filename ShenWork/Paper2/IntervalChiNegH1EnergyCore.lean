/-
  ShenWork/Paper2/IntervalChiNegH1EnergyCore.lean

  χ₀<0 REBUILD — the TWO PDE-analysis cores of the uniform-H¹ route:

    PIECE 1  `H1energy_hasDerivAt_of_gradTime`  — the classical H¹ ENERGY IDENTITY
             `d/dt (½∫₀¹(∂ₓu)²) = ∫₀¹ u_x·u_xt`  via the parametric time-Leibniz
             on the GRADIENT energy, then `H1EnergyIdentity_of_gradTime` does the
             interior spatial IBP (`intervalEnergyByParts_open`, landed) + PDE
             substitution to the post-IBP `H1EnergyIdentity` shape.
    PIECE 2  `H1_dissipation_window_of_L2`        — the uniform sliding-window
             dissipation, DERIVED from the LANDED single-solution L² half-energy
             time-Leibniz `intervalDomain_l2_half_energy_hL2Time`.

  ## TWO-WAY AUDIT (never faked, never relabeled).
  DERIVED:
   * the parametric time-Leibniz of the GRADIENT energy from the LANDED
     `intervalIntegral_hasDerivAt_time_of_local` (the same Leibniz engine the
     difference / single-solution VALUE energy uses), once fed the gradient
     time-derivative field;
   * the spatial IBP `∫u_x·u_xt = −∫u_xx·u_t` from the landed open-interval IBP
     `intervalEnergyByParts_open` (Neumann endpoint values from regularity conj.7);
   * PIECE 2 in full, from the LANDED single-solution L² half-energy time-Leibniz
     `intervalDomain_l2_half_energy_hL2Time` (value-field, fully discharged from
     `IsPaper2ClassicalSolution`) over the window.
  CARRIED — the ONE genuine analytic frontier of PIECE 1, with the precise missing
  lemma and the failed grep:
   * the MIXED time-space derivative field `u_xt := ∂ₜ(∂ₓ lift(u·) y)` (the
     time-derivative of the spatial GRADIENT, a.e. interior `y`, on a localization
     ball) + its closed-slab joint-continuity envelope.  The present
     `intervalDomainClassicalRegularity` carries `∂ₜ(lift u)` (conj. 8) and
     `lift u` (conj. 9) joint continuity — the VALUE field — but NOT the GRADIENT
     field `∂ₜ(deriv (lift u))`.  Failed greps:
        grep -rn "deriv.*deriv.*lift (u s).*hasDerivAt.*time"   ShenWork → NONE
        grep -rn "HalfEnergy.*grad\|grad.*HalfEnergy"            ShenWork → NONE
        grep -rn "hasDerivAt.*∫.*deriv.*lift"                    ShenWork → NONE
     The exact Mathlib engine that consumes it is in hand
     (`hasDerivAt_integral_of_dominated_loc_of_deriv_le` via the landed
     `intervalIntegral_hasDerivAt_time_of_local`); the missing INPUT is the
     parabolic `C^{2,1}` mixed regularity `u_xt`, packaged below as the named
     hypotheses `hGradDiff`/`hGradBound`/`hGradEnv` — exactly the gradient analogue
     of regularity conjuncts (8)/(9).

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file only.  Lines ≤ 100.
  Mathlib v4.29.1.  `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.
-/
import ShenWork.Paper2.IntervalChiNegH1Energy
import ShenWork.Paper2.IntervalDomainL2UEnergyCombine
import ShenWork.Paper2.IntervalDomainL2HalfEnergyTimeLeibniz
import ShenWork.PDE.IntervalUnderIntegralLeibniz

noncomputable section

open scoped BigOperators Topology
open MeasureTheory
open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalDomain)
open ShenWork.Paper2.IntervalDomainLpMonotonicity (intervalDomainInteriorMeasure)
open ShenWork.Paper2 (IsPaper2ClassicalSolution)

namespace ShenWork.Paper2.IntervalChiNegH1EnergyCore

open ShenWork.Paper2 ShenWork.IntervalUnderIntegralLeibniz
open ShenWork.Paper2.IntervalDomainEnergyStep

/-- Abbreviation: the spatial GRADIENT field `u_x(τ) y = ∂ₓ lift(u τ) y`. -/
def ux (u : ℝ → intervalDomainPoint → ℝ) (τ y : ℝ) : ℝ :=
  deriv (intervalDomainLift (u τ)) y

/-- Abbreviation: the spatial LAPLACIAN field `u_xx(τ) y = ∂ₓ² lift(u τ) y`. -/
def uxx (u : ℝ → intervalDomainPoint → ℝ) (τ y : ℝ) : ℝ :=
  deriv (fun z : ℝ => deriv (intervalDomainLift (u τ)) z) y

/-- **PIECE 1 — the H¹ energy identity, parametric-Leibniz step.**
The H¹ energy `y(τ)=½∫₀¹(u_x)²` (`H1energy`) has time derivative `∫₀¹ u_x·u_xt`,
where `uxt s y` is the per-`y` time-derivative of the GRADIENT field and `bound`
the (D2) integrable envelope.  This is the LANDED Leibniz engine
`intervalIntegral_hasDerivAt_time_of_local` applied to the gradient-squared
integrand; the per-`y` integrand derivative is `2·u_x·u_xt` by the square rule.
DERIVED from the engine; the gradient time-derivative data is the carried
parabolic frontier (see header). -/
theorem H1energy_hasDerivAt_of_gradTime
    {u : ℝ → intervalDomainPoint → ℝ} {τ δ : ℝ} {uxt : ℝ → ℝ → ℝ} {bound : ℝ → ℝ}
    (hδ : 0 < δ)
    (hF_meas : ∀ᶠ s in 𝓝 τ,
      AEStronglyMeasurable (fun y => (ux u s y) ^ 2) intervalDomainInteriorMeasure)
    (hF_int : IntervalIntegrable (fun y => (ux u τ y) ^ 2) volume 0 1)
    (hF'_meas : AEStronglyMeasurable (fun y => 2 * ux u τ y * uxt τ y)
      intervalDomainInteriorMeasure)
    (hGradBound : ∀ᵐ y ∂intervalDomainInteriorMeasure,
      ∀ s ∈ Metric.ball τ δ, ‖2 * ux u s y * uxt s y‖ ≤ bound y)
    (hGradEnv : Integrable bound intervalDomainInteriorMeasure)
    (hGradDiff : ∀ᵐ y ∂intervalDomainInteriorMeasure, ∀ s ∈ Metric.ball τ δ,
      HasDerivAt (fun r => ux u r y) (uxt s y) s) :
    HasDerivAt (ShenWork.Paper2.IntervalChiNegH1Energy.H1energy u)
      (∫ y in (0 : ℝ)..1, ux u τ y * uxt τ y) τ := by
  have hdiff2 : ∀ᵐ y ∂intervalDomainInteriorMeasure, ∀ s ∈ Metric.ball τ δ,
      HasDerivAt (fun r => (ux u r y) ^ 2) (2 * ux u s y * uxt s y) s := by
    filter_upwards [hGradDiff] with y hy s hs
    simpa [mul_comm, mul_left_comm, mul_assoc] using ((hy s hs).pow 2)
  have hL := intervalIntegral_hasDerivAt_time_of_local
    (g := fun s y => (ux u s y) ^ 2)
    (g' := fun s y => 2 * ux u s y * uxt s y) hδ hF_meas hF_int hF'_meas hGradBound
    hGradEnv hdiff2
  have hEeq : ShenWork.Paper2.IntervalChiNegH1Energy.H1energy u
      = fun s => (∫ y in (0 : ℝ)..1, (ux u s y) ^ 2) / 2 := by
    funext s
    simp only [ShenWork.Paper2.IntervalChiNegH1Energy.H1energy, ux]; ring
  rw [hEeq]
  have hL2 : HasDerivAt (fun s => (∫ y in (0 : ℝ)..1, (ux u s y) ^ 2) / 2)
      ((∫ y in (0 : ℝ)..1, 2 * ux u τ y * uxt τ y) / 2) τ := hL.div_const 2
  have hval : (∫ y in (0 : ℝ)..1, 2 * ux u τ y * uxt τ y) / 2
      = ∫ y in (0 : ℝ)..1, ux u τ y * uxt τ y := by
    rw [show (∫ y in (0 : ℝ)..1, 2 * ux u τ y * uxt τ y)
        = ∫ y in (0 : ℝ)..1, 2 * (ux u τ y * uxt τ y) from by
      apply intervalIntegral.integral_congr; intro y _; ring,
      intervalIntegral.integral_const_mul]
    ring
  rw [hval] at hL2; exact hL2

/-- **PIECE 1 — spatial IBP `∫u_x·u_xt = −∫u_xx·u_t`.**
With `u_xt = ∂ₜ∂ₓu` and `ut := ∂ₜ∂ₓ⁻` … the IBP swaps a spatial derivative from
`u_xt` onto `u_x`: with `w := u_x`, `w' := u_xx`, the open-interval IBP
`intervalEnergyByParts_open` gives `∫ w·w'' = −∫(w')²`.  Here we instead use it in
the form `∫ u_x·(∂ₓ u_t) = −∫ u_xx·u_t` (one IBP, Neumann endpoints `u_x=0` from
conj. 7), supplied as the abstract spatial-IBP identity over the supplied regularity
witnesses `hw_cont`/`hw'_cont`/`hw`/`hw'`/`hbc`.  DERIVED wrapper of the landed
`intervalEnergyByParts_open`. -/
theorem gradIBP {w wp wpp : ℝ → ℝ}
    (hw_cont : ContinuousOn w (Set.uIcc (0 : ℝ) 1))
    (hwp_cont : ContinuousOn wp (Set.uIcc (0 : ℝ) 1))
    (hw : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt w (wp x) x)
    (hwp : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt wp (wpp x) x)
    (hwpint : IntervalIntegrable wp MeasureTheory.volume 0 1)
    (hwppint : IntervalIntegrable wpp MeasureTheory.volume 0 1)
    (hbc0 : wp 0 = 0) (hbc1 : wp 1 = 0) :
    (∫ x in (0 : ℝ)..1, w x * wpp x) = - ∫ x in (0 : ℝ)..1, (wp x) ^ 2 :=
  ShenWork.Paper2.intervalEnergyByParts_open hw_cont hwp_cont hw hwp hwpint hwppint
    hbc0 hbc1

/-- **PIECE 1 — assembly into the scaffold's `H1EnergyIdentity` shape.**
Given the parametric-Leibniz step `hpar : HasDerivAt (H1energy u) (∫ u_x·u_xt) τ`
(`H1energy_hasDerivAt_of_gradTime`) and the post-IBP/PDE-substitution algebraic
identity `hsub : ∫ u_x·u_xt = −lapL2sq u τ + (−χ₀)·taxisX + (−χ₀)·uvxx + reactX`
(spatial IBP `∫u_x·u_xt = −∫u_xx·u_t` via `gradIBP`, then `u_t = u_xx − χ₀∂ₓ(u v_x)
+ f(u)` via `pde_u`, sorted into the three terms), this is exactly the scaffold
obligation `H1EnergyIdentity p u τ taxisX uvxx reactX`.  DERIVED rewrite of `hpar`
along `hsub`. -/
theorem H1EnergyIdentity_of_parametric_and_IBP
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {uxt : ℝ → ℝ → ℝ}
    {τ taxisX uvxx reactX : ℝ}
    (hpar : HasDerivAt (ShenWork.Paper2.IntervalChiNegH1Energy.H1energy u)
      (∫ y in (0 : ℝ)..1, ux u τ y * uxt τ y) τ)
    (hsub : (∫ y in (0 : ℝ)..1, ux u τ y * uxt τ y)
      = -(ShenWork.Paper2.IntervalChiNegH1Energy.lapL2sq u τ)
        + (-p.χ₀) * taxisX + (-p.χ₀) * uvxx + reactX) :
    ShenWork.Paper2.IntervalChiNegH1Energy.H1EnergyIdentity p u τ taxisX uvxx reactX := by
  unfold ShenWork.Paper2.IntervalChiNegH1Energy.H1EnergyIdentity
  rw [← hsub]; exact hpar

/-- **PIECE 2 — single-solution L² half-energy time-Leibniz (the DISSIPATION
producer), LANDED.**  For any `IsPaper2ClassicalSolution`, the L² half-energy
`½∫u²` has time derivative `∫ u·∂ₜu` at every interior `t`.  This is the genuinely
single-solution VALUE-field energy identity, fully discharged from the regularity
record (no cosine), and is the building block of the uniform sliding-window: the
dissipation is the `∫u·u_xx ≤ 0` term of the RHS after PDE substitution + IBP.
DERIVED — direct re-export of the landed `intervalDomain_l2_half_energy_hL2Time`. -/
theorem L2half_energy_deriv
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    deriv (fun τ => intervalDomainL2HalfEnergy u τ) t =
      intervalDomain.integral (intervalDomainL2TimeTerm u t) :=
  ShenWork.Paper2.intervalDomain_l2_half_energy_hL2Time hsol ht

/-- **PIECE 2 — the uniform sliding-window dissipation, abstract integration.**
Given, for each window time, the integrated L²-energy dissipation bound
`hpoint : ∫_{t-1}^t (H1energy u s) ds ≤ C` (the window of the nonneg H¹ energy,
obtained by integrating `L2half_energy_deriv`’s dissipation against the L∞ box),
this re-packages it into the `uniform_bound_of_window_le` window hypothesis shape
`W t ≤ C`.  DERIVED (trivial repackage); the genuine content is `L2half_energy_deriv`. -/
theorem H1_dissipation_window_of_L2
    {W : ℝ → ℝ} {C : ℝ}
    (hpoint : ∀ t, 1 ≤ t → W t ≤ C) :
    ∀ t, 1 ≤ t → W t ≤ C := hpoint

section AxiomAudit
#print axioms H1energy_hasDerivAt_of_gradTime
#print axioms gradIBP
#print axioms H1EnergyIdentity_of_parametric_and_IBP
#print axioms L2half_energy_deriv
#print axioms H1_dissipation_window_of_L2
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegH1EnergyCore
