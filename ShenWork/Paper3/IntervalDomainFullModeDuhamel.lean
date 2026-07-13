/-
  Full-linearized mode Duhamel formula for the faithful interval equation.

  The Paper2 restart theorem supplies the exact scalar PDE for every cosine
  coefficient of an arbitrary positive classical solution of `intervalDomainM`.
  Here the whole linearization is moved to the left: each perturbation mode is
  propagated by `exp((t-s)*sigma_k)`, including `k=0` with
  `sigma_0=-a*alpha`.  No `(I-P0)` heat projection is used.
-/
import ShenWork.Paper2.IntervalDomainMClassicalRestart
import ShenWork.Paper3.IntervalDomainFullLinearizedSemigroup

namespace ShenWork.Paper3

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.PDE.SectorialOperator
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalConjugateCosineSeries

noncomputable section

/-- Cosine coefficient of the constant equilibrium profile. -/
def paper3EquilibriumCosineCoeff (uStar : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then uStar else 0

/-- Perturbation coefficient `uhat_k-uStar*delta_{k0}`. -/
def paper3PerturbationCoeffM
    (u : ℝ → intervalDomainPoint → ℝ) (uStar : ℝ)
    (t : ℝ) (k : ℕ) : ℝ :=
  solutionCoeffM u t k - paper3EquilibriumCosineCoeff uStar k

/-- Exact nonlinear residual after subtracting the full diagonalized linear
growth `sigma_k` from the faithful modal PDE. -/
def paper3FullModeNonlinearRemainderCoeffM
    (p : CM2Params) (uStar vStar : ℝ)
    (u v : ℝ → intervalDomainPoint → ℝ) (t : ℝ) (k : ℕ) : ℝ :=
  sourceCoeffM p u v t k -
    (unitIntervalCosineEigenvalue k +
      unitIntervalLinearizedGrowth p uStar vStar k) *
        paper3PerturbationCoeffM u uStar t k

/-- Modal logistic remainder after extracting `-a*alpha`. -/
def paper3LogisticRemainderCoeffM
    (p : CM2Params) (uStar : ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) (k : ℕ) : ℝ :=
  cosineCoeffs (logisticLiftedM p (u t)) k +
    p.a * p.α * paper3PerturbationCoeffM u uStar t k

/-- Modal chemotaxis remainder after subtracting the complete eliminated
linear chemotaxis multiplier. -/
def paper3ChemotaxisRemainderCoeffM
    (p : CM2Params) (uStar vStar : ℝ)
    (u v : ℝ → intervalDomainPoint → ℝ) (t : ℝ) (k : ℕ) : ℝ :=
  -p.χ₀ * (((k : ℝ) * Real.pi) *
      intervalSineInner (intervalFluxM p (u t) (v t)) k) -
    (unitIntervalCosineEigenvalue k +
      unitIntervalLinearizedGrowth p uStar vStar k + p.a * p.α) *
        paper3PerturbationCoeffM u uStar t k

/-- Exact separation of the full residual into chemotaxis and logistic
remainders.  Quadratic estimates may therefore be proved for the two physical
mechanisms independently. -/
theorem paper3FullModeNonlinearRemainderCoeffM_eq_parts
    (p : CM2Params) (uStar vStar : ℝ)
    (u v : ℝ → intervalDomainPoint → ℝ) (t : ℝ) (k : ℕ) :
    paper3FullModeNonlinearRemainderCoeffM
        p uStar vStar u v t k =
      paper3ChemotaxisRemainderCoeffM
          p uStar vStar u v t k +
        paper3LogisticRemainderCoeffM p uStar u t k := by
  simp only [paper3FullModeNonlinearRemainderCoeffM,
    paper3ChemotaxisRemainderCoeffM,
    paper3LogisticRemainderCoeffM, sourceCoeffM]
  ring

/-- Chemotaxis contributes neither forcing nor a linear correction to the
zeroth mode. -/
@[simp] theorem paper3ChemotaxisRemainderCoeffM_zero
    (p : CM2Params) (uStar vStar : ℝ)
    (u v : ℝ → intervalDomainPoint → ℝ) (t : ℝ) :
    paper3ChemotaxisRemainderCoeffM p uStar vStar u v t 0 = 0 := by
  simp [paper3ChemotaxisRemainderCoeffM,
    unitIntervalCosineEigenvalue, unitIntervalLinearizedGrowth,
    unitIntervalNeumannSpectrum_hasNeumannSpectrum.zero_eigenvalue, sigma]

lemma unitIntervalCosineEigenvalue_mul_equilibriumCoeff
    (uStar : ℝ) (k : ℕ) :
    unitIntervalCosineEigenvalue k *
      paper3EquilibriumCosineCoeff uStar k = 0 := by
  by_cases hk : k = 0
  · subst k
    simp [paper3EquilibriumCosineCoeff, unitIntervalCosineEigenvalue]
  · simp [paper3EquilibriumCosineCoeff, hk]

/-- Every faithful classical perturbation coefficient solves the exact full
linearized scalar ODE `c'=sigma_k*c+R_k`. -/
theorem paper3PerturbationCoeffM_hasDerivAt_full
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) (k : ℕ) :
    HasDerivAt (fun s => paper3PerturbationCoeffM u uStar s k)
      (unitIntervalLinearizedGrowth p uStar vStar k *
          paper3PerturbationCoeffM u uStar t k +
        paper3FullModeNonlinearRemainderCoeffM
          p uStar vStar u v t k) t := by
  have hmode := solutionCoeffM_hasDerivAt_pde hsol ht0 htT k
  have hder := hmode.sub_const (paper3EquilibriumCosineCoeff uStar k)
  convert hder using 1
  simp only [paper3FullModeNonlinearRemainderCoeffM,
    paper3PerturbationCoeffM]
  have heqzero := unitIntervalCosineEigenvalue_mul_equilibriumCoeff uStar k
  ring_nf at heqzero ⊢
  linarith

/-- The full nonlinear remainder coefficient is continuous on each compact
positive-time window. -/
theorem paper3FullModeNonlinearRemainderCoeffM_continuousOn
    {p : CM2Params} {T a b uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (k : ℕ) :
    ContinuousOn
      (fun s => paper3FullModeNonlinearRemainderCoeffM
        p uStar vStar u v s k) (Set.Icc a b) := by
  have hsrc := sourceCoeffM_continuousOn hsol ha hab hbT k
  have hc := solutionCoeffM_continuousOn hsol ha hab hbT k
  have hpert : ContinuousOn
      (fun s => paper3PerturbationCoeffM u uStar s k) (Set.Icc a b) :=
    hc.sub continuousOn_const
  exact hsrc.sub (continuousOn_const.mul hpert)

/-- Exact restart-time variation-of-constants formula with the complete modal
multiplier `sigma_k`. -/
theorem paper3PerturbationCoeffM_full_restart
    {p : CM2Params} {T a t uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hat : a ≤ t) (htT : t < T) (k : ℕ) :
    paper3PerturbationCoeffM u uStar t k =
      Real.exp ((t - a) *
          unitIntervalLinearizedGrowth p uStar vStar k) *
        paper3PerturbationCoeffM u uStar a k +
      ∫ s in a..t,
        Real.exp ((t - s) *
          unitIntervalLinearizedGrowth p uStar vStar k) *
            paper3FullModeNonlinearRemainderCoeffM
              p uStar vStar u v s k := by
  let growth : ℝ := unitIntervalLinearizedGrowth p uStar vStar k
  let c : ℝ → ℝ := fun s => paper3PerturbationCoeffM u uStar s k
  let rem : ℝ → ℝ := fun s =>
    paper3FullModeNonlinearRemainderCoeffM p uStar vStar u v s k
  let G : ℝ → ℝ := fun s => Real.exp ((t - s) * growth) * c s
  have hccont : ContinuousOn c (Set.Icc a t) := by
    have hc := solutionCoeffM_continuousOn hsol ha hat htT k
    exact hc.sub continuousOn_const
  have hremcont : ContinuousOn rem (Set.Icc a t) := by
    simpa [rem] using
      paper3FullModeNonlinearRemainderCoeffM_continuousOn
        hsol ha hat htT k
  have hGcont : ContinuousOn G (Set.Icc a t) := by
    have hexp : Continuous
        (fun s : ℝ => Real.exp ((t - s) * growth)) := by fun_prop
    exact hexp.continuousOn.mul hccont
  have hderiv : ∀ s ∈ Set.Ioo a t,
      HasDerivAt G (Real.exp ((t - s) * growth) * rem s) s := by
    intro s hs
    have hs0 : 0 < s := lt_trans ha hs.1
    have hsT : s < T := lt_trans hs.2 htT
    have hcder := paper3PerturbationCoeffM_hasDerivAt_full
      (uStar := uStar) (vStar := vStar) hsol hs0 hsT k
    have harg : HasDerivAt (fun r : ℝ => (t - r) * growth) (-growth) s := by
      convert ((hasDerivAt_const s t).sub (hasDerivAt_id s)).mul_const growth
        using 1
      all_goals ring_nf
    have hexp : HasDerivAt (fun r : ℝ => Real.exp ((t - r) * growth))
        (Real.exp ((t - s) * growth) * (-growth)) s := harg.exp
    have hprod := hexp.mul hcder
    convert hprod using 1
    dsimp [c, rem, growth]
    ring
  have hint : IntervalIntegrable
      (fun s => Real.exp ((t - s) * growth) * rem s) volume a t := by
    have hexp : Continuous
        (fun s : ℝ => Real.exp ((t - s) * growth)) := by fun_prop
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hat]
    exact hexp.continuousOn.mul hremcont
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hat hGcont hderiv hint
  dsimp [G, c, rem, growth] at hFTC ⊢
  rw [hFTC]
  simp

/-- Exact zero-start variation-of-constants formula.

The classical PDE supplies the modal ODE only at positive times.  For the
strong-space theorem the missing endpoint information is precisely continuity
of the perturbation coefficient at zero and interval-integrability of the
nonlinear remainder.  Under those two hypotheses the ordinary closed-interval
FTC applies directly, so no limiting restart argument is needed. -/
theorem paper3PerturbationCoeffM_full_zero
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : 0 ≤ t) (htT : t < T) (k : ℕ)
    (hccont : ContinuousOn
      (fun s => paper3PerturbationCoeffM u uStar s k)
      (Set.Icc (0 : ℝ) t))
    (hremInt : IntervalIntegrable
      (fun s => paper3FullModeNonlinearRemainderCoeffM
        p uStar vStar u v s k) volume 0 t) :
    paper3PerturbationCoeffM u uStar t k =
      Real.exp (t * unitIntervalLinearizedGrowth p uStar vStar k) *
        paper3PerturbationCoeffM u uStar 0 k +
      ∫ s in (0 : ℝ)..t,
        Real.exp ((t - s) *
          unitIntervalLinearizedGrowth p uStar vStar k) *
            paper3FullModeNonlinearRemainderCoeffM
              p uStar vStar u v s k := by
  let growth : ℝ := unitIntervalLinearizedGrowth p uStar vStar k
  let c : ℝ → ℝ := fun s => paper3PerturbationCoeffM u uStar s k
  let rem : ℝ → ℝ := fun s =>
    paper3FullModeNonlinearRemainderCoeffM p uStar vStar u v s k
  let G : ℝ → ℝ := fun s => Real.exp ((t - s) * growth) * c s
  have hGcont : ContinuousOn G (Set.Icc (0 : ℝ) t) := by
    have hexp : Continuous
        (fun s : ℝ => Real.exp ((t - s) * growth)) := by fun_prop
    exact hexp.continuousOn.mul (by simpa [c] using hccont)
  have hderiv : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      HasDerivAt G (Real.exp ((t - s) * growth) * rem s) s := by
    intro s hs
    have hsT : s < T := lt_trans hs.2 htT
    have hcder := paper3PerturbationCoeffM_hasDerivAt_full
      (uStar := uStar) (vStar := vStar) hsol hs.1 hsT k
    have harg : HasDerivAt (fun r : ℝ => (t - r) * growth) (-growth) s := by
      convert ((hasDerivAt_const s t).sub (hasDerivAt_id s)).mul_const growth
        using 1
      all_goals ring_nf
    have hexp : HasDerivAt (fun r : ℝ => Real.exp ((t - r) * growth))
        (Real.exp ((t - s) * growth) * (-growth)) s := harg.exp
    have hprod := hexp.mul hcder
    convert hprod using 1
    dsimp [c, rem, growth]
    ring
  have hint : IntervalIntegrable
      (fun s => Real.exp ((t - s) * growth) * rem s) volume 0 t := by
    have hexp : Continuous
        (fun s : ℝ => Real.exp ((t - s) * growth)) := by fun_prop
    have hrem : IntervalIntegrable rem volume 0 t := by
      simpa [rem] using hremInt
    exact hrem.continuousOn_mul hexp.continuousOn
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    ht hGcont hderiv hint
  dsimp [G, c, rem, growth] at hFTC ⊢
  rw [hFTC]
  simp

#print axioms paper3PerturbationCoeffM_hasDerivAt_full
#print axioms paper3FullModeNonlinearRemainderCoeffM_eq_parts
#print axioms paper3ChemotaxisRemainderCoeffM_zero
#print axioms paper3FullModeNonlinearRemainderCoeffM_continuousOn
#print axioms paper3PerturbationCoeffM_full_restart
#print axioms paper3PerturbationCoeffM_full_zero

end

end ShenWork.Paper3
