/-
  Exact coefficient and mean-mode identities for the Paper3 interval flow.

  These are the representation-side inputs to the nonlinear Duhamel argument:
  cosine coefficients can be differentiated at every positive interior time,
  chemotactic divergence has exactly zero mean, and the only mean forcing is
  the nonlinear logistic remainder.
-/
import ShenWork.Paper2.IntervalDomainMass
import ShenWork.Paper2.IntervalMildPicardRegularity
import ShenWork.PDE.IntervalSolutionCoeffDeriv

namespace ShenWork.Paper3

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain
open ShenWork.IntervalUnderIntegralLeibniz
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalMildPicardRegularity
open ShenWork.Paper2

noncomputable section

/-- Cosine coefficients of every classical solution slice may be
differentiated under the spatial integral at positive interior times. -/
theorem intervalDomain_solution_cosineCoeffs_hasDerivAt
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) (n : ℕ) :
    HasDerivAt
      (fun s => cosineCoeffs (intervalDomainLift (u s)) n)
      (cosineCoeffs (intervalDomainMassTimeDerivIntegrand u t) n) t := by
  obtain ⟨δ, hδ, hball, hIcc⟩ := exists_closedSlab_subset ht
  have hfield : ContinuousOn
      (Function.uncurry (fun (s : ℝ) (x : ℝ) => intervalDomainLift (u s) x))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    hsol.regularity.2.2.2.2.2.2.1
  have hf_int : ∀ᶠ s in nhds t,
      IntervalIntegrable (intervalDomainLift (u s)) volume (0 : ℝ) 1 := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    have hslice : ContinuousOn (intervalDomainLift (u s)) (Set.Icc (0 : ℝ) 1) :=
      intervalDomain_continuousOn_timeSlice hfield hs
    have hslice' : ContinuousOn (intervalDomainLift (u s))
        (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using hslice
    exact hslice'.intervalIntegrable
  have hdiff : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball t δ,
      HasDerivAt (fun r => intervalDomainLift (u r) x)
        (intervalDomainMassTimeDerivIntegrand u s x) s := by
    intro x hx s hs
    exact intervalDomainMassIntegrand_hasDerivAt_interior hsol hx (hball hs)
  have hjoint : ContinuousOn
      (Function.uncurry (intervalDomainMassTimeDerivIntegrand u))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    hsol.regularity.2.2.2.2.2.1.1
  have hslab : ContinuousOn
      (Function.uncurry (intervalDomainMassTimeDerivIntegrand u))
      (Set.Icc (t - δ) (t + δ) ×ˢ Set.Icc (0 : ℝ) 1) :=
    hjoint.mono (Set.prod_mono hIcc (le_refl _))
  exact cosineCoeffs_hasDerivAt_of_smooth_param hδ hf_int hdiff hslab

/-- The zero cosine coefficient is the physical spatial mean on `[0,1]`. -/
theorem intervalDomain_cosineCoeffs_zero_eq_integral
    (f : intervalDomain.Point → ℝ) :
    cosineCoeffs (intervalDomainLift f) 0 = intervalDomain.integral f := by
  rw [cosineCoeffs_zero_eq_integral]
  rfl

/-- The chemotactic source is exactly mean-zero for every positive classical
time; no estimate or smallness assumption is involved. -/
theorem intervalDomain_solution_chemotaxis_zeroCoeff
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    cosineCoeffs
        (intervalDomainLift
          (fun x => intervalDomain.chemotaxisDiv p (u t) (v t) x)) 0 = 0 := by
  rw [intervalDomain_cosineCoeffs_zero_eq_integral]
  exact intervalDomain_chemotaxisDiv_integral_eq_zero hsol ht

/-- Mean of the perturbation from a constant equilibrium. -/
def intervalDomainMeanPerturbation
    (u : ℝ → intervalDomain.Point → ℝ) (uStar t : ℝ) : ℝ :=
  intervalDomain.integral (u t) - uStar

/-- Exact nonlinear forcing left after extracting the scalar logistic damping
`-aα` from the mean equation. -/
def intervalDomainMeanLogisticRemainder
    (p : CM2Params) (u : ℝ → intervalDomain.Point → ℝ)
    (uStar t : ℝ) : ℝ :=
  intervalDomain.integral
      (fun x => u t x * (p.a - p.b * (u t x) ^ p.α)) +
    p.a * p.α * intervalDomainMeanPerturbation u uStar t

/-- The mean mode of every global classical solution satisfies the exact
forced scalar ODE `m' = -aα m + remainder`. -/
theorem intervalDomain_global_meanPerturbation_hasDerivAt
    {p : CM2Params} {uStar t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain p u v)
    (ht : 0 < t) :
    HasDerivAt (intervalDomainMeanPerturbation u uStar)
      (-p.a * p.α * intervalDomainMeanPerturbation u uStar t +
        intervalDomainMeanLogisticRemainder p u uStar t) t := by
  have hT : 0 < t + 1 := by linarith
  have hsol := hglobal.classical hT
  have hmass := intervalDomain_mass_hasDerivAt hsol
    (t := t) (show t ∈ Set.Ioo (0 : ℝ) (t + 1) by constructor <;> linarith)
  have hreaction := intervalDomain_timeDeriv_integral_eq_reaction hsol ht (by linarith)
  have hmass' : HasDerivAt (fun s => intervalDomain.integral (u s))
      (intervalDomain.integral
        (fun x => u t x * (p.a - p.b * (u t x) ^ p.α))) t := by
    rwa [hreaction] at hmass
  have htarget :
      -p.a * p.α * intervalDomainMeanPerturbation u uStar t +
          intervalDomainMeanLogisticRemainder p u uStar t =
        intervalDomain.integral
          (fun x => u t x * (p.a - p.b * (u t x) ^ p.α)) := by
    simp only [intervalDomainMeanPerturbation,
      intervalDomainMeanLogisticRemainder]
    ring
  rw [htarget]
  exact hmass'.sub_const uStar

/-- In the zero-reaction branch, compatible initial mass removes the mean
mode identically at every positive time. -/
theorem intervalDomain_global_meanPerturbation_eq_zero_of_massCompatible
    {p : CM2Params} {uStar t : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain p u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (ha : p.a = 0) (hb : p.b = 0)
    (hmass : intervalDomain.integral u₀ = intervalDomain.volume * uStar)
    (ht : 0 < t) :
    intervalDomainMeanPerturbation u uStar t = 0 := by
  have hT : 0 < t + 1 := by linarith
  have hconserved :=
    (intervalDomain_Proposition_2_4 p u₀ hu₀ (t + 1) hT u v
      (hglobal.classical hT) htrace).1 ha hb t ht (by linarith)
  rw [intervalDomainMeanPerturbation, hconserved, hmass]
  change 1 * uStar - uStar = 0
  ring

#print axioms intervalDomain_solution_cosineCoeffs_hasDerivAt
#print axioms intervalDomain_solution_chemotaxis_zeroCoeff
#print axioms intervalDomain_global_meanPerturbation_hasDerivAt
#print axioms intervalDomain_global_meanPerturbation_eq_zero_of_massCompatible

end

end ShenWork.Paper3
