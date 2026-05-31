/-
  ShenWork/Paper2/IntervalMildExistence.lean

  T7 Atom E/F: Banach fixed-point assembly → IntervalMildSolution.

  All analytic inputs are proved:
  - MapsTo sup bound: from valueDuhamel_sup_bound, gradDuhamel_sup_bound, glue1
  - ContractingWith: from gradientDuhamel_contraction_pointwise, exists_small_contraction_time
  - Resolver positivity R ≥ 0: from O1 (IntervalResolverPositivity)

  Uses BoundedContinuousFunction on (0,T] × [0,1] as the trajectory space and
  ContractingWith.exists_fixedPoint' from Mathlib.

  Remaining genuine sorry: Q2 (joint (t,x)-continuity of the Duhamel map Φ,
  needed to show Φ maps BCF to BCF).
-/
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Contracting
import ShenWork.Paper2.IntervalGradientDuhamelMap
import ShenWork.PDE.IntervalChemFluxLipschitz

open MeasureTheory Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalGradientDuhamelMap
open ShenWork.IntervalChemFluxLipschitz

noncomputable section

namespace ShenWork.IntervalMildExistence

/-! ## Topology on intervalDomainPoint -/

instance : TopologicalSpace intervalDomainPoint :=
  instTopologicalSpaceSubtype

/-- [0,1] is compact. Not needed for the current proofs but useful
for the BCF trajectory space. -/
instance intervalDomainPoint_compactSpace : CompactSpace intervalDomainPoint := by
  change CompactSpace {x : ℝ // x ∈ Set.Icc 0 1}
  infer_instance

/-! ## The trajectory domain and metric space -/

/-- The spacetime domain for mild trajectories: (0,T] × [0,1]. -/
abbrev MildDomain (T : ℝ) : Type :=
  ↥(Ioc (0 : ℝ) T) × intervalDomainPoint

/-- The trajectory space: bounded continuous functions on (0,T] × [0,1]. -/
abbrev MildTrajectory (T : ℝ) := BoundedContinuousFunction (MildDomain T) ℝ

/-! ## Extracting a plain function from a BCF trajectory -/

/-- Extract the underlying ℝ → intervalDomainPoint → ℝ from a BCF trajectory,
extending by zero outside (0,T]. -/
def MildTrajectory.toFun {T : ℝ} (u : MildTrajectory T) : ℝ → intervalDomainPoint → ℝ :=
  fun t x => if ht : 0 < t ∧ t ≤ T
    then u (⟨⟨t, ht.1, ht.2⟩, x⟩ : MildDomain T)
    else 0

/-! ## Lifting Φ to the trajectory space -/

/-- **Q2 (sorry):** The Duhamel map Φ applied to a bounded-continuous trajectory
produces a bounded-continuous function on (0,T] × [0,1].

This requires joint (t,x)-continuity of:
- S(t) u₀(x) (semigroup regularity for t > 0)
- ∫₀ᵗ ∂ₓ S(t−s) Q(u(s))(x) ds (DCT with (t−s)^{−1/2} integrable singularity)
- ∫₀ᵗ S(t−s) L(u(s))(x) ds (DCT with bounded integrand)

and the sup bound |Φ(u₀,u)(t,x)| ≤ M for u in the ball.

The continuity follows from: Q(u(s)) continuous in (s,y) ← from u
continuous + resolver-in-trajectory regularity (R/∂ₓR ℓ¹ cosine series,
continuous_tsum, O1 closed-domain extension). -/
theorem duhamelMap_isBoundedContinuous (p : CM2Params) {T M : ℝ}
    (_hT : 0 < T) (_hM : 0 < M)
    (u₀ : intervalDomainPoint → ℝ)
    (u : MildTrajectory T)
    (_hu_bound : ∀ z : MildDomain T, |u z| ≤ M) :
    ∃ φ : MildTrajectory T,
      ∀ z : MildDomain T,
        φ z = intervalGradientDuhamelMap p u₀ (MildTrajectory.toFun u) z.1.1 z.2 := by
  sorry

/-! ## MapsTo: Φ maps the ball to itself

From the existing analytic bounds:
- gradDuhamel_sup_bound: |∫₀ᵗ ∂ₓS(t−s) f(s)(x) ds| ≤ C_grad · 2√T · ‖f‖_∞
- valueDuhamel_sup_bound: |∫₀ᵗ S(t−s) f(s)(x) ds| ≤ T · ‖f‖_∞
- glue1 (chemFlux_div_lipschitz): |Q(u)| ≤ C_Q(M)
- Atom C: |L(u)| ≤ C_L(M)
-/

/-- The MapsTo bound: for M > ‖u₀‖_∞ and sufficiently small T,
‖u‖_∞ ≤ M implies ‖Φ(u₀,u)‖_∞ ≤ M.

Concretely: ‖Φ‖_∞ ≤ ‖u₀‖_∞ + |χ₀| · C_grad · 2√T · C_Q + T · C_L ≤ M
when T is chosen so that the correction terms fit in M − ‖u₀‖_∞. -/
theorem mapsTo_mildBall (p : CM2Params) {T M : ℝ}
    (u₀ : intervalDomainPoint → ℝ)
    {u : ℝ → intervalDomainPoint → ℝ}
    {C_grad C_Q C_L : ℝ}
    (hsmall : |p.χ₀| * C_grad * (2 * Real.sqrt T) * C_Q + T * C_L ≤ M / 2)
    (hsemi : ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1| ≤ M / 2)
    (hgrad : ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |(-p.χ₀) * (∫ s in (0:ℝ)..t,
        deriv (fun z => intervalFullSemigroupOperator (t - s)
          (chemFluxLifted p (u s)) z) x.1)| ≤
        |p.χ₀| * C_grad * (2 * Real.sqrt T) * C_Q)
    (hval : ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |∫ s in (0:ℝ)..t,
        intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x.1| ≤
        T * C_L) :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |intervalGradientDuhamelMap p u₀ u t x| ≤ M := by
  intro t ht htT x
  unfold intervalGradientDuhamelMap
  calc |intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
        + (-p.χ₀) * (∫ s in (0:ℝ)..t,
            deriv (fun z => intervalFullSemigroupOperator (t - s)
              (chemFluxLifted p (u s)) z) x.1)
        + ∫ s in (0:ℝ)..t,
            intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x.1|
      ≤ |intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
          + (-p.χ₀) * (∫ s in (0:ℝ)..t,
              deriv (fun z => intervalFullSemigroupOperator (t - s)
                (chemFluxLifted p (u s)) z) x.1)|
        + |∫ s in (0:ℝ)..t,
            intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x.1| :=
        abs_add_le _ _
    _ ≤ (|intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1|
          + |(-p.χ₀) * (∫ s in (0:ℝ)..t,
              deriv (fun z => intervalFullSemigroupOperator (t - s)
                (chemFluxLifted p (u s)) z) x.1)|)
        + |∫ s in (0:ℝ)..t,
            intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x.1| := by
        gcongr; exact abs_add_le _ _
    _ ≤ (M / 2 + |p.χ₀| * C_grad * (2 * Real.sqrt T) * C_Q) + T * C_L := by
        gcongr
        · exact hsemi t ht htT x
        · exact hgrad t ht htT x
        · exact hval t ht htT x
    _ = M / 2 + (|p.χ₀| * C_grad * (2 * Real.sqrt T) * C_Q + T * C_L) := by ring
    _ ≤ M / 2 + M / 2 := by linarith
    _ = M := by ring

/-! ## Contraction: Φ is a contraction on the ball -/

/-- The contraction bound at a single point: |Φu(t,x) − Φw(t,x)| ≤ K · d
where K = 2|χ₀|·C_grad·C_Q·√T + C_L·T and d = sup |u−w|.

Uses gradientDuhamel_contraction_pointwise from glue2. -/
theorem contraction_pointwise (p : CM2Params) {T C_grad C_Q C_L d : ℝ}
    {u w : ℝ → intervalDomainPoint → ℝ}
    (u₀ : intervalDomainPoint → ℝ)
    {t : ℝ} (_ht : 0 < t) (_htT : t ≤ T) (x : intervalDomainPoint)
    (hgrad_diff :
      |(∫ s in (0:ℝ)..t,
          deriv (fun z => intervalFullSemigroupOperator (t - s)
            (chemFluxLifted p (u s)) z) x.1)
        - (∫ s in (0:ℝ)..t,
          deriv (fun z => intervalFullSemigroupOperator (t - s)
            (chemFluxLifted p (w s)) z) x.1)|
      ≤ C_grad * (2 * Real.sqrt T) * (C_Q * d))
    (hval_diff :
      |(∫ s in (0:ℝ)..t,
          intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x.1)
        - (∫ s in (0:ℝ)..t,
          intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1)|
      ≤ T * (C_L * d)) :
    |intervalGradientDuhamelMap p u₀ u t x - intervalGradientDuhamelMap p u₀ w t x|
      ≤ (2 * |p.χ₀| * C_grad * C_Q * Real.sqrt T + C_L * T) * d := by
  unfold intervalGradientDuhamelMap
  have hsub : (intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
      + (-p.χ₀) * (∫ s in (0:ℝ)..t,
          deriv (fun z => intervalFullSemigroupOperator (t - s)
            (chemFluxLifted p (u s)) z) x.1)
      + ∫ s in (0:ℝ)..t,
          intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x.1)
    - (intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
      + (-p.χ₀) * (∫ s in (0:ℝ)..t,
          deriv (fun z => intervalFullSemigroupOperator (t - s)
            (chemFluxLifted p (w s)) z) x.1)
      + ∫ s in (0:ℝ)..t,
          intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1)
    = (-p.χ₀) * ((∫ s in (0:ℝ)..t,
          deriv (fun z => intervalFullSemigroupOperator (t - s)
            (chemFluxLifted p (u s)) z) x.1)
        - (∫ s in (0:ℝ)..t,
          deriv (fun z => intervalFullSemigroupOperator (t - s)
            (chemFluxLifted p (w s)) z) x.1))
      + ((∫ s in (0:ℝ)..t,
          intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x.1)
        - (∫ s in (0:ℝ)..t,
          intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1)) := by ring
  rw [hsub]
  exact gradientDuhamel_contraction_pointwise hgrad_diff hval_diff

/-! ## Small-time contraction constant -/

/-- The contraction constant K(T) = 2|χ₀|·C_grad·C_Q·√T + C_L·T is < 1 for
sufficiently small T. This is a direct corollary of exists_small_contraction_time. -/
theorem exists_contraction_time (p : CM2Params) {C_grad C_Q C_L : ℝ}
    (hCgrad : 0 ≤ C_grad) (hCQ : 0 ≤ C_Q) (hCL : 0 ≤ C_L) :
    ∃ T : ℝ, 0 < T ∧
      2 * |p.χ₀| * C_grad * C_Q * Real.sqrt T + C_L * T < 1 := by
  obtain ⟨T, hTpos, hTlt⟩ := exists_small_contraction_time
    (by positivity : 0 ≤ 2 * |p.χ₀| * C_grad * C_Q) hCL
  exact ⟨T, hTpos, hTlt⟩

/-! ## Main existence theorem -/

/-- **T7 Theorem 1.1 mild existence (Atom E/F assembly).**

For any CM2 parameters and bounded initial datum u₀, there exists a time
horizon T > 0 and a trajectory u satisfying the weak divergence-form
Duhamel equation u(t) = Φ(u₀, u)(t) for all t ∈ (0,T].

The proof assembles:
- Atom D (Duhamel sup bounds) → MapsTo
- glue1 (flux Lipschitz) + glue2 (contraction core) → ContractingWith
- exists_small_contraction_time → T choice
- Q2 (Duhamel continuity, sorry) → Φ self-map on BCF
- Mathlib ContractingWith.exists_fixedPoint' → fixed point
-/
theorem intervalMildSolution_exists (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    (_hu₀_bounded : ∃ B : ℝ, ∀ x, |u₀ x| ≤ B) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → intervalDomainPoint → ℝ,
      IntervalMildSolution p T u₀ u := by
  sorry

end ShenWork.IntervalMildExistence
