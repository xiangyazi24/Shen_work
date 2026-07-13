import ShenWork.Paper1.Lemma25Helpers

open Filter Topology MeasureTheory

noncomputable section

namespace ShenWork.Paper1

/-!
# Coordinate audit for Paper 1 Theorem 1.2

Section 5 performs its energy estimate after passing to the coordinate
`z = x - c t`, where the wave is stationary.  The weighted energy in that
coordinate is not the laboratory-coordinate integral printed in (1.21): the
two differ by the exponentially growing factor `exp (2 η c t)`.
-/

/-- Weighted perturbation energy in the coordinate moving with the wave. -/
def coMovingWeightedL2Energy
    (η c : ℝ) (u : ℝ → ℝ → ℝ) (U : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ z : ℝ,
    Real.exp (2 * η * z) * |u t (z + c * t) - U z| ^ 2

/-- The laboratory-coordinate weighted perturbation energy appearing in the
current Lean headline and literally printed in (1.21). -/
def laboratoryWeightedL2Energy
    (η c : ℝ) (u : ℝ → ℝ → ℝ) (U : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℝ,
    Real.exp (2 * η * x) * |u t x - U (x - c * t)| ^ 2

/-- Exact change of variables between the two energies. -/
theorem laboratoryWeightedL2Energy_eq_exp_mul_coMoving
    (η c : ℝ) (u : ℝ → ℝ → ℝ) (U : ℝ → ℝ) (t : ℝ) :
    laboratoryWeightedL2Energy η c u U t =
      Real.exp (2 * η * (c * t)) * coMovingWeightedL2Energy η c u U t := by
  let f : ℝ → ℝ := fun x =>
    Real.exp (2 * η * x) * |u t x - U (x - c * t)| ^ 2
  have htranslate :=
    integral_add_right_eq_self (μ := (volume : Measure ℝ)) f (c * t)
  rw [show laboratoryWeightedL2Energy η c u U t = ∫ x : ℝ, f x by rfl]
  rw [← htranslate]
  unfold coMovingWeightedL2Energy
  rw [← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp [f, coMovingWeightedL2Energy]
    rw [show z + c * t - c * t = z by ring]
    have hexp :
        Real.exp (2 * η * (z + c * t)) =
          Real.exp (2 * η * (c * t)) * Real.exp (2 * η * z) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    ring

/-- The convergence actually proved by a moving-coordinate energy argument. -/
def CoMovingWeightedL2Convergence
    (η c : ℝ) (u : ℝ → ℝ → ℝ) (U : ℝ → ℝ) : Prop :=
  Tendsto (coMovingWeightedL2Energy η c u U) atTop (𝓝 0)

/-- A quantitative conversion is possible only if the moving-coordinate
energy decays faster than the coordinate factor grows. -/
theorem WeightedL2MovingFrameConvergence.of_coMoving_exponential_decay
    {η c lam A : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hgap : 2 * η * c < lam)
    (hdecay : ∀ᶠ t in atTop,
      coMovingWeightedL2Energy η c u U t ≤ A * Real.exp (-lam * t)) :
    WeightedL2MovingFrameConvergence η c u U := by
  have hgap_pos : 0 < lam - 2 * η * c := by linarith
  have hbound : ∀ᶠ t in atTop,
      laboratoryWeightedL2Energy η c u U t ≤
        A * Real.exp (-(lam - 2 * η * c) * t) := by
    filter_upwards [hdecay] with t ht
    rw [laboratoryWeightedL2Energy_eq_exp_mul_coMoving]
    have hexp_nn : 0 ≤ Real.exp (2 * η * (c * t)) := (Real.exp_pos _).le
    calc
      Real.exp (2 * η * (c * t)) * coMovingWeightedL2Energy η c u U t ≤
          Real.exp (2 * η * (c * t)) * (A * Real.exp (-lam * t)) :=
        mul_le_mul_of_nonneg_left ht hexp_nn
      _ = A * (Real.exp (2 * η * (c * t)) * Real.exp (-lam * t)) := by ring
      _ = A * Real.exp (-(lam - 2 * η * c) * t) := by
        rw [← Real.exp_add]
        congr 2
        ring
  have hbound' : ∀ᶠ t in atTop,
      (∫ x : ℝ,
        Real.exp (2 * η * x) * |u t x - U (x - c * t)| ^ 2) ≤
          A * Real.exp (-(lam - 2 * η * c) * t) := by
    simpa [laboratoryWeightedL2Energy] using hbound
  exact WeightedL2MovingFrameConvergence.of_eventual_exponential_decay
    hgap_pos hbound'

/-! ## A concrete factor-growth model

The next identities are not PDE counterexamples.  They are a sanity check
showing that moving-coordinate decay cannot simply be relabelled as (1.21):
for a perturbation of the form `exp (-lam t) f(x-ct)`, the two energies have
different exponential rates.
-/

def transportedDecayingPerturbation
    (c lam : ℝ) (U f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  U (x - c * t) + Real.exp (-lam * t) * f (x - c * t)

theorem coMovingWeightedL2Energy_transportedDecayingPerturbation
    (η c lam : ℝ) (U f : ℝ → ℝ) (t : ℝ) :
    coMovingWeightedL2Energy η c
        (transportedDecayingPerturbation c lam U f) U t =
      Real.exp (-2 * lam * t) *
        ∫ z : ℝ, Real.exp (2 * η * z) * |f z| ^ 2 := by
  unfold coMovingWeightedL2Energy transportedDecayingPerturbation
  rw [← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    have hexp_nn : 0 ≤ Real.exp (-lam * t) := (Real.exp_pos _).le
    change
      Real.exp (2 * η * z) *
          |U (z + c * t - c * t) +
              Real.exp (-lam * t) * f (z + c * t - c * t) - U z| ^ 2 =
        Real.exp (-2 * lam * t) * (Real.exp (2 * η * z) * |f z| ^ 2)
    rw [show z + c * t - c * t = z by ring]
    rw [show U z + Real.exp (-lam * t) * f z - U z =
      Real.exp (-lam * t) * f z by ring]
    rw [abs_mul, abs_of_nonneg hexp_nn, mul_pow]
    have hexpsq : Real.exp (-lam * t) ^ 2 = Real.exp (-2 * lam * t) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [hexpsq]
    ring

theorem laboratoryWeightedL2Energy_transportedDecayingPerturbation
    (η c lam : ℝ) (U f : ℝ → ℝ) (t : ℝ) :
    laboratoryWeightedL2Energy η c
        (transportedDecayingPerturbation c lam U f) U t =
      Real.exp (2 * (η * c - lam) * t) *
        ∫ z : ℝ, Real.exp (2 * η * z) * |f z| ^ 2 := by
  rw [laboratoryWeightedL2Energy_eq_exp_mul_coMoving,
    coMovingWeightedL2Energy_transportedDecayingPerturbation]
  calc
    Real.exp (2 * η * (c * t)) *
          (Real.exp (-2 * lam * t) *
            ∫ z : ℝ, Real.exp (2 * η * z) * |f z| ^ 2) =
        (Real.exp (2 * η * (c * t)) * Real.exp (-2 * lam * t)) *
          ∫ z : ℝ, Real.exp (2 * η * z) * |f z| ^ 2 := by ring
    _ = Real.exp (2 * (η * c - lam) * t) *
          ∫ z : ℝ, Real.exp (2 * η * z) * |f z| ^ 2 := by
      rw [← Real.exp_add]
      congr 2
      ring

theorem coMovingWeightedL2Convergence_transportedDecayingPerturbation
    {η c lam : ℝ} (hlam : 0 < lam) (U f : ℝ → ℝ) :
    CoMovingWeightedL2Convergence η c
      (transportedDecayingPerturbation c lam U f) U := by
  unfold CoMovingWeightedL2Convergence
  rw [show coMovingWeightedL2Energy η c
      (transportedDecayingPerturbation c lam U f) U =
      fun t => Real.exp (-2 * lam * t) *
        ∫ z : ℝ, Real.exp (2 * η * z) * |f z| ^ 2 by
    funext t
    exact coMovingWeightedL2Energy_transportedDecayingPerturbation η c lam U f t]
  have hlin : Tendsto (fun t : ℝ => -2 * lam * t) atTop atBot := by
    exact tendsto_id.const_mul_atTop_of_neg (by nlinarith)
  have hexp : Tendsto (fun t : ℝ => Real.exp (-2 * lam * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hlin
  simpa using hexp.mul_const
    (∫ z : ℝ, Real.exp (2 * η * z) * f z ^ 2)

theorem laboratoryWeightedL2Energy_transportedDecayingPerturbation_tendsto_atTop
    {η c lam : ℝ} (hgrowth : lam < η * c) (U f : ℝ → ℝ)
    (henergy : 0 < ∫ z : ℝ, Real.exp (2 * η * z) * |f z| ^ 2) :
    Tendsto
      (laboratoryWeightedL2Energy η c
        (transportedDecayingPerturbation c lam U f) U)
      atTop atTop := by
  rw [show laboratoryWeightedL2Energy η c
      (transportedDecayingPerturbation c lam U f) U =
      fun t => Real.exp (2 * (η * c - lam) * t) *
        ∫ z : ℝ, Real.exp (2 * η * z) * |f z| ^ 2 by
    funext t
    exact laboratoryWeightedL2Energy_transportedDecayingPerturbation η c lam U f t]
  have hcoef : 0 < 2 * (η * c - lam) := by linarith
  have hlin : Tendsto (fun t : ℝ => 2 * (η * c - lam) * t) atTop atTop :=
    tendsto_id.const_mul_atTop hcoef
  have hexp : Tendsto (fun t : ℝ => Real.exp (2 * (η * c - lam) * t))
      atTop atTop := Real.tendsto_exp_atTop.comp hlin
  exact hexp.atTop_mul_const henergy

theorem transportedDecayingPerturbation_not_weightedL2MovingFrameConvergence
    {η c lam : ℝ} (hgrowth : lam < η * c) (U f : ℝ → ℝ)
    (henergy : 0 < ∫ z : ℝ, Real.exp (2 * η * z) * |f z| ^ 2) :
    ¬WeightedL2MovingFrameConvergence η c
      (transportedDecayingPerturbation c lam U f) U := by
  intro hconv
  have hlab : Tendsto
      (laboratoryWeightedL2Energy η c
        (transportedDecayingPerturbation c lam U f) U)
      atTop (𝓝 0) := by
    change Tendsto
      (fun t : ℝ => ∫ x : ℝ,
        Real.exp (2 * η * x) *
          |transportedDecayingPerturbation c lam U f t x - U (x - c * t)| ^ 2)
      atTop (𝓝 0)
    exact hconv
  exact not_tendsto_nhds_of_tendsto_atTop
    (laboratoryWeightedL2Energy_transportedDecayingPerturbation_tendsto_atTop
      hgrowth U f henergy) 0 hlab

/-- A compactly supported pulse normalized so its `η`-weighted energy is
exactly one. -/
def compactWeightedPulse (η z : ℝ) : ℝ :=
  Set.indicator (Set.Icc (0 : ℝ) 1) (fun y => Real.exp (-η * y)) z

theorem compactWeightedPulse_energy (η : ℝ) :
    (∫ z : ℝ,
      Real.exp (2 * η * z) * |compactWeightedPulse η z| ^ 2) = 1 := by
  have hfun : (fun z : ℝ =>
      Real.exp (2 * η * z) * |compactWeightedPulse η z| ^ 2) =
      Set.indicator (Set.Icc (0 : ℝ) 1) (fun _z : ℝ => 1) := by
    funext z
    by_cases hz : z ∈ Set.Icc (0 : ℝ) 1
    · simp only [compactWeightedPulse, Set.indicator_of_mem hz]
      rw [abs_of_pos (Real.exp_pos _), pow_two, ← Real.exp_add]
      rw [← Real.exp_add]
      ring_nf
      simp
    · simp [compactWeightedPulse, hz]
  rw [hfun]
  simp

/-- Fully concrete coordinate-mismatch witness.  Its moving-coordinate
weighted energy tends to zero, while the laboratory-coordinate quantity in
the current headline tends to `+∞`. -/
theorem coordinate_weight_mismatch_nonvacuous (U : ℝ → ℝ) :
    CoMovingWeightedL2Convergence 1 3
        (transportedDecayingPerturbation 3 1 U (compactWeightedPulse 1)) U ∧
      ¬WeightedL2MovingFrameConvergence 1 3
        (transportedDecayingPerturbation 3 1 U (compactWeightedPulse 1)) U := by
  constructor
  · exact coMovingWeightedL2Convergence_transportedDecayingPerturbation
      (by norm_num) U (compactWeightedPulse 1)
  · apply transportedDecayingPerturbation_not_weightedL2MovingFrameConvergence
      (η := 1) (c := 3) (lam := 1)
    · norm_num
    · rw [compactWeightedPulse_energy]
      norm_num

section Theorem12CoordinateAuditAxioms
#print axioms laboratoryWeightedL2Energy_eq_exp_mul_coMoving
#print axioms WeightedL2MovingFrameConvergence.of_coMoving_exponential_decay
#print axioms coMovingWeightedL2Energy_transportedDecayingPerturbation
#print axioms laboratoryWeightedL2Energy_transportedDecayingPerturbation
#print axioms coordinate_weight_mismatch_nonvacuous
end Theorem12CoordinateAuditAxioms

end ShenWork.Paper1
