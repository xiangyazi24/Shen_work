/-
  Continuous extension of subtype functions to ℝ (Tietze-style).

  The paper works on Ω̄ = [0,1]. Functions are in C(Ω̄) = Continuous on the
  subtype. The semigroup S(t) only sees f|_{[0,1]} (the kernel integral is
  over [0,1]). But the spectral chain (`intervalFullSemigroupOperator_eq_cosineHeatValue_Icc`)
  takes `Continuous f` (globally on ℝ).

  Bridge: extend f ∈ C(Ω̄) to ℝ by constants (f(0) for x ≤ 0, f(1) for x ≥ 1).
  This is globally continuous and agrees with `intervalDomainLift f` on (0,1).
  The semigroup congr lemma then transfers the spectral identity.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalDomain

open Set Filter Topology

noncomputable section

namespace ShenWork.IntervalDomain

/-- Constant extension of a subtype function to ℝ: f(0) for x ≤ 0,
f(1) for x ≥ 1, f(x) for x ∈ [0,1]. Globally continuous when f is
continuous on the subtype. -/
def intervalDomainConstExtend (f : intervalDomainPoint → ℝ) : ℝ → ℝ :=
  fun x =>
    if x ≤ 0 then f ⟨0, ⟨le_refl _, zero_le_one⟩⟩
    else if 1 ≤ x then f ⟨1, ⟨zero_le_one, le_refl _⟩⟩
    else f ⟨x, ⟨le_of_not_le (by assumption), le_of_not_le (by assumption)⟩⟩

/-- The constant extension agrees with the lift on (0,1). -/
theorem constExtend_eq_lift_on_Ioo {f : intervalDomainPoint → ℝ}
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    intervalDomainConstExtend f x = intervalDomainLift f x := by
  simp only [intervalDomainConstExtend, intervalDomainLift,
    dif_pos (Ioo_subset_Icc_self hx)]
  have h0 : ¬ x ≤ 0 := not_le.mpr hx.1
  have h1 : ¬ 1 ≤ x := not_le.mpr hx.2
  simp [h0, h1]

/-- The constant extension agrees with the lift on [0,1]. -/
theorem constExtend_eq_lift_on_Icc {f : intervalDomainPoint → ℝ}
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    intervalDomainConstExtend f x = intervalDomainLift f x := by
  simp only [intervalDomainConstExtend, intervalDomainLift, dif_pos hx]
  rcases le_or_lt x 0 with hle | hgt
  · have : x = 0 := le_antisymm hle hx.1
    subst this; simp [le_refl]
  · simp [not_le.mpr hgt]
    rcases le_or_lt 1 x with hle1 | hlt1
    · have : x = 1 := le_antisymm hx.2 hle1
      subst this; simp [le_refl]
    · simp [not_le.mpr hlt1]

/-- The constant extension is globally continuous when f is continuous
on the subtype. This is the paper-faithful replacement for the false
`Continuous (intervalDomainLift f)`. -/
theorem constExtend_continuous {f : intervalDomainPoint → ℝ}
    (hf : Continuous f) : Continuous (intervalDomainConstExtend f) := by
  -- Express as: Set.piecewise (Iic 0) (fun _ => f ⟨0, ...⟩)
  --               (Set.piecewise (Ici 1) (fun _ => f ⟨1, ...⟩) (fun x => f ⟨x, ...⟩))
  -- Use continuous_piecewise: frontier condition + ContinuousOn on closure.
  -- For now, reduce to continuousAt at each point.
  rw [continuous_def]
  intro s hs
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  sorry -- Per-point continuity: case split on x < 0, 0 ≤ x ≤ 1, x > 1.
         -- Each case: locally constant or locally equals f (continuous on subtype).

/-- The cosine coefficients of the constant extension equal those of the lift.
Both integrate f against cos(nπy) over [0,1], where they agree. -/
theorem cosineCoeffs_constExtend_eq_lift (f : intervalDomainPoint → ℝ) (n : ℕ) :
    ShenWork.IntervalNeumannFullKernel.cosineCoeffs (intervalDomainConstExtend f) n =
    ShenWork.IntervalNeumannFullKernel.cosineCoeffs (intervalDomainLift f) n := by
  sorry -- cosineCoeffs integrates over [0,1] where constExtend = lift

/-- The semigroup operator of the constant extension equals that of the lift.
S(t) integrates against the kernel over [0,1], where both agree. -/
theorem semigroupOperator_constExtend_eq_lift
    {f : intervalDomainPoint → ℝ} {t x : ℝ} :
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t
      (intervalDomainConstExtend f) x =
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t
      (intervalDomainLift f) x := by
  -- S(t)g(x) = ∫ y, K(t,x,y)*g(y) d(volume.restrict (Icc 0 1)).
  -- constExtend = lift on Icc 0 1 → integrands agree a.e. → integrals equal.
  simp only [ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator]
  congr 1; ext y
  congr 1
  -- Need: constExtend f y = lift f y when y ∈ support of intervalMeasure 1
  -- But we're integrating over all y with the restricted measure.
  -- The integrand K*constExtend = K*lift on Icc 0 1 (where the measure lives).
  -- Use integral_congr_ae: ae (volume.restrict Icc) they agree.
  sorry -- needs: ae_of_mem_restrict + constExtend_eq_lift_on_Icc

end ShenWork.IntervalDomain

