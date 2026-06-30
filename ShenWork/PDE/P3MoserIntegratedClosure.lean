import ShenWork.PDE.P3MoserDissipationShape

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-!
This file isolates the routine part of the integrated-Moser route.  The hard
PDE step is represented by `IntegratedMoserFirstCrossingStep`; downstream
iteration and endpoint closure are proved here from that step.
-/

/-- Closed-time and time-integrability data needed by an integrated
first-crossing Moser step.  The existing L2 closed-energy bridge is not enough:
this data is indexed by every exponent `p >= p0` used in the ladder. -/
structure IntegratedMoserFirstCrossingRegularity
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T p0 : ℝ) : Prop where
  energyContinuous :
    ∀ p, p0 ≤ p →
      ContinuousOn
        (fun t => D.integral (fun x => (u t x) ^ p))
        (Set.Icc (0 : ℝ) T)
  initialPowerBound :
    ∀ p, p0 ≤ p →
      ∃ C0, 0 ≤ C0 ∧
        D.integral (fun x => (u 0 x) ^ p) ≤ C0
  powerTimeIntegrable :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t => D.integral (fun x => (u t x) ^ p))
        (Set.uIcc (0 : ℝ) T) volume
  gradientTimeIntegrable :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t =>
          D.integral (fun x =>
            (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
        (Set.uIcc (0 : ℝ) T) volume

/-- The one-step output needed from the integrated first-crossing argument. -/
def IntegratedMoserFirstCrossingStep
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p →
    LpPowerBoundedBefore D p T u →
      LpPowerBoundedBefore D (p + rho) T u

/-- Algebraic consequence of the integrated Moser inequality: once the
endpoint `Y_p` values and the time integral of `max 1 Y_p` are controlled on a
window, the time integral of the Moser gradient is controlled on that window. -/
theorem integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M H : ℝ}
    (hinteg : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hp : p0 ≤ p)
    (hp_nonneg : 0 ≤ p)
    (haT : a ∈ Set.Icc (0 : ℝ) T)
    (hbT : b ∈ Set.Icc a T)
    (hYa : D.integral (fun x => (u a x) ^ p) ≤ M)
    (hYb_nonneg : 0 ≤ D.integral (fun x => (u b x) ^ p))
    (hmaxInt :
      ∫ s in a..b, max 1 (D.integral (fun x => (u s x) ^ p)) ≤ H) :
    ∃ C, 0 ≤ C ∧
      2 * ∫ s in a..b,
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2) ≤
        M + C * p * H := by
  rcases hinteg p hp with ⟨C, hC_nonneg, hCineq⟩
  refine ⟨C, hC_nonneg, ?_⟩
  have hCp_nonneg : 0 ≤ C * p := mul_nonneg hC_nonneg hp_nonneg
  have hmax_scaled :
      C * p *
          ∫ s in a..b, max 1 (D.integral (fun x => (u s x) ^ p)) ≤
        C * p * H :=
    mul_le_mul_of_nonneg_left hmaxInt hCp_nonneg
  have hCineq_ab := hCineq a haT b hbT
  linarith

/-- Bound the integrated `max 1 Y` term by a uniform pointwise bound on `Y`. -/
theorem intervalIntegral_max_one_le_length_mul_max_one_of_Icc_bound
    {a b M : ℝ} {Y : ℝ → ℝ}
    (hab : a ≤ b)
    (hYmax_int :
      IntervalIntegrable (fun s => max (1 : ℝ) (Y s)) volume a b)
    (hY_le : ∀ s ∈ Set.Icc a b, Y s ≤ M) :
    ∫ s in a..b, max (1 : ℝ) (Y s) ≤
      (b - a) * max (1 : ℝ) M := by
  have hpoint :
      ∀ s ∈ Set.Icc a b,
        max (1 : ℝ) (Y s) ≤ max (1 : ℝ) M := by
    intro s hs
    exact max_le
      (le_max_left (1 : ℝ) M)
      (le_trans (hY_le s hs) (le_max_right (1 : ℝ) M))
  have hmono :=
    intervalIntegral.integral_mono_on hab
      hYmax_int intervalIntegrable_const hpoint
  have hconst :
      (∫ _s in a..b, max (1 : ℝ) M) =
        (b - a) * max (1 : ℝ) M := by
    rw [intervalIntegral.integral_const]
    simp [smul_eq_mul]
  rw [hconst] at hmono
  exact hmono

/-- Moser-energy specialization of
`intervalIntegral_max_one_le_length_mul_max_one_of_Icc_bound`. -/
theorem integratedMoser_maxOneEnergy_timeIntegral_le_of_Icc_bound
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {a b M p : ℝ}
    (hab : a ≤ b)
    (hYmax_int :
      IntervalIntegrable
        (fun s => max (1 : ℝ)
          (D.integral (fun x => (u s x) ^ p)))
        volume a b)
    (hY_le :
      ∀ s ∈ Set.Icc a b,
        D.integral (fun x => (u s x) ^ p) ≤ M) :
    ∫ s in a..b,
      max (1 : ℝ) (D.integral (fun x => (u s x) ^ p)) ≤
        (b - a) * max (1 : ℝ) M :=
  intervalIntegral_max_one_le_length_mul_max_one_of_Icc_bound
    (Y := fun s => D.integral (fun x => (u s x) ^ p))
    hab hYmax_int hY_le

/-- Integrate a pointwise affine upper bound over a non-reversed interval. -/
theorem intervalIntegral_le_const_mul_integral_add_length_mul_const_of_le_on
    {a b A B : ℝ} {F G : ℝ → ℝ}
    (hab : a ≤ b)
    (hF_int : IntervalIntegrable F volume a b)
    (hG_int : IntervalIntegrable G volume a b)
    (hpoint : ∀ s ∈ Set.Icc a b, F s ≤ A * G s + B) :
    ∫ s in a..b, F s ≤
      A * (∫ s in a..b, G s) + (b - a) * B := by
  have hR_int :
      IntervalIntegrable (fun s => A * G s + B) volume a b :=
    (hG_int.const_mul A).add intervalIntegrable_const
  have hmono :=
    intervalIntegral.integral_mono_on hab hF_int hR_int hpoint
  have hR :
      (∫ s in a..b, A * G s + B) =
        A * (∫ s in a..b, G s) + (b - a) * B := by
    have hmul :
        (∫ s in a..b, A * G s) = A * (∫ s in a..b, G s) :=
      intervalIntegral.integral_const_mul A G
    have hconst : (∫ _s in a..b, B) = (b - a) * B := by
      rw [intervalIntegral.integral_const]
      simp [smul_eq_mul]
    calc
      (∫ s in a..b, A * G s + B)
          = (∫ s in a..b, A * G s) + ∫ _s in a..b, B := by
            exact intervalIntegral.integral_add
              (hG_int.const_mul A) intervalIntegrable_const
      _ = A * (∫ s in a..b, G s) + (b - a) * B := by
            rw [hmul, hconst]
  rw [hR] at hmono
  exact hmono

/-- Integrate the relative Moser interpolation inequality over a fixed time
window, under a uniform current-exponent bound on that window. -/
theorem relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_bound
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M eps : ℝ}
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hp : p0 ≤ p)
    (heps : 0 < eps)
    (hab : a ≤ b)
    (ha : 0 < a)
    (hb : b < T)
    (hZ_int :
      IntervalIntegrable
        (fun s => D.integral (fun x => (u s x) ^ (p + rho)))
        volume a b)
    (hG_int :
      IntervalIntegrable
        (fun s =>
          D.integral (fun x =>
            (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2))
        volume a b)
    (hY_le :
      ∀ s ∈ Set.Icc a b,
        D.integral (fun x => (u s x) ^ p) ≤ M) :
    ∃ Ceps, 0 ≤ Ceps ∧
      ∫ s in a..b,
          D.integral (fun x => (u s x) ^ (p + rho)) ≤
        eps * (∫ s in a..b,
          D.integral (fun x =>
            (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)) +
        (b - a) * (Ceps * M) := by
  rcases hrel p hp eps heps with ⟨Ceps, hCeps_nonneg, hrel_eps⟩
  refine ⟨Ceps, hCeps_nonneg, ?_⟩
  exact
    intervalIntegral_le_const_mul_integral_add_length_mul_const_of_le_on
      (F := fun s => D.integral (fun x => (u s x) ^ (p + rho)))
      (G := fun s =>
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2))
      (A := eps) (B := Ceps * M)
      hab hZ_int hG_int
      (by
        intro s hs
        have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
        have hsT : s < T := lt_of_le_of_lt hs.2 hb
        have hrel_s := hrel_eps s hs0 hsT
        have hY_s := hY_le s hs
        have hCY_s :
            Ceps * D.integral (fun x => (u s x) ^ p) ≤ Ceps * M :=
          mul_le_mul_of_nonneg_left hY_s hCeps_nonneg
        linarith)

/-- Integrated relative-Moser bound after substituting a supplied bound on the
integrated gradient term. -/
theorem
    relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M eps Gbound : ℝ}
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hp : p0 ≤ p)
    (heps : 0 < eps)
    (hab : a ≤ b)
    (ha : 0 < a)
    (hb : b < T)
    (hZ_int :
      IntervalIntegrable
        (fun s => D.integral (fun x => (u s x) ^ (p + rho)))
        volume a b)
    (hG_int :
      IntervalIntegrable
        (fun s =>
          D.integral (fun x =>
            (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2))
        volume a b)
    (hY_le :
      ∀ s ∈ Set.Icc a b,
        D.integral (fun x => (u s x) ^ p) ≤ M)
    (hG_le :
      ∫ s in a..b,
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2) ≤
        Gbound) :
    ∃ Ceps, 0 ≤ Ceps ∧
      ∫ s in a..b,
          D.integral (fun x => (u s x) ^ (p + rho)) ≤
        eps * Gbound + (b - a) * (Ceps * M) := by
  rcases
    relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_bound
      (D := D) (u := u) (T := T) (rho := rho) (p0 := p0)
      (p := p) (a := a) (b := b) (M := M) (eps := eps)
      hrel hp heps hab ha hb hZ_int hG_int hY_le with
    ⟨Ceps, hCeps_nonneg, htime⟩
  refine ⟨Ceps, hCeps_nonneg, ?_⟩
  have hscaled :
      eps * (∫ s in a..b,
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)) ≤
      eps * Gbound :=
    mul_le_mul_of_nonneg_left hG_le heps.le
  let rest := (b - a) * (Ceps * M)
  have hscaled_rest :
      eps * (∫ s in a..b,
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)) + rest ≤
        eps * Gbound + rest := by
    linarith
  exact le_trans htime (by simpa [rest] using hscaled_rest)

/-! ### Honest precrossing/window plumbing before the first-crossing frontier -/

/-- Short name for the current Moser energy `Y_p(t)`. -/
def integratedMoserEnergy
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (p t : ℝ) : ℝ :=
  D.integral (fun x => (u t x) ^ p)

/-- Short name for the Moser gradient energy `G_p(t)`. -/
def integratedMoserGradientEnergy
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (p t : ℝ) : ℝ :=
  D.integral (fun x =>
    (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2)

/-- Restrict an `IntegrableOn` hypothesis on `uIcc 0 T` to an
`IntervalIntegrable` statement on a non-reversed interval `a..b`. -/
theorem intervalIntegrable_of_integrableOn_uIcc_of_Icc_subset
    {f : ℝ → ℝ} {T a b : ℝ}
    (hab : a ≤ b)
    (hint : IntegrableOn f (Set.uIcc (0 : ℝ) T) volume)
    (hsub : Set.Icc a b ⊆ Set.uIcc (0 : ℝ) T) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact hint.mono_set (Set.Ioc_subset_Icc_self.trans hsub)

/-- Endpoint hypotheses used by the integrated Moser extraction give the
corresponding set inclusion for every point of the closed window. -/
theorem Icc_subset_uIcc_zero_T_of_endpoint_memberships
    {T a b : ℝ}
    (haT : a ∈ Set.Icc (0 : ℝ) T)
    (hbT : b ∈ Set.Icc a T) :
    Set.Icc a b ⊆ Set.uIcc (0 : ℝ) T := by
  intro s hs
  have h0T : (0 : ℝ) ≤ T := le_trans haT.1 haT.2
  rw [Set.uIcc_of_le h0T]
  exact ⟨le_trans haT.1 hs.1, le_trans hs.2 hbT.2⟩

/-- Power-profile interval integrability from the first-crossing regularity
package. -/
theorem IntegratedMoserFirstCrossingRegularity.power_intervalIntegrable_of_Icc
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T p0 p a b : ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hp : p0 ≤ p)
    (hab : a ≤ b)
    (hsub : Set.Icc a b ⊆ Set.uIcc (0 : ℝ) T) :
    IntervalIntegrable (fun s => integratedMoserEnergy D u p s) volume a b := by
  exact intervalIntegrable_of_integrableOn_uIcc_of_Icc_subset
    hab (hreg.powerTimeIntegrable p hp) hsub

/-- Gradient-profile interval integrability from the first-crossing regularity
package. -/
theorem IntegratedMoserFirstCrossingRegularity.gradient_intervalIntegrable_of_Icc
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T p0 p a b : ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hp : p0 ≤ p)
    (hab : a ≤ b)
    (hsub : Set.Icc a b ⊆ Set.uIcc (0 : ℝ) T) :
    IntervalIntegrable
      (fun s => integratedMoserGradientEnergy D u p s) volume a b := by
  exact intervalIntegrable_of_integrableOn_uIcc_of_Icc_subset
    hab (hreg.gradientTimeIntegrable p hp) hsub

/-- If `Y` is interval-integrable on a non-reversed interval, so is
`max 1 Y`.

The proof uses `max 1 y = (1 + y + |1 - y|) / 2`, avoiding any dependency on a
Mathlib lemma name for integrability under `max`. -/
theorem intervalIntegrable_max_one_of_intervalIntegrable
    {Y : ℝ → ℝ} {a b : ℝ}
    (hY : IntervalIntegrable Y volume a b) :
    IntervalIntegrable (fun s => max (1 : ℝ) (Y s)) volume a b := by
  have hconst :
      IntervalIntegrable (fun _s : ℝ => (1 : ℝ)) volume a b :=
    intervalIntegrable_const
  have hdiff :
      IntervalIntegrable (fun s => (1 : ℝ) - Y s) volume a b :=
    hconst.sub hY
  have habs :
      IntervalIntegrable (fun s => |(1 : ℝ) - Y s|) volume a b :=
    hdiff.abs
  have hnum :
      IntervalIntegrable
        (fun s => (1 : ℝ) + Y s + |(1 : ℝ) - Y s|) volume a b :=
    (hconst.add hY).add habs
  have hformula :
      IntervalIntegrable
        (fun s => ((1 : ℝ) + Y s + |(1 : ℝ) - Y s|) / 2) volume a b := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hnum.const_mul ((1 : ℝ) / 2)
  refine hformula.congr ?_
  intro s _hs
  by_cases hle : (1 : ℝ) ≤ Y s
  · dsimp
    rw [max_eq_right hle, abs_of_nonpos (sub_nonpos.mpr hle)]
    ring
  · have hY_le : Y s ≤ 1 := le_of_not_ge hle
    dsimp
    rw [max_eq_left hY_le, abs_of_nonneg (sub_nonneg.mpr hY_le)]
    ring

/-- Max-one current-energy interval integrability from the regularity package. -/
theorem IntegratedMoserFirstCrossingRegularity.maxOneEnergy_intervalIntegrable_of_Icc
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T p0 p a b : ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hp : p0 ≤ p)
    (hab : a ≤ b)
    (hsub : Set.Icc a b ⊆ Set.uIcc (0 : ℝ) T) :
    IntervalIntegrable
      (fun s => max (1 : ℝ) (integratedMoserEnergy D u p s))
      volume a b := by
  exact intervalIntegrable_max_one_of_intervalIntegrable
    (hreg.power_intervalIntegrable_of_Icc hp hab hsub)

/-- Abstract nonnegativity of Moser energies at interior times.

This stays explicit at the abstract `BoundedDomainData` level.  Concrete
`intervalDomain` producers can later prove it from positivity of classical
solutions and interval-integral monotonicity.  The first-crossing window only
uses this for right endpoints `b` with `0 < b < T`; requiring a value at
`t = 0` would add an unnecessary initial-trace side condition. -/
def IntegratedMoserEnergyNonnegativity
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → 0 ≤ p → ∀ t, 0 < t → t < T →
    0 ≤ integratedMoserEnergy D u p t

/-- The concrete unit-interval integral preserves nonnegative functions. -/
theorem intervalDomain_integral_nonneg
    (f : intervalDomain.Point → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    0 ≤ intervalDomain.integral f := by
  change 0 ≤ intervalDomainIntegral f
  unfold intervalDomainIntegral
  refine ShenWork.IntervalDomain.intervalIntegral_nonneg
    (L := 1) (by norm_num) ?_
  intro x hx
  unfold intervalDomainLift
  simpa [hx] using hf ⟨x, hx⟩

/-- Pointwise nonnegativity of an interval-domain slice gives nonnegative
Moser energy for every real exponent. -/
theorem intervalDomain_integratedMoserEnergy_nonneg_of_pointwise_nonneg
    {u : ℝ → intervalDomain.Point → ℝ} {p t : ℝ}
    (hu_nonneg : ∀ x : intervalDomain.Point, 0 ≤ u t x) :
    0 ≤ integratedMoserEnergy intervalDomain u p t := by
  unfold integratedMoserEnergy
  exact intervalDomain_integral_nonneg _
    (fun x => Real.rpow_nonneg (hu_nonneg x) p)

/-- Produce the integrated-Moser energy nonnegativity package from pointwise
nonnegativity of the interval-domain solution at all interior times. -/
theorem intervalDomain_integratedMoserEnergyNonnegativity_of_pointwise_nonneg
    {u : ℝ → intervalDomain.Point → ℝ} {T p0 : ℝ}
    (hu_nonneg :
      ∀ t, 0 < t → t < T → ∀ x : intervalDomain.Point, 0 ≤ u t x) :
    IntegratedMoserEnergyNonnegativity intervalDomain u T p0 := by
  intro p _hp _hp_nonneg t ht0 htT
  exact intervalDomain_integratedMoserEnergy_nonneg_of_pointwise_nonneg
    (u := u) (p := p) (t := t) (hu_nonneg t ht0 htT)

/-- A positive classical interval-domain Paper2 solution supplies the
integrated-Moser energy nonnegativity package. -/
theorem intervalDomain_integratedMoserEnergyNonnegativity_of_classical
    {params : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    {T p0 : ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    IntegratedMoserEnergyNonnegativity intervalDomain u T p0 := by
  exact intervalDomain_integratedMoserEnergyNonnegativity_of_pointwise_nonneg
    (fun t ht0 htT x => (hsol.u_pos' (x := x) ht0 htT).le)

/-- A global positive classical interval-domain Paper2 solution supplies the
finite-horizon integrated-Moser energy nonnegativity package. -/
theorem intervalDomain_integratedMoserEnergyNonnegativity_of_global_classical
    {params : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    {T p0 : ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v) :
    IntegratedMoserEnergyNonnegativity intervalDomain u T p0 := by
  intro p hp hp_nonneg t ht0 htT
  have hT : 0 < T := lt_trans ht0 htT
  exact intervalDomain_integratedMoserEnergyNonnegativity_of_classical
    (T := T) (p0 := p0) (hglobal.classical hT)
    p hp hp_nonneg t ht0 htT

/-- Extract an Icc current-energy bound from `LpPowerBoundedBefore`. -/
theorem currentEnergy_Icc_bound_of_LpPowerBoundedBefore
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T p a b : ℝ}
    (hLp : LpPowerBoundedBefore D p T u)
    (ha : 0 < a) (hb : b < T) :
    ∃ M, ∀ s ∈ Set.Icc a b, integratedMoserEnergy D u p s ≤ M := by
  rcases hLp with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro s hs
  exact hM s (lt_of_lt_of_le ha hs.1) (lt_of_le_of_lt hs.2 hb)

/-- Data available on an honest precrossing/window interval.  This record only
packages fixed-window hypotheses; it does not assert any pointwise bound for the
next exponent. -/
structure IntegratedMoserPrecrossingIntervalData
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 p a b M : ℝ) : Prop where
  hp : p0 ≤ p
  hp_nonneg : 0 ≤ p
  hab : a < b
  ha_pos : 0 < a
  hb_lt : b < T
  haT : a ∈ Set.Icc (0 : ℝ) T
  hbT : b ∈ Set.Icc a T
  currentEnergy_le_Icc :
    ∀ s ∈ Set.Icc a b,
      integratedMoserEnergy D u p s ≤ M
  right_currentEnergy_nonneg :
    0 ≤ integratedMoserEnergy D u p b
  maxOneEnergy_intervalIntegrable :
    IntervalIntegrable
      (fun s => max (1 : ℝ) (integratedMoserEnergy D u p s))
      volume a b
  higherPower_intervalIntegrable :
    IntervalIntegrable
      (fun s => integratedMoserEnergy D u (p + rho) s)
      volume a b
  gradient_intervalIntegrable :
    IntervalIntegrable
      (fun s => integratedMoserGradientEnergy D u p s)
      volume a b

namespace IntegratedMoserPrecrossingIntervalData

/-- Left-end current-energy bound extracted from the Icc current-energy field. -/
theorem left_currentEnergy_le
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M : ℝ}
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p0 p a b M) :
    integratedMoserEnergy D u p a ≤ M :=
  hI.currentEnergy_le_Icc a ⟨le_rfl, hI.hab.le⟩

/-- Max-one time-integral control in the exact form needed by the integrated
Moser extraction lemma. -/
theorem maxOneEnergy_timeIntegral_le
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M : ℝ}
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p0 p a b M) :
    (∫ s in a..b,
      max (1 : ℝ) (integratedMoserEnergy D u p s)) ≤
        (b - a) * max (1 : ℝ) M := by
  simpa [integratedMoserEnergy] using
    integratedMoser_maxOneEnergy_timeIntegral_le_of_Icc_bound
      (D := D) (u := u) (a := a) (b := b) (M := M) (p := p)
      hI.hab.le hI.maxOneEnergy_intervalIntegrable hI.currentEnergy_le_Icc

end IntegratedMoserPrecrossingIntervalData

/-- Build the precrossing/window data from first-crossing regularity,
energy-nonnegativity, and a current-exponent Icc bound. -/
theorem integratedMoserPrecrossingIntervalData_of_regular_window
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M : ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hnonneg : IntegratedMoserEnergyNonnegativity D u T p0)
    (hp : p0 ≤ p)
    (hp_nonneg : 0 ≤ p)
    (hrho_nonneg : 0 ≤ rho)
    (hab : a < b)
    (ha_pos : 0 < a)
    (hb_lt : b < T)
    (haT : a ∈ Set.Icc (0 : ℝ) T)
    (hbT : b ∈ Set.Icc a T)
    (hY_le :
      ∀ s ∈ Set.Icc a b,
        integratedMoserEnergy D u p s ≤ M) :
    IntegratedMoserPrecrossingIntervalData D u T rho p0 p a b M := by
  have hsub : Set.Icc a b ⊆ Set.uIcc (0 : ℝ) T :=
    Icc_subset_uIcc_zero_T_of_endpoint_memberships haT hbT
  have hp_rho : p0 ≤ p + rho := by linarith
  have hb_pos : 0 < b := lt_of_lt_of_le ha_pos hbT.1
  refine
    { hp := hp
      hp_nonneg := hp_nonneg
      hab := hab
      ha_pos := ha_pos
      hb_lt := hb_lt
      haT := haT
      hbT := hbT
      currentEnergy_le_Icc := hY_le
      right_currentEnergy_nonneg := hnonneg p hp hp_nonneg b hb_pos hb_lt
      maxOneEnergy_intervalIntegrable := ?_
      higherPower_intervalIntegrable := ?_
      gradient_intervalIntegrable := ?_ }
  · exact hreg.maxOneEnergy_intervalIntegrable_of_Icc hp hab.le hsub
  · exact hreg.power_intervalIntegrable_of_Icc hp_rho hab.le hsub
  · exact hreg.gradient_intervalIntegrable_of_Icc hp hab.le hsub

/-- Witness-level form of the fixed-window integrated Moser upper-bound
calculation.  Keeping `Gbound` and `Ceps` explicit prevents later frontiers from
accidentally quantifying over arbitrary, larger upper-bound witnesses. -/
def IntegratedMoserWindowUpperBoundWitness
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (rho p a b M eps Gbound Ceps : ℝ) : Prop :=
  0 ≤ Ceps ∧
    (∫ s in a..b, integratedMoserGradientEnergy D u p s) ≤ Gbound ∧
    (∫ s in a..b, integratedMoserEnergy D u (p + rho) s) ≤
      eps * Gbound + (b - a) * (Ceps * M)

/-- Constants and estimates produced by the fixed-window integrated Moser
upper-bound calculation. -/
structure IntegratedMoserWindowUpperBoundData
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (rho p a b M eps : ℝ) : Prop where
  bounds :
    ∃ Gbound Ceps : ℝ,
      IntegratedMoserWindowUpperBoundWitness
        D u rho p a b M eps Gbound Ceps

/-- Package the existing fixed-window integrated-Moser and relative-Moser
helpers into a reusable upper-bound record.  This is still only a time-integral
theorem, not a pointwise extraction theorem. -/
theorem integratedMoser_windowUpperBoundData_of_precrossing
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M eps : ℝ}
    (hinteg : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p0 p a b M)
    (heps : 0 < eps) :
    IntegratedMoserWindowUpperBoundData D u rho p a b M eps := by
  have hleft :
      D.integral (fun x => (u a x) ^ p) ≤ M := by
    simpa [integratedMoserEnergy] using
      IntegratedMoserPrecrossingIntervalData.left_currentEnergy_le hI
  have hright_nonneg :
      0 ≤ D.integral (fun x => (u b x) ^ p) := by
    simpa [integratedMoserEnergy] using hI.right_currentEnergy_nonneg
  have hmaxInt :
      ∫ s in a..b, max 1 (D.integral (fun x => (u s x) ^ p)) ≤
        (b - a) * max (1 : ℝ) M := by
    simpa [integratedMoserEnergy] using
      IntegratedMoserPrecrossingIntervalData.maxOneEnergy_timeIntegral_le hI
  rcases
    integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds
      (D := D) (u := u) (T := T) (rho := rho) (p0 := p0)
      (p := p) (a := a) (b := b) (M := M)
      (H := (b - a) * max (1 : ℝ) M)
      hinteg hI.hp hI.hp_nonneg hI.haT hI.hbT
      hleft hright_nonneg hmaxInt with
    ⟨C, _hC_nonneg, hgrad_two⟩
  let Gbound : ℝ := (M + C * p * ((b - a) * max (1 : ℝ) M)) / 2
  have hGbound_raw :
      (∫ s in a..b,
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)) ≤ Gbound := by
    dsimp [Gbound] at hgrad_two ⊢
    linarith
  have hGbound :
      (∫ s in a..b, integratedMoserGradientEnergy D u p s) ≤ Gbound := by
    simpa [integratedMoserGradientEnergy] using hGbound_raw
  have hZ_int :
      IntervalIntegrable
        (fun s => D.integral (fun x => (u s x) ^ (p + rho)))
        volume a b := by
    simpa [integratedMoserEnergy] using hI.higherPower_intervalIntegrable
  have hG_int :
      IntervalIntegrable
        (fun s =>
          D.integral (fun x =>
            (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2))
        volume a b := by
    simpa [integratedMoserGradientEnergy] using hI.gradient_intervalIntegrable
  have hY_le_raw :
      ∀ s ∈ Set.Icc a b, D.integral (fun x => (u s x) ^ p) ≤ M := by
    intro s hs
    simpa [integratedMoserEnergy] using hI.currentEnergy_le_Icc s hs
  rcases
    relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound
      (D := D) (u := u) (T := T) (rho := rho) (p0 := p0)
      (p := p) (a := a) (b := b) (M := M)
      (eps := eps) (Gbound := Gbound)
      hrel hI.hp heps hI.hab.le hI.ha_pos hI.hb_lt
      hZ_int hG_int hY_le_raw hGbound_raw with
    ⟨Ceps, hCeps_nonneg, hZ⟩
  refine ⟨Gbound, Ceps, hCeps_nonneg, hGbound, ?_⟩
  simpa [integratedMoserEnergy] using hZ

/-- Data supplied by a genuine high-excursion argument for one candidate
violation of the next Moser exponent bound.

The lower-average and strict-gap fields are analytic input.  This structure
does not derive a pointwise bound from a time-integral estimate. -/
structure IntegratedMoserHighExcursionContradictionWindow
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 p : ℝ) where
  a : ℝ
  b : ℝ
  M : ℝ
  eps : ℝ
  lowerBound : ℝ
  Gbound : ℝ
  Ceps : ℝ
  eps_pos : 0 < eps
  upperWitness :
    IntegratedMoserWindowUpperBoundWitness
      D u rho p a b M eps Gbound Ceps
  lowerAverage :
    lowerBound ≤ ∫ s in a..b, integratedMoserEnergy D u (p + rho) s
  upper_lt_lower :
    eps * Gbound + (b - a) * (Ceps * M) < lowerBound

/-- Pure contradiction once the same upper-bound witnesses also satisfy a
strict lower-average gap. -/
theorem false_of_windowUpperBoundWitness_lowerAverage_gap
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {rho p a b M eps Gbound Ceps lower : ℝ}
    (hupper :
      IntegratedMoserWindowUpperBoundWitness
        D u rho p a b M eps Gbound Ceps)
    (hlower :
      lower ≤ ∫ s in a..b, integratedMoserEnergy D u (p + rho) s)
    (hgap : eps * Gbound + (b - a) * (Ceps * M) < lower) :
    False := by
  rcases hupper with ⟨_hCeps_nonneg, _hG, hYupper⟩
  linarith

/-- Pure eliminator for a packaged high-excursion contradiction window. -/
theorem false_of_integratedMoserHighExcursionContradictionWindow
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p : ℝ}
    (hwin :
      IntegratedMoserHighExcursionContradictionWindow
        D u T rho p0 p) :
    False :=
  false_of_windowUpperBoundWitness_lowerAverage_gap
    hwin.upperWitness hwin.lowerAverage hwin.upper_lt_lower

/-- A high-excursion window carrying the lower-average information, before any
choice of fixed-window upper-bound witnesses.  Producing this is the
thickness/modulus part of the analytic frontier. -/
structure IntegratedMoserHighExcursionLowerAverageWindow
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 p Cnext t : ℝ) where
  a : ℝ
  b : ℝ
  M : ℝ
  lowerBound : ℝ
  hab : a < b
  ha_pos : 0 < a
  hb_lt : b < T
  haT : a ∈ Set.Icc (0 : ℝ) T
  hbT : b ∈ Set.Icc a T
  currentEnergy_le_Icc :
    ∀ s ∈ Set.Icc a b,
      integratedMoserEnergy D u p s ≤ M
  lowerAverage :
    lowerBound ≤ ∫ s in a..b, integratedMoserEnergy D u (p + rho) s

/-- Analytic frontier: a pointwise high excursion produces a window with a
quantitative lower average. -/
structure IntegratedMoserHighExcursionLowerAverageWindowFrontier
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 p Cnext : ℝ) where
  produce :
    p0 ≤ p →
      0 ≤ p →
      LpPowerBoundedBefore D p T u →
      ∀ t, 0 < t → t < T →
        Cnext < integratedMoserEnergy D u (p + rho) t →
          IntegratedMoserHighExcursionLowerAverageWindow
            D u T rho p0 p Cnext t

/-- A tied fixed-window upper-bound witness and strict gap below the selected
lower average.  This is where `eps`, `Gbound`, and `Ceps` stay linked. -/
structure IntegratedMoserWindowUpperGapWitness
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (rho p a b M lowerBound : ℝ) where
  eps : ℝ
  Gbound : ℝ
  Ceps : ℝ
  eps_pos : 0 < eps
  upperWitness :
    IntegratedMoserWindowUpperBoundWitness
      D u rho p a b M eps Gbound Ceps
  upper_lt_lower :
    eps * Gbound + (b - a) * (Ceps * M) < lowerBound

/-- Quantitative upper-gap frontier for a selected lower-average window.  This
is the analytic home for the `eps`/`Ceps` dependence. -/
structure IntegratedMoserWindowUpperGapWitnessFrontier
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 p : ℝ) where
  produce :
    ∀ {Cnext t : ℝ},
      (hwin : IntegratedMoserHighExcursionLowerAverageWindow
        D u T rho p0 p Cnext t) →
        IntegratedMoserWindowUpperGapWitness
          D u rho p hwin.a hwin.b hwin.M hwin.lowerBound

/-- Quantitative choice of a window epsilon that closes the strict
lower-average gap after the fixed-window upper-bound calculation supplies its
`Gbound` and `Ceps` witnesses. -/
structure IntegratedMoserWindowUpperGapEpsilonFrontier
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 p : ℝ) : Prop where
  choose :
    ∀ {Cnext t : ℝ},
      (hwin : IntegratedMoserHighExcursionLowerAverageWindow
        D u T rho p0 p Cnext t) →
        ∃ eps : ℝ, 0 < eps ∧
          ∀ {Gbound Ceps : ℝ},
            IntegratedMoserWindowUpperBoundWitness
              D u rho p hwin.a hwin.b hwin.M eps Gbound Ceps →
              eps * Gbound + (hwin.b - hwin.a) * (Ceps * hwin.M) <
                hwin.lowerBound

/-- Build the fixed-window upper-bound data for a selected lower-average
window.  This factors out the routine regularity/dissipation construction so
gap frontiers can reason only about choosing a useful witness. -/
def integratedMoser_windowUpperBoundData_of_lowerAverageWindow
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p Cnext t eps : ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hnonneg : IntegratedMoserEnergyNonnegativity D u T p0)
    (hinteg : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hp : p0 ≤ p)
    (hp_nonneg : 0 ≤ p)
    (hrho_pos : 0 < rho)
    (hwin : IntegratedMoserHighExcursionLowerAverageWindow
      D u T rho p0 p Cnext t)
    (heps : 0 < eps) :
    IntegratedMoserWindowUpperBoundData
      D u rho p hwin.a hwin.b hwin.M eps := by
  let hI :=
    integratedMoserPrecrossingIntervalData_of_regular_window
      hreg hnonneg hp hp_nonneg hrho_pos.le hwin.hab hwin.ha_pos
      hwin.hb_lt hwin.haT hwin.hbT hwin.currentEnergy_le_Icc
  exact integratedMoser_windowUpperBoundData_of_precrossing
    hinteg hrel hI heps

/-- Upper-gap frontier that may consult the fixed-window upper-bound data
producer for the selected lower-average window.

Unlike `IntegratedMoserWindowUpperGapEpsilonFrontier`, this does not require
the strict gap to hold for every possible witness with the same epsilon.  It
chooses one actual fixed-window witness supplied by the upper-bound calculation,
which is the non-vacuous interface needed by the high-excursion plan. -/
structure IntegratedMoserWindowUpperDataGapFrontier
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 p : ℝ) where
  produce :
    ∀ {Cnext t : ℝ},
      (hwin : IntegratedMoserHighExcursionLowerAverageWindow
        D u T rho p0 p Cnext t) →
      (∀ eps : ℝ, 0 < eps →
        IntegratedMoserWindowUpperBoundData
          D u rho p hwin.a hwin.b hwin.M eps) →
        IntegratedMoserWindowUpperGapWitness
          D u rho p hwin.a hwin.b hwin.M hwin.lowerBound

/-- Compatibility adapter: the older all-witness epsilon-gap frontier implies
the new upper-data-aware frontier.  This direction is intentionally one-way;
the new frontier is weaker because it only has to close the gap for one chosen
upper-bound witness. -/
def integratedMoserWindowUpperDataGapFrontier_of_epsilonGap
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p : ℝ}
    (hgap : IntegratedMoserWindowUpperGapEpsilonFrontier D u T rho p0 p) :
    IntegratedMoserWindowUpperDataGapFrontier D u T rho p0 p where
  produce := by
    intro Cnext t hwin hupperData
    let eps : ℝ := Classical.choose (hgap.choose hwin)
    have heps_spec := Classical.choose_spec (hgap.choose hwin)
    have heps : 0 < eps := heps_spec.1
    have hstrict :
        ∀ {Gbound Ceps : ℝ},
          IntegratedMoserWindowUpperBoundWitness
            D u rho p hwin.a hwin.b hwin.M eps Gbound Ceps →
          eps * Gbound + (hwin.b - hwin.a) * (Ceps * hwin.M) <
            hwin.lowerBound :=
      heps_spec.2
    let hUpperData := hupperData eps heps
    let Gbound : ℝ := Classical.choose hUpperData.bounds
    let hGbound_spec := Classical.choose_spec hUpperData.bounds
    let Ceps : ℝ := Classical.choose hGbound_spec
    have hupper :
        IntegratedMoserWindowUpperBoundWitness
          D u rho p hwin.a hwin.b hwin.M eps Gbound Ceps :=
      Classical.choose_spec hGbound_spec
    exact
      { eps := eps
        Gbound := Gbound
        Ceps := Ceps
        eps_pos := heps
        upperWitness := hupper
        upper_lt_lower := hstrict hupper }

/-- Produce the tied upper-gap witness frontier from an upper-data-aware gap
frontier and the already-proved fixed-window upper-bound calculation. -/
def integratedMoserWindowUpperGapWitnessFrontier_of_upperDataGap
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p : ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hnonneg : IntegratedMoserEnergyNonnegativity D u T p0)
    (hinteg : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hp : p0 ≤ p)
    (hp_nonneg : 0 ≤ p)
    (hrho_pos : 0 < rho)
    (hgap : IntegratedMoserWindowUpperDataGapFrontier D u T rho p0 p) :
    IntegratedMoserWindowUpperGapWitnessFrontier D u T rho p0 p where
  produce := by
    intro Cnext t hwin
    exact
      hgap.produce hwin
        (fun eps heps =>
          integratedMoser_windowUpperBoundData_of_lowerAverageWindow
            hreg hnonneg hinteg hrel hp hp_nonneg hrho_pos hwin heps)

/-- Produce the upper-gap frontier from the already-proved fixed-window
integrated-Moser upper-bound data, leaving only the quantitative epsilon-gap
choice as a frontier. -/
def integratedMoserWindowUpperGapWitnessFrontier_of_epsilonGap
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p : ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hnonneg : IntegratedMoserEnergyNonnegativity D u T p0)
    (hinteg : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hp : p0 ≤ p)
    (hp_nonneg : 0 ≤ p)
    (hrho_pos : 0 < rho)
    (hgap : IntegratedMoserWindowUpperGapEpsilonFrontier D u T rho p0 p) :
    IntegratedMoserWindowUpperGapWitnessFrontier D u T rho p0 p :=
  integratedMoserWindowUpperGapWitnessFrontier_of_upperDataGap
    hreg hnonneg hinteg hrel hp hp_nonneg hrho_pos
    (integratedMoserWindowUpperDataGapFrontier_of_epsilonGap hgap)

/-- Pure assembly of a lower-average window and a tied upper-gap witness into
the packaged contradiction-window frontier object. -/
def integratedMoserContradictionWindow_of_lowerAverage_upperGap
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p Cnext t : ℝ}
    (hlower :
      IntegratedMoserHighExcursionLowerAverageWindow
        D u T rho p0 p Cnext t)
    (hupper :
      IntegratedMoserWindowUpperGapWitness
        D u rho p hlower.a hlower.b hlower.M hlower.lowerBound) :
    IntegratedMoserHighExcursionContradictionWindow
      D u T rho p0 p where
  a := hlower.a
  b := hlower.b
  M := hlower.M
  eps := hupper.eps
  lowerBound := hlower.lowerBound
  Gbound := hupper.Gbound
  Ceps := hupper.Ceps
  eps_pos := hupper.eps_pos
  upperWitness := hupper.upperWitness
  lowerAverage := hlower.lowerAverage
  upper_lt_lower := hupper.upper_lt_lower

/-- Exponentwise high-excursion exclusion input.  A violation above `Cnext`
must produce a contradiction window; constructing that window is the real
analytic frontier. -/
structure IntegratedMoserHighExcursionContradictionWindowFrontier
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 p : ℝ) where
  Cnext : ℝ
  contradictionWindow :
    ∀ t, 0 < t → t < T →
      Cnext < integratedMoserEnergy D u (p + rho) t →
        IntegratedMoserHighExcursionContradictionWindow D u T rho p0 p

/-- Pure assembly from the lower-average and tied upper-gap frontiers to the
existing high-excursion contradiction-window frontier. -/
def integratedMoserContradictionWindowFrontier_of_lowerAverage_upperGap
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p Cnext : ℝ}
    (hp : p0 ≤ p)
    (hp_nonneg : 0 ≤ p)
    (hLp : LpPowerBoundedBefore D p T u)
    (hlower :
      IntegratedMoserHighExcursionLowerAverageWindowFrontier
        D u T rho p0 p Cnext)
    (hupper :
      IntegratedMoserWindowUpperGapWitnessFrontier
        D u T rho p0 p) :
    IntegratedMoserHighExcursionContradictionWindowFrontier
      D u T rho p0 p := by
  refine ⟨Cnext, ?_⟩
  intro t ht0 htT hhigh
  let hwin :=
    hlower.produce hp hp_nonneg hLp t ht0 htT hhigh
  exact
    integratedMoserContradictionWindow_of_lowerAverage_upperGap
      hwin (hupper.produce hwin)

/-- Per-exponent lower-average and upper-gap frontiers.  This Type-valued
record keeps the chosen next-exponent threshold `Cnext` tied to both frontier
suppliers. -/
structure IntegratedMoserLowerUpperWindowFrontiers
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 p : ℝ) where
  Cnext : ℝ
  lowerAverage :
    IntegratedMoserHighExcursionLowerAverageWindowFrontier
      D u T rho p0 p Cnext
  upperGap :
    IntegratedMoserWindowUpperGapWitnessFrontier D u T rho p0 p

namespace IntegratedMoserLowerUpperWindowFrontiers

/-- Convert per-exponent lower-average and upper-gap frontiers to the
contradiction-window frontier consumed by the first-crossing step. -/
def to_contradictionWindowFrontier
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p : ℝ}
    (h : IntegratedMoserLowerUpperWindowFrontiers D u T rho p0 p)
    (hp : p0 ≤ p)
    (hp_nonneg : 0 ≤ p)
    (hLp : LpPowerBoundedBefore D p T u) :
    IntegratedMoserHighExcursionContradictionWindowFrontier
      D u T rho p0 p :=
  integratedMoserContradictionWindowFrontier_of_lowerAverage_upperGap
    hp hp_nonneg hLp h.lowerAverage h.upperGap

end IntegratedMoserLowerUpperWindowFrontiers

/-- Pure contradiction step from the high-excursion frontier to the next
exponent's `LpPowerBoundedBefore` statement.

The proof uses the supplied contradiction window; it does not use a bare
time-integral-to-pointwise principle. -/
theorem LpPowerBoundedBefore_of_highExcursionContradictionWindowFrontier
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p : ℝ}
    (hfront :
      IntegratedMoserHighExcursionContradictionWindowFrontier
        D u T rho p0 p) :
    LpPowerBoundedBefore D (p + rho) T u := by
  refine ⟨hfront.Cnext, ?_⟩
  intro t ht0 htT
  by_contra hnot
  have hhigh_raw :
      hfront.Cnext < D.integral (fun x => (u t x) ^ (p + rho)) :=
    lt_of_not_ge hnot
  have hhigh :
      hfront.Cnext < integratedMoserEnergy D u (p + rho) t := by
    simpa [integratedMoserEnergy] using hhigh_raw
  let hwin := hfront.contradictionWindow t ht0 htT hhigh
  exact false_of_integratedMoserHighExcursionContradictionWindow hwin

/-- Exponentwise high-excursion frontiers sufficient to produce the integrated
first-crossing step.  The current-exponent `LpPowerBoundedBefore` input remains
available because it is needed to build the current window bound. -/
structure IntegratedMoserFirstCrossingFromWindowFrontier
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) where
  highExcursion :
    ∀ p, p0 ≤ p →
      LpPowerBoundedBefore D p T u →
        IntegratedMoserHighExcursionContradictionWindowFrontier
          D u T rho p0 p

/-- Cross-exponent first-crossing frontier split into the lower-average and
upper-gap pieces.  The `p0_nonneg` field is explicit because the lower-average
frontier requires `0 ≤ p`, while the final first-crossing step only quantifies
over `p0 ≤ p`. -/
structure IntegratedMoserFirstCrossingLowerUpperFrontiers
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) where
  p0_nonneg : 0 ≤ p0
  frontiers :
    ∀ p, p0 ≤ p →
      LpPowerBoundedBefore D p T u →
        IntegratedMoserLowerUpperWindowFrontiers D u T rho p0 p

/-- Arithmetic consequence of the abstract Lp bootstrap hypothesis: the base
Moser exponent is nonnegative. -/
theorem p0_nonneg_of_abstractLpBootstrapHypothesis
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {N T rho p0 : ℝ}
    (hboot : AbstractLpBootstrapHypothesis D u N T rho p0) :
    0 ≤ p0 := by
  have hthreshold := AbstractLpBootstrapHypothesis.p0_gt_threshold hboot
  have hone_le : (1 : ℝ) ≤ max 1 (rho * N / 2) := le_max_left _ _
  have hp0_pos : 0 < p0 := by linarith
  exact hp0_pos.le

/-- Producer data reducing the full lower/upper first-crossing package to two
analytic frontiers: high-excursion lower-average thickness and the remaining
epsilon-gap choice.  The fixed-window upper-bound calculation itself is
discharged by `integratedMoserWindowUpperGapWitnessFrontier_of_epsilonGap`. -/
structure IntegratedMoserFirstCrossingLowerAverageEpsilonData
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop where
  regularity : IntegratedMoserFirstCrossingRegularity D u T p0
  energyNonneg : IntegratedMoserEnergyNonnegativity D u T p0
  dissipation : IntegratedMoserDissipationDropBefore D u T rho p0
  relative : RelativeMoserInterpolationBefore D u T rho p0
  rho_pos : 0 < rho
  p0_nonneg : 0 ≤ p0
  lowerAverage :
    ∀ p, p0 ≤ p →
      0 ≤ p →
      LpPowerBoundedBefore D p T u →
        Nonempty
          (Σ Cnext : ℝ,
            IntegratedMoserHighExcursionLowerAverageWindowFrontier
              D u T rho p0 p Cnext)
  epsilonGap :
    ∀ p, p0 ≤ p →
      0 ≤ p →
        IntegratedMoserWindowUpperGapEpsilonFrontier D u T rho p0 p

namespace IntegratedMoserFirstCrossingLowerAverageEpsilonData

/-- Collapse lower-average thickness plus epsilon-gap data to the split
lower/upper first-crossing package. -/
def toLowerUpperFrontiers
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (h : IntegratedMoserFirstCrossingLowerAverageEpsilonData D u T rho p0) :
    IntegratedMoserFirstCrossingLowerUpperFrontiers D u T rho p0 where
  p0_nonneg := h.p0_nonneg
  frontiers := by
    intro p hp hLp
    have hp_nonneg : 0 ≤ p := le_trans h.p0_nonneg hp
    let hlowerChoice :=
      Classical.choice (h.lowerAverage p hp hp_nonneg hLp)
    exact
      { Cnext := hlowerChoice.1
        lowerAverage := hlowerChoice.2
        upperGap :=
          integratedMoserWindowUpperGapWitnessFrontier_of_epsilonGap
            h.regularity h.energyNonneg h.dissipation h.relative
            hp hp_nonneg h.rho_pos (h.epsilonGap p hp hp_nonneg) }

end IntegratedMoserFirstCrossingLowerAverageEpsilonData

/-- Producer data reducing the first-crossing package to lower-average
thickness plus an upper-data-aware strict-gap chooser.

This is the preferred non-vacuous split for the high-excursion route: the gap
chooser is allowed to inspect the fixed-window upper-bound data producer, and
therefore only has to close the gap for one selected witness rather than every
larger witness satisfying the same upper-bound inequality. -/
structure IntegratedMoserFirstCrossingLowerAverageUpperDataGapData
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop where
  regularity : IntegratedMoserFirstCrossingRegularity D u T p0
  energyNonneg : IntegratedMoserEnergyNonnegativity D u T p0
  dissipation : IntegratedMoserDissipationDropBefore D u T rho p0
  relative : RelativeMoserInterpolationBefore D u T rho p0
  rho_pos : 0 < rho
  p0_nonneg : 0 ≤ p0
  lowerAverage :
    ∀ p, p0 ≤ p →
      0 ≤ p →
      LpPowerBoundedBefore D p T u →
        Nonempty
          (Σ Cnext : ℝ,
            IntegratedMoserHighExcursionLowerAverageWindowFrontier
              D u T rho p0 p Cnext)
  upperDataGap :
    ∀ p, p0 ≤ p →
      0 ≤ p →
        Nonempty
          (IntegratedMoserWindowUpperDataGapFrontier D u T rho p0 p)

namespace IntegratedMoserFirstCrossingLowerAverageUpperDataGapData

/-- Collapse lower-average thickness plus the upper-data-aware gap chooser to
the split lower/upper first-crossing package. -/
def toLowerUpperFrontiers
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (h : IntegratedMoserFirstCrossingLowerAverageUpperDataGapData
      D u T rho p0) :
    IntegratedMoserFirstCrossingLowerUpperFrontiers D u T rho p0 where
  p0_nonneg := h.p0_nonneg
  frontiers := by
    intro p hp hLp
    have hp_nonneg : 0 ≤ p := le_trans h.p0_nonneg hp
    let hlowerChoice :=
      Classical.choice (h.lowerAverage p hp hp_nonneg hLp)
    let hupperDataGap :=
      Classical.choice (h.upperDataGap p hp hp_nonneg)
    exact
      { Cnext := hlowerChoice.1
        lowerAverage := hlowerChoice.2
        upperGap :=
          integratedMoserWindowUpperGapWitnessFrontier_of_upperDataGap
            h.regularity h.energyNonneg h.dissipation h.relative
            hp hp_nonneg h.rho_pos hupperDataGap }

end IntegratedMoserFirstCrossingLowerAverageUpperDataGapData

/-- Compatibility conversion from the older all-witness epsilon-gap package to
the preferred upper-data-aware package. -/
def IntegratedMoserFirstCrossingLowerAverageEpsilonData.toUpperDataGapData
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (h : IntegratedMoserFirstCrossingLowerAverageEpsilonData D u T rho p0) :
    IntegratedMoserFirstCrossingLowerAverageUpperDataGapData D u T rho p0 where
  regularity := h.regularity
  energyNonneg := h.energyNonneg
  dissipation := h.dissipation
  relative := h.relative
  rho_pos := h.rho_pos
  p0_nonneg := h.p0_nonneg
  lowerAverage := h.lowerAverage
  upperDataGap := by
    intro p hp hp_nonneg
    exact
      ⟨integratedMoserWindowUpperDataGapFrontier_of_epsilonGap
        (h.epsilonGap p hp hp_nonneg)⟩

/-- Pure wrapper from split lower-average/upper-gap frontiers to the
high-excursion contradiction-window frontier. -/
def integratedMoserFirstCrossingFromWindowFrontier_of_lowerUpperFrontiers
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (hfront :
      IntegratedMoserFirstCrossingLowerUpperFrontiers D u T rho p0) :
    IntegratedMoserFirstCrossingFromWindowFrontier D u T rho p0 where
  highExcursion := by
    intro p hp hLp
    exact
      (hfront.frontiers p hp hLp).to_contradictionWindowFrontier
        hp (le_trans hfront.p0_nonneg hp) hLp

/-- Pure wrapper from the high-excursion window frontier to the existing
`IntegratedMoserFirstCrossingStep` atom. -/
theorem integratedMoserFirstCrossingStep_of_windowFrontier
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (hfront : IntegratedMoserFirstCrossingFromWindowFrontier D u T rho p0) :
    IntegratedMoserFirstCrossingStep D u T rho p0 := by
  intro p hp hLp
  exact LpPowerBoundedBefore_of_highExcursionContradictionWindowFrontier
    (hfront.highExcursion p hp hLp)

/-- Pure wrapper from split lower-average/upper-gap frontiers to the existing
`IntegratedMoserFirstCrossingStep` atom. -/
theorem integratedMoserFirstCrossingStep_of_lowerUpperFrontiers
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (hfront :
      IntegratedMoserFirstCrossingLowerUpperFrontiers D u T rho p0) :
    IntegratedMoserFirstCrossingStep D u T rho p0 :=
  integratedMoserFirstCrossingStep_of_windowFrontier
    (integratedMoserFirstCrossingFromWindowFrontier_of_lowerUpperFrontiers
      hfront)

/-- Direct consumer for the preferred lower-average plus upper-data-aware gap
package. -/
theorem integratedMoserFirstCrossingStep_of_lowerAverageUpperDataGapData
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (hdata :
      IntegratedMoserFirstCrossingLowerAverageUpperDataGapData
        D u T rho p0) :
    IntegratedMoserFirstCrossingStep D u T rho p0 :=
  integratedMoserFirstCrossingStep_of_lowerUpperFrontiers
    hdata.toLowerUpperFrontiers

/-- Direct compatibility consumer for the older all-witness epsilon-gap
package. -/
theorem integratedMoserFirstCrossingStep_of_lowerAverageEpsilonData
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (hdata :
      IntegratedMoserFirstCrossingLowerAverageEpsilonData
        D u T rho p0) :
    IntegratedMoserFirstCrossingStep D u T rho p0 :=
  integratedMoserFirstCrossingStep_of_lowerAverageUpperDataGapData
    hdata.toUpperDataGapData

#print axioms intervalIntegrable_of_integrableOn_uIcc_of_Icc_subset
#print axioms Icc_subset_uIcc_zero_T_of_endpoint_memberships
#print axioms IntegratedMoserFirstCrossingRegularity.power_intervalIntegrable_of_Icc
#print axioms IntegratedMoserFirstCrossingRegularity.gradient_intervalIntegrable_of_Icc
#print axioms intervalIntegrable_max_one_of_intervalIntegrable
#print axioms IntegratedMoserFirstCrossingRegularity.maxOneEnergy_intervalIntegrable_of_Icc
#print axioms intervalDomain_integral_nonneg
#print axioms intervalDomain_integratedMoserEnergy_nonneg_of_pointwise_nonneg
#print axioms intervalDomain_integratedMoserEnergyNonnegativity_of_pointwise_nonneg
#print axioms intervalDomain_integratedMoserEnergyNonnegativity_of_classical
#print axioms intervalDomain_integratedMoserEnergyNonnegativity_of_global_classical
#print axioms currentEnergy_Icc_bound_of_LpPowerBoundedBefore
#print axioms IntegratedMoserPrecrossingIntervalData.left_currentEnergy_le
#print axioms IntegratedMoserPrecrossingIntervalData.maxOneEnergy_timeIntegral_le
#print axioms integratedMoserPrecrossingIntervalData_of_regular_window
#print axioms integratedMoser_windowUpperBoundData_of_precrossing
#print axioms integratedMoser_windowUpperBoundData_of_lowerAverageWindow
#print axioms integratedMoserWindowUpperDataGapFrontier_of_epsilonGap
#print axioms integratedMoserWindowUpperGapWitnessFrontier_of_upperDataGap
#print axioms integratedMoserWindowUpperGapWitnessFrontier_of_epsilonGap
#print axioms false_of_windowUpperBoundWitness_lowerAverage_gap
#print axioms false_of_integratedMoserHighExcursionContradictionWindow
#print axioms integratedMoserContradictionWindow_of_lowerAverage_upperGap
#print axioms integratedMoserContradictionWindowFrontier_of_lowerAverage_upperGap
#print axioms IntegratedMoserLowerUpperWindowFrontiers.to_contradictionWindowFrontier
#print axioms p0_nonneg_of_abstractLpBootstrapHypothesis
#print axioms IntegratedMoserFirstCrossingLowerAverageEpsilonData.toLowerUpperFrontiers
#print axioms IntegratedMoserFirstCrossingLowerAverageUpperDataGapData.toLowerUpperFrontiers
#print axioms IntegratedMoserFirstCrossingLowerAverageEpsilonData.toUpperDataGapData
#print axioms LpPowerBoundedBefore_of_highExcursionContradictionWindowFrontier
#print axioms integratedMoserFirstCrossingFromWindowFrontier_of_lowerUpperFrontiers
#print axioms integratedMoserFirstCrossingStep_of_windowFrontier
#print axioms integratedMoserFirstCrossingStep_of_lowerUpperFrontiers
#print axioms integratedMoserFirstCrossingStep_of_lowerAverageUpperDataGapData
#print axioms integratedMoserFirstCrossingStep_of_lowerAverageEpsilonData

/-- Iterate a supplied integrated first-crossing step along the arithmetic
Moser ladder. -/
theorem moser_iteration_chain_of_integrated_first_crossing_step
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T p0 rho : ℝ}
    (hrho : 0 < rho)
    (hbase : LpPowerBoundedBefore D p0 T u)
    (hstep : IntegratedMoserFirstCrossingStep D u T rho p0) :
    ∀ n : ℕ, LpPowerBoundedBefore D (p0 + n * rho) T u := by
  intro n
  induction n with
  | zero =>
      simp only [CharP.cast_eq_zero, zero_mul, add_zero]
      exact hbase
  | succ n ih =>
      have hexp_eq :
          p0 + (↑(n + 1) : ℝ) * rho = (p0 + ↑n * rho) + rho := by
        push_cast
        ring
      rw [hexp_eq]
      have hp_ge : p0 ≤ p0 + ↑n * rho :=
        le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hrho.le)
      exact hstep (p0 + ↑n * rho) hp_ge ih

/-- A supplied integrated first-crossing step plus downward Lp monotonicity
gives all finite exponents. -/
theorem all_exponents_of_integrated_first_crossing_step_lpmono
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {N T rho p0 : ℝ}
    (hboot : AbstractLpBootstrapHypothesis D u N T rho p0)
    (hstep : IntegratedMoserFirstCrossingStep D u T rho p0)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore D q T u → LpPowerBoundedBefore D p T u) :
    ∀ pExp > 1, LpPowerBoundedBefore D pExp T u := by
  exact all_exponents_of_chain_and_lp_mono
    (AbstractLpBootstrapHypothesis.rho_pos hboot)
    (moser_iteration_chain_of_integrated_first_crossing_step
      (AbstractLpBootstrapHypothesis.rho_pos hboot)
      (AbstractLpBootstrapHypothesis.initial_lp_bound hboot)
      hstep)
    hLpMono

/-- Interval-domain finite-horizon boundedness from a supplied integrated
first-crossing step and the existing quantitative endpoint. -/
theorem intervalDomain_boundedBefore_of_integrated_first_crossing_step
    {u : ℝ → intervalDomain.Point → ℝ} {N T rho p0 : ℝ}
    {pSeq rootBound : ℕ → ℝ}
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u N T rho p0)
    (hstep : IntegratedMoserFirstCrossingStep intervalDomain u T rho p0)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore intervalDomain q T u →
        LpPowerBoundedBefore intervalDomain p T u)
    (hEndpoint :
      (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
        IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound) :
    IsPaper2BoundedBefore intervalDomain T u := by
  have hAll : ∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u :=
    all_exponents_of_integrated_first_crossing_step_lpmono
      hboot hstep hLpMono
  exact intervalDomain_boundedBefore_of_moser_quantitative_endpoint
    (hEndpoint hAll)

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

end
