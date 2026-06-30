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
