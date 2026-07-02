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

/-- Pointwise agreement on the strict positive-time slab used by before-time
Lp bounds. -/
def EqOnPositiveTimesBefore
    {D : BoundedDomainData} (T : ℝ)
    (u w : ℝ → D.Point → ℝ) : Prop :=
  ∀ t, 0 < t → t < T → ∀ x : D.Point, u t x = w t x

/-- `LpPowerBoundedBefore` only samples `0 < t < T`, so it is invariant under
pointwise agreement on that positive-time slab. -/
theorem LpPowerBoundedBefore_congr_pos
    {D : BoundedDomainData} {p T : ℝ}
    {u w : ℝ → D.Point → ℝ}
    (hEq : EqOnPositiveTimesBefore (D := D) T u w) :
    LpPowerBoundedBefore D p T u →
      LpPowerBoundedBefore D p T w := by
  intro h
  rcases h with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro t ht0 htT
  have hfun :
      (fun x : D.Point => (w t x) ^ p) =
        (fun x : D.Point => (u t x) ^ p) := by
    funext x
    rw [← hEq t ht0 htT x]
  simpa [hfun] using hC t ht0 htT

/-- Symmetric positive-time locality for `LpPowerBoundedBefore`. -/
theorem LpPowerBoundedBefore_iff_of_pos_eq
    {D : BoundedDomainData} {p T : ℝ}
    {u w : ℝ → D.Point → ℝ}
    (hEq : EqOnPositiveTimesBefore (D := D) T u w) :
    LpPowerBoundedBefore D p T u ↔
      LpPowerBoundedBefore D p T w := by
  constructor
  · exact LpPowerBoundedBefore_congr_pos hEq
  · exact LpPowerBoundedBefore_congr_pos
      (fun t ht0 htT x => (hEq t ht0 htT x).symm)

/-- The abstract bootstrap hypothesis is positive-time-local because the only
field depending on `u` is `LpPowerBoundedBefore`. -/
theorem AbstractLpBootstrapHypothesis_congr_pos
    {D : BoundedDomainData} {N T rho p0 : ℝ}
    {u w : ℝ → D.Point → ℝ}
    (hEq : EqOnPositiveTimesBefore (D := D) T u w)
    (hboot : AbstractLpBootstrapHypothesis D u N T rho p0) :
    AbstractLpBootstrapHypothesis D w N T rho p0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact AbstractLpBootstrapHypothesis.rho_pos hboot
  · exact AbstractLpBootstrapHypothesis.T_pos hboot
  · exact AbstractLpBootstrapHypothesis.p0_gt_threshold hboot
  · exact LpPowerBoundedBefore_congr_pos hEq
      (AbstractLpBootstrapHypothesis.initial_lp_bound hboot)

/-- `IntegratedMoserFirstCrossingStep` is positive-time-local because it is a
map between `LpPowerBoundedBefore` predicates. -/
theorem IntegratedMoserFirstCrossingStep_congr_pos
    {D : BoundedDomainData} {T rho p0 : ℝ}
    {u w : ℝ → D.Point → ℝ}
    (hEq : EqOnPositiveTimesBefore (D := D) T u w) :
    IntegratedMoserFirstCrossingStep D u T rho p0 →
      IntegratedMoserFirstCrossingStep D w T rho p0 := by
  intro hstep p hp hLp_w
  have hLp_u : LpPowerBoundedBefore D p T u :=
    LpPowerBoundedBefore_congr_pos
      (fun t ht0 htT x => (hEq t ht0 htT x).symm) hLp_w
  exact LpPowerBoundedBefore_congr_pos hEq (hstep p hp hLp_u)

/-- Symmetric positive-time locality for `IntegratedMoserFirstCrossingStep`. -/
theorem IntegratedMoserFirstCrossingStep_iff_of_pos_eq
    {D : BoundedDomainData} {T rho p0 : ℝ}
    {u w : ℝ → D.Point → ℝ}
    (hEq : EqOnPositiveTimesBefore (D := D) T u w) :
    IntegratedMoserFirstCrossingStep D u T rho p0 ↔
      IntegratedMoserFirstCrossingStep D w T rho p0 := by
  constructor
  · exact IntegratedMoserFirstCrossingStep_congr_pos hEq
  · exact IntegratedMoserFirstCrossingStep_congr_pos
      (fun t ht0 htT x => (hEq t ht0 htT x).symm)

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

/-- Pure scalar absorption for one integrated Moser time window, with the
explicit final constant.

`Ydiff` is the endpoint energy difference, `Gint` is the Moser-gradient
integral, `Zint` is the higher-power integral, and `Hint` is the time integral
of the current energy envelope.  If the already-integrated inequality has
gradient coefficient `A`, higher-power coefficient `K`, and interpolation
cost `K * eps`, any surplus `K * eps ≤ A - theta` yields a coefficient-`theta`
integrated drop. -/
theorem scalar_absorb_higherPower_window_const
    {Ydiff Gint Zint Hint A K C0 L p eps Ceps theta : ℝ}
    (hp : 0 < p)
    (hG : 0 ≤ Gint)
    (hC0 : 0 ≤ C0)
    (hK : 0 ≤ K)
    (hL : 0 ≤ L)
    (hCeps : 0 ≤ Ceps)
    (henergy :
      Ydiff + A * Gint ≤ C0 * p * Hint + K * Zint + L * Hint)
    (hrel : Zint ≤ eps * Gint + Ceps * Hint)
    (habsorb : K * eps ≤ A - theta) :
    0 ≤ C0 + (K * Ceps + L) / p ∧
      Ydiff + theta * Gint ≤
        (C0 + (K * Ceps + L) / p) * p * Hint := by
  constructor
  · have hKCeps_nonneg : 0 ≤ K * Ceps := mul_nonneg hK hCeps
    have hnum_nonneg : 0 ≤ K * Ceps + L := add_nonneg hKCeps_nonneg hL
    exact add_nonneg hC0 (div_nonneg hnum_nonneg hp.le)
  · have hKrel :
        K * Zint ≤ K * (eps * Gint + Ceps * Hint) :=
      mul_le_mul_of_nonneg_left hrel hK
    have henergy_rel :
        Ydiff + A * Gint ≤
          C0 * p * Hint + K * (eps * Gint + Ceps * Hint) +
            L * Hint := by
      linarith
    have htheta_le : theta ≤ A - K * eps := by
      linarith
    have hthetaG :
        theta * Gint ≤ (A - K * eps) * Gint :=
      mul_le_mul_of_nonneg_right htheta_le hG
    have hmain :
        Ydiff + theta * Gint ≤
          C0 * p * Hint + (K * Ceps + L) * Hint := by
      nlinarith
    have hfinal :
        (C0 + (K * Ceps + L) / p) * p * Hint =
          C0 * p * Hint + (K * Ceps + L) * Hint := by
      field_simp [ne_of_gt hp]
    simpa [hfinal]

/-- Existential packaging of `scalar_absorb_higherPower_window_const`. -/
theorem scalar_absorb_higherPower_window
    {Ydiff Gint Zint Hint A K C0 L p eps Ceps theta : ℝ}
    (hp : 0 < p)
    (hG : 0 ≤ Gint)
    (hC0 : 0 ≤ C0)
    (hK : 0 ≤ K)
    (hL : 0 ≤ L)
    (hCeps : 0 ≤ Ceps)
    (henergy :
      Ydiff + A * Gint ≤ C0 * p * Hint + K * Zint + L * Hint)
    (hrel : Zint ≤ eps * Gint + Ceps * Hint)
    (habsorb : K * eps ≤ A - theta) :
    ∃ Cfinal, 0 ≤ Cfinal ∧
      Ydiff + theta * Gint ≤ Cfinal * p * Hint := by
  rcases scalar_absorb_higherPower_window_const
      hp hG hC0 hK hL hCeps henergy hrel habsorb with
    ⟨hC, hineq⟩
  exact ⟨C0 + (K * Ceps + L) / p, hC, hineq⟩

/-- A positive coefficient gap gives an epsilon small enough for the integrated
Moser absorption surplus.

The absolute value in the denominator keeps this scalar lemma independent of
any sign information on `p * K`. -/
theorem exists_pos_eps_mul_le_sub_of_coeff_gap
    {p A K theta : ℝ}
    (hgap : theta < p * A) :
    ∃ eps : ℝ, 0 < eps ∧ (p * K) * eps ≤ p * A - theta := by
  let N : ℝ := p * A - theta
  let den : ℝ := 2 * (|p * K| + 1)
  have hN : 0 < N := by
    dsimp [N]
    linarith
  have hden : 0 < den := by
    dsimp [den]
    have habs : 0 ≤ |p * K| := abs_nonneg _
    nlinarith
  refine ⟨N / den, div_pos hN hden, ?_⟩
  by_cases hx : 0 ≤ p * K
  · have hratio : (p * K) / den ≤ 1 := by
      rw [div_le_one hden]
      dsimp [den]
      have hle_abs : p * K ≤ |p * K| := le_abs_self _
      have hle_den : |p * K| ≤ 2 * (|p * K| + 1) := by
        nlinarith [abs_nonneg (p * K)]
      exact le_trans hle_abs hle_den
    calc
      (p * K) * (N / den) = N * ((p * K) / den) := by
        ring_nf
      _ ≤ N * 1 := mul_le_mul_of_nonneg_left hratio hN.le
      _ = N := by ring
  · have hxneg : p * K < 0 := lt_of_not_ge hx
    have hprod_nonpos : (p * K) * (N / den) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hxneg.le (div_nonneg hN.le hden.le)
    exact le_trans hprod_nonpos hN.le

/-- Package a scalar coefficient gap in the surplus shape expected by
`integratedHigherPowerEnergyWindowCoeffFrontier_of_LpBootstrapEnergyInequality`. -/
theorem integratedMoser_surplus_of_coeff_gap
    {theta p0 : ℝ}
    (hgap :
      ∀ p, p0 ≤ p → ∀ A K : ℝ, 0 < A → 0 < K → theta < p * A) :
    ∀ p, p0 ≤ p → ∀ A K : ℝ, 0 < A → 0 < K →
      ∃ eps : ℝ, 0 < eps ∧ (p * K) * eps ≤ p * A - theta := by
  intro p hp A K hA hK
  exact exists_pos_eps_mul_le_sub_of_coeff_gap
    (p := p) (A := A) (K := K) (theta := theta)
    (hgap p hp A K hA hK)

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

/-- The time length of a non-reversed window is controlled by the integral of
`max 1 Y` over that window.  This absorbs constant lower-order terms into the
same envelope used by the integrated Moser drop. -/
theorem intervalIntegral_length_le_integral_max_one
    {a b : ℝ} {Y : ℝ → ℝ}
    (hab : a ≤ b)
    (hYmax_int :
      IntervalIntegrable (fun s => max (1 : ℝ) (Y s)) volume a b) :
    b - a ≤ ∫ s in a..b, max (1 : ℝ) (Y s) := by
  have hconst : IntervalIntegrable (fun _s : ℝ => (1 : ℝ)) volume a b :=
    intervalIntegrable_const
  have hmono :
      (∫ _s in a..b, (1 : ℝ)) ≤
        ∫ s in a..b, max (1 : ℝ) (Y s) :=
    intervalIntegral.integral_mono_on hab hconst hYmax_int
      (fun s _hs => le_max_left (1 : ℝ) (Y s))
  have hlen : (∫ _s in a..b, (1 : ℝ)) = b - a := by
    rw [intervalIntegral.integral_const]
    simp [smul_eq_mul]
  simpa [hlen] using hmono

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

/-- Window fundamental theorem of calculus for the Moser energy profile
`Y_p(t) = integratedMoserEnergy D u p t`.

This is intentionally separate from `IntegratedMoserFirstCrossingRegularity`:
continuity and time-integrability of `Y_p` do not by themselves give
integrability of `deriv Y_p` or the endpoint identity. -/
structure IntegratedMoserEnergyWindowFTC
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T p0 : ℝ) : Prop where
  deriv_intervalIntegrable :
    ∀ p, p0 ≤ p →
      ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        IntervalIntegrable
          (fun s => deriv (fun τ => integratedMoserEnergy D u p τ) s)
          volume t1 t2
  window_ftc :
    ∀ p, p0 ≤ p →
      ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        (∫ s in t1..t2,
          deriv (fun τ => integratedMoserEnergy D u p τ) s) =
        integratedMoserEnergy D u p t2 -
          integratedMoserEnergy D u p t1

/-- The derivative-integrability part of the Moser-energy window FTC.  This is
the analytic frontier that has to come from a genuine time-Leibniz/absolute
continuity producer. -/
def IntegratedMoserEnergyDerivativeWindowIntegrability
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p →
    ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
      IntervalIntegrable
        (fun s => deriv (fun τ => integratedMoserEnergy D u p τ) s)
        volume t1 t2

/-- Coefficient-level full-window higher-power energy input for the integrated
Moser absorption step.

The theorem `integratedMoserDissipationDropBeforeCoeff_of_higherPower_and_relative`
consumes exactly this kind of window inequality together with integrated
relative-Moser interpolation.  The final surplus field records the coefficient
gap needed to absorb the higher-power term into the gradient term. -/
def IntegratedHigherPowerEnergyWindowCoeffFrontier
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 theta : ℝ) : Prop :=
  ∀ p, p0 ≤ p →
    ∃ A K C0 L eps : ℝ,
      0 < eps ∧ 0 ≤ K ∧ 0 ≤ C0 ∧ 0 ≤ L ∧
      (∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        integratedMoserEnergy D u p t2 -
            integratedMoserEnergy D u p t1 +
          A * (∫ s in t1..t2,
            integratedMoserGradientEnergy D u p s) ≤
        (C0 * p * (∫ s in t1..t2,
            max 1 (integratedMoserEnergy D u p s)) +
          K * (∫ s in t1..t2,
            integratedMoserEnergy D u (p + rho) s)) +
          L * (∫ s in t1..t2,
            max 1 (integratedMoserEnergy D u p s))) ∧
      K * eps ≤ A - theta

/-- Integrate one strict-time higher-power energy witness over one closed
window.

The pointwise hypothesis is only required at strict interior times.  Endpoint
issues are handled by the existing a.e. closed-window bridge, while the
endpoint energy difference is supplied explicitly by the window FTC input. -/
theorem integratedHigherPowerEnergyWindowCoeff_of_pointwise_witness
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p A B K L_const t1 t2 : ℝ}
    (hp_pos : 0 < p)
    (hA : 0 < A) (hB : 0 < B) (hK : 0 < K)
    (ht1 : t1 ∈ Set.Icc (0 : ℝ) T)
    (ht2 : t2 ∈ Set.Icc t1 T)
    (hfull :
      ∀ t, 0 < t → t < T →
        (1 / p) *
            deriv (fun τ => integratedMoserEnergy D u p τ) t +
          A * integratedMoserGradientEnergy D u p t +
          B * integratedMoserEnergy D u p t ≤
        K * integratedMoserEnergy D u (p + rho) t + L_const)
    (hFTC :
      (∫ s in t1..t2,
          deriv (fun τ => integratedMoserEnergy D u p τ) s) =
        integratedMoserEnergy D u p t2 -
          integratedMoserEnergy D u p t1)
    (hDeriv_int :
      IntervalIntegrable
        (fun s => deriv (fun τ => integratedMoserEnergy D u p τ) s)
        volume t1 t2)
    (hG_int :
      IntervalIntegrable
        (fun s => integratedMoserGradientEnergy D u p s) volume t1 t2)
    (hY_int :
      IntervalIntegrable
        (fun s => integratedMoserEnergy D u p s) volume t1 t2)
    (hZ_int :
      IntervalIntegrable
        (fun s => integratedMoserEnergy D u (p + rho) s) volume t1 t2)
    (hMax_int :
      IntervalIntegrable
        (fun s => max (1 : ℝ) (integratedMoserEnergy D u p s))
        volume t1 t2)
    (hY_integral_nonneg :
      0 ≤ ∫ s in t1..t2, integratedMoserEnergy D u p s) :
    0 < p * A ∧ 0 ≤ p * K ∧ 0 ≤ (0 : ℝ) ∧
      0 ≤ max (0 : ℝ) (p * L_const) ∧
      integratedMoserEnergy D u p t2 -
          integratedMoserEnergy D u p t1 +
        (p * A) *
          (∫ s in t1..t2, integratedMoserGradientEnergy D u p s) ≤
      ((0 : ℝ) * p *
          (∫ s in t1..t2,
            max (1 : ℝ) (integratedMoserEnergy D u p s)) +
        (p * K) *
          (∫ s in t1..t2,
            integratedMoserEnergy D u (p + rho) s)) +
        max (0 : ℝ) (p * L_const) *
          (∫ s in t1..t2,
            max (1 : ℝ) (integratedMoserEnergy D u p s)) := by
  have hab : t1 ≤ t2 := ht2.1
  have hp_nonneg : 0 ≤ p := hp_pos.le
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  let dY : ℝ → ℝ :=
    fun s => deriv (fun τ => integratedMoserEnergy D u p τ) s
  let G : ℝ → ℝ := fun s => integratedMoserGradientEnergy D u p s
  let Y : ℝ → ℝ := fun s => integratedMoserEnergy D u p s
  let Z : ℝ → ℝ := fun s => integratedMoserEnergy D u (p + rho) s
  let H : ℝ → ℝ := fun s => max (1 : ℝ) (Y s)
  let F : ℝ → ℝ := fun s => dY s + (p * A) * G s + (p * B) * Y s
  let R : ℝ → ℝ := fun s => (p * K) * Z s + p * L_const
  have hF_int : IntervalIntegrable F volume t1 t2 := by
    dsimp [F]
    exact (hDeriv_int.add (hG_int.const_mul (p * A))).add
      (hY_int.const_mul (p * B))
  have hR_int : IntervalIntegrable R volume t1 t2 := by
    dsimp [R]
    exact (hZ_int.const_mul (p * K)).add intervalIntegrable_const
  have hstrict_ae :
      ∀ᵐ s ∂(volume.restrict (Set.Icc t1 t2)), 0 < s ∧ s < T := by
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    have hnull : volume ({(0 : ℝ), T} : Set ℝ) = 0 := by
      exact Set.Finite.measure_zero
        ((Set.finite_singleton T).insert (0 : ℝ)) volume
    refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
    intro s hs
    simp only [Set.mem_setOf_eq] at hs
    have hsIcc : s ∈ Set.Icc t1 t2 := by
      by_contra hs_not
      exact hs (fun hs_mem => False.elim (hs_not hs_mem))
    have hbad : ¬ (0 < s ∧ s < T) := by
      intro hs_good
      exact hs (fun _ => hs_good)
    have hs_nonneg : 0 ≤ s := le_trans ht1.1 hsIcc.1
    have hs_le_T : s ≤ T := le_trans hsIcc.2 ht2.2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    by_cases hs_pos : 0 < s
    · right
      have hT_le_s : T ≤ s :=
        le_of_not_gt (fun hs_lt => hbad ⟨hs_pos, hs_lt⟩)
      exact le_antisymm hs_le_T hT_le_s
    · left
      have hs_nonpos : s ≤ 0 := le_of_not_gt hs_pos
      exact le_antisymm hs_nonpos hs_nonneg
  have hpoint_ae : F ≤ᵐ[volume.restrict (Set.Icc t1 t2)] R := by
    filter_upwards [hstrict_ae] with s hs
    rcases hs with ⟨hs0, hsT⟩
    have hpt := hfull s hs0 hsT
    have hmul := mul_le_mul_of_nonneg_left hpt hp_nonneg
    have hleft_scale :
        p *
            ((1 / p) * dY s + A * G s + B * Y s) =
          dY s + (p * A) * G s + (p * B) * Y s := by
      field_simp [hp_ne]
    have hright_scale :
        p * (K * Z s + L_const) = (p * K) * Z s + p * L_const := by
      ring
    dsimp [F, R]
    calc
      dY s + (p * A) * G s + (p * B) * Y s =
          p * ((1 / p) * dY s + A * G s + B * Y s) := hleft_scale.symm
      _ ≤ p * (K * Z s + L_const) := hmul
      _ = (p * K) * Z s + p * L_const := hright_scale
  have hmono : ∫ s in t1..t2, F s ≤ ∫ s in t1..t2, R s :=
    intervalIntegral.integral_mono_ae_restrict hab hF_int hR_int hpoint_ae
  have hF_eq :
      (∫ s in t1..t2, F s) =
        (∫ s in t1..t2, dY s) +
          (p * A) * (∫ s in t1..t2, G s) +
          (p * B) * (∫ s in t1..t2, Y s) := by
    dsimp [F]
    rw [intervalIntegral.integral_add
      (hDeriv_int.add (hG_int.const_mul (p * A)))
      (hY_int.const_mul (p * B))]
    rw [intervalIntegral.integral_add hDeriv_int (hG_int.const_mul (p * A))]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_const_mul]
  have hR_eq :
      (∫ s in t1..t2, R s) =
        (p * K) * (∫ s in t1..t2, Z s) +
          (t2 - t1) * (p * L_const) := by
    dsimp [R]
    rw [intervalIntegral.integral_add
      (hZ_int.const_mul (p * K)) intervalIntegrable_const]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_const]
    simp [smul_eq_mul, Z]
  have hmono_expanded :
      integratedMoserEnergy D u p t2 -
            integratedMoserEnergy D u p t1 +
          (p * A) *
            (∫ s in t1..t2, integratedMoserGradientEnergy D u p s) +
          (p * B) *
            (∫ s in t1..t2, integratedMoserEnergy D u p s) ≤
        (p * K) *
            (∫ s in t1..t2,
              integratedMoserEnergy D u (p + rho) s) +
          (t2 - t1) * (p * L_const) := by
    rw [hF_eq, hR_eq] at hmono
    simpa [dY, G, Y, Z, hFTC] using hmono
  have hBterm_nonneg :
      0 ≤ (p * B) *
        (∫ s in t1..t2, integratedMoserEnergy D u p s) :=
    mul_nonneg (mul_nonneg hp_nonneg hB.le) hY_integral_nonneg
  have hdrop :
      integratedMoserEnergy D u p t2 -
            integratedMoserEnergy D u p t1 +
          (p * A) *
            (∫ s in t1..t2, integratedMoserGradientEnergy D u p s) ≤
        (p * K) *
            (∫ s in t1..t2,
              integratedMoserEnergy D u (p + rho) s) +
          (t2 - t1) * (p * L_const) := by
    nlinarith [hmono_expanded, hBterm_nonneg]
  have hlen_nonneg : 0 ≤ t2 - t1 := sub_nonneg.mpr hab
  have hlen_le_H :
      t2 - t1 ≤
        ∫ s in t1..t2,
          max (1 : ℝ) (integratedMoserEnergy D u p s) :=
    intervalIntegral_length_le_integral_max_one hab hMax_int
  have hH_nonneg :
      0 ≤ ∫ s in t1..t2,
        max (1 : ℝ) (integratedMoserEnergy D u p s) :=
    le_trans hlen_nonneg hlen_le_H
  have hconst :
      (t2 - t1) * (p * L_const) ≤
        max (0 : ℝ) (p * L_const) *
          (∫ s in t1..t2,
            max (1 : ℝ) (integratedMoserEnergy D u p s)) := by
    by_cases hpL_nonneg : 0 ≤ p * L_const
    · have hscale :=
        mul_le_mul_of_nonneg_left hlen_le_H hpL_nonneg
      have hmax : max (0 : ℝ) (p * L_const) = p * L_const :=
        max_eq_right hpL_nonneg
      nlinarith
    · have hpL_nonpos : p * L_const ≤ 0 := le_of_not_ge hpL_nonneg
      have hleft_nonpos : (t2 - t1) * (p * L_const) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hlen_nonneg hpL_nonpos
      have hright_nonneg :
          0 ≤ max (0 : ℝ) (p * L_const) *
            (∫ s in t1..t2,
              max (1 : ℝ) (integratedMoserEnergy D u p s)) :=
        mul_nonneg (le_max_left _ _) hH_nonneg
      linarith
  refine ⟨mul_pos hp_pos hA, mul_nonneg hp_nonneg hK.le, by norm_num,
    le_max_left _ _, ?_⟩
  nlinarith [hdrop, hconst]

/-- Closed-window higher-power energy frontier from the strict-time
`LpBootstrapEnergyInequality`, assuming the separate window FTC, window
integrability/nonnegativity, and the coefficient surplus needed for the target
drop coefficient.

This theorem is intentionally honest about the remaining analytic inputs:
`IntegratedMoserEnergyWindowFTC` is not derived from continuity, and the final
surplus is supplied explicitly. -/
theorem
    integratedHigherPowerEnergyWindowCoeffFrontier_of_LpBootstrapEnergyInequality
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 theta : ℝ}
    (henergy : LpBootstrapEnergyInequality D u T rho p0)
    (hFTC : IntegratedMoserEnergyWindowFTC D u T p0)
    (hp_pos : ∀ p, p0 ≤ p → 0 < p)
    (hG_int :
      ∀ p, p0 ≤ p → ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        IntervalIntegrable
          (fun s => integratedMoserGradientEnergy D u p s) volume t1 t2)
    (hY_int :
      ∀ p, p0 ≤ p → ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        IntervalIntegrable
          (fun s => integratedMoserEnergy D u p s) volume t1 t2)
    (hZ_int :
      ∀ p, p0 ≤ p → ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        IntervalIntegrable
          (fun s => integratedMoserEnergy D u (p + rho) s)
          volume t1 t2)
    (hMax_int :
      ∀ p, p0 ≤ p → ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        IntervalIntegrable
          (fun s => max (1 : ℝ) (integratedMoserEnergy D u p s))
          volume t1 t2)
    (hY_integral_nonneg :
      ∀ p, p0 ≤ p → ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        0 ≤ ∫ s in t1..t2, integratedMoserEnergy D u p s)
    (hsurplus :
      ∀ p, p0 ≤ p → ∀ A K, 0 < A → 0 < K →
        ∃ eps, 0 < eps ∧ (p * K) * eps ≤ p * A - theta) :
    IntegratedHigherPowerEnergyWindowCoeffFrontier D u T rho p0 theta := by
  intro p hp
  rcases henergy p hp with ⟨A, hA, B, hB, K, hK, L_const, hpoint_raw⟩
  rcases hsurplus p hp A K hA hK with ⟨eps, heps, habsorb⟩
  have hp_pos_p : 0 < p := hp_pos p hp
  have hpoint :
      ∀ t, 0 < t → t < T →
        (1 / p) *
            deriv (fun τ => integratedMoserEnergy D u p τ) t +
          A * integratedMoserGradientEnergy D u p t +
          B * integratedMoserEnergy D u p t ≤
        K * integratedMoserEnergy D u (p + rho) t + L_const := by
    intro t ht0 htT
    simpa [integratedMoserEnergy, integratedMoserGradientEnergy] using
      hpoint_raw t ht0 htT
  refine
    ⟨p * A, p * K, 0, max (0 : ℝ) (p * L_const), eps,
      heps, mul_nonneg hp_pos_p.le hK.le, by norm_num,
      le_max_left _ _, ?_, habsorb⟩
  intro t1 ht1 t2 ht2
  rcases
    integratedHigherPowerEnergyWindowCoeff_of_pointwise_witness
      (D := D) (u := u) (T := T) (rho := rho) (p := p)
      (A := A) (B := B) (K := K) (L_const := L_const)
      (t1 := t1) (t2 := t2)
      hp_pos_p hA hB hK ht1 ht2 hpoint
      (hFTC.window_ftc p hp t1 ht1 t2 ht2)
      (hFTC.deriv_intervalIntegrable p hp t1 ht1 t2 ht2)
      (hG_int p hp t1 ht1 t2 ht2)
      (hY_int p hp t1 ht1 t2 ht2)
      (hZ_int p hp t1 ht1 t2 ht2)
      (hMax_int p hp t1 ht1 t2 ht2)
      (hY_integral_nonneg p hp t1 ht1 t2 ht2) with
    ⟨_hAwin, _hKwin, _hC0, _hLwin, hwindow⟩
  simpa using hwindow

/-- Closed-window higher-power energy frontier from the strict-time
`LpBootstrapEnergyInequality`, with the absorption surplus supplied by a
scalar coefficient gap `theta < p * A`. -/
theorem
    integratedHigherPowerEnergyWindowCoeffFrontier_of_LpBootstrapEnergyInequality_coeffGap
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 theta : ℝ}
    (henergy : LpBootstrapEnergyInequality D u T rho p0)
    (hFTC : IntegratedMoserEnergyWindowFTC D u T p0)
    (hp_pos : ∀ p, p0 ≤ p → 0 < p)
    (hG_int :
      ∀ p, p0 ≤ p → ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        IntervalIntegrable
          (fun s => integratedMoserGradientEnergy D u p s) volume t1 t2)
    (hY_int :
      ∀ p, p0 ≤ p → ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        IntervalIntegrable
          (fun s => integratedMoserEnergy D u p s) volume t1 t2)
    (hZ_int :
      ∀ p, p0 ≤ p → ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        IntervalIntegrable
          (fun s => integratedMoserEnergy D u (p + rho) s)
          volume t1 t2)
    (hMax_int :
      ∀ p, p0 ≤ p → ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        IntervalIntegrable
          (fun s => max (1 : ℝ) (integratedMoserEnergy D u p s))
          volume t1 t2)
    (hY_integral_nonneg :
      ∀ p, p0 ≤ p → ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        0 ≤ ∫ s in t1..t2, integratedMoserEnergy D u p s)
    (hgap :
      ∀ p, p0 ≤ p → ∀ A K : ℝ, 0 < A → 0 < K → theta < p * A) :
    IntegratedHigherPowerEnergyWindowCoeffFrontier D u T rho p0 theta :=
  integratedHigherPowerEnergyWindowCoeffFrontier_of_LpBootstrapEnergyInequality
    henergy hFTC hp_pos hG_int hY_int hZ_int hMax_int
    hY_integral_nonneg
    (integratedMoser_surplus_of_coeff_gap hgap)

/-- Window-level absorption into the coefficient-parameterized integrated
Moser drop.

This theorem deliberately starts from already-integrated window inequalities.
Producing those inequalities from the PDE energy identity is the remaining PDE
frontier; the algebraic absorption step itself is closed here. -/
theorem
    integratedMoserDissipationDropBeforeCoeff_of_higherPower_and_relative
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 theta : ℝ}
    (hp_pos : ∀ p, p0 ≤ p → 0 < p)
    (henergy :
      ∀ p, p0 ≤ p →
        ∃ A K C0 L eps : ℝ,
          0 < eps ∧ 0 ≤ K ∧ 0 ≤ C0 ∧ 0 ≤ L ∧
          (∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
            integratedMoserEnergy D u p t2 -
                integratedMoserEnergy D u p t1 +
              A * ∫ s in t1..t2,
                integratedMoserGradientEnergy D u p s ≤
            (C0 * p * (∫ s in t1..t2,
                max 1 (integratedMoserEnergy D u p s)) +
              K * (∫ s in t1..t2,
                integratedMoserEnergy D u (p + rho) s)) +
              L * (∫ s in t1..t2,
                max 1 (integratedMoserEnergy D u p s))) ∧
          K * eps ≤ A - theta)
    (hrelInt :
      ∀ p, p0 ≤ p → ∀ eps, 0 < eps →
        ∃ Ceps, 0 ≤ Ceps ∧
          ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
            ∫ s in t1..t2,
                integratedMoserEnergy D u (p + rho) s ≤
              eps * (∫ s in t1..t2,
                integratedMoserGradientEnergy D u p s) +
              Ceps * (∫ s in t1..t2,
                max 1 (integratedMoserEnergy D u p s)))
    (hG_nonneg :
      ∀ p, p0 ≤ p → ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        0 ≤ ∫ s in t1..t2, integratedMoserGradientEnergy D u p s) :
    IntegratedMoserDissipationDropBeforeCoeff theta D u T rho p0 := by
  intro p hp
  rcases henergy p hp with
    ⟨A, K, C0, L, eps, heps, hK, hC0, hL, henergy_window, habsorb⟩
  rcases hrelInt p hp eps heps with
    ⟨Ceps, hCeps, hrel_window⟩
  refine ⟨C0 + (K * Ceps + L) / p, ?_, ?_⟩
  · have hKCeps_nonneg : 0 ≤ K * Ceps := mul_nonneg hK hCeps
    have hnum_nonneg : 0 ≤ K * Ceps + L := add_nonneg hKCeps_nonneg hL
    exact add_nonneg hC0 (div_nonneg hnum_nonneg (hp_pos p hp).le)
  · intro t1 ht1 t2 ht2
    have henergy_scalar :
        integratedMoserEnergy D u p t2 -
              integratedMoserEnergy D u p t1 +
            A * ∫ s in t1..t2, integratedMoserGradientEnergy D u p s ≤
          (C0 * p *
              (∫ s in t1..t2, max 1 (integratedMoserEnergy D u p s)) +
            K * (∫ s in t1..t2,
              integratedMoserEnergy D u (p + rho) s)) +
          L * (∫ s in t1..t2,
            max 1 (integratedMoserEnergy D u p s)) := by
      exact henergy_window t1 ht1 t2 ht2
    rcases
      scalar_absorb_higherPower_window_const
        (Ydiff :=
          integratedMoserEnergy D u p t2 -
            integratedMoserEnergy D u p t1)
        (Gint :=
          ∫ s in t1..t2, integratedMoserGradientEnergy D u p s)
        (Zint :=
          ∫ s in t1..t2, integratedMoserEnergy D u (p + rho) s)
        (Hint :=
          ∫ s in t1..t2, max 1 (integratedMoserEnergy D u p s))
        (A := A) (K := K) (C0 := C0) (L := L) (p := p)
        (eps := eps) (Ceps := Ceps) (theta := theta)
        (hp_pos p hp) (hG_nonneg p hp t1 ht1 t2 ht2)
        hC0 hK hL hCeps
        henergy_scalar
        (hrel_window t1 ht1 t2 ht2)
        habsorb with
      ⟨_hCfinal, hwindow⟩
    simpa [integratedMoserEnergy, integratedMoserGradientEnergy]
      using hwindow

/-- Named-frontier version of
`integratedMoserDissipationDropBeforeCoeff_of_higherPower_and_relative`. -/
theorem
    integratedMoserDissipationDropBeforeCoeff_of_higherPowerFrontier_and_relative
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 theta : ℝ}
    (hp_pos : ∀ p, p0 ≤ p → 0 < p)
    (henergy :
      IntegratedHigherPowerEnergyWindowCoeffFrontier D u T rho p0 theta)
    (hrelInt :
      ∀ p, p0 ≤ p → ∀ eps, 0 < eps →
        ∃ Ceps, 0 ≤ Ceps ∧
          ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
            ∫ s in t1..t2,
                integratedMoserEnergy D u (p + rho) s ≤
              eps * (∫ s in t1..t2,
                integratedMoserGradientEnergy D u p s) +
              Ceps * (∫ s in t1..t2,
                max 1 (integratedMoserEnergy D u p s)))
    (hG_nonneg :
      ∀ p, p0 ≤ p → ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        0 ≤ ∫ s in t1..t2, integratedMoserGradientEnergy D u p s) :
    IntegratedMoserDissipationDropBeforeCoeff theta D u T rho p0 :=
  integratedMoserDissipationDropBeforeCoeff_of_higherPower_and_relative
    hp_pos henergy hrelInt hG_nonneg

/-- A nonnegative gradient energy has a nonnegative interval integral over a
non-reversed time interval. -/
theorem integratedMoserGradientEnergy_intervalIntegral_nonneg_of_forall
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {p a b : ℝ}
    (hab : a ≤ b)
    (hG_nonneg : ∀ t, 0 ≤ integratedMoserGradientEnergy D u p t) :
    0 ≤ ∫ t in a..b, integratedMoserGradientEnergy D u p t :=
  intervalIntegral.integral_nonneg_of_forall hab hG_nonneg

/-- A nonnegative gradient energy on the integration window has a nonnegative
interval integral over that non-reversed window. -/
theorem integratedMoserGradientEnergy_intervalIntegral_nonneg_of_nonneg_on
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {p a b : ℝ}
    (hab : a ≤ b)
    (hG_nonneg :
      ∀ t ∈ Set.Icc a b,
        0 ≤ integratedMoserGradientEnergy D u p t) :
    0 ≤ ∫ t in a..b, integratedMoserGradientEnergy D u p t :=
  intervalIntegral.integral_nonneg hab hG_nonneg

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

/-- On a closed Moser window `[a,b] ⊆ [0,T]`, almost every point in the
closed interval is a strict interior time.  The only possible failures are the
endpoint singletons `{0,T}`. -/
theorem ae_restrict_Icc_strictInterior_of_Icc_endpoints
    {T a b : ℝ}
    (haT : a ∈ Set.Icc (0 : ℝ) T)
    (hbT : b ∈ Set.Icc a T) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc a b)), 0 < s ∧ s < T := by
  refine (ae_restrict_iff' measurableSet_Icc).2 ?_
  have hnull : volume ({(0 : ℝ), T} : Set ℝ) = 0 := by
    exact Set.Finite.measure_zero ((Set.finite_singleton T).insert (0 : ℝ)) volume
  refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
  intro s hs
  simp only [Set.mem_setOf_eq] at hs
  have hsIcc : s ∈ Set.Icc a b := by
    by_contra hs_not
    exact hs (fun hs_mem => False.elim (hs_not hs_mem))
  have hbad : ¬ (0 < s ∧ s < T) := by
    intro hs_good
    exact hs (fun _ => hs_good)
  have hs_nonneg : 0 ≤ s := le_trans haT.1 hsIcc.1
  have hs_le_T : s ≤ T := le_trans hsIcc.2 hbT.2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  by_cases hs_pos : 0 < s
  · right
    have hT_le_s : T ≤ s := by
      exact le_of_not_gt (fun hs_lt => hbad ⟨hs_pos, hs_lt⟩)
    exact le_antisymm hs_le_T hT_le_s
  · left
    have hs_nonpos : s ≤ 0 := le_of_not_gt hs_pos
    exact le_antisymm hs_nonpos hs_nonneg

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

/-- Strict-interior integrated relative-Moser estimate with a fixed relative
constant and the lower-order term kept as `∫ max 1 Y_p`.

The strict endpoint assumptions are essential for this direct pointwise
integration route: `RelativeMoserInterpolationBefore` only supplies the
interpolation inequality for `0 < t < T`. -/
theorem
    relativeMoser_higherPower_timeIntegral_le_of_Icc_currentEnergy_maxOne_const
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p a b eps Ceps : ℝ}
    (hCeps_nonneg : 0 ≤ Ceps)
    (hrel_eps :
      ∀ t, 0 < t → t < T →
        D.integral (fun x => (u t x) ^ (p + rho)) ≤
          eps * D.integral (fun x =>
            (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
          Ceps * D.integral (fun x => (u t x) ^ p))
    (hab : a ≤ b)
    (ha : 0 < a)
    (hb : b < T)
    (hZ_int :
      IntervalIntegrable
        (fun s => integratedMoserEnergy D u (p + rho) s)
        volume a b)
    (hG_int :
      IntervalIntegrable
        (fun s => integratedMoserGradientEnergy D u p s)
        volume a b)
    (hY_int :
      IntervalIntegrable
        (fun s => integratedMoserEnergy D u p s)
        volume a b) :
    ∫ s in a..b, integratedMoserEnergy D u (p + rho) s ≤
      eps * (∫ s in a..b, integratedMoserGradientEnergy D u p s) +
      Ceps * (∫ s in a..b,
        max (1 : ℝ) (integratedMoserEnergy D u p s)) := by
  have hYmax_int :
      IntervalIntegrable
        (fun s => max (1 : ℝ) (integratedMoserEnergy D u p s))
        volume a b :=
    intervalIntegrable_max_one_of_intervalIntegrable hY_int
  have hR_int :
      IntervalIntegrable
        (fun s =>
          eps * integratedMoserGradientEnergy D u p s +
            Ceps * integratedMoserEnergy D u p s)
        volume a b :=
    (hG_int.const_mul eps).add (hY_int.const_mul Ceps)
  have hpoint :
      ∀ s ∈ Set.Icc a b,
        integratedMoserEnergy D u (p + rho) s ≤
          eps * integratedMoserGradientEnergy D u p s +
            Ceps * integratedMoserEnergy D u p s := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    have hsT : s < T := lt_of_le_of_lt hs.2 hb
    simpa [integratedMoserEnergy, integratedMoserGradientEnergy] using
      hrel_eps s hs0 hsT
  have hmono :
      ∫ s in a..b, integratedMoserEnergy D u (p + rho) s ≤
        ∫ s in a..b,
          eps * integratedMoserGradientEnergy D u p s +
            Ceps * integratedMoserEnergy D u p s :=
    intervalIntegral.integral_mono_on hab hZ_int hR_int hpoint
  have hR_eq :
      (∫ s in a..b,
          eps * integratedMoserGradientEnergy D u p s +
            Ceps * integratedMoserEnergy D u p s) =
        eps * (∫ s in a..b, integratedMoserGradientEnergy D u p s) +
          Ceps * (∫ s in a..b, integratedMoserEnergy D u p s) := by
    have hG_mul :
        (∫ s in a..b, eps * integratedMoserGradientEnergy D u p s) =
          eps * (∫ s in a..b, integratedMoserGradientEnergy D u p s) :=
      intervalIntegral.integral_const_mul eps
        (fun s => integratedMoserGradientEnergy D u p s)
    have hY_mul :
        (∫ s in a..b, Ceps * integratedMoserEnergy D u p s) =
          Ceps * (∫ s in a..b, integratedMoserEnergy D u p s) :=
      intervalIntegral.integral_const_mul Ceps
        (fun s => integratedMoserEnergy D u p s)
    calc
      (∫ s in a..b,
          eps * integratedMoserGradientEnergy D u p s +
            Ceps * integratedMoserEnergy D u p s)
          = (∫ s in a..b, eps * integratedMoserGradientEnergy D u p s) +
              ∫ s in a..b, Ceps * integratedMoserEnergy D u p s := by
            exact intervalIntegral.integral_add
              (hG_int.const_mul eps) (hY_int.const_mul Ceps)
      _ = eps * (∫ s in a..b, integratedMoserGradientEnergy D u p s) +
            Ceps * (∫ s in a..b, integratedMoserEnergy D u p s) := by
            rw [hG_mul, hY_mul]
  have hY_le_max_point :
      ∀ s ∈ Set.Icc a b,
        integratedMoserEnergy D u p s ≤
          max (1 : ℝ) (integratedMoserEnergy D u p s) := by
    intro s _hs
    exact le_max_right (1 : ℝ) (integratedMoserEnergy D u p s)
  have hY_le_max_int :
      ∫ s in a..b, integratedMoserEnergy D u p s ≤
        ∫ s in a..b,
          max (1 : ℝ) (integratedMoserEnergy D u p s) :=
    intervalIntegral.integral_mono_on hab hY_int hYmax_int hY_le_max_point
  have hscaled :
      Ceps * (∫ s in a..b, integratedMoserEnergy D u p s) ≤
        Ceps * (∫ s in a..b,
          max (1 : ℝ) (integratedMoserEnergy D u p s)) :=
    mul_le_mul_of_nonneg_left hY_le_max_int hCeps_nonneg
  rw [hR_eq] at hmono
  linarith

/-- Strict-interior integrated relative-Moser estimate with the lower-order
current energy kept as `∫ max 1 Y_p`. -/
theorem relativeMoser_higherPower_timeIntegral_le_of_Icc_currentEnergy_maxOne
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b eps : ℝ}
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hp : p0 ≤ p)
    (heps : 0 < eps)
    (hab : a ≤ b)
    (ha : 0 < a)
    (hb : b < T)
    (hZ_int :
      IntervalIntegrable
        (fun s => integratedMoserEnergy D u (p + rho) s)
        volume a b)
    (hG_int :
      IntervalIntegrable
        (fun s => integratedMoserGradientEnergy D u p s)
        volume a b)
    (hY_int :
      IntervalIntegrable
        (fun s => integratedMoserEnergy D u p s)
        volume a b) :
    ∃ Ceps, 0 ≤ Ceps ∧
      ∫ s in a..b, integratedMoserEnergy D u (p + rho) s ≤
        eps * (∫ s in a..b, integratedMoserGradientEnergy D u p s) +
        Ceps * (∫ s in a..b,
          max (1 : ℝ) (integratedMoserEnergy D u p s)) := by
  rcases hrel p hp eps heps with ⟨Ceps, hCeps_nonneg, hrel_eps⟩
  refine ⟨Ceps, hCeps_nonneg, ?_⟩
  exact
    relativeMoser_higherPower_timeIntegral_le_of_Icc_currentEnergy_maxOne_const
      (D := D) (u := u) (T := T) (rho := rho) (p := p)
      (a := a) (b := b) (eps := eps) (Ceps := Ceps)
      hCeps_nonneg hrel_eps hab ha hb hZ_int hG_int hY_int

/-- Strict-interior all-window version of the integrated relative-Moser estimate.
This matches the desired full-window `hrelInt` shape except that windows must lie
strictly inside `(0,T)`, reflecting the current pointwise predicate. -/
theorem relativeMoser_hrelInt_strictInterior
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hrho_nonneg : 0 ≤ rho) :
    ∀ p, p0 ≤ p → ∀ eps, 0 < eps →
      ∃ Ceps, 0 ≤ Ceps ∧
        ∀ a b, a ≤ b → 0 < a → b < T →
          ∫ s in a..b, integratedMoserEnergy D u (p + rho) s ≤
            eps * (∫ s in a..b, integratedMoserGradientEnergy D u p s) +
            Ceps * (∫ s in a..b,
              max (1 : ℝ) (integratedMoserEnergy D u p s)) := by
  intro p hp eps heps
  rcases hrel p hp eps heps with ⟨Ceps, hCeps_nonneg, hrel_eps⟩
  refine ⟨Ceps, hCeps_nonneg, ?_⟩
  intro a b hab ha hb
  have hT_nonneg : 0 ≤ T := le_trans ha.le (le_trans hab hb.le)
  have hsub : Set.Icc a b ⊆ Set.uIcc (0 : ℝ) T := by
    intro s hs
    rw [Set.uIcc_of_le hT_nonneg]
    exact ⟨le_trans ha.le hs.1, le_trans hs.2 hb.le⟩
  have hp_rho : p0 ≤ p + rho := by
    linarith
  have hZ_int :
      IntervalIntegrable
        (fun s => integratedMoserEnergy D u (p + rho) s) volume a b :=
    hreg.power_intervalIntegrable_of_Icc hp_rho hab hsub
  have hG_int :
      IntervalIntegrable
        (fun s => integratedMoserGradientEnergy D u p s) volume a b :=
    hreg.gradient_intervalIntegrable_of_Icc hp hab hsub
  have hY_int :
      IntervalIntegrable
        (fun s => integratedMoserEnergy D u p s) volume a b :=
    hreg.power_intervalIntegrable_of_Icc hp hab hsub
  exact
    relativeMoser_higherPower_timeIntegral_le_of_Icc_currentEnergy_maxOne_const
      (D := D) (u := u) (T := T) (rho := rho) (p := p)
      (a := a) (b := b) (eps := eps) (Ceps := Ceps)
      hCeps_nonneg hrel_eps hab ha hb hZ_int hG_int hY_int

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

/-- Full closed-window integrated relative-Moser estimate.  Endpoint failures
are ignored by an a.e. monotonicity argument on the interval-integral domain. -/
theorem relativeMoser_hrelInt_closedWindow_of_regular
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hrho_nonneg : 0 ≤ rho) :
    ∀ p, p0 ≤ p → ∀ eps, 0 < eps →
      ∃ Ceps, 0 ≤ Ceps ∧
        ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
          ∫ s in t1..t2, integratedMoserEnergy D u (p + rho) s ≤
            eps * (∫ s in t1..t2,
              integratedMoserGradientEnergy D u p s) +
            Ceps * (∫ s in t1..t2,
              max (1 : ℝ) (integratedMoserEnergy D u p s)) := by
  intro p hp eps heps
  rcases hrel p hp eps heps with ⟨Ceps, hCeps_nonneg, hrel_eps⟩
  refine ⟨Ceps, hCeps_nonneg, ?_⟩
  intro t1 ht1 t2 ht2
  have hab : t1 ≤ t2 := ht2.1
  have hp_rho : p0 ≤ p + rho := by
    linarith
  have hsub : Set.Icc t1 t2 ⊆ Set.uIcc (0 : ℝ) T :=
    Icc_subset_uIcc_zero_T_of_endpoint_memberships ht1 ht2
  have hZ_int :
      IntervalIntegrable
        (fun s => integratedMoserEnergy D u (p + rho) s) volume t1 t2 :=
    hreg.power_intervalIntegrable_of_Icc hp_rho hab hsub
  have hG_int :
      IntervalIntegrable
        (fun s => integratedMoserGradientEnergy D u p s) volume t1 t2 :=
    hreg.gradient_intervalIntegrable_of_Icc hp hab hsub
  have hYmax_int :
      IntervalIntegrable
        (fun s => max (1 : ℝ) (integratedMoserEnergy D u p s)) volume t1 t2 :=
    hreg.maxOneEnergy_intervalIntegrable_of_Icc hp hab hsub
  let R : ℝ → ℝ := fun s =>
    eps * integratedMoserGradientEnergy D u p s +
      Ceps * max (1 : ℝ) (integratedMoserEnergy D u p s)
  have hR_int : IntervalIntegrable R volume t1 t2 := by
    dsimp [R]
    exact (hG_int.const_mul eps).add (hYmax_int.const_mul Ceps)
  have hpoint_ae :
      integratedMoserEnergy D u (p + rho) ≤ᵐ[volume.restrict (Set.Icc t1 t2)]
        R := by
    filter_upwards
      [ae_restrict_Icc_strictInterior_of_Icc_endpoints ht1 ht2] with s hs
    rcases hs with ⟨hs0, hsT⟩
    have hrel_s := hrel_eps s hs0 hsT
    have hY_le_max :
        integratedMoserEnergy D u p s ≤
          max (1 : ℝ) (integratedMoserEnergy D u p s) :=
      le_max_right _ _
    have hCY_le :
        Ceps * integratedMoserEnergy D u p s ≤
          Ceps * max (1 : ℝ) (integratedMoserEnergy D u p s) :=
      mul_le_mul_of_nonneg_left hY_le_max hCeps_nonneg
    have hCY_le' :
        Ceps * (D.integral fun x => u s x ^ p) ≤
          Ceps * max (1 : ℝ) (D.integral fun x => u s x ^ p) := by
      simpa [integratedMoserEnergy] using hCY_le
    dsimp [R, integratedMoserEnergy, integratedMoserGradientEnergy]
    exact hrel_s.trans (add_le_add_right hCY_le' _)
  have hmono :
      ∫ s in t1..t2, integratedMoserEnergy D u (p + rho) s ≤
        ∫ s in t1..t2, R s :=
    intervalIntegral.integral_mono_ae_restrict hab hZ_int hR_int hpoint_ae
  have hR_eq :
      (∫ s in t1..t2, R s) =
        eps * (∫ s in t1..t2,
          integratedMoserGradientEnergy D u p s) +
        Ceps * (∫ s in t1..t2,
          max (1 : ℝ) (integratedMoserEnergy D u p s)) := by
    dsimp [R]
    have hG_mul :
        (∫ s in t1..t2, eps * integratedMoserGradientEnergy D u p s) =
          eps * (∫ s in t1..t2,
            integratedMoserGradientEnergy D u p s) :=
      intervalIntegral.integral_const_mul eps
        (fun s => integratedMoserGradientEnergy D u p s)
    have hY_mul :
        (∫ s in t1..t2,
            Ceps * max (1 : ℝ) (integratedMoserEnergy D u p s)) =
          Ceps * (∫ s in t1..t2,
            max (1 : ℝ) (integratedMoserEnergy D u p s)) :=
      intervalIntegral.integral_const_mul Ceps
        (fun s => max (1 : ℝ) (integratedMoserEnergy D u p s))
    calc
      (∫ s in t1..t2,
          eps * integratedMoserGradientEnergy D u p s +
            Ceps * max (1 : ℝ) (integratedMoserEnergy D u p s))
          = (∫ s in t1..t2,
              eps * integratedMoserGradientEnergy D u p s) +
            ∫ s in t1..t2,
              Ceps * max (1 : ℝ) (integratedMoserEnergy D u p s) := by
            exact intervalIntegral.integral_add
              (hG_int.const_mul eps) (hYmax_int.const_mul Ceps)
      _ = eps * (∫ s in t1..t2,
              integratedMoserGradientEnergy D u p s) +
            Ceps * (∫ s in t1..t2,
              max (1 : ℝ) (integratedMoserEnergy D u p s)) := by
            rw [hG_mul, hY_mul]
  exact le_trans hmono (by rw [hR_eq])

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

/-- Abstract nonnegativity of Moser gradient energies at interior times. -/
def IntegratedMoserGradientEnergyNonnegativity
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → 0 ≤ p → ∀ t, 0 < t → t < T →
    0 ≤ integratedMoserGradientEnergy D u p t

/-- Package-level version of gradient-energy interval-integral nonnegativity
on an interior time window. -/
theorem integratedMoserGradientEnergy_intervalIntegral_nonneg_of_package
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T p0 p a b : ℝ}
    (hgrad : IntegratedMoserGradientEnergyNonnegativity D u T p0)
    (hp : p0 ≤ p) (hp_nonneg : 0 ≤ p)
    (hab : a ≤ b) (ha_pos : 0 < a) (hb_lt : b < T) :
    0 ≤ ∫ t in a..b, integratedMoserGradientEnergy D u p t := by
  refine integratedMoserGradientEnergy_intervalIntegral_nonneg_of_nonneg_on
    (D := D) (u := u) (p := p) hab ?_
  intro t ht
  exact hgrad p hp hp_nonneg t
    (lt_of_lt_of_le ha_pos ht.1)
    (lt_of_le_of_lt ht.2 hb_lt)

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

/-- For `intervalDomain`, Moser gradient energy is pointwise nonnegative. -/
theorem intervalDomain_integratedMoserGradientEnergy_nonneg
    {u : ℝ → intervalDomain.Point → ℝ} {p t : ℝ} :
    0 ≤ integratedMoserGradientEnergy intervalDomain u p t := by
  exact intervalDomain_integral_nonneg _
    (fun _ => sq_nonneg _)

/-- The interval domain supplies the abstract gradient-energy nonnegativity
package. -/
theorem intervalDomain_integratedMoserGradientEnergyNonnegativity
    {u : ℝ → intervalDomain.Point → ℝ} {T p0 : ℝ} :
    IntegratedMoserGradientEnergyNonnegativity intervalDomain u T p0 := by
  intro p _hp _hp_nonneg t _ht0 _htT
  exact intervalDomain_integratedMoserGradientEnergy_nonneg
    (u := u) (p := p) (t := t)

/-- For `intervalDomain`, Moser gradient energies have nonnegative interval
integrals over non-reversed time intervals. -/
theorem intervalDomain_integratedMoserGradientEnergy_intervalIntegral_nonneg
    {u : ℝ → intervalDomain.Point → ℝ}
    {p a b : ℝ}
    (hab : a ≤ b) :
    0 ≤ ∫ t in a..b,
      integratedMoserGradientEnergy intervalDomain u p t :=
  integratedMoserGradientEnergy_intervalIntegral_nonneg_of_forall hab
    (fun _ => intervalDomain_integratedMoserGradientEnergy_nonneg)

/-- Interval-domain packaging for the coefficient-form integrated Moser
dissipation theorem.  The hard producer inputs are the full-window higher-power
energy inequality and the full-window integrated relative-Moser inequality; this
wrapper only supplies `p > 0` from the bootstrap hypothesis and `∫ G_p >= 0`
from the concrete interval domain. -/
theorem
    intervalDomain_integratedMoserDissipationDropBeforeCoeff_of_windowEnergy_and_relative
    {params : CM2Params} {T rho p0 theta : ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (henergy :
      ∀ p, p0 ≤ p →
        ∃ A K C0 L eps : ℝ,
          0 < eps ∧ 0 ≤ K ∧ 0 ≤ C0 ∧ 0 ≤ L ∧
          (∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
            integratedMoserEnergy intervalDomain u p t2 -
                integratedMoserEnergy intervalDomain u p t1 +
              A * (∫ s in t1..t2,
                integratedMoserGradientEnergy intervalDomain u p s) ≤
            (C0 * p * (∫ s in t1..t2,
                max 1 (integratedMoserEnergy intervalDomain u p s)) +
              K * (∫ s in t1..t2,
                integratedMoserEnergy intervalDomain u (p + rho) s)) +
              L * (∫ s in t1..t2,
                max 1 (integratedMoserEnergy intervalDomain u p s))) ∧
          K * eps ≤ A - theta)
    (hrelInt :
      ∀ p, p0 ≤ p → ∀ eps, 0 < eps →
        ∃ Ceps, 0 ≤ Ceps ∧
          ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
            ∫ s in t1..t2,
                integratedMoserEnergy intervalDomain u (p + rho) s ≤
              eps * (∫ s in t1..t2,
                integratedMoserGradientEnergy intervalDomain u p s) +
              Ceps * (∫ s in t1..t2,
                max 1 (integratedMoserEnergy intervalDomain u p s))) :
    IntegratedMoserDissipationDropBeforeCoeff
      theta intervalDomain u T rho p0 := by
  have hp_pos : ∀ p, p0 ≤ p → 0 < p := by
    intro p hp
    have hthreshold := AbstractLpBootstrapHypothesis.p0_gt_threshold hboot
    have hone_le :
        (1 : ℝ) ≤ max 1 (rho * (params.N : ℝ) / 2) :=
      le_max_left _ _
    have hp0_pos : 0 < p0 := by linarith
    linarith
  have hG_nonneg :
      ∀ p, p0 ≤ p →
      ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        0 ≤ ∫ s in t1..t2,
          integratedMoserGradientEnergy intervalDomain u p s := by
    intro p _hp t1 _ht1 t2 ht2
    exact intervalDomain_integratedMoserGradientEnergy_intervalIntegral_nonneg
      (u := u) (p := p) ht2.1
  exact
    integratedMoserDissipationDropBeforeCoeff_of_higherPower_and_relative
      hp_pos henergy hrelInt hG_nonneg

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

/-- Full-window higher-power coefficient frontier from the strict-time
`LpBootstrapEnergyInequality`, with all routine window integrability and
nonnegativity inputs supplied by first-crossing regularity.

The remaining non-routine inputs are the window FTC, regularity itself, energy
nonnegativity, and the scalar surplus needed for absorption. -/
theorem higherPowerWindowCoeffFrontier_of_regularEnergy
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 theta : ℝ}
    (henergy : LpBootstrapEnergyInequality D u T rho p0)
    (hFTC : IntegratedMoserEnergyWindowFTC D u T p0)
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hnonneg : IntegratedMoserEnergyNonnegativity D u T p0)
    (hp_pos : ∀ p, p0 ≤ p → 0 < p)
    (hrho_nonneg : 0 ≤ rho)
    (hsurplus :
      ∀ p, p0 ≤ p → ∀ A K, 0 < A → 0 < K →
        ∃ eps, 0 < eps ∧ (p * K) * eps ≤ p * A - theta) :
    IntegratedHigherPowerEnergyWindowCoeffFrontier D u T rho p0 theta := by
  refine
    integratedHigherPowerEnergyWindowCoeffFrontier_of_LpBootstrapEnergyInequality
      henergy hFTC hp_pos ?_ ?_ ?_ ?_ ?_ hsurplus
  · intro p hp t1 ht1 t2 ht2
    have hsub : Set.Icc t1 t2 ⊆ Set.uIcc (0 : ℝ) T :=
      Icc_subset_uIcc_zero_T_of_endpoint_memberships ht1 ht2
    exact hreg.gradient_intervalIntegrable_of_Icc hp ht2.1 hsub
  · intro p hp t1 ht1 t2 ht2
    have hsub : Set.Icc t1 t2 ⊆ Set.uIcc (0 : ℝ) T :=
      Icc_subset_uIcc_zero_T_of_endpoint_memberships ht1 ht2
    exact hreg.power_intervalIntegrable_of_Icc hp ht2.1 hsub
  · intro p hp t1 ht1 t2 ht2
    have hsub : Set.Icc t1 t2 ⊆ Set.uIcc (0 : ℝ) T :=
      Icc_subset_uIcc_zero_T_of_endpoint_memberships ht1 ht2
    have hp_rho : p0 ≤ p + rho := by
      linarith
    exact hreg.power_intervalIntegrable_of_Icc hp_rho ht2.1 hsub
  · intro p hp t1 ht1 t2 ht2
    have hsub : Set.Icc t1 t2 ⊆ Set.uIcc (0 : ℝ) T :=
      Icc_subset_uIcc_zero_T_of_endpoint_memberships ht1 ht2
    exact hreg.maxOneEnergy_intervalIntegrable_of_Icc hp ht2.1 hsub
  · intro p hp t1 ht1 t2 ht2
    have hp_nonneg : 0 ≤ p := (hp_pos p hp).le
    have hY_ae :
        ∀ᵐ s ∂(volume.restrict (Set.Icc t1 t2)),
          0 ≤ integratedMoserEnergy D u p s := by
      filter_upwards
        [ae_restrict_Icc_strictInterior_of_Icc_endpoints ht1 ht2] with s hs
      exact hnonneg p hp hp_nonneg s hs.1 hs.2
    exact intervalIntegral.integral_nonneg_of_ae_restrict ht2.1 hY_ae

/-- Coefficient-gap version of
`higherPowerWindowCoeffFrontier_of_regularEnergy`. -/
theorem higherPowerWindowCoeffFrontier_of_regularEnergy_coeffGap
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 theta : ℝ}
    (henergy : LpBootstrapEnergyInequality D u T rho p0)
    (hFTC : IntegratedMoserEnergyWindowFTC D u T p0)
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hnonneg : IntegratedMoserEnergyNonnegativity D u T p0)
    (hp_pos : ∀ p, p0 ≤ p → 0 < p)
    (hrho_nonneg : 0 ≤ rho)
    (hgap :
      ∀ p, p0 ≤ p → ∀ A K : ℝ, 0 < A → 0 < K → theta < p * A) :
    IntegratedHigherPowerEnergyWindowCoeffFrontier D u T rho p0 theta :=
  higherPowerWindowCoeffFrontier_of_regularEnergy
    henergy hFTC hreg hnonneg hp_pos hrho_nonneg
    (integratedMoser_surplus_of_coeff_gap hgap)

/-- Interval-domain coefficient dissipation from the strict-time bootstrap
energy inequality, window FTC, regularity, nonnegativity, relative interpolation,
and a scalar coefficient gap.

This is pure wiring: it discharges the routine window-integrability inputs and
then invokes the existing absorption theorem. -/
theorem intervalDomain_dissipationCoeff_of_regularEnergy_coeffGap
    {params : CM2Params} {T rho p0 theta : ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0)
    (hFTC : IntegratedMoserEnergyWindowFTC intervalDomain u T p0)
    (hreg : IntegratedMoserFirstCrossingRegularity intervalDomain u T p0)
    (hnonneg : IntegratedMoserEnergyNonnegativity intervalDomain u T p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hgap :
      ∀ p, p0 ≤ p → ∀ A K : ℝ, 0 < A → 0 < K → theta < p * A) :
    IntegratedMoserDissipationDropBeforeCoeff
      theta intervalDomain u T rho p0 := by
  have hp_pos : ∀ p, p0 ≤ p → 0 < p := by
    intro p hp
    have hthreshold := AbstractLpBootstrapHypothesis.p0_gt_threshold hboot
    have hone_le :
        (1 : ℝ) ≤ max 1 (rho * (params.N : ℝ) / 2) :=
      le_max_left _ _
    have hp0_pos : 0 < p0 := by
      linarith
    linarith
  have hrho_pos : 0 < rho := AbstractLpBootstrapHypothesis.rho_pos hboot
  have hwindow :
      IntegratedHigherPowerEnergyWindowCoeffFrontier
        intervalDomain u T rho p0 theta :=
    higherPowerWindowCoeffFrontier_of_regularEnergy_coeffGap
      henergy hFTC hreg hnonneg hp_pos hrho_pos.le hgap
  have hrelInt :
      ∀ p, p0 ≤ p → ∀ eps, 0 < eps →
        ∃ Ceps, 0 ≤ Ceps ∧
          ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
            ∫ s in t1..t2,
                integratedMoserEnergy intervalDomain u (p + rho) s ≤
              eps * (∫ s in t1..t2,
                integratedMoserGradientEnergy intervalDomain u p s) +
              Ceps * (∫ s in t1..t2,
                max 1 (integratedMoserEnergy intervalDomain u p s)) :=
    relativeMoser_hrelInt_closedWindow_of_regular hrel hreg hrho_pos.le
  exact
    intervalDomain_integratedMoserDissipationDropBeforeCoeff_of_windowEnergy_and_relative
      hboot hwindow hrelInt

/-- Fixed-coefficient integrated Moser drop from the regular-energy
coefficient-gap route.

This specializes `intervalDomain_dissipationCoeff_of_regularEnergy_coeffGap`
to `theta = 2`, then converts the coefficient-parametric predicate to the
public `IntegratedMoserDissipationDropBefore` predicate. -/
theorem intervalDomain_integratedMoserDissipationDropBefore_of_regularEnergy_coeffGap
    {params : CM2Params} {T rho p0 : ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0)
    (hFTC : IntegratedMoserEnergyWindowFTC intervalDomain u T p0)
    (hreg : IntegratedMoserFirstCrossingRegularity intervalDomain u T p0)
    (hnonneg : IntegratedMoserEnergyNonnegativity intervalDomain u T p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hgap :
      ∀ p, p0 ≤ p → ∀ A K : ℝ, 0 < A → 0 < K → (2 : ℝ) < p * A) :
    IntegratedMoserDissipationDropBefore intervalDomain u T rho p0 :=
  integratedMoserDissipationDropBefore_of_coeff_two
    (intervalDomain_dissipationCoeff_of_regularEnergy_coeffGap
      (params := params) (T := T) (rho := rho) (p0 := p0)
      (theta := (2 : ℝ)) (u := u)
      hboot henergy hFTC hreg hnonneg hrel hgap)

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

/-- Pure wrapper from the preferred lower-average plus upper-data-aware gap
package to the high-excursion window frontier. -/
def integratedMoserFirstCrossingFromWindowFrontier_of_lowerAverageUpperDataGapData
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (hdata :
      IntegratedMoserFirstCrossingLowerAverageUpperDataGapData
        D u T rho p0) :
    IntegratedMoserFirstCrossingFromWindowFrontier D u T rho p0 :=
  integratedMoserFirstCrossingFromWindowFrontier_of_lowerUpperFrontiers
    hdata.toLowerUpperFrontiers

/-- Compatibility wrapper from the older all-witness epsilon-gap package to
the high-excursion window frontier. -/
def integratedMoserFirstCrossingFromWindowFrontier_of_lowerAverageEpsilonData
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (hdata :
      IntegratedMoserFirstCrossingLowerAverageEpsilonData
        D u T rho p0) :
    IntegratedMoserFirstCrossingFromWindowFrontier D u T rho p0 :=
  integratedMoserFirstCrossingFromWindowFrontier_of_lowerAverageUpperDataGapData
    hdata.toUpperDataGapData

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
  integratedMoserFirstCrossingStep_of_windowFrontier
    (integratedMoserFirstCrossingFromWindowFrontier_of_lowerAverageUpperDataGapData
      hdata)

/-- Direct compatibility consumer for the older all-witness epsilon-gap
package. -/
theorem integratedMoserFirstCrossingStep_of_lowerAverageEpsilonData
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (hdata :
      IntegratedMoserFirstCrossingLowerAverageEpsilonData
        D u T rho p0) :
    IntegratedMoserFirstCrossingStep D u T rho p0 :=
  integratedMoserFirstCrossingStep_of_windowFrontier
    (integratedMoserFirstCrossingFromWindowFrontier_of_lowerAverageEpsilonData
      hdata)

#print axioms intervalIntegrable_of_integrableOn_uIcc_of_Icc_subset
#print axioms Icc_subset_uIcc_zero_T_of_endpoint_memberships
#print axioms ae_restrict_Icc_strictInterior_of_Icc_endpoints
#print axioms IntegratedMoserFirstCrossingRegularity.power_intervalIntegrable_of_Icc
#print axioms IntegratedMoserFirstCrossingRegularity.gradient_intervalIntegrable_of_Icc
#print axioms intervalIntegrable_max_one_of_intervalIntegrable
#print axioms intervalIntegral_length_le_integral_max_one
#print axioms exists_pos_eps_mul_le_sub_of_coeff_gap
#print axioms integratedMoser_surplus_of_coeff_gap
#print axioms integratedHigherPowerEnergyWindowCoeff_of_pointwise_witness
#print axioms
  integratedHigherPowerEnergyWindowCoeffFrontier_of_LpBootstrapEnergyInequality
#print axioms
  integratedHigherPowerEnergyWindowCoeffFrontier_of_LpBootstrapEnergyInequality_coeffGap
#print axioms relativeMoser_higherPower_timeIntegral_le_of_Icc_currentEnergy_maxOne_const
#print axioms relativeMoser_higherPower_timeIntegral_le_of_Icc_currentEnergy_maxOne
#print axioms relativeMoser_hrelInt_strictInterior
#print axioms IntegratedMoserFirstCrossingRegularity.maxOneEnergy_intervalIntegrable_of_Icc
#print axioms relativeMoser_hrelInt_closedWindow_of_regular
#print axioms intervalDomain_integral_nonneg
#print axioms intervalDomain_integratedMoserEnergy_nonneg_of_pointwise_nonneg
#print axioms intervalDomain_integratedMoserEnergyNonnegativity_of_pointwise_nonneg
#print axioms intervalDomain_integratedMoserEnergyNonnegativity_of_classical
#print axioms intervalDomain_integratedMoserEnergyNonnegativity_of_global_classical
#print axioms higherPowerWindowCoeffFrontier_of_regularEnergy
#print axioms higherPowerWindowCoeffFrontier_of_regularEnergy_coeffGap
#print axioms intervalDomain_dissipationCoeff_of_regularEnergy_coeffGap
#print axioms
  intervalDomain_integratedMoserDissipationDropBefore_of_regularEnergy_coeffGap
#print axioms integratedMoserGradientEnergy_intervalIntegral_nonneg_of_forall
#print axioms integratedMoserGradientEnergy_intervalIntegral_nonneg_of_nonneg_on
#print axioms integratedMoserGradientEnergy_intervalIntegral_nonneg_of_package
#print axioms intervalDomain_integratedMoserGradientEnergy_nonneg
#print axioms intervalDomain_integratedMoserGradientEnergyNonnegativity
#print axioms intervalDomain_integratedMoserGradientEnergy_intervalIntegral_nonneg
#print axioms
  intervalDomain_integratedMoserDissipationDropBeforeCoeff_of_windowEnergy_and_relative
#print axioms scalar_absorb_higherPower_window_const
#print axioms scalar_absorb_higherPower_window
#print axioms
  integratedMoserDissipationDropBeforeCoeff_of_higherPower_and_relative
#print axioms
  integratedMoserDissipationDropBeforeCoeff_of_higherPowerFrontier_and_relative
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
#print axioms
  integratedMoserFirstCrossingFromWindowFrontier_of_lowerAverageUpperDataGapData
#print axioms
  integratedMoserFirstCrossingFromWindowFrontier_of_lowerAverageEpsilonData
#print axioms integratedMoserFirstCrossingStep_of_windowFrontier
#print axioms integratedMoserFirstCrossingStep_of_lowerUpperFrontiers
#print axioms integratedMoserFirstCrossingStep_of_lowerAverageUpperDataGapData
#print axioms integratedMoserFirstCrossingStep_of_lowerAverageEpsilonData
#print axioms LpPowerBoundedBefore_congr_pos
#print axioms LpPowerBoundedBefore_iff_of_pos_eq
#print axioms AbstractLpBootstrapHypothesis_congr_pos
#print axioms IntegratedMoserFirstCrossingStep_congr_pos
#print axioms IntegratedMoserFirstCrossingStep_iff_of_pos_eq

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

/-- A high-excursion window frontier directly generates the arithmetic Moser
ladder. -/
theorem moser_iteration_chain_of_windowFrontier
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T p0 rho : ℝ}
    (hrho : 0 < rho)
    (hbase : LpPowerBoundedBefore D p0 T u)
    (hfront : IntegratedMoserFirstCrossingFromWindowFrontier D u T rho p0) :
    ∀ n : ℕ, LpPowerBoundedBefore D (p0 + n * rho) T u :=
  moser_iteration_chain_of_integrated_first_crossing_step hrho hbase
    (integratedMoserFirstCrossingStep_of_windowFrontier hfront)

/-- Split lower/upper frontiers directly generate the arithmetic Moser
ladder. -/
theorem moser_iteration_chain_of_lowerUpperFrontiers
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T p0 rho : ℝ}
    (hrho : 0 < rho)
    (hbase : LpPowerBoundedBefore D p0 T u)
    (hfront :
      IntegratedMoserFirstCrossingLowerUpperFrontiers D u T rho p0) :
    ∀ n : ℕ, LpPowerBoundedBefore D (p0 + n * rho) T u :=
  moser_iteration_chain_of_integrated_first_crossing_step hrho hbase
    (integratedMoserFirstCrossingStep_of_lowerUpperFrontiers hfront)

/-- Preferred lower-average plus upper-data-gap data directly generates the
arithmetic Moser ladder. -/
theorem moser_iteration_chain_of_lowerAverageUpperDataGapData
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T p0 rho : ℝ}
    (hrho : 0 < rho)
    (hbase : LpPowerBoundedBefore D p0 T u)
    (hdata :
      IntegratedMoserFirstCrossingLowerAverageUpperDataGapData
        D u T rho p0) :
    ∀ n : ℕ, LpPowerBoundedBefore D (p0 + n * rho) T u :=
  moser_iteration_chain_of_integrated_first_crossing_step hrho hbase
    (integratedMoserFirstCrossingStep_of_lowerAverageUpperDataGapData hdata)

/-- Legacy lower-average plus all-witness epsilon-gap data directly generates
the arithmetic Moser ladder. -/
theorem moser_iteration_chain_of_lowerAverageEpsilonData
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T p0 rho : ℝ}
    (hrho : 0 < rho)
    (hbase : LpPowerBoundedBefore D p0 T u)
    (hdata :
      IntegratedMoserFirstCrossingLowerAverageEpsilonData D u T rho p0) :
    ∀ n : ℕ, LpPowerBoundedBefore D (p0 + n * rho) T u :=
  moser_iteration_chain_of_integrated_first_crossing_step hrho hbase
    (integratedMoserFirstCrossingStep_of_lowerAverageEpsilonData hdata)

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

/-- A supplied high-excursion window frontier plus downward Lp monotonicity
gives all finite exponents. -/
theorem all_exponents_of_windowFrontier_lpmono
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {N T rho p0 : ℝ}
    (hboot : AbstractLpBootstrapHypothesis D u N T rho p0)
    (hfront : IntegratedMoserFirstCrossingFromWindowFrontier D u T rho p0)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore D q T u → LpPowerBoundedBefore D p T u) :
    ∀ pExp > 1, LpPowerBoundedBefore D pExp T u :=
  all_exponents_of_integrated_first_crossing_step_lpmono hboot
    (integratedMoserFirstCrossingStep_of_windowFrontier hfront) hLpMono

/-- Split lower/upper frontiers plus downward Lp monotonicity give all finite
exponents. -/
theorem all_exponents_of_lowerUpperFrontiers_lpmono
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {N T rho p0 : ℝ}
    (hboot : AbstractLpBootstrapHypothesis D u N T rho p0)
    (hfront :
      IntegratedMoserFirstCrossingLowerUpperFrontiers D u T rho p0)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore D q T u → LpPowerBoundedBefore D p T u) :
    ∀ pExp > 1, LpPowerBoundedBefore D pExp T u :=
  all_exponents_of_integrated_first_crossing_step_lpmono hboot
    (integratedMoserFirstCrossingStep_of_lowerUpperFrontiers hfront) hLpMono

/-- Preferred lower-average plus upper-data-gap data, together with downward
Lp monotonicity, gives all finite exponents. -/
theorem all_exponents_of_lowerAverageUpperDataGapData_lpmono
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {N T rho p0 : ℝ}
    (hboot : AbstractLpBootstrapHypothesis D u N T rho p0)
    (hdata :
      IntegratedMoserFirstCrossingLowerAverageUpperDataGapData
        D u T rho p0)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore D q T u → LpPowerBoundedBefore D p T u) :
    ∀ pExp > 1, LpPowerBoundedBefore D pExp T u :=
  all_exponents_of_integrated_first_crossing_step_lpmono hboot
    (integratedMoserFirstCrossingStep_of_lowerAverageUpperDataGapData hdata)
    hLpMono

/-- Legacy lower-average plus all-witness epsilon-gap data, together with
downward Lp monotonicity, gives all finite exponents. -/
theorem all_exponents_of_lowerAverageEpsilonData_lpmono
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {N T rho p0 : ℝ}
    (hboot : AbstractLpBootstrapHypothesis D u N T rho p0)
    (hdata :
      IntegratedMoserFirstCrossingLowerAverageEpsilonData D u T rho p0)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore D q T u → LpPowerBoundedBefore D p T u) :
    ∀ pExp > 1, LpPowerBoundedBefore D pExp T u :=
  all_exponents_of_integrated_first_crossing_step_lpmono hboot
    (integratedMoserFirstCrossingStep_of_lowerAverageEpsilonData hdata)
    hLpMono

/-- Interval-domain finite-horizon boundedness directly from a high-excursion
window frontier. -/
theorem intervalDomain_boundedBefore_of_windowFrontier
    {u : ℝ → intervalDomain.Point → ℝ} {N T rho p0 : ℝ}
    {pSeq rootBound : ℕ → ℝ}
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u N T rho p0)
    (hfront :
      IntegratedMoserFirstCrossingFromWindowFrontier
        intervalDomain u T rho p0)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore intervalDomain q T u →
        LpPowerBoundedBefore intervalDomain p T u)
    (hEndpoint :
      (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
        IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound) :
    IsPaper2BoundedBefore intervalDomain T u :=
  intervalDomain_boundedBefore_of_integrated_first_crossing_step hboot
    (integratedMoserFirstCrossingStep_of_windowFrontier hfront)
    hLpMono hEndpoint

/-- Interval-domain finite-horizon boundedness directly from split lower/upper
frontiers. -/
theorem intervalDomain_boundedBefore_of_lowerUpperFrontiers
    {u : ℝ → intervalDomain.Point → ℝ} {N T rho p0 : ℝ}
    {pSeq rootBound : ℕ → ℝ}
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u N T rho p0)
    (hfront :
      IntegratedMoserFirstCrossingLowerUpperFrontiers
        intervalDomain u T rho p0)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore intervalDomain q T u →
        LpPowerBoundedBefore intervalDomain p T u)
    (hEndpoint :
      (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
        IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound) :
    IsPaper2BoundedBefore intervalDomain T u :=
  intervalDomain_boundedBefore_of_integrated_first_crossing_step hboot
    (integratedMoserFirstCrossingStep_of_lowerUpperFrontiers hfront)
    hLpMono hEndpoint

/-- Interval-domain finite-horizon boundedness directly from the preferred
lower-average plus upper-data-gap package. -/
theorem intervalDomain_boundedBefore_of_lowerAverageUpperDataGapData
    {u : ℝ → intervalDomain.Point → ℝ} {N T rho p0 : ℝ}
    {pSeq rootBound : ℕ → ℝ}
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u N T rho p0)
    (hdata :
      IntegratedMoserFirstCrossingLowerAverageUpperDataGapData
        intervalDomain u T rho p0)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore intervalDomain q T u →
        LpPowerBoundedBefore intervalDomain p T u)
    (hEndpoint :
      (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
        IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound) :
    IsPaper2BoundedBefore intervalDomain T u :=
  intervalDomain_boundedBefore_of_integrated_first_crossing_step hboot
    (integratedMoserFirstCrossingStep_of_lowerAverageUpperDataGapData hdata)
    hLpMono hEndpoint

/-- Interval-domain finite-horizon boundedness directly from the legacy
lower-average plus all-witness epsilon-gap package. -/
theorem intervalDomain_boundedBefore_of_lowerAverageEpsilonData
    {u : ℝ → intervalDomain.Point → ℝ} {N T rho p0 : ℝ}
    {pSeq rootBound : ℕ → ℝ}
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u N T rho p0)
    (hdata :
      IntegratedMoserFirstCrossingLowerAverageEpsilonData
        intervalDomain u T rho p0)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore intervalDomain q T u →
        LpPowerBoundedBefore intervalDomain p T u)
    (hEndpoint :
      (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
        IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound) :
    IsPaper2BoundedBefore intervalDomain T u :=
  intervalDomain_boundedBefore_of_integrated_first_crossing_step hboot
    (integratedMoserFirstCrossingStep_of_lowerAverageEpsilonData hdata)
    hLpMono hEndpoint

#print axioms moser_iteration_chain_of_integrated_first_crossing_step
#print axioms moser_iteration_chain_of_windowFrontier
#print axioms moser_iteration_chain_of_lowerUpperFrontiers
#print axioms moser_iteration_chain_of_lowerAverageUpperDataGapData
#print axioms moser_iteration_chain_of_lowerAverageEpsilonData
#print axioms all_exponents_of_integrated_first_crossing_step_lpmono
#print axioms intervalDomain_boundedBefore_of_integrated_first_crossing_step
#print axioms all_exponents_of_windowFrontier_lpmono
#print axioms all_exponents_of_lowerUpperFrontiers_lpmono
#print axioms all_exponents_of_lowerAverageUpperDataGapData_lpmono
#print axioms all_exponents_of_lowerAverageEpsilonData_lpmono
#print axioms intervalDomain_boundedBefore_of_windowFrontier
#print axioms intervalDomain_boundedBefore_of_lowerUpperFrontiers
#print axioms intervalDomain_boundedBefore_of_lowerAverageUpperDataGapData
#print axioms intervalDomain_boundedBefore_of_lowerAverageEpsilonData

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

end
