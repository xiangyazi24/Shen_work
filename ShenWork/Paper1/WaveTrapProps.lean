/-
  Trap-property lemmas for the monotone wave trap set.

  These discharge the `mk_auto_limits` hypotheses for the B1 traveling-wave
  existence assembly that are pure trap-membership facts (independent of the
  Schauder fixed-point construction):

  * uniform boundedness of a trap profile, and
  * the right limit U → 0 at +∞.

  Both follow directly from `InMonotoneWaveTrapSet κ M U` membership.
  (Strict positivity 0 < U is NOT a trap-membership fact — see the module
  comment at the end.)
-/
import ShenWork.Paper1.Statements
import ShenWork.Paper1.WaveRotheStep
import ShenWork.Paper1.WaveRotheStationary
import ShenWork.PDE.TravelingWaveODE

open Filter Topology Set MeasureTheory

namespace ShenWork.Paper1

open ShenWork.PDE.TravelingWaveODE

/-- A monotone-wave-trap profile is `C`-uniformly bounded.

`InMonotoneWaveTrapSet κ M U` packages `InWaveTrapSet κ M U`, whose first
component is exactly `IsCUnifBdd U`, so this is immediate from the trap. -/
theorem inMonotoneWaveTrapSet_isCUnifBdd
    (_p : CMParams) (κ M : ℝ) (U : ℝ → ℝ)
    (hU : InMonotoneWaveTrapSet κ M U) :
    IsCUnifBdd U :=
  hU.trap.cunif_bdd

/-- A monotone-wave-trap profile tends to `0` at `+∞`.

By the squeeze `0 ≤ U x ≤ upperBarrier κ M x ≤ exp (-κ x)` with
`exp (-κ x) → 0` (using `0 < κ`). The positivity of `κ` is a genuine side
condition of the upper-barrier decay, not derivable from trap membership
alone; the existence-assembly callsites supply it. -/
theorem inMonotoneWaveTrapSet_tendsto_atTop_zero
    (_p : CMParams) (κ M : ℝ) (U : ℝ → ℝ)
    (hκ : 0 < κ) (hU : InMonotoneWaveTrapSet κ M U) :
    Filter.Tendsto U Filter.atTop (nhds 0) :=
  hU.trap.tendsto_atTop_zero hκ

/-- Exact universal `hbdd` profile obligation discharged from trap membership. -/
theorem monotoneTrap_profile_hbdd {κ M : ℝ} :
    ∀ U : ℝ → ℝ, InMonotoneWaveTrapSet κ M U → IsCUnifBdd U :=
  fun _U hU => hU.trap.cunif_bdd

/-- Exact universal `hlim_pos` profile obligation discharged from the trap
upper barrier, assuming the exponential rate is strictly positive. -/
theorem monotoneTrap_profile_hlim_pos {κ M : ℝ} (hκ : 0 < κ) :
    ∀ U : ℝ → ℝ,
      InMonotoneWaveTrapSet κ M U → Tendsto U atTop (𝓝 0) :=
  fun _U hU => hU.tendsto_atTop_zero hκ

/-- A paper-positive datum is strictly positive at every point, by its uniform
floor. -/
theorem PaperPositiveInitialDatum.pos {U : ℝ → ℝ}
    (hfloor : PaperPositiveInitialDatum U) :
    ∀ x, 0 < U x :=
  hfloor.floor.pos

/-- Non-triviality of a nonnegative wave profile: positive somewhere.

This is the non-vacuous pin needed before applying the strong maximum
principle.  The zero profile does not satisfy it, while a positive decaying
traveling wave does. -/
def ProfileNontrivial (U : ℝ → ℝ) : Prop :=
  ∃ x : ℝ, 0 < U x

theorem not_profileNontrivial_zero :
    ¬ ProfileNontrivial (fun _ : ℝ => (0 : ℝ)) := by
  rintro ⟨x, hx⟩
  exact (lt_irrefl (0 : ℝ)) hx

/-- The zero profile is a stationary solution of the frozen wave operator. -/
theorem frozenWaveOperator_zero_eq_zero (p : CMParams) (c x : ℝ) :
    frozenWaveOperator p c (fun _ : ℝ => (0 : ℝ))
      (fun _ : ℝ => (0 : ℝ)) x = 0 := by
  unfold frozenWaveOperator
  have hm_ne : p.m ≠ 0 := by linarith [p.hm]
  have hα_ne : p.α ≠ 0 := by linarith [p.hα]
  simp [Real.zero_rpow hm_ne, Real.zero_rpow hα_ne]

/-- A stationary strong-maximum-principle frontier for trapped profiles.

It is intentionally conditional on `ProfileNontrivial U`; hence the zero
stationary solution is excluded by a satisfiable hypothesis, not by a uniform
floor on the whole trap. -/
def StationaryStrongMaxPrinciple
    (p : CMParams) (c κ M : ℝ) : Prop :=
  ∀ U : ℝ → ℝ,
    InMonotoneWaveTrapSet κ M U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        ProfileNontrivial U →
          ∀ x, 0 < U x

/-- The two-dimensional Cauchy jet `(U,U')` used for the direct
strong-maximum-principle route. -/
abbrev StationaryJet : Type := Fin 2 → ℝ

noncomputable def stationaryJet (U : ℝ → ℝ) (x : ℝ) : StationaryJet :=
  ![U x, deriv U x]

noncomputable def stationaryJetDeriv (U : ℝ → ℝ) (x : ℝ) : StationaryJet :=
  ![deriv U x, deriv (deriv U) x]

private theorem stationaryJet_hasDerivWithinAt
    {U : ℝ → ℝ} (hU_diff : Differentiable ℝ U)
    (hUd_diff : Differentiable ℝ (deriv U)) (x : ℝ) :
    HasDerivWithinAt (stationaryJet U) (stationaryJetDeriv U x) (Ici x) x := by
  rw [hasDerivWithinAt_pi]
  intro i
  fin_cases i
  · simpa [stationaryJet, stationaryJetDeriv] using
      (hU_diff x).hasDerivAt.hasDerivWithinAt
  · simpa [stationaryJet, stationaryJetDeriv] using
      (hUd_diff x).hasDerivAt.hasDerivWithinAt

private theorem stationaryJet_continuous
    {U : ℝ → ℝ} (hU_diff : Differentiable ℝ U)
    (hUd_diff : Differentiable ℝ (deriv U)) :
    Continuous (stationaryJet U) := by
  refine continuous_pi ?_
  intro i
  fin_cases i
  · simpa [stationaryJet] using hU_diff.continuous
  · simpa [stationaryJet] using hUd_diff.continuous

/-- Grönwall zero-Cauchy uniqueness for a second-order scalar profile written
as the first-order jet `(U,U')`.

This is the direct linear-ODE uniqueness step used below.  The hypothesis
`hbound` is exactly the bounded-coefficient estimate
`‖(U',U'')‖ ≤ K ‖(U,U')‖` on the compact interval. -/
theorem stationaryJet_zero_of_gronwall_right
    {U : ℝ → ℝ} {a b K : ℝ}
    (_hab : a ≤ b)
    (hU_diff : Differentiable ℝ U)
    (hUd_diff : Differentiable ℝ (deriv U))
    (hbound : ∀ x ∈ Ico a b,
      ‖stationaryJetDeriv U x‖ ≤ K * ‖stationaryJet U x‖)
    (hUa : U a = 0) (hDa : deriv U a = 0) :
    ∀ x ∈ Icc a b, U x = 0 ∧ deriv U x = 0 := by
  have hjet0 : stationaryJet U a = 0 := by
    ext i
    fin_cases i <;> simp [stationaryJet, hUa, hDa]
  have hzero :
      ∀ x ∈ Icc a b, stationaryJet U x = 0 :=
    eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      (f := stationaryJet U) (f' := stationaryJetDeriv U)
      (K := K) (a := a) (b := b)
      (stationaryJet_continuous hU_diff hUd_diff).continuousOn
      (fun x _hx => stationaryJet_hasDerivWithinAt hU_diff hUd_diff x)
      hjet0 hbound
  intro x hx
  have hxzero := hzero x hx
  constructor
  · have hcomp := congrFun hxzero 0
    simpa [stationaryJet] using hcomp
  · have hcomp := congrFun hxzero 1
    simpa [stationaryJet] using hcomp

/-- Direct real-exponent linearization data for the stationary strong maximum
principle.

For a stationary trapped profile, the frozen equation is used only through the
bounded linear Cauchy-jet estimate on every compact interval, together with the
same estimate after reflection for the left side.  This is the formal
strong-max-principle input for real `m, α, γ ≥ 1`; it does not pass through the
integer-exponent traveling-wave ODE. -/
def StationaryLinearGronwallData
    (p : CMParams) (c κ M : ℝ) : Prop :=
  ∀ U : ℝ → ℝ,
    InMonotoneWaveTrapSet κ M U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        Differentiable ℝ U ∧
        Differentiable ℝ (deriv U) ∧
        ∀ x₀, U x₀ = 0 → deriv U x₀ = 0 →
          (∀ y, x₀ ≤ y →
            ∃ K : ℝ, ∀ x ∈ Ico x₀ y,
              ‖stationaryJetDeriv U x‖ ≤ K * ‖stationaryJet U x‖) ∧
          (∀ y, y ≤ x₀ →
            ∃ K : ℝ, ∀ x ∈ Ico (-x₀) (-y),
              ‖stationaryJetDeriv (fun t => U (-t)) x‖ ≤
                K * ‖stationaryJet (fun t => U (-t)) x‖)

/-- Profile-wise version of the linear Grönwall payload. -/
def StationaryLinearGronwallProfileData (U : ℝ → ℝ) : Prop :=
  ∀ x₀, U x₀ = 0 → deriv U x₀ = 0 →
    (∀ y, x₀ ≤ y →
      ∃ K : ℝ, ∀ x ∈ Ico x₀ y,
        ‖stationaryJetDeriv U x‖ ≤ K * ‖stationaryJet U x‖) ∧
    (∀ y, y ≤ x₀ →
      ∃ K : ℝ, ∀ x ∈ Ico (-x₀) (-y),
        ‖stationaryJetDeriv (fun t => U (-t)) x‖ ≤
          K * ‖stationaryJet (fun t => U (-t)) x‖)

/-- The strong maximum principle for one profile once its regularity and
linear Grönwall data are available. -/
theorem stationaryProfile_strictlyPositive_of_linearGronwall
    {U : ℝ → ℝ}
    (hU_nonneg : ∀ x, 0 ≤ U x)
    (hU_diff : Differentiable ℝ U)
    (hUd_diff : Differentiable ℝ (deriv U))
    (hlin : StationaryLinearGronwallProfileData U)
    (hnontriv : ProfileNontrivial U) :
    ∀ x, 0 < U x := by
  intro x₀
  by_contra hnot
  have hx₀_zero : U x₀ = 0 :=
    le_antisymm (not_lt.mp hnot) (hU_nonneg x₀)
  have hmin : IsLocalMin U x₀ := by
    dsimp [IsLocalMin, IsMinFilter]
    exact Eventually.of_forall fun x => by
      simpa [hx₀_zero] using hU_nonneg x
  have hx₀_deriv : deriv U x₀ = 0 :=
    hmin.hasDerivAt_eq_zero (hU_diff x₀).hasDerivAt
  rcases hlin x₀ hx₀_zero hx₀_deriv with ⟨hright, hleft⟩
  have hzero_all : ∀ y, U y = 0 := by
    intro y
    by_cases hxy : x₀ ≤ y
    · rcases hright y hxy with ⟨K, hK⟩
      exact (stationaryJet_zero_of_gronwall_right hxy
        hU_diff hUd_diff hK hx₀_zero hx₀_deriv y ⟨hxy, le_rfl⟩).1
    · have hyx : y ≤ x₀ := le_of_not_ge hxy
      rcases hleft y hyx with ⟨K, hK⟩
      let Urev : ℝ → ℝ := fun t => U (-t)
      have hneg_diff : Differentiable ℝ (fun t : ℝ => -t) :=
        differentiable_id.neg
      have hUrev_diff : Differentiable ℝ Urev := by
        intro t
        exact (hU_diff (-t)).comp t (hneg_diff t)
      have hUrev_deriv_eq :
          deriv Urev = fun t => -deriv U (-t) := by
        funext t
        simpa [Urev] using deriv_comp_neg (f := U) (x := t)
      have hUrev_deriv_diff : Differentiable ℝ (deriv Urev) := by
        rw [hUrev_deriv_eq]
        intro t
        exact ((hUd_diff (-t)).comp t (hneg_diff t)).neg
      have hrev0 : Urev (-x₀) = 0 := by
        simp [Urev, hx₀_zero]
      have hrevD : deriv Urev (-x₀) = 0 := by
        rw [hUrev_deriv_eq]
        simp [hx₀_deriv]
      have hle_rev : -x₀ ≤ -y := neg_le_neg hyx
      have hrez := stationaryJet_zero_of_gronwall_right hle_rev
        hUrev_diff hUrev_deriv_diff hK hrev0 hrevD (-y)
        ⟨hle_rev, le_rfl⟩
      simpa [Urev] using hrez.1
  have hUzero : U = fun _ : ℝ => (0 : ℝ) := funext hzero_all
  exact not_profileNontrivial_zero (by simpa [hUzero] using hnontriv)

/-- The direct strong-maximum-principle theorem from the real-exponent
linear-ODE structure.  If a nonnegative trapped stationary profile touches zero,
then the interior minimum gives `U'=0`; the Grönwall zero-Cauchy uniqueness
propagates the zero profile to both sides, contradicting nontriviality. -/
theorem stationaryStrongMaxPrinciple_of_linearGronwall
    {p : CMParams} {c κ M : ℝ}
    (hlin : StationaryLinearGronwallData p c κ M) :
    StationaryStrongMaxPrinciple p c κ M := by
  intro U hU hstat hnontriv
  rcases hlin U hU hstat with
    ⟨hU_diff, hUd_diff, hzeroCauchy⟩
  exact stationaryProfile_strictlyPositive_of_linearGronwall
    hU.nonneg hU_diff hUd_diff hzeroCauchy hnontriv

private theorem rpow_le_mul_rpow_sub_one_of_mem_band
    {u M a : ℝ} (ha : 1 ≤ a)
    (hu0 : 0 ≤ u) (huM : u ≤ M) :
    u ^ a ≤ M ^ (a - 1) * u := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  by_cases hu : u = 0
  · subst u
    have hane : a ≠ 0 := ne_of_gt ha0
    simp [Real.zero_rpow hane]
  · have hupos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
    have hpow : u ^ a = u ^ (a - 1) * u := by
      calc
        u ^ a = u ^ ((a - 1) + 1) := by ring_nf
        _ = u ^ (a - 1) * u ^ (1 : ℝ) := by
          rw [Real.rpow_add hupos]
        _ = u ^ (a - 1) * u := by rw [Real.rpow_one]
    have hm1 : 0 ≤ a - 1 := by linarith
    have hle : u ^ (a - 1) ≤ M ^ (a - 1) :=
      Real.rpow_le_rpow hupos.le huM hm1
    rw [hpow]
    exact mul_le_mul_of_nonneg_right hle hupos.le

private theorem stationary_flux_deriv_eq
    {p : CMParams} {κ M : ℝ} {U : ℝ → ℝ}
    (hU : InMonotoneWaveTrapSet κ M U)
    (hU_diff : Differentiable ℝ U) (x : ℝ) :
    deriv (fun y => (U y) ^ p.m * deriv (frozenElliptic p U) y) x =
      deriv U x * p.m * (U x) ^ (p.m - 1) *
          deriv (frozenElliptic p U) x +
        (U x) ^ p.m * (frozenElliptic p U x - (U x) ^ p.γ) := by
  have hU_pow_deriv : HasDerivAt (fun y => (U y) ^ p.m)
      (deriv U x * p.m * (U x) ^ (p.m - 1)) x :=
    (hU_diff x).hasDerivAt.rpow_const (Or.inr p.hm)
  have hV'' := frozenElliptic_deriv_deriv_eq p
    hU.trap.cunif_bdd hU.nonneg x
  have hV_deriv : HasDerivAt (deriv (frozenElliptic p U))
      (frozenElliptic p U x - (U x) ^ p.γ) x := by
    convert (frozenElliptic_deriv_differentiableAt p
      hU.trap.cunif_bdd hU.nonneg x).hasDerivAt using 1
    exact hV''.symm
  have hprod := hU_pow_deriv.mul hV_deriv
  have hfun_eq :
      (fun y => (U y) ^ p.m * deriv (frozenElliptic p U) y) =
        (fun y => (U y) ^ p.m) * deriv (frozenElliptic p U) := by
    ext y
    simp [Pi.mul_apply]
  rw [hfun_eq, hprod.deriv]

private theorem frozenElliptic_deriv_continuous_of_trap
    {p : CMParams} {κ M : ℝ} {U : ℝ → ℝ}
    (hU : InMonotoneWaveTrapSet κ M U) :
    Continuous (deriv (frozenElliptic p U)) := by
  refine continuous_iff_continuousAt.mpr ?_
  intro x
  exact (frozenElliptic_deriv_differentiableAt p
    hU.trap.cunif_bdd hU.nonneg x).continuousAt

private theorem stationary_second_deriv_eq_of_trap
    {p : CMParams} {c κ M : ℝ} {U : ℝ → ℝ}
    (hU : InMonotoneWaveTrapSet κ M U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hU_diff : Differentiable ℝ U) (x : ℝ) :
    deriv (deriv U) x =
      -c * deriv U x +
        p.χ *
          (deriv U x * p.m * (U x) ^ (p.m - 1) *
              deriv (frozenElliptic p U) x +
            (U x) ^ p.m * (frozenElliptic p U x - (U x) ^ p.γ)) -
        U x * (1 - (U x) ^ p.α) := by
  have hflux_eq := stationary_flux_deriv_eq (p := p) hU hU_diff x
  have hstatx := hstat x
  unfold frozenWaveOperator at hstatx
  have hiter : iteratedDeriv 2 U x = deriv (deriv U) x := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [hiter, hflux_eq] at hstatx
  linarith

private theorem stationary_second_deriv_rhs_continuous_of_trap
    {p : CMParams} {c κ M : ℝ} {U : ℝ → ℝ}
    (hU : InMonotoneWaveTrapSet κ M U)
    (hderivU_cont : Continuous (deriv U)) :
    Continuous
      (fun x =>
        -c * deriv U x +
          p.χ *
            (deriv U x * p.m * (U x) ^ (p.m - 1) *
                deriv (frozenElliptic p U) x +
              (U x) ^ p.m * (frozenElliptic p U x - (U x) ^ p.γ)) -
          U x * (1 - (U x) ^ p.α)) := by
  have hU_cont : Continuous U := hU.trap.cunif_bdd.1
  have hV_cont : Continuous (frozenElliptic p U) :=
    frozenElliptic_continuous p hU.trap.cunif_bdd hU.nonneg
  have hVd_cont : Continuous (deriv (frozenElliptic p U)) :=
    frozenElliptic_deriv_continuous_of_trap hU
  have hm0 : 0 ≤ p.m := le_trans zero_le_one p.hm
  have hm1 : 0 ≤ p.m - 1 := by linarith [p.hm]
  have hα0 : 0 ≤ p.α := le_trans zero_le_one p.hα
  have hγ0 : 0 ≤ p.γ := le_trans zero_le_one p.hγ
  have hUm_cont : Continuous (fun x => (U x) ^ p.m) :=
    hU_cont.rpow_const (fun _ => Or.inr hm0)
  have hUm1_cont : Continuous (fun x => (U x) ^ (p.m - 1)) :=
    hU_cont.rpow_const (fun _ => Or.inr hm1)
  have hUα_cont : Continuous (fun x => (U x) ^ p.α) :=
    hU_cont.rpow_const (fun _ => Or.inr hα0)
  have hUγ_cont : Continuous (fun x => (U x) ^ p.γ) :=
    hU_cont.rpow_const (fun _ => Or.inr hγ0)
  have hterm1 :
      Continuous
        (fun x =>
          deriv U x * p.m * (U x) ^ (p.m - 1) *
            deriv (frozenElliptic p U) x) :=
    ((hderivU_cont.mul continuous_const).mul hUm1_cont).mul hVd_cont
  have hterm2 :
      Continuous
        (fun x =>
          (U x) ^ p.m * (frozenElliptic p U x - (U x) ^ p.γ)) :=
    hUm_cont.mul (hV_cont.sub hUγ_cont)
  have hreaction :
      Continuous (fun x => U x * (1 - (U x) ^ p.α)) :=
    hU_cont.mul (continuous_const.sub hUα_cont)
  exact ((continuous_const.mul hderivU_cont).add
    (continuous_const.mul (hterm1.add hterm2))).sub hreaction

private theorem stationary_second_deriv_abs_le_of_trap
    {p : CMParams} {c κ M : ℝ} {U : ℝ → ℝ}
    (hM : 0 < M)
    (hU : InMonotoneWaveTrapSet κ M U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hU_diff : Differentiable ℝ U) :
    ∀ x,
      |deriv (deriv U) x| ≤
        (|c| + |p.χ| * |p.m| * M ^ (p.m - 1) * M ^ p.γ) *
            |deriv U x| +
          (|p.χ| * M ^ (p.m - 1) * (M ^ p.γ + M ^ p.γ) +
              (1 + M ^ p.α)) *
            |U x| := by
  intro x
  have hM0 : 0 ≤ M := hM.le
  have hUx0 : 0 ≤ U x := hU.nonneg x
  have hUxM : U x ≤ M := hU.le_M x
  have hm0 : 0 ≤ p.m := le_trans zero_le_one p.hm
  have hm1 : 0 ≤ p.m - 1 := by linarith [p.hm]
  have hα0 : 0 ≤ p.α := le_trans zero_le_one p.hα
  have hγ0 : 0 ≤ p.γ := le_trans zero_le_one p.hγ
  have hMm1_nonneg : 0 ≤ M ^ (p.m - 1) := Real.rpow_nonneg hM0 _
  have hMγ_nonneg : 0 ≤ M ^ p.γ := Real.rpow_nonneg hM0 _
  have hMα_nonneg : 0 ≤ M ^ p.α := Real.rpow_nonneg hM0 _
  have hUm1_abs : |(U x) ^ (p.m - 1)| ≤ M ^ (p.m - 1) := by
    rw [abs_of_nonneg (Real.rpow_nonneg hUx0 _)]
    exact Real.rpow_le_rpow hUx0 hUxM hm1
  have hUm_abs : |(U x) ^ p.m| ≤ M ^ (p.m - 1) * |U x| := by
    rw [abs_of_nonneg (Real.rpow_nonneg hUx0 _), abs_of_nonneg hUx0]
    exact rpow_le_mul_rpow_sub_one_of_mem_band p.hm hUx0 hUxM
  have hUα_abs : |(U x) ^ p.α| ≤ M ^ p.α := by
    rw [abs_of_nonneg (Real.rpow_nonneg hUx0 _)]
    exact Real.rpow_le_rpow hUx0 hUxM hα0
  have hUγ_abs : |(U x) ^ p.γ| ≤ M ^ p.γ := by
    rw [abs_of_nonneg (Real.rpow_nonneg hUx0 _)]
    exact Real.rpow_le_rpow hUx0 hUxM hγ0
  have hV'_abs : |deriv (frozenElliptic p U) x| ≤ M ^ p.γ := by
    calc
      |deriv (frozenElliptic p U) x| ≤ frozenElliptic p U x :=
        frozenElliptic_deriv_abs_le p hU.trap.cunif_bdd hU.nonneg x
      _ ≤ M ^ p.γ :=
        frozenElliptic_le_rpow_of_inWaveTrapSet p hM hU.trap x
  have hV_abs : |frozenElliptic p U x| ≤ M ^ p.γ := by
    rw [abs_of_nonneg (frozenElliptic_nonneg p hU.nonneg x)]
    exact frozenElliptic_le_rpow_of_inWaveTrapSet p hM hU.trap x
  have hflux_eq := stationary_flux_deriv_eq (p := p) hU hU_diff x
  have hflux_bound :
      |deriv (fun y => (U y) ^ p.m * deriv (frozenElliptic p U) y) x| ≤
        |p.m| * M ^ (p.m - 1) * M ^ p.γ * |deriv U x| +
          M ^ (p.m - 1) * (M ^ p.γ + M ^ p.γ) * |U x| := by
    rw [hflux_eq]
    have hterm1 :
        |deriv U x * p.m * (U x) ^ (p.m - 1) *
            deriv (frozenElliptic p U) x| ≤
          |p.m| * M ^ (p.m - 1) * M ^ p.γ * |deriv U x| := by
      rw [abs_mul, abs_mul, abs_mul]
      have hA :
          |deriv U x| * |p.m| * |(U x) ^ (p.m - 1)|
            ≤ |deriv U x| * |p.m| * M ^ (p.m - 1) := by
        exact mul_le_mul_of_nonneg_left hUm1_abs
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      have hB :
          |deriv U x| * |p.m| * |(U x) ^ (p.m - 1)| *
              |deriv (frozenElliptic p U) x|
            ≤ |deriv U x| * |p.m| * M ^ (p.m - 1) * M ^ p.γ := by
        exact mul_le_mul hA hV'_abs (abs_nonneg _)
          (mul_nonneg
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hMm1_nonneg)
      calc
        |deriv U x| * |p.m| * |(U x) ^ (p.m - 1)| *
            |deriv (frozenElliptic p U) x|
            ≤ |deriv U x| * |p.m| * M ^ (p.m - 1) * M ^ p.γ := hB
        _ = |p.m| * M ^ (p.m - 1) * M ^ p.γ * |deriv U x| := by ring
    have hterm2 :
        |(U x) ^ p.m *
            (frozenElliptic p U x - (U x) ^ p.γ)| ≤
          M ^ (p.m - 1) * (M ^ p.γ + M ^ p.γ) * |U x| := by
      rw [abs_mul]
      have hdiff :
          |frozenElliptic p U x - (U x) ^ p.γ| ≤
            M ^ p.γ + M ^ p.γ := by
        calc
          |frozenElliptic p U x - (U x) ^ p.γ|
              ≤ |frozenElliptic p U x| + |(U x) ^ p.γ| := abs_sub _ _
          _ ≤ M ^ p.γ + M ^ p.γ := add_le_add hV_abs hUγ_abs
      calc
        |(U x) ^ p.m| * |frozenElliptic p U x - (U x) ^ p.γ|
            ≤ (M ^ (p.m - 1) * |U x|) * (M ^ p.γ + M ^ p.γ) :=
          mul_le_mul hUm_abs hdiff (abs_nonneg _)
            (mul_nonneg hMm1_nonneg (abs_nonneg _))
        _ = M ^ (p.m - 1) * (M ^ p.γ + M ^ p.γ) * |U x| := by ring
    calc
      |deriv U x * p.m * (U x) ^ (p.m - 1) *
            deriv (frozenElliptic p U) x +
          (U x) ^ p.m *
            (frozenElliptic p U x - (U x) ^ p.γ)|
          ≤ |deriv U x * p.m * (U x) ^ (p.m - 1) *
                deriv (frozenElliptic p U) x| +
              |(U x) ^ p.m *
                (frozenElliptic p U x - (U x) ^ p.γ)| := abs_add_le _ _
      _ ≤ |p.m| * M ^ (p.m - 1) * M ^ p.γ * |deriv U x| +
            M ^ (p.m - 1) * (M ^ p.γ + M ^ p.γ) * |U x| :=
          add_le_add hterm1 hterm2
  have hreact_bound :
      |U x * (1 - (U x) ^ p.α)| ≤ (1 + M ^ p.α) * |U x| := by
    rw [abs_mul]
    have hfac : |1 - (U x) ^ p.α| ≤ 1 + M ^ p.α := by
      rw [abs_le]
      have hpow_nonneg : 0 ≤ (U x) ^ p.α := Real.rpow_nonneg hUx0 _
      have hpow_le : (U x) ^ p.α ≤ M ^ p.α := by
        simpa [abs_of_nonneg (Real.rpow_nonneg hUx0 _)] using hUα_abs
      constructor
      · linarith [hpow_le]
      · linarith [hpow_nonneg, hMα_nonneg]
    calc
      |U x| * |1 - (U x) ^ p.α| ≤ |U x| * (1 + M ^ p.α) :=
        mul_le_mul_of_nonneg_left hfac (abs_nonneg _)
      _ = (1 + M ^ p.α) * |U x| := by ring
  have hstatx := hstat x
  unfold frozenWaveOperator at hstatx
  have hiter : iteratedDeriv 2 U x = deriv (deriv U) x := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hdd_eq :
      deriv (deriv U) x =
        -c * deriv U x +
          p.χ * deriv (fun y => (U y) ^ p.m *
            deriv (frozenElliptic p U) y) x -
          U x * (1 - (U x) ^ p.α) := by
    rw [hiter] at hstatx
    linarith
  rw [hdd_eq]
  calc
    |-c * deriv U x +
          p.χ * deriv (fun y => (U y) ^ p.m *
            deriv (frozenElliptic p U) y) x -
          U x * (1 - (U x) ^ p.α)|
        ≤ |-c * deriv U x| +
            |p.χ * deriv (fun y => (U y) ^ p.m *
              deriv (frozenElliptic p U) y) x| +
            |U x * (1 - (U x) ^ p.α)| := by
          calc
            |-c * deriv U x +
                p.χ * deriv (fun y => (U y) ^ p.m *
                  deriv (frozenElliptic p U) y) x -
                U x * (1 - (U x) ^ p.α)|
                ≤ |-c * deriv U x +
                    p.χ * deriv (fun y => (U y) ^ p.m *
                      deriv (frozenElliptic p U) y) x| +
                    |U x * (1 - (U x) ^ p.α)| := abs_sub _ _
            _ ≤ |-c * deriv U x| +
                  |p.χ * deriv (fun y => (U y) ^ p.m *
                    deriv (frozenElliptic p U) y) x| +
                  |U x * (1 - (U x) ^ p.α)| := by
                    linarith [abs_add_le (-c * deriv U x)
                      (p.χ * deriv (fun y => (U y) ^ p.m *
                        deriv (frozenElliptic p U) y) x)]
    _ = |c| * |deriv U x| +
          |p.χ| * |deriv (fun y => (U y) ^ p.m *
            deriv (frozenElliptic p U) y) x| +
          |U x * (1 - (U x) ^ p.α)| := by
            rw [abs_mul, abs_neg, abs_mul]
    _ ≤ |c| * |deriv U x| +
            |p.χ| *
              (|p.m| * M ^ (p.m - 1) * M ^ p.γ * |deriv U x| +
                M ^ (p.m - 1) * (M ^ p.γ + M ^ p.γ) * |U x|) +
            (1 + M ^ p.α) * |U x| := by
              have hchem_scaled :
                  |p.χ| *
                      |deriv (fun y => (U y) ^ p.m *
                        deriv (frozenElliptic p U) y) x| ≤
                    |p.χ| *
                      (|p.m| * M ^ (p.m - 1) * M ^ p.γ * |deriv U x| +
                        M ^ (p.m - 1) * (M ^ p.γ + M ^ p.γ) * |U x|) :=
                mul_le_mul_of_nonneg_left hflux_bound (abs_nonneg p.χ)
              have hchem_with_c :
                  |c| * |deriv U x| +
                      |p.χ| *
                        |deriv (fun y => (U y) ^ p.m *
                          deriv (frozenElliptic p U) y) x| ≤
                    |c| * |deriv U x| +
                      |p.χ| *
                        (|p.m| * M ^ (p.m - 1) * M ^ p.γ * |deriv U x| +
                          M ^ (p.m - 1) * (M ^ p.γ + M ^ p.γ) * |U x|) := by
                simpa [add_comm, add_left_comm, add_assoc] using
                  add_le_add_right hchem_scaled (|c| * |deriv U x|)
              exact add_le_add hchem_with_c hreact_bound
    _ =
        (|c| + |p.χ| * |p.m| * M ^ (p.m - 1) * M ^ p.γ) *
            |deriv U x| +
          (|p.χ| * M ^ (p.m - 1) * (M ^ p.γ + M ^ p.γ) +
              (1 + M ^ p.α)) *
            |U x| := by ring

private theorem stationaryJet_bound_of_second_deriv_abs_le
    {U : ℝ → ℝ} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hsecond : ∀ x,
      |deriv (deriv U) x| ≤ A * |deriv U x| + B * |U x|) :
    ∃ K : ℝ, ∀ x,
      ‖stationaryJetDeriv U x‖ ≤ K * ‖stationaryJet U x‖ := by
  let K : ℝ := max 1 (A + B)
  have hK_nonneg : 0 ≤ K := by
    exact le_trans zero_le_one (le_max_left _ _)
  have hK_one : 1 ≤ K := le_max_left _ _
  have hK_AB : A + B ≤ K := le_max_right _ _
  refine ⟨K, ?_⟩
  intro x
  have htarget_nonneg : 0 ≤ K * ‖stationaryJet U x‖ :=
    mul_nonneg hK_nonneg (norm_nonneg _)
  rw [pi_norm_le_iff_of_nonneg htarget_nonneg]
  intro i
  fin_cases i
  · have hD_comp :
        |deriv U x| ≤ ‖stationaryJet U x‖ := by
      simpa [stationaryJet, Real.norm_eq_abs] using
        (norm_le_pi_norm (stationaryJet U x) (1 : Fin 2))
    have hscale :
        ‖stationaryJet U x‖ ≤ K * ‖stationaryJet U x‖ := by
      calc
        ‖stationaryJet U x‖ = 1 * ‖stationaryJet U x‖ := by ring
        _ ≤ K * ‖stationaryJet U x‖ :=
          mul_le_mul_of_nonneg_right hK_one (norm_nonneg _)
    simpa [stationaryJetDeriv, Real.norm_eq_abs] using
      le_trans hD_comp hscale
  · have hD_comp :
        |deriv U x| ≤ ‖stationaryJet U x‖ := by
      simpa [stationaryJet, Real.norm_eq_abs] using
        (norm_le_pi_norm (stationaryJet U x) (1 : Fin 2))
    have hU_comp :
        |U x| ≤ ‖stationaryJet U x‖ := by
      simpa [stationaryJet, Real.norm_eq_abs] using
        (norm_le_pi_norm (stationaryJet U x) (0 : Fin 2))
    have hlin :
        A * |deriv U x| + B * |U x| ≤
          (A + B) * ‖stationaryJet U x‖ := by
      nlinarith [mul_le_mul_of_nonneg_left hD_comp hA,
        mul_le_mul_of_nonneg_left hU_comp hB]
    have hscale :
        (A + B) * ‖stationaryJet U x‖ ≤
          K * ‖stationaryJet U x‖ :=
      mul_le_mul_of_nonneg_right hK_AB (norm_nonneg _)
    have hdd :
        |deriv (deriv U) x| ≤ K * ‖stationaryJet U x‖ :=
      le_trans (hsecond x) (le_trans hlin hscale)
    simpa [stationaryJetDeriv, Real.norm_eq_abs] using hdd

private theorem reflected_second_deriv_abs_le
    {U : ℝ → ℝ} {A B : ℝ}
    (hUd_diff : Differentiable ℝ (deriv U))
    (hsecond : ∀ x,
      |deriv (deriv U) x| ≤ A * |deriv U x| + B * |U x|) :
    ∀ x,
      |deriv (deriv (fun t => U (-t))) x| ≤
        A * |deriv (fun t => U (-t)) x| + B * |(fun t => U (-t)) x| := by
  let Urev : ℝ → ℝ := fun t => U (-t)
  have hneg_diff : Differentiable ℝ (fun t : ℝ => -t) := differentiable_id.neg
  have hUrev_deriv_eq :
      deriv Urev = fun t => -deriv U (-t) := by
    funext t
    simpa [Urev] using deriv_comp_neg (f := U) (x := t)
  have hUrev_deriv2_eq :
      deriv (deriv Urev) = fun t => deriv (deriv U) (-t) := by
    funext t
    have hbase :
        deriv (fun s => deriv U (-s)) t = -deriv (deriv U) (-t) := by
      simpa using deriv_comp_neg (f := deriv U) (x := t)
    rw [hUrev_deriv_eq]
    have hbase_at : HasDerivAt (fun s => deriv U (-s))
        (-deriv (deriv U) (-t)) t := by
      simpa using ((hUd_diff (-t)).hasDerivAt.comp t
        ((hasDerivAt_id t).neg))
    have hneg_at : HasDerivAt (fun s => -deriv U (-s))
        (deriv (deriv U) (-t)) t := by
      convert hbase_at.neg using 1
      ring
    exact hneg_at.deriv
  intro x
  rw [hUrev_deriv2_eq, hUrev_deriv_eq]
  simpa [Urev, abs_neg] using hsecond (-x)

/-- A global linear bound for the second derivative supplies the profile-wise
Grönwall zero-Cauchy data.  This is the reusable scalar ODE core behind both
strict positivity of `U` and, below, strict positivity of `1 - U`. -/
theorem stationaryLinearGronwallProfileData_of_second_deriv_abs_le
    {U : ℝ → ℝ} {A B : ℝ}
    (hUd_diff : Differentiable ℝ (deriv U))
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hsecond : ∀ x,
      |deriv (deriv U) x| ≤ A * |deriv U x| + B * |U x|) :
    StationaryLinearGronwallProfileData U := by
  obtain ⟨K, hK⟩ :=
    stationaryJet_bound_of_second_deriv_abs_le
      (U := U) hA hB hsecond
  have hsecond_rev :
      ∀ x,
        |deriv (deriv (fun t => U (-t))) x| ≤
          A * |deriv (fun t => U (-t)) x| +
            B * |(fun t => U (-t)) x| :=
    reflected_second_deriv_abs_le hUd_diff hsecond
  obtain ⟨Krev, hKrev⟩ :=
    stationaryJet_bound_of_second_deriv_abs_le
      (U := fun t => U (-t)) hA hB hsecond_rev
  intro x₀ _hx₀ _hDx₀
  constructor
  · intro y _hy
    exact ⟨K, fun x _hx => hK x⟩
  · intro y _hy
    exact ⟨Krev, fun x _hx => hKrev x⟩

/-- The regularity frontier needed before the trap/stationary equation can
construct the direct linear Grönwall data.  The pointwise frozen equation alone
mentions `deriv`/`iteratedDeriv`, but does not by itself provide
`HasDerivAt`/`Differentiable` facts in Lean. -/
def StationaryC2RegularityFromEquation
    (p : CMParams) (c κ M : ℝ) : Prop :=
  ∀ U : ℝ → ℝ,
    InMonotoneWaveTrapSet κ M U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        Differentiable ℝ U ∧ Differentiable ℝ (deriv U)

/-- Exact Green-representation floor for stationary trapped profiles.

This packages the non-circular data needed to turn stationarity into C²
regularity: the diagonal cross map is fixed, its stationary source is continuous
with the two weighted Green tails, and the cross-map/Green identity data are
available. -/
def StationaryGreenRepresentationFromEquation
    (p : CMParams) (c lam κ M : ℝ) : Prop :=
  ∀ U : ℝ → ℝ,
    InMonotoneWaveTrapSet κ M U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        StationaryCrossGreenData p c lam U ∧
        Continuous (crossSource p lam U U U) ∧
        (∀ x,
          IntegrableOn
            (gWeight (greenRootPlus c lam) (crossSource p lam U U U))
            (Ioi x)) ∧
        (∀ x,
          IntegrableOn
            (gWeight (greenRootMinus c lam) (crossSource p lam U U U))
            (Iic x)) ∧
        crossImplicitMap p c lam U U U = U

/-- A profile represented by a Green convolution of a continuous source is C²
for the purposes of the stationary Grönwall route. -/
theorem stationaryC2Regularity_of_greenRepresentation
    {c lam : ℝ} {U R : ℝ → ℝ}
    (hR_cont : Continuous R)
    (hRhi : ∀ x,
      IntegrableOn (gWeight (greenRootPlus c lam) R) (Ioi x))
    (hRlo : ∀ x,
      IntegrableOn (gWeight (greenRootMinus c lam) R) (Iic x))
    (hgreen : U = fun x => greenConv c lam R x) :
    Differentiable ℝ U ∧ Differentiable ℝ (deriv U) := by
  have hG_diff : Differentiable ℝ (greenConv c lam R) :=
    fun x =>
      (greenConv_hasDerivAt
        (c := c) (lam := lam) (H := R) hR_cont hRhi hRlo x).differentiableAt
  have hG_deriv_eq :
      deriv (greenConv c lam R) = fun x => greenConvDeriv c lam R x :=
    funext fun x =>
      (greenConv_hasDerivAt
        (c := c) (lam := lam) (H := R) hR_cont hRhi hRlo x).deriv
  have hGd_diff : Differentiable ℝ (deriv (greenConv c lam R)) := by
    rw [hG_deriv_eq]
    intro x
    exact (greenConvDeriv_hasDerivAt
      (c := c) (lam := lam) (H := R) hR_cont hRhi hRlo x).differentiableAt
  constructor
  · simpa [hgreen] using hG_diff
  · simpa [hgreen] using hGd_diff

/-- C² regularity from the diagonal cross fixed point, via the Green
representation of `crossSource`. -/
theorem stationaryC2Regularity_of_crossImplicitMap_fixed
    {p : CMParams} {c lam : ℝ} {U : ℝ → ℝ}
    (hlam : 0 < lam)
    (hdata : StationaryCrossGreenData p c lam U)
    (hR_cont : Continuous (crossSource p lam U U U))
    (hRhi : ∀ x,
      IntegrableOn
        (gWeight (greenRootPlus c lam) (crossSource p lam U U U))
        (Ioi x))
    (hRlo : ∀ x,
      IntegrableOn
        (gWeight (greenRootMinus c lam) (crossSource p lam U U U))
        (Iic x))
    (hcross : crossImplicitMap p c lam U U U = U) :
    Differentiable ℝ U ∧ Differentiable ℝ (deriv U) := by
  have hgreen :
      U = fun x => greenConv c lam (crossSource p lam U U U) x := by
    calc
      U = crossImplicitMap p c lam U U U := hcross.symm
      _ = fun x => greenConv c lam (crossSource p lam U U U) x :=
        StationaryCrossGreenData.crossImplicitMap_eq_greenConv_crossSource
          (p := p) (c := c) (lam := lam) (U := U) hlam hdata
  exact stationaryC2Regularity_of_greenRepresentation
    (c := c) (lam := lam) (U := U) (R := crossSource p lam U U U)
    hR_cont hRhi hRlo hgreen

/-- Discharge the `StationaryC2RegularityFromEquation` frontier from a
non-circular Green-representation provider for stationary trapped profiles.  The
C² source is the Green representation, not the pointwise totalized equation. -/
theorem stationaryC2RegularityFromEquation_of_trap
    {p : CMParams} {c lam κ M : ℝ}
    (hlam : 0 < lam)
    (hgreen : StationaryGreenRepresentationFromEquation p c lam κ M) :
    StationaryC2RegularityFromEquation p c κ M := by
  intro U hU hstat
  rcases hgreen U hU hstat with
    ⟨hdata, hR_cont, hRhi, hRlo, hcross⟩
  exact stationaryC2Regularity_of_crossImplicitMap_fixed
    (p := p) (c := c) (lam := lam) (U := U)
    hlam hdata hR_cont hRhi hRlo hcross

/-- Build the real-exponent linear Grönwall payload for one stationary trapped
profile. -/
theorem stationaryLinearGronwallProfileData_of_trap
    {p : CMParams} {c κ M : ℝ} {U : ℝ → ℝ}
    (hM : 0 < M)
    (hU : InMonotoneWaveTrapSet κ M U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hU_diff : Differentiable ℝ U)
    (hUd_diff : Differentiable ℝ (deriv U)) :
    StationaryLinearGronwallProfileData U := by
  intro x₀ _hx₀ _hDx₀
  let A : ℝ := |c| + |p.χ| * |p.m| * M ^ (p.m - 1) * M ^ p.γ
  let B : ℝ := |p.χ| * M ^ (p.m - 1) * (M ^ p.γ + M ^ p.γ) +
    (1 + M ^ p.α)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hsecond : ∀ x,
      |deriv (deriv U) x| ≤ A * |deriv U x| + B * |U x| := by
    intro x
    simpa [A, B] using
      stationary_second_deriv_abs_le_of_trap
        (p := p) (c := c) (κ := κ) (M := M) (U := U)
        hM hU hstat hU_diff x
  obtain ⟨K, hK⟩ :=
    stationaryJet_bound_of_second_deriv_abs_le
      (U := U) hA_nonneg hB_nonneg hsecond
  have hsecond_rev :
      ∀ x,
        |deriv (deriv (fun t => U (-t))) x| ≤
          A * |deriv (fun t => U (-t)) x| +
            B * |(fun t => U (-t)) x| :=
    reflected_second_deriv_abs_le hUd_diff hsecond
  obtain ⟨Krev, hKrev⟩ :=
    stationaryJet_bound_of_second_deriv_abs_le
      (U := fun t => U (-t)) hA_nonneg hB_nonneg hsecond_rev
  constructor
  · intro y _hy
    exact ⟨K, fun x _hx => hK x⟩
  · intro y _hy
    exact ⟨Krev, fun x _hx => hKrev x⟩

/-- Strict positivity for one nontrivial stationary profile, with its `C²`
regularity supplied by the construction. -/
theorem stationaryProfile_strictlyPositive_of_trap_regularity
    {p : CMParams} {c κ M : ℝ} {U : ℝ → ℝ}
    (hM : 0 < M)
    (hU : InMonotoneWaveTrapSet κ M U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hU_diff : Differentiable ℝ U)
    (hUd_diff : Differentiable ℝ (deriv U))
    (hnontriv : ProfileNontrivial U) :
    ∀ x, 0 < U x :=
  stationaryProfile_strictlyPositive_of_linearGronwall
    hU.nonneg hU_diff hUd_diff
      (stationaryLinearGronwallProfileData_of_trap
        hM hU hstat hU_diff hUd_diff)
    hnontriv

/-- In the zero-sensitivity scalar equation, a nonconstant stationary profile
trapped below `1` is strictly below `1` at every finite point.

Apply the same zero-Cauchy Grönwall argument to `Q = 1 - U`.  The stationary
equation gives
`Q'' = -c Q' + U (1 - U^α)`; Lipschitz continuity of `s ↦ s^α` on
`[0,1]` makes the last term linear in `Q`.  The right limit `U → 0`
excludes the constant solution `U ≡ 1`. -/
theorem stationaryProfile_strictlyBelow_one_of_chi_zero_trap_regularity
    {p : CMParams} {c κ : ℝ} {U : ℝ → ℝ}
    (hchi : p.χ = 0)
    (hU : InMonotoneWaveTrapSet κ 1 U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hU_diff : Differentiable ℝ U)
    (hUd_diff : Differentiable ℝ (deriv U))
    (hlim : Tendsto U atTop (nhds 0)) :
    ∀ x, U x < 1 := by
  let Q : ℝ → ℝ := fun x => 1 - U x
  have hQ_nonneg : ∀ x, 0 ≤ Q x := by
    intro x
    dsimp [Q]
    exact sub_nonneg.mpr (hU.le_M x)
  have hQ_diff : Differentiable ℝ Q := by
    intro x
    exact (differentiableAt_const (c := (1 : ℝ))).sub (hU_diff x)
  have hQ_deriv : deriv Q = fun x => -deriv U x := by
    funext x
    simpa [Q] using ((hasDerivAt_const (x := x) (c := (1 : ℝ))).sub
      (hU_diff x).hasDerivAt).deriv
  have hQd_diff : Differentiable ℝ (deriv Q) := by
    rw [hQ_deriv]
    exact hUd_diff.neg
  let A : ℝ := |c|
  let B : ℝ := rpowLip p.α 1
  have hA : 0 ≤ A := abs_nonneg c
  have hB : 0 ≤ B := rpowLip_nonneg p.hα zero_le_one
  have hsecond : ∀ x,
      |deriv (deriv Q) x| ≤ A * |deriv Q x| + B * |Q x| := by
    intro x
    have hUdd := stationary_second_deriv_eq_of_trap
      (p := p) (c := c) (U := U) hU hstat hU_diff x
    rw [hchi] at hUdd
    simp only [zero_mul] at hUdd
    have hQdd : deriv (deriv Q) x = -deriv (deriv U) x := by
      rw [hQ_deriv]
      exact ((hUd_diff x).hasDerivAt.neg).deriv
    have hQformula :
        deriv (deriv Q) x =
          -c * deriv Q x + U x * (1 - (U x) ^ p.α) := by
      rw [hQdd, hUdd, congrFun hQ_deriv x]
      ring
    have hUx : U x ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨hU.nonneg x, hU.le_M x⟩
    have hOne : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
    have hLip := rpow_m_lipschitz_on_Icc
      (m := p.α) (M := (1 : ℝ)) p.hα zero_le_one
    have hdistE := hLip hUx hOne
    rw [edist_dist, edist_dist] at hdistE
    have hdist :
        dist ((U x) ^ p.α) ((1 : ℝ) ^ p.α) ≤
          (Real.toNNReal (rpowLip p.α 1) : ℝ) * dist (U x) 1 := by
      have hraw := hdistE
      rw [← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_le_ofReal_iff (by positivity)] at hraw
      exact hraw
    rw [Real.coe_toNNReal _ hB] at hdist
    have hpow :
        |1 - (U x) ^ p.α| ≤ B * |Q x| := by
      simpa [B, Q, Real.dist_eq, abs_sub_comm] using hdist
    have hUabs : |U x| ≤ 1 := by
      rw [abs_of_nonneg (hU.nonneg x)]
      exact hU.le_M x
    have hreact :
        |U x * (1 - (U x) ^ p.α)| ≤ B * |Q x| := by
      rw [abs_mul]
      calc
        |U x| * |1 - (U x) ^ p.α|
            ≤ 1 * (B * |Q x|) :=
          mul_le_mul hUabs hpow (abs_nonneg _)
            (by positivity)
        _ = B * |Q x| := one_mul _
    rw [hQformula]
    calc
      |-c * deriv Q x + U x * (1 - (U x) ^ p.α)|
          ≤ |-c * deriv Q x| + |U x * (1 - (U x) ^ p.α)| :=
        abs_add_le _ _
      _ ≤ |c| * |deriv Q x| + B * |Q x| := by
        rw [abs_mul, abs_neg]
        exact add_le_add le_rfl hreact
      _ = A * |deriv Q x| + B * |Q x| := rfl
  have hlin : StationaryLinearGronwallProfileData Q :=
    stationaryLinearGronwallProfileData_of_second_deriv_abs_le
      hQd_diff hA hB hsecond
  have hQ_nontriv : ProfileNontrivial Q := by
    by_contra hnot
    simp only [ProfileNontrivial, not_exists, not_lt] at hnot
    have hQzero : ∀ x, Q x = 0 := by
      intro x
      exact le_antisymm (hnot x) (hQ_nonneg x)
    have hUone : U = fun _ : ℝ => (1 : ℝ) := by
      funext x
      have hx := hQzero x
      dsimp [Q] at hx
      linarith
    have hlim_one : Tendsto U atTop (nhds (1 : ℝ)) := by
      rw [hUone]
      exact tendsto_const_nhds
    have hbad : (1 : ℝ) = 0 := tendsto_nhds_unique hlim_one hlim
    norm_num at hbad
  have hQpos : ∀ x, 0 < Q x :=
    stationaryProfile_strictlyPositive_of_linearGronwall
      hQ_nonneg hQ_diff hQd_diff hlin hQ_nontriv
  intro x
  have := hQpos x
  dsimp [Q] at this
  linarith

/-- Once the missing C² regularity frontier is supplied, the real-exponent
trap-band estimates construct the `StationaryLinearGronwallData` needed by the
strong maximum principle.  No integer exponent or traveling-wave ODE
realization is used here. -/
theorem stationaryLinearGronwallData_of_trap
    {p : CMParams} {c κ M : ℝ}
    (hM : 0 < M)
    (hreg : StationaryC2RegularityFromEquation p c κ M) :
    StationaryLinearGronwallData p c κ M := by
  intro U hU hstat
  rcases hreg U hU hstat with ⟨hU_diff, hUd_diff⟩
  refine ⟨hU_diff, hUd_diff, ?_⟩
  intro x₀ _hx₀ _hDx₀
  let A : ℝ := |c| + |p.χ| * |p.m| * M ^ (p.m - 1) * M ^ p.γ
  let B : ℝ := |p.χ| * M ^ (p.m - 1) * (M ^ p.γ + M ^ p.γ) +
    (1 + M ^ p.α)
  have hM0 : 0 ≤ M := hM.le
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hsecond : ∀ x,
      |deriv (deriv U) x| ≤ A * |deriv U x| + B * |U x| := by
    intro x
    simpa [A, B] using
      stationary_second_deriv_abs_le_of_trap
        (p := p) (c := c) (κ := κ) (M := M) (U := U)
        hM hU hstat hU_diff x
  obtain ⟨K, hK⟩ :=
    stationaryJet_bound_of_second_deriv_abs_le
      (U := U) hA_nonneg hB_nonneg hsecond
  have hsecond_rev :
      ∀ x,
        |deriv (deriv (fun t => U (-t))) x| ≤
          A * |deriv (fun t => U (-t)) x| +
            B * |(fun t => U (-t)) x| :=
    reflected_second_deriv_abs_le hUd_diff hsecond
  obtain ⟨Krev, hKrev⟩ :=
    stationaryJet_bound_of_second_deriv_abs_le
      (U := fun t => U (-t)) hA_nonneg hB_nonneg hsecond_rev
  constructor
  · intro y _hy
    exact ⟨K, fun x _hx => hK x⟩
  · intro y _hy
    exact ⟨Krev, fun x _hx => hKrev x⟩

theorem stationaryStrongMaxPrinciple_of_trap_regularity
    {p : CMParams} {c κ M : ℝ}
    (hM : 0 < M)
    (hreg : StationaryC2RegularityFromEquation p c κ M) :
    StationaryStrongMaxPrinciple p c κ M :=
  stationaryStrongMaxPrinciple_of_linearGronwall
    (stationaryLinearGronwallData_of_trap hM hreg)

/-- Strong maximum principle closed from the trap Green-representation data,
without routing through the integer-exponent traveling-wave ODE. -/
theorem stationaryStrongMaxPrinciple_of_trap
    {p : CMParams} {c lam κ M : ℝ}
    (hM : 0 < M) (hlam : 0 < lam)
    (hgreen : StationaryGreenRepresentationFromEquation p c lam κ M) :
    StationaryStrongMaxPrinciple p c κ M :=
  stationaryStrongMaxPrinciple_of_trap_regularity hM
    (stationaryC2RegularityFromEquation_of_trap
      (p := p) (c := c) (lam := lam) (κ := κ) (M := M) hlam hgreen)

/-- The paper-positive floor cannot be carried for every trapped profile:
the zero trapped profile refutes it. -/
theorem not_monotoneTrap_profile_paperPositiveInitialDatum
    {κ M : ℝ} (hM : 0 ≤ M) :
    ¬ (∀ U : ℝ → ℝ,
      InMonotoneWaveTrapSet κ M U → PaperPositiveInitialDatum U) := by
  intro hfloor
  exact not_profileNontrivial_zero
    ⟨0, (hfloor (fun _ : ℝ => (0 : ℝ))
      (InMonotoneWaveTrapSet.zero (κ := κ) (M := M) hM)).pos 0⟩

/-- Exact universal `hpos` profile obligation discharged from the
paper-positive floor carried for each trapped profile. -/
theorem monotoneTrap_profile_hpos_of_floor {κ M : ℝ}
    (hfloor : ∀ U : ℝ → ℝ,
      InMonotoneWaveTrapSet κ M U → PaperPositiveInitialDatum U) :
    ∀ U : ℝ → ℝ, InMonotoneWaveTrapSet κ M U → ∀ x, 0 < U x :=
  fun U hU => (hfloor U hU).pos

/-- A monotone-wave-trap profile has a finite left limit.

This is the monotone-convergence part of the route to the left endpoint:
antitonicity gives the `atBot` limit as the supremum of the range, while the
trap bounds place the limit in `[0, M]`. -/
theorem monotoneTrap_left_limit_exists {κ M : ℝ} {U : ℝ → ℝ}
    (hU : InMonotoneWaveTrapSet κ M U) :
    ∃ L : ℝ, Tendsto U atBot (𝓝 L) ∧ 0 ≤ L ∧ L ≤ M := by
  let L : ℝ := sSup (Set.range U)
  have hbdd : BddAbove (Set.range U) := by
    refine ⟨M, ?_⟩
    rintro y ⟨x, rfl⟩
    exact hU.le_M x
  have hlim : Tendsto U atBot (𝓝 L) := by
    simpa [L] using tendsto_atBot_ciSup hU.antitone hbdd
  have hL0 : 0 ≤ L := by
    have hU0_le : U 0 ≤ L := by
      simpa [L] using le_csSup hbdd (Set.mem_range_self (0 : ℝ))
    exact le_trans (hU.nonneg 0) hU0_le
  have hLM : L ≤ M := by
    have hne : (Set.range U).Nonempty := Set.range_nonempty U
    simpa [L] using csSup_le hne (by
      rintro y ⟨x, rfl⟩
      exact hU.le_M x)
  exact ⟨L, hlim, hL0, hLM⟩

/-- A genuine left lower pin makes a finite left limit strictly positive. -/
theorem StrictlyPositiveAtLeft.limit_pos {U : ℝ → ℝ} {L : ℝ}
    (hleft : StrictlyPositiveAtLeft U) (hlim : Tendsto U atBot (𝓝 L)) :
    0 < L := by
  rcases hleft with ⟨δ, hδ, hδle⟩
  exact lt_of_lt_of_le hδ (ge_of_tendsto hlim hδle)

/-- Positive roots of the logistic reaction `s ↦ s * (1 - s ^ a)` equal `1`. -/
theorem reactionFun_root_eq_one_of_pos {a L : ℝ}
    (ha : 0 < a) (hL : 0 < L) (hroot : reactionFun a L = 0) :
    L = 1 := by
  have hfactor : 1 - L ^ a = 0 := by
    unfold reactionFun at hroot
    rcases mul_eq_zero.mp hroot with hLzero | hfac
    · exact False.elim ((ne_of_gt hL) hLzero)
    · exact hfac
  have hpow : L ^ a = 1 := by linarith
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hpow_lt : L ^ a < 1 := by
      rw [← Real.one_rpow a]
      exact Real.rpow_lt_rpow hL.le hlt ha
    linarith
  · have hpow_gt : 1 < L ^ a := by
      rw [← Real.one_rpow a]
      exact Real.rpow_lt_rpow zero_le_one hgt ha
    linarith

/-- Route-b pin step: a left limit that is a positive reaction root is `1`. -/
theorem tendsto_atBot_one_of_reaction_root_pin
    {a L : ℝ} {U : ℝ → ℝ}
    (ha : 0 < a) (hlim : Tendsto U atBot (𝓝 L))
    (hL : 0 < L) (hroot : reactionFun a L = 0) :
    Tendsto U atBot (𝓝 1) := by
  have hLone : L = 1 := reactionFun_root_eq_one_of_pos ha hL hroot
  simpa [hLone] using hlim

/-- Pointwise positivity plus monotonicity gives the route-b lower pin at
`-∞`: use `U 0` as the eventual lower bound on the left half-line. -/
theorem InMonotoneWaveTrapSet.strictlyPositiveAtLeft_of_pos
    {κ M : ℝ} {U : ℝ → ℝ} (hU : InMonotoneWaveTrapSet κ M U)
    (hpos : ∀ x, 0 < U x) :
    StrictlyPositiveAtLeft U := by
  refine ⟨U 0, hpos 0, ?_⟩
  refine eventually_atBot.2 ⟨0, ?_⟩
  intro x hx
  exact hU.antitone hx

/-- A lower pin that is positive at one point gives a strictly positive left
tail.  Monotonicity transports the positive value at `x₀` to every `x ≤ x₀`. -/
theorem InMonotoneWaveTrapSet.strictlyPositiveAtLeft_of_lower_pin_at
    {κ M : ℝ} {φ U : ℝ → ℝ} (hU : InMonotoneWaveTrapSet κ M U)
    (hlower : ∀ x, φ x ≤ U x) {x₀ : ℝ} (hφpos : 0 < φ x₀) :
    StrictlyPositiveAtLeft U := by
  refine ⟨φ x₀, hφpos, ?_⟩
  refine eventually_atBot.2 ⟨x₀, ?_⟩
  intro x hx
  exact le_trans (hlower x₀) (hU.antitone hx)

/-- Single-profile route (b): monotone left limit + pointwise positivity
lower-pin + reaction-root at every left limit. -/
theorem InMonotoneWaveTrapSet.tendsto_atBot_one_of_limit_root_and_pos
    {κ M : ℝ} {U : ℝ → ℝ} (p : CMParams)
    (hU : InMonotoneWaveTrapSet κ M U)
    (hpos : ∀ x, 0 < U x)
    (hroot : ∀ L : ℝ, Tendsto U atBot (𝓝 L) → reactionFun p.α L = 0) :
    Tendsto U atBot (𝓝 1) := by
  rcases monotoneTrap_left_limit_exists hU with ⟨L, hlim, _hL0, _hLM⟩
  have hα : 0 < p.α := lt_of_lt_of_le zero_lt_one p.hα
  have hleft : StrictlyPositiveAtLeft U := hU.strictlyPositiveAtLeft_of_pos hpos
  have hL : 0 < L := hleft.limit_pos hlim
  exact tendsto_atBot_one_of_reaction_root_pin hα hlim hL (hroot L hlim)

/-- Single-profile route (b) with an explicit lower pin `φ ≤ U`, assuming the
pin is positive at one point. -/
theorem InMonotoneWaveTrapSet.tendsto_atBot_one_of_limit_root_and_lower_pin_at
    {κ M : ℝ} {φ U : ℝ → ℝ} (p : CMParams)
    (hU : InMonotoneWaveTrapSet κ M U)
    (hlower : ∀ x, φ x ≤ U x) {x₀ : ℝ} (hφpos : 0 < φ x₀)
    (hroot : ∀ L : ℝ, Tendsto U atBot (𝓝 L) → reactionFun p.α L = 0) :
    Tendsto U atBot (𝓝 1) := by
  rcases monotoneTrap_left_limit_exists hU with ⟨L, hlim, _hL0, _hLM⟩
  have hα : 0 < p.α := lt_of_lt_of_le zero_lt_one p.hα
  have hleft : StrictlyPositiveAtLeft U :=
    hU.strictlyPositiveAtLeft_of_lower_pin_at hlower hφpos
  have hL : 0 < L := hleft.limit_pos hlim
  exact tendsto_atBot_one_of_reaction_root_pin hα hlim hL (hroot L hlim)

/-- Single-profile route (b) with the paper-faithful uniform floor as the lower
pin.  The floor is the whole-line version of paper eq. (1.11). -/
theorem InMonotoneWaveTrapSet.tendsto_atBot_one_of_limit_root_and_floor
    {κ M : ℝ} {U : ℝ → ℝ} (p : CMParams)
    (hU : InMonotoneWaveTrapSet κ M U)
    (hfloor : PaperPositiveInitialDatum U)
    (hroot : ∀ L : ℝ, Tendsto U atBot (𝓝 L) → reactionFun p.α L = 0) :
    Tendsto U atBot (𝓝 1) := by
  rcases monotoneTrap_left_limit_exists hU with ⟨L, hlim, _hL0, _hLM⟩
  have hα : 0 < p.α := lt_of_lt_of_le zero_lt_one p.hα
  have hleft : StrictlyPositiveAtLeft U := hfloor.strictlyPositiveAtLeft
  have hL : 0 < L := hleft.limit_pos hlim
  exact tendsto_atBot_one_of_reaction_root_pin hα hlim hL (hroot L hlim)

/-- Flatness of a stationary frozen profile at the left endpoint: the two
linear derivative terms and the chemotactic flux derivative vanish at `-∞`. -/
def FrozenStationaryFlatAtLeft (p : CMParams) (U : ℝ → ℝ) : Prop :=
  Tendsto (fun x => iteratedDeriv 2 U x) atBot (𝓝 0) ∧
    Tendsto (fun x => deriv U x) atBot (𝓝 0) ∧
      Tendsto
        (fun x => deriv
          (fun y => (U y) ^ p.m * deriv (frozenElliptic p U) y) x)
        atBot (𝓝 0)

/-- Stationary-limit root step under the explicit flatness hypotheses at
`-∞`.  This isolates the analytic input still needed to derive `hroot` from
the stationary equation. -/
theorem reactionFun_root_of_stationary_flat_limit
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ} {L : ℝ}
    (hlim : Tendsto U atBot (𝓝 L))
    (hD2 : Tendsto (fun x => iteratedDeriv 2 U x) atBot (𝓝 0))
    (hD1 : Tendsto (fun x => deriv U x) atBot (𝓝 0))
    (hFlux : Tendsto
      (fun x => deriv
        (fun y => (U y) ^ p.m * deriv (frozenElliptic p U) y) x)
      atBot (𝓝 0))
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0) :
    reactionFun p.α L = 0 := by
  have hα_nonneg : 0 ≤ p.α := le_trans zero_le_one p.hα
  have hpow :
      Tendsto (fun x => (U x) ^ p.α) atBot (𝓝 (L ^ p.α)) :=
    hlim.rpow_const (Or.inr hα_nonneg)
  have hreact :
      Tendsto (fun x => reactionFun p.α (U x)) atBot
        (𝓝 (reactionFun p.α L)) := by
    unfold reactionFun
    exact hlim.mul (tendsto_const_nhds.sub hpow)
  have hsum :
      Tendsto
        (fun x =>
          iteratedDeriv 2 U x + c * deriv U x -
            p.χ *
              deriv
                (fun y => (U y) ^ p.m * deriv (frozenElliptic p U) y) x +
            reactionFun p.α (U x))
        atBot (𝓝 (reactionFun p.α L)) := by
    simpa using
      (((hD2.add (hD1.const_mul c)).add (hFlux.const_mul (-p.χ))).add hreact)
  have hop :
      Tendsto (fun x => frozenWaveOperator p c U U x) atBot
        (𝓝 (reactionFun p.α L)) := by
    simpa [frozenWaveOperator, reactionFun, sub_eq_add_neg, mul_assoc] using hsum
  have hzero : Tendsto (fun x => frozenWaveOperator p c U U x) atBot (𝓝 0) := by
    simp [hstat]
  exact tendsto_nhds_unique hop hzero

/-- Equilibrium step at the left endpoint: passing the stationary frozen
equation to an `atBot` profile limit leaves exactly the logistic reaction root. -/
theorem reactionFun_root_of_stationary_equation_atBot_limit
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ} {L : ℝ}
    (hlim : Tendsto U atBot (𝓝 L))
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hflat : FrozenStationaryFlatAtLeft p U) :
    reactionFun p.α L = 0 := by
  exact reactionFun_root_of_stationary_flat_limit hlim
    hflat.1 hflat.2.1 hflat.2.2 hstat

/-- Single-profile route (b) with all analytic ingredients explicit:
monotone bounded left limit, stationary-flat root, and paper floor pin. -/
theorem InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_floor
    {κ M : ℝ} {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hU : InMonotoneWaveTrapSet κ M U)
    (hfloor : PaperPositiveInitialDatum U)
    (hflat : FrozenStationaryFlatAtLeft p U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0) :
    Tendsto U atBot (𝓝 1) := by
  refine InMonotoneWaveTrapSet.tendsto_atBot_one_of_limit_root_and_floor
    p hU hfloor ?_
  intro L hlim
  exact reactionFun_root_of_stationary_equation_atBot_limit hlim hstat hflat

/-- Single-profile route (b) with an explicit lower pin and the stationary-flat
reaction-root step. -/
theorem InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_lower_pin_at
    {κ M : ℝ} {p : CMParams} {c : ℝ} {φ U : ℝ → ℝ}
    (hU : InMonotoneWaveTrapSet κ M U)
    (hlower : ∀ x, φ x ≤ U x) {x₀ : ℝ} (hφpos : 0 < φ x₀)
    (hflat : FrozenStationaryFlatAtLeft p U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0) :
    Tendsto U atBot (𝓝 1) := by
  refine InMonotoneWaveTrapSet.tendsto_atBot_one_of_limit_root_and_lower_pin_at
    p hU hlower hφpos ?_
  intro L hlim
  exact reactionFun_root_of_stationary_equation_atBot_limit hlim hstat hflat

/-- The raw lower barrier supplies the explicit positive lower pin at
`lowerBarrierXPlus`, and monotonicity transports it to the whole left tail. -/
theorem InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_lowerBarrierRaw_pin
    {κ κtilde D M : ℝ} {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D)
    (hU : InMonotoneWaveTrapSet κ M U)
    (hlower : ∀ x, lowerBarrierRaw κ κtilde D x ≤ U x)
    (hflat : FrozenStationaryFlatAtLeft p U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0) :
    Tendsto U atBot (𝓝 1) := by
  exact InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_lower_pin_at
    (p := p) (c := c) (hU := hU)
    (φ := lowerBarrierRaw κ κtilde D) hlower
    (x₀ := lowerBarrierXPlus κ κtilde D)
    (lowerBarrierRaw_pos_at_xplus hκ hgap hD) hflat hstat

/-- Single-profile route (b) with pointwise positivity instead of the vacuous
whole-trap paper floor. -/
theorem InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_pos
    {κ M : ℝ} {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hU : InMonotoneWaveTrapSet κ M U)
    (hpos : ∀ x, 0 < U x)
    (hflat : FrozenStationaryFlatAtLeft p U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0) :
    Tendsto U atBot (𝓝 1) := by
  refine InMonotoneWaveTrapSet.tendsto_atBot_one_of_limit_root_and_pos
    p hU hpos ?_
  intro L hlim
  exact reactionFun_root_of_stationary_equation_atBot_limit hlim hstat hflat

/-- Strong-maximum-principle route: non-trivial stationary nonnegative trapped
profiles are strictly positive; then the flat left endpoint pins the left
limit to `1`. -/
theorem InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_nontrivial
    {κ M : ℝ} {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hU : InMonotoneWaveTrapSet κ M U)
    (hsmp : StationaryStrongMaxPrinciple p c κ M)
    (hnontriv : ProfileNontrivial U)
    (hflat : FrozenStationaryFlatAtLeft p U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0) :
    Tendsto U atBot (𝓝 1) := by
  exact InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_pos
    hU (hsmp U hU hstat hnontriv) hflat hstat

/-- ODE-uniqueness bridge for the strong maximum principle.

This is the single analytic input supplied by the 1-D traveling-wave ODE:
if a stationary trapped profile touches the equilibrium component `U = 0`, then
the Cauchy data agree with `TravelingWaveODE.E0`; Picard-Lindelöf uniqueness for
`TravelingWaveODE.vectorField` therefore propagates the zero profile. -/
def StationaryZeroPropagatesByODEUniqueness
    (p : CMParams) (c κ M : ℝ) : Prop :=
  ∀ U, InMonotoneWaveTrapSet κ M U →
    (∀ x, frozenWaveOperator p c U U x = 0) →
      ∀ x₀, U x₀ = 0 → ∀ x, U x = 0

/-- The stationary equation has been realized as the autonomous traveling-wave
ODE, with the first component equal to the trapped profile. -/
def StationaryTravelingWaveODERealization
    (p : Params) (κ M : ℝ) : Prop :=
  ∀ U, InMonotoneWaveTrapSet κ M U →
    (∀ x, frozenWaveOperator p.toCMParams p.c U U x = 0) →
      ∃ z : ℝ → State, SolvesTWODE p z ∧ ∀ x, z x 0 = U x

private noncomputable def zeroUFiber
    (_p : Params) (a v₀ v₁ : ℝ) :
    ℝ → State :=
  fun t => ![
    0,
    0,
    v₀ * Real.cosh (t - a) + v₁ * Real.sinh (t - a),
    v₀ * Real.sinh (t - a) + v₁ * Real.cosh (t - a)]

private theorem zeroUFiber_solves
    (p : Params) (a v₀ v₁ : ℝ) :
    SolvesTWODE p (zeroUFiber p a v₀ v₁) := by
  intro t
  rw [hasDerivAt_pi]
  intro i
  have hcosh :
      HasDerivAt (fun s : ℝ => Real.cosh (s - a)) (Real.sinh (t - a)) t := by
    simpa using (Real.hasDerivAt_cosh (t - a)).comp t
      ((hasDerivAt_id t).sub_const a)
  have hsinh :
      HasDerivAt (fun s : ℝ => Real.sinh (s - a)) (Real.cosh (t - a)) t := by
    simpa using (Real.hasDerivAt_sinh (t - a)).comp t
      ((hasDerivAt_id t).sub_const a)
  fin_cases i
  · simpa [zeroUFiber, vectorField] using
      (hasDerivAt_const (x := t) (c := (0 : ℝ)))
  · simpa [zeroUFiber, vectorField,
      Nat.ne_of_gt p.hm, Nat.ne_of_gt p.hgamma, zero_pow] using
      (hasDerivAt_const (x := t) (c := (0 : ℝ)))
  · simpa [zeroUFiber, vectorField, mul_comm, mul_left_comm, mul_assoc,
      add_comm, add_left_comm, add_assoc] using
      (hcosh.const_mul v₀).add (hsinh.const_mul v₁)
  · simpa [zeroUFiber, vectorField, Nat.ne_of_gt p.hgamma, zero_pow, mul_comm,
      mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using
      (hsinh.const_mul v₀).add (hcosh.const_mul v₁)

/-- Once the stationary profile has been packaged as the traveling-wave ODE,
local Cauchy uniqueness propagates a zero of `U` to all of `ℝ`.  The comparison
solution keeps the actual `(V,V')` Cauchy data, so no false `E0` assumption on
the elliptic component is used. -/
theorem stationaryZeroPropagatesByODEUniqueness_of_ode
    {p : Params} {κ M : ℝ}
    (hrealize : StationaryTravelingWaveODERealization p κ M) :
    StationaryZeroPropagatesByODEUniqueness p.toCMParams p.c κ M := by
  intro U hU hstat x₀ hx₀
  rcases hrealize U hU hstat with ⟨z, hz, hzU⟩
  let S : Set ℝ := {x | z x 0 = 0 ∧ z x 1 = 0}
  have hxS : x₀ ∈ S := by
    have hmin : IsLocalMin U x₀ := by
      dsimp [IsLocalMin, IsMinFilter]
      exact Eventually.of_forall fun x => by simpa [hx₀] using hU.nonneg x
    have hfun : (fun x => z x 0) = U := funext hzU
    have hderiv : HasDerivAt U (z x₀ 1) x₀ := by
      simpa [hfun] using hz.hasDerivAt_U x₀
    exact ⟨by simp [hzU x₀, hx₀], hmin.hasDerivAt_eq_zero hderiv⟩
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    let g : ℝ → State := zeroUFiber p y (z y 2) (z y 3)
    have hg : SolvesTWODE p g := zeroUFiber_solves p y (z y 2) (z y 3)
    have hgy : g y = z y := by
      ext i
      fin_cases i
      · exact hy.1.symm
      · exact hy.2.symm
      · simp [g, zeroUFiber]
      · simp [g, zeroUFiber]
    rcases (vectorField_contDiffAt p (z y)).exists_lipschitzOnWith with
      ⟨K, s, hs, hLip⟩
    have hv :
        ∀ᶠ t in 𝓝 y,
          LipschitzOnWith K ((fun _ : ℝ => vectorField p) t) s :=
      Eventually.of_forall fun _ => hLip
    have hzmem : ∀ᶠ t in 𝓝 y, z t ∈ s :=
      hz.differentiable.continuous.continuousAt.eventually hs
    have hgmem : ∀ᶠ t in 𝓝 y, g t ∈ s := by
      have hgcont : Continuous g := hg.differentiable.continuous
      have hs' : s ∈ 𝓝 (g y) := by simpa [hgy] using hs
      exact hgcont.continuousAt.eventually hs'
    have hzev :
        ∀ᶠ t in 𝓝 y,
          HasDerivAt z (((fun _ : ℝ => vectorField p) t) (z t)) t ∧ z t ∈ s :=
      (Eventually.of_forall fun t => hz.hasDerivAt t).and hzmem
    have hgev :
        ∀ᶠ t in 𝓝 y,
          HasDerivAt g (((fun _ : ℝ => vectorField p) t) (g t)) t ∧ g t ∈ s :=
      (Eventually.of_forall fun t => hg.hasDerivAt t).and hgmem
    have hEq : z =ᶠ[𝓝 y] g :=
      ODE_solution_unique_of_eventually
        (v := fun _ : ℝ => vectorField p) (s := fun _ : ℝ => s)
        hv hzev hgev hgy.symm
    filter_upwards [hEq] with t ht
    constructor <;> rw [ht] <;> simp [g, zeroUFiber]
  have hSclosed : IsClosed S := by
    exact (isClosed_eq (hz.component_contDiff_two 0).continuous continuous_const).inter
      (isClosed_eq (hz.component_contDiff_two 1).continuous continuous_const)
  have hSuniv : S = Set.univ :=
    IsClopen.eq_univ (s := S) ⟨hSclosed, hSopen⟩ ⟨x₀, hxS⟩
  intro x
  have hx : x ∈ S := by simp [hSuniv]
  rw [← hzU x]
  exact hx.1

/-- The ODE-uniqueness bridge gives the stationary strong maximum principle:
a nonnegative stationary trapped profile cannot touch zero unless it is the zero
profile, contradicting `ProfileNontrivial`. -/
theorem stationaryStrongMaxPrinciple_of_odeUniqueness
    {p : CMParams} {c κ M : ℝ}
    (huniq : StationaryZeroPropagatesByODEUniqueness p c κ M) :
    StationaryStrongMaxPrinciple p c κ M := by
  intro U hU hstat hnontriv x
  by_contra hnot
  have hx0 : U x = 0 :=
    le_antisymm (not_lt.mp hnot) (hU.nonneg x)
  have hzero : ∀ y, U y = 0 := huniq U hU hstat x hx0
  have hUzero : U = fun _ : ℝ => (0 : ℝ) := funext hzero
  exact not_profileNontrivial_zero (by simpa [hUzero] using hnontriv)

theorem stationaryStrongMaxPrinciple_of_odeRealization
    {p : Params} {κ M : ℝ}
    (hrealize : StationaryTravelingWaveODERealization p κ M) :
    StationaryStrongMaxPrinciple p.toCMParams p.c κ M :=
  stationaryStrongMaxPrinciple_of_odeUniqueness
    (stationaryZeroPropagatesByODEUniqueness_of_ode hrealize)

/-- Formal route (b): monotone left limit + reaction-root + lower-pin. -/
theorem monotoneTrap_profile_hlim_neg_of_limit_root_and_pin
    {κ M : ℝ} (p : CMParams)
    (hroot : ∀ U : ℝ → ℝ, InMonotoneWaveTrapSet κ M U →
      ∀ L : ℝ, Tendsto U atBot (𝓝 L) → reactionFun p.α L = 0)
    (hpin : ∀ U : ℝ → ℝ,
      InMonotoneWaveTrapSet κ M U → StrictlyPositiveAtLeft U) :
    ∀ U : ℝ → ℝ,
      InMonotoneWaveTrapSet κ M U → Tendsto U atBot (𝓝 1) := by
  intro U hU
  rcases monotoneTrap_left_limit_exists hU with ⟨L, hlim, _hL0, _hLM⟩
  have hα : 0 < p.α := lt_of_lt_of_le zero_lt_one p.hα
  have hL : 0 < L := (hpin U hU).limit_pos hlim
  exact tendsto_atBot_one_of_reaction_root_pin hα hlim hL (hroot U hU L hlim)

/-- Route (b) with the lower pin supplied by the usual pointwise positivity
profile obligation.  The remaining input is exactly the stationary-limit
reaction-root fact. -/
theorem monotoneTrap_profile_hlim_neg_of_limit_root_and_pos
    {κ M : ℝ} (p : CMParams)
    (hroot : ∀ U : ℝ → ℝ, InMonotoneWaveTrapSet κ M U →
      ∀ L : ℝ, Tendsto U atBot (𝓝 L) → reactionFun p.α L = 0)
    (hpos : ∀ U : ℝ → ℝ,
      InMonotoneWaveTrapSet κ M U → ∀ x, 0 < U x) :
    ∀ U : ℝ → ℝ,
      InMonotoneWaveTrapSet κ M U → Tendsto U atBot (𝓝 1) :=
  monotoneTrap_profile_hlim_neg_of_limit_root_and_pin p hroot
    (fun U hU => hU.strictlyPositiveAtLeft_of_pos (hpos U hU))

/-- Route (b) with the lower pin supplied by `PaperPositiveInitialDatum`, whose
uniform floor is the faithful paper eq. (1.11) input. -/
theorem monotoneTrap_profile_hlim_neg_of_limit_root_and_floor
    {κ M : ℝ} (p : CMParams)
    (hroot : ∀ U : ℝ → ℝ, InMonotoneWaveTrapSet κ M U →
      ∀ L : ℝ, Tendsto U atBot (𝓝 L) → reactionFun p.α L = 0)
    (hfloor : ∀ U : ℝ → ℝ,
      InMonotoneWaveTrapSet κ M U → PaperPositiveInitialDatum U) :
    ∀ U : ℝ → ℝ,
      InMonotoneWaveTrapSet κ M U → Tendsto U atBot (𝓝 1) :=
  monotoneTrap_profile_hlim_neg_of_limit_root_and_pin p hroot
    (fun U hU => (hfloor U hU).strictlyPositiveAtLeft)

/-- Universal profile obligation from stationary flatness plus an explicit
single-point-positive lower pin. -/
theorem monotoneTrap_profile_hlim_neg_of_stationary_flat_and_lower_pin_at
    {κ M : ℝ} (p : CMParams) (c : ℝ) {φ : ℝ → ℝ} {x₀ : ℝ}
    (hφpos : 0 < φ x₀) :
    ∀ U : ℝ → ℝ,
      InMonotoneWaveTrapSet κ M U →
        (∀ x, φ x ≤ U x) →
          FrozenStationaryFlatAtLeft p U →
            (∀ x, frozenWaveOperator p c U U x = 0) →
              Tendsto U atBot (𝓝 1) :=
  fun _U hU hlower hflat hstat =>
    InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_lower_pin_at
      hU hlower hφpos hflat hstat

/-- Universal profile obligation specialized to the paper raw lower barrier.
This is the route-b `hlim_neg` constructor: monotone bounded left limit,
stationary-flat reaction root, and the raw lower pin rule out the zero root. -/
theorem monotoneTrap_profile_hlim_neg_of_stationary_flat_and_lowerBarrierRaw_pin
    {κ κtilde D M : ℝ} (p : CMParams) (c : ℝ)
    (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D) :
    ∀ U : ℝ → ℝ,
      InMonotoneWaveTrapSet κ M U →
        (∀ x, lowerBarrierRaw κ κtilde D x ≤ U x) →
          FrozenStationaryFlatAtLeft p U →
            (∀ x, frozenWaveOperator p c U U x = 0) →
              Tendsto U atBot (𝓝 1) :=
  fun _U hU hlower hflat hstat =>
    InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_lowerBarrierRaw_pin
      hκ hgap hD hU hlower hflat hstat

/-- Route-b `hlim_neg` for the lower-raw pinned trap: trap membership supplies
the raw lower pin, stationarity passes to the left-limit reaction root, and the
positive raw barrier pin rules out the zero root. -/
theorem monotoneTrap_profile_hlim_neg
    {κ κtilde D M : ℝ} {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D)
    (hU :
      InMonotoneWaveTrapSet κ M U ∧
        ∀ x, lowerBarrierRaw κ κtilde D x ≤ U x)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hflat : FrozenStationaryFlatAtLeft p U) :
    Tendsto U atBot (𝓝 1) := by
  exact InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_lowerBarrierRaw_pin
    hκ hgap hD hU.1 hU.2 hflat hstat

/-- The route-b lower pin is not a monotone-trap fact: the zero profile refutes it. -/
theorem not_monotoneTrap_profile_strictlyPositiveAtLeft
    {κ M : ℝ} (hM : 0 ≤ M) :
    ¬ (∀ U : ℝ → ℝ,
      InMonotoneWaveTrapSet κ M U → StrictlyPositiveAtLeft U) := by
  intro h
  rcases h (fun _ : ℝ => (0 : ℝ))
      (InMonotoneWaveTrapSet.zero (κ := κ) (M := M) hM) with
    ⟨δ, hδ, hδle⟩
  have hδle0 : δ ≤ 0 := by
    exact ge_of_tendsto (f := fun _ : ℝ => (0 : ℝ)) tendsto_const_nhds hδle
  linarith

/-- Strict positivity is not a consequence of monotone-trap membership:
the zero profile is trapped whenever `0 ≤ M`. -/
theorem not_monotoneTrap_profile_hpos {κ M : ℝ} (hM : 0 ≤ M) :
    ¬ (∀ U : ℝ → ℝ,
      InMonotoneWaveTrapSet κ M U → ∀ x, 0 < U x) := by
  intro h
  have h0 : 0 < (0 : ℝ) := by
    simpa using h (fun _ : ℝ => (0 : ℝ))
      (InMonotoneWaveTrapSet.zero (κ := κ) (M := M) hM) 0
  exact (lt_irrefl (0 : ℝ)) h0

/-- The left endpoint limit `U → 1` at `-∞` is not a trap consequence:
the same zero trapped profile would have to tend to both `0` and `1`. -/
theorem not_monotoneTrap_profile_hlim_neg {κ M : ℝ} (hM : 0 ≤ M) :
    ¬ (∀ U : ℝ → ℝ,
      InMonotoneWaveTrapSet κ M U → Tendsto U atBot (𝓝 1)) := by
  intro h
  have hzero : Tendsto (fun _ : ℝ => (0 : ℝ)) atBot (𝓝 1) :=
    h (fun _ : ℝ => (0 : ℝ))
      (InMonotoneWaveTrapSet.zero (κ := κ) (M := M) hM)
  have hconst : Tendsto (fun _ : ℝ => (0 : ℝ)) atBot (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds
  have h01 : (0 : ℝ) = 1 := tendsto_nhds_unique hconst hzero
  norm_num at h01

/-
  STALL REPORT — strict positivity `0 < U x` is NOT a trap-membership fact.

  Target (3),

      inMonotoneWaveTrapSet_pos
        (p : CMParams) (κ M : ℝ) (U : ℝ → ℝ)
        (hU : InMonotoneWaveTrapSet κ M U) (x : ℝ) : 0 < U x,

  does not follow from `InMonotoneWaveTrapSet κ M U` alone.

  Unfolding the definitions (Statements.lean):

    InMonotoneWaveTrapSet κ M u := InWaveTrapSet κ M u ∧ NonincreasingProfile u   (L4377)
    InWaveTrapSet κ M u :=
      IsCUnifBdd u ∧ ∀ x, 0 ≤ u x ∧ u x ≤ upperBarrier κ M x                       (L4371)

  The only lower bound the trap carries is the NON-strict `0 ≤ u x`.  There is
  no lower-barrier component in the membership predicate.  Concretely the zero
  function is a trap member: `InWaveTrapSet.zero` (Statements.lean L4745) proves
  `InWaveTrapSet κ M (fun _ => 0)` for `0 ≤ M`, and it is trivially antitone, so
  `InMonotoneWaveTrapSet κ M (fun _ => 0)` holds while `0 < (fun _ => 0) x` is
  false.  Hence the goal is unprovable from `hU` and is in fact a counterexample.

  The lower barrier `lowerBarrierPlateau κ κtilde D` (Statements.lean L4220),
  which IS strictly positive (`lowerBarrierPlateau_pos`, L4246, needs
  `0 < κ`, `0 < κtilde - κ`, `0 < D`), is used only to EXHIBIT specific trap
  members (`exists_D_gt_lowerBarrierPlateau_mem_InMonotoneWaveTrapSet`, L4968);
  it is not part of trap membership.

  Strict positivity of the constructed wave profile must therefore come from the
  Schauder fixed-point construction / Shen package (where the iterate is pinned
  above the positive lower barrier), supplied to `mk_auto_limits` as the
  hypothesis `hU_pos : ∀ x, 0 < U x` (see the callsite
  `Theorem_1_1.of_raw_frozen_stationary_branches`, Statements.lean L16429,
  which consumes `hU_pos` from the existence proof `hneg`/`hpos`).

  Required extra hypothesis (true one): a strict lower bound on `U`, e.g.
  `∀ x, lowerBarrierPlateau κ κtilde D x ≤ U x` together with the plateau
  positivity, or directly `∀ x, 0 < U x` from the construction.  None of these
  is available from `InMonotoneWaveTrapSet κ M U`.

  STALL REPORT — `hGreen` is likewise not a trap-membership fact.

  Target shape:

      ∀ U, InMonotoneWaveTrapSet κ M U →
        rotheLimit (rotheSeq U) = U → GreenIdentity p c lam U

  The trap supplies only continuity, boundedness, nonnegativity, upper-barrier
  control, and antitonicity.  `GreenIdentity` is the variation-of-parameters
  identity for `auxMap`, and the committed closing theorem is
  `greenIdentity_holds`, which additionally needs source continuity, the two
  weighted Green-tail integrability hypotheses, and the convolution
  representation of `auxMap`.  None of those data are fields of
  `InMonotoneWaveTrapSet`, and the fixed-point equality of the Rothe limit is not
  itself a convolution representation.  Thus `hGreen` remains the genuine
  Green-representation frontier.
-/

section AxiomAudit
#print axioms monotoneTrap_profile_hbdd
#print axioms monotoneTrap_profile_hlim_pos
#print axioms PaperPositiveInitialDatum.pos
#print axioms not_profileNontrivial_zero
#print axioms frozenWaveOperator_zero_eq_zero
#print axioms stationaryJet_zero_of_gronwall_right
#print axioms stationaryProfile_strictlyPositive_of_linearGronwall
#print axioms stationaryLinearGronwallProfileData_of_second_deriv_abs_le
#print axioms stationaryLinearGronwallProfileData_of_trap
#print axioms stationaryProfile_strictlyPositive_of_trap_regularity
#print axioms stationaryProfile_strictlyBelow_one_of_chi_zero_trap_regularity
#print axioms stationaryStrongMaxPrinciple_of_linearGronwall
#print axioms stationaryC2Regularity_of_greenRepresentation
#print axioms stationaryC2Regularity_of_crossImplicitMap_fixed
#print axioms stationaryC2RegularityFromEquation_of_trap
#print axioms stationaryStrongMaxPrinciple_of_trap
#print axioms not_monotoneTrap_profile_paperPositiveInitialDatum
#print axioms monotoneTrap_profile_hpos_of_floor
#print axioms monotoneTrap_left_limit_exists
#print axioms StrictlyPositiveAtLeft.limit_pos
#print axioms reactionFun_root_eq_one_of_pos
#print axioms tendsto_atBot_one_of_reaction_root_pin
#print axioms InMonotoneWaveTrapSet.strictlyPositiveAtLeft_of_pos
#print axioms InMonotoneWaveTrapSet.strictlyPositiveAtLeft_of_lower_pin_at
#print axioms InMonotoneWaveTrapSet.tendsto_atBot_one_of_limit_root_and_pos
#print axioms InMonotoneWaveTrapSet.tendsto_atBot_one_of_limit_root_and_lower_pin_at
#print axioms InMonotoneWaveTrapSet.tendsto_atBot_one_of_limit_root_and_floor
#print axioms reactionFun_root_of_stationary_flat_limit
#print axioms reactionFun_root_of_stationary_equation_atBot_limit
#print axioms InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_floor
#print axioms InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_lower_pin_at
#print axioms InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_lowerBarrierRaw_pin
#print axioms InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_pos
#print axioms InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_nontrivial
#print axioms stationaryStrongMaxPrinciple_of_odeUniqueness
#print axioms stationaryZeroPropagatesByODEUniqueness_of_ode
#print axioms stationaryStrongMaxPrinciple_of_odeRealization
#print axioms monotoneTrap_profile_hlim_neg_of_limit_root_and_pin
#print axioms monotoneTrap_profile_hlim_neg_of_limit_root_and_pos
#print axioms monotoneTrap_profile_hlim_neg_of_limit_root_and_floor
#print axioms monotoneTrap_profile_hlim_neg_of_stationary_flat_and_lower_pin_at
#print axioms monotoneTrap_profile_hlim_neg_of_stationary_flat_and_lowerBarrierRaw_pin
#print axioms monotoneTrap_profile_hlim_neg
#print axioms not_monotoneTrap_profile_strictlyPositiveAtLeft
#print axioms not_monotoneTrap_profile_hpos
#print axioms not_monotoneTrap_profile_hlim_neg
end AxiomAudit

end ShenWork.Paper1
