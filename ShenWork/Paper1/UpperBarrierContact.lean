/-
  Paper1 positive upper-barrier contact refinements.

  This file keeps the statement assembly lean: it imports the existing
  kink-avoidance lemma only here, then exposes a narrower no-contact frontier for
  the two smooth branches of the positive upper barrier.
-/
import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper1.WaveRotheMaxPrincipleClosers
import ShenWork.Paper1.WaveRotheResidualClose

open Filter Topology

namespace ShenWork.Paper1

noncomputable section

/-- The remaining analytic atom for the positive branch after the interface kink
is discharged by differentiability. -/
def PositiveUpperBarrierSmoothBranchNoContact
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop :=
  (∀ x, MChi p < Real.exp (-(kappa c) * x) →
      U x = MChi p → False) ∧
  (∀ x, Real.exp (-(kappa c) * x) < MChi p →
      U x = Real.exp (-(kappa c) * x) → False)

/-- Assemble the full contact-contradiction record from smooth-branch
no-contact plus an interface no-contact proof. -/
theorem PositiveUpperBarrierContactContradictions.of_smoothBranchNoContact
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hsmooth : PositiveUpperBarrierSmoothBranchNoContact p c U)
    (hinterface :
      ∀ x, Real.exp (-(kappa c) * x) = MChi p →
        U x = MChi p → False) :
    PositiveUpperBarrierContactContradictions p c U :=
  { const_branch := hsmooth.1
    exp_branch := hsmooth.2
    interface := hinterface }

/-- A differentiable trapped profile cannot touch a `min(M, exp(-κx))` upper
barrier at its nonsmooth interface. -/
theorem upperBarrier_interfaceNoContact_of_profile_differentiable
    {κ M : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < κ) (hM : 0 < M)
    (htrap : InMonotoneWaveTrapSet κ M U)
    (hUdiff : Differentiable ℝ U) :
    ∀ x, Real.exp (-κ * x) = M → U x = M → False := by
  intro x hx hUx
  have hbarrier_x : upperBarrier κ M x = M :=
    upperBarrier_eq_M_of_le_exp hx.ge
  have hmax : IsLocalMax (fun y => U y - upperBarrier κ M y) x := by
    dsimp [IsLocalMax, IsMaxFilter]
    refine Filter.Eventually.of_forall fun y => ?_
    have hy : U y - upperBarrier κ M y ≤ 0 :=
      sub_nonpos.mpr (htrap.le_upperBarrier y)
    have hx0 : U x - upperBarrier κ M x = 0 := by
      rw [hUx, hbarrier_x, sub_self]
    simpa [hx0] using hy
  exact maxSub_upperBarrier_ne_interface
    hκ hM (hUdiff x) hmax hx

/-- A differentiable trapped profile cannot touch the positive upper barrier at
the nonsmooth interface.  This reuses the existing kink-avoidance lemma for
local maxima of `U - upperBarrier`. -/
theorem positiveUpperBarrier_interfaceNoContact_of_profile_differentiable
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < kappa c) (hM : 0 < MChi p)
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U)
    (hUdiff : Differentiable ℝ U) :
    ∀ x, Real.exp (-(kappa c) * x) = MChi p →
      U x = MChi p → False := by
  intro x hx hUx
  have hbarrier_x :
      upperBarrier (kappa c) (MChi p) x = MChi p :=
    upperBarrier_eq_M_of_le_exp hx.ge
  have hmax :
      IsLocalMax
        (fun y => U y - upperBarrier (kappa c) (MChi p) y) x := by
    dsimp [IsLocalMax, IsMaxFilter]
    refine Filter.Eventually.of_forall fun y => ?_
    have hy : U y - upperBarrier (kappa c) (MChi p) y ≤ 0 :=
      sub_nonpos.mpr (htrap.le_upperBarrier y)
    have hx0 :
        U x - upperBarrier (kappa c) (MChi p) x = 0 := by
      rw [hUx, hbarrier_x, sub_self]
    simpa [hx0] using hy
  exact
    maxSub_upperBarrier_ne_interface
      (κ := kappa c) (M := MChi p) (W := U) (x := x)
      hκ hM (hUdiff x) hmax hx

theorem positiveUpperBarrier_interfaceNoContact_of_regular_stationary
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < kappa c) (hM : 0 < MChi p)
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hreg : StationaryC2RegularityFromEquation p c (kappa c) (MChi p)) :
    ∀ x, Real.exp (-(kappa c) * x) = MChi p →
      U x = MChi p → False :=
  positiveUpperBarrier_interfaceNoContact_of_profile_differentiable
    hκ hM htrap (hreg U htrap hstat).1

/-- Regular stationary data discharges the interface field, so only the two
smooth-branch no-contact facts remain. -/
theorem PositiveUpperBarrierContactContradictions.of_smoothBranchNoContact_regularStationary
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hsmooth : PositiveUpperBarrierSmoothBranchNoContact p c U)
    (hκ : 0 < kappa c) (hM : 0 < MChi p)
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hreg : StationaryC2RegularityFromEquation p c (kappa c) (MChi p)) :
    PositiveUpperBarrierContactContradictions p c U :=
  PositiveUpperBarrierContactContradictions.of_smoothBranchNoContact hsmooth
    (positiveUpperBarrier_interfaceNoContact_of_regular_stationary
      hκ hM htrap hstat hreg)

/-- Construction-site interface closure using regularity of the selected
profile only. -/
theorem PositiveUpperBarrierContactContradictions.of_smoothBranchNoContact_profile
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hsmooth : PositiveUpperBarrierSmoothBranchNoContact p c U)
    (hκ : 0 < kappa c) (hM : 0 < MChi p)
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U)
    (hUdiff : Differentiable ℝ U) :
    PositiveUpperBarrierContactContradictions p c U :=
  PositiveUpperBarrierContactContradictions.of_smoothBranchNoContact hsmooth
    (positiveUpperBarrier_interfaceNoContact_of_profile_differentiable
      hκ hM htrap hUdiff)

/-- Constant-branch contact with the upper trap level forces a full left
plateau by monotonicity. -/
theorem constBranch_contact_forces_left_plateau
    {κ M : ℝ} {U : ℝ → ℝ}
    (htrap : InMonotoneWaveTrapSet κ M U)
    {x : ℝ} (hUx : U x = M) :
    ∀ y, y ≤ x → U y = M := by
  intro y hy
  exact le_antisymm
    (htrap.le_M y)
    (by
      have hmono : U x ≤ U y := htrap.antitone hy
      simpa [hUx] using hmono)

/-- A profile tending to `1` at `-∞` cannot have a left plateau at a distinct
level `MChi p`. -/
theorem no_const_left_plateau_of_tendsto_atBot_one
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hlim : Tendsto U atBot (𝓝 (1 : ℝ)))
    (hMne : MChi p ≠ 1) :
    ∀ x, MChi p < Real.exp (-(kappa c) * x) →
      (∀ y, y ≤ x → U y = MChi p) → False := by
  intro x _hx hplateau
  have hev : U =ᶠ[atBot] fun _ : ℝ => MChi p := by
    exact eventually_atBot.2 ⟨x, fun y hy => hplateau y hy⟩
  have hlimM : Tendsto U atBot (𝓝 (MChi p)) :=
    tendsto_const_nhds.congr' (hev.mono fun _ hy => hy.symm)
  have hEq : (1 : ℝ) = MChi p := tendsto_nhds_unique hlim hlimM
  exact hMne hEq.symm

/-- Strictly positive sensitivity pushes the positive-branch normalization above
`1`. -/
theorem one_lt_MChi_of_chi_pos_lt_one
    (p : CMParams) (hχ_pos : 0 < p.χ) (hχ_lt : p.χ < 1) :
    1 < MChi p := by
  have hden_pos : 0 < 1 - p.χ := by linarith
  have hbase_gt : 1 < 1 / (1 - p.χ) := by
    rw [lt_div_iff₀ hden_pos]
    linarith
  have hα_pos : 0 < p.α := lt_of_lt_of_le zero_lt_one p.hα
  have hexp_pos : 0 < 1 / p.α := div_pos one_pos hα_pos
  rw [MChi_eq_rpow_of_chi_pos p hχ_pos]
  exact Real.one_lt_rpow hbase_gt hexp_pos

theorem MChi_ne_one_of_chi_pos_lt_one
    (p : CMParams) (hχ_pos : 0 < p.χ) (hχ_lt : p.χ < 1) :
    MChi p ≠ 1 :=
  ne_of_gt (one_lt_MChi_of_chi_pos_lt_one p hχ_pos hχ_lt)

/-- The left-end profile limit discharges the constant-branch residual when
`MChi p` is forced away from `1`. -/
theorem no_const_left_plateau_of_profile_chi_pos
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hprofile : FrozenStationaryWaveProfile p c U)
    (hχ_pos : 0 < p.χ) (hχ_lt : p.χ < 1) :
    ∀ x, MChi p < Real.exp (-(kappa c) * x) →
      (∀ y, y ≤ x → U y = MChi p) → False :=
  no_const_left_plateau_of_tendsto_atBot_one
    hprofile.lim_neg_inf.1
    (MChi_ne_one_of_chi_pos_lt_one p hχ_pos hχ_lt)

/-- Pointwise second-derivative comparison against the exponential branch from
a local maximum of `U - expDecay κ`.

The regularity frontier supplies differentiability of `U` and of `deriv U`, but
not a `ContDiffAt ℝ 2 U x` package.  This bridge proves only the derivative
linearity needed at the point. -/
theorem iteratedDeriv2_le_expDecay_of_isLocalMax_sub
    {U : ℝ → ℝ} {κ x : ℝ}
    (hUdiff : Differentiable ℝ U)
    (hUd_diff : Differentiable ℝ (deriv U))
    (hmax : IsLocalMax (fun y => U y - expDecay κ y) x) :
    iteratedDeriv 2 U x ≤ iteratedDeriv 2 (expDecay κ) x := by
  have hUcont : ContinuousAt U x := (hUdiff x).continuousAt
  have hBcont : ContinuousAt (expDecay κ) x :=
    (expDecay_hasDerivAt κ x).continuousAt
  have hc : ContinuousAt (fun y => U y - expDecay κ y) x :=
    hUcont.sub hBcont
  have hnonpos :=
    iteratedDeriv2_nonpos_of_isLocalMax hmax hc
  have hderiv_sub_fun :
      deriv (fun y => U y - expDecay κ y) =
        fun y => deriv U y - deriv (expDecay κ) y := by
    funext y
    exact deriv_sub (hUdiff y)
      ((expDecay_hasDerivAt κ y).differentiableAt)
  have hExpDerivEq :
      deriv (expDecay κ) = fun y => -κ * expDecay κ y := by
    funext y
    exact expDecay_deriv κ y
  have hExpDerivDiff :
      DifferentiableAt ℝ (deriv (expDecay κ)) x := by
    rw [hExpDerivEq]
    exact ((expDecay_hasDerivAt κ x).const_mul (-κ)).differentiableAt
  have hsecond :
      deriv (fun y => deriv U y - deriv (expDecay κ) y) x =
        deriv (deriv U) x - deriv (deriv (expDecay κ)) x :=
    deriv_sub (hUd_diff x) hExpDerivDiff
  have hlin :
      iteratedDeriv 2 (fun y => U y - expDecay κ y) x =
        iteratedDeriv 2 U x - iteratedDeriv 2 (expDecay κ) x := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
    rw [hderiv_sub_fun]
    simpa [iteratedDeriv_succ, iteratedDeriv_zero] using hsecond
  rw [hlin] at hnonpos
  linarith

/-- At an exponential-branch contact, the stationary trapped profile is below
the frozen operator applied to the upper barrier.  This closes the
`exp_operator_compare_at_contact` field from trap membership, stationarity, and
the C² regularity frontier; no Route-A lower-pin data is used. -/
theorem positiveUpperBarrier_expOperatorCompareAtContact_of_profile_regularity
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hM0 : 0 ≤ MChi p)
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U)
    (hUdiff : Differentiable ℝ U)
    (hUd_diff : Differentiable ℝ (deriv U)) :
    ∀ x, Real.exp (-(kappa c) * x) < MChi p →
      U x = Real.exp (-(kappa c) * x) →
        frozenWaveOperator p c U U x ≤
          frozenWaveOperator p c U
            (upperBarrier (kappa c) (MChi p)) x := by
  intro x hx hUx
  let κ := kappa c
  have hxExp : expDecay κ x < MChi p := by
    simpa [κ, expDecay] using hx
  have hUx_exp : U x = expDecay κ x := by
    simpa [κ, expDecay] using hUx
  have hEqExp :
      upperBarrier κ (MChi p) =ᶠ[𝓝 x] expDecay κ :=
    upperBarrier_eventuallyEq_exp_of_lt (κ := κ) (M := MChi p) hx
  have hmax : IsLocalMax (fun y => U y - expDecay κ y) x := by
    dsimp [IsLocalMax, IsMaxFilter]
    have hx0 : U x - expDecay κ x = 0 := by
      rw [hUx_exp, sub_self]
    filter_upwards [hEqExp] with y hy
    have hy_le : U y - upperBarrier κ (MChi p) y ≤ 0 :=
      sub_nonpos.mpr (htrap.le_upperBarrier y)
    have hy_le_exp : U y - expDecay κ y ≤ 0 := by
      simpa [hy] using hy_le
    simpa [hx0] using hy_le_exp
  have hφderiv :
      deriv (fun y => U y - expDecay κ y) x = 0 :=
    hmax.deriv_eq_zero
  have hderiv_sub :
      deriv (fun y => U y - expDecay κ y) x =
        deriv U x - deriv (expDecay κ) x :=
    deriv_sub (hUdiff x)
      ((expDecay_hasDerivAt κ x).differentiableAt)
  have hderiv1 : deriv U x = deriv (expDecay κ) x := by
    rw [hderiv_sub] at hφderiv
    linarith
  have hderiv2 :
      iteratedDeriv 2 U x ≤ iteratedDeriv 2 (expDecay κ) x :=
    iteratedDeriv2_le_expDecay_of_isLocalMax_sub
      hUdiff hUd_diff hmax
  have hWmem : U x ∈ Set.Icc (0 : ℝ) (MChi p) :=
    ⟨htrap.nonneg x, htrap.le_M x⟩
  have hBmem : expDecay κ x ∈ Set.Icc (0 : ℝ) (MChi p) :=
    ⟨(expDecay_pos κ x).le, le_of_lt hxExp⟩
  have hBW : expDecay κ x ≤ U x := by
    exact le_of_eq hUx_exp.symm
  have hchem_zero :
      deriv (chemFlux p U U) x - deriv (chemFlux p U (expDecay κ)) x = 0 := by
    have hsplit :=
      chemFlux_increment_split (p := p) (u := U) (W := U)
        (B := expDecay κ) (x₀ := x)
        htrap.trap.cunif_bdd htrap.nonneg
        (hUdiff x) ((expDecay_hasDerivAt κ x).differentiableAt)
        hderiv1
    have hpow_m1 :
        (U x) ^ (p.m - 1) - (expDecay κ x) ^ (p.m - 1) = 0 := by
      rw [hUx_exp]
      ring
    have hpow_m :
        (U x) ^ p.m - (expDecay κ x) ^ p.m = 0 := by
      rw [hUx_exp]
      ring
    rw [hsplit, hpow_m1, hpow_m]
    ring
  have hchem :
      -p.χ *
          (deriv (chemFlux p U U) x -
            deriv (chemFlux p U (expDecay κ)) x)
        ≤ (0 : ℝ) * (U x - expDecay κ x) := by
    rw [hchem_zero]
    ring_nf
    exact le_rfl
  have hstep :=
    implicitStep_oneSided_max_estimate (p := p) (c := c)
      (M := MChi p) (C_chem := 0) (u := U)
      (W := U) (B := expDecay κ) (x₀ := x)
      hM0 hWmem hBmem hBW hderiv1 hderiv2 hchem
  have hdiff_le0 :
      frozenWaveOperator p c U U x -
        frozenWaveOperator p c U (expDecay κ) x ≤ 0 := by
    simpa [hUx_exp] using hstep
  have hle_exp :
      frozenWaveOperator p c U U x ≤
        frozenWaveOperator p c U (expDecay κ) x := by
    linarith
  rw [frozenWaveOperator_upperBarrier_exp_region_eq
    (p := p) (c := c) (κ := κ) (M := MChi p) (u := U) (x := x) hxExp]
  exact hle_exp

/-- Universal regularity wrapper for the profile-wise contact comparison. -/
theorem positiveUpperBarrier_expOperatorCompareAtContact_of_regular_stationary
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hM0 : 0 ≤ MChi p)
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hreg : StationaryC2RegularityFromEquation p c (kappa c) (MChi p)) :
    ∀ x, Real.exp (-(kappa c) * x) < MChi p →
      U x = Real.exp (-(kappa c) * x) →
        frozenWaveOperator p c U U x ≤
          frozenWaveOperator p c U
            (upperBarrier (kappa c) (MChi p)) x := by
  rcases hreg U htrap hstat with ⟨hUdiff, hUd_diff⟩
  exact positiveUpperBarrier_expOperatorCompareAtContact_of_profile_regularity
    hM0 htrap hUdiff hUd_diff

/-- Finer smooth-branch frontier for the positive upper barrier.

The constant branch is reduced to a no-left-plateau statement.  The exponential
branch is now reduced only to strict upper super-barrier residual at contact:
the operator comparison is closed above from regular stationary data. -/
structure PositiveUpperBarrierRemainingContactResidual
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop where
  no_const_left_plateau :
    ∀ x, MChi p < Real.exp (-(kappa c) * x) →
      (∀ y, y ≤ x → U y = MChi p) → False
  exp_strict_super_at_contact :
    ∀ x, Real.exp (-(kappa c) * x) < MChi p →
      U x = Real.exp (-(kappa c) * x) →
        frozenWaveOperator p c U
          (upperBarrier (kappa c) (MChi p)) x < 0

/-- The constant-branch part of the remaining upper-contact residual. -/
structure PositiveUpperBarrierConstLeftPlateauResidual
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop where
  no_const_left_plateau :
    ∀ x, MChi p < Real.exp (-(kappa c) * x) →
      (∀ y, y ≤ x → U y = MChi p) → False

/-- Under `0 < χ`, the constant-branch residual is discharged from the profile
limit, so only strict exponential contact remains. -/
structure PositiveUpperBarrierExpStrictContactResidual
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop where
  exp_strict_super_at_contact :
    ∀ x, Real.exp (-(kappa c) * x) < MChi p →
      U x = Real.exp (-(kappa c) * x) →
        frozenWaveOperator p c U
          (upperBarrier (kappa c) (MChi p)) x < 0

/-- Positive branch data in the exponential region produces the strict
upper-barrier residual at contact.  The equality `U x = exp (-κ x)` is unused:
strictness comes from the scalar budget `p.χ < 1` and the standard positive
superbarrier side condition `p.m * kappa c ≤ 1`. -/
theorem positiveUpperBarrier_expStrictSuperAtContact_of_positive_region
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hα : p.α = p.m + p.γ - 1)
    (hχ_nonneg : 0 ≤ p.χ)
    (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    (hc : 2 < c)
    (hmκ : p.m * kappa c ≤ 1)
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U) :
    PositiveUpperBarrierExpStrictContactResidual p c U := by
  refine ⟨?_⟩
  intro x hx _hUx
  have hχ_half : p.χ < (1 / 2 : ℝ) :=
    lt_of_lt_of_le hχ_small (min_le_left _ _)
  have hχ_lt_one : p.χ < 1 := by
    linarith
  have hx_exp : expDecay (kappa c) x < MChi p := by
    simpa [expDecay] using hx
  exact
    frozenWaveOperator_upperBarrier_exp_region_neg_of_chi_nonneg
      p (le_of_lt hc) rfl hχ_nonneg hχ_lt_one hα
      (kappa_pos_of_two_lt hc).le hmκ hx_exp htrap.trap
      (frozenElliptic_deriv_differentiableAt p
        htrap.trap.cunif_bdd htrap.nonneg x)

/-- A profile with `χ > 0` supplies the constant-branch residual. -/
theorem PositiveUpperBarrierConstLeftPlateauResidual.of_profile_chi_pos
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hprofile : FrozenStationaryWaveProfile p c U)
    (hχ_pos : 0 < p.χ) (hχ_lt : p.χ < 1) :
    PositiveUpperBarrierConstLeftPlateauResidual p c U :=
  { no_const_left_plateau :=
      no_const_left_plateau_of_profile_chi_pos
        hprofile hχ_pos hχ_lt }

/-- Constant-branch residual plus the positive-region strict exponential
superbarrier close the full remaining smooth-contact residual on the `hmκ`
subregime. -/
theorem PositiveUpperBarrierRemainingContactResidual.of_constLeftPlateau_positiveRegion
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hα : p.α = p.m + p.γ - 1)
    (hχ_nonneg : 0 ≤ p.χ)
    (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    (hc : 2 < c)
    (hmκ : p.m * kappa c ≤ 1)
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U)
    (hconst : PositiveUpperBarrierConstLeftPlateauResidual p c U) :
    PositiveUpperBarrierRemainingContactResidual p c U :=
  { no_const_left_plateau := hconst.no_const_left_plateau
    exp_strict_super_at_contact :=
      (positiveUpperBarrier_expStrictSuperAtContact_of_positive_region
        hα hχ_nonneg hχ_small hc hmκ htrap).exp_strict_super_at_contact }

/-- Profile convergence and the positive-region strict superbarrier close the
entire remaining smooth-contact residual, provided the scalar branch also has
`p.m * kappa c ≤ 1`. -/
theorem PositiveUpperBarrierRemainingContactResidual.of_positive_region_profile_chi_pos
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hα : p.α = p.m + p.γ - 1)
    (hχ_pos : 0 < p.χ)
    (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    (hc : 2 < c)
    (hmκ : p.m * kappa c ≤ 1)
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U)
    (hprofile : FrozenStationaryWaveProfile p c U) :
    PositiveUpperBarrierRemainingContactResidual p c U := by
  have hχ_half : p.χ < (1 / 2 : ℝ) :=
    lt_of_lt_of_le hχ_small (min_le_left _ _)
  have hχ_lt_one : p.χ < 1 := by
    linarith
  exact
    PositiveUpperBarrierRemainingContactResidual.of_constLeftPlateau_positiveRegion
      hα hχ_pos.le hχ_small hc hmκ htrap
      (PositiveUpperBarrierConstLeftPlateauResidual.of_profile_chi_pos
        hprofile hχ_pos hχ_lt_one)

/-- Profile plus strict positive sensitivity narrows the smooth-contact residual
to the strict exponential-contact field alone. -/
theorem PositiveUpperBarrierRemainingContactResidual.of_expStrict_profile_chi_pos
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hprofile : FrozenStationaryWaveProfile p c U)
    (hχ_pos : 0 < p.χ) (hχ_lt : p.χ < 1)
    (hstrict : PositiveUpperBarrierExpStrictContactResidual p c U) :
    PositiveUpperBarrierRemainingContactResidual p c U :=
  { no_const_left_plateau :=
      no_const_left_plateau_of_profile_chi_pos
        hprofile hχ_pos hχ_lt
    exp_strict_super_at_contact :=
      hstrict.exp_strict_super_at_contact }

@[deprecated PositiveUpperBarrierRemainingContactResidual (since := "2026-06-29")]
abbrev PositiveUpperBarrierSmoothBranchResidual :=
  PositiveUpperBarrierRemainingContactResidual

/-- The finer smooth-branch residual assembles the original smooth no-contact
pair. -/
theorem positiveUpperBarrierSmoothBranchNoContact_of_remainingResidual
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hM0 : 0 ≤ MChi p)
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hreg : StationaryC2RegularityFromEquation p c (kappa c) (MChi p))
    (hres : PositiveUpperBarrierRemainingContactResidual p c U) :
    PositiveUpperBarrierSmoothBranchNoContact p c U := by
  constructor
  · intro x hx hUx
    exact hres.no_const_left_plateau x hx
      (constBranch_contact_forces_left_plateau htrap hUx)
  · intro x hx hUx
    have hcmp :=
      positiveUpperBarrier_expOperatorCompareAtContact_of_regular_stationary
        (p := p) (c := c) (U := U) hM0 htrap hstat hreg x hx hUx
    have hstrict := hres.exp_strict_super_at_contact x hx hUx
    have hnonneg :
        0 ≤ frozenWaveOperator p c U
          (upperBarrier (kappa c) (MChi p)) x := by
      simpa [hstat x] using hcmp
    exact (not_lt_of_ge hnonneg) hstrict

/-- Profile-wise regularity version used at the Route-A construction site. -/
theorem positiveUpperBarrierSmoothBranchNoContact_of_remainingResidual_profile
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hM0 : 0 ≤ MChi p)
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hUdiff : Differentiable ℝ U)
    (hUd_diff : Differentiable ℝ (deriv U))
    (hres : PositiveUpperBarrierRemainingContactResidual p c U) :
    PositiveUpperBarrierSmoothBranchNoContact p c U := by
  constructor
  · intro x hx hUx
    exact hres.no_const_left_plateau x hx
      (constBranch_contact_forces_left_plateau htrap hUx)
  · intro x hx hUx
    have hcmp :=
      positiveUpperBarrier_expOperatorCompareAtContact_of_profile_regularity
        hM0 htrap hUdiff hUd_diff x hx hUx
    have hstrict := hres.exp_strict_super_at_contact x hx hUx
    have hnonneg :
        0 ≤ frozenWaveOperator p c U
          (upperBarrier (kappa c) (MChi p)) x := by
      simpa [hstat x] using hcmp
    exact (not_lt_of_ge hnonneg) hstrict

@[deprecated positiveUpperBarrierSmoothBranchNoContact_of_remainingResidual
  (since := "2026-06-29")]
theorem positiveUpperBarrierSmoothBranchNoContact_of_residual
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hM0 : 0 ≤ MChi p)
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hreg : StationaryC2RegularityFromEquation p c (kappa c) (MChi p))
    (hres : PositiveUpperBarrierRemainingContactResidual p c U) :
    PositiveUpperBarrierSmoothBranchNoContact p c U :=
  positiveUpperBarrierSmoothBranchNoContact_of_remainingResidual
    hM0 htrap hstat hreg hres

/-- On the strict positive-sensitivity route, profile convergence closes the
constant-branch contact residual, so smooth no-contact needs only strict
exponential contact. -/
theorem positiveUpperBarrierSmoothBranchNoContact_of_expStrict_profile_chi_pos
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U)
    (hprofile : FrozenStationaryWaveProfile p c U)
    (hχ_pos : 0 < p.χ) (hχ_lt : p.χ < 1)
    (hreg : StationaryC2RegularityFromEquation p c (kappa c) (MChi p))
    (hstrict : PositiveUpperBarrierExpStrictContactResidual p c U) :
    PositiveUpperBarrierSmoothBranchNoContact p c U :=
  positiveUpperBarrierSmoothBranchNoContact_of_remainingResidual
    (MChi_pos_of_chi_lt_one p hχ_lt).le
    htrap hprofile.stationary_eq hreg
    (PositiveUpperBarrierRemainingContactResidual.of_expStrict_profile_chi_pos
      hprofile hχ_pos hχ_lt hstrict)

/-- On the `hmκ` subregime, the strict positive-sensitivity route closes smooth
no-contact directly from profile convergence, trap membership, and regularity. -/
theorem positiveUpperBarrierSmoothBranchNoContact_of_positive_region_profile_chi_pos
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hα : p.α = p.m + p.γ - 1)
    (hχ_pos : 0 < p.χ)
    (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    (hc : 2 < c)
    (hmκ : p.m * kappa c ≤ 1)
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U)
    (hprofile : FrozenStationaryWaveProfile p c U)
    (hreg : StationaryC2RegularityFromEquation p c (kappa c) (MChi p)) :
    PositiveUpperBarrierSmoothBranchNoContact p c U := by
  exact
    positiveUpperBarrierSmoothBranchNoContact_of_remainingResidual
      (MChi_pos_of_chi_lt_one p
        (by
          have hχ_half : p.χ < (1 / 2 : ℝ) :=
            lt_of_lt_of_le hχ_small (min_le_left _ _)
          linarith)).le
      htrap hprofile.stationary_eq hreg
      (PositiveUpperBarrierRemainingContactResidual.of_positive_region_profile_chi_pos
        hα hχ_pos hχ_small hc hmκ htrap hprofile)

/-- Strict positive sensitivity and strict exponential contact close the full
upper-barrier no-contact package once the regular stationary data are present. -/
theorem PositiveUpperBarrierContactContradictions.of_expStrict_profile_chi_pos_regularStationary
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < kappa c)
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U)
    (hprofile : FrozenStationaryWaveProfile p c U)
    (hχ_pos : 0 < p.χ) (hχ_lt : p.χ < 1)
    (hreg : StationaryC2RegularityFromEquation p c (kappa c) (MChi p))
    (hstrict : PositiveUpperBarrierExpStrictContactResidual p c U) :
    PositiveUpperBarrierContactContradictions p c U :=
  PositiveUpperBarrierContactContradictions.of_smoothBranchNoContact_regularStationary
    (positiveUpperBarrierSmoothBranchNoContact_of_expStrict_profile_chi_pos
      htrap hprofile hχ_pos hχ_lt hreg hstrict)
    hκ
    (MChi_pos_of_chi_lt_one p hχ_lt)
    htrap hprofile.stationary_eq hreg

/-- On the `hmκ` subregime, the positive upper-barrier contact package is
closed without any explicit smooth-contact residual field. -/
theorem PositiveUpperBarrierContactContradictions.of_profile_chi_pos_hmk_regularStationary
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hα : p.α = p.m + p.γ - 1)
    (hχ_pos : 0 < p.χ)
    (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    (hc : 2 < c)
    (hmκ : p.m * kappa c ≤ 1)
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U)
    (hprofile : FrozenStationaryWaveProfile p c U)
    (hreg : StationaryC2RegularityFromEquation p c (kappa c) (MChi p)) :
    PositiveUpperBarrierContactContradictions p c U :=
  PositiveUpperBarrierContactContradictions.of_smoothBranchNoContact_regularStationary
    (positiveUpperBarrierSmoothBranchNoContact_of_positive_region_profile_chi_pos
      hα hχ_pos hχ_small hc hmκ htrap hprofile hreg)
    (kappa_pos_of_two_lt hc)
    (MChi_pos_of_chi_lt_one p
      (by
        have hχ_half : p.χ < (1 / 2 : ℝ) :=
          lt_of_lt_of_le hχ_small (min_le_left _ _)
        linarith))
    htrap hprofile.stationary_eq hreg

/-- Positive critical branch data that preserves the raw lower pin and carries
only the truly remaining smooth-contact residual.  The exponential-branch
operator comparison is produced from the regular stationary data. -/
structure Paper1PositiveLowerPinnedRawRemainingContactBranchData : Prop where
  produce :
    ∀ p : CMParams, p.α = p.m + p.γ - 1 →
      0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
      ∀ c : ℝ, 2 < c →
        ∃ κtilde D : ℝ, ∃ U : ℝ → ℝ,
          0 ≤ D ∧
          positiveBranchTailCap p c ≤ κtilde ∧
          FrozenStationaryWaveProfile p c U ∧
          InLowerPinnedMonotoneTrap (kappa c) (MChi p)
            (lowerBarrierRaw (kappa c) κtilde D) U ∧
          PositiveUpperBarrierRemainingContactResidual p c U ∧
          Differentiable ℝ U ∧ Differentiable ℝ (deriv U)

/-- Positive critical branch data that preserves the current raw lower pin and
carries only smooth-branch no-contact; the interface is discharged from
regularity. -/
structure Paper1PositiveLowerPinnedRawSmoothContactBranchData : Prop where
  produce :
    ∀ p : CMParams, p.α = p.m + p.γ - 1 →
      0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
      ∀ c : ℝ, 2 < c →
        ∃ κtilde D : ℝ, ∃ U : ℝ → ℝ,
          0 ≤ D ∧
          positiveBranchTailCap p c ≤ κtilde ∧
          FrozenStationaryWaveProfile p c U ∧
          InLowerPinnedMonotoneTrap (kappa c) (MChi p)
            (lowerBarrierRaw (kappa c) κtilde D) U ∧
          PositiveUpperBarrierSmoothBranchNoContact p c U ∧
          Differentiable ℝ U ∧ Differentiable ℝ (deriv U)

/-- Remaining-contact raw data produces the previous smooth-contact package by
closing the exponential operator comparison from regular stationarity. -/
theorem paper1_positiveLowerPinnedRawSmoothContactData_of_remainingContactData
    (hData : Paper1PositiveLowerPinnedRawRemainingContactBranchData) :
    Paper1PositiveLowerPinnedRawSmoothContactBranchData := by
  refine ⟨?_⟩
  intro p hα hχ_nonneg hχ_small c hc
  rcases hData.produce p hα hχ_nonneg hχ_small c hc with
    ⟨κtilde, D, U, hD, hcover, hprofile, hpin, hres,
      hUdiff, hUderivDiff⟩
  have hχ_star : p.χ < chiStar p :=
    lt_of_lt_of_le hχ_small (min_le_right _ _)
  have hM0 : 0 ≤ MChi p :=
    (MChi_pos_of_chi_lt_chiStar p hχ_star).le
  exact
    ⟨κtilde, D, U, hD, hcover, hprofile, hpin,
      positiveUpperBarrierSmoothBranchNoContact_of_remainingResidual_profile
        hM0 hpin.bare hprofile.stationary_eq hUdiff hUderivDiff hres,
      hUdiff, hUderivDiff⟩

/-- Raw lower-pinned smooth-branch contact data produces the full raw-contact
package by closing the interface from regularity. -/
theorem paper1_positiveLowerPinnedRawContactData_of_smoothContactData
    (hData : Paper1PositiveLowerPinnedRawSmoothContactBranchData) :
    Paper1PositiveLowerPinnedRawContactBranchData := by
  refine ⟨?_⟩
  intro p hα hχ_nonneg hχ_small c hc
  rcases hData.produce p hα hχ_nonneg hχ_small c hc with
    ⟨κtilde, D, U, hD, hcover, hprofile, hpin, hsmooth,
      hUdiff, _hUderivDiff⟩
  have hχ_star : p.χ < chiStar p :=
    lt_of_lt_of_le hχ_small (min_le_right _ _)
  exact
    ⟨κtilde, D, U, hD, hcover, hprofile, hpin,
      PositiveUpperBarrierContactContradictions.of_smoothBranchNoContact_profile
        hsmooth (kappa_pos_of_two_lt hc)
        (MChi_pos_of_chi_lt_chiStar p hχ_star)
        hpin.bare hUdiff⟩

/-- Positive branch wrapper through raw lower-pinned smooth-contact data. -/
theorem paper1_positiveContactBranch_of_lowerPinnedRawSmoothContactData
    (hData : Paper1PositiveLowerPinnedRawSmoothContactBranchData) :
    Paper1PositiveCriticalFrozenStationaryContactBranch :=
  paper1_positiveContactBranch_of_lowerPinnedRawContactData
    (paper1_positiveLowerPinnedRawContactData_of_smoothContactData hData)

/-- Strict-barrier branch wrapper through raw lower-pinned smooth-contact data. -/
theorem paper1_positiveStrictBarrierBranch_of_lowerPinnedRawSmoothContactData
    (hData : Paper1PositiveLowerPinnedRawSmoothContactBranchData) :
    Paper1PositiveCriticalFrozenStationaryStrictBarrierBranch :=
  paper1_positiveStrictBarrierBranch_of_lowerPinnedRawContactData
    (paper1_positiveLowerPinnedRawContactData_of_smoothContactData hData)

/-- Positive contact branch through raw lower-pinned remaining-contact data. -/
theorem paper1_positiveContactBranch_of_lowerPinnedRawRemainingContactData
    (hData : Paper1PositiveLowerPinnedRawRemainingContactBranchData) :
    Paper1PositiveCriticalFrozenStationaryContactBranch :=
  paper1_positiveContactBranch_of_lowerPinnedRawSmoothContactData
    (paper1_positiveLowerPinnedRawSmoothContactData_of_remainingContactData
      hData)

/-- Strict-barrier branch through raw lower-pinned remaining-contact data. -/
theorem paper1_positiveStrictBarrierBranch_of_lowerPinnedRawRemainingContactData
    (hData : Paper1PositiveLowerPinnedRawRemainingContactBranchData) :
    Paper1PositiveCriticalFrozenStationaryStrictBarrierBranch :=
  paper1_positiveStrictBarrierBranch_of_lowerPinnedRawSmoothContactData
    (paper1_positiveLowerPinnedRawSmoothContactData_of_remainingContactData
      hData)

/-- Main-statement input package with the positive branch routed through raw
lower-pinned smooth-branch no-contact data. -/
structure Paper1MainStatementLowerPinnedRawSmoothContactData
    (cStarStarFn : CMParams → ℝ → ℝ) : Prop where
  constructionNeg : ConstructionNegSMPProvider
  positiveLowerPinnedRawSmoothContact :
    Paper1PositiveLowerPinnedRawSmoothContactBranchData
  mainline : Paper1MainlineExistence cStarStarFn

/-- Main-statement wrapper through raw lower-pinned smooth-contact data. -/
theorem paper1_mainStatementTargets_of_lowerPinnedRawSmoothContactData
    {cStarStarFn : CMParams → ℝ → ℝ}
    (hData : Paper1MainStatementLowerPinnedRawSmoothContactData cStarStarFn) :
    Paper1MainStatementTargets :=
  paper1_mainStatementTargets_of_lowerPinnedRawContactData
    { constructionNeg := hData.constructionNeg
      positiveLowerPinnedRawContact :=
        paper1_positiveLowerPinnedRawContactData_of_smoothContactData
          hData.positiveLowerPinnedRawSmoothContact
      mainline := hData.mainline }

/-- Instance-facing wrapper for the raw lower-pinned smooth-contact
main-statement route. -/
theorem paper1_mainStatementTargets_of_lowerPinnedRawSmoothContactDataFact
    (cStarStarFn : CMParams → ℝ → ℝ)
    [hData :
      Fact (Paper1MainStatementLowerPinnedRawSmoothContactData cStarStarFn)] :
    Paper1MainStatementTargets :=
  paper1_mainStatementTargets_of_lowerPinnedRawSmoothContactData hData.out

/-- Bundled data for Paper1 combined statement targets using the raw
lower-pinned smooth-contact positive branch. -/
structure Paper1CombinedLowerPinnedRawSmoothContactStatementData
    (cStarStarFn : CMParams → ℝ → ℝ) : Prop where
  main : Paper1MainStatementLowerPinnedRawSmoothContactData cStarStarFn
  propositions : Paper1PropositionFrontierData
  lemma51 : Paper1Lemma51FrontierData
  lemma52 : Paper1Lemma52FrontierData

/-- Assemble the Paper1 combined statement targets through the raw
lower-pinned smooth-contact route. -/
theorem paper1_combinedStatementTargets_of_lowerPinnedRawSmoothContactData
    {cStarStarFn : CMParams → ℝ → ℝ}
    (hData :
      Paper1CombinedLowerPinnedRawSmoothContactStatementData cStarStarFn) :
    Paper1CombinedStatementTargets :=
  ⟨paper1_mainStatementTargets_of_lowerPinnedRawSmoothContactData hData.main,
    paper1_propositionTargets_of_frontierData hData.propositions,
    paper1_lemma25Targets,
    paper1_lemma51And52Targets_of_frontierData
      hData.lemma51 hData.lemma52⟩

/-- Instance-facing wrapper for the combined raw lower-pinned smooth-contact
Paper1 statement route. -/
theorem paper1_combinedStatementTargets_of_lowerPinnedRawSmoothContactDataFact
    (cStarStarFn : CMParams → ℝ → ℝ)
    [hData :
      Fact (Paper1CombinedLowerPinnedRawSmoothContactStatementData
        cStarStarFn)] :
    Paper1CombinedStatementTargets :=
  paper1_combinedStatementTargets_of_lowerPinnedRawSmoothContactData hData.out

/-- Main-statement input package whose positive branch carries only the
remaining contact residual. -/
structure Paper1MainStatementLowerPinnedRawRemainingContactData
    (cStarStarFn : CMParams → ℝ → ℝ) : Prop where
  constructionNeg : ConstructionNegSMPProvider
  positiveLowerPinnedRawRemainingContact :
    Paper1PositiveLowerPinnedRawRemainingContactBranchData
  mainline : Paper1MainlineExistence cStarStarFn

/-- Main-statement wrapper through the remaining-contact raw route. -/
theorem paper1_mainStatementTargets_of_lowerPinnedRawRemainingContactData
    {cStarStarFn : CMParams → ℝ → ℝ}
    (hData :
      Paper1MainStatementLowerPinnedRawRemainingContactData cStarStarFn) :
    Paper1MainStatementTargets :=
  paper1_mainStatementTargets_of_lowerPinnedRawSmoothContactData
    { constructionNeg := hData.constructionNeg
      positiveLowerPinnedRawSmoothContact :=
        paper1_positiveLowerPinnedRawSmoothContactData_of_remainingContactData
          hData.positiveLowerPinnedRawRemainingContact
      mainline := hData.mainline }

/-- Instance-facing wrapper for the raw lower-pinned remaining-contact
main-statement route. -/
theorem paper1_mainStatementTargets_of_lowerPinnedRawRemainingContactDataFact
    (cStarStarFn : CMParams → ℝ → ℝ)
    [hData :
      Fact (Paper1MainStatementLowerPinnedRawRemainingContactData
        cStarStarFn)] :
    Paper1MainStatementTargets :=
  paper1_mainStatementTargets_of_lowerPinnedRawRemainingContactData hData.out

/-- Bundled data for Paper1 combined statement targets using the raw
lower-pinned remaining-contact positive branch. -/
structure Paper1CombinedLowerPinnedRawRemainingContactStatementData
    (cStarStarFn : CMParams → ℝ → ℝ) : Prop where
  main : Paper1MainStatementLowerPinnedRawRemainingContactData cStarStarFn
  propositions : Paper1PropositionFrontierData
  lemma51 : Paper1Lemma51FrontierData
  lemma52 : Paper1Lemma52FrontierData

/-- Assemble Paper1 combined statement targets through the raw lower-pinned
remaining-contact route. -/
theorem paper1_combinedStatementTargets_of_lowerPinnedRawRemainingContactData
    {cStarStarFn : CMParams → ℝ → ℝ}
    (hData :
      Paper1CombinedLowerPinnedRawRemainingContactStatementData cStarStarFn) :
    Paper1CombinedStatementTargets :=
  paper1_combinedStatementTargets_of_lowerPinnedRawSmoothContactData
    { main :=
        { constructionNeg := hData.main.constructionNeg
          positiveLowerPinnedRawSmoothContact :=
            paper1_positiveLowerPinnedRawSmoothContactData_of_remainingContactData
              hData.main.positiveLowerPinnedRawRemainingContact
          mainline := hData.main.mainline }
      propositions := hData.propositions
      lemma51 := hData.lemma51
      lemma52 := hData.lemma52 }

/-- Instance-facing wrapper for the combined raw lower-pinned remaining-contact
Paper1 statement route. -/
theorem paper1_combinedStatementTargets_of_lowerPinnedRawRemainingContactDataFact
    (cStarStarFn : CMParams → ℝ → ℝ)
    [hData :
      Fact (Paper1CombinedLowerPinnedRawRemainingContactStatementData
        cStarStarFn)] :
    Paper1CombinedStatementTargets :=
  paper1_combinedStatementTargets_of_lowerPinnedRawRemainingContactData
    hData.out

section AxiomAudit
#print axioms positiveUpperBarrier_expOperatorCompareAtContact_of_profile_regularity
#print axioms positiveUpperBarrierSmoothBranchNoContact_of_remainingResidual_profile
#print axioms upperBarrier_interfaceNoContact_of_profile_differentiable
end AxiomAudit

end

end ShenWork.Paper1
