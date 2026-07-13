/- Strict upper-barrier comparison for the nonmonotone positive Schauder profile. -/
import ShenWork.Paper1.WavePositiveStrictMaximum
import ShenWork.Paper1.WaveRotheMaxPrincipleClosers
import ShenWork.Paper1.WaveRotheResidualClose

open Filter Real Set Topology

noncomputable section

namespace ShenWork.Paper1

/-- Pointwise comparison of the paper-expanded operator at a smooth contact.
Every lower-order coefficient agrees at contact, leaving only the second
derivative inequality. -/
theorem paperWaveOperator_le_of_contact
    (p : CMParams) {c x : ℝ} {u W B : ℝ → ℝ}
    (hvalue : W x = B x)
    (hderiv : deriv W x = deriv B x)
    (hsecond : iteratedDeriv 2 W x ≤ iteratedDeriv 2 B x) :
    paperWaveOperator p c u W x ≤ paperWaveOperator p c u B x := by
  unfold paperWaveOperator
  dsimp only
  rw [hvalue, hderiv]
  linarith

/-- A differentiable profile below the nonsmooth upper barrier cannot touch
its corner.  Spatial monotonicity is not used. -/
theorem upperBarrier_interfaceNoContact_of_waveTrap
    {κ M : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < κ) (hM : 0 < M)
    (hU : InWaveTrapSet κ M U)
    (hUdiff : Differentiable ℝ U) :
    ∀ x, Real.exp (-κ * x) = M → U x = M → False := by
  intro x hx hUx
  have hbarrier : upperBarrier κ M x = M :=
    upperBarrier_eq_M_of_le_exp hx.ge
  have hlocal : IsLocalMax (fun y => U y - upperBarrier κ M y) x := by
    dsimp [IsLocalMax, IsMaxFilter]
    refine Eventually.of_forall fun y => ?_
    have hy : U y - upperBarrier κ M y ≤ 0 :=
      sub_nonpos.mpr (hU.le_upperBarrier y)
    have hx0 : U x - upperBarrier κ M x = 0 := by
      rw [hUx, hbarrier, sub_self]
    simpa [hx0] using hy
  exact maxSub_upperBarrier_ne_interface hκ hM (hUdiff x) hlocal hx

/-- At a contact in the smooth exponential branch, stationarity and the
strict whole-line paper super-barrier are incompatible. -/
theorem positiveStationary_no_exp_upperBarrier_contact
    (p : CMParams) {c κ M : ℝ} {U : ℝ → ℝ}
    (hχ0 : 0 ≤ p.χ) (hχ : p.χ < chiStar p)
    (hα : p.α = p.m + p.γ - 1)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hc : c = κ + κ⁻¹)
    (hU : InWaveTrapSet κ M U)
    (hU2 : ContDiff ℝ 2 U)
    (hpaper : ∀ x, paperWaveOperator p c U U x = 0) :
    ∀ x, Real.exp (-κ * x) < M →
      U x = Real.exp (-κ * x) → False := by
  intro x hx hUx
  have hEq : upperBarrier κ M =ᶠ[nhds x] expDecay κ :=
    upperBarrier_eventuallyEq_exp_of_lt hx
  have hUxE : U x = expDecay κ x := by
    simpa [expDecay] using hUx
  have hlocal : IsLocalMax (fun y => U y - expDecay κ y) x := by
    dsimp [IsLocalMax, IsMaxFilter]
    have hx0 : U x - expDecay κ x = 0 := by rw [hUxE, sub_self]
    filter_upwards [hEq] with y hy
    have hyle : U y - upperBarrier κ M y ≤ 0 :=
      sub_nonpos.mpr (hU.le_upperBarrier y)
    have hyle' : U y - expDecay κ y ≤ 0 := by simpa [hy] using hyle
    simpa [hx0] using hyle'
  have hfirst0 : deriv (fun y => U y - expDecay κ y) x = 0 :=
    hlocal.deriv_eq_zero
  have hfirstEq : deriv (fun y => U y - expDecay κ y) x =
      deriv U x - deriv (expDecay κ) x :=
    deriv_sub (hU2.differentiable (by norm_num) x)
      ((expDecay_hasDerivAt κ x).differentiableAt)
  have hfirst : deriv U x = deriv (expDecay κ) x := by
    rw [hfirstEq] at hfirst0
    linarith
  have hE2 : ContDiffAt ℝ 2 (expDecay κ) x := by
    simpa [expDecay] using
      (by fun_prop : ContDiffAt ℝ 2 (fun y : ℝ => Real.exp (-κ * y)) x)
  have hsecond : iteratedDeriv 2 U x ≤
      iteratedDeriv 2 (expDecay κ) x :=
    iteratedDeriv2_le_of_isLocalMax_sub hU2.contDiffAt hE2 hlocal
  have hBvalue : expDecay κ x = upperBarrier κ M x := by
    rw [upperBarrier_eq_exp_of_exp_le hx.le]
    simp [expDecay]
  have hBderiv : deriv (expDecay κ) x =
      deriv (upperBarrier κ M) x := by
    rw [upperBarrier_deriv_eq_exp_of_lt hx, expDecay_deriv]
  have hBsecond : iteratedDeriv 2 (expDecay κ) x =
      iteratedDeriv 2 (upperBarrier κ M) x := by
    rw [upperBarrier_iteratedDeriv_two_eq_exp_of_lt hx,
      expDecay_iteratedDeriv_two]
  have hcompare : paperWaveOperator p c U U x ≤
      paperWaveOperator p c U (upperBarrier κ M) x :=
    paperWaveOperator_le_of_contact p
      (hUxE.trans hBvalue) (hfirst.trans hBderiv)
      (hsecond.trans_eq hBsecond)
  have hstrict : paperWaveOperator p c U (upperBarrier κ M) x < 0 :=
    paperWaveOperator_upperBarrier_exp_region_strict_pos
      p hχ0 hχ hα hκ hκ1 hc hU hx
  rw [hpaper x] at hcompare
  linarith

/-- A positive-attraction stationary profile cannot touch the smooth constant
branch of the canonical upper barrier. -/
theorem positiveStationary_no_const_upperBarrier_contact_of_chi_pos
    (p : CMParams) {c κ : ℝ} {U : ℝ → ℝ}
    (hχ : 0 < p.χ) (hχ1 : p.χ < 1)
    (hα : p.α = p.m + p.γ - 1)
    (hU : InWaveTrapSet κ (MChi p) U)
    (hUpos : ∀ x, 0 < U x)
    (hU2 : ContDiff ℝ 2 U)
    (hpaper : ∀ x, paperWaveOperator p c U U x = 0) :
    ∀ x, U x = MChi p → False := by
  intro x hUx
  have hlocal : IsLocalMax U x := by
    dsimp [IsLocalMax, IsMaxFilter]
    exact Eventually.of_forall fun y => by
      simpa [hUx] using hU.le_M y
  have hfirst : deriv U x = 0 := hlocal.deriv_eq_zero
  have hsecond : iteratedDeriv 2 U x ≤ 0 :=
    iteratedDeriv2_nonpos_of_isLocalMax hlocal
      (hU2.continuous.continuousAt)
  have hconst2 : iteratedDeriv 2 (fun _ : ℝ => MChi p) x = 0 := by
    simp [iteratedDeriv_succ, iteratedDeriv_zero]
  have hcompare : paperWaveOperator p c U U x ≤
      paperWaveOperator p c U (fun _ => MChi p) x := by
    apply paperWaveOperator_le_of_contact p
    · simpa using hUx
    · simpa using hfirst
    · rw [hconst2]
      exact hsecond
  have hstrict := paperWaveOperator_MChi_strict_neg_of_chi_pos
    p (c := c) hχ hχ1 hα hU hUpos x
  rw [hpaper x] at hcompare
  linarith

/-- The nonmonotone positive Schauder profile lies strictly below the
canonical nonsmooth upper barrier at every finite point. -/
theorem positiveStationary_strict_upperBarrier
    (p : CMParams) {c : ℝ} {U : ℝ → ℝ}
    (hα : p.α = p.m + p.γ - 1)
    (hχ0 : 0 ≤ p.χ)
    (hχsmall : p.χ < min (1 / 2 : ℝ) (chiStar p))
    (hc : 2 < c)
    (hU : InWaveTrapSet (kappa c) (MChi p) U)
    (hUpos : ∀ x, 0 < U x)
    (hU2 : ContDiff ℝ 2 U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hright : Tendsto U atTop (nhds 0)) :
    ∀ x, U x < upperBarrier (kappa c) (MChi p) x := by
  have hχ1 : p.χ < 1 := by
    have hhalf : p.χ < (1 / 2 : ℝ) :=
      lt_of_lt_of_le hχsmall (min_le_left _ _)
    linarith
  have hM : 0 < MChi p := MChi_pos_of_chi_lt_one p hχ1
  have hκ : 0 < kappa c := kappa_pos_of_two_lt hc
  have hκ1 : kappa c < 1 := kappa_lt_one_of_two_lt hc
  have hspeed : c = kappa c + (kappa c)⁻¹ :=
    (kappa_add_inv_eq_of_two_lt hc).symm
  have hχstar : p.χ < chiStar p :=
    lt_of_lt_of_le hχsmall (min_le_right _ _)
  have hpaper : ∀ x, paperWaveOperator p c U U x = 0 := by
    intro x
    rw [paperWaveOperator_eq_frozenWaveOperator_at_fixed_point p x
      hU.cunif_bdd hU.nonneg
      (hU2.differentiable (by norm_num) x)
      (frozenElliptic_deriv_differentiableAt p hU.cunif_bdd hU.nonneg x)
      ((hU2.differentiable (by norm_num) x).rpow_const (Or.inr p.hm))]
    exact hstat x
  intro x
  have hle : U x ≤ upperBarrier (kappa c) (MChi p) x :=
    hU.le_upperBarrier x
  by_cases hlt : U x < upperBarrier (kappa c) (MChi p) x
  · exact hlt
  have hcontact : U x = upperBarrier (kappa c) (MChi p) x :=
    le_antisymm hle (le_of_not_gt hlt)
  rcases lt_trichotomy (Real.exp (-(kappa c) * x)) (MChi p) with
      hexp | hinterface | hconst
  · have hbar : upperBarrier (kappa c) (MChi p) x =
        Real.exp (-(kappa c) * x) :=
      upperBarrier_eq_exp_of_exp_le hexp.le
    have hUx : U x = Real.exp (-(kappa c) * x) := hcontact.trans hbar
    exact False.elim (positiveStationary_no_exp_upperBarrier_contact
      p hχ0 hχstar hα hκ hκ1 hspeed hU hU2 hpaper x hexp hUx)
  · have hbar : upperBarrier (kappa c) (MChi p) x = MChi p :=
      upperBarrier_eq_M_of_le_exp hinterface.ge
    have hUx : U x = MChi p := hcontact.trans hbar
    exact False.elim (upperBarrier_interfaceNoContact_of_waveTrap
      hκ hM hU (hU2.differentiable (by norm_num)) x hinterface hUx)
  · have hbar : upperBarrier (kappa c) (MChi p) x = MChi p :=
      upperBarrier_eq_M_of_le_exp hconst.le
    have hUx : U x = MChi p := hcontact.trans hbar
    by_cases hχzero : p.χ = 0
    · have hMone : MChi p = 1 :=
        MChi_eq_one_of_chi_nonpos p (by linarith)
      have hUone : InWaveTrapSet (kappa c) 1 U := by
        simpa [hMone] using hU
      have hstrictOne := stationaryProfile_strictlyBelow_one_of_chi_zero_waveTrap
        hχzero hUone hstat (hU2.differentiable (by norm_num))
        (by
          have hU2' : ContDiff ℝ ((1 : ℕ∞) + 1) U := by simpa using hU2
          exact (contDiff_succ_iff_deriv.mp hU2').2.2.differentiable
            (by norm_num))
        hright x
      rw [hMone] at hUx
      exact False.elim ((ne_of_lt hstrictOne) hUx)
    · have hχpos : 0 < p.χ := lt_of_le_of_ne hχ0 (Ne.symm hχzero)
      exact False.elim
        (positiveStationary_no_const_upperBarrier_contact_of_chi_pos
          p hχpos hχ1 hα hU hUpos hU2 hpaper x hUx)

section AxiomAudit

#print axioms paperWaveOperator_le_of_contact
#print axioms upperBarrier_interfaceNoContact_of_waveTrap
#print axioms positiveStationary_no_exp_upperBarrier_contact
#print axioms positiveStationary_no_const_upperBarrier_contact_of_chi_pos
#print axioms positiveStationary_strict_upperBarrier

end AxiomAudit

end ShenWork.Paper1
