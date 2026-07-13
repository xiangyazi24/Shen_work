/- Strict maximum-principle inputs for the nonmonotone positive profile. -/
import ShenWork.Paper1.WavePositiveLeftEndpoint
import ShenWork.Paper1.WavePaperSuperBarrierPos
import ShenWork.Paper1.WaveTrapProps

open Filter MeasureTheory Real Set Topology

noncomputable section

namespace ShenWork.Paper1

/-- A pointwise positive bounded profile has a strictly positive whole-line
elliptic Green convolution. -/
theorem frozenElliptic_pos_of_pos
    (p : CMParams) {U : ℝ → ℝ}
    (hU : IsCUnifBdd U) (hU0 : ∀ x, 0 ≤ U x)
    (hUpos : ∀ x, 0 < U x) (x : ℝ) :
    0 < frozenElliptic p U x := by
  rw [frozenElliptic_eq_translated_integral p hU hU0 x]
  let F : ℝ → ℝ := fun t =>
    Real.exp (-1 * |t|) * (U (x + t)) ^ p.γ
  have hFint : Integrable F := by
    simpa [F] using
      frozenElliptic_translated_integrand_integrable p hU hU0 x
  have hFcont : Continuous F := by
    have hpow : Continuous (fun t : ℝ => (U (x + t)) ^ p.γ) :=
      (rpow_cunif_bdd_of_nonneg p hU hU0).1.comp
        (continuous_const.add continuous_id)
    exact (by fun_prop : Continuous (fun t : ℝ => Real.exp (-1 * |t|))).mul hpow
  have hF0 : 0 ≤ F := by
    intro t
    exact mul_nonneg (Real.exp_nonneg _)
      (Real.rpow_nonneg (hU0 (x + t)) _)
  have hFat0 : 0 < F 0 := by
    dsimp [F]
    simp only [abs_zero, mul_zero, Real.exp_zero, one_mul]
    simpa using Real.rpow_pos_of_pos (hUpos x) p.γ
  have hint : 0 < ∫ t : ℝ, F t :=
    integral_pos_of_integrable_nonneg_nonzero hFcont hFint hF0
      (x := 0) (ne_of_gt hFat0)
  positivity

/-- The positive normalization is the exact positive root of
`(1-chi) M^alpha = 1`. -/
theorem MChi_rpow_alpha_eq_one_div_one_sub_chi
    (p : CMParams) (hχ0 : 0 ≤ p.χ) (hχ1 : p.χ < 1) :
    (MChi p) ^ p.α = 1 / (1 - p.χ) := by
  let b : ℝ := 1 / (1 - p.χ)
  have hb : 0 < b := by
    dsimp [b]
    exact one_div_pos.mpr (sub_pos.mpr hχ1)
  have hα : p.α ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one p.hα)
  rw [MChi_eq_rpow_of_chi_nonneg_lt_one p hχ0 hχ1]
  change (b ^ (1 / p.α)) ^ p.α = b
  rw [← Real.rpow_mul hb.le]
  have hexp : (1 / p.α) * p.α = 1 := by
    field_simp
  rw [hexp, Real.rpow_one]

/-- With positive attraction the paper-expanded constant upper branch is a
strict supersolution.  Strictness is the favorable diagonal term containing
the strictly positive elliptic convolution. -/
theorem paperWaveOperator_MChi_strict_neg_of_chi_pos
    (p : CMParams) {c κ : ℝ} {U : ℝ → ℝ}
    (hχ : 0 < p.χ) (hχ1 : p.χ < 1)
    (hα : p.α = p.m + p.γ - 1)
    (hU : InWaveTrapSet κ (MChi p) U)
    (hUpos : ∀ x, 0 < U x) (x : ℝ) :
    paperWaveOperator p c U (fun _ => MChi p) x < 0 := by
  rw [paperWaveOperator_const_eq p hU.cunif_bdd hU.nonneg x]
  have hM : 0 < MChi p := MChi_pos_of_chi_lt_one p hχ1
  have hV : 0 < frozenElliptic p U x :=
    frozenElliptic_pos_of_pos p hU.cunif_bdd hU.nonneg hUpos x
  have hMα : (MChi p) ^ p.α = 1 / (1 - p.χ) :=
    MChi_rpow_alpha_eq_one_div_one_sub_chi p hχ.le hχ1
  have hden : 1 - p.χ ≠ 0 := ne_of_gt (by linarith)
  have hm : 0 < (MChi p) ^ (p.m - 1) :=
    Real.rpow_pos_of_pos hM _
  rw [← hα]
  calc
    MChi p *
          (1 - p.χ * (MChi p) ^ (p.m - 1) * frozenElliptic p U x -
            ((MChi p) ^ p.α - p.χ * (MChi p) ^ p.α)) =
        -(MChi p * p.χ * (MChi p) ^ (p.m - 1) *
          frozenElliptic p U x) := by
      rw [hMα]
      field_simp [hden]
      ring
    _ < 0 := neg_neg_of_pos (by positivity)

/-- Scalar strong maximum principle at `chi = 0`, requiring only the
nonmonotone wave-trap bounds. -/
theorem stationaryProfile_strictlyBelow_one_of_chi_zero_waveTrap
    {p : CMParams} {c κ : ℝ} {U : ℝ → ℝ}
    (hchi : p.χ = 0)
    (hU : InWaveTrapSet κ 1 U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hU_diff : Differentiable ℝ U)
    (hUd_diff : Differentiable ℝ (deriv U))
    (hlim : Tendsto U atTop (nhds 0)) :
    ∀ x, U x < 1 := by
  let Q : ℝ → ℝ := fun x => 1 - U x
  have hQ_nonneg : ∀ x, 0 ≤ Q x := by
    intro x
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
    have hstatx := hstat x
    unfold frozenWaveOperator at hstatx
    rw [hchi] at hstatx
    simp only [zero_mul, sub_zero] at hstatx
    have hiter : iteratedDeriv 2 U x = deriv (deriv U) x := by
      simp [iteratedDeriv_succ, iteratedDeriv_zero]
    rw [hiter] at hstatx
    have hUdd : deriv (deriv U) x =
        -c * deriv U x - U x * (1 - (U x) ^ p.α) := by
      linarith
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
    have hpow : |1 - (U x) ^ p.α| ≤ B * |Q x| := by
      simpa [B, Q, Real.dist_eq, abs_sub_comm] using hdist
    have hUabs : |U x| ≤ 1 := by
      rw [abs_of_nonneg (hU.nonneg x)]
      exact hU.le_M x
    have hreact : |U x * (1 - (U x) ^ p.α)| ≤ B * |Q x| := by
      rw [abs_mul]
      calc
        |U x| * |1 - (U x) ^ p.α| ≤ 1 * (B * |Q x|) :=
          mul_le_mul hUabs hpow (abs_nonneg _) (by positivity)
        _ = B * |Q x| := one_mul _
    rw [hQformula]
    calc
      |-c * deriv Q x + U x * (1 - (U x) ^ p.α)| ≤
          |-c * deriv Q x| + |U x * (1 - (U x) ^ p.α)| :=
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
  have hx := hQpos x
  dsimp [Q] at hx
  linarith

section AxiomAudit

#print axioms frozenElliptic_pos_of_pos
#print axioms MChi_rpow_alpha_eq_one_div_one_sub_chi
#print axioms paperWaveOperator_MChi_strict_neg_of_chi_pos
#print axioms stationaryProfile_strictlyBelow_one_of_chi_zero_waveTrap

end AxiomAudit

end ShenWork.Paper1
