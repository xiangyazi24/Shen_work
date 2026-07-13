/- Left-end selection for the nonmonotone positive Schauder profile. -/
import ShenWork.Paper1.WavePositiveStationaryLiouville

open Filter Set Topology Real

noncomputable section

namespace ShenWork.Paper1

theorem isCUnifBdd_comp_add_const
    {f : ℝ → ℝ} (hf : IsCUnifBdd f) (a : ℝ) :
    IsCUnifBdd (fun x => f (x + a)) := by
  refine ⟨hf.1.comp (continuous_id.add continuous_const), ?_⟩
  obtain ⟨B, hB⟩ := hf.2
  exact ⟨B, fun x => hB (x + a)⟩

/-- The whole-line elliptic convolution commutes with translations. -/
theorem frozenElliptic_comp_add_const
    (p : CMParams) {U : ℝ → ℝ}
    (hU : IsCUnifBdd U) (hU0 : ∀ x, 0 ≤ U x) (a x : ℝ) :
    frozenElliptic p (fun y => U (y + a)) x =
      frozenElliptic p U (x + a) := by
  rw [frozenElliptic_eq_translated_integral p (isCUnifBdd_comp_add_const hU a)
      (fun y => hU0 (y + a)),
    frozenElliptic_eq_translated_integral p hU hU0]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  congr 2
  ring

theorem frozenElliptic_comp_add_const_fun
    (p : CMParams) {U : ℝ → ℝ}
    (hU : IsCUnifBdd U) (hU0 : ∀ x, 0 ≤ U x) (a : ℝ) :
    frozenElliptic p (fun y => U (y + a)) =
      fun x => frozenElliptic p U (x + a) := by
  funext x
  exact frozenElliptic_comp_add_const p hU hU0 a x

theorem frozenElliptic_deriv_comp_add_const
    (p : CMParams) {U : ℝ → ℝ}
    (hU : IsCUnifBdd U) (hU0 : ∀ x, 0 ≤ U x) (a x : ℝ) :
    deriv (frozenElliptic p (fun y => U (y + a))) x =
      deriv (frozenElliptic p U) (x + a) := by
  rw [frozenElliptic_comp_add_const_fun p hU hU0 a]
  exact deriv_comp_add_const (frozenElliptic p U) a x

/-- Translation covariance of the expanded diagonal paper operator. -/
theorem paperWaveOperator_self_comp_add_const
    (p : CMParams) {c : ℝ} {U : ℝ → ℝ}
    (hU : IsCUnifBdd U) (hU0 : ∀ x, 0 ≤ U x) (a x : ℝ) :
    paperWaveOperator p c (fun y => U (y + a)) (fun y => U (y + a)) x =
      paperWaveOperator p c U U (x + a) := by
  unfold paperWaveOperator
  simp only
  rw [congrFun (iteratedDeriv_comp_add_const 2 U a) x,
    deriv_comp_add_const U a x,
    frozenElliptic_comp_add_const p hU hU0 a x,
    frozenElliptic_deriv_comp_add_const p hU hU0 a x]

/-- The positive plateau pin makes every left translation cluster uniformly
positive by the same explicit constant. -/
theorem lowerPinned_leftTranslationCluster_lower
    {κ κtilde D : ℝ} {U W : ℝ → ℝ} {a : ℕ → ℝ}
    (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D)
    (hlower : ∀ x, lowerBarrierPlateau κ κtilde D x ≤ U x)
    (ha : ∀ n, a n < -(n : ℝ))
    (hconv : LocallyUniformConverges (fun n x => U (x + a n)) W) :
    ∀ x, lowerBarrierRaw κ κtilde D
        (lowerBarrierXPlus κ κtilde D) ≤ W x := by
  intro x
  let d := lowerBarrierRaw κ κtilde D
    (lowerBarrierXPlus κ κtilde D)
  have hpos : 0 < d := lowerBarrierRaw_pos_at_xplus hκ hgap hD
  obtain ⟨N, hN⟩ := exists_nat_gt (x - lowerBarrierXPlus κ κtilde D)
  have hev : ∀ᶠ n : ℕ in atTop, d ≤ U (x + a n) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hxleft : x + a n ≤ lowerBarrierXPlus κ κtilde D := by
      have han := ha n
      have hN' : x - lowerBarrierXPlus κ κtilde D < (N : ℝ) := hN
      linarith
    simpa [d, lowerBarrierPlateau_eq_const_of_le hxleft] using
      hlower (x + a n)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds (hconv.tendsto_at x) hev

/-- Every sequence of left translates has a `C²`, stationary, uniformly
positive local-uniform cluster. -/
theorem positiveStationary_leftTranslationCluster
    (p : CMParams) {c lam κ M κtilde D Λ : ℝ} {U : ℝ → ℝ}
    (hM : 0 < M) (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D)
    (hU : InLowerPinnedC1UniformModulusWaveTrap κ M
      (max 1 Λ) (lowerBarrierPlateau κ κtilde D) U)
    (A : PaperStepAnalytic p c lam M κ Λ U U U)
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    {a : ℕ → ℝ} (ha : ∀ n, a n < -(n : ℝ)) :
    ∃ sub : ℕ → ℕ, StrictMono sub ∧ ∃ W,
      LocallyUniformConverges (fun n x => U (x + a (sub n))) W ∧
      IsCUnifBdd W ∧ (∀ x, 0 ≤ W x) ∧ (∀ x, W x ≤ M) ∧
      (∀ x, lowerBarrierRaw κ κtilde D
        (lowerBarrierXPlus κ κtilde D) ≤ W x) ∧
      ContDiff ℝ 2 W ∧
      (∀ x, frozenWaveOperator p c W W x = 0) := by
  let us : ℕ → ℝ → ℝ := fun n x => U (x + a n)
  let Q : ℝ := max M (max 1 Λ)
  have hQ0 : 0 ≤ Q := le_trans hM.le (le_max_left M (max 1 Λ))
  have husLip : ∀ n x y, |us n x - us n y| ≤ Q * |x - y| := by
    intro n x y
    calc
      |us n x - us n y| ≤ max 1 Λ * |(x + a n) - (y + a n)| :=
        hU.modulus (x + a n) (y + a n)
      _ = max 1 Λ * |x - y| := by congr 2 <;> ring
      _ ≤ Q * |x - y| := mul_le_mul_of_nonneg_right
        (le_max_right M (max 1 Λ)) (abs_nonneg _)
  have husBdd : ∀ n x, |us n x| ≤ Q := by
    intro n x
    rw [abs_of_nonneg (hU.bare.nonneg (x + a n))]
    exact (hU.bare.le_M (x + a n)).trans (le_max_left M (max 1 Λ))
  obtain ⟨sub₁, hsub₁, W, hpoint, hWQ⟩ :=
    helly_pointwise_selection Q us husLip husBdd
  have hval₁ : LocallyUniformConverges (fun n => us (sub₁ n)) W :=
    locallyUniform_of_helly_pointwise hQ0 hpoint husLip hWQ
  have hW0 : ∀ x, 0 ≤ W x := fun x =>
    hval₁.nonneg_of_forall_nonneg
      (fun n => hU.bare.nonneg (x + a (sub₁ n)))
  have hWM : ∀ x, W x ≤ M := fun x =>
    hval₁.le_of_forall_le (fun n => hU.bare.le_M (x + a (sub₁ n)))
  have hWcont : Continuous W := continuous_of_locallyUniform
    (fun n => (isCUnifBdd_comp_add_const hU.bare.cunif_bdd
      (a (sub₁ n))).1) hval₁
  have hWbdd : IsCUnifBdd W := by
    refine ⟨hWcont, ⟨M, fun x => ?_⟩⟩
    rw [abs_of_nonneg (hW0 x)]
    exact hWM x
  let C2 : ℝ := paperStepC2Bound c lam M Λ
  have hC20 : 0 ≤ C2 := paperStepC2Bound_nonneg hlam hM.le hΛ
  let ds : ℕ → ℝ → ℝ := fun n x => deriv U (x + a (sub₁ n))
  have hdsHas : ∀ n x,
      HasDerivAt (ds n) (iteratedDeriv 2 U (x + a (sub₁ n))) x := by
    intro n x
    convert (paperStep_hasDerivAt_deriv A (x + a (sub₁ n))).comp x
      ((hasDerivAt_id x).add_const (a (sub₁ n))) using 1 <;>
      simp only [Function.comp_apply, id_eq, mul_one]
  have hdsBound : ∀ n x, |ds n x| ≤ Λ := by
    intro n x
    exact paperStep_deriv_le hlam A (x + a (sub₁ n))
  have hddsBound : ∀ n x,
      |iteratedDeriv 2 U (x + a (sub₁ n))| ≤ C2 := by
    intro n x
    exact paperStep_second_deriv_le hlam hM.le hΛ
      (fun y => by
        rw [abs_of_nonneg (hU.bare.nonneg y)]
        exact hU.bare.le_M y) A (x + a (sub₁ n))
  have hdsLip : ∀ n x y, |ds n x - ds n y| ≤ C2 * |x - y| := by
    intro n x y
    have hlip : LipschitzWith (Real.toNNReal C2) (ds n) :=
      crossImplicitStep_lipschitz hC20
        (fun z => (hdsHas n z).differentiableAt)
        (fun z => by rw [(hdsHas n z).deriv]; exact hddsBound n z)
    have hdxy := hlip.dist_le_mul x y
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hC20] at hdxy
    exact hdxy
  let Qd : ℝ := max Λ C2
  have hQd0 : 0 ≤ Qd := le_trans hΛ (le_max_left Λ C2)
  have hdsLipQ : ∀ n x y, |ds n x - ds n y| ≤ Qd * |x - y| := by
    intro n x y
    exact (hdsLip n x y).trans (mul_le_mul_of_nonneg_right
      (le_max_right Λ C2) (abs_nonneg _))
  have hdsBddQ : ∀ n x, |ds n x| ≤ Qd := fun n x =>
    (hdsBound n x).trans (le_max_left Λ C2)
  obtain ⟨sub₂, hsub₂, P, hdpoint, hPQ⟩ :=
    helly_pointwise_selection Qd ds hdsLipQ hdsBddQ
  have hderiv : LocallyUniformConverges (fun n => ds (sub₂ n)) P :=
    locallyUniform_of_helly_pointwise hQd0 hdpoint hdsLipQ hPQ
  let sub : ℕ → ℕ := sub₁ ∘ sub₂
  have hsub : StrictMono sub := hsub₁.comp hsub₂
  let vs : ℕ → ℝ → ℝ := fun n => us (sub n)
  let dvs : ℕ → ℝ → ℝ := fun n => ds (sub₂ n)
  have hval : LocallyUniformConverges vs W := by
    simpa [vs, sub, Function.comp_apply] using hval₁.comp_strictMono hsub₂
  have hdval : LocallyUniformConverges dvs P := by simpa [dvs] using hderiv
  have hvsHas : ∀ n x, HasDerivAt (vs n) (dvs n x) x := by
    intro n x
    dsimp [vs, dvs, us, ds, sub]
    convert (paperStep_hasDerivAt_value A (x + a (sub₁ (sub₂ n)))).comp x
      ((hasDerivAt_id x).add_const (a (sub₁ (sub₂ n)))) using 1 <;>
      simp only [Function.comp_apply, id_eq, mul_one]
  have hWhas : ∀ x, HasDerivAt W (P x) x := by
    intro x
    exact hasDerivAt_of_tendstoLocallyUniformlyOn
      (𝕜 := ℝ) (l := atTop) (s := (Set.univ : Set ℝ))
      (f := vs) (g := W) (f' := dvs) (g' := P)
      isOpen_univ hdval.tendstoLocallyUniformlyOn_univ
      (Eventually.of_forall fun n y _ => hvsHas n y)
      (fun y _ => hval.tendsto_at y) (Set.mem_univ x)
  have hWderiv : deriv W = P := by
    funext x
    exact (hWhas x).deriv
  have hvsDeriv : ∀ n, deriv (vs n) = dvs n := by
    intro n
    funext x
    dsimp [vs, dvs, us, ds, sub]
    exact deriv_comp_add_const U (a (sub₁ (sub₂ n))) x
  have hvsC : ∀ n, IsCUnifBdd (vs n) := fun n =>
    isCUnifBdd_comp_add_const hU.bare.cunif_bdd (a (sub n))
  have hvs0 : ∀ n x, 0 ≤ vs n x := fun n x =>
    hU.bare.nonneg (x + a (sub n))
  have hvsM : ∀ n x, vs n x ≤ M := fun n x =>
    hU.bare.le_M (x + a (sub n))
  have hV : LocallyUniformConverges
      (fun n => frozenElliptic p (vs n)) (frozenElliptic p W) :=
    frozenEllipticDependence_of_nonneg_le p hM.le hvsC hvs0 hvsM
      hWbdd hW0 hWM hval
  have hVd : LocallyUniformConverges
      (fun n x => deriv (frozenElliptic p (vs n)) x)
      (fun x => deriv (frozenElliptic p W) x) :=
    frozenEllipticDerivDependence_of_nonneg_le p hM.le hvsC hvs0 hvsM
      hWbdd hW0 hWM hval
  have hPbound : ∀ x, |P x| ≤ Qd := fun x =>
    le_of_tendsto (hdval.tendsto_at x).abs
      (Eventually.of_forall fun n => hdsBddQ (sub₂ n) x)
  have hbW : LocallyBoundedOnCompacts W :=
    LocallyBoundedOnCompacts.of_global_bound hM.le (fun x => by
      rw [abs_of_nonneg (hW0 x)]; exact hWM x)
  have hbP : LocallyBoundedOnCompacts P :=
    LocallyBoundedOnCompacts.of_global_bound hQd0 hPbound
  have hMγ0 : 0 ≤ M ^ p.γ := Real.rpow_nonneg hM.le _
  have hVbound : ∀ x, |frozenElliptic p W x| ≤ M ^ p.γ := by
    intro x
    rw [abs_of_nonneg (frozenElliptic_nonneg p hW0 x)]
    exact frozenElliptic_le_of_rpow_le p hMγ0 hWcont hW0
      (fun y => Real.rpow_le_rpow (hW0 y) (hWM y)
        (le_trans zero_le_one p.hγ)) x
  have hVdbound : ∀ x, |deriv (frozenElliptic p W) x| ≤ M ^ p.γ := fun x =>
    (frozenElliptic_deriv_abs_le p hWbdd hW0 x).trans
      (by simpa [abs_of_nonneg (frozenElliptic_nonneg p hW0 x)] using hVbound x)
  have hbV := LocallyBoundedOnCompacts.of_global_bound hMγ0 hVbound
  have hbVd := LocallyBoundedOnCompacts.of_global_bound hMγ0 hVdbound
  have hm10 : 0 ≤ p.m - 1 := by linarith [p.hm]
  have hpowM1 : LocallyUniformConverges
      (fun n x => (vs n x) ^ (p.m - 1))
      (fun x => (W x) ^ (p.m - 1)) :=
    hval.rpow_of_nonneg_le hm10 hM.le hvs0 hvsM hW0 hWM
  have hpowA : LocallyUniformConverges
      (fun n x => (vs n x) ^ p.α) (fun x => (W x) ^ p.α) :=
    hval.rpow_of_nonneg_le (le_trans zero_le_one p.hα) hM.le
      hvs0 hvsM hW0 hWM
  have hpowMG : LocallyUniformConverges
      (fun n x => (vs n x) ^ (p.m + p.γ - 1))
      (fun x => (W x) ^ (p.m + p.γ - 1)) :=
    hval.rpow_of_nonneg_le (by linarith [p.hm, p.hγ]) hM.le
      hvs0 hvsM hW0 hWM
  have hMpow0 : 0 ≤ M ^ (p.m - 1) := Real.rpow_nonneg hM.le _
  have hpowBound : ∀ x, |(W x) ^ (p.m - 1)| ≤ M ^ (p.m - 1) := by
    intro x
    rw [abs_of_nonneg (Real.rpow_nonneg (hW0 x) _)]
    exact Real.rpow_le_rpow (hW0 x) (hWM x) hm10
  have hbPow := LocallyBoundedOnCompacts.of_global_bound hMpow0 hpowBound
  have hpowVd := hpowM1.mul hVd hbPow hbVd
  have hbPowVd := hbPow.mul hbVd
  have hchemCore := hpowVd.mul hdval hbPowVd hbP
  have hchem : LocallyUniformConverges
      (fun n => paperWaveChemTerm p (vs n) (vs n))
      (paperWaveChemTerm p W W) := by
    have hseq : (fun n => paperWaveChemTerm p (vs n) (vs n)) =
        fun n x => (-p.χ * p.m) *
          (((vs n x) ^ (p.m - 1) *
            deriv (frozenElliptic p (vs n)) x) * dvs n x) := by
      funext n x
      unfold paperWaveChemTerm paperWaveChemCore
      rw [congrFun (hvsDeriv n) x]
      ring
    have hlim : paperWaveChemTerm p W W = fun x =>
        (-p.χ * p.m) * (((W x) ^ (p.m - 1) *
          deriv (frozenElliptic p W) x) * P x) := by
      funext x
      unfold paperWaveChemTerm paperWaveChemCore
      rw [congrFun hWderiv x]
      ring
    rw [hseq, hlim]
    simpa [mul_assoc] using hchemCore.const_mul (-p.χ * p.m)
  have hpowV := hpowM1.mul hV hbPow hbV
  have hbPowV := hbPow.mul hbV
  have hleft := (hpowV.const_mul p.χ).const_sub 1
  have hright := hpowA.sub (hpowMG.const_mul p.χ)
  have hbracket : LocallyUniformConverges
      (fun n => paperWaveReactionBracket p (vs n) (vs n))
      (paperWaveReactionBracket p W W) := by
    simpa [paperWaveReactionBracket, mul_assoc] using hleft.sub hright
  have hbLeft := (hbPowV.const_mul p.χ).const_sub 1
  have hMα0 : 0 ≤ M ^ p.α := Real.rpow_nonneg hM.le _
  have hMmg0 : 0 ≤ M ^ (p.m + p.γ - 1) := Real.rpow_nonneg hM.le _
  have hbA := LocallyBoundedOnCompacts.of_global_bound hMα0 (fun x => by
    rw [abs_of_nonneg (Real.rpow_nonneg (hW0 x) _)]
    exact Real.rpow_le_rpow (hW0 x) (hWM x) (le_trans zero_le_one p.hα))
  have hbMG := LocallyBoundedOnCompacts.of_global_bound hMmg0 (fun x => by
    rw [abs_of_nonneg (Real.rpow_nonneg (hW0 x) _)]
    exact Real.rpow_le_rpow (hW0 x) (hWM x) (by linarith [p.hm, p.hγ]))
  have hbRight := hbA.sub (hbMG.const_mul p.χ)
  have hbBracket := hbLeft.sub hbRight
  have hreaction : LocallyUniformConverges
      (fun n => paperWaveReactionTerm p (vs n) (vs n))
      (paperWaveReactionTerm p W W) := by
    simpa [paperWaveReactionTerm] using hval.mul hbracket hbW hbBracket
  have hdrift : LocallyUniformConverges
      (fun n => paperWaveDriftTerm c (vs n))
      (paperWaveDriftTerm c W) := by
    have hseq : (fun n => paperWaveDriftTerm c (vs n)) =
        fun n x => c * dvs n x := by
      funext n x
      unfold paperWaveDriftTerm
      rw [congrFun (hvsDeriv n) x]
    have hlim : paperWaveDriftTerm c W = fun x => c * P x := by
      funext x
      unfold paperWaveDriftTerm
      rw [congrFun hWderiv x]
    rw [hseq, hlim]
    exact hdval.const_mul c
  let lower : ℕ → ℝ → ℝ := fun n x =>
    paperWaveDriftTerm c (vs n) x + paperWaveChemTerm p (vs n) (vs n) x +
      paperWaveReactionTerm p (vs n) (vs n) x
  let lowerLim : ℝ → ℝ := fun x =>
    paperWaveDriftTerm c W x + paperWaveChemTerm p W W x +
      paperWaveReactionTerm p W W x
  have hlowerConv : LocallyUniformConverges lower lowerLim := by
    simpa [lower, lowerLim, add_assoc] using (hdrift.add hchem).add hreaction
  let rhs : ℕ → ℝ → ℝ := fun n x => -lower n x
  let rhsLim : ℝ → ℝ := fun x => -lowerLim x
  have hrhs : LocallyUniformConverges rhs rhsLim := by
    simpa [rhs, rhsLim] using hlowerConv.neg
  have hpaperU : ∀ x, paperWaveOperator p c U U x = 0 := by
    intro x
    rw [paperWaveOperator_eq_frozenWaveOperator_at_fixed_point p x
      hU.bare.cunif_bdd hU.bare.nonneg
      (paperStep_hasDerivAt_value A x).differentiableAt
      (frozenElliptic_deriv_differentiableAt p hU.bare.cunif_bdd
        hU.bare.nonneg x)
      ((paperStep_hasDerivAt_value A x).rpow_const (Or.inr p.hm)).differentiableAt]
    exact hstat x
  have hpaperVs : ∀ n x, paperWaveOperator p c (vs n) (vs n) x = 0 := by
    intro n x
    dsimp [vs, us, sub]
    rw [paperWaveOperator_self_comp_add_const p hU.bare.cunif_bdd
      hU.bare.nonneg]
    exact hpaperU (x + a (sub₁ (sub₂ n)))
  have hsecondStep : ∀ n x, HasDerivAt (dvs n) (rhs n x) x := by
    intro n x
    have hbase := hdsHas (sub₂ n) x
    have hdd : iteratedDeriv 2 U (x + a (sub₁ (sub₂ n))) = rhs n x := by
      have hop := hpaperVs n x
      have hterms := congrFun (paperWaveOperator_eq_terms p c (vs n) (vs n)) x
      rw [hop] at hterms
      have hd2 : paperWaveD2Term (vs n) x =
          iteratedDeriv 2 U (x + a (sub₁ (sub₂ n))) := by
        unfold paperWaveD2Term
        dsimp [vs, us, sub]
        exact congrFun (iteratedDeriv_comp_add_const 2 U
          (a (sub₁ (sub₂ n)))) x
      dsimp [rhs, lower]
      rw [hd2] at hterms
      linarith
    exact hbase.congr_deriv hdd
  have hPhas : ∀ x, HasDerivAt P (rhsLim x) x := by
    intro x
    exact hasDerivAt_of_tendstoLocallyUniformlyOn
      (𝕜 := ℝ) (l := atTop) (s := (Set.univ : Set ℝ))
      (f := dvs) (g := P) (f' := rhs) (g' := rhsLim)
      isOpen_univ hrhs.tendstoLocallyUniformlyOn_univ
      (Eventually.of_forall fun n y _ => hsecondStep n y)
      (fun y _ => hdval.tendsto_at y) (Set.mem_univ x)
  have hPdiff : Differentiable ℝ P := fun x => (hPhas x).differentiableAt
  have hLowerCont : Continuous lowerLim := by
    have hPcont : Continuous P := hPdiff.continuous
    have hVcont := frozenElliptic_continuous p hWbdd hW0
    have hVdcont : Continuous (deriv (frozenElliptic p W)) :=
      continuous_iff_continuousAt.mpr fun x =>
        (frozenElliptic_deriv_differentiableAt p hWbdd hW0 x).continuousAt
    have hWm1cont : Continuous (fun x => (W x) ^ (p.m - 1)) :=
      hWcont.rpow_const (fun _ => Or.inr hm10)
    have hWAcont : Continuous (fun x => (W x) ^ p.α) :=
      hWcont.rpow_const (fun _ => Or.inr (le_trans zero_le_one p.hα))
    have hWMGcont : Continuous (fun x => (W x) ^ (p.m + p.γ - 1)) :=
      hWcont.rpow_const (fun _ => Or.inr (by linarith [p.hm, p.hγ]))
    have hchemCont : Continuous (fun x =>
        -(p.χ * p.m) * ((W x) ^ (p.m - 1) *
          (deriv (frozenElliptic p W) x * P x))) :=
      continuous_const.mul (hWm1cont.mul (hVdcont.mul hPcont))
    have hbracketCont : Continuous (fun x =>
        1 - p.χ * ((W x) ^ (p.m - 1) * frozenElliptic p W x) -
          ((W x) ^ p.α - p.χ * (W x) ^ (p.m + p.γ - 1))) :=
      (continuous_const.sub
        (continuous_const.mul (hWm1cont.mul hVcont))).sub
          (hWAcont.sub (continuous_const.mul hWMGcont))
    dsimp [lowerLim, paperWaveDriftTerm, paperWaveChemTerm, paperWaveChemCore,
      paperWaveReactionTerm, paperWaveReactionBracket]
    rw [hWderiv]
    simpa [mul_assoc] using
      ((continuous_const.mul hPcont).add hchemCont).add
        (hWcont.mul hbracketCont)
  have hW2 : ContDiff ℝ 2 W := by
    have hWdiff : Differentiable ℝ W := fun x => (hWhas x).differentiableAt
    have hP1 : ContDiff ℝ 1 P := by
      rw [contDiff_one_iff_deriv]
      exact ⟨hPdiff, by
        have hrhsDeriv : deriv P = rhsLim := by funext x; exact (hPhas x).deriv
        rw [hrhsDeriv]
        exact hLowerCont.neg⟩
    have hW2' : ContDiff ℝ ((1 : ℕ∞) + 1) W := by
      rw [contDiff_succ_iff_deriv]
      exact ⟨hWdiff, by simp, by simpa [hWderiv] using hP1⟩
    simpa using hW2'
  have hpaperW : ∀ x, paperWaveOperator p c W W x = 0 := by
    intro x
    have hPd := (hPhas x).deriv
    have hD2 : paperWaveD2Term W x = rhsLim x := by
      unfold paperWaveD2Term
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
        iteratedDeriv_one, hWderiv]
      exact hPd
    have hterms := congrFun (paperWaveOperator_eq_terms p c W W) x
    rw [hterms, hD2]
    dsimp [rhsLim, lowerLim]
    ring
  have hstatW : ∀ x, frozenWaveOperator p c W W x = 0 := by
    intro x
    rw [← paperWaveOperator_eq_frozenWaveOperator_at_fixed_point p x
      hWbdd hW0 (hW2.differentiable (by norm_num) x)
      (frozenElliptic_deriv_differentiableAt p hWbdd hW0 x)
      ((hW2.differentiable (by norm_num) x).rpow_const (Or.inr p.hm))]
    exact hpaperW x
  have haSub : ∀ n, a (sub n) < -(n : ℝ) := by
    intro n
    have hid : n ≤ sub n := StrictMono.id_le hsub n
    have hcast : (n : ℝ) ≤ (sub n : ℝ) := by exact_mod_cast hid
    exact lt_of_lt_of_le (ha (sub n)) (by linarith)
  have hclusterLower := lowerPinned_leftTranslationCluster_lower
    hκ hgap hD hU.lower haSub (by simpa [vs] using hval)
  exact ⟨sub, hsub, W, by simpa [vs] using hval, hWbdd, hW0, hWM,
    hclusterLower, hW2, hstatW⟩

/-- The positive Schauder fixed point approaches the positive equilibrium at
the left endpoint.  The proof is a translation-cluster contradiction; no
spatial monotonicity is used. -/
theorem positiveStationary_tendsto_atBot_one
    (p : CMParams) {c lam κ M κtilde D Λ : ℝ} {U : ℝ → ℝ}
    (hα : p.α = p.m + p.γ - 1)
    (hχ0 : 0 ≤ p.χ) (hχhalf : p.χ < 1 / 2)
    (hM : 0 < M) (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D)
    (hU : InLowerPinnedC1UniformModulusWaveTrap κ M
      (max 1 Λ) (lowerBarrierPlateau κ κtilde D) U)
    (A : PaperStepAnalytic p c lam M κ Λ U U U)
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0) :
    Tendsto U atBot (nhds 1) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  by_contra hnot
  rw [Filter.not_eventually] at hnot
  simp only [Real.dist_eq, not_lt] at hnot
  rw [frequently_atBot'] at hnot
  have hbad : ∀ n : ℕ, ∃ x, x < -(n : ℝ) ∧ ε ≤ |U x - 1| := by
    intro n
    exact hnot (-(n : ℝ))
  choose a ha hfar using hbad
  obtain ⟨sub, hsub, W, hconv, hWbdd, hW0, hWM, hWlower, hW2, hstatW⟩ :=
    positiveStationary_leftTranslationCluster p hM hκ hgap hD hU A
      hlam hΛ hstat ha
  let d := lowerBarrierRaw κ κtilde D (lowerBarrierXPlus κ κtilde D)
  have hd : 0 < d := lowerBarrierRaw_pos_at_xplus hκ hgap hD
  have hWone : W = fun _ => (1 : ℝ) :=
    positiveStationary_eq_one_of_uniformlyPositive p hα hχ0 hχhalf
      hM hd hWbdd hW0 hWM hWlower hW2 hstatW
  have hbadSub : ∀ n, ε ≤ |U (a (sub n)) - 1| := fun n => hfar (sub n)
  have hlimit0 : Tendsto (fun n => U (a (sub n))) atTop (nhds (W 0)) := by
    have := hconv.tendsto_at 0
    simpa using this
  have haway : ε ≤ |W 0 - 1| :=
    ge_of_tendsto (hlimit0.sub_const 1).abs (Eventually.of_forall hbadSub)
  rw [hWone] at haway
  norm_num at haway
  linarith

section AxiomAudit

#print axioms frozenElliptic_comp_add_const
#print axioms positiveStationary_leftTranslationCluster
#print axioms positiveStationary_tendsto_atBot_one

end AxiomAudit

end ShenWork.Paper1
