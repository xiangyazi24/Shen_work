import ShenWork.PDE.IntervalDuhamelSpectralDerivOn
import ShenWork.Paper2.IntervalPicardLimitRestartWeak
import ShenWork.Wiener.EWA.SourceReducedCoreWire
import ShenWork.Wiener.EWA.SourceJointRegularityOn

noncomputable section

namespace ShenWork.EWA

open scoped BigOperators
open MeasureTheory Set Filter Topology
open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff)
open ShenWork.IntervalPicardLimitRestartWeak
  (DuhamelSourceL1ContOn abs_duhamelSpectralCoeff_le_weak)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs)
open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildRegularityBootstrap
  (unitIntervalCosineEigenvalue_mul_exp_summable)

variable {T : ℝ}

/-! ## 1a. L1-continuous Duhamel spectral coefficient derivative -/

/-- Windowed spectral Duhamel ODE from `DuhamelSourceL1ContOn`. -/
theorem duhamelSpectralCoeff_hasDerivAt_of_L1ContOn
    {a : ℝ → ℕ → ℝ} {T : ℝ} (src : DuhamelSourceL1ContOn a T)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (n : ℕ) :
    HasDerivAt (fun r => duhamelSpectralCoeff a r n)
      (a t n - unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a t n) t := by
  set lam := unitIntervalCosineEigenvalue n
  have hcontOn := src.hcont n
  have hcont_at : ContinuousAt (fun s => a s n) t :=
    hcontOn.continuousAt (Icc_mem_nhds ht0 htT)
  set G : ℝ → ℝ := fun r => ∫ s in (0 : ℝ)..r, Real.exp (s * lam) * a s n
  have hfactor : ∀ r, duhamelSpectralCoeff a r n = Real.exp (-r * lam) * G r := by
    intro r
    show (∫ s in (0 : ℝ)..r, _) = _
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun s _ => by
      rw [show -(r - s) * lam = -r * lam + s * lam from by ring,
        Real.exp_add, mul_assoc])
  have hd_exp : HasDerivAt (fun r => Real.exp (-r * lam))
      (-lam * Real.exp (-t * lam)) t := by
    have h1 : HasDerivAt (fun r : ℝ => -r * lam) (-1 * lam) t :=
      (hasDerivAt_id t).neg.mul_const lam
    have h2 := h1.exp
    simp only [neg_mul, one_mul] at h2 ⊢
    convert h2 using 1
    ring
  set integrand := fun s => Real.exp (s * lam) * a s n
  have hI_contOn : ContinuousOn integrand (Icc 0 T) :=
    ((Real.continuous_exp.comp (continuous_id.mul continuous_const)).continuousOn).mul
      hcontOn
  have hG_ii : IntervalIntegrable integrand volume 0 t :=
    (hI_contOn.mono (Icc_subset_Icc le_rfl htT.le)).intervalIntegrable_of_Icc ht0.le
  have hG_ca : ContinuousAt integrand t :=
    hI_contOn.continuousAt (Icc_mem_nhds ht0 htT)
  have hG_smf : StronglyMeasurableAtFilter integrand (𝓝 t) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
      (hI_contOn.mono Ioo_subset_Icc_self) t ⟨ht0, htT⟩
  have hd_G : HasDerivAt G (Real.exp (t * lam) * a t n) t :=
    intervalIntegral.integral_hasDerivAt_right hG_ii hG_smf hG_ca
  have hexp_cancel : Real.exp (-t * lam) * Real.exp (t * lam) = 1 := by
    rw [← Real.exp_add, show -t * lam + t * lam = 0 from by ring, Real.exp_zero]
  have hderiv_val : -lam * Real.exp (-t * lam) * G t +
      Real.exp (-t * lam) * (Real.exp (t * lam) * a t n) =
      a t n - lam * (Real.exp (-t * lam) * G t) := by
    rw [← mul_assoc (Real.exp _), hexp_cancel, one_mul]
    ring
  rw [show (fun r => duhamelSpectralCoeff a r n) =
      (fun r => Real.exp (-r * lam) * G r) from funext hfactor, hfactor t]
  exact (hd_exp.mul hd_G).congr_deriv hderiv_val

/-- Windowed continuity of the Duhamel spectral coefficient on `(0,T)`. -/
theorem duhamelSpectralCoeff_continuous_of_L1ContOn
    {a : ℝ → ℕ → ℝ} {T : ℝ} (src : DuhamelSourceL1ContOn a T) (n : ℕ) :
    ContinuousOn (fun r => duhamelSpectralCoeff a r n) (Ioo 0 T) :=
  fun _ ht =>
    ContinuousAt.continuousWithinAt
      (HasDerivAt.continuousAt
        (duhamelSpectralCoeff_hasDerivAt_of_L1ContOn src ht.1 ht.2 n))

/-! ## 1b. L1-continuous derivative of `fullSourceCoeff` -/

private theorem fullSourceCoeff_hasDerivAt_of_L1ContOn (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ)
    (hchem : DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs p u) T)
    (hlog : DuhamelSourceL1ContOn (coupledLogisticSourceCoeffs p u) T)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (n : ℕ) :
    HasDerivAt (fun s => fullSourceCoeff p u u₀cos s n)
      (fullSourceCoeffDot p u u₀cos t n) t := by
  have hexp : HasDerivAt (fun r : ℝ => Real.exp (-r * unitIntervalCosineEigenvalue n))
      (-unitIntervalCosineEigenvalue n *
        Real.exp (-t * unitIntervalCosineEigenvalue n)) t := by
    have h1 : HasDerivAt (fun r : ℝ => -r * unitIntervalCosineEigenvalue n)
        (-1 * unitIntervalCosineEigenvalue n) t :=
      (hasDerivAt_id t).neg.mul_const (unitIntervalCosineEigenvalue n)
    have h2 := h1.exp
    simp only [neg_mul, one_mul] at h2 ⊢
    convert h2 using 1
    ring
  exact ((hexp.mul_const _).add
    ((duhamelSpectralCoeff_hasDerivAt_of_L1ContOn hchem ht0 htT n).const_mul _)).add
    (duhamelSpectralCoeff_hasDerivAt_of_L1ContOn hlog ht0 htT n)

/-! ## 1c. Direct semigroup bound for the Duhamel derivative coefficient -/

private theorem duhamelDeriv_abs_le_two_env
    {a : ℝ → ℕ → ℝ} {T : ℝ} (src : DuhamelSourceL1ContOn a T)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (n : ℕ) :
    |a t n - unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a t n|
      ≤ 2 * src.envelope n := by
  have hlam : (0 : ℝ) ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue
    positivity
  have hsrc : |a t n| ≤ src.envelope n :=
    src.henv_bound t ht.le htT n
  have hduh :
      |unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a t n|
        ≤ src.envelope n := by
    rw [abs_mul, abs_of_nonneg hlam]
    exact eigenvalue_mul_abs_duhamelSpectralCoeff_le_envelope src ht htT n
  have htri :
      |a t n - unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a t n|
        ≤ |a t n| + |unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a t n| := by
    simpa [sub_eq_add_neg, abs_neg] using
      abs_add_le (a t n) (-(unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a t n))
  calc
    |a t n - unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a t n|
        ≤ |a t n| + |unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a t n| :=
          htri
    _ ≤ src.envelope n + src.envelope n := add_le_add hsrc hduh
    _ = 2 * src.envelope n := by ring

/-! ## 1d-1f. Direct derivative majorant -/

private noncomputable def dotMajDirect (p : CM2Params)
    (Mu0 c : ℝ) (chemEnv logEnv : ℕ → ℝ) (n : ℕ) : ℝ :=
  Mu0 * (unitIntervalCosineEigenvalue n *
      Real.exp (-c * unitIntervalCosineEigenvalue n))
    + 2 * |p.χ₀| * chemEnv n + 2 * logEnv n

private theorem dotMajDirect_summable (p : CM2Params) (Mu0 : ℝ)
    {c : ℝ} (hc : 0 < c) (chemEnv logEnv : ℕ → ℝ)
    (hchemSum : Summable chemEnv) (hlogSum : Summable logEnv) :
    Summable (dotMajDirect p Mu0 c chemEnv logEnv) := by
  unfold dotMajDirect
  have hheat : Summable (fun n => Mu0 * (unitIntervalCosineEigenvalue n *
      Real.exp (-c * unitIntervalCosineEigenvalue n))) :=
    (unitIntervalCosineEigenvalue_mul_exp_summable hc).mul_left Mu0
  have hchem : Summable (fun n => 2 * |p.χ₀| * chemEnv n) :=
    hchemSum.mul_left (2 * |p.χ₀|)
  have hlog : Summable (fun n => 2 * logEnv n) :=
    hlogSum.mul_left 2
  exact (hheat.add hchem).add hlog

private theorem dotMajDirect_bound (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs p u) T)
    (hlog : DuhamelSourceL1ContOn (coupledLogisticSourceCoeffs p u) T)
    {c : ℝ} (hc : 0 < c) (_hcT : c < T) (x : ℝ) (n : ℕ)
    (s : ℝ) (hs : s ∈ Ioo c T) :
    ‖fullSourceCoeffDot p u u₀cos s n * cosineMode n x‖ ≤
      dotMajDirect p Mu0 c hchem.envelope hlog.envelope n := by
  have hcs : c ≤ s := hs.1.le
  have hsT : s ≤ T := hs.2.le
  have hspos : 0 < s := lt_of_lt_of_le hc hcs
  have hlam : (0 : ℝ) ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue
    positivity
  have hheat : |-(unitIntervalCosineEigenvalue n) *
        Real.exp (-s * unitIntervalCosineEigenvalue n) * u₀cos n|
      ≤ Mu0 * (unitIntervalCosineEigenvalue n *
          Real.exp (-c * unitIntervalCosineEigenvalue n)) := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hlam,
      abs_of_nonneg (Real.exp_nonneg _), mul_comm Mu0]
    exact mul_le_mul (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp_of_le (by nlinarith [hcs, hlam])) hlam) (hu0bd n)
      (abs_nonneg _) (by positivity)
  have hchemLeg : |(-p.χ₀) * (coupledChemDivSourceCoeffs p u s n
        - unitIntervalCosineEigenvalue n *
          duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) s n)|
      ≤ 2 * |p.χ₀| * hchem.envelope n := by
    rw [abs_mul, abs_neg]
    calc
      |p.χ₀| * |coupledChemDivSourceCoeffs p u s n
          - unitIntervalCosineEigenvalue n *
            duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) s n|
          ≤ |p.χ₀| * (2 * hchem.envelope n) :=
            mul_le_mul_of_nonneg_left
              (duhamelDeriv_abs_le_two_env hchem hspos hsT n) (abs_nonneg _)
      _ = 2 * |p.χ₀| * hchem.envelope n := by ring
  have hlogLeg : |coupledLogisticSourceCoeffs p u s n
        - unitIntervalCosineEigenvalue n *
          duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) s n|
      ≤ 2 * hlog.envelope n :=
    duhamelDeriv_abs_le_two_env hlog hspos hsT n
  rw [Real.norm_eq_abs, abs_mul]
  calc
    |fullSourceCoeffDot p u u₀cos s n| * |cosineMode n x|
        ≤ |fullSourceCoeffDot p u u₀cos s n| :=
          mul_le_of_le_one_right (abs_nonneg _) (by
            simp only [cosineMode]
            exact Real.abs_cos_le_one _)
    _ ≤ dotMajDirect p Mu0 c hchem.envelope hlog.envelope n := by
        simp only [fullSourceCoeffDot, dotMajDirect]
        calc
          _ ≤ |-(unitIntervalCosineEigenvalue n) *
                  Real.exp (-s * unitIntervalCosineEigenvalue n) * u₀cos n|
                + |(-p.χ₀) * (coupledChemDivSourceCoeffs p u s n
                    - unitIntervalCosineEigenvalue n *
                      duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) s n)|
                + |coupledLogisticSourceCoeffs p u s n
                    - unitIntervalCosineEigenvalue n *
                      duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) s n| :=
              abs_add_three _ _ _
          _ ≤ _ := add_le_add (add_le_add hheat hchemLeg) hlogLeg

/-! ## 1g. Value summability for `fullSourceCoeff` -/

private theorem fsc_summable_of_L1ContOn (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs p u) T)
    (hlog : DuhamelSourceL1ContOn (coupledLogisticSourceCoeffs p u) T)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (x : ℝ) :
    Summable (fun n => fullSourceCoeff p u u₀cos t n * cosineMode n x) := by
  have hM : 0 ≤ Mu0 := le_trans (abs_nonneg _) (hu0bd 0)
  refine Summable.of_norm ((((
    (ShenWork.HeatKernelGradientEstimates.unitIntervalCosineHeatTrace_single_exp_summable
      ht).mul_left Mu0).add
    ((hchem.henv_summable.mul_left t).mul_left |(-p.χ₀)|)).add
    (hlog.henv_summable.mul_left t)).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  calc
    |fullSourceCoeff p u u₀cos t n| * |cosineMode n x|
        ≤ |fullSourceCoeff p u u₀cos t n| :=
          mul_le_of_le_one_right (abs_nonneg _) (by
            simp only [cosineMode]
            exact Real.abs_cos_le_one _)
    _ ≤ _ := by
        simp only [fullSourceCoeff]
        calc
          _ ≤ |Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n|
                + |(-p.χ₀) *
                    duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n|
                + |duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) t n| :=
              abs_add_three _ _ _
          _ ≤ _ := by
              gcongr
              · rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _), mul_comm]
                exact mul_le_mul_of_nonneg_right (hu0bd n) (Real.exp_nonneg _)
              · rw [abs_mul]
                exact mul_le_mul_of_nonneg_left
                  (abs_duhamelSpectralCoeff_le_weak hchem ht htT n) (abs_nonneg _)
              · exact abs_duhamelSpectralCoeff_le_weak hlog ht htT n

/-! ## 1h. Term-by-term synthesis differentiation -/

theorem synthesis_hasDerivAt_of_L1ContOn (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs p u) T)
    (hlog : DuhamelSourceL1ContOn (coupledLogisticSourceCoeffs p u) T)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) T) (x : ℝ) :
    HasDerivAt (fun s => ∑' n, fullSourceCoeff p u u₀cos s n * cosineMode n x)
      (∑' n, fullSourceCoeffDot p u u₀cos t₀ n * cosineMode n x) t₀ := by
  set c := t₀ / 2 with hc_def
  have ht0_pos : 0 < t₀ := ht₀.1
  have ht0_lt_T : t₀ < T := ht₀.2
  have hc : 0 < c := by
    rw [hc_def]
    linarith
  have hcT : c < T := by
    rw [hc_def]
    linarith
  have hc_lt_t0 : c < t₀ := by
    rw [hc_def]
    linarith
  exact hasDerivAt_tsum_of_isPreconnected
    (dotMajDirect_summable p Mu0 hc hchem.envelope hlog.envelope
      hchem.henv_summable hlog.henv_summable)
    isOpen_Ioo isPreconnected_Ioo
    (fun n s hs => (fullSourceCoeff_hasDerivAt_of_L1ContOn p u u₀cos hchem hlog
      (lt_trans hc hs.1) hs.2 n).mul_const _)
    (fun n s hs => dotMajDirect_bound p u u₀cos hu0bd hchem hlog hc hcT x n s hs)
    ⟨hc_lt_t0, ht0_lt_T⟩
    (fsc_summable_of_L1ContOn p u u₀cos hu0bd hchem hlog ht0_pos ht0_lt_T.le x)
    ⟨hc_lt_t0, ht0_lt_T⟩

/-! ## 1i. Duhamel value and derivative series joint continuity -/

private theorem cosineMode_abs_le_one_L1 (n : ℕ) (x : ℝ) :
    |cosineMode n x| ≤ 1 := by
  simp only [cosineMode]
  exact Real.abs_cos_le_one _

private theorem cosineMode_continuous_L1 (n : ℕ) :
    Continuous (fun x : ℝ => cosineMode n x) :=
  Real.continuous_cos.comp (continuous_const.mul continuous_id)

/-- L1-continuous Duhamel VALUE leg: joint continuity on `Ioo 0 T ×ˢ univ`. -/
theorem duhamelSeries_jointContinuousOn_of_L1ContOn
    {a : ℝ → ℕ → ℝ} {T : ℝ} (src : DuhamelSourceL1ContOn a T) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          ∑' n, duhamelSpectralCoeff a t n * cosineMode n x))
      (Ioo (0 : ℝ) T ×ˢ univ) := by
  change ContinuousOn
    (fun p : ℝ × ℝ => ∑' n, duhamelSpectralCoeff a p.1 n * cosineMode n p.2)
    (Ioo 0 T ×ˢ univ)
  apply continuousOn_of_forall_continuousAt
  intro p hp
  obtain ⟨hτ₀, _⟩ := mem_prod.1 hp
  have hτ₀_pos : 0 < p.1 := (mem_Ioo.1 hτ₀).1
  have hτ₀_lt_T : p.1 < T := (mem_Ioo.1 hτ₀).2
  have h0T : (0 : ℝ) ≤ T := le_of_lt (lt_trans hτ₀_pos hτ₀_lt_T)
  set c := p.1 / 2 with hc_def
  set d := (p.1 + T) / 2 with hd_def
  have hc_pos : 0 < c := by
    rw [hc_def]
    linarith
  have hd_le_T : d ≤ T := by
    simp [hd_def]
    linarith
  have hp_in_cd : p.1 ∈ Ioo c d := by
    constructor <;> simp [hc_def, hd_def] <;> linarith
  have henv_nn : ∀ n, 0 ≤ src.envelope n := fun n =>
    le_trans (abs_nonneg _) (src.henv_bound 0 le_rfl h0T n)
  have hu : Summable (fun n => T * src.envelope n) :=
    src.henv_summable.mul_left T
  have hcont_on : ContinuousOn
      (fun q : ℝ × ℝ => ∑' n, duhamelSpectralCoeff a q.1 n * cosineMode n q.2)
      (Ioo c d ×ˢ univ) := by
    apply continuousOn_tsum
    · intro n
      apply ContinuousOn.mul
      · exact ((duhamelSpectralCoeff_continuous_of_L1ContOn src n).comp
          continuous_fst.continuousOn (fun q hq =>
            let ⟨hτ, _⟩ := mem_prod.1 hq
            ⟨lt_trans hc_pos (mem_Ioo.1 hτ).1,
             lt_of_lt_of_le (mem_Ioo.1 hτ).2 hd_le_T⟩))
      · exact ((cosineMode_continuous_L1 n).comp continuous_snd).continuousOn
    · exact hu
    · intro n q hq
      obtain ⟨hτ, _⟩ := mem_prod.1 hq
      have hτ_pos : 0 < q.1 := lt_trans hc_pos (mem_Ioo.1 hτ).1
      have hτ_le_T : q.1 ≤ T := le_trans (mem_Ioo.1 hτ).2.le hd_le_T
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |duhamelSpectralCoeff a q.1 n| * |cosineMode n q.2|
            ≤ (q.1 * src.envelope n) * 1 :=
              mul_le_mul (abs_duhamelSpectralCoeff_le_weak src hτ_pos hτ_le_T n)
                (cosineMode_abs_le_one_L1 n q.2) (abs_nonneg _)
                (mul_nonneg hτ_pos.le (henv_nn n))
        _ = q.1 * src.envelope n := mul_one _
        _ ≤ T * src.envelope n :=
            mul_le_mul_of_nonneg_right hτ_le_T (henv_nn n)
  exact hcont_on.continuousAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      (mem_prod.2 ⟨hp_in_cd, mem_univ _⟩))

/-- L1-continuous Duhamel DERIVATIVE leg: joint continuity on `Ioo 0 T ×ˢ univ`. -/
theorem duhamelDerivSeries_jointContinuousOn_of_L1ContOn
    {a : ℝ → ℕ → ℝ} {T : ℝ} (src : DuhamelSourceL1ContOn a T) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          ∑' n, (a t n - unitIntervalCosineEigenvalue n *
            duhamelSpectralCoeff a t n) * cosineMode n x))
      (Ioo (0 : ℝ) T ×ˢ univ) := by
  change ContinuousOn
    (fun p : ℝ × ℝ => ∑' n,
      (a p.1 n - unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a p.1 n) *
        cosineMode n p.2)
    (Ioo 0 T ×ˢ univ)
  apply continuousOn_of_forall_continuousAt
  intro p hp
  obtain ⟨hτ₀, _⟩ := mem_prod.1 hp
  have hτ₀_pos : 0 < p.1 := (mem_Ioo.1 hτ₀).1
  have hτ₀_lt_T : p.1 < T := (mem_Ioo.1 hτ₀).2
  have h0T : (0 : ℝ) ≤ T := le_of_lt (lt_trans hτ₀_pos hτ₀_lt_T)
  set c := p.1 / 2 with hc_def
  set d := (p.1 + T) / 2 with hd_def
  have hc_pos : 0 < c := by
    rw [hc_def]
    linarith
  have hd_le_T : d ≤ T := by
    simp [hd_def]
    linarith
  have hp_in_cd : p.1 ∈ Ioo c d := by
    constructor <;> simp [hc_def, hd_def] <;> linarith
  have henv_nn : ∀ n, 0 ≤ src.envelope n := fun n =>
    le_trans (abs_nonneg _) (src.henv_bound 0 le_rfl h0T n)
  have hu : Summable (fun n => 2 * src.envelope n) :=
    src.henv_summable.mul_left 2
  have hu_nn : ∀ n, 0 ≤ 2 * src.envelope n := fun n =>
    mul_nonneg (by norm_num) (henv_nn n)
  have hcont_on : ContinuousOn
      (fun q : ℝ × ℝ => ∑' n,
        (a q.1 n - unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a q.1 n) *
          cosineMode n q.2)
      (Ioo c d ×ˢ univ) := by
    apply continuousOn_tsum
    · intro n
      apply ContinuousOn.mul
      · apply ContinuousOn.sub
        · exact ((src.hcont n).comp continuous_fst.continuousOn (fun q hq =>
            let ⟨hτ, _⟩ := mem_prod.1 hq
            ⟨le_of_lt (lt_trans hc_pos (mem_Ioo.1 hτ).1),
             le_trans (mem_Ioo.1 hτ).2.le hd_le_T⟩))
        · exact ((continuous_const).continuousOn.mul
            ((duhamelSpectralCoeff_continuous_of_L1ContOn src n).comp
              continuous_fst.continuousOn (fun q hq =>
                let ⟨hτ, _⟩ := mem_prod.1 hq
                ⟨lt_trans hc_pos (mem_Ioo.1 hτ).1,
                 lt_of_lt_of_le (mem_Ioo.1 hτ).2 hd_le_T⟩)))
      · exact ((cosineMode_continuous_L1 n).comp continuous_snd).continuousOn
    · exact hu
    · intro n q hq
      obtain ⟨hτ, _⟩ := mem_prod.1 hq
      have hτ_pos : 0 < q.1 := lt_trans hc_pos (mem_Ioo.1 hτ).1
      have hτ_le_T : q.1 ≤ T := le_trans (mem_Ioo.1 hτ).2.le hd_le_T
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |a q.1 n - unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a q.1 n| *
              |cosineMode n q.2|
            ≤ (2 * src.envelope n) * 1 :=
              mul_le_mul (duhamelDeriv_abs_le_two_env src hτ_pos hτ_le_T n)
                (cosineMode_abs_le_one_L1 n q.2) (abs_nonneg _) (hu_nn n)
        _ = 2 * src.envelope n := mul_one _
  exact hcont_on.continuousAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      (mem_prod.2 ⟨hp_in_cd, mem_univ _⟩))

/-! ## 1j. Three-leg splits and full joint continuity -/

private theorem heatValueSeries_jointContinuousOn_L1 (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0) :
    ContinuousOn
      (fun q : ℝ × ℝ =>
        ∑' n, Real.exp (-q.1 * unitIntervalCosineEigenvalue n) *
          u₀cos n * cosineMode n q.2)
      (Ioi (0 : ℝ) ×ˢ univ) := by
  have hMu0 : 0 ≤ Mu0 := le_trans (abs_nonneg _) (hu0bd 0)
  apply continuousOn_of_forall_continuousAt
  intro p hp
  obtain ⟨hp1, _⟩ := mem_prod.1 hp
  have hp1 : 0 < p.1 := mem_Ioi.1 hp1
  set c := p.1 / 2 with hc_def
  have hc : 0 < c := by
    rw [hc_def]
    linarith
  have hcont : ContinuousOn
      (fun q : ℝ × ℝ =>
        ∑' n, Real.exp (-q.1 * unitIntervalCosineEigenvalue n) *
          u₀cos n * cosineMode n q.2)
      (Ioo c (p.1 + 1) ×ˢ univ) := by
    apply continuousOn_tsum
    · intro n
      have hheat : Continuous (fun t : ℝ =>
          Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n) :=
        (Real.continuous_exp.comp (continuous_id.neg.mul continuous_const)).mul
          continuous_const
      exact ((hheat.comp continuous_fst).mul
        ((cosineMode_continuous_L1 n).comp continuous_snd)).continuousOn
    · exact (ShenWork.HeatKernelGradientEstimates.unitIntervalCosineHeatTrace_single_exp_summable
        hc).mul_left Mu0
    · intro n q hq
      obtain ⟨ht, _⟩ := mem_prod.1 hq
      obtain ⟨hct, _⟩ := mem_Ioo.1 ht
      have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
        unfold unitIntervalCosineEigenvalue
        positivity
      rw [Real.norm_eq_abs,
        show Real.exp (-q.1 * unitIntervalCosineEigenvalue n) *
              u₀cos n * cosineMode n q.2 =
            Real.exp (-q.1 * unitIntervalCosineEigenvalue n) *
              (u₀cos n * cosineMode n q.2) from by ring,
        abs_mul, abs_of_nonneg (Real.exp_nonneg _), mul_comm Mu0]
      refine mul_le_mul ?_ ?_ (abs_nonneg _) (Real.exp_nonneg _)
      · exact Real.exp_le_exp_of_le (by nlinarith [hct, hlam])
      · rw [abs_mul]
        calc
          |u₀cos n| * |cosineMode n q.2|
              ≤ Mu0 * 1 :=
                mul_le_mul (hu0bd n) (cosineMode_abs_le_one_L1 n q.2)
                  (abs_nonneg _) hMu0
          _ = Mu0 := mul_one _
  exact hcont.continuousAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      (mem_prod.2
        ⟨mem_Ioo.2 ⟨by simp [hc_def]; linarith, by linarith⟩, mem_univ _⟩))

private theorem heatDerivSeries_jointContinuousOn_L1 (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0) :
    ContinuousOn
      (fun q : ℝ × ℝ =>
        ∑' n, -(unitIntervalCosineEigenvalue n) *
          Real.exp (-q.1 * unitIntervalCosineEigenvalue n) *
          u₀cos n * cosineMode n q.2)
      (Ioi (0 : ℝ) ×ˢ univ) := by
  have hMu0 : 0 ≤ Mu0 := le_trans (abs_nonneg _) (hu0bd 0)
  apply continuousOn_of_forall_continuousAt
  intro p hp
  obtain ⟨hp1, _⟩ := mem_prod.1 hp
  have hp1 : 0 < p.1 := mem_Ioi.1 hp1
  set c := p.1 / 2 with hc_def
  have hc : 0 < c := by
    rw [hc_def]
    linarith
  have hcont : ContinuousOn
      (fun q : ℝ × ℝ =>
        ∑' n, -(unitIntervalCosineEigenvalue n) *
          Real.exp (-q.1 * unitIntervalCosineEigenvalue n) *
          u₀cos n * cosineMode n q.2)
      (Ioo c (p.1 + 1) ×ˢ univ) := by
    apply continuousOn_tsum
    · intro n
      have hheat : Continuous (fun t : ℝ => -(unitIntervalCosineEigenvalue n) *
          Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n) :=
        (continuous_const.mul
          (Real.continuous_exp.comp (continuous_id.neg.mul continuous_const))).mul
          continuous_const
      exact ((hheat.comp continuous_fst).mul
        ((cosineMode_continuous_L1 n).comp continuous_snd)).continuousOn
    · exact (unitIntervalCosineEigenvalue_mul_exp_summable hc).mul_left Mu0
    · intro n q hq
      obtain ⟨ht, _⟩ := mem_prod.1 hq
      obtain ⟨hct, _⟩ := mem_Ioo.1 ht
      have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
        unfold unitIntervalCosineEigenvalue
        positivity
      rw [Real.norm_eq_abs,
        show -(unitIntervalCosineEigenvalue n) *
              Real.exp (-q.1 * unitIntervalCosineEigenvalue n) *
              u₀cos n * cosineMode n q.2 =
            -(unitIntervalCosineEigenvalue n *
              Real.exp (-q.1 * unitIntervalCosineEigenvalue n) *
              u₀cos n * cosineMode n q.2) from by ring,
        abs_neg, abs_mul, abs_mul, abs_mul, abs_of_nonneg hlam,
        abs_of_nonneg (Real.exp_nonneg _)]
      have hexp : Real.exp (-q.1 * unitIntervalCosineEigenvalue n) ≤
          Real.exp (-c * unitIntervalCosineEigenvalue n) :=
        Real.exp_le_exp_of_le (by nlinarith [hct, hlam])
      calc
        unitIntervalCosineEigenvalue n *
              Real.exp (-q.1 * unitIntervalCosineEigenvalue n) *
              |u₀cos n| * |cosineMode n q.2|
            ≤ unitIntervalCosineEigenvalue n *
                Real.exp (-c * unitIntervalCosineEigenvalue n) * Mu0 * 1 := by
              apply mul_le_mul (mul_le_mul
                (mul_le_mul_of_nonneg_left hexp hlam) (hu0bd n)
                (abs_nonneg _) (by positivity)) (cosineMode_abs_le_one_L1 n q.2)
                (abs_nonneg _) (by positivity)
        _ = Mu0 * (unitIntervalCosineEigenvalue n *
              Real.exp (-c * unitIntervalCosineEigenvalue n)) := by ring
  exact hcont.continuousAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      (mem_prod.2
        ⟨mem_Ioo.2 ⟨by simp [hc_def]; linarith, by linarith⟩, mem_univ _⟩))

private theorem heatVal_summable_L1 (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Summable (fun n =>
      Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n x) := by
  have hMu0 : 0 ≤ Mu0 := le_trans (abs_nonneg _) (hu0bd 0)
  refine Summable.of_norm_bounded
    (g := fun n => Real.exp (-t * unitIntervalCosineEigenvalue n) * Mu0)
    ((ShenWork.HeatKernelGradientEstimates.unitIntervalCosineHeatTrace_single_exp_summable
      ht).mul_right Mu0) (fun n => ?_)
  rw [Real.norm_eq_abs,
    show Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n x =
      Real.exp (-t * unitIntervalCosineEigenvalue n) * (u₀cos n * cosineMode n x)
      from by ring,
    abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
  rw [abs_mul]
  calc
    |u₀cos n| * |cosineMode n x|
        ≤ Mu0 * 1 := mul_le_mul (hu0bd n) (cosineMode_abs_le_one_L1 n x)
          (abs_nonneg _) hMu0
    _ = Mu0 := mul_one _

private theorem heatDerivVal_summable_L1 (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Summable (fun n => -(unitIntervalCosineEigenvalue n) *
      Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n x) := by
  have hMu0 : 0 ≤ Mu0 := le_trans (abs_nonneg _) (hu0bd 0)
  refine Summable.of_norm
    (((unitIntervalCosineEigenvalue_mul_exp_summable ht).mul_left Mu0).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun n => ?_))
  have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue
    positivity
  rw [Real.norm_eq_abs,
    show -(unitIntervalCosineEigenvalue n) *
        Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n x =
        -(unitIntervalCosineEigenvalue n * Real.exp (-t * unitIntervalCosineEigenvalue n) *
          u₀cos n * cosineMode n x) from by ring,
    abs_neg, abs_mul, abs_mul, abs_mul, abs_of_nonneg hlam,
    abs_of_nonneg (Real.exp_nonneg _)]
  calc
    unitIntervalCosineEigenvalue n * Real.exp (-t * unitIntervalCosineEigenvalue n) *
          |u₀cos n| * |cosineMode n x|
        ≤ unitIntervalCosineEigenvalue n *
            Real.exp (-t * unitIntervalCosineEigenvalue n) * Mu0 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hu0bd n) (by positivity))
            (cosineMode_abs_le_one_L1 n x) (abs_nonneg _) (by positivity)
    _ = Mu0 * (unitIntervalCosineEigenvalue n *
          Real.exp (-t * unitIntervalCosineEigenvalue n)) := by ring

private theorem duhamelVal_summable_of_L1ContOn
    {a : ℝ → ℕ → ℝ} {T : ℝ} (src : DuhamelSourceL1ContOn a T)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (x : ℝ) :
    Summable (fun n => duhamelSpectralCoeff a t n * cosineMode n x) := by
  refine Summable.of_norm ((src.henv_summable.mul_left t).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun n => ?_))
  have henv_nn : 0 ≤ src.envelope n :=
    le_trans (abs_nonneg _) (src.henv_bound t ht.le htT n)
  rw [Real.norm_eq_abs, abs_mul]
  calc
    |duhamelSpectralCoeff a t n| * |cosineMode n x|
        ≤ (t * src.envelope n) * 1 :=
          mul_le_mul (abs_duhamelSpectralCoeff_le_weak src ht htT n)
            (cosineMode_abs_le_one_L1 n x) (abs_nonneg _)
            (mul_nonneg ht.le henv_nn)
    _ = t * src.envelope n := mul_one _

private theorem duhamelDerivVal_summable_of_L1ContOn
    {a : ℝ → ℕ → ℝ} {T : ℝ} (src : DuhamelSourceL1ContOn a T)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (x : ℝ) :
    Summable (fun n => (a t n - unitIntervalCosineEigenvalue n *
      duhamelSpectralCoeff a t n) * cosineMode n x) := by
  refine Summable.of_norm ((src.henv_summable.mul_left 2).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun n => ?_))
  have henv_nn : 0 ≤ src.envelope n :=
    le_trans (abs_nonneg _) (src.henv_bound t ht.le htT n)
  rw [Real.norm_eq_abs, abs_mul]
  calc
    |a t n - unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a t n| *
          |cosineMode n x|
        ≤ (2 * src.envelope n) * 1 :=
          mul_le_mul (duhamelDeriv_abs_le_two_env src ht htT n)
            (cosineMode_abs_le_one_L1 n x) (abs_nonneg _)
            (mul_nonneg (by norm_num) henv_nn)
    _ = 2 * src.envelope n := mul_one _

theorem fullSourceCoeff_tsum_split_L1 (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs p u) T)
    (hlog : DuhamelSourceL1ContOn (coupledLogisticSourceCoeffs p u) T)
    {q : ℝ × ℝ} (hq : q ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)) :
    (∑' n, fullSourceCoeff p u u₀cos q.1 n * cosineMode n q.2) =
      (∑' n, Real.exp (-q.1 * unitIntervalCosineEigenvalue n) *
          u₀cos n * cosineMode n q.2)
      + (-p.χ₀) * (∑' n, duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u)
          q.1 n * cosineMode n q.2)
      + (∑' n, duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u)
          q.1 n * cosineMode n q.2) := by
  obtain ⟨hq1, _⟩ := mem_prod.1 hq
  have hqp : 0 < q.1 := (mem_Ioo.1 hq1).1
  have hqT : q.1 < T := (mem_Ioo.1 hq1).2
  have hheat := heatVal_summable_L1 u₀cos hu0bd hqp q.2
  have hchemS :=
    (duhamelVal_summable_of_L1ContOn hchem hqp hqT.le q.2).mul_left (-p.χ₀)
  have hlogS := duhamelVal_summable_of_L1ContOn hlog hqp hqT.le q.2
  rw [← tsum_mul_left (a := -p.χ₀), ← hheat.tsum_add hchemS,
    ← (hheat.add hchemS).tsum_add hlogS]
  refine (tsum_congr (fun n => ?_)).symm
  simp only [fullSourceCoeff]
  ring

theorem fullSourceCoeffDot_tsum_split_L1 (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs p u) T)
    (hlog : DuhamelSourceL1ContOn (coupledLogisticSourceCoeffs p u) T)
    {q : ℝ × ℝ} (hq : q ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)) :
    (∑' n, fullSourceCoeffDot p u u₀cos q.1 n * cosineMode n q.2) =
      (∑' n, -(unitIntervalCosineEigenvalue n) *
          Real.exp (-q.1 * unitIntervalCosineEigenvalue n) *
          u₀cos n * cosineMode n q.2)
      + (-p.χ₀) * (∑' n, (coupledChemDivSourceCoeffs p u q.1 n
          - unitIntervalCosineEigenvalue n
            * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) q.1 n)
          * cosineMode n q.2)
      + (∑' n, (coupledLogisticSourceCoeffs p u q.1 n
          - unitIntervalCosineEigenvalue n
            * duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) q.1 n)
          * cosineMode n q.2) := by
  obtain ⟨hq1, _⟩ := mem_prod.1 hq
  have hqp : 0 < q.1 := (mem_Ioo.1 hq1).1
  have hqT : q.1 < T := (mem_Ioo.1 hq1).2
  have hheat := heatDerivVal_summable_L1 u₀cos hu0bd hqp q.2
  have hchemS :=
    (duhamelDerivVal_summable_of_L1ContOn hchem hqp hqT.le q.2).mul_left (-p.χ₀)
  have hlogS := duhamelDerivVal_summable_of_L1ContOn hlog hqp hqT.le q.2
  rw [← tsum_mul_left (a := -p.χ₀), ← hheat.tsum_add hchemS,
    ← (hheat.add hchemS).tsum_add hlogS]
  refine (tsum_congr (fun n => ?_)).symm
  simp only [fullSourceCoeffDot]
  ring

theorem fullSourceCoeff_jointContinuousOn_of_L1ContOn (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs p u) T)
    (hlog : DuhamelSourceL1ContOn (coupledLogisticSourceCoeffs p u) T) :
    ContinuousOn
      (fun q : ℝ × ℝ => ∑' n, fullSourceCoeff p u u₀cos q.1 n * cosineMode n q.2)
      (Ioo (0 : ℝ) T ×ˢ univ) := by
  have hsub : Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ) ⊆ Ioi (0 : ℝ) ×ˢ univ :=
    prod_mono (fun _ ht => mem_Ioi.2 (mem_Ioo.1 ht).1) (subset_refl _)
  have hheat := (heatValueSeries_jointContinuousOn_L1 u₀cos hu0bd).mono hsub
  have hchemJ := duhamelSeries_jointContinuousOn_of_L1ContOn hchem
  have hlogJ := duhamelSeries_jointContinuousOn_of_L1ContOn hlog
  have hsum := ((hheat.add (hchemJ.const_smul (-p.χ₀))).add hlogJ)
  refine hsum.congr (fun q hq => ?_)
  have := fullSourceCoeff_tsum_split_L1 p u u₀cos hu0bd hchem hlog hq
  simp only [Pi.add_apply, Function.uncurry, smul_eq_mul] at this ⊢
  rw [this]

theorem fullSourceCoeffDot_jointContinuousOn_of_L1ContOn (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs p u) T)
    (hlog : DuhamelSourceL1ContOn (coupledLogisticSourceCoeffs p u) T) :
    ContinuousOn
      (fun q : ℝ × ℝ => ∑' n, fullSourceCoeffDot p u u₀cos q.1 n * cosineMode n q.2)
      (Ioo (0 : ℝ) T ×ˢ univ) := by
  have hsub : Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ) ⊆ Ioi (0 : ℝ) ×ˢ univ :=
    prod_mono (fun _ ht => mem_Ioi.2 (mem_Ioo.1 ht).1) (subset_refl _)
  have hheat := (heatDerivSeries_jointContinuousOn_L1 u₀cos hu0bd).mono hsub
  have hchemJ := duhamelDerivSeries_jointContinuousOn_of_L1ContOn hchem
  have hlogJ := duhamelDerivSeries_jointContinuousOn_of_L1ContOn hlog
  have hsum := ((hheat.add (hchemJ.const_smul (-p.χ₀))).add hlogJ)
  refine hsum.congr (fun q hq => ?_)
  have := fullSourceCoeffDot_tsum_split_L1 p u u₀cos hu0bd hchem hlog hq
  simp only [Pi.add_apply, Function.uncurry, smul_eq_mul] at this ⊢
  rw [this]

/-! ## 1k. Closed and interior corollaries -/

theorem fullSourceCoeffDot_jointTimeDerivClosed_of_L1ContOn
    {T : ℝ} (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs p u) T)
    (hlog : DuhamelSourceL1ContOn (coupledLogisticSourceCoeffs p u) T) :
    ContinuousOn
      (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
        ∑' n, fullSourceCoeffDot p u u₀cos t n * cosineMode n x))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
  (fullSourceCoeffDot_jointContinuousOn_of_L1ContOn p u u₀cos hu0bd hchem hlog).mono
    (prod_mono (subset_refl _) (subset_univ _))

theorem fullSourceCoeffDot_jointTimeDerivInterior_of_L1ContOn
    {T : ℝ} (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs p u) T)
    (hlog : DuhamelSourceL1ContOn (coupledLogisticSourceCoeffs p u) T) :
    ContinuousOn
      (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
        ∑' n, fullSourceCoeffDot p u u₀cos t n * cosineMode n x))
      (Ioo (0 : ℝ) T ×ˢ Ioo (0 : ℝ) 1) :=
  (fullSourceCoeffDot_jointContinuousOn_of_L1ContOn p u u₀cos hu0bd hchem hlog).mono
    (prod_mono (subset_refl _) (subset_univ _))

theorem fullSourceCoeff_jointSolutionClosed_of_L1ContOn
    {T : ℝ} (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs p u) T)
    (hlog : DuhamelSourceL1ContOn (coupledLogisticSourceCoeffs p u) T) :
    ContinuousOn
      (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
        ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
  (fullSourceCoeff_jointContinuousOn_of_L1ContOn p u u₀cos hu0bd hchem hlog).mono
    (prod_mono (subset_refl _) (subset_univ _))

#print axioms duhamelSpectralCoeff_hasDerivAt_of_L1ContOn
#print axioms synthesis_hasDerivAt_of_L1ContOn
#print axioms duhamelDerivSeries_jointContinuousOn_of_L1ContOn
#print axioms fullSourceCoeffDot_jointContinuousOn_of_L1ContOn
#print axioms fullSourceCoeffDot_jointTimeDerivClosed_of_L1ContOn
#print axioms fullSourceCoeffDot_jointTimeDerivInterior_of_L1ContOn
#print axioms fullSourceCoeff_jointSolutionClosed_of_L1ContOn

end ShenWork.EWA
