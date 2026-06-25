/-
  ShenWork/Wiener/EWA/SourceReducedCoreWire.lean

  **χ₀<0 capstone — the MAXIMALLY-WIRED reduced coupled-Duhamel classical core.**

  REFACTORED: `hchem`/`hlog` binders changed from global `DuhamelSourceTimeC1`
  (unsatisfiable) to windowed `DuhamelSourceTimeC1On ... 0 T` (satisfiable).
  Classical regularity is now a pre-computed hypothesis `hclassReg`.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceReducedCore
import ShenWork.Wiener.EWA.SourceChiNegUncondWire
import ShenWork.Wiener.EWA.SourcePdeUFamilyDischarge
import ShenWork.Wiener.EWA.SourceHchemInvDirect
import ShenWork.Wiener.EWA.SourceSliceC2Neumann
import ShenWork.Wiener.EWA.SourceTimeDerivDischarge
import ShenWork.Wiener.EWA.SourceEndpointNonvanish
import ShenWork.Wiener.EWA.SourceResolverSpectralDischarge
import ShenWork.PDE.IntervalDuhamelSpectralDerivOn

noncomputable section

namespace ShenWork.EWA

open scoped BigOperators
open Set Metric Filter Topology
open ShenWork.GWA ShenWork.Wiener ShenWork.CosineSpectrum
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)
open ShenWork.PDE
  (intervalNeumannResolverCoeff intervalNeumannResolverSourceCoeff)
open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalDomainChemotaxisDiv
    intervalDomain intervalDomainClassicalRegularity)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalResolverDirectTimeRegularity (HasResolverDirectSpectralData)
open ShenWork.Paper2 (SourceCoeffQuadraticDecay)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs
    coupledChemicalConcentration CoupledDuhamelReducedClassicalCore)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1 duhamelSpectralCoeff)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.IntervalDuhamelSpectralDerivOn
  (duhamelSpectralCoeff_hasDerivAt_of_on)
open ShenWork.IntervalMildRegularityBootstrap
  (unitIntervalCosineEigenvalue_mul_exp_summable)
open ShenWork.IntervalDomainRegularityBootstrap
  (reciprocalSquareTerm reciprocalSquareTerm_summable)
open ShenWork.HeatKernelGradientEstimates
  (unitIntervalCosineHeatTrace_single_exp_summable)

variable {T : ℝ}

/-! ### The slab `realizes` with the three hard-core `evalST` atoms discharged. -/

theorem realSlice_realizes_slab_evalST_discharged
    (p : CM2Params) (u₀cos : ℕ → ℝ)
    (hsumc : Summable (fun k => |u₀cos k|)) (hmem : MemW 1 (ofCosineCoeffs u₀cos))
    (hT : (0 : ℝ) ≤ T)
    {ρ L_Q L_G δ : ℝ} (hδpos : 0 < δ) (u_star : EWA T 1)
    (hfix : u_star = picardEWA p p.μ p.ν p.γ p.hμ hT
      (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1) u_star)
    (hρ : 0 ≤ ρ)
    (hself : MapsTo
      (picardEWA p p.μ p.ν p.γ p.hμ hT (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1))
      (Metric.closedBall (heatEWA (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ)
      (Metric.closedBall (heatEWA (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ))
    (hLipQ : ∀ a ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ,
      ∀ b ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ,
      ‖chemFluxEWA p.μ p.ν p.β p.γ p.hμ a - chemFluxEWA p.μ p.ν p.β p.γ p.hμ b‖
        ≤ L_Q * ‖a - b‖)
    (hLipG : ∀ a ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ,
      ∀ b ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ,
      ‖growthEWA p.α p.a p.b a - growthEWA p.α p.a p.b b‖ ≤ L_G * ‖a - b‖)
    (hKnn : (0 : ℝ) ≤ |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T)
    (hK : |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T < 1)
    (hmem_star : u_star ∈ Metric.closedBall (heatEWA (T := T)
      (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ)
    (hβpos : 0 < p.β) (hαnn : 0 ≤ p.α) (hμle1 : p.μ ≤ 1)
    (hfloorδ : δ = T) (hfloor : UniformFloor u_star δ)
    (hsumR : ∀ σ : TimeDom T, ResolverSourceSummable p (realSlice u_star σ.1))
    (hgrad : ∀ (τ : TimeDom T),
      Summable fun k : ℕ =>
        |(intervalNeumannResolverCoeff p (realSlice u_star τ.1) k).re| *
          ((k : ℝ) * Real.pi))
    (f : ℝ → ℝ → ℝ) (hf_cont : ∀ σ : TimeDom T, Continuous (f σ.1))
    (hf_nonneg : ∀ (σ : TimeDom T) (y : ℝ), 0 ≤ f σ.1 y)
    (hf_coeff : ∀ (σ : TimeDom T) (k : ℕ),
      cosineCoeffs (f σ.1) k =
        (intervalNeumannResolverSourceCoeff p (realSlice u_star σ.1) k).re)
    (hf2 : ∀ σ : TimeDom T, Summable (fun k => (cosineCoeffs (f σ.1) k) ^ 2))
    (h_flux_diff : ∀ (τ : TimeDom T), ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (chemFluxLifted p (realSlice u_star τ.1)) x)
    (h_src_cont_log : ∀ (τ : TimeDom T), Continuous (wLog p u_star τ.1)) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x =
        ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x := by
  intro t ht
  exact realizes_evalST_discharged p u₀cos hsumc hmem hT hδpos u_star hfix hρ hself
    hLipQ hLipG hKnn hK hmem_star hβpos hαnn hμle1 hfloorδ hfloor hsumR hgrad
    f hf_cont hf_nonneg hf_coeff hf2 h_flux_diff h_src_cont_log t ht.1 ht.2.le

/-! ### Private windowed wrappers. -/

private theorem cosineMode_abs_le (n : ℕ) (x : ℝ) : |cosineMode n x| ≤ 1 := by
  simp only [cosineMode]; exact Real.abs_cos_le_one _

private theorem hsum_chem_of_on (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ)
    (src : DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p u) 0 T) :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint, x.1 ∈ Ioo (0 : ℝ) 1 →
      Summable (fun n => coupledChemDivSourceCoeffs p u t n * cosineMode n x.1) := by
  intro t ht x _
  exact Summable.of_norm (src.henv_summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    fun n => by
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (cosineMode_abs_le n x.1)).trans
        (src.henv_bound t ⟨ht.1.le, ht.2.le⟩ n))

private theorem hsum_log_of_on (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ)
    (src : DuhamelSourceTimeC1On (coupledLogisticSourceCoeffs p u) 0 T) :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint, x.1 ∈ Ioo (0 : ℝ) 1 →
      Summable (fun n => coupledLogisticSourceCoeffs p u t n * cosineMode n x.1) := by
  intro t ht x _
  exact Summable.of_norm (src.henv_summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    fun n => by
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (cosineMode_abs_le n x.1)).trans
        (src.henv_bound t ⟨ht.1.le, ht.2.le⟩ n))

private theorem fullSourceCoeff_hasDerivAt_on (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ)
    (hchem : DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p u) 0 T)
    (hlog : DuhamelSourceTimeC1On (coupledLogisticSourceCoeffs p u) 0 T)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (n : ℕ) :
    HasDerivAt (fun r => fullSourceCoeff p u u₀cos r n)
      (fullSourceCoeffDot p u u₀cos t n) t := by
  have hexp : HasDerivAt (fun r : ℝ => Real.exp (-r * unitIntervalCosineEigenvalue n))
      (-unitIntervalCosineEigenvalue n *
        Real.exp (-t * unitIntervalCosineEigenvalue n)) t := by
    have h1 : HasDerivAt (fun r : ℝ => -r * unitIntervalCosineEigenvalue n)
        (-1 * unitIntervalCosineEigenvalue n) t :=
      (hasDerivAt_id t).neg.mul_const (unitIntervalCosineEigenvalue n)
    have h2 := h1.exp
    simp only [neg_mul, one_mul] at h2 ⊢
    convert h2 using 1; ring
  exact ((hexp.mul_const _).add
    ((duhamelSpectralCoeff_hasDerivAt_of_on hchem ht0 htT n).const_mul _)).add
    (duhamelSpectralCoeff_hasDerivAt_of_on hlog ht0 htT n)

private theorem abs_duhamel_le_on {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC1On a 0 T)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (n : ℕ) :
    |duhamelSpectralCoeff a t n| ≤ t * src.envelope n := by
  show |∫ s in (0:ℝ)..t,
      Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * a s n| ≤ _
  have henv_nn : 0 ≤ src.envelope n :=
    le_trans (abs_nonneg _) (src.henv_bound 0 ⟨le_refl _, by linarith⟩ n)
  have hlam_nn : (0 : ℝ) ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue; positivity
  -- bound: |∫| ≤ ∫ |integrand| ≤ ∫ envelope = t * envelope
  have h_norm := intervalIntegral.norm_integral_le_integral_norm (μ := MeasureTheory.MeasureSpace.volume) ht.le
    (f := fun s => Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * a s n)
  rw [Real.norm_eq_abs] at h_norm
  calc |∫ s in (0:ℝ)..t,
        Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * a s n|
      ≤ ∫ s in (0:ℝ)..t,
          ‖Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * a s n‖ := h_norm
    _ ≤ ∫ s in (0:ℝ)..t, src.envelope n := by
        apply intervalIntegral.integral_mono_on ht.le
        · have hcontOn : ContinuousOn (fun s => a s n) (Icc 0 T) :=
            fun s hs => (src.hderiv s hs n).continuousWithinAt
          exact ((((Real.continuous_exp.comp (by fun_prop : Continuous (fun s =>
              -(t - s) * unitIntervalCosineEigenvalue n))).continuousOn).mul
            (hcontOn.mono (Icc_subset_Icc le_rfl htT))).norm).intervalIntegrable_of_Icc ht.le
        · exact intervalIntegrable_const
        · intro s hs
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
          calc Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * |a s n|
              ≤ 1 * src.envelope n := by
                gcongr
                · exact Real.exp_le_one_iff.2 (by nlinarith [hs.2])
                · exact src.henv_bound s ⟨hs.1, le_trans hs.2 htT⟩ n
            _ = src.envelope n := one_mul _
    _ = t * src.envelope n := by
        rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]

private theorem fsc_summable_on (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p u) 0 T)
    (hlog : DuhamelSourceTimeC1On (coupledLogisticSourceCoeffs p u) 0 T)
    {t₀ : ℝ} (ht0 : 0 < t₀) (ht0T : t₀ ≤ T) (x : ℝ) :
    Summable (fun n => fullSourceCoeff p u u₀cos t₀ n * cosineMode n x) := by
  have hM : 0 ≤ Mu0 := le_trans (abs_nonneg _) (hu0bd 0)
  refine Summable.of_norm ((((
    (unitIntervalCosineHeatTrace_single_exp_summable ht0).mul_left Mu0).add
    ((hchem.henv_summable.mul_left t₀).mul_left |(-p.χ₀)|)).add
    (hlog.henv_summable.mul_left t₀)).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  calc |fullSourceCoeff p u u₀cos t₀ n| * |cosineMode n x|
      ≤ |fullSourceCoeff p u u₀cos t₀ n| :=
        mul_le_of_le_one_right (abs_nonneg _) (cosineMode_abs_le n x)
    _ ≤ _ := by
        simp only [fullSourceCoeff]
        calc _ ≤ |Real.exp (-t₀ * unitIntervalCosineEigenvalue n) * u₀cos n|
              + |(-p.χ₀) * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t₀ n|
              + |duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) t₀ n| :=
            abs_add_three _ _ _
          _ ≤ _ := by
              gcongr
              · rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _), mul_comm]
                exact mul_le_mul_of_nonneg_right (hu0bd n) (Real.exp_nonneg _)
              · rw [abs_mul]; exact mul_le_mul_of_nonneg_left
                  (abs_duhamel_le_on hchem ht0 ht0T n) (abs_nonneg _)
              · exact abs_duhamel_le_on hlog ht0 ht0T n

/-- Windowed version of `duhamelSpectralCoeff_deriv_summable_uniform_bound`.
For `DuhamelSourceTimeC1On a 0 T` and `0 < t ≤ T`:
`|a(t,n) − λₙ·bₙ(t)| ≤ envelope(n) + derivBound·reciprocalSquareTerm(n)`. -/
private theorem duhamel_deriv_bound_on {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC1On a 0 T)
    {t : ℝ} (ht0 : 0 < t) (htT : t ≤ T) (n : ℕ) :
    |a t n - unitIntervalCosineEigenvalue n *
      duhamelSpectralCoeff a t n| ≤
      src.envelope n + src.derivBound * reciprocalSquareTerm n := by
  have hdb_nn : 0 ≤ src.derivBound :=
    le_trans (abs_nonneg _) (src.hderivBound 0 ⟨le_refl _, by linarith⟩ 0)
  have hlam_nn : (0 : ℝ) ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue; positivity
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · -- n = 0: λ₀ = 0
    subst hn0
    have h1 : unitIntervalCosineEigenvalue 0 = 0 := by
      simp [unitIntervalCosineEigenvalue]
    have h2 : reciprocalSquareTerm 0 = 0 := by
      simp [reciprocalSquareTerm]
    simp only [h1, zero_mul, sub_zero, h2, mul_zero, add_zero]
    exact src.henv_bound t ⟨ht0.le, htT⟩ 0
  · -- n ≥ 1: use the windowed eigenvalue IBP.
    have hlam_pos : 0 < unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      have : (0 : ℝ) < n := Nat.cast_pos.2 hn
      positivity
    -- From the windowed IBP:
    -- λₙ · |bₙ(t)| = |a(t,n) − e^{−tλₙ}·a(0,n) − ∫₀ᵗ e^{−(t−s)λₙ}·ȧ(s,n) ds|
    have hIBP := ShenWork.IntervalDuhamelSpectralDerivOn.duhamelCoeff_eigenvalue_mul_of_on
      src ht0 htT n
    -- So a(t,n) − λₙ·bₙ(t) = a(t,n) − (a(t,n) − e^{−tλₙ}·a(0,n) − ∫ ...) ± ...
    -- Actually, from the ODE form: a(t,n) − λₙ·bₙ(t) is the spectral Duhamel ODE RHS.
    -- Bound |a(t,n)| ≤ envelope(n) and |λₙ·bₙ(t)| needs care.
    -- Use triangle: |a − λ·b| ≤ |a| + λ·|b|. But this is too loose.
    -- Better: use the IBP directly to express λₙ·bₙ and bound the residual.
    -- From the IBP identity:
    -- λₙ · ∫₀ᵗ e^{-(t-s)λₙ} · a(s,n) ds = a(t,n) − e^{-tλₙ}·a(0,n) − ∫₀ᵗ e^{-(t-s)λₙ}·ȧ(s,n)ds
    -- So: a(t,n) − λₙ · bₙ(t) = e^{-tλₙ}·a(0,n) + ∫₀ᵗ e^{-(t-s)λₙ}·ȧ(s,n)ds
    -- Therefore: |a(t,n) − λₙ·bₙ(t)| ≤ |a(0,n)| + ∫₀ᵗ e^{-(t-s)λₙ} · |ȧ(s,n)| ds
    -- ≤ envelope(n) + derivBound · ∫₀ᵗ e^{-(t-s)λₙ} ds
    -- ≤ envelope(n) + derivBound / λₙ ≤ envelope(n) + derivBound · reciprocalSquareTerm(n)
    -- Derive: a(t,n) − λₙ·bₙ(t) = e^{−tλₙ}·a(0,n) + ∫₀ᵗ e^{−(t−s)λₙ}·ȧ(s,n) ds
    have hkey := ShenWork.IntervalDuhamelSourceTimeC1On.duhamelCoeff_eigenvalue_mul_on
      (lo := 0) (hi := T) (t := t) (lam := unitIntervalCosineEigenvalue n)
      (a := fun s => a s n) (adot := fun s => src.adot s n)
      (by linarith) ht0.le htT
      (fun s hs => src.hderiv s ⟨hs.1, le_trans hs.2 htT⟩ n) (src.hadotcont n)
    -- hkey : λₙ · ∫₀ᵗ ... = a(t,n) − e^{−(t−0)λₙ}·a(0,n) − ∫₀ᵗ e^{−(t−s)λₙ}·ȧ(s,n)ds
    simp only [sub_zero] at hkey
    -- So a(t,n) − λₙ·bₙ(t) = e^{−tλₙ}·a(0,n) + ∫₀ᵗ e^{−(t−s)λₙ}·ȧ(s,n)ds
    have hres : a t n - unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a t n
        = Real.exp (-t * unitIntervalCosineEigenvalue n) * a 0 n
          + ∫ s in (0:ℝ)..t,
            Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n := by
      show a t n - unitIntervalCosineEigenvalue n *
        (∫ s in (0:ℝ)..t, Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * a s n) = _
      linarith
    rw [hres]
    -- Bound the two pieces:
    have h_exp_piece : |Real.exp (-t * unitIntervalCosineEigenvalue n) * a 0 n| ≤
        src.envelope n := by
      rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      calc Real.exp (-t * unitIntervalCosineEigenvalue n) * |a 0 n|
          ≤ 1 * |a 0 n| := by
            gcongr
            exact Real.exp_le_one_iff.2 (by nlinarith)
        _ = |a 0 n| := one_mul _
        _ ≤ src.envelope n := src.henv_bound 0 ⟨le_refl _, by linarith⟩ n
    have hadotcontOn : ContinuousOn (fun s => src.adot s n) (Icc 0 T) := src.hadotcont n
    have h_int_piece : |∫ s in (0:ℝ)..t,
          Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n| ≤
        src.derivBound * reciprocalSquareTerm n := by
      have h_norm := intervalIntegral.norm_integral_le_integral_norm
        (μ := MeasureTheory.MeasureSpace.volume) ht0.le
        (f := fun s => Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n)
      rw [Real.norm_eq_abs] at h_norm
      have hii1 : IntervalIntegrable
          (fun s => ‖Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n‖)
          MeasureTheory.MeasureSpace.volume 0 t :=
        ((((Real.continuous_exp.comp (by fun_prop : Continuous (fun s =>
            -(t - s) * unitIntervalCosineEigenvalue n))).continuousOn).mul
          (hadotcontOn.mono (Icc_subset_Icc le_rfl htT))).norm).intervalIntegrable_of_Icc ht0.le
      calc |∫ s in (0:ℝ)..t,
              Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n|
          ≤ ∫ s in (0:ℝ)..t,
              ‖Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n‖ := h_norm
        _ ≤ ∫ s in (0:ℝ)..t,
              src.derivBound * Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) := by
            apply intervalIntegral.integral_mono_on ht0.le hii1
              (Continuous.intervalIntegrable (by fun_prop) _ _)
            intro s hs
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _), mul_comm]
            exact mul_le_mul_of_nonneg_right
              (src.hderivBound s ⟨hs.1, le_trans hs.2 htT⟩ n) (Real.exp_nonneg _)
        _ = src.derivBound * ∫ s in (0:ℝ)..t,
              Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) := by
            rw [intervalIntegral.integral_const_mul]
        _ ≤ src.derivBound * (1 / unitIntervalCosineEigenvalue n) := by
            gcongr
            rw [le_div_iff₀ hlam_pos]
            linarith [ShenWork.IntervalDuhamelRegularity.parabolicGain_le_one hlam_nn ht0.le]
        _ ≤ src.derivBound * reciprocalSquareTerm n := by
            gcongr
            rw [reciprocalSquareTerm, unitIntervalCosineEigenvalue]
            apply div_le_div_of_nonneg_left (by linarith) (by positivity)
            calc ((n : ℝ) * Real.pi) ^ 2
                = (n : ℝ) ^ 2 * Real.pi ^ 2 := by ring
              _ ≥ (n : ℝ) ^ 2 * 1 := by
                  apply mul_le_mul_of_nonneg_left _ (by positivity)
                  nlinarith [Real.pi_gt_three]
              _ = (n : ℝ) ^ 2 := mul_one _
    linarith [abs_add_le
      (Real.exp (-t * unitIntervalCosineEigenvalue n) * a 0 n)
      (∫ s in (0:ℝ)..t,
        Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n)]

private noncomputable def dotMaj (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (Mu0 c : ℝ)
    (hchem : DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p u) 0 T)
    (hlog : DuhamelSourceTimeC1On (coupledLogisticSourceCoeffs p u) 0 T)
    (n : ℕ) : ℝ :=
  Mu0 * (unitIntervalCosineEigenvalue n *
      Real.exp (-c * unitIntervalCosineEigenvalue n))
    + |(-p.χ₀)| * (hchem.envelope n + hchem.derivBound * reciprocalSquareTerm n)
    + (hlog.envelope n + hlog.derivBound * reciprocalSquareTerm n)

private theorem dotMaj_summable (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (Mu0 : ℝ) {c : ℝ} (hc : 0 < c)
    (hchem : DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p u) 0 T)
    (hlog : DuhamelSourceTimeC1On (coupledLogisticSourceCoeffs p u) 0 T) :
    Summable (dotMaj p u Mu0 c hchem hlog) :=
  ((((unitIntervalCosineEigenvalue_mul_exp_summable hc).mul_left Mu0).add
    ((hchem.henv_summable.add
      (reciprocalSquareTerm_summable.mul_left hchem.derivBound)).mul_left |(-p.χ₀)|)).add
    (hlog.henv_summable.add (reciprocalSquareTerm_summable.mul_left hlog.derivBound)))

private theorem dotMaj_bound (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p u) 0 T)
    (hlog : DuhamelSourceTimeC1On (coupledLogisticSourceCoeffs p u) 0 T)
    {c : ℝ} (hc : 0 < c) (_hcT : c < T) (x : ℝ) (n : ℕ)
    (s : ℝ) (hs : s ∈ Ioo c T) :
    ‖fullSourceCoeffDot p u u₀cos s n * cosineMode n x‖ ≤
      dotMaj p u Mu0 c hchem hlog n := by
  have hcs : c ≤ s := hs.1.le
  have hs0 : 0 ≤ s := le_trans hc.le hcs
  have hsT : s ≤ T := hs.2.le
  have hlam : (0 : ℝ) ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue; positivity
  rw [Real.norm_eq_abs, abs_mul]
  calc |fullSourceCoeffDot p u u₀cos s n| * |cosineMode n x|
      ≤ |fullSourceCoeffDot p u u₀cos s n| :=
        mul_le_of_le_one_right (abs_nonneg _) (cosineMode_abs_le n x)
    _ ≤ dotMaj p u Mu0 c hchem hlog n := by
        simp only [fullSourceCoeffDot, dotMaj]
        calc _ ≤ |-(unitIntervalCosineEigenvalue n) *
                  Real.exp (-s * unitIntervalCosineEigenvalue n) * u₀cos n|
              + |(-p.χ₀) * (coupledChemDivSourceCoeffs p u s n
                  - unitIntervalCosineEigenvalue n *
                    duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) s n)|
              + |(coupledLogisticSourceCoeffs p u s n
                  - unitIntervalCosineEigenvalue n *
                    duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) s n)| :=
            abs_add_three _ _ _
          _ ≤ _ := by
              gcongr
              · rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hlam,
                  abs_of_nonneg (Real.exp_nonneg _), mul_comm Mu0]
                exact mul_le_mul (mul_le_mul_of_nonneg_left
                  (Real.exp_le_exp_of_le (by nlinarith)) hlam) (hu0bd n)
                  (abs_nonneg _) (by positivity)
              · rw [abs_mul]
                exact mul_le_mul_of_nonneg_left
                  (duhamel_deriv_bound_on hchem (lt_of_lt_of_le hc hcs) hsT n)
                  (abs_nonneg _)
              · exact duhamel_deriv_bound_on hlog (lt_of_lt_of_le hc hcs) hsT n

private theorem synthesis_hasDerivAt_on (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p u) 0 T)
    (hlog : DuhamelSourceTimeC1On (coupledLogisticSourceCoeffs p u) 0 T)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) T) (x : ℝ) :
    HasDerivAt (fun s => ∑' n, fullSourceCoeff p u u₀cos s n * cosineMode n x)
      (∑' n, fullSourceCoeffDot p u u₀cos t₀ n * cosineMode n x) t₀ := by
  set c := t₀ / 2 with hc_def
  have ht0_pos : 0 < t₀ := ht₀.1
  have ht0_lt_T : t₀ < T := ht₀.2
  have hc : 0 < c := by rw [hc_def]; linarith
  have hcT : c < T := by rw [hc_def]; linarith
  have hc_lt_t0 : c < t₀ := by rw [hc_def]; linarith
  exact hasDerivAt_tsum_of_isPreconnected
    (dotMaj_summable p u Mu0 hc hchem hlog) isOpen_Ioo isPreconnected_Ioo
    (fun n s hs => (fullSourceCoeff_hasDerivAt_on p u u₀cos hchem hlog
      (lt_trans hc hs.1) hs.2 n).mul_const _)
    (fun n s hs => dotMaj_bound p u u₀cos hu0bd hchem hlog hc hcT x n s hs)
    ⟨hc_lt_t0, ht0_lt_T⟩
    (fsc_summable_on p u u₀cos hu0bd hchem hlog ht0_pos ht0_lt_T.le x)
    ⟨hc_lt_t0, ht0_lt_T⟩

private theorem slice_hasDerivAt_on (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p u) 0 T)
    (hlog : DuhamelSourceTimeC1On (coupledLogisticSourceCoeffs p u) 0 T)
    (hrealizes : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u t) x =
        ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (x : intervalDomainPoint) :
    HasDerivAt (fun s => u s x)
      (∑' n, fullSourceCoeffDot p u u₀cos t n * cosineMode n x.1) t :=
  (synthesis_hasDerivAt_on p u u₀cos hu0bd hchem hlog ht x.1).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht) fun s hs => by
      have : intervalDomainLift (u s) x.1 = u s x := by simp [intervalDomainLift]
      rw [← this, hrealizes s hs x.1 x.2])

private theorem htime_of_on (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p u) 0 T)
    (hlog : DuhamelSourceTimeC1On (coupledLogisticSourceCoeffs p u) 0 T)
    (hrealizes : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u t) x =
        ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x) :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint, x.1 ∈ Ioo (0 : ℝ) 1 →
      intervalDomain.timeDeriv u t x =
        ∑' n, fullSourceCoeffDot p u u₀cos t n * cosineMode n x.1 :=
  fun t ht x _ =>
    (slice_hasDerivAt_on p u u₀cos hu0bd hchem hlog hrealizes ht x).deriv

/-! ### The maximally-wired reduced core. -/

theorem realSlice_reducedCore_wired (p : CM2Params) (u_star : EWA T 1)
    (u₀ : intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ)
    {Mu0 : ℝ} (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    {u₀E : WA 1} {δ ρ : ℝ} (hδρ : 0 < δ - ρ)
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ)
    (hu_ball : u_star ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ)
    (hsumc : Summable (fun k => |u₀cos k|)) (hmem : MemW 1 (ofCosineCoeffs u₀cos))
    (hT0 : (0 : ℝ) ≤ T) {L_Q L_G δ' ρ' : ℝ} (hδ'pos : 0 < δ')
    (hρ'ρ : ρ' = ρ)
    (hfix : u_star = picardEWA p p.μ p.ν p.γ p.hμ hT0
      (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1) u_star)
    (hρ' : 0 ≤ ρ')
    (hself : MapsTo
      (picardEWA p p.μ p.ν p.γ p.hμ hT0 (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1))
      (Metric.closedBall (heatEWA (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ')
      (Metric.closedBall (heatEWA (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ'))
    (hLipQ : ∀ a ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ',
      ∀ b ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ',
      ‖chemFluxEWA p.μ p.ν p.β p.γ p.hμ a - chemFluxEWA p.μ p.ν p.β p.γ p.hμ b‖
        ≤ L_Q * ‖a - b‖)
    (hLipG : ∀ a ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ',
      ∀ b ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ',
      ‖growthEWA p.α p.a p.b a - growthEWA p.α p.a p.b b‖ ≤ L_G * ‖a - b‖)
    (hKnn : (0 : ℝ) ≤ |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T)
    (hK : |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T < 1)
    (hmem_star : u_star ∈ Metric.closedBall (heatEWA (T := T)
      (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ')
    (hβpos : 0 < p.β) (hαnn : 0 ≤ p.α) (hμle1 : p.μ ≤ 1)
    (hfloorδ : δ' = T) (hfloor : UniformFloor u_star δ')
    (hsumR : ∀ σ : TimeDom T, ResolverSourceSummable p (realSlice u_star σ.1))
    (hgrad : ∀ (τ : TimeDom T),
      Summable fun k : ℕ =>
        |(intervalNeumannResolverCoeff p (realSlice u_star τ.1) k).re| *
          ((k : ℝ) * Real.pi))
    (f : ℝ → ℝ → ℝ) (hf_cont : ∀ σ : TimeDom T, Continuous (f σ.1))
    (hf_nonneg : ∀ (σ : TimeDom T) (y : ℝ), 0 ≤ f σ.1 y)
    (hf_coeff : ∀ (σ : TimeDom T) (k : ℕ),
      cosineCoeffs (f σ.1) k =
        (intervalNeumannResolverSourceCoeff p (realSlice u_star σ.1) k).re)
    (hf2 : ∀ σ : TimeDom T, Summable (fun k => (cosineCoeffs (f σ.1) k) ^ 2))
    (h_flux_diff : ∀ (τ : TimeDom T), ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (chemFluxLifted p (realSlice u_star τ.1)) x)
    (h_src_cont_log : ∀ (τ : TimeDom T), Continuous (wLog p u_star τ.1))
    -- source TIME-C¹ packages (WINDOWED — satisfiable):
    (hchem_on : DuhamelSourceTimeC1On
      (coupledChemDivSourceCoeffs p (realSlice u_star)) 0 T)
    (hlog_on : DuhamelSourceTimeC1On
      (coupledLogisticSourceCoeffs p (realSlice u_star)) 0 T)
    -- classical regularity (pre-computed):
    (hclassReg : intervalDomainClassicalRegularity T (realSlice u_star)
      (mildChemicalConcentration p (realSlice u_star)))
    -- eigenvalue-l1 summability:
    (hsumE : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Summable (fun n => unitIntervalCosineEigenvalue n *
        |fullSourceCoeff p (realSlice u_star) u₀cos t n|))
    -- chem-source inversion data:
    {μc νc γc : ℝ} (hμc : 0 < μc) (Uc : EWA T 1)
    (hcontChem : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Continuous (fun x : intervalDomainPoint =>
        intervalDomainChemotaxisDiv p (realSlice u_star t)
          (coupledChemicalConcentration p (realSlice u_star) t) x))
    (h_coeffChem : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
        |coupledChemDivSourceCoeffs p (realSlice u_star) s n| ≤
          sourceEnvelope (chemDivEWA μc νc γc hμc p Uc) n)
    (hlogNE0 : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      intervalDomainLift (intervalLogisticSource p (realSlice u_star t)) 0 ≠ 0)
    (hlogNE1 : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      intervalDomainLift (intervalLogisticSource p (realSlice u_star t)) 1 ≠ 0)
    (Hv : HasResolverDirectSpectralData T
      (mildChemicalConcentration p (realSlice u_star)) p)
    (hT : (0 : ℝ) < T)
    (hu0cos : Summable (fun n => |u₀cos n|))
    (hrecon : ∀ x : intervalDomainPoint,
      u₀ x = ∑' n, u₀cos n * cosineMode n x.1)
    (hdefect : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Summable (fun n =>
        |fullSourceCoeff p (realSlice u_star) u₀cos t n - u₀cos n|))
    (htrace : Filter.Tendsto
      (fun t => ∑' n,
        |fullSourceCoeff p (realSlice u_star) u₀cos t n - u₀cos n|)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) :
    CoupledDuhamelReducedClassicalCore p T u₀ (realSlice u_star) := by
  have hrealizes : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x =
        ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x := by
    refine realSlice_realizes_slab_evalST_discharged p u₀cos hsumc hmem hT0 hδ'pos
      u_star ?_ hρ' ?_ ?_ ?_ hKnn hK ?_ hβpos hαnn hμle1 hfloorδ hfloor hsumR hgrad
      f hf_cont hf_nonneg hf_coeff hf2 h_flux_diff h_src_cont_log
    · exact hfix
    · exact hρ'ρ ▸ hself
    · exact hρ'ρ ▸ hLipQ
    · exact hρ'ρ ▸ hLipG
    · exact hρ'ρ ▸ hmem_star
  have huNE0 := realSlice_lift_endpoint0_ne_zero hδρ hheat hu_ball (T := T)
  have huNE1 := realSlice_lift_endpoint1_ne_zero hδρ hheat hu_ball (T := T)
  have htime := htime_of_on p (realSlice u_star) u₀cos hu0bd hchem_on hlog_on hrealizes
  have hlap := realSlice_hlap_of_atoms p (realSlice u_star) u₀cos hsumE hrealizes
  have hsum_lap := realSlice_hsum_lap_of_atoms p (realSlice u_star) u₀cos hsumE
  have hsc := hsum_chem_of_on p (realSlice u_star) hchem_on (T := T)
  have hsl := hsum_log_of_on p (realSlice u_star) hlog_on (T := T)
  have hchemInv := realSlice_hchemInv_direct_realSlice hμc p u_star Uc hcontChem h_coeffChem
  have hlogInv := realSlice_hlogInv_of_bankedU p u_star u₀cos hδρ hheat hu_ball hsumE
    hrealizes hlogNE0 hlogNE1
  exact realSlice_reducedCore p u_star u₀ u₀cos hδρ hheat hu_ball
    htime hlap hchemInv hlogInv hsum_lap hsc hsl
    hclassReg hrealizes
    hT hu0cos hrecon hdefect htrace

end ShenWork.EWA

#print axioms ShenWork.EWA.realSlice_realizes_slab_evalST_discharged
#print axioms ShenWork.EWA.realSlice_reducedCore_wired
