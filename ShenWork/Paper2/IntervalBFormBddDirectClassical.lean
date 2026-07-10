/-
  B-form direct classical assembly with an endpoint-patched bounded source.

  The from-zero source is an explicit family `aB`, so its value at time zero
  may be patched.  Spatial smoothing and time differentiation both use the
  continuity-only `DuhamelSourceBddOn` interface.  Around each positive time,
  a soft clamp turns the source into a globally continuous relative-time family
  without changing it on the active Duhamel interval.
-/
import ShenWork.Paper2.IntervalBFormBddRestart
import ShenWork.Paper2.IntervalBFormPIDUnconditional
import ShenWork.Paper2.IntervalMildRegularityFrontierAssembly
import ShenWork.Paper2.IntervalDomainTheorem11Umbrella
import ShenWork.Paper2.IntervalBFormInitialTrace
import ShenWork.Paper2.IntervalBankChemSliceFix
import ShenWork.Paper2.IntervalBFormRestart
import ShenWork.Paper2.IntervalPicardLimitK1Weak
import ShenWork.Paper2.IntervalBFormPatchedSource
import ShenWork.PDE.IntervalCoupledRegularityBootstrap
import ShenWork.PDE.IntervalCosineSliceRegularity
import ShenWork.PDE.IntervalResolverSpatialC2

open Filter Topology Set

open ShenWork.IntervalDomain
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData ConjugatePicardInfThresholdData
   conjugatePicardLimit paperPositiveFloor)
open ShenWork.IntervalMildTimeDerivContinuity
  (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalResolverDirectTimeRegularity
  (HasResolverDirectSpectralData)
open ShenWork.IntervalMildToClassical
  (mildChemicalConcentration)
open ShenWork.IntervalSourceCoefficientTimeC1
  (localRestartCoeff)
open ShenWork.IntervalPicardLimitRestartBdd
  (DuhamelSourceBddOn)
open ShenWork.Paper2.BFormBddRestart
  (softClampedShiftSource softClampedShiftSource_continuous
   softClampedShiftSource_eq_of_mem localRestartCoeff_abs_summable_bdd
   localRestartCoeff_eigenvalue_summable_bdd)
open ShenWork.Paper2.BFormPatchedSource
  (patchedBFormSourceCoeffs patchedBFormSourceCoeffs_eq_of_pos
   localRestartCoeff_patched_eq_canonical)
open ShenWork.IntervalBFormSpectral
  (LogisticCosineFourierData
   logisticCosineFourierData_constExtend)
open ShenWork.Paper2.BankChemSliceFix
  (ChemDivCosineFourierDataIoo)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceCoeffs
   coupledLogisticSourceCoeffs sourceCoeffQuadraticDecay_of_closedC2_neumann_slice
   coupledChemical_ellipticPDE_of_closedC2_neumann
   coupledChemical_neumannBC_of_closedC2_neumann)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs)
open ShenWork.CosineSpectrum
  (cosineMode)
open ShenWork.Paper2
open ShenWork.Paper2.RegularityFrontierAssembly
open ShenWork.IntervalResolverSpatialC2
  (resolverR_summability)
open ShenWork.IntervalCosineSliceRegularity
  (intervalDomainCosineSlice_contDiffOn_Ioo
   intervalDomainCosineSlice_neumann_limit_left
   intervalDomainCosineSlice_neumann_limit_right
   intervalDomainCosineSlice_conjunct7)
open ShenWork.PDE

noncomputable section

namespace ShenWork.Paper2.BFormBddDirectClassical

/-- Local restart data sufficient for the interior PDE identity. -/
structure BFormBddLocalSourceData
    (p : CM2Params) (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    (t₀ : ℝ) where
  a₀ : ℕ → ℝ
  M : ℝ
  hM : 0 ≤ M
  ha₀ : ∀ n, |a₀ n| ≤ M
  a : ℝ → ℕ → ℝ
  W : ℝ
  src : DuhamelSourceBddOn a W
  hcont : ∀ n, Continuous (fun s => a s n)
  offset : ℝ
  hrelPos : 0 < t₀ - offset
  hrelLt : t₀ - offset < W
  hlog : LogisticCosineFourierData p u t₀
  hchem : ChemDivCosineFourierDataIoo p (u t₀)
    (coupledChemicalConcentration p u t₀)
  hrep : ∀ᶠ s in 𝓝 t₀, ∀ y : intervalDomainPoint,
    u s y = ∑' n, localRestartCoeff a₀ a (s - offset) n * cosineMode n y.1
  hsource : ∀ n, a (t₀ - offset) n =
    coupledLogisticSourceCoeffs p u t₀ n
      - p.χ₀ * coupledChemDivSourceCoeffs p u t₀ n

private theorem eigenvalue_coeff_cosine_summable
    {b : ℕ → ℝ}
    (hsum : Summable (fun n => unitIntervalCosineEigenvalue n * |b n|))
    (x : ℝ) :
    Summable (fun n => unitIntervalCosineEigenvalue n * b n * cosineMode n x) := by
  refine Summable.of_norm_bounded
    (g := fun n => unitIntervalCosineEigenvalue n * |b n|) hsum ?_
  intro n
  have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue
    positivity
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hlam]
  calc
    unitIntervalCosineEigenvalue n * |b n| * |cosineMode n x|
        ≤ unitIntervalCosineEigenvalue n * |b n| * 1 :=
          mul_le_mul_of_nonneg_left
            (by simp only [cosineMode]; exact Real.abs_cos_le_one _)
            (mul_nonneg hlam (abs_nonneg _))
    _ = unitIntervalCosineEigenvalue n * |b n| := mul_one _

/-- The general-chi PDE identity from a continuity-only bounded local restart. -/
theorem hpde_u_of_generalChi_bddSourceData
    (p : CM2Params) {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (Hsource : ∀ t₀, 0 < t₀ → t₀ < T →
      BFormBddLocalSourceData p T u t₀) :
    ∀ t x, 0 < t → t < T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv u t x =
        intervalDomain.laplacian (u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (u t)
              (mildChemicalConcentration p u t) x
          + u t x * (p.a - p.b * (u t x) ^ p.α) := by
  intro t x ht htT hx
  let H := Hsource t ht htT
  have htimeRaw :
      intervalDomain.timeDeriv u t x = ∑' n,
        (H.a (t - H.offset) n - unitIntervalCosineEigenvalue n *
          localRestartCoeff H.a₀ H.a (t - H.offset) n) * cosineMode n x.1 := by
    have hspec :=
      ShenWork.Paper2.PicardLimitK1Weak.restartCosineSeries_hasDerivAt_time_bdd
        H.ha₀ H.src H.hcont H.hrelPos H.hrelLt x.1
    have hshift : HasDerivAt (fun s : ℝ => s - H.offset) 1 t :=
      (hasDerivAt_id t).sub_const H.offset
    have hcomp := hspec.comp t hshift
    simp only [mul_one] at hcomp
    have hev : (fun s => u s x) =ᶠ[𝓝 t]
        (fun s => ∑' n, localRestartCoeff H.a₀ H.a (s - H.offset) n *
          cosineMode n x.1) :=
      H.hrep.mono (fun _ hs => hs x)
    exact (hcomp.congr_of_eventuallyEq hev).deriv
  have htime :
      intervalDomain.timeDeriv u t x = ∑' n,
        (coupledLogisticSourceCoeffs p u t n
          - p.χ₀ * coupledChemDivSourceCoeffs p u t n
          - unitIntervalCosineEigenvalue n *
            localRestartCoeff H.a₀ H.a (t - H.offset) n) * cosineMode n x.1 := by
    rw [htimeRaw]
    exact tsum_congr (fun n => by rw [H.hsource n])
  have hsum_b : Summable (fun n => unitIntervalCosineEigenvalue n *
      |localRestartCoeff H.a₀ H.a (t - H.offset) n|) :=
    localRestartCoeff_eigenvalue_summable_bdd
      H.ha₀ H.src H.hrelPos H.hrelLt.le
  have hrepReal : ∀ z ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (u t) z = ∑' n,
        localRestartCoeff H.a₀ H.a (t - H.offset) n * cosineMode n z := by
    intro z hz
    rw [intervalDomainLift, dif_pos hz]
    exact H.hrep.self_of_nhds ⟨z, hz⟩
  have hlap : intervalDomain.laplacian (u t) x = ∑' n,
      localRestartCoeff H.a₀ H.a (t - H.offset) n *
        (-(((n : ℝ) * Real.pi) ^ 2) * Real.cos ((n : ℝ) * Real.pi * x.1)) :=
    ShenWork.IntervalDomainPdeUChiZero.laplacian_eq_of_rep hsum_b hrepReal hx
  have hreact :
      (∑' n, coupledLogisticSourceCoeffs p u t n * cosineMode n x.1) =
        u t x * (p.a - p.b * (u t x) ^ p.α) :=
    ShenWork.IntervalBFormSpectral.coupledLogistic_cosineFourier_convergence
      H.hlog hx
  have hchem :
      (∑' n, coupledChemDivSourceCoeffs p u t n * cosineMode n x.1) =
        intervalDomain.chemotaxisDiv p (u t)
          (mildChemicalConcentration p u t) x :=
    ShenWork.Paper2.BankChemSliceFix.coupledChemDiv_cosineFourier_convergence_Ioo
      p u t H.hchem hx
  have hsumSrc :=
    ShenWork.IntervalBFormSpectral.coupledLogistic_cosineSeries_summable H.hlog hx
  have hsumChem :=
    ShenWork.Paper2.BankChemSliceFix.coupledChemDiv_cosineSeries_summable_Ioo
      p u t H.hchem hx
  have hsumLap := eigenvalue_coeff_cosine_summable hsum_b x.1
  exact ShenWork.IntervalConjugateDuhamelMap.hpde_u_core_general_chi p
    hsumSrc hsumChem hsumLap htime hlap hreact hchem

/-- Build the local bounded restart data by soft-clamping the patched from-zero
source inside a compact positive-time window. -/
noncomputable def bFormBddLocalSourceData_of_global
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (aInit : ℕ → ℝ) (aB : ℝ → ℕ → ℝ)
    {MInit : ℝ} (haInit : ∀ n, |aInit n| ≤ MInit)
    (hsrcBdd : DuhamelSourceBddOn aB T)
    (hBglobal : ∀ t, 0 < t → t ≤ T →
      Set.EqOn (intervalDomainLift (u t))
        (fun x => ∑' n, localRestartCoeff aInit aB t n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1))
    (hsourceSplit : ∀ σ, 0 < σ → σ < T → ∀ n,
      aB σ n = coupledLogisticSourceCoeffs p u σ n
        - p.χ₀ * coupledChemDivSourceCoeffs p u σ n)
    (hlogData : ∀ t, 0 < t → t < T → LogisticCosineFourierData p u t)
    (hchemData : ∀ t, 0 < t → t < T →
      ChemDivCosineFourierDataIoo p (u t)
        (coupledChemicalConcentration p u t))
    {t₀ : ℝ} (ht₀ : 0 < t₀) (ht₀T : t₀ < T) :
    BFormBddLocalSourceData p T u t₀ := by
  let τ : ℝ := t₀ / 2
  let c : ℝ := t₀ / 4
  let d : ℝ := (t₀ + T) / 2
  let d' : ℝ := (t₀ + 3 * T) / 4
  have hτpos : 0 < τ := by dsimp [τ]; linarith
  have hτt₀ : τ < t₀ := by dsimp [τ]; linarith
  have hτT : τ < T := lt_trans hτt₀ ht₀T
  have hcτ : c < τ := by dsimp [c, τ]; linarith
  have hc : 0 < c := by dsimp [c]; linarith
  have hτd : τ ≤ d := by dsimp [τ, d]; linarith
  have hdd' : d < d' := by dsimp [d, d']; linarith
  have hd'T : d' ≤ T := by dsimp [d']; linarith
  have ht₀d : t₀ < d := by dsimp [d]; linarith
  let aC : ℝ → ℕ → ℝ := softClampedShiftSource aB c τ d d'
  have hcontC : ∀ n, Continuous (fun r => aC r n) := by
    intro n
    exact softClampedShiftSource_continuous
      hsrcBdd hc.le hcτ hτd hdd' hd'T n
  have hsrcC : DuhamelSourceBddOn aC (d - τ) := by
    exact ShenWork.Paper2.BFormBddRestart.DuhamelSourceBddOn.softClampShift
      hsrcBdd hc hcτ hτd hdd' hd'T
  have hsumGlobal : ∀ t, 0 < t → t ≤ T →
      Summable (fun n => |localRestartCoeff aInit aB t n|) := by
    intro t ht htT
    exact localRestartCoeff_abs_summable_bdd haInit hsrcBdd ht htT
  have hrestart := ShenWork.IntervalConjugatePicard.bForm_restart_of_global_cosine
    (u := u) (T := T) (a₀ := aInit) (aB := aB)
    hsrcBdd.hcont hBglobal hsumGlobal t₀ ht₀ ht₀T
  let a₀ : ℕ → ℝ := cosineCoeffs (intervalDomainLift (u τ))
  have hrestart' : ∀ᶠ s in 𝓝 t₀, ∀ y : intervalDomainPoint,
      u s y = ∑' n,
        localRestartCoeff a₀ (fun ρ n => aB (τ + ρ) n) (s - τ) n *
          cosineMode n y.1 := by
    simpa [a₀, τ] using hrestart
  have hsumτ : Summable (fun n => |localRestartCoeff aInit aB τ n|) :=
    hsumGlobal τ hτpos hτT.le
  let M : ℝ := ∑' n, |localRestartCoeff aInit aB τ n|
  have hM : 0 ≤ M := tsum_nonneg (fun n => abs_nonneg _)
  have ha₀Eq : ∀ n, a₀ n = localRestartCoeff aInit aB τ n := by
    intro n
    exact ShenWork.IntervalConjugatePicard.cosineCoeffs_eq_localRestartCoeff_of_bForm_global_rep
      (u := u) (a₀ := aInit) (aB := aB) (τ := τ)
      (hBglobal τ hτpos hτT.le) hsumτ n
  have ha₀ : ∀ n, |a₀ n| ≤ M := by
    intro n
    rw [ha₀Eq n]
    have hnn : ∀ k, 0 ≤ |localRestartCoeff aInit aB τ k| :=
      fun k => abs_nonneg _
    simpa [M] using
      hsumτ.sum_le_tsum ({n} : Finset ℕ) (fun k _ => hnn k)
  have hrep : ∀ᶠ s in 𝓝 t₀, ∀ y : intervalDomainPoint,
      u s y = ∑' n, localRestartCoeff a₀ aC (s - τ) n * cosineMode n y.1 := by
    filter_upwards [hrestart', isOpen_Ioo.mem_nhds ⟨hτt₀, ht₀d⟩] with s hs hswin
    intro y
    rw [hs y]
    refine tsum_congr (fun n => ?_)
    congr 1
    unfold localRestartCoeff ShenWork.IntervalDuhamelClosedC2.duhamelSpectralCoeff
    congr 1
    apply intervalIntegral.integral_congr
    intro r hr
    rw [Set.uIcc_of_le (by linarith [hswin.1] : (0 : ℝ) ≤ s - τ)] at hr
    have hmem : τ + r ∈ Set.Icc τ d :=
      ⟨by linarith [hr.1], by linarith [hr.2, hswin.2.le]⟩
    change Real.exp (-(s - τ - r) * unitIntervalCosineEigenvalue n) *
        aB (τ + r) n =
      Real.exp (-(s - τ - r) * unitIntervalCosineEigenvalue n) * aC r n
    rw [show aC r n = aB (τ + r) n from
      softClampedShiftSource_eq_of_mem hcτ hdd' hmem n]
  have hsource : ∀ n, aC (t₀ - τ) n =
      coupledLogisticSourceCoeffs p u t₀ n
        - p.χ₀ * coupledChemDivSourceCoeffs p u t₀ n := by
    intro n
    rw [show aC (t₀ - τ) n = aB (τ + (t₀ - τ)) n from
      softClampedShiftSource_eq_of_mem hcτ hdd'
        (by constructor <;> linarith [hτt₀, ht₀d]) n]
    convert hsourceSplit t₀ ht₀ ht₀T n using 1
    all_goals ring_nf
  refine
    { a₀ := a₀
      M := M
      hM := hM
      ha₀ := ha₀
      a := aC
      W := d - τ
      src := hsrcC
      hcont := hcontC
      offset := τ
      hrelPos := by linarith
      hrelLt := by linarith
      hlog := hlogData t₀ ht₀ ht₀T
      hchem := hchemData t₀ ht₀ ht₀T
      hrep := hrep
      hsource := hsource }

/-- Interior PDE identity from the bounded/patched source interface. -/
theorem hpde_u_of_bForm_global_generalChi_bdd
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (aInit : ℕ → ℝ) (aB : ℝ → ℕ → ℝ)
    {MInit : ℝ} (haInit : ∀ n, |aInit n| ≤ MInit)
    (hsrcBdd : DuhamelSourceBddOn aB T)
    (hBglobal : ∀ t, 0 < t → t ≤ T →
      Set.EqOn (intervalDomainLift (u t))
        (fun x => ∑' n, localRestartCoeff aInit aB t n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1))
    (hsourceSplit : ∀ σ, 0 < σ → σ < T → ∀ n,
      aB σ n = coupledLogisticSourceCoeffs p u σ n
        - p.χ₀ * coupledChemDivSourceCoeffs p u σ n)
    (hlogData : ∀ t, 0 < t → t < T → LogisticCosineFourierData p u t)
    (hchemData : ∀ t, 0 < t → t < T →
      ChemDivCosineFourierDataIoo p (u t)
        (coupledChemicalConcentration p u t)) :
    ∀ t x, 0 < t → t < T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv u t x =
        intervalDomain.laplacian (u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (u t)
              (mildChemicalConcentration p u t) x
          + u t x * (p.a - p.b * (u t x) ^ p.α) :=
  hpde_u_of_generalChi_bddSourceData p
    (fun _ ht htT => bFormBddLocalSourceData_of_global
      aInit aB haInit hsrcBdd hBglobal hsourceSplit hlogData hchemData ht htT)

/-- Banked B-form inputs with an explicit endpoint-patched source family. -/
structure BFormBddBankedInputs
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) where
  huPaper : PaperPositiveInitialDatum intervalDomain u₀
  Hinf : ConjugatePicardInfThresholdData p u₀ DB.T
  hsmall :
    |p.χ₀| * (heatGradientLinftyLinftyConstant *
        (2 * Real.sqrt DB.T) * Hinf.CQ)
      + DB.T * Hinf.CL ≤ paperPositiveFloor huPaper / 2
  MInit : ℝ
  haInit : ∀ n, |cosineCoeffs (intervalDomainLift u₀) n| ≤ MInit
  aB : ℝ → ℕ → ℝ
  hsrcBdd : DuhamelSourceBddOn aB DB.T
  hsourceSplit : ∀ σ, 0 < σ → σ < DB.T → ∀ n,
    aB σ n =
      coupledLogisticSourceCoeffs p (conjugatePicardLimit p u₀ DB.T) σ n
        - p.χ₀ * coupledChemDivSourceCoeffs p
            (conjugatePicardLimit p u₀ DB.T) σ n
  hBglobal : ∀ t, 0 < t → t ≤ DB.T →
    Set.EqOn
      (intervalDomainLift (conjugatePicardLimit p u₀ DB.T t))
      (fun x => ∑' n,
        localRestartCoeff (cosineCoeffs (intervalDomainLift u₀)) aB t n *
          cosineMode n x)
      (Set.Icc (0 : ℝ) 1)
  hlogCont : ∀ t, 0 < t → t < DB.T →
    Continuous
      (intervalDomainConstExtend
        (ShenWork.IntervalDomainExistence.intervalLogisticSource p
          ((conjugatePicardLimit p u₀ DB.T) t)))
  hlogFourier : ∀ t, 0 < t → t < DB.T →
    Summable (fun n : ℤ =>
      fourierCoeff
        (ShenWork.IntervalCosineInversion.reflCircle
          (intervalDomainConstExtend
            (ShenWork.IntervalDomainExistence.intervalLogisticSource p
              ((conjugatePicardLimit p u₀ DB.T) t)))) n)
  hchemIoo : ∀ t, 0 < t → t < DB.T →
    ChemDivCosineFourierDataIoo p
      ((conjugatePicardLimit p u₀ DB.T) t)
      (coupledChemicalConcentration p
        (conjugatePicardLimit p u₀ DB.T) t)

/-- At positive times the patched source is the physical B-form split. -/
theorem patchedBFormSourceCoeffs_sourceSplit
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ)
    {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    patchedBFormSourceCoeffs p u₀ u σ n =
      coupledLogisticSourceCoeffs p u σ n
        - p.χ₀ * coupledChemDivSourceCoeffs p u σ n := by
  rw [patchedBFormSourceCoeffs_eq_of_pos p u₀ u hσ n]
  rfl

/-- Rewrite a canonical from-zero cosine representation to the endpoint-patched
source.  A single endpoint does not change any positive-time Duhamel coefficient. -/
theorem hBglobal_patched_of_canonical
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) {T : ℝ}
    (hcanonical : ∀ t, 0 < t → t ≤ T →
      Set.EqOn (intervalDomainLift (u t))
        (fun x => ∑' n,
          localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
            (ShenWork.IntervalBFormSpectral.bFormSourceCoeffs p u) t n *
              cosineMode n x)
        (Set.Icc (0 : ℝ) 1)) :
    ∀ t, 0 < t → t ≤ T →
      Set.EqOn (intervalDomainLift (u t))
        (fun x => ∑' n,
          localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
            (patchedBFormSourceCoeffs p u₀ u) t n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1) := by
  intro t ht htT x hx
  rw [hcanonical t ht htT hx]
  refine tsum_congr (fun n => ?_)
  rw [localRestartCoeff_patched_eq_canonical p u₀ u
    (cosineCoeffs (intervalDomainLift u₀)) ht n]

/-- Construct the bounded bank from the endpoint-patched source and an existing
canonical cosine representation. -/
noncomputable def BFormBddBankedInputs.of_patched
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (huPaper : PaperPositiveInitialDatum intervalDomain u₀)
    (Hinf : ConjugatePicardInfThresholdData p u₀ DB.T)
    (hsmall :
      |p.χ₀| * (heatGradientLinftyLinftyConstant *
          (2 * Real.sqrt DB.T) * Hinf.CQ)
        + DB.T * Hinf.CL ≤ paperPositiveFloor huPaper / 2)
    (MInit : ℝ)
    (haInit : ∀ n, |cosineCoeffs (intervalDomainLift u₀) n| ≤ MInit)
    (hsrcBdd : DuhamelSourceBddOn
      (patchedBFormSourceCoeffs p u₀
        (conjugatePicardLimit p u₀ DB.T)) DB.T)
    (hBcanonical : ∀ t, 0 < t → t ≤ DB.T →
      Set.EqOn
        (intervalDomainLift (conjugatePicardLimit p u₀ DB.T t))
        (fun x => ∑' n,
          localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
            (ShenWork.IntervalBFormSpectral.bFormSourceCoeffs p
              (conjugatePicardLimit p u₀ DB.T)) t n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1))
    (hlogCont : ∀ t, 0 < t → t < DB.T →
      Continuous
        (intervalDomainConstExtend
          (ShenWork.IntervalDomainExistence.intervalLogisticSource p
            ((conjugatePicardLimit p u₀ DB.T) t))))
    (hlogFourier : ∀ t, 0 < t → t < DB.T →
      Summable (fun n : ℤ =>
        fourierCoeff
          (ShenWork.IntervalCosineInversion.reflCircle
            (intervalDomainConstExtend
              (ShenWork.IntervalDomainExistence.intervalLogisticSource p
                ((conjugatePicardLimit p u₀ DB.T) t)))) n))
    (hchemIoo : ∀ t, 0 < t → t < DB.T →
      ChemDivCosineFourierDataIoo p
        ((conjugatePicardLimit p u₀ DB.T) t)
        (coupledChemicalConcentration p
          (conjugatePicardLimit p u₀ DB.T) t)) :
    BFormBddBankedInputs p DB where
  huPaper := huPaper
  Hinf := Hinf
  hsmall := hsmall
  MInit := MInit
  haInit := haInit
  aB := patchedBFormSourceCoeffs p u₀
    (conjugatePicardLimit p u₀ DB.T)
  hsrcBdd := hsrcBdd
  hsourceSplit := fun _ hσ _ n =>
    patchedBFormSourceCoeffs_sourceSplit p u₀
      (conjugatePicardLimit p u₀ DB.T) hσ n
  hBglobal := hBglobal_patched_of_canonical p u₀
    (conjugatePicardLimit p u₀ DB.T) hBcanonical
  hlogCont := hlogCont
  hlogFourier := hlogFourier
  hchemIoo := hchemIoo

private theorem bform_restartCoeff_eigenvalue_summable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBddBankedInputs p DB)
    {t : ℝ} (ht : 0 < t) (htT : t < DB.T) :
    Summable (fun n : ℕ => unitIntervalCosineEigenvalue n *
      |localRestartCoeff (cosineCoeffs (intervalDomainLift u₀)) B.aB t n|) :=
  localRestartCoeff_eigenvalue_summable_bdd B.haInit B.hsrcBdd ht htT.le

private theorem bform_B_global_as_restartCoeff_eqOn
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBddBankedInputs p DB)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DB.T) :
    Set.EqOn (intervalDomainLift (conjugatePicardLimit p u₀ DB.T t))
      (fun x : ℝ => ∑' n : ℕ,
        localRestartCoeff (cosineCoeffs (intervalDomainLift u₀)) B.aB t n *
          cosineMode n x)
      (Set.Icc (0 : ℝ) 1) :=
  B.hBglobal t ht htT

theorem BFormBddBankedInputs.hpde_u
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBddBankedInputs p DB) :
    ∀ t x, 0 < t → t < DB.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv (conjugatePicardLimit p u₀ DB.T) t x =
        intervalDomain.laplacian ((conjugatePicardLimit p u₀ DB.T) t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p
              ((conjugatePicardLimit p u₀ DB.T) t)
              (mildChemicalConcentration p
                (conjugatePicardLimit p u₀ DB.T) t) x
          + (conjugatePicardLimit p u₀ DB.T) t x *
              (p.a - p.b * ((conjugatePicardLimit p u₀ DB.T) t x) ^ p.α) :=
  hpde_u_of_bForm_global_generalChi_bdd
    (cosineCoeffs (intervalDomainLift u₀)) B.aB B.haInit
    B.hsrcBdd B.hBglobal B.hsourceSplit
    (fun t ht htT =>
      logisticCosineFourierData_constExtend p
        (conjugatePicardLimit p u₀ DB.T) t
        (B.hlogCont t ht htT) (B.hlogFourier t ht htT))
    (fun t ht htT => B.hchemIoo t ht htT)

/-- Direct frontier using the bounded/patched B-form bank. -/
structure BFormBddDirectFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) where
  bank : BFormBddBankedInputs p DB
  hTimeNhd :
    HasTimeNeighborhoodSpectralAgreement DB.T
      (conjugatePicardLimit p u₀ DB.T)
  hResolverData :
    HasResolverDirectSpectralData DB.T
      (mildChemicalConcentration p (conjugatePicardLimit p u₀ DB.T)) p
  hVpos : ∀ t, 0 < t → t < DB.T → ∀ x : intervalDomainPoint,
    0 < mildChemicalConcentration p
      (conjugatePicardLimit p u₀ DB.T) t x

private theorem bform_u_pos
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBddBankedInputs p DB) :
    ∀ t x, 0 < t → t < DB.T →
      0 < conjugatePicardLimit p u₀ DB.T t x := by
  intro t x ht htT
  exact ShenWork.IntervalConjugatePicard.conjugatePicardLimit_pos_of_PID
    B.huPaper B.Hinf B.hsmall t ht htT.le x

private theorem bform_u_closedC2_endpointDerivs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBddBankedInputs p DB) :
    ∀ t, 0 < t → t < DB.T →
      ContDiffOn ℝ 2
          (intervalDomainLift (conjugatePicardLimit p u₀ DB.T t))
          (Set.Icc (0 : ℝ) 1) ∧
        deriv (intervalDomainLift (conjugatePicardLimit p u₀ DB.T t)) 0 = 0 ∧
        deriv (intervalDomainLift (conjugatePicardLimit p u₀ DB.T t)) 1 = 0 := by
  intro t ht htT
  have h0 : intervalDomainLift (conjugatePicardLimit p u₀ DB.T t) 0 ≠ 0 := by
    have hmem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
    simp only [intervalDomainLift, hmem, dif_pos]
    exact ne_of_gt (bform_u_pos B t ⟨0, hmem⟩ ht htT)
  have h1 : intervalDomainLift (conjugatePicardLimit p u₀ DB.T t) 1 ≠ 0 := by
    have hmem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
    simp only [intervalDomainLift, hmem, dif_pos]
    exact ne_of_gt (bform_u_pos B t ⟨1, hmem⟩ ht htT)
  exact intervalDomainCosineSlice_conjunct7
    (bform_restartCoeff_eigenvalue_summable B ht htT)
    (bform_B_global_as_restartCoeff_eqOn B ht htT.le) h0 h1

private theorem bform_u_neumann_left
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBddBankedInputs p DB) :
    ∀ t, 0 < t → t < DB.T →
      Filter.Tendsto
        (deriv (intervalDomainLift (conjugatePicardLimit p u₀ DB.T t)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  intro t ht htT
  exact intervalDomainCosineSlice_neumann_limit_left
    (bform_restartCoeff_eigenvalue_summable B ht htT)
    (bform_B_global_as_restartCoeff_eqOn B ht htT.le)

private theorem bform_u_neumann_right
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBddBankedInputs p DB) :
    ∀ t, 0 < t → t < DB.T →
      Filter.Tendsto
        (deriv (intervalDomainLift (conjugatePicardLimit p u₀ DB.T t)))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by
  intro t ht htT
  exact intervalDomainCosineSlice_neumann_limit_right
    (bform_restartCoeff_eigenvalue_summable B ht htT)
    (bform_B_global_as_restartCoeff_eqOn B ht htT.le)

private def bform_sourceDecay
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBddBankedInputs p DB)
    {t : ℝ} (ht : 0 < t) (htT : t < DB.T) :
    SourceCoeffQuadraticDecay p (conjugatePicardLimit p u₀ DB.T t) := by
  have hposLift : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardLimit p u₀ DB.T t) y := by
    intro y hy
    simp only [intervalDomainLift, hy, dif_pos]
    exact bform_u_pos B t ⟨y, hy⟩ ht htT
  exact sourceCoeffQuadraticDecay_of_closedC2_neumann_slice
    (p := p) (u := conjugatePicardLimit p u₀ DB.T t)
    (bform_u_closedC2_endpointDerivs B t ht htT).1
    (bform_u_neumann_left B t ht htT)
    (bform_u_neumann_right B t ht htT) hposLift

private theorem lift_resolver_eqOn_Icc
    (p : CM2Params) (u : intervalDomainPoint → ℝ) :
    Set.EqOn
      (intervalDomainLift (intervalNeumannResolverR p u))
      (fun x : ℝ => ∑' k : ℕ,
        (intervalNeumannResolverCoeff p u k).re * cosineMode k x)
      (Set.Icc (0 : ℝ) 1) := by
  intro x hx
  simp only [intervalDomainLift, dif_pos hx,
    ShenWork.IntervalResolverGradientBridge.resolverR_apply_eq, cosineMode]

private theorem resolver_lift_ne_zero
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (x : intervalDomainPoint)
    (hpos : 0 < intervalNeumannResolverR p u x) :
    intervalDomainLift (intervalNeumannResolverR p u) x.1 ≠ 0 := by
  have heq : intervalDomainLift (intervalNeumannResolverR p u) x.1 =
      intervalNeumannResolverR p u x := by
    unfold intervalDomainLift
    split
    · rfl
    · exact absurd x.2 ‹_›
  rw [heq]
  exact ne_of_gt hpos

private theorem bform_vSpatialInterior
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBddBankedInputs p DB) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) DB.T →
      ContDiffOn ℝ 2
        (intervalDomainLift
          (mildChemicalConcentration p (conjugatePicardLimit p u₀ DB.T) t))
        (Set.Ioo (0 : ℝ) 1) := by
  intro t ht
  change ContDiffOn ℝ 2
    (intervalDomainLift
      (intervalNeumannResolverR p (conjugatePicardLimit p u₀ DB.T t)))
    (Set.Ioo (0 : ℝ) 1)
  exact intervalDomainCosineSlice_contDiffOn_Ioo
    (resolverR_summability (bform_sourceDecay B ht.1 ht.2))
    (lift_resolver_eqOn_Icc p (conjugatePicardLimit p u₀ DB.T t))

private theorem bform_vNeumannLimits
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBddBankedInputs p DB) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) DB.T →
      Filter.Tendsto
          (deriv (intervalDomainLift
            (mildChemicalConcentration p
              (conjugatePicardLimit p u₀ DB.T) t)))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto
          (deriv (intervalDomainLift
            (mildChemicalConcentration p
              (conjugatePicardLimit p u₀ DB.T) t)))
          (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by
  intro t ht
  change Filter.Tendsto
          (deriv (intervalDomainLift
            (intervalNeumannResolverR p (conjugatePicardLimit p u₀ DB.T t))))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto
          (deriv (intervalDomainLift
            (intervalNeumannResolverR p (conjugatePicardLimit p u₀ DB.T t))))
          (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0)
  exact
    ⟨intervalDomainCosineSlice_neumann_limit_left
        (resolverR_summability (bform_sourceDecay B ht.1 ht.2))
        (lift_resolver_eqOn_Icc p (conjugatePicardLimit p u₀ DB.T t)),
      intervalDomainCosineSlice_neumann_limit_right
        (resolverR_summability (bform_sourceDecay B ht.1 ht.2))
        (lift_resolver_eqOn_Icc p (conjugatePicardLimit p u₀ DB.T t))⟩

private theorem bform_vClosedSpatial
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBddBankedInputs p DB)
    (hVpos : ∀ t, 0 < t → t < DB.T → ∀ x : intervalDomainPoint,
      0 < mildChemicalConcentration p
        (conjugatePicardLimit p u₀ DB.T) t x) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) DB.T →
      ContDiffOn ℝ 2
          (intervalDomainLift
            (mildChemicalConcentration p
              (conjugatePicardLimit p u₀ DB.T) t))
          (Set.Icc (0 : ℝ) 1) ∧
        deriv
          (intervalDomainLift
            (mildChemicalConcentration p
              (conjugatePicardLimit p u₀ DB.T) t)) 0 = 0 ∧
        deriv
          (intervalDomainLift
            (mildChemicalConcentration p
              (conjugatePicardLimit p u₀ DB.T) t)) 1 = 0 := by
  intro t ht
  change ContDiffOn ℝ 2
          (intervalDomainLift
            (intervalNeumannResolverR p (conjugatePicardLimit p u₀ DB.T t)))
          (Set.Icc (0 : ℝ) 1) ∧
        deriv
          (intervalDomainLift
            (intervalNeumannResolverR p (conjugatePicardLimit p u₀ DB.T t))) 0 = 0 ∧
        deriv
          (intervalDomainLift
            (intervalNeumannResolverR p (conjugatePicardLimit p u₀ DB.T t))) 1 = 0
  have hv0 : 0 < intervalNeumannResolverR p
      (conjugatePicardLimit p u₀ DB.T t)
      ⟨0, by constructor <;> norm_num⟩ := by
    simpa [mildChemicalConcentration] using
      hVpos t ht.1 ht.2 ⟨0, by constructor <;> norm_num⟩
  have hv1 : 0 < intervalNeumannResolverR p
      (conjugatePicardLimit p u₀ DB.T t)
      ⟨1, by constructor <;> norm_num⟩ := by
    simpa [mildChemicalConcentration] using
      hVpos t ht.1 ht.2 ⟨1, by constructor <;> norm_num⟩
  exact intervalDomainCosineSlice_conjunct7
    (resolverR_summability (bform_sourceDecay B ht.1 ht.2))
    (lift_resolver_eqOn_Icc p (conjugatePicardLimit p u₀ DB.T t))
    (resolver_lift_ne_zero ⟨0, by constructor <;> norm_num⟩ hv0)
    (resolver_lift_ne_zero ⟨1, by constructor <;> norm_num⟩ hv1)

theorem intervalConjugatePicardLimit_classicalRegularity_bdd
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : BFormBddDirectFrontier p DB) :
    intervalDomainClassicalRegularity DB.T
      (conjugatePicardLimit p u₀ DB.T)
      (mildChemicalConcentration p
        (conjugatePicardLimit p u₀ DB.T)) := by
  unfold intervalDomainClassicalRegularity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact
      ⟨(bform_u_closedC2_endpointDerivs F.bank t ht.1 ht.2).1.mono
          Set.Ioo_subset_Icc_self,
        bform_vSpatialInterior F.bank t ht⟩
  · intro x t ht
    have hu := timeSlices_u_of_spectralAgreement F.hTimeNhd x
    have hv := timeSlices_v_of_resolverSpectral F.hResolverData x
    exact ⟨⟨hu.1 t ht, hv.1 t ht⟩, ⟨hu.2, hv.2⟩⟩
  · exact
      ⟨jointTimeDerivInterior_u_of_spectralAgreement F.hTimeNhd,
       jointTimeDerivInterior_v_of_resolverSpectral F.hResolverData⟩
  · intro t ht
    exact
      ⟨⟨bform_u_neumann_left F.bank t ht.1 ht.2,
          bform_u_neumann_right F.bank t ht.1 ht.2⟩,
        bform_vNeumannLimits F.bank t ht⟩
  · intro t ht
    exact
      ⟨bform_u_closedC2_endpointDerivs F.bank t ht.1 ht.2,
        bform_vClosedSpatial F.bank F.hVpos t ht⟩
  · exact
      ⟨jointTimeDerivClosed_u_of_spectralAgreement F.hTimeNhd,
       jointTimeDerivClosed_v_of_resolverSpectral F.hResolverData⟩
  · exact
      ⟨jointSolutionClosed_u_of_spectralAgreement F.hTimeNhd,
       jointSolutionClosed_v_of_resolverSpectral F.hResolverData⟩

theorem intervalConjugatePicardLimit_initialTrace_bdd
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : BFormBddDirectFrontier p DB) :
    InitialTrace intervalDomain u₀ (conjugatePicardLimit p u₀ DB.T) :=
  ShenWork.Paper2.BFormInitialTrace.conjugatePicardLimit_initialTrace_of_conjugate_data
    p (PaperPositiveInitialDatum.admissible F.bank.huPaper).2 DB

theorem intervalConjugatePicardLimit_isClassicalSolution_bdd
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : BFormBddDirectFrontier p DB) :
    IsPaper2ClassicalSolution intervalDomain p DB.T
      (conjugatePicardLimit p u₀ DB.T)
      (mildChemicalConcentration p
        (conjugatePicardLimit p u₀ DB.T)) := by
  refine IsPaper2ClassicalSolution.of_components DB.hT
    (intervalConjugatePicardLimit_classicalRegularity_bdd F)
    ?_ ?_ ?_ ?_ ?_
  · exact bform_u_pos F.bank
  · intro t x ht htT
    exact le_of_lt (F.hVpos t ht htT x)
  · exact F.bank.hpde_u
  · have h :=
      coupledChemical_ellipticPDE_of_closedC2_neumann p
        (bform_u_pos F.bank)
        (fun t ht htT => (bform_u_closedC2_endpointDerivs F.bank t ht htT).1)
        (bform_u_neumann_left F.bank)
        (bform_u_neumann_right F.bank)
    simpa [coupledChemicalConcentration, mildChemicalConcentration] using h
  · have h :=
      coupledChemical_neumannBC_of_closedC2_neumann p
        (bform_u_pos F.bank)
        (fun t ht htT => (bform_u_closedC2_endpointDerivs F.bank t ht htT).1)
        (bform_u_neumann_left F.bank)
        (bform_u_neumann_right F.bank)
    simpa [coupledChemicalConcentration, mildChemicalConcentration] using h

theorem localClassicalSolution_of_BFormBddDirectFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : BFormBddDirectFrontier p DB) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u₀ u := by
  refine ⟨DB.T, DB.hT,
    conjugatePicardLimit p u₀ DB.T,
    mildChemicalConcentration p (conjugatePicardLimit p u₀ DB.T), ?_⟩
  exact ⟨intervalConjugatePicardLimit_isClassicalSolution_bdd F,
    intervalConjugatePicardLimit_initialTrace_bdd F⟩

def BFormBddPaperLocalFrontier (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomainPoint → ℝ,
    PaperPositiveInitialDatum intervalDomain u₀ →
      ∃ DB : ConjugateMildExistenceData p u₀,
        Nonempty (BFormBddDirectFrontier p DB)

theorem paperPositive_localExistence_of_BFormBddDirect
    {p : CM2Params}
    (hPerDatum : BFormBddPaperLocalFrontier p) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PaperPositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro u₀ hu₀
  obtain ⟨DB, ⟨F⟩⟩ := hPerDatum u₀ hu₀
  exact localClassicalSolution_of_BFormBddDirectFrontier F

section AxiomAudit
#print axioms hpde_u_of_generalChi_bddSourceData
#print axioms bFormBddLocalSourceData_of_global
#print axioms hpde_u_of_bForm_global_generalChi_bdd
#print axioms patchedBFormSourceCoeffs_sourceSplit
#print axioms hBglobal_patched_of_canonical
#print axioms BFormBddBankedInputs.of_patched
#print axioms BFormBddBankedInputs.hpde_u
#print axioms intervalConjugatePicardLimit_classicalRegularity_bdd
#print axioms intervalConjugatePicardLimit_isClassicalSolution_bdd
#print axioms localClassicalSolution_of_BFormBddDirectFrontier
#print axioms paperPositive_localExistence_of_BFormBddDirect
end AxiomAudit

end ShenWork.Paper2.BFormBddDirectClassical
