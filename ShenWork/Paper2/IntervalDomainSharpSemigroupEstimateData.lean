import ShenWork.Paper2.IntervalSharpSpectralPhysicalL2
import ShenWork.Paper2.IntervalSharpSpectralPhysicalFractionalDivergenceL2
import ShenWork.Paper2.IntervalSharpSpectralHolderEmbedding
import ShenWork.Paper2.IntervalSharpSemigroupFrontier
import ShenWork.Paper2.IntervalPicardIterateRestart

/-!
# Sharp `q = 2` semigroup data on the unit interval

The old `intervalDomainSemigroupEstimateData` uses the same physical `L^q`
seminorm for every fractional exponent.  This file supplies a second,
non-degenerate data value.  At `q = 2` its scalar and fractional fields are
the Neumann cosine coefficient norm and the genuine shift-one spectral graph
norm.  Its embedding field is the weighted coefficient norm that controls the
sharp Hölder embedding.  Away from `q = 2` the fields fall back to the old
physical norms; no estimate for those fallback branches is asserted here.

The point-function outputs are cosine-coordinate realizations of the shifted
heat and divergence multipliers.  This is deliberate: one common coefficient
carrier lets the single `fractionalNorm` field measure both outputs.  The
physical sine realization of the divergence multiplier is recorded separately
below through the fresh Parseval theorem.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace ShenWork.Paper2.IntervalDomainSharpSemigroupEstimateData

open ShenWork.IntervalDomain
open ShenWork.HeatKernelGradientEstimates
open ShenWork.IntervalNeumannFullKernel
open ShenWork.CosineSpectrum
open ShenWork.PDE.FractionalPower
open ShenWork.PDE.AnalyticSemigroupGen
open ShenWork.PDE.ResolventEstimate
open ShenWork.Paper2.IntervalDomainLemma21
open ShenWork.Paper2.IntervalSharpSpectralCalculus
open ShenWork.Paper2.IntervalSharpSpectralHolderEmbedding
open ShenWork.Paper2.IntervalSharpSpectralPhysicalFractionalDivergenceL2
open ShenWork.Paper2.IntervalSharpSpectralPhysicalL2

/-- Real Neumann cosine coefficients of an interval point-function. -/
def intervalDomainSharpRealCoeff
    (u : intervalDomain.Point → ℝ) (n : ℕ) : ℝ :=
  cosineCoeffs (intervalDomainLift u) n

/-- The same coefficients in the complex scalar field used by the sharp
spectral calculus. -/
def intervalDomainSharpCoeff
    (u : intervalDomain.Point → ℝ) (n : ℕ) : ℂ :=
  intervalDomainSharpRealCoeff u n

/-- Honest `L²` coefficient-domain predicate for a point-function. -/
def IntervalDomainSharpCoeffL2 (u : intervalDomain.Point → ℝ) : Prop :=
  Summable fun n : ℕ => ‖intervalDomainSharpCoeff u n‖ ^ 2

/-- Honest shift-one fractional-domain predicate. -/
def IntervalDomainSharpFractionalMem
    (sigma : ℝ) (u : intervalDomain.Point → ℝ) : Prop :=
  Summable fun n : ℕ =>
    ‖shiftedSpectralFractionalCoeff 1 sigma
      (intervalDomainSharpCoeff u) n‖ ^ 2

/-- Ambient real cosine-series value for a real coefficient sequence. -/
def intervalDomainCosineCarrierValue (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, c n * cosineMode n x

/-- Real cosine-series carrier for a real coefficient sequence. -/
def intervalDomainCosineCarrier (c : ℕ → ℝ) : intervalDomain.Point → ℝ :=
  fun x => intervalDomainCosineCarrierValue c x.1

/-- Shifted heat coefficient in the real cosine carrier. -/
def intervalDomainSharpHeatCoeff
    (omega t : ℝ) (u : intervalDomain.Point → ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(shiftedNeumannEigenvalue omega n * t)) *
    intervalDomainSharpRealCoeff u n

/-- Divergence multiplier in the common real cosine carrier.  Its physical
counterpart is the sine series from
`intervalShiftOneFractionalFullHeatGradientValue`. -/
def intervalDomainSharpDivergenceCoeff
    (omega t : ℝ) (u : intervalDomain.Point → ℝ) (n : ℕ) : ℝ :=
  intervalShiftOneFractionalDivergenceAmp omega 0 t
    (intervalDomainSharpRealCoeff u) n

/-- Shifted Neumann heat flow in the common cosine-coordinate carrier. -/
def intervalDomainSharpHeatSemigroup
    (omega t : ℝ) (u : intervalDomain.Point → ℝ) :
    intervalDomain.Point → ℝ :=
  intervalDomainCosineCarrier (intervalDomainSharpHeatCoeff omega t u)

/-- Shifted divergence multiplier in the common cosine-coordinate carrier. -/
def intervalDomainSharpDivergenceSemigroup
    (omega t : ℝ) (u : intervalDomain.Point → ℝ) :
    intervalDomain.Point → ℝ :=
  intervalDomainCosineCarrier (intervalDomainSharpDivergenceCoeff omega t u)

/-- The genuine shift-one spectral graph norm of an interval point-function. -/
def intervalDomainShiftOneFractionalNorm
    (sigma : ℝ) (u : intervalDomain.Point → ℝ) : ℝ :=
  shiftedSpectralFractionalNorm 1 sigma (intervalDomainSharpCoeff u)

/-- The spectral Hölder coefficient norm controlled by the sharp embedding. -/
def intervalDomainSpectralHolderNorm
    (theta : ℝ) (u : intervalDomain.Point → ℝ) : ℝ :=
  ∑' n : ℕ, holderCoeffNorm theta (intervalDomainSharpCoeff u) n

/-- Non-degenerate interval semigroup data.  The sharp branch is selected at
`q = 2`; other exponents retain the old physical seminorm fields and are left
as the precise full-`Lᵖ` multiplier frontier. -/
def intervalDomainSharpSemigroupEstimateData (omega : ℝ) :
    SemigroupEstimateData intervalDomain where
  lpNorm := fun q u =>
    if q = 2 then coeffL2Norm (intervalDomainSharpCoeff u)
    else intervalDomainLpNorm q u
  vectorLpNorm := fun q u =>
    if q = 2 then coeffL2Norm (intervalDomainSharpCoeff u)
    else intervalDomainLpNorm q u
  fractionalNorm := fun sigma q u =>
    if q = 2 then intervalDomainShiftOneFractionalNorm sigma u
    else intervalDomainLpNorm q u
  semigroup := intervalDomainSharpHeatSemigroup omega
  divergenceSemigroup := intervalDomainSharpDivergenceSemigroup omega
  embeddingNorm := fun theta r _sigma u =>
    if r = 2 then intervalDomainSpectralHolderNorm theta u
    else intervalDomainLpNorm r u

@[simp] theorem intervalDomainSharpSemigroupEstimateData_lpNorm_two
    (omega : ℝ) (u : intervalDomain.Point → ℝ) :
    (intervalDomainSharpSemigroupEstimateData omega).lpNorm 2 u =
      coeffL2Norm (intervalDomainSharpCoeff u) := by
  simp [intervalDomainSharpSemigroupEstimateData]

@[simp] theorem intervalDomainSharpSemigroupEstimateData_vectorLpNorm_two
    (omega : ℝ) (u : intervalDomain.Point → ℝ) :
    (intervalDomainSharpSemigroupEstimateData omega).vectorLpNorm 2 u =
      coeffL2Norm (intervalDomainSharpCoeff u) := by
  simp [intervalDomainSharpSemigroupEstimateData]

@[simp] theorem intervalDomainSharpSemigroupEstimateData_fractionalNorm_two
    (omega sigma : ℝ) (u : intervalDomain.Point → ℝ) :
    (intervalDomainSharpSemigroupEstimateData omega).fractionalNorm sigma 2 u =
      shiftedSpectralFractionalNorm 1 sigma
        (intervalDomainSharpCoeff u) := by
  simp [intervalDomainSharpSemigroupEstimateData,
    intervalDomainShiftOneFractionalNorm]

@[simp] theorem intervalDomainSharpSemigroupEstimateData_embeddingNorm_two
    (omega theta sigma : ℝ) (u : intervalDomain.Point → ℝ) :
    (intervalDomainSharpSemigroupEstimateData omega).embeddingNorm
        theta 2 sigma u =
      ∑' n : ℕ, holderCoeffNorm theta (intervalDomainSharpCoeff u) n := by
  simp [intervalDomainSharpSemigroupEstimateData,
    intervalDomainSpectralHolderNorm]

/-! ## Coefficient extraction for the two carrier outputs -/

/-- Cosine coefficients only see the open physical interval. -/
theorem cosineCoeffs_congr_on_unitIntervalInterior
    {f g : ℝ → ℝ}
    (hfg : ∀ x ∈ Set.Ioo (0 : ℝ) 1, f x = g x) (k : ℕ) :
    cosineCoeffs f k = cosineCoeffs g k := by
  rw [ShenWork.IntervalMildPicardRegularity.cosineCoeffs_eq_factor_mul_integral,
    ShenWork.IntervalMildPicardRegularity.cosineCoeffs_eq_factor_mul_integral]
  congr 1
  apply intervalIntegral.integral_congr_ae
  rw [MeasureTheory.ae_iff]
  apply MeasureTheory.measure_mono_null
      (t := ({(1 : ℝ)} : Set ℝ)) ?_ (by simp)
  intro x hx
  simp only [Set.mem_setOf_eq, not_forall] at hx
  obtain ⟨hmem, hfail⟩ := hx
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.mem_Ioc] at hmem
  simp only [Set.mem_singleton_iff]
  by_contra hx1
  exact hfail (by rw [hfg x ⟨hmem.1, lt_of_le_of_ne hmem.2 hx1⟩])

/-- The interval carrier has exactly its prescribed real cosine
coefficients whenever they are absolutely summable. -/
theorem intervalDomainSharpRealCoeff_cosineCarrier
    {c : ℕ → ℝ} (hc : Summable fun n : ℕ => |c n|) (k : ℕ) :
    intervalDomainSharpRealCoeff (intervalDomainCosineCarrier c) k = c k := by
  unfold intervalDomainSharpRealCoeff
  rw [cosineCoeffs_congr_on_unitIntervalInterior
    (g := fun x : ℝ => ∑' n : ℕ, c n * cosineMode n x) (k := k)]
  · exact
      ShenWork.IntervalPicardIterateRestart.cosineCoeffs_of_l1_cosineSeries
        hc k
  · intro x hx
    simp [intervalDomainLift, intervalDomainCosineCarrier,
      intervalDomainCosineCarrierValue, hx.1.le, hx.2.le]

/-- Absolute coefficient summability makes the ambient carrier continuous. -/
theorem intervalDomainCosineCarrierValue_continuous
    {c : ℕ → ℝ} (hc : Summable fun n : ℕ => |c n|) :
    Continuous (intervalDomainCosineCarrierValue c) := by
  unfold intervalDomainCosineCarrierValue
  exact continuous_tsum
    (fun n => by
      change Continuous fun x : ℝ =>
        c n * Real.cos ((n : ℝ) * Real.pi * x)
      fun_prop)
    hc
    (fun n x => by
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul_of_nonneg_left
        (Real.abs_cos_le_one ((n : ℝ) * Real.pi * x))
        (abs_nonneg (c n))).trans_eq (mul_one _))

/-- Subtractivity of cosine coefficients under the minimal interval
integrability hypotheses. -/
theorem cosineCoeffs_sub_of_intervalIntegrable
    {f g : ℝ → ℝ} (k : ℕ)
    (hf : IntervalIntegrable f volume 0 1)
    (hg : IntervalIntegrable g volume 0 1) :
    cosineCoeffs (fun x => f x - g x) k =
      cosineCoeffs f k - cosineCoeffs g k := by
  rw [ShenWork.IntervalMildPicardRegularity.cosineCoeffs_eq_factor_mul_integral,
    ShenWork.IntervalMildPicardRegularity.cosineCoeffs_eq_factor_mul_integral,
    ShenWork.IntervalMildPicardRegularity.cosineCoeffs_eq_factor_mul_integral]
  let w : ℝ → ℝ := fun x => Real.cos ((k : ℝ) * Real.pi * x)
  have hw : ContinuousOn w (Set.uIcc (0 : ℝ) 1) := by
    exact (Real.continuous_cos.comp (by fun_prop)).continuousOn
  have hfw : IntervalIntegrable (fun x => w x * f x) volume 0 1 :=
    hf.continuousOn_mul hw
  have hgw : IntervalIntegrable (fun x => w x * g x) volume 0 1 :=
    hg.continuousOn_mul hw
  have hsplit :
      (∫ x in (0 : ℝ)..1, w x * (f x - g x)) =
        (∫ x in (0 : ℝ)..1, w x * f x) -
          ∫ x in (0 : ℝ)..1, w x * g x := by
    rw [← intervalIntegral.integral_sub hfw hgw]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    ring
  rw [hsplit]
  ring

/-- A physical `MemLp 2` input is interval-integrable. -/
theorem intervalDomainLift_intervalIntegrable_of_memLp_two
    {u : intervalDomain.Point → ℝ}
    (hu : MemLp (intervalDomainLift u) 2 (intervalMeasure 1)) :
    IntervalIntegrable (intervalDomainLift u) volume 0 1 := by
  have huL1 : Integrable (intervalDomainLift u) (intervalMeasure 1) :=
    memLp_one_iff_integrable.mp (hu.mono_exponent (by norm_num))
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by norm_num : (0 : ℝ) ≤ 1)]
  have huIcc : IntegrableOn (intervalDomainLift u)
      (Set.Icc (0 : ℝ) 1) volume := huL1
  exact huIcc.mono_set Set.Ioc_subset_Icc_self

/-- `MemLp 2` supplies the coefficient-domain hypothesis used below. -/
theorem intervalDomainSharpCoeffL2_of_memLp
    {u : intervalDomain.Point → ℝ}
    (hu : MemLp (intervalDomainLift u) 2 (intervalMeasure 1)) :
    IntervalDomainSharpCoeffL2 u := by
  rcases ShenWork.IntervalNeumannHeatGradientL2.cosineCoeffs_l2_of_memLp hu with
    ⟨hsum, _hbound⟩
  simpa [IntervalDomainSharpCoeffL2, intervalDomainSharpCoeff,
    intervalDomainSharpRealCoeff, Complex.norm_real, Real.norm_eq_abs,
    sq_abs] using hsum

/-- Positive shifted heat damping makes the carrier coefficients absolutely
summable from `L²` coefficient data. -/
theorem intervalDomainSharpHeatCoeff_abs_summable
    {omega t : ℝ} (_homega : 0 < omega) (ht : 0 < t)
    {u : intervalDomain.Point → ℝ} (hu : IntervalDomainSharpCoeffL2 u) :
    Summable fun n : ℕ => |intervalDomainSharpHeatCoeff omega t u n| := by
  have htrace :=
    unitIntervalCosineHeatTrace_single_exp_summable (t := 2 * t) (by linarith)
  have hmultSq : Summable fun n : ℕ =>
      (Real.exp (-(shiftedNeumannEigenvalue omega n * t))) ^ 2 := by
    refine (htrace.mul_left (Real.exp (-(2 * omega * t)))).congr ?_
    intro n
    calc
      Real.exp (-(2 * omega * t)) *
          Real.exp (-(2 * t) * unitIntervalCosineEigenvalue n) =
        Real.exp (-(2 * omega * t) +
          -(2 * t) * unitIntervalCosineEigenvalue n) := by
            rw [Real.exp_add]
      _ = Real.exp
          (-((shiftedNeumannEigenvalue omega n) * t) +
            -((shiftedNeumannEigenvalue omega n) * t)) := by
        congr 1
        unfold shiftedNeumannEigenvalue unitIntervalCosineEigenvalue
          ShenWork.Paper3.unitIntervalNeumannSpectrum
        ring
      _ = Real.exp (-(shiftedNeumannEigenvalue omega n * t)) *
          Real.exp (-(shiftedNeumannEigenvalue omega n * t)) := by
        rw [Real.exp_add]
      _ = (Real.exp (-(shiftedNeumannEigenvalue omega n * t))) ^ 2 := by
        ring
  have huReal : Summable fun n : ℕ =>
      (intervalDomainSharpRealCoeff u n) ^ 2 := by
    simpa [IntervalDomainSharpCoeffL2, intervalDomainSharpCoeff,
      Complex.norm_real, Real.norm_eq_abs, sq_abs] using hu
  have hproduct := real_summable_abs_mul_of_summable_sq hmultSq huReal
  exact hproduct.congr fun n => by
    simp only [intervalDomainSharpHeatCoeff]

/-- Exact complex coefficient identity for the heat carrier. -/
theorem intervalDomainSharpCoeff_heatSemigroup
    {omega t : ℝ} (homega : 0 < omega) (ht : 0 < t)
    {u : intervalDomain.Point → ℝ} (hu : IntervalDomainSharpCoeffL2 u) :
    intervalDomainSharpCoeff
        (intervalDomainSharpHeatSemigroup omega t u) =
      shiftedNeumannHeatCoeff omega t (intervalDomainSharpCoeff u) := by
  funext n
  have hreal := intervalDomainSharpRealCoeff_cosineCarrier
    (intervalDomainSharpHeatCoeff_abs_summable homega ht hu) n
  change
    ((intervalDomainSharpRealCoeff
      (intervalDomainCosineCarrier
        (intervalDomainSharpHeatCoeff omega t u)) n : ℝ) : ℂ) = _
  rw [hreal]
  simp [intervalDomainSharpHeatCoeff, shiftedNeumannHeatCoeff,
    intervalDomainSharpCoeff, intervalDomainSharpRealCoeff]

/-- Exact coefficient identity for the physical pointwise heat difference.
Unlike the raw statement-layer interface, this bridge explicitly asks that
the input be in physical `L²`. -/
theorem intervalDomainSharpCoeff_heatSemigroup_sub
    {omega t : ℝ} (homega : 0 < omega) (ht : 0 < t)
    {u : intervalDomain.Point → ℝ}
    (huMem : MemLp (intervalDomainLift u) 2 (intervalMeasure 1)) :
    intervalDomainSharpCoeff
        (fun x => intervalDomainSharpHeatSemigroup omega t u x - u x) =
      shiftedNeumannHeatDifferenceCoeff omega t
        (intervalDomainSharpCoeff u) := by
  have huCoeff : IntervalDomainSharpCoeffL2 u :=
    intervalDomainSharpCoeffL2_of_memLp huMem
  have hsum := intervalDomainSharpHeatCoeff_abs_summable
    homega ht huCoeff
  let G : ℝ → ℝ :=
    intervalDomainCosineCarrierValue (intervalDomainSharpHeatCoeff omega t u)
  have hGcont : Continuous G := by
    exact intervalDomainCosineCarrierValue_continuous hsum
  have hGint : IntervalIntegrable G volume 0 1 :=
    hGcont.intervalIntegrable 0 1
  have huInt : IntervalIntegrable (intervalDomainLift u) volume 0 1 :=
    intervalDomainLift_intervalIntegrable_of_memLp_two huMem
  funext n
  have hcongr :
      cosineCoeffs
          (intervalDomainLift
            (fun x => intervalDomainSharpHeatSemigroup omega t u x - u x)) n =
        cosineCoeffs (fun x => G x - intervalDomainLift u x) n := by
    apply cosineCoeffs_congr_on_unitIntervalInterior
    intro x hx
    simp [intervalDomainLift, intervalDomainSharpHeatSemigroup,
      intervalDomainCosineCarrier, G, hx.1.le, hx.2.le]
  have hGcoeff :
      cosineCoeffs G n = intervalDomainSharpHeatCoeff omega t u n := by
    exact
      ShenWork.IntervalPicardIterateRestart.cosineCoeffs_of_l1_cosineSeries
        hsum n
  change
    ((cosineCoeffs
      (intervalDomainLift
        (fun x => intervalDomainSharpHeatSemigroup omega t u x - u x)) n : ℝ) : ℂ) = _
  rw [hcongr, cosineCoeffs_sub_of_intervalIntegrable n hGint huInt, hGcoeff]
  simp [intervalDomainSharpHeatCoeff, shiftedNeumannHeatDifferenceCoeff,
    shiftedNeumannHeatCoeff, intervalDomainSharpCoeff,
    intervalDomainSharpRealCoeff]

/-- Positive shifted divergence damping makes its carrier coefficients
absolutely summable from `L²` coefficient data. -/
theorem intervalDomainSharpDivergenceCoeff_abs_summable
    {omega t : ℝ} (homega : 0 < omega) (ht : 0 < t)
    {u : intervalDomain.Point → ℝ} (hu : IntervalDomainSharpCoeffL2 u) :
    Summable fun n : ℕ =>
      |intervalDomainSharpDivergenceCoeff omega t u n| := by
  have huReal : Summable fun n : ℕ =>
      (intervalDomainSharpRealCoeff u n) ^ 2 := by
    simpa [IntervalDomainSharpCoeffL2, intervalDomainSharpCoeff,
      Complex.norm_real, Real.norm_eq_abs, sq_abs] using hu
  simpa [intervalDomainSharpDivergenceCoeff, Real.norm_eq_abs] using
    intervalShiftOneFractionalDivergenceAmp_abs_summable
      homega (show (0 : ℝ) ≤ 0 by norm_num) ht huReal

/-- Exact complex coefficient identity for the divergence carrier. -/
theorem intervalDomainSharpCoeff_divergenceSemigroup
    {omega t : ℝ} (homega : 0 < omega) (ht : 0 < t)
    {u : intervalDomain.Point → ℝ} (hu : IntervalDomainSharpCoeffL2 u) :
    intervalDomainSharpCoeff
        (intervalDomainSharpDivergenceSemigroup omega t u) =
      shiftedNeumannDivergenceHeatCoeff omega t
        (intervalDomainSharpCoeff u) := by
  funext n
  have hreal := intervalDomainSharpRealCoeff_cosineCarrier
    (intervalDomainSharpDivergenceCoeff_abs_summable homega ht hu) n
  change
    ((intervalDomainSharpRealCoeff
      (intervalDomainCosineCarrier
        (intervalDomainSharpDivergenceCoeff omega t u)) n : ℝ) : ℂ) = _
  rw [hreal]
  simpa [intervalDomainSharpDivergenceCoeff,
    intervalDomainSharpCoeff, shiftedSpectralFractionalCoeff] using
    intervalShiftOneFractionalDivergenceAmp_ofReal
      omega 0 t (intervalDomainSharpRealCoeff u) n

/-- On physical `L²` inputs, the heat carrier is the genuine shifted full
Neumann kernel on every interior point. -/
theorem intervalDomainSharpHeatSemigroup_eq_shiftedFull
    {omega t : ℝ} (ht : 0 < t)
    {u : intervalDomain.Point → ℝ}
    (hu : MemLp (intervalDomainLift u) 2 (intervalMeasure 1))
    (x : intervalDomain.Point) (hx : x.1 ∈ Set.Ioo (0 : ℝ) 1) :
    intervalDomainSharpHeatSemigroup omega t u x =
      ShenWork.Paper2.IntervalSharpSemigroupFrontier.intervalShiftedFullSemigroupOperator
        omega t (intervalDomainLift u) x.1 := by
  have huInt : Integrable (intervalDomainLift u) (intervalMeasure 1) :=
    memLp_one_iff_integrable.mp (hu.mono_exponent (by norm_num))
  have hop :=
    ShenWork.IntervalNeumannHeatGradientL2.operator_eq_cosineModel_of_integrable
      ht huInt hx
  unfold intervalDomainSharpHeatSemigroup intervalDomainCosineCarrier
    intervalDomainCosineCarrierValue intervalDomainSharpHeatCoeff
    ShenWork.Paper2.IntervalSharpSemigroupFrontier.intervalShiftedFullSemigroupOperator
  rw [hop,
    ShenWork.IntervalPicardIterateRestart.heatValue_eq_cosineSeries]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold shiftedNeumannEigenvalue unitIntervalCosineEigenvalue
  simp only [ShenWork.Paper3.unitIntervalNeumannSpectrum]
  rw [show
      -(((n : ℝ) ^ 2 * Real.pi ^ 2 + omega) * t) =
        -(omega * t) + -(t * ((n : ℝ) * Real.pi) ^ 2) by ring,
    Real.exp_add]
  unfold intervalDomainSharpRealCoeff
  ring_nf

/-! ## Sharp `q = 2` Lemma 2.1--2.4 fields -/

/-- Sharp `q = 2` form of both branches of Lemma 2.1 for the new data.
The difference branch carries exactly the genuine fractional-domain
hypothesis absent from the raw statement-layer interface. -/
theorem Lemma_2_1_intervalDomain_sharp
    (p : CM2Params) :
    ( (∀ sigma delta : ℝ, 0 ≤ sigma → 0 < delta → delta < p.μ →
        ∃ C > 0, ∀ t > 0, ∀ u : intervalDomain.Point → ℝ,
          IntervalDomainSharpCoeffL2 u →
          (intervalDomainSharpSemigroupEstimateData p.μ).fractionalNorm
              sigma 2
              ((intervalDomainSharpSemigroupEstimateData p.μ).semigroup t u) ≤
            C * t ^ (-sigma) * Real.exp (-(delta * t)) *
              (intervalDomainSharpSemigroupEstimateData p.μ).lpNorm 2 u) ) ∧
      (∀ sigma : ℝ, 0 < sigma → sigma ≤ 1 →
        ∃ C > 0, ∀ t > 0, ∀ u : intervalDomain.Point → ℝ,
          MemLp (intervalDomainLift u) 2 (intervalMeasure 1) →
          IntervalDomainSharpFractionalMem sigma u →
          (intervalDomainSharpSemigroupEstimateData p.μ).lpNorm 2
              (fun x =>
                (intervalDomainSharpSemigroupEstimateData p.μ).semigroup
                  t u x - u x) ≤
            C * t ^ sigma *
              (intervalDomainSharpSemigroupEstimateData p.μ).fractionalNorm
                sigma 2 u) := by
  constructor
  · intro sigma delta hsigma hdelta hdelta_mu
    rcases shiftOneSpectralFractionalNorm_heat_decay_exists
        p.hμ hdelta hdelta_mu hsigma with ⟨C, hC, hbase⟩
    refine ⟨C, hC, ?_⟩
    intro t ht u hu
    rw [intervalDomainSharpSemigroupEstimateData_fractionalNorm_two,
      intervalDomainSharpSemigroupEstimateData_lpNorm_two]
    change
      shiftedSpectralFractionalNorm 1 sigma
          (intervalDomainSharpCoeff
            (intervalDomainSharpHeatSemigroup p.μ t u)) ≤
        C * t ^ (-sigma) * Real.exp (-(delta * t)) *
          coeffL2Norm (intervalDomainSharpCoeff u)
    rw [intervalDomainSharpCoeff_heatSemigroup p.hμ ht hu]
    exact hbase t ht (intervalDomainSharpCoeff u) hu
  · intro sigma hsigma hsigma_one
    rcases shiftedNeumannHeatDifferenceCoeff_shiftOneNorm_exists
        p.hμ hsigma hsigma_one with ⟨C, hC, hbase⟩
    refine ⟨C, hC, ?_⟩
    intro t ht u huMem hfrac
    rw [intervalDomainSharpSemigroupEstimateData_lpNorm_two,
      intervalDomainSharpSemigroupEstimateData_fractionalNorm_two]
    change
      coeffL2Norm
          (intervalDomainSharpCoeff
            (fun x => intervalDomainSharpHeatSemigroup p.μ t u x - u x)) ≤
        C * t ^ sigma *
          shiftedSpectralFractionalNorm 1 sigma
            (intervalDomainSharpCoeff u)
    rw [intervalDomainSharpCoeff_heatSemigroup_sub p.hμ ht huMem]
    exact hbase t ht (intervalDomainSharpCoeff u) hfrac

/-- Sharp `q = 2` Hölder branch of Lemma 2.2.  It specializes to `C⁰`
at `theta = 0` (`sigma > 1/4`) and to the Lipschitz/`C¹` threshold at
`theta = 1` (`sigma > 3/4`). -/
theorem Lemma_2_2_intervalDomain_sharp
    (omega : ℝ) :
    ∀ sigma theta : ℝ, 0 ≤ theta → theta ≤ 1 →
      theta < 2 * sigma - intervalDomain.volume / 2 →
      ∃ C > 0, ∀ u : intervalDomain.Point → ℝ,
        IntervalDomainSharpFractionalMem sigma u →
        (intervalDomainSharpSemigroupEstimateData omega).embeddingNorm
            theta 2 sigma u ≤
          C * (intervalDomainSharpSemigroupEstimateData omega).fractionalNorm
            sigma 2 u := by
  intro sigma theta htheta htheta_one hgap
  have hvolume : intervalDomain.volume = 1 := rfl
  have hgap' : theta < 2 * sigma - 1 / 2 := by
    simpa [hvolume] using hgap
  have htrace := holderReciprocalFractionalPowerWeight_summable htheta hgap'
  let R : ℝ :=
    (∑' n : ℕ, holderReciprocalFractionalPowerWeight sigma theta n) ^
      (1 / (2 : ℝ))
  let C : ℝ := max 1 R
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left 1 R)
  refine ⟨C, hC, ?_⟩
  intro u hfrac
  have henergy : Summable fun n : ℕ =>
      fractionalPowerEnergyTerm 1 sigma (intervalDomainSharpCoeff u) n :=
    (fractionalPowerSpace_iff_shiftedCoeff_summable
      sigma (intervalDomainSharpCoeff u)).2 hfrac
  have hholder := summable_and_tsum_holderCoeffNorm_le
    (intervalDomainSharpCoeff u) henergy htrace
  rw [intervalDomainSharpSemigroupEstimateData_embeddingNorm_two,
    intervalDomainSharpSemigroupEstimateData_fractionalNorm_two]
  have hroot :
      (∑' n : ℕ,
        fractionalPowerEnergyTerm 1 sigma (intervalDomainSharpCoeff u) n) ^
          (1 / (2 : ℝ)) =
        shiftedSpectralFractionalNorm 1 sigma
          (intervalDomainSharpCoeff u) := by
    rw [← Real.sqrt_eq_rpow,
      ← shiftedSpectralFractionalEnergy_one_eq_fractionalPowerEnergy]
    rfl
  rw [hroot] at hholder
  have hRle : R ≤ C := le_max_right 1 R
  have hfrac_nonneg :
      0 ≤ shiftedSpectralFractionalNorm 1 sigma
        (intervalDomainSharpCoeff u) := shiftedSpectralFractionalNorm_nonneg _ _ _
  calc
    (∑' n : ℕ, holderCoeffNorm theta (intervalDomainSharpCoeff u) n) ≤
        shiftedSpectralFractionalNorm 1 sigma
          (intervalDomainSharpCoeff u) * R := by
      simpa [R] using hholder.2
    _ ≤ shiftedSpectralFractionalNorm 1 sigma
          (intervalDomainSharpCoeff u) * C :=
      mul_le_mul_of_nonneg_left hRle hfrac_nonneg
    _ = C * shiftedSpectralFractionalNorm 1 sigma
          (intervalDomainSharpCoeff u) := by ring

/-- The sharp `C⁰` endpoint of the `q = 2` embedding field. -/
theorem Lemma_2_2_intervalDomain_sharp_C0
    (omega sigma : ℝ) (hsigma : 1 / 4 < sigma) :
    ∃ C > 0, ∀ u : intervalDomain.Point → ℝ,
      IntervalDomainSharpFractionalMem sigma u →
      (intervalDomainSharpSemigroupEstimateData omega).embeddingNorm
          0 2 sigma u ≤
        C * (intervalDomainSharpSemigroupEstimateData omega).fractionalNorm
          sigma 2 u := by
  apply Lemma_2_2_intervalDomain_sharp omega sigma 0 (by norm_num) (by norm_num)
  change 0 < 2 * sigma - 1 / 2
  linarith

/-- The sharp Lipschitz/`C¹` endpoint of the `q = 2` embedding field. -/
theorem Lemma_2_2_intervalDomain_sharp_C1
    (omega sigma : ℝ) (hsigma : 3 / 4 < sigma) :
    ∃ C > 0, ∀ u : intervalDomain.Point → ℝ,
      IntervalDomainSharpFractionalMem sigma u →
      (intervalDomainSharpSemigroupEstimateData omega).embeddingNorm
          1 2 sigma u ≤
        C * (intervalDomainSharpSemigroupEstimateData omega).fractionalNorm
          sigma 2 u := by
  apply Lemma_2_2_intervalDomain_sharp omega sigma 1 (by norm_num) (by norm_num)
  change 1 < 2 * sigma - 1 / 2
  linarith

/-- Sharp `q = 2` Lemma 2.3 field. -/
theorem Lemma_2_3_intervalDomain_sharp
    (p : CM2Params) :
    ∃ C > 0, ∀ t > 0, ∀ phi : intervalDomain.Point → ℝ,
      IntervalDomainSharpCoeffL2 phi →
      (intervalDomainSharpSemigroupEstimateData p.μ).lpNorm 2
          ((intervalDomainSharpSemigroupEstimateData p.μ).divergenceSemigroup
            t phi) ≤
        C * (1 + t ^ (-(1 / 2 : ℝ))) * Real.exp (-(p.μ * t)) *
          (intervalDomainSharpSemigroupEstimateData p.μ).vectorLpNorm 2 phi := by
  rcases shiftedNeumannDivergenceHeatCoeff_l2_decay_exists p.μ with
    ⟨C, hC, hbase⟩
  refine ⟨C, hC, ?_⟩
  intro t ht phi hphi
  rw [intervalDomainSharpSemigroupEstimateData_lpNorm_two,
    intervalDomainSharpSemigroupEstimateData_vectorLpNorm_two]
  change
    coeffL2Norm
        (intervalDomainSharpCoeff
          (intervalDomainSharpDivergenceSemigroup p.μ t phi)) ≤
      C * (1 + t ^ (-(1 / 2 : ℝ))) * Real.exp (-(p.μ * t)) *
        coeffL2Norm (intervalDomainSharpCoeff phi)
  rw [intervalDomainSharpCoeff_divergenceSemigroup p.hμ ht hphi]
  exact hbase t ht (intervalDomainSharpCoeff phi) hphi

/-- Sharp `q = 2` Lemma 2.4 field. -/
theorem Lemma_2_4_intervalDomain_sharp
    (p : CM2Params) :
    ∀ sigma : ℝ, 0 < sigma →
      ∃ C > 0, ∀ t > 0, ∀ phi : intervalDomain.Point → ℝ,
        IntervalDomainSharpCoeffL2 phi →
        (intervalDomainSharpSemigroupEstimateData p.μ).fractionalNorm sigma 2
            ((intervalDomainSharpSemigroupEstimateData p.μ).divergenceSemigroup
              t phi) ≤
          C * t ^ (-sigma) * (1 + t ^ (-(1 / 2 : ℝ))) *
            Real.exp (-((p.μ / 2) * t)) *
              (intervalDomainSharpSemigroupEstimateData p.μ).vectorLpNorm 2 phi := by
  intro sigma hsigma
  rcases shiftOneFractionalDivergenceHeatCoeff_l2_decay_exists
      p.hμ hsigma with ⟨C, hC, hbase⟩
  refine ⟨C, hC, ?_⟩
  intro t ht phi hphi
  rw [intervalDomainSharpSemigroupEstimateData_fractionalNorm_two,
    intervalDomainSharpSemigroupEstimateData_vectorLpNorm_two]
  change
    shiftedSpectralFractionalNorm 1 sigma
        (intervalDomainSharpCoeff
          (intervalDomainSharpDivergenceSemigroup p.μ t phi)) ≤
      C * t ^ (-sigma) * (1 + t ^ (-(1 / 2 : ℝ))) *
        Real.exp (-((p.μ / 2) * t)) *
          coeffL2Norm (intervalDomainSharpCoeff phi)
  rw [intervalDomainSharpCoeff_divergenceSemigroup p.hμ ht hphi]
  exact hbase t ht (intervalDomainSharpCoeff phi) hphi

#print axioms intervalDomainSharpCoeffL2_of_memLp
#print axioms intervalDomainSharpCoeff_heatSemigroup
#print axioms intervalDomainSharpCoeff_divergenceSemigroup
#print axioms intervalDomainSharpHeatSemigroup_eq_shiftedFull
#print axioms Lemma_2_1_intervalDomain_sharp
#print axioms Lemma_2_2_intervalDomain_sharp
#print axioms Lemma_2_2_intervalDomain_sharp_C0
#print axioms Lemma_2_2_intervalDomain_sharp_C1
#print axioms Lemma_2_3_intervalDomain_sharp
#print axioms Lemma_2_4_intervalDomain_sharp

end ShenWork.Paper2.IntervalDomainSharpSemigroupEstimateData
