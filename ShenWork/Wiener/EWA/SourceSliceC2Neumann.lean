/-
  ShenWork/Wiener/EWA/SourceSliceC2Neumann.lean

  **χ₀<0 — discharging the C²-Neumann source-slice regularity carried by
  `realSlice_hlogInv_of_C2Neumann` / `realSlice_hchemInv_of_C2Neumann`
  (SourceInversionDischarge.lean) from the ALREADY-BANKED regularity of the
  realized slice `u = realSlice u_star`.**

  `realSlice_hlogInv_of_C2Neumann` / `realSlice_hchemInv_of_C2Neumann` carry, per
  interior time `t`, the C²-Neumann data of the source slice:
    * continuity of the slice on the subtype,
    * `ContDiffOn ℝ 2 (intervalDomainLift s_t) (Icc 0 1)`,
    * one-sided endpoint derivative limits `→ 0` (htend0/htend1),
    * homogeneous Neumann `deriv (lift s_t) 0 = 0`, `deriv (lift s_t) 1 = 0`.

  This file discharges that data for the LOGISTIC source slice
  `intervalLogisticSource p (u t) x = u t x · (a − b · (u t x)^α)`, fully from the
  banked u-side regularity (the eigenvalue-ℓ¹ summability `hsumE`, the slab
  `realizes` `hrealizes`, and the heat-floor positivity atoms `hδρ/hheat/hu_ball`),
  via the committed logistic-source machinery in `IntervalMildPicardRegularity`:

    * The u-slice cosine series `cs := ∑ₙ fullSourceCoeff·cos` is GLOBALLY `C²`
      (`cosineCoeffSeries_contDiff_two hsumE`), positive on `[0,1]` (heat floor +
      `hrealizes` agreement), and Neumann (`cosineCoeffSeries_deriv_at_{zero,one}`).
    * `logisticSourceFun p.a p.b p.α cs` is then `C²`-Neumann
      (`logisticSourceFun_contDiffOn_Icc`, `..._tendsto_deriv_{left,right}`,
      `..._deriv_zero_at_{zero,one}`).
    * On `[0,1]` the lift of the logistic source slice EQUALS
      `logisticSourceFun p.a p.b p.α cs` (slice defeq + `hrealizes`), transferring
      `hC2`/`htend0`/`htend1`.  The endpoint POINT-derivatives `hbc0`/`hbc1` of the
      ZERO-EXTENSION lift use the junk-value route
      `intervalDomainLift_deriv_{left,right}_endpoint_zero_of_ne`, hence carry the
      logistic-source endpoint nonvanishing `hlogNE0`/`hlogNE1` — the exact analogue
      of the `huNE0`/`huNE1` already carried by `realSlice_classicalRegularity`.

  The two assembled discharges are
    `realSlice_hlogInv_of_C2NeumannData` (log slice C²-Neumann, then `hlogInv`),
  feeding `realSlice_hlogInv_of_C2Neumann` directly.

  **CHEM source — precise regularity-budget residual (NOT discharged).**
  `intervalDomainChemotaxisDiv p u v x = ∂ₓ( lift u · ∂ₓ(lift v) / (1 + lift v)^β )`
  is ONE spatial derivative of an expression already containing `∂ₓ(lift v)`.  For
  this slice to be `ContDiffOn ℝ 2` on `[0,1]` the bracketed inner expression must be
  `ContDiffOn ℝ 3`, which forces `lift u ∈ C³` AND `∂ₓ(lift v) ∈ C³`, i.e.
  `lift v ∈ C⁴`.  The banked u/v regularity is only `C²` on both sides — the sole
  smoothness producer in this track is `cosineCoeffSeries_contDiff_two` (C²), and the
  banked resolver coefficient summability `resolverR_summability`
  (`SourceCoeffQuadraticDecay`) is `λ_k|v̂_k|`-summable = C² only, NOT `λ_k²|v̂_k|`
  (C⁴).  So the chem source genuinely needs `lift (realSlice u_star t) ∈ C³` and
  `lift (coupledChemicalConcentration p (realSlice u_star) t) ∈ C⁴`; neither is among
  the banked atoms.  This is the honest χ₀<0 chem-source residual, stated precisely in
  `realSlice_hchemInv_C2Neumann_residual` below (it merely re-exports
  `realSlice_hchemInv_of_C2Neumann`, since the C²-Neumann chem data cannot be produced
  from banked C² u/v).

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceInversionDischarge
import ShenWork.Wiener.EWA.SourceResolverSpectralDischarge
import ShenWork.Paper2.IntervalMildPicardRegularity

noncomputable section

namespace ShenWork.EWA

open Set Filter Topology
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDomain
  (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalDuhamelClosedC2
  (cosineCoeffSeries_contDiff_two cosineCoeffSeries_deriv_at_zero
   cosineCoeffSeries_deriv_at_one)
open ShenWork.IntervalCosineSliceRegularity
  (intervalDomainLift_deriv_left_endpoint_zero_of_ne
   intervalDomainLift_deriv_right_endpoint_zero_of_ne)
open ShenWork.IntervalMildPicardRegularity
  (logisticSourceFun logisticSourceFun_contDiffOn_Icc
   logisticSourceFun_tendsto_deriv_left logisticSourceFun_tendsto_deriv_right)

variable {T : ℝ}

/-! ### The u-slice cosine series and its banked global C²-Neumann-positive data. -/

/-- The globally-`C²` u-slice cosine series at interior time `t`. -/
private def uSliceSeries (p : CM2Params) (u_star : EWA T 1) (u₀cos : ℕ → ℝ)
    (t : ℝ) : ℝ → ℝ :=
  fun y => ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n y

/-- On `[0,1]` the logistic source slice lift equals `logisticSourceFun a b α` of the
u-slice cosine series.  Off `[0,1]` only the lift is forced to `0`. -/
private theorem logSourceLift_eqOn_Icc
    (p : CM2Params) (u_star : EWA T 1) (u₀cos : ℕ → ℝ) {t : ℝ}
    (hrealizes : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x
        = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x) :
    Set.EqOn (intervalDomainLift (intervalLogisticSource p (realSlice u_star t)))
      (logisticSourceFun p.a p.b p.α (uSliceSeries p u_star u₀cos t))
      (Set.Icc (0 : ℝ) 1) := by
  intro x hx
  have hlift : intervalDomainLift (intervalLogisticSource p (realSlice u_star t)) x
      = intervalLogisticSource p (realSlice u_star t) ⟨x, hx⟩ := by
    simp only [intervalDomainLift, dif_pos hx]
  have hu : realSlice u_star t ⟨x, hx⟩ = uSliceSeries p u_star u₀cos t x := by
    have h := hrealizes x hx
    rwa [intervalDomainLift, dif_pos hx] at h
  rw [hlift]
  simp only [intervalLogisticSource, logisticSourceFun, hu]

/-! ### Banked global C²-Neumann-positive data for `uSliceSeries`. -/

private theorem uSliceSeries_contDiff
    (p : CM2Params) (u_star : EWA T 1) (u₀cos : ℕ → ℝ) {t : ℝ}
    (hsumE : Summable (fun n => unitIntervalCosineEigenvalue n *
      |fullSourceCoeff p (realSlice u_star) u₀cos t n|)) :
    ContDiff ℝ 2 (uSliceSeries p u_star u₀cos t) :=
  cosineCoeffSeries_contDiff_two hsumE

private theorem uSliceSeries_pos_Icc
    (p : CM2Params) (u_star : EWA T 1) (u₀cos : ℕ → ℝ)
    {u₀E : WA 1} {δ ρ : ℝ} (hδρ : 0 < δ - ρ)
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ)
    (hu_ball : u_star ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hrealizes : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x
        = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < uSliceSeries p u_star u₀cos t x := by
  intro x hx
  have hpos := realSlice_pos hδρ hheat hu_ball ⟨ht.1.le, ht.2.le⟩ ⟨x, hx⟩
  have hval : uSliceSeries p u_star u₀cos t x = realSlice u_star t ⟨x, hx⟩ := by
    have h := hrealizes x hx
    rw [intervalDomainLift, dif_pos hx] at h
    exact h.symm
  rw [hval]; exact hpos

private theorem uSliceSeries_neumann0
    (p : CM2Params) (u_star : EWA T 1) (u₀cos : ℕ → ℝ) {t : ℝ}
    (hsumE : Summable (fun n => unitIntervalCosineEigenvalue n *
      |fullSourceCoeff p (realSlice u_star) u₀cos t n|)) :
    deriv (uSliceSeries p u_star u₀cos t) 0 = 0 :=
  cosineCoeffSeries_deriv_at_zero hsumE

private theorem uSliceSeries_neumann1
    (p : CM2Params) (u_star : EWA T 1) (u₀cos : ℕ → ℝ) {t : ℝ}
    (hsumE : Summable (fun n => unitIntervalCosineEigenvalue n *
      |fullSourceCoeff p (realSlice u_star) u₀cos t n|)) :
    deriv (uSliceSeries p u_star u₀cos t) 1 = 0 :=
  cosineCoeffSeries_deriv_at_one hsumE

/-! ### LOG source C²-Neumann data (per interior time), from banked u-data. -/

/-- **Logistic source slice C²-Neumann data, discharged from banked u-data.**

For each interior `t`, the four C²-Neumann hypotheses of
`realSlice_hlogInv_of_C2Neumann` hold for the logistic source slice
`intervalLogisticSource p (realSlice u_star t)`, produced from the globally-`C²`,
positive, Neumann u-slice cosine series via the committed logistic-source machinery.
The endpoint POINT-derivatives `hbc0`/`hbc1` of the zero-extension lift use the
junk-value route, hence the carried logistic-source endpoint nonvanishing
`hlogNE0`/`hlogNE1`. -/
theorem realSlice_logSource_C2Neumann
    (p : CM2Params) (u_star : EWA T 1) (u₀cos : ℕ → ℝ)
    {u₀E : WA 1} {δ ρ : ℝ} (hδρ : 0 < δ - ρ)
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ)
    (hu_ball : u_star ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ)
    (hsumE : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Summable (fun n => unitIntervalCosineEigenvalue n *
        |fullSourceCoeff p (realSlice u_star) u₀cos t n|))
    (hrealizes : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x
        = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x)
    (hlogNE0 : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      intervalDomainLift (intervalLogisticSource p (realSlice u_star t)) 0 ≠ 0)
    (hlogNE1 : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      intervalDomainLift (intervalLogisticSource p (realSlice u_star t)) 1 ≠ 0) :
    (∀ t ∈ Set.Ioo (0 : ℝ) T,
      Continuous (fun x : intervalDomainPoint =>
        intervalLogisticSource p (realSlice u_star t) x)) ∧
    (∀ t ∈ Set.Ioo (0 : ℝ) T,
      ContDiffOn ℝ 2
        (intervalDomainLift (intervalLogisticSource p (realSlice u_star t)))
        (Set.Icc (0 : ℝ) 1)) ∧
    (∀ t ∈ Set.Ioo (0 : ℝ) T,
      Tendsto (deriv (intervalDomainLift (intervalLogisticSource p (realSlice u_star t))))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) ∧
    (∀ t ∈ Set.Ioo (0 : ℝ) T,
      Tendsto (deriv (intervalDomainLift (intervalLogisticSource p (realSlice u_star t))))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0)) ∧
    (∀ t ∈ Set.Ioo (0 : ℝ) T,
      deriv (intervalDomainLift (intervalLogisticSource p (realSlice u_star t))) 0 = 0) ∧
    (∀ t ∈ Set.Ioo (0 : ℝ) T,
      deriv (intervalDomainLift (intervalLogisticSource p (realSlice u_star t))) 1 = 0) := by
  -- Per-time C²-Neumann data for `logisticSourceFun p.a p.b p.α (uSliceSeries …)`.
  have hcs : ∀ t ∈ Set.Ioo (0 : ℝ) T, ContDiff ℝ 2 (uSliceSeries p u_star u₀cos t) :=
    fun t ht => uSliceSeries_contDiff p u_star u₀cos (hsumE t ht)
  have hcspos : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < uSliceSeries p u_star u₀cos t x :=
    fun t ht => uSliceSeries_pos_Icc p u_star u₀cos hδρ hheat hu_ball ht (hrealizes t ht)
  have hcsN0 : ∀ t ∈ Set.Ioo (0 : ℝ) T, deriv (uSliceSeries p u_star u₀cos t) 0 = 0 :=
    fun t ht => uSliceSeries_neumann0 p u_star u₀cos (hsumE t ht)
  have hcsN1 : ∀ t ∈ Set.Ioo (0 : ℝ) T, deriv (uSliceSeries p u_star u₀cos t) 1 = 0 :=
    fun t ht => uSliceSeries_neumann1 p u_star u₀cos (hsumE t ht)
  -- `ContDiffOn ℝ 2 (lift logSource) Icc` via the Icc-agreement with `logisticSourceFun`.
  have hC2 : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      ContDiffOn ℝ 2
        (intervalDomainLift (intervalLogisticSource p (realSlice u_star t)))
        (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    refine (logisticSourceFun_contDiffOn_Icc (a := p.a) (b := p.b) (α := p.α)
      (g := uSliceSeries p u_star u₀cos t) (hcs t ht) (hcspos t ht)).congr ?_
    exact fun x hx => (logSourceLift_eqOn_Icc p u_star u₀cos (hrealizes t ht) hx)
  refine ⟨?_, hC2, ?_, ?_, ?_, ?_⟩
  · -- continuity of the slice: it is the `Icc`-restriction of the (continuousOn) lift.
    intro t ht
    have hCon : ContinuousOn
        (intervalDomainLift (intervalLogisticSource p (realSlice u_star t)))
        (Set.Icc (0 : ℝ) 1) := (hC2 t ht).continuousOn
    rw [continuousOn_iff_continuous_restrict] at hCon
    have heq : (Set.Icc (0 : ℝ) 1).restrict
        (intervalDomainLift (intervalLogisticSource p (realSlice u_star t)))
        = fun x : intervalDomainPoint => intervalLogisticSource p (realSlice u_star t) x := by
      funext ⟨y, hy⟩
      simp only [Set.restrict_apply, intervalDomainLift, dif_pos hy]
      exact congr_arg _ (Subtype.ext rfl)
    rwa [heq] at hCon
  · -- left Neumann limit: lift deriv =ᶠ logisticSourceFun deriv near 0⁺, which → 0.
    intro t ht
    refine Filter.Tendsto.congr' ?_
      (logisticSourceFun_tendsto_deriv_left (a := p.a) (b := p.b) (α := p.α)
        (hcs t ht) (hcspos t ht) (hcsN0 t ht))
    have hmem : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      mem_nhdsWithin.mpr ⟨Set.Iio 1, isOpen_Iio, by norm_num, fun z hz => ⟨hz.2, hz.1⟩⟩
    filter_upwards [hmem] with y hy
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz
    exact (logSourceLift_eqOn_Icc p u_star u₀cos (hrealizes t ht)
      (Set.Ioo_subset_Icc_self hz)).symm
  · -- right Neumann limit (symmetric).
    intro t ht
    refine Filter.Tendsto.congr' ?_
      (logisticSourceFun_tendsto_deriv_right (a := p.a) (b := p.b) (α := p.α)
        (hcs t ht) (hcspos t ht) (hcsN1 t ht))
    have hmem : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (1 : ℝ) (Set.Iio 1) :=
      mem_nhdsWithin.mpr ⟨Set.Ioi 0, isOpen_Ioi, by norm_num, fun z hz => ⟨hz.1, hz.2⟩⟩
    filter_upwards [hmem] with y hy
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz
    exact (logSourceLift_eqOn_Icc p u_star u₀cos (hrealizes t ht)
      (Set.Ioo_subset_Icc_self hz)).symm
  · -- `hbc0` of the zero-extension lift: junk-value via nonvanishing.
    exact fun t ht => intervalDomainLift_deriv_left_endpoint_zero_of_ne (hlogNE0 t ht)
  · -- `hbc1` of the zero-extension lift: junk-value via nonvanishing.
    exact fun t ht => intervalDomainLift_deriv_right_endpoint_zero_of_ne (hlogNE1 t ht)

/-! ### `hlogInv` fully discharged from banked u-data. -/

/-- **`hlogInv` of the `pde_u` family, discharged from banked u-data alone.**

Chaining `realSlice_logSource_C2Neumann` into `realSlice_hlogInv_of_C2Neumann`
yields the logistic inversion identity at every interior point, with NO carried
C²-Neumann data beyond the banked u-side atoms (`hsumE`, `hrealizes`, the heat-floor
positivity) plus the logistic-source endpoint nonvanishing `hlogNE0`/`hlogNE1`. -/
theorem realSlice_hlogInv_of_bankedU
    (p : CM2Params) (u_star : EWA T 1) (u₀cos : ℕ → ℝ)
    {u₀E : WA 1} {δ ρ : ℝ} (hδρ : 0 < δ - ρ)
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ)
    (hu_ball : u_star ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ)
    (hsumE : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Summable (fun n => unitIntervalCosineEigenvalue n *
        |fullSourceCoeff p (realSlice u_star) u₀cos t n|))
    (hrealizes : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x
        = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x)
    (hlogNE0 : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      intervalDomainLift (intervalLogisticSource p (realSlice u_star t)) 0 ≠ 0)
    (hlogNE1 : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      intervalDomainLift (intervalLogisticSource p (realSlice u_star t)) 1 ≠ 0) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint,
      x.1 ∈ Set.Ioo (0 : ℝ) 1 →
      (∑' n, ShenWork.IntervalCoupledRegularityBootstrap.coupledLogisticSourceCoeffs
          p (realSlice u_star) t n * cosineMode n x.1)
        = realSlice u_star t x
            * (p.a - p.b * (realSlice u_star t x) ^ p.α) := by
  obtain ⟨hcont, hC2, htend0, htend1, hbc0, hbc1⟩ :=
    realSlice_logSource_C2Neumann p u_star u₀cos hδρ hheat hu_ball hsumE hrealizes
      hlogNE0 hlogNE1
  exact realSlice_hlogInv_of_C2Neumann p (realSlice u_star)
    hcont hC2 htend0 htend1 hbc0 hbc1

/-! ### CHEM source — precise regularity-budget residual.

`intervalDomainChemotaxisDiv p u v x
  = ∂ₓ( lift u y · ∂ₓ(lift v) y / (1 + lift v y)^β )` (at `y = x.1`).
The chem source slice is therefore ONE spatial derivative of an inner expression that
ALREADY contains `∂ₓ(lift v)`.  For the slice to be `ContDiffOn ℝ 2` on `[0,1]`, the
inner expression must be `ContDiffOn ℝ 3`, which forces:
  * `lift (realSlice u_star t) ∈ C³`  (the factor `lift u`),
  * `∂ₓ(lift v) ∈ C³`, i.e. `lift v ∈ C⁴`  (the gradient factor and the saturation
    denominator `(1 + lift v)^β`).
The banked regularity gives only `C²` on BOTH sides:
  * the sole smoothness producer here is `cosineCoeffSeries_contDiff_two` (→ `C²`);
  * the banked resolver coefficient summability `resolverR_summability`
    (from `SourceCoeffQuadraticDecay`) is `λ_k|v̂_k|`-summable = `C²` only, NOT
    `λ_k²|v̂_k|` (`C⁴`).
So the chem-source C²-Neumann data CANNOT be produced from the banked C² u/v atoms.
The missing data is exactly: `lift (realSlice u_star t) ∈ C³` and
`lift (coupledChemicalConcentration p (realSlice u_star) t) ∈ C⁴`, per interior `t`.
This residual lemma re-exports `realSlice_hchemInv_of_C2Neumann`, which still carries
the chem C²-Neumann data as named hypotheses (the honest chem-source frontier). -/
theorem realSlice_hchemInv_C2Neumann_residual
    (p : CM2Params) (u_star : EWA T 1)
    (hcont : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Continuous (fun x : intervalDomainPoint =>
        ShenWork.IntervalDomain.intervalDomainChemotaxisDiv p (realSlice u_star t)
          (ShenWork.IntervalCoupledRegularityBootstrap.coupledChemicalConcentration
            p (realSlice u_star) t) x))
    (hC2 : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      ContDiffOn ℝ 2
        (intervalDomainLift (fun x =>
          ShenWork.IntervalDomain.intervalDomainChemotaxisDiv p (realSlice u_star t)
            (ShenWork.IntervalCoupledRegularityBootstrap.coupledChemicalConcentration
              p (realSlice u_star) t) x)) (Set.Icc (0 : ℝ) 1))
    (htend0 : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Tendsto (deriv (intervalDomainLift (fun x =>
        ShenWork.IntervalDomain.intervalDomainChemotaxisDiv p (realSlice u_star t)
          (ShenWork.IntervalCoupledRegularityBootstrap.coupledChemicalConcentration
            p (realSlice u_star) t) x)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htend1 : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Tendsto (deriv (intervalDomainLift (fun x =>
        ShenWork.IntervalDomain.intervalDomainChemotaxisDiv p (realSlice u_star t)
          (ShenWork.IntervalCoupledRegularityBootstrap.coupledChemicalConcentration
            p (realSlice u_star) t) x)))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0))
    (hbc0 : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      deriv (intervalDomainLift (fun x =>
        ShenWork.IntervalDomain.intervalDomainChemotaxisDiv p (realSlice u_star t)
          (ShenWork.IntervalCoupledRegularityBootstrap.coupledChemicalConcentration
            p (realSlice u_star) t) x)) 0 = 0)
    (hbc1 : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      deriv (intervalDomainLift (fun x =>
        ShenWork.IntervalDomain.intervalDomainChemotaxisDiv p (realSlice u_star t)
          (ShenWork.IntervalCoupledRegularityBootstrap.coupledChemicalConcentration
            p (realSlice u_star) t) x)) 1 = 0) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint,
      x.1 ∈ Set.Ioo (0 : ℝ) 1 →
      (∑' n, ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivSourceCoeffs
          p (realSlice u_star) t n * cosineMode n x.1)
        = ShenWork.IntervalDomain.intervalDomainChemotaxisDiv p (realSlice u_star t)
            (ShenWork.IntervalCoupledRegularityBootstrap.coupledChemicalConcentration
              p (realSlice u_star) t) x :=
  realSlice_hchemInv_of_C2Neumann p (realSlice u_star)
    hcont hC2 htend0 htend1 hbc0 hbc1

end ShenWork.EWA
