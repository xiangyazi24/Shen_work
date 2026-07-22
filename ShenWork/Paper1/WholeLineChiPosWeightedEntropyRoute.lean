import ShenWork.Paper1.WholeLineChiPosSharpEntropyDissipation
import ShenWork.Paper1.WholeLineLocalMoment

/-!
# Slowly localized sharp-entropy route

The periodic entropy law in `WholeLineChiPosSharpEntropyDissipation` has the
sharp nonlinear coefficient `1 - chi^2/16`.  A whole-line Liouville argument
needs an integrable weight.  This file isolates the exact quantitative loss
caused by a slowly varying weight.

If `phi >= 0` and `|phi_x| <= k phi`, weighted testing of
`-r_xx + r = w` gives, after two integrations by parts,

`integral phi r_x^2 <= (1+k)/(4(1-k)) integral phi w^2`.

The constant tends to the sharp `1/4` as `k -> 0`.  The theorem below is
stated in terms of the five scalar integrals produced by those integrations
by parts; this makes the remaining analytic interface explicit and reusable.

For the entropy equation, reserving `k` of the diffusion controls the
diffusion-weight flux, while the drift and chemotaxis-weight fluxes cost only
`O(k)`.  The resulting explicit loss tends to `chi^2/16`.  Consequently every
`0 <= chi < 4` admits a positive localization slope with strictly positive
weighted entropy margin.
-/

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-- The near-sharp resolver gradient gain for a weight with logarithmic slope
at most `k`. -/
def weightedResolverNearSharpGain (k : ℝ) : ℝ :=
  (1 + k) / (4 * (1 - k))

/-- Algebraic closure of the weighted resolver test.  The hypotheses are the
exact scalar output of testing `-r_xx+r=w` by `phi*r`, expanding the source
square, and estimating `J = integral phi_x*r*r_x` from
`|phi_x| <= k*phi`.

`S,A,I,C` stand for the weighted squares of `w,r,r_x,r_xx`; `R` is the
weighted `w*r` pairing. -/
theorem weighted_resolver_near_sharp_of_testing
    {k S A I C J R : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hS : 0 ≤ S) (hA : 0 ≤ A) (hI : 0 ≤ I) (_hC : 0 ≤ C)
    (htest : A + I + J = R)
    (hpair : 2 * R ≤ S + A)
    (hJ : |J| ≤ (k / 2) * (A + I))
    (hsource : S = A + 2 * I + 2 * J + C)
    (hsecondYoung : 2 * I + 2 * J ≤ A + C) :
    I ≤ weightedResolverNearSharpGain k * S := by
  have hkpos : 0 < 1 - k := sub_pos.mpr hk1
  have hJlower : -(k / 2 * (A + I)) ≤ J := (abs_le.mp hJ).1
  have hH : (1 - k) * (A + I) ≤ S := by
    nlinarith [htest, hpair, hJlower]
  have hsourceCore : 4 * I + 4 * J ≤ S := by
    nlinarith [hsource, hsecondYoung]
  have hbase : 4 * I ≤ S + 4 * |J| := by
    nlinarith [hsourceCore, neg_abs_le J]
  have hJscaled : 4 * |J| ≤ 2 * k * (A + I) := by
    nlinarith [hJ]
  have hbase' : 4 * I ≤ S + 2 * k * (A + I) := hbase.trans (by linarith)
  have hbaseScaled := mul_le_mul_of_nonneg_left hbase' hkpos.le
  have hHscaled := mul_le_mul_of_nonneg_left hH hk0
  have hpoly : 4 * (1 - k) * I ≤ (1 + k) * S := by
    nlinarith
  unfold weightedResolverNearSharpGain
  rw [show (1 + k) / (4 * (1 - k)) * S =
      ((1 + k) * S) / (4 * (1 - k)) by ring]
  exact (le_div_iff₀ (by positivity : 0 < 4 * (1 - k))).2 (by
    nlinarith [hpoly])

/-- Polynomial form of the same estimate; useful before division. -/
theorem weighted_resolver_near_sharp_polynomial
    {k S A I C J R : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hS : 0 ≤ S) (hA : 0 ≤ A) (hI : 0 ≤ I) (hC : 0 ≤ C)
    (htest : A + I + J = R)
    (hpair : 2 * R ≤ S + A)
    (hJ : |J| ≤ (k / 2) * (A + I))
    (hsource : S = A + 2 * I + 2 * J + C)
    (hsecondYoung : 2 * I + 2 * J ≤ A + C) :
    4 * (1 - k) * I ≤ (1 + k) * S := by
  have hgain := weighted_resolver_near_sharp_of_testing hk0 hk1 hS hA hI hC
    htest hpair hJ hsource hsecondYoung
  have hkpos : 0 < 1 - k := sub_pos.mpr hk1
  unfold weightedResolverNearSharpGain at hgain
  rw [show (1 + k) / (4 * (1 - k)) * S =
      ((1 + k) * S) / (4 * (1 - k)) by ring] at hgain
  have hraw := (le_div_iff₀ (by positivity : 0 < 4 * (1 - k))).1 hgain
  nlinarith

/-! ## Entropy and flux algebra -/

/-- The relative entropy is nonnegative on the positive axis. -/
theorem chiOneRelativeEntropy_nonneg {u : ℝ} (hu : 0 < u) :
    0 ≤ chiOneRelativeEntropy u := by
  unfold chiOneRelativeEntropy
  linarith [Real.log_le_sub_one_of_pos hu]

/-- On a positive band with floor `ell`, the entropy is controlled by the
squared displacement.  The elementary lower logarithm bound is enough; no
Taylor theorem is needed. -/
theorem chiOneRelativeEntropy_le_sq_div
    {ell u : ℝ} (hell : 0 < ell) (hellu : ell ≤ u) :
    chiOneRelativeEntropy u ≤ (u - 1) ^ 2 / ell := by
  have hu : 0 < u := hell.trans_le hellu
  have hlog := Real.one_sub_inv_le_log_of_pos hu
  have hraw : chiOneRelativeEntropy u ≤ (u - 1) ^ 2 / u := by
    apply (le_div_iff₀ hu).2
    unfold chiOneRelativeEntropy
    have hmul := mul_le_mul_of_nonneg_left hlog hu.le
    field_simp [hu.ne'] at hmul
    nlinarith
  exact hraw.trans <| by
    have hsquare : 0 ≤ (u - 1) ^ 2 := sq_nonneg _
    exact div_le_div_of_nonneg_left hsquare hell hellu

/-- Explicit coefficient left after the three weight-flux estimates and the
near-sharp weighted resolver bound. -/
def chiOneWeightedEntropyLoss (chi c ell k : ℝ) : ℝ :=
  chi ^ 2 * weightedResolverNearSharpGain k / (4 * (1 - k)) +
    k / 4 +
    chi * k / 2 * (1 + weightedResolverNearSharpGain k) +
    |c| * k / ell

/-- Abstract closure of the localized entropy calculation.  `D,I,W,X,Q,F`
are respectively the weighted squares of `u_x/u`, `r_x`, `u-1`, the main
cross pairing, entropy production, and the sum of weight-flux errors.

The hypotheses `hmainCross` and `hflux` are exactly the two pointwise Young
estimates obtained from `|phi_x| <= k phi`; no nonlinear smallness of `u-1`
is assumed, only a positive floor through the drift entropy bound. -/
theorem weighted_entropy_decay_of_flux_budget
    {chi c ell k D I W X Q F : ℝ}
    (hchi : 0 ≤ chi) (hell : 0 < ell)
    (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hD : 0 ≤ D) (hW : 0 ≤ W)
    (hresolver : I ≤ weightedResolverNearSharpGain k * W)
    (hproduction : Q ≤ -D + chi * X - W + F)
    (hmainCross : chi * X ≤
      (1 - k) * D + chi ^ 2 / (4 * (1 - k)) * I)
    (hflux : F ≤
      (k * D +
        (k / 4 + chi * k / 2 + |c| * k / ell) * W +
          (chi * k / 2) * I)) :
    Q ≤ -(1 - chiOneWeightedEntropyLoss chi c ell k) * W := by
  have hkpos : 0 < 1 - k := sub_pos.mpr hk1
  have hchiSq : 0 ≤ chi ^ 2 / (4 * (1 - k)) := by positivity
  have hresScaled := mul_le_mul_of_nonneg_left hresolver hchiSq
  have hchiK : 0 ≤ chi * k / 2 := by positivity
  have hresChemScaled := mul_le_mul_of_nonneg_left hresolver hchiK
  have hcombined :
      Q ≤
        (chi ^ 2 / (4 * (1 - k)) + chi * k / 2) * I +
          (-1 + k / 4 + chi * k / 2 + |c| * k / ell) * W := by
    nlinarith [hproduction, hmainCross, hflux]
  calc
    Q ≤
        (chi ^ 2 / (4 * (1 - k)) + chi * k / 2) * I +
          (-1 + k / 4 + chi * k / 2 + |c| * k / ell) * W := hcombined
    _ ≤
        (chi ^ 2 / (4 * (1 - k)) * weightedResolverNearSharpGain k +
            chi * k / 2 * weightedResolverNearSharpGain k) * W +
          (-1 + k / 4 + chi * k / 2 + |c| * k / ell) * W := by
      nlinarith [hresScaled, hresChemScaled]
    _ = -(1 - chiOneWeightedEntropyLoss chi c ell k) * W := by
      unfold chiOneWeightedEntropyLoss
      ring

/-! ## Every sub-Turing sensitivity admits a slow localization -/

/-- A convenient explicit localization slope. -/
def chiOneLocalizationSlope (chi : ℝ) : ℝ :=
  (16 - chi ^ 2) / (2 * (16 + chi ^ 2))

theorem chiOneLocalizationSlope_pos
    {chi : ℝ} (hchi : 0 ≤ chi) (hchi4 : chi < 4) :
    0 < chiOneLocalizationSlope chi := by
  unfold chiOneLocalizationSlope
  have hnum : 0 < 16 - chi ^ 2 := by nlinarith
  have hden : 0 < 2 * (16 + chi ^ 2) := by positivity
  positivity

theorem chiOneLocalizationSlope_lt_one
    {chi : ℝ} (hchi : 0 ≤ chi) (hchi4 : chi < 4) :
    chiOneLocalizationSlope chi < 1 := by
  have hpos := chiOneLocalizationSlope_pos hchi hchi4
  unfold chiOneLocalizationSlope at hpos ⊢
  have hden : 0 < 2 * (16 + chi ^ 2) := by positivity
  rw [div_lt_one hden]
  nlinarith [sq_nonneg chi]

/-- The resolver-only weighted margin is already positive at the explicit
slope. -/
theorem chiOneLocalizationSlope_resolver_margin
    {chi : ℝ} (hchi : 0 ≤ chi) (hchi4 : chi < 4) :
    chi ^ 2 * (1 + chiOneLocalizationSlope chi) <
      16 * (1 - chiOneLocalizationSlope chi) := by
  have hnum : 0 < 16 - chi ^ 2 := by nlinarith
  have hden : 2 * (16 + chi ^ 2) ≠ 0 := by positivity
  have heq :
      16 * (1 - chiOneLocalizationSlope chi) -
          chi ^ 2 * (1 + chiOneLocalizationSlope chi) =
        (16 - chi ^ 2) / 2 := by
    unfold chiOneLocalizationSlope
    field_simp [hden]
    ring
  nlinarith

/-- The full localized entropy loss converges to the sharp value
`chi^2/16` as the logarithmic slope tends to zero. -/
theorem chiOneWeightedEntropyLoss_continuousAt_zero
    {chi c ell : ℝ} (hell : ell ≠ 0) :
    ContinuousAt (chiOneWeightedEntropyLoss chi c ell) 0 := by
  have hk : ContinuousAt (fun k : ℝ ↦ k) 0 := continuousAt_id
  have hsub : ContinuousAt (fun k : ℝ ↦ 1 - k) 0 :=
    continuousAt_const.sub hk
  have hden : ContinuousAt (fun k : ℝ ↦ 4 * (1 - k)) 0 :=
    continuousAt_const.mul hsub
  have hden0 : (4 * (1 - (0 : ℝ))) ≠ 0 := by norm_num
  have hgain : ContinuousAt weightedResolverNearSharpGain 0 := by
    unfold weightedResolverNearSharpGain
    exact (continuousAt_const.add hk).div hden hden0
  have hterm1 : ContinuousAt
      (fun k ↦ chi ^ 2 * weightedResolverNearSharpGain k /
        (4 * (1 - k))) 0 :=
    (continuousAt_const.mul hgain).div hden hden0
  have hterm2 : ContinuousAt (fun k : ℝ ↦ k / 4) 0 :=
    hk.div_const 4
  have hterm3 : ContinuousAt
      (fun k ↦ chi * k / 2 * (1 + weightedResolverNearSharpGain k)) 0 :=
    ((continuousAt_const.mul hk).div_const 2).mul
      (continuousAt_const.add hgain)
  have hterm4 : ContinuousAt (fun k : ℝ ↦ |c| * k / ell) 0 :=
    (continuousAt_const.mul hk).div_const ell
  unfold chiOneWeightedEntropyLoss
  exact ((hterm1.add hterm2).add hterm3).add hterm4

theorem chiOneWeightedEntropyLoss_zero
    (chi c ell : ℝ) :
    chiOneWeightedEntropyLoss chi c ell 0 = chi ^ 2 / 16 := by
  unfold chiOneWeightedEntropyLoss weightedResolverNearSharpGain
  ring

/-- **Localization exists on the full nonlinear sharp range.**  For every
`0 <= chi < 4`, every speed `c`, and every positive population floor `ell`,
one can choose an integrable-weight logarithmic slope `0 < k < 1` for which
all explicit resolver and weight-flux losses leave a positive entropy margin.
-/
theorem exists_chiOne_localizationSlope_full_sharp_range
    {chi c ell : ℝ} (hchi : 0 ≤ chi) (hchi4 : chi < 4) (hell : 0 < ell) :
    ∃ k : ℝ, 0 < k ∧ k < 1 ∧ chiOneWeightedEntropyLoss chi c ell k < 1 := by
  have hzero : chi ^ 2 / 16 < 1 := by nlinarith
  have hcont := chiOneWeightedEntropyLoss_continuousAt_zero
    (chi := chi) (c := c) (ell := ell) hell.ne'
  have hev : ∀ᶠ k in 𝓝 (0 : ℝ), chiOneWeightedEntropyLoss chi c ell k < 1 := by
    have hIio : Set.Iio (1 : ℝ) ∈ 𝓝 (chiOneWeightedEntropyLoss chi c ell 0) := by
      rw [chiOneWeightedEntropyLoss_zero]
      exact Iio_mem_nhds hzero
    exact hcont hIio
  have hset :
      {k : ℝ | chiOneWeightedEntropyLoss chi c ell k < 1} ∈ 𝓝 (0 : ℝ) := hev
  rw [Metric.mem_nhds_iff] at hset
  obtain ⟨eps, heps, hball⟩ := hset
  let k : ℝ := min (eps / 2) (1 / 2)
  have hkpos : 0 < k := by
    dsimp [k]
    exact lt_min (half_pos heps) (by norm_num)
  have hkhalf : k ≤ 1 / 2 := min_le_right _ _
  have hkeps : k < eps := by
    have hk : k ≤ eps / 2 := min_le_left _ _
    linarith
  have hkball : k ∈ Metric.ball (0 : ℝ) eps := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hkpos]
    exact hkeps
  exact ⟨k, hkpos, hkhalf.trans_lt (by norm_num), hball hkball⟩

section AxiomAudit

#print axioms weighted_resolver_near_sharp_of_testing
#print axioms weighted_resolver_near_sharp_polynomial
#print axioms chiOneRelativeEntropy_nonneg
#print axioms chiOneRelativeEntropy_le_sq_div
#print axioms weighted_entropy_decay_of_flux_budget
#print axioms chiOneLocalizationSlope_resolver_margin
#print axioms exists_chiOne_localizationSlope_full_sharp_range

end AxiomAudit

end ShenWork.Paper1
