/-
# The doubly-even `C⁶` source representative (ROUTE B: cosine series)

`ShenWork.Paper2.ChiNegUnconditionalClose.chiNeg_resolverC2Coeff_unconditional`
asks, per restart `L`, for smooth representatives `fSrc`/`fAdot : ℝ → ℝ` of the
source / time-derivative coefficient families `L.aC` / `L.srcC.adot`, with

  * `hSrcCoeff` : `L.aC s n = cosineCoeffs (fSrc s) n`,
  * `hSrcCD6`   : `ContDiff ℝ 6 (fSrc s)`,
  * `hSrcN0/N1` : the odd-derivative Neumann vanishing of `gTower (fSrc s)`,
  * `hSrcTop`   : `|rawCoeff n (gTower (fSrc s) 3)| ≤ M`.

**ROUTE B — the Neumann cosine series.**  We take the *honest* spatial source input
`DuhamelSourceSpatialWeightThree L.aC` (the eigen-**cube** coefficient summability
of `L.aC`/`L.srcC.adot`: the `k = 6` source regularity already isolated in the
`C⁷` ladder).  From its cube envelope we set

  `fSrc s x := ∑' n, L.aC s n · cosineMode n x`   (and likewise `fAdot`),

and discharge ALL FOUR families:

  * `hSrcCoeff` is the **coefficient-recovery** identity for an `ℓ¹` cosine series
    (`cosineCoeffs_of_l1_cosineSeries`; `ℓ¹` from the cube bound, `λₙ³ ≥ 1`),
  * `hSrcCD6` is **global** `ContDiff ℝ 6` from the eigen-cube summability
    (`cosineCoeffSeries_contDiff_six_of_eigenvalue_cube_summable`) — NO even-periodic
    extension needed: the series is genuinely a function on all of `ℝ`,
  * `hSrcN0/N1` are the double-even (cosine) parity (`higherNeumannCompatibility_of_doublyEven`,
    `DoublyEven` of the convergent cosine series — proved here),
  * `hSrcTop` is the sup-bound of `∂ₓ⁶ fSrc` on `[0,1]` (continuous on a compact).

No even-periodic-extension `ContDiffOn → ContDiff` bridge is invoked: ROUTE B sidesteps
the Mathlib gap entirely because the cosine **series** is global by construction, and
its global `C⁶` is exactly the eigen-cube coefficient summability.

No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalChiNegUnconditionalClose
import ShenWork.Paper2.IntervalSpatialC6Certificate
import ShenWork.Paper2.IntervalSourceRepresentative
import ShenWork.Paper2.IntervalPicardIterateRestart

open Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.Paper2.NeumannTowerOfC6 (gTower gTower_zero)
open ShenWork.Paper2.SourceRepresentative
open ShenWork.Paper2.SpatialC6Certificate
open ShenWork.Paper2.ParabolicDuhamelGainNonCircular (DuhamelSourceSpatialWeightThree)
open ShenWork.IntervalIBPCoeffExtraction (rawCoeff)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.Paper2.PicardLimitK1 (LocalRestart)
open ShenWork.Paper2.ChiNegUnconditionalClose
  (neumannTower_gTower_three_of_contDiff_six sourceEigenCubeTailFields_of_sourceRegularity)

noncomputable section

namespace ShenWork.Paper2.SourceC6Representative

/-- `unitIntervalCosineEigenvalue n ≥ 1` for `n ≥ 1` (`(nπ)² ≥ π² > 1`). -/
theorem one_le_eigenvalue {n : ℕ} (hn : 1 ≤ n) :
    (1 : ℝ) ≤ unitIntervalCosineEigenvalue n := by
  unfold unitIntervalCosineEigenvalue
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpi : (2 : ℝ) ≤ (n : ℝ) * Real.pi := by
    nlinarith [Real.two_le_pi, hn1, Real.pi_pos]
  nlinarith [hnpi]

/-- The cosine series of a sequence with finite eigen-cube weight is **doubly even**. -/
theorem doublyEven_cosineSeries (c : ℕ → ℝ) :
    DoublyEven (fun x => ∑' n, c n * cosineMode n x) where
  about0 := fun x => by
    refine tsum_congr (fun n => ?_)
    have := (doublyEven_cos n).about0 x
    simp only [cosineMode]; rw [this]
  about1 := fun x => by
    refine tsum_congr (fun n => ?_)
    have := (doublyEven_cos n).about1 x
    simp only [cosineMode]; rw [this]

/-- **`ℓ¹` from the eigen-cube bound.**  If `λₙ³ · |c n| ≤ E n` with `E` summable,
then `c` is absolutely summable (`λₙ³ ≥ 1` for `n ≥ 1`; the single `n = 0` term is finite). -/
theorem l1_of_eigenCube_summable {c E : ℕ → ℝ}
    (hE : Summable E)
    (hbound : ∀ n, unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n * |c n|)) ≤ E n) :
    Summable (fun n => |c n|) := by
  apply (summable_nat_add_iff 1).mp
  refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) ?_
    ((summable_nat_add_iff 1).mpr hE)
  intro k
  have hk1 : 1 ≤ k + 1 := Nat.le_add_left 1 k
  have hlam := one_le_eigenvalue hk1
  have hcube : (1 : ℝ) ≤ unitIntervalCosineEigenvalue (k + 1) *
      (unitIntervalCosineEigenvalue (k + 1) * unitIntervalCosineEigenvalue (k + 1)) := by
    nlinarith [hlam, mul_nonneg (le_trans zero_le_one hlam) (le_trans zero_le_one hlam)]
  have hstep : |c (k + 1)| ≤ unitIntervalCosineEigenvalue (k + 1) *
      (unitIntervalCosineEigenvalue (k + 1) * unitIntervalCosineEigenvalue (k + 1)) *
      |c (k + 1)| := by
    nlinarith [mul_le_mul_of_nonneg_right hcube (abs_nonneg (c (k + 1)))]
  refine le_trans hstep ?_
  have hb := hbound (k + 1)
  nlinarith [hb]

/-- The eigen-cube **summability** of `c` from the bound (for the `C⁶` certificate). -/
theorem eigenCube_summable_of_bound {c E : ℕ → ℝ}
    (hE : Summable E)
    (hbound : ∀ n, unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n * |c n|)) ≤ E n) :
    Summable (fun n => unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n * |c n|))) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) hbound hE
  have h0 : (0:ℝ) ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue; positivity
  positivity

/-- **`rawCoeff` sup-bound.**  If `|g x| ≤ M` for `x ∈ [0,1]` and `g` is continuous,
then `|rawCoeff n g| ≤ M`. -/
theorem abs_rawCoeff_le {g : ℝ → ℝ} {M : ℝ}
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, |g x| ≤ M) :
    |rawCoeff n g| ≤ M := by
  unfold rawCoeff
  have hbnd : ∀ x ∈ uIoc (0:ℝ) 1, ‖Real.cos ((n:ℝ) * Real.pi * x) * g x‖ ≤ M := by
    intro x hx
    rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    rw [Real.norm_eq_abs, abs_mul]
    have hc : |Real.cos ((n:ℝ) * Real.pi * x)| ≤ 1 := Real.abs_cos_le_one _
    have hgx : |g x| ≤ M := hb x ⟨le_of_lt hx.1, hx.2⟩
    calc |Real.cos ((n:ℝ) * Real.pi * x)| * |g x| ≤ 1 * M :=
          mul_le_mul hc hgx (abs_nonneg _) zero_le_one
      _ = M := one_mul M
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1) hbnd
  rw [Real.norm_eq_abs] at this
  simpa using this

/-- Envelope value is `≤` its sum (all terms nonneg). -/
theorem envelope_le_tsum {E : ℕ → ℝ} (hE : Summable E) (hEnn : ∀ n, 0 ≤ E n)
    (n : ℕ) : E n ≤ ∑' m, E m := by
  have hsingle := hE.sum_le_tsum ({n} : Finset ℕ) (fun m _hm => hEnn m)
  simpa using hsingle

/-- `cosineCoeffs f n = 2 · rawCoeff n f` for `n ≥ 1`. -/
theorem cosineCoeffs_eq_two_rawCoeff {f : ℝ → ℝ} {n : ℕ} (hn : 1 ≤ n) :
    cosineCoeffs f n = 2 * rawCoeff n f := by
  rw [ShenWork.IntervalMildPicardRegularity.cosineCoeffs_eq_factor_mul_integral]
  simp only [Nat.one_le_iff_ne_zero.mp hn, if_false]
  rfl

/-- **The per-restart eigen-cube source tail from the cosine-series `C⁶` representative.**

ROUTE B: the source representatives are the Neumann cosine **series** of `L.aC`/`L.srcC.adot`,
which are global `C⁶` (eigen-cube coefficient summability) and doubly even (cosine parity).
The eigen-cube bound on the coefficients discharges `hSrcCoeff` (ℓ¹ recovery), `hSrcCD6`
(global `C⁶`), `hSrcN0`/`hSrcN1` (parity), and `hSrcTop` (IBP: the top tower coefficient is
`λₙ³·L.aC/2`, bounded by the envelope sum).  `SourceEigenCubeTailFields` is the conclusion. -/
theorem sourceEigenCubeTailFields_of_weightThree
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {T σ : ℝ}
    (L : LocalRestart p u T σ)
    {Esrc Eadot : ℕ → ℝ}
    (hEsrc_nn : ∀ n, 0 ≤ Esrc n) (hEsrc_sum : Summable Esrc)
    (hEsrc_bd : ∀ s, 0 ≤ s → ∀ n, unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n * |L.aC s n|)) ≤ Esrc n)
    (hEadot_nn : ∀ n, 0 ≤ Eadot n) (hEadot_sum : Summable Eadot)
    (hEadot_bd : ∀ s, 0 ≤ s → ∀ n, unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n * |L.srcC.adot s n|)) ≤ Eadot n)
    {C0 C0dot : ℝ} (hC0 : 0 ≤ C0) (hC0dot : 0 ≤ C0dot)
    (hSrcZero : ∀ s, 0 ≤ s → |L.aC s 0| ≤ C0)
    (hAdotZero : ∀ s, 0 ≤ s → |L.srcC.adot s 0| ≤ C0dot) :
    ShenWork.Paper2.ChiNegSourceTail.SourceEigenCubeTailFields
      L C0 (2 * (∑' m, Esrc m)) C0dot (2 * (∑' m, Eadot m)) := by
  -- The cosine-series representatives.
  set fSrc : ℝ → ℝ → ℝ := fun s => fun x => ∑' n, L.aC s n * cosineMode n x with hfSrc
  set fAdot : ℝ → ℝ → ℝ := fun s => fun x => ∑' n, L.srcC.adot s n * cosineMode n x with hfAdot
  -- Generic discharge bundle for one coefficient family `a` with envelope `E`.
  have disch : ∀ (a : ℝ → ℕ → ℝ) (E : ℕ → ℝ),
      (∀ n, 0 ≤ E n) → Summable E →
      (∀ s, 0 ≤ s → ∀ n, unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n * |a s n|)) ≤ E n) →
      (∀ s, 0 ≤ s → ∀ n, a s n = cosineCoeffs (fun x => ∑' m, a s m * cosineMode m x) n) ∧
      (∀ s, 0 ≤ s → ContDiff ℝ (6:ℕ) (fun x => ∑' m, a s m * cosineMode m x)) ∧
      (∀ s, 0 ≤ s → ∀ i, i < 3 →
        deriv (gTower (fun x => ∑' m, a s m * cosineMode m x) i) 0 = 0) ∧
      (∀ s, 0 ≤ s → ∀ i, i < 3 →
        deriv (gTower (fun x => ∑' m, a s m * cosineMode m x) i) 1 = 0) ∧
      (∀ s, 0 ≤ s → ∀ n, 1 ≤ n →
        |rawCoeff n (gTower (fun x => ∑' m, a s m * cosineMode m x) 3)| ≤
          (∑' m, E m)) := by
    intro a E hEnn hEsum hEbd
    have hl1 : ∀ s, 0 ≤ s → Summable (fun n => |a s n|) := fun s hs =>
      l1_of_eigenCube_summable hEsum (hEbd s hs)
    have hcube : ∀ s, 0 ≤ s → Summable (fun n => unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n * |a s n|))) := fun s hs =>
      eigenCube_summable_of_bound hEsum (hEbd s hs)
    have hcoeff : ∀ s, 0 ≤ s → ∀ n,
        a s n = cosineCoeffs (fun x => ∑' m, a s m * cosineMode m x) n := fun s hs n =>
      (ShenWork.IntervalPicardIterateRestart.cosineCoeffs_of_l1_cosineSeries
        (hl1 s hs) n).symm
    have hcd6 : ∀ s, 0 ≤ s → ContDiff ℝ (6:ℕ)
        (fun x => ∑' m, a s m * cosineMode m x) := fun s hs =>
      cosineCoeffSeries_contDiff_six_of_eigenvalue_cube_summable (hcube s hs)
    have hde : ∀ s, DoublyEven (fun x => ∑' m, a s m * cosineMode m x) := fun s =>
      doublyEven_cosineSeries (a s)
    refine ⟨hcoeff, hcd6, ?_, ?_, ?_⟩
    · exact fun s hs i _ => (higherNeumannCompatibility_of_doublyEven (hde s)).1 i (by omega)
    · exact fun s hs i _ => (higherNeumannCompatibility_of_doublyEven (hde s)).2 i (by omega)
    · -- hSrcTop via IBP on the (gTower) Neumann tower.
      intro s hs n hn
      have htower := neumannTower_gTower_three_of_contDiff_six (hcd6 s hs)
        (fun i _ => (higherNeumannCompatibility_of_doublyEven (hde s)).1 i (by omega))
        (fun i _ => (higherNeumannCompatibility_of_doublyEven (hde s)).2 i (by omega))
      have hit := ShenWork.IntervalIBPCoeffExtraction.rawCoeff_iterate n htower
      rw [gTower_zero] at hit
      rw [hit]
      -- rawCoeff n base = cosineCoeffs / 2 = a s n / 2.
      have hbase : rawCoeff n (fun x => ∑' m, a s m * cosineMode m x) = a s n / 2 := by
        have := cosineCoeffs_eq_two_rawCoeff (f := fun x => ∑' m, a s m * cosineMode m x) hn
        rw [← hcoeff s hs n] at this
        linarith [this]
      rw [hbase]
      have hpow : |(-((n : ℝ) * Real.pi) ^ 2) ^ 3 * (a s n / 2)| =
          unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              (unitIntervalCosineEigenvalue n * |a s n|)) / 2 := by
        unfold unitIntervalCosineEigenvalue
        rw [show (-((n : ℝ) * Real.pi) ^ 2) ^ 3 * (a s n / 2)
            = (-(((n : ℝ) * Real.pi) ^ 2) ^ 3) * (a s n / 2) by ring]
        rw [abs_mul, abs_neg, abs_div]
        have hcb : (0:ℝ) ≤ (((n : ℝ) * Real.pi) ^ 2) ^ 3 := by positivity
        rw [abs_of_nonneg hcb, show |(2:ℝ)| = 2 by norm_num]
        ring
      rw [hpow]
      have hbd := hEbd s hs n
      have hle := envelope_le_tsum hEsum hEnn n
      have hEpos : 0 ≤ ∑' m, E m := le_trans (hEnn n) hle
      have hcubenn : 0 ≤ unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n * |a s n|)) := by
        have h0 : (0:ℝ) ≤ unitIntervalCosineEigenvalue n := by
          unfold unitIntervalCosineEigenvalue; positivity
        positivity
      have hnum : unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n * |a s n|)) ≤ ∑' m, E m :=
        le_trans hbd hle
      linarith [hnum, hcubenn]
  obtain ⟨hSC, hSD, hSN0, hSN1, hST⟩ := disch L.aC Esrc hEsrc_nn hEsrc_sum hEsrc_bd
  obtain ⟨hAC, hAD, hAN0, hAN1, hAT⟩ := disch L.srcC.adot Eadot hEadot_nn hEadot_sum hEadot_bd
  exact sourceEigenCubeTailFields_of_sourceRegularity
    L hC0 hC0dot hSC hSD hSN0 hSN1 hST hAC hAD hAN0 hAN1 hAT hSrcZero hAdotZero

#print axioms sourceEigenCubeTailFields_of_weightThree

end ShenWork.Paper2.SourceC6Representative
