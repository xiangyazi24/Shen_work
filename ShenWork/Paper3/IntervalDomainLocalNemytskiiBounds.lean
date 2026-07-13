/-
  Local scalar Nemytskii bounds around a positive equilibrium.

  Arbitrary real powers are smooth on a compact interval separated from zero.
  These estimates supply the `u^m-uStar^m`, bounded `u^m`, and
  `(1+v)^(-beta)` factors used by the eliminated flux remainder.
-/
import ShenWork.Paper3.IntervalDomainEliminatedNonlinearity

namespace ShenWork.Paper3

open Set Real

noncomputable section

/-- The positive power map is locally Lipschitz around a positive base point. -/
theorem paper3Power_local_lipschitz
    {exponent uStar : ℝ} (huStar : 0 < uStar) :
    ∃ L > 0, ∀ x ∈ Set.Icc (uStar / 2) (3 * uStar / 2),
      |x ^ exponent - uStar ^ exponent| ≤ L * |x - uStar| := by
  let I : Set ℝ := Set.Icc (uStar / 2) (3 * uStar / 2)
  let derivPower : ℝ → ℝ := fun z => exponent * z ^ (exponent - 1)
  have hlower : 0 < uStar / 2 := by linarith
  have hpos : ∀ z ∈ I, 0 < z := by
    intro z hz
    exact lt_of_lt_of_le hlower hz.1
  have hcont : ContinuousOn derivPower I := by
    exact continuousOn_const.mul
      (continuousOn_id.rpow_const (fun z hz => Or.inl (hpos z hz).ne'))
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have huI : uStar ∈ I := by
    constructor <;> dsimp [I] <;> linarith
  have hM0 : 0 ≤ M := (norm_nonneg (derivPower uStar)).trans (hM uStar huI)
  let L : ℝ := M + 1
  have hL : 0 < L := by dsimp [L]; linarith
  refine ⟨L, hL, ?_⟩
  intro x hx
  have hder : ∀ z ∈ I,
      HasDerivWithinAt (fun y : ℝ => y ^ exponent) (derivPower z) I z := by
    intro z hz
    simpa [derivPower] using
      (Real.hasDerivAt_rpow_const
        (x := z) (p := exponent) (Or.inl (hpos z hz).ne')).hasDerivWithinAt
  have hbound : ∀ z ∈ I, ‖derivPower z‖ ≤ L := by
    intro z hz
    exact (hM z hz).trans (by dsimp [L]; linarith)
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    hder hbound (convex_Icc _ _) huI hx
  simpa [I, Real.norm_eq_abs] using hmv

/-- A positive power is uniformly bounded on the same compact neighborhood. -/
theorem paper3Power_local_abs_bound
    {exponent uStar : ℝ} (huStar : 0 < uStar) :
    ∃ U > 0, ∀ x ∈ Set.Icc (uStar / 2) (3 * uStar / 2),
      |x ^ exponent| ≤ U := by
  let I : Set ℝ := Set.Icc (uStar / 2) (3 * uStar / 2)
  have hlower : 0 < uStar / 2 := by linarith
  have hpos : ∀ z ∈ I, 0 < z := by
    intro z hz
    exact lt_of_lt_of_le hlower hz.1
  have hcont : ContinuousOn (fun z : ℝ => z ^ exponent) I :=
    continuousOn_id.rpow_const (fun z hz => Or.inl (hpos z hz).ne')
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have huI : uStar ∈ I := by
    constructor <;> dsimp [I] <;> linarith
  have hM0 : 0 ≤ M := (norm_nonneg (uStar ^ exponent)).trans (hM uStar huI)
  let U : ℝ := M + 1
  refine ⟨U, by dsimp [U]; linarith, ?_⟩
  intro x hx
  simpa [Real.norm_eq_abs] using
    (hM x hx).trans (show M ≤ U by dsimp [U]; linarith)

/-- Signal-dependent sensitivity factor. -/
def paper3SensitivityFactor (beta z : ℝ) : ℝ :=
  (1 + z) ^ (-beta)

/-- On any nonnegative bounded signal interval, the sensitivity factor is
Lipschitz. -/
theorem paper3SensitivityFactor_lipschitzOn_nonneg
    {beta V : ℝ} (hV : 0 < V) :
    ∃ L > 0, ∀ x ∈ Set.Icc (0 : ℝ) V,
      ∀ y ∈ Set.Icc (0 : ℝ) V,
        |paper3SensitivityFactor beta x -
            paper3SensitivityFactor beta y| ≤ L * |x - y| := by
  let I : Set ℝ := Set.Icc (0 : ℝ) V
  let derivSensitivity : ℝ → ℝ := fun z =>
    -beta * (1 + z) ^ (-beta - 1)
  have hbase : ∀ z ∈ I, 0 < 1 + z := by intro z hz; linarith [hz.1]
  have hcont : ContinuousOn derivSensitivity I := by
    exact continuousOn_const.mul
      ((continuousOn_const.add continuousOn_id).rpow_const
        (fun z hz => Or.inl (hbase z hz).ne'))
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hzeroI : (0 : ℝ) ∈ I := by constructor <;> linarith
  have hM0 : 0 ≤ M :=
    (norm_nonneg (derivSensitivity 0)).trans (hM 0 hzeroI)
  let L : ℝ := M + 1
  have hL : 0 < L := by dsimp [L]; linarith
  refine ⟨L, hL, ?_⟩
  intro x hx y hy
  have hder : ∀ z ∈ I,
      HasDerivWithinAt (paper3SensitivityFactor beta)
        (derivSensitivity z) I z := by
    intro z hz
    have hinner : HasDerivAt (fun w : ℝ => 1 + w) 1 z := by
      simpa using (hasDerivAt_const z (1 : ℝ)).add (hasDerivAt_id z)
    have hpow := (Real.hasDerivAt_rpow_const
      (x := 1 + z) (p := -beta) (Or.inl (hbase z hz).ne')).comp z hinner
    simpa [paper3SensitivityFactor, derivSensitivity, Function.comp_def]
      using hpow.hasDerivWithinAt
  have hbound : ∀ z ∈ I, ‖derivSensitivity z‖ ≤ L := by
    intro z hz
    exact (hM z hz).trans (by dsimp [L]; linarith)
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    hder hbound (convex_Icc _ _) hy hx
  simpa [I, Real.norm_eq_abs] using hmv

#print axioms paper3Power_local_lipschitz
#print axioms paper3Power_local_abs_bound
#print axioms paper3SensitivityFactor_lipschitzOn_nonneg

end

end ShenWork.Paper3
