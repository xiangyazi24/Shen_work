import ShenWork.PaperOne.WholeLineMildMap

open MeasureTheory Filter Topology Real

noncomputable section

namespace ShenWork.PaperOne

/-- Spatial translation by `a`: `(τ_a F)(x) = F(x+a)`. -/
def spatialTranslate (a : ℝ) (F : ℝ → ℝ) : ℝ → ℝ :=
  fun x => F (x + a)

/--
Moving-frame heat operator for `Δ + c∂ₓ - I`.

The drift semigroup is translation by `c t`, so this is the whole-line modified
heat semigroup evaluated at `x + c t`.
-/
def movingFrameHeatOp (c t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  wholeLineHeatOp t f (x + c * t)

/-- The moving-frame semigroup is the translated whole-line `e^{(Δ-I)t}` semigroup. -/
theorem movingFrameHeatOp_eq_translate (c t : ℝ) (f : ℝ → ℝ) :
    movingFrameHeatOp c t f = spatialTranslate (c * t) (wholeLineHeatOp t f) := by
  rfl

/-- Kernel representation: `e^{(Δ+c∂ₓ-I)t} f(x) = e^{-t} (G_t∗f)(x+ct)`. -/
theorem movingFrameHeatOp_eq_shifted_heat (c t : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    movingFrameHeatOp c t f x =
      Real.exp (-t) * heatSemigroup t f (x + c * t) := by
  rfl

/-- Interval preservation for the shifted modified heat semigroup. -/
theorem movingFrameHeatOp_interval_bound {c : ℝ} {f : ℝ → ℝ} {lo hi Mf t : ℝ}
    (hf_ge : ∀ x, lo ≤ f x) (hf_le : ∀ x, f x ≤ hi)
    (hf_bound : ∀ x, |f x| ≤ Mf)
    (hf_meas : AEStronglyMeasurable f volume) (ht : 0 < t) :
    ∀ x, Real.exp (-t) * lo ≤ movingFrameHeatOp c t f x ∧
      movingFrameHeatOp c t f x ≤ Real.exp (-t) * hi := by
  intro x
  simpa [movingFrameHeatOp] using
    wholeLineHeatOp_interval_bound hf_ge hf_le hf_bound hf_meas ht (x + c * t)

/-- Uniform `L∞` bound for nonnegative times, including the kernel's zero-time convention. -/
theorem movingFrameHeatOp_abs_bound_of_nonneg_time {c t M : ℝ} {f : ℝ → ℝ}
    (hf_bound : ∀ x, |f x| ≤ M) (hM : 0 ≤ M)
    (hf_meas : AEStronglyMeasurable f volume) (ht : 0 ≤ t) :
    ∀ x, |movingFrameHeatOp c t f x| ≤ M := by
  intro x
  by_cases ht0 : t = 0
  · subst t
    simpa [movingFrameHeatOp, wholeLineHeatOp, modifiedSemigroup, heatSemigroup_zero]
      using hM
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have hbound :
        |movingFrameHeatOp c t f x| ≤ Real.exp (-t) * M := by
      simpa [movingFrameHeatOp, wholeLineHeatOp] using
        modifiedSemigroup_Linfty_bound hf_bound htpos hM hf_meas (x + c * t)
    have hexp_le : Real.exp (-t) ≤ 1 := by
      exact Real.exp_le_one_iff.mpr (by linarith)
    have hdecay : Real.exp (-t) * M ≤ M := by
      simpa using mul_le_mul_of_nonneg_right hexp_le hM
    exact hbound.trans hdecay

/--
Frozen-`V` auxiliary nonlinearity from (4.12).

`W` is the current slice, `Wx` its spatial derivative field, and `V`, `Vx` are
frozen signal data.
-/
def auxiliaryFrozenNonlinearity (p : CMParams)
    (W Wx V Vx : ℝ → ℝ) (x : ℝ) : ℝ :=
  -p.χ * p.m * (W x) ^ (p.m - 1) * Wx x * Vx x
    - p.χ * (W x) ^ p.m * V x
    + p.χ * (W x) ^ (p.m + p.γ)
    + wholeLineReaction p W x

/-- Duhamel term for a generic source in the moving frame. -/
def movingFrameDuhamel (c : ℝ) (F : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  ∫ s in Set.Icc (0 : ℝ) t, movingFrameHeatOp c (t - s) (F s) x

/--
Pointwise boundedness of the moving-frame Duhamel term.

If the source is uniformly bounded by `C` on `0 ≤ s ≤ t`, then the Duhamel
integral is bounded by `C t`.
-/
theorem movingFrameDuhamel_abs_le_of_bound {c C t : ℝ} {F : ℝ → ℝ → ℝ}
    (ht : 0 ≤ t) (hC : 0 ≤ C)
    (hF_bound : ∀ s ∈ Set.Icc (0 : ℝ) t, ∀ y, |F s y| ≤ C)
    (hF_meas : ∀ s ∈ Set.Icc (0 : ℝ) t, AEStronglyMeasurable (F s) volume) :
    ∀ x, |movingFrameDuhamel c F t x| ≤ C * t := by
  intro x
  have hfinite : volume (Set.Icc (0 : ℝ) t) < ⊤ := by
    exact measure_Icc_lt_top
  have hnorm :
      ‖∫ s in Set.Icc (0 : ℝ) t, movingFrameHeatOp c (t - s) (F s) x‖ ≤
        C * volume.real (Set.Icc (0 : ℝ) t) := by
    refine norm_setIntegral_le_of_norm_le_const (μ := volume)
      (s := Set.Icc (0 : ℝ) t) (f := fun s => movingFrameHeatOp c (t - s) (F s) x)
      hfinite ?_
    intro s hs
    have htau : 0 ≤ t - s := sub_nonneg.mpr hs.2
    have hsem :=
      movingFrameHeatOp_abs_bound_of_nonneg_time
        (c := c) (t := t - s) (M := C) (f := F s)
        (hF_bound s hs) hC (hF_meas s hs) htau x
    simpa [Real.norm_eq_abs] using hsem
  have hvol : volume.real (Set.Icc (0 : ℝ) t) = t := by
    simpa using Real.volume_real_Icc_of_le ht
  simpa [movingFrameDuhamel, Real.norm_eq_abs, hvol] using hnorm

/-- Auxiliary Duhamel term for the frozen-`V` nonlinearity. -/
def auxiliaryDuhamel (p : CMParams) (c : ℝ)
    (W Wx : ℝ → ℝ → ℝ) (V Vx : ℝ → ℝ) (t x : ℝ) : ℝ :=
  movingFrameDuhamel c
    (fun s y => auxiliaryFrozenNonlinearity p (W s) (Wx s) V Vx y) t x

/-- Mild map for the auxiliary moving-frame problem (4.12). -/
def auxiliaryMildMap (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ)
    (W Wx : ℝ → ℝ → ℝ) (V Vx : ℝ → ℝ) (t x : ℝ) : ℝ :=
  movingFrameHeatOp c t Uplus x + auxiliaryDuhamel p c W Wx V Vx t x

/-- Source-bound package for the frozen-`V` auxiliary Duhamel term. -/
structure AuxiliaryFrozenSourceBound (p : CMParams)
    (W Wx : ℝ → ℝ → ℝ) (V Vx : ℝ → ℝ) (C t : ℝ) : Prop where
  nonneg : 0 ≤ C
  bound :
    ∀ s ∈ Set.Icc (0 : ℝ) t, ∀ y,
      |auxiliaryFrozenNonlinearity p (W s) (Wx s) V Vx y| ≤ C
  measurable :
    ∀ s ∈ Set.Icc (0 : ℝ) t,
      AEStronglyMeasurable
        (fun y => auxiliaryFrozenNonlinearity p (W s) (Wx s) V Vx y) volume

/-- Boundedness of the frozen-`V` auxiliary Duhamel term from a source bound. -/
theorem auxiliaryDuhamel_abs_le_of_sourceBound {p : CMParams} {c C t : ℝ}
    {W Wx : ℝ → ℝ → ℝ} {V Vx : ℝ → ℝ}
    (ht : 0 ≤ t) (H : AuxiliaryFrozenSourceBound p W Wx V Vx C t) :
    ∀ x, |auxiliaryDuhamel p c W Wx V Vx t x| ≤ C * t := by
  intro x
  simpa [auxiliaryDuhamel] using
    movingFrameDuhamel_abs_le_of_bound (c := c) (C := C) (t := t)
      (F := fun s y => auxiliaryFrozenNonlinearity p (W s) (Wx s) V Vx y)
      ht H.nonneg H.bound H.measurable x

/-- Absolute bound for the whole auxiliary mild map from initial and source bounds. -/
theorem auxiliaryMildMap_abs_le_of_sourceBound {p : CMParams} {c C M0 t : ℝ}
    {Uplus : ℝ → ℝ} {W Wx : ℝ → ℝ → ℝ} {V Vx : ℝ → ℝ}
    (hU_bound : ∀ y, |Uplus y| ≤ M0) (hM0 : 0 ≤ M0)
    (hU_meas : AEStronglyMeasurable Uplus volume)
    (ht : 0 ≤ t) (H : AuxiliaryFrozenSourceBound p W Wx V Vx C t) :
    ∀ x, |auxiliaryMildMap p c Uplus W Wx V Vx t x| ≤ M0 + C * t := by
  intro x
  have hS :=
    movingFrameHeatOp_abs_bound_of_nonneg_time
      (c := c) (t := t) (M := M0) (f := Uplus)
      hU_bound hM0 hU_meas ht x
  have hD := auxiliaryDuhamel_abs_le_of_sourceBound
    (p := p) (c := c) (C := C) (t := t)
    (W := W) (Wx := Wx) (V := V) (Vx := Vx) ht H x
  calc
    |auxiliaryMildMap p c Uplus W Wx V Vx t x|
        ≤ |movingFrameHeatOp c t Uplus x| +
            |auxiliaryDuhamel p c W Wx V Vx t x| := by
          simpa [auxiliaryMildMap] using
            abs_add_le (movingFrameHeatOp c t Uplus x)
              (auxiliaryDuhamel p c W Wx V Vx t x)
    _ ≤ M0 + C * t := add_le_add hS hD

/--
Correction inequalities sufficient for invariance of a constant trap `[lo, hi]`.
This mirrors `WholeLineConstantBarrierCorrections` for the divergence-form mild map.
-/
def AuxiliaryConstantTrapCorrections (p : CMParams) (c : ℝ)
    (W Wx : ℝ → ℝ → ℝ) (V Vx : ℝ → ℝ) (lo hi t x : ℝ) : Prop :=
  (1 - Real.exp (-t)) * lo ≤ auxiliaryDuhamel p c W Wx V Vx t x ∧
    auxiliaryDuhamel p c W Wx V Vx t x ≤ (1 - Real.exp (-t)) * hi

/-- Constant-trap preservation for the auxiliary moving-frame mild map. -/
theorem auxiliaryMildMap_mapsTo {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ}
    {W Wx : ℝ → ℝ → ℝ} {V Vx : ℝ → ℝ} {lo hi Mf t : ℝ}
    (hU_ge : ∀ x, lo ≤ Uplus x) (hU_le : ∀ x, Uplus x ≤ hi)
    (hU_bound : ∀ x, |Uplus x| ≤ Mf)
    (hU_meas : AEStronglyMeasurable Uplus volume) (ht : 0 < t)
    (hcorr : ∀ x, AuxiliaryConstantTrapCorrections p c W Wx V Vx lo hi t x) :
    ∀ x, lo ≤ auxiliaryMildMap p c Uplus W Wx V Vx t x ∧
      auxiliaryMildMap p c Uplus W Wx V Vx t x ≤ hi := by
  intro x
  have hS := movingFrameHeatOp_interval_bound
    (c := c) (f := Uplus) (lo := lo) (hi := hi) (Mf := Mf) (t := t)
    hU_ge hU_le hU_bound hU_meas ht x
  rcases hcorr x with ⟨hlo, hhi⟩
  constructor
  · unfold auxiliaryMildMap
    linarith
  · unfold auxiliaryMildMap
    linarith

/-- A time-window trap `[lo, hi]` for a profile family. -/
def AuxiliaryTrap (lo hi T : ℝ) (W : ℝ → ℝ → ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, lo ≤ W t x ∧ W t x ≤ hi

/-- Pointwise `C¹`-style distance control on the time window. -/
def AuxiliaryC1DistanceBound (T D : ℝ)
    (W Wx Z Zx : ℝ → ℝ → ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
    |W t x - Z t x| ≤ D ∧ |Wx t x - Zx t x| ≤ D

/--
Contraction/local-existence data for the auxiliary mild map on a short time
window.  The source estimates above close the semigroup and Duhamel analytic
pieces; this structure records the short-time trap invariance and the
contraction constant supplied by the surrounding Picard machinery.
-/
structure AuxiliaryMildLocalExistenceData (p : CMParams) (c : ℝ)
    (Uplus : ℝ → ℝ) (V Vx : ℝ → ℝ) (lo hi : ℝ) where
  T : ℝ
  hT_pos : 0 < T
  K : ℝ
  hK_nonneg : 0 ≤ K
  hK_lt_one : K < 1
  mapsTo :
    ∀ W Wx, AuxiliaryTrap lo hi T W →
      AuxiliaryTrap lo hi T (auxiliaryMildMap p c Uplus W Wx V Vx)
  contraction :
    ∀ W Wx Z Zx D, 0 ≤ D →
      AuxiliaryTrap lo hi T W →
      AuxiliaryTrap lo hi T Z →
      AuxiliaryC1DistanceBound T D W Wx Z Zx →
        AuxiliaryC1DistanceBound T (K * D)
          (auxiliaryMildMap p c Uplus W Wx V Vx) Wx
          (auxiliaryMildMap p c Uplus Z Zx V Vx) Zx

/-- Extract the short-time contraction statement from the auxiliary local data. -/
theorem auxiliaryMildLocalExistence_contraction
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ} {V Vx : ℝ → ℝ} {lo hi : ℝ}
    (H : AuxiliaryMildLocalExistenceData p c Uplus V Vx lo hi) :
    0 < H.T ∧ 0 ≤ H.K ∧ H.K < 1 ∧
      (∀ W Wx, AuxiliaryTrap lo hi H.T W →
        AuxiliaryTrap lo hi H.T (auxiliaryMildMap p c Uplus W Wx V Vx)) := by
  exact ⟨H.hT_pos, H.hK_nonneg, H.hK_lt_one, H.mapsTo⟩

#print axioms movingFrameHeatOp_eq_translate
#print axioms movingFrameHeatOp_eq_shifted_heat
#print axioms movingFrameHeatOp_interval_bound
#print axioms movingFrameHeatOp_abs_bound_of_nonneg_time
#print axioms movingFrameDuhamel_abs_le_of_bound
#print axioms auxiliaryDuhamel_abs_le_of_sourceBound
#print axioms auxiliaryMildMap_abs_le_of_sourceBound
#print axioms auxiliaryMildMap_mapsTo
#print axioms auxiliaryMildLocalExistence_contraction

end ShenWork.PaperOne
