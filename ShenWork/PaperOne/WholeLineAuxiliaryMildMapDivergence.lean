import ShenWork.PaperOne.WholeLineAuxiliaryExistence
import ShenWork.PaperOne.WholeLineDuhamelDifferentiation
import ShenWork.Paper1.WaveRotheStep
import Mathlib.Tactic

open MeasureTheory Filter Topology Real Set
open scoped Topology
open intervalIntegral

noncomputable section

namespace ShenWork.PaperOne

/-!
# Divergence-form auxiliary mild map

This file replaces the expanded frozen auxiliary source by the faithful
divergence form

`-χ ∂x (W^m Vx) + χ W^m (W^γ - u^γ) + W(1 - W^α)`.

The flux source `W^m Vx` is fed to the moving-frame gradient Duhamel operator.
The lower-order source is fed to the value Duhamel operator.  The pointwise
source Lipschitz constants below only use Lipschitz continuity of `r ↦ r^q` on
`[0,1]` for `q ≥ 1`; no derivative source involving `Wx` is present.
-/

/-- Unit-interval trap for a spatial profile. -/
def UnitIntervalProfile (f : ℝ → ℝ) : Prop :=
  ∀ x, f x ∈ Set.Icc (0 : ℝ) 1

/-- Value-distance control on a finite time window. -/
def AuxiliaryValueDistanceBound (T dist : ℝ)
    (W Z : ℝ → ℝ → ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, |W t x - Z t x| ≤ dist

theorem AuxiliaryC1DistanceBound.valueDistance
    {T dist : ℝ} {W Wx Z Zx : ℝ → ℝ → ℝ}
    (H : AuxiliaryC1DistanceBound T dist W Wx Z Zx) :
    AuxiliaryValueDistanceBound T dist W Z := by
  intro t ht x
  exact (H t ht x).1

private theorem abs_mul_sub_mul_le
    {a b c d : ℝ} :
    |a * b - c * d| ≤ |a| * |b - d| + |d| * |a - c| := by
  calc
    |a * b - c * d|
        = |a * (b - d) + (a - c) * d| := by ring_nf
    _ ≤ |a * (b - d)| + |(a - c) * d| := abs_add_le _ _
    _ = |a| * |b - d| + |d| * |a - c| := by
      rw [abs_mul, abs_mul, mul_comm |d|]

theorem rpow_lipschitz_on_unit {q : ℝ} (hq : 1 ≤ q) {a b : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    |a ^ q - b ^ q| ≤ q * |a - b| := by
  have hL :=
    ShenWork.Paper1.rpow_m_lipschitz_on_Icc
      (m := q) (M := (1 : ℝ)) hq (by norm_num)
  have hdist := hL.dist_le_mul a ha b hb
  rw [Real.dist_eq, Real.dist_eq] at hdist
  have hq_nonneg : 0 ≤ q := le_trans zero_le_one hq
  have hraw : |a ^ q - b ^ q| ≤ |a - b| * max q 0 := by
    simpa [ShenWork.Paper1.rpowLip, Real.coe_toNNReal, abs_sub_comm,
      sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hdist
  have hmax : max q 0 = q := max_eq_left hq_nonneg
  calc
    |a ^ q - b ^ q| ≤ |a - b| * max q 0 := hraw
    _ = q * |a - b| := by rw [hmax, mul_comm]

theorem reaction_lipschitz_on_unit {a : ℝ} (ha : 1 ≤ a) {r s : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    |r * (1 - r ^ a) - s * (1 - s ^ a)| ≤ (a + 2) * |r - s| := by
  have hL :=
    ShenWork.Paper1.reaction_lipschitz_on_Icc
      (a := a) (M := (1 : ℝ)) ha (by norm_num)
  have hdist := hL.dist_le_mul r hr s hs
  rw [Real.dist_eq, Real.dist_eq] at hdist
  have hraw :
      |r * (1 - r ^ a) - s * (1 - s ^ a)|
        ≤ |r - s| * max (1 + (a + 1)) 0 := by
    simpa [ShenWork.Paper1.reactionFun, ShenWork.Paper1.reactionLip,
      Real.coe_toNNReal, abs_sub_comm, sub_eq_add_neg, mul_comm, mul_left_comm,
      mul_assoc] using hdist
  have hmax : max (1 + (a + 1)) 0 = a + 2 := by
    rw [max_eq_left]
    · ring
    · linarith
  calc
    |r * (1 - r ^ a) - s * (1 - s ^ a)|
        ≤ |r - s| * max (1 + (a + 1)) 0 := hraw
    _ = (a + 2) * |r - s| := by rw [hmax, mul_comm]

/-- Divergence-form chemotaxis flux source, depending on `W` but not on `Wx`. -/
def auxiliaryDivergenceChemSource (p : CMParams)
    (W V Vx : ℝ → ℝ) : ℝ → ℝ :=
  let _keepV := V
  fun y => (W y) ^ p.m * Vx y

/-- Lower-order source in the divergence-form auxiliary equation. -/
def auxiliaryValueSource (p : CMParams)
    (W u : ℝ → ℝ) : ℝ → ℝ :=
  fun y =>
    p.χ * (W y) ^ p.m * ((W y) ^ p.γ - (u y) ^ p.γ) +
      W y * (1 - (W y) ^ p.α)

/-- Gradient-Duhamel term for the divergence chemotaxis flux. -/
def auxiliaryDivergenceChemDuhamel (p : CMParams) (c : ℝ)
    (W : ℝ → ℝ → ℝ) (V Vx : ℝ → ℝ) (t x : ℝ) : ℝ :=
  movingFrameGradDuhamel c
    (fun s y => auxiliaryDivergenceChemSource p (W s) V Vx y) t x

/-- Value-Duhamel term for the lower-order divergence-form auxiliary source. -/
def auxiliaryValueDuhamelDiv (p : CMParams) (c : ℝ)
    (W : ℝ → ℝ → ℝ) (u : ℝ → ℝ) (t x : ℝ) : ℝ :=
  movingFrameDuhamel c
    (fun s y => auxiliaryValueSource p (W s) u y) t x

/-- Divergence-form moving-frame auxiliary mild map. -/
def auxiliaryMildMapDiv (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ) (V Vx u : ℝ → ℝ) (t x : ℝ) : ℝ :=
  movingFrameHeatOp c t Uplus x
    - p.χ * auxiliaryDivergenceChemDuhamel p c W V Vx t x
    + auxiliaryValueDuhamelDiv p c W u t x

/-- Difference of two divergence chemotaxis flux sources. -/
def auxiliaryDivergenceChemSourceDiff (p : CMParams)
    (W Z : ℝ → ℝ → ℝ) (V Vx : ℝ → ℝ) (s y : ℝ) : ℝ :=
  auxiliaryDivergenceChemSource p (W s) V Vx y -
    auxiliaryDivergenceChemSource p (Z s) V Vx y

/-- Difference of two lower-order value sources. -/
def auxiliaryValueSourceDiff (p : CMParams)
    (W Z : ℝ → ℝ → ℝ) (u : ℝ → ℝ) (s y : ℝ) : ℝ :=
  auxiliaryValueSource p (W s) u y -
    auxiliaryValueSource p (Z s) u y

/-- Flux-source Lipschitz constant on the unit trap. -/
def auxiliaryDivergenceChemSourceLipConst (p : CMParams) (CVx : ℝ) : ℝ :=
  p.m * CVx

/-- Lower-order source Lipschitz constant on the unit trap. -/
def auxiliaryValueSourceLipConst (p : CMParams) : ℝ :=
  |p.χ| * (p.γ + 2 * p.m) + (p.α + 2)

theorem auxiliaryDivergenceChemSourceLipConst_nonneg
    (p : CMParams) {CVx : ℝ} (hCVx : 0 ≤ CVx) :
    0 ≤ auxiliaryDivergenceChemSourceLipConst p CVx := by
  unfold auxiliaryDivergenceChemSourceLipConst
  exact mul_nonneg (le_trans zero_le_one p.hm) hCVx

theorem auxiliaryValueSourceLipConst_nonneg (p : CMParams) :
    0 ≤ auxiliaryValueSourceLipConst p := by
  unfold auxiliaryValueSourceLipConst
  have hm : 0 ≤ p.m := le_trans zero_le_one p.hm
  have hγ : 0 ≤ p.γ := le_trans zero_le_one p.hγ
  have hα2 : 0 ≤ p.α + 2 := by linarith [p.hα]
  have hcore : 0 ≤ p.γ + 2 * p.m := by nlinarith
  exact add_nonneg (mul_nonneg (abs_nonneg p.χ) hcore) hα2

private theorem rpow_abs_le_one_of_unit
    {q a : ℝ} (hq : 0 ≤ q) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    |a ^ q| ≤ 1 := by
  have hnonneg : 0 ≤ a ^ q := Real.rpow_nonneg ha.1 q
  have hle : a ^ q ≤ (1 : ℝ) ^ q :=
    Real.rpow_le_rpow ha.1 ha.2 hq
  simpa [abs_of_nonneg hnonneg] using hle

private theorem unit_rpow_sub_abs_le_two
    {q a b : ℝ} (hq : 0 ≤ q)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    |a ^ q - b ^ q| ≤ 2 := by
  have ha1 : |a ^ q| ≤ 1 := rpow_abs_le_one_of_unit hq ha
  have hb1 : |b ^ q| ≤ 1 := rpow_abs_le_one_of_unit hq hb
  calc
    |a ^ q - b ^ q| = |a ^ q + -(b ^ q)| := by ring_nf
    _ ≤ |a ^ q| + |-(b ^ q)| := abs_add_le _ _
    _ = |a ^ q| + |b ^ q| := by rw [abs_neg]
    _ ≤ 1 + 1 := add_le_add ha1 hb1
    _ = 2 := by norm_num

theorem auxiliaryDivergenceChemSource_lipschitz_pointwise
    {p : CMParams} {W Z V Vx : ℝ → ℝ} {CVx dist : ℝ}
    (hCVx : 0 ≤ CVx) (hVx : ∀ y, |Vx y| ≤ CVx)
    (hW : UnitIntervalProfile W) (hZ : UnitIntervalProfile Z)
    (hdist_nonneg : 0 ≤ dist)
    (hdist : ∀ y, |W y - Z y| ≤ dist) :
    ∀ y,
      |auxiliaryDivergenceChemSource p W V Vx y -
        auxiliaryDivergenceChemSource p Z V Vx y|
        ≤ auxiliaryDivergenceChemSourceLipConst p CVx * dist := by
  intro y
  have _hLip_nonneg : 0 ≤ auxiliaryDivergenceChemSourceLipConst p CVx :=
    auxiliaryDivergenceChemSourceLipConst_nonneg p hCVx
  have hm_nonneg : 0 ≤ p.m := le_trans zero_le_one p.hm
  have hpow :
      |(W y) ^ p.m - (Z y) ^ p.m| ≤ p.m * dist := by
    exact (rpow_lipschitz_on_unit p.hm (hW y) (hZ y)).trans
      (mul_le_mul_of_nonneg_left (hdist y) hm_nonneg)
  have hpowdist_nonneg : 0 ≤ p.m * dist := mul_nonneg hm_nonneg hdist_nonneg
  unfold auxiliaryDivergenceChemSource auxiliaryDivergenceChemSourceLipConst
  have hfact :
      (W y) ^ p.m * Vx y - (Z y) ^ p.m * Vx y =
        ((W y) ^ p.m - (Z y) ^ p.m) * Vx y := by ring
  rw [hfact, abs_mul]
  calc
    |(W y) ^ p.m - (Z y) ^ p.m| * |Vx y|
        ≤ (p.m * dist) * CVx :=
          mul_le_mul hpow (hVx y) (abs_nonneg _) hpowdist_nonneg
    _ = p.m * CVx * dist := by ring

theorem auxiliaryValueSource_lipschitz_pointwise
    {p : CMParams} {W Z u : ℝ → ℝ} {dist : ℝ}
    (hW : UnitIntervalProfile W) (hZ : UnitIntervalProfile Z)
    (hu : UnitIntervalProfile u)
    (hdist_nonneg : 0 ≤ dist)
    (hdist : ∀ y, |W y - Z y| ≤ dist) :
    ∀ y,
      |auxiliaryValueSource p W u y - auxiliaryValueSource p Z u y|
        ≤ auxiliaryValueSourceLipConst p * dist := by
  intro y
  have hm_nonneg : 0 ≤ p.m := le_trans zero_le_one p.hm
  have hγ_nonneg : 0 ≤ p.γ := le_trans zero_le_one p.hγ
  have hWm_abs : |(W y) ^ p.m| ≤ 1 :=
    rpow_abs_le_one_of_unit hm_nonneg (hW y)
  have hZγ_uγ_abs :
      |(Z y) ^ p.γ - (u y) ^ p.γ| ≤ 2 :=
    unit_rpow_sub_abs_le_two hγ_nonneg (hZ y) (hu y)
  have hpow_m :
      |(W y) ^ p.m - (Z y) ^ p.m| ≤ p.m * dist := by
    exact (rpow_lipschitz_on_unit p.hm (hW y) (hZ y)).trans
      (mul_le_mul_of_nonneg_left (hdist y) hm_nonneg)
  have hpow_γ :
      |(W y) ^ p.γ - (Z y) ^ p.γ| ≤ p.γ * dist := by
    exact (rpow_lipschitz_on_unit p.hγ (hW y) (hZ y)).trans
      (mul_le_mul_of_nonneg_left (hdist y) hγ_nonneg)
  have hm_dist_nonneg : 0 ≤ p.m * dist := mul_nonneg hm_nonneg hdist_nonneg
  have hγ_dist_nonneg : 0 ≤ p.γ * dist := mul_nonneg hγ_nonneg hdist_nonneg
  have hcore :
      |(W y) ^ p.m * ((W y) ^ p.γ - (u y) ^ p.γ) -
        (Z y) ^ p.m * ((Z y) ^ p.γ - (u y) ^ p.γ)|
        ≤ (p.γ + 2 * p.m) * dist := by
    have hsplit :=
      abs_mul_sub_mul_le
        (a := (W y) ^ p.m)
        (b := (W y) ^ p.γ - (u y) ^ p.γ)
        (c := (Z y) ^ p.m)
        (d := (Z y) ^ p.γ - (u y) ^ p.γ)
    have hterm1 :
        |(W y) ^ p.m| *
          |((W y) ^ p.γ - (u y) ^ p.γ) -
            ((Z y) ^ p.γ - (u y) ^ p.γ)|
          ≤ 1 * (p.γ * dist) := by
      have hdiff :
          |((W y) ^ p.γ - (u y) ^ p.γ) -
            ((Z y) ^ p.γ - (u y) ^ p.γ)|
            = |(W y) ^ p.γ - (Z y) ^ p.γ| := by ring_nf
      rw [hdiff]
      exact mul_le_mul hWm_abs hpow_γ (abs_nonneg _) (by norm_num)
    have hterm2 :
        |(Z y) ^ p.γ - (u y) ^ p.γ| *
          |(W y) ^ p.m - (Z y) ^ p.m|
          ≤ 2 * (p.m * dist) := by
      exact mul_le_mul hZγ_uγ_abs hpow_m (abs_nonneg _) (by norm_num)
    calc
      |(W y) ^ p.m * ((W y) ^ p.γ - (u y) ^ p.γ) -
        (Z y) ^ p.m * ((Z y) ^ p.γ - (u y) ^ p.γ)|
          ≤
            |(W y) ^ p.m| *
              |((W y) ^ p.γ - (u y) ^ p.γ) -
                ((Z y) ^ p.γ - (u y) ^ p.γ)| +
            |(Z y) ^ p.γ - (u y) ^ p.γ| *
              |(W y) ^ p.m - (Z y) ^ p.m| := hsplit
      _ ≤ 1 * (p.γ * dist) + 2 * (p.m * dist) :=
          add_le_add hterm1 hterm2
      _ = (p.γ + 2 * p.m) * dist := by ring
  have hreaction :
      |W y * (1 - (W y) ^ p.α) - Z y * (1 - (Z y) ^ p.α)|
        ≤ (p.α + 2) * dist := by
    exact (reaction_lipschitz_on_unit p.hα (hW y) (hZ y)).trans
      (mul_le_mul_of_nonneg_left (hdist y) (by linarith [p.hα]))
  unfold auxiliaryValueSource auxiliaryValueSourceLipConst
  have hdecomp :
      (p.χ * (W y) ^ p.m * ((W y) ^ p.γ - (u y) ^ p.γ) +
          W y * (1 - (W y) ^ p.α))
        -
        (p.χ * (Z y) ^ p.m * ((Z y) ^ p.γ - (u y) ^ p.γ) +
          Z y * (1 - (Z y) ^ p.α))
      =
        p.χ *
          ((W y) ^ p.m * ((W y) ^ p.γ - (u y) ^ p.γ) -
            (Z y) ^ p.m * ((Z y) ^ p.γ - (u y) ^ p.γ))
        +
        (W y * (1 - (W y) ^ p.α) -
          Z y * (1 - (Z y) ^ p.α)) := by ring
  rw [hdecomp]
  calc
    |p.χ *
          ((W y) ^ p.m * ((W y) ^ p.γ - (u y) ^ p.γ) -
            (Z y) ^ p.m * ((Z y) ^ p.γ - (u y) ^ p.γ))
        +
        (W y * (1 - (W y) ^ p.α) -
          Z y * (1 - (Z y) ^ p.α))|
        ≤
          |p.χ *
            ((W y) ^ p.m * ((W y) ^ p.γ - (u y) ^ p.γ) -
              (Z y) ^ p.m * ((Z y) ^ p.γ - (u y) ^ p.γ))| +
          |W y * (1 - (W y) ^ p.α) -
            Z y * (1 - (Z y) ^ p.α)| := abs_add_le _ _
    _ ≤ |p.χ| * ((p.γ + 2 * p.m) * dist) + (p.α + 2) * dist := by
          rw [abs_mul]
          exact add_le_add
            (mul_le_mul_of_nonneg_left hcore (abs_nonneg p.χ))
            hreaction
    _ = (|p.χ| * (p.γ + 2 * p.m) + (p.α + 2)) * dist := by ring

/-- Both divergence-form sources are Lipschitz in `W` on the unit trap. -/
theorem auxiliaryDivSource_lipschitz
    {p : CMParams} {W Z V Vx u : ℝ → ℝ} {CVx dist : ℝ}
    (hCVx : 0 ≤ CVx) (hVx : ∀ y, |Vx y| ≤ CVx)
    (hW : UnitIntervalProfile W) (hZ : UnitIntervalProfile Z)
    (hu : UnitIntervalProfile u)
    (hdist_nonneg : 0 ≤ dist)
    (hdist : ∀ y, |W y - Z y| ≤ dist) :
    (∀ y,
      |auxiliaryDivergenceChemSource p W V Vx y -
        auxiliaryDivergenceChemSource p Z V Vx y|
        ≤ auxiliaryDivergenceChemSourceLipConst p CVx * dist) ∧
    (∀ y,
      |auxiliaryValueSource p W u y - auxiliaryValueSource p Z u y|
        ≤ auxiliaryValueSourceLipConst p * dist) := by
  exact
    ⟨auxiliaryDivergenceChemSource_lipschitz_pointwise
        hCVx hVx hW hZ hdist_nonneg hdist,
      auxiliaryValueSource_lipschitz_pointwise
        hW hZ hu hdist_nonneg hdist⟩

theorem auxiliaryDivergenceChemSourceDiff_bound_of_trap
    {p : CMParams} {V Vx : ℝ → ℝ}
    {κ κt D CVx : ℝ}
    (hCVx : 0 ≤ CVx) (hVx : ∀ y, |Vx y| ≤ CVx) :
    ∀ T W Z dist, 0 ≤ dist →
      AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T Z →
      AuxiliaryValueDistanceBound T dist W Z →
        ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y,
          |auxiliaryDivergenceChemSourceDiff p W Z V Vx s y|
            ≤ auxiliaryDivergenceChemSourceLipConst p CVx * dist := by
  intro T W Z dist hdist hW hZ hdistWZ s hs y
  unfold auxiliaryDivergenceChemSourceDiff
  exact
    auxiliaryDivergenceChemSource_lipschitz_pointwise
      (p := p) (W := W s) (Z := Z s) (V := V) (Vx := Vx)
      (CVx := CVx) (dist := dist)
      hCVx hVx
      (fun z => ⟨auxiliaryBarrierTrap_nonneg hW s hs z,
        auxiliaryBarrierTrap_le_one hW s hs z⟩)
      (fun z => ⟨auxiliaryBarrierTrap_nonneg hZ s hs z,
        auxiliaryBarrierTrap_le_one hZ s hs z⟩)
      hdist (fun z => hdistWZ s hs z) y

theorem auxiliaryValueSourceDiff_bound_of_trap
    {p : CMParams} {u : ℝ → ℝ}
    {κ κt D : ℝ}
    (hu : UnitIntervalProfile u) :
    ∀ T W Z dist, 0 ≤ dist →
      AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T Z →
      AuxiliaryValueDistanceBound T dist W Z →
        ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y,
          |auxiliaryValueSourceDiff p W Z u s y|
            ≤ auxiliaryValueSourceLipConst p * dist := by
  intro T W Z dist hdist hW hZ hdistWZ s hs y
  unfold auxiliaryValueSourceDiff
  exact
    auxiliaryValueSource_lipschitz_pointwise
      (p := p) (W := W s) (Z := Z s) (u := u) (dist := dist)
      (fun z => ⟨auxiliaryBarrierTrap_nonneg hW s hs z,
        auxiliaryBarrierTrap_le_one hW s hs z⟩)
      (fun z => ⟨auxiliaryBarrierTrap_nonneg hZ s hs z,
        auxiliaryBarrierTrap_le_one hZ s hs z⟩)
      hu hdist (fun z => hdistWZ s hs z) y

/-- Gradient-Duhamel rate generated by a bounded source difference. -/
def auxiliaryDivMovingFrameGradientRate (B : ℝ) : ℝ :=
  4 * B / Real.sqrt (4 * Real.pi)

theorem auxiliaryDivMovingFrameGradientRate_nonneg {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ auxiliaryDivMovingFrameGradientRate B := by
  unfold auxiliaryDivMovingFrameGradientRate
  exact div_nonneg (mul_nonneg (by norm_num) hB) (Real.sqrt_nonneg _)

/-- The divergence flux contribution to the mild-map value Lipschitz rate. -/
def auxiliaryMildMapDivGradientRate (p : CMParams) (CVx : ℝ) : ℝ :=
  |p.χ| *
    auxiliaryDivMovingFrameGradientRate
      (auxiliaryDivergenceChemSourceLipConst p CVx)

theorem auxiliaryMildMapDivGradientRate_nonneg
    (p : CMParams) {CVx : ℝ} (hCVx : 0 ≤ CVx) :
    0 ≤ auxiliaryMildMapDivGradientRate p CVx := by
  unfold auxiliaryMildMapDivGradientRate
  exact mul_nonneg (abs_nonneg p.χ)
    (auxiliaryDivMovingFrameGradientRate_nonneg
      (auxiliaryDivergenceChemSourceLipConst_nonneg p hCVx))

theorem auxiliaryValueSourceDiffDuhamel_abs_le
    {p : CMParams} {c : ℝ} {u : ℝ → ℝ}
    {κ κt D B : ℝ}
    (hB : 0 ≤ B)
    (source_bound :
      ∀ T W Z dist, 0 ≤ dist →
        AuxiliaryBarrierTrap κ κt D T W →
        AuxiliaryBarrierTrap κ κt D T Z →
        AuxiliaryValueDistanceBound T dist W Z →
          ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y,
            |auxiliaryValueSourceDiff p W Z u s y| ≤ B * dist)
    (source_measurable :
      ∀ T W Z dist, 0 ≤ dist →
        AuxiliaryBarrierTrap κ κt D T W →
        AuxiliaryBarrierTrap κ κt D T Z →
        AuxiliaryValueDistanceBound T dist W Z →
          ∀ t ∈ Set.Icc (0 : ℝ) T,
            ∀ s ∈ Set.Icc (0 : ℝ) t,
              AEStronglyMeasurable
                (fun y => auxiliaryValueSourceDiff p W Z u s y) volume) :
    ∀ T W Z dist, 0 ≤ dist →
      AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T Z →
      AuxiliaryValueDistanceBound T dist W Z →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
          |movingFrameDuhamel c
            (fun s y => auxiliaryValueSourceDiff p W Z u s y) t x|
            ≤ B * T * dist := by
  intro T W Z dist hdist hW hZ hdistWZ t ht x
  have hC : 0 ≤ B * dist := mul_nonneg hB hdist
  have hduh :
      |movingFrameDuhamel c
          (fun s y => auxiliaryValueSourceDiff p W Z u s y) t x|
        ≤ (B * dist) * t := by
    refine movingFrameDuhamel_abs_le_of_bound
      (c := c) (C := B * dist) (t := t)
      (F := fun s y => auxiliaryValueSourceDiff p W Z u s y)
      ht.1 hC ?_ ?_ x
    · intro s hs y
      have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1, le_trans hs.2 ht.2⟩
      exact source_bound T W Z dist hdist hW hZ hdistWZ s hsT y
    · intro s hs
      exact source_measurable T W Z dist hdist hW hZ hdistWZ t ht s hs
  have hBT : B * t ≤ B * T := mul_le_mul_of_nonneg_left ht.2 hB
  have hBTdist : B * t * dist ≤ B * T * dist :=
    mul_le_mul_of_nonneg_right hBT hdist
  calc
    |movingFrameDuhamel c
        (fun s y => auxiliaryValueSourceDiff p W Z u s y) t x|
        ≤ (B * dist) * t := hduh
    _ = B * t * dist := by ring
    _ ≤ B * T * dist := hBTdist

theorem auxiliaryDivergenceChemSourceDiffGradDuhamel_abs_le
    {p : CMParams} {c : ℝ} {V Vx : ℝ → ℝ}
    {κ κt D B : ℝ}
    (hB : 0 ≤ B)
    (source_bound :
      ∀ T W Z dist, 0 ≤ dist →
        AuxiliaryBarrierTrap κ κt D T W →
        AuxiliaryBarrierTrap κ κt D T Z →
        AuxiliaryValueDistanceBound T dist W Z →
          ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y,
            |auxiliaryDivergenceChemSourceDiff p W Z V Vx s y| ≤ B * dist)
    (grad_integrable :
      ∀ T W Z dist, 0 ≤ dist →
        AuxiliaryBarrierTrap κ κt D T W →
        AuxiliaryBarrierTrap κ κt D T Z →
        AuxiliaryValueDistanceBound T dist W Z →
          ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
            IntervalIntegrable
              (fun s : ℝ =>
                movingFrameHeatGradOp c (t - s)
                  (fun y => auxiliaryDivergenceChemSourceDiff p W Z V Vx s y) x)
              volume 0 t) :
    ∀ T W Z dist, 0 ≤ dist →
      AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T Z →
      AuxiliaryValueDistanceBound T dist W Z →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
          |movingFrameGradDuhamel c
            (fun s y => auxiliaryDivergenceChemSourceDiff p W Z V Vx s y) t x|
            ≤ auxiliaryDivMovingFrameGradientRate B * Real.sqrt T * dist := by
  intro T W Z dist hdist hW hZ hdistWZ t ht x
  by_cases ht0 : t = 0
  · subst t
    have hrate_nonneg : 0 ≤ auxiliaryDivMovingFrameGradientRate B :=
      auxiliaryDivMovingFrameGradientRate_nonneg hB
    have hnonneg :
        0 ≤ auxiliaryDivMovingFrameGradientRate B * Real.sqrt T * dist :=
      mul_nonneg (mul_nonneg hrate_nonneg (Real.sqrt_nonneg T)) hdist
    simp [movingFrameGradDuhamel, hnonneg]
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hrate_nonneg : 0 ≤ auxiliaryDivMovingFrameGradientRate B :=
      auxiliaryDivMovingFrameGradientRate_nonneg hB
    have hgrad :=
      movingFrameGradDuhamel_abs_le_sqrt_of_slice_bound
        (c := c)
        (A := (auxiliaryDivMovingFrameGradientRate B * dist) / 2)
        (t := t)
        (F := fun s y => auxiliaryDivergenceChemSourceDiff p W Z V Vx s y)
        htpos x
        (grad_integrable T W Z dist hdist hW hZ hdistWZ t ht x)
        ?_
    · have hsqr : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt ht.2
      have hrate_dist_nonneg :
          0 ≤ auxiliaryDivMovingFrameGradientRate B * dist :=
        mul_nonneg hrate_nonneg hdist
      have hmul :
          (auxiliaryDivMovingFrameGradientRate B * dist) * Real.sqrt t
            ≤ (auxiliaryDivMovingFrameGradientRate B * dist) * Real.sqrt T :=
        mul_le_mul_of_nonneg_left hsqr hrate_dist_nonneg
      calc
        |movingFrameGradDuhamel c
          (fun s y => auxiliaryDivergenceChemSourceDiff p W Z V Vx s y) t x|
            ≤ ((auxiliaryDivMovingFrameGradientRate B * dist) / 2) *
                (2 * Real.sqrt t) := hgrad
        _ = (auxiliaryDivMovingFrameGradientRate B * dist) * Real.sqrt t := by ring
        _ ≤ (auxiliaryDivMovingFrameGradientRate B * dist) * Real.sqrt T := hmul
        _ = auxiliaryDivMovingFrameGradientRate B * Real.sqrt T * dist := by ring
    · intro s hs0 hst
      have hsT : s ∈ Set.Icc (0 : ℝ) T :=
        ⟨hs0, le_trans (le_of_lt hst) ht.2⟩
      have hM : 0 ≤ B * dist := mul_nonneg hB hdist
      have hbase :=
        movingFrameHeatGradOp_norm_le_rpow
          (c := c)
          (τ := t - s)
          (M := B * dist)
          (f := fun y => auxiliaryDivergenceChemSourceDiff p W Z V Vx s y)
          (sub_pos.mpr hst)
          hM
          (source_bound T W Z dist hdist hW hZ hdistWZ s hsT)
          x
      calc
        |movingFrameHeatGradOp c (t - s)
          (fun y => auxiliaryDivergenceChemSourceDiff p W Z V Vx s y) x|
            = ‖movingFrameHeatGradOp c (t - s)
                (fun y => auxiliaryDivergenceChemSourceDiff p W Z V Vx s y) x‖ := by
                rw [Real.norm_eq_abs]
        _ ≤ ((2 / Real.sqrt (4 * Real.pi)) * (B * dist)) *
            (t - s) ^ (-(1 / 2 : ℝ)) := hbase
        _ = (((auxiliaryDivMovingFrameGradientRate B) * dist) / 2) *
            (t - s) ^ (-(1 / 2 : ℝ)) := by
            unfold auxiliaryDivMovingFrameGradientRate
            ring_nf

/-- Exact maps-to frontier for the divergence-form auxiliary mild map. -/
def AuxiliaryMildMapDivMapsToFrontier
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx u : ℝ → ℝ)
    (κ κt D A B : ℝ) : Prop :=
  ∀ T, 0 < T → A * Real.sqrt T + B * T < 1 →
    ∀ W, AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T
        (auxiliaryMildMapDiv p c Uplus W V Vx u)

/-- Value contraction frontier for the divergence-form auxiliary mild map. -/
def AuxiliaryMildMapDivValueDiffFrontier
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx u : ℝ → ℝ)
    (κ κt D A B : ℝ) : Prop :=
  ∀ T, 0 < T → A * Real.sqrt T + B * T < 1 →
    ∀ W Z dist, 0 ≤ dist →
      AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T Z →
      AuxiliaryValueDistanceBound T dist W Z →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
          |auxiliaryMildMapDiv p c Uplus W V Vx u t x -
            auxiliaryMildMapDiv p c Uplus Z V Vx u t x| ≤
              (A * Real.sqrt T + B * T) * dist

/-- Rate estimates for the divergence-form auxiliary mild map. -/
structure AuxiliaryMildMapDivRateEstimates
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx u : ℝ → ℝ)
    (κ κt D A B : ℝ) : Prop where
  hA_nonneg : 0 ≤ A
  hB_nonneg : 0 ≤ B
  mapsTo_of_small :
    AuxiliaryMildMapDivMapsToFrontier p c Uplus V Vx u κ κt D A B
  value_diff_of_small :
    AuxiliaryMildMapDivValueDiffFrontier p c Uplus V Vx u κ κt D A B

/-- Concrete, satisfiable bottom data for the divergence-form rate package. -/
structure AuxiliaryMildMapDivRateData
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ) (V Vx u : ℝ → ℝ)
    (κ κt D CVx : ℝ) : Prop where
  CVx_nonneg : 0 ≤ CVx
  Vx_bound : ∀ y, |Vx y| ≤ CVx
  u_unit : UnitIntervalProfile u
  mapsTo :
    AuxiliaryMildMapDivMapsToFrontier p c Uplus V Vx u κ κt D
      (auxiliaryMildMapDivGradientRate p CVx)
      (auxiliaryValueSourceLipConst p)
  value_source_measurable :
    ∀ T W Z dist, 0 ≤ dist →
      AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T Z →
      AuxiliaryValueDistanceBound T dist W Z →
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          ∀ s ∈ Set.Icc (0 : ℝ) t,
            AEStronglyMeasurable
              (fun y => auxiliaryValueSourceDiff p W Z u s y) volume
  value_duhamel_sub :
    ∀ T W Z dist, 0 ≤ dist →
      AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T Z →
      AuxiliaryValueDistanceBound T dist W Z →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
          auxiliaryValueDuhamelDiv p c W u t x -
              auxiliaryValueDuhamelDiv p c Z u t x =
            movingFrameDuhamel c
              (fun s y => auxiliaryValueSourceDiff p W Z u s y) t x
  div_grad_integrable :
    ∀ T W Z dist, 0 ≤ dist →
      AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T Z →
      AuxiliaryValueDistanceBound T dist W Z →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
          IntervalIntegrable
            (fun s : ℝ =>
              movingFrameHeatGradOp c (t - s)
                (fun y => auxiliaryDivergenceChemSourceDiff p W Z V Vx s y) x)
            volume 0 t
  div_grad_duhamel_sub :
    ∀ T W Z dist, 0 ≤ dist →
      AuxiliaryBarrierTrap κ κt D T W →
      AuxiliaryBarrierTrap κ κt D T Z →
      AuxiliaryValueDistanceBound T dist W Z →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
          auxiliaryDivergenceChemDuhamel p c W V Vx t x -
              auxiliaryDivergenceChemDuhamel p c Z V Vx t x =
            movingFrameGradDuhamel c
              (fun s y => auxiliaryDivergenceChemSourceDiff p W Z V Vx s y) t x

theorem auxiliaryMildMapDiv_valueDiffFrontier_of_rateData
    {p : CMParams} {c : ℝ} {Uplus V Vx u : ℝ → ℝ}
    {κ κt D CVx : ℝ}
    (H : AuxiliaryMildMapDivRateData p c Uplus V Vx u κ κt D CVx) :
    AuxiliaryMildMapDivValueDiffFrontier p c Uplus V Vx u κ κt D
      (auxiliaryMildMapDivGradientRate p CVx)
      (auxiliaryValueSourceLipConst p) := by
  intro T hT _hsmall W Z dist hdist hW hZ hdistWZ t ht x
  let Ldiv := auxiliaryDivergenceChemSourceLipConst p CVx
  let A0 := auxiliaryDivMovingFrameGradientRate Ldiv
  let A := auxiliaryMildMapDivGradientRate p CVx
  let B := auxiliaryValueSourceLipConst p
  have hLdiv_nonneg : 0 ≤ Ldiv := by
    dsimp [Ldiv]
    exact auxiliaryDivergenceChemSourceLipConst_nonneg p H.CVx_nonneg
  have hA0_nonneg : 0 ≤ A0 := by
    dsimp [A0]
    exact auxiliaryDivMovingFrameGradientRate_nonneg hLdiv_nonneg
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact auxiliaryValueSourceLipConst_nonneg p
  have hdiv_bound :
      |movingFrameGradDuhamel c
        (fun s y => auxiliaryDivergenceChemSourceDiff p W Z V Vx s y) t x|
        ≤ A0 * Real.sqrt T * dist := by
    dsimp [A0, Ldiv]
    exact
      auxiliaryDivergenceChemSourceDiffGradDuhamel_abs_le
        (p := p) (c := c) (V := V) (Vx := Vx)
        (κ := κ) (κt := κt) (D := D)
        (B := auxiliaryDivergenceChemSourceLipConst p CVx)
        hLdiv_nonneg
        (auxiliaryDivergenceChemSourceDiff_bound_of_trap
          (p := p) (V := V) (Vx := Vx)
          (κ := κ) (κt := κt) (D := D)
          H.CVx_nonneg H.Vx_bound)
        H.div_grad_integrable
        T W Z dist hdist hW hZ hdistWZ t ht x
  have hdiv_sub :=
    H.div_grad_duhamel_sub T W Z dist hdist hW hZ hdistWZ t ht x
  have hval_bound :
      |movingFrameDuhamel c
        (fun s y => auxiliaryValueSourceDiff p W Z u s y) t x|
        ≤ B * T * dist := by
    dsimp [B]
    exact
      auxiliaryValueSourceDiffDuhamel_abs_le
        (p := p) (c := c) (u := u)
        (κ := κ) (κt := κt) (D := D)
        (B := auxiliaryValueSourceLipConst p)
        hB_nonneg
        (auxiliaryValueSourceDiff_bound_of_trap
          (p := p) (u := u) (κ := κ) (κt := κt) (D := D) H.u_unit)
        H.value_source_measurable
        T W Z dist hdist hW hZ hdistWZ t ht x
  have hval_sub :=
    H.value_duhamel_sub T W Z dist hdist hW hZ hdistWZ t ht x
  have hcancel :
      auxiliaryMildMapDiv p c Uplus W V Vx u t x -
          auxiliaryMildMapDiv p c Uplus Z V Vx u t x =
        -p.χ *
            (auxiliaryDivergenceChemDuhamel p c W V Vx t x -
              auxiliaryDivergenceChemDuhamel p c Z V Vx t x)
          +
            (auxiliaryValueDuhamelDiv p c W u t x -
              auxiliaryValueDuhamelDiv p c Z u t x) := by
    unfold auxiliaryMildMapDiv
    ring
  calc
    |auxiliaryMildMapDiv p c Uplus W V Vx u t x -
        auxiliaryMildMapDiv p c Uplus Z V Vx u t x|
        =
      |-p.χ *
          (auxiliaryDivergenceChemDuhamel p c W V Vx t x -
            auxiliaryDivergenceChemDuhamel p c Z V Vx t x)
        +
          (auxiliaryValueDuhamelDiv p c W u t x -
            auxiliaryValueDuhamelDiv p c Z u t x)| := by rw [hcancel]
    _ =
      |-p.χ *
          movingFrameGradDuhamel c
            (fun s y => auxiliaryDivergenceChemSourceDiff p W Z V Vx s y) t x
        +
          movingFrameDuhamel c
            (fun s y => auxiliaryValueSourceDiff p W Z u s y) t x| := by
          rw [hdiv_sub, hval_sub]
    _ ≤
        |p.χ| *
          |movingFrameGradDuhamel c
            (fun s y => auxiliaryDivergenceChemSourceDiff p W Z V Vx s y) t x| +
        |movingFrameDuhamel c
            (fun s y => auxiliaryValueSourceDiff p W Z u s y) t x| := by
          calc
            |-p.χ *
                movingFrameGradDuhamel c
                  (fun s y => auxiliaryDivergenceChemSourceDiff p W Z V Vx s y) t x
              +
                movingFrameDuhamel c
                  (fun s y => auxiliaryValueSourceDiff p W Z u s y) t x|
                ≤
                  |-p.χ *
                    movingFrameGradDuhamel c
                      (fun s y => auxiliaryDivergenceChemSourceDiff p W Z V Vx s y) t x| +
                  |movingFrameDuhamel c
                    (fun s y => auxiliaryValueSourceDiff p W Z u s y) t x| :=
                    abs_add_le _ _
            _ =
                  |p.χ| *
                    |movingFrameGradDuhamel c
                      (fun s y => auxiliaryDivergenceChemSourceDiff p W Z V Vx s y) t x| +
                  |movingFrameDuhamel c
                    (fun s y => auxiliaryValueSourceDiff p W Z u s y) t x| := by
                  rw [abs_mul, abs_neg]
    _ ≤ |p.χ| * (A0 * Real.sqrt T * dist) + B * T * dist :=
          add_le_add
            (mul_le_mul_of_nonneg_left hdiv_bound (abs_nonneg p.χ))
            hval_bound
    _ = (A * Real.sqrt T + B * T) * dist := by
          dsimp [A, A0, Ldiv, B, auxiliaryMildMapDivGradientRate]
          ring

/-- Final divergence-form rate package, with only satisfiable bottom conditions. -/
theorem auxiliaryMildMapDiv_rateEstimates
    {p : CMParams} {c : ℝ} {Uplus V Vx u : ℝ → ℝ}
    {κ κt D CVx : ℝ}
    (H : AuxiliaryMildMapDivRateData p c Uplus V Vx u κ κt D CVx) :
    AuxiliaryMildMapDivRateEstimates p c Uplus V Vx u κ κt D
      (auxiliaryMildMapDivGradientRate p CVx)
      (auxiliaryValueSourceLipConst p) where
  hA_nonneg := auxiliaryMildMapDivGradientRate_nonneg p H.CVx_nonneg
  hB_nonneg := auxiliaryValueSourceLipConst_nonneg p
  mapsTo_of_small := H.mapsTo
  value_diff_of_small := auxiliaryMildMapDiv_valueDiffFrontier_of_rateData H

#check auxiliaryDivergenceChemSource
#check auxiliaryValueSource
#check auxiliaryMildMapDiv
#check auxiliaryDivSource_lipschitz
#check auxiliaryMildMapDiv_rateEstimates

#print axioms rpow_lipschitz_on_unit
#print axioms reaction_lipschitz_on_unit
#print axioms auxiliaryDivergenceChemSource_lipschitz_pointwise
#print axioms auxiliaryValueSource_lipschitz_pointwise
#print axioms auxiliaryDivSource_lipschitz
#print axioms auxiliaryDivergenceChemSourceDiffGradDuhamel_abs_le
#print axioms auxiliaryMildMapDiv_rateEstimates

end ShenWork.PaperOne
