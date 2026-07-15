import ShenWork.Paper1.WholeLineWeightedRegularityNonlinearity
import Mathlib.Analysis.Calculus.MeanValue

open Filter MeasureTheory Set

noncomputable section

namespace ShenWork.Paper1

/-- Matched four-point estimate obtained by differentiating the straight
segment in the convex square. -/
theorem matched_fourPoint_quotient_abs_le
    {f f' : ℝ → ℝ} {M L K DU h a2 b2 a1 b1 : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hK : 0 ≤ K) (hDU : 0 ≤ DU)
    (hh : h ≠ 0)
    (ha2 : a2 ∈ Set.Icc (0 : ℝ) M)
    (hb2 : b2 ∈ Set.Icc (0 : ℝ) M)
    (ha1 : a1 ∈ Set.Icc (0 : ℝ) M)
    (hb1 : b1 ∈ Set.Icc (0 : ℝ) M)
    (hder : ∀ z ∈ Set.Icc (0 : ℝ) M, HasDerivAt f (f' z) z)
    (hder_bound : ∀ z ∈ Set.Icc (0 : ℝ) M, |f' z| ≤ L)
    (hder_lip : ∀ z ∈ Set.Icc (0 : ℝ) M,
      ∀ w ∈ Set.Icc (0 : ℝ) M,
        |f' z - f' w| ≤ K * |z - w|)
    (hbase_quot : |(b2 - b1) / h| ≤ DU) :
    |((f a2 - f b2) - (f a1 - f b1)) / h| ≤
      (L + K * M) * |((a2 - b2) - (a1 - b1)) / h| +
        K * DU * |a1 - b1| := by
  let da : ℝ := a2 - a1
  let db : ℝ := b2 - b1
  let dd : ℝ := (a2 - b2) - (a1 - b1)
  let A : ℝ → ℝ := fun theta => a1 + theta * da
  let B : ℝ → ℝ := fun theta => b1 + theta * db
  let phi : ℝ → ℝ := fun theta => f (A theta) - f (B theta)
  have hda : da = dd + db := by
    dsimp [da, dd, db]
    ring
  have hA_mem : ∀ theta ∈ Set.Icc (0 : ℝ) 1,
      A theta ∈ Set.Icc (0 : ℝ) M := by
    intro theta htheta
    dsimp [A, da]
    have htheta' : 0 ≤ 1 - theta := sub_nonneg.mpr htheta.2
    rw [show a1 + theta * (a2 - a1) =
        (1 - theta) * a1 + theta * a2 by ring]
    constructor
    · exact add_nonneg (mul_nonneg htheta' ha1.1)
        (mul_nonneg htheta.1 ha2.1)
    · calc
        (1 - theta) * a1 + theta * a2 ≤
            (1 - theta) * M + theta * M :=
          add_le_add
            (mul_le_mul_of_nonneg_left ha1.2 htheta')
            (mul_le_mul_of_nonneg_left ha2.2 htheta.1)
        _ = M := by ring
  have hB_mem : ∀ theta ∈ Set.Icc (0 : ℝ) 1,
      B theta ∈ Set.Icc (0 : ℝ) M := by
    intro theta htheta
    dsimp [B, db]
    have htheta' : 0 ≤ 1 - theta := sub_nonneg.mpr htheta.2
    rw [show b1 + theta * (b2 - b1) =
        (1 - theta) * b1 + theta * b2 by ring]
    constructor
    · exact add_nonneg (mul_nonneg htheta' hb1.1)
        (mul_nonneg htheta.1 hb2.1)
    · calc
        (1 - theta) * b1 + theta * b2 ≤
            (1 - theta) * M + theta * M :=
          add_le_add
            (mul_le_mul_of_nonneg_left hb1.2 htheta')
            (mul_le_mul_of_nonneg_left hb2.2 htheta.1)
        _ = M := by ring
  have hA_sub_B : ∀ theta,
      A theta - B theta = (a1 - b1) + theta * dd := by
    intro theta
    dsimp [A, B]
    rw [hda]
    ring
  have hdb_abs : |db| ≤ M := by
    dsimp [db]
    rw [abs_le]
    constructor <;> linarith [hb1.1, hb1.2, hb2.1, hb2.2]
  have hphi_der : ∀ theta ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt phi
        (f' (A theta) * da - f' (B theta) * db)
        (Set.Icc (0 : ℝ) 1) theta := by
    intro theta htheta
    have hAder : HasDerivAt A da theta := by
      dsimp [A]
      convert (hasDerivAt_const theta a1).add
        ((hasDerivAt_id theta).mul_const da) using 1 <;> ring
    have hBder : HasDerivAt B db theta := by
      dsimp [B]
      convert (hasDerivAt_const theta b1).add
        ((hasDerivAt_id theta).mul_const db) using 1 <;> ring
    have hfA := (hder (A theta) (hA_mem theta htheta)).comp theta hAder
    have hfB := (hder (B theta) (hB_mem theta htheta)).comp theta hBder
    exact (hfA.sub hfB).hasDerivWithinAt
  have hphi_bound : ∀ theta ∈ Set.Icc (0 : ℝ) 1,
      ‖f' (A theta) * da - f' (B theta) * db‖ ≤
        (L + K * M) * |dd| + K * |db| * |a1 - b1| := by
    intro theta htheta
    have htheta_abs : |theta| ≤ 1 := by
      rw [abs_of_nonneg htheta.1]
      exact htheta.2
    have hAB : |A theta - B theta| ≤ |a1 - b1| + |dd| := by
      rw [hA_sub_B]
      calc
        |(a1 - b1) + theta * dd| ≤
            |a1 - b1| + |theta * dd| := abs_add_le _ _
        _ = |a1 - b1| + |theta| * |dd| := by rw [abs_mul]
        _ ≤ |a1 - b1| + 1 * |dd| := by
          gcongr
        _ = |a1 - b1| + |dd| := by ring
    have hsplit :
        f' (A theta) * da - f' (B theta) * db =
          f' (A theta) * dd + (f' (A theta) - f' (B theta)) * db := by
      rw [hda]
      ring
    rw [Real.norm_eq_abs, hsplit]
    calc
      |f' (A theta) * dd + (f' (A theta) - f' (B theta)) * db| ≤
          |f' (A theta) * dd| +
            |(f' (A theta) - f' (B theta)) * db| := abs_add_le _ _
      _ = |f' (A theta)| * |dd| +
          |f' (A theta) - f' (B theta)| * |db| := by rw [abs_mul, abs_mul]
      _ ≤ L * |dd| + (K * |A theta - B theta|) * |db| := by
        gcongr
        · exact hder_bound (A theta) (hA_mem theta htheta)
        · exact hder_lip (A theta) (hA_mem theta htheta)
            (B theta) (hB_mem theta htheta)
      _ ≤ L * |dd| + (K * (|a1 - b1| + |dd|)) * |db| := by
        gcongr
      _ ≤ (L + K * M) * |dd| + K * |db| * |a1 - b1| := by
        have hKdd : 0 ≤ K * |dd| := mul_nonneg hK (abs_nonneg _)
        have hx := mul_le_mul_of_nonneg_left hdb_abs hKdd
        nlinarith
  have hmv : |phi 1 - phi 0| ≤
      (L + K * M) * |dd| + K * |db| * |a1 - b1| := by
    have hraw := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      hphi_der hphi_bound (convex_Icc (0 : ℝ) 1)
      (by simp : (0 : ℝ) ∈ Set.Icc 0 1)
      (by simp : (1 : ℝ) ∈ Set.Icc 0 1)
    simpa [Real.norm_eq_abs] using hraw
  have hphi_values :
      phi 1 - phi 0 = (f a2 - f b2) - (f a1 - f b1) := by
    dsimp [phi, A, B, da, db]
    ring
  rw [hphi_values] at hmv
  have habsh : 0 < |h| := abs_pos.mpr hh
  have hbase_abs : |db| / |h| ≤ DU := by
    rw [← abs_div]
    simpa only [db] using hbase_quot
  rw [abs_div]
  calc
    |(f a2 - f b2) - (f a1 - f b1)| / |h| ≤
        ((L + K * M) * |dd| + K * |db| * |a1 - b1|) / |h| :=
      (div_le_div_iff_of_pos_right habsh).2 hmv
    _ = (L + K * M) * (|dd| / |h|) +
          K * (|db| / |h|) * |a1 - b1| := by field_simp
    _ ≤ (L + K * M) * (|dd| / |h|) +
          K * DU * |a1 - b1| := by
      gcongr
    _ = (L + K * M) * |dd / h| + K * DU * |a1 - b1| := by
      rw [abs_div]
    _ = (L + K * M) * |((a2 - b2) - (a1 - b1)) / h| +
      K * DU * |a1 - b1| := by rfl

/-- Explicit Lipschitz constant of the reaction derivative on `[0,M]`. -/
def fourProfileReactionDerivativeLip (alpha M : ℝ) : ℝ :=
  (alpha + 1) * rpowLip alpha M

theorem fourProfileReactionDerivativeLip_nonneg
    {alpha M : ℝ} (halpha : 1 ≤ alpha) (hM : 0 ≤ M) :
    0 ≤ fourProfileReactionDerivativeLip alpha M := by
  unfold fourProfileReactionDerivativeLip
  exact mul_nonneg (by linarith) (rpowLip_nonneg halpha hM)

theorem reaction_matched_fourPoint_quotient_abs_le
    {alpha M DU h a2 b2 a1 b1 : ℝ}
    (halpha : 1 ≤ alpha) (hM : 0 ≤ M) (hDU : 0 ≤ DU)
    (hh : h ≠ 0)
    (ha2 : a2 ∈ Set.Icc (0 : ℝ) M)
    (hb2 : b2 ∈ Set.Icc (0 : ℝ) M)
    (ha1 : a1 ∈ Set.Icc (0 : ℝ) M)
    (hb1 : b1 ∈ Set.Icc (0 : ℝ) M)
    (hbase_quot : |(b2 - b1) / h| ≤ DU) :
    |((reactionFun alpha a2 - reactionFun alpha b2) -
          (reactionFun alpha a1 - reactionFun alpha b1)) / h| ≤
      (reactionLip alpha M + fourProfileReactionDerivativeLip alpha M * M) *
          |((a2 - b2) - (a1 - b1)) / h| +
        fourProfileReactionDerivativeLip alpha M * DU * |a1 - b1| := by
  let f' : ℝ → ℝ := fun z => 1 - (alpha + 1) * z ^ alpha
  have hder : ∀ z ∈ Set.Icc (0 : ℝ) M,
      HasDerivAt (reactionFun alpha) (f' z) z := by
    intro z hz
    have hzpow := mul_rpow_sub_one alpha halpha hz.1
    convert reactionFun_hasDerivAt alpha halpha z using 1
    dsimp [f']
    rw [hzpow]
    ring
  have hder_bound : ∀ z ∈ Set.Icc (0 : ℝ) M,
      |f' z| ≤ reactionLip alpha M := by
    intro z hz
    have hza_nonneg : 0 ≤ z ^ alpha := Real.rpow_nonneg hz.1 alpha
    have hza_le : z ^ alpha ≤ M ^ alpha :=
      Real.rpow_le_rpow hz.1 hz.2 (by linarith)
    have hcoef : 0 ≤ alpha + 1 := by linarith
    dsimp [f']
    unfold reactionLip
    rw [abs_le]
    constructor
    · have hmul := mul_le_mul_of_nonneg_left hza_le hcoef
      linarith
    · nlinarith [mul_nonneg hcoef hza_nonneg]
  have hpLip := rpow_m_lipschitz_on_Icc
    (m := alpha) (M := M) halpha hM
  have hpLip_real : ∀ z ∈ Set.Icc (0 : ℝ) M,
      ∀ w ∈ Set.Icc (0 : ℝ) M,
        |z ^ alpha - w ^ alpha| ≤ rpowLip alpha M * |z - w| := by
    intro z hz w hw
    have hp := hpLip.dist_le_mul z hz w hw
    rw [Real.coe_toNNReal _ (rpowLip_nonneg halpha hM)] at hp
    simpa [Real.dist_eq] using hp
  have hder_lip : ∀ z ∈ Set.Icc (0 : ℝ) M,
      ∀ w ∈ Set.Icc (0 : ℝ) M,
        |f' z - f' w| ≤
          fourProfileReactionDerivativeLip alpha M * |z - w| := by
    intro z hz w hw
    have hp := hpLip_real z hz w hw
    have hcoef : 0 ≤ alpha + 1 := by linarith
    dsimp [f']
    rw [show (1 - (alpha + 1) * z ^ alpha) -
        (1 - (alpha + 1) * w ^ alpha) =
          -(alpha + 1) * (z ^ alpha - w ^ alpha) by ring,
      abs_mul, abs_neg, abs_of_nonneg hcoef]
    unfold fourProfileReactionDerivativeLip
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hp hcoef
  exact matched_fourPoint_quotient_abs_le
    hM (reactionLip_nonneg halpha hM)
    (fourProfileReactionDerivativeLip_nonneg halpha hM) hDU hh
    ha2 hb2 ha1 hb1 hder hder_bound hder_lip hbase_quot

/-- Two-term cap-weighted `L²` lift. -/
theorem capWeighted_twoTerm_l2_bounded
    {eta R Cq C0 : ℝ} (hCq : 0 ≤ Cq) (hC0 : 0 ≤ C0)
    {q d out : ℝ → ℝ}
    (hout_cont : Continuous out)
    (hq : Integrable (fun x => capWeight eta R x * |q x| ^ 2))
    (hd : Integrable (fun x => capWeight eta R x * |d x| ^ 2))
    (hpoint : ∀ x, |out x| ≤ Cq * |q x| + C0 * |d x|) :
    Integrable (fun x => (capWeightSqrt eta R x * out x) ^ 2) ∧
      (∫ x : ℝ, (capWeightSqrt eta R x * out x) ^ 2) ≤
        2 * Cq ^ 2 *
            (∫ x : ℝ, capWeight eta R x * |q x| ^ 2) +
          2 * C0 ^ 2 *
            (∫ x : ℝ, capWeight eta R x * |d x| ^ 2) := by
  let qw : ℝ → ℝ := fun x => capWeightSqrt eta R x * q x
  let dw : ℝ → ℝ := fun x => capWeightSqrt eta R x * d x
  let ow : ℝ → ℝ := fun x => capWeightSqrt eta R x * out x
  have hqw : Integrable (fun x => qw x ^ 2) := by
    refine hq.congr (Eventually.of_forall fun x => ?_)
    dsimp [qw]
    exact (capWeightSqrt_mul_sq_eq eta R x (q x)).symm
  have hdw : Integrable (fun x => dw x ^ 2) := by
    refine hd.congr (Eventually.of_forall fun x => ?_)
    dsimp [dw]
    exact (capWeightSqrt_mul_sq_eq eta R x (d x)).symm
  have how_cont : Continuous ow := by
    dsimp [ow]
    exact (capWeightSqrt_continuous eta R).mul hout_cont
  have hpoint_w : ∀ x,
      |ow x| ≤ Cq * |qw x| + C0 * |dw x| := by
    intro x
    have hw : 0 ≤ capWeightSqrt eta R x :=
      (capWeightSqrt_pos eta R x).le
    dsimp [ow, qw, dw]
    rw [abs_mul, abs_of_nonneg hw, abs_mul, abs_of_nonneg hw,
      abs_mul, abs_of_nonneg hw]
    calc
      capWeightSqrt eta R x * |out x| ≤
          capWeightSqrt eta R x * (Cq * |q x| + C0 * |d x|) :=
        mul_le_mul_of_nonneg_left (hpoint x) hw
      _ = Cq * (capWeightSqrt eta R x * |q x|) +
          C0 * (capWeightSqrt eta R x * |d x|) := by ring
  have hpoint_sq : ∀ x, ow x ^ 2 ≤
      2 * Cq ^ 2 * qw x ^ 2 + 2 * C0 ^ 2 * dw x ^ 2 := by
    intro x
    have hrhs : 0 ≤ Cq * |qw x| + C0 * |dw x| :=
      add_nonneg (mul_nonneg hCq (abs_nonneg _))
        (mul_nonneg hC0 (abs_nonneg _))
    have hs := (sq_le_sq₀ (abs_nonneg _) hrhs).2 (hpoint_w x)
    calc
      ow x ^ 2 = |ow x| ^ 2 := (sq_abs _).symm
      _ ≤ (Cq * |qw x| + C0 * |dw x|) ^ 2 := hs
      _ ≤ 2 * ((Cq * |qw x|) ^ 2 + (C0 * |dw x|) ^ 2) := add_sq_le
      _ = 2 * Cq ^ 2 * qw x ^ 2 + 2 * C0 ^ 2 * dw x ^ 2 := by
        rw [mul_pow, mul_pow, sq_abs, sq_abs]
        ring
  have hdom : Integrable (fun x =>
      2 * Cq ^ 2 * qw x ^ 2 + 2 * C0 ^ 2 * dw x ^ 2) :=
    (hqw.const_mul (2 * Cq ^ 2)).add (hdw.const_mul (2 * C0 ^ 2))
  have how : Integrable (fun x => ow x ^ 2) := by
    refine Integrable.mono' hdom (how_cont.pow 2).aestronglyMeasurable ?_
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpoint_sq x
  have hqw_eq : (∫ x : ℝ, qw x ^ 2) =
      ∫ x : ℝ, capWeight eta R x * |q x| ^ 2 := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x =>
      capWeightSqrt_mul_sq_eq eta R x (q x)
  have hdw_eq : (∫ x : ℝ, dw x ^ 2) =
      ∫ x : ℝ, capWeight eta R x * |d x| ^ 2 := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x =>
      capWeightSqrt_mul_sq_eq eta R x (d x)
  refine ⟨by simpa only [ow] using how, ?_⟩
  calc
    (∫ x : ℝ, (capWeightSqrt eta R x * out x) ^ 2) =
        ∫ x : ℝ, ow x ^ 2 := by rfl
    _ ≤ ∫ x : ℝ,
        (2 * Cq ^ 2 * qw x ^ 2 + 2 * C0 ^ 2 * dw x ^ 2) :=
      integral_mono how hdom hpoint_sq
    _ = 2 * Cq ^ 2 * (∫ x : ℝ, qw x ^ 2) +
          2 * C0 ^ 2 * (∫ x : ℝ, dw x ^ 2) := by
      rw [integral_add (hqw.const_mul _) (hdw.const_mul _),
        integral_const_mul, integral_const_mul]
    _ = 2 * Cq ^ 2 *
            (∫ x : ℝ, capWeight eta R x * |q x| ^ 2) +
          2 * C0 ^ 2 *
            (∫ x : ℝ, capWeight eta R x * |d x| ^ 2) := by
      rw [hqw_eq, hdw_eq]

/-- Direct cap-weighted profile wrapper for the matched reaction quotient. -/
theorem capWeighted_reactionMatchedFourProfile_quotient_l2_bounded
    {alpha M DU eta R h : ℝ}
    (halpha : 1 ≤ alpha) (hM : 0 ≤ M) (hDU : 0 ≤ DU)
    (hh : h ≠ 0)
    {a2 b2 a1 b1 : ℝ → ℝ}
    (ha2 : IsCUnifBdd a2) (hb2 : IsCUnifBdd b2)
    (ha1 : IsCUnifBdd a1) (hb1 : IsCUnifBdd b1)
    (ha2_mem : ∀ x, a2 x ∈ Set.Icc (0 : ℝ) M)
    (hb2_mem : ∀ x, b2 x ∈ Set.Icc (0 : ℝ) M)
    (ha1_mem : ∀ x, a1 x ∈ Set.Icc (0 : ℝ) M)
    (hb1_mem : ∀ x, b1 x ∈ Set.Icc (0 : ℝ) M)
    (hbase_quot : ∀ x, |(b2 x - b1 x) / h| ≤ DU)
    (hquot : Integrable (fun x => capWeight eta R x *
      |((a2 x - b2 x) - (a1 x - b1 x)) / h| ^ 2))
    (hdiff : Integrable (fun x => capWeight eta R x *
      |a1 x - b1 x| ^ 2)) :
    Integrable (fun x =>
        (capWeightSqrt eta R x *
          (((reactionFun alpha (a2 x) - reactionFun alpha (b2 x)) -
            (reactionFun alpha (a1 x) - reactionFun alpha (b1 x))) / h)) ^ 2) ∧
      (∫ x : ℝ,
        (capWeightSqrt eta R x *
          (((reactionFun alpha (a2 x) - reactionFun alpha (b2 x)) -
            (reactionFun alpha (a1 x) - reactionFun alpha (b1 x))) / h)) ^ 2) ≤
        2 * (reactionLip alpha M +
            fourProfileReactionDerivativeLip alpha M * M) ^ 2 *
          (∫ x : ℝ, capWeight eta R x *
            |((a2 x - b2 x) - (a1 x - b1 x)) / h| ^ 2) +
        2 * (fourProfileReactionDerivativeLip alpha M * DU) ^ 2 *
          (∫ x : ℝ, capWeight eta R x * |a1 x - b1 x| ^ 2) := by
  let q : ℝ → ℝ := fun x => ((a2 x - b2 x) - (a1 x - b1 x)) / h
  let d : ℝ → ℝ := fun x => a1 x - b1 x
  let out : ℝ → ℝ := fun x =>
    ((reactionFun alpha (a2 x) - reactionFun alpha (b2 x)) -
      (reactionFun alpha (a1 x) - reactionFun alpha (b1 x))) / h
  let Cq : ℝ := reactionLip alpha M +
    fourProfileReactionDerivativeLip alpha M * M
  let C0 : ℝ := fourProfileReactionDerivativeLip alpha M * DU
  have hCq : 0 ≤ Cq := by
    dsimp [Cq]
    exact add_nonneg (reactionLip_nonneg halpha hM)
      (mul_nonneg (fourProfileReactionDerivativeLip_nonneg halpha hM) hM)
  have hC0 : 0 ≤ C0 := by
    dsimp [C0]
    exact mul_nonneg (fourProfileReactionDerivativeLip_nonneg halpha hM) hDU
  have hreac : Continuous (reactionFun alpha) :=
    continuous_reactionFun (le_trans zero_le_one halpha)
  have hout_cont : Continuous out := by
    dsimp [out]
    exact (((hreac.comp ha2.1).sub (hreac.comp hb2.1)).sub
      ((hreac.comp ha1.1).sub (hreac.comp hb1.1))).div_const h
  have hpoint : ∀ x, |out x| ≤ Cq * |q x| + C0 * |d x| := by
    intro x
    exact reaction_matched_fourPoint_quotient_abs_le
      halpha hM hDU hh (ha2_mem x) (hb2_mem x) (ha1_mem x) (hb1_mem x)
      (hbase_quot x)
  have hcore := capWeighted_twoTerm_l2_bounded
    (eta := eta) (R := R) hCq hC0 hout_cont
    (by simpa only [q] using hquot)
    (by simpa only [d] using hdiff) hpoint
  simpa only [q, d, out, Cq, C0] using hcore

#print axioms matched_fourPoint_quotient_abs_le
#print axioms reaction_matched_fourPoint_quotient_abs_le
#print axioms capWeighted_twoTerm_l2_bounded
#print axioms capWeighted_reactionMatchedFourProfile_quotient_l2_bounded

end ShenWork.Paper1

