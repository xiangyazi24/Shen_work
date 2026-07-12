import ShenWork.Paper1.WaveG1Bridge
import ShenWork.Paper1.WaveLemma42Paper

namespace ShenWork.Paper1

open Filter Topology

noncomputable section

/-- Concrete projected order-cube approximation data for one lower-pinned
wave-map.  This is the finite-dimensional residual left by the `proj/lift`
construction; it is not the old provider over all self-maps. -/
abbrev LowerPinnedOrderCubeApproxData
    (κ M : ℝ) (φ : ℝ → ℝ) (Tmap : (ℝ → ℝ) → ℝ → ℝ) : Type :=
  ProjectedCubeApproxData (InLowerPinnedMonotoneTrap κ M φ) Tmap

abbrev LowerPinnedWaveCubeApproxData
    (κ M : ℝ) (φ : ℝ → ℝ)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ) : Type :=
  LowerPinnedOrderCubeApproxData κ M φ
    (fun u => rotheLimit (rotheSeq u))

/-! ## Concrete order-cube mesh for the lower-pinned wave map -/

def waveCubeDim (N : ℕ) : ℕ :=
  2 * (N + 1) * (N + 1) + 1

lemma waveCubeDim_pos (N : ℕ) : 0 < waveCubeDim N := by
  unfold waveCubeDim
  omega

lemma waveCubeUniv_nonempty (N : ℕ) :
    (Finset.univ : Finset (Fin (waveCubeDim N))).Nonempty :=
  ⟨⟨0, waveCubeDim_pos N⟩, Finset.mem_univ _⟩

def waveCubeRadius (N : ℕ) : ℝ :=
  (N + 1 : ℝ)

def waveCubeMesh (N : ℕ) : ℝ :=
  ((N + 1 : ℝ))⁻¹

def waveCubeNode (N : ℕ) (i : Fin (waveCubeDim N)) : ℝ :=
  -waveCubeRadius N + (i : ℕ) * waveCubeMesh N

lemma waveCubeMesh_pos (N : ℕ) : 0 < waveCubeMesh N := by
  unfold waveCubeMesh
  positivity

lemma waveCubeMesh_nonneg (N : ℕ) : 0 ≤ waveCubeMesh N :=
  (waveCubeMesh_pos N).le

noncomputable def waveOrderEnvelope (M : ℝ) (N : ℕ)
    (a : Fin (waveCubeDim N) → ℝ) (x : ℝ) : ℝ :=
  M * (Finset.univ.inf' (waveCubeUniv_nonempty N)
    (fun i : Fin (waveCubeDim N) => a i + max 0 (waveCubeNode N i - x)))

noncomputable def waveRawLift (κ M κtilde D : ℝ) (N : ℕ)
    (a : Fin (waveCubeDim N) → ℝ) (x : ℝ) : ℝ :=
  max (lowerBarrierPlateau κ κtilde D x)
    (min (upperBarrier κ M x) (waveOrderEnvelope M N a x))

noncomputable def waveValueProj (M : ℝ) (N : ℕ)
    (u : ℝ → ℝ) : Fin (waveCubeDim N) → ℝ :=
  fun i => u (waveCubeNode N i) / M

def waveCubeEps (N : ℕ) : ℝ :=
  ((N + 1 : ℝ))⁻¹

def waveCubeLocalError (M : ℝ) (N : ℕ) (_R : ℝ) : ℝ :=
  if _R ≤ waveCubeRadius N then
    (4 * M + 2) * waveCubeEps N
  else
    2 * M + 1

lemma waveCubeEps_pos (N : ℕ) : 0 < waveCubeEps N := by
  unfold waveCubeEps
  positivity

lemma waveCubeEps_nonneg (N : ℕ) : 0 ≤ waveCubeEps N :=
  (waveCubeEps_pos N).le

lemma waveCubeEps_tendsto :
    Tendsto waveCubeEps atTop (𝓝 0) := by
  simpa [waveCubeEps, one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma waveCubeLocalError_nonneg {M : ℝ} (hM : 0 ≤ M) (N : ℕ) (R : ℝ) :
    0 ≤ waveCubeLocalError M N R := by
  unfold waveCubeLocalError
  split_ifs
  · exact mul_nonneg (by nlinarith) (waveCubeEps_nonneg N)
  · nlinarith

lemma waveCubeLocalError_tendsto {M R : ℝ} :
    Tendsto (fun N => waveCubeLocalError M N R) atTop (𝓝 0) := by
  have hev : ∀ᶠ N : ℕ in atTop, R ≤ waveCubeRadius N := by
    obtain ⟨N0, hN0⟩ := exists_nat_gt R
    refine eventually_atTop.mpr ⟨N0, ?_⟩
    intro N hN
    unfold waveCubeRadius
    have hNR : R < (N0 : ℝ) := hN0
    have hN0N : (N0 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hsmall : Tendsto (fun N => (4 * M + 2) * waveCubeEps N)
      atTop (𝓝 0) := by
    simpa using (waveCubeEps_tendsto.const_mul (4 * M + 2))
  refine Tendsto.congr' ?_ hsmall
  filter_upwards [hev] with N hN
  simp [waveCubeLocalError, hN]

lemma lowerBarrierRaw_le_plateau
    {κ κtilde D : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hD : 0 < D) (x : ℝ) :
    lowerBarrierRaw κ κtilde D x ≤ lowerBarrierPlateau κ κtilde D x := by
  by_cases hx : x ≤ lowerBarrierXPlus κ κtilde D
  · rw [lowerBarrierPlateau_eq_const_of_le hx]
    have hmono : MonotoneOn (lowerBarrierRaw κ κtilde D)
        (Set.Iic (lowerBarrierXPlus κ κtilde D)) := by
      apply monotoneOn_of_deriv_nonneg (convex_Iic _)
      · exact (lowerBarrierRaw_continuous κ κtilde D).continuousOn
      · intro y _hy
        exact (lowerBarrierRaw_hasDerivAt κ κtilde D y).differentiableAt
          |>.differentiableWithinAt
      · intro y hy
        have hyle : y ≤ lowerBarrierXPlus κ κtilde D := by
          exact le_of_lt (by simpa using hy)
        exact lowerBarrierRaw_deriv_nonneg_of_le_xplus hκ hgap hD hyle
    exact hmono hx (by simp) hx
  · have hxlt : lowerBarrierXPlus κ κtilde D < x := lt_of_not_ge hx
    rw [lowerBarrierPlateau_eq_raw_of_xplus_lt hxlt]

lemma waveValueProj_mem_unitCube {κ M : ℝ} {φ : ℝ → ℝ}
    (hM : 0 < M) (N : ℕ)
    {u : ℝ → ℝ} (hu : InLowerPinnedMonotoneTrap κ M φ u) :
    waveValueProj M N u ∈ Freudenthal.unitCube (waveCubeDim N) := by
  intro i
  constructor
  · exact div_nonneg (hu.bare.nonneg _) hM.le
  · exact (div_le_one hM).mpr (hu.bare.le_M _)

lemma waveOrderEnvelope_continuous (M : ℝ) (N : ℕ)
    (a : Fin (waveCubeDim N) → ℝ) :
    Continuous (waveOrderEnvelope M N a) := by
  unfold waveOrderEnvelope
  apply continuous_const.mul
  apply Continuous.finset_inf'_apply (waveCubeUniv_nonempty N)
  intro i _hi
  exact continuous_const.add
    (continuous_const.max (continuous_const.sub continuous_id))

lemma waveOrderEnvelope_antitone {M : ℝ} (hM : 0 ≤ M) (N : ℕ)
    (a : Fin (waveCubeDim N) → ℝ) :
    Antitone (waveOrderEnvelope M N a) := by
  intro x y hxy
  unfold waveOrderEnvelope
  apply mul_le_mul_of_nonneg_left _ hM
  apply Finset.le_inf' (waveCubeUniv_nonempty N)
  intro i hi
  have hsub : waveCubeNode N i - y ≤ waveCubeNode N i - x := by
    linarith
  have hterm :
      a i + max 0 (waveCubeNode N i - y) ≤
        a i + max 0 (waveCubeNode N i - x) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_right
        (max_le_max (show (0 : ℝ) ≤ 0 from le_rfl) hsub) (a i)
  exact le_trans (Finset.inf'_le (f :=
    fun i : Fin (waveCubeDim N) => a i + max 0 (waveCubeNode N i - y)) hi) hterm

lemma waveRawLift_continuous (κ M κtilde D : ℝ) (N : ℕ)
    (a : Fin (waveCubeDim N) → ℝ) :
    Continuous (waveRawLift κ M κtilde D N a) := by
  unfold waveRawLift
  exact (lowerBarrierPlateau_continuous κ κtilde D).max
    ((upperBarrier_continuous κ M).min
      (waveOrderEnvelope_continuous M N a))

lemma waveRawLift_antitone {κ M κtilde D : ℝ}
    (hκ : 0 ≤ κ) (hM : 0 ≤ M)
    (hκpos : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D)
    (N : ℕ) (a : Fin (waveCubeDim N) → ℝ) :
    Antitone (waveRawLift κ M κtilde D N a) := by
  intro x y hxy
  unfold waveRawLift
  exact max_le_max
    (lowerBarrierPlateau_antitone hκpos hgap hD hxy)
    (min_le_min (upperBarrier_antitone hκ hxy)
      (waveOrderEnvelope_antitone hM N a hxy))

lemma waveRawLift_mem_lowerPinned
    {κ M κtilde D : ℝ}
    (hκpos : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D)
    (hM : 0 ≤ M)
    (hplat : InMonotoneWaveTrapSet κ M (lowerBarrierPlateau κ κtilde D))
    (N : ℕ) (a : Fin (waveCubeDim N) → ℝ) :
    InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D)
      (waveRawLift κ M κtilde D N a) := by
  have hκ : 0 ≤ κ := hκpos.le
  refine ⟨?_, ?_⟩
  · refine ⟨?_, waveRawLift_antitone hκ hM hκpos hgap hD N a⟩
    refine ⟨⟨waveRawLift_continuous κ M κtilde D N a, ?_⟩, ?_⟩
    · refine ⟨M, fun x => ?_⟩
      have hnonneg : 0 ≤ waveRawLift κ M κtilde D N a x := by
        unfold waveRawLift
        exact le_trans (hplat.nonneg x) (le_max_left _ _)
      have hleUpper : waveRawLift κ M κtilde D N a x ≤
          upperBarrier κ M x := by
        unfold waveRawLift
        exact max_le (hplat.le_upperBarrier x) (min_le_left _ _)
      have hleM : waveRawLift κ M κtilde D N a x ≤ M := by
        exact le_trans hleUpper (upperBarrier_le_M κ M x)
      rw [abs_of_nonneg hnonneg]
      exact hleM
    · intro x
      constructor
      · unfold waveRawLift
        exact le_trans (hplat.nonneg x) (le_max_left _ _)
      · unfold waveRawLift
        exact max_le (hplat.le_upperBarrier x) (min_le_left _ _)
  · intro x
    exact le_trans (lowerBarrierRaw_le_plateau hκpos hgap hD x)
      (by unfold waveRawLift; exact le_max_left _ _)

lemma waveCube_cover (N : ℕ) {R x : ℝ}
    (hR : R ≤ waveCubeRadius N) (hx : x ∈ Set.Icc (-R) R) :
    ∃ i : Fin (waveCubeDim N), |x - waveCubeNode N i| ≤ waveCubeEps N := by
  set A : ℝ := (N + 1 : ℝ) with hA
  set η : ℝ := waveCubeEps N with hη
  have hApos : 0 < A := by positivity
  have hηpos : 0 < η := by simpa [hη] using waveCubeEps_pos N
  have hηeq : η = A⁻¹ := by simp [hη, waveCubeEps, hA]
  have hηA : η * A = 1 := by
    rw [hηeq]
    exact inv_mul_cancel₀ (ne_of_gt hApos)
  have hrad : waveCubeRadius N = A := by simp [waveCubeRadius, hA]
  rw [Set.mem_Icc] at hx
  have hx_low : -A ≤ x := by linarith
  have hx_high : x ≤ A := by linarith
  set t : ℝ := (x + A) / η with ht
  have ht_nonneg : 0 ≤ t := by
    rw [ht]
    exact div_nonneg (by linarith) hηpos.le
  let iNat : ℕ := ⌊t⌋₊
  have hi_le_t : (iNat : ℝ) ≤ t := Nat.floor_le ht_nonneg
  have ht_le : t ≤ (2 * (N + 1) * (N + 1) : ℕ) := by
    rw [ht]
    have hnum : x + A ≤ 2 * A := by linarith
    have hdiv : (x + A) / η ≤ (2 * A) / η :=
      div_le_div_of_nonneg_right hnum hηpos.le
    have htarget : (2 * A) / η = 2 * A * A := by
      rw [div_eq_mul_inv, hηeq]
      field_simp [ne_of_gt hApos]
    have hcast : ((2 * (N + 1) * (N + 1) : ℕ) : ℝ) = 2 * A * A := by
      norm_num [hA]
    linarith
  have hi_bound : iNat ≤ 2 * (N + 1) * (N + 1) := by
    have : (iNat : ℝ) ≤ (2 * (N + 1) * (N + 1) : ℕ) :=
      le_trans hi_le_t ht_le
    exact_mod_cast this
  refine ⟨⟨iNat, ?_⟩, ?_⟩
  · unfold waveCubeDim
    omega
  · have ht_lt : t < (iNat : ℝ) + 1 := Nat.lt_floor_add_one t
    have hlow : (iNat : ℝ) * η ≤ x + A := by
      have := mul_le_mul_of_nonneg_right hi_le_t hηpos.le
      rwa [ht, div_mul_cancel₀ _ (ne_of_gt hηpos)] at this
    have hhigh : x + A < ((iNat : ℝ) + 1) * η := by
      have := mul_lt_mul_of_pos_right ht_lt hηpos
      rwa [ht, div_mul_cancel₀ _ (ne_of_gt hηpos)] at this
    have hnode : waveCubeNode N ⟨iNat, by unfold waveCubeDim; omega⟩ =
        -A + (iNat : ℝ) * η := by
      rw [waveCubeNode, waveCubeRadius, waveCubeMesh, hA, hη, waveCubeEps]
    rw [hnode, abs_le]
    constructor
    · nlinarith
    · nlinarith [hhigh]

lemma finset_inf'_abs_sub_le {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {f g : ι → ℝ} {δ : ℝ}
    (hfg : ∀ i ∈ s, |f i - g i| ≤ δ) :
    |s.inf' hs f - s.inf' hs g| ≤ δ := by
  rw [abs_le]
  constructor
  · have hle : s.inf' hs f - δ ≤ s.inf' hs g := by
      apply Finset.le_inf' hs
      intro i hi
      have hf : s.inf' hs f ≤ f i := Finset.inf'_le _ hi
      have hfg' : f i ≤ g i + δ := by
        have := (abs_le.mp (hfg i hi)).2
        linarith
      linarith
    have hle' : s.inf' hs g - δ ≤ s.inf' hs f := by
      apply Finset.le_inf' hs
      intro i hi
      have hg : s.inf' hs g ≤ g i := Finset.inf'_le _ hi
      have hgf' : g i ≤ f i + δ := by
        have := (abs_le.mp (hfg i hi)).1
        linarith
      linarith
    linarith
  · have hle : s.inf' hs f - δ ≤ s.inf' hs g := by
      apply Finset.le_inf' hs
      intro i hi
      have hf : s.inf' hs f ≤ f i := Finset.inf'_le _ hi
      have hfg' : f i ≤ g i + δ := by
        have := (abs_le.mp (hfg i hi)).2
        linarith
      linarith
    linarith

lemma clamp_between_lipschitz (l u s t : ℝ) :
    |max l (min u s) - max l (min u t)| ≤ |s - t| := by
  have hLip : LipschitzWith 1 (fun z : ℝ => max l (min u z)) :=
    (LipschitzWith.id.const_min u).const_max l
  have h := hLip.dist_le_mul s t
  simpa [Real.dist_eq] using h

lemma plateau_le_of_lowerPinnedRaw
    {κ M κtilde D : ℝ} {u : ℝ → ℝ}
    (hu : InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u)
    (x : ℝ) :
    lowerBarrierPlateau κ κtilde D x ≤ u x := by
  by_cases hx : x ≤ lowerBarrierXPlus κ κtilde D
  · rw [lowerBarrierPlateau_eq_const_of_le hx]
    exact le_trans (hu.lower (lowerBarrierXPlus κ κtilde D))
      (hu.bare.antitone hx)
  · have hxlt : lowerBarrierXPlus κ κtilde D < x := lt_of_not_ge hx
    rw [lowerBarrierPlateau_eq_raw_of_xplus_lt hxlt]
    exact hu.lower x

lemma waveEnvelope_proj_lower {M : ℝ} (hM : 0 < M) (N : ℕ)
    {f : ℝ → ℝ} (hanti : Antitone f)
    (hLip : ∀ x y, |f x - f y| ≤ M * |x - y|) (x : ℝ) :
    f x ≤ waveOrderEnvelope M N (waveValueProj M N f) x := by
  unfold waveOrderEnvelope waveValueProj
  have hle : f x / M ≤ Finset.univ.inf' (waveCubeUniv_nonempty N)
      (fun i : Fin (waveCubeDim N) =>
        f (waveCubeNode N i) / M + max 0 (waveCubeNode N i - x)) := by
    apply Finset.le_inf' (waveCubeUniv_nonempty N)
    intro i _hi
    by_cases hix : waveCubeNode N i ≤ x
    · have hf : f x ≤ f (waveCubeNode N i) := hanti hix
      have hdiv : f x / M ≤ f (waveCubeNode N i) / M :=
        div_le_div_of_nonneg_right hf hM.le
      have hmax : 0 ≤ max 0 (waveCubeNode N i - x) := le_max_left _ _
      linarith
    · have hxi : x ≤ waveCubeNode N i := le_of_not_ge hix
      have habs := hLip x (waveCubeNode N i)
      have hdiff : f x - f (waveCubeNode N i) ≤
          M * (waveCubeNode N i - x) := by
        have hright := (abs_le.mp habs).2
        have hdist : |x - waveCubeNode N i| = waveCubeNode N i - x := by
          rw [abs_of_nonpos (by linarith)]
          linarith
        rwa [hdist] at hright
      have hdiv : f x / M - f (waveCubeNode N i) / M ≤
          waveCubeNode N i - x := by
        field_simp [ne_of_gt hM]
        nlinarith
      have hmax : max 0 (waveCubeNode N i - x) =
          waveCubeNode N i - x := max_eq_right (sub_nonneg.mpr hxi)
      rw [hmax]
      linarith
  calc
    f x = M * (f x / M) := by field_simp [ne_of_gt hM]
    _ ≤ M * Finset.univ.inf' (waveCubeUniv_nonempty N)
        (fun i : Fin (waveCubeDim N) =>
          f (waveCubeNode N i) / M + max 0 (waveCubeNode N i - x)) :=
        mul_le_mul_of_nonneg_left hle hM.le

lemma waveEnvelope_proj_upper_near {M : ℝ} (hM : 0 < M) (N : ℕ)
    {f : ℝ → ℝ} (hLip : ∀ x y, |f x - f y| ≤ M * |x - y|)
    {x : ℝ} {i : Fin (waveCubeDim N)}
    (hnear : |x - waveCubeNode N i| ≤ waveCubeEps N) :
    waveOrderEnvelope M N (waveValueProj M N f) x ≤
      f x + 2 * M * waveCubeEps N := by
  unfold waveOrderEnvelope waveValueProj
  have hmin := Finset.inf'_le
    (s := (Finset.univ : Finset (Fin (waveCubeDim N))))
    (f := fun i : Fin (waveCubeDim N) =>
      f (waveCubeNode N i) / M + max 0 (waveCubeNode N i - x))
    (Finset.mem_univ i)
  have hmul := mul_le_mul_of_nonneg_left hmin hM.le
  have hmax_le : max 0 (waveCubeNode N i - x) ≤ waveCubeEps N := by
    apply max_le
    · exact waveCubeEps_nonneg N
    · have hle_abs : waveCubeNode N i - x ≤ |x - waveCubeNode N i| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      exact le_trans hle_abs hnear
  have hf_le : f (waveCubeNode N i) ≤ f x + M * waveCubeEps N := by
    have habs := hLip (waveCubeNode N i) x
    have hright := (abs_le.mp habs).2
    have hdist : |waveCubeNode N i - x| ≤ waveCubeEps N := by
      simpa [abs_sub_comm] using hnear
    nlinarith [le_trans hright (mul_le_mul_of_nonneg_left hdist hM.le)]
  calc
    M * (Finset.univ.inf' (waveCubeUniv_nonempty N)
        (fun i : Fin (waveCubeDim N) =>
          f (waveCubeNode N i) / M + max 0 (waveCubeNode N i - x)))
        ≤ M * (f (waveCubeNode N i) / M +
            max 0 (waveCubeNode N i - x)) := hmul
    _ = f (waveCubeNode N i) + M * max 0 (waveCubeNode N i - x) := by
        field_simp [ne_of_gt hM]
    _ ≤ f x + 2 * M * waveCubeEps N := by
        nlinarith [hf_le, mul_le_mul_of_nonneg_left hmax_le hM.le]

lemma waveOrderEnvelope_abs_sub_le_of_coords {M : ℝ} (hM : 0 ≤ M) (N : ℕ)
    {a b : Fin (waveCubeDim N) → ℝ} {δ x : ℝ}
    (hcoord : ∀ i, |a i - b i| ≤ δ) :
    |waveOrderEnvelope M N a x - waveOrderEnvelope M N b x| ≤ M * δ := by
  unfold waveOrderEnvelope
  set ia := Finset.univ.inf' (waveCubeUniv_nonempty N)
    (fun i : Fin (waveCubeDim N) => a i + max 0 (waveCubeNode N i - x))
  set ib := Finset.univ.inf' (waveCubeUniv_nonempty N)
    (fun i : Fin (waveCubeDim N) => b i + max 0 (waveCubeNode N i - x))
  have hinf : |ia - ib| ≤ δ := by
    apply finset_inf'_abs_sub_le (waveCubeUniv_nonempty N)
    intro i _hi
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hcoord i
  calc
    |M * ia - M * ib| = M * |ia - ib| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg hM]
    _ ≤ M * δ := mul_le_mul_of_nonneg_left hinf hM

lemma waveRawLift_abs_sub_le_of_coords {κ M κtilde D : ℝ} (hM : 0 ≤ M)
    (N : ℕ) {a b : Fin (waveCubeDim N) → ℝ} {δ x : ℝ}
    (hcoord : ∀ i, |a i - b i| ≤ δ) :
    |waveRawLift κ M κtilde D N a x - waveRawLift κ M κtilde D N b x| ≤
      M * δ := by
  unfold waveRawLift
  exact le_trans (clamp_between_lipschitz _ _ _ _)
    (waveOrderEnvelope_abs_sub_le_of_coords hM N hcoord)

lemma coord_abs_sub_le_of_norm {n : ℕ} {a b : Fin n → ℝ} {ε : ℝ}
    (h : ‖b - a‖ ≤ ε) (i : Fin n) :
    |b i - a i| ≤ ε := by
  have hi : ‖(b - a) i‖ ≤ ‖b - a‖ := norm_le_pi_norm (b - a) i
  simpa [Pi.sub_apply, Real.norm_eq_abs] using le_trans hi h

lemma waveRawLift_proj_error {κ M κtilde D : ℝ} (hM : 0 < M) (N : ℕ)
    {f : ℝ → ℝ} (hf : InLowerPinnedMonotoneTrap κ M
      (lowerBarrierRaw κ κtilde D) f)
    (hLip : ∀ x y, |f x - f y| ≤ M * |x - y|)
    {x : ℝ} {i : Fin (waveCubeDim N)}
    (hnear : |x - waveCubeNode N i| ≤ waveCubeEps N) :
    |f x - waveRawLift κ M κtilde D N (waveValueProj M N f) x| ≤
      2 * M * waveCubeEps N := by
  have henv_lo :=
    waveEnvelope_proj_lower hM N hf.bare.antitone hLip x
  have henv_hi :=
    waveEnvelope_proj_upper_near hM N hLip hnear
  have hplat_le : lowerBarrierPlateau κ κtilde D x ≤ f x :=
    plateau_le_of_lowerPinnedRaw hf x
  have hclip_lo : f x ≤
      waveRawLift κ M κtilde D N (waveValueProj M N f) x := by
    unfold waveRawLift
    exact le_trans
      (le_min (hf.bare.le_upperBarrier x) henv_lo)
      (le_max_right _ _)
  have hclip_hi :
      waveRawLift κ M κtilde D N (waveValueProj M N f) x ≤
        waveOrderEnvelope M N (waveValueProj M N f) x := by
    unfold waveRawLift
    exact max_le (le_trans hplat_le henv_lo) (min_le_right _ _)
  rw [abs_of_nonpos (sub_nonpos.mpr hclip_lo)]
  nlinarith [le_trans hclip_hi henv_hi]

lemma waveCube_residual_le
    {κ M κtilde D : ℝ} (hM : 0 < M)
    (hκpos : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D)
    (hplat : InMonotoneWaveTrapSet κ M (lowerBarrierPlateau κ κtilde D))
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hTlower : ∀ u,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
        InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) (Tmap u))
    (hTLip : ∀ u,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
        ∀ x y, |Tmap u x - Tmap u y| ≤ M * |x - y|)
    (N : ℕ) (a : Fin (waveCubeDim N) → ℝ)
    (_ha : a ∈ Freudenthal.unitCube (waveCubeDim N))
    (hclose : ‖waveValueProj M N (Tmap (waveRawLift κ M κtilde D N a)) - a‖ ≤
      waveCubeEps N)
    (R : ℝ) (_hRpos : 0 < R) (x : ℝ) (hx : x ∈ Set.Icc (-R) R) :
    |Tmap (waveRawLift κ M κtilde D N a) x -
      waveRawLift κ M κtilde D N a x| ≤
        waveCubeLocalError M N R := by
  have hM0 : 0 ≤ M := hM.le
  let u := waveRawLift κ M κtilde D N a
  have hu : InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u :=
    waveRawLift_mem_lowerPinned hκpos hgap hD hM0 hplat N a
  let f := Tmap u
  have hf : InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) f :=
    hTlower u hu
  have hLip : ∀ x y, |f x - f y| ≤ M * |x - y| := hTLip u hu
  by_cases hcov : R ≤ waveCubeRadius N
  · obtain ⟨i, hnear⟩ := waveCube_cover N hcov hx
    have hproj :=
      waveRawLift_proj_error hM N hf hLip hnear
    have hcoord : ∀ i, |waveValueProj M N f i - a i| ≤ waveCubeEps N :=
      coord_abs_sub_le_of_norm hclose
    have hlift :
        |waveRawLift κ M κtilde D N (waveValueProj M N f) x -
          waveRawLift κ M κtilde D N a x| ≤ M * waveCubeEps N :=
      waveRawLift_abs_sub_le_of_coords hM0 N hcoord
    have htri :
        |f x - waveRawLift κ M κtilde D N a x| ≤
          |f x - waveRawLift κ M κtilde D N (waveValueProj M N f) x| +
          |waveRawLift κ M κtilde D N (waveValueProj M N f) x -
            waveRawLift κ M κtilde D N a x| := by
      simpa using abs_sub_le (f x)
        (waveRawLift κ M κtilde D N (waveValueProj M N f) x)
        (waveRawLift κ M κtilde D N a x)
    have herr : |f x - waveRawLift κ M κtilde D N a x| ≤
        (4 * M + 2) * waveCubeEps N := by
      nlinarith [htri, hproj, hlift, waveCubeEps_nonneg N, hM0]
    simpa [waveCubeLocalError, hcov, u, f] using herr
  · have hf_nonneg : 0 ≤ f x := hf.bare.nonneg x
    have hf_le : f x ≤ M := hf.bare.le_M x
    have hu_nonneg : 0 ≤ u x := hu.bare.nonneg x
    have hu_le : u x ≤ M := hu.bare.le_M x
    have hrough : |f x - u x| ≤ 2 * M + 1 := by
      have htri0 : |f x - u x| ≤ |f x| + |u x| := by
        simpa [sub_zero, zero_sub, abs_neg] using abs_sub_le (f x) 0 (u x)
      calc
        |f x - u x| ≤ |f x| + |u x| := htri0
        _ = f x + u x := by
          rw [abs_of_nonneg hf_nonneg, abs_of_nonneg hu_nonneg]
        _ ≤ 2 * M + 1 := by nlinarith
    simpa [waveCubeLocalError, hcov, u, f] using hrough

lemma waveRawLift_locallyUniform_of_tendsto
    {κ M κtilde D : ℝ} (hM : 0 ≤ M) (N : ℕ)
    {seq : ℕ → Fin (waveCubeDim N) → ℝ} {a : Fin (waveCubeDim N) → ℝ}
    (hseq : Tendsto seq atTop (𝓝 a)) :
    LocallyUniformConverges
      (fun n => waveRawLift κ M κtilde D N (seq n))
      (waveRawLift κ M κtilde D N a) := by
  intro R _hR ε hε
  set δ : ℝ := ε / (M + 1) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    positivity
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.mp hseq δ hδpos
  have hev : ∀ᶠ n in atTop, dist (seq n) a < δ :=
    eventually_atTop.2 ⟨N0, hN0⟩
  filter_upwards [hev] with n hn x _hx
  have hnorm : ‖seq n - a‖ < δ := by
    simpa [dist_eq_norm] using hn
  have hcoord : ∀ i, |seq n i - a i| ≤ ‖seq n - a‖ :=
    fun i => coord_abs_sub_le_of_norm le_rfl i
  have hlift :=
    waveRawLift_abs_sub_le_of_coords (κ := κ) (M := M)
      (κtilde := κtilde) (D := D) hM N hcoord (x := x)
  have hmul : M * ‖seq n - a‖ < ε := by
    have hdenpos : 0 < M + 1 := by linarith
    have hMdelta_lt : M * δ < ε := by
      rw [hδ]
      have haux : M * (ε / (M + 1)) = (M * ε) / (M + 1) := by ring
      rw [haux, div_lt_iff₀ hdenpos]
      nlinarith [hM, hε]
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left (le_of_lt hnorm) hM) hMdelta_lt
  exact lt_of_le_of_lt hlift hmul

lemma waveTfin_continuous
    {κ M κtilde D : ℝ} (hM : 0 < M)
    (hκpos : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D)
    (hplat : InMonotoneWaveTrapSet κ M (lowerBarrierPlateau κ κtilde D))
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hcont : LocalUniformContinuousOn
      (InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D)) Tmap)
    (N : ℕ) :
    Continuous
      (fun a : Fin (waveCubeDim N) → ℝ =>
        waveValueProj M N (Tmap (waveRawLift κ M κtilde D N a))) := by
  rw [continuous_iff_continuousAt]
  intro a
  rw [ContinuousAt, tendsto_nhds_iff_seq_tendsto]
  intro seq hseq
  rw [tendsto_pi_nhds]
  intro i
  have hlift : LocallyUniformConverges
      (fun n => waveRawLift κ M κtilde D N (seq n))
      (waveRawLift κ M κtilde D N a) :=
    waveRawLift_locallyUniform_of_tendsto hM.le N hseq
  have htrap_seq : ∀ n, InLowerPinnedMonotoneTrap κ M
      (lowerBarrierRaw κ κtilde D)
      (waveRawLift κ M κtilde D N (seq n)) :=
    fun n => waveRawLift_mem_lowerPinned hκpos hgap hD hM.le hplat N (seq n)
  have htrap_a : InLowerPinnedMonotoneTrap κ M
      (lowerBarrierRaw κ κtilde D)
      (waveRawLift κ M κtilde D N a) :=
    waveRawLift_mem_lowerPinned hκpos hgap hD hM.le hplat N a
  have hT := hcont _ _ htrap_seq htrap_a hlift
  have hpoint := hT.tendsto_at (waveCubeNode N i)
  unfold waveValueProj
  exact hpoint.div_const M

lemma lowerBarrierExpXPlus_le_one_of_one_le_D
    {κ κtilde D M : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hD1 : 1 ≤ D) (hM1 : 1 ≤ M) :
    Real.exp (-κ * lowerBarrierXPlus κ κtilde D) ≤ M := by
  have hκtilde_pos : 0 < κtilde := by linarith
  have hargpos : 0 < κtilde * D / κ := by positivity
  have hκ_le : κ ≤ κtilde * D := by
    have hκ_le_κtilde : κ ≤ κtilde := by linarith
    calc
      κ ≤ κtilde := hκ_le_κtilde
      _ = κtilde * 1 := by ring
      _ ≤ κtilde * D := mul_le_mul_of_nonneg_left hD1 hκtilde_pos.le
  have harg_ge_one : 1 ≤ κtilde * D / κ := by
    rw [le_div_iff₀ hκ]
    simpa [one_mul] using hκ_le
  have hlog_nonneg : 0 ≤ Real.log (κtilde * D / κ) :=
    Real.log_nonneg harg_ge_one
  have hxplus_nonneg : 0 ≤ lowerBarrierXPlus κ κtilde D := by
    unfold lowerBarrierXPlus
    exact div_nonneg hlog_nonneg hgap.le
  have hexp_le_one :
      Real.exp (-κ * lowerBarrierXPlus κ κtilde D) ≤ 1 := by
    have hle0 : -κ * lowerBarrierXPlus κ κtilde D ≤ 0 := by
      nlinarith [mul_nonneg hκ.le hxplus_nonneg]
    exact Real.exp_le_one_iff.mpr hle0
  exact le_trans hexp_le_one hM1

noncomputable def lowerPinnedRawWaveCubeApproxData
    (p : CMParams) (c lam M κ κtilde D : ℝ)
    (hM : 0 < M)
    (hκpos : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D)
    (hplat : InMonotoneWaveTrapSet κ M
      (lowerBarrierPlateau κ κtilde D))
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ)
    (hŪbdd : IsBddFun (upperBarrier κ M))
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M)
        rotheSeq)
    (hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
        PaperRotheOrbitData p c lam M κ rotheSeq u)
    (hlower : RotheOrbitLowerBound κ M
      (lowerBarrierRaw κ κtilde D) rotheSeq) :
    LowerPinnedWaveCubeApproxData κ M (lowerBarrierRaw κ κtilde D)
      rotheSeq := by
  let Tmap : (ℝ → ℝ) → ℝ → ℝ := fun u => rotheLimit (rotheSeq u)
  have hbareInv :
      ∀ u, InMonotoneWaveTrapSet κ M u →
        InMonotoneWaveTrapSet κ M (Tmap u) :=
    paperTmap_maps_trap p c lam M κ hM.le rotheSeq hŪbdd hdata
  have hlowerT :
      ∀ u, InLowerPinnedMonotoneTrap κ M
        (lowerBarrierRaw κ κtilde D) u → ∀ x,
          lowerBarrierRaw κ κtilde D x ≤ Tmap u x :=
    Tmap_lowerInvariant_of_rotheOrbitLowerBound hlower
  have hTlower :
      ∀ u, InLowerPinnedMonotoneTrap κ M
        (lowerBarrierRaw κ κtilde D) u →
          InLowerPinnedMonotoneTrap κ M
            (lowerBarrierRaw κ κtilde D) (Tmap u) := by
    intro u hu
    exact ⟨hbareInv u hu.bare, hlowerT u hu⟩
  have hcontLower :
      LocalUniformContinuousOn
        (InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D))
        Tmap := by
    intro seq u hseq hu hconv
    exact hdep seq u (fun n => (hseq n).bare) hu.bare hconv
  have hTLip :
      ∀ u, InLowerPinnedMonotoneTrap κ M
        (lowerBarrierRaw κ κtilde D) u → ∀ x y,
          |Tmap u x - Tmap u y| ≤ M * |x - y| := by
    intro u hu x y
    simpa [Tmap] using (hdata u hu.bare).limitLip x y
  refine
    { dim := waveCubeDim
      proj := waveValueProj M
      lift := waveRawLift κ M κtilde D
      eps := waveCubeEps
      localError := waveCubeLocalError M
      eps_pos := waveCubeEps_pos
      proj_trap := ?_
      maps := ?_
      cont := ?_
      lift_trap := ?_
      localError_nonneg := ?_
      localError_tendsto := ?_
      residual_le := ?_ }
  · intro N u hu
    exact waveValueProj_mem_unitCube hM N hu
  · intro N a _ha
    exact waveValueProj_mem_unitCube hM N
      (hTlower (waveRawLift κ M κtilde D N a)
        (waveRawLift_mem_lowerPinned hκpos hgap hD hM.le hplat N a))
  · intro N
    exact (waveTfin_continuous hM hκpos hgap hD hplat
      hcontLower N).continuousOn
  · intro N a _ha
    exact waveRawLift_mem_lowerPinned hκpos hgap hD hM.le hplat N a
  · intro N R
    exact waveCubeLocalError_nonneg hM.le N R
  · intro R _hR
    exact waveCubeLocalError_tendsto
  · intro N a ha hclose R hR x hx
    exact waveCube_residual_le hM hκpos hgap hD hplat hTlower
      hTLip N a ha hclose R hR x hx

/-- Lower-pinned Rothe fixed point with `hprinciple` replaced by finite cube
approximation data. -/
theorem paperLowerPinnedSchauder_fixedPoint_of_cubeApproxData
    (p : CMParams) (c lam M κ : ℝ) (φ : ℝ → ℝ)
    (hM : 0 ≤ M)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ)
    (hŪbdd : IsBddFun (upperBarrier κ M))
    (hHelly : HellyPointwiseSelection M)
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M)
        rotheSeq)
    (hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
        PaperRotheOrbitData p c lam M κ rotheSeq u)
    (hlower : RotheOrbitLowerBound κ M φ rotheSeq)
    (Happrox : LowerPinnedWaveCubeApproxData κ M φ rotheSeq) :
    ∃ U, InLowerPinnedMonotoneTrap κ M φ U ∧
      rotheLimit (rotheSeq U) = U := by
  let Tmap : (ℝ → ℝ) → ℝ → ℝ := fun u => rotheLimit (rotheSeq u)
  have hbareInv :
      ∀ u, InMonotoneWaveTrapSet κ M u → InMonotoneWaveTrapSet κ M (Tmap u) :=
    paperTmap_maps_trap p c lam M κ hM rotheSeq hŪbdd hdata
  have hlowerT :
      ∀ u, InLowerPinnedMonotoneTrap κ M φ u → ∀ x, φ x ≤ Tmap u x :=
    Tmap_lowerInvariant_of_rotheOrbitLowerBound hlower
  have hcont : LocalUniformContinuousOn (InLowerPinnedMonotoneTrap κ M φ) Tmap := by
    intro seq u hseq hu hconv
    exact hdep seq u (fun n => (hseq n).bare) hu.bare hconv
  have hcompactBare :
      LocalUniformSequentiallyCompactRange (InMonotoneWaveTrapSet κ M) Tmap :=
    paperTmap_compactRange p c lam M κ hM rotheSeq hHelly hdata
  have hcompact :
      LocalUniformSequentiallyCompactRange
        (InLowerPinnedMonotoneTrap κ M φ) Tmap := by
    intro seq hseq
    obtain ⟨subseq, hsubseq, U, hUbare, hconv⟩ :=
      hcompactBare seq (fun n => (hseq n).bare)
    refine ⟨subseq, hsubseq, U, ⟨hUbare, ?_⟩, hconv⟩
    intro x
    have hlimit :
        Tendsto (fun n => Tmap (seq (subseq n)) x) atTop (𝓝 (U x)) :=
      hconv.tendsto_at x
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hlimit
      (Filter.Eventually.of_forall fun n =>
        hlowerT (seq (subseq n)) (hseq (subseq n)) x)
  obtain ⟨U, hU, hfix⟩ :=
    localUniformFixedPoint_of_cubeApproxData hcont hcompact
      (ProjectedCubeApproxData.toLocalUniformCubeApproxData Happrox)
  exact ⟨U, hU, by simpa [Tmap] using hfix⟩

theorem b1_chiNeg_existence_paper_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hprodAll : ∀ u, PaperRotheStepProducer p c lam M κ Λ u)
    (hbarLip :
      ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hŪbdd : IsBddFun (upperBarrier κ M))
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M)
      (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond hprodAll))
    (hauxData : ∀ u,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
        ∀ k, (∀ x, lowerBarrierRaw κ κtilde D x ≤
          rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond hprodAll u k x) →
          ∃ C_chem La Lb,
            PaperLowerRawStepAux p c lam M κ κtilde D C_chem La Lb u
              (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond hprodAll u
                (k + 1)))
    (hstationary : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
        rotheLimit
          (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond hprodAll U) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hsmp : StationaryStrongMaxPrinciple p c κ M)
    (hflat : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U := by
  let zseq :=
    rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond hprodAll
  have hM0 : 0 ≤ M := le_trans zero_le_one hcond.hM
  have hcpos : 0 < c := by
    rw [hcond.hc]
    have hinv : 0 < κ⁻¹ := inv_pos.mpr hcond.hκ0
    nlinarith [hcond.hκ0, hinv]
  have hstep :
      RotheStepLowerInvariant κ M (lowerBarrierRaw κ κtilde D) zseq := by
    have haux' : ∀ u,
        InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
          ∀ k, (∀ x, lowerBarrierRaw κ κtilde D x ≤
            rotheSeqOfPaper p c lam M κ Λ u (hprodAll u) hcond.hκ0.le hM0 k x) →
            ∃ C_chem La Lb,
              PaperLowerRawStepAux p c lam M κ κtilde D C_chem La Lb u
                (rotheSeqOfPaper p c lam M κ Λ u (hprodAll u)
                  hcond.hκ0.le hM0 (k + 1)) := by
      simpa [zseq, rotheSeqOfPaperFromCond, hM0] using hauxData
    simpa [zseq, rotheSeqOfPaperFromCond, hM0] using
      rotheSeqOfPaper_lowerBarrierRaw_stepInvariant hcond hD hD_ge_one
        hprodAll hcond.hκ0.le hM0 haux'
  have hlower :
      RotheOrbitLowerBound κ M (lowerBarrierRaw κ κtilde D) zseq :=
    rotheOrbitLowerBound_of_stepLowerInvariant
      (fun u hu => by
        simpa [zseq, rotheSeqOfPaperFromCond, hM0] using
          rotheSeqOfPaper_lowerPinned_base (hprodAll u) hcond.hκ0.le hM0 hu)
      hstep
  have hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperRotheOrbitData p c lam M κ zseq u := by
    intro u _hu
    simpa [zseq, rotheSeqOfPaperFromCond, hM0] using
      paperRotheOrbitData (p := p) (c := c) (lam := lam) (M := M)
        (κ := κ) (Λ := Λ) (u := u) hprodAll hcond.hκ0.le hM0
        hΛ0 hΛM hbarLip
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hcond.hM
  have hgap_pos : 0 < κtilde - κ := sub_pos.mpr hcond.hgap
  have hDpos : 0 < D := D_pos_of_paperDMin_lt hcond hD
  have hExpM :
      Real.exp (-κ * lowerBarrierXPlus κ κtilde D) ≤ M :=
    lowerBarrierExpXPlus_le_one_of_one_le_D hcond.hκ0 hgap_pos
      hD_ge_one hcond.hM
  have hplat : InMonotoneWaveTrapSet κ M
      (lowerBarrierPlateau κ κtilde D) :=
    lowerBarrierPlateau_mem_InMonotoneWaveTrapSet_of_exp_xplus_le
      hcond.hκ0 hgap_pos hDpos hExpM
  have Happrox : LowerPinnedWaveCubeApproxData κ M
      (lowerBarrierRaw κ κtilde D) zseq :=
    lowerPinnedRawWaveCubeApproxData p c lam M κ κtilde D hMpos
      hcond.hκ0 hgap_pos hDpos hplat zseq hŪbdd hdep hdata hlower
  obtain ⟨U, hU, hfix⟩ :=
    paperLowerPinnedSchauder_fixedPoint_of_cubeApproxData p c lam M κ
      (lowerBarrierRaw κ κtilde D) hM0 zseq hŪbdd
      (helly_pointwise_selection M) hdep hdata hlower Happrox
  have hstat : ∀ x, frozenWaveOperator p c U U x = 0 :=
    hstationary U hU (by simpa [zseq] using hfix)
  have hnontriv : ProfileNontrivial U :=
    profileNontrivial_of_lowerBarrierRaw_tail_bound hcond hD
      (fun x _hx => hU.lower x)
  have hpos : ∀ x, 0 < U x :=
    hsmp U hU.bare hstat hnontriv
  have hlim_neg : Tendsto U atBot (𝓝 1) :=
    InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_nontrivial
      hU.bare hsmp hnontriv (hflat U hU hstat) hstat
  have hlim_pos : Tendsto U atTop (𝓝 0) :=
    hU.bare.tendsto_atTop_zero hcond.hκ0
  exact ⟨U, hU,
    FrozenStationaryWaveProfile.mk_auto_limits hcpos hpos
      hU.bare.trap.cunif_bdd hstat hlim_neg hlim_pos⟩

theorem b1_chiNeg_existence_paper'_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hprodAll : ∀ u, PaperLowerRawStepProducer p c lam M κ κtilde D Λ
      hcond.hκ0.le (le_trans zero_le_one hcond.hM) u)
    (hbarLip :
      ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M)
      (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond
        (fun u => (hprodAll u).producer)))
    (hstationary : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
        rotheLimit
          (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond
            (fun u => (hprodAll u).producer) U) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hrealize : StationaryStrongMaxPrincipleODERealization p c κ M)
    (hflat : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_paper_of_cubeApproxData p c lam M κ κtilde D Λ
    hcond hD hD_ge_one hΛ0 hΛM (fun u => (hprodAll u).producer)
    hbarLip (upperBarrier_isBddFun (le_trans zero_le_one hcond.hM))
    hdep (hauxData_of_conditions hcond hD hD_ge_one hprodAll)
    hstationary (hsmp_of_odeRealization hrealize) hflat

theorem b1_chiNeg_existence_paper_clean_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hprodAll : ∀ u, PaperLowerRawStepProducer p c lam M κ κtilde D Λ
      hcond.hκ0.le (le_trans zero_le_one hcond.hM) u)
    (hbarLip :
      ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hstep : PaperRotheSeqStepDependence p c lam M κ Λ
      (fun u => (hprodAll u).producer) hcond.hκ0.le
      (le_trans zero_le_one hcond.hM))
    (htail : PaperRotheTailUniform p c lam M κ Λ
      (fun u => (hprodAll u).producer) hcond.hκ0.le
      (le_trans zero_le_one hcond.hM))
    (hstationary : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
        rotheLimit
          (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond
            (fun u => (hprodAll u).producer) U) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hrealize : StationaryStrongMaxPrincipleODERealization p c κ M)
    (hflat : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_paper'_of_cubeApproxData p c lam M κ κtilde D Λ
    hcond hD hD_ge_one hΛ0 hΛM hprodAll hbarLip
    (by
      simpa [rotheSeqOfPaperFromCond] using
        paperRotheContinuousDependence p c lam M κ Λ
          (fun u => (hprodAll u).producer) hcond.hκ0.le
          (le_trans zero_le_one hcond.hM) hstep htail)
    hstationary hrealize hflat

/-- Clean χ≤0 paper wrapper with the base-barrier Lipschitz scalar condition
discharged from `PaperLemma42ExactConditions`. -/
theorem b1_chiNeg_existence_paper_clean_autoBar_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hprodAll : ∀ u, PaperLowerRawStepProducer p c lam M κ κtilde D Λ
      hcond.hκ0.le (le_trans zero_le_one hcond.hM) u)
    (hstep : PaperRotheSeqStepDependence p c lam M κ Λ
      (fun u => (hprodAll u).producer) hcond.hκ0.le
      (le_trans zero_le_one hcond.hM))
    (htail : PaperRotheTailUniform p c lam M κ Λ
      (fun u => (hprodAll u).producer) hcond.hκ0.le
      (le_trans zero_le_one hcond.hM))
    (hstationary : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
        rotheLimit
          (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond
            (fun u => (hprodAll u).producer) U) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hrealize : StationaryStrongMaxPrincipleODERealization p c κ M)
    (hflat : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_paper_clean_of_cubeApproxData
    p c lam M κ κtilde D Λ hcond hD hD_ge_one hΛ0 hΛM
    hprodAll hcond.upperBarrier_barLip hstep htail hstationary hrealize hflat

/-- Clean χ≤0 paper wrapper using only a tail uniform along each convergent
profile family.  This is the continuity-strength tail actually consumed by the
Schauder map; it does not quantify uniformly over the whole trap. -/
theorem b1_chiNeg_existence_paper_clean_autoBar_tailAlong_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hprodAll : ∀ u, PaperLowerRawStepProducer p c lam M κ κtilde D Λ
      hcond.hκ0.le (le_trans zero_le_one hcond.hM) u)
    (hstep : PaperRotheSeqStepDependence p c lam M κ Λ
      (fun u => (hprodAll u).producer) hcond.hκ0.le
      (le_trans zero_le_one hcond.hM))
    (htail : PaperRotheTailUniformAlongConvergentSeq p c lam M κ Λ
      (fun u => (hprodAll u).producer) hcond.hκ0.le
      (le_trans zero_le_one hcond.hM))
    (hstationary : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
        rotheLimit
          (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond
            (fun u => (hprodAll u).producer) U) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hrealize : StationaryStrongMaxPrincipleODERealization p c κ M)
    (hflat : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_paper'_of_cubeApproxData p c lam M κ κtilde D Λ
    hcond hD hD_ge_one hΛ0 hΛM hprodAll hcond.upperBarrier_barLip
    (by
      simpa [rotheSeqOfPaperFromCond] using
        paperRotheContinuousDependence_of_tailAlongConvergentSeq
          p c lam M κ Λ (fun u => (hprodAll u).producer)
          hcond.hκ0.le (le_trans zero_le_one hcond.hM) hstep htail)
    hstationary hrealize hflat

theorem b1_chiNeg_existence_paper_min_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hpar :
      PaperLowerRawParabolicFloor p c lam M κ κtilde D Λ
        hcond.hκ0.le (le_trans zero_le_one hcond.hM))
    (hconv :
      PaperLowerPinnedStationaryFlatFloor p c κ M
        (lowerBarrierRaw κ κtilde D)
        (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond
          (fun u => (hpar.producer u).producer)))
    (hsmp : StationaryStrongMaxPrinciple p c κ M) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_paper_of_cubeApproxData p c lam M κ κtilde D Λ
    hcond hD hD_ge_one hΛ0 hΛM
    (fun u => (hpar.producer u).producer) hpar.barLip
    (upperBarrier_isBddFun (le_trans zero_le_one hcond.hM))
    (by
      simpa [rotheSeqOfPaperFromCond] using
        paperRotheContinuousDependence p c lam M κ Λ
          (fun u => (hpar.producer u).producer) hcond.hκ0.le
          (le_trans zero_le_one hcond.hM) hpar.step hpar.tail)
    (hauxData_of_conditions hcond hD hD_ge_one hpar.producer)
    hconv.stationary hsmp hconv.flat

/-- Minimal χ≤0 paper wrapper with the base-barrier Lipschitz field removed
from the parabolic floor package. -/
theorem b1_chiNeg_existence_paper_min_noBar_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hpar :
      PaperLowerRawParabolicFloorNoBar p c lam M κ κtilde D Λ
        hcond.hκ0.le (le_trans zero_le_one hcond.hM))
    (hconv :
      PaperLowerPinnedStationaryFlatFloor p c κ M
        (lowerBarrierRaw κ κtilde D)
        (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond
          (fun u => (hpar.producer u).producer)))
    (hsmp : StationaryStrongMaxPrinciple p c κ M) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_paper_min_of_cubeApproxData
    p c lam M κ κtilde D Λ hcond hD hD_ge_one hΛ0 hΛM
    (paperLowerRawParabolicFloor_of_noBar hcond hpar) hconv hsmp

theorem b1_chiNeg_existence_paper_min_core_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hpar :
      PaperLowerRawParabolicFloorCore p c lam M κ κtilde D Λ
        hcond.hκ0.le (le_trans zero_le_one hcond.hM))
    (hconv :
      PaperLowerPinnedStationaryFlatFloor p c κ M
        (lowerBarrierRaw κ κtilde D)
        (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond
          (fun u =>
            (paperLowerRawParabolicFloor_of_core hpar).producer u |>.producer)))
    (hsmp : StationaryStrongMaxPrinciple p c κ M) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_paper_min_of_cubeApproxData p c lam M κ κtilde D Λ
    hcond hD hD_ge_one hΛ0 hΛM
    (paperLowerRawParabolicFloor_of_core hpar) hconv hsmp

/-- Minimal core χ≤0 paper wrapper with the base-barrier Lipschitz field
removed from the core parabolic floor package. -/
theorem b1_chiNeg_existence_paper_min_core_noBar_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hpar :
      PaperLowerRawParabolicFloorCoreNoBar p c lam M κ κtilde D Λ
        hcond.hκ0.le (le_trans zero_le_one hcond.hM))
    (hconv :
      PaperLowerPinnedStationaryFlatFloor p c κ M
        (lowerBarrierRaw κ κtilde D)
        (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond
          (fun u =>
            (paperLowerRawParabolicFloor_of_core
              (paperLowerRawParabolicFloorCore_of_noBar hcond hpar)).producer u
              |>.producer)))
    (hsmp : StationaryStrongMaxPrinciple p c κ M) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_paper_min_core_of_cubeApproxData
    p c lam M κ κtilde D Λ hcond hD hD_ge_one hΛ0 hΛM
    (paperLowerRawParabolicFloorCore_of_noBar hcond hpar) hconv hsmp

/-- Route-A headline wrapper: the old all-`u` producer hypothesis is replaced
by the Route-A parabolic floor.  The actual per-step producer is obtained by
`paperRotheStepProducer_of_routeA_greenCore`, whose output now threads the paper
super-solution of the previous iterate through the Rothe orbit. -/
theorem b1_chiNeg_existence_paper_routeA_core_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hpar :
      PaperLowerRawParabolicFloorRouteACore p c lam M κ κtilde D Λ
        hcond.hκ0.le (le_trans zero_le_one hcond.hM))
    (hconv :
      PaperLowerPinnedStationaryFlatFloor p c κ M
        (lowerBarrierRaw κ κtilde D)
        (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond
          (fun u =>
            (paperLowerRawParabolicFloor_of_routeA_core hpar).producer u
              |>.producer)))
    (hsmp : StationaryStrongMaxPrinciple p c κ M) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_paper_min_of_cubeApproxData p c lam M κ κtilde D Λ
    hcond hD hD_ge_one hΛ0 hΛM
    (paperLowerRawParabolicFloor_of_routeA_core hpar) hconv hsmp

/-- Route-A headline wrapper with the base-barrier Lipschitz scalar condition
discharged from `PaperLemma42ExactConditions`. -/
theorem b1_chiNeg_existence_paper_routeA_core_noBar_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hpar :
      PaperLowerRawParabolicFloorRouteACoreNoBar p c lam M κ κtilde D Λ
        hcond.hκ0.le (le_trans zero_le_one hcond.hM))
    (hconv :
      PaperLowerPinnedStationaryFlatFloor p c κ M
        (lowerBarrierRaw κ κtilde D)
        (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond
          (fun u =>
            (paperLowerRawParabolicFloor_of_routeA_core
              (paperLowerRawParabolicFloorRouteACore_of_noBar hcond hpar)).producer u
              |>.producer)))
    (hsmp : StationaryStrongMaxPrinciple p c κ M) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_paper_routeA_core_of_cubeApproxData
    p c lam M κ κtilde D Λ hcond hD hD_ge_one hΛ0 hΛM
    (paperLowerRawParabolicFloorRouteACore_of_noBar hcond hpar) hconv hsmp

theorem b1_chiPos_existence_paper_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hprodAll : ∀ u, PaperRotheStepProducer p c lam M κ Λ u)
    (hbarLip :
      ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hŪbdd : IsBddFun (upperBarrier κ M))
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M)
      (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond hprodAll))
    (hauxData : ∀ u,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
        ∀ k, (∀ x, lowerBarrierRaw κ κtilde D x ≤
          rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
            hprodAll u k x) →
          ∃ C_chem La Lb,
            PaperLowerRawStepAux p c lam M κ κtilde D C_chem La Lb u
              (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
                hprodAll u (k + 1)))
    (hstationary : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
        rotheLimit
          (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
            hprodAll U) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hsmp : StationaryStrongMaxPrinciple p c κ M)
    (hflat : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U := by
  let zseq :=
    rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond hprodAll
  have hM0 : 0 ≤ M := le_trans zero_le_one hcond.hM
  have hcpos : 0 < c := by
    rw [hcond.hc]
    have hinv : 0 < κ⁻¹ := inv_pos.mpr hcond.hκ0
    nlinarith [hcond.hκ0, hinv]
  have hstep :
      RotheStepLowerInvariant κ M (lowerBarrierRaw κ κtilde D) zseq := by
    have haux' : ∀ u,
        InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
          ∀ k, (∀ x, lowerBarrierRaw κ κtilde D x ≤
            rotheSeqOfPaper p c lam M κ Λ u (hprodAll u) hcond.hκ0.le hM0 k x) →
            ∃ C_chem La Lb,
              PaperLowerRawStepAux p c lam M κ κtilde D C_chem La Lb u
                (rotheSeqOfPaper p c lam M κ Λ u (hprodAll u)
                  hcond.hκ0.le hM0 (k + 1)) := by
      simpa [zseq, rotheSeqOfPaperFromPositiveCond, hM0] using hauxData
    simpa [zseq, rotheSeqOfPaperFromPositiveCond, hM0] using
      rotheSeqOfPaper_lowerBarrierRaw_positive_stepInvariant hcond hD
        hD_ge_one hprodAll hcond.hκ0.le hM0 haux'
  have hlower :
      RotheOrbitLowerBound κ M (lowerBarrierRaw κ κtilde D) zseq :=
    rotheOrbitLowerBound_of_stepLowerInvariant
      (fun u hu => by
        simpa [zseq, rotheSeqOfPaperFromPositiveCond, hM0] using
          rotheSeqOfPaper_lowerPinned_base (hprodAll u) hcond.hκ0.le hM0 hu)
      hstep
  have hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperRotheOrbitData p c lam M κ zseq u := by
    intro u _hu
    simpa [zseq, rotheSeqOfPaperFromPositiveCond, hM0] using
      paperRotheOrbitData (p := p) (c := c) (lam := lam) (M := M)
        (κ := κ) (Λ := Λ) (u := u) hprodAll hcond.hκ0.le hM0
        hΛ0 hΛM hbarLip
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hcond.hM
  have hgap_pos : 0 < κtilde - κ := sub_pos.mpr hcond.hgap
  have hDpos : 0 < D := D_pos_of_positive_paperDMin_lt hcond hD
  have hExpM :
      Real.exp (-κ * lowerBarrierXPlus κ κtilde D) ≤ M :=
    lowerBarrierExpXPlus_le_one_of_one_le_D hcond.hκ0 hgap_pos
      hD_ge_one hcond.hM
  have hplat : InMonotoneWaveTrapSet κ M
      (lowerBarrierPlateau κ κtilde D) :=
    lowerBarrierPlateau_mem_InMonotoneWaveTrapSet_of_exp_xplus_le
      hcond.hκ0 hgap_pos hDpos hExpM
  have Happrox : LowerPinnedWaveCubeApproxData κ M
      (lowerBarrierRaw κ κtilde D) zseq :=
    lowerPinnedRawWaveCubeApproxData p c lam M κ κtilde D hMpos
      hcond.hκ0 hgap_pos hDpos hplat zseq hŪbdd hdep hdata hlower
  obtain ⟨U, hU, hfix⟩ :=
    paperLowerPinnedSchauder_fixedPoint_of_cubeApproxData p c lam M κ
      (lowerBarrierRaw κ κtilde D) hM0 zseq hŪbdd
      (helly_pointwise_selection M) hdep hdata hlower Happrox
  have hstat : ∀ x, frozenWaveOperator p c U U x = 0 :=
    hstationary U hU (by simpa [zseq] using hfix)
  have hnontriv : ProfileNontrivial U :=
    profileNontrivial_of_lowerBarrierRaw_positive_tail_bound hcond hD
      (fun x _hx => hU.lower x)
  have hpos : ∀ x, 0 < U x :=
    hsmp U hU.bare hstat hnontriv
  have hlim_neg : Tendsto U atBot (𝓝 1) :=
    InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_nontrivial
      hU.bare hsmp hnontriv (hflat U hU hstat) hstat
  have hlim_pos : Tendsto U atTop (𝓝 0) :=
    hU.bare.tendsto_atTop_zero hcond.hκ0
  exact ⟨U, hU,
    FrozenStationaryWaveProfile.mk_auto_limits hcpos hpos
      hU.bare.trap.cunif_bdd hstat hlim_neg hlim_pos⟩

theorem b1_chiPos_existence_paper'_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hprodAll : ∀ u, PaperLowerRawStepProducer p c lam M κ κtilde D Λ
      hcond.hκ0.le (le_trans zero_le_one hcond.hM) u)
    (hbarLip :
      ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M)
      (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
        (fun u => (hprodAll u).producer)))
    (hstationary : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
        rotheLimit
          (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
            (fun u => (hprodAll u).producer) U) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hrealize : StationaryStrongMaxPrincipleODERealization p c κ M)
    (hflat : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiPos_existence_paper_of_cubeApproxData p c lam M κ κtilde D Λ
    hcond hD hD_ge_one hΛ0 hΛM (fun u => (hprodAll u).producer)
    hbarLip (upperBarrier_isBddFun (le_trans zero_le_one hcond.hM))
    hdep (hauxData_of_positive_conditions hcond hD hD_ge_one hprodAll)
    hstationary (hsmp_of_odeRealization hrealize) hflat

theorem b1_chiPos_existence_paper_clean_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hprodAll : ∀ u, PaperLowerRawStepProducer p c lam M κ κtilde D Λ
      hcond.hκ0.le (le_trans zero_le_one hcond.hM) u)
    (hbarLip :
      ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hstep : PaperRotheSeqStepDependence p c lam M κ Λ
      (fun u => (hprodAll u).producer) hcond.hκ0.le
      (le_trans zero_le_one hcond.hM))
    (htail : PaperRotheTailUniform p c lam M κ Λ
      (fun u => (hprodAll u).producer) hcond.hκ0.le
      (le_trans zero_le_one hcond.hM))
    (hstationary : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
        rotheLimit
          (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
            (fun u => (hprodAll u).producer) U) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hrealize : StationaryStrongMaxPrincipleODERealization p c κ M)
    (hflat : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiPos_existence_paper'_of_cubeApproxData p c lam M κ κtilde D Λ
    hcond hD hD_ge_one hΛ0 hΛM hprodAll hbarLip
    (by
      simpa [rotheSeqOfPaperFromPositiveCond] using
        paperRotheContinuousDependence p c lam M κ Λ
          (fun u => (hprodAll u).producer) hcond.hκ0.le
          (le_trans zero_le_one hcond.hM) hstep htail)
    hstationary hrealize hflat

/-- Clean χ≥0 paper wrapper with the base-barrier Lipschitz scalar condition
discharged from `PositivePaperLemma42ExactConditions`. -/
theorem b1_chiPos_existence_paper_clean_autoBar_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hprodAll : ∀ u, PaperLowerRawStepProducer p c lam M κ κtilde D Λ
      hcond.hκ0.le (le_trans zero_le_one hcond.hM) u)
    (hstep : PaperRotheSeqStepDependence p c lam M κ Λ
      (fun u => (hprodAll u).producer) hcond.hκ0.le
      (le_trans zero_le_one hcond.hM))
    (htail : PaperRotheTailUniform p c lam M κ Λ
      (fun u => (hprodAll u).producer) hcond.hκ0.le
      (le_trans zero_le_one hcond.hM))
    (hstationary : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
        rotheLimit
          (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
            (fun u => (hprodAll u).producer) U) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hrealize : StationaryStrongMaxPrincipleODERealization p c κ M)
    (hflat : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiPos_existence_paper_clean_of_cubeApproxData
    p c lam M κ κtilde D Λ hcond hD hD_ge_one hΛ0 hΛM
    hprodAll hcond.upperBarrier_barLip hstep htail hstationary hrealize hflat

/-- Clean χ≥0 paper wrapper using only a tail uniform along each convergent
profile family. -/
theorem b1_chiPos_existence_paper_clean_autoBar_tailAlong_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hprodAll : ∀ u, PaperLowerRawStepProducer p c lam M κ κtilde D Λ
      hcond.hκ0.le (le_trans zero_le_one hcond.hM) u)
    (hstep : PaperRotheSeqStepDependence p c lam M κ Λ
      (fun u => (hprodAll u).producer) hcond.hκ0.le
      (le_trans zero_le_one hcond.hM))
    (htail : PaperRotheTailUniformAlongConvergentSeq p c lam M κ Λ
      (fun u => (hprodAll u).producer) hcond.hκ0.le
      (le_trans zero_le_one hcond.hM))
    (hstationary : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
        rotheLimit
          (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
            (fun u => (hprodAll u).producer) U) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hrealize : StationaryStrongMaxPrincipleODERealization p c κ M)
    (hflat : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiPos_existence_paper'_of_cubeApproxData p c lam M κ κtilde D Λ
    hcond hD hD_ge_one hΛ0 hΛM hprodAll hcond.upperBarrier_barLip
    (by
      simpa [rotheSeqOfPaperFromPositiveCond] using
        paperRotheContinuousDependence_of_tailAlongConvergentSeq
          p c lam M κ Λ (fun u => (hprodAll u).producer)
          hcond.hκ0.le (le_trans zero_le_one hcond.hM) hstep htail)
    hstationary hrealize hflat

theorem b1_chiPos_existence_paper_min_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hpar :
      PaperLowerRawParabolicFloor p c lam M κ κtilde D Λ
        hcond.hκ0.le (le_trans zero_le_one hcond.hM))
    (hconv :
      PaperLowerPinnedStationaryFlatFloor p c κ M
        (lowerBarrierRaw κ κtilde D)
        (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
          (fun u => (hpar.producer u).producer)))
    (hsmp : StationaryStrongMaxPrinciple p c κ M) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiPos_existence_paper_of_cubeApproxData p c lam M κ κtilde D Λ
    hcond hD hD_ge_one hΛ0 hΛM
    (fun u => (hpar.producer u).producer) hpar.barLip
    (upperBarrier_isBddFun (le_trans zero_le_one hcond.hM))
    (by
      simpa [rotheSeqOfPaperFromPositiveCond] using
        paperRotheContinuousDependence p c lam M κ Λ
          (fun u => (hpar.producer u).producer) hcond.hκ0.le
          (le_trans zero_le_one hcond.hM) hpar.step hpar.tail)
    (hauxData_of_positive_conditions hcond hD hD_ge_one hpar.producer)
    hconv.stationary hsmp hconv.flat

/-- Minimal χ≥0 paper wrapper with the base-barrier Lipschitz field removed
from the parabolic floor package. -/
theorem b1_chiPos_existence_paper_min_noBar_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hpar :
      PaperLowerRawParabolicFloorNoBar p c lam M κ κtilde D Λ
        hcond.hκ0.le (le_trans zero_le_one hcond.hM))
    (hconv :
      PaperLowerPinnedStationaryFlatFloor p c κ M
        (lowerBarrierRaw κ κtilde D)
        (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
          (fun u => (hpar.producer u).producer)))
    (hsmp : StationaryStrongMaxPrinciple p c κ M) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiPos_existence_paper_min_of_cubeApproxData
    p c lam M κ κtilde D Λ hcond hD hD_ge_one hΛ0 hΛM
    (PositivePaperLemma42ExactConditions.paperLowerRawParabolicFloor_of_noBar
      hcond hpar)
    hconv hsmp

theorem b1_chiPos_existence_paper_min_core_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hpar :
      PaperLowerRawParabolicFloorCore p c lam M κ κtilde D Λ
        hcond.hκ0.le (le_trans zero_le_one hcond.hM))
    (hconv :
      PaperLowerPinnedStationaryFlatFloor p c κ M
        (lowerBarrierRaw κ κtilde D)
        (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
          (fun u =>
            (paperLowerRawParabolicFloor_of_core hpar).producer u |>.producer)))
    (hsmp : StationaryStrongMaxPrinciple p c κ M) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiPos_existence_paper_min_of_cubeApproxData p c lam M κ κtilde D Λ
    hcond hD hD_ge_one hΛ0 hΛM
    (paperLowerRawParabolicFloor_of_core hpar) hconv hsmp

/-- Minimal core χ≥0 paper wrapper with the base-barrier Lipschitz field
removed from the core parabolic floor package. -/
theorem b1_chiPos_existence_paper_min_core_noBar_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hpar :
      PaperLowerRawParabolicFloorCoreNoBar p c lam M κ κtilde D Λ
        hcond.hκ0.le (le_trans zero_le_one hcond.hM))
    (hconv :
      PaperLowerPinnedStationaryFlatFloor p c κ M
        (lowerBarrierRaw κ κtilde D)
        (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
          (fun u =>
            (paperLowerRawParabolicFloor_of_core
              (PositivePaperLemma42ExactConditions.paperLowerRawParabolicFloorCore_of_noBar
                hcond hpar)).producer u |>.producer)))
    (hsmp : StationaryStrongMaxPrinciple p c κ M) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiPos_existence_paper_min_core_of_cubeApproxData
    p c lam M κ κtilde D Λ hcond hD hD_ge_one hΛ0 hΛM
    (PositivePaperLemma42ExactConditions.paperLowerRawParabolicFloorCore_of_noBar
      hcond hpar)
    hconv hsmp

/-- Fill the `barLip` field of the Route-A floor from the positive paper Lemma
4.2 parameter conditions. -/
def positivePaperLowerRawParabolicFloorRouteACore_of_noBar
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (h : PaperLowerRawParabolicFloorRouteACoreNoBar
      p c lam M κ κtilde D Λ hκ hM) :
    PaperLowerRawParabolicFloorRouteACore
      p c lam M κ κtilde D Λ hκ hM where
  producer := h.producer
  barLip := hcond.upperBarrier_barLip
  step := h.step
  tail := h.tail

/-- Route-A χ≥0 wrapper: the old all-`u` producer hypothesis is replaced by
the Route-A parabolic floor. -/
theorem b1_chiPos_existence_paper_routeA_core_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hpar :
      PaperLowerRawParabolicFloorRouteACore p c lam M κ κtilde D Λ
        hcond.hκ0.le (le_trans zero_le_one hcond.hM))
    (hconv :
      PaperLowerPinnedStationaryFlatFloor p c κ M
        (lowerBarrierRaw κ κtilde D)
        (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
          (fun u =>
            (paperLowerRawParabolicFloor_of_routeA_core hpar).producer u
              |>.producer)))
    (hsmp : StationaryStrongMaxPrinciple p c κ M) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiPos_existence_paper_min_of_cubeApproxData p c lam M κ κtilde D Λ
    hcond hD hD_ge_one hΛ0 hΛM
    (paperLowerRawParabolicFloor_of_routeA_core hpar) hconv hsmp

/-- Route-A χ≥0 wrapper with the base-barrier Lipschitz scalar condition
discharged from `PositivePaperLemma42ExactConditions`. -/
theorem b1_chiPos_existence_paper_routeA_core_noBar_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hpar :
      PaperLowerRawParabolicFloorRouteACoreNoBar p c lam M κ κtilde D Λ
        hcond.hκ0.le (le_trans zero_le_one hcond.hM))
    (hconv :
      PaperLowerPinnedStationaryFlatFloor p c κ M
        (lowerBarrierRaw κ κtilde D)
        (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
          (fun u =>
            (paperLowerRawParabolicFloor_of_routeA_core
              (positivePaperLowerRawParabolicFloorRouteACore_of_noBar
                hcond hpar)).producer u
              |>.producer)))
    (hsmp : StationaryStrongMaxPrinciple p c κ M) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiPos_existence_paper_routeA_core_of_cubeApproxData
    p c lam M κ κtilde D Λ hcond hD hD_ge_one hΛ0 hΛM
    (positivePaperLowerRawParabolicFloorRouteACore_of_noBar hcond hpar)
    hconv hsmp

#print axioms paperLowerPinnedSchauder_fixedPoint_of_cubeApproxData
#print axioms b1_chiNeg_existence_paper_of_cubeApproxData
#print axioms b1_chiNeg_existence_paper'_of_cubeApproxData
#print axioms b1_chiNeg_existence_paper_clean_of_cubeApproxData
#print axioms b1_chiNeg_existence_paper_clean_autoBar_of_cubeApproxData
#print axioms b1_chiNeg_existence_paper_clean_autoBar_tailAlong_of_cubeApproxData
#print axioms b1_chiNeg_existence_paper_min_of_cubeApproxData
#print axioms b1_chiNeg_existence_paper_min_noBar_of_cubeApproxData
#print axioms b1_chiNeg_existence_paper_min_core_of_cubeApproxData
#print axioms b1_chiNeg_existence_paper_min_core_noBar_of_cubeApproxData
#print axioms b1_chiNeg_existence_paper_routeA_core_of_cubeApproxData
#print axioms b1_chiNeg_existence_paper_routeA_core_noBar_of_cubeApproxData
#print axioms b1_chiPos_existence_paper_of_cubeApproxData
#print axioms b1_chiPos_existence_paper'_of_cubeApproxData
#print axioms b1_chiPos_existence_paper_clean_of_cubeApproxData
#print axioms b1_chiPos_existence_paper_clean_autoBar_of_cubeApproxData
#print axioms b1_chiPos_existence_paper_clean_autoBar_tailAlong_of_cubeApproxData
#print axioms b1_chiPos_existence_paper_min_of_cubeApproxData
#print axioms b1_chiPos_existence_paper_min_noBar_of_cubeApproxData
#print axioms b1_chiPos_existence_paper_min_core_of_cubeApproxData
#print axioms b1_chiPos_existence_paper_min_core_noBar_of_cubeApproxData
#print axioms b1_chiPos_existence_paper_routeA_core_of_cubeApproxData
#print axioms b1_chiPos_existence_paper_routeA_core_noBar_of_cubeApproxData

end

end ShenWork.Paper1
