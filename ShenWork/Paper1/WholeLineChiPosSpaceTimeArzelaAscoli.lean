import ShenWork.Paper1.WholeLineChiPosEntropyFarLeftNormalFamily
import ShenWork.Paper1.WaveRotheHelly

/-!
# A space-time Arzelà--Ascoli theorem for far-left translates

This is the two-variable normal-family argument needed by the whole-line
far-left route.  Its hypotheses are deliberately eventual on each compact
box: a translate with center time tending to infinity need not have uniform
estimates on a fixed box for the first finitely many indices.

The proof uses Tychonoff sequential compactness on the countable dense set
`ℚ × ℚ`, upgrades the rational diagonal to pointwise convergence by local
equicontinuity, and then uses a finite two-dimensional grid to obtain local
uniform convergence.
-/

open Filter Real Set Topology

noncomputable section

namespace ShenWork.Paper1

/-- Eventual uniform boundedness on each compact space-time box. -/
def SpaceTimeLocallyEquibounded (seq : ℕ → ℝ → ℝ → ℝ) : Prop :=
  ∀ R > 0, ∃ B : ℝ, ∀ᶠ n in atTop,
    ∀ t ∈ Set.Icc (-R) R, ∀ x ∈ Set.Icc (-R) R, |seq n t x| ≤ B

namespace SpaceTimeLocallyEquibounded

theorem comp_strictMono
    {seq : ℕ → ℝ → ℝ → ℝ} {subseq : ℕ → ℕ}
    (h : SpaceTimeLocallyEquibounded seq) (hsubseq : StrictMono subseq) :
    SpaceTimeLocallyEquibounded (fun n => seq (subseq n)) := by
  intro R hR
  obtain ⟨B, hev⟩ := h R hR
  exact ⟨B, hsubseq.tendsto_atTop.eventually hev⟩

end SpaceTimeLocallyEquibounded

/-- Eventual equicontinuity on each compact space-time box.  The same `δ`
controls the time and space coordinates in the max-product metric. -/
def SpaceTimeLocallyEquicontinuous (seq : ℕ → ℝ → ℝ → ℝ) : Prop :=
  ∀ R > 0, ∀ ε > 0, ∃ δ > 0, ∀ᶠ n in atTop,
    ∀ t ∈ Set.Icc (-R) R, ∀ s ∈ Set.Icc (-R) R,
    ∀ x ∈ Set.Icc (-R) R, ∀ y ∈ Set.Icc (-R) R,
      |t - s| < δ → |x - y| < δ → |seq n t x - seq n s y| < ε

namespace SpaceTimeLocallyEquicontinuous

theorem comp_strictMono
    {seq : ℕ → ℝ → ℝ → ℝ} {subseq : ℕ → ℕ}
    (h : SpaceTimeLocallyEquicontinuous seq) (hsubseq : StrictMono subseq) :
    SpaceTimeLocallyEquicontinuous (fun n => seq (subseq n)) := by
  intro R hR ε hε
  obtain ⟨δ, hδ, hev⟩ := h R hR ε hε
  exact ⟨δ, hδ, hsubseq.tendsto_atTop.eventually hev⟩

end SpaceTimeLocallyEquicontinuous

namespace SpaceTimeLocallyUniformConverges

theorem comp_strictMono
    {seq : ℕ → ℝ → ℝ → ℝ} {limit : ℝ → ℝ → ℝ}
    {subseq : ℕ → ℕ}
    (h : SpaceTimeLocallyUniformConverges seq limit)
    (hsubseq : StrictMono subseq) :
    SpaceTimeLocallyUniformConverges (fun n => seq (subseq n)) limit := by
  intro R hR ε hε
  exact hsubseq.tendsto_atTop.eventually (h R hR ε hε)

end SpaceTimeLocallyUniformConverges

/-- Eventual local boundedness implies boundedness of the value sequence at
each fixed space-time point, including its finite initial prefix. -/
private theorem exists_coordinate_bound
    {seq : ℕ → ℝ → ℝ → ℝ}
    (hbound : SpaceTimeLocallyEquibounded seq) (t x : ℝ) :
    ∃ C : ℝ, ∀ n : ℕ, |seq n t x| ≤ C := by
  let R : ℝ := max |t| |x| + 1
  have hR : 0 < R := by
    dsimp only [R]
    have hmax : 0 ≤ max |t| |x| :=
      le_trans (abs_nonneg t) (le_max_left _ _)
    linarith
  have htR : t ∈ Set.Icc (-R) R := by
    apply abs_le.mp
    dsimp only [R]
    exact le_trans (le_max_left |t| |x|) (le_add_of_nonneg_right zero_le_one)
  have hxR : x ∈ Set.Icc (-R) R := by
    apply abs_le.mp
    dsimp only [R]
    exact le_trans (le_max_right |t| |x|) (le_add_of_nonneg_right zero_le_one)
  obtain ⟨B, hB⟩ := hbound R hR
  rcases eventually_atTop.1 hB with ⟨N, hN⟩
  let C : ℝ := |B| + ∑ i ∈ Finset.range N, |seq i t x|
  refine ⟨C, ?_⟩
  intro n
  by_cases hn : n < N
  · have hsingle : |seq n t x| ≤ ∑ i ∈ Finset.range N, |seq i t x| :=
      Finset.single_le_sum
        (fun i _hi => abs_nonneg (seq i t x)) (Finset.mem_range.mpr hn)
    exact le_trans hsingle (by
      dsimp only [C]
      exact le_add_of_nonneg_left (abs_nonneg B))
  · have hnN : N ≤ n := Nat.le_of_not_gt hn
    have htail := hN n hnN t htR x hxR
    have hsum_nonneg : 0 ≤ ∑ i ∈ Finset.range N, |seq i t x| :=
      Finset.sum_nonneg fun i _hi => abs_nonneg (seq i t x)
    exact le_trans htail <| le_trans (le_abs_self B) <| by
      dsimp only [C]
      exact le_add_of_nonneg_right hsum_nonneg

/-- Tychonoff diagonal extraction on the dense set `ℚ × ℚ`. -/
private theorem spaceTime_rational_diagonal
    (seq : ℕ → ℝ → ℝ → ℝ)
    (hbound : SpaceTimeLocallyEquibounded seq) :
    ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
      ∃ f₀ : ℚ × ℚ → ℝ, ∀ q : ℚ × ℚ,
        Tendsto (fun n => seq (subseq n) (q.1 : ℝ) (q.2 : ℝ))
          atTop (𝓝 (f₀ q)) := by
  have hcoord : ∀ q : ℚ × ℚ, ∃ C : ℝ,
      ∀ n : ℕ, |seq n (q.1 : ℝ) (q.2 : ℝ)| ≤ C := by
    intro q
    exact exists_coordinate_bound hbound (q.1 : ℝ) (q.2 : ℝ)
  let C : ℚ × ℚ → ℝ := fun q => Classical.choose (hcoord q)
  have hC : ∀ q n, |seq n (q.1 : ℝ) (q.2 : ℝ)| ≤ C q := by
    intro q
    exact Classical.choose_spec (hcoord q)
  let S : Set ((ℚ × ℚ) → ℝ) :=
    Set.pi Set.univ (fun q => Set.Icc (-C q) (C q))
  have hScompact : IsCompact S :=
    isCompact_univ_pi (fun q : ℚ × ℚ => isCompact_Icc)
  let F : ℕ → ((ℚ × ℚ) → ℝ) :=
    fun n q => seq n (q.1 : ℝ) (q.2 : ℝ)
  have hFmem : ∀ n, F n ∈ S := by
    intro n q _hq
    exact abs_le.mp (hC q n)
  obtain ⟨f₀, _hf₀, subseq, hsubseq, hconv⟩ :=
    hScompact.isSeqCompact hFmem
  refine ⟨subseq, hsubseq, f₀, ?_⟩
  have hpoint :=
    (tendsto_pi_nhds (f := F ∘ subseq) (g := f₀) (u := atTop)).1 hconv
  intro q
  exact hpoint q

/-- The rational diagonal and local equicontinuity give a subsequence
converging at every real space-time point. -/
private theorem exists_spaceTime_pointwise_subsequence
    (seq : ℕ → ℝ → ℝ → ℝ)
    (hbound : SpaceTimeLocallyEquibounded seq)
    (hequicont : SpaceTimeLocallyEquicontinuous seq) :
    ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
      ∃ limit : ℝ → ℝ → ℝ, ∀ t x,
        Tendsto (fun n => seq (subseq n) t x) atTop (𝓝 (limit t x)) := by
  obtain ⟨subseq, hsubseq, f₀, hrat⟩ :=
    spaceTime_rational_diagonal seq hbound
  have hcauchy : ∀ t x : ℝ, CauchySeq (fun n => seq (subseq n) t x) := by
    intro t x
    rw [Metric.cauchySeq_iff]
    intro ε hε
    let R : ℝ := max |t| |x| + 2
    have hR : 0 < R := by
      dsimp only [R]
      have hmax : 0 ≤ max |t| |x| :=
        le_trans (abs_nonneg t) (le_max_left _ _)
      linarith
    obtain ⟨δ₀, hδ₀, heq⟩ := hequicont R hR (ε / 3) (by linarith)
    let δ : ℝ := min δ₀ 1
    have hδ : 0 < δ := lt_min hδ₀ zero_lt_one
    obtain ⟨qt, hqt⟩ := exists_rat_near t hδ
    obtain ⟨qx, hqx⟩ := exists_rat_near x hδ
    have htR : t ∈ Set.Icc (-R) R := by
      apply abs_le.mp
      dsimp only [R]
      linarith [le_max_left |t| |x|]
    have hxR : x ∈ Set.Icc (-R) R := by
      apply abs_le.mp
      dsimp only [R]
      linarith [le_max_right |t| |x|]
    have hqtR : (qt : ℝ) ∈ Set.Icc (-R) R := by
      apply abs_le.mp
      have hqt_one : |t - (qt : ℝ)| < 1 :=
        lt_of_lt_of_le hqt (le_trans (min_le_right _ _) le_rfl)
      have habs : |(qt : ℝ)| ≤ |t| + |t - (qt : ℝ)| := by
        calc
          |(qt : ℝ)| = |t + ((qt : ℝ) - t)| := by ring_nf
          _ ≤ |t| + |(qt : ℝ) - t| := abs_add_le _ _
          _ = |t| + |t - (qt : ℝ)| := by rw [abs_sub_comm]
      dsimp only [R]
      linarith [le_max_left |t| |x|]
    have hqxR : (qx : ℝ) ∈ Set.Icc (-R) R := by
      apply abs_le.mp
      have hqx_one : |x - (qx : ℝ)| < 1 :=
        lt_of_lt_of_le hqx (le_trans (min_le_right _ _) le_rfl)
      have habs : |(qx : ℝ)| ≤ |x| + |x - (qx : ℝ)| := by
        calc
          |(qx : ℝ)| = |x + ((qx : ℝ) - x)| := by ring_nf
          _ ≤ |x| + |(qx : ℝ) - x| := abs_add_le _ _
          _ = |x| + |x - (qx : ℝ)| := by rw [abs_sub_comm]
      dsimp only [R]
      linarith [le_max_right |t| |x|]
    have hqtδ : |t - (qt : ℝ)| < δ₀ :=
      lt_of_lt_of_le hqt (min_le_left _ _)
    have hqxδ : |x - (qx : ℝ)| < δ₀ :=
      lt_of_lt_of_le hqx (min_le_left _ _)
    have heqSub := hsubseq.tendsto_atTop.eventually heq
    rcases eventually_atTop.1 heqSub with ⟨Neq, hNeq⟩
    have hratCauchy :
        CauchySeq (fun n => seq (subseq n) (qt : ℝ) (qx : ℝ)) :=
      (hrat (qt, qx)).cauchySeq
    rw [Metric.cauchySeq_iff] at hratCauchy
    obtain ⟨Nrat, hNrat⟩ := hratCauchy (ε / 3) (by linarith)
    refine ⟨max Neq Nrat, ?_⟩
    intro m hm n hn
    have hmEq : Neq ≤ m := le_trans (le_max_left _ _) hm
    have hnEq : Neq ≤ n := le_trans (le_max_left _ _) hn
    have hmRat : Nrat ≤ m := le_trans (le_max_right _ _) hm
    have hnRat : Nrat ≤ n := le_trans (le_max_right _ _) hn
    have hleft :
        |seq (subseq m) t x - seq (subseq m) (qt : ℝ) (qx : ℝ)| < ε / 3 :=
      hNeq m hmEq t htR qt hqtR x hxR qx hqxR hqtδ hqxδ
    have hright :
        |seq (subseq n) t x - seq (subseq n) (qt : ℝ) (qx : ℝ)| < ε / 3 :=
      hNeq n hnEq t htR qt hqtR x hxR qx hqxR hqtδ hqxδ
    have hmiddle := hNrat m hmRat n hnRat
    rw [Real.dist_eq] at hmiddle ⊢
    have htri :
        |seq (subseq m) t x - seq (subseq n) t x| ≤
          |seq (subseq m) t x - seq (subseq m) (qt : ℝ) (qx : ℝ)| +
          |seq (subseq m) (qt : ℝ) (qx : ℝ) -
            seq (subseq n) (qt : ℝ) (qx : ℝ)| +
          |seq (subseq n) (qt : ℝ) (qx : ℝ) - seq (subseq n) t x| := by
      calc
        |seq (subseq m) t x - seq (subseq n) t x| =
            |(seq (subseq m) t x - seq (subseq m) (qt : ℝ) (qx : ℝ)) +
             (seq (subseq m) (qt : ℝ) (qx : ℝ) -
               seq (subseq n) (qt : ℝ) (qx : ℝ)) +
             (seq (subseq n) (qt : ℝ) (qx : ℝ) -
               seq (subseq n) t x)| := by ring_nf
        _ ≤ _ := by
          calc
            |(seq (subseq m) t x - seq (subseq m) (qt : ℝ) (qx : ℝ)) +
                (seq (subseq m) (qt : ℝ) (qx : ℝ) -
                  seq (subseq n) (qt : ℝ) (qx : ℝ)) +
                (seq (subseq n) (qt : ℝ) (qx : ℝ) - seq (subseq n) t x)| ≤
              |(seq (subseq m) t x - seq (subseq m) (qt : ℝ) (qx : ℝ)) +
                (seq (subseq m) (qt : ℝ) (qx : ℝ) -
                  seq (subseq n) (qt : ℝ) (qx : ℝ))| +
                |seq (subseq n) (qt : ℝ) (qx : ℝ) - seq (subseq n) t x| :=
                  abs_add_le _ _
            _ ≤ _ := by
              gcongr
              exact abs_add_le _ _
    have hright' :
        |seq (subseq n) (qt : ℝ) (qx : ℝ) - seq (subseq n) t x| < ε / 3 := by
      rw [abs_sub_comm]
      exact hright
    linarith
  choose limit hlimit using fun t x =>
    cauchySeq_tendsto_of_complete (hcauchy t x)
  exact ⟨subseq, hsubseq, limit, hlimit⟩

/-- Pointwise convergence plus eventual local equicontinuity upgrades to
local-uniform convergence on compact space-time boxes. -/
private theorem spaceTimeLocallyUniform_of_pointwise_of_equicontinuous
    {seq : ℕ → ℝ → ℝ → ℝ} {limit : ℝ → ℝ → ℝ}
    (hpoint : ∀ t x, Tendsto (fun n => seq n t x) atTop (𝓝 (limit t x)))
    (hequicont : SpaceTimeLocallyEquicontinuous seq) :
    SpaceTimeLocallyUniformConverges seq limit := by
  intro R hR ε hε
  let S : ℝ := R + 1
  have hS : 0 < S := by dsimp only [S]; linarith
  obtain ⟨δ₀, hδ₀, heq⟩ := hequicont S hS (ε / 3) (by linarith)
  let η : ℝ := min (δ₀ / 2) 1
  have hη : 0 < η := lt_min (half_pos hδ₀) zero_lt_one
  have hηδ : η < δ₀ :=
    lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ₀)
  obtain ⟨Nnode, hNnode⟩ := exists_nat_gt (2 * R / η)
  let node : ℕ → ℝ := fun i => -R + (i : ℝ) * η
  have hcover : ∀ a ∈ Set.Icc (-R) R,
      ∃ i : ℕ, i ≤ Nnode ∧ |a - node i| ≤ η := by
    intro a ha
    obtain ⟨ha1, ha2⟩ := ha
    let q : ℝ := (a + R) / η
    have hq0 : 0 ≤ q := by
      dsimp only [q]
      exact div_nonneg (by linarith) hη.le
    let i : ℕ := ⌊q⌋₊
    refine ⟨i, ?_, ?_⟩
    · have hiq : (i : ℝ) ≤ q := Nat.floor_le hq0
      have hqR : q ≤ 2 * R / η := by
        dsimp only [q]
        have hnum : a + R ≤ 2 * R := by linarith
        gcongr
      have hiN : (i : ℝ) < (Nnode : ℝ) :=
        lt_of_le_of_lt (le_trans hiq hqR) hNnode
      exact le_of_lt (by exact_mod_cast hiN)
    · have hiq : (i : ℝ) ≤ q := Nat.floor_le hq0
      have hqi : q < (i : ℝ) + 1 := Nat.lt_floor_add_one q
      have hlo : (i : ℝ) * η ≤ a + R := by
        have := mul_le_mul_of_nonneg_right hiq hη.le
        rwa [show q * η = a + R by
          dsimp only [q]; exact div_mul_cancel₀ _ (ne_of_gt hη)] at this
      have hhi : a + R < ((i : ℝ) + 1) * η := by
        have := mul_lt_mul_of_pos_right hqi hη
        rwa [show q * η = a + R by
          dsimp only [q]; exact div_mul_cancel₀ _ (ne_of_gt hη)] at this
      dsimp only [node]
      rw [abs_le]
      constructor <;> linarith
  have hnodeS : ∀ a ∈ Set.Icc (-R) R, ∀ i, |a - node i| ≤ η →
      node i ∈ Set.Icc (-S) S := by
    intro a ha i hai
    apply abs_le.mp
    have hηone : η ≤ 1 := min_le_right _ _
    have habs : |node i| ≤ |a| + |a - node i| := by
      calc
        |node i| = |a + (node i - a)| := by ring_nf
        _ ≤ |a| + |node i - a| := abs_add_le _ _
        _ = |a| + |a - node i| := by rw [abs_sub_comm]
    have haabs : |a| ≤ R := abs_le.mpr ha
    dsimp only [S]
    linarith
  have hpointGrid : ∀ i j : ℕ, ∀ᶠ n in atTop,
      |seq n (node i) (node j) - limit (node i) (node j)| < ε / 3 := by
    intro i j
    obtain ⟨N, hN⟩ :=
      (Metric.tendsto_atTop.1 (hpoint (node i) (node j))) (ε / 3) (by linarith)
    exact eventually_atTop.2 ⟨N, fun n hn => by
      simpa only [Real.dist_eq] using hN n hn⟩
  have hfinite : ∀ᶠ n in atTop, ∀ i, i ≤ Nnode → ∀ j, j ≤ Nnode →
      |seq n (node i) (node j) - limit (node i) (node j)| < ε / 3 := by
    have hfin : ∀ᶠ n in atTop,
        ∀ i ∈ Finset.range (Nnode + 1), ∀ j ∈ Finset.range (Nnode + 1),
          |seq n (node i) (node j) - limit (node i) (node j)| < ε / 3 := by
      apply (eventually_all_finset (Finset.range (Nnode + 1))).mpr
      intro i _hi
      apply (eventually_all_finset (Finset.range (Nnode + 1))).mpr
      intro j _hj
      exact hpointGrid i j
    filter_upwards [hfin] with n hn i hi j hj
    exact hn i (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
      j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  have hlimitModulus :
      ∀ t ∈ Set.Icc (-S) S, ∀ s ∈ Set.Icc (-S) S,
      ∀ x ∈ Set.Icc (-S) S, ∀ y ∈ Set.Icc (-S) S,
        |t - s| < δ₀ → |x - y| < δ₀ →
          |limit t x - limit s y| ≤ ε / 3 := by
    intro t ht s hs x hx y hy hts hxy
    have htend : Tendsto (fun n => |seq n t x - seq n s y|) atTop
        (𝓝 |limit t x - limit s y|) := ((hpoint t x).sub (hpoint s y)).abs
    exact le_of_tendsto htend <| heq.mono fun n hn =>
      le_of_lt (hn t ht s hs x hx y hy hts hxy)
  filter_upwards [heq, hfinite] with n hnEq hnFin
  intro t ht x hx
  obtain ⟨i, hi, hti⟩ := hcover t ht
  obtain ⟨j, hj, hxj⟩ := hcover x hx
  have htS : t ∈ Set.Icc (-S) S := by
    constructor <;> dsimp only [S] <;> linarith [ht.1, ht.2]
  have hxS : x ∈ Set.Icc (-S) S := by
    constructor <;> dsimp only [S] <;> linarith [hx.1, hx.2]
  have hnodeiS := hnodeS t ht i hti
  have hnodejS := hnodeS x hx j hxj
  have htiδ : |t - node i| < δ₀ := lt_of_le_of_lt hti hηδ
  have hxjδ : |x - node j| < δ₀ := lt_of_le_of_lt hxj hηδ
  have hseqMod : |seq n t x - seq n (node i) (node j)| < ε / 3 :=
    hnEq t htS (node i) hnodeiS x hxS (node j) hnodejS htiδ hxjδ
  have hmid := hnFin i hi j hj
  have hlimMod : |limit (node i) (node j) - limit t x| ≤ ε / 3 := by
    apply hlimitModulus (node i) hnodeiS t htS (node j) hnodejS x hxS
    · rw [abs_sub_comm]; exact htiδ
    · rw [abs_sub_comm]; exact hxjδ
  have htri : |seq n t x - limit t x| ≤
      |seq n t x - seq n (node i) (node j)| +
      |seq n (node i) (node j) - limit (node i) (node j)| +
      |limit (node i) (node j) - limit t x| := by
    calc
      |seq n t x - limit t x| =
          |(seq n t x - seq n (node i) (node j)) +
           (seq n (node i) (node j) - limit (node i) (node j)) +
           (limit (node i) (node j) - limit t x)| := by ring_nf
      _ ≤ _ := by
        calc
          |(seq n t x - seq n (node i) (node j)) +
              (seq n (node i) (node j) - limit (node i) (node j)) +
              (limit (node i) (node j) - limit t x)| ≤
            |(seq n t x - seq n (node i) (node j)) +
              (seq n (node i) (node j) - limit (node i) (node j))| +
              |limit (node i) (node j) - limit t x| := abs_add_le _ _
          _ ≤ _ := by
            gcongr
            exact abs_add_le _ _
  linarith

/-- Two-dimensional Arzelà--Ascoli, in the exact eventual-on-boxes form used
by sequences of late-time/far-left translates. -/
theorem exists_spaceTimeLocallyUniform_subsequence
    (seq : ℕ → ℝ → ℝ → ℝ)
    (hbound : SpaceTimeLocallyEquibounded seq)
    (hequicont : SpaceTimeLocallyEquicontinuous seq) :
    ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
      ∃ limit : ℝ → ℝ → ℝ,
        SpaceTimeLocallyUniformConverges (fun n => seq (subseq n)) limit := by
  obtain ⟨subseq, hsubseq, limit, hpoint⟩ :=
    exists_spaceTime_pointwise_subsequence seq hbound hequicont
  refine ⟨subseq, hsubseq, limit, ?_⟩
  exact spaceTimeLocallyUniform_of_pointwise_of_equicontinuous hpoint
    (hequicont.comp_strictMono hsubseq)

section AxiomAudit

#print axioms exists_spaceTimeLocallyUniform_subsequence

end AxiomAudit

end ShenWork.Paper1
