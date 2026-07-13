import ShenWork.Paper1.SchauderPrincipleAssembled
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Sequences

namespace ShenWork.Paper1

open Set Filter Topology

noncomputable section

/-- Restrict a continuous profile to the compact interval `[-R, R]`, as a
continuous map with the uniform metric. -/
def profileRestrictIcc (R : ℝ) (u : ℝ → ℝ) (hu : Continuous u) :
    C(Set.Icc (-R) R, ℝ) where
  toFun x := u x.1
  continuous_toFun := hu.comp continuous_subtype_val

/-- Local-uniform convergence gives convergence in the uniform metric after
restricting to a fixed compact interval. -/
theorem tendsto_profileRestrictIcc_of_locallyUniform
    {seq : ℕ → ℝ → ℝ} {u : ℝ → ℝ} {R : ℝ}
    (hR : 0 < R) (hseqcont : ∀ n, Continuous (seq n)) (hucont : Continuous u)
    (hconv : LocallyUniformConverges seq u) :
    Tendsto (fun n => profileRestrictIcc R (seq n) (hseqcont n)) atTop
      (𝓝 (profileRestrictIcc R u hucont)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hconv R hR ε hε)
  refine ⟨N, ?_⟩
  intro n hnN
  haveI : Nonempty (Set.Icc (-R) R) := by
    refine ⟨⟨0, ?_⟩⟩
    constructor <;> linarith
  apply ContinuousMap.dist_lt_of_nonempty
  intro x
  have hx : (x : ℝ) ∈ Set.Icc (-R) R := x.2
  have h := hN n hnN (x : ℝ) hx
  simpa [profileRestrictIcc, Real.dist_eq, abs_sub_comm] using h

/-- A relative sequential compactness criterion for total boundedness.  The
limit of the convergent subsequence need not lie in the original set. -/
theorem totallyBounded_of_subseq_tendsto {α : Type*} [PseudoMetricSpace α]
    {s : Set α}
    (hseq : ∀ u : ℕ → α, (∀ n, u n ∈ s) →
      ∃ x : α, ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n => u (φ n)) atTop (𝓝 x)) :
    TotallyBounded s := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  by_contra hcover
  push Not at hcover
  have hfinite : ∀ t : Set α, t.Finite → ∃ c : α,
      c ∈ s ∧ ∀ y ∈ t, c ∉ Metric.ball y ε := by
    intro t ht
    have hnot : ¬ s ⊆ ⋃ y ∈ t, Metric.ball y ε := by
      intro hs
      exact hcover t ht hs
    rw [Set.not_subset] at hnot
    rcases hnot with ⟨c, hc_s, hc_not⟩
    refine ⟨c, hc_s, ?_⟩
    intro y hy hball
    exact hc_not (by exact Set.mem_iUnion₂.mpr ⟨y, hy, hball⟩)
  obtain ⟨u, hu⟩ := seq_of_forall_finite_exists
    (P := fun c t => c ∈ s ∧ ∀ y ∈ t, c ∉ Metric.ball y ε) hfinite
  have hu_s : ∀ n, u n ∈ s := fun n => (hu n).1
  rcases hseq u hu_s with ⟨_x, φ, hφ, htend⟩
  have hcauchy : CauchySeq (fun n => u (φ n)) := htend.cauchySeq
  rw [Metric.cauchySeq_iff] at hcauchy
  rcases hcauchy ε hε with ⟨N, hN⟩
  have hlt : φ N < φ (N + 1) := hφ (Nat.lt_succ_self N)
  have hprev : u (φ N) ∈ u '' Iio (φ (N + 1)) := by
    exact ⟨φ N, hlt, rfl⟩
  have hnotball := (hu (φ (N + 1))).2 (u (φ N)) hprev
  have hdist : dist (u (φ N)) (u (φ (N + 1))) < ε := by
    exact hN N le_rfl (N + 1) (Nat.le_succ N)
  exact hnotball (by simpa [Metric.mem_ball, dist_comm] using hdist)

/-- The interval-restricted image set of a wave-trap self-map.  Centers in this
set have actual full-profile representatives in the monotone wave trap. -/
def waveTrapImageRestrictSet (κ M R : ℝ) (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u)) :
    Set C(Set.Icc (-R) R, ℝ) :=
  {g | ∃ u, ∃ hu : InMonotoneWaveTrapSet κ M u,
    g = profileRestrictIcc R (Tmap u) ((hmap u hu).trap.cunif_bdd.1)}

/-- The compact-range hypothesis implies total boundedness of every
interval-restricted image set. -/
theorem waveTrapImageRestrictSet_totallyBounded {κ M R : ℝ}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hR : 0 < R)
    (hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u))
    (hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap) :
    TotallyBounded (waveTrapImageRestrictSet κ M R Tmap hmap) := by
  apply totallyBounded_of_subseq_tendsto
  intro gseq hgseq
  choose u hu hgeq using hgseq
  rcases hcompact u hu with ⟨φ, hφ, U, hU, hconv⟩
  refine ⟨profileRestrictIcc R U hU.trap.cunif_bdd.1, φ, hφ, ?_⟩
  have htend := tendsto_profileRestrictIcc_of_locallyUniform
    (R := R) hR
    (seq := fun n => Tmap (u (φ n))) (u := U)
    (fun n => (hmap (u (φ n)) (hu (φ n))).trap.cunif_bdd.1)
    hU.trap.cunif_bdd.1 hconv
  exact htend.congr' (Eventually.of_forall fun n => by
    simpa [profileRestrictIcc] using (hgeq (φ n)).symm)

/-- The same total boundedness gives compactness of the closure in the
continuous-function uniform metric. -/
theorem waveTrapImageRestrictSet_isCompact_closure {κ M R : ℝ}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hR : 0 < R)
    (hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u))
    (hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap) :
    IsCompact (closure (waveTrapImageRestrictSet κ M R Tmap hmap)) := by
  exact isCompact_iff_totallyBounded_isComplete.mpr
    ⟨(waveTrapImageRestrictSet_totallyBounded hR hmap hcompact).closure,
      isClosed_closure.isComplete⟩

/-- Finite ε-net for the compact closure, obtained specifically from
`exists_finite_eps_net`.  The eventual Schauder projection uses image-set
centers; this closure-net lemma records the compact finite-net input requested
by the partition-of-unity route. -/
theorem exists_finite_eps_net_waveTrapImageRestrict_closure {κ M R ε : ℝ}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hR : 0 < R) (hε : 0 < ε)
    (hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u))
    (hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap) :
    ∃ s ⊆ closure (waveTrapImageRestrictSet κ M R Tmap hmap),
      s.Finite ∧
        closure (waveTrapImageRestrictSet κ M R Tmap hmap) ⊆
          ⋃ x ∈ s, Metric.ball x ε :=
  exists_finite_eps_net
    (waveTrapImageRestrictSet_isCompact_closure hR hmap hcompact) hε

/-- Finite ε-net with centers in the actual restricted image set.  These centers
are the ones suitable for choosing full wave-trap profiles for a Schauder
partition-of-unity lift. -/
theorem exists_finite_eps_net_waveTrapImageRestrict {κ M R ε : ℝ}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hR : 0 < R) (hε : 0 < ε)
    (hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u))
    (hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap) :
    ∃ s ⊆ waveTrapImageRestrictSet κ M R Tmap hmap,
      s.Finite ∧ waveTrapImageRestrictSet κ M R Tmap hmap ⊆
        ⋃ x ∈ s, Metric.ball x ε :=
  Metric.finite_approx_of_totallyBounded
    (waveTrapImageRestrictSet_totallyBounded hR hmap hcompact) ε hε

/-- Compactly supported linear bump used for the Schauder partition of unity. -/
def schauderBump {α : Type*} [PseudoMetricSpace α] (ε : ℝ) (center x : α) : ℝ :=
  max (ε - dist x center) 0

theorem schauderBump_nonneg {α : Type*} [PseudoMetricSpace α]
    (ε : ℝ) (center x : α) :
    0 ≤ schauderBump ε center x := by
  unfold schauderBump
  exact le_max_right _ _

theorem schauderBump_pos_of_mem_ball {α : Type*} [PseudoMetricSpace α]
    {ε : ℝ} {center x : α} (hx : x ∈ Metric.ball center ε) :
    0 < schauderBump ε center x := by
  unfold schauderBump
  rw [Metric.mem_ball] at hx
  exact lt_max_of_lt_left (sub_pos.mpr (by simpa [dist_comm] using hx))

def schauderBumpSum {α ι : Type*} [PseudoMetricSpace α] [Fintype ι]
    (ε : ℝ) (center : ι → α) (x : α) : ℝ :=
  ∑ i : ι, schauderBump ε (center i) x

theorem schauderBumpSum_pos_of_mem_ball {α ι : Type*}
    [PseudoMetricSpace α] [Fintype ι] {ε : ℝ} {center : ι → α} {x : α}
    {i₀ : ι} (hx : x ∈ Metric.ball (center i₀) ε) :
    0 < schauderBumpSum ε center x := by
  unfold schauderBumpSum
  exact Finset.sum_pos'
    (fun i _ => schauderBump_nonneg ε (center i) x)
    ⟨i₀, Finset.mem_univ i₀, schauderBump_pos_of_mem_ball hx⟩

def schauderBumpWeight {α ι : Type*} [PseudoMetricSpace α] [Fintype ι]
    (ε : ℝ) (center : ι → α) (x : α) (i : ι) : ℝ :=
  if _ : 0 < schauderBumpSum ε center x then
    schauderBump ε (center i) x / schauderBumpSum ε center x
  else
    0

theorem schauderBumpWeight_nonneg {α ι : Type*}
    [PseudoMetricSpace α] [Fintype ι]
    (ε : ℝ) (center : ι → α) (x : α) (i : ι) :
    0 ≤ schauderBumpWeight ε center x i := by
  by_cases hsum : 0 < schauderBumpSum ε center x
  · simp [schauderBumpWeight, hsum,
      div_nonneg (schauderBump_nonneg ε (center i) x) hsum.le]
  · simp [schauderBumpWeight, hsum]

theorem schauderBumpWeight_le_one {α ι : Type*}
    [PseudoMetricSpace α] [Fintype ι]
    (ε : ℝ) (center : ι → α) (x : α) (i : ι) :
    schauderBumpWeight ε center x i ≤ 1 := by
  by_cases hsum : 0 < schauderBumpSum ε center x
  · simp only [schauderBumpWeight, hsum, dite_true]
    rw [div_le_one hsum]
    unfold schauderBumpSum
    exact Finset.single_le_sum
      (fun j _ => schauderBump_nonneg ε (center j) x)
      (Finset.mem_univ i)
  · simp [schauderBumpWeight, hsum]

theorem sum_schauderBumpWeight_of_sum_pos {α ι : Type*}
    [PseudoMetricSpace α] [Fintype ι]
    {ε : ℝ} {center : ι → α} {x : α}
    (hsum : 0 < schauderBumpSum ε center x) :
    ∑ i : ι, schauderBumpWeight ε center x i = 1 := by
  simp only [schauderBumpWeight, dif_pos hsum]
  rw [← Finset.sum_div]
  unfold schauderBumpSum
  have hsum' : (∑ i, schauderBump ε (center i) x) ≠ 0 := by
    exact (by simpa [schauderBumpSum] using hsum : 0 <
      (∑ i, schauderBump ε (center i) x)).ne'
  rw [div_self hsum']

theorem schauderBumpWeightFin_mem_unitCube {α : Type*} [PseudoMetricSpace α]
    {n : ℕ} (ε : ℝ) (center : Fin n → α) (x : α) :
    (fun i : Fin n => schauderBumpWeight ε center x i) ∈
      Freudenthal.unitCube n := by
  intro i
  exact ⟨schauderBumpWeight_nonneg ε center x i,
    schauderBumpWeight_le_one ε center x i⟩

theorem tendsto_schauderBump {α β : Type*} [PseudoMetricSpace α]
    {l : Filter β} {xseq : β → α} {x : α}
    (hseq : Tendsto xseq l (𝓝 x)) (ε : ℝ) (center : α) :
    Tendsto (fun n => schauderBump ε center (xseq n)) l
      (𝓝 (schauderBump ε center x)) := by
  unfold schauderBump
  have hdist :
      Tendsto (fun n => dist (xseq n) center) l (𝓝 (dist x center)) :=
    ((continuous_id.dist continuous_const).tendsto x).comp hseq
  exact (tendsto_const_nhds.sub hdist).max tendsto_const_nhds

theorem tendsto_schauderBumpSum {α β ι : Type*}
    [PseudoMetricSpace α] [Fintype ι]
    {l : Filter β} {xseq : β → α} {x : α}
    (hseq : Tendsto xseq l (𝓝 x)) (ε : ℝ) (center : ι → α) :
    Tendsto (fun n => schauderBumpSum ε center (xseq n)) l
      (𝓝 (schauderBumpSum ε center x)) := by
  unfold schauderBumpSum
  exact tendsto_finset_sum Finset.univ
    (fun i _ => tendsto_schauderBump hseq ε (center i))

theorem tendsto_schauderBumpWeight_of_sum_pos {α β ι : Type*}
    [PseudoMetricSpace α] [Fintype ι]
    {l : Filter β} {xseq : β → α} {x : α}
    (hseq : Tendsto xseq l (𝓝 x)) {ε : ℝ} {center : ι → α}
    (hsum : 0 < schauderBumpSum ε center x) (i : ι) :
    Tendsto (fun n => schauderBumpWeight ε center (xseq n) i) l
      (𝓝 (schauderBumpWeight ε center x i)) := by
  have hbump := tendsto_schauderBump hseq ε (center i)
  have hsum_tend := tendsto_schauderBumpSum hseq ε center
  have hsum_ne : schauderBumpSum ε center x ≠ 0 := hsum.ne'
  have hformula_lim :
      schauderBumpWeight ε center x i =
        schauderBump ε (center i) x / schauderBumpSum ε center x := by
    simp [schauderBumpWeight, hsum]
  have hdiv :
      Tendsto
        (fun n => schauderBump ε (center i) (xseq n) /
          schauderBumpSum ε center (xseq n)) l
        (𝓝 (schauderBump ε (center i) x /
          schauderBumpSum ε center x)) :=
    hbump.div hsum_tend hsum_ne
  have hev : ∀ᶠ n in l, 0 < schauderBumpSum ε center (xseq n) :=
    hsum_tend.eventually (Ioi_mem_nhds hsum)
  have hcongr :
      (fun n => schauderBump ε (center i) (xseq n) /
          schauderBumpSum ε center (xseq n)) =ᶠ[l]
        (fun n => schauderBumpWeight ε center (xseq n) i) := by
    filter_upwards [hev] with n hn
    simp [schauderBumpWeight, hn]
  exact Tendsto.congr' hcongr (by simpa [hformula_lim] using hdiv)

theorem dist_lt_of_schauderBumpWeight_pos {α ι : Type*}
    [PseudoMetricSpace α] [Fintype ι]
    {ε : ℝ} {center : ι → α} {x : α} {i : ι}
    (hsum : 0 < schauderBumpSum ε center x)
    (hw : 0 < schauderBumpWeight ε center x i) :
    dist x (center i) < ε := by
  have hbump_pos :
      0 < schauderBump ε (center i) x := by
    have hw' :
        0 < schauderBump ε (center i) x /
          schauderBumpSum ε center x := by
      simpa [schauderBumpWeight, hsum] using hw
    exact (div_pos_iff_of_pos_right hsum).mp hw'
  unfold schauderBump at hbump_pos
  by_contra hnot
  have hle : ε - dist x (center i) ≤ 0 := sub_nonpos.mpr (le_of_not_gt hnot)
  have hmax : max (ε - dist x (center i)) 0 = 0 := max_eq_right hle
  linarith

lemma abs_sub_weighted_sum_le
    {ι : Type*} [Fintype ι] {w : ι → ℝ} {y : ℝ}
    {z : ι → ℝ} {η : ℝ}
    (hw_nonneg : ∀ i, 0 ≤ w i)
    (hw_sum : ∑ i : ι, w i = 1)
    (hterm : ∀ i, w i * |y - z i| ≤ w i * η) :
    |y - ∑ i : ι, w i * z i| ≤ η := by
  have hrewrite :
      y - ∑ i : ι, w i * z i =
        ∑ i : ι, w i * (y - z i) := by
    calc
      y - ∑ i : ι, w i * z i
          = (∑ i : ι, w i) * y - ∑ i : ι, w i * z i := by
              rw [hw_sum]
              ring
      _ = (∑ i : ι, w i * y) - ∑ i : ι, w i * z i := by
              rw [Finset.sum_mul]
      _ = ∑ i : ι, (w i * y - w i * z i) := by
              rw [Finset.sum_sub_distrib]
      _ = ∑ i : ι, w i * (y - z i) := by
              apply Finset.sum_congr rfl
              intro i _hi
              ring
  rw [hrewrite]
  calc
    |∑ i : ι, w i * (y - z i)|
        ≤ ∑ i : ι, |w i * (y - z i)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : ι, w i * |y - z i| := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [abs_mul, abs_of_nonneg (hw_nonneg i)]
    _ ≤ ∑ i : ι, w i * η := by
          exact Finset.sum_le_sum (fun i _ => hterm i)
    _ = (∑ i : ι, w i) * η := by
          rw [Finset.sum_mul]
    _ = η := by rw [hw_sum, one_mul]

/-- Finite convex combinations of monotone wave-trap profiles remain in the
monotone wave trap. -/
theorem inMonotoneWaveTrapSet_finset_sum_mem
    {κ M : ℝ} {ι : Type*} [Fintype ι]
    {w : ι → ℝ} {center : ι → ℝ → ℝ}
    (hw_nonneg : ∀ i, 0 ≤ w i)
    (hw_sum : ∑ i : ι, w i = 1)
    (hcenter : ∀ i, InMonotoneWaveTrapSet κ M (center i)) :
    InMonotoneWaveTrapSet κ M (∑ i : ι, w i • center i) := by
  exact (InMonotoneWaveTrapSet.set_convex κ M).sum_mem
    (t := Finset.univ)
    (fun i _ => hw_nonneg i)
    (by simpa using hw_sum)
    (fun i _ => hcenter i)

/-- The bump-normalized partition-of-unity lift of finitely many wave-trap
profiles remains in the monotone wave trap whenever the bump denominator is
positive. -/
theorem inMonotoneWaveTrapSet_bumpPartition_mem
    {κ M : ℝ} {α ι : Type*} [PseudoMetricSpace α] [Fintype ι]
    {ε : ℝ} {anchor : ι → α} {x : α} {center : ι → ℝ → ℝ}
    (hsum : 0 < schauderBumpSum ε anchor x)
    (hcenter : ∀ i, InMonotoneWaveTrapSet κ M (center i)) :
    InMonotoneWaveTrapSet κ M
      (∑ i : ι, schauderBumpWeight ε anchor x i • center i) := by
  exact inMonotoneWaveTrapSet_finset_sum_mem
    (κ := κ) (M := M)
    (fun i => schauderBumpWeight_nonneg ε anchor x i)
    (sum_schauderBumpWeight_of_sum_pos hsum)
    hcenter

def projectedCubeRadius (N : ℕ) : ℝ :=
  (N + 1 : ℝ)

def projectedCubeNetRadius (N : ℕ) : ℝ :=
  ((N + 1 : ℝ))⁻¹

lemma projectedCubeRadius_pos (N : ℕ) : 0 < projectedCubeRadius N := by
  unfold projectedCubeRadius
  positivity

lemma projectedCubeNetRadius_pos (N : ℕ) :
    0 < projectedCubeNetRadius N := by
  unfold projectedCubeNetRadius
  positivity

lemma projectedCubeNetRadius_nonneg (N : ℕ) :
    0 ≤ projectedCubeNetRadius N :=
  (projectedCubeNetRadius_pos N).le

lemma projectedCubeNetRadius_tendsto :
    Tendsto projectedCubeNetRadius atTop (𝓝 0) := by
  simpa [projectedCubeNetRadius, one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

def profileRestrictIccIf (R : ℝ) (u : ℝ → ℝ) :
    C(Set.Icc (-R) R, ℝ) := by
  classical
  exact if hu : Continuous u then profileRestrictIcc R u hu else 0

lemma profileRestrictIccIf_eq (R : ℝ) {u : ℝ → ℝ} (hu : Continuous u) :
    profileRestrictIccIf R u = profileRestrictIcc R u hu := by
  classical
  simp [profileRestrictIccIf, hu]

lemma waveTrapImageRestrictSet_fullRep
    {κ M R : ℝ} {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u)}
    {g : C(Set.Icc (-R) R, ℝ)}
    (hg : g ∈ waveTrapImageRestrictSet κ M R Tmap hmap) :
    ∃ v, ∃ hv : InMonotoneWaveTrapSet κ M v,
      g = profileRestrictIcc R v
        (hv.trap.cunif_bdd.1) := by
  rcases hg with ⟨u, hu, rfl⟩
  exact ⟨Tmap u, hmap u hu, rfl⟩

noncomputable def waveTrapImageFullProfile
    {κ M R : ℝ} {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u)}
    (g : C(Set.Icc (-R) R, ℝ))
    (hg : g ∈ waveTrapImageRestrictSet κ M R Tmap hmap) :
    ℝ → ℝ :=
  Classical.choose (waveTrapImageRestrictSet_fullRep (hmap := hmap) hg)

lemma waveTrapImageFullProfile_trap
    {κ M R : ℝ} {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u)}
    (g : C(Set.Icc (-R) R, ℝ))
    (hg : g ∈ waveTrapImageRestrictSet κ M R Tmap hmap) :
    InMonotoneWaveTrapSet κ M
      (waveTrapImageFullProfile (hmap := hmap) g hg) :=
  Classical.choose (Classical.choose_spec
    (waveTrapImageRestrictSet_fullRep (hmap := hmap) hg))

lemma waveTrapImageFullProfile_restrict
    {κ M R : ℝ} {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u)}
    (g : C(Set.Icc (-R) R, ℝ))
    (hg : g ∈ waveTrapImageRestrictSet κ M R Tmap hmap) :
    g = profileRestrictIcc R
      (waveTrapImageFullProfile (hmap := hmap) g hg)
      ((waveTrapImageFullProfile_trap (hmap := hmap) g hg).trap.cunif_bdd.1) :=
  Classical.choose_spec (Classical.choose_spec
    (waveTrapImageRestrictSet_fullRep (hmap := hmap) hg))

noncomputable def projectedCubeRawNet
    (κ M : ℝ) (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u))
    (hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap)
    (N : ℕ) :
    Set C(Set.Icc (-(projectedCubeRadius N)) (projectedCubeRadius N), ℝ) :=
  Classical.choose
    (exists_finite_eps_net_waveTrapImageRestrict
      (κ := κ) (M := M) (R := projectedCubeRadius N)
      (ε := projectedCubeNetRadius N) (Tmap := Tmap)
      (projectedCubeRadius_pos N) (projectedCubeNetRadius_pos N)
      hmap hcompact)

lemma projectedCubeRawNet_subset
    {κ M : ℝ} {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u)}
    {hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap}
    (N : ℕ) :
    projectedCubeRawNet κ M Tmap hmap hcompact N ⊆
      waveTrapImageRestrictSet κ M (projectedCubeRadius N) Tmap hmap :=
  (Classical.choose_spec
    (exists_finite_eps_net_waveTrapImageRestrict
      (κ := κ) (M := M) (R := projectedCubeRadius N)
      (ε := projectedCubeNetRadius N) (Tmap := Tmap)
      (projectedCubeRadius_pos N) (projectedCubeNetRadius_pos N)
      hmap hcompact)).1

lemma projectedCubeRawNet_finite
    {κ M : ℝ} {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u)}
    {hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap}
    (N : ℕ) :
    (projectedCubeRawNet κ M Tmap hmap hcompact N).Finite :=
  (Classical.choose_spec
    (exists_finite_eps_net_waveTrapImageRestrict
      (κ := κ) (M := M) (R := projectedCubeRadius N)
      (ε := projectedCubeNetRadius N) (Tmap := Tmap)
      (projectedCubeRadius_pos N) (projectedCubeNetRadius_pos N)
      hmap hcompact)).2.1

lemma projectedCubeRawNet_covers
    {κ M : ℝ} {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u)}
    {hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap}
    (N : ℕ) :
    waveTrapImageRestrictSet κ M (projectedCubeRadius N) Tmap hmap ⊆
      ⋃ x ∈ projectedCubeRawNet κ M Tmap hmap hcompact N,
        Metric.ball x (projectedCubeNetRadius N) :=
  (Classical.choose_spec
    (exists_finite_eps_net_waveTrapImageRestrict
      (κ := κ) (M := M) (R := projectedCubeRadius N)
      (ε := projectedCubeNetRadius N) (Tmap := Tmap)
      (projectedCubeRadius_pos N) (projectedCubeNetRadius_pos N)
      hmap hcompact)).2.2

noncomputable def projectedCubeBaseCenter
    (κ M : ℝ) (hM : 0 ≤ M)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u))
    (N : ℕ) :
    C(Set.Icc (-(projectedCubeRadius N)) (projectedCubeRadius N), ℝ) :=
  profileRestrictIcc (projectedCubeRadius N)
    (Tmap (fun _ : ℝ => 0))
    ((hmap (fun _ : ℝ => 0) (InMonotoneWaveTrapSet.zero hM)).trap.cunif_bdd.1)

lemma projectedCubeBaseCenter_mem
    {κ M : ℝ} {hM : 0 ≤ M}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u)}
    (N : ℕ) :
    projectedCubeBaseCenter κ M hM Tmap hmap N ∈
      waveTrapImageRestrictSet κ M (projectedCubeRadius N) Tmap hmap := by
  exact ⟨fun _ : ℝ => 0, InMonotoneWaveTrapSet.zero hM, rfl⟩

noncomputable def projectedCubeNetSet
    (κ M : ℝ) (hM : 0 ≤ M)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u))
    (hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap)
    (N : ℕ) :
    Set C(Set.Icc (-(projectedCubeRadius N)) (projectedCubeRadius N), ℝ) :=
  projectedCubeRawNet κ M Tmap hmap hcompact N ∪
    {projectedCubeBaseCenter κ M hM Tmap hmap N}

lemma projectedCubeNetSet_subset
    {κ M : ℝ} {hM : 0 ≤ M}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u)}
    {hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap}
    (N : ℕ) :
    projectedCubeNetSet κ M hM Tmap hmap hcompact N ⊆
      waveTrapImageRestrictSet κ M (projectedCubeRadius N) Tmap hmap := by
  intro g hg
  rcases hg with hg | hg
  · exact projectedCubeRawNet_subset N hg
  · have hgeq :
        g = projectedCubeBaseCenter κ M hM Tmap hmap N := by
      simpa using hg
    simpa [hgeq] using projectedCubeBaseCenter_mem (hM := hM)
      (hmap := hmap) N

lemma projectedCubeNetSet_finite
    {κ M : ℝ} {hM : 0 ≤ M}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u)}
    {hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap}
    (N : ℕ) :
    (projectedCubeNetSet κ M hM Tmap hmap hcompact N).Finite := by
  exact (projectedCubeRawNet_finite (hmap := hmap) (hcompact := hcompact) N).union
    (Set.finite_singleton _)

lemma projectedCubeNetSet_nonempty
    {κ M : ℝ} {hM : 0 ≤ M}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u)}
    {hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap}
    (N : ℕ) :
    (projectedCubeNetSet κ M hM Tmap hmap hcompact N).Nonempty :=
  ⟨projectedCubeBaseCenter κ M hM Tmap hmap N, Or.inr rfl⟩

lemma projectedCubeNetSet_covers
    {κ M : ℝ} {hM : 0 ≤ M}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u)}
    {hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap}
    (N : ℕ) :
    waveTrapImageRestrictSet κ M (projectedCubeRadius N) Tmap hmap ⊆
      ⋃ x ∈ projectedCubeNetSet κ M hM Tmap hmap hcompact N,
        Metric.ball x (projectedCubeNetRadius N) := by
  intro g hg
  rcases Set.mem_iUnion₂.mp
      (projectedCubeRawNet_covers (hmap := hmap)
        (hcompact := hcompact) N hg) with ⟨x, hxraw, hxball⟩
  exact Set.mem_iUnion₂.mpr ⟨x, Or.inl hxraw, hxball⟩

noncomputable def projectedCubeNetIndex
    (κ M : ℝ) (hM : 0 ≤ M)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u))
    (hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap)
    (N : ℕ) : Type :=
  {g : C(Set.Icc (-(projectedCubeRadius N)) (projectedCubeRadius N), ℝ) //
    g ∈ projectedCubeNetSet κ M hM Tmap hmap hcompact N}

instance projectedCubeNetIndex_fintype
    (κ M : ℝ) (hM : 0 ≤ M)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u))
    (hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap)
    (N : ℕ) :
    Fintype (projectedCubeNetIndex κ M hM Tmap hmap hcompact N) :=
  Set.Finite.fintype (projectedCubeNetSet_finite
    (hM := hM) (hmap := hmap) (hcompact := hcompact) N)

instance projectedCubeNetIndex_nonempty
    (κ M : ℝ) (hM : 0 ≤ M)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u))
    (hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap)
    (N : ℕ) :
    Nonempty (projectedCubeNetIndex κ M hM Tmap hmap hcompact N) :=
  let hne := projectedCubeNetSet_nonempty
    (hM := hM) (hmap := hmap) (hcompact := hcompact) N
  ⟨⟨Classical.choose hne, Classical.choose_spec hne⟩⟩

noncomputable def projectedCubeDim
    (κ M : ℝ) (hM : 0 ≤ M)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u))
    (hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap)
    (N : ℕ) : ℕ :=
  Fintype.card (projectedCubeNetIndex κ M hM Tmap hmap hcompact N)

noncomputable def projectedCubeIndexEquiv
    (κ M : ℝ) (hM : 0 ≤ M)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u))
    (hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap)
    (N : ℕ) :
    projectedCubeNetIndex κ M hM Tmap hmap hcompact N ≃
      Fin (projectedCubeDim κ M hM Tmap hmap hcompact N) :=
  Fintype.equivFin (projectedCubeNetIndex κ M hM Tmap hmap hcompact N)

noncomputable def projectedCubeAnchor
    (κ M : ℝ) (hM : 0 ≤ M)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u))
    (hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap)
    (N : ℕ) :
    Fin (projectedCubeDim κ M hM Tmap hmap hcompact N) →
      C(Set.Icc (-(projectedCubeRadius N)) (projectedCubeRadius N), ℝ) :=
  fun i => ((projectedCubeIndexEquiv κ M hM Tmap hmap hcompact N).symm i).1

lemma projectedCubeAnchor_mem
    {κ M : ℝ} {hM : 0 ≤ M}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u)}
    {hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap}
    (N : ℕ)
    (i : Fin (projectedCubeDim κ M hM Tmap hmap hcompact N)) :
    projectedCubeAnchor κ M hM Tmap hmap hcompact N i ∈
      waveTrapImageRestrictSet κ M (projectedCubeRadius N) Tmap hmap :=
  projectedCubeNetSet_subset (hM := hM) (hmap := hmap)
    (hcompact := hcompact) N
    (((projectedCubeIndexEquiv κ M hM Tmap hmap hcompact N).symm i).2)

noncomputable def projectedCubeCenterProfile
    (κ M : ℝ) (hM : 0 ≤ M)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u))
    (hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap)
    (N : ℕ)
    (i : Fin (projectedCubeDim κ M hM Tmap hmap hcompact N)) :
    ℝ → ℝ :=
  waveTrapImageFullProfile
    (hmap := hmap)
    (projectedCubeAnchor κ M hM Tmap hmap hcompact N i)
    (projectedCubeAnchor_mem (hM := hM) (hmap := hmap)
      (hcompact := hcompact) N i)

lemma projectedCubeCenterProfile_trap
    {κ M : ℝ} {hM : 0 ≤ M}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u)}
    {hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap}
    (N : ℕ)
    (i : Fin (projectedCubeDim κ M hM Tmap hmap hcompact N)) :
    InMonotoneWaveTrapSet κ M
      (projectedCubeCenterProfile κ M hM Tmap hmap hcompact N i) :=
  waveTrapImageFullProfile_trap (hmap := hmap)
    (projectedCubeAnchor κ M hM Tmap hmap hcompact N i)
    (projectedCubeAnchor_mem (hM := hM) (hmap := hmap)
      (hcompact := hcompact) N i)

lemma projectedCubeCenterProfile_restrict
    {κ M : ℝ} {hM : 0 ≤ M}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u)}
    {hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap}
    (N : ℕ)
    (i : Fin (projectedCubeDim κ M hM Tmap hmap hcompact N)) :
    projectedCubeAnchor κ M hM Tmap hmap hcompact N i =
      profileRestrictIcc (projectedCubeRadius N)
        (projectedCubeCenterProfile κ M hM Tmap hmap hcompact N i)
        ((projectedCubeCenterProfile_trap (hM := hM) (hmap := hmap)
          (hcompact := hcompact) N i).trap.cunif_bdd.1) :=
  waveTrapImageFullProfile_restrict (hmap := hmap)
    (projectedCubeAnchor κ M hM Tmap hmap hcompact N i)
    (projectedCubeAnchor_mem (hM := hM) (hmap := hmap)
      (hcompact := hcompact) N i)

lemma projectedCubeProfileRestrictIf_mem_image_of_map
    {κ M : ℝ}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u)}
    (N : ℕ) {u : ℝ → ℝ} (hu : InMonotoneWaveTrapSet κ M u) :
    profileRestrictIccIf (projectedCubeRadius N) (Tmap u) ∈
      waveTrapImageRestrictSet κ M (projectedCubeRadius N) Tmap hmap := by
  rw [profileRestrictIccIf_eq _ ((hmap u hu).trap.cunif_bdd.1)]
  exact ⟨u, hu, rfl⟩

lemma projectedCubeBumpSum_pos_of_mem_image
    {κ M : ℝ} {hM : 0 ≤ M}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u)}
    {hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap}
    (N : ℕ)
    {g : C(Set.Icc (-(projectedCubeRadius N)) (projectedCubeRadius N), ℝ)}
    (hg : g ∈ waveTrapImageRestrictSet κ M (projectedCubeRadius N) Tmap hmap) :
    0 < schauderBumpSum (projectedCubeNetRadius N)
      (projectedCubeAnchor κ M hM Tmap hmap hcompact N) g := by
  rcases Set.mem_iUnion₂.mp
      (projectedCubeNetSet_covers (hM := hM) (hmap := hmap)
        (hcompact := hcompact) N hg) with ⟨y, hyNet, hyBall⟩
  let j : projectedCubeNetIndex κ M hM Tmap hmap hcompact N :=
    ⟨y, hyNet⟩
  let i : Fin (projectedCubeDim κ M hM Tmap hmap hcompact N) :=
    projectedCubeIndexEquiv κ M hM Tmap hmap hcompact N j
  have hanchor :
      projectedCubeAnchor κ M hM Tmap hmap hcompact N i = y := by
    simp [projectedCubeAnchor, projectedCubeIndexEquiv, i, j]
  have hball :
      g ∈ Metric.ball
        (projectedCubeAnchor κ M hM Tmap hmap hcompact N i)
        (projectedCubeNetRadius N) := by
    simpa [hanchor] using hyBall
  exact schauderBumpSum_pos_of_mem_ball hball

lemma projectedCubeDim_pos
    {κ M : ℝ} {hM : 0 ≤ M}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u)}
    {hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap}
    (N : ℕ) :
    0 < projectedCubeDim κ M hM Tmap hmap hcompact N := by
  unfold projectedCubeDim
  exact Fintype.card_pos

lemma projectedCubeDim_cast_pos
    {κ M : ℝ} {hM : 0 ≤ M}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u)}
    {hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap}
    (N : ℕ) :
    0 < (projectedCubeDim κ M hM Tmap hmap hcompact N : ℝ) := by
  exact_mod_cast projectedCubeDim_pos (hM := hM) (hmap := hmap)
    (hcompact := hcompact) N

noncomputable def projectedCubeCoordTol
    (κ M : ℝ) (hM : 0 ≤ M)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u))
    (hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap)
    (N : ℕ) : ℝ :=
  projectedCubeNetRadius N /
    ((16 : ℝ) *
      (projectedCubeDim κ M hM Tmap hmap hcompact N + 1 : ℝ) ^ 2 *
        (M + 1))

lemma projectedCubeCoordTol_pos
    {κ M : ℝ} {hM : 0 ≤ M}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u)}
    {hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap}
    (N : ℕ) :
    0 < projectedCubeCoordTol κ M hM Tmap hmap hcompact N := by
  unfold projectedCubeCoordTol
  have hden :
      0 < (16 : ℝ) *
        (projectedCubeDim κ M hM Tmap hmap hcompact N + 1 : ℝ) ^ 2 *
          (M + 1) := by
    have hdim :
        0 < (projectedCubeDim κ M hM Tmap hmap hcompact N + 1 : ℝ) := by
      positivity
    have hM1 : 0 < M + 1 := by linarith
    positivity
  exact div_pos (projectedCubeNetRadius_pos N) hden

lemma projectedCubeCoordTol_nonneg
    {κ M : ℝ} {hM : 0 ≤ M}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u)}
    {hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap}
    (N : ℕ) :
    0 ≤ projectedCubeCoordTol κ M hM Tmap hmap hcompact N :=
  (projectedCubeCoordTol_pos (hM := hM) (hmap := hmap)
    (hcompact := hcompact) N).le

def smoothCubeWeightDenom {n : ℕ} (c : ℝ) (a : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, (a i + c)

def smoothCubeWeight {n : ℕ} (c : ℝ) (a : Fin n → ℝ) (i : Fin n) :
    ℝ :=
  (a i + c) / smoothCubeWeightDenom c a

lemma smoothCubeWeightDenom_pos {n : ℕ} {c : ℝ}
    {a : Fin n → ℝ} (hc : 0 < c) (ha : a ∈ Freudenthal.unitCube n)
    (hn : 0 < n) :
    0 < smoothCubeWeightDenom c a := by
  unfold smoothCubeWeightDenom
  exact Finset.sum_pos'
    (fun i _ => (add_pos_of_nonneg_of_pos (ha i).1 hc).le)
    ⟨⟨0, hn⟩, Finset.mem_univ _, add_pos_of_nonneg_of_pos (ha ⟨0, hn⟩).1 hc⟩

lemma smoothCubeWeight_nonneg {n : ℕ} {c : ℝ}
    {a : Fin n → ℝ} (hc : 0 < c) (ha : a ∈ Freudenthal.unitCube n)
    (i : Fin n) :
    0 ≤ smoothCubeWeight c a i := by
  unfold smoothCubeWeight
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.2
  exact div_nonneg (add_nonneg (ha i).1 hc.le)
    (smoothCubeWeightDenom_pos hc ha hn).le

lemma smoothCubeWeight_le_one {n : ℕ} {c : ℝ}
    {a : Fin n → ℝ} (hc : 0 < c) (ha : a ∈ Freudenthal.unitCube n)
    (i : Fin n) :
    smoothCubeWeight c a i ≤ 1 := by
  unfold smoothCubeWeight
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.2
  rw [div_le_one (smoothCubeWeightDenom_pos hc ha hn)]
  unfold smoothCubeWeightDenom
  exact Finset.single_le_sum
    (fun j _ => add_nonneg (ha j).1 hc.le)
    (Finset.mem_univ i)

lemma smoothCubeWeight_sum_eq_one {n : ℕ} {c : ℝ}
    {a : Fin n → ℝ} (hc : 0 < c) (ha : a ∈ Freudenthal.unitCube n)
    (hn : 0 < n) :
    ∑ i : Fin n, smoothCubeWeight c a i = 1 := by
  unfold smoothCubeWeight
  rw [← Finset.sum_div]
  have hden_ne : smoothCubeWeightDenom c a ≠ 0 :=
    (smoothCubeWeightDenom_pos hc ha hn).ne'
  exact div_self hden_ne

lemma smoothCubeWeight_mem_unitCube {n : ℕ} {c : ℝ}
    {a : Fin n → ℝ} (hc : 0 < c) (ha : a ∈ Freudenthal.unitCube n) :
    (fun i : Fin n => smoothCubeWeight c a i) ∈
      Freudenthal.unitCube n := by
  intro i
  exact ⟨smoothCubeWeight_nonneg hc ha i,
    smoothCubeWeight_le_one hc ha i⟩

lemma tendsto_smoothCubeWeightDenom {β : Type*} {n : ℕ}
    {l : Filter β} {seq : β → Fin n → ℝ} {a : Fin n → ℝ}
    (hseq : Tendsto seq l (𝓝 a)) (c : ℝ) :
    Tendsto (fun m => smoothCubeWeightDenom c (seq m)) l
      (𝓝 (smoothCubeWeightDenom c a)) := by
  unfold smoothCubeWeightDenom
  exact tendsto_finset_sum Finset.univ
    (fun i _ => ((tendsto_pi_nhds.mp hseq i).add tendsto_const_nhds))

lemma tendsto_smoothCubeWeight {β : Type*} {n : ℕ} {c : ℝ}
    {l : Filter β} {seq : β → Fin n → ℝ} {a : Fin n → ℝ}
    (hseq : Tendsto seq l (𝓝 a)) (hc : 0 < c)
    (ha : a ∈ Freudenthal.unitCube n) (hn : 0 < n) (i : Fin n) :
    Tendsto (fun m => smoothCubeWeight c (seq m) i) l
      (𝓝 (smoothCubeWeight c a i)) := by
  unfold smoothCubeWeight
  have hnum :
      Tendsto (fun m => seq m i + c) l (𝓝 (a i + c)) :=
    (tendsto_pi_nhds.mp hseq i).add tendsto_const_nhds
  have hden := tendsto_smoothCubeWeightDenom hseq c
  exact hnum.div hden (smoothCubeWeightDenom_pos hc ha hn).ne'

lemma tendsto_smoothCubeWeight_abs_sum {β : Type*} {n : ℕ} {c : ℝ}
    {l : Filter β} {seq : β → Fin n → ℝ} {a : Fin n → ℝ}
    (hseq : Tendsto seq l (𝓝 a)) (hc : 0 < c)
    (ha : a ∈ Freudenthal.unitCube n) (hn : 0 < n) :
    Tendsto
      (fun m => ∑ i : Fin n, |smoothCubeWeight c (seq m) i -
        smoothCubeWeight c a i|) l (𝓝 0) := by
  have hsum :
      Tendsto
        (fun m => ∑ i : Fin n, |smoothCubeWeight c (seq m) i -
          smoothCubeWeight c a i|) l
        (𝓝 (∑ i : Fin n, |smoothCubeWeight c a i -
          smoothCubeWeight c a i|)) := by
    exact tendsto_finset_sum Finset.univ
      (fun i _ =>
        (((tendsto_smoothCubeWeight hseq hc ha hn i).sub
          tendsto_const_nhds).abs))
  simpa using hsum

lemma projectedCube_coord_abs_sub_le_of_norm {n : ℕ}
    {a b : Fin n → ℝ} {δ : ℝ} (h : ‖a - b‖ ≤ δ) (i : Fin n) :
    |a i - b i| ≤ δ := by
  have hcoord := norm_le_pi_norm (a - b) i
  exact le_trans (by simpa [Pi.sub_apply, Real.norm_eq_abs] using hcoord) h

lemma smoothCubeWeight_close_to_simplex_weights
    {n : ℕ} {c : ℝ} {a p : Fin n → ℝ}
    (hc : 0 ≤ c)
    (hp : p ∈ Freudenthal.unitCube n)
    (hp_sum : ∑ i : Fin n, p i = 1)
    (hcoord : ∀ i : Fin n, |a i - p i| ≤ c) :
    ∑ i : Fin n, |smoothCubeWeight c a i - p i| ≤
      (n : ℝ) * (2 * (n + 1 : ℝ) * c) := by
  let D := smoothCubeWeightDenom c a
  have hp_le_ac : ∀ i : Fin n, p i ≤ a i + c := by
    intro i
    have habs := abs_le.mp (hcoord i)
    linarith
  have hD_ge_one : 1 ≤ D := by
    have hsum_le : (∑ i : Fin n, p i) ≤ ∑ i : Fin n, (a i + c) :=
      Finset.sum_le_sum (fun i _ => hp_le_ac i)
    simpa [D, smoothCubeWeightDenom, hp_sum] using hsum_le
  have hD_pos : 0 < D := lt_of_lt_of_le zero_lt_one hD_ge_one
  have hDsub_eq :
      D - 1 = ∑ i : Fin n, ((a i - p i) + c) := by
    calc
      D - 1 = (∑ i : Fin n, (a i + c)) - ∑ i : Fin n, p i := by
        simp [D, smoothCubeWeightDenom, hp_sum]
      _ = ∑ i : Fin n, ((a i + c) - p i) := by
        rw [Finset.sum_sub_distrib]
      _ = ∑ i : Fin n, ((a i - p i) + c) := by
        apply Finset.sum_congr rfl
        intro i _hi
        ring
  have hDsub_abs :
      |D - 1| ≤ (n : ℝ) * (2 * c) := by
    calc
      |D - 1| = |∑ i : Fin n, ((a i - p i) + c)| := by
        rw [hDsub_eq]
      _ ≤ ∑ i : Fin n, |(a i - p i) + c| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n, (|a i - p i| + c) := by
        apply Finset.sum_le_sum
        intro i _hi
        calc
          |(a i - p i) + c| ≤ |a i - p i| + |c| :=
            abs_add_le (a i - p i) c
          _ = |a i - p i| + c := by rw [abs_of_nonneg hc]
      _ ≤ ∑ i : Fin n, (c + c) := by
        apply Finset.sum_le_sum
        intro i _hi
        exact add_le_add (hcoord i) le_rfl
      _ = (n : ℝ) * (2 * c) := by
        rw [Finset.sum_const, Finset.card_fin]
        simp [nsmul_eq_mul]
        ring
  have hpoint :
      ∀ i : Fin n, |smoothCubeWeight c a i - p i| ≤
        2 * (n + 1 : ℝ) * c := by
    intro i
    let A := a i + c
    have hD_abs : |D| = D := abs_of_nonneg hD_pos.le
    have hdiv :
        |smoothCubeWeight c a i - p i| =
          |A - p i * D| / D := by
      have hD_ne : D ≠ 0 := ne_of_gt hD_pos
      unfold smoothCubeWeight
      have hsub :
          (a i + c) / smoothCubeWeightDenom c a - p i =
            (A - p i * D) / D := by
        field_simp [hD_ne, A, D]
        ring
      rw [hsub, abs_div, hD_abs]
    have hdiv_le :
        |A - p i * D| / D ≤ |A - p i * D| := by
      rw [div_le_iff₀ hD_pos]
      have hnonneg : 0 ≤ |A - p i * D| := abs_nonneg _
      nlinarith
    have hnum_eq :
        A - p i * D = (a i - p i) + c - p i * (D - 1) := by
      simp [A]
      ring
    have hnum_bound :
        |A - p i * D| ≤ 2 * (n + 1 : ℝ) * c := by
      calc
        |A - p i * D|
            = |(a i - p i) + c - p i * (D - 1)| := by
                rw [hnum_eq]
        _ ≤ |(a i - p i) + c| + |p i * (D - 1)| :=
                by
                  simpa [sub_zero, zero_sub, abs_neg] using
                    abs_sub_le ((a i - p i) + c) 0 (p i * (D - 1))
        _ ≤ (|a i - p i| + c) + |p i| * |D - 1| := by
                gcongr
                · calc
                    |(a i - p i) + c| ≤ |a i - p i| + |c| :=
                      abs_add_le (a i - p i) c
                    _ = |a i - p i| + c := by rw [abs_of_nonneg hc]
                · rw [abs_mul]
        _ ≤ (c + c) + 1 * ((n : ℝ) * (2 * c)) := by
                have hpabs : |p i| ≤ 1 := by
                  rw [abs_of_nonneg (hp i).1]
                  exact (hp i).2
                exact add_le_add
                  (add_le_add (hcoord i) le_rfl)
                  (mul_le_mul hpabs hDsub_abs (abs_nonneg _) (by norm_num))
        _ ≤ 2 * (n + 1 : ℝ) * c := by
                ring_nf
                exact le_rfl
    exact le_trans (by rw [hdiv]; exact hdiv_le) hnum_bound
  calc
    ∑ i : Fin n, |smoothCubeWeight c a i - p i|
        ≤ ∑ _i : Fin n, (2 * (n + 1 : ℝ) * c) :=
          Finset.sum_le_sum (fun i _ => hpoint i)
    _ = (n : ℝ) * (2 * (n + 1 : ℝ) * c) := by
          rw [Finset.sum_const, Finset.card_fin]
          norm_num [nsmul_eq_mul]

noncomputable def projectedCubeProj
    (κ M : ℝ) (hM : 0 ≤ M)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u))
    (hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap)
    (N : ℕ) (u : ℝ → ℝ) :
    Fin (projectedCubeDim κ M hM Tmap hmap hcompact N) → ℝ :=
  fun i =>
    schauderBumpWeight (projectedCubeNetRadius N)
      (projectedCubeAnchor κ M hM Tmap hmap hcompact N)
      (profileRestrictIccIf (projectedCubeRadius N) u) i

lemma projectedCubeProj_mem_unitCube
    {κ M : ℝ} {hM : 0 ≤ M}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u)}
    {hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap}
    (N : ℕ) (u : ℝ → ℝ) :
    projectedCubeProj κ M hM Tmap hmap hcompact N u ∈
      Freudenthal.unitCube
        (projectedCubeDim κ M hM Tmap hmap hcompact N) :=
  schauderBumpWeightFin_mem_unitCube (projectedCubeNetRadius N)
    (projectedCubeAnchor κ M hM Tmap hmap hcompact N)
    (profileRestrictIccIf (projectedCubeRadius N) u)

noncomputable def projectedCubeLift
    (κ M : ℝ) (hM : 0 ≤ M)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u))
    (hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap)
    (N : ℕ)
    (a : Fin (projectedCubeDim κ M hM Tmap hmap hcompact N) → ℝ) :
    ℝ → ℝ :=
  ∑ i : Fin (projectedCubeDim κ M hM Tmap hmap hcompact N),
    smoothCubeWeight
      (projectedCubeCoordTol κ M hM Tmap hmap hcompact N) a i •
        projectedCubeCenterProfile κ M hM Tmap hmap hcompact N i

lemma projectedCubeLift_trap
    {κ M : ℝ} {hM : 0 ≤ M}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u)}
    {hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap}
    (N : ℕ)
    {a : Fin (projectedCubeDim κ M hM Tmap hmap hcompact N) → ℝ}
    (ha : a ∈ Freudenthal.unitCube
      (projectedCubeDim κ M hM Tmap hmap hcompact N)) :
    InMonotoneWaveTrapSet κ M
      (projectedCubeLift κ M hM Tmap hmap hcompact N a) := by
  exact inMonotoneWaveTrapSet_finset_sum_mem
    (κ := κ) (M := M)
    (w := fun i : Fin (projectedCubeDim κ M hM Tmap hmap hcompact N) =>
      smoothCubeWeight
        (projectedCubeCoordTol κ M hM Tmap hmap hcompact N) a i)
    (center := projectedCubeCenterProfile κ M hM Tmap hmap hcompact N)
    (fun i => smoothCubeWeight_nonneg
      (projectedCubeCoordTol_pos (hM := hM) (hmap := hmap)
        (hcompact := hcompact) N) ha i)
    (smoothCubeWeight_sum_eq_one
      (projectedCubeCoordTol_pos (hM := hM) (hmap := hmap)
        (hcompact := hcompact) N) ha
      (projectedCubeDim_pos (hM := hM) (hmap := hmap)
        (hcompact := hcompact) N))
    (projectedCubeCenterProfile_trap (hM := hM) (hmap := hmap)
      (hcompact := hcompact) N)

lemma abs_finset_weighted_profile_sum_sub_le
    {ι : Type*} [Fintype ι]
    {w v : ι → ℝ} {center : ι → ℝ → ℝ} {M : ℝ}
    {x : ℝ} (hcenter : ∀ i, |center i x| ≤ M) :
    |(∑ i : ι, w i • center i) x -
      (∑ i : ι, v i • center i) x| ≤
        M * ∑ i : ι, |w i - v i| := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hrewrite :
      (∑ i : ι, w i * center i x) -
        (∑ i : ι, v i * center i x) =
          ∑ i : ι, (w i - v i) * center i x := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [hrewrite]
  calc
    |∑ i : ι, (w i - v i) * center i x|
        ≤ ∑ i : ι, |(w i - v i) * center i x| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : ι, |w i - v i| * |center i x| := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [abs_mul]
    _ ≤ ∑ i : ι, |w i - v i| * M := by
          apply Finset.sum_le_sum
          intro i _hi
          exact mul_le_mul_of_nonneg_left (hcenter i) (abs_nonneg _)
    _ = (∑ i : ι, |w i - v i|) * M := by
          rw [Finset.sum_mul]
    _ = M * ∑ i : ι, |w i - v i| := by ring

theorem projectedCubeLift_locallyUniform_of_tendsto
    {κ M : ℝ} {hM : 0 ≤ M}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u)}
    {hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap}
    (N : ℕ)
    {seq : ℕ → Fin (projectedCubeDim κ M hM Tmap hmap hcompact N) → ℝ}
    {a : Fin (projectedCubeDim κ M hM Tmap hmap hcompact N) → ℝ}
    (hseq : Tendsto seq atTop (𝓝 a))
    (ha : a ∈ Freudenthal.unitCube
      (projectedCubeDim κ M hM Tmap hmap hcompact N)) :
    LocallyUniformConverges
      (fun n => projectedCubeLift κ M hM Tmap hmap hcompact N (seq n))
      (projectedCubeLift κ M hM Tmap hmap hcompact N a) := by
  intro R _hR ε hε
  let c := projectedCubeCoordTol κ M hM Tmap hmap hcompact N
  let d := projectedCubeDim κ M hM Tmap hmap hcompact N
  have hc : 0 < c := projectedCubeCoordTol_pos
    (hM := hM) (hmap := hmap) (hcompact := hcompact) N
  have hd : 0 < d := projectedCubeDim_pos
    (hM := hM) (hmap := hmap) (hcompact := hcompact) N
  have hS_tend :
      Tendsto
        (fun n => ∑ i : Fin d,
          |smoothCubeWeight c (seq n) i - smoothCubeWeight c a i|)
        atTop (𝓝 0) := by
    exact tendsto_smoothCubeWeight_abs_sum
      (n := d) (c := c) hseq hc ha hd
  have hdenpos : 0 < M + 1 := by linarith
  have hδ : 0 < ε / (M + 1) := div_pos hε hdenpos
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.mp hS_tend
    (ε / (M + 1)) hδ
  filter_upwards [eventually_atTop.mpr ⟨N0, hN0⟩] with n hn x _hx
  let S : ℝ := ∑ i : Fin d,
    |smoothCubeWeight c (seq n) i - smoothCubeWeight c a i|
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hS_lt : S < ε / (M + 1) := by
    have hdist := hn
    have habs : |S - 0| < ε / (M + 1) := by
      simpa [Real.dist_eq, S, d, c] using hdist
    simpa [sub_zero, abs_of_nonneg hS_nonneg] using habs
  have hcenter :
      ∀ i : Fin d,
        |projectedCubeCenterProfile κ M hM Tmap hmap hcompact N i x| ≤ M := by
    intro i
    have ht := projectedCubeCenterProfile_trap
      (hM := hM) (hmap := hmap) (hcompact := hcompact) N i
    rw [abs_of_nonneg (ht.nonneg x)]
    exact ht.le_M x
  have hbound :
      |projectedCubeLift κ M hM Tmap hmap hcompact N (seq n) x -
        projectedCubeLift κ M hM Tmap hmap hcompact N a x| ≤ M * S := by
    simpa [projectedCubeLift, S, c, d] using
      abs_finset_weighted_profile_sum_sub_le
        (w := fun i : Fin d => smoothCubeWeight c (seq n) i)
        (v := fun i : Fin d => smoothCubeWeight c a i)
        (center := projectedCubeCenterProfile κ M hM Tmap hmap hcompact N)
        (M := M) (x := x) hcenter
  have hMsum_le : M * S ≤ (M + 1) * S := by
    nlinarith [hM, hS_nonneg]
  have hsmall : (M + 1) * S < ε := by
    have hmul := mul_lt_mul_of_pos_left hS_lt hdenpos
    have hright : (M + 1) * (ε / (M + 1)) = ε := by
      field_simp [ne_of_gt hdenpos]
    simpa [hright] using hmul
  exact lt_of_le_of_lt hbound (lt_of_le_of_lt hMsum_le hsmall)

theorem projectedCubeTfin_continuousOn
    {κ M : ℝ} {hM : 0 ≤ M}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u)}
    {hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap}
    (hcont : LocalUniformContinuousOn (InMonotoneWaveTrapSet κ M) Tmap)
    (N : ℕ) :
    ContinuousOn
      (fun a =>
        projectedCubeProj κ M hM Tmap hmap hcompact N
          (Tmap (projectedCubeLift κ M hM Tmap hmap hcompact N a)))
      (Freudenthal.unitCube
        (projectedCubeDim κ M hM Tmap hmap hcompact N)) := by
  rw [continuousOn_iff_continuous_restrict]
  rw [continuous_iff_continuousAt]
  intro a0
  rw [ContinuousAt, tendsto_nhds_iff_seq_tendsto]
  intro seq hseq
  rw [tendsto_pi_nhds]
  intro i
  let d := projectedCubeDim κ M hM Tmap hmap hcompact N
  let R := projectedCubeRadius N
  let eta := projectedCubeNetRadius N
  let anchor := projectedCubeAnchor κ M hM Tmap hmap hcompact N
  let lift := projectedCubeLift κ M hM Tmap hmap hcompact N
  have hseq_val :
      Tendsto (fun n : ℕ => (seq n : Fin d → ℝ)) atTop
        (𝓝 (a0 : Fin d → ℝ)) :=
    (continuous_subtype_val.tendsto a0).comp hseq
  have hlift :
      LocallyUniformConverges (fun n => lift (seq n))
        (lift a0) := by
    simpa [lift, d] using
      projectedCubeLift_locallyUniform_of_tendsto
        (hM := hM) (hmap := hmap) (hcompact := hcompact)
        N hseq_val a0.2
  have htrap_seq :
      ∀ n, InMonotoneWaveTrapSet κ M (lift (seq n)) := by
    intro n
    simpa [lift, d] using
      projectedCubeLift_trap (hM := hM) (hmap := hmap)
        (hcompact := hcompact) N (seq n).2
  have htrap_a :
      InMonotoneWaveTrapSet κ M (lift a0) := by
    simpa [lift, d] using
      projectedCubeLift_trap (hM := hM) (hmap := hmap)
        (hcompact := hcompact) N a0.2
  have hT :
      LocallyUniformConverges
        (fun n => Tmap (lift (seq n))) (Tmap (lift a0)) :=
    hcont (fun n => lift (seq n)) (lift a0) htrap_seq htrap_a hlift
  have hrest :
      Tendsto
        (fun n =>
          profileRestrictIcc R (Tmap (lift (seq n)))
            ((hmap (lift (seq n)) (htrap_seq n)).trap.cunif_bdd.1))
        atTop
        (𝓝 (profileRestrictIcc R (Tmap (lift a0))
          ((hmap (lift a0) htrap_a).trap.cunif_bdd.1))) := by
    exact tendsto_profileRestrictIcc_of_locallyUniform
      (R := R) (seq := fun n => Tmap (lift (seq n)))
      (u := Tmap (lift a0)) (projectedCubeRadius_pos N)
      (fun n => ((hmap (lift (seq n)) (htrap_seq n)).trap.cunif_bdd.1))
      ((hmap (lift a0) htrap_a).trap.cunif_bdd.1) hT
  have hif :
      Tendsto
        (fun n => profileRestrictIccIf R (Tmap (lift (seq n))))
        atTop (𝓝 (profileRestrictIccIf R (Tmap (lift a0)))) := by
    have hseq_eq :
        (fun n =>
          profileRestrictIcc R (Tmap (lift (seq n)))
            ((hmap (lift (seq n)) (htrap_seq n)).trap.cunif_bdd.1)) =ᶠ[atTop]
          (fun n => profileRestrictIccIf R (Tmap (lift (seq n)))) := by
      exact Eventually.of_forall fun n => by
        exact (profileRestrictIccIf_eq R
          ((hmap (lift (seq n)) (htrap_seq n)).trap.cunif_bdd.1)).symm
    have hlim_eq :
        profileRestrictIccIf R (Tmap (lift a0)) =
          profileRestrictIcc R (Tmap (lift a0))
            ((hmap (lift a0) htrap_a).trap.cunif_bdd.1) := by
      rw [profileRestrictIccIf_eq R
        ((hmap (lift a0) htrap_a).trap.cunif_bdd.1)]
    exact Tendsto.congr' hseq_eq (by simpa [hlim_eq] using hrest)
  have hmem :
      profileRestrictIccIf R (Tmap (lift a0)) ∈
        waveTrapImageRestrictSet κ M R Tmap hmap := by
    simpa [R] using
      projectedCubeProfileRestrictIf_mem_image_of_map
        (hmap := hmap) N htrap_a
  have hsum :
      0 < schauderBumpSum eta anchor
        (profileRestrictIccIf R (Tmap (lift a0))) := by
    simpa [eta, anchor, R] using
      projectedCubeBumpSum_pos_of_mem_image
        (hM := hM) (hmap := hmap) (hcompact := hcompact)
        N hmem
  simpa [projectedCubeProj, eta, anchor, R, lift, d] using
    tendsto_schauderBumpWeight_of_sum_pos
      (xseq := fun n => profileRestrictIccIf R (Tmap (lift (seq n))))
      (x := profileRestrictIccIf R (Tmap (lift a0)))
      hif hsum i

theorem projectedCubePartition_error_le
    {κ M : ℝ} {hM : 0 ≤ M}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u)}
    {hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap}
    (N : ℕ) {u : ℝ → ℝ} (hu : InMonotoneWaveTrapSet κ M u)
    {x : ℝ} (hx : x ∈ Set.Icc (-(projectedCubeRadius N)) (projectedCubeRadius N)) :
    |Tmap u x -
      (∑ i : Fin (projectedCubeDim κ M hM Tmap hmap hcompact N),
        projectedCubeProj κ M hM Tmap hmap hcompact N (Tmap u) i •
          projectedCubeCenterProfile κ M hM Tmap hmap hcompact N i) x| ≤
        projectedCubeNetRadius N := by
  let d := projectedCubeDim κ M hM Tmap hmap hcompact N
  let R := projectedCubeRadius N
  let eta := projectedCubeNetRadius N
  let anchor := projectedCubeAnchor κ M hM Tmap hmap hcompact N
  let p := projectedCubeProj κ M hM Tmap hmap hcompact N (Tmap u)
  let center := projectedCubeCenterProfile κ M hM Tmap hmap hcompact N
  let g := profileRestrictIccIf R (Tmap u)
  have hmem : g ∈ waveTrapImageRestrictSet κ M R Tmap hmap := by
    simpa [g, R] using
      projectedCubeProfileRestrictIf_mem_image_of_map
        (hmap := hmap) N hu
  have hsum_pos : 0 < schauderBumpSum eta anchor g := by
    simpa [eta, anchor, g, R] using
      projectedCubeBumpSum_pos_of_mem_image
        (hM := hM) (hmap := hmap) (hcompact := hcompact) N hmem
  have hp_sum : ∑ i : Fin d, p i = 1 := by
    simpa [p, projectedCubeProj, eta, anchor, g, R, d] using
      sum_schauderBumpWeight_of_sum_pos hsum_pos
  have hp_nonneg : ∀ i : Fin d, 0 ≤ p i := by
    intro i
    simpa [p, projectedCubeProj, eta, anchor, g, R, d] using
      schauderBumpWeight_nonneg eta anchor g i
  have hterm :
      ∀ i : Fin d, p i *
        |Tmap u x - center i x| ≤ p i * eta := by
    intro i
    by_cases hpi_zero : p i = 0
    · simp [hpi_zero]
    · have hpi_pos : 0 < p i := lt_of_le_of_ne (hp_nonneg i) (Ne.symm hpi_zero)
      have hdist_fun : dist g (anchor i) < eta := by
        have hdist := dist_lt_of_schauderBumpWeight_pos
          (ε := eta) (center := anchor) (x := g) (i := i)
          hsum_pos
        have hp_eq :
            schauderBumpWeight eta anchor g i = p i := by
          simp [p, projectedCubeProj, eta, anchor, g, R, d]
        exact hdist (by simpa [hp_eq] using hpi_pos)
      let xR : Set.Icc (-R) R := ⟨x, by simpa [R] using hx⟩
      have hpoint_dist :
          dist (g xR) (anchor i xR) < eta :=
        lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist xR) hdist_fun
      have hg_apply : g xR = Tmap u x := by
        have hcontu := (hmap u hu).trap.cunif_bdd.1
        change profileRestrictIccIf R (Tmap u) xR = Tmap u x
        rw [profileRestrictIccIf_eq R hcontu]
        rfl
      have hanchor_apply : anchor i xR = center i x := by
        have hres := projectedCubeCenterProfile_restrict
          (hM := hM) (hmap := hmap) (hcompact := hcompact) N i
        have hres' :
            anchor i =
              profileRestrictIcc R (center i)
                ((projectedCubeCenterProfile_trap
                  (hM := hM) (hmap := hmap) (hcompact := hcompact)
                  N i).trap.cunif_bdd.1) := by
          simpa [anchor, center, R] using hres
        rw [hres']
        rfl
      have habs : |Tmap u x - center i x| < eta := by
        simpa [Real.dist_eq, hg_apply, hanchor_apply] using hpoint_dist
      exact mul_le_mul_of_nonneg_left (le_of_lt habs) (hp_nonneg i)
  simpa [p, center, d] using
    abs_sub_weighted_sum_le
      (w := p) (y := Tmap u x) (z := fun i : Fin d => center i x)
      (η := eta) hp_nonneg hp_sum hterm

def projectedCubeLocalError (M : ℝ) (N : ℕ) (R : ℝ) : ℝ :=
  if R ≤ projectedCubeRadius N then
    4 * projectedCubeNetRadius N
  else
    2 * M + 1

lemma projectedCubeLocalError_nonneg {M : ℝ} (hM : 0 ≤ M)
    (N : ℕ) (R : ℝ) :
    0 ≤ projectedCubeLocalError M N R := by
  unfold projectedCubeLocalError
  split_ifs
  · exact mul_nonneg (by norm_num) (projectedCubeNetRadius_nonneg N)
  · nlinarith

lemma projectedCubeLocalError_tendsto {M R : ℝ} :
    Tendsto (fun N => projectedCubeLocalError M N R) atTop (𝓝 0) := by
  have hev : ∀ᶠ N : ℕ in atTop, R ≤ projectedCubeRadius N := by
    obtain ⟨N0, hN0⟩ := exists_nat_gt R
    refine eventually_atTop.mpr ⟨N0, ?_⟩
    intro N hN
    unfold projectedCubeRadius
    have hNR : R < (N0 : ℝ) := hN0
    have hN0N : (N0 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hsmall :
      Tendsto (fun N => 4 * projectedCubeNetRadius N) atTop (𝓝 0) := by
    simpa using projectedCubeNetRadius_tendsto.const_mul 4
  refine Tendsto.congr' ?_ hsmall
  filter_upwards [hev] with N hN
  simp [projectedCubeLocalError, hN]

lemma projectedCube_smoothWeight_error_scale_le
    {κ M : ℝ} {hM : 0 ≤ M}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u)}
    {hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap}
    (N : ℕ) :
    M *
      ((projectedCubeDim κ M hM Tmap hmap hcompact N : ℝ) *
        (2 * (projectedCubeDim κ M hM Tmap hmap hcompact N + 1 : ℝ) *
            projectedCubeCoordTol κ M hM Tmap hmap hcompact N)) ≤
      projectedCubeNetRadius N := by
  let d : ℝ := projectedCubeDim κ M hM Tmap hmap hcompact N
  let eta : ℝ := projectedCubeNetRadius N
  let c : ℝ := projectedCubeCoordTol κ M hM Tmap hmap hcompact N
  have hd_nonneg : 0 ≤ d := by
    dsimp [d]
    positivity
  have hd1_pos : 0 < d + 1 := by
    dsimp [d]
    positivity
  have hM1_pos : 0 < M + 1 := by linarith
  have heta_nonneg : 0 ≤ eta := by
    dsimp [eta]
    exact projectedCubeNetRadius_nonneg N
  have hfracM : M / (M + 1) ≤ 1 := (div_le_one hM1_pos).mpr (by linarith)
  have hfracM_nonneg : 0 ≤ M / (M + 1) := div_nonneg hM hM1_pos.le
  have hfracD :
      d / (8 * (d + 1)) ≤ 1 := by
    rw [div_le_one]
    · nlinarith [hd_nonneg]
    · positivity
  have hfracD_nonneg : 0 ≤ d / (8 * (d + 1)) := by
    exact div_nonneg hd_nonneg (by positivity)
  have hrewrite :
      M * (d * (2 * (d + 1) * c)) =
        eta * ((M / (M + 1)) * (d / (8 * (d + 1)))) := by
    dsimp [c, d, eta, projectedCubeCoordTol]
    field_simp [ne_of_gt hM1_pos, ne_of_gt hd1_pos]
    ring
  rw [show
      M *
        ((projectedCubeDim κ M hM Tmap hmap hcompact N : ℝ) *
          (2 *
            (projectedCubeDim κ M hM Tmap hmap hcompact N + 1 : ℝ) *
              projectedCubeCoordTol κ M hM Tmap hmap hcompact N)) =
        M * (d * (2 * (d + 1) * c)) by simp [d, c]]
  rw [hrewrite]
  calc
    eta * ((M / (M + 1)) * (d / (8 * (d + 1))))
        ≤ eta * (1 * 1) := by
          apply mul_le_mul_of_nonneg_left _ heta_nonneg
          exact mul_le_mul hfracM hfracD hfracD_nonneg (by norm_num)
    _ = eta := by ring

theorem projectedCubeResidual_le
    {κ M : ℝ} {hM : 0 ≤ M}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u)}
    {hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap}
    (N : ℕ)
    (a : Fin (projectedCubeDim κ M hM Tmap hmap hcompact N) → ℝ)
    (ha : a ∈ Freudenthal.unitCube
      (projectedCubeDim κ M hM Tmap hmap hcompact N))
    (hclose :
      ‖projectedCubeProj κ M hM Tmap hmap hcompact N
          (Tmap (projectedCubeLift κ M hM Tmap hmap hcompact N a)) - a‖ ≤
        projectedCubeCoordTol κ M hM Tmap hmap hcompact N)
    (R : ℝ) (_hR : 0 < R) (x : ℝ) (hx : x ∈ Set.Icc (-R) R) :
    |Tmap (projectedCubeLift κ M hM Tmap hmap hcompact N a) x -
      projectedCubeLift κ M hM Tmap hmap hcompact N a x| ≤
        projectedCubeLocalError M N R := by
  let d := projectedCubeDim κ M hM Tmap hmap hcompact N
  let eta := projectedCubeNetRadius N
  let c := projectedCubeCoordTol κ M hM Tmap hmap hcompact N
  let lift := projectedCubeLift κ M hM Tmap hmap hcompact N
  let p := projectedCubeProj κ M hM Tmap hmap hcompact N (Tmap (lift a))
  let q : Fin d → ℝ := fun i => smoothCubeWeight c a i
  let center := projectedCubeCenterProfile κ M hM Tmap hmap hcompact N
  have hlift_trap : InMonotoneWaveTrapSet κ M (lift a) := by
    simpa [lift, d] using
      projectedCubeLift_trap (hM := hM) (hmap := hmap)
        (hcompact := hcompact) N ha
  have hf_trap : InMonotoneWaveTrapSet κ M (Tmap (lift a)) :=
    hmap (lift a) hlift_trap
  by_cases hcov : R ≤ projectedCubeRadius N
  · have hxN :
        x ∈ Set.Icc (-(projectedCubeRadius N)) (projectedCubeRadius N) := by
      rcases hx with ⟨hxL, hxU⟩
      constructor <;> linarith
    have hpart :
        |Tmap (lift a) x -
          (∑ i : Fin d, p i • center i) x| ≤ eta := by
      simpa [lift, p, center, d, eta] using
        projectedCubePartition_error_le
          (hM := hM) (hmap := hmap) (hcompact := hcompact)
          N hlift_trap hxN
    have hp_unit : p ∈ Freudenthal.unitCube d := by
      simpa [p, d] using
        projectedCubeProj_mem_unitCube
          (hM := hM) (hmap := hmap) (hcompact := hcompact)
          N (Tmap (lift a))
    have hmem :
        profileRestrictIccIf (projectedCubeRadius N) (Tmap (lift a)) ∈
          waveTrapImageRestrictSet κ M (projectedCubeRadius N) Tmap hmap := by
      simpa [lift] using
        projectedCubeProfileRestrictIf_mem_image_of_map
          (hmap := hmap) N hlift_trap
    have hsum_pos :
        0 < schauderBumpSum eta
          (projectedCubeAnchor κ M hM Tmap hmap hcompact N)
          (profileRestrictIccIf (projectedCubeRadius N) (Tmap (lift a))) := by
      simpa [eta] using
        projectedCubeBumpSum_pos_of_mem_image
          (hM := hM) (hmap := hmap) (hcompact := hcompact)
          N hmem
    have hp_sum : ∑ i : Fin d, p i = 1 := by
      simpa [p, projectedCubeProj, d, eta] using
        sum_schauderBumpWeight_of_sum_pos hsum_pos
    have hcoord : ∀ i : Fin d, |a i - p i| ≤ c := by
      intro i
      have hi := projectedCube_coord_abs_sub_le_of_norm hclose i
      simpa [p, c, d, Pi.sub_apply, abs_sub_comm] using hi
    have hq_p_sum :
        ∑ i : Fin d, |q i - p i| ≤
          (d : ℝ) * (2 * (d + 1 : ℝ) * c) := by
      simpa [q, d, c] using
        smoothCubeWeight_close_to_simplex_weights
          (n := d) (c := c) (a := a) (p := p)
          (projectedCubeCoordTol_nonneg
            (hM := hM) (hmap := hmap) (hcompact := hcompact) N)
          hp_unit hp_sum hcoord
    have hp_q_sum :
        ∑ i : Fin d, |p i - q i| ≤
          (d : ℝ) * (2 * (d + 1 : ℝ) * c) := by
      simpa [abs_sub_comm] using hq_p_sum
    have hcenter :
        ∀ i : Fin d, |center i x| ≤ M := by
      intro i
      have ht := projectedCubeCenterProfile_trap
        (hM := hM) (hmap := hmap) (hcompact := hcompact) N i
      rw [abs_of_nonneg (ht.nonneg x)]
      exact ht.le_M x
    have hweight_raw :
        |(∑ i : Fin d, p i • center i) x -
          (∑ i : Fin d, q i • center i) x| ≤
            M * ∑ i : Fin d, |p i - q i| := by
      exact abs_finset_weighted_profile_sum_sub_le
        (w := p) (v := q) (center := center) (M := M) (x := x) hcenter
    have hweight :
        |(∑ i : Fin d, p i • center i) x - lift a x| ≤ eta := by
      have hscale :
          M * ∑ i : Fin d, |p i - q i| ≤ eta := by
        have hmul := mul_le_mul_of_nonneg_left hp_q_sum hM
        exact le_trans hmul
          (by
            simpa [d, c, eta] using
              projectedCube_smoothWeight_error_scale_le
                (hM := hM) (hmap := hmap) (hcompact := hcompact) N)
      have hlift_eq :
          lift a = ∑ i : Fin d, q i • center i := by
        simp [lift, projectedCubeLift, q, center, c, d]
      simpa [hlift_eq] using le_trans hweight_raw hscale
    have htri :
        |Tmap (lift a) x - lift a x| ≤
          |Tmap (lift a) x - (∑ i : Fin d, p i • center i) x| +
            |(∑ i : Fin d, p i • center i) x - lift a x| := by
      simpa using abs_sub_le (Tmap (lift a) x)
        ((∑ i : Fin d, p i • center i) x) (lift a x)
    have herr : |Tmap (lift a) x - lift a x| ≤ 4 * eta := by
      nlinarith [htri, hpart, hweight, projectedCubeNetRadius_nonneg N]
    simpa [projectedCubeLocalError, hcov, eta, lift] using herr
  · have hf_nonneg : 0 ≤ Tmap (lift a) x := hf_trap.nonneg x
    have hf_le : Tmap (lift a) x ≤ M := hf_trap.le_M x
    have hu_nonneg : 0 ≤ lift a x := hlift_trap.nonneg x
    have hu_le : lift a x ≤ M := hlift_trap.le_M x
    have hrough : |Tmap (lift a) x - lift a x| ≤ 2 * M + 1 := by
      have htri0 :
          |Tmap (lift a) x - lift a x| ≤
            |Tmap (lift a) x| + |lift a x| := by
        simpa [sub_zero, zero_sub, abs_neg] using
          abs_sub_le (Tmap (lift a) x) 0 (lift a x)
      calc
        |Tmap (lift a) x - lift a x|
            ≤ |Tmap (lift a) x| + |lift a x| := htri0
        _ = Tmap (lift a) x + lift a x := by
            rw [abs_of_nonneg hf_nonneg, abs_of_nonneg hu_nonneg]
        _ ≤ 2 * M + 1 := by nlinarith
    simpa [projectedCubeLocalError, hcov, lift] using hrough

noncomputable def waveTrapProjectedCubeApproxData
    {κ M : ℝ} (hM : 0 ≤ M)
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hmap : ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (Tmap u))
    (hcont : LocalUniformContinuousOn (InMonotoneWaveTrapSet κ M) Tmap)
    (hcompact : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) Tmap) :
    ProjectedCubeApproxData (InMonotoneWaveTrapSet κ M) Tmap := by
  refine
    { dim := projectedCubeDim κ M hM Tmap hmap hcompact
      proj := projectedCubeProj κ M hM Tmap hmap hcompact
      lift := projectedCubeLift κ M hM Tmap hmap hcompact
      eps := projectedCubeCoordTol κ M hM Tmap hmap hcompact
      localError := projectedCubeLocalError M
      eps_pos := ?_
      proj_trap := ?_
      maps := ?_
      cont := ?_
      lift_trap := ?_
      localError_nonneg := ?_
      localError_tendsto := ?_
      residual_le := ?_ }
  · intro N
    exact projectedCubeCoordTol_pos (hM := hM) (hmap := hmap)
      (hcompact := hcompact) N
  · intro N u _hu
    exact projectedCubeProj_mem_unitCube (hM := hM) (hmap := hmap)
      (hcompact := hcompact) N u
  · intro N a _ha
    exact projectedCubeProj_mem_unitCube (hM := hM) (hmap := hmap)
      (hcompact := hcompact) N
      (Tmap (projectedCubeLift κ M hM Tmap hmap hcompact N a))
  · intro N
    exact projectedCubeTfin_continuousOn (hM := hM) (hmap := hmap)
      (hcompact := hcompact) hcont N
  · intro N a ha
    exact projectedCubeLift_trap (hM := hM) (hmap := hmap)
      (hcompact := hcompact) N ha
  · intro N R
    exact projectedCubeLocalError_nonneg hM N R
  · intro R _hR
    exact projectedCubeLocalError_tendsto
  · intro N a ha hclose R hR x hx
    exact projectedCubeResidual_le (hM := hM) (hmap := hmap)
      (hcompact := hcompact) N a ha hclose R hR x hx

#print axioms profileRestrictIcc
#print axioms tendsto_profileRestrictIcc_of_locallyUniform
#print axioms totallyBounded_of_subseq_tendsto
#print axioms waveTrapImageRestrictSet_totallyBounded
#print axioms waveTrapImageRestrictSet_isCompact_closure
#print axioms exists_finite_eps_net_waveTrapImageRestrict_closure
#print axioms exists_finite_eps_net_waveTrapImageRestrict
#print axioms schauderBump
#print axioms schauderBumpWeight
#print axioms sum_schauderBumpWeight_of_sum_pos
#print axioms inMonotoneWaveTrapSet_finset_sum_mem
#print axioms inMonotoneWaveTrapSet_bumpPartition_mem
#print axioms projectedCubeLift_locallyUniform_of_tendsto
#print axioms projectedCubeTfin_continuousOn
#print axioms projectedCubePartition_error_le
#print axioms projectedCubeResidual_le
#print axioms waveTrapProjectedCubeApproxData

end

end ShenWork.Paper1
