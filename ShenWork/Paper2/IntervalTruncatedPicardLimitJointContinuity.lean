import ShenWork.Paper2.IntervalBFormCron2TruncatedPicard
import ShenWork.Paper2.IntervalDomainPositiveWindowK1OnEndpoint
import Mathlib.Topology.UniformSpace.UniformApproximation

open Filter Topology Set
open scoped Topology

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalMildPicard (HasContinuousSlices HasJointMeasurability)
open ShenWork.IntervalDomainPositiveWindowK1OnEndpoint
  (cosineCoeffs_continuousOn_of_jointContinuousOn_Icc)

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-- A positive-time version of the compact-parameter cosine-coefficient
continuity lemma.  Around each `s₀ > 0`, restrict to the closed window
`[s₀/2,T]` and use the existing `Icc` theorem. -/
theorem cosineCoeffs_continuousOn_of_jointContinuousOn_Ioc
    {f : ℝ → ℝ → ℝ} {T : ℝ} (k : ℕ)
    (hf : ContinuousOn (Function.uncurry f)
      (Set.Ioc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (fun s => ShenWork.IntervalNeumannFullKernel.cosineCoeffs (f s) k)
      (Set.Ioc (0 : ℝ) T) := by
  intro s hs
  set a : ℝ := s / 2
  have ha : 0 < a := by
    dsimp [a]
    linarith [hs.1]
  have hsa : s ∈ Set.Icc a T := by
    exact ⟨by dsimp [a]; linarith [hs.1], hs.2⟩
  have hsub :
      Set.Icc a T ×ˢ Set.Icc (0 : ℝ) 1 ⊆
        Set.Ioc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1 := by
    intro q hq
    obtain ⟨ht, hx⟩ := Set.mem_prod.mp hq
    exact Set.mem_prod.mpr ⟨⟨lt_of_lt_of_le ha ht.1, ht.2⟩, hx⟩
  have hf_closed : ContinuousOn (Function.uncurry f)
      (Set.Icc a T ×ˢ Set.Icc (0 : ℝ) 1) :=
    hf.mono hsub
  have hcoeff : ContinuousOn
      (fun r => ShenWork.IntervalNeumannFullKernel.cosineCoeffs (f r) k)
      (Set.Icc a T) :=
    cosineCoeffs_continuousOn_of_jointContinuousOn_Icc (f := f) (c := a) (T := T)
      k hf_closed
  have hnh : Set.Icc a T ∈ 𝓝[Set.Ioc (0 : ℝ) T] s := by
    have hIoi : Set.Ioi a ∈ 𝓝 s :=
      Ioi_mem_nhds (by dsimp [a]; linarith [hs.1])
    have hinter : Set.Ioc (0 : ℝ) T ∩ Set.Ioi a ∈ 𝓝[Set.Ioc (0 : ℝ) T] s :=
      inter_mem_nhdsWithin _ hIoi
    exact mem_of_superset hinter (by
      intro y hy
      exact ⟨le_of_lt hy.2, hy.1.2⟩)
  exact (hcoeff.continuousWithinAt hsa).mono_of_mem_nhdsWithin hnh

/-- The lifted joint field of a truncated Picard iterate. -/
def truncatedConjugatePicardIterJoint (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ) (n : ℕ) : ℝ × ℝ → ℝ :=
  fun q => intervalDomainLift (truncatedConjugatePicardIter p u₀ n q.1) q.2

/-- The lifted joint field of the truncated Picard limit. -/
def truncatedConjugatePicardLimitJoint (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ) (T : ℝ) : ℝ × ℝ → ℝ :=
  fun q => intervalDomainLift (truncatedConjugatePicardLimit p u₀ T q.1) q.2

/-- The geometric tail estimate gives uniform convergence of the lifted Picard
iterates to the lifted limit on the positive-time slab `(0,T] × [0,1]`. -/
theorem truncatedConjugatePicardIter_tendstoUniformlyOn_joint_Ioc
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {T K C₀ : ℝ} (hT : 0 < T) (hK : K < 1) (hK_nn : 0 ≤ K)
    (hC₀ : 0 ≤ C₀)
    (hbound : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T →
      ∀ x : intervalDomainPoint,
        |truncatedConjugatePicardIter p u₀ (n + 1) t x
          - truncatedConjugatePicardIter p u₀ n t x| ≤ K ^ n * C₀) :
    TendstoUniformlyOn
      (fun n => truncatedConjugatePicardIterJoint p u₀ n)
      (truncatedConjugatePicardLimitJoint p u₀ T) atTop
      (Set.Ioc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ :=
    truncatedConjugatePicardIter_uniform_convergence p u₀ hT hK hK_nn hC₀
      hbound ε hε
  filter_upwards [eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hn q hq
  obtain ⟨ht, hx⟩ := Set.mem_prod.mp hq
  have htail := hN n hn q.1 ht.1 ht.2 ⟨q.2, hx⟩
  simpa [truncatedConjugatePicardIterJoint, truncatedConjugatePicardLimitJoint,
    intervalDomainLift, hx, Real.dist_eq, abs_sub_comm] using htail

/-- Uniform convergence plus joint continuity of every iterate gives joint
continuity of the truncated Picard limit on `(0,T] × [0,1]`.  The iterate-side
joint continuity is an explicit hypothesis: the contraction data alone only
stores spatial slice continuity. -/
theorem truncatedConjugatePicardLimit_jointContinuousOn_Ioc
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {T K C₀ : ℝ} (hT : 0 < T) (hK : K < 1) (hK_nn : 0 ≤ K)
    (hC₀ : 0 ≤ C₀)
    (hbound : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T →
      ∀ x : intervalDomainPoint,
        |truncatedConjugatePicardIter p u₀ (n + 1) t x
          - truncatedConjugatePicardIter p u₀ n t x| ≤ K ^ n * C₀)
    (hiter_joint : ∀ n,
      ContinuousOn (truncatedConjugatePicardIterJoint p u₀ n)
        (Set.Ioc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (truncatedConjugatePicardLimitJoint p u₀ T)
      (Set.Ioc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
  exact
    (truncatedConjugatePicardIter_tendstoUniformlyOn_joint_Ioc
      p u₀ hT hK hK_nn hC₀ hbound).continuousOn
      (Filter.Eventually.frequently (Filter.Eventually.of_forall hiter_joint))

/-- Data-level wrapper: the existence data provide the geometric Picard
convergence bound.  The only additional input is the genuinely separate
iterate-side joint continuity on the positive-time slab. -/
theorem truncatedConjugatePicardLimit_jointContinuousOn_Ioc_of_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : TruncatedConjugateMildExistenceData p u₀)
    (hiter_joint : ∀ n,
      ContinuousOn (truncatedConjugatePicardIterJoint p u₀ n)
        (Set.Ioc (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (truncatedConjugatePicardLimitJoint p u₀ D.T)
      (Set.Ioc (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hball_cont := fun n =>
    truncatedConjugatePicardIter_ball p u₀ D.hbase_ball D.hbase_cont
      D.hmapsTo D.hcont_preserved D.hbase_meas D.hmeas_preserved n
  have hball := fun n => (hball_cont n).1
  have hcont_iterates := fun n => (hball_cont n).2
  have hmeas_iterates :
      ∀ n, HasJointMeasurability (truncatedConjugatePicardIter p u₀ n) := by
    intro n
    induction n with
    | zero => exact D.hbase_meas
    | succ n ih => exact D.hmeas_preserved _ ih
  have hgeom := truncatedConjugatePicardIter_geometric p u₀ D.hK_nn hball
    hcont_iterates hmeas_iterates D.hcontr D.hC₀ D.hbase_diff
  exact
    truncatedConjugatePicardLimit_jointContinuousOn_Ioc p u₀
      D.hT D.hK D.hK_nn D.hC₀ (fun n => hgeom n) hiter_joint

/-- The joint positive-time continuity immediately gives time continuity at each
fixed spatial point. -/
theorem truncatedConjugatePicardLimit_timeSlice_continuousOn_Ioc
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {T : ℝ}
    (hjoint : ContinuousOn (truncatedConjugatePicardLimitJoint p u₀ T)
      (Set.Ioc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1))
    (x : intervalDomainPoint) :
    ContinuousOn (fun s => truncatedConjugatePicardLimit p u₀ T s x)
      (Set.Ioc (0 : ℝ) T) := by
  have hpair : ContinuousOn (fun s : ℝ => ((s, x.1) : ℝ × ℝ))
      (Set.Ioc (0 : ℝ) T) :=
    continuousOn_id.prodMk continuousOn_const
  have hmaps : MapsTo (fun s : ℝ => ((s, x.1) : ℝ × ℝ))
      (Set.Ioc (0 : ℝ) T)
      (Set.Ioc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro s hs
    exact Set.mem_prod.mpr ⟨hs, x.2⟩
  have hcomp := hjoint.comp hpair hmaps
  simpa [Function.comp_def, truncatedConjugatePicardLimitJoint,
    intervalDomainLift, x.2] using hcomp

/-- Data-level time-slice continuity of the limit at a fixed spatial point,
once the Picard iterates are jointly continuous on `(0,T] × [0,1]`. -/
theorem truncatedConjugatePicardLimit_timeSlice_continuousOn_Ioc_of_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : TruncatedConjugateMildExistenceData p u₀)
    (hiter_joint : ∀ n,
      ContinuousOn (truncatedConjugatePicardIterJoint p u₀ n)
        (Set.Ioc (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1))
    (x : intervalDomainPoint) :
    ContinuousOn (fun s => truncatedConjugatePicardLimit p u₀ D.T s x)
      (Set.Ioc (0 : ℝ) D.T) :=
  truncatedConjugatePicardLimit_timeSlice_continuousOn_Ioc p u₀
    (truncatedConjugatePicardLimit_jointContinuousOn_Ioc_of_data D hiter_joint) x

/-- Spatial slice continuity can also be read from the joint positive-time
continuity.  This is useful when replacing older `HasContinuousSlices` inputs. -/
theorem truncatedConjugatePicardLimit_hasContinuousSlices_of_joint_Ioc
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {T : ℝ}
    (hjoint : ContinuousOn (truncatedConjugatePicardLimitJoint p u₀ T)
      (Set.Ioc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)) :
    HasContinuousSlices T (truncatedConjugatePicardLimit p u₀ T) := by
  intro t ht htT
  rw [continuous_iff_continuousAt]
  intro x
  have hpair : Continuous (fun y : intervalDomainPoint => ((t, y.1) : ℝ × ℝ)) :=
    continuous_const.prodMk continuous_subtype_val
  have hmaps : MapsTo (fun y : intervalDomainPoint => ((t, y.1) : ℝ × ℝ))
      Set.univ (Set.Ioc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro y _hy
    exact Set.mem_prod.mpr ⟨⟨ht, htT⟩, y.2⟩
  have hcont : ContinuousOn
      (fun y : intervalDomainPoint =>
        truncatedConjugatePicardLimitJoint p u₀ T (t, y.1)) Set.univ :=
    hjoint.comp hpair.continuousOn hmaps
  have hx : ContinuousWithinAt
      (fun y : intervalDomainPoint =>
        truncatedConjugatePicardLimitJoint p u₀ T (t, y.1)) Set.univ x :=
    hcont.continuousWithinAt trivial
  simpa [truncatedConjugatePicardLimitJoint, intervalDomainLift, x.2] using
    hx.continuousAt (by simp)

end ShenWork.Paper2.BFormPositiveDatumNegPart
