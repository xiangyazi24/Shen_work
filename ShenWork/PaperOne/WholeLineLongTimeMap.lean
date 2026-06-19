import ShenWork.PaperOne.WholeLineLongTimeLimit
import ShenWork.PaperOne.WholeLineWaveTrap
import ShenWork.PaperOne.WholeLineMildMapContinuity

open Filter Set Topology
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

/-!
Long-time map for the whole-line auxiliary flow.

The analytic inputs which are not part of the order/compactness wiring are kept
as named hypotheses:
* continuity of each long-time profile;
* parabolic equicontinuity of the image family on compact windows;
* fixed-time local-uniform continuity of the mild flow;
* locally uniform convergence of finite-time slices to the long-time limit,
  uniformly over the trap.
-/

/-- The long-time map `T u = U∞(·; u)` associated to an auxiliary orbit `w[u]`. -/
def longTimeMap (w : (ℝ → ℝ) → ℝ → ℝ → ℝ) :
    (ℝ → ℝ) → (ℝ → ℝ) :=
  fun u => wholeLineLongTimeLimit (w u)

/-- Continuity of each long-time profile, supplied by the parabolic limit layer. -/
def LongTimeMapImageContinuity (κ κt D : ℝ)
    (w : (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop :=
  ∀ u, u ∈ WaveTrap κ κt D → Continuous (longTimeMap w u)

/-- The parabolic equicontinuity estimate for images of trapped profiles. -/
def LongTimeMapParabolicEquicontinuity (κ κt D : ℝ)
    (w : (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop :=
  ∀ seq : ℕ → ℝ → ℝ, (∀ n, seq n ∈ WaveTrap κ κt D) →
    ∀ K : Set ℝ, IsCompact K →
      EquicontinuousOn (fun n x => longTimeMap w (seq n) x) K

/-- Fixed-time local-uniform continuity of the auxiliary mild flow. -/
def LongTimeMapFiniteTimeContinuity (κ κt D : ℝ)
    (w : (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop :=
  ∀ t : ℝ,
    ShenWork.Paper1.LocalUniformContinuousOn
      (fun u => u ∈ WaveTrap κ κt D) (fun u => w u t)

/-- Uniform local convergence of finite-time slices to the long-time profile. -/
def LongTimeMapUniformTail (κ κt D : ℝ)
    (w : (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop :=
  ∀ R > 0, ∀ ε > 0, ∃ τ : ℝ,
    ∀ u, u ∈ WaveTrap κ κt D →
      ∀ x : ℝ, x ∈ Icc (-R) R →
        |w u τ x - longTimeMap w u x| < ε

/-- Barrier bounds and spatial antitonicity pass from the orbit to the long-time map. -/
theorem longTimeMap_mapsTo
    {κ κt D : ℝ} {w : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    (hlower : ∀ u, u ∈ WaveTrap κ κt D →
      ∀ t x, lowerBarrier κ κt D x ≤ w u t x)
    (hupper : ∀ u, u ∈ WaveTrap κ κt D →
      ∀ t x, w u t x ≤ upperBarrier κ x)
    (hspace : ∀ u, u ∈ WaveTrap κ κt D → ∀ t, Antitone (w u t)) :
    ∀ u, u ∈ WaveTrap κ κt D →
      longTimeMap w u ∈ WaveTrap κ κt D := by
  intro u hu
  constructor
  · simpa [longTimeMap] using
      wholeLine_longTime_limit_barrier_bounds
        (κ := κ) (κt := κt) (D := D) (w := w u)
        (hlower u hu) (hupper u hu)
  · simpa [longTimeMap] using
      wholeLine_longTime_limit_antitone
        (κ := κ) (κt := κt) (D := D) (w := w u)
        (hlower u hu) (hspace u hu)

/--
The same maps-to statement in the older Paper 1 monotone wave-trap interface
with height `1`.
-/
theorem longTimeMap_mapsTo_InMonotoneWaveTrapSet
    {κ κt D : ℝ} {w : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    (hlower : ∀ u, u ∈ WaveTrap κ κt D →
      ∀ t x, lowerBarrier κ κt D x ≤ w u t x)
    (hupper : ∀ u, u ∈ WaveTrap κ κt D →
      ∀ t x, w u t x ≤ upperBarrier κ x)
    (hspace : ∀ u, u ∈ WaveTrap κ κt D → ∀ t, Antitone (w u t))
    (hcont : LongTimeMapImageContinuity κ κt D w) :
    ∀ u, u ∈ WaveTrap κ κt D →
      ShenWork.Paper1.InMonotoneWaveTrapSet κ 1 (longTimeMap w u) := by
  intro u hu
  simpa [longTimeMap] using
    wholeLine_longTime_limit_mem_InMonotoneWaveTrapSet
      (κ := κ) (κt := κt) (D := D) (w := w u)
      (hlower u hu) (hupper u hu) (hspace u hu)
      (by simpa [longTimeMap] using hcont u hu)

/-- The image family satisfies the Ascoli hypotheses once the parabolic
equicontinuity estimate is supplied. -/
theorem longTimeMap_locallyUniformlyBoundedEquicont
    {κ κt D : ℝ} {w : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    (hmap : ∀ u, u ∈ WaveTrap κ κt D →
      longTimeMap w u ∈ WaveTrap κ κt D)
    (hcont : LongTimeMapImageContinuity κ κt D w)
    (hequi : LongTimeMapParabolicEquicontinuity κ κt D w)
    (seq : ℕ → ℝ → ℝ) (hseq : ∀ n, seq n ∈ WaveTrap κ κt D) :
    LocallyUniformlyBoundedEquicont (fun n => longTimeMap w (seq n)) where
  continuous := fun n => hcont (seq n) (hseq n)
  locally_bounded := by
    intro _K _hK
    refine ⟨1, ?_⟩
    intro n x _hx
    have hT : longTimeMap w (seq n) ∈ WaveTrap κ κt D :=
      hmap (seq n) (hseq n)
    constructor
    · exact le_trans (by norm_num : (-1 : ℝ) ≤ 0) (waveTrap_mem_nonneg hT x)
    · exact waveTrap_mem_le_one hT x
  equicontinuous_on_compacts := hequi seq hseq

/-- Compactness of the long-time map image in the local-uniform topology. -/
theorem longTimeMap_compact
    {κ κt D : ℝ} {w : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    (hmap : ∀ u, u ∈ WaveTrap κ κt D →
      longTimeMap w u ∈ WaveTrap κ κt D)
    (hcont : LongTimeMapImageContinuity κ κt D w)
    (hequi : LongTimeMapParabolicEquicontinuity κ κt D w) :
    ShenWork.Paper1.LocalUniformSequentiallyCompactRange
      (fun u => u ∈ WaveTrap κ κt D) (longTimeMap w) := by
  refine ShenWork.Paper1.localUniformSequentiallyCompactRange_of_layer4 ?_ ?_
  · intro seq hseq
    exact longTimeMap_locallyUniformlyBoundedEquicont hmap hcont hequi seq hseq
  · intro seq subseq f hseq _hsubseq hlim
    exact
      waveTrap_closed_locUnif
        (κ := κ) (κt := κt) (D := D)
        (u := fun n => longTimeMap w (seq (subseq n)))
        (f := f)
        (fun n => hmap (seq (subseq n)) (hseq (subseq n)))
        hlim

/-- Fixed-time continuity from the mild-map decomposition and the two Duhamel
term continuity inputs. -/
theorem longTimeMap_finiteTimeContinuity_of_mild_decomp
    {κ κt D χ : ℝ} {w : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {semigroupTerm : ℝ → ℝ → ℝ}
    {chemDuhamel reactionDuhamel : ℝ → (ℝ → ℝ) → ℝ → ℝ}
    (hdecomp : ∀ t U x, w U t x =
      semigroupTerm t x + (-χ) * chemDuhamel t U x +
        reactionDuhamel t U x)
    (hchem : ∀ t,
      ShenWork.Paper1.LocalUniformContinuousOn
        (fun u => u ∈ WaveTrap κ κt D) (chemDuhamel t))
    (hreaction : ∀ t,
      ShenWork.Paper1.LocalUniformContinuousOn
        (fun u => u ∈ WaveTrap κ κt D) (reactionDuhamel t)) :
    LongTimeMapFiniteTimeContinuity κ κt D w := by
  intro t
  exact
    ShenWork.Paper1.wholeLineMildMap_continuous_in_U
      (trap := fun u => u ∈ WaveTrap κ κt D)
      (χ := χ)
      (wholeLineMildMap := fun U x => w U t x)
      (semigroupTerm := semigroupTerm t)
      (chemDuhamel := chemDuhamel t)
      (logisticDuhamel := reactionDuhamel t)
      (hdecomp t) (hchem t) (hreaction t)

/-- Continuity of the long-time map from fixed-time mild continuity and uniform
local convergence of the finite-time slices to the long-time limit. -/
theorem longTimeMap_continuous
    {κ κt D : ℝ} {w : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    (hfinite : LongTimeMapFiniteTimeContinuity κ κt D w)
    (htail : LongTimeMapUniformTail κ κt D w) :
    ShenWork.Paper1.LocalUniformContinuousOn
      (fun u => u ∈ WaveTrap κ κt D) (longTimeMap w) := by
  intro seq u hseq hu hconv R hR ε hε
  have hε3 : 0 < ε / 3 := by linarith
  rcases htail R hR (ε / 3) hε3 with ⟨τ, hτ⟩
  have hτcont := hfinite τ seq u hseq hu hconv
  filter_upwards [hτcont R hR (ε / 3) hε3] with n hn
  intro x hx
  have hleft :
      |longTimeMap w (seq n) x - w (seq n) τ x| < ε / 3 := by
    simpa [abs_sub_comm] using hτ (seq n) (hseq n) x hx
  have hmid : |w (seq n) τ x - w u τ x| < ε / 3 :=
    hn x hx
  have hright : |w u τ x - longTimeMap w u x| < ε / 3 :=
    hτ u hu x hx
  have htri :
      |longTimeMap w (seq n) x - longTimeMap w u x| ≤
        |longTimeMap w (seq n) x - w (seq n) τ x| +
          (|w (seq n) τ x - w u τ x| +
            |w u τ x - longTimeMap w u x|) := by
    calc
      |longTimeMap w (seq n) x - longTimeMap w u x|
          =
            |(longTimeMap w (seq n) x - w (seq n) τ x) +
              ((w (seq n) τ x - w u τ x) +
                (w u τ x - longTimeMap w u x))| := by
              ring_nf
      _ ≤
          |longTimeMap w (seq n) x - w (seq n) τ x| +
            |(w (seq n) τ x - w u τ x) +
              (w u τ x - longTimeMap w u x)| :=
          abs_add_le _ _
      _ ≤
          |longTimeMap w (seq n) x - w (seq n) τ x| +
            (|w (seq n) τ x - w u τ x| +
              |w u τ x - longTimeMap w u x|) :=
          add_le_add le_rfl (abs_add_le _ _)
  exact lt_of_le_of_lt htri (by nlinarith [hleft, hmid, hright])

#print axioms longTimeMap
#print axioms LongTimeMapImageContinuity
#print axioms LongTimeMapParabolicEquicontinuity
#print axioms LongTimeMapFiniteTimeContinuity
#print axioms LongTimeMapUniformTail
#print axioms longTimeMap_mapsTo
#print axioms longTimeMap_mapsTo_InMonotoneWaveTrapSet
#print axioms longTimeMap_locallyUniformlyBoundedEquicont
#print axioms longTimeMap_compact
#print axioms longTimeMap_finiteTimeContinuity_of_mild_decomp
#print axioms longTimeMap_continuous

end ShenWork.PaperOne
