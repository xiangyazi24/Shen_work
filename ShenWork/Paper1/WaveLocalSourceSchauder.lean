/-
  Compact-open Schauder construction for one whole-line paper Green step.

  The source set here contains exactly the data used by local compactness:
  continuity, the weighted right-tail bound, and one spatial Holder modulus.
  In particular it does not impose a family-uniform left-tail rate.  Such a
  rate is neither needed for the fixed-source equation nor preserved by the
  Rothe recursion.
-/
import ShenWork.Paper1.CompactConvexProfileSchauder
import ShenWork.Paper1.WavePaperRotheProducer

open Filter Topology Real Set

noncomputable section

namespace ShenWork.Paper1

theorem PaperLocalHolderSourceBox.zero_mem
    {κ M β B H : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hH : 0 ≤ H) :
    PaperLocalHolderSourceBox κ M β B H (fun _ => 0) := by
  refine
    { cont := continuous_const
      bound := ?_
      holder := ?_ }
  · intro x
    simp only [abs_zero]
    exact mul_nonneg hB (upperBarrier_nonneg hM x)
  · intro x y
    simp only [sub_self, abs_zero]
    exact mul_nonneg hH (Real.rpow_nonneg (abs_nonneg _) β)

theorem PaperLocalHolderSourceBox.set_convex
    (κ M β B H : ℝ) :
    Convex ℝ {R : ℝ → ℝ | PaperLocalHolderSourceBox κ M β B H R} := by
  rw [convex_iff_add_mem]
  intro R hR S hS a b ha hb hab
  refine
    { cont := ?_
      bound := ?_
      holder := ?_ }
  · exact (hR.cont.const_smul a).add (hS.cont.const_smul b)
  · intro x
    have htri : |a * R x + b * S x| ≤ a * |R x| + b * |S x| := by
      calc
        |a * R x + b * S x| ≤ |a * R x| + |b * S x| := abs_add_le _ _
        _ = a * |R x| + b * |S x| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    calc
      |(a • R + b • S) x| = |a * R x + b * S x| := by rfl
      _ ≤ a * |R x| + b * |S x| := htri
      _ ≤ a * (B * upperBarrier κ M x) +
            b * (B * upperBarrier κ M x) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hR.bound x) ha)
          (mul_le_mul_of_nonneg_left (hS.bound x) hb)
      _ = B * upperBarrier κ M x := by rw [← add_mul, hab, one_mul]
  · intro x y
    have hrewrite :
        (a • R + b • S) x - (a • R + b • S) y =
          a * (R x - R y) + b * (S x - S y) := by
      change (a * R x + b * S x) - (a * R y + b * S y) =
        a * (R x - R y) + b * (S x - S y)
      ring
    rw [hrewrite]
    calc
      |a * (R x - R y) + b * (S x - S y)|
          ≤ |a * (R x - R y)| + |b * (S x - S y)| := abs_add_le _ _
      _ = a * |R x - R y| + b * |S x - S y| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * (H * |x - y| ^ β) + b * (H * |x - y| ^ β) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hR.holder x y) ha)
          (mul_le_mul_of_nonneg_left (hS.holder x y) hb)
      _ = H * |x - y| ^ β := by rw [← add_mul, hab, one_mul]

def paperLocalHolderSourceBox_trapData
    {κ M β B H : ℝ}
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hH : 0 ≤ H) :
    BoundedConvexProfileTrapData
      (PaperLocalHolderSourceBox κ M β B H) (B * M) where
  nonempty := ⟨fun _ => 0, PaperLocalHolderSourceBox.zero_mem hM hB hH⟩
  convex := PaperLocalHolderSourceBox.set_convex κ M β B H
  continuous := fun _ hR => hR.cont
  abs_le := fun _ hR => hR.abs_le_const hB

/-- Local Arzela--Ascoli compactness of the no-tail source box. -/
theorem localUniformSequentiallyCompactRange_localHolderSourceBox_of_mapsTo
    {κ M β B H : ℝ}
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hH : 0 ≤ H) (hβ : 0 < β)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ R, PaperLocalHolderSourceBox κ M β B H R →
      PaperLocalHolderSourceBox κ M β B H (Tmap R)) :
    LocalUniformSequentiallyCompactRange
      (PaperLocalHolderSourceBox κ M β B H) Tmap := by
  intro seq hseq
  set gs : ℕ → ℝ → ℝ := fun n => Tmap (seq n) with hgs
  have hbox : ∀ n, PaperLocalHolderSourceBox κ M β B H (gs n) := by
    intro n
    exact hmap (seq n) (hseq n)
  have hgsH : ∀ k, ∀ x y, |gs k x - gs k y| ≤ H * |x - y| ^ β := by
    intro k x y
    exact (hbox k).holder x y
  have hgsB : ∀ k x, |gs k x| ≤ B * M := by
    intro k x
    exact (hbox k).abs_le_const hB x
  obtain ⟨subseq, hsub, g, hpt, hgH⟩ :=
    holder_pointwise_selection (B * M) H β (mul_nonneg hB hM) hH hβ
      gs hgsH hgsB
  have hLU : LocallyUniformConverges (fun n => gs (subseq n)) g :=
    locallyUniform_of_pointwise_of_equiHolder hH hβ hpt
      (fun n => hgsH (subseq n)) hgH
  have hgcont : Continuous g :=
    continuous_of_locallyUniform (fun n => (hbox (subseq n)).cont) hLU
  have hgbound : ∀ x, |g x| ≤ B * upperBarrier κ M x := by
    intro x
    have htend : Tendsto (fun n => |gs (subseq n) x|) atTop (𝓝 (|g x|)) :=
      (hLU.tendsto_at x).abs
    exact le_of_tendsto' htend (fun n => (hbox (subseq n)).bound x)
  refine ⟨subseq, hsub, g, ?_, ?_⟩
  · exact { cont := hgcont, bound := hgbound, holder := hgH }
  · simpa [hgs] using hLU

/-- Local-uniform continuity of the truncated source map on the no-tail box. -/
theorem paperFixedSourceMap_continuousOn_of_localBox
    (p : CMParams) {c lam M κ β B H : ℝ} {u Z : ℝ → ℝ}
    (hlam : 0 < lam) (hB : 0 ≤ B) (hH : 0 ≤ H) (hβ : 0 < β)
    (hmap_holder : ∀ R, PaperLocalHolderSourceBox κ M β B H R →
      ∀ x y,
        |paperFixedSourceMap p c lam M κ u Z R x -
            paperFixedSourceMap p c lam M κ u Z R y| ≤ H * |x - y| ^ β) :
    LocalUniformContinuousOn
      (PaperLocalHolderSourceBox κ M β B H)
      (paperFixedSourceMap p c lam M κ u Z) := by
  intro seq R hseq hR hLU
  apply locallyUniform_of_pointwise_of_equiHolder hH hβ
  · intro x
    exact paperFixedSourceMap_tendsto_of_source_locallyUniform_localSourceBox
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
      (β := β) (B := B) (H := H) (u := u) (Z := Z)
      (Rs := seq) (R := R) hlam hB hseq hR hLU x
  · intro n x y
    exact hmap_holder (seq n) (hseq n) x y
  · intro x y
    exact hmap_holder R hR x y

/-- Generic compact-open Schauder fixed point on a local source box. -/
theorem paperLocalHolderSourceBox_exists_fixed
    {κ M β B H : ℝ}
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hH : 0 ≤ H) (hβ : 0 < β)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ R, PaperLocalHolderSourceBox κ M β B H R →
      PaperLocalHolderSourceBox κ M β B H (Tmap R))
    (hcont : LocalUniformContinuousOn
      (PaperLocalHolderSourceBox κ M β B H) Tmap) :
    ∃ R, PaperLocalHolderSourceBox κ M β B H R ∧ Tmap R = R := by
  let data : BoundedConvexProfileTrapData
      (PaperLocalHolderSourceBox κ M β B H) (B * M) :=
    paperLocalHolderSourceBox_trapData
      (κ := κ) (M := M) (β := β) (B := B) (H := H) hM hB hH
  exact data.exists_fixed hmap hcont
    (localUniformSequentiallyCompactRange_localHolderSourceBox_of_mapsTo
      hM hB hH hβ Tmap hmap)

/-- The whole-line truncated Green source has a genuine compact-open Schauder
fixed point without any frozen-profile or family-uniform left-tail rate. -/
theorem paperFixedSourceMap_exists_fixed_local_of_oldData
    (p : CMParams)
    {c lam M κ B H : ℝ} {u Z : ℝ → ℝ}
    (hlam : 0 < lam)
    (hrpκ : κ < greenRootPlus c lam)
    (hrmκ : κ < -greenRootMinus c lam)
    (hκ : 0 ≤ κ) (hM : 0 < M) (hB : 0 ≤ B)
    (hu : InMonotoneWaveTrapSet κ M u)
    (hZ : PaperFixedSourceOldData κ M Z)
    (hscalar :
      |(-p.χ * p.m)| * M ^ (p.m - 1) * M ^ p.γ *
            greenWeightedMass1 c lam κ * B
        + (1 + |p.χ| * M ^ (p.m - 1) * M ^ p.γ
            + M ^ p.α + |p.χ| * M ^ (p.m + p.γ - 1))
        + lam ≤ B)
    (hHolder :
      Classical.choose
        (paperFixedSourceMap_holder_kernel_of_oldData
          (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (B := B)
          (u := u) (Z := Z)
          hlam hrpκ hrmκ hκ hM hB hu.trap hZ) ≤ H) :
    ∃ R,
      PaperLocalHolderSourceBox κ M (paperWeightedHolderExponent p) B H R ∧
      paperFixedSourceMap p c lam M κ u Z R = R := by
  let holderKernel :=
    paperFixedSourceMap_holder_kernel_of_oldData
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (B := B)
      (u := u) (Z := Z)
      hlam hrpκ hrmκ hκ hM hB hu.trap hZ
  let H0 : ℝ := Classical.choose holderKernel
  have hH0 : 0 ≤ H0 := (Classical.choose_spec holderKernel).1
  have hH : 0 ≤ H := hH0.trans hHolder
  let hmap_cont :
      ∀ R,
        PaperLocalHolderSourceBox κ M (paperWeightedHolderExponent p) B H R →
        Continuous (paperFixedSourceMap p c lam M κ u Z R) := by
    intro R hR
    exact paperFixedSourceMap_continuous_of_localSourceBox
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
      (β := paperWeightedHolderExponent p) (B := B) (H := H)
      (u := u) (Z := Z) (R := R)
      hlam hB hZ.cont
      (frozenElliptic_continuous p hu.trap.cunif_bdd hu.nonneg)
      (frozenElliptic_deriv_continuous p hu.trap.cunif_bdd hu.nonneg) hR
  let hmap_bound :
      ∀ R,
        PaperLocalHolderSourceBox κ M (paperWeightedHolderExponent p) B H R →
        ∀ x, |paperFixedSourceMap p c lam M κ u Z R x| ≤
          B * upperBarrier κ M x := by
    intro R hR
    have hVbound : ∀ x, |frozenElliptic p u x| ≤ M ^ p.γ := by
      intro x
      rw [abs_of_nonneg (frozenElliptic_nonneg_of_inWaveTrapSet p hu.trap x)]
      exact frozenElliptic_le_rpow_of_inWaveTrapSet p hM hu.trap x
    have hVderiv : ∀ x, |deriv (frozenElliptic p u) x| ≤ M ^ p.γ := by
      intro x
      exact (frozenElliptic_deriv_abs_le p hu.trap.cunif_bdd hu.nonneg x).trans
        (frozenElliptic_le_rpow_of_inWaveTrapSet p hM hu.trap x)
    exact paperFixedSourceMap_bound_of_localSourceBox
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
      (β := paperWeightedHolderExponent p) (B := B) (H := H)
      (BV := M ^ p.γ) (BVd := M ^ p.γ)
      (u := u) (Z := Z) (R := R)
      hlam hrpκ hrmκ hκ hM.le hB
      (Real.rpow_nonneg hM.le p.γ) (Real.rpow_nonneg hM.le p.γ)
      hZ.nonneg hZ.le_barrier hVbound hVderiv hscalar hR
  let hmap_holder :
      ∀ R,
        PaperLocalHolderSourceBox κ M (paperWeightedHolderExponent p) B H R →
        ∀ x y,
          |paperFixedSourceMap p c lam M κ u Z R x -
              paperFixedSourceMap p c lam M κ u Z R y| ≤
            H * |x - y| ^ paperWeightedHolderExponent p := by
    intro R hR x y
    have h0 :=
      (Classical.choose_spec holderKernel).2 H (fun _ => 0) R hR x y
    exact h0.trans (mul_le_mul_of_nonneg_right hHolder
      (Real.rpow_nonneg (abs_nonneg _) (paperWeightedHolderExponent p)))
  let hmap :
      ∀ R,
        PaperLocalHolderSourceBox κ M (paperWeightedHolderExponent p) B H R →
        PaperLocalHolderSourceBox κ M (paperWeightedHolderExponent p) B H
          (paperFixedSourceMap p c lam M κ u Z R) := by
    intro R hR
    exact
      { cont := hmap_cont R hR
        bound := hmap_bound R hR
        holder := hmap_holder R hR }
  exact paperLocalHolderSourceBox_exists_fixed
    hM.le hB hH (paperWeightedHolderExponent_pos p)
    (paperFixedSourceMap p c lam M κ u Z) hmap
    (paperFixedSourceMap_continuousOn_of_localBox
      p hlam hB hH (paperWeightedHolderExponent_pos p) hmap_holder)

/-- Backwards-compatible fixed-source existence wrapper for a full Rothe old
iterate. -/
theorem paperFixedSourceMap_exists_fixed_local_of_trap
    (p : CMParams)
    {c lam M κ B H : ℝ} {u Z : ℝ → ℝ}
    (hlam : 0 < lam)
    (hrpκ : κ < greenRootPlus c lam)
    (hrmκ : κ < -greenRootMinus c lam)
    (hκ : 0 ≤ κ) (hM : 0 < M) (hB : 0 ≤ B)
    (hu : InMonotoneWaveTrapSet κ M u)
    (hZ : PaperIterateBase p c κ M u Z)
    (hscalar :
      |(-p.χ * p.m)| * M ^ (p.m - 1) * M ^ p.γ *
            greenWeightedMass1 c lam κ * B
        + (1 + |p.χ| * M ^ (p.m - 1) * M ^ p.γ
            + M ^ p.α + |p.χ| * M ^ (p.m + p.γ - 1))
        + lam ≤ B)
    (hHolder :
      Classical.choose
        (paperFixedSourceMap_holder_kernel
          (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (B := B)
          (u := u) (Z := Z)
          hlam hrpκ hrmκ hκ hM hB hu.trap hZ) ≤ H) :
    ∃ R,
      PaperLocalHolderSourceBox κ M (paperWeightedHolderExponent p) B H R ∧
      paperFixedSourceMap p c lam M κ u Z R = R := by
  let hZold := hZ.toFixedSourceOldData hκ hM.le
  have hkernelEq :
      paperFixedSourceMap_holder_kernel p hlam hrpκ hrmκ hκ hM hB hu.trap hZ =
        paperFixedSourceMap_holder_kernel_of_oldData p hlam hrpκ hrmκ hκ hM hB
          hu.trap hZold := rfl
  apply paperFixedSourceMap_exists_fixed_local_of_oldData
    p hlam hrpκ hrmκ hκ hM hB hu hZold hscalar
  simpa [hkernelEq] using hHolder

section AxiomAudit

#print axioms PaperLocalHolderSourceBox.set_convex
#print axioms localUniformSequentiallyCompactRange_localHolderSourceBox_of_mapsTo
#print axioms paperLocalHolderSourceBox_exists_fixed
#print axioms paperFixedSourceMap_exists_fixed_local_of_oldData
#print axioms paperFixedSourceMap_exists_fixed_local_of_trap

end AxiomAudit

end ShenWork.Paper1
