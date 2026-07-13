import ShenWork.Paper1.WaveUniformModulusTrap
import ShenWork.Paper1.WaveLemma42Paper
import ShenWork.Paper1.CompactConvexProfileSchauder

open Filter Set Topology

noncomputable section

namespace ShenWork.Paper1

/-- The compact parameter trap actually needed by the weighted whole-line
Green construction.  Besides the paper order bounds and lower pin, profiles
share both a spatial modulus and a quantitative left-tail modulus.  The left
limit itself may vary in `[0,M]`, which keeps the set convex and matches the
paper's pre-fixed-point parameter class. -/
structure InControlledLowerPinnedMonotoneTrap
    (κ M L sigma aL C : ℝ) (φ u : ℝ → ℝ) : Prop where
  uniformTrap : InUniformModulusMonotoneWaveTrap κ M L u
  lower : ∀ x, φ x ≤ u x
  leftRateData : ∃ ell : ℝ,
    ell ∈ Icc (0 : ℝ) M ∧ ExpLeftRate sigma aL C u ell

namespace InControlledLowerPinnedMonotoneTrap

variable {κ M L sigma aL C : ℝ} {φ u : ℝ → ℝ}

theorem bare
    (h : InControlledLowerPinnedMonotoneTrap κ M L sigma aL C φ u) :
    InMonotoneWaveTrapSet κ M u :=
  h.uniformTrap.bare

theorem modulus
    (h : InControlledLowerPinnedMonotoneTrap κ M L sigma aL C φ u) :
    ∀ x y, |u x - u y| ≤ L * |x - y| :=
  h.uniformTrap.modulus

theorem set_convex (κ M L sigma aL C : ℝ) (φ : ℝ → ℝ) :
    Convex ℝ
      {u : ℝ → ℝ |
        InControlledLowerPinnedMonotoneTrap κ M L sigma aL C φ u} := by
  rw [convex_iff_add_mem]
  intro u hu v hv a b ha hb hab
  rcases hu.leftRateData with ⟨ellu, hellu_mem, hu_rate⟩
  rcases hv.leftRateData with ⟨ellv, hellv_mem, hv_rate⟩
  let ell : ℝ := a * ellu + b * ellv
  refine
    { uniformTrap :=
        InUniformModulusMonotoneWaveTrap.set_convex κ M L
          hu.uniformTrap hv.uniformTrap ha hb hab
      lower := ?_
      leftRateData := ⟨ell, ?_, ?_⟩ }
  · intro x
    change φ x ≤ a * u x + b * v x
    calc
      φ x = (a + b) * φ x := by rw [hab, one_mul]
      _ = a * φ x + b * φ x := by ring
      _ ≤ a * u x + b * v x :=
        add_le_add
          (mul_le_mul_of_nonneg_left
            (InControlledLowerPinnedMonotoneTrap.lower hu x) ha)
          (mul_le_mul_of_nonneg_left
            (InControlledLowerPinnedMonotoneTrap.lower hv x) hb)
  · constructor
    · dsimp [ell]
      exact add_nonneg
        (mul_nonneg ha hellu_mem.1)
        (mul_nonneg hb hellv_mem.1)
    · dsimp [ell]
      calc
        a * ellu + b * ellv ≤ a * M + b * M :=
          add_le_add
            (mul_le_mul_of_nonneg_left hellu_mem.2 ha)
            (mul_le_mul_of_nonneg_left hellv_mem.2 hb)
        _ = M := by rw [← add_mul, hab, one_mul]
  · intro x
    change
      |(a * u x + b * v x) - ell| ≤
        C * Real.exp (sigma * (x - aL))
    have hu_rate_x := hu_rate x
    have hv_rate_x := hv_rate x
    calc
      |(a * u x + b * v x) - ell|
          = |a * (u x - ellu) +
              b * (v x - ellv)| := by
                dsimp [ell]
                ring_nf
      _ ≤ |a * (u x - ellu)| +
          |b * (v x - ellv)| := abs_add_le _ _
      _ = a * |u x - ellu| +
          b * |v x - ellv| := by
            rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * (C * Real.exp (sigma * (x - aL))) +
          b * (C * Real.exp (sigma * (x - aL))) :=
            add_le_add
              (mul_le_mul_of_nonneg_left hu_rate_x ha)
              (mul_le_mul_of_nonneg_left hv_rate_x hb)
      _ = C * Real.exp (sigma * (x - aL)) := by
            rw [← add_mul, hab, one_mul]

/-- The controlled trap is sequentially compact for local-uniform convergence.
The spatial modulus gives Arzelà--Ascoli on compact windows; compactness of the
left-limit interval and the shared exponential estimate keep the quantitative
left tail in the limit. -/
theorem locallyUniform_sequentiallyCompact
    (hM : 0 ≤ M) (hL : 0 ≤ L) :
    LocalUniformSequentiallyCompactRange
      (InControlledLowerPinnedMonotoneTrap κ M L sigma aL C φ)
      (fun u => u) := by
  intro seq hseq
  let baseSeq : ℕ → ℝ → ℝ := seq
  have hbase : ∀ n,
      InLowerPinnedUniformModulusMonotoneTrap κ M L φ (baseSeq n) := by
    intro n
    exact ⟨(hseq n).uniformTrap, (hseq n).lower⟩
  obtain ⟨sub₁, hsub₁, g, hgbase, hconv₁⟩ :=
    InLowerPinnedUniformModulusMonotoneTrap.locallyUniform_sequentiallyCompact
      (κ := κ) (M := M) (L := L) (φ := φ) hM hL baseSeq hbase
  let ells : ℕ → ℝ := fun n =>
    Classical.choose (hseq (sub₁ n)).leftRateData
  have hells_mem : ∀ n, ells n ∈ Icc (0 : ℝ) M :=
    fun n => (Classical.choose_spec (hseq (sub₁ n)).leftRateData).1
  obtain ⟨ell, hell_mem, sub₂, hsub₂, hell_conv⟩ :=
    isCompact_Icc.tendsto_subseq hells_mem
  let sub : ℕ → ℕ := fun n => sub₁ (sub₂ n)
  have hsub : StrictMono sub := hsub₁.comp hsub₂
  have hconv : LocallyUniformConverges (fun n => seq (sub n)) g := by
    simpa [sub, baseSeq] using hconv₁.comp_strictMono hsub₂
  have hrate : ExpLeftRate sigma aL C g ell := by
    intro x
    have htend :
        Tendsto
          (fun n => |seq (sub n) x - ells (sub₂ n)|)
          atTop (𝓝 (|g x - ell|)) := by
      exact (hconv.tendsto_at x).sub hell_conv |>.abs
    refine le_of_tendsto htend ?_
    filter_upwards with n
    simpa [sub, ells] using
      (Classical.choose_spec (hseq (sub n)).leftRateData).2 x
  refine
    ⟨sub, hsub, g,
      { uniformTrap := hgbase.uniformTrap
        lower := hgbase.lower
        leftRateData := ⟨ell, hell_mem, hrate⟩ },
      hconv⟩

/-- Concrete non-vacuity of the corrected trap.  Whenever the lower pin lies
below the paper upper barrier, that upper barrier itself belongs to a
controlled trap for explicit spatial modulus `κ*M` and for the exponential
left-rate constants already constructed by the Green/Rothe infrastructure. -/
theorem exists_controls_upper_mem
    {κ M : ℝ} {φ : ℝ → ℝ}
    (hκ : 0 < κ) (hM : 0 < M)
    (hφ : ∀ x, φ x ≤ upperBarrier κ M x) :
    ∃ sigma aL C ell : ℝ,
      0 < sigma ∧ ell ∈ Icc (0 : ℝ) M ∧
      InControlledLowerPinnedMonotoneTrap
        κ M (κ * M) sigma aL C φ (upperBarrier κ M) := by
  rcases upperBarrier_expLeftRateData hκ.le hM.le with
    ⟨sigma, aL, C, ell, hsigma, hrate⟩
  have hell : ell ∈ Icc (0 : ℝ) M :=
    ExpLeftRate.limit_mem_Icc hsigma hrate
      (fun x => upperBarrier_nonneg hM.le x)
      (fun x => upperBarrier_le_M κ M x)
  refine ⟨sigma, aL, C, ell, hsigma, hell, ?_⟩
  exact
    { uniformTrap :=
        { bare := upperBarrier_mem_InMonotoneWaveTrapSet hκ.le hM.le
          modulus :=
            PaperLemma42ExactConditions.upperBarrier_abs_sub_le_mul hκ.le hM }
      lower := hφ
      leftRateData := ⟨ell, hell, hrate⟩ }

/-- The controlled parameter trap satisfies the exact hypotheses of the
compact-open Schauder--Tychonoff construction. -/
theorem boundedConvexProfileTrapData
    (hne : ∃ u,
      InControlledLowerPinnedMonotoneTrap κ M L sigma aL C φ u) :
    BoundedConvexProfileTrapData
      (InControlledLowerPinnedMonotoneTrap κ M L sigma aL C φ) M := by
  refine
    { nonempty := hne
      convex := set_convex κ M L sigma aL C φ
      continuous := ?_
      abs_le := ?_ }
  · intro u hu
    exact hu.bare.trap.cunif_bdd.1
  · intro u hu x
    rw [abs_of_nonneg (hu.bare.nonneg x)]
    exact hu.bare.le_M x

/-- Schauder--Tychonoff on the corrected compact convex parameter trap, with
no finite-cube approximation package left as a hypothesis. -/
theorem schauderPrinciple
    (hne : ∃ u,
      InControlledLowerPinnedMonotoneTrap κ M L sigma aL C φ u) :
    LocalUniformSchauderFixedPointPrinciple
      (InControlledLowerPinnedMonotoneTrap κ M L sigma aL C φ) :=
  (boundedConvexProfileTrapData hne).schauderPrinciple

end InControlledLowerPinnedMonotoneTrap

section AxiomAudit

#print axioms InControlledLowerPinnedMonotoneTrap.set_convex
#print axioms InControlledLowerPinnedMonotoneTrap.locallyUniform_sequentiallyCompact
#print axioms InControlledLowerPinnedMonotoneTrap.exists_controls_upper_mem
#print axioms InControlledLowerPinnedMonotoneTrap.boundedConvexProfileTrapData
#print axioms InControlledLowerPinnedMonotoneTrap.schauderPrinciple

end AxiomAudit

end ShenWork.Paper1
