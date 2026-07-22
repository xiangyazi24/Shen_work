import ShenWork.Paper1.WholeLineChiPosSpaceTimeArzelaAscoli
import ShenWork.Paper1.WholeLineChiPosEntropyClassicalCertification

/-!
# Classical normal-family characterization of far-left entropy compactness

This file changes the compactness target from a weighted entropy package to a
bounded entire classical limit.  The preceding certification theorem then
supplies all weighted analytic fields automatically.
-/

open Filter Real Set Topology

noncomputable section

namespace ShenWork.Paper1

namespace SpaceTimeLocallyUniformConverges

theorem spatial_slice
    {seq : ℕ → ℝ → ℝ → ℝ} {limit : ℝ → ℝ → ℝ}
    (h : SpaceTimeLocallyUniformConverges seq limit) (t : ℝ) :
    LocallyUniformConverges (fun n x => seq n t x) (limit t) := by
  intro R hR ε hε
  let S : ℝ := max R |t| + 1
  have hS : 0 < S := by
    dsimp only [S]
    linarith [le_max_left R |t|]
  have htS : t ∈ Set.Icc (-S) S := by
    apply abs_le.mp
    dsimp only [S]
    exact le_trans (le_max_right R |t|) (le_add_of_nonneg_right zero_le_one)
  filter_upwards [h S hS ε hε] with n hn
  intro x hx
  have hxS : x ∈ Set.Icc (-S) S := by
    constructor <;> dsimp only [S] <;> linarith [hx.1, hx.2, le_max_left R |t|]
  exact hn t htS x hxS

theorem temporal_slice
    {seq : ℕ → ℝ → ℝ → ℝ} {limit : ℝ → ℝ → ℝ}
    (h : SpaceTimeLocallyUniformConverges seq limit) (x : ℝ) :
    LocallyUniformConverges (fun n t => seq n t x) (fun t => limit t x) := by
  intro R hR ε hε
  let S : ℝ := max R |x| + 1
  have hS : 0 < S := by
    dsimp only [S]
    linarith [le_max_left R |x|]
  have hxS : x ∈ Set.Icc (-S) S := by
    apply abs_le.mp
    dsimp only [S]
    exact le_trans (le_max_right R |x|) (le_add_of_nonneg_right zero_le_one)
  filter_upwards [h S hS ε hε] with n hn
  intro t ht
  have htS : t ∈ Set.Icc (-S) S := by
    constructor <;> dsimp only [S] <;> linarith [ht.1, ht.2, le_max_left R |x|]
  exact hn t htS x hxS

theorem continuous_spatial_limit
    {seq : ℕ → ℝ → ℝ → ℝ} {limit : ℝ → ℝ → ℝ}
    (h : SpaceTimeLocallyUniformConverges seq limit)
    (hcont : ∀ n t, Continuous (seq n t)) :
    ∀ t, Continuous (limit t) := by
  intro t
  exact continuous_of_locallyUniform (fun n => hcont n t) (h.spatial_slice t)

theorem abs_le_of_eventually_box_abs_le
    {seq : ℕ → ℝ → ℝ → ℝ} {limit : ℝ → ℝ → ℝ} {C : ℝ}
    (h : SpaceTimeLocallyUniformConverges seq limit)
    (hbound : ∀ R > 0, ∀ᶠ n in atTop,
      ∀ t ∈ Set.Icc (-R) R, ∀ x ∈ Set.Icc (-R) R, |seq n t x| ≤ C) :
    ∀ t x, |limit t x| ≤ C := by
  intro t x
  let R : ℝ := max |t| |x| + 1
  have hR : 0 < R := by
    dsimp only [R]
    linarith [abs_nonneg t, le_max_left |t| |x|]
  have htR : t ∈ Set.Icc (-R) R := by
    apply abs_le.mp
    dsimp only [R]
    exact le_trans (le_max_left |t| |x|) (le_add_of_nonneg_right zero_le_one)
  have hxR : x ∈ Set.Icc (-R) R := by
    apply abs_le.mp
    dsimp only [R]
    exact le_trans (le_max_right |t| |x|) (le_add_of_nonneg_right zero_le_one)
  have hev : ∀ᶠ n in atTop, |seq n t x| ≤ C :=
    (hbound R hR).mono fun n hn => hn t htR x hxR
  exact le_of_tendsto (h.tendsto_at t x).abs hev

theorem lower_of_eventually_box_lower
    {seq : ℕ → ℝ → ℝ → ℝ} {limit : ℝ → ℝ → ℝ} {ell : ℝ}
    (h : SpaceTimeLocallyUniformConverges seq limit)
    (hfloor : ∀ R > 0, ∀ᶠ n in atTop,
      ∀ t ∈ Set.Icc (-R) R, ∀ x ∈ Set.Icc (-R) R, ell ≤ seq n t x) :
    ∀ t x, ell ≤ limit t x := by
  intro t x
  let R : ℝ := max |t| |x| + 1
  have hR : 0 < R := by
    dsimp only [R]
    linarith [abs_nonneg t, le_max_left |t| |x|]
  have htR : t ∈ Set.Icc (-R) R := by
    apply abs_le.mp
    dsimp only [R]
    exact le_trans (le_max_left |t| |x|) (le_add_of_nonneg_right zero_le_one)
  have hxR : x ∈ Set.Icc (-R) R := by
    apply abs_le.mp
    dsimp only [R]
    exact le_trans (le_max_right |t| |x|) (le_add_of_nonneg_right zero_le_one)
  have hev : ∀ᶠ n in atTop, ell ≤ seq n t x :=
    (hfloor R hR).mono fun n hn => hn t htR x hxR
  exact le_of_tendsto_of_tendsto tendsto_const_nhds (h.tendsto_at t x) hev

end SpaceTimeLocallyUniformConverges

/-- Local uniform convergence of a function and its spatial derivative
preserves the derivative identity. -/
theorem hasDerivAt_spatial_limit
    {f fx : ℕ → ℝ → ℝ → ℝ} {g gx : ℝ → ℝ → ℝ}
    (hf : SpaceTimeLocallyUniformConverges f g)
    (hfx : SpaceTimeLocallyUniformConverges fx gx)
    (hderiv : ∀ n t x, HasDerivAt (f n t) (fx n t x) x) :
    ∀ t x, HasDerivAt (g t) (gx t x) x := by
  intro t x
  apply hasDerivAt_of_tendstoLocallyUniformlyOn
    (l := atTop) (s := (Set.univ : Set ℝ)) isOpen_univ
    (hfx.spatial_slice t).tendstoLocallyUniformlyOn_univ
    (Eventually.of_forall fun n y _hy => hderiv n t y)
    (fun y _hy => (hf.spatial_slice t).tendsto_at y)
    (Set.mem_univ x)

/-- The analogous closedness result for the time derivative. -/
theorem hasDerivAt_temporal_limit
    {f ft : ℕ → ℝ → ℝ → ℝ} {g gt : ℝ → ℝ → ℝ}
    (hf : SpaceTimeLocallyUniformConverges f g)
    (hft : SpaceTimeLocallyUniformConverges ft gt)
    (hderiv : ∀ n t x, HasDerivAt (fun s => f n s x) (ft n t x) t) :
    ∀ t x, HasDerivAt (fun s => g s x) (gt t x) t := by
  intro t x
  apply hasDerivAt_of_tendstoLocallyUniformlyOn
    (l := atTop) (s := (Set.univ : Set ℝ)) isOpen_univ
    (hft.temporal_slice x).tendstoLocallyUniformlyOn_univ
    (Eventually.of_forall fun n s _hs => hderiv n s x)
    (fun s _hs => (hf.temporal_slice x).tendsto_at s)
    (Set.mem_univ t)

/-- The normalized co-moving population equation is closed under pointwise
(hence local-uniform) convergence of all seven fields. -/
theorem chiOne_population_pde_of_locallyUniform
    {chi c : ℝ}
    {u ux uxx ut r rx rxx : ℕ → ℝ → ℝ → ℝ}
    {U Ux Uxx Ut R Rx Rxx : ℝ → ℝ → ℝ}
    (hu : SpaceTimeLocallyUniformConverges u U)
    (hux : SpaceTimeLocallyUniformConverges ux Ux)
    (huxx : SpaceTimeLocallyUniformConverges uxx Uxx)
    (hut : SpaceTimeLocallyUniformConverges ut Ut)
    (_hr : SpaceTimeLocallyUniformConverges r R)
    (hrx : SpaceTimeLocallyUniformConverges rx Rx)
    (hrxx : SpaceTimeLocallyUniformConverges rxx Rxx)
    (hpde : ∀ n t x,
      ut n t x = uxx n t x + c * ux n t x -
        chi * (ux n t x * rx n t x + u n t x * rxx n t x) +
          u n t x * (1 - u n t x)) :
    ∀ t x, Ut t x = Uxx t x + c * Ux t x -
      chi * (Ux t x * Rx t x + U t x * Rxx t x) +
        U t x * (1 - U t x) := by
  intro t x
  have hU := hu.tendsto_at t x
  have hUx := hux.tendsto_at t x
  have hUxx := huxx.tendsto_at t x
  have hUt := hut.tendsto_at t x
  have hRx := hrx.tendsto_at t x
  have hRxx := hrxx.tendsto_at t x
  have hc : Tendsto (fun _n : ℕ => c) atTop (𝓝 c) := tendsto_const_nhds
  have hchiConst : Tendsto (fun _n : ℕ => chi) atTop (𝓝 chi) :=
    tendsto_const_nhds
  have hone : Tendsto (fun _n : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hrhs : Tendsto
      (fun n => uxx n t x + c * ux n t x -
        chi * (ux n t x * rx n t x + u n t x * rxx n t x) +
          u n t x * (1 - u n t x)) atTop
      (𝓝 (Uxx t x + c * Ux t x -
        chi * (Ux t x * Rx t x + U t x * Rxx t x) +
          U t x * (1 - U t x))) :=
    (hUxx.add (hc.mul hUx)).sub
      (hchiConst.mul ((hUx.mul hRx).add (hU.mul hRxx))) |>.add
        (hU.mul (hone.sub hU))
  have hfun : (fun n => ut n t x) = fun n =>
      uxx n t x + c * ux n t x -
        chi * (ux n t x * rx n t x + u n t x * rxx n t x) +
          u n t x * (1 - u n t x) := by
    funext n
    exact hpde n t x
  rw [hfun] at hUt
  exact tendsto_nhds_unique hUt hrhs

theorem chiOne_resolver_of_locallyUniform
    {u r rxx : ℕ → ℝ → ℝ → ℝ}
    {U R Rxx : ℝ → ℝ → ℝ}
    (hu : SpaceTimeLocallyUniformConverges u U)
    (hr : SpaceTimeLocallyUniformConverges r R)
    (hrxx : SpaceTimeLocallyUniformConverges rxx Rxx)
    (hresolver : ∀ n t x, -rxx n t x + r n t x = u n t x - 1) :
    ∀ t x, -Rxx t x + R t x = U t x - 1 := by
  intro t x
  have hleft := (hrxx.tendsto_at t x).neg.add (hr.tendsto_at t x)
  have hone : Tendsto (fun _n : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hright : Tendsto (fun n => u n t x - 1) atTop (𝓝 (U t x - 1)) :=
    (hu.tendsto_at t x).sub hone
  have hfun : (fun n => -rxx n t x + r n t x) =
      fun n => u n t x - 1 := by
    funext n
    exact hresolver n t x
  rw [hfun] at hleft
  exact tendsto_nhds_unique hleft hright

/-- The two hypotheses discharged by the space-time Arzelà--Ascoli theorem. -/
structure SpaceTimeLocallyPrecompact
    (seq : ℕ → ℝ → ℝ → ℝ) : Prop where
  equibounded : SpaceTimeLocallyEquibounded seq
  equicontinuous : SpaceTimeLocallyEquicontinuous seq

/-- Seven scalar fields admit one common locally-uniformly convergent
subsequence.  This is the diagonal needed for `u,uₓ,uₓₓ,uₜ,r,rₓ,rₓₓ`. -/
theorem exists_sevenField_spaceTimeLocallyUniform_subsequence
    (f₁ f₂ f₃ f₄ f₅ f₆ f₇ : ℕ → ℝ → ℝ → ℝ)
    (h₁ : SpaceTimeLocallyPrecompact f₁)
    (h₂ : SpaceTimeLocallyPrecompact f₂)
    (h₃ : SpaceTimeLocallyPrecompact f₃)
    (h₄ : SpaceTimeLocallyPrecompact f₄)
    (h₅ : SpaceTimeLocallyPrecompact f₅)
    (h₆ : SpaceTimeLocallyPrecompact f₆)
    (h₇ : SpaceTimeLocallyPrecompact f₇) :
    ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
      ∃ (g₁ g₂ g₃ g₄ g₅ g₆ g₇ : ℝ → ℝ → ℝ),
        SpaceTimeLocallyUniformConverges (fun n => f₁ (subseq n)) g₁ ∧
        SpaceTimeLocallyUniformConverges (fun n => f₂ (subseq n)) g₂ ∧
        SpaceTimeLocallyUniformConverges (fun n => f₃ (subseq n)) g₃ ∧
        SpaceTimeLocallyUniformConverges (fun n => f₄ (subseq n)) g₄ ∧
        SpaceTimeLocallyUniformConverges (fun n => f₅ (subseq n)) g₅ ∧
        SpaceTimeLocallyUniformConverges (fun n => f₆ (subseq n)) g₆ ∧
        SpaceTimeLocallyUniformConverges (fun n => f₇ (subseq n)) g₇ := by
  obtain ⟨s₁, hs₁, g₁, hg₁⟩ :=
    exists_spaceTimeLocallyUniform_subsequence f₁ h₁.equibounded h₁.equicontinuous
  obtain ⟨s₂, hs₂, g₂, hg₂⟩ := exists_spaceTimeLocallyUniform_subsequence
    (fun n => f₂ (s₁ n)) (h₂.equibounded.comp_strictMono hs₁)
      (h₂.equicontinuous.comp_strictMono hs₁)
  let s₁₂ := s₁ ∘ s₂
  have hs₁₂ : StrictMono s₁₂ := hs₁.comp hs₂
  have hg₁₁₂ : SpaceTimeLocallyUniformConverges (fun n => f₁ (s₁₂ n)) g₁ := by
    simpa only [s₁₂, Function.comp_apply] using hg₁.comp_strictMono hs₂
  have hg₂₁₂ : SpaceTimeLocallyUniformConverges (fun n => f₂ (s₁₂ n)) g₂ := by
    simpa only [s₁₂, Function.comp_apply] using hg₂
  obtain ⟨s₃, hs₃, g₃, hg₃⟩ := exists_spaceTimeLocallyUniform_subsequence
    (fun n => f₃ (s₁₂ n)) (h₃.equibounded.comp_strictMono hs₁₂)
      (h₃.equicontinuous.comp_strictMono hs₁₂)
  let s₁₂₃ := s₁₂ ∘ s₃
  have hs₁₂₃ : StrictMono s₁₂₃ := hs₁₂.comp hs₃
  have hg₁₁₂₃ : SpaceTimeLocallyUniformConverges (fun n => f₁ (s₁₂₃ n)) g₁ := by
    simpa only [s₁₂₃, Function.comp_apply] using hg₁₁₂.comp_strictMono hs₃
  have hg₂₁₂₃ : SpaceTimeLocallyUniformConverges (fun n => f₂ (s₁₂₃ n)) g₂ := by
    simpa only [s₁₂₃, Function.comp_apply] using hg₂₁₂.comp_strictMono hs₃
  have hg₃₁₂₃ : SpaceTimeLocallyUniformConverges (fun n => f₃ (s₁₂₃ n)) g₃ := by
    simpa only [s₁₂₃, Function.comp_apply] using hg₃
  obtain ⟨s₄, hs₄, g₄, hg₄⟩ := exists_spaceTimeLocallyUniform_subsequence
    (fun n => f₄ (s₁₂₃ n)) (h₄.equibounded.comp_strictMono hs₁₂₃)
      (h₄.equicontinuous.comp_strictMono hs₁₂₃)
  let s₁₂₃₄ := s₁₂₃ ∘ s₄
  have hs₁₂₃₄ : StrictMono s₁₂₃₄ := hs₁₂₃.comp hs₄
  have hg₁₁₂₃₄ : SpaceTimeLocallyUniformConverges (fun n => f₁ (s₁₂₃₄ n)) g₁ := by
    simpa only [s₁₂₃₄, Function.comp_apply] using hg₁₁₂₃.comp_strictMono hs₄
  have hg₂₁₂₃₄ : SpaceTimeLocallyUniformConverges (fun n => f₂ (s₁₂₃₄ n)) g₂ := by
    simpa only [s₁₂₃₄, Function.comp_apply] using hg₂₁₂₃.comp_strictMono hs₄
  have hg₃₁₂₃₄ : SpaceTimeLocallyUniformConverges (fun n => f₃ (s₁₂₃₄ n)) g₃ := by
    simpa only [s₁₂₃₄, Function.comp_apply] using hg₃₁₂₃.comp_strictMono hs₄
  have hg₄₁₂₃₄ : SpaceTimeLocallyUniformConverges (fun n => f₄ (s₁₂₃₄ n)) g₄ := by
    simpa only [s₁₂₃₄, Function.comp_apply] using hg₄
  obtain ⟨s₅, hs₅, g₅, hg₅⟩ := exists_spaceTimeLocallyUniform_subsequence
    (fun n => f₅ (s₁₂₃₄ n)) (h₅.equibounded.comp_strictMono hs₁₂₃₄)
      (h₅.equicontinuous.comp_strictMono hs₁₂₃₄)
  let s₁₂₃₄₅ := s₁₂₃₄ ∘ s₅
  have hs₁₂₃₄₅ : StrictMono s₁₂₃₄₅ := hs₁₂₃₄.comp hs₅
  have hg₁₁₂₃₄₅ : SpaceTimeLocallyUniformConverges (fun n => f₁ (s₁₂₃₄₅ n)) g₁ := by
    simpa only [s₁₂₃₄₅, Function.comp_apply] using hg₁₁₂₃₄.comp_strictMono hs₅
  have hg₂₁₂₃₄₅ : SpaceTimeLocallyUniformConverges (fun n => f₂ (s₁₂₃₄₅ n)) g₂ := by
    simpa only [s₁₂₃₄₅, Function.comp_apply] using hg₂₁₂₃₄.comp_strictMono hs₅
  have hg₃₁₂₃₄₅ : SpaceTimeLocallyUniformConverges (fun n => f₃ (s₁₂₃₄₅ n)) g₃ := by
    simpa only [s₁₂₃₄₅, Function.comp_apply] using hg₃₁₂₃₄.comp_strictMono hs₅
  have hg₄₁₂₃₄₅ : SpaceTimeLocallyUniformConverges (fun n => f₄ (s₁₂₃₄₅ n)) g₄ := by
    simpa only [s₁₂₃₄₅, Function.comp_apply] using hg₄₁₂₃₄.comp_strictMono hs₅
  have hg₅₁₂₃₄₅ : SpaceTimeLocallyUniformConverges (fun n => f₅ (s₁₂₃₄₅ n)) g₅ := by
    simpa only [s₁₂₃₄₅, Function.comp_apply] using hg₅
  obtain ⟨s₆, hs₆, g₆, hg₆⟩ := exists_spaceTimeLocallyUniform_subsequence
    (fun n => f₆ (s₁₂₃₄₅ n)) (h₆.equibounded.comp_strictMono hs₁₂₃₄₅)
      (h₆.equicontinuous.comp_strictMono hs₁₂₃₄₅)
  let s₁₂₃₄₅₆ := s₁₂₃₄₅ ∘ s₆
  have hs₁₂₃₄₅₆ : StrictMono s₁₂₃₄₅₆ := hs₁₂₃₄₅.comp hs₆
  have hg₁₁₂₃₄₅₆ : SpaceTimeLocallyUniformConverges (fun n => f₁ (s₁₂₃₄₅₆ n)) g₁ := by
    simpa only [s₁₂₃₄₅₆, Function.comp_apply] using hg₁₁₂₃₄₅.comp_strictMono hs₆
  have hg₂₁₂₃₄₅₆ : SpaceTimeLocallyUniformConverges (fun n => f₂ (s₁₂₃₄₅₆ n)) g₂ := by
    simpa only [s₁₂₃₄₅₆, Function.comp_apply] using hg₂₁₂₃₄₅.comp_strictMono hs₆
  have hg₃₁₂₃₄₅₆ : SpaceTimeLocallyUniformConverges (fun n => f₃ (s₁₂₃₄₅₆ n)) g₃ := by
    simpa only [s₁₂₃₄₅₆, Function.comp_apply] using hg₃₁₂₃₄₅.comp_strictMono hs₆
  have hg₄₁₂₃₄₅₆ : SpaceTimeLocallyUniformConverges (fun n => f₄ (s₁₂₃₄₅₆ n)) g₄ := by
    simpa only [s₁₂₃₄₅₆, Function.comp_apply] using hg₄₁₂₃₄₅.comp_strictMono hs₆
  have hg₅₁₂₃₄₅₆ : SpaceTimeLocallyUniformConverges (fun n => f₅ (s₁₂₃₄₅₆ n)) g₅ := by
    simpa only [s₁₂₃₄₅₆, Function.comp_apply] using hg₅₁₂₃₄₅.comp_strictMono hs₆
  have hg₆₁₂₃₄₅₆ : SpaceTimeLocallyUniformConverges (fun n => f₆ (s₁₂₃₄₅₆ n)) g₆ := by
    simpa only [s₁₂₃₄₅₆, Function.comp_apply] using hg₆
  obtain ⟨s₇, hs₇, g₇, hg₇⟩ := exists_spaceTimeLocallyUniform_subsequence
    (fun n => f₇ (s₁₂₃₄₅₆ n)) (h₇.equibounded.comp_strictMono hs₁₂₃₄₅₆)
      (h₇.equicontinuous.comp_strictMono hs₁₂₃₄₅₆)
  let subseq := s₁₂₃₄₅₆ ∘ s₇
  have hsubseq : StrictMono subseq := hs₁₂₃₄₅₆.comp hs₇
  refine ⟨subseq, hsubseq, g₁, g₂, g₃, g₄, g₅, g₆, g₇, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [subseq, Function.comp_apply] using hg₁₁₂₃₄₅₆.comp_strictMono hs₇
  · simpa only [subseq, Function.comp_apply] using hg₂₁₂₃₄₅₆.comp_strictMono hs₇
  · simpa only [subseq, Function.comp_apply] using hg₃₁₂₃₄₅₆.comp_strictMono hs₇
  · simpa only [subseq, Function.comp_apply] using hg₄₁₂₃₄₅₆.comp_strictMono hs₇
  · simpa only [subseq, Function.comp_apply] using hg₅₁₂₃₄₅₆.comp_strictMono hs₇
  · simpa only [subseq, Function.comp_apply] using hg₆₁₂₃₄₅₆.comp_strictMono hs₇
  · simpa only [subseq, Function.comp_apply] using hg₇

/-- Exact estimates and closed identities needed on a sequence of translated
classical solutions.  The only non-algebraic fields are the seven local
equibounded/equicontinuous packages. -/
structure ChiOneClassicalSequenceData
    (chi c ell k : ℝ)
    (u ux uxx ut r rx rxx : ℕ → ℝ → ℝ → ℝ) : Prop where
  hkpos : 0 < k
  hk1 : k < 1
  hchi : 0 ≤ chi
  hell : 0 < ell
  u_precompact : SpaceTimeLocallyPrecompact u
  ux_precompact : SpaceTimeLocallyPrecompact ux
  uxx_precompact : SpaceTimeLocallyPrecompact uxx
  ut_precompact : SpaceTimeLocallyPrecompact ut
  r_precompact : SpaceTimeLocallyPrecompact r
  rx_precompact : SpaceTimeLocallyPrecompact rx
  rxx_precompact : SpaceTimeLocallyPrecompact rxx
  u_space_deriv : ∀ n t x, HasDerivAt (u n t) (ux n t x) x
  ux_space_deriv : ∀ n t x, HasDerivAt (ux n t) (uxx n t x) x
  r_space_deriv : ∀ n t x, HasDerivAt (r n t) (rx n t x) x
  rx_space_deriv : ∀ n t x, HasDerivAt (rx n t) (rxx n t x) x
  u_time_deriv : ∀ n t x, HasDerivAt (fun s => u n s x) (ut n t x) t
  uxx_continuous : ∀ n t, Continuous (uxx n t)
  ut_continuous : ∀ n t, Continuous (ut n t)
  rxx_continuous : ∀ n t, Continuous (rxx n t)
  population_pde : ∀ n t x,
    ut n t x = uxx n t x + c * ux n t x -
      chi * (ux n t x * rx n t x + u n t x * rxx n t x) +
        u n t x * (1 - u n t x)
  resolver : ∀ n t x, -rxx n t x + r n t x = u n t x - 1
  floor : ∀ R > 0, ∀ᶠ n in atTop,
    ∀ t ∈ Set.Icc (-R) R, ∀ x ∈ Set.Icc (-R) R, ell ≤ u n t x
  uniform_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ R > 0, ∀ᶠ n in atTop,
    ∀ t ∈ Set.Icc (-R) R, ∀ x ∈ Set.Icc (-R) R,
      |u n t x| ≤ C ∧ |ux n t x| ≤ C ∧ |uxx n t x| ≤ C ∧
      |ut n t x| ≤ C ∧ |r n t x| ≤ C ∧ |rx n t x| ≤ C ∧
      |rxx n t x| ≤ C

/-- The sequence estimates above produce a bounded entire classical limit,
with all differential identities and global bounds passed to the limit. -/
theorem ChiOneClassicalSequenceData.exists_entireClassical_subsequence
    {chi c ell k : ℝ}
    {u ux uxx ut r rx rxx : ℕ → ℝ → ℝ → ℝ}
    (H : ChiOneClassicalSequenceData chi c ell k u ux uxx ut r rx rxx) :
    ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
      ∃ (U Ux Uxx Ut R Rx Rxx : ℝ → ℝ → ℝ),
        ChiOneEntireBoundedClassicalData chi c ell k 0
          U Ux Uxx Ut R Rx Rxx ∧
        SpaceTimeLocallyUniformConverges (fun n => u (subseq n)) U ∧
        SpaceTimeLocallyUniformConverges (fun n => ux (subseq n)) Ux ∧
        SpaceTimeLocallyUniformConverges (fun n => uxx (subseq n)) Uxx ∧
        SpaceTimeLocallyUniformConverges (fun n => ut (subseq n)) Ut ∧
        SpaceTimeLocallyUniformConverges (fun n => r (subseq n)) R ∧
        SpaceTimeLocallyUniformConverges (fun n => rx (subseq n)) Rx ∧
        SpaceTimeLocallyUniformConverges (fun n => rxx (subseq n)) Rxx := by
  obtain ⟨subseq, hsubseq, U, Ux, Uxx, Ut, R, Rx, Rxx,
      hU, hUx, hUxx, hUt, hR, hRx, hRxx⟩ :=
    exists_sevenField_spaceTimeLocallyUniform_subsequence
      u ux uxx ut r rx rxx H.u_precompact H.ux_precompact H.uxx_precompact
        H.ut_precompact H.r_precompact H.rx_precompact H.rxx_precompact
  have hfloorSub : ∀ A > 0, ∀ᶠ n in atTop,
      ∀ t ∈ Set.Icc (-A) A, ∀ x ∈ Set.Icc (-A) A,
        ell ≤ u (subseq n) t x := by
    intro A hA
    exact hsubseq.tendsto_atTop.eventually (H.floor A hA)
  obtain ⟨C, hC0, hbound⟩ := H.uniform_bound
  have hboundSub : ∀ A > 0, ∀ᶠ n in atTop,
      ∀ t ∈ Set.Icc (-A) A, ∀ x ∈ Set.Icc (-A) A,
        |u (subseq n) t x| ≤ C ∧ |ux (subseq n) t x| ≤ C ∧
        |uxx (subseq n) t x| ≤ C ∧ |ut (subseq n) t x| ≤ C ∧
        |r (subseq n) t x| ≤ C ∧ |rx (subseq n) t x| ≤ C ∧
        |rxx (subseq n) t x| ≤ C := by
    intro A hA
    exact hsubseq.tendsto_atTop.eventually (hbound A hA)
  have hUbound : ∀ t x, |U t x| ≤ C :=
    hU.abs_le_of_eventually_box_abs_le fun A hA =>
      (hboundSub A hA).mono fun _ hn t ht x hx => (hn t ht x hx).1
  have hUxbound : ∀ t x, |Ux t x| ≤ C :=
    hUx.abs_le_of_eventually_box_abs_le fun A hA =>
      (hboundSub A hA).mono fun _ hn t ht x hx => (hn t ht x hx).2.1
  have hUxxbound : ∀ t x, |Uxx t x| ≤ C :=
    hUxx.abs_le_of_eventually_box_abs_le fun A hA =>
      (hboundSub A hA).mono fun _ hn t ht x hx => (hn t ht x hx).2.2.1
  have hUtbound : ∀ t x, |Ut t x| ≤ C :=
    hUt.abs_le_of_eventually_box_abs_le fun A hA =>
      (hboundSub A hA).mono fun _ hn t ht x hx => (hn t ht x hx).2.2.2.1
  have hRbound : ∀ t x, |R t x| ≤ C :=
    hR.abs_le_of_eventually_box_abs_le fun A hA =>
      (hboundSub A hA).mono fun _ hn t ht x hx => (hn t ht x hx).2.2.2.2.1
  have hRxbound : ∀ t x, |Rx t x| ≤ C :=
    hRx.abs_le_of_eventually_box_abs_le fun A hA =>
      (hboundSub A hA).mono fun _ hn t ht x hx => (hn t ht x hx).2.2.2.2.2.1
  have hRxxbound : ∀ t x, |Rxx t x| ≤ C :=
    hRxx.abs_le_of_eventually_box_abs_le fun A hA =>
      (hboundSub A hA).mono fun _ hn t ht x hx => (hn t ht x hx).2.2.2.2.2.2
  have Hclassical : ChiOneEntireBoundedClassicalData chi c ell k 0
      U Ux Uxx Ut R Rx Rxx :=
    { hkpos := H.hkpos
      hk1 := H.hk1
      hchi := H.hchi
      hell := H.hell
      u_floor := hU.lower_of_eventually_box_lower hfloorSub
      u_space_deriv := hasDerivAt_spatial_limit hU hUx
        (fun n => H.u_space_deriv (subseq n))
      ux_space_deriv := hasDerivAt_spatial_limit hUx hUxx
        (fun n => H.ux_space_deriv (subseq n))
      r_space_deriv := hasDerivAt_spatial_limit hR hRx
        (fun n => H.r_space_deriv (subseq n))
      rx_space_deriv := hasDerivAt_spatial_limit hRx hRxx
        (fun n => H.rx_space_deriv (subseq n))
      u_time_deriv := hasDerivAt_temporal_limit hU hUt
        (fun n => H.u_time_deriv (subseq n))
      uxx_continuous := hUxx.continuous_spatial_limit
        (fun n => H.uxx_continuous (subseq n))
      ut_continuous := hUt.continuous_spatial_limit
        (fun n => H.ut_continuous (subseq n))
      rxx_continuous := hRxx.continuous_spatial_limit
        (fun n => H.rxx_continuous (subseq n))
      population_pde := chiOne_population_pde_of_locallyUniform
        hU hUx hUxx hUt hR hRx hRxx (fun n => H.population_pde (subseq n))
      resolver := chiOne_resolver_of_locallyUniform hU hR hRxx
        (fun n => H.resolver (subseq n))
      uniform_bound := ⟨C, hC0, fun t x =>
        ⟨hUbound t x, hUxbound t x, hUxxbound t x, hUtbound t x,
          hRbound t x, hRxbound t x, hRxxbound t x⟩⟩ }
  exact ⟨subseq, hsubseq, U, Ux, Uxx, Ut, R, Rx, Rxx, Hclassical,
    hU, hUx, hUxx, hUt, hR, hRx, hRxx⟩

/-- The precise remaining parabolic-compactness obligation for an orbit.
For every late-time/far-left translation sequence, one must supply the six
derivative/resolver translate fields and the uniform local estimates in
`ChiOneClassicalSequenceData`. -/
structure ChiOneFarLeftParabolicCompactness
    (chi c ell k : ℝ) (orbit : ℝ → ℝ → ℝ) : Prop where
  translatedData :
    ∀ (timeShift spaceShift : ℕ → ℝ),
      (∀ n : ℕ, (n : ℝ) ≤ timeShift n) →
      (∀ n : ℕ, spaceShift n ≤ -(n : ℝ)) →
      ∃ (ux uxx ut r rx rxx : ℕ → ℝ → ℝ → ℝ),
        ChiOneClassicalSequenceData chi c ell k
          (fun n => chiOneFarLeftTranslate c orbit timeShift spaceShift n)
          ux uxx ut r rx rxx

/-- Classical entire-limit extraction, with no weighted integrability or IBP
fields in its statement. -/
structure ChiOneFarLeftClassicalNormalFamily
    (chi c ell k : ℝ) (orbit : ℝ → ℝ → ℝ) : Prop where
  extract :
    ∀ (timeShift spaceShift : ℕ → ℝ),
      (∀ n : ℕ, (n : ℝ) ≤ timeShift n) →
      (∀ n : ℕ, spaceShift n ≤ -(n : ℝ)) →
      ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
        ∃ (u ux uxx ut r rx rxx : ℝ → ℝ → ℝ),
          ChiOneEntireBoundedClassicalData chi c ell k 0
            u ux uxx ut r rx rxx ∧
          SpaceTimeLocallyUniformConverges
            (fun n => chiOneFarLeftTranslate c orbit timeShift spaceShift
              (subseq n)) u

theorem ChiOneFarLeftParabolicCompactness.to_classicalNormalFamily
    {chi c ell k : ℝ} {orbit : ℝ → ℝ → ℝ}
    (H : ChiOneFarLeftParabolicCompactness chi c ell k orbit) :
    ChiOneFarLeftClassicalNormalFamily chi c ell k orbit := by
  constructor
  intro timeShift spaceShift htime hspace
  obtain ⟨ux, uxx, ut, r, rx, rxx, Hseq⟩ :=
    H.translatedData timeShift spaceShift htime hspace
  obtain ⟨subseq, hsubseq, U, Ux, Uxx, Ut, R, Rx, Rxx,
      Hclassical, hU, _hUx, _hUxx, _hUt, _hR, _hRx, _hRxx⟩ :=
    Hseq.exists_entireClassical_subsequence
  exact ⟨subseq, hsubseq, U, Ux, Uxx, Ut, R, Rx, Rxx, Hclassical, hU⟩

theorem ChiOneFarLeftClassicalNormalFamily.to_entropyCompactness
    {chi c ell k : ℝ} {orbit : ℝ → ℝ → ℝ}
    (H : ChiOneFarLeftClassicalNormalFamily chi c ell k orbit) :
    ChiOneFarLeftEntropyCompactness chi c ell k orbit := by
  constructor
  intro timeShift spaceShift htime hspace
  obtain ⟨subseq, hsubseq, u, ux, uxx, ut, r, rx, rxx, Hclassical, hconv⟩ :=
    H.extract timeShift spaceShift htime hspace
  refine ⟨subseq, hsubseq, u, ux, uxx, ut, r, rx, rxx,
    Hclassical.to_entireWeightedEntropyData, ?_⟩
  simpa only [chiOneFarLeftTranslate, add_zero] using hconv.tendsto_at 0 0

theorem uniformCoMovingLeftEquilibriumConvergence_chiPos_upto_four_of_classicalNormalFamily
    {chi c ell : ℝ} {orbit : ℝ → ℝ → ℝ}
    (hchi : 0 ≤ chi) (hchi4 : chi < 4) (hell : 0 < ell)
    (Hnormal : ∀ k : ℝ, 0 < k → k < 1 →
      ChiOneFarLeftClassicalNormalFamily chi c ell k orbit) :
    UniformCoMovingLeftEquilibriumConvergence c orbit := by
  apply
    uniformCoMovingLeftEquilibriumConvergence_chiOne_full_sharp_range_of_entropyCompactness
      hchi hchi4 hell
  intro k hkpos hk1
  exact (Hnormal k hkpos hk1).to_entropyCompactness

/-- Final sharp-range theorem with the remaining analytic hypothesis stated
only as uniform parabolic normal-family estimates on the translated fields. -/
theorem uniformCoMovingLeftEquilibriumConvergence_chiPos_upto_four_of_parabolicCompactness
    {chi c ell : ℝ} {orbit : ℝ → ℝ → ℝ}
    (hchi : 0 ≤ chi) (hchi4 : chi < 4) (hell : 0 < ell)
    (Hcompact : ∀ k : ℝ, 0 < k → k < 1 →
      ChiOneFarLeftParabolicCompactness chi c ell k orbit) :
    UniformCoMovingLeftEquilibriumConvergence c orbit := by
  apply uniformCoMovingLeftEquilibriumConvergence_chiPos_upto_four_of_classicalNormalFamily
    hchi hchi4 hell
  intro k hkpos hk1
  exact (Hcompact k hkpos hk1).to_classicalNormalFamily

def CanonicalChiOneFarLeftParabolicCompactness
    (p : CMParams) (chi c ell k : ℝ) (u₀ : WholeLineBUC) : Prop :=
  ChiOneFarLeftParabolicCompactness chi c ell k
    (wholeLineCauchyGlobalU p u₀)

theorem uniformCoMovingLeftEquilibriumConvergence_chiPos_upto_four_of_canonicalParabolicCompactness
    {p : CMParams} {chi c ell : ℝ} {u₀ : WholeLineBUC}
    (hchi : 0 ≤ chi) (hchi4 : chi < 4) (hell : 0 < ell)
    (Hcompact : ∀ k : ℝ, 0 < k → k < 1 →
      CanonicalChiOneFarLeftParabolicCompactness p chi c ell k u₀) :
    UniformCoMovingLeftEquilibriumConvergence c
      (wholeLineCauchyGlobalU p u₀) :=
  uniformCoMovingLeftEquilibriumConvergence_chiPos_upto_four_of_parabolicCompactness
    hchi hchi4 hell Hcompact

section AxiomAudit

#print axioms hasDerivAt_spatial_limit
#print axioms hasDerivAt_temporal_limit
#print axioms chiOne_population_pde_of_locallyUniform
#print axioms exists_sevenField_spaceTimeLocallyUniform_subsequence
#print axioms ChiOneClassicalSequenceData.exists_entireClassical_subsequence
#print axioms ChiOneFarLeftParabolicCompactness.to_classicalNormalFamily
#print axioms ChiOneFarLeftClassicalNormalFamily.to_entropyCompactness
#print axioms
  uniformCoMovingLeftEquilibriumConvergence_chiPos_upto_four_of_classicalNormalFamily
#print axioms
  uniformCoMovingLeftEquilibriumConvergence_chiPos_upto_four_of_canonicalParabolicCompactness

end AxiomAudit

end ShenWork.Paper1
