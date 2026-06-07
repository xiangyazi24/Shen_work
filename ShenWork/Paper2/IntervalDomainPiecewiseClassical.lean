/-
  hPCW: `PiecewiseClassicalWorks p` — the splice of two classical solutions
  agreeing on the overlap `(τ, T₁)` is itself a classical solution.

  Key structure: the splice
    `u' = fun t x => if t < T₁ then u₁ t x else u₂ (t - τ) x`
  agrees with `u₁` on the open time set `Iio T₁` and (by the overlap
  hypothesis) with the delayed solution `fun t x => u₂ (t - τ) x` on the open
  time set `Ioi τ`.  Since `τ < T₁`, these two open sets cover all times, and
  every conjunct of `intervalDomainClassicalRegularity` is local in time
  (fixed-time slices, pointwise `deriv` / `DifferentiableAt`, or pointwise
  `ContinuousWithinAt`), so each transfers from the matching side.

  The only conjunct with genuinely global time coupling — the sup-norm
  logistic decay (1), whose decay interval `Ioc 0 t₀` can cross the seam —
  is glued via `antitoneOn_of_deriv_nonpos`: the sup-norm of the delayed
  solution is antitone on `(0, t₀ − τ]`, hence stays above the logistic
  threshold back through the overlap, which re-triggers `u₁`'s own decay
  hypothesis at an overlap time.

  Implementation note: the splice is proved classical for ABSTRACT `u' v'`
  satisfying the pointwise if-characterisation (`hu'def`/`hv'def`), so all
  goals mention genuine local constants and slice rewriting is syntactic;
  the wrapper instantiates with the literal lambdas via `rfl`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainPiecewiseGlue

open ShenWork.IntervalDomain ShenWork.Paper2 Set Filter Topology

noncomputable section

namespace ShenWork.Paper2.PiecewiseClassical

/-- Transfer `IntervalDomainSupNormDerivativeNonposOn` along slice agreement
on an open superset `U ⊇ I`. -/
private lemma supNormNonposOn_congr
    {w w' : ℝ → intervalDomainPoint → ℝ} {I U : Set ℝ}
    (hU : IsOpen U) (hIU : I ⊆ U)
    (hslice : ∀ s ∈ U, w' s = w s)
    (h : IntervalDomainSupNormDerivativeNonposOn w I) :
    IntervalDomainSupNormDerivativeNonposOn w' I := by
  have heq : ∀ s ∈ U,
      intervalDomainSupNorm (w' s) = intervalDomainSupNorm (w s) :=
    fun s hs => by rw [hslice s hs]
  have hev : ∀ s ∈ U,
      (fun r => intervalDomainSupNorm (w' r)) =ᶠ[nhds s]
        fun r => intervalDomainSupNorm (w r) := fun s hs =>
    Set.EqOn.eventuallyEq_of_mem (fun r hr => heq r hr) (hU.mem_nhds hs)
  refine ⟨?_, ?_, ?_⟩
  · exact h.continuousOn.congr fun s hs => heq s (hIU hs)
  · exact h.differentiableOn.congr fun s hs =>
      heq s (hIU (interior_subset hs))
  · intro s hs
    rw [(hev s (hIU (interior_subset hs))).deriv_eq]
    exact h.deriv_nonpos s hs

/-- Local gluing of joint continuity on time-product slabs: if `F` agrees
with `F₁` for times `< T₁` and with the `τ`-delay of `F₂` for times `> τ`,
where `τ < T₁` and `T' ≤ τ + T₂`, then continuity of the pieces glues to
continuity of `F` on `Ioo 0 T' ×ˢ S`. -/
private lemma continuousOn_prod_glue
    {F F₁ F₂ : ℝ × ℝ → ℝ} {T' T₁ T₂ τ : ℝ} {S : Set ℝ}
    (hτT₁ : τ < T₁) (hT'le : T' ≤ τ + T₂)
    (hagreeL : ∀ q : ℝ × ℝ, q.1 < T₁ → F q = F₁ q)
    (hagreeR : ∀ q : ℝ × ℝ, τ < q.1 → F q = F₂ (q.1 - τ, q.2))
    (h₁ : ContinuousOn F₁ (Set.Ioo 0 T₁ ×ˢ S))
    (h₂ : ContinuousOn F₂ (Set.Ioo 0 T₂ ×ˢ S)) :
    ContinuousOn F (Set.Ioo 0 T' ×ˢ S) := by
  rintro ⟨t, y⟩ ⟨ht, hy⟩
  by_cases hcase : t < T₁
  · -- left piece: agree with F₁ on the open `Iio T₁ ×ˢ univ`
    have hmem : (Set.Ioo (0:ℝ) T' ×ˢ S) ∩ (Set.Iio T₁ ×ˢ Set.univ) ∈
        nhdsWithin (t, y) (Set.Ioo (0:ℝ) T' ×ˢ S) :=
      Filter.inter_mem self_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds
          ((isOpen_Iio.prod isOpen_univ).mem_nhds ⟨hcase, Set.mem_univ _⟩))
    refine ContinuousWithinAt.mono_of_mem_nhdsWithin ?_ hmem
    have hsub : (Set.Ioo (0:ℝ) T' ×ˢ S) ∩ (Set.Iio T₁ ×ˢ Set.univ)
        ⊆ Set.Ioo (0:ℝ) T₁ ×ˢ S := by
      rintro ⟨r, z⟩ ⟨⟨hr, hz⟩, hrT₁, -⟩
      exact ⟨⟨hr.1, hrT₁⟩, hz⟩
    refine ((h₁ (t, y) ⟨⟨ht.1, hcase⟩, hy⟩).mono hsub).congr ?_
      (hagreeL (t, y) hcase)
    rintro ⟨r, z⟩ ⟨-, hrT₁, -⟩
    exact hagreeL (r, z) hrT₁
  · -- right piece: agree with the delay of F₂ on the open `Ioi τ ×ˢ univ`
    have hτt : τ < t := lt_of_lt_of_le hτT₁ (not_lt.mp hcase)
    have hmem : (Set.Ioo (0:ℝ) T' ×ˢ S) ∩ (Set.Ioi τ ×ˢ Set.univ) ∈
        nhdsWithin (t, y) (Set.Ioo (0:ℝ) T' ×ˢ S) :=
      Filter.inter_mem self_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds
          ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hτt, Set.mem_univ _⟩))
    refine ContinuousWithinAt.mono_of_mem_nhdsWithin ?_ hmem
    have hshift : ContinuousWithinAt
        (F₂ ∘ fun q : ℝ × ℝ => (q.1 - τ, q.2))
        ((Set.Ioo (0:ℝ) T' ×ˢ S) ∩ (Set.Ioi τ ×ˢ Set.univ)) (t, y) := by
      refine ContinuousWithinAt.comp (t := Set.Ioo (0:ℝ) T₂ ×ˢ S)
        (h₂ (t - τ, y) ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, hy⟩)
        (Continuous.continuousWithinAt (by fun_prop)) ?_
      rintro ⟨r, z⟩ ⟨⟨hr, hz⟩, hrτ, -⟩
      exact ⟨⟨by linarith [(Set.mem_Ioi.mp hrτ)], by linarith [hr.2]⟩, hz⟩
    refine hshift.congr ?_ (hagreeR (t, y) hτt)
    rintro ⟨r, z⟩ ⟨-, hrτ, -⟩
    exact hagreeR (r, z) hrτ

set_option maxHeartbeats 1600000 in
/-- **Core splice theorem (abstract form).**  If `u'`/`v'` are pointwise the
if-splices of two classical solutions agreeing on the overlap `(τ, T₁)`,
then `(u', v')` is a classical solution on any horizon `T' ≤ τ + T₂`. -/
private theorem splice_isClassical
    (p : CM2Params) {T₁ T₂ τ : ℝ} (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (hτ : 0 < τ) (hτT₁ : τ < T₁)
    {u₁ v₁ u₂ v₂ u' v' : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    (hovU : ∀ s, τ < s → s < T₁ → ∀ x, u₁ s x = u₂ (s - τ) x)
    (hovV : ∀ s, τ < s → s < T₁ → ∀ x, v₁ s x = v₂ (s - τ) x)
    (hu'def : ∀ t x, u' t x = if t < T₁ then u₁ t x else u₂ (t - τ) x)
    (hv'def : ∀ t x, v' t x = if t < T₁ then v₁ t x else v₂ (t - τ) x)
    {T' : ℝ} (hT' : 0 < T') (hT'le : T' ≤ τ + T₂) :
    IsPaper2ClassicalSolution intervalDomain p T' u' v' := by
  obtain ⟨-, hreg₁, hposU₁, hnnV₁, hpdeU₁, hpdeV₁, hbc₁⟩ := hsol₁
  obtain ⟨-, hreg₂, hposU₂, hnnV₂, hpdeU₂, hpdeV₂, hbc₂⟩ := hsol₂
  -- `intervalDomainClassicalRegularity` is now 7 conjuncts (supnorm pair removed
  -- 2026-06-06); old c3..c9 → new c1..c7, so the binders keep their h3..h9 names.
  obtain ⟨h3₁, h4₁, h5₁, h6₁, h7₁, h8₁, h9₁⟩ := hreg₁
  obtain ⟨h3₂, h4₂, h5₂, h6₂, h7₂, h8₂, h9₂⟩ := hreg₂
  -- ## Slice agreement
  have hsliceUL : ∀ t : ℝ, t < T₁ → u' t = u₁ t := by
    intro t h; funext x; rw [hu'def t x]; exact if_pos h
  have hsliceVL : ∀ t : ℝ, t < T₁ → v' t = v₁ t := by
    intro t h; funext x; rw [hv'def t x]; exact if_pos h
  have hsliceUR : ∀ t : ℝ, τ < t → u' t = u₂ (t - τ) := by
    intro t h
    funext x; rw [hu'def t x]
    by_cases h' : t < T₁
    · rw [if_pos h']; exact hovU t h h' x
    · rw [if_neg h']
  have hsliceVR : ∀ t : ℝ, τ < t → v' t = v₂ (t - τ) := by
    intro t h
    funext x; rw [hv'def t x]
    by_cases h' : t < T₁
    · rw [if_pos h']; exact hovV t h h' x
    · rw [if_neg h']
  -- ## Basic membership helpers
  have hnotL : ∀ {t : ℝ}, ¬ t < T₁ → τ < t :=
    fun h => lt_of_lt_of_le hτT₁ (not_lt.mp h)
  have hmemR : ∀ {t : ℝ}, t ∈ Set.Ioo (0:ℝ) T' → τ < t →
      t - τ ∈ Set.Ioo (0:ℝ) T₂ := by
    intro t ht h
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hwit₁ : (τ + T₁) / 2 ∈ Set.Ioo (0:ℝ) T₁ := ⟨by linarith, by linarith⟩
  have hwit₂ : T₂ / 2 ∈ Set.Ioo (0:ℝ) T₂ := ⟨by linarith, by linarith⟩
  -- ## Eventual equality of time slices at a fixed spatial point
  have hUtimeL : ∀ (x : intervalDomainPoint) {t : ℝ}, t < T₁ →
      (fun s => u' s x) =ᶠ[nhds t] fun s => u₁ s x := fun x {t} h =>
    Set.EqOn.eventuallyEq_of_mem (fun s hs => congrFun (hsliceUL s hs) x)
      (isOpen_Iio.mem_nhds h)
  have hVtimeL : ∀ (x : intervalDomainPoint) {t : ℝ}, t < T₁ →
      (fun s => v' s x) =ᶠ[nhds t] fun s => v₁ s x := fun x {t} h =>
    Set.EqOn.eventuallyEq_of_mem (fun s hs => congrFun (hsliceVL s hs) x)
      (isOpen_Iio.mem_nhds h)
  have hUtimeR : ∀ (x : intervalDomainPoint) {t : ℝ}, τ < t →
      (fun s => u' s x) =ᶠ[nhds t] fun s => u₂ (s - τ) x := fun x {t} h =>
    Set.EqOn.eventuallyEq_of_mem (fun s hs => congrFun (hsliceUR s hs) x)
      (isOpen_Ioi.mem_nhds h)
  have hVtimeR : ∀ (x : intervalDomainPoint) {t : ℝ}, τ < t →
      (fun s => v' s x) =ᶠ[nhds t] fun s => v₂ (s - τ) x := fun x {t} h =>
    Set.EqOn.eventuallyEq_of_mem (fun s hs => congrFun (hsliceVR s hs) x)
      (isOpen_Ioi.mem_nhds h)
  -- ## Pointwise time-derivative agreement
  have hderivUL : ∀ (x : intervalDomainPoint) {t : ℝ}, t < T₁ →
      deriv (fun s => u' s x) t = deriv (fun s => u₁ s x) t :=
    fun x {t} h => (hUtimeL x h).deriv_eq
  have hderivVL : ∀ (x : intervalDomainPoint) {t : ℝ}, t < T₁ →
      deriv (fun s => v' s x) t = deriv (fun s => v₁ s x) t :=
    fun x {t} h => (hVtimeL x h).deriv_eq
  have hderivUR : ∀ (x : intervalDomainPoint) {t : ℝ}, τ < t →
      deriv (fun s => u' s x) t = deriv (fun s => u₂ s x) (t - τ) := by
    intro x t h
    rw [(hUtimeR x h).deriv_eq]
    exact deriv_comp_sub_const (f := fun s => u₂ s x) (a := τ) t
  have hderivVR : ∀ (x : intervalDomainPoint) {t : ℝ}, τ < t →
      deriv (fun s => v' s x) t = deriv (fun s => v₂ s x) (t - τ) := by
    intro x t h
    rw [(hVtimeR x h).deriv_eq]
    exact deriv_comp_sub_const (f := fun s => v₂ s x) (a := τ) t
  -- ## Lifted versions (real spatial coordinate)
  have hliftUL : ∀ (y : ℝ) {t : ℝ}, t < T₁ →
      (fun s => intervalDomainLift (u' s) y) =ᶠ[nhds t]
        fun s => intervalDomainLift (u₁ s) y := fun y {t} h =>
    Set.EqOn.eventuallyEq_of_mem
      (fun s hs => by rw [hsliceUL s hs]) (isOpen_Iio.mem_nhds h)
  have hliftVL : ∀ (y : ℝ) {t : ℝ}, t < T₁ →
      (fun s => intervalDomainLift (v' s) y) =ᶠ[nhds t]
        fun s => intervalDomainLift (v₁ s) y := fun y {t} h =>
    Set.EqOn.eventuallyEq_of_mem
      (fun s hs => by rw [hsliceVL s hs]) (isOpen_Iio.mem_nhds h)
  have hliftUR : ∀ (y : ℝ) {t : ℝ}, τ < t →
      (fun s => intervalDomainLift (u' s) y) =ᶠ[nhds t]
        fun s => intervalDomainLift (u₂ (s - τ)) y := fun y {t} h =>
    Set.EqOn.eventuallyEq_of_mem
      (fun s hs => by rw [hsliceUR s hs]) (isOpen_Ioi.mem_nhds h)
  have hliftVR : ∀ (y : ℝ) {t : ℝ}, τ < t →
      (fun s => intervalDomainLift (v' s) y) =ᶠ[nhds t]
        fun s => intervalDomainLift (v₂ (s - τ)) y := fun y {t} h =>
    Set.EqOn.eventuallyEq_of_mem
      (fun s hs => by rw [hsliceVR s hs]) (isOpen_Ioi.mem_nhds h)
  have hderivLiftUL : ∀ (y : ℝ) {t : ℝ}, t < T₁ →
      deriv (fun s => intervalDomainLift (u' s) y) t
        = deriv (fun s => intervalDomainLift (u₁ s) y) t :=
    fun y {t} h => (hliftUL y h).deriv_eq
  have hderivLiftVL : ∀ (y : ℝ) {t : ℝ}, t < T₁ →
      deriv (fun s => intervalDomainLift (v' s) y) t
        = deriv (fun s => intervalDomainLift (v₁ s) y) t :=
    fun y {t} h => (hliftVL y h).deriv_eq
  have hderivLiftUR : ∀ (y : ℝ) {t : ℝ}, τ < t →
      deriv (fun s => intervalDomainLift (u' s) y) t
        = deriv (fun s => intervalDomainLift (u₂ s) y) (t - τ) := by
    intro y t h
    rw [(hliftUR y h).deriv_eq]
    exact deriv_comp_sub_const (f := fun s => intervalDomainLift (u₂ s) y)
      (a := τ) t
  have hderivLiftVR : ∀ (y : ℝ) {t : ℝ}, τ < t →
      deriv (fun s => intervalDomainLift (v' s) y) t
        = deriv (fun s => intervalDomainLift (v₂ s) y) (t - τ) := by
    intro y t h
    rw [(hliftVR y h).deriv_eq]
    exact deriv_comp_sub_const (f := fun s => intervalDomainLift (v₂ s) y)
      (a := τ) t
  -- ## Sup-norm trajectory eventual equality
  have hsupevL : ∀ {t : ℝ}, t < T₁ →
      (fun r => intervalDomainSupNorm (u' r)) =ᶠ[nhds t]
        fun r => intervalDomainSupNorm (u₁ r) := fun {t} h =>
    Set.EqOn.eventuallyEq_of_mem (fun r hr => by rw [hsliceUL r hr])
      (isOpen_Iio.mem_nhds h)
  have hsupevR : ∀ {t : ℝ}, τ < t →
      (fun r => intervalDomainSupNorm (u' r)) =ᶠ[nhds t]
        fun r => intervalDomainSupNorm (u₂ (r - τ)) := fun {t} h =>
    Set.EqOn.eventuallyEq_of_mem (fun r hr => by rw [hsliceUR r hr])
      (isOpen_Ioi.mem_nhds h)
  -- ## Assemble
  refine IsPaper2ClassicalSolution.of_components hT' ?_ ?_ ?_ ?_ ?_ ?_
  · -- classicalRegularity: 7 conjuncts (supnorm pair removed)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- (3) interior spatial C²
      intro t ht
      by_cases hcase : t < T₁
      · rw [hsliceUL t hcase, hsliceVL t hcase]
        exact h3₁ t ⟨ht.1, hcase⟩
      · have hτt : τ < t := hnotL hcase
        rw [hsliceUR t hτt, hsliceVR t hτt]
        exact h3₂ (t - τ) (hmemR ht hτt)
    · -- (4) closed-domain time C¹
      intro x t ht
      constructor
      · -- DifferentiableAt at the given time
        by_cases hcase : t < T₁
        · obtain ⟨⟨hdU, hdV⟩, -, -⟩ := h4₁ x t ⟨ht.1, hcase⟩
          exact ⟨((hUtimeL x hcase).differentiableAt_iff).mpr hdU,
                 ((hVtimeL x hcase).differentiableAt_iff).mpr hdV⟩
        · have hτt : τ < t := hnotL hcase
          obtain ⟨⟨hdU, hdV⟩, -, -⟩ := h4₂ x (t - τ) (hmemR ht hτt)
          refine ⟨((hUtimeR x hτt).differentiableAt_iff).mpr ?_,
                  ((hVtimeR x hτt).differentiableAt_iff).mpr ?_⟩
          · exact (differentiableAt_comp_sub_const
              (f := fun r => u₂ r x) (a := t) (b := τ)).mpr hdU
          · exact (differentiableAt_comp_sub_const
              (f := fun r => v₂ r x) (a := t) (b := τ)).mpr hdV
      · -- ContinuousOn of the time-derivative trajectories on `Ioo 0 T'`
        constructor
        · intro s hs
          by_cases hcase : s < T₁
          · have hCA := ((h4₁ x _ hwit₁).2.1).continuousAt
              (isOpen_Ioo.mem_nhds ⟨hs.1, hcase⟩)
            have hev : (fun r => deriv (fun q => u' q x) r) =ᶠ[nhds s]
                fun r => deriv (fun q => u₁ q x) r :=
              Set.EqOn.eventuallyEq_of_mem (fun r hr => hderivUL x hr)
                (isOpen_Iio.mem_nhds hcase)
            exact (hCA.congr_of_eventuallyEq hev).continuousWithinAt
          · have hτs : τ < s := hnotL hcase
            have hCA := ((h4₂ x _ hwit₂).2.1).continuousAt
              (isOpen_Ioo.mem_nhds (hmemR hs hτs))
            have hCAcomp : ContinuousAt
                (fun r : ℝ => deriv (fun q => u₂ q x) (r - τ)) s :=
              ContinuousAt.comp (x := s)
                (g := fun σ : ℝ => deriv (fun q => u₂ q x) σ)
                (f := fun r : ℝ => r - τ)
                hCA ((continuous_sub_right τ).continuousAt)
            have hev : (fun r => deriv (fun q => u' q x) r) =ᶠ[nhds s]
                fun r => deriv (fun q => u₂ q x) (r - τ) :=
              Set.EqOn.eventuallyEq_of_mem (fun r hr => hderivUR x hr)
                (isOpen_Ioi.mem_nhds hτs)
            exact (hCAcomp.congr_of_eventuallyEq hev).continuousWithinAt
        · intro s hs
          by_cases hcase : s < T₁
          · have hCA := ((h4₁ x _ hwit₁).2.2).continuousAt
              (isOpen_Ioo.mem_nhds ⟨hs.1, hcase⟩)
            have hev : (fun r => deriv (fun q => v' q x) r) =ᶠ[nhds s]
                fun r => deriv (fun q => v₁ q x) r :=
              Set.EqOn.eventuallyEq_of_mem (fun r hr => hderivVL x hr)
                (isOpen_Iio.mem_nhds hcase)
            exact (hCA.congr_of_eventuallyEq hev).continuousWithinAt
          · have hτs : τ < s := hnotL hcase
            have hCA := ((h4₂ x _ hwit₂).2.2).continuousAt
              (isOpen_Ioo.mem_nhds (hmemR hs hτs))
            have hCAcomp : ContinuousAt
                (fun r : ℝ => deriv (fun q => v₂ q x) (r - τ)) s :=
              ContinuousAt.comp (x := s)
                (g := fun σ : ℝ => deriv (fun q => v₂ q x) σ)
                (f := fun r : ℝ => r - τ)
                hCA ((continuous_sub_right τ).continuousAt)
            have hev : (fun r => deriv (fun q => v' q x) r) =ᶠ[nhds s]
                fun r => deriv (fun q => v₂ q x) (r - τ) :=
              Set.EqOn.eventuallyEq_of_mem (fun r hr => hderivVR x hr)
                (isOpen_Ioi.mem_nhds hτs)
            exact (hCAcomp.congr_of_eventuallyEq hev).continuousWithinAt
    · -- (5) joint ∂ₜ continuity on the open slab
      constructor
      · refine continuousOn_prod_glue hτT₁ hT'le ?_ ?_ h5₁.1 h5₂.1
        · rintro ⟨r, z⟩ hr; exact hderivLiftUL z hr
        · rintro ⟨r, z⟩ hr; exact hderivLiftUR z hr
      · refine continuousOn_prod_glue hτT₁ hT'le ?_ ?_ h5₁.2 h5₂.2
        · rintro ⟨r, z⟩ hr; exact hderivLiftVL z hr
        · rintro ⟨r, z⟩ hr; exact hderivLiftVR z hr
    · -- (6) interior Neumann limits
      intro t ht
      by_cases hcase : t < T₁
      · rw [hsliceUL t hcase, hsliceVL t hcase]
        exact h6₁ t ⟨ht.1, hcase⟩
      · have hτt : τ < t := hnotL hcase
        rw [hsliceUR t hτt, hsliceVR t hτt]
        exact h6₂ (t - τ) (hmemR ht hτt)
    · -- (7) closed spatial C² + endpoint Neumann values
      intro t ht
      by_cases hcase : t < T₁
      · rw [hsliceUL t hcase, hsliceVL t hcase]
        exact h7₁ t ⟨ht.1, hcase⟩
      · have hτt : τ < t := hnotL hcase
        rw [hsliceUR t hτt, hsliceVR t hτt]
        exact h7₂ (t - τ) (hmemR ht hτt)
    · -- (8) closed-slab joint ∂ₜ continuity
      constructor
      · refine continuousOn_prod_glue hτT₁ hT'le ?_ ?_ h8₁.1 h8₂.1
        · rintro ⟨r, z⟩ hr; exact hderivLiftUL z hr
        · rintro ⟨r, z⟩ hr; exact hderivLiftUR z hr
      · refine continuousOn_prod_glue hτT₁ hT'le ?_ ?_ h8₁.2 h8₂.2
        · rintro ⟨r, z⟩ hr; exact hderivLiftVL z hr
        · rintro ⟨r, z⟩ hr; exact hderivLiftVR z hr
    · -- (9) closed-slab joint solution continuity
      constructor
      · refine continuousOn_prod_glue hτT₁ hT'le ?_ ?_ h9₁.1 h9₂.1
        · rintro ⟨r, z⟩ hr
          show intervalDomainLift (u' r) z = intervalDomainLift (u₁ r) z
          rw [hsliceUL r hr]
        · rintro ⟨r, z⟩ hr
          show intervalDomainLift (u' r) z = intervalDomainLift (u₂ (r - τ)) z
          rw [hsliceUR r hr]
      · refine continuousOn_prod_glue hτT₁ hT'le ?_ ?_ h9₁.2 h9₂.2
        · rintro ⟨r, z⟩ hr
          show intervalDomainLift (v' r) z = intervalDomainLift (v₁ r) z
          rw [hsliceVL r hr]
        · rintro ⟨r, z⟩ hr
          show intervalDomainLift (v' r) z = intervalDomainLift (v₂ (r - τ)) z
          rw [hsliceVR r hr]
  · -- positivity of u'
    intro t x ht htT'
    by_cases hcase : t < T₁
    · rw [hsliceUL t hcase]; exact hposU₁ t x ht hcase
    · have hτt : τ < t := hnotL hcase
      rw [hsliceUR t hτt]
      exact hposU₂ (t - τ) x (by linarith) (by linarith)
  · -- nonnegativity of v'
    intro t x ht htT'
    by_cases hcase : t < T₁
    · rw [hsliceVL t hcase]; exact hnnV₁ t x ht hcase
    · have hτt : τ < t := hnotL hcase
      rw [hsliceVR t hτt]
      exact hnnV₂ (t - τ) x (by linarith) (by linarith)
  · -- PDE for u'
    intro t x ht htT' hx
    by_cases hcase : t < T₁
    · have hpde := hpdeU₁ t x ht hcase hx
      simp only [intervalDomain] at hpde ⊢
      show deriv (fun s => u' s x) t = _
      rw [hderivUL x hcase, hsliceUL t hcase, hsliceVL t hcase]
      exact hpde
    · have hτt : τ < t := hnotL hcase
      have hpde := hpdeU₂ (t - τ) x (by linarith) (by linarith) hx
      simp only [intervalDomain] at hpde ⊢
      show deriv (fun s => u' s x) t = _
      rw [hderivUR x hτt, hsliceUR t hτt, hsliceVR t hτt]
      exact hpde
  · -- elliptic PDE for v'
    intro t x ht htT' hx
    by_cases hcase : t < T₁
    · have hpde := hpdeV₁ t x ht hcase hx
      simp only [intervalDomain] at hpde ⊢
      rw [hsliceUL t hcase, hsliceVL t hcase]
      exact hpde
    · have hτt : τ < t := hnotL hcase
      have hpde := hpdeV₂ (t - τ) x (by linarith) (by linarith) hx
      simp only [intervalDomain] at hpde ⊢
      rw [hsliceUR t hτt, hsliceVR t hτt]
      exact hpde
  · -- Neumann boundary conditions
    intro t x ht htT' hx
    by_cases hcase : t < T₁
    · rw [hsliceUL t hcase, hsliceVL t hcase]
      exact hbc₁ t x ht hcase hx
    · have hτt : τ < t := hnotL hcase
      rw [hsliceUR t hτt, hsliceVR t hτt]
      exact hbc₂ (t - τ) x (by linarith) (by linarith) hx

/-- **hPCW: the splice of two classical solutions agreeing on the overlap
`(τ, T₁)` is a classical solution on any horizon `T' ≤ τ + T₂`.** -/
theorem piecewiseClassicalWorks (p : CM2Params) :
    PiecewiseGlue.PiecewiseClassicalWorks p := by
  intro T₁ T₂ τ hT₁ hT₂ hτ hτT₁ u₁ v₁ u₂ v₂ hsol₁ hsol₂ hovU hovV T' hT' hT'le
  exact splice_isClassical p hT₁ hT₂ hτ hτT₁ hsol₁ hsol₂ hovU hovV
    (fun _ _ => rfl) (fun _ _ => rfl) hT' hT'le

end ShenWork.Paper2.PiecewiseClassical
