import ShenWork.Paper1.WaveTrapProjectedCubeApproxData

namespace ShenWork.Paper1

open Set Filter Topology

noncomputable section

/-- Minimal concrete hypotheses on a profile trap needed by the compact-open
Schauder projection.  Compactness is requested only for the image of the map,
as in the classical compact-map version of Schauder's theorem. -/
structure BoundedConvexProfileTrapData
    (trap : (ℝ → ℝ) → Prop) (B : ℝ) : Prop where
  nonempty : ∃ u, trap u
  convex : Convex ℝ {u : ℝ → ℝ | trap u}
  continuous : ∀ u, trap u → Continuous u
  abs_le : ∀ u, trap u → ∀ x, |u x| ≤ B

/-- Restriction of the image of a profile-trap map to a compact interval. -/
def convexProfileImageRestrictSet
    (trap : (ℝ → ℝ) → Prop) (R : ℝ)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ u, trap u → trap (Tmap u))
    (hcont : ∀ u, trap u → Continuous u) :
    Set C(Set.Icc (-R) R, ℝ) :=
  {g | ∃ u, ∃ hu : trap u,
    g = profileRestrictIcc R (Tmap u) (hcont (Tmap u) (hmap u hu))}

/-- Sequential compactness of the compact-open image implies total
boundedness of each interval restriction. -/
theorem convexProfileImageRestrictSet_totallyBounded
    {trap : (ℝ → ℝ) → Prop} {R : ℝ}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, trap u → trap (Tmap u)}
    {hcont : ∀ u, trap u → Continuous u}
    (hR : 0 < R)
    (hcompact : LocalUniformSequentiallyCompactRange trap Tmap) :
    TotallyBounded
      (convexProfileImageRestrictSet trap R Tmap hmap hcont) := by
  apply totallyBounded_of_subseq_tendsto
  intro gseq hgseq
  choose u hu hgeq using hgseq
  rcases hcompact u hu with ⟨sub, hsub, U, hU, hconv⟩
  refine ⟨profileRestrictIcc R U (hcont U hU), sub, hsub, ?_⟩
  have htend := tendsto_profileRestrictIcc_of_locallyUniform
    (R := R) hR
    (seq := fun n => Tmap (u (sub n))) (u := U)
    (fun n => hcont (Tmap (u (sub n))) (hmap (u (sub n)) (hu (sub n))))
    (hcont U hU) hconv
  exact htend.congr' (Eventually.of_forall fun n => by
    simpa [profileRestrictIcc] using (hgeq (sub n)).symm)

theorem exists_finite_eps_net_convexProfileImageRestrict
    {trap : (ℝ → ℝ) → Prop} {R ε : ℝ}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, trap u → trap (Tmap u)}
    {hcont : ∀ u, trap u → Continuous u}
    (hR : 0 < R) (hε : 0 < ε)
    (hcompact : LocalUniformSequentiallyCompactRange trap Tmap) :
    ∃ s ⊆ convexProfileImageRestrictSet trap R Tmap hmap hcont,
      s.Finite ∧
        convexProfileImageRestrictSet trap R Tmap hmap hcont ⊆
          ⋃ x ∈ s, Metric.ball x ε :=
  Metric.finite_approx_of_totallyBounded
    (convexProfileImageRestrictSet_totallyBounded hR hcompact) ε hε

lemma convexProfileImageRestrictSet_fullRep
    {trap : (ℝ → ℝ) → Prop} {R : ℝ}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, trap u → trap (Tmap u)}
    {hcont : ∀ u, trap u → Continuous u}
    {g : C(Set.Icc (-R) R, ℝ)}
    (hg : g ∈ convexProfileImageRestrictSet trap R Tmap hmap hcont) :
    ∃ v, ∃ hv : trap v,
      g = profileRestrictIcc R v (hcont v hv) := by
  rcases hg with ⟨u, hu, rfl⟩
  exact ⟨Tmap u, hmap u hu, rfl⟩

noncomputable def convexProfileImageFullProfile
    {trap : (ℝ → ℝ) → Prop} {R : ℝ}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, trap u → trap (Tmap u)}
    {hcont : ∀ u, trap u → Continuous u}
    (g : C(Set.Icc (-R) R, ℝ))
    (hg : g ∈ convexProfileImageRestrictSet trap R Tmap hmap hcont) :
    ℝ → ℝ :=
  Classical.choose (convexProfileImageRestrictSet_fullRep hg)

lemma convexProfileImageFullProfile_trap
    {trap : (ℝ → ℝ) → Prop} {R : ℝ}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, trap u → trap (Tmap u)}
    {hcont : ∀ u, trap u → Continuous u}
    (g : C(Set.Icc (-R) R, ℝ))
    (hg : g ∈ convexProfileImageRestrictSet trap R Tmap hmap hcont) :
    trap (convexProfileImageFullProfile g hg) :=
  Classical.choose (Classical.choose_spec
    (convexProfileImageRestrictSet_fullRep hg))

lemma convexProfileImageFullProfile_restrict
    {trap : (ℝ → ℝ) → Prop} {R : ℝ}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, trap u → trap (Tmap u)}
    {hcont : ∀ u, trap u → Continuous u}
    (g : C(Set.Icc (-R) R, ℝ))
    (hg : g ∈ convexProfileImageRestrictSet trap R Tmap hmap hcont) :
    g = profileRestrictIcc R (convexProfileImageFullProfile g hg)
      (hcont _ (convexProfileImageFullProfile_trap g hg)) :=
  Classical.choose_spec (Classical.choose_spec
    (convexProfileImageRestrictSet_fullRep hg))

noncomputable def convexProfileRawNet
    (trap : (ℝ → ℝ) → Prop)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ u, trap u → trap (Tmap u))
    (hcont : ∀ u, trap u → Continuous u)
    (hcompact : LocalUniformSequentiallyCompactRange trap Tmap)
    (N : ℕ) :
    Set C(Set.Icc (-(projectedCubeRadius N)) (projectedCubeRadius N), ℝ) :=
  Classical.choose
    (exists_finite_eps_net_convexProfileImageRestrict
      (trap := trap) (Tmap := Tmap) (hmap := hmap) (hcont := hcont)
      (projectedCubeRadius_pos N) (projectedCubeNetRadius_pos N) hcompact)

lemma convexProfileRawNet_subset
    {trap : (ℝ → ℝ) → Prop}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, trap u → trap (Tmap u)}
    {hcont : ∀ u, trap u → Continuous u}
    {hcompact : LocalUniformSequentiallyCompactRange trap Tmap}
    (N : ℕ) :
    convexProfileRawNet trap Tmap hmap hcont hcompact N ⊆
      convexProfileImageRestrictSet trap (projectedCubeRadius N)
        Tmap hmap hcont :=
  (Classical.choose_spec
    (exists_finite_eps_net_convexProfileImageRestrict
      (trap := trap) (Tmap := Tmap) (hmap := hmap) (hcont := hcont)
      (projectedCubeRadius_pos N) (projectedCubeNetRadius_pos N) hcompact)).1

lemma convexProfileRawNet_finite
    {trap : (ℝ → ℝ) → Prop}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, trap u → trap (Tmap u)}
    {hcont : ∀ u, trap u → Continuous u}
    {hcompact : LocalUniformSequentiallyCompactRange trap Tmap}
    (N : ℕ) :
    (convexProfileRawNet trap Tmap hmap hcont hcompact N).Finite :=
  (Classical.choose_spec
    (exists_finite_eps_net_convexProfileImageRestrict
      (trap := trap) (Tmap := Tmap) (hmap := hmap) (hcont := hcont)
      (projectedCubeRadius_pos N) (projectedCubeNetRadius_pos N) hcompact)).2.1

lemma convexProfileRawNet_covers
    {trap : (ℝ → ℝ) → Prop}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, trap u → trap (Tmap u)}
    {hcont : ∀ u, trap u → Continuous u}
    {hcompact : LocalUniformSequentiallyCompactRange trap Tmap}
    (N : ℕ) :
    convexProfileImageRestrictSet trap (projectedCubeRadius N)
        Tmap hmap hcont ⊆
      ⋃ x ∈ convexProfileRawNet trap Tmap hmap hcont hcompact N,
        Metric.ball x (projectedCubeNetRadius N) :=
  (Classical.choose_spec
    (exists_finite_eps_net_convexProfileImageRestrict
      (trap := trap) (Tmap := Tmap) (hmap := hmap) (hcont := hcont)
      (projectedCubeRadius_pos N) (projectedCubeNetRadius_pos N) hcompact)).2.2

noncomputable def convexProfileBaseCenter
    (trap : (ℝ → ℝ) → Prop)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ u, trap u → trap (Tmap u))
    (hcont : ∀ u, trap u → Continuous u)
    (hne : ∃ u, trap u) (N : ℕ) :
    C(Set.Icc (-(projectedCubeRadius N)) (projectedCubeRadius N), ℝ) :=
  let u := Classical.choose hne
  let hu := Classical.choose_spec hne
  profileRestrictIcc (projectedCubeRadius N) (Tmap u)
    (hcont (Tmap u) (hmap u hu))

lemma convexProfileBaseCenter_mem
    {trap : (ℝ → ℝ) → Prop}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, trap u → trap (Tmap u)}
    {hcont : ∀ u, trap u → Continuous u}
    {hne : ∃ u, trap u} (N : ℕ) :
    convexProfileBaseCenter trap Tmap hmap hcont hne N ∈
      convexProfileImageRestrictSet trap (projectedCubeRadius N)
        Tmap hmap hcont := by
  exact ⟨Classical.choose hne, Classical.choose_spec hne, rfl⟩

noncomputable def convexProfileNetSet
    (trap : (ℝ → ℝ) → Prop)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ u, trap u → trap (Tmap u))
    (hcont : ∀ u, trap u → Continuous u)
    (hne : ∃ u, trap u)
    (hcompact : LocalUniformSequentiallyCompactRange trap Tmap)
    (N : ℕ) :=
  convexProfileRawNet trap Tmap hmap hcont hcompact N ∪
    {convexProfileBaseCenter trap Tmap hmap hcont hne N}

lemma convexProfileNetSet_subset
    {trap : (ℝ → ℝ) → Prop}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, trap u → trap (Tmap u)}
    {hcont : ∀ u, trap u → Continuous u}
    {hne : ∃ u, trap u}
    {hcompact : LocalUniformSequentiallyCompactRange trap Tmap}
    (N : ℕ) :
    convexProfileNetSet trap Tmap hmap hcont hne hcompact N ⊆
      convexProfileImageRestrictSet trap (projectedCubeRadius N)
        Tmap hmap hcont := by
  intro g hg
  rcases hg with hg | hg
  · exact convexProfileRawNet_subset N hg
  · have : g = convexProfileBaseCenter trap Tmap hmap hcont hne N := by
      simpa using hg
    simpa [this] using
      (convexProfileBaseCenter_mem
        (hmap := hmap) (hcont := hcont) (hne := hne) N)

lemma convexProfileNetSet_finite
    {trap : (ℝ → ℝ) → Prop}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, trap u → trap (Tmap u)}
    {hcont : ∀ u, trap u → Continuous u}
    {hne : ∃ u, trap u}
    {hcompact : LocalUniformSequentiallyCompactRange trap Tmap}
    (N : ℕ) :
    (convexProfileNetSet trap Tmap hmap hcont hne hcompact N).Finite :=
  (convexProfileRawNet_finite
    (hmap := hmap) (hcont := hcont) (hcompact := hcompact) N).union
      (Set.finite_singleton _)

lemma convexProfileNetSet_nonempty
    {trap : (ℝ → ℝ) → Prop}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, trap u → trap (Tmap u)}
    {hcont : ∀ u, trap u → Continuous u}
    {hne : ∃ u, trap u}
    {hcompact : LocalUniformSequentiallyCompactRange trap Tmap}
    (N : ℕ) :
    (convexProfileNetSet trap Tmap hmap hcont hne hcompact N).Nonempty :=
  ⟨convexProfileBaseCenter trap Tmap hmap hcont hne N, Or.inr rfl⟩

lemma convexProfileNetSet_covers
    {trap : (ℝ → ℝ) → Prop}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, trap u → trap (Tmap u)}
    {hcont : ∀ u, trap u → Continuous u}
    {hne : ∃ u, trap u}
    {hcompact : LocalUniformSequentiallyCompactRange trap Tmap}
    (N : ℕ) :
    convexProfileImageRestrictSet trap (projectedCubeRadius N)
        Tmap hmap hcont ⊆
      ⋃ x ∈ convexProfileNetSet trap Tmap hmap hcont hne hcompact N,
        Metric.ball x (projectedCubeNetRadius N) := by
  intro g hg
  rcases Set.mem_iUnion₂.mp
      (convexProfileRawNet_covers
        (hmap := hmap) (hcont := hcont) (hcompact := hcompact) N hg) with
    ⟨x, hx, hball⟩
  exact Set.mem_iUnion₂.mpr ⟨x, Or.inl hx, hball⟩

noncomputable def convexProfileNetIndex
    (trap : (ℝ → ℝ) → Prop)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ u, trap u → trap (Tmap u))
    (hcont : ∀ u, trap u → Continuous u)
    (hne : ∃ u, trap u)
    (hcompact : LocalUniformSequentiallyCompactRange trap Tmap)
    (N : ℕ) : Type :=
  {g : C(Set.Icc (-(projectedCubeRadius N)) (projectedCubeRadius N), ℝ) //
    g ∈ convexProfileNetSet trap Tmap hmap hcont hne hcompact N}

instance convexProfileNetIndex_fintype
    (trap : (ℝ → ℝ) → Prop)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ u, trap u → trap (Tmap u))
    (hcont : ∀ u, trap u → Continuous u)
    (hne : ∃ u, trap u)
    (hcompact : LocalUniformSequentiallyCompactRange trap Tmap)
    (N : ℕ) :
    Fintype (convexProfileNetIndex trap Tmap hmap hcont hne hcompact N) :=
  Set.Finite.fintype
    (convexProfileNetSet_finite
      (hmap := hmap) (hcont := hcont) (hne := hne)
      (hcompact := hcompact) N)

instance convexProfileNetIndex_nonempty
    (trap : (ℝ → ℝ) → Prop)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ u, trap u → trap (Tmap u))
    (hcont : ∀ u, trap u → Continuous u)
    (hne : ∃ u, trap u)
    (hcompact : LocalUniformSequentiallyCompactRange trap Tmap)
    (N : ℕ) :
    Nonempty (convexProfileNetIndex trap Tmap hmap hcont hne hcompact N) :=
  let hne' := convexProfileNetSet_nonempty
    (hmap := hmap) (hcont := hcont) (hne := hne)
    (hcompact := hcompact) N
  ⟨⟨Classical.choose hne', Classical.choose_spec hne'⟩⟩

noncomputable def convexProfileDim
    (trap : (ℝ → ℝ) → Prop)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ u, trap u → trap (Tmap u))
    (hcont : ∀ u, trap u → Continuous u)
    (hne : ∃ u, trap u)
    (hcompact : LocalUniformSequentiallyCompactRange trap Tmap)
    (N : ℕ) : ℕ :=
  Fintype.card
    (convexProfileNetIndex trap Tmap hmap hcont hne hcompact N)

noncomputable def convexProfileIndexEquiv
    (trap : (ℝ → ℝ) → Prop)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ u, trap u → trap (Tmap u))
    (hcont : ∀ u, trap u → Continuous u)
    (hne : ∃ u, trap u)
    (hcompact : LocalUniformSequentiallyCompactRange trap Tmap)
    (N : ℕ) :
    convexProfileNetIndex trap Tmap hmap hcont hne hcompact N ≃
      Fin (convexProfileDim trap Tmap hmap hcont hne hcompact N) :=
  Fintype.equivFin _

noncomputable def convexProfileAnchor
    (trap : (ℝ → ℝ) → Prop)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ u, trap u → trap (Tmap u))
    (hcont : ∀ u, trap u → Continuous u)
    (hne : ∃ u, trap u)
    (hcompact : LocalUniformSequentiallyCompactRange trap Tmap)
    (N : ℕ) :
    Fin (convexProfileDim trap Tmap hmap hcont hne hcompact N) →
      C(Set.Icc (-(projectedCubeRadius N)) (projectedCubeRadius N), ℝ) :=
  fun i =>
    ((convexProfileIndexEquiv trap Tmap hmap hcont hne hcompact N).symm i).1

lemma convexProfileAnchor_mem
    {trap : (ℝ → ℝ) → Prop}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, trap u → trap (Tmap u)}
    {hcont : ∀ u, trap u → Continuous u}
    {hne : ∃ u, trap u}
    {hcompact : LocalUniformSequentiallyCompactRange trap Tmap}
    (N : ℕ)
    (i : Fin (convexProfileDim trap Tmap hmap hcont hne hcompact N)) :
    convexProfileAnchor trap Tmap hmap hcont hne hcompact N i ∈
      convexProfileImageRestrictSet trap (projectedCubeRadius N)
        Tmap hmap hcont :=
  convexProfileNetSet_subset
    (hmap := hmap) (hcont := hcont) (hne := hne)
    (hcompact := hcompact) N
    (((convexProfileIndexEquiv trap Tmap hmap hcont hne hcompact N).symm i).2)

noncomputable def convexProfileCenter
    (trap : (ℝ → ℝ) → Prop)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ u, trap u → trap (Tmap u))
    (hcont : ∀ u, trap u → Continuous u)
    (hne : ∃ u, trap u)
    (hcompact : LocalUniformSequentiallyCompactRange trap Tmap)
    (N : ℕ)
    (i : Fin (convexProfileDim trap Tmap hmap hcont hne hcompact N)) :
    ℝ → ℝ :=
  convexProfileImageFullProfile
    (convexProfileAnchor trap Tmap hmap hcont hne hcompact N i)
    (convexProfileAnchor_mem
      (hmap := hmap) (hcont := hcont) (hne := hne)
      (hcompact := hcompact) N i)

lemma convexProfileCenter_trap
    {trap : (ℝ → ℝ) → Prop}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, trap u → trap (Tmap u)}
    {hcont : ∀ u, trap u → Continuous u}
    {hne : ∃ u, trap u}
    {hcompact : LocalUniformSequentiallyCompactRange trap Tmap}
    (N : ℕ)
    (i : Fin (convexProfileDim trap Tmap hmap hcont hne hcompact N)) :
    trap (convexProfileCenter trap Tmap hmap hcont hne hcompact N i) :=
  convexProfileImageFullProfile_trap
    (convexProfileAnchor trap Tmap hmap hcont hne hcompact N i)
    (convexProfileAnchor_mem
      (hmap := hmap) (hcont := hcont) (hne := hne)
      (hcompact := hcompact) N i)

lemma convexProfileCenter_restrict
    {trap : (ℝ → ℝ) → Prop}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, trap u → trap (Tmap u)}
    {hcont : ∀ u, trap u → Continuous u}
    {hne : ∃ u, trap u}
    {hcompact : LocalUniformSequentiallyCompactRange trap Tmap}
    (N : ℕ)
    (i : Fin (convexProfileDim trap Tmap hmap hcont hne hcompact N)) :
    convexProfileAnchor trap Tmap hmap hcont hne hcompact N i =
      profileRestrictIcc (projectedCubeRadius N)
        (convexProfileCenter trap Tmap hmap hcont hne hcompact N i)
        (hcont _ (convexProfileCenter_trap
          (hmap := hmap) (hcont := hcont) (hne := hne)
          (hcompact := hcompact) N i)) :=
  convexProfileImageFullProfile_restrict
    (convexProfileAnchor trap Tmap hmap hcont hne hcompact N i)
    (convexProfileAnchor_mem
      (hmap := hmap) (hcont := hcont) (hne := hne)
      (hcompact := hcompact) N i)

lemma convexProfileRestrictIf_mem_image_of_map
    {trap : (ℝ → ℝ) → Prop}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, trap u → trap (Tmap u)}
    {hcont : ∀ u, trap u → Continuous u}
    (N : ℕ) {u : ℝ → ℝ} (hu : trap u) :
    profileRestrictIccIf (projectedCubeRadius N) (Tmap u) ∈
      convexProfileImageRestrictSet trap (projectedCubeRadius N)
        Tmap hmap hcont := by
  rw [profileRestrictIccIf_eq _ (hcont _ (hmap u hu))]
  exact ⟨u, hu, rfl⟩

lemma convexProfileBumpSum_pos_of_mem_image
    {trap : (ℝ → ℝ) → Prop}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, trap u → trap (Tmap u)}
    {hcont : ∀ u, trap u → Continuous u}
    {hne : ∃ u, trap u}
    {hcompact : LocalUniformSequentiallyCompactRange trap Tmap}
    (N : ℕ)
    {g : C(Set.Icc (-(projectedCubeRadius N)) (projectedCubeRadius N), ℝ)}
    (hg : g ∈ convexProfileImageRestrictSet trap (projectedCubeRadius N)
      Tmap hmap hcont) :
    0 < schauderBumpSum (projectedCubeNetRadius N)
      (convexProfileAnchor trap Tmap hmap hcont hne hcompact N) g := by
  rcases Set.mem_iUnion₂.mp
      (convexProfileNetSet_covers
        (hmap := hmap) (hcont := hcont) (hne := hne)
        (hcompact := hcompact) N hg) with ⟨y, hy, hball⟩
  let j : convexProfileNetIndex trap Tmap hmap hcont hne hcompact N :=
    ⟨y, hy⟩
  let i : Fin (convexProfileDim trap Tmap hmap hcont hne hcompact N) :=
    convexProfileIndexEquiv trap Tmap hmap hcont hne hcompact N j
  have hanchor :
      convexProfileAnchor trap Tmap hmap hcont hne hcompact N i = y := by
    simp [convexProfileAnchor, convexProfileIndexEquiv, i, j]
  have hball' : g ∈ Metric.ball
      (convexProfileAnchor trap Tmap hmap hcont hne hcompact N i)
      (projectedCubeNetRadius N) := by
    simpa [hanchor] using hball
  exact schauderBumpSum_pos_of_mem_ball hball'

lemma convexProfileDim_pos
    {trap : (ℝ → ℝ) → Prop}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, trap u → trap (Tmap u)}
    {hcont : ∀ u, trap u → Continuous u}
    {hne : ∃ u, trap u}
    {hcompact : LocalUniformSequentiallyCompactRange trap Tmap}
    (N : ℕ) :
    0 < convexProfileDim trap Tmap hmap hcont hne hcompact N := by
  unfold convexProfileDim
  exact Fintype.card_pos

noncomputable def convexProfileCoordTol
    (trap : (ℝ → ℝ) → Prop) (B : ℝ)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ u, trap u → trap (Tmap u))
    (hcont : ∀ u, trap u → Continuous u)
    (hne : ∃ u, trap u)
    (hcompact : LocalUniformSequentiallyCompactRange trap Tmap)
    (N : ℕ) : ℝ :=
  projectedCubeNetRadius N /
    ((16 : ℝ) *
      (convexProfileDim trap Tmap hmap hcont hne hcompact N + 1 : ℝ) ^ 2 *
        (B + 1))

lemma convexProfileCoordTol_pos
    {trap : (ℝ → ℝ) → Prop} {B : ℝ}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, trap u → trap (Tmap u)}
    {hcont : ∀ u, trap u → Continuous u}
    {hne : ∃ u, trap u}
    {hcompact : LocalUniformSequentiallyCompactRange trap Tmap}
    (hB : 0 ≤ B) (N : ℕ) :
    0 < convexProfileCoordTol trap B Tmap hmap hcont hne hcompact N := by
  unfold convexProfileCoordTol
  have hden : 0 < (16 : ℝ) *
      (convexProfileDim trap Tmap hmap hcont hne hcompact N + 1 : ℝ) ^ 2 *
        (B + 1) := by
    have hd : 0 <
        (convexProfileDim trap Tmap hmap hcont hne hcompact N + 1 : ℝ) := by
      positivity
    have hB1 : 0 < B + 1 := by linarith
    positivity
  exact div_pos (projectedCubeNetRadius_pos N) hden

noncomputable def convexProfileProj
    (trap : (ℝ → ℝ) → Prop) (B : ℝ)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ u, trap u → trap (Tmap u))
    (hcont : ∀ u, trap u → Continuous u)
    (hne : ∃ u, trap u)
    (hcompact : LocalUniformSequentiallyCompactRange trap Tmap)
    (N : ℕ) (u : ℝ → ℝ) :
    Fin (convexProfileDim trap Tmap hmap hcont hne hcompact N) → ℝ :=
  fun i => schauderBumpWeight (projectedCubeNetRadius N)
    (convexProfileAnchor trap Tmap hmap hcont hne hcompact N)
    (profileRestrictIccIf (projectedCubeRadius N) u) i

lemma convexProfileProj_mem_unitCube
    {trap : (ℝ → ℝ) → Prop} {B : ℝ}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, trap u → trap (Tmap u)}
    {hcont : ∀ u, trap u → Continuous u}
    {hne : ∃ u, trap u}
    {hcompact : LocalUniformSequentiallyCompactRange trap Tmap}
    (N : ℕ) (u : ℝ → ℝ) :
    convexProfileProj trap B Tmap hmap hcont hne hcompact N u ∈
      Freudenthal.unitCube
        (convexProfileDim trap Tmap hmap hcont hne hcompact N) :=
  schauderBumpWeightFin_mem_unitCube (projectedCubeNetRadius N)
    (convexProfileAnchor trap Tmap hmap hcont hne hcompact N)
    (profileRestrictIccIf (projectedCubeRadius N) u)

noncomputable def convexProfileLift
    (trap : (ℝ → ℝ) → Prop) (B : ℝ)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ u, trap u → trap (Tmap u))
    (hcont : ∀ u, trap u → Continuous u)
    (hne : ∃ u, trap u)
    (hcompact : LocalUniformSequentiallyCompactRange trap Tmap)
    (N : ℕ)
    (a : Fin (convexProfileDim trap Tmap hmap hcont hne hcompact N) → ℝ) :
    ℝ → ℝ :=
  ∑ i : Fin (convexProfileDim trap Tmap hmap hcont hne hcompact N),
    smoothCubeWeight
      (convexProfileCoordTol trap B Tmap hmap hcont hne hcompact N) a i •
        convexProfileCenter trap Tmap hmap hcont hne hcompact N i

lemma convexProfileLift_trap
    {trap : (ℝ → ℝ) → Prop} {B : ℝ}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, trap u → trap (Tmap u)}
    {hcompact : LocalUniformSequentiallyCompactRange trap Tmap}
    (data : BoundedConvexProfileTrapData trap B)
    (N : ℕ)
    {a : Fin (convexProfileDim trap Tmap hmap data.continuous
      data.nonempty hcompact N) → ℝ}
    (ha : a ∈ Freudenthal.unitCube
      (convexProfileDim trap Tmap hmap data.continuous
        data.nonempty hcompact N)) :
    trap (convexProfileLift trap B Tmap hmap data.continuous
      data.nonempty hcompact N a) := by
  have hB : 0 ≤ B :=
    le_trans (abs_nonneg _)
      (data.abs_le (Classical.choose data.nonempty)
        (Classical.choose_spec data.nonempty) 0)
  have hc : 0 < convexProfileCoordTol trap B Tmap hmap data.continuous
      data.nonempty hcompact N :=
    convexProfileCoordTol_pos (B := B) (hmap := hmap)
      (hcont := data.continuous) (hne := data.nonempty)
      (hcompact := hcompact) hB N
  exact data.convex.sum_mem
    (t := Finset.univ)
    (fun i _ => smoothCubeWeight_nonneg hc ha i)
    (by simpa using (smoothCubeWeight_sum_eq_one hc ha
      (convexProfileDim_pos (hmap := hmap) (hcont := data.continuous)
        (hne := data.nonempty) (hcompact := hcompact) N)))
    (fun i _ => convexProfileCenter_trap
      (hmap := hmap) (hcont := data.continuous) (hne := data.nonempty)
      (hcompact := hcompact) N i)

theorem convexProfileLift_locallyUniform_of_tendsto
    {trap : (ℝ → ℝ) → Prop} {B : ℝ}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, trap u → trap (Tmap u)}
    {hcompact : LocalUniformSequentiallyCompactRange trap Tmap}
    (data : BoundedConvexProfileTrapData trap B)
    (N : ℕ)
    {seq : ℕ → Fin (convexProfileDim trap Tmap hmap data.continuous
      data.nonempty hcompact N) → ℝ}
    {a : Fin (convexProfileDim trap Tmap hmap data.continuous
      data.nonempty hcompact N) → ℝ}
    (hseq : Tendsto seq atTop (𝓝 a))
    (ha : a ∈ Freudenthal.unitCube
      (convexProfileDim trap Tmap hmap data.continuous
        data.nonempty hcompact N)) :
    LocallyUniformConverges
      (fun n => convexProfileLift trap B Tmap hmap data.continuous
        data.nonempty hcompact N (seq n))
      (convexProfileLift trap B Tmap hmap data.continuous
        data.nonempty hcompact N a) := by
  intro R _hR ε hε
  let c := convexProfileCoordTol trap B Tmap hmap data.continuous
    data.nonempty hcompact N
  let d := convexProfileDim trap Tmap hmap data.continuous
    data.nonempty hcompact N
  have hB : 0 ≤ B :=
    le_trans (abs_nonneg _)
      (data.abs_le (Classical.choose data.nonempty)
        (Classical.choose_spec data.nonempty) 0)
  have hc : 0 < c := by
    dsimp [c]
    exact convexProfileCoordTol_pos (B := B) (hmap := hmap)
      (hcont := data.continuous) (hne := data.nonempty)
      (hcompact := hcompact) hB N
  have hd : 0 < d := by
    dsimp [d]
    exact convexProfileDim_pos (hmap := hmap) (hcont := data.continuous)
      (hne := data.nonempty) (hcompact := hcompact) N
  have hS_tend : Tendsto
      (fun n => ∑ i : Fin d,
        |smoothCubeWeight c (seq n) i - smoothCubeWeight c a i|)
      atTop (𝓝 0) :=
    tendsto_smoothCubeWeight_abs_sum (n := d) (c := c) hseq hc ha hd
  have hdenpos : 0 < B + 1 := by linarith
  have hδ : 0 < ε / (B + 1) := div_pos hε hdenpos
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.mp hS_tend
    (ε / (B + 1)) hδ
  filter_upwards [eventually_atTop.mpr ⟨N0, hN0⟩] with n hn x _hx
  let S : ℝ := ∑ i : Fin d,
    |smoothCubeWeight c (seq n) i - smoothCubeWeight c a i|
  have hS_nonneg : 0 ≤ S := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hS_lt : S < ε / (B + 1) := by
    have hdist := hn
    have habs : |S - 0| < ε / (B + 1) := by
      simpa [Real.dist_eq, S, d, c] using hdist
    simpa [sub_zero, abs_of_nonneg hS_nonneg] using habs
  have hcenter : ∀ i : Fin d,
      |convexProfileCenter trap Tmap hmap data.continuous
        data.nonempty hcompact N i x| ≤ B := by
    intro i
    exact data.abs_le _
      (convexProfileCenter_trap
        (hmap := hmap) (hcont := data.continuous) (hne := data.nonempty)
        (hcompact := hcompact) N i) x
  have hbound :
      |convexProfileLift trap B Tmap hmap data.continuous
          data.nonempty hcompact N (seq n) x -
        convexProfileLift trap B Tmap hmap data.continuous
          data.nonempty hcompact N a x| ≤ B * S := by
    simpa [convexProfileLift, S, c, d] using
      abs_finset_weighted_profile_sum_sub_le
        (w := fun i : Fin d => smoothCubeWeight c (seq n) i)
        (v := fun i : Fin d => smoothCubeWeight c a i)
        (center := convexProfileCenter trap Tmap hmap data.continuous
          data.nonempty hcompact N) (M := B) (x := x) hcenter
  have hBsum_le : B * S ≤ (B + 1) * S := by
    nlinarith [hB, hS_nonneg]
  have hsmall : (B + 1) * S < ε := by
    have hmul := mul_lt_mul_of_pos_left hS_lt hdenpos
    have hright : (B + 1) * (ε / (B + 1)) = ε := by
      field_simp [ne_of_gt hdenpos]
    simpa [hright] using hmul
  exact lt_of_le_of_lt hbound (lt_of_le_of_lt hBsum_le hsmall)

theorem convexProfileTfin_continuousOn
    {trap : (ℝ → ℝ) → Prop} {B : ℝ}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, trap u → trap (Tmap u)}
    {hcompact : LocalUniformSequentiallyCompactRange trap Tmap}
    (data : BoundedConvexProfileTrapData trap B)
    (hTcont : LocalUniformContinuousOn trap Tmap)
    (N : ℕ) :
    ContinuousOn
      (fun a => convexProfileProj trap B Tmap hmap data.continuous
        data.nonempty hcompact N
          (Tmap (convexProfileLift trap B Tmap hmap data.continuous
            data.nonempty hcompact N a)))
      (Freudenthal.unitCube
        (convexProfileDim trap Tmap hmap data.continuous
          data.nonempty hcompact N)) := by
  rw [continuousOn_iff_continuous_restrict]
  rw [continuous_iff_continuousAt]
  intro a0
  rw [ContinuousAt, tendsto_nhds_iff_seq_tendsto]
  intro seq hseq
  rw [tendsto_pi_nhds]
  intro i
  let d := convexProfileDim trap Tmap hmap data.continuous
    data.nonempty hcompact N
  let R := projectedCubeRadius N
  let eta := projectedCubeNetRadius N
  let anchor := convexProfileAnchor trap Tmap hmap data.continuous
    data.nonempty hcompact N
  let lift := convexProfileLift trap B Tmap hmap data.continuous
    data.nonempty hcompact N
  have hseq_val : Tendsto (fun n : ℕ => (seq n : Fin d → ℝ)) atTop
      (𝓝 (a0 : Fin d → ℝ)) :=
    (continuous_subtype_val.tendsto a0).comp hseq
  have hlift : LocallyUniformConverges (fun n => lift (seq n))
      (lift a0) := by
    simpa [lift, d] using
      convexProfileLift_locallyUniform_of_tendsto data N hseq_val a0.2
  have htrap_seq : ∀ n, trap (lift (seq n)) := by
    intro n
    simpa [lift, d] using
      convexProfileLift_trap data N (seq n).2
  have htrap_a : trap (lift a0) := by
    simpa [lift, d] using convexProfileLift_trap data N a0.2
  have hT : LocallyUniformConverges
      (fun n => Tmap (lift (seq n))) (Tmap (lift a0)) :=
    hTcont _ _ htrap_seq htrap_a hlift
  have hrest : Tendsto
      (fun n => profileRestrictIcc R (Tmap (lift (seq n)))
        (data.continuous _ (hmap _ (htrap_seq n)))) atTop
      (𝓝 (profileRestrictIcc R (Tmap (lift a0))
        (data.continuous _ (hmap _ htrap_a)))) :=
    tendsto_profileRestrictIcc_of_locallyUniform
      (R := R) (seq := fun n => Tmap (lift (seq n)))
      (u := Tmap (lift a0)) (projectedCubeRadius_pos N)
      (fun n => data.continuous _ (hmap _ (htrap_seq n)))
      (data.continuous _ (hmap _ htrap_a)) hT
  have hif : Tendsto
      (fun n => profileRestrictIccIf R (Tmap (lift (seq n)))) atTop
      (𝓝 (profileRestrictIccIf R (Tmap (lift a0)))) := by
    have heq :
        (fun n => profileRestrictIcc R (Tmap (lift (seq n)))
          (data.continuous _ (hmap _ (htrap_seq n)))) =ᶠ[atTop]
        (fun n => profileRestrictIccIf R (Tmap (lift (seq n)))) :=
      Eventually.of_forall fun n =>
        (profileRestrictIccIf_eq R
          (data.continuous _ (hmap _ (htrap_seq n)))).symm
    have hlim : profileRestrictIccIf R (Tmap (lift a0)) =
        profileRestrictIcc R (Tmap (lift a0))
          (data.continuous _ (hmap _ htrap_a)) :=
      profileRestrictIccIf_eq R (data.continuous _ (hmap _ htrap_a))
    exact Tendsto.congr' heq (by simpa [hlim] using hrest)
  have hmem : profileRestrictIccIf R (Tmap (lift a0)) ∈
      convexProfileImageRestrictSet trap R Tmap hmap data.continuous := by
    simpa [R] using convexProfileRestrictIf_mem_image_of_map
      (hmap := hmap) (hcont := data.continuous) N htrap_a
  have hsum : 0 < schauderBumpSum eta anchor
      (profileRestrictIccIf R (Tmap (lift a0))) := by
    simpa [eta, anchor, R] using convexProfileBumpSum_pos_of_mem_image
      (hmap := hmap) (hcont := data.continuous) (hne := data.nonempty)
      (hcompact := hcompact) N hmem
  simpa [convexProfileProj, eta, anchor, R, lift, d] using
    tendsto_schauderBumpWeight_of_sum_pos
      (xseq := fun n => profileRestrictIccIf R (Tmap (lift (seq n))))
      (x := profileRestrictIccIf R (Tmap (lift a0))) hif hsum i

theorem convexProfilePartition_error_le
    {trap : (ℝ → ℝ) → Prop} {B : ℝ}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, trap u → trap (Tmap u)}
    {hcompact : LocalUniformSequentiallyCompactRange trap Tmap}
    (data : BoundedConvexProfileTrapData trap B)
    (N : ℕ) {u : ℝ → ℝ} (hu : trap u)
    {x : ℝ} (hx : x ∈ Set.Icc
      (-(projectedCubeRadius N)) (projectedCubeRadius N)) :
    |Tmap u x -
      (∑ i : Fin (convexProfileDim trap Tmap hmap data.continuous
          data.nonempty hcompact N),
        convexProfileProj trap B Tmap hmap data.continuous data.nonempty
          hcompact N (Tmap u) i •
        convexProfileCenter trap Tmap hmap data.continuous data.nonempty
          hcompact N i) x| ≤ projectedCubeNetRadius N := by
  let d := convexProfileDim trap Tmap hmap data.continuous
    data.nonempty hcompact N
  let R := projectedCubeRadius N
  let eta := projectedCubeNetRadius N
  let anchor := convexProfileAnchor trap Tmap hmap data.continuous
    data.nonempty hcompact N
  let p := convexProfileProj trap B Tmap hmap data.continuous
    data.nonempty hcompact N (Tmap u)
  let center := convexProfileCenter trap Tmap hmap data.continuous
    data.nonempty hcompact N
  let g := profileRestrictIccIf R (Tmap u)
  have hmem : g ∈ convexProfileImageRestrictSet trap R Tmap hmap
      data.continuous := by
    simpa [g, R] using convexProfileRestrictIf_mem_image_of_map
      (hmap := hmap) (hcont := data.continuous) N hu
  have hsum_pos : 0 < schauderBumpSum eta anchor g := by
    simpa [eta, anchor, g, R] using convexProfileBumpSum_pos_of_mem_image
      (hmap := hmap) (hcont := data.continuous) (hne := data.nonempty)
      (hcompact := hcompact) N hmem
  have hp_sum : ∑ i : Fin d, p i = 1 := by
    simpa [p, convexProfileProj, eta, anchor, g, R, d] using
      sum_schauderBumpWeight_of_sum_pos hsum_pos
  have hp_nonneg : ∀ i : Fin d, 0 ≤ p i := by
    intro i
    simpa [p, convexProfileProj, eta, anchor, g, R, d] using
      schauderBumpWeight_nonneg eta anchor g i
  have hterm : ∀ i : Fin d,
      p i * |Tmap u x - center i x| ≤ p i * eta := by
    intro i
    by_cases hpi : p i = 0
    · simp [hpi]
    · have hpi_pos : 0 < p i := lt_of_le_of_ne (hp_nonneg i) (Ne.symm hpi)
      have hdist_fun : dist g (anchor i) < eta := by
        have hdist := dist_lt_of_schauderBumpWeight_pos
          (ε := eta) (center := anchor) (x := g) (i := i) hsum_pos
        have hp_eq : schauderBumpWeight eta anchor g i = p i := by
          simp [p, convexProfileProj, eta, anchor, g, R, d]
        exact hdist (by simpa [hp_eq] using hpi_pos)
      let xR : Set.Icc (-R) R := ⟨x, by simpa [R] using hx⟩
      have hpoint : dist (g xR) (anchor i xR) < eta :=
        lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist xR) hdist_fun
      have hg_apply : g xR = Tmap u x := by
        change profileRestrictIccIf R (Tmap u) xR = Tmap u x
        rw [profileRestrictIccIf_eq R (data.continuous _ (hmap u hu))]
        rfl
      have hanchor_apply : anchor i xR = center i x := by
        have hres := convexProfileCenter_restrict
          (hmap := hmap) (hcont := data.continuous) (hne := data.nonempty)
          (hcompact := hcompact) N i
        have hres' : anchor i = profileRestrictIcc R (center i)
            (data.continuous _ (convexProfileCenter_trap
              (hmap := hmap) (hcont := data.continuous)
              (hne := data.nonempty) (hcompact := hcompact) N i)) := by
          simpa [anchor, center, R] using hres
        rw [hres']
        rfl
      have habs : |Tmap u x - center i x| < eta := by
        simpa [Real.dist_eq, hg_apply, hanchor_apply] using hpoint
      exact mul_le_mul_of_nonneg_left (le_of_lt habs) (hp_nonneg i)
  simpa [p, center, d] using
    abs_sub_weighted_sum_le
      (w := p) (y := Tmap u x) (z := fun i : Fin d => center i x)
      (η := eta) hp_nonneg hp_sum hterm

lemma convexProfile_smoothWeight_error_scale_le
    {trap : (ℝ → ℝ) → Prop} {B : ℝ}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, trap u → trap (Tmap u)}
    {hcont : ∀ u, trap u → Continuous u}
    {hne : ∃ u, trap u}
    {hcompact : LocalUniformSequentiallyCompactRange trap Tmap}
    (hB : 0 ≤ B) (N : ℕ) :
    B * ((convexProfileDim trap Tmap hmap hcont hne hcompact N : ℝ) *
      (2 * (convexProfileDim trap Tmap hmap hcont hne hcompact N + 1 : ℝ) *
        convexProfileCoordTol trap B Tmap hmap hcont hne hcompact N)) ≤
      projectedCubeNetRadius N := by
  let d : ℝ := convexProfileDim trap Tmap hmap hcont hne hcompact N
  let eta : ℝ := projectedCubeNetRadius N
  let c : ℝ := convexProfileCoordTol trap B Tmap hmap hcont hne hcompact N
  have hd_nonneg : 0 ≤ d := by dsimp [d]; positivity
  have hd1_pos : 0 < d + 1 := by dsimp [d]; positivity
  have hB1_pos : 0 < B + 1 := by linarith
  have heta_nonneg : 0 ≤ eta := projectedCubeNetRadius_nonneg N
  have hfracB : B / (B + 1) ≤ 1 :=
    (div_le_one hB1_pos).mpr (by linarith)
  have hfracD : d / (8 * (d + 1)) ≤ 1 := by
    rw [div_le_one]
    · nlinarith [hd_nonneg]
    · positivity
  have hfracD_nonneg : 0 ≤ d / (8 * (d + 1)) :=
    div_nonneg hd_nonneg (by positivity)
  have hrewrite :
      B * (d * (2 * (d + 1) * c)) =
        eta * ((B / (B + 1)) * (d / (8 * (d + 1)))) := by
    dsimp [c, d, eta, convexProfileCoordTol]
    field_simp [ne_of_gt hB1_pos, ne_of_gt hd1_pos]
    ring
  rw [show B *
      ((convexProfileDim trap Tmap hmap hcont hne hcompact N : ℝ) *
        (2 *
          (convexProfileDim trap Tmap hmap hcont hne hcompact N + 1 : ℝ) *
          convexProfileCoordTol trap B Tmap hmap hcont hne hcompact N)) =
      B * (d * (2 * (d + 1) * c)) by simp [d, c]]
  rw [hrewrite]
  calc
    eta * ((B / (B + 1)) * (d / (8 * (d + 1))))
        ≤ eta * (1 * 1) := by
          apply mul_le_mul_of_nonneg_left _ heta_nonneg
          exact mul_le_mul hfracB hfracD hfracD_nonneg (by norm_num)
    _ = eta := by ring

theorem convexProfileResidual_le
    {trap : (ℝ → ℝ) → Prop} {B : ℝ}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    {hmap : ∀ u, trap u → trap (Tmap u)}
    {hcompact : LocalUniformSequentiallyCompactRange trap Tmap}
    (data : BoundedConvexProfileTrapData trap B)
    (N : ℕ)
    (a : Fin (convexProfileDim trap Tmap hmap data.continuous
      data.nonempty hcompact N) → ℝ)
    (ha : a ∈ Freudenthal.unitCube
      (convexProfileDim trap Tmap hmap data.continuous
        data.nonempty hcompact N))
    (hclose :
      ‖convexProfileProj trap B Tmap hmap data.continuous data.nonempty
          hcompact N
          (Tmap (convexProfileLift trap B Tmap hmap data.continuous
            data.nonempty hcompact N a)) - a‖ ≤
        convexProfileCoordTol trap B Tmap hmap data.continuous
          data.nonempty hcompact N)
    (R : ℝ) (_hR : 0 < R) (x : ℝ) (hx : x ∈ Set.Icc (-R) R) :
    |Tmap (convexProfileLift trap B Tmap hmap data.continuous
        data.nonempty hcompact N a) x -
      convexProfileLift trap B Tmap hmap data.continuous
        data.nonempty hcompact N a x| ≤
      projectedCubeLocalError B N R := by
  let d := convexProfileDim trap Tmap hmap data.continuous
    data.nonempty hcompact N
  let eta := projectedCubeNetRadius N
  let c := convexProfileCoordTol trap B Tmap hmap data.continuous
    data.nonempty hcompact N
  let lift := convexProfileLift trap B Tmap hmap data.continuous
    data.nonempty hcompact N
  let p := convexProfileProj trap B Tmap hmap data.continuous
    data.nonempty hcompact N (Tmap (lift a))
  let q : Fin d → ℝ := fun i => smoothCubeWeight c a i
  let center := convexProfileCenter trap Tmap hmap data.continuous
    data.nonempty hcompact N
  have hB : 0 ≤ B :=
    le_trans (abs_nonneg _)
      (data.abs_le (Classical.choose data.nonempty)
        (Classical.choose_spec data.nonempty) 0)
  have hlift_trap : trap (lift a) := by
    simpa [lift, d] using convexProfileLift_trap data N ha
  have hf_trap : trap (Tmap (lift a)) := hmap _ hlift_trap
  by_cases hcov : R ≤ projectedCubeRadius N
  · have hxN : x ∈ Set.Icc
        (-(projectedCubeRadius N)) (projectedCubeRadius N) := by
      rcases hx with ⟨hxL, hxU⟩
      constructor <;> linarith
    have hpart :
        |Tmap (lift a) x - (∑ i : Fin d, p i • center i) x| ≤ eta := by
      simpa [lift, p, center, d, eta] using
        convexProfilePartition_error_le data N hlift_trap hxN
    have hp_unit : p ∈ Freudenthal.unitCube d := by
      simpa [p, d] using convexProfileProj_mem_unitCube
        (trap := trap) (B := B) (hmap := hmap)
        (hcont := data.continuous) (hne := data.nonempty)
        (hcompact := hcompact) N (Tmap (lift a))
    have hmem : profileRestrictIccIf (projectedCubeRadius N)
        (Tmap (lift a)) ∈ convexProfileImageRestrictSet trap
          (projectedCubeRadius N) Tmap hmap data.continuous := by
      simpa [lift] using convexProfileRestrictIf_mem_image_of_map
        (hmap := hmap) (hcont := data.continuous) N hlift_trap
    have hsum_pos : 0 < schauderBumpSum eta
        (convexProfileAnchor trap Tmap hmap data.continuous
          data.nonempty hcompact N)
        (profileRestrictIccIf (projectedCubeRadius N) (Tmap (lift a))) := by
      simpa [eta] using convexProfileBumpSum_pos_of_mem_image
        (hmap := hmap) (hcont := data.continuous) (hne := data.nonempty)
        (hcompact := hcompact) N hmem
    have hp_sum : ∑ i : Fin d, p i = 1 := by
      simpa [p, convexProfileProj, d, eta] using
        sum_schauderBumpWeight_of_sum_pos hsum_pos
    have hcoord : ∀ i : Fin d, |a i - p i| ≤ c := by
      intro i
      have hi := projectedCube_coord_abs_sub_le_of_norm hclose i
      simpa [p, c, d, Pi.sub_apply, abs_sub_comm] using hi
    have hq_p_sum : ∑ i : Fin d, |q i - p i| ≤
        (d : ℝ) * (2 * (d + 1 : ℝ) * c) := by
      simpa [q, d, c] using smoothCubeWeight_close_to_simplex_weights
        (n := d) (c := c) (a := a) (p := p)
        (convexProfileCoordTol_pos (B := B) (hmap := hmap)
          (hcont := data.continuous) (hne := data.nonempty)
          (hcompact := hcompact) hB N).le
        hp_unit hp_sum hcoord
    have hp_q_sum : ∑ i : Fin d, |p i - q i| ≤
        (d : ℝ) * (2 * (d + 1 : ℝ) * c) := by
      simpa [abs_sub_comm] using hq_p_sum
    have hcenter : ∀ i : Fin d, |center i x| ≤ B := by
      intro i
      exact data.abs_le _
        (convexProfileCenter_trap
          (hmap := hmap) (hcont := data.continuous) (hne := data.nonempty)
          (hcompact := hcompact) N i) x
    have hweight_raw :
        |(∑ i : Fin d, p i • center i) x -
          (∑ i : Fin d, q i • center i) x| ≤
        B * ∑ i : Fin d, |p i - q i| :=
      abs_finset_weighted_profile_sum_sub_le hcenter
    have hweight :
        |(∑ i : Fin d, p i • center i) x - lift a x| ≤ eta := by
      have hscale : B * ∑ i : Fin d, |p i - q i| ≤ eta := by
        have hmul := mul_le_mul_of_nonneg_left hp_q_sum hB
        exact le_trans hmul (by
          simpa [d, c, eta] using
            convexProfile_smoothWeight_error_scale_le
              (hmap := hmap) (hcont := data.continuous)
              (hne := data.nonempty) (hcompact := hcompact) hB N)
      have hlift_eq : lift a = ∑ i : Fin d, q i • center i := by
        simp [lift, convexProfileLift, q, center, c, d]
      simpa [hlift_eq] using le_trans hweight_raw hscale
    have htri : |Tmap (lift a) x - lift a x| ≤
        |Tmap (lift a) x - (∑ i : Fin d, p i • center i) x| +
        |(∑ i : Fin d, p i • center i) x - lift a x| := by
      simpa using abs_sub_le (Tmap (lift a) x)
        ((∑ i : Fin d, p i • center i) x) (lift a x)
    have herr : |Tmap (lift a) x - lift a x| ≤ 4 * eta := by
      nlinarith [htri, hpart, hweight, projectedCubeNetRadius_nonneg N]
    simpa [projectedCubeLocalError, hcov, eta, lift] using herr
  · have hf_abs : |Tmap (lift a) x| ≤ B := data.abs_le _ hf_trap x
    have hu_abs : |lift a x| ≤ B := data.abs_le _ hlift_trap x
    have hrough : |Tmap (lift a) x - lift a x| ≤ 2 * B + 1 := by
      have htri : |Tmap (lift a) x - lift a x| ≤
          |Tmap (lift a) x| + |lift a x| := by
        simpa [sub_zero, zero_sub, abs_neg] using
          abs_sub_le (Tmap (lift a) x) 0 (lift a x)
      nlinarith
    simpa [projectedCubeLocalError, hcov, lift] using hrough

/-- The finite-dimensional Schauder projection for any bounded nonempty convex
profile trap.  This is the genuine Schauder--Tychonoff construction used by the
controlled whole-line parameter trap. -/
noncomputable def boundedConvexProfileProjectedCubeApproxData
    {trap : (ℝ → ℝ) → Prop} {B : ℝ}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (data : BoundedConvexProfileTrapData trap B)
    (hmap : ∀ u, trap u → trap (Tmap u))
    (hTcont : LocalUniformContinuousOn trap Tmap)
    (hcompact : LocalUniformSequentiallyCompactRange trap Tmap) :
    ProjectedCubeApproxData trap Tmap := by
  have hB : 0 ≤ B :=
    le_trans (abs_nonneg _)
      (data.abs_le (Classical.choose data.nonempty)
        (Classical.choose_spec data.nonempty) 0)
  refine
    { dim := convexProfileDim trap Tmap hmap data.continuous
        data.nonempty hcompact
      proj := convexProfileProj trap B Tmap hmap data.continuous
        data.nonempty hcompact
      lift := convexProfileLift trap B Tmap hmap data.continuous
        data.nonempty hcompact
      eps := convexProfileCoordTol trap B Tmap hmap data.continuous
        data.nonempty hcompact
      localError := projectedCubeLocalError B
      eps_pos := ?_
      proj_trap := ?_
      maps := ?_
      cont := ?_
      lift_trap := ?_
      localError_nonneg := ?_
      localError_tendsto := ?_
      residual_le := ?_ }
  · exact fun N => convexProfileCoordTol_pos (B := B) (hmap := hmap)
      (hcont := data.continuous) (hne := data.nonempty)
      (hcompact := hcompact) hB N
  · intro N u _hu
    exact convexProfileProj_mem_unitCube
      (trap := trap) (B := B) (hmap := hmap) (hcont := data.continuous)
      (hne := data.nonempty) (hcompact := hcompact) N u
  · intro N a _ha
    exact convexProfileProj_mem_unitCube
      (trap := trap) (B := B) (hmap := hmap) (hcont := data.continuous)
      (hne := data.nonempty) (hcompact := hcompact) N
      (Tmap (convexProfileLift trap B Tmap hmap data.continuous
        data.nonempty hcompact N a))
  · exact fun N => convexProfileTfin_continuousOn data hTcont N
  · exact fun N _a ha => convexProfileLift_trap data N ha
  · exact fun N R => projectedCubeLocalError_nonneg hB N R
  · exact fun _R _hR => projectedCubeLocalError_tendsto
  · intro N a ha hclose R hR x hx
    exact convexProfileResidual_le data N a ha hclose R hR x hx

theorem BoundedConvexProfileTrapData.exists_fixed
    {trap : (ℝ → ℝ) → Prop} {B : ℝ}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (data : BoundedConvexProfileTrapData trap B)
    (hmap : ∀ u, trap u → trap (Tmap u))
    (hTcont : LocalUniformContinuousOn trap Tmap)
    (hcompact : LocalUniformSequentiallyCompactRange trap Tmap) :
    ∃ U, trap U ∧ Tmap U = U :=
  localUniformFixedPoint_of_schauderProjectionData hTcont hcompact
    (boundedConvexProfileProjectedCubeApproxData data hmap hTcont hcompact)

theorem BoundedConvexProfileTrapData.schauderPrinciple
    {trap : (ℝ → ℝ) → Prop} {B : ℝ}
    (data : BoundedConvexProfileTrapData trap B) :
    LocalUniformSchauderFixedPointPrinciple trap := by
  intro Tmap hmap hTcont hcompact
  exact data.exists_fixed hmap hTcont hcompact

section AxiomAudit

#print axioms convexProfileImageRestrictSet_totallyBounded
#print axioms exists_finite_eps_net_convexProfileImageRestrict
#print axioms boundedConvexProfileProjectedCubeApproxData
#print axioms BoundedConvexProfileTrapData.exists_fixed
#print axioms BoundedConvexProfileTrapData.schauderPrinciple

end AxiomAudit

end

end ShenWork.Paper1
