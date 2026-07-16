import ShenWork.Paper1.WholeLineWeightedRegularityChiZeroHalfLineComparisonNatural

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-!
# Target-capped KPP floors on a fixed left half-line

The abstract half-line order theorem is specialized here to the explicit
floor which relaxes from a positive number `C` toward a lateral target
`L < 1`.  The second theorem removes the finite terminal time by applying
the comparison on an arbitrary larger slab.
-/

/-- The target-capped KPP floor remains below a scalar KPP supersolution on
every finite left-half-line slab. -/
theorem leftHalfLine_ge_chiZeroKPPFloor
    {alpha T z₀ c M C L : ℝ} {q : ℝ → ℝ → ℝ}
    (halpha : 1 ≤ alpha) (hT : 0 < T) (hM : 0 ≤ M)
    (hC : 0 < C) (hCL : C < L) (hL1 : L < 1) (hLM : L ≤ M)
    (hcontq : Continuous (fun p : ℝ × ℝ => q p.1 p.2))
    (hqrange : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Iic z₀,
      q t x ∈ Set.Icc (0 : ℝ) M)
    (hinit : ∀ x ∈ Set.Iic z₀, C ≤ q 0 x)
    (hboundary : ∀ t ∈ Set.Icc (0 : ℝ) T, L ≤ q t z₀)
    (htimeq : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => q s x)
        (deriv (fun s : ℝ => q s x) t) t)
    (hspace1q : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => q t y)
        (deriv (fun y : ℝ => q t y) x) x)
    (hspace2q : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => q t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x) x)
    (hpdeq : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T → x < z₀ →
      deriv (fun s : ℝ => q s x) t ≥
        deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x +
          c * deriv (fun y : ℝ => q t y) x + reactionFun alpha (q t x)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Iic z₀,
      chiZeroKPPFloor C L (chiZeroKPPFloorRate alpha C L) t ≤ q t x := by
  let lam : ℝ := chiZeroKPPFloorRate alpha C L
  have hlam : 0 < lam := chiZeroKPPFloorRate_pos halpha hC hCL hL1
  apply leftHalfLine_ge_of_reaction_subsolution
      (b := chiZeroKPPFloor C L lam) halpha hT hM hcontq
  · unfold chiZeroKPPFloor
    fun_prop
  · exact hqrange
  · intro t ht
    constructor
    · exact hC.le.trans
        (chiZeroKPPFloor_ge_start hCL.le hlam.le ht.1)
    · exact (chiZeroKPPFloor_le_target hCL.le).trans hLM
  · simpa [lam] using hinit
  · intro t ht
    exact (chiZeroKPPFloor_le_target hCL.le).trans (hboundary t ht)
  · exact htimeq
  · exact hspace1q
  · exact hspace2q
  · intro t ht
    exact (chiZeroKPPFloor_hasDerivAt C L lam t).differentiableAt.hasDerivAt
  · exact hpdeq
  · intro t ht
    exact chiZeroKPPFloor_deriv_le_reaction halpha hC hCL.le hL1
      hlam.le ht.1.le
      (chiZeroKPPFloorRate_mul_gap_le halpha hC hCL hL1)

/-- A persistent fixed lateral floor `L` and a positive initial floor on the
left half-line force eventual convergence from below to every `L₀ < L`.
Only finite-slab comparison is used; no compactness or global floor enters. -/
theorem eventually_leftHalfLine_ge_of_fixed_boundary_kpp
    {alpha z₀ c M C L₀ L : ℝ} {q : ℝ → ℝ → ℝ}
    (halpha : 1 ≤ alpha) (hM : 0 ≤ M)
    (hC : 0 < C) (hCL : C < L) (hL1 : L < 1) (hLM : L ≤ M)
    (hL₀L : L₀ < L)
    (hcontq : Continuous (fun p : ℝ × ℝ => q p.1 p.2))
    (hqrange : ∀ t, 0 ≤ t → ∀ x ∈ Set.Iic z₀,
      q t x ∈ Set.Icc (0 : ℝ) M)
    (hinit : ∀ x ∈ Set.Iic z₀, C ≤ q 0 x)
    (hboundary : ∀ t, 0 ≤ t → L ≤ q t z₀)
    (htimeq : ∀ ⦃t x : ℝ⦄, 0 < t →
      HasDerivAt (fun s : ℝ => q s x)
        (deriv (fun s : ℝ => q s x) t) t)
    (hspace1q : ∀ ⦃t x : ℝ⦄, 0 < t →
      HasDerivAt (fun y : ℝ => q t y)
        (deriv (fun y : ℝ => q t y) x) x)
    (hspace2q : ∀ ⦃t x : ℝ⦄, 0 < t →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => q t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x) x)
    (hpdeq : ∀ ⦃t x : ℝ⦄, 0 < t → x < z₀ →
      deriv (fun s : ℝ => q s x) t ≥
        deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x +
          c * deriv (fun y : ℝ => q t y) x + reactionFun alpha (q t x)) :
    ∃ S : ℝ, ∀ t, S ≤ t → ∀ x ∈ Set.Iic z₀, L₀ < q t x := by
  let lam : ℝ := chiZeroKPPFloorRate alpha C L
  have hlam : 0 < lam := chiZeroKPPFloorRate_pos halpha hC hCL hL1
  have htend : Tendsto (chiZeroKPPFloor C L lam) atTop (nhds L) :=
    chiZeroKPPFloor_tendsto_target hlam
  have hIoi : Set.Ioi L₀ ∈ nhds L := Ioi_mem_nhds hL₀L
  obtain ⟨S, hfloor⟩ := eventually_atTop.1 (htend.eventually hIoi)
  refine ⟨max S 0, ?_⟩
  intro t ht x hx
  have ht0 : 0 ≤ t := (le_max_right S 0).trans ht
  have hSt : S ≤ t := (le_max_left S 0).trans ht
  have hT : 0 < t + 1 := by linarith
  have hcomp := leftHalfLine_ge_chiZeroKPPFloor
    (T := t + 1) (q := q) halpha hT hM hC hCL hL1 hLM hcontq
    (fun s hs y hy => hqrange s hs.1 y hy) hinit
    (fun s hs => hboundary s hs.1)
    (fun _s _y hs => htimeq hs.1)
    (fun _s _y hs => hspace1q hs.1)
    (fun _s _y hs => hspace2q hs.1)
    (fun _s _y hs hy => hpdeq hs.1 hy)
  exact (hfloor t hSt).trans_le
    (hcomp t ⟨ht0, by linarith⟩ x hx)

section AxiomAudit

#print axioms leftHalfLine_ge_chiZeroKPPFloor
#print axioms eventually_leftHalfLine_ge_of_fixed_boundary_kpp

end AxiomAudit

end ShenWork.Paper1
