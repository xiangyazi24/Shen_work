import ShenWork.Paper1.WholeLineParabolicDirect

/-!
# Direct parabolic UPPER barrier (mirror of the lower via negation)

The upper barrier `u(t,z) ≤ β(t)` follows from
`parabolic_lower_barrier_direct_of_initial_interval` applied to `−u` with lower
barrier `−β` and lower envelope `−b` (where `b = sup_z u` is the upper envelope):
`(−β) ≤ (−u) ⟺ u ≤ β`, and `inf_z (−u) = −sup_z u = −b`.
-/

open Filter Topology Set

noncomputable section

namespace ShenWork.Paper1

/-- **Direct parabolic upper barrier.**  With a continuous attained UPPER envelope
`b`, initial-interval confinement, and the touch-slope `ut t z0 < dβ t` at a spatial
maximum touching `β`, one gets `u(t,z) ≤ β t` for all `t ≥ 0`, `z`. -/
theorem parabolic_upper_barrier_direct_of_initial_interval
    {u : ℝ → ℝ → ℝ} {b β dβ : ℝ → ℝ} {ut : ℝ → ℝ → ℝ}
    (hβ : ∀ t, HasDerivAt β (dβ t) t)
    (hut : ∀ t z, 0 < t → HasDerivAt (fun s => u s z) (ut t z) t)
    (hb_cont : Continuous b)
    (hb_ub : ∀ t z, u t z ≤ b t)
    (hb_attain : ∀ t, ∃ z0, b t = u t z0)
    (hstart : ∃ ε, 0 < ε ∧ ∀ t, 0 ≤ t → t ≤ ε → b t ≤ β t)
    (hrate : ∀ t z0, 0 ≤ t →
      (∀ z, u t z ≤ u t z0) → u t z0 = β t → ut t z0 < dβ t) :
    ∀ t z, 0 ≤ t → u t z ≤ β t := by
  -- apply the lower theorem to `-u`, barrier `-β`, envelope `-b`
  have key := parabolic_lower_barrier_direct_of_initial_interval
    (u := fun t z => -u t z) (a := fun t => -b t) (α := fun t => -β t)
    (dα := fun t => -dβ t) (ut := fun t z => -ut t z)
    (fun t => (hβ t).neg)
    (fun t z ht => (hut t z ht).neg)
    hb_cont.neg
    (fun t z => by simpa using neg_le_neg (hb_ub t z))
    (fun t => by obtain ⟨z0, hz0⟩ := hb_attain t; exact ⟨z0, by show -b t = -u t z0; rw [hz0]⟩)
    (by obtain ⟨ε, hεpos, hε⟩ := hstart
        exact ⟨ε, hεpos, fun t ht htε => neg_le_neg (hε t ht htε)⟩)
    (by
      intro t z0 ht hmin htouch
      -- `hmin : ∀ z, -u t z0 ≤ -u t z` means z0 is a spatial MAX of u
      have hmax : ∀ z, u t z ≤ u t z0 := fun z => by
        have := hmin z; linarith
      have htb : u t z0 = β t := by linarith [htouch]
      have := hrate t z0 ht hmax htb
      linarith)
  intro t z ht
  have := key t z ht
  linarith

section AxiomAudit
#print axioms parabolic_upper_barrier_direct_of_initial_interval
end AxiomAudit

end ShenWork.Paper1
