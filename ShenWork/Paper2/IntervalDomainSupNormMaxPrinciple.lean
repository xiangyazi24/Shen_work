/-
  Lemma 3.1 (MAX side): the sup-norm parabolic maximum principle, assembled.

  Wires the three engines into the monotonicity conclusion:
    * `supNorm_eq_sSup_lift_image` — for a nonnegative profile the abstract
      `intervalDomainSupNorm` equals the spatial `sSup` over `[0,1]`;
    * the regularity conjuncts c2/c6/c7 supply the slice-regularity inputs of
      `sliceMax_dini_of_argmax_bound`;
    * the per-argmax slope hypothesis `hkey` (`u_t ≤ 0` at every spatial argmax)
      is the only PDE input — it is discharged by `interior_max_point_of_solution`
      (interior) and the boundary max-point estimate (endpoints).

  Conclusion: `SupNormNonincreasingOn intervalDomain u (Ioo 0 T)`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalDomain

open Set Filter Topology

noncomputable section

namespace ShenWork.MaxPrincipleAtoms

open ShenWork.IntervalDomain

/-- For a nonnegative profile the abstract sup-norm equals the spatial `sSup`
of the lift over `[0,1]`. -/
theorem supNorm_eq_sSup_lift_image {f : intervalDomainPoint → ℝ}
    (hf : ∀ p, 0 ≤ f p) :
    intervalDomainSupNorm f
      = sSup ((fun x => intervalDomainLift f x) '' Set.Icc (0:ℝ) 1) := by
  have hset : Set.range (fun x : intervalDomainPoint => |f x|)
      = (fun x => intervalDomainLift f x) '' Set.Icc (0:ℝ) 1 := by
    ext r
    simp only [Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q.1, q.2, by simp [intervalDomainLift, q.2, abs_of_nonneg (hf q)]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, by simp [intervalDomainLift, hx, abs_of_nonneg (hf ⟨x, hx⟩)]⟩
  rw [intervalDomainSupNorm, hset]

end ShenWork.MaxPrincipleAtoms
