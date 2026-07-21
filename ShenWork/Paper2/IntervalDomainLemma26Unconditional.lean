/-
  ShenWork/Paper2/IntervalDomainLemma26Unconditional.lean

  Paper 2 Lemma 2.6 (Lᵖ bootstrap) on the concrete `intervalDomain`.

  ASSESSMENT.  The literal `Lemma_2_6 intervalDomain` is the genuine Lᵖ
  bootstrap: from a seed bound at `p0` plus the energy inequality, conclude a
  *uniform-on-(0,T)* Lᵖ bound at every exponent `pExp > 1`.  Two facts govern
  its reachability.

  (1)  It is NOT dischargeable from the currently-proved concrete pieces by
       elementary calculus.  The `hgrad` frontier consumed by the interval
       Moser engine,
         `∫ u^(p+ρ-2) |∂u|² ≤ cGrad · ∫ |∂(u^(p/2))|²`,
       is, via the exact chain-rule identity on the interior
         `∂(u^(p/2)) = (p/2) · u^(p/2-1) · ∂u`   ⟹
         `|∂(u^(p/2))|² = (p/2)² · u^(p-2) · |∂u|²`,
       equivalent to
         `∫ u^ρ · [u^(p-2)|∂u|²] ≤ cGrad (p/2)² · ∫ [u^(p-2)|∂u|²]`,
       which holds iff `‖u‖_∞^ρ ≤ cGrad (p/2)²`, i.e. iff an a-priori `L∞`
       bound on `u` is already available.  That `L∞` bound is exactly the
       boundedness the bootstrap is meant to produce, so `hgrad` is not
       elementary chain-rule content — it encodes the a-priori bound and is
       genuinely conditional.  (`hMG` = Lemma 4.1 is proved; `hgrad`/`hdiss`
       are not, and cannot be, discharged for arbitrary `u`.)

  (2)  As with Lemma 2.7 (`not_Lemma_2_7_intervalDomain`), the abstract
       ALL-TIME form `LpPowerBoundedBefore` on `(0,T)` is exactly the piece
       that fails for arbitrary data: nothing in the hypotheses controls the
       Lᵖ mass as `t → 0⁺`.  The seed at `p0` does bound the `p0`-mass
       uniformly, but on a fixed measure-1 domain a `p0`-bound does not bound
       higher moments (concentration), and the energy inequality's grip on
       concentration is precisely the a-priori bound of point (1).

  REACHABLE FAITHFUL FORM.  What IS unconditionally true and elementary is the
  extreme-value-theorem closure: once the Lᵖ-power mass map is continuous on
  the CLOSED interval `[0,T]` (equivalently, it has a finite limit as
  `t → 0⁺`, as a classical solution with a continuous initial trace does), the
  uniform bound is immediate.  This is the honest analogue of
  `unitPointDomain.Lemma_2_7_from_continuous_bound` and of
  `Lemma_2_7_intervalDomain_from_continuous_bound`, and it is what the actual
  Paper 2 workflow supplies through the classical solution's regularity.  The
  solution-slice route to the FULL bootstrap already exists in the repo
  (`Corollary_2_1_intervalDomain_of_..._from_solution_positivity`), which keeps
  `hgrad`/`hdiss` as the genuine remaining PDE frontiers.

  NEW FILE — no edits to existing files.
-/
import ShenWork.Paper2.Statements

open ShenWork.IntervalDomain
open MeasureTheory Set
open scoped Topology

noncomputable section

namespace ShenWork.Paper2.IntervalDomainLemma26Unconditional

/-- **Extreme-value closure (the reachable elementary core).**

If the Lᵖ-power mass map `t ↦ ∫₀¹ (u t)^pExp` is continuous on the compact
`[0,T]`, it attains a maximum there, giving the uniform bound on `(0,T)`.
This is the single true ingredient that the abstract all-time Lemma 2.6/2.7
statements are missing for arbitrary data. -/
theorem lpPowerBoundedBefore_of_continuousOn_Icc
    {u : ℝ → intervalDomain.Point → ℝ} {T pExp : ℝ} (hT : 0 < T)
    (hcont :
      ContinuousOn
        (fun t => intervalDomain.integral (fun x => (u t x) ^ pExp))
        (Set.Icc 0 T)) :
    LpPowerBoundedBefore intervalDomain pExp T u := by
  have hne : (Set.Icc (0 : ℝ) T).Nonempty := ⟨0, Set.left_mem_Icc.mpr hT.le⟩
  obtain ⟨t₀, ht₀, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hcont
  refine ⟨intervalDomain.integral (fun x => (u t₀ x) ^ pExp), ?_⟩
  intro t ht_pos ht_lt
  exact hmax ⟨ht_pos.le, ht_lt.le⟩

/-- **Paper 2 Lemma 2.6 on `intervalDomain`, faithful (reachable) form.**

Given, for each admissible instance, continuity of every Lᵖ-power mass map on
the CLOSED interval `[0,T]` (the non-blowup-at-`0` datum a classical solution
supplies), the full bootstrap conclusion of `Lemma_2_6 intervalDomain` holds.

This isolates precisely the ingredient the abstract statement lacks for
arbitrary data: the seed and energy inequality are carried unchanged, and the
only added input is closed-interval continuity of the Lᵖ mass.  It is TRUE and
clean (only propext / Classical.choice / Quot.sound); it does not smuggle in
the `hgrad`/`hdiss` a-priori `L∞` bound discussed in the file header. -/
theorem Lemma_2_6_intervalDomain_from_continuous_lp_bounds
    (hcont :
      ∀ (N : ℝ), 0 < N → ∀ (u : ℝ → intervalDomain.Point → ℝ) (T rho p0 : ℝ),
        AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
        LpBootstrapEnergyInequality intervalDomain u T rho p0 →
        ∀ pExp : ℝ, 1 < pExp →
          ContinuousOn
            (fun t => intervalDomain.integral (fun x => (u t x) ^ pExp))
            (Set.Icc 0 T)) :
    Lemma_2_6 intervalDomain := by
  intro N hN u T rho p0 hboot henergy pExp hpExp
  exact lpPowerBoundedBefore_of_continuousOn_Icc hboot.T_pos
    (hcont N hN u T rho p0 hboot henergy pExp hpExp)

end ShenWork.Paper2.IntervalDomainLemma26Unconditional
