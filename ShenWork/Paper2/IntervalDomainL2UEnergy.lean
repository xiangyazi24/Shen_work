/-
  The STANDARD parabolic–elliptic uniqueness energy: the `u`-only L² difference
  energy `E_u(t) = ∫₀¹ (u − U)²`.

  ## Why this is the right energy (and the joint energy is a genuine dead-end)

  The existing track uses the JOINT L² difference energy
  `E(t) = ∫₀¹ (u−U)² + (v−V)²` (`intervalDomainClassicalL2DifferenceEnergy`).
  Differentiating that energy in time forces a time derivative `∂ₜ(v−V)` of the
  `v`-difference.  But `v` is the ELLIPTIC component — it is slaved to `u` at each
  fixed time by `0 = ∂ₓₓv − μ v + ν u^γ` with Neumann BC — so there is NO time
  equation for `v−V` among the hypotheses of a classical solution.  The
  `2∫ (v−V) · ∂ₜ(v−V)` contribution to `E'` therefore cannot be bounded; this is
  the structural reason the joint energy stalls.

  The standard parabolic–elliptic argument controls the `v`-difference
  STATICALLY instead.  We:

  * use only the PARABOLIC `u`-energy `E_u(t) = ∫₀¹ (u−U)²`; its time derivative
    `E_u' = 2∫₀¹ (u−U)·∂ₜ(u−U)` substitutes the PARABOLIC `u`-PDE alone
    (diffusion `−2∫(∂ₓw)² ≤ 0` by Neumann IBP, plus chemotaxis + reaction terms
    bounded by Lipschitz);
  * control `z = v−V` STATICALLY by `‖u^γ − U^γ‖`, hence by `E_u`, via the
    elliptic resolver Lipschitz lemmas;
  * conclude `E_u' ≤ K·E_u`, run Grönwall ⇒ `E_u ≡ 0` ⇒ `u = U`;
  * derive `v = V` from `u = U` by ELLIPTIC UNIQUENESS.

  ## What this file does (ADDITIVELY — the joint def/track is untouched)

  It adds the parallel `u`-only track, fully mirroring the joint track in
  `IntervalDomainClassicalUniqueness` / `IntervalDomainL2UniquenessCertificate`:

  * `intervalDomainClassicalL2DifferenceEnergyU u U t := ∫₀¹ (u−U)²` (+ nonneg);
  * `IntervalDomainClassicalOverlapL2UEnergyCertificate` — the `u`-only overlap
    certificate, whose Grönwall-to-zero half is PROVED here, and whose
    `zero_pointwise` concludes `u = U` AND `v = V`;
  * `intervalDomain_classicalSolution_overlap_unique_of_l2UEnergyCertificate` —
    overlap uniqueness from such a certificate (PROVED, reusing the shared
    Grönwall core);
  * `IntervalDomainL2UDifferenceEnergyFrontier` / `…_of_uFrontier` — the analytic
    frontier interface and the assembly of the certificate from it;
  * `IntervalDomainL2UJointTimeRegularity` and
    `intervalDomainClassicalUniquenessL2EnergyMethod_of_uJointTimeRegularity`:
    the entire L²-energy uniqueness method (hence
    `GlobalSolutionGluingFromReachability`, via the existing
    `GlobalSolutionGluingFromReachability_of_l2EnergyMethod`) reduces to the
    single named `u`-only obligation — which, crucially, no longer requires the
    impossible `∂ₜ(v−V)` control.

  This file contains **no `sorry`, no `admit`, no custom `axiom`.**
-/
import ShenWork.Paper2.IntervalDomainL2UniquenessCertificate

open ShenWork.IntervalDomain
open scoped Topology

namespace ShenWork.Paper2

noncomputable section

/-- **The `u`-only L² difference energy** `E_u(t) = ∫₀¹ (u−U)²`.

This is the standard parabolic–elliptic uniqueness energy: it bundles ONLY the
parabolic `u`-difference, so its time derivative substitutes the `u`-PDE alone
and never asks for a `v−V` time derivative. -/
def intervalDomainClassicalL2DifferenceEnergyU
    (u U : ℝ → intervalDomain.Point → ℝ) (t : ℝ) : ℝ :=
  intervalDomain.integral fun x => (u t x - U t x) ^ 2

/-- The `u`-only L² difference energy is nonnegative (integral of a square). -/
theorem intervalDomainClassicalL2DifferenceEnergyU_nonneg
    (u U : ℝ → intervalDomain.Point → ℝ) (t : ℝ) :
    0 ≤ intervalDomainClassicalL2DifferenceEnergyU u U t := by
  unfold intervalDomainClassicalL2DifferenceEnergyU
  show 0 ≤ intervalDomainIntegral (fun x => (u t x - U t x) ^ 2)
  unfold intervalDomainIntegral
  apply intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1)
  intro x _hx
  unfold intervalDomainLift
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · simp only [hx, dif_pos]; positivity
  · simp only [hx, dif_neg, not_false_iff, le_refl]

/-- **`u`-only L²-energy overlap-uniqueness certificate.**

Mirrors `IntervalDomainClassicalOverlapL2EnergyCertificate` but with the
PARABOLIC `u`-only energy.  The four standard fields:

* `l2u_energy_nonneg`               — `E_u ≥ 0` (proved automatically below);
* `l2u_gronwall_from_positive_times`— the positive-time Grönwall bound for `E_u`;
* `l2u_initial_error_vanishes`      — the positive-time initial `E_u` error → 0;
* `l2u_zero_controls_pointwise`     — `E_u t = 0` forces `u = U` AND, via elliptic
  uniqueness from `u = U`, also `v = V`.

The `v = V` conclusion is built INTO `l2u_zero_controls_pointwise` precisely so
that the certificate never differentiates `v−V` in time: the `v`-equality comes
from the STATIC elliptic relation, not from any parabolic flow of `v`. -/
structure IntervalDomainClassicalOverlapL2UEnergyCertificate
    (p : CM2Params) (T : ℝ)
    (u v U V : ℝ → intervalDomain.Point → ℝ) where
  left_solution : IsPaper2ClassicalSolution intervalDomain p T u v
  right_solution : IsPaper2ClassicalSolution intervalDomain p T U V
  l2u_energy_nonneg :
    ∀ t, 0 < t → t < T →
      0 ≤ intervalDomainClassicalL2DifferenceEnergyU u U t
  l2u_gronwall_from_positive_times :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ s t, 0 < s → s ≤ t → t < T →
        intervalDomainClassicalL2DifferenceEnergyU u U t ≤
          intervalDomainClassicalL2DifferenceEnergyU u U s *
            Real.exp (K * (t - s))
  l2u_initial_error_vanishes :
    ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → s < T →
      intervalDomainClassicalL2DifferenceEnergyU u U s < ε
  l2u_zero_controls_pointwise :
    ∀ t, 0 < t → t < T →
      intervalDomainClassicalL2DifferenceEnergyU u U t = 0 →
        ∀ x : intervalDomain.Point, u t x = U t x ∧ v t x = V t x

/-- **Overlap uniqueness from the `u`-only certificate (PROVED).**

Reuses the SHARED Grönwall-to-zero core
`intervalDomain_energy_eq_zero_of_gronwall` (private in
`IntervalDomainClassicalUniqueness`, re-derived inline here through the public
`intervalDomainL2_gronwall_exp_of_diffIneq` pathway is not needed — we mirror the
existing public theorem structure): `E_u` vanishes on positive times, then the
`u`-only `zero_pointwise` gives both `u = U` and `v = V`. -/
theorem intervalDomain_classicalSolution_overlap_unique_of_l2UEnergyCertificate
    {p : CM2Params} {T : ℝ}
    {u v U V : ℝ → intervalDomain.Point → ℝ}
    (hcert :
      IntervalDomainClassicalOverlapL2UEnergyCertificate p T u v U V) :
    ∀ t, 0 < t → t < T →
      ∀ x : intervalDomain.Point, u t x = U t x ∧ v t x = V t x := by
  -- Grönwall-to-zero: identical scalar argument to the joint case.
  have hE_zero :
      ∀ t, 0 < t → t < T →
        intervalDomainClassicalL2DifferenceEnergyU u U t = 0 := by
    intro t ht0 htT
    have hEt_nonneg : 0 ≤ intervalDomainClassicalL2DifferenceEnergyU u U t :=
      hcert.l2u_energy_nonneg t ht0 htT
    by_contra hEt_ne
    have hEt_pos : 0 < intervalDomainClassicalL2DifferenceEnergyU u U t :=
      lt_of_le_of_ne hEt_nonneg (Ne.symm hEt_ne)
    obtain ⟨K, hK_nonneg, hG⟩ := hcert.l2u_gronwall_from_positive_times
    have hExp_pos : 0 < Real.exp (K * t) := Real.exp_pos _
    set ε : ℝ :=
      intervalDomainClassicalL2DifferenceEnergyU u U t / (2 * Real.exp (K * t))
      with hε
    have hε_pos : 0 < ε :=
      div_pos hEt_pos (mul_pos (by norm_num) hExp_pos)
    obtain ⟨δ, hδ_pos, hδ⟩ := hcert.l2u_initial_error_vanishes ε hε_pos
    set s : ℝ := min (δ / 2) (t / 2) with hs
    have hs_pos : 0 < s := lt_min (by linarith) (by linarith)
    have hs_lt_δ : s < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hs_lt_t : s < t := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hs_le_t : s ≤ t := le_of_lt hs_lt_t
    have hsT : s < T := lt_trans hs_lt_t htT
    have hEs_nonneg : 0 ≤ intervalDomainClassicalL2DifferenceEnergyU u U s :=
      hcert.l2u_energy_nonneg s hs_pos hsT
    have hEs_lt : intervalDomainClassicalL2DifferenceEnergyU u U s < ε :=
      hδ s hs_pos hs_lt_δ hsT
    have hExp_le : Real.exp (K * (t - s)) ≤ Real.exp (K * t) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hK_nonneg, hs_pos]
    have hEt_le :
        intervalDomainClassicalL2DifferenceEnergyU u U t ≤
          intervalDomainClassicalL2DifferenceEnergyU u U s * Real.exp (K * t) :=
      le_trans (hG s t hs_pos hs_le_t htT)
        (mul_le_mul_of_nonneg_left hExp_le hEs_nonneg)
    have hEs_mul_lt :
        intervalDomainClassicalL2DifferenceEnergyU u U s * Real.exp (K * t) <
          ε * Real.exp (K * t) :=
      mul_lt_mul_of_pos_right hEs_lt hExp_pos
    have hε_mul :
        ε * Real.exp (K * t)
          = intervalDomainClassicalL2DifferenceEnergyU u U t / 2 := by
      rw [hε]; field_simp [ne_of_gt hExp_pos]
    have hEt_lt_half :
        intervalDomainClassicalL2DifferenceEnergyU u U t <
          intervalDomainClassicalL2DifferenceEnergyU u U t / 2 :=
      lt_of_le_of_lt hEt_le (by simpa [hε_mul] using hEs_mul_lt)
    linarith
  intro t ht0 htT x
  exact hcert.l2u_zero_controls_pointwise t ht0 htT (hE_zero t ht0 htT) x

/-- **The `u`-only analytic frontier** (mirror of
`IntervalDomainL2DifferenceEnergyFrontier`).

The four standard fields for the PARABOLIC `u`-energy `E_u(t) = ∫₀¹ (u−U)²`:
`cont` (continuity on subintervals), `diffIneq` (`E_u' ≤ K·E_u`, the parabolic
differential inequality — NO `v` time derivative), `initial_vanishes`, and
`zero_pointwise` (concluding `u = U` AND `v = V`). -/
structure IntervalDomainL2UDifferenceEnergyFrontier
    (p : CM2Params) (T : ℝ)
    (u v U V : ℝ → intervalDomain.Point → ℝ) where
  Eprime : ℝ → ℝ
  K : ℝ
  K_nonneg : 0 ≤ K
  cont :
    ∀ s t, 0 < s → s ≤ t → t < T →
      ContinuousOn
        (intervalDomainClassicalL2DifferenceEnergyU u U) (Set.Icc s t)
  diffIneq :
    ∀ τ, 0 < τ → τ < T →
      HasDerivWithinAt
        (intervalDomainClassicalL2DifferenceEnergyU u U) (Eprime τ)
        (Set.Ici τ) τ ∧
      Eprime τ ≤ K * intervalDomainClassicalL2DifferenceEnergyU u U τ
  initial_vanishes :
    ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → s < T →
      intervalDomainClassicalL2DifferenceEnergyU u U s < ε
  zero_pointwise :
    ∀ t, 0 < t → t < T →
      intervalDomainClassicalL2DifferenceEnergyU u U t = 0 →
        ∀ x : intervalDomain.Point, u t x = U t x ∧ v t x = V t x

/-- Assemble the `u`-only overlap certificate from the `u`-only frontier.  The
Grönwall and nonnegativity fields are discharged here by genuine proofs (the
shared Grönwall exponential bound `intervalDomainL2_gronwall_exp_of_diffIneq`
applied to `E_u`). -/
def intervalDomainClassicalOverlapL2UEnergyCertificate_of_diffIneqFrontier
    {p : CM2Params} {T : ℝ}
    {u v U V : ℝ → intervalDomain.Point → ℝ}
    (hsol_left : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hsol_right : IsPaper2ClassicalSolution intervalDomain p T U V)
    (hfront : IntervalDomainL2UDifferenceEnergyFrontier p T u v U V) :
    IntervalDomainClassicalOverlapL2UEnergyCertificate p T u v U V where
  left_solution := hsol_left
  right_solution := hsol_right
  l2u_energy_nonneg := fun t _ _ =>
    intervalDomainClassicalL2DifferenceEnergyU_nonneg u U t
  l2u_gronwall_from_positive_times := by
    refine ⟨hfront.K, hfront.K_nonneg, ?_⟩
    intro s t hs0 hst htT
    refine intervalDomainL2_gronwall_exp_of_diffIneq (E' := hfront.Eprime) hst
      (hfront.cont s t hs0 hst htT) ?_ ?_
    · intro τ hτ
      exact (hfront.diffIneq τ (lt_of_lt_of_le hs0 hτ.1)
        (lt_trans hτ.2 htT)).1
    · intro τ hτ
      exact (hfront.diffIneq τ (lt_of_lt_of_le hs0 hτ.1)
        (lt_trans hτ.2 htT)).2
  l2u_initial_error_vanishes := hfront.initial_vanishes
  l2u_zero_controls_pointwise := hfront.zero_pointwise

/-- A per-pair `u`-only frontier builder: for any two interval classical
solutions with the same initial `u`-trace, produce the `u`-only difference
energy frontier.  This is the single remaining genuinely-upstream PDE obligation
of the standard parabolic–elliptic uniqueness method. -/
structure IntervalDomainL2UDifferenceEnergyFrontierBuilder
    (p : CM2Params) where
  frontier :
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
      ∀ {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          IntervalDomainL2UDifferenceEnergyFrontier
              p (min T₁ T₂) u₁ v₁ u₂ v₂

/-- **From the `u`-only frontier builder to the JOINT L²-energy uniqueness
method (PROVED).**

The `u`-only overlap certificate already yields BOTH `u = U` and `v = V` on the
overlap (its `zero_pointwise` builds in the elliptic `v`-equality).  That is
exactly the conclusion of the joint method's user-facing theorem, so we package
it as a `IntervalDomainClassicalUniquenessL2EnergyMethod p` by producing, for
each pair, a joint overlap certificate whose `l2_zero_controls_pointwise` is
discharged from the `u`-only certificate's overlap equality (the joint Grönwall /
nonnegativity fields are filled by the trivial joint-energy facts, but they are
never actually used to conclude — uniqueness is driven entirely by the `u`-only
Grönwall inside `…_unique_of_l2UEnergyCertificate`). -/
def intervalDomainClassicalUniquenessL2EnergyMethod_of_uFrontier
    {p : CM2Params}
    (hbuilder : IntervalDomainL2UDifferenceEnergyFrontierBuilder p) :
    IntervalDomainClassicalUniquenessL2EnergyMethod p where
  certificate := by
    intro u₀ hu₀ T₁ T₂ u₁ v₁ u₂ v₂ hsol₁ hsol₂ htr₁ htr₂
    -- Restrict each solution to the overlap horizon `min T₁ T₂`.
    have hsol₁' :
        IsPaper2ClassicalSolution intervalDomain p (min T₁ T₂) u₁ v₁ := by
      refine ⟨lt_min hsol₁.T_pos hsol₂.T_pos, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact intervalDomainClassicalRegularity_mono_horizon
          (min_le_left _ _) hsol₁.regularity
      · exact fun t x ht0 htT =>
          hsol₁.u_pos' ht0 (lt_of_lt_of_le htT (min_le_left _ _))
      · exact fun t x ht0 htT =>
          hsol₁.v_nonneg ht0 (lt_of_lt_of_le htT (min_le_left _ _))
      · exact fun t x ht0 htT hx =>
          hsol₁.pde_u ht0 (lt_of_lt_of_le htT (min_le_left _ _)) hx
      · exact fun t x ht0 htT hx =>
          hsol₁.pde_v ht0 (lt_of_lt_of_le htT (min_le_left _ _)) hx
      · exact fun t x ht0 htT hx =>
          hsol₁.neumann ht0 (lt_of_lt_of_le htT (min_le_left _ _)) hx
    have hsol₂' :
        IsPaper2ClassicalSolution intervalDomain p (min T₁ T₂) u₂ v₂ := by
      refine ⟨lt_min hsol₁.T_pos hsol₂.T_pos, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact intervalDomainClassicalRegularity_mono_horizon
          (min_le_right _ _) hsol₂.regularity
      · exact fun t x ht0 htT =>
          hsol₂.u_pos' ht0 (lt_of_lt_of_le htT (min_le_right _ _))
      · exact fun t x ht0 htT =>
          hsol₂.v_nonneg ht0 (lt_of_lt_of_le htT (min_le_right _ _))
      · exact fun t x ht0 htT hx =>
          hsol₂.pde_u ht0 (lt_of_lt_of_le htT (min_le_right _ _)) hx
      · exact fun t x ht0 htT hx =>
          hsol₂.pde_v ht0 (lt_of_lt_of_le htT (min_le_right _ _)) hx
      · exact fun t x ht0 htT hx =>
          hsol₂.neumann ht0 (lt_of_lt_of_le htT (min_le_right _ _)) hx
    -- The `u`-only certificate yields overlap equality of BOTH `u` and `v`.
    have hucert :
        IntervalDomainClassicalOverlapL2UEnergyCertificate
          p (min T₁ T₂) u₁ v₁ u₂ v₂ :=
      intervalDomainClassicalOverlapL2UEnergyCertificate_of_diffIneqFrontier
        hsol₁' hsol₂'
        (hbuilder.frontier hu₀ hsol₁ hsol₂ htr₁ htr₂)
    have hoverlap :
        ∀ t, 0 < t → t < min T₁ T₂ →
          ∀ x : intervalDomain.Point, u₁ t x = u₂ t x ∧ v₁ t x = v₂ t x :=
      intervalDomain_classicalSolution_overlap_unique_of_l2UEnergyCertificate
        hucert
    -- Repackage as a JOINT overlap certificate (the joint energy is never used
    -- to drive uniqueness; only `l2_zero_controls_pointwise` is consulted, and
    -- it is supplied directly by `hoverlap`).
    refine
      { left_solution := hsol₁'
        right_solution := hsol₂'
        l2_energy_nonneg := fun t _ _ =>
          intervalDomainClassicalL2DifferenceEnergy_nonneg u₁ v₁ u₂ v₂ t
        l2_gronwall_from_positive_times := ?_
        l2_initial_error_vanishes := ?_
        l2_zero_controls_pointwise := fun t ht0 htT _ x => hoverlap t ht0 htT x }
    · -- Trivial Grönwall with `K = 0`: the joint energy equals itself.  This
      -- field is required by the joint certificate's signature but is NOT used to
      -- conclude (uniqueness already follows from `hoverlap`).  We must still
      -- provide it honestly; we cannot, in general, prove a joint Grönwall, so we
      -- instead supply it from the established overlap equality, under which the
      -- joint energy is constantly `0` on positive times.
      refine ⟨0, le_refl 0, ?_⟩
      intro s t hs0 hst htT
      have hEt0 :
          intervalDomainClassicalL2DifferenceEnergy u₁ v₁ u₂ v₂ t = 0 := by
        unfold intervalDomainClassicalL2DifferenceEnergy
        have : (fun x => (u₁ t x - u₂ t x) ^ 2 + (v₁ t x - v₂ t x) ^ 2)
            = fun _ => (0 : ℝ) := by
          funext x
          obtain ⟨hu, hv⟩ :=
            hoverlap t (lt_of_lt_of_le hs0 hst) htT x
          rw [hu, hv]; ring
        rw [this]
        show intervalDomainIntegral (fun _ => (0 : ℝ)) = 0
        unfold intervalDomainIntegral intervalDomainLift
        simp
      have hEs0 :
          0 ≤ intervalDomainClassicalL2DifferenceEnergy u₁ v₁ u₂ v₂ s :=
        intervalDomainClassicalL2DifferenceEnergy_nonneg u₁ v₁ u₂ v₂ s
      rw [hEt0]
      positivity
    · -- Initial vanishing of the joint energy follows likewise from `hoverlap`.
      intro ε hε
      refine ⟨1, by norm_num, ?_⟩
      intro s hs0 _ hsT
      have hEs0 :
          intervalDomainClassicalL2DifferenceEnergy u₁ v₁ u₂ v₂ s = 0 := by
        unfold intervalDomainClassicalL2DifferenceEnergy
        have : (fun x => (u₁ s x - u₂ s x) ^ 2 + (v₁ s x - v₂ s x) ^ 2)
            = fun _ => (0 : ℝ) := by
          funext x
          obtain ⟨hu, hv⟩ := hoverlap s hs0 hsT x
          rw [hu, hv]; ring
        rw [this]
        show intervalDomainIntegral (fun _ => (0 : ℝ)) = 0
        unfold intervalDomainIntegral intervalDomainLift
        simp
      rw [hEs0]; exact hε

/-- **The single named `u`-only joint-time obligation** (replaces the joint
`IntervalDomainL2JointTimeRegularity`).

It packages exactly the analytic content of the PARABOLIC `u`-only differential
inequality `E_u' ≤ K·E_u` (time-Leibniz of `∫(u−U)²` + Neumann IBP dissipation +
chemotaxis/reaction Lipschitz absorption) together with the STATIC elliptic
control of `v−V` by `u−U` (resolver Lipschitz) used by `zero_pointwise`.  It is
STRICTLY WEAKER than the joint obligation because it does NOT require any time
derivative of `v−V`. -/
structure IntervalDomainL2UJointTimeRegularity
    (p : CM2Params) where
  frontier :
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
      ∀ {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          IntervalDomainL2UDifferenceEnergyFrontier
              p (min T₁ T₂) u₁ v₁ u₂ v₂

/-- **Builder from the named `u`-only obligation.** -/
def intervalDomainL2UDifferenceEnergyFrontierBuilder_of_uJointTimeRegularity
    {p : CM2Params}
    (hjoint : IntervalDomainL2UJointTimeRegularity p) :
    IntervalDomainL2UDifferenceEnergyFrontierBuilder p where
  frontier := fun {_u₀} hu₀ {_T₁} {_T₂} {_u₁} {_v₁} {_u₂} {_v₂}
      hsol₁ hsol₂ htr₁ htr₂ =>
    hjoint.frontier hu₀ hsol₁ hsol₂ htr₁ htr₂

/-- **Uniqueness method from the `u`-only obligation (PROVED).**

The entire L²-energy uniqueness method — hence
`GlobalSolutionGluingFromReachability p` via the existing
`GlobalSolutionGluingFromReachability_of_l2EnergyMethod` — reduces to the single
named `u`-only obligation `IntervalDomainL2UJointTimeRegularity p`, which (unlike
the joint obligation) does not entangle the impossible `∂ₜ(v−V)`. -/
theorem intervalDomainClassicalUniquenessL2EnergyMethod_of_uJointTimeRegularity
    (p : CM2Params)
    (hjoint : IntervalDomainL2UJointTimeRegularity p) :
    IntervalDomainClassicalUniquenessL2EnergyMethod p :=
  intervalDomainClassicalUniquenessL2EnergyMethod_of_uFrontier
    (intervalDomainL2UDifferenceEnergyFrontierBuilder_of_uJointTimeRegularity
      hjoint)

end

end ShenWork.Paper2
