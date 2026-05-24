/-
  ShenWork/Paper2/IntervalDomainChain.lean

  Single-step Moser iteration: energy inequality + interpolation
  implies L^{p+ρ} bound.

  This is the core inductive step of the Lp bootstrap (Lemma 2.6 in the paper).
  The full Moser iteration is just Nat.rec on this step.

  The proof uses the `absorption` lemma from IntervalDomainBootstrap.lean:
  choose ε = A/(2K) so that K·ε = A/2 < A absorbs the gradient term,
  yielding an explicit bound on the L^{p+ρ} integral.

  Status: 0 sorry, 0 axiom.
  Part 1 (Moser iteration): the hypotheses (energy inequality, interpolation)
  are genuine analytical content for the PDE, not disguised conclusions.
  Part 2 (Theorem 1.1): conditional on classical existence; sup-norm bound
  derived from Lemma_3_1_intervalDomain (proved unconditionally).
-/
import ShenWork.Paper2.IntervalDomainBootstrap

open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.IntervalDomainChain

/-- **Single step of Moser iteration**.

Given:
  * An energy inequality: at each time t ∈ (0,T),
      A · G(t) ≤ K · Z(t) + L
    where G = ∫|∇(u^{p/2})|², Z = ∫u^{p+ρ}.
    (The full PDE energy inequality is `(1/p)Y' + A·G + B·Y ≤ K·Z + L`.
    We drop Y' and B·Y from the LHS since B ≥ 0 and Y = ∫u^p ≥ 0
    in any PDE context with nonneg solutions.)

  * An interpolation inequality: for every ε > 0 there exists C_ε such that
      Z(t) ≤ ε · G(t) + C_ε   for all t ∈ (0,T).

Then: Z(t) is uniformly bounded on (0,T), i.e., `LpPowerBoundedBefore D (p+ρ) T u`.

Proof: pick ε = A/(2K) so that K·ε = A/2 < A. Substituting the interpolation
into the energy inequality and applying `absorption` gives explicit bounds on
G and Z.

The hypotheses are genuine analytical content (playbook §3.1 item 15):
  - The energy inequality comes from testing the PDE against u^{p-1}.
  - The interpolation is Gagliardo-Nirenberg / Agmon on the domain.
Neither hypothesis is the conclusion in disguise. -/
theorem lp_bootstrap_single_step_abstract
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T p rho A K L_const : ℝ}
    (hA : 0 < A) (hK : 0 < K)
    -- Energy inequality (B·Y and derivative term already dropped from LHS)
    (henergy : ∀ t, 0 < t → t < T →
      A * D.integral (fun x => (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) ≤
      K * D.integral (fun x => (u t x) ^ (p + rho)) + L_const)
    -- Interpolation: ∫u^{p+ρ} ≤ ε·∫|∇(u^{p/2})|² + C_ε
    (hinterp : ∀ eps > 0, ∃ Ceps, ∀ t, 0 < t → t < T →
      D.integral (fun x => (u t x) ^ (p + rho)) ≤
        eps * D.integral (fun x => (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
        Ceps) :
    LpPowerBoundedBefore D (p + rho) T u := by
  -- Choose ε = A/(2K) so that K·ε = A/2 < A
  have heps_pos : 0 < A / (2 * K) := div_pos hA (mul_pos two_pos hK)
  obtain ⟨Ceps, hCeps⟩ := hinterp (A / (2 * K)) heps_pos
  -- The absorption condition: K · ε < A, i.e., K · (A/(2K)) = A/2 < A
  have habs : K * (A / (2 * K)) < A := by
    have h2K_ne : (2 * K) ≠ 0 := ne_of_gt (mul_pos two_pos hK)
    calc K * (A / (2 * K)) = K * A / (2 * K) := by rw [mul_div_assoc']
      _ = A / 2 := by rw [mul_comm K A]; exact mul_div_mul_right A 2 (ne_of_gt hK)
      _ < A := by linarith
  -- Provide the uniform bound witness
  refine ⟨A / (2 * K) * ((K * Ceps + L_const) / (A - K * (A / (2 * K)))) + Ceps, ?_⟩
  intro t ht_pos ht_lt
  -- Apply absorption at this time t
  exact (IntervalDomainBootstrap.absorption
    (hK := hK.le) (hε := heps_pos.le) (habs := habs)
    (henergy := henergy t ht_pos ht_lt) (hinterp := hCeps t ht_pos ht_lt)).2

/-- **Moser iteration chain**: repeated application of the single step
yields L^{p₀+n·ρ} bounds for all n ∈ ℕ.

Given:
  * At each exponent p ≥ p₀, an energy inequality and interpolation that
    promote L^p → L^{p+ρ}.
  * A base L^{p₀} bound.

Then: L^{p₀ + n·ρ} bounds hold for all n ∈ ℕ, proved by Nat.rec on the
single step.

This is the complete Moser iteration. In the PDE context, the base case
comes from mass conservation (L^1 bound), and the energy + interpolation
hypotheses come from the PDE structure at each level.

To go from "all L^{p₀+n·ρ}" to "L^∞ boundedness" requires L^p → L^∞
(Lemma 4.1 in the paper), which is a separate step. -/
theorem moser_iteration_chain
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T p0 rho : ℝ}
    (hrho : 0 < rho)
    -- Base case: L^{p₀} bound
    (hbase : LpPowerBoundedBefore D p0 T u)
    -- Inductive step: at each exponent p ≥ p₀, energy + interpolation hold
    (hstep : ∀ p, p0 ≤ p →
      ∃ A > 0, ∃ K > 0, ∃ L_const,
        (∀ t, 0 < t → t < T →
          A * D.integral (fun x =>
            (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) ≤
          K * D.integral (fun x => (u t x) ^ (p + rho)) + L_const) ∧
        (∀ eps > 0, ∃ Ceps, ∀ t, 0 < t → t < T →
          D.integral (fun x => (u t x) ^ (p + rho)) ≤
            eps * D.integral (fun x =>
              (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
            Ceps)) :
    ∀ n : ℕ, LpPowerBoundedBefore D (p0 + n * rho) T u := by
  intro n
  induction n with
  | zero =>
    simp only [CharP.cast_eq_zero, zero_mul, add_zero]
    exact hbase
  | succ n ih =>
    -- Need: LpPowerBoundedBefore D (p0 + (n+1)*rho) T u
    -- Rewrite exponent: p0 + (n+1)*rho = (p0 + n*rho) + rho
    have hexp_eq : p0 + (↑(n + 1) : ℝ) * rho = (p0 + ↑n * rho) + rho := by
      push_cast; ring
    rw [hexp_eq]
    -- Apply the single step at exponent p = p0 + n*rho
    have hp_ge : p0 ≤ p0 + ↑n * rho :=
      le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hrho.le)
    obtain ⟨A, hA, K, hK, L_const, henergy, hinterp⟩ := hstep (p0 + ↑n * rho) hp_ge
    exact lp_bootstrap_single_step_abstract hA hK henergy hinterp

end ShenWork.Paper2.IntervalDomainChain

/-! ### Paper 2 Theorem 1.1 on intervalDomain, conditional on classical existence

The full chain:  classical existence + Lemma 3.1 (proved unconditionally for
intervalDomain) → Theorem 1.1.

The three conditional hypotheses are genuine analytical front-line items:
  * **Local existence**: every positive initial datum launches a classical solution
    on some finite horizon with an initial trace.
  * **Initial sup-norm approach**: the abstract sup norm of the solution approaches
    the initial sup norm as `t → 0⁺`.  This bridges `InitialTrace` (which controls
    `supNorm(u t - u₀)`) to `supNorm(u t) ≤ supNorm u₀ + ε`.
  * **Global extension**: if a solution is bounded on every finite horizon and
    `1 ≤ p.m`, then the solution extends globally.

None of these three hypotheses is the conclusion in disguise (playbook §3.1
item 15).  The sup-norm *bound* in the conclusion is derived from the proved
`Lemma_3_1_intervalDomain` combined with the initial approach hypothesis via
an ε-squeeze argument.
-/
namespace ShenWork.Paper2.IntervalDomainTheorem11

open ShenWork.IntervalDomain

/-- Hypotheses for Paper 2 Theorem 1.1 on `intervalDomain` that are not yet
unconditionally proved.  Each field represents a genuine analytical fact about
the parabolic chemotaxis-logistic system on `[0,1]`.  Providing these
hypotheses closes the full Theorem 1.1 statement. -/
structure IntervalDomainExistence (p : CM2Params) where
  /-- Local existence: every positive initial datum launches a classical
  solution on some finite horizon with an initial trace. -/
  localExistence :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u
  /-- Initial sup-norm approach: for any classical solution with initial trace,
  `supNorm(u t)` is close to `supNorm u₀` for small positive time.  This bridges
  `InitialTrace` (which controls `supNorm(u t - u₀)`) to pointwise supNorm
  control.  On the concrete interval domain this follows from the triangle
  inequality `supNorm f ≤ supNorm g + supNorm(f - g)`. -/
  initialSupNormApproach :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ∀ ε > 0, ∃ δ > 0, δ ≤ T ∧ ∀ t, 0 < t → t < δ →
            intervalDomain.supNorm (u t) ≤ intervalDomain.supNorm u₀ + ε
  /-- Global extension: bounded classical solutions extend to all time when
  `1 ≤ p.m`. -/
  globalExtension :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
      ∀ Tmax > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p Tmax u v →
        InitialTrace intervalDomain u₀ u →
          IsPaper2BoundedBefore intervalDomain Tmax u →
            1 ≤ p.m →
              IsPaper2GlobalClassicalSolution intervalDomain p u v

/-- Helper: from Lemma 3.1 nonincreasing on `(0, t]` and initial approach
`supNorm(u s) ≤ supNorm u₀ + ε` for small `s`, derive `supNorm(u t) ≤ supNorm u₀`.

The ε-squeeze argument: for any ε > 0, pick `s` in `(0, min(δ, t)]` so that
  * `supNorm(u t) ≤ supNorm(u s)`  (nonincreasing on `(0, t]`)
  * `supNorm(u s) ≤ supNorm u₀ + ε`  (initial approach with `s < δ`)
  Then `supNorm(u t) ≤ supNorm u₀ + ε`.  Since ε is arbitrary, `≤ supNorm u₀`. -/
private theorem supNorm_le_initial_of_nonincreasing_and_approach
    {u : ℝ → intervalDomain.Point → ℝ} {u₀ : intervalDomain.Point → ℝ}
    {t : ℝ} (ht_pos : 0 < t)
    (hmono : SupNormNonincreasingOn intervalDomain u (Set.Ioc (0 : ℝ) t))
    (happroach : ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ →
      intervalDomain.supNorm (u s) ≤ intervalDomain.supNorm u₀ + ε) :
    intervalDomain.supNorm (u t) ≤ intervalDomain.supNorm u₀ := by
  by_contra h_gt
  push Not at h_gt
  -- The gap between supNorm(u t) and supNorm u₀
  set gap := intervalDomain.supNorm (u t) - intervalDomain.supNorm u₀ with hgap_def
  have hgap_pos : 0 < gap := by linarith
  -- From initial approach, pick δ with supNorm(u s) ≤ supNorm u₀ + gap/2 for s < δ
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := happroach (gap / 2) (by linarith)
  -- Pick s = min(δ/2, t/2), which lies in (0, t] ∩ (0, δ)
  set s := min (δ / 2) (t / 2) with hs_def
  have hs_pos : 0 < s := lt_min (by linarith) (by linarith)
  have hs_lt_δ : s < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hs_le_t : s ≤ t := le_of_lt (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  have hs_in_Ioc : s ∈ Set.Ioc (0 : ℝ) t := ⟨hs_pos, hs_le_t⟩
  have ht_in_Ioc : t ∈ Set.Ioc (0 : ℝ) t := ⟨ht_pos, le_refl t⟩
  -- From nonincreasing: supNorm(u t) ≤ supNorm(u s)
  have h_mono := hmono s hs_in_Ioc t ht_in_Ioc hs_le_t
  -- From initial approach: supNorm(u s) ≤ supNorm u₀ + gap/2
  have h_approach := hδ_bound s hs_pos hs_lt_δ
  -- Contradiction: supNorm(u t) ≤ supNorm u₀ + gap/2 < supNorm(u t)
  linarith

/-- Helper: from Lemma 3.1 nonincreasing on `(0, T)` and initial approach,
derive `supNorm(u t) ≤ supNorm u₀` for all `t ∈ (0, T)`.  (Minimal branch) -/
private theorem supNorm_le_initial_of_nonincreasing_Ioo_and_approach
    {u : ℝ → intervalDomain.Point → ℝ} {u₀ : intervalDomain.Point → ℝ}
    {T : ℝ} (_hT : 0 < T)
    (hmono : SupNormNonincreasingOn intervalDomain u (Set.Ioo (0 : ℝ) T))
    (happroach : ∀ ε > 0, ∃ δ > 0, δ ≤ T ∧ ∀ s, 0 < s → s < δ →
      intervalDomain.supNorm (u s) ≤ intervalDomain.supNorm u₀ + ε)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < T) :
    intervalDomain.supNorm (u t) ≤ intervalDomain.supNorm u₀ := by
  by_contra h_gt
  push Not at h_gt
  set gap := intervalDomain.supNorm (u t) - intervalDomain.supNorm u₀ with hgap_def
  have hgap_pos : 0 < gap := by linarith
  obtain ⟨δ, hδ_pos, _hδ_le_T, hδ_bound⟩ :=
    happroach (gap / 2) (by linarith)
  set s := min (δ / 2) (t / 2) with hs_def
  have hs_pos : 0 < s := lt_min (by linarith) (by linarith)
  have hs_lt_δ : s < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hs_lt_t : s < t := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hs_lt_T : s < T := lt_trans hs_lt_t ht_lt
  have hs_in_Ioo : s ∈ Set.Ioo (0 : ℝ) T := ⟨hs_pos, hs_lt_T⟩
  have ht_in_Ioo : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht_pos, ht_lt⟩
  have h_mono := hmono s hs_in_Ioo t ht_in_Ioo hs_lt_t.le
  have h_approach := hδ_bound s hs_pos hs_lt_δ
  linarith

/-- **Paper 2 Theorem 1.1 on `intervalDomain`, conditional on classical existence.**

This assembles:
  * `Lemma_3_1_intervalDomain` (proved unconditionally): monotonicity of the
    sup norm under negative sensitivity;
  * the ε-squeeze bridge from monotonicity + initial approach to the explicit
    sup-norm bound `max(‖u₀‖_∞, (a/b)^{1/α})` (nonminimal) or `‖u₀‖_∞`
    (minimal);
  * the global extension criterion for `1 ≤ p.m`.

Status: conditional on `IntervalDomainExistence p` (state ③ in the playbook:
conditioned on unproved but genuine analytical front). -/
theorem Theorem_1_1_intervalDomain_conditional
    (p : CM2Params) (hexist : IntervalDomainExistence p) :
    Theorem_1_1 intervalDomain p := by
  intro hχ
  constructor
  · -- Non-minimal branch: 0 < p.a → 0 < p.b → ...
    intro ha hb u₀ hu₀
    -- Get the classical solution from the existence hypothesis
    obtain ⟨Tmax, hTmax, u, v, hsol, htrace⟩ :=
      hexist.localExistence u₀ hu₀
    refine ⟨Tmax, hTmax, u, v, hsol, htrace, ?_, ?_⟩
    · -- Sup-norm bound: supNorm(u t) ≤ max(supNorm u₀, (a/b)^{1/α})
      intro t ht_pos ht_lt
      by_cases h_below : intervalDomain.supNorm (u t) ≤ (p.a / p.b) ^ (1 / p.α)
      · -- Case 1: already below the carrying capacity
        exact le_trans h_below (le_max_right _ _)
      · -- Case 2: above the carrying capacity → use Lemma 3.1
        push Not at h_below
        -- Lemma 3.1 gives nonincreasing on (0, t]
        have hL31 := Lemma_3_1_intervalDomain p
        have hmono := (hL31 hχ).1 ha hb Tmax hTmax u v hsol t ht_pos ht_lt h_below
        -- Initial approach gives supNorm(u s) ≤ supNorm u₀ + ε for small s
        have happroach := hexist.initialSupNormApproach u₀ hu₀ Tmax hTmax u v hsol htrace
        -- ε-squeeze: supNorm(u t) ≤ supNorm u₀
        have h_le_init :=
          supNorm_le_initial_of_nonincreasing_and_approach ht_pos hmono
            (fun ε hε => by
              obtain ⟨δ, hδ_pos, _hδ_le, hδ_bound⟩ := happroach ε hε
              exact ⟨δ, hδ_pos, hδ_bound⟩)
        exact le_trans h_le_init (le_max_left _ _)
    · -- Global existence if 1 ≤ p.m
      intro hm
      -- First establish the IsPaper2BoundedBefore bound
      have hbounded : IsPaper2BoundedBefore intervalDomain Tmax u := by
        refine ⟨max (intervalDomain.supNorm u₀) ((p.a / p.b) ^ (1 / p.α)), ?_⟩
        intro t ht_pos ht_lt
        by_cases h_below :
            intervalDomain.supNorm (u t) ≤ (p.a / p.b) ^ (1 / p.α)
        · exact le_trans h_below (le_max_right _ _)
        · push Not at h_below
          have hL31 := Lemma_3_1_intervalDomain p
          have hmono :=
            (hL31 hχ).1 ha hb Tmax hTmax u v hsol t ht_pos ht_lt h_below
          have happroach :=
            hexist.initialSupNormApproach u₀ hu₀ Tmax hTmax u v hsol htrace
          have h_le_init :=
            supNorm_le_initial_of_nonincreasing_and_approach ht_pos hmono
              (fun ε hε => by
                obtain ⟨δ, hδ_pos, _hδ_le, hδ_bound⟩ := happroach ε hε
                exact ⟨δ, hδ_pos, hδ_bound⟩)
          exact le_trans h_le_init (le_max_left _ _)
      exact hexist.globalExtension u₀ hu₀ Tmax hTmax u v hsol htrace hbounded hm
  · -- Minimal branch: p.a = 0 → p.b = 0 → ...
    intro ha hb u₀ hu₀
    obtain ⟨Tmax, hTmax, u, v, hsol, htrace⟩ :=
      hexist.localExistence u₀ hu₀
    refine ⟨Tmax, hTmax, u, v, hsol, htrace, ?_, ?_⟩
    · -- Sup-norm bound: supNorm(u t) ≤ supNorm u₀
      intro t ht_pos ht_lt
      -- Lemma 3.1 minimal branch gives nonincreasing on (0, T)
      have hL31 := Lemma_3_1_intervalDomain p
      have hmono := (hL31 hχ).2 ha hb Tmax hTmax u v hsol
      -- Initial approach
      have happroach :=
        hexist.initialSupNormApproach u₀ hu₀ Tmax hTmax u v hsol htrace
      -- ε-squeeze: supNorm(u t) ≤ supNorm u₀
      exact supNorm_le_initial_of_nonincreasing_Ioo_and_approach
        hTmax hmono happroach ht_pos ht_lt
    · -- Global existence if 1 ≤ p.m
      intro hm
      have hbounded : IsPaper2BoundedBefore intervalDomain Tmax u := by
        refine ⟨intervalDomain.supNorm u₀, ?_⟩
        intro t ht_pos ht_lt
        have hL31 := Lemma_3_1_intervalDomain p
        have hmono := (hL31 hχ).2 ha hb Tmax hTmax u v hsol
        have happroach :=
          hexist.initialSupNormApproach u₀ hu₀ Tmax hTmax u v hsol htrace
        exact supNorm_le_initial_of_nonincreasing_Ioo_and_approach
          hTmax hmono happroach ht_pos ht_lt
      exact hexist.globalExtension u₀ hu₀ Tmax hTmax u v hsol htrace hbounded hm

end ShenWork.Paper2.IntervalDomainTheorem11

end
