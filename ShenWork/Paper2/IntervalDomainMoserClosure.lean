/-
  ShenWork/Paper2/IntervalDomainMoserClosure.lean

  Closing the exponent-lattice part of the Moser iteration.

  Intended role in Paper 2 Lemma 2.6:
    The single-step bootstrap gives bounds at exponents p₀+nρ.  Since ρ>0,
    this arithmetic progression eventually dominates every target p>1.
    On a finite-measure domain, L^q control implies L^p control for p≤q.
    Combining these two facts closes the "all p>1" exponent step.

  This file proves the order/Archimedean part.  The finite-measure Lp
  monotonicity is kept as an explicit hypothesis because the abstract
  `BoundedDomainData` interface does not include measure-theoretic fields
  strong enough to derive it internally.
-/
import ShenWork.Paper2.IntervalDomainChain

open ShenWork.Paper2
open ShenWork.IntervalDomain
open MeasureTheory Set intervalIntegral
open scoped Interval

noncomputable section

namespace ShenWork.Paper2.IntervalDomainMoserClosure

/-- A concrete envelope for a family of Lp bounds on `(0,T)`.  Unlike
`LpPowerBoundedBefore`, the constants are kept as an explicit function of the
exponent, which is the data needed for the final `p → ∞` Moser step. -/
def LpPowerBoundEnvelopeBefore
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ) (T pMin : ℝ)
    (lpBound : ℝ → ℝ) : Prop :=
  ∀ pExp, pMin ≤ pExp → ∀ t, 0 < t → t < T →
    D.integral (fun x => (u t x) ^ pExp) ≤ lpBound pExp

/-- The final one-dimensional Moser endpoint supplied analytically by
Gagliardo--Nirenberg/Agmon plus the `p → ∞` iteration.

This is kept as an explicit frontier because the abstract `BoundedDomainData`
API has no topology, interval coordinate, or chain-rule data from which the
endpoint inequality can be derived. -/
def GagliardoNirenbergAgmonLpToLinftyFrontier
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ) (T pMin : ℝ) : Prop :=
  ∀ lpBound : ℝ → ℝ,
    LpPowerBoundEnvelopeBefore D u T pMin lpBound →
      ∃ M, ∀ t, 0 < t → t < T → D.supNorm (u t) ≤ M

/-- Turn pointwise existential Lp bounds at all exponents above `pMin` into
one explicit exponent envelope. -/
theorem lpPowerBoundEnvelopeBefore_of_all_LpPowerBoundedBefore
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T pMin : ℝ}
    (hLp :
      ∀ pExp, pMin ≤ pExp → LpPowerBoundedBefore D pExp T u) :
    ∃ lpBound : ℝ → ℝ, LpPowerBoundEnvelopeBefore D u T pMin lpBound := by
  classical
  let lpBound : ℝ → ℝ :=
    fun pExp => if hp : pMin ≤ pExp then Classical.choose (hLp pExp hp) else 0
  refine ⟨lpBound, ?_⟩
  intro pExp hp t ht0 htT
  have hbound := Classical.choose_spec (hLp pExp hp)
  simpa [lpBound, hp] using hbound t ht0 htT

/-- All Lp bounds plus the GN/Agmon `p → ∞` endpoint give the uniform
finite-horizon sup bound. -/
theorem boundedBefore_of_all_LpPowerBoundedBefore_and_GN_Agmon_frontier
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T pMin : ℝ}
    (hLp :
      ∀ pExp, pMin ≤ pExp → LpPowerBoundedBefore D pExp T u)
    (hFrontier : GagliardoNirenbergAgmonLpToLinftyFrontier D u T pMin) :
    IsPaper2BoundedBefore D T u := by
  rcases lpPowerBoundEnvelopeBefore_of_all_LpPowerBoundedBefore hLp with
    ⟨lpBound, hEnvelope⟩
  exact hFrontier lpBound hEnvelope

/-- If an arithmetic Moser exponent chain `p₀+nρ` is bounded and Lp bounds are
monotone downward in the exponent, then every exponent `p>1` is bounded.

This is the non-PDE, non-energy part of the full Moser closure. -/
theorem all_exponents_of_chain_and_lp_mono
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T p0 rho : ℝ}
    (hrho : 0 < rho)
    (hchain : ∀ n : ℕ, LpPowerBoundedBefore D (p0 + n * rho) T u)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore D q T u → LpPowerBoundedBefore D p T u) :
    ∀ pExp > 1, LpPowerBoundedBefore D pExp T u := by
  intro pExp hpExp
  by_cases hp_le_p0 : pExp ≤ p0
  · have hbase : LpPowerBoundedBefore D p0 T u := by
      simpa using hchain 0
    exact hLpMono hpExp hp_le_p0 hbase
  · push Not at hp_le_p0
    obtain ⟨n, hn⟩ := exists_nat_gt ((pExp - p0) / rho)
    have hp_sub_lt : pExp - p0 < (n : ℝ) * rho := by
      have hmul := mul_lt_mul_of_pos_right hn hrho
      rwa [div_mul_cancel₀ _ (ne_of_gt hrho)] at hmul
    have hp_le_chain : pExp ≤ p0 + (n : ℝ) * rho := by
      linarith
    exact hLpMono hpExp hp_le_chain (hchain n)

/-- Moser chain plus downward Lp monotonicity yields bounds at every exponent
`p>1`.

This combines `IntervalDomainChain.moser_iteration_chain` with
`all_exponents_of_chain_and_lp_mono`. -/
theorem all_exponents_of_moser_iteration_chain
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T p0 rho : ℝ}
    (hrho : 0 < rho)
    (hbase : LpPowerBoundedBefore D p0 T u)
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
            Ceps))
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore D q T u → LpPowerBoundedBefore D p T u) :
    ∀ pExp > 1, LpPowerBoundedBefore D pExp T u := by
  exact all_exponents_of_chain_and_lp_mono hrho
    (IntervalDomainChain.moser_iteration_chain hrho hbase hstep) hLpMono

/-- Moser exponent chain plus downward Lp monotonicity and the GN/Agmon
`p → ∞` endpoint close the bootstrap to a uniform sup-norm bound. -/
theorem boundedBefore_of_chain_lp_mono_and_GN_Agmon_frontier
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T p0 rho pMin : ℝ}
    (hpMin : 1 < pMin)
    (hrho : 0 < rho)
    (hchain : ∀ n : ℕ, LpPowerBoundedBefore D (p0 + n * rho) T u)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore D q T u → LpPowerBoundedBefore D p T u)
    (hFrontier : GagliardoNirenbergAgmonLpToLinftyFrontier D u T pMin) :
    IsPaper2BoundedBefore D T u := by
  have hAll : ∀ pExp > 1, LpPowerBoundedBefore D pExp T u :=
    all_exponents_of_chain_and_lp_mono hrho hchain hLpMono
  exact boundedBefore_of_all_LpPowerBoundedBefore_and_GN_Agmon_frontier
    (D := D) (u := u) (T := T) (pMin := pMin)
    (fun pExp hp => hAll pExp (lt_of_lt_of_le hpMin hp))
    hFrontier

/-- Full Moser iteration closure to finite-horizon `L∞`, conditional only on
the already-separated analytic inputs: the single-step energy/interpolation
family, downward Lp monotonicity, and the GN/Agmon endpoint. -/
theorem boundedBefore_of_moser_iteration_chain_and_GN_Agmon_frontier
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T p0 rho pMin : ℝ}
    (hpMin : 1 < pMin)
    (hrho : 0 < rho)
    (hbase : LpPowerBoundedBefore D p0 T u)
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
            Ceps))
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore D q T u → LpPowerBoundedBefore D p T u)
    (hFrontier : GagliardoNirenbergAgmonLpToLinftyFrontier D u T pMin) :
    IsPaper2BoundedBefore D T u := by
  exact boundedBefore_of_chain_lp_mono_and_GN_Agmon_frontier
    (D := D) (u := u) (T := T) (p0 := p0) (rho := rho) (pMin := pMin)
    hpMin hrho
    (IntervalDomainChain.moser_iteration_chain hrho hbase hstep)
    hLpMono hFrontier

/-! ### Solution-structured quantitative endpoint

The pure envelope endpoint above is intentionally left as a frontier and is
audited below: it is false without solution regularity.  The valid terminal
handoff for Theorem 1.1 is instead a quantitative Moser endpoint produced from
the solution's energy step together with interval GN/Agmon estimates.  At this
level we record the exact interval-domain terminal hook: once that structured
iteration gives a pointwise power control at some positive exponent, the
paper's finite-horizon `L∞` bound follows with no abstract envelope principle.
-/

/-- An interval-domain pointwise power estimate on the open time slab
`0 < t < T`.  This is the kind of terminal estimate obtained from the
solution-structured Moser iteration, after the per-exponent constants have been
controlled. -/
def IntervalDomainMoserPointwisePowerControlBefore
    (u : ℝ → intervalDomain.Point → ℝ) (T pExp R : ℝ) : Prop :=
  ∀ t, 0 < t → t < T → ∀ x : intervalDomain.Point,
    |u t x| ^ pExp ≤ R ^ pExp

/-- A quantitative Lp-root envelope for the interval-domain Moser chain.  The
constants are stored before taking `p → ∞`, so a later energy/GN step can prove
that their roots stay uniformly controlled. -/
def IntervalDomainMoserLpAbsRootBoundBefore
    (u : ℝ → intervalDomain.Point → ℝ) (T pExp R : ℝ) : Prop :=
  ∀ t, 0 < t → t < T →
    intervalDomain.integral (fun x : intervalDomain.Point => |u t x| ^ pExp) ≤
      R ^ pExp

/-- The concrete interval-domain terminal estimate: pointwise control of
`|u|^p` at one positive exponent controls the interval-domain sup norm. -/
theorem intervalDomain_supNorm_le_of_pointwise_power_control
    {v : intervalDomain.Point → ℝ} {pExp R : ℝ}
    (hp : 0 < pExp) (hR : 0 ≤ R)
    (hpoint : ∀ x : intervalDomain.Point, |v x| ^ pExp ≤ R ^ pExp) :
    intervalDomain.supNorm v ≤ R := by
  change intervalDomainSupNorm v ≤ R
  unfold intervalDomainSupNorm
  apply Real.sSup_le
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    exact (Real.rpow_le_rpow_iff (abs_nonneg (v x)) hR hp).mp (hpoint x)
  · exact hR

/-- A structured Moser terminal pointwise estimate closes the interval-domain
bounded-before conclusion directly. -/
theorem intervalDomain_boundedBefore_of_pointwise_power_control
    {u : ℝ → intervalDomain.Point → ℝ} {T pExp R : ℝ}
    (hp : 0 < pExp) (hR : 0 ≤ R)
    (hpoint : IntervalDomainMoserPointwisePowerControlBefore u T pExp R) :
    IsPaper2BoundedBefore intervalDomain T u := by
  refine ⟨R, ?_⟩
  intro t ht0 htT
  exact intervalDomain_supNorm_le_of_pointwise_power_control hp hR
    (hpoint t ht0 htT)

/-- Data expected from the solution-structured Moser iteration after the
energy step and interval GN/Agmon estimates have controlled the constants: a
bounded root tower and one positive exponent where the pointwise terminal
estimate is available. -/
def IntervalDomainMoserQuantitativeEndpoint
    (u : ℝ → intervalDomain.Point → ℝ) (T : ℝ)
    (pSeq rootBound : ℕ → ℝ) : Prop :=
  ∃ M, 0 ≤ M ∧ ∃ n : ℕ,
    0 < pSeq n ∧ 0 ≤ rootBound n ∧ rootBound n ≤ M ∧
      IntervalDomainMoserPointwisePowerControlBefore u T (pSeq n) (rootBound n)

/-- The honest replacement for the false envelope endpoint: once the
solution-structured Moser chain supplies a quantitative endpoint, the concrete
interval-domain `L∞` bound follows. -/
theorem intervalDomain_boundedBefore_of_moser_quantitative_endpoint
    {u : ℝ → intervalDomain.Point → ℝ} {T : ℝ}
    {pSeq rootBound : ℕ → ℝ}
    (hEndpoint : IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound) :
    IsPaper2BoundedBefore intervalDomain T u := by
  rcases hEndpoint with ⟨M, _hM, n, hp, hR, hR_le_M, hpoint⟩
  refine ⟨M, ?_⟩
  intro t ht0 htT
  exact (intervalDomain_supNorm_le_of_pointwise_power_control hp hR
    (hpoint t ht0 htT)).trans hR_le_M

/-- Feed the solution's single-step Moser energy inequality through the already
proved exponent chain, then close with the structured quantitative endpoint.

The remaining endpoint premise is deliberately not the false abstract Lp
envelope frontier.  It is the place where the concrete solution structure
supplies controlled per-exponent constants and the final pointwise power
estimate via interval GN/Agmon. -/
theorem intervalDomain_boundedBefore_of_moser_iteration_chain_and_quantitative_endpoint
    {u : ℝ → intervalDomain.Point → ℝ} {T p0 rho : ℝ}
    {pSeq rootBound : ℕ → ℝ}
    (hrho : 0 < rho)
    (hbase : LpPowerBoundedBefore intervalDomain p0 T u)
    (hstep : ∀ p, p0 ≤ p →
      ∃ A > 0, ∃ K > 0, ∃ L_const,
        (∀ t, 0 < t → t < T →
          A * intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) ≤
          K * intervalDomain.integral (fun x => (u t x) ^ (p + rho)) +
            L_const) ∧
        (∀ eps > 0, ∃ Ceps, ∀ t, 0 < t → t < T →
          intervalDomain.integral (fun x => (u t x) ^ (p + rho)) ≤
            eps * intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
            Ceps))
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore intervalDomain q T u →
        LpPowerBoundedBefore intervalDomain p T u)
    (hEndpoint :
      (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
        IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound) :
    IsPaper2BoundedBefore intervalDomain T u := by
  have hAll : ∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u :=
    all_exponents_of_moser_iteration_chain
      (D := intervalDomain) (u := u) (T := T) (p0 := p0) (rho := rho)
      hrho hbase hstep hLpMono
  exact intervalDomain_boundedBefore_of_moser_quantitative_endpoint
    (hEndpoint hAll)

/-! ### Relative-energy Moser chain

The relative GN/Young estimate used by the PDE has the form
`Z <= eps * G + Ceps * Y`.  The existing single-step Moser interface expects
`Z <= eps * G + C`.  The conversion is valid only inside the solution
iteration, where the current `Y = ∫u^p` bound is already known.  The lemmas in
this section make that dependency explicit and keep the final endpoint
solution-structured.
-/

/-- Dissipation/drop condition needed to reduce the full Lp energy inequality
to the Moser gradient inequality. -/
def MoserDissipationDropBefore
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → ∀ A B K L_const,
    (∀ t, 0 < t → t < T →
      (1 / p) * deriv (fun τ => D.integral (fun x => (u τ x) ^ p)) t +
        A * D.integral (fun x =>
          (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
        B * D.integral (fun x => (u t x) ^ p) ≤
      K * D.integral (fun x => (u t x) ^ (p + rho)) + L_const) →
    ∀ t, 0 < t → t < T →
      0 ≤
        (1 / p) * deriv (fun τ => D.integral (fun x => (u τ x) ^ p)) t +
          B * D.integral (fun x => (u t x) ^ p)

/-- Relative GN/Young interpolation in the form used by the solution Moser
iteration.  The lower-order factor is `∫u^p`, so it must be paired with the
current exponent's Lp bound inside the induction. -/
def RelativeMoserInterpolationBefore
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → ∀ eps > 0, ∃ Ceps, 0 ≤ Ceps ∧
    ∀ t, 0 < t → t < T →
      D.integral (fun x => (u t x) ^ (p + rho)) ≤
        eps * D.integral (fun x =>
          (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
        Ceps * D.integral (fun x => (u t x) ^ p)

/-- Convert relative interpolation to the constant interpolation needed by the
single-step Moser interface, using the current exponent's Lp bound. -/
theorem moser_constant_interpolation_of_relative_interpolation_and_lp_bound
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T p rho : ℝ}
    (hLp : LpPowerBoundedBefore D p T u)
    (hrel : ∀ eps > 0, ∃ Ceps, 0 ≤ Ceps ∧ ∀ t, 0 < t → t < T →
      D.integral (fun x => (u t x) ^ (p + rho)) ≤
        eps * D.integral (fun x =>
          (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
        Ceps * D.integral (fun x => (u t x) ^ p)) :
    ∀ eps > 0, ∃ Cconst, ∀ t, 0 < t → t < T →
      D.integral (fun x => (u t x) ^ (p + rho)) ≤
        eps * D.integral (fun x =>
          (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
        Cconst := by
  rcases hLp with ⟨Cp, hCp⟩
  intro eps heps
  rcases hrel eps heps with ⟨Ceps, hCeps_nonneg, hCeps⟩
  refine ⟨Ceps * Cp, ?_⟩
  intro t ht0 htT
  have hmain := hCeps t ht0 htT
  have hY := hCp t ht0 htT
  have hscaled :
      Ceps * D.integral (fun x => (u t x) ^ p) ≤ Ceps * Cp :=
    mul_le_mul_of_nonneg_left hY hCeps_nonneg
  linarith

/-- Per-exponent Moser step from the full solution energy inequality,
dissipation/drop, and relative interpolation, using the current Lp bound. -/
theorem moser_step_of_energy_dissipation_relative_interpolation
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T rho p0 p : ℝ}
    (henergy : LpBootstrapEnergyInequality D u T rho p0)
    (hdiss : MoserDissipationDropBefore D u T rho p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hp : p0 ≤ p)
    (hLp : LpPowerBoundedBefore D p T u) :
    ∃ A > 0, ∃ K > 0, ∃ L_const,
      (∀ t, 0 < t → t < T →
        A * D.integral (fun x =>
          (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) ≤
        K * D.integral (fun x => (u t x) ^ (p + rho)) + L_const) ∧
      (∀ eps > 0, ∃ Ceps, ∀ t, 0 < t → t < T →
        D.integral (fun x => (u t x) ^ (p + rho)) ≤
          eps * D.integral (fun x =>
            (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
          Ceps) := by
  rcases henergy p hp with ⟨A, hA, B, _hB, K, hK, L_const, hfull⟩
  refine ⟨A, hA, K, hK, L_const, ?_, ?_⟩
  · intro t ht0 htT
    have hfull_t := hfull t ht0 htT
    have hdrop_t := hdiss p hp A B K L_const hfull t ht0 htT
    linarith
  · exact moser_constant_interpolation_of_relative_interpolation_and_lp_bound
      hLp (hrel p hp)

/-- The solution-structured relative Moser induction along the arithmetic
exponent chain. -/
theorem moser_iteration_chain_of_energy_dissipation_relative_interpolation
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T p0 rho : ℝ}
    (hrho : 0 < rho)
    (hbase : LpPowerBoundedBefore D p0 T u)
    (henergy : LpBootstrapEnergyInequality D u T rho p0)
    (hdiss : MoserDissipationDropBefore D u T rho p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0) :
    ∀ n : ℕ, LpPowerBoundedBefore D (p0 + n * rho) T u := by
  intro n
  induction n with
  | zero =>
    simp only [CharP.cast_eq_zero, zero_mul, add_zero]
    exact hbase
  | succ n ih =>
    have hexp_eq : p0 + (↑(n + 1) : ℝ) * rho = (p0 + ↑n * rho) + rho := by
      push_cast
      ring
    rw [hexp_eq]
    have hp_ge : p0 ≤ p0 + ↑n * rho :=
      le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hrho.le)
    obtain ⟨A, hA, K, hK, L_const, hstep_energy, hstep_interp⟩ :=
      moser_step_of_energy_dissipation_relative_interpolation
        henergy hdiss hrel hp_ge ih
    exact IntervalDomainChain.lp_bootstrap_single_step_abstract
      (L_const := L_const) hA hK hstep_energy hstep_interp

/-- All finite exponents from the relative solution Moser chain plus downward
Lp monotonicity. -/
theorem all_exponents_of_energy_dissipation_relative_interpolation_lpmono
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {N T rho p0 : ℝ}
    (hboot : AbstractLpBootstrapHypothesis D u N T rho p0)
    (henergy : LpBootstrapEnergyInequality D u T rho p0)
    (hdiss : MoserDissipationDropBefore D u T rho p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore D q T u → LpPowerBoundedBefore D p T u) :
    ∀ pExp > 1, LpPowerBoundedBefore D pExp T u := by
  exact all_exponents_of_chain_and_lp_mono
    (AbstractLpBootstrapHypothesis.rho_pos hboot)
    (moser_iteration_chain_of_energy_dissipation_relative_interpolation
      (AbstractLpBootstrapHypothesis.rho_pos hboot)
      (AbstractLpBootstrapHypothesis.initial_lp_bound hboot)
      henergy hdiss hrel)
    hLpMono

/-- Interval-domain finite-horizon `L∞` bound from the solution-structured
relative Moser chain and a quantitative endpoint. -/
theorem intervalDomain_boundedBefore_of_energy_dissipation_relative_interpolation
    {u : ℝ → intervalDomain.Point → ℝ} {N T rho p0 : ℝ}
    {pSeq rootBound : ℕ → ℝ}
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u N T rho p0)
    (henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0)
    (hdiss : MoserDissipationDropBefore intervalDomain u T rho p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore intervalDomain q T u →
        LpPowerBoundedBefore intervalDomain p T u)
    (hEndpoint :
      (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
        IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound) :
    IsPaper2BoundedBefore intervalDomain T u := by
  have hAll : ∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u :=
    all_exponents_of_energy_dissipation_relative_interpolation_lpmono
      hboot henergy hdiss hrel hLpMono
  exact intervalDomain_boundedBefore_of_moser_quantitative_endpoint
    (hEndpoint hAll)

/-- Pack the structured solution data needed to turn the relative Moser chain
into an interval-domain finite-horizon `L∞` bound.  The endpoint field is where
the concrete solution regularity, interval GN/Agmon estimates, and controlled
per-exponent constants enter; it is not the invalid abstract Lp-envelope
frontier. -/
structure IntervalDomainStructuredMoserBootstrapData
    (u : ℝ → intervalDomain.Point → ℝ) (T : ℝ) where
  N : ℝ
  rho : ℝ
  p0 : ℝ
  boot : AbstractLpBootstrapHypothesis intervalDomain u N T rho p0
  energy : LpBootstrapEnergyInequality intervalDomain u T rho p0
  dissipation : MoserDissipationDropBefore intervalDomain u T rho p0
  relativeInterpolation : RelativeMoserInterpolationBefore intervalDomain u T rho p0
  lpMono :
    ∀ {p q : ℝ}, 1 < p → p ≤ q →
      LpPowerBoundedBefore intervalDomain q T u →
      LpPowerBoundedBefore intervalDomain p T u
  pSeq : ℕ → ℝ
  rootBound : ℕ → ℝ
  endpoint :
    (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
      IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound

theorem IntervalDomainStructuredMoserBootstrapData.boundedBefore
    {u : ℝ → intervalDomain.Point → ℝ} {T : ℝ}
    (h : IntervalDomainStructuredMoserBootstrapData u T) :
    IsPaper2BoundedBefore intervalDomain T u :=
  intervalDomain_boundedBefore_of_energy_dissipation_relative_interpolation
    h.boot h.energy h.dissipation h.relativeInterpolation h.lpMono h.endpoint

/-- From Lemma 3.1 monotonicity on `(0,t]` and initial sup-norm approach,
derive `supNorm(u t) <= supNorm u₀`. -/
private theorem supNorm_le_initial_of_Ioc_monotone_and_approach
    {u : ℝ → intervalDomain.Point → ℝ} {u₀ : intervalDomain.Point → ℝ}
    {t : ℝ} (ht_pos : 0 < t)
    (hmono : SupNormNonincreasingOn intervalDomain u (Set.Ioc (0 : ℝ) t))
    (happroach : ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ →
      intervalDomain.supNorm (u s) ≤ intervalDomain.supNorm u₀ + ε) :
    intervalDomain.supNorm (u t) ≤ intervalDomain.supNorm u₀ := by
  by_contra h_gt
  push Not at h_gt
  set gap := intervalDomain.supNorm (u t) - intervalDomain.supNorm u₀ with hgap_def
  have hgap_pos : 0 < gap := by linarith
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := happroach (gap / 2) (by linarith)
  set s := min (δ / 2) (t / 2) with hs_def
  have hs_pos : 0 < s := lt_min (by linarith) (by linarith)
  have hs_lt_δ : s < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hs_le_t : s ≤ t := le_of_lt (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  have hs_in_Ioc : s ∈ Set.Ioc (0 : ℝ) t := ⟨hs_pos, hs_le_t⟩
  have ht_in_Ioc : t ∈ Set.Ioc (0 : ℝ) t := ⟨ht_pos, le_rfl⟩
  have h_mono := hmono s hs_in_Ioc t ht_in_Ioc hs_le_t
  have h_approach := hδ_bound s hs_pos hs_lt_δ
  linarith

/-- From Lemma 3.1 monotonicity on `(0,T)` and initial sup-norm approach,
derive `supNorm(u t) <= supNorm u₀`. -/
private theorem supNorm_le_initial_of_Ioo_monotone_and_approach
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

/-- Nonminimal negative-sensitivity branch: the local interval solution is
bounded before `T`.  This is a genuine solution sup-bound proof from the
already-proved Lemma 3.1 maximum-principle chain and initial approach. -/
theorem intervalDomain_boundedBefore_nonminimal_of_negative_sensitivity
    (p : CM2Params)
    (hexist : IntervalDomainTheorem11.IntervalDomainExistence p)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    {u₀ : intervalDomain.Point → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {T : ℝ} (hT : 0 < T)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (htrace : InitialTrace intervalDomain u₀ u) :
    IsPaper2BoundedBefore intervalDomain T u := by
  refine ⟨max (intervalDomain.supNorm u₀) ((p.a / p.b) ^ (1 / p.α)), ?_⟩
  intro t ht_pos ht_lt
  by_cases h_below :
      intervalDomain.supNorm (u t) ≤ (p.a / p.b) ^ (1 / p.α)
  · exact le_trans h_below (le_max_right _ _)
  · push Not at h_below
    have hL31 := Lemma_3_1_intervalDomain p
    have hmono :=
      (hL31 hχ).1 ha hb T hT u v hsol t ht_pos ht_lt h_below
    have happroach :=
      hexist.initialSupNormApproach u₀ hu₀ T hT u v hsol htrace
    have h_le_init :=
      supNorm_le_initial_of_Ioc_monotone_and_approach ht_pos hmono
        (fun ε hε => by
          obtain ⟨δ, hδ_pos, _hδ_le, hδ_bound⟩ := happroach ε hε
          exact ⟨δ, hδ_pos, hδ_bound⟩)
    exact le_trans h_le_init (le_max_left _ _)

/-- Minimal negative-sensitivity branch: the local interval solution is
bounded before `T`. -/
theorem intervalDomain_boundedBefore_minimal_of_negative_sensitivity
    (p : CM2Params)
    (hexist : IntervalDomainTheorem11.IntervalDomainExistence p)
    (hχ : p.χ₀ ≤ 0) (ha : p.a = 0) (hb : p.b = 0)
    {u₀ : intervalDomain.Point → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {T : ℝ} (hT : 0 < T)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (htrace : InitialTrace intervalDomain u₀ u) :
    IsPaper2BoundedBefore intervalDomain T u := by
  refine ⟨intervalDomain.supNorm u₀, ?_⟩
  intro t ht_pos ht_lt
  have hL31 := Lemma_3_1_intervalDomain p
  have hmono := (hL31 hχ).2 ha hb T hT u v hsol
  have happroach :=
    hexist.initialSupNormApproach u₀ hu₀ T hT u v hsol htrace
  exact supNorm_le_initial_of_Ioo_monotone_and_approach
    hT hmono happroach ht_pos ht_lt

/-- Theorem 1.1 bridge with the branch Moser endpoint no longer assumed.

The finite-horizon boundedness needed by global extension is proved here from
the solution's negative-sensitivity maximum-principle structure, not assumed as
`hnonminimalMoser`/`hminimalMoser`.  The relative-energy Moser component
package remains below as an explicit frontier for the still-open analytic
energy endpoint; it is not needed as a hypothesis of this bridge. -/
theorem Theorem_1_1_intervalDomain_of_structured_relative_moser_endpoint
    (p : CM2Params)
    (hexist : IntervalDomainTheorem11.IntervalDomainExistence p) :
    Theorem_1_1 intervalDomain p := by
  intro hχ
  let hexist' : IntervalDomainTheorem11.IntervalDomainExistence p :=
    { localExistence := hexist.localExistence
      initialSupNormApproach := hexist.initialSupNormApproach
      globalExtension := by
        intro u₀ hu₀ Tmax hTmax u v hsol htrace hbounded hm
        by_cases hpos : 0 < p.a ∧ 0 < p.b
        · have hdata :=
            intervalDomain_boundedBefore_nonminimal_of_negative_sensitivity
              p hexist hχ hpos.1 hpos.2 hu₀ hTmax hsol htrace
          exact hexist.globalExtension u₀ hu₀ Tmax hTmax u v hsol htrace
            hdata hm
        · by_cases hzero : p.a = 0 ∧ p.b = 0
          · have hdata :=
              intervalDomain_boundedBefore_minimal_of_negative_sensitivity
                p hexist hχ hzero.1 hzero.2 hu₀ hTmax hsol htrace
            exact hexist.globalExtension u₀ hu₀ Tmax hTmax u v hsol htrace
              hdata hm
          · exact hexist.globalExtension u₀ hu₀ Tmax hTmax u v hsol htrace
              hbounded hm }
  exact (IntervalDomainTheorem11.Theorem_1_1_intervalDomain_conditional
    p hexist') hχ

/-- Explicit relative-energy component package for one solution branch.  This
is intentionally lower-level than `IntervalDomainStructuredMoserBootstrapData`:
it names the bootstrap seed, energy inequality, relative eps-absorption, Lp
monotonicity, and endpoint data separately. -/
structure IntervalDomainRelativeMoserEndpointComponents
    (u : ℝ → intervalDomain.Point → ℝ) (T : ℝ) where
  N : ℝ
  rho : ℝ
  p0 : ℝ
  pSeq : ℕ → ℝ
  rootBound : ℕ → ℝ
  boot : AbstractLpBootstrapHypothesis intervalDomain u N T rho p0
  energy : LpBootstrapEnergyInequality intervalDomain u T rho p0
  dissipation : MoserDissipationDropBefore intervalDomain u T rho p0
  relativeInterpolation : RelativeMoserInterpolationBefore intervalDomain u T rho p0
  lpMono :
    ∀ {p q : ℝ}, 1 < p → p ≤ q →
      LpPowerBoundedBefore intervalDomain q T u →
      LpPowerBoundedBefore intervalDomain p T u
  endpoint :
    (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
      IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound

/-- Component-level constructor for the structured Moser data.  This replaces
an opaque branch-level Moser package by the exact relative-energy inputs used
by the chain.  The component fields remain the honest upstream analytic
frontier. -/
def IntervalDomainRelativeMoserEndpointComponents.toStructuredData
    {u : ℝ → intervalDomain.Point → ℝ} {T : ℝ}
    (h : IntervalDomainRelativeMoserEndpointComponents u T) :
    IntervalDomainStructuredMoserBootstrapData u T :=
  { N := h.N
    rho := h.rho
    p0 := h.p0
    boot := h.boot
    energy := h.energy
    dissipation := h.dissipation
    relativeInterpolation := h.relativeInterpolation
    lpMono := h.lpMono
    pSeq := h.pSeq
    rootBound := h.rootBound
    endpoint := h.endpoint }

/-- Compatibility wrapper for callers that already expose the relative-energy
Moser components.

The current Theorem 1.1 bridge no longer needs those components as hypotheses:
branch boundedness is proved above from Lemma 3.1 and initial approach.  The
component package remains the honest frontier for the independent analytic
Moser endpoint. -/
theorem Theorem_1_1_intervalDomain_of_relative_moser_endpoint_components
    (p : CM2Params)
    (hexist : IntervalDomainTheorem11.IntervalDomainExistence p)
    (_hnonminimalComponents :
      p.χ₀ ≤ 0 → 0 < p.a → 0 < p.b →
        ∀ u₀ : intervalDomain.Point → ℝ,
          PositiveInitialDatum intervalDomain u₀ →
        ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p T u v →
          InitialTrace intervalDomain u₀ u →
            IntervalDomainRelativeMoserEndpointComponents u T)
    (_hminimalComponents :
      p.χ₀ ≤ 0 → p.a = 0 → p.b = 0 →
        ∀ u₀ : intervalDomain.Point → ℝ,
          PositiveInitialDatum intervalDomain u₀ →
        ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p T u v →
          InitialTrace intervalDomain u₀ u →
            IntervalDomainRelativeMoserEndpointComponents u T) :
    Theorem_1_1 intervalDomain p := by
  exact Theorem_1_1_intervalDomain_of_structured_relative_moser_endpoint
    p hexist

/-! ### Concrete interval-domain endpoint audit

The abstract frontier above cannot be discharged from an Lp envelope alone,
even for `intervalDomain`.  The real one-dimensional GN/Agmon theorems require
space regularity and gradient/integrability hypotheses.  Those hypotheses are
not present in `GagliardoNirenbergAgmonLpToLinftyFrontier`, whose input only
records upper bounds for the interval integrals of powers.

The endpoint spike below is invisible to the interval integral, but visible to
the pointwise `supNorm`.  It is the concrete obstruction to treating the
frontier as an unconditional interval-domain theorem. -/

/-- Endpoint spike on `[0,1]`: a value at `x=0` blowing up as `t → 1`. -/
def intervalDomainEndpointSpike (t : ℝ) (x : intervalDomain.Point) : ℝ :=
  if x.1 = 0 then (1 - t)⁻¹ else 0

def intervalDomainZeroPoint : intervalDomain.Point :=
  ⟨0, by exact ⟨by norm_num, by norm_num⟩⟩

lemma intervalDomainEndpointSpike_integral_pow_eq_zero
    {pExp : ℝ} (hpExp : 0 < pExp) (t : ℝ) :
    intervalDomain.integral
      (fun x : intervalDomain.Point => (intervalDomainEndpointSpike t x) ^ pExp) = 0 := by
  change ∫ y in (0 : ℝ)..1,
      intervalDomainLift
        (fun x : intervalDomain.Point => (intervalDomainEndpointSpike t x) ^ pExp) y = 0
  apply intervalIntegral.integral_zero_ae
  filter_upwards with y hy
  have hy_ne_zero : y ≠ 0 := by
    intro hy0
    rw [hy0] at hy
    simp at hy
  by_cases hyIcc : y ∈ Set.Icc (0 : ℝ) 1
  · have hp_ne : pExp ≠ 0 := ne_of_gt hpExp
    simp [intervalDomainLift, hyIcc, intervalDomainEndpointSpike, hy_ne_zero,
      Real.zero_rpow hp_ne]
  · simp [intervalDomainLift, hyIcc]

theorem intervalDomainEndpointSpike_LpPowerBoundEnvelopeBefore :
    LpPowerBoundEnvelopeBefore intervalDomain intervalDomainEndpointSpike 1 2
      (fun _ => 0) := by
  intro pExp hp t _ht0 _htT
  have hp_pos : 0 < pExp := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hp
  rw [intervalDomainEndpointSpike_integral_pow_eq_zero hp_pos t]

lemma intervalDomainEndpointSpike_le_supNorm {t : ℝ}
    (hpos : 0 ≤ (1 - t)⁻¹) :
    (1 - t)⁻¹ ≤ intervalDomain.supNorm (intervalDomainEndpointSpike t) := by
  let x0 : intervalDomain.Point := intervalDomainZeroPoint
  have hmem : |intervalDomainEndpointSpike t x0| ∈
      Set.range (fun x : intervalDomain.Point => |intervalDomainEndpointSpike t x|) :=
    ⟨x0, rfl⟩
  have hbdd : BddAbove
      (Set.range (fun x : intervalDomain.Point => |intervalDomainEndpointSpike t x|)) := by
    refine ⟨|(1 - t)⁻¹|, ?_⟩
    rintro y ⟨x, rfl⟩
    by_cases hx : x.1 = 0
    · simp [intervalDomainEndpointSpike, hx]
    · simp [intervalDomainEndpointSpike, hx]
  have hx0 : intervalDomainEndpointSpike t x0 = (1 - t)⁻¹ := by
    simp [x0, intervalDomainZeroPoint, intervalDomainEndpointSpike]
  have hle_abs : (1 - t)⁻¹ ≤ |intervalDomainEndpointSpike t x0| := by
    rw [hx0, abs_of_nonneg hpos]
  have habs_le_sup :
      |intervalDomainEndpointSpike t x0| ≤
        intervalDomain.supNorm (intervalDomainEndpointSpike t) := by
    simpa [intervalDomain, intervalDomainSupNorm] using le_csSup hbdd hmem
  exact hle_abs.trans habs_le_sup

/-- The current GN/Agmon endpoint frontier is false as an unconditional
`intervalDomain` theorem.  The missing input is not the already-proved interval
GN/Agmon inequality itself, but the regularity/gradient control needed to apply
it and to exclude point spikes invisible to the interval integral. -/
theorem not_intervalDomain_GagliardoNirenbergAgmonLpToLinftyFrontier_endpoint_spike :
    ¬ GagliardoNirenbergAgmonLpToLinftyFrontier
      intervalDomain intervalDomainEndpointSpike 1 2 := by
  intro hFrontier
  rcases hFrontier (fun _ => 0)
      intervalDomainEndpointSpike_LpPowerBoundEnvelopeBefore with
    ⟨M, hM⟩
  let C : ℝ := max M 0 + 2
  let t : ℝ := 1 - C⁻¹
  have hC_pos : 0 < C := by
    dsimp [C]
    have hmax_nonneg : 0 ≤ max M 0 := le_max_right M 0
    linarith
  have hC_gt_one : 1 < C := by
    dsimp [C]
    have hmax_nonneg : 0 ≤ max M 0 := le_max_right M 0
    linarith
  have ht0 : 0 < t := by
    dsimp [t]
    have h_inv_lt_one : C⁻¹ < 1 := inv_lt_one_of_one_lt₀ hC_gt_one
    linarith
  have ht1 : t < 1 := by
    dsimp [t]
    have h_inv_pos : 0 < C⁻¹ := inv_pos.mpr hC_pos
    linarith
  have hval : (1 - t)⁻¹ = C := by
    have hden : 1 - t = C⁻¹ := by
      dsimp [t]
      ring
    rw [hden, inv_inv]
  have hC_le_sup : C ≤ intervalDomain.supNorm (intervalDomainEndpointSpike t) := by
    have hpos : 0 ≤ (1 - t)⁻¹ := by
      rw [hval]
      exact hC_pos.le
    simpa [hval] using
      intervalDomainEndpointSpike_le_supNorm (t := t) hpos
  have hsup_le :
      intervalDomain.supNorm (intervalDomainEndpointSpike t) ≤ M :=
    hM t ht0 ht1
  have hM_lt_C : M < C := by
    dsimp [C]
    have hM_le_max : M ≤ max M 0 := le_max_left M 0
    linarith
  linarith

end ShenWork.Paper2.IntervalDomainMoserClosure

end
