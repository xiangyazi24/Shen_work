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
