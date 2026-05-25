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

end ShenWork.Paper2.IntervalDomainMoserClosure

end
