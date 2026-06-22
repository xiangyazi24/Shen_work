/-
  Constant coexistence-equilibrium witness for Chen-Ruau-Shen Paper 3.

  Goal.  The landed Paper-3 Theorem 2.1 persistence theorem
  `intervalDomain_sectorialTheorem21Persistence_actualLinearSmall` is stated for
  every `PositiveGlobalBoundedSolution intervalDomain p u v` -- i.e. *conditional*
  on a solution existing.  This file discharges that hypothesis class on the
  concrete interval domain by exhibiting the **constant coexistence equilibrium**
  `u ≡ U*`, `v ≡ V*` with `U* = (a/b)^{1/α}`, `V* = (ν/μ) U*^γ`, proving it is a
  `PositiveGlobalBoundedSolution`, and combining with the persistence theorem to
  obtain the UNCONDITIONAL statement: *a persisting positive bounded solution
  provably exists*.

  HONESTY.  This is the TRIVIAL equilibrium witness.  It proves the hypothesis
  class of Theorem 2.1 is non-empty (so the persistence conclusion is not
  vacuous), NOT the general existence of non-trivial classical solutions, which
  is Paper 2's Theorem 1.1.  At `U* = (a/b)^{1/α}` the logistic reaction balances
  `U*(a - b U*^α) = 0` and the elliptic chemical balances `μ V* = ν U*^γ`; every
  spatial/temporal derivative of a constant vanishes on the open interior; the
  Neumann boundary holds because the (junk-valued) endpoint derivative of the
  zero-extended constant lift is `0`.
-/
import ShenWork.Paper3.IntervalDomainPersistenceActualLinearSectorial

open Filter Topology
open ShenWork.IntervalDomain ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

/-- The full coexistence equilibrium for the cell density: `U* = (a/b)^{1/α}`.
This is the FULL logistic equilibrium, strictly larger than the persistence
threshold `θ = ((a - Cχ)/b)^{1/α}`. -/
def constEqU (p : CM2Params) : ℝ := (p.a / p.b) ^ (1 / p.α)

/-- The coexistence equilibrium for the chemical: `V* = (ν/μ) U*^γ`, the unique
constant solving the elliptic balance `μ V* = ν U*^γ`. -/
def constEqV (p : CM2Params) : ℝ := p.ν / p.μ * (constEqU p) ^ p.γ

lemma constEqU_pos {p : CM2Params} (ha : 0 < p.a) (hb : 0 < p.b) :
    0 < constEqU p :=
  Real.rpow_pos_of_pos (div_pos ha hb) _

lemma constEqU_rpow_alpha {p : CM2Params} (ha : 0 < p.a) (hb : 0 < p.b) :
    (constEqU p) ^ p.α = p.a / p.b := by
  unfold constEqU
  rw [← Real.rpow_mul (le_of_lt (div_pos ha hb)), one_div,
    inv_mul_cancel₀ (ne_of_gt p.hα), Real.rpow_one]

lemma constEqV_nonneg {p : CM2Params} (ha : 0 < p.a) (hb : 0 < p.b) :
    0 ≤ constEqV p := by
  unfold constEqV
  have hU : 0 < (constEqU p) ^ p.γ := Real.rpow_pos_of_pos (constEqU_pos ha hb) _
  have hratio : 0 ≤ p.ν / p.μ := le_of_lt (div_pos p.hν p.hμ)
  exact mul_nonneg hratio (le_of_lt hU)

/-! ### Constant-lift derivative facts on the interval domain. -/

/-- On the open interior `(0,1)` the zero-extended lift of a constant agrees with
that constant on a neighbourhood, so its derivative vanishes. -/
lemma lift_const_deriv_interior (c : ℝ) {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (intervalDomainLift (fun _ : intervalDomainPoint => c)) x = 0 := by
  have hloc : intervalDomainLift (fun _ : intervalDomainPoint => c) =ᶠ[𝓝 x]
      (fun _ => c) := by
    filter_upwards [Icc_mem_nhds hx.1 hx.2] with y hy; simp [intervalDomainLift, hy]
  rw [hloc.deriv_eq]; simp

/-- The constant lift is discontinuous at the left endpoint `0` when `c ≠ 0`
(left limit `0`, value `c`). -/
lemma not_contAt_zero (c : ℝ) (hc : c ≠ 0) :
    ¬ ContinuousAt (intervalDomainLift (fun _ : intervalDomainPoint => c)) 0 := by
  intro hcont
  have hval0 : intervalDomainLift (fun _ : intervalDomainPoint => c) 0 = c := by
    simp [intervalDomainLift]
  have hleft : Tendsto (intervalDomainLift (fun _ : intervalDomainPoint => c))
      (𝓝[Set.Iio 0] (0 : ℝ)) (𝓝 c) := by
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio (0 : ℝ)))
    rwa [hval0] at this
  have hzero : Tendsto (intervalDomainLift (fun _ : intervalDomainPoint => c))
      (𝓝[Set.Iio 0] (0 : ℝ)) (𝓝 0) := by
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hyneg : y < 0 := hy
    have : y ∉ Set.Icc (0 : ℝ) 1 := by
      simp only [Set.mem_Icc, not_and, not_le]; intro h0; linarith
    simp [intervalDomainLift, this]
  haveI : (𝓝[Set.Iio (0 : ℝ)] (0 : ℝ)).NeBot := nhdsWithin_Iio_neBot le_rfl
  exact hc (tendsto_nhds_unique hleft hzero)

/-- The constant lift is discontinuous at the right endpoint `1` when `c ≠ 0`. -/
lemma not_contAt_one (c : ℝ) (hc : c ≠ 0) :
    ¬ ContinuousAt (intervalDomainLift (fun _ : intervalDomainPoint => c)) 1 := by
  intro hcont
  have hval1 : intervalDomainLift (fun _ : intervalDomainPoint => c) 1 = c := by
    simp [intervalDomainLift]
  have hright : Tendsto (intervalDomainLift (fun _ : intervalDomainPoint => c))
      (𝓝[Set.Ioi 1] (1 : ℝ)) (𝓝 c) := by
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
    rwa [hval1] at this
  have hzero : Tendsto (intervalDomainLift (fun _ : intervalDomainPoint => c))
      (𝓝[Set.Ioi 1] (1 : ℝ)) (𝓝 0) := by
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hygt : 1 < y := hy
    have : y ∉ Set.Icc (0 : ℝ) 1 := by
      simp only [Set.mem_Icc, not_and, not_le]; intro _; linarith
    simp [intervalDomainLift, this]
  haveI : (𝓝[Set.Ioi (1 : ℝ)] (1 : ℝ)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  exact hc (tendsto_nhds_unique hright hzero)

/-- The (full, two-sided) endpoint derivative of a constant lift vanishes: for
`c = 0` the lift is globally `0`; for `c ≠ 0` it is not differentiable there, so
`deriv` is its junk value `0`. -/
lemma lift_const_deriv_endpoint (c : ℝ) {e : ℝ} (he : e = 0 ∨ e = 1) :
    deriv (intervalDomainLift (fun _ : intervalDomainPoint => c)) e = 0 := by
  by_cases hc : c = 0
  · subst hc
    have : intervalDomainLift (fun _ : intervalDomainPoint => (0 : ℝ)) = fun _ => 0 := by
      ext y; simp [intervalDomainLift]
    rw [this]; simp
  · apply deriv_zero_of_not_differentiableAt
    intro hdiff
    rcases he with h | h
    · exact not_contAt_zero c hc (h ▸ hdiff.continuousAt)
    · exact not_contAt_one c hc (h ▸ hdiff.continuousAt)

/-- The lift of a constant agrees with that constant on `[0,1]`. -/
lemma lift_const_eqOn (c : ℝ) :
    Set.EqOn (intervalDomainLift (fun _ : intervalDomainPoint => c))
      (fun _ => c) (Set.Icc (0 : ℝ) 1) := fun y hy => by simp [intervalDomainLift, hy]

/-- The interior derivative tends to `0` at the left endpoint `0⁺`. -/
lemma tendsto_deriv_zero_right (c : ℝ) :
    Tendsto (deriv (intervalDomainLift (fun _ : intervalDomainPoint => c)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  apply Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with y hy1 hy2
  exact (lift_const_deriv_interior c ⟨hy1, hy2⟩).symm

/-- The interior derivative tends to `0` at the right endpoint `1⁻`. -/
lemma tendsto_deriv_zero_left (c : ℝ) :
    Tendsto (deriv (intervalDomainLift (fun _ : intervalDomainPoint => c)))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by
  apply Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with y hy1 hy2
  exact (lift_const_deriv_interior c ⟨hy2, hy1⟩).symm

/-! ### The full `intervalDomainClassicalRegularity` for a pair of constants.

All seven conjuncts (spatial `C²` on the open interior / time differentiability /
joint `∂ₜ`-field continuity / interior Neumann tendsto / closed `C²` + endpoint
Neumann values / closed-slab `∂ₜ` continuity / closed-slab solution-field
continuity) are discharged: a constant's lift is constant on `[0,1]`, so every
spatial derivative on the interior is `0`, every time derivative is `0`, and the
endpoint derivatives are `0` (junk value of a jump). -/
lemma const_classicalRegularity (cu cv : ℝ) (T : ℝ) :
    intervalDomainClassicalRegularity T
      (fun (_ : ℝ) (_ : intervalDomainPoint) => cu)
      (fun (_ : ℝ) (_ : intervalDomainPoint) => cv) := by
  have hcd : ∀ c : ℝ, ContDiffOn ℝ 2
      (intervalDomainLift (fun _ : intervalDomainPoint => c)) (Set.Icc (0 : ℝ) 1) :=
    fun c => (contDiffOn_const (c := c)).congr (lift_const_eqOn c)
  have hcd' : ∀ c : ℝ, ContDiffOn ℝ 2
      (intervalDomainLift (fun _ : intervalDomainPoint => c)) (Set.Ioo (0 : ℝ) 1) :=
    fun c => (hcd c).mono Set.Ioo_subset_Icc_self
  have htd : ∀ c : ℝ, (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
      deriv (fun s : ℝ => intervalDomainLift (fun _ : intervalDomainPoint => c) x) t))
      = fun _ => 0 := by intro c; funext q; simp [Function.uncurry]
  have hsf : ∀ c : ℝ, ContinuousOn (Function.uncurry (fun (_ : ℝ) (x : ℝ) =>
      intervalDomainLift (fun _ : intervalDomainPoint => c) x))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro c
    apply ContinuousOn.congr (continuousOn_const (c := c))
    rintro ⟨t, x⟩ hp; simp [Function.uncurry, intervalDomainLift, hp.2]
  have hslice : ∀ (c : ℝ) (x : intervalDomainPoint),
      ContinuousOn (fun s : ℝ => deriv (fun r : ℝ =>
        (fun (_ : ℝ) (_ : intervalDomainPoint) => c) r x) s) (Set.Ioo (0 : ℝ) T) := by
    intro c x
    have : (fun s : ℝ => deriv (fun r : ℝ =>
        (fun (_ : ℝ) (_ : intervalDomainPoint) => c) r x) s) = fun _ => 0 := by
      funext s; simp
    rw [this]; exact continuousOn_const
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t _; exact ⟨hcd' cu, hcd' cv⟩
  · intro x t _; exact ⟨⟨by simp, by simp⟩, hslice cu x, hslice cv x⟩
  · exact ⟨by rw [htd cu]; exact continuousOn_const, by rw [htd cv]; exact continuousOn_const⟩
  · intro t _
    exact ⟨⟨tendsto_deriv_zero_right cu, tendsto_deriv_zero_left cu⟩,
      tendsto_deriv_zero_right cv, tendsto_deriv_zero_left cv⟩
  · intro t _
    exact ⟨⟨hcd cu, lift_const_deriv_endpoint cu (Or.inl rfl),
        lift_const_deriv_endpoint cu (Or.inr rfl)⟩,
      hcd cv, lift_const_deriv_endpoint cv (Or.inl rfl),
        lift_const_deriv_endpoint cv (Or.inr rfl)⟩
  · exact ⟨by rw [htd cu]; exact continuousOn_const, by rw [htd cv]; exact continuousOn_const⟩
  · exact ⟨hsf cu, hsf cv⟩

/-- The Laplacian of a constant vanishes on the open interior. -/
lemma const_lap_interior (c : ℝ) {x : intervalDomainPoint} (hx : x.1 ∈ Set.Ioo (0 : ℝ) 1) :
    intervalDomainLaplacian (fun _ : intervalDomainPoint => c) x = 0 := by
  unfold intervalDomainLaplacian
  have hloc : (fun y : ℝ => deriv (intervalDomainLift (fun _ : intervalDomainPoint => c)) y)
      =ᶠ[𝓝 x.1] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact lift_const_deriv_interior c hy
  rw [hloc.deriv_eq]; simp

/-- The chemotactic divergence vanishes on the open interior when `v` is constant
(its lift's derivative is `0`, killing the flux). -/
lemma const_chemo_interior (p : CM2Params) (cu cv : ℝ)
    {x : intervalDomainPoint} (hx : x.1 ∈ Set.Ioo (0 : ℝ) 1) :
    intervalDomainChemotaxisDiv p (fun _ => cu) (fun _ => cv) x = 0 := by
  unfold intervalDomainChemotaxisDiv
  have hloc : (fun y : ℝ =>
      intervalDomainLift (fun _ : intervalDomainPoint => cu) y *
        deriv (intervalDomainLift (fun _ : intervalDomainPoint => cv)) y /
        (1 + intervalDomainLift (fun _ : intervalDomainPoint => cv) y) ^ p.β)
      =ᶠ[𝓝 x.1] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    rw [lift_const_deriv_interior cv hy]; ring
  rw [hloc.deriv_eq]; simp

/-- **The constant coexistence equilibrium is a Paper-2 classical solution** on
`[0,1]` for every horizon `T > 0`.  The logistic reaction balances
(`U*(a - b U*^α) = 0`), the elliptic chemical balances (`μ V* = ν U*^γ`), all
interior derivatives vanish, and the Neumann boundary holds. -/
lemma constEquilibrium_classical {p : CM2Params}
    (ha : 0 < p.a) (hb : 0 < p.b) {T : ℝ} (hT : 0 < T) :
    IsPaper2ClassicalSolution intervalDomain p T
      (fun (_ : ℝ) (_ : intervalDomainPoint) => constEqU p)
      (fun (_ : ℝ) (_ : intervalDomainPoint) => constEqV p) := by
  refine IsPaper2ClassicalSolution.of_components hT
    (const_classicalRegularity _ _ T) ?_ ?_ ?_ ?_ ?_
  · intro t x _ _; exact constEqU_pos ha hb
  · intro t x _ _; exact constEqV_nonneg ha hb
  · intro t x _ _ hx
    have hxi : x.1 ∈ Set.Ioo (0 : ℝ) 1 := hx
    change deriv (fun _ : ℝ => constEqU p) t
      = intervalDomainLaplacian (fun _ => constEqU p) x
        - p.χ₀ * intervalDomainChemotaxisDiv p (fun _ => constEqU p) (fun _ => constEqV p) x
        + constEqU p * (p.a - p.b * (constEqU p) ^ p.α)
    rw [const_lap_interior (constEqU p) hxi, const_chemo_interior p _ _ hxi,
      constEqU_rpow_alpha ha hb]
    have hb' : p.b ≠ 0 := ne_of_gt hb
    simp only [deriv_const']; field_simp; ring
  · intro t x _ _ hx
    have hxi : x.1 ∈ Set.Ioo (0 : ℝ) 1 := hx
    change (0 : ℝ) = intervalDomainLaplacian (fun _ => constEqV p) x
      - p.μ * constEqV p + p.ν * (constEqU p) ^ p.γ
    rw [const_lap_interior (constEqV p) hxi]
    unfold constEqV
    have hmu : p.μ ≠ 0 := ne_of_gt p.hμ
    field_simp; ring
  · intro t x _ _ hx
    have hxb : x.1 = 0 ∨ x.1 = 1 := hx
    exact ⟨intervalDomainNormalDeriv_const_endpoint_zero _ hxb,
      intervalDomainNormalDeriv_const_endpoint_zero _ hxb⟩

/-- **The constant coexistence equilibrium is a positive global bounded solution.**
Globality is `constEquilibrium_classical` for every `T > 0`; boundedness is
`supNorm ≡ |U*|`; positivity is `U* > 0`. -/
lemma constEquilibrium_positiveGlobalBounded {p : CM2Params}
    (ha : 0 < p.a) (hb : 0 < p.b) :
    PositiveGlobalBoundedSolution intervalDomain p
      (fun (_ : ℝ) (_ : intervalDomainPoint) => constEqU p)
      (fun (_ : ℝ) (_ : intervalDomainPoint) => constEqV p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro T hT; exact constEquilibrium_classical ha hb hT
  · haveI : Nonempty intervalDomainPoint := ⟨⟨0, le_refl _, zero_le_one⟩⟩
    refine IsPaper2Bounded.of_forall_nonneg_supNorm_le (M := |constEqU p|) ?_
    intro t _
    change intervalDomainSupNorm (fun _ : intervalDomainPoint => constEqU p) ≤ |constEqU p|
    unfold intervalDomainSupNorm
    rw [Set.range_const, csSup_singleton]
  · intro t x _ _; exact constEqU_pos ha hb

/-- **Unconditional persistence: a persisting positive bounded solution provably
exists.**  Combining the constant coexistence-equilibrium witness with the landed
Paper-3 Theorem 2.1 persistence theorem
(`intervalDomain_sectorialTheorem21Persistence_actualLinearSmall`), on the
interval domain `[0,1]` with `m = 1`, `β ≥ 1` and small linear sensitivity, there
EXISTS a positive global bounded solution whose long-time `inf` liminf is bounded
below by a positive constant `δu` (the cell density persists) together with the
chemical lower envelope `(ν/μ) δu^γ`.  This discharges the existential hypothesis
of Theorem 2.1 with a concrete witness: the persistence conclusion is provably
non-vacuous.

HONESTY.  This is the TRIVIAL equilibrium witness.  It proves the hypothesis
class of Theorem 2.1 is non-empty; it does NOT prove general existence of
non-trivial classical solutions (that is Paper 2's Theorem 1.1). -/
theorem intervalDomain_persistingSolution_exists {p : CM2Params}
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1))) :
    ∃ u v : ℝ → intervalDomain.Point → ℝ,
      PositiveGlobalBoundedSolution intervalDomain p u v ∧
        ∃ δu > 0, δu ≤ liminfInfValue intervalDomain u ∧
          p.ν / p.μ * (liminfInfValue intervalDomain u) ^ p.γ ≤
            liminfInfValue intervalDomain v := by
  have hpersist := intervalDomain_sectorialTheorem21Persistence_actualLinearSmall
    (uBar := (0 : ℝ)) ha hb hχ0 hm hβ hχ
  have hsol := constEquilibrium_positiveGlobalBounded ha hb
  have hbounds := hpersist.part1 (by rw [hm]) _ _ hsol
  exact ⟨_, _, hsol, hbounds⟩

end

end ShenWork.Paper3
