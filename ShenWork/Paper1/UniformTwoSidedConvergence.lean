import ShenWork.Paper1.WholeLineCauchyLongTimeBound

open Filter Topology MeasureTheory Real Set Function
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section

namespace ShenWork.Paper1

/-!
# Two-sided uniform convergence toolkit for Proposition 1.2 (χ ≤ 0)

The upper side of Proposition 1.2(1) is the exponentially relaxing ceiling
`wholeLineCauchyExpCeiling C t = 1 + (C - 1) exp (-t)` with `C ≥ 1`
(see `WholeLineCauchyLongTimeBound`).  The paper's lower side (§3.2,
"similar arguments of (1.9)") is the mirror: the SAME barrier with
`0 < C < 1` is an exponentially relaxing FLOOR, rising to `1` from below.

This file provides the interface pieces shared by the floor campaign:

* `UniformLiminfGe`, the uniform lower-envelope predicate mirroring
  `UniformLimsupLe`;
* the combination lemma turning the two one-sided envelopes into
  `UniformConvergesToConstant`;
* the floor-side range lemmas for `wholeLineCauchyExpCeiling` with `C ≤ 1`;
* the lower-bound mirror of `Psi_le_const_general_of_nonneg_le` and its
  `frozenElliptic` corollary: the elliptic resolver of a function whose
  `γ`-power is bounded below by `c ≥ 0` is itself bounded below by `c`.
-/

/-- Uniform-in-space eventual lower bound: mirror of `UniformLimsupLe`. -/
def UniformLiminfGe (u : ℝ → ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ t in atTop, ∀ x, L - ε ≤ u t x

theorem UniformLiminfGe.shift_space
    {u : ℝ → ℝ → ℝ} {L : ℝ} (h : UniformLiminfGe u L) (a : ℝ) :
    UniformLiminfGe (fun t x => u t (x + a)) L := by
  intro ε hε
  exact (h ε hε).mono fun _t ht x => ht (x + a)

theorem UniformLiminfGe.mono
    {u : ℝ → ℝ → ℝ} {L₁ L₂ : ℝ}
    (h : UniformLiminfGe u L₁) (hL : L₂ ≤ L₁) :
    UniformLiminfGe u L₂ := by
  intro ε hε
  exact (h ε hε).mono fun _t ht x => by
    have := ht x
    linarith

theorem UniformConvergesToConstant.uniformLiminfGe
    {u : ℝ → ℝ → ℝ} {a : ℝ} (h : UniformConvergesToConstant u a) :
    UniformLiminfGe u a := by
  intro ε hε
  rcases h ε hε with ⟨T, hT⟩
  refine eventually_atTop.2 ⟨T, ?_⟩
  intro t ht x
  have habs : |u t x - a| < ε := hT t x ht
  have hle : a - u t x ≤ |u t x - a| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  linarith

/-- The two one-sided uniform envelopes at the same constant combine into
uniform convergence to that constant. -/
theorem uniformConvergesToConstant_of_limsupLe_liminfGe
    {u : ℝ → ℝ → ℝ} {a : ℝ}
    (hub : UniformLimsupLe u a) (hlb : UniformLiminfGe u a) :
    UniformConvergesToConstant u a := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  rcases eventually_atTop.1 ((hub (ε / 2) hε2).and (hlb (ε / 2) hε2)) with
    ⟨T, hT⟩
  refine ⟨T, fun t x ht => ?_⟩
  have hup := (hT t ht).1 x
  have hlow := (hT t ht).2 x
  rw [abs_lt]
  constructor <;> linarith

/-! ## Floor-side range lemmas for the relaxing barrier with `C ≤ 1` -/

theorem wholeLineCauchyExpCeiling_le_one
    {C t : ℝ} (hC : C ≤ 1) :
    wholeLineCauchyExpCeiling C t ≤ 1 := by
  unfold wholeLineCauchyExpCeiling
  have hmul : (C - 1) * Real.exp (-t) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_nonneg _)
  linarith

theorem wholeLineCauchyExpCeiling_ge
    {C t : ℝ} (hC : C ≤ 1) (ht : 0 ≤ t) :
    C ≤ wholeLineCauchyExpCeiling C t := by
  have hexp : Real.exp (-t) ≤ 1 := by
    simpa using Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
  unfold wholeLineCauchyExpCeiling
  nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hexp)]

theorem wholeLineCauchyExpCeiling_pos
    {C t : ℝ} (hC : 0 < C) (hC1 : C ≤ 1) (ht : 0 ≤ t) :
    0 < wholeLineCauchyExpCeiling C t :=
  lt_of_lt_of_le hC (wholeLineCauchyExpCeiling_ge hC1 ht)

/-! ## Lower-bound mirror for the elliptic resolver -/

/-- Mirror of `Psi_le_const_general_of_nonneg_le`: a continuous input pinched
in `[c, M]` has resolvent bounded below by `(μ/l)·c`. -/
theorem Psi_ge_const_general_of_nonneg_le
    {u : ℝ → ℝ} {l mu c M : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hM : 0 ≤ M) (hc : 0 ≤ c)
    (hu_cont : Continuous u)
    (huM : ∀ y, u y ≤ M)
    (hcu : ∀ y, c ≤ u y) (x : ℝ) :
    (mu / l) * c ≤ Psi u l mu x := by
  have hu_nonneg : ∀ y, 0 ≤ u y := fun y => hc.trans (hcu y)
  have hiu :
      MeasureTheory.Integrable
        (fun y => Real.exp (-Real.sqrt l * |x - y|) * u y) :=
    psi_kernel_mul_bounded_integrable hl hM
      (fun y => by
        rw [abs_of_nonneg (hu_nonneg y)]
        exact huM y)
      x hu_cont.aestronglyMeasurable
  have hic :
      MeasureTheory.Integrable
        (fun y =>
          Real.exp (-Real.sqrt l * |x - y|) * (fun _ : ℝ => c) y) :=
    psi_kernel_mul_bounded_integrable hl hc
      (fun _ => by simp [abs_of_nonneg hc])
      x aestronglyMeasurable_const
  calc
    (mu / l) * c = Psi (fun _ : ℝ => c) l mu x :=
      (Psi_const_general hl x).symm
    _ ≤ Psi u l mu x := Psi_mono hl hmu (fun y => hcu y) x hic hiu

/-- Mirror of `frozenElliptic_le_of_rpow_le`: if the `γ`-power of a bounded
continuous nonnegative input is bounded below by `c ≥ 0`, so is the frozen
elliptic resolver. -/
theorem frozenElliptic_ge_of_rpow_ge
    (p : CMParams) {u : ℝ → ℝ} {c M : ℝ}
    (hM : 0 ≤ M) (hc : 0 ≤ c)
    (hu_cont : Continuous u)
    (_hu_nonneg : ∀ x, 0 ≤ u x)
    (hu_rpow_le : ∀ x, (u x) ^ p.γ ≤ M)
    (hu_rpow_ge : ∀ x, c ≤ (u x) ^ p.γ) (x : ℝ) :
    c ≤ frozenElliptic p u x := by
  unfold frozenElliptic
  have hγ : 0 ≤ p.γ := by linarith [p.hγ]
  have h := Psi_ge_const_general_of_nonneg_le one_pos one_pos hM hc
    (hu_cont.rpow_const (fun _ => Or.inr hγ))
    hu_rpow_le hu_rpow_ge x
  simpa using h

/-! ## The exponentially relaxing floor

For `χ ≤ 0` and uniformly positive initial data, the barrier

`F_{c,λ}(t) = 1 + (c - 1) exp (-λ t)`,  `0 < λ ≤ c ≤ 1`

is a subsolution rising from `c` to `1`.  The relaxation RATE `λ` must be
decoupled from the LEVEL `c`: the naive mirror of the ceiling (rate `1`)
fails — for `α = 1` the inequality `1 - B ≤ B (1 - B^α)` is false for every
`B < 1` (it reads `-(1-B)^2 ≥ 0`).  The correct arithmetic is
`λ (1 - B) ≤ B (1 - B^α)` for `λ ≤ c ≤ B ≤ 1`, using `B^α ≤ B` on `[0,1]`
for `α ≥ 1`.  Restarts move the level but keep the rate, so the restart
identity holds with `λ` fixed. -/

def wholeLineCauchyExpFloor (c lam t : ℝ) : ℝ :=
  1 + (c - 1) * Real.exp (-(lam * t))

theorem wholeLineCauchyExpFloor_zero (c lam : ℝ) :
    wholeLineCauchyExpFloor c lam 0 = c := by
  simp [wholeLineCauchyExpFloor]

theorem wholeLineCauchyExpFloor_hasDerivAt (c lam t : ℝ) :
    HasDerivAt (wholeLineCauchyExpFloor c lam)
      (-((c - 1) * lam * Real.exp (-(lam * t)))) t := by
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(lam * s)))
      (-lam * Real.exp (-(lam * t))) t := by
    have hlin : HasDerivAt (fun s : ℝ => -(lam * s)) (-lam) t := by
      simpa using ((hasDerivAt_id t).const_mul lam).neg
    simpa [mul_comm] using hlin.exp
  have h := (hasDerivAt_const t (1 : ℝ)).add (hexp.const_mul (c - 1))
  convert h using 1
  ring

theorem wholeLineCauchyExpFloor_deriv_eq_sub
    (c lam t : ℝ) :
    deriv (wholeLineCauchyExpFloor c lam) t =
      lam * (1 - wholeLineCauchyExpFloor c lam t) := by
  rw [(wholeLineCauchyExpFloor_hasDerivAt c lam t).deriv]
  simp only [wholeLineCauchyExpFloor]
  ring

theorem wholeLineCauchyExpFloor_le_one
    {c lam : ℝ} (hc : c ≤ 1) (t : ℝ) :
    wholeLineCauchyExpFloor c lam t ≤ 1 := by
  unfold wholeLineCauchyExpFloor
  have hmul : (c - 1) * Real.exp (-(lam * t)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_nonneg _)
  linarith

theorem wholeLineCauchyExpFloor_ge
    {c lam t : ℝ} (hc : c ≤ 1) (hlam : 0 ≤ lam) (ht : 0 ≤ t) :
    c ≤ wholeLineCauchyExpFloor c lam t := by
  have hexp : Real.exp (-(lam * t)) ≤ 1 := by
    simpa using
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hlam ht))
  unfold wholeLineCauchyExpFloor
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hexp)]

theorem wholeLineCauchyExpFloor_pos
    {c lam t : ℝ} (hc0 : 0 < c) (hc : c ≤ 1) (hlam : 0 ≤ lam)
    (ht : 0 ≤ t) :
    0 < wholeLineCauchyExpFloor c lam t :=
  lt_of_lt_of_le hc0 (wholeLineCauchyExpFloor_ge hc hlam ht)

theorem wholeLineCauchyExpFloor_restart (c lam a s : ℝ) :
    wholeLineCauchyExpFloor (wholeLineCauchyExpFloor c lam a) lam s =
      wholeLineCauchyExpFloor c lam (a + s) := by
  unfold wholeLineCauchyExpFloor
  rw [show -(lam * (a + s)) = -(lam * a) + -(lam * s) from by ring,
    Real.exp_add]
  ring

theorem wholeLineCauchyExpFloor_tendsto_one
    {c lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun t : ℝ => wholeLineCauchyExpFloor c lam t)
      atTop (𝓝 1) := by
  have hmul : Tendsto (fun t : ℝ => lam * t) atTop atTop :=
    Tendsto.const_mul_atTop hlam tendsto_id
  have hneg : Tendsto (fun t : ℝ => -(lam * t)) atTop atBot :=
    tendsto_neg_atBot_iff.mpr hmul
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(lam * t)))
      atTop (𝓝 0) := Real.tendsto_exp_atBot.comp hneg
  have h1 : Tendsto (fun t : ℝ => 1 + (c - 1) * Real.exp (-(lam * t)))
      atTop (𝓝 (1 + (c - 1) * 0)) :=
    tendsto_const_nhds.add (hexp.const_mul (c - 1))
  simpa [wholeLineCauchyExpFloor] using h1

theorem wholeLineCauchyExpFloor_eventually_ge
    {c lam : ℝ} (hlam : 0 < lam) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t in atTop, 1 - ε ≤ wholeLineCauchyExpFloor c lam t := by
  have hmem : ∀ᶠ t in atTop,
      wholeLineCauchyExpFloor c lam t ∈ Set.Ioi (1 - ε) :=
    (wholeLineCauchyExpFloor_tendsto_one hlam).eventually_mem
      (Ioi_mem_nhds (by linarith))
  exact hmem.mono fun t ht => le_of_lt ht

/-- The floor subsolution arithmetic: for `α ≥ 1` and `0 < λ ≤ c ≤ B ≤ 1`,
the relaxation drift `λ (1 - B)` is dominated by the logistic reaction
`B (1 - B^α)`.  This is the inequality the naive rate-1 mirror of the
ceiling gets WRONG (it fails at `α = 1`). -/
theorem expFloor_reaction_dominates
    {α c lam B : ℝ} (hα : 1 ≤ α) (hlam : 0 < lam) (hlamc : lam ≤ c)
    (hcB : c ≤ B) (hB1 : B ≤ 1) :
    lam * (1 - B) ≤ B * (1 - B ^ α) := by
  have hB0 : 0 < B := lt_of_lt_of_le hlam (hlamc.trans hcB)
  have hpow : B ^ α ≤ B := by
    calc B ^ α ≤ B ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hB0 hB1 hα
    _ = B := Real.rpow_one B
  have h1 : lam * (1 - B) ≤ B * (1 - B) := by
    have h1B : 0 ≤ 1 - B := by linarith
    exact mul_le_mul_of_nonneg_right (hlamc.trans hcB) h1B
  have h2 : B * (1 - B) ≤ B * (1 - B ^ α) := by
    apply mul_le_mul_of_nonneg_left _ hB0.le
    linarith
  linarith


/-- The rate-`1` floor is exactly the relaxing ceiling barrier: the two
families share all algebra through this identification. -/
theorem wholeLineCauchyExpCeiling_eq_expFloor_rate_one (C t : ℝ) :
    wholeLineCauchyExpCeiling C t = wholeLineCauchyExpFloor C 1 t := by
  simp [wholeLineCauchyExpCeiling, wholeLineCauchyExpFloor]

/-! ## End-to-end conditional assembly for Proposition 1.2(1)

The χ ≤ 0 branch of Proposition 1.2, for the canonical whole-line Cauchy
solution, carrying the two facts the floor campaign must deliver as named
hypotheses: the uniform lower envelope at `1` and strict interior
positivity.  Everything else (existence, upper envelope, combination) is
already banked.  When `WholeLineCauchyLongTimeFloor` lands, both carried
hypotheses discharge from the global floor theorem and this becomes the
unconditional branch. -/

theorem Proposition_1_2_negative_branch_of_floor
    (p : CMParams) (hχ : p.χ ≤ 0)
    (u₀ : ℝ → ℝ) (hu₀ : PaperNonnegativeInitialDatum u₀)
    (hfloor : UniformLiminfGe
      (wholeLineCauchyGlobalU p (wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1)) 1)
    (hstrict : ∀ t x : ℝ, 0 < t →
      0 < wholeLineCauchyGlobalU p (wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1) t x) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalCauchySolutionFrom p u₀ u v ∧
      UniformConvergesToConstant u 1 := by
  let w : WholeLineBUC := wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1
  have hw0 : ∀ x, 0 ≤ w.1 x := by
    intro x
    simpa [w] using hu₀.2 x
  let hregime : WholeLineCauchyCeilingRegime p :=
    WholeLineCauchyCeilingRegime.of_nonpositive hχ
  have hnonneg :
      IsGlobalNonnegativeCauchySolutionFrom p u₀
        (wholeLineCauchyGlobalU p w) (wholeLineCauchyGlobalV p w) := by
    simpa [w] using
      wholeLineCauchyGlobal_isGlobalNonnegativeCauchySolutionFrom
        p hregime w hw0
  have hlimsup : UniformLimsupLe (wholeLineCauchyGlobalU p w) 1 :=
    wholeLineCauchyGlobal_uniformLimsupLe_one_of_chi_nonpos p hχ w hw0
  refine ⟨wholeLineCauchyGlobalU p w, wholeLineCauchyGlobalV p w, ?_, ?_⟩
  · exact ⟨hnonneg.1, hnonneg.2.1, hnonneg.2.2.1, hstrict⟩
  · exact uniformConvergesToConstant_of_limsupLe_liminfGe hlimsup hfloor

end ShenWork.Paper1
