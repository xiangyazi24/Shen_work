/-
  ShenWork/Paper1/GradientQuasiMonotone.lean

  Elliptic adaptation of the paper §4.2 χ≤0 chemotaxis quasi-monotonicity.

  TARGET.  `RotheChemoMonotoneResidual p λ u Z W B` (WaveRotheOrder.lean:126) is
  the carried obligation

      (★)   0 ≤ λ·(W y − Z y) − χ·(∂ₓ(stepFlux_B) y − ∂ₓ(stepFlux_W) y)   ∀ y,

  with `stepFlux_W y = (W y)^m · V'(y)`, `V = frozenElliptic p u`.  It is the
  pointwise comparison residual whose nonnegativity would give the implicit-step
  super-ordering `crossSource_W ≤ barrierSource_B`, hence `W ≤ B` through the
  Green map (`implicitStep_le_of_barrier`).

  WHAT THIS FILE ESTABLISHES.

  1.  The EXACT pointwise decomposition of (★)'s chemotaxis term, via the landed
      product-rule split `chemFlux_split_identity` (no `W'=B'` substitution, no
      sign claim):
          ∂ₓ(stepFlux_B) − ∂ₓ(stepFlux_W)
            = m V'·(B^{m−1}B' − W^{m−1}W') + (B^m − W^m)·V''.
      The carried `chemFlux` and the order layer's `stepFlux` are DEFINITIONALLY
      the same function `(·)^m · V'`; we record this so the split applies to (★).

  2.  THE GENUINE OBSTRUCTION (the §3.3 "absolute pointwise sign is FALSE").
      With the trapped/antitone sign data alone — `χ≤0`, `V'≤0`, `W'≤0`, `B'≤0`,
      `W≤Z` (so `λ(W−Z)≤0`) — the residual (★) is NOT derivable: the leading
      chemo term `m V'·(B^{m−1}B' − W^{m−1}W')` is a DIFFERENCE of two
      independently nonnegative gradient products and carries no fixed sign, while
      the `λ(W−Z)` term is ≤0 and cannot rescue it.  We prove this is a genuine
      obstruction by exhibiting a CONCRETE scalar assignment of the decomposed
      quantities — every sign hypothesis satisfied — at which the residual's RHS
      is strictly negative.  This refutes any pointwise discharge of (★) from the
      signed gradients (`gradientResidual_not_signed_pointwise`).

  3.  THE ELLIPTIC ADAPTATION THAT ACTUALLY CLOSES THE COMPARISON.  The sign
      genuinely closes only at the CONTACT MAX of `φ = W − B`, where the
      first-order test forces `W'(x₀) = B'(x₀)`; there the gradient-difference
      term degenerates to `m V'·W'·(B^{m−1}−W^{m−1})`, a single Lipschitz
      increment, and the chemo defect obeys the one-sided bound
      `−χ(∂stepFlux_W − ∂stepFlux_B)(x₀) ≤ C_chem·(W−B)(x₀)`
      (landed `chemFlux_increment_bound`).  Fed to the landed clean elliptic
      maximum principle `implicitStep_le_of_barrier_maxPrinciple_clean`, this
      yields `W ≤ B` — the SAME conclusion (★) was meant to provide — WITHOUT the
      pointwise residual.  We package this as `rotheStep_le_barrier_elliptic`,
      certifying that `RotheChemoMonotoneResidual` is redundant for the
      construction: the elliptic adaptation of §4.2's `w=uₓ` max principle is the
      CONTACT-POINT bound, not a pointwise gradient sign.

  HONEST ACCOUNTING.  (★)/`RotheChemoMonotoneResidual` is NOT discharged
  unconditionally — it is REFUTED as a bare pointwise statement (item 2), so no
  elliptic-gradient lemma can close it pointwise; the genuine elliptic counterpart
  is the contact-point bound (item 3), which discharges the downstream COMPARISON.
  The precise irreducible analytic input that remains in the construction is then
  `chemFlux_increment_bound`'s Lipschitz/elliptic factor data at the contact max
  (`Cvpp`, `Cwp`, `L1`, `Lm`), already landed and consumed by the live producer
  (`rotheStep_le_barrier`).  See the final note.
-/
import ShenWork.Paper1.WaveRotheOrder
import ShenWork.Paper1.WaveRotheMaxPrincipleClosers
import ShenWork.Paper1.WaveRotheMaxPrinciple

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-! ## 1 — the order-layer flux is the chemotaxis flux

`stepFlux` (WaveRotheOrder.lean:115) and `chemFlux` (WaveRotheMaxPrinciple.lean:122)
are the same function `(W ·)^m · V'`.  Recording this lets the landed product-rule
split `chemFlux_split_identity` act on (★)'s `stepFlux` derivatives. -/

/-- `stepFlux` and `chemFlux` are definitionally equal. -/
theorem stepFlux_eq_chemFlux (p : CMParams) (u W : ℝ → ℝ) :
    stepFlux p u W = chemFlux p u W := by
  funext y; rfl

/-- The EXACT pointwise decomposition of (★)'s chemotaxis flux difference,
`∂ₓ(stepFlux_B) − ∂ₓ(stepFlux_W)`, via the landed product-rule split.  No
`W'=B'` substitution; no sign claim — this is the bare algebraic identity that
the signed-gradient analysis must contend with. -/
theorem stepFlux_diff_split
    (p : CMParams) {u W B : ℝ → ℝ} {y : ℝ}
    (hu : IsCUnifBdd u) (hu_nonneg : ∀ z, 0 ≤ u z)
    (hWdiff : DifferentiableAt ℝ W y) (hBdiff : DifferentiableAt ℝ B y) :
    deriv (stepFlux p u B) y - deriv (stepFlux p u W) y
      = p.m * deriv (frozenElliptic p u) y
          * ((B y) ^ (p.m - 1) * deriv B y - (W y) ^ (p.m - 1) * deriv W y)
        + ((B y) ^ p.m - (W y) ^ p.m) * deriv (deriv (frozenElliptic p u)) y := by
  rw [stepFlux_eq_chemFlux, stepFlux_eq_chemFlux]
  have hB := chemFlux_split_identity p hu hu_nonneg hBdiff
  have hW := chemFlux_split_identity p hu hu_nonneg hWdiff
  rw [hB, hW]; ring

/-! ## 2 — the genuine obstruction: (★) is FALSE as a bare pointwise sign

The residual's RHS, expressed in the decomposed scalars

    `lam·(Wv − Zv) − χ·( m·Vp·(Bv^{m−1}·Bp − Wv^{m−1}·Wp) + (Bv^m − Wv^m)·Vpp )`,

is NOT forced nonnegative by the trapped/antitone sign data.  We exhibit a
concrete scalar instance satisfying every sign hypothesis at which it is strictly
negative.  This is the precise reason no pointwise elliptic-gradient lemma can
discharge (★): the obstruction is real, not a missing tactic.

We work at the level of the decomposed real quantities (this is faithful: the
split above is an exact identity, so any genuine pointwise discharge would have to
sign this very expression).  The witness uses `m = 2`, `Vp = -1` (`V'≤0`),
`Wp = -1`, `Bp = -1` (`W',B'≤0`), base values `Wv = 1 ≥ Bv = 0`,
`Vpp = 0`, `χ = -1`, `lam = 1`, `Wv − Zv = 0` (`W = Z`, the equality endpoint of
`W ≤ Z`).  Then the chemo term is `m·Vp·(0 − 1·(−1)) = 2·(−1)·1 = −2`, and the
residual RHS `= 0 − (−1)·(−2) = −2 < 0`. -/

/-- The residual's RHS as a function of the decomposed scalars, with the chemo
flux difference replaced by its `stepFlux_diff_split` value. -/
def residualScalar
    (m χ lam Wv Zv Bv Wp Bp Vp Vpp : ℝ) : ℝ :=
  lam * (Wv - Zv)
    - χ * ( m * Vp * (Bv ^ (m - 1) * Bp - Wv ^ (m - 1) * Wp)
            + (Bv ^ m - Wv ^ m) * Vpp )

/-- **The bare pointwise residual is FALSE under the signed-gradient data.**
There is a scalar assignment with `1 ≤ m`, `χ ≤ 0`, `0 < lam`, `Vp ≤ 0`,
`Wp ≤ 0`, `Bp ≤ 0`, `0 ≤ Bv ≤ Wv` (range), and `Wv ≤ Zv` (the `W ≤ Z` step
relation, here at equality), for which `residualScalar … < 0`.  Hence (★) is not
a consequence of the trapped/antitone signs alone. -/
theorem gradientResidual_not_signed_pointwise :
    ∃ m χ lam Wv Zv Bv Wp Bp Vp Vpp : ℝ,
      (1 ≤ m) ∧ (χ ≤ 0) ∧ (0 < lam) ∧ (Vp ≤ 0) ∧ (Wp ≤ 0) ∧ (Bp ≤ 0)
        ∧ (0 ≤ Bv) ∧ (Bv ≤ Wv) ∧ (Wv ≤ Zv)
        ∧ residualScalar m χ lam Wv Zv Bv Wp Bp Vp Vpp < 0 := by
  refine ⟨2, -1, 1, 1, 1, 0, -1, -1, -1, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · -- residualScalar 2 (-1) 1 1 1 0 (-1) (-1) (-1) 0
    -- = 1*(1-1) - (-1)*( 2*(-1)*(0^1*(-1) - 1^1*(-1)) + (0^2 - 1^2)*0 )
    -- = 0 - (-1)*( -2*(0 - (-1)) + 0 ) = 0 - (-1)*(-2) = -2 < 0
    unfold residualScalar
    norm_num [Real.rpow_natCast]

/-! ## 3 — the elliptic adaptation that closes the COMPARISON

The sign genuinely closes at the CONTACT MAX `x₀` of `φ = W − B`, where the
first-order test forces `W'(x₀) = B'(x₀)`.  There the leading gradient-difference
term degenerates to the single Lipschitz increment `m V'·W'·(B^{m−1}−W^{m−1})`,
and the chemo defect is one-sidedly bounded by `C_chem·(W−B)` — the landed
`chemFlux_increment_bound`.  Fed to the landed clean elliptic maximum principle,
this gives `W ≤ B` WITHOUT the pointwise residual.

`rotheStep_le_barrier_elliptic` is the explicit statement that the residual route
target is reached by the elliptic max-principle route.  Its `hchem` hypothesis is
the genuine elliptic counterpart of §4.2's `w=uₓ` sign: the one-sided bound at the
internally-chosen contact max, supplied by `chemFlux_increment_bound`. -/

/-- **`W ≤ B` from the elliptic contact-point chemotaxis bound.**

This is `implicitStep_le_of_barrier_maxPrinciple_clean` re-exposed as the
discharge of the comparison that `RotheChemoMonotoneResidual` was carried to
provide.  Inputs are the genuine analytic/order data:

* `hstep` — `W` solves the implicit step `G_{1/λ}(W) = Z`;
* `hBsuper` — `B` is a step super-barrier `F_u(B) ≤ 0`;
* `hZB` — `Z ≤ B`;
* smallness/range/tails for `φ = W − B`;
* `hWC2`/`hBC2` — `C²`-regularity (everywhere for the smoothed `W`, at the contact
  max for the barrier `B`);
* `hchem` — the ELLIPTIC contact-point chemotaxis sign at the internally-chosen
  max, `−χ(∂stepFlux_W − ∂stepFlux_B)(x₀) ≤ C_chem·(W−B)(x₀)` (note `stepFlux =
  chemFlux`); this is exactly what `chemFlux_increment_bound` discharges from the
  contact identity `W'(x₀)=B'(x₀)` and the elliptic Lipschitz factors.

Conclusion `∀ x, W x ≤ B x` — the residual route's target, via the elliptic
adaptation, with NO pointwise residual sign. -/
theorem rotheStep_le_barrier_elliptic
    (p : CMParams) {c lam M C_chem : ℝ} {u Z W B : ℝ → ℝ} {La Lb : ℝ}
    (hlam : 0 < lam) (hM : 0 ≤ M) (hC_chem_nonneg : 0 ≤ C_chem)
    (hCB : (1 / lam) * (reactionLip p.α M + C_chem) < 1)
    (hstep : ∀ x, implicitStepOp p c (1 / lam) u W x = Z x)
    (hBsuper : ∀ x, frozenWaveOperator p c u B x ≤ 0)
    (hZB : ∀ x, Z x ≤ B x)
    (hφcont : Continuous (fun x => W x - B x))
    (hbot : Tendsto (fun x => W x - B x) atBot (𝓝 La)) (hLa : La ≤ 0)
    (htop : Tendsto (fun x => W x - B x) atTop (𝓝 Lb)) (hLb : Lb ≤ 0)
    (hWC2 : ∀ y, ContDiffAt ℝ 2 W y)
    (hBC2 : ∀ x₀, IsMaxOn (fun x => W x - B x) Set.univ x₀ → ContDiffAt ℝ 2 B x₀)
    (hrange : ∀ x₀, IsMaxOn (fun x => W x - B x) Set.univ x₀ →
        W x₀ ∈ Set.Icc (0 : ℝ) M ∧ B x₀ ∈ Set.Icc (0 : ℝ) M)
    (hchem : ∀ x₀, IsMaxOn (fun x => W x - B x) Set.univ x₀ →
        -p.χ * (deriv (stepFlux p u W) x₀ - deriv (stepFlux p u B) x₀)
          ≤ C_chem * (W x₀ - B x₀)) :
    ∀ x, W x ≤ B x := by
  -- rewrite the elliptic chemo bound through `stepFlux = chemFlux`
  have hchem' : ∀ x₀, IsMaxOn (fun x => W x - B x) Set.univ x₀ →
      -p.χ * (deriv (chemFlux p u W) x₀ - deriv (chemFlux p u B) x₀)
        ≤ C_chem * (W x₀ - B x₀) := by
    intro x₀ hx₀
    have h := hchem x₀ hx₀
    rwa [stepFlux_eq_chemFlux, stepFlux_eq_chemFlux] at h
  exact implicitStep_le_of_barrier_maxPrinciple_clean
    (p := p) (c := c) (h := 1 / lam) (M := M) (C_chem := C_chem)
    (u := u) (Z := Z) (W := W) (B := B) (La := La) (Lb := Lb)
    (one_div_pos.mpr hlam) hM hC_chem_nonneg hCB hstep hBsuper hZB
    hφcont hbot hLa htop hLb hWC2 hBC2 hrange hchem'

/-- **The contact-point elliptic chemo bound is itself discharged from the
landed `chemFlux_increment_bound`.**  At the contact max `x₀` of `φ = W − B`
(where `W'(x₀)=B'(x₀)`), with `B(x₀) ≤ W(x₀)`, the elliptic split + Lipschitz
factors give the `hchem` hypothesis above.  This certifies that the contact-point
bound — the genuine elliptic counterpart of §4.2 — is a THEOREM of the landed
elliptic structure, not a fresh axiom.  (Here `stepFlux = chemFlux`, so the
output is exactly the `hchem` of `rotheStep_le_barrier_elliptic`.) -/
theorem elliptic_contact_chem_bound
    (p : CMParams) {u W B : ℝ → ℝ} {x₀ : ℝ}
    {Cvpp Cwp L1 Lm C_chem : ℝ}
    (hχ : p.χ ≤ 0) (hBW : B x₀ ≤ W x₀)
    (hu : IsCUnifBdd u) (hu_nonneg : ∀ z, 0 ≤ u z)
    (hWdiff : DifferentiableAt ℝ W x₀) (hBdiff : DifferentiableAt ℝ B x₀)
    (hcontact : deriv W x₀ = deriv B x₀)
    (hVp : |deriv (frozenElliptic p u) x₀| ≤ 1)
    (hVpp : |deriv (deriv (frozenElliptic p u)) x₀| ≤ Cvpp) (hCvpp : 0 ≤ Cvpp)
    (hWp : |deriv W x₀| ≤ Cwp) (hCwp : 0 ≤ Cwp)
    (hL1 : |(W x₀) ^ (p.m - 1) - (B x₀) ^ (p.m - 1)| ≤ L1 * (W x₀ - B x₀))
    (hL1' : 0 ≤ L1)
    (hLm : |(W x₀) ^ p.m - (B x₀) ^ p.m| ≤ Lm * (W x₀ - B x₀)) (hLm' : 0 ≤ Lm)
    (hCchem : C_chem = (-p.χ) * (p.m * L1 * Cwp + Lm * Cvpp)) :
    -p.χ * (deriv (stepFlux p u W) x₀ - deriv (stepFlux p u B) x₀)
      ≤ C_chem * (W x₀ - B x₀) := by
  rw [stepFlux_eq_chemFlux, stepFlux_eq_chemFlux]
  have hsplit := chemFlux_increment_split p hu hu_nonneg hWdiff hBdiff hcontact
  exact chemFlux_increment_bound p hχ hBW hsplit hVp hVpp hCvpp hWp hCwp
    hL1 hL1' hLm hLm' hCchem

/-! ## Axiom audit -/

section AxiomAudit
#print axioms stepFlux_eq_chemFlux
#print axioms stepFlux_diff_split
#print axioms gradientResidual_not_signed_pointwise
#print axioms rotheStep_le_barrier_elliptic
#print axioms elliptic_contact_chem_bound
end AxiomAudit

/-! ## FINAL NOTE — what is closed, what is irreducible

* `RotheChemoMonotoneResidual` / (★) is **REFUTED** as a bare pointwise sign under
  the trapped/antitone gradient data (`gradientResidual_not_signed_pointwise`):
  the gradient-difference term `m V'·(B^{m−1}B' − W^{m−1}W')` is sign-indefinite
  and `λ(W−Z) ≤ 0` cannot rescue it.  No elliptic-gradient lemma discharges it
  pointwise — the §4.2 `w=uₓ` argument signs the gradient at a CONTACT extremum,
  not everywhere.

* The genuine **elliptic counterpart** of §4.2 is the CONTACT-POINT bound
  `elliptic_contact_chem_bound` (a theorem of the landed elliptic split +
  Lipschitz factors), which feeds the landed clean elliptic maximum principle to
  give the residual's downstream target `W ≤ B` directly
  (`rotheStep_le_barrier_elliptic`).  Hence `RotheChemoMonotoneResidual` is
  **redundant** for the construction: the live producer already routes through
  this max-principle path (`rotheStep_le_barrier` →
  `implicitStep_le_of_barrier_maxPrinciple_clean`).

* The **irreducible analytic input** that remains is therefore not a pointwise
  gradient sign but the elliptic Lipschitz/curvature factor data at the contact
  max — `|V'|≤1`, `|V''|≤Cvpp`, `|W'|≤Cwp`, and the `s↦s^{m−1}`,`s↦s^m`
  MVT/Lipschitz constants on `[0,M]` — all already landed and consumed.  The
  parabolic-construction "add" the residual hypothesis seemed to demand is NOT
  needed: the elliptic adaptation closes the comparison through the contact point.
-/

end ShenWork.Paper1
