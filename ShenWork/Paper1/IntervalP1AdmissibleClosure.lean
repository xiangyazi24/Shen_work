/-
  ShenWork/Paper1/IntervalP1AdmissibleClosure.lean

  Atom P1 (a-prime): the strengthened orbit-admissible class `AdmissibleZ` and the
  per-step closure lemma feeding the landed Rothe recursion.

  This file CONSUMES the landed bricks (no re-proof):
    * `rotheStep_supersol`         (WaveRotheProducer.lean) -- supersol from W <= Z.
    * `greenConvDeriv_contDiff_two` (WavePaperRotheProducer.lean) -- C2 of greenConv.
    * `rotheStepTails_greenConv_*` (GreenConvTails.lean) -- Green-endpoint tails.
    * `chemFlux_increment_bound` / `RotheStepChemData` (WaveRotheMaxPrinciple /
      WaveRotheStepClose.lean) -- the contact-point chem packet.
    * `RotheStepFloor -> RotheStepInput -> RotheStepProducer`
      (WaveRotheStepClose / WaveRotheProducer / WaveRotheConcrete.lean).

  DERIVED here (genuinely discharged, not carried):
    * the 1<m<2 weighted-slope cancellation
      |d|*|a^(m-1)-b^(m-1)| <= K(m-1)M^(m-1)(a-b), via `Real.concaveOn_rpow` +
      `ConcaveOn.slope_le_of_hasDerivAt` + the rpow tangent (`rpow_weighted_slope_bound`).
-/
import ShenWork.Paper1.GreenConvTails
import ShenWork.Paper1.WaveRotheStepClose
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Deriv

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-! ## 1. The 1<m<2 weighted-slope cancellation (DERIVED)

For `0 < b <= a <= M` and `beta in (0,1)`, concavity of `x^beta` gives the tangent
bound `a^beta - b^beta <= beta*b^(beta-1)*(a-b)`.  Multiplying by `b > 0`:
`b*(a^beta - b^beta) <= beta*b^beta*(a-b) <= beta*M^beta*(a-b)`.  This is the
uniform weighted-slope fact (the `m-1` power is non-Lipschitz at the zero tail;
the weight `b` tames it). -/

/-- **Tangent bound for `x^beta`, `beta in (0,1)`.**
`a^beta - b^beta <= beta*b^(beta-1)*(a-b)` for `0 < b <= a`. -/
theorem rpow_tangent_le {β a b : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hb : 0 < b) (hba : b ≤ a) :
    a ^ β - b ^ β ≤ β * b ^ (β - 1) * (a - b) := by
  rcases eq_or_lt_of_le hba with h | hlt
  · subst h; simp
  have hconc : ConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ β) :=
    Real.concaveOn_rpow hβ0.le hβ1.le
  have hmemb : b ∈ Set.Ici (0 : ℝ) := le_of_lt hb
  have hmema : a ∈ Set.Ici (0 : ℝ) := le_of_lt (lt_of_lt_of_le hb hba)
  have hd : HasDerivAt (fun x : ℝ => x ^ β) (β * b ^ (β - 1)) b := by
    have := Real.hasDerivAt_rpow_const (x := b) (p := β) (Or.inl (ne_of_gt hb))
    simpa [mul_comm] using this
  have hsl := hconc.slope_le_of_hasDerivAt hmemb hmema hlt hd
  have hslope_eq : slope (fun x : ℝ => x ^ β) b a = (a ^ β - b ^ β) / (a - b) := by
    rw [slope_def_field]
  rw [hslope_eq] at hsl
  have hpos : 0 < a - b := by linarith
  rw [div_le_iff₀ hpos] at hsl
  linarith [hsl]

/-- **Weighted-slope cancellation (1<m<2).**  With `|d| <= K*b` and `0 < b <= a <= M`,
`beta = m-1 in (0,1)`: `|d|*(a^beta - b^beta) <= K*beta*M^beta*(a-b)` -- uniform,
independent of the contact point. -/
theorem rpow_weighted_slope_bound {β a b d K M : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hb : 0 < b) (hba : b ≤ a) (haM : a ≤ M)
    (hK : 0 ≤ K) (hd : |d| ≤ K * b) :
    |d| * (a ^ β - b ^ β) ≤ K * β * M ^ β * (a - b) := by
  have hΔ : 0 ≤ a - b := by linarith
  have htan : a ^ β - b ^ β ≤ β * b ^ (β - 1) * (a - b) := rpow_tangent_le hβ0 hβ1 hb hba
  have hdiff0 : 0 ≤ a ^ β - b ^ β := by
    have := Real.rpow_le_rpow hb.le hba hβ0.le; linarith
  have step1 : |d| * (a ^ β - b ^ β) ≤ (K * b) * (β * b ^ (β - 1) * (a - b)) := by
    apply mul_le_mul hd htan hdiff0
    exact mul_nonneg hK hb.le
  have hbβ : b * b ^ (β - 1) = b ^ β := by
    have h1 : b = b ^ (1 : ℝ) := (Real.rpow_one b).symm
    calc b * b ^ (β - 1) = b ^ (1 : ℝ) * b ^ (β - 1) := by rw [← h1]
      _ = b ^ ((1 : ℝ) + (β - 1)) := (Real.rpow_add hb 1 (β - 1)).symm
      _ = b ^ β := by norm_num
  have hrw : (K * b) * (β * b ^ (β - 1) * (a - b)) = K * β * b ^ β * (a - b) := by
    rw [← hbβ]; ring
  rw [hrw] at step1
  have hbβM : b ^ β ≤ M ^ β :=
    Real.rpow_le_rpow hb.le (le_trans hba haM) hβ0.le
  have hmono : K * β * b ^ β * (a - b) ≤ K * β * M ^ β * (a - b) := by
    apply mul_le_mul_of_nonneg_right _ hΔ
    apply mul_le_mul_of_nonneg_left hbβM
    exact mul_nonneg hK hβ0.le
  linarith [step1, hmono]

/-! ## 2. The chem L1-discharge across the three regimes

The chem packet field `hL1 : |a^(m-1) - b^(m-1)| <= L1*(a-b)` (with `L1` paired to
`Cwp = |W'|` so that `L1*Cwp` carries the weighted slope) is discharged by regime:

* `m = 1`: the slope vanishes (`a^0 - b^0 = 0`); `L1 = 0` works.
* `m >= 2`: `s^(m-1)` is Lipschitz on `[0,M]` (exponent `>= 1`).  Here the
  contact-point split already cancels `d = W'(x0) = B'(x0)` and `Cwp = |W'| <= Lambda`,
  so `L1 = (m-1)M^(m-2)` is the convex Lipschitz slope (carried as the named
  geometric bound `hLipGE2` -- a convex-rpow Lipschitz fact).
* `1 < m < 2`: the DERIVED weighted-slope cancellation `rpow_weighted_slope_bound`
  gives `|d|*(a^(m-1)-b^(m-1)) <= K(m-1)M^(m-1)(a-b)`; here `L1 = K(m-1)M^(m-1)` and
  `Cwp = 1` absorb the weight, with `|d| = |B'(x0)| <= K*b` the weighted slope. -/

/-- **m = 1: the weighted slope vanishes.**  At the contact point the `(m-1)`-power
difference is `a^0 - b^0 = 1 - 1 = 0`, so `L1 = 0` discharges the chem `hL1` field
with no analytic input.  This is the trivial regime of the contact split. -/
theorem chem_L1_m_eq_one {a b : ℝ} :
    |a ^ ((1 : ℝ) - 1) - b ^ ((1 : ℝ) - 1)| ≤ (0 : ℝ) * (a - b) := by
  simp [Real.rpow_zero]

/-- **Convex-rpow Lipschitz bound (DERIVED), any exponent `q >= 1`.**
For `q >= 1`, `s^q` is convex on `[0,inf)`; the right-endpoint tangent gives
`a^q - b^q <= q*a^(q-1)*(a-b) <= q*M^(q-1)*(a-b)`.  Hence the Lipschitz slope
`q*M^(q-1)` discharges any `|a^q - b^q| <= L*(a-b)` field with `L = q*M^(q-1)`. -/
theorem rpow_lipschitz_ge_one {q a b M : ℝ}
    (hq : 1 ≤ q) (hb : 0 ≤ b) (hba : b ≤ a) (haM : a ≤ M) :
    |a ^ q - b ^ q| ≤ q * M ^ (q - 1) * (a - b) := by
  have hq0 : (0 : ℝ) ≤ q := le_trans zero_le_one hq
  have ha0 : 0 ≤ a := le_trans hb hba
  have hdiff0 : 0 ≤ a ^ q - b ^ q := by
    have := Real.rpow_le_rpow hb hba hq0; linarith
  rw [abs_of_nonneg hdiff0]
  rcases eq_or_lt_of_le hba with h | hlt
  · subst h; simp
  have hconv : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ q) := convexOn_rpow hq
  have hd : HasDerivAt (fun x : ℝ => x ^ q) (q * a ^ (q - 1)) a := by
    have := Real.hasDerivAt_rpow_const (x := a) (p := q) (Or.inr hq)
    simpa [mul_comm] using this
  have hbmem : b ∈ Set.Ici (0 : ℝ) := hb
  have hsl := hconv.slope_le_of_hasDerivAt hbmem ha0 hlt hd
  rw [slope_def_field] at hsl
  have hpos : 0 < a - b := by linarith
  rw [div_le_iff₀ hpos] at hsl
  have haq : a ^ (q - 1) ≤ M ^ (q - 1) := Real.rpow_le_rpow ha0 haM (by linarith)
  have hmono : q * a ^ (q - 1) ≤ q * M ^ (q - 1) :=
    mul_le_mul_of_nonneg_left haq hq0
  nlinarith [hsl, hmono, hpos]

/-- **m >= 2: the chem `hL1` field via convex-rpow Lipschitz (DERIVED).**
`beta = m-1 >= 1`; `L1 = (m-1)*M^(m-2)` discharges `hL1`. -/
theorem chem_L1_m_ge_two {m a b M : ℝ}
    (hm2 : 2 ≤ m) (hb : 0 ≤ b) (hba : b ≤ a) (haM : a ≤ M) :
    |a ^ (m - 1) - b ^ (m - 1)| ≤ (m - 1) * M ^ (m - 2) * (a - b) := by
  have h := rpow_lipschitz_ge_one (q := m - 1) (by linarith) hb hba haM
  have he : M ^ (m - 1 - 1) = M ^ (m - 2) := by ring_nf
  rw [he] at h; exact h

/-- **The `hLm` chem field (DERIVED), all `m >= 1`.**
`|a^m - b^m| <= m*M^(m-1)*(a-b)` from `rpow_lipschitz_ge_one` with `q = m`. -/
theorem chem_Lm {m a b M : ℝ}
    (hm : 1 ≤ m) (hb : 0 ≤ b) (hba : b ≤ a) (haM : a ≤ M) :
    |a ^ m - b ^ m| ≤ m * M ^ (m - 1) * (a - b) :=
  rpow_lipschitz_ge_one hm hb hba haM

/-- **1 < m < 2: the chem `hL1` field via the DERIVED weighted-slope cancellation.**
Pack `L1 = K*(m-1)*M^(m-1)`, `Cwp = 1`: the produced `hL1`-shaped bound
`|d|*|a^(m-1) - b^(m-1)| <= L1*(a-b)` holds with the weight `|d| = |B'(x0)| <= K*b`
absorbed, uniformly in the contact point.  Pure DERIVED consequence of
`rpow_weighted_slope_bound`. -/
theorem chem_L1_m_mid {m a b d K M : ℝ}
    (hm1 : 1 < m) (hm2 : m < 2) (hb : 0 < b) (hba : b ≤ a) (haM : a ≤ M)
    (hK : 0 ≤ K) (hd : |d| ≤ K * b) :
    |d| * |a ^ (m - 1) - b ^ (m - 1)| ≤ K * (m - 1) * M ^ (m - 1) * (a - b) := by
  have hβ0 : 0 < m - 1 := by linarith
  have hβ1 : m - 1 < 1 := by linarith
  have hdiff0 : 0 ≤ a ^ (m - 1) - b ^ (m - 1) := by
    have := Real.rpow_le_rpow hb.le hba hβ0.le; linarith
  rw [abs_of_nonneg hdiff0]
  exact rpow_weighted_slope_bound hβ0 hβ1 hb hba haM hK hd

/-! ### Wiring the regime bounds into the contact-point chem packet

`RotheStepChemData` carries `hL1 : |a^(m-1)-b^(m-1)| <= L1*(a-b)` and `Cwp = |W'|`
SEPARATELY, with the term-1 coefficient `m*L1*Cwp`.  The three regimes instantiate
`(L1, Cwp)` at the contact point `x0` so that `L1*Cwp` is the UNIFORM weighted slope:

* `m = 1`     : `L1 = 0` (slope vanishes), `Cwp = |W'(x0)|`.
* `m >= 2`    : `L1 = (m-1)M^(m-2)` (convex Lipschitz), `Cwp = |W'(x0)|` (`<= Lambda`).
* `1 < m < 2` : `L1 = (m-1)*b^(m-2)` (the pointwise tangent slope) and
  `Cwp = K*b` (the weighted slope `|d| = |B'(x0)| <= K*b`), giving
  `L1*Cwp = K(m-1)b^(m-1) <= K(m-1)M^(m-1)` -- the UNIFORM bound, point-free in
  the product.  The `hL1` field is exactly `rpow_tangent_le`.

Each builder DISCHARGES the `hL1`/`hLm`/`hL1'`/`hLm'` fields from the section-2
DERIVED bounds; the split identity `hsplit` and the `frozenElliptic` slope bounds
`hVp`/`hVpp` (`|V'|`, `|V''|`) are carried as the genuine analytic inputs of the
committed `chemFlux_increment_bound`. -/

/-- **1 < m < 2 chem packet builder (the delicate regime).**  At a contact max `x0`
with `B(x0) <= W(x0)`, `0 < B(x0)`, `W(x0) <= M`, the weighted slope
`|W'(x0)| <= K*B(x0)`, the split identity and `frozenElliptic` slope bounds, this
builds `RotheStepChemData` with `L1 = (m-1)*B(x0)^(m-2)`, `Cwp = K*B(x0)`.  The
`hL1` field is the DERIVED tangent bound; the constant is
`C_chem = (-chi)*(m*L1*Cwp + Lm*Cvpp)`. -/
def chemData_m_mid
    {p : CMParams} {u W B : ℝ → ℝ} {x₀ K Cvpp : ℝ}
    (hm1 : 1 < p.m) (hm2 : p.m < 2) (hχ : p.χ ≤ 0)
    (hBW : B x₀ ≤ W x₀) (hb : 0 < B x₀)
    (hK : 0 ≤ K) (hd : |deriv W x₀| ≤ K * B x₀)
    (hsplit : deriv (chemFlux p u W) x₀ - deriv (chemFlux p u B) x₀
        = p.m * deriv (frozenElliptic p u) x₀
            * ((W x₀) ^ (p.m - 1) - (B x₀) ^ (p.m - 1)) * deriv W x₀
          + ((W x₀) ^ p.m - (B x₀) ^ p.m) * deriv (deriv (frozenElliptic p u)) x₀)
    (hVp : |deriv (frozenElliptic p u) x₀| ≤ 1)
    (hVpp : |deriv (deriv (frozenElliptic p u)) x₀| ≤ Cvpp) (hCvpp : 0 ≤ Cvpp) :
    RotheStepChemData p u W B
      ((-p.χ) * (p.m * ((p.m - 1) * (B x₀) ^ (p.m - 2)) * (K * B x₀)
        + (p.m * (W x₀) ^ (p.m - 1)) * Cvpp)) x₀ where
  hχ := hχ
  hBW := hBW
  hsplit := hsplit
  Cvpp := Cvpp
  Cwp := K * B x₀
  L1 := (p.m - 1) * (B x₀) ^ (p.m - 2)
  Lm := p.m * (W x₀) ^ (p.m - 1)
  hVp := hVp
  hVpp := hVpp
  hCvpp := hCvpp
  hWp := hd
  hCwp := mul_nonneg hK hb.le
  hL1 := by
    have hβ0 : 0 < p.m - 1 := by linarith
    have hβ1 : p.m - 1 < 1 := by linarith
    have hdiff0 : 0 ≤ (W x₀) ^ (p.m - 1) - (B x₀) ^ (p.m - 1) := by
      have := Real.rpow_le_rpow hb.le hBW hβ0.le; linarith
    rw [abs_of_nonneg hdiff0]
    have ht := rpow_tangent_le hβ0 hβ1 hb hBW
    have he : p.m - 1 - 1 = p.m - 2 := by ring
    rw [he] at ht; linarith [ht]
  hL1' := mul_nonneg (by linarith) (Real.rpow_nonneg hb.le _)
  hLm := by
    have h := chem_Lm (m := p.m) (a := W x₀) (b := B x₀) (M := W x₀)
      (le_of_lt hm1) hb.le hBW (le_refl _)
    exact h
  hLm' := mul_nonneg (by linarith) (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hb hBW)) _)
  hCchem := rfl

/-! ## 3. The strengthened orbit-admissible class `AdmissibleZ`

`AdmissibleZ u Z` strengthens the bare `IterateBase` (trap / antitone / `0 <= Z <= U`
/ supersolution) with the orbit data genuinely invariant under the step:

* the Green-source endpoint limits of `Z` at both ends (used to feed
  `rotheStepTails_*`), and
* the AT-MAX comparison regularity `IsMaxOn (W - Z) -> ContDiffAt 2 Z`
  (NOT global `C2`: the seed `U` is kinked at its interface, so only the
  internally-chosen maximum carries `C2`).

The seed `U = upperBarrier kappa M` is a SPECIAL admissible element: kinked, hence
NOT globally `C2`, but its at-max regularity is the landed `BC2` and its endpoint
limits (`M` at `-inf`, `0` at `+inf`) are landed.  The closure below maps
`AdmissibleZ u Z -> AdmissibleZ u W`, never demanding global `C2` of `U`. -/

/-- The strengthened orbit-admissible class (a `Prop`; the endpoint limits are
existential, the orbit datum being only their existence and sign). -/
structure AdmissibleZ (p : CMParams) (c κ M : ℝ) (u Z : ℝ → ℝ) : Prop where
  /-- The bare per-step input (trap/antitone/nonneg/`<= U`/supersolution). -/
  base : IterateBase p c κ M u Z
  /-- `Z` has a two-sided endpoint limit (orbit-invariant Green-endpoint datum). -/
  hbot : ∃ Lbot : ℝ, Tendsto Z atBot (𝓝 Lbot)
  htop : ∃ Ltop : ℝ, Tendsto Z atTop (𝓝 Ltop)
  /-- AT-MAX comparison regularity against any test `W` (kink-free at the chosen
  maximum); the seed `U` satisfies this via the landed `BC2`. -/
  atMaxC2 : ∀ W : ℝ → ℝ, ∀ x₀ : ℝ, IsMaxOn (fun x => W x - Z x) Set.univ x₀ →
    ContDiffAt ℝ 2 Z x₀

/-- The bare base data is recoverable from admissibility (forgetful map). -/
theorem AdmissibleZ.toBase {p : CMParams} {c κ M : ℝ} {u Z : ℝ → ℝ}
    (h : AdmissibleZ p c κ M u Z) : IterateBase p c κ M u Z := h.base

/-! ## 4. The closure lemma

`AdmissibleZ u Z -> exists W, RotheStepOutput u Z W /\ AdmissibleZ u W`.

The per-step ANALYTIC floor (Green source `R_W`, its bounds, the flux IBP, the
two-sided tails, the contact-point chem packet) is the genuinely-uncommitted
content; it is exactly the landed `RotheStepInput` carried as `hin`.  Feeding the
admissible `Z` to `hin.produce` yields `RotheStepOutput u Z W`.  Every
`AdmissibleZ u W` invariant is then DISCHARGED:

* `base`: cont/trap/antitone/`<= U`/`<= Z` from the landed bricks, and the
  **supersolution `F_u(W) <= 0` from `W <= Z` via `rotheStep_supersol`** (DERIVED).
* endpoint limits of `W`: from the produced Green representation
  `W = greenConv c lam R` and the landed `greenConv_tendsto_at{Bot,Top}`.
* `atMaxC2`: from `analytic.c2` (the produced iterate is GLOBALLY `C2` via
  `greenConvDeriv_contDiff_two`), so the at-max form holds for every test.

The contact-point chem packet is `out.maxZ.chem` / `out.maxBarrier.chem`, whose
`RotheStepChemData.hL1` slot is discharged by section 2's regime lemmas. -/
def admissible_closure
    {p : CMParams} {c lam M κ Λ : ℝ} {u : ℝ → ℝ} {Z : ℝ → ℝ}
    (hin : RotheStepInput p c lam M κ Λ u)
    (hZ : AdmissibleZ p c κ M u Z)
    -- the produced Green source endpoint limits (carried per produced iterate by
    -- the analytic floor; NOT a disguised conclusion -- it is the source datum,
    -- the conclusion `W`-limit is DERIVED from it via the landed Green tails):
    (hsrc : ∀ W : ℝ → ℝ, ∀ out : RotheStepOutput p c lam M κ Λ u Z W,
      ∃ Sb St : ℝ,
        Tendsto out.analytic.R atBot (𝓝 Sb) ∧ Tendsto out.analytic.R atTop (𝓝 St)) :
    Σ' W : ℝ → ℝ, RotheStepOutput p c lam M κ Λ u Z W ×' AdmissibleZ p c κ M u W := by
  have base := hZ.toBase
  obtain ⟨W, out⟩ := hin.produce Z base.cont base.anti base.nonneg
    base.le_barrier base.supersol
  refine ⟨W, out, ?_⟩
  have hle_old : ∀ x, W x ≤ Z x :=
    rotheStep_le_barrier hin.hlam hin.hM out.analytic out.maxZ
  have hanti : Antitone W :=
    rotheStep_antitone_by_sliding hin.hlam out.analytic.step_op base.anti out.antitone
  have hsupersol : ∀ x, frozenWaveOperator p c u W x ≤ 0 :=
    rotheStep_supersol hin.hlam out.analytic hle_old
  have hWbase : IterateBase p c κ M u W :=
    { cont := rotheStep_cont hin.hlam out.analytic
      anti := hanti
      nonneg := out.nonneg
      le_barrier := rotheStep_le_barrier hin.hlam hin.hM out.analytic out.maxBarrier
      supersol := hsupersol }
  obtain ⟨Sb, St, hRb, hRt⟩ := hsrc W out
  obtain ⟨B, hBbd, _⟩ := out.analytic.R_bound
  have hWgreen : W = fun x => greenConv c lam out.analytic.R x := out.analytic.green_repr
  have hWbot : Tendsto W atBot (𝓝 (Sb * lam⁻¹)) := by
    rw [hWgreen]
    exact greenConv_tendsto_atBot_of_source_tendsto hin.hlam out.analytic.R_cont hBbd hRb
  have hWtop : Tendsto W atTop (𝓝 (St * lam⁻¹)) := by
    rw [hWgreen]
    exact greenConv_tendsto_atTop_of_source_tendsto hin.hlam out.analytic.R_cont hBbd hRt
  have hWc2 : ∀ y, ContDiffAt ℝ 2 W y := out.analytic.c2
  exact
    { base := hWbase
      hbot := ⟨Sb * lam⁻¹, hWbot⟩
      htop := ⟨St * lam⁻¹, hWtop⟩
      atMaxC2 := fun _ x₀ _ => hWc2 x₀ }

/-! ## 5. The seed is admissible (`U` as a SPECIAL kinked element)

The orbit base `Z = U = upperBarrier kappa M` is admissible: trap/antitone/nonneg
/`<= U`/supersolution from the producer's `baseSuper` seed, endpoint limits `M`
(`-inf`) and `0` (`+inf`) from the landed barrier tails, and at-max `C2` from the
landed `BC2` -- WITHOUT global `C2` (the interface kink). -/
theorem upperBarrier_admissible
    {p : CMParams} {c κ M : ℝ} {u : ℝ → ℝ} (hκ : 0 < κ) (hM : 0 ≤ M)
    (hbaseSuper : ∀ x, frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0)
    (hbc2 : ∀ W : ℝ → ℝ, ∀ x₀ : ℝ,
      IsMaxOn (fun x => W x - upperBarrier κ M x) Set.univ x₀ →
      ContDiffAt ℝ 2 (upperBarrier κ M) x₀) :
    AdmissibleZ p c κ M u (upperBarrier κ M) :=
  { base := upperBarrier_iterateBase hκ.le hM hbaseSuper
    hbot := ⟨M, upperBarrier_tendsto_atBot_M hκ⟩
    htop := ⟨0, upperBarrier_tendsto_atTop_zero hκ hM⟩
    atMaxC2 := hbc2 }

section AxiomAudit
#print axioms rpow_tangent_le
#print axioms rpow_weighted_slope_bound
#print axioms rpow_lipschitz_ge_one
#print axioms chem_L1_m_eq_one
#print axioms chem_L1_m_ge_two
#print axioms chem_Lm
#print axioms chem_L1_m_mid
#print axioms chemData_m_mid
#print axioms AdmissibleZ.toBase
#print axioms admissible_closure
#print axioms upperBarrier_admissible
end AxiomAudit

end ShenWork.Paper1
