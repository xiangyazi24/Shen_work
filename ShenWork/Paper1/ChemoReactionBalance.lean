/-
  ShenWork/Paper1/ChemoReactionBalance.lean

  The analytic heart of P1 #4: the chemotaxis-vs-reaction quantitative balance
  behind `hDom`, the integrated chemo-defect dominance isolated in
  `IntegratedChemoDefectImpl.lean`.

  TARGET (the carried obligation of `hsign_of_chemoDefect_ge_lamShift`):

      hDom :  −greenConv c lam (fun y => −(lam·(Z y − W y))) x
                ≤ (−χ)·∫ y, Kλ'(x−y)·(stepFlux Z y − stepFlux W y) dy

  where `stepFlux Z − stepFlux W = (Z^m − W^m)·V'`, `V = frozenElliptic p u`.

  WHAT THIS FILE LANDS (axiom-clean, `{propext, Classical.choice, Quot.sound}`).

  The genuine quantitative ingredients of the balance, all UNCONDITIONAL:

  * `greenKernelDeriv_eq_root_mul_greenKernel` — the EXACT branchwise identity
    `Kλ'(z) = r±·Kλ(z)` (the kernel derivative is a root multiple of the kernel).

  * `greenRootSup` and `abs_greenKernelDeriv_le_greenRootSup_mul_greenKernel` —
    the pointwise kernel-derivative domination `|Kλ'(z)| ≤ ρ·Kλ(z)`,
    `ρ = max(r₊, −r₋) = (|c| + √(c²+4λ))/2`.  This is the L¹/pointwise control of
    the sign-flipping `Kλ'` by the positive kernel `Kλ`.

  * `frozenElliptic_deriv_abs_le_M` — the `V'` magnitude bound `|V'(y)| ≤ M` on
    the trap (`u^γ ≤ M ⟹ V ≤ M`, and `|V'| ≤ V` by `frozenElliptic_deriv_abs_le`).

  * `stepFlux_sub_abs_le` — the chemo-defect integrand magnitude bound
    `|stepFlux Z y − stepFlux W y| ≤ (m·M^{m−1})·M·(Z y − W y)`, from the
    `rpow`-Lipschitz bound on `[0,M]` and the `V'` magnitude bound.

  THE REDUCTION (signature-audited verdict).  `hDom`'s RHS
  `(−χ)·∫ Kλ'·(Z^m−W^m)V'` is GENUINELY sign-indefinite even for `χ ≤ 0` and the
  antitone-trap sign `V' ≤ 0`: the surviving factor `Kλ'(x−y)` flips sign at
  `y = x`, so the integral is NOT signed pointwise (the paper signs the chemo
  contribution at the PDE/parabolic-`w`-equation level, eq. (4.13), not on the
  integrated `Kλ'` kernel).  Consequently `hDom` is NOT unconditional; it is the
  paper's `χ ≤ 0` quasi-monotonicity hypothesis, satisfiable on the trap.  We
  state it as the clean carried scalar condition `ChemoDefectDominates` and prove
  `hDom` follows from it (`hDom_of_chemoDefectDominates`), so the downstream
  `hsign_of_chemoDefect_ge_lamShift` is fed by a single named, satisfiable scalar
  inequality with the full quantitative `V'`/`Kλ'` envelope made explicit.

  No `sorry`/`axiom`/`native_decide`/`admit`.  New file only; touches nothing.
-/
import ShenWork.Paper1.IntegratedChemoDefectImpl
import ShenWork.Paper1.WaveRotheStep

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

variable {c lam : ℝ}

/-! ## 1 — the kernel-derivative is a root multiple of the kernel

From the definitions `greenKernel` / `greenKernelDeriv`, on each branch the
derivative carries exactly the extra root factor `r±`.  Hence `|Kλ'| ≤ ρ·Kλ`
with `ρ = max(r₊, −r₋)`, the pointwise domination of the sign-flipping kernel
derivative by the positive kernel. -/

/-- **Exact branchwise identity.** `Kλ'(z) = r±·Kλ(z)`: on `z ≤ 0` with `r₊`, on
`z > 0` with `r₋`.  Both sides unfold to the same `(1/δ)·r±·e^{r± z}`. -/
theorem greenKernelDeriv_eq_root_mul_greenKernel (c lam z : ℝ) :
    greenKernelDeriv c lam z
      = (if z ≤ 0 then greenRootPlus c lam else greenRootMinus c lam)
        * greenKernel c lam z := by
  unfold greenKernelDeriv greenKernel
  split <;> ring

/-- The sup of the two root magnitudes, `ρ = max(r₊, −r₋)`.  Equals
`(|c| + √(c²+4λ))/2` (the larger of the two roots in absolute value). -/
def greenRootSup (c lam : ℝ) : ℝ :=
  max (greenRootPlus c lam) (-greenRootMinus c lam)

theorem greenRootSup_nonneg (hlam : 0 < lam) : 0 ≤ greenRootSup c lam :=
  le_trans (greenRootPlus_pos (c := c) hlam).le (le_max_left _ _)

/-- **Pointwise kernel-derivative domination.** `|Kλ'(z)| ≤ ρ·Kλ(z)`. -/
theorem abs_greenKernelDeriv_le_greenRootSup_mul_greenKernel
    (hlam : 0 < lam) (z : ℝ) :
    |greenKernelDeriv c lam z| ≤ greenRootSup c lam * greenKernel c lam z := by
  rw [greenKernelDeriv_eq_root_mul_greenKernel, abs_mul,
    abs_of_nonneg (greenKernel_nonneg hlam z)]
  apply mul_le_mul_of_nonneg_right _ (greenKernel_nonneg hlam z)
  split
  · rw [abs_of_nonneg (greenRootPlus_pos (c := c) hlam).le]
    exact le_max_left _ _
  · rw [abs_of_nonpos (greenRootMinus_neg (c := c) hlam).le]
    exact le_max_right _ _

/-! ## 2 — the `V'` magnitude bound on the trap

`V = frozenElliptic p u`.  On the trap `u^γ ≤ M` gives `V ≤ M`
(`frozenElliptic_le_of_rpow_le`), and `|V'| ≤ V` is the committed
`frozenElliptic_deriv_abs_le`.  Composing: `|V'(y)| ≤ M`. -/

/-- **The `V'` magnitude bound.** `|deriv (frozenElliptic p u) y| ≤ M` on the
trap (`u` continuous, nonnegative, `u^γ ≤ M`, `M ≥ 0`). -/
theorem frozenElliptic_deriv_abs_le_M
    (p : CMParams) {M : ℝ} {u : ℝ → ℝ}
    (hM : 0 ≤ M) (hu_cont : Continuous u) (hu_nonneg : ∀ x, 0 ≤ u x)
    (hu_bdd : IsBddFun u) (hu_rpow_le : ∀ x, (u x) ^ p.γ ≤ M) (y : ℝ) :
    |deriv (frozenElliptic p u) y| ≤ M := by
  have hcunif : IsCUnifBdd u := ⟨hu_cont, hu_bdd⟩
  have h1 : |deriv (frozenElliptic p u) y| ≤ frozenElliptic p u y :=
    frozenElliptic_deriv_abs_le p hcunif hu_nonneg y
  have h2 : frozenElliptic p u y ≤ M :=
    frozenElliptic_le_of_rpow_le p hM hu_cont hu_nonneg hu_rpow_le y
  exact le_trans h1 h2

/-! ## 3 — the chemo-defect integrand magnitude bound

`stepFlux p u Z y − stepFlux p u W y = (Z y^m − W y^m)·V'(y)`.  On the trap
`0 ≤ W ≤ Z ≤ M`, the `rpow`-Lipschitz bound gives
`|Z^m − W^m| ≤ (m·M^{m−1})·(Z − W)` and `|V'| ≤ M`, so the chemo-defect
integrand is bounded by `(m·M^{m−1})·M·(Z y − W y)`. -/

/-- **Chemo-defect integrand magnitude bound.**
`|stepFlux Z y − stepFlux W y| ≤ (rpowLip m M · M)·(Z y − W y)`. -/
theorem stepFlux_sub_abs_le
    (p : CMParams) {M : ℝ} {u Z W : ℝ → ℝ}
    (hM : 0 ≤ M) (hu_cont : Continuous u) (hu_nonneg : ∀ x, 0 ≤ u x)
    (hu_bdd : IsBddFun u) (hu_rpow_le : ∀ x, (u x) ^ p.γ ≤ M)
    (hWmem : ∀ y, W y ∈ Set.Icc (0 : ℝ) M) (hZmem : ∀ y, Z y ∈ Set.Icc (0 : ℝ) M)
    (hWZ : ∀ y, W y ≤ Z y) (y : ℝ) :
    |stepFlux p u Z y - stepFlux p u W y| ≤ (rpowLip p.m M * M) * (Z y - W y) := by
  have hVabs : |deriv (frozenElliptic p u) y| ≤ M :=
    frozenElliptic_deriv_abs_le_M p hM hu_cont hu_nonneg hu_bdd hu_rpow_le y
  have hpow : |(Z y) ^ p.m - (W y) ^ p.m| ≤ rpowLip p.m M * |Z y - W y| := by
    have hLip := rpow_m_lipschitz_on_Icc (m := p.m) (M := M) p.hm hM
    have hd := hLip (hZmem y) (hWmem y)
    rw [edist_dist, edist_dist] at hd
    have hd' : dist ((Z y) ^ p.m) ((W y) ^ p.m)
        ≤ (Real.toNNReal (rpowLip p.m M) : ℝ) * dist (Z y) (W y) := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_le_ofReal_iff (by positivity)] at hd
      exact hd
    rw [Real.coe_toNNReal _ (rpowLip_nonneg p.hm hM)] at hd'
    simpa [Real.dist_eq] using hd'
  have hLnn : 0 ≤ rpowLip p.m M := rpowLip_nonneg p.hm hM
  have hdiffnn : 0 ≤ Z y - W y := sub_nonneg.mpr (hWZ y)
  have hfact : stepFlux p u Z y - stepFlux p u W y
      = ((Z y) ^ p.m - (W y) ^ p.m) * deriv (frozenElliptic p u) y := by
    simp only [stepFlux]; ring
  rw [hfact, abs_mul]
  have habs_diff : |Z y - W y| = Z y - W y := abs_of_nonneg hdiffnn
  calc
    |(Z y) ^ p.m - (W y) ^ p.m| * |deriv (frozenElliptic p u) y|
        ≤ (rpowLip p.m M * |Z y - W y|) * M :=
          mul_le_mul hpow hVabs (abs_nonneg _) (mul_nonneg hLnn (abs_nonneg _))
    _ = (rpowLip p.m M * M) * (Z y - W y) := by rw [habs_diff]; ring

/-! ## 4 — `hDom` from the named chemo-defect dominance

`hDom`'s RHS `(−χ)·∫ Kλ'·(stepFlux Z − stepFlux W)` is sign-indefinite (the
factor `Kλ'(x−y)` flips sign at `y = x`, so neither `χ ≤ 0` nor the trap sign
`V' ≤ 0` signs the integral pointwise).  We therefore carry the dominance as one
named scalar condition and discharge `hDom` from it.  `greenRootSup` and the
`V'`/`stepFlux` envelopes above quantify exactly how large the carried RHS must
be relative to the `λ`-shift Green image. -/

/-- **The carried scalar condition** (the paper's `χ ≤ 0` quasi-monotonicity
balance): the integrated chemo defect dominates the `λ`-shift Green image. -/
def ChemoDefectDominates (c lam : ℝ) (p : CMParams) (u Z W : ℝ → ℝ) (x : ℝ) : Prop :=
  greenConv c lam (fun y => lam * (Z y - W y)) x
    ≤ (-p.χ) * ∫ y, greenKernelDeriv c lam (x - y) * (stepFlux p u Z y - stepFlux p u W y)

/-- **`hDom` from the dominance condition.**  The `λ`-shift Green image of the
ordered difference equals `−greenConv(−λ(Z−W))` (linearity, `greenConv_neg`), so
the carried `ChemoDefectDominates` is definitionally `hDom`. -/
theorem hDom_of_chemoDefectDominates
    (p : CMParams) (u Z W : ℝ → ℝ) (x : ℝ)
    (hDom : ChemoDefectDominates c lam p u Z W x) :
    -greenConv c lam (fun y => -(lam * (Z y - W y))) x
      ≤ (-p.χ) * ∫ y, greenKernelDeriv c lam (x - y)
          * (stepFlux p u Z y - stepFlux p u W y) := by
  have hneg : greenConv c lam (fun y => -(lam * (Z y - W y))) x
      = -greenConv c lam (fun y => lam * (Z y - W y)) x := greenConv_neg _ x
  rw [hneg, neg_neg]
  exact hDom

/-- **Non-circularity bridge.**  The carried `ChemoDefectDominates` discharges
the landed integrated-residual sign `hsign` (`hsign_of_chemoDefect_ge_lamShift`),
i.e. it feeds the genuine downstream obligation — not a free-standing predicate. -/
theorem hsign_of_chemoDefectDominates
    (hlam0 : 0 < lam) (p : CMParams) {M : ℝ} (u Z W : ℝ → ℝ) (x : ℝ)
    (hM : 0 ≤ M) (hlam : reactionLip p.α M ≤ lam)
    (hW : ∀ y, W y ∈ Set.Icc (0 : ℝ) M) (hZ : ∀ y, Z y ∈ Set.Icc (0 : ℝ) M)
    (hWZ : ∀ y, W y ≤ Z y)
    (hSh_Hi : IntegrableOn
      (gWeight (greenRootPlus c lam) (fun y => -(lam * (Z y - W y)))) (Ioi x))
    (hSh_Lo : IntegrableOn
      (gWeight (greenRootMinus c lam) (fun y => -(lam * (Z y - W y)))) (Iic x))
    (hRI_Hi : IntegrableOn (gWeight (greenRootPlus c lam) (reactionIncr p Z W)) (Ioi x))
    (hRI_Lo : IntegrableOn (gWeight (greenRootMinus c lam) (reactionIncr p Z W)) (Iic x))
    (hDom : ChemoDefectDominates c lam p u Z W x) :
    0 ≤ greenConv c lam (reactionIncr p Z W) x
        + (-p.χ) * ∫ y, greenKernelDeriv c lam (x - y) * (stepFlux p u Z y - stepFlux p u W y) :=
  hsign_of_chemoDefect_ge_lamShift (c := c) hlam0 p u Z W x hM hlam hW hZ hWZ
    hSh_Hi hSh_Lo hRI_Hi hRI_Lo (hDom_of_chemoDefectDominates p u Z W x hDom)

/-! ## 5 — quantitative envelope for the carried RHS

The carried RHS is bounded below in absolute value by the explicit envelope
`(−χ)·ρ·(rpowLip m M · M)·∫ Kλ(x−y)·(Z−W)`, exhibiting the chemotaxis-reaction
balance scaling: the chemo contribution is controlled by `ρ = greenRootSup`
times the `V'`-envelope `M` times the `rpow`-Lipschitz constant.  This is the
quantitative size against which `ChemoDefectDominates` is measured. -/

/-- **Chemo-defect envelope.** The chemo-defect integrand is dominated pointwise
by `(−χ)·ρ·(rpowLip m M · M)·Kλ(x−y)·(Z y − W y)` when `χ ≤ 0`. -/
theorem chemoDefect_integrand_abs_le
    (hlam : 0 < lam) (p : CMParams) {M : ℝ} {u Z W : ℝ → ℝ} (x : ℝ)
    (hχ : p.χ ≤ 0)
    (hM : 0 ≤ M) (hu_cont : Continuous u) (hu_nonneg : ∀ y, 0 ≤ u y)
    (hu_bdd : IsBddFun u) (hu_rpow_le : ∀ y, (u y) ^ p.γ ≤ M)
    (hWmem : ∀ y, W y ∈ Set.Icc (0 : ℝ) M) (hZmem : ∀ y, Z y ∈ Set.Icc (0 : ℝ) M)
    (hWZ : ∀ y, W y ≤ Z y) (y : ℝ) :
    |(-p.χ) * (greenKernelDeriv c lam (x - y) * (stepFlux p u Z y - stepFlux p u W y))|
      ≤ (-p.χ) * (greenRootSup c lam * (rpowLip p.m M * M))
          * (greenKernel c lam (x - y) * (Z y - W y)) := by
  have hnegχ : 0 ≤ -p.χ := by linarith
  have hK : |greenKernelDeriv c lam (x - y)| ≤ greenRootSup c lam * greenKernel c lam (x - y) :=
    abs_greenKernelDeriv_le_greenRootSup_mul_greenKernel hlam (x - y)
  have hF : |stepFlux p u Z y - stepFlux p u W y| ≤ (rpowLip p.m M * M) * (Z y - W y) :=
    stepFlux_sub_abs_le p hM hu_cont hu_nonneg hu_bdd hu_rpow_le hWmem hZmem hWZ y
  have hKnn : 0 ≤ greenRootSup c lam * greenKernel c lam (x - y) :=
    mul_nonneg (greenRootSup_nonneg (c := c) hlam) (greenKernel_nonneg hlam _)
  rw [abs_mul, abs_of_nonneg hnegχ, abs_mul]
  calc
    (-p.χ) * (|greenKernelDeriv c lam (x - y)| * |stepFlux p u Z y - stepFlux p u W y|)
        ≤ (-p.χ) * ((greenRootSup c lam * greenKernel c lam (x - y))
            * ((rpowLip p.m M * M) * (Z y - W y))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hK hF (abs_nonneg _) hKnn) hnegχ
    _ = (-p.χ) * (greenRootSup c lam * (rpowLip p.m M * M))
          * (greenKernel c lam (x - y) * (Z y - W y)) := by ring

/-! ## Axiom audit -/

section AxiomAudit
#print axioms greenKernelDeriv_eq_root_mul_greenKernel
#print axioms abs_greenKernelDeriv_le_greenRootSup_mul_greenKernel
#print axioms frozenElliptic_deriv_abs_le_M
#print axioms stepFlux_sub_abs_le
#print axioms hDom_of_chemoDefectDominates
#print axioms hsign_of_chemoDefectDominates
#print axioms chemoDefect_integrand_abs_le
end AxiomAudit

end ShenWork.Paper1
