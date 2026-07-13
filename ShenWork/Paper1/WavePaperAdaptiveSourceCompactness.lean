import ShenWork.Paper1.WavePaperAdaptiveClosedGraph

open Filter Topology Set

noncomputable section

namespace ShenWork.Paper1

/-- Non-diagonal local-uniform continuity of the actual paper Green source.
The frozen profile, old iterate, and new iterate may vary independently; the
only first-order input is convergence of the new-iterate derivatives. -/
theorem paperStepSource_locallyUniform_nonDiagonal
    (p : CMParams) {c lam M κ : ℝ}
    {us Zs Ws : ℕ → ℝ → ℝ} {u Z W : ℝ → ℝ}
    (hM : 0 < M)
    (husTrap : ∀ n, InMonotoneWaveTrapSet κ M (us n))
    (huTrap : InMonotoneWaveTrapSet κ M u)
    (hWs0 : ∀ n x, 0 ≤ Ws n x) (hWsM : ∀ n x, Ws n x ≤ M)
    (hW0 : ∀ x, 0 ≤ W x) (hWM : ∀ x, W x ≤ M)
    (hus : LocallyUniformConverges us u)
    (hZs : LocallyUniformConverges Zs Z)
    (hWs : LocallyUniformConverges Ws W)
    (hWds : LocallyUniformConverges
      (fun n x => deriv (Ws n) x) (fun x => deriv W x))
    (hbddDerivW : LocallyBoundedOnCompacts (fun x => deriv W x)) :
    LocallyUniformConverges
      (fun n => paperStepSource p c lam (us n) (Zs n) (Ws n))
      (paperStepSource p c lam u Z W) := by
  have hM0 : 0 ≤ M := hM.le
  have hV : LocallyUniformConverges
      (fun n => frozenElliptic p (us n)) (frozenElliptic p u) :=
    frozenEllipticDependence p hM0 us u husTrap huTrap hus
  have hVd : LocallyUniformConverges
      (fun n x => deriv (frozenElliptic p (us n)) x)
      (fun x => deriv (frozenElliptic p u) x) :=
    frozenEllipticDerivDependence p hM0 us u husTrap huTrap hus
  have hpowM1 : LocallyUniformConverges
      (fun n x => (Ws n x) ^ (p.m - 1))
      (fun x => (W x) ^ (p.m - 1)) :=
    hWs.rpow_of_nonneg_le (by linarith [p.hm]) hM0 hWs0 hWsM hW0 hWM
  have hpowA : LocallyUniformConverges
      (fun n x => (Ws n x) ^ p.α) (fun x => (W x) ^ p.α) :=
    hWs.rpow_of_nonneg_le (by linarith [p.hα]) hM0 hWs0 hWsM hW0 hWM
  have hpowMG : LocallyUniformConverges
      (fun n x => (Ws n x) ^ (p.m + p.γ - 1))
      (fun x => (W x) ^ (p.m + p.γ - 1)) :=
    hWs.rpow_of_nonneg_le (by linarith [p.hm, p.hγ]) hM0
      hWs0 hWsM hW0 hWM
  have hbddW : LocallyBoundedOnCompacts W :=
    LocallyBoundedOnCompacts.of_global_bound hM0 (fun x => by
      rw [abs_of_nonneg (hW0 x)]
      exact hWM x)
  have hMγ0 : 0 ≤ M ^ p.γ := Real.rpow_nonneg hM0 p.γ
  have hbddV : LocallyBoundedOnCompacts (frozenElliptic p u) :=
    LocallyBoundedOnCompacts.of_global_bound hMγ0 (fun x => by
      rw [abs_of_nonneg (frozenElliptic_nonneg p huTrap.nonneg x)]
      exact frozenElliptic_le_rpow_of_inWaveTrapSet p hM huTrap.trap x)
  have hbddVd : LocallyBoundedOnCompacts
      (fun x => deriv (frozenElliptic p u) x) :=
    LocallyBoundedOnCompacts.of_global_bound hMγ0 (fun x =>
      le_trans
        (frozenElliptic_deriv_abs_le p huTrap.trap.cunif_bdd huTrap.nonneg x)
        (frozenElliptic_le_rpow_of_inWaveTrapSet p hM huTrap.trap x))
  have hMm10 : 0 ≤ M ^ (p.m - 1) := Real.rpow_nonneg hM0 _
  have hbddPowM1 : LocallyBoundedOnCompacts
      (fun x => (W x) ^ (p.m - 1)) :=
    LocallyBoundedOnCompacts.of_global_bound hMm10 (fun x => by
      rw [abs_of_nonneg (Real.rpow_nonneg (hW0 x) _)]
      exact Real.rpow_le_rpow (hW0 x) (hWM x) (by linarith [p.hm]))
  have hMα0 : 0 ≤ M ^ p.α := Real.rpow_nonneg hM0 _
  have hbddPowA : LocallyBoundedOnCompacts (fun x => (W x) ^ p.α) :=
    LocallyBoundedOnCompacts.of_global_bound hMα0 (fun x => by
      rw [abs_of_nonneg (Real.rpow_nonneg (hW0 x) _)]
      exact Real.rpow_le_rpow (hW0 x) (hWM x) (by linarith [p.hα]))
  have hMmg0 : 0 ≤ M ^ (p.m + p.γ - 1) := Real.rpow_nonneg hM0 _
  have hbddPowMG : LocallyBoundedOnCompacts
      (fun x => (W x) ^ (p.m + p.γ - 1)) :=
    LocallyBoundedOnCompacts.of_global_bound hMmg0 (fun x => by
      rw [abs_of_nonneg (Real.rpow_nonneg (hW0 x) _)]
      exact Real.rpow_le_rpow (hW0 x) (hWM x)
        (by linarith [p.hm, p.hγ]))
  have hVdWd : LocallyUniformConverges
      (fun n x => deriv (frozenElliptic p (us n)) x * deriv (Ws n) x)
      (fun x => deriv (frozenElliptic p u) x * deriv W x) :=
    hVd.mul hWds hbddVd hbddDerivW
  have hbddVdWd : LocallyBoundedOnCompacts
      (fun x => deriv (frozenElliptic p u) x * deriv W x) :=
    hbddVd.mul hbddDerivW
  have hchemCore : LocallyUniformConverges
      (fun n => paperWaveChemCore p (us n) (Ws n))
      (paperWaveChemCore p u W) := by
    have hmul := hpowM1.mul hVdWd hbddPowM1 hbddVdWd
    simpa [paperWaveChemCore, mul_assoc] using hmul
  have hchem : LocallyUniformConverges
      (fun n => paperWaveChemTerm p (us n) (Ws n))
      (paperWaveChemTerm p u W) := by
    simpa [paperWaveChemTerm] using hchemCore.const_mul (-(p.χ * p.m))
  have hpowM1V : LocallyUniformConverges
      (fun n x => (Ws n x) ^ (p.m - 1) * frozenElliptic p (us n) x)
      (fun x => (W x) ^ (p.m - 1) * frozenElliptic p u x) :=
    hpowM1.mul hV hbddPowM1 hbddV
  have hleft : LocallyUniformConverges
      (fun n x => 1 - p.χ *
        ((Ws n x) ^ (p.m - 1) * frozenElliptic p (us n) x))
      (fun x => 1 - p.χ * ((W x) ^ (p.m - 1) * frozenElliptic p u x)) :=
    hpowM1V.const_mul p.χ |>.const_sub 1
  have hright : LocallyUniformConverges
      (fun n x => (Ws n x) ^ p.α - p.χ * (Ws n x) ^ (p.m + p.γ - 1))
      (fun x => (W x) ^ p.α - p.χ * (W x) ^ (p.m + p.γ - 1)) :=
    hpowA.sub (hpowMG.const_mul p.χ)
  have hbracket : LocallyUniformConverges
      (fun n => paperWaveReactionBracket p (us n) (Ws n))
      (paperWaveReactionBracket p u W) := by
    simpa [paperWaveReactionBracket] using hleft.sub hright
  have hbddM1V : LocallyBoundedOnCompacts
      (fun x => (W x) ^ (p.m - 1) * frozenElliptic p u x) :=
    hbddPowM1.mul hbddV
  have hbddLeft : LocallyBoundedOnCompacts
      (fun x => 1 - p.χ * ((W x) ^ (p.m - 1) * frozenElliptic p u x)) :=
    (hbddM1V.const_mul p.χ).const_sub 1
  have hbddRight : LocallyBoundedOnCompacts
      (fun x => (W x) ^ p.α - p.χ * (W x) ^ (p.m + p.γ - 1)) :=
    hbddPowA.sub (hbddPowMG.const_mul p.χ)
  have hbddBracket : LocallyBoundedOnCompacts
      (paperWaveReactionBracket p u W) := by
    simpa [paperWaveReactionBracket] using hbddLeft.sub hbddRight
  have hreaction : LocallyUniformConverges
      (fun n => paperWaveReactionTerm p (us n) (Ws n))
      (paperWaveReactionTerm p u W) := by
    have hmul := hWs.mul hbracket hbddW hbddBracket
    simpa [paperWaveReactionTerm] using hmul
  have hnonlinear : LocallyUniformConverges
      (fun n x => paperWaveChemTerm p (us n) (Ws n) x +
        paperWaveReactionTerm p (us n) (Ws n) x)
      (fun x => paperWaveChemTerm p u W x + paperWaveReactionTerm p u W x) :=
    hchem.add hreaction
  have hlinear : LocallyUniformConverges
      (fun n x => lam * Zs n x) (fun x => lam * Z x) :=
    hZs.const_mul lam
  have hsum := hnonlinear.add hlinear
  have hseqEq :
      (fun n => paperStepSource p c lam (us n) (Zs n) (Ws n)) =
        fun n x => paperWaveChemTerm p (us n) (Ws n) x +
          paperWaveReactionTerm p (us n) (Ws n) x + lam * Zs n x := by
    funext n x
    unfold paperStepSource paperStepNonlinearity paperWaveChemTerm
      paperWaveChemCore paperWaveReactionTerm paperWaveReactionBracket
    ring
  have hlimitEq : paperStepSource p c lam u Z W =
      fun x => paperWaveChemTerm p u W x +
        paperWaveReactionTerm p u W x + lam * Z x := by
    funext x
    unfold paperStepSource paperStepNonlinearity paperWaveChemTerm
      paperWaveChemCore paperWaveReactionTerm paperWaveReactionBracket
    ring
  rw [hseqEq, hlimitEq]
  exact hsum

/-- Actual paper steps have compact Green sources automatically.  The proof
first extracts a locally-uniform derivative cluster from the uniform first- and
second-derivative bounds, identifies it as `deriv U` by the uniform-limits
derivative theorem, and then applies the non-diagonal source convergence above. -/
theorem paperGreenRotheAdaptiveSourceCompactness_of_stepAnalytic
    (p : CMParams) (c lam M κ Λ : ℝ)
    (hM : 0 < M) (hΛ : 0 ≤ Λ) (hlam : 0 < lam)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ)
    (hanalytic : ∀ u, InMonotoneWaveTrapSet κ M u → ∀ k,
      PaperStepAnalytic p c lam M κ Λ u (rotheSeq u k) (rotheSeq u (k + 1)))
    (hnew0 : ∀ u, InMonotoneWaveTrapSet κ M u → ∀ k x,
      0 ≤ rotheSeq u (k + 1) x)
    (hnewM : ∀ u, InMonotoneWaveTrapSet κ M u → ∀ k x,
      rotheSeq u (k + 1) x ≤ M) :
    PaperGreenRotheAdaptiveSourceCompactnessOnTrap p c lam M κ Λ rotheSeq := by
  intro seq U ks hseq hU houter _hks hold hnew
  let Zs : ℕ → ℝ → ℝ := fun n => rotheSeq (seq n) (ks n)
  let Ws : ℕ → ℝ → ℝ := fun n => rotheSeq (seq n) (ks n + 1)
  let A : ∀ n, PaperStepAnalytic p c lam M κ Λ (seq n) (Zs n) (Ws n) :=
    fun n => hanalytic (seq n) (hseq n) (ks n)
  let C2 : ℝ := paperStepC2Bound c lam M Λ
  let Q : ℝ := max Λ C2
  have hC2 : 0 ≤ C2 := paperStepC2Bound_nonneg hlam hM.le hΛ
  have hQ : 0 ≤ Q := by
    rcases le_total Λ C2 with h | h
    · simpa [Q, max_eq_right h] using hC2
    · simpa [Q, max_eq_left h] using hΛ
  have hderivLip : ∀ n x y,
      |deriv (Ws n) x - deriv (Ws n) y| ≤ Q * |x - y| := by
    intro n x y
    have hdiff : Differentiable ℝ (fun t => deriv (Ws n) t) :=
      fun t => (paperStep_hasDerivAt_deriv (A n) t).differentiableAt
    have hbound : ∀ t, |deriv (fun s => deriv (Ws n) s) t| ≤ C2 := by
      intro t
      rw [(paperStep_hasDerivAt_deriv (A n) t).deriv]
      exact paperStep_second_deriv_le hlam hM.le hΛ
        (fun z => by
          rw [abs_of_nonneg (hnew0 (seq n) (hseq n) (ks n) z)]
          exact hnewM (seq n) (hseq n) (ks n) z)
        (A n) t
    exact le_trans (abs_sub_le_of_deriv_abs_le_core hdiff hbound x y)
      (mul_le_mul_of_nonneg_right (le_max_right Λ C2) (abs_nonneg _))
  have hderivBdd : ∀ n x, |deriv (Ws n) x| ≤ Q := by
    intro n x
    exact le_trans (paperStep_deriv_le hlam (A n) x) (le_max_left Λ C2)
  obtain ⟨sub, hsub, D, hDpt, hDLip⟩ :=
    helly_pointwise_selection Q (fun n x => deriv (Ws n) x)
      hderivLip hderivBdd
  have hDLU : LocallyUniformConverges
      (fun n x => deriv (Ws (sub n)) x) D :=
    locallyUniform_of_helly_pointwise hQ hDpt hderivLip hDLip
  have hWsub : LocallyUniformConverges (fun n => Ws (sub n)) U := by
    simpa [Ws] using hnew.comp_strictMono hsub
  have hUhas : ∀ x, HasDerivAt U (D x) x := by
    intro x
    exact hasDerivAt_of_tendstoLocallyUniformlyOn
      (𝕜 := ℝ) (l := atTop) (s := (Set.univ : Set ℝ))
      (f := fun n => Ws (sub n)) (g := U)
      (f' := fun n x => deriv (Ws (sub n)) x) (g' := D)
      isOpen_univ hDLU.tendstoLocallyUniformlyOn_univ
      (Eventually.of_forall fun n y _hy =>
        paperStep_hasDerivAt_value (A (sub n)) y)
      (fun y _hy => hWsub.tendsto_at y) (Set.mem_univ x)
  have hD_eq : D = fun x => deriv U x := by
    funext x
    exact (hUhas x).deriv.symm
  have hWd : LocallyUniformConverges
      (fun n x => deriv (Ws (sub n)) x) (fun x => deriv U x) := by
    simpa [hD_eq] using hDLU
  have hderivU : ∀ x, |deriv U x| ≤ Λ := by
    intro x
    rw [← congrFun hD_eq x]
    refine le_of_tendsto (hDpt x).abs ?_
    exact Eventually.of_forall fun n => paperStep_deriv_le hlam (A (sub n)) x
  have hbddDerivU : LocallyBoundedOnCompacts (fun x => deriv U x) :=
    LocallyBoundedOnCompacts.of_global_bound hΛ hderivU
  have houter' : LocallyUniformConverges (fun n => seq (sub n)) U :=
    houter.comp_strictMono hsub
  have hold' : LocallyUniformConverges (fun n => Zs (sub n)) U := by
    simpa [Zs] using hold.comp_strictMono hsub
  have hnew' : LocallyUniformConverges (fun n => Ws (sub n)) U := hWsub
  have hsource : LocallyUniformConverges
      (fun n => paperStepSource p c lam (seq (sub n))
        (Zs (sub n)) (Ws (sub n)))
      (paperStepSource p c lam U U U) :=
    paperStepSource_locallyUniform_nonDiagonal p hM
      (fun n => hseq (sub n)) hU
      (fun n x => hnew0 (seq (sub n)) (hseq (sub n)) (ks (sub n)) x)
      (fun n x => hnewM (seq (sub n)) (hseq (sub n)) (ks (sub n)) x)
      hU.nonneg hU.le_M
      houter' hold' hnew' hWd hbddDerivU
  have hRlu : LocallyUniformConverges
      (fun n => (A (sub n)).R) (paperStepSource p c lam U U U) := by
    have heq : (fun n => (A (sub n)).R) =
        fun n => paperStepSource p c lam (seq (sub n))
          (Zs (sub n)) (Ws (sub n)) := by
      funext n
      exact (A (sub n)).source_eq
    simpa [heq] using hsource
  let B : ℝ := paperStepRBoundFromLambda c lam Λ
  have hB : 0 ≤ B := paperStepRBoundFromLambda_nonneg hlam hΛ
  have hRbound : ∀ x, |paperStepSource p c lam U U U x| ≤ B := by
    intro x
    refine le_of_tendsto (hRlu.tendsto_at x).abs ?_
    exact Eventually.of_forall fun n =>
      paperStep_R_abs_le_from_lambda hlam (A (sub n)) x
  have hRcont : Continuous (paperStepSource p c lam U U U) :=
    continuous_of_locallyUniform (fun n => (A (sub n)).R_cont) hRlu
  exact ⟨
    { sub := sub
      sub_strictMono := hsub
      analytic := fun n => A (sub n)
      R := paperStepSource p c lam U U U
      R_cont := hRcont
      B := B
      source_bound := fun n x => paperStep_R_abs_le_from_lambda hlam (A (sub n)) x
      limit_bound := hRbound
      source_locallyUniform := hRlu
      new_nonneg := fun n x =>
        hnew0 (seq (sub n)) (hseq (sub n)) (ks (sub n)) x
      new_le_M := fun n x =>
        hnewM (seq (sub n)) (hseq (sub n)) (ks (sub n)) x }⟩

/-- Off-diagonal adaptive closed graph: the frozen profiles may converge to
`u` while the old and new iterates converge to a different profile `W`.  This
is the form needed to identify cluster points of the Rothe limit map. -/
def PaperGreenRotheAdaptiveOffDiagonalStepClosedGraphOnTrap
    (p : CMParams) (c lam M κ : ℝ)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ) : Prop :=
  ∀ (seq : ℕ → ℝ → ℝ) (u W : ℝ → ℝ) (ks : ℕ → ℕ),
    (∀ n, InMonotoneWaveTrapSet κ M (seq n)) →
      InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M W →
      LocallyUniformConverges seq u →
      Tendsto ks atTop atTop →
      LocallyUniformConverges (fun n => rotheSeq (seq n) (ks n)) W →
      LocallyUniformConverges (fun n => rotheSeq (seq n) (ks n + 1)) W →
        (∀ x, paperImplicitStepOp p c (1 / lam) u W x = W x) ∧
          Differentiable ℝ W ∧ Differentiable ℝ (deriv W)

/-- The analytic-preserving whole-line Green orbit has the off-diagonal
adaptive closed graph.  The proof extracts a derivative cluster, passes the
actual non-diagonal source, and identifies the limit by Green-kernel dominated
convergence. -/
theorem paperGreenRotheAdaptiveOffDiagonalStepClosedGraph_of_stepAnalytic
    (p : CMParams) (c lam M κ Λ : ℝ)
    (hM : 0 < M) (hΛ : 0 ≤ Λ) (hlam : 0 < lam)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ)
    (hanalytic : ∀ u, InMonotoneWaveTrapSet κ M u → ∀ k,
      PaperStepAnalytic p c lam M κ Λ u (rotheSeq u k) (rotheSeq u (k + 1)))
    (hnew0 : ∀ u, InMonotoneWaveTrapSet κ M u → ∀ k x,
      0 ≤ rotheSeq u (k + 1) x)
    (hnewM : ∀ u, InMonotoneWaveTrapSet κ M u → ∀ k x,
      rotheSeq u (k + 1) x ≤ M) :
    PaperGreenRotheAdaptiveOffDiagonalStepClosedGraphOnTrap
      p c lam M κ rotheSeq := by
  intro seq u W ks hseq hu hW houter _hks hold hnew
  let Zs : ℕ → ℝ → ℝ := fun n => rotheSeq (seq n) (ks n)
  let Ws : ℕ → ℝ → ℝ := fun n => rotheSeq (seq n) (ks n + 1)
  let A : ∀ n, PaperStepAnalytic p c lam M κ Λ (seq n) (Zs n) (Ws n) :=
    fun n => hanalytic (seq n) (hseq n) (ks n)
  let C2 : ℝ := paperStepC2Bound c lam M Λ
  let Q : ℝ := max Λ C2
  have hC2 : 0 ≤ C2 := paperStepC2Bound_nonneg hlam hM.le hΛ
  have hQ : 0 ≤ Q := by
    rcases le_total Λ C2 with h | h
    · simpa [Q, max_eq_right h] using hC2
    · simpa [Q, max_eq_left h] using hΛ
  have hderivLip : ∀ n x y,
      |deriv (Ws n) x - deriv (Ws n) y| ≤ Q * |x - y| := by
    intro n x y
    have hdiff : Differentiable ℝ (fun t => deriv (Ws n) t) :=
      fun t => (paperStep_hasDerivAt_deriv (A n) t).differentiableAt
    have hbound : ∀ t, |deriv (fun s => deriv (Ws n) s) t| ≤ C2 := by
      intro t
      rw [(paperStep_hasDerivAt_deriv (A n) t).deriv]
      exact paperStep_second_deriv_le hlam hM.le hΛ
        (fun z => by
          rw [abs_of_nonneg (hnew0 (seq n) (hseq n) (ks n) z)]
          exact hnewM (seq n) (hseq n) (ks n) z)
        (A n) t
    exact le_trans (abs_sub_le_of_deriv_abs_le_core hdiff hbound x y)
      (mul_le_mul_of_nonneg_right (le_max_right Λ C2) (abs_nonneg _))
  have hderivBdd : ∀ n x, |deriv (Ws n) x| ≤ Q := by
    intro n x
    exact le_trans (paperStep_deriv_le hlam (A n) x) (le_max_left Λ C2)
  obtain ⟨sub, hsub, D, hDpt, hDLip⟩ :=
    helly_pointwise_selection Q (fun n x => deriv (Ws n) x)
      hderivLip hderivBdd
  have hDLU : LocallyUniformConverges
      (fun n x => deriv (Ws (sub n)) x) D :=
    locallyUniform_of_helly_pointwise hQ hDpt hderivLip hDLip
  have hWsub : LocallyUniformConverges (fun n => Ws (sub n)) W := by
    simpa [Ws] using hnew.comp_strictMono hsub
  have hWhas : ∀ x, HasDerivAt W (D x) x := by
    intro x
    exact hasDerivAt_of_tendstoLocallyUniformlyOn
      (𝕜 := ℝ) (l := atTop) (s := (Set.univ : Set ℝ))
      (f := fun n => Ws (sub n)) (g := W)
      (f' := fun n x => deriv (Ws (sub n)) x) (g' := D)
      isOpen_univ hDLU.tendstoLocallyUniformlyOn_univ
      (Eventually.of_forall fun n y _hy =>
        paperStep_hasDerivAt_value (A (sub n)) y)
      (fun y _hy => hWsub.tendsto_at y) (Set.mem_univ x)
  have hD_eq : D = fun x => deriv W x := by
    funext x
    exact (hWhas x).deriv.symm
  have hWd : LocallyUniformConverges
      (fun n x => deriv (Ws (sub n)) x) (fun x => deriv W x) := by
    simpa [hD_eq] using hDLU
  have hderivW : ∀ x, |deriv W x| ≤ Λ := by
    intro x
    rw [← congrFun hD_eq x]
    refine le_of_tendsto (hDpt x).abs ?_
    exact Eventually.of_forall fun n => paperStep_deriv_le hlam (A (sub n)) x
  have hbddDerivW : LocallyBoundedOnCompacts (fun x => deriv W x) :=
    LocallyBoundedOnCompacts.of_global_bound hΛ hderivW
  have houter' : LocallyUniformConverges (fun n => seq (sub n)) u :=
    houter.comp_strictMono hsub
  have hold' : LocallyUniformConverges (fun n => Zs (sub n)) W := by
    simpa [Zs] using hold.comp_strictMono hsub
  have hsource : LocallyUniformConverges
      (fun n => paperStepSource p c lam (seq (sub n))
        (Zs (sub n)) (Ws (sub n)))
      (paperStepSource p c lam u W W) :=
    paperStepSource_locallyUniform_nonDiagonal p hM
      (fun n => hseq (sub n)) hu
      (fun n x => hnew0 (seq (sub n)) (hseq (sub n)) (ks (sub n)) x)
      (fun n x => hnewM (seq (sub n)) (hseq (sub n)) (ks (sub n)) x)
      hW.nonneg hW.le_M houter' hold' hWsub hWd hbddDerivW
  have hRlu : LocallyUniformConverges
      (fun n => (A (sub n)).R) (paperStepSource p c lam u W W) := by
    have heq : (fun n => (A (sub n)).R) =
        fun n => paperStepSource p c lam (seq (sub n))
          (Zs (sub n)) (Ws (sub n)) := by
      funext n
      exact (A (sub n)).source_eq
    simpa [heq] using hsource
  let B : ℝ := paperStepRBoundFromLambda c lam Λ
  have hRbound : ∀ x, |paperStepSource p c lam u W W x| ≤ B := by
    intro x
    refine le_of_tendsto (hRlu.tendsto_at x).abs ?_
    exact Eventually.of_forall fun n =>
      paperStep_R_abs_le_from_lambda hlam (A (sub n)) x
  have hRcont : Continuous (paperStepSource p c lam u W W) :=
    continuous_of_locallyUniform (fun n => (A (sub n)).R_cont) hRlu
  have hWgreen : W = fun x =>
      greenConv c lam (paperStepSource p c lam u W W) x := by
    funext x
    have hseqGreen : Tendsto
        (fun n => greenConv c lam (A (sub n)).R x) atTop (𝓝 (W x)) := by
      have heq : (fun n => Ws (sub n) x) =
          fun n => greenConv c lam (A (sub n)).R x := by
        funext n
        exact congrFun (A (sub n)).green_repr x
      simpa [heq] using hWsub.tendsto_at x
    have hlimitGreen :=
      greenConv_tendsto_of_source_locallyUniform_of_uniform_bound
        (c := c) (lam := lam) hlam (fun n => (A (sub n)).R_cont)
        hRcont
        (fun n x => paperStep_R_abs_le_from_lambda hlam (A (sub n)) x)
        hRbound hRlu x
    exact tendsto_nhds_unique hseqGreen hlimitGreen
  have hRhi : ∀ x, MeasureTheory.IntegrableOn
      (gWeight (greenRootPlus c lam) (paperStepSource p c lam u W W))
        (Set.Ioi x) :=
    fun x => gWeight_integrableOn_Ioi_of_bounded
      (greenRootPlus_pos (c := c) hlam) hRcont hRbound x
  have hRlo : ∀ x, MeasureTheory.IntegrableOn
      (gWeight (greenRootMinus c lam) (paperStepSource p c lam u W W))
        (Set.Iic x) :=
    fun x => gWeight_integrableOn_Iic_of_bounded
      (greenRootMinus_neg (c := c) hlam) hRcont hRbound x
  obtain ⟨hWdiff, hWderivDiff⟩ :=
    stationaryC2Regularity_of_greenRepresentation
      hRcont hRhi hRlo hWgreen
  exact ⟨paperImplicitStepOp_of_greenConv_source hlam rfl hWgreen
    hRcont hRhi hRlo, hWdiff, hWderivDiff⟩

section AxiomAudit

#print axioms paperStepSource_locallyUniform_nonDiagonal
#print axioms paperGreenRotheAdaptiveSourceCompactness_of_stepAnalytic
#print axioms paperGreenRotheAdaptiveOffDiagonalStepClosedGraph_of_stepAnalytic

end AxiomAudit

end ShenWork.Paper1
