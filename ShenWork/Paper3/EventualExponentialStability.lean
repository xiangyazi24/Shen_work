/-
  Paper3 eventual local exponential stability.

  This additive statement layer keeps the original all-time Theorem 2.2 API
  unchanged.  Its nonlinear conclusion starts at an existential positive
  time, which is the faithful formulation available from rough initial data
  after parabolic smoothing.
-/
import ShenWork.Paper3.Statements

namespace ShenWork.Paper3

open ShenWork.Paper2

noncomputable section

/-- Exponential `C¹` convergence after an explicitly supplied starting time. -/
def EventualExponentialC1ConvergenceWith
    (D : BoundedDomainData) (N : StabilityNorms D)
    (u v : ℝ → D.Point → ℝ) (uStar vStar C rate t₀ : ℝ) : Prop :=
  ∀ t, t₀ ≤ t →
    N.c1Distance (u t) (fun _ => uStar) +
      N.c1Distance (v t) (fun _ => vStar) ≤ C * Real.exp (-rate * t)

lemma EventualExponentialC1ConvergenceWith.bound_at
    {D : BoundedDomainData} {N : StabilityNorms D}
    {u v : ℝ → D.Point → ℝ} {uStar vStar C rate t₀ : ℝ}
    (h :
      EventualExponentialC1ConvergenceWith
        D N u v uStar vStar C rate t₀)
    {t : ℝ} (ht : t₀ ≤ t) :
    N.c1Distance (u t) (fun _ => uStar) +
      N.c1Distance (v t) (fun _ => vStar) ≤ C * Real.exp (-rate * t) :=
  h t ht

/-- The two constants are a positive spatially homogeneous steady state of
the parabolic-elliptic Paper3 system. -/
structure Paper3ConstantEquilibrium
    (p : CM2Params) (uStar vStar : ℝ) : Prop where
  u_pos : 0 < uStar
  v_nonneg : 0 ≤ vStar
  reaction_eq_zero :
    uStar * (p.a - p.b * uStar ^ p.α) = 0
  elliptic_relation :
    p.μ * vStar = p.ν * uStar ^ p.γ

/-- The positive logistic equilibrium is a constant PDE equilibrium. -/
theorem paper3ConstantEquilibrium_positive
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) :
    Paper3ConstantEquilibrium p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  exact
    { u_pos := positiveEquilibrium_fst_pos p ⟨ha, hb⟩
      v_nonneg := (positiveEquilibrium_snd_pos p ⟨ha, hb⟩).le
      reaction_eq_zero := positiveEquilibrium_reaction_zero p ⟨ha, hb⟩
      elliptic_relation := positiveEquilibrium_elliptic_relation p ⟨ha, hb⟩ }

/-- The mass-parametrized equilibrium is a constant PDE equilibrium when the
reaction coefficients vanish. -/
theorem paper3ConstantEquilibrium_minimal
    (p : CM2Params) (ha : p.a = 0) (hb : p.b = 0)
    (uStar : ℝ) (huStar : 0 < uStar) :
    Paper3ConstantEquilibrium p
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 := by
  exact
    { u_pos := by simpa [minimalEquilibrium] using huStar
      v_nonneg := (minimalEquilibrium_snd_pos p huStar).le
      reaction_eq_zero :=
        minimalEquilibrium_reaction_zero_of_a_b_zero p uStar ha hb
      elliptic_relation := minimalEquilibrium_elliptic_relation p uStar }

/-- Initial mass compatibility needed only when the logistic reaction
vanishes and the constant mode is conserved. -/
def EquilibriumInitialMassCompatible
    (D : BoundedDomainData) (p : CM2Params)
    (uStar : ℝ) (u₀ : D.Point → ℝ) : Prop :=
  p.a = 0 → p.b = 0 → D.integral u₀ = D.volume * uStar

/-- Raw sectorial local stability with decay required only after an
existential positive smoothing time. -/
def EventualSectorialLocalExponentialRaw
    (D : BoundedDomainData) (p : CM2Params) (S : SpectralData)
    (c1Distance : (D.Point → ℝ) → (D.Point → ℝ) → ℝ)
    (xpSigmaDistance : ℝ → ℝ → (D.Point → ℝ) → (D.Point → ℝ) → ℝ) : Prop :=
  ∀ sigma pNorm uStar vStar,
    1 / 2 < sigma → sigma < 1 → 1 < pNorm →
    Paper3ConstantEquilibrium p uStar vStar →
    LinearlyStable S p uStar vStar →
      ∃ eps > 0, ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
        ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
          xpSigmaDistance sigma pNorm u₀ (fun _ => uStar) ≤ eps →
          EquilibriumInitialMassCompatible D p uStar u₀ →
            ∀ u v : ℝ → D.Point → ℝ,
              IsPaper2GlobalClassicalSolution D p u v →
              InitialTrace D u₀ u →
                ∀ t, t₀ ≤ t →
                  c1Distance (u t) (fun _ => uStar) +
                    c1Distance (v t) (fun _ => vStar) ≤
                      C * Real.exp (-rate * t)

lemma EventualSectorialLocalExponentialRaw.local_exponential_stability
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {c1Distance : (D.Point → ℝ) → (D.Point → ℝ) → ℝ}
    {xpSigmaDistance : ℝ → ℝ → (D.Point → ℝ) → (D.Point → ℝ) → ℝ}
    (h :
      EventualSectorialLocalExponentialRaw
        D p S c1Distance xpSigmaDistance)
    {sigma pNorm uStar vStar : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hstable : LinearlyStable S p uStar vStar) :
    ∃ eps > 0, ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        xpSigmaDistance sigma pNorm u₀ (fun _ => uStar) ≤ eps →
        EquilibriumInitialMassCompatible D p uStar u₀ →
          ∀ u v : ℝ → D.Point → ℝ,
            IsPaper2GlobalClassicalSolution D p u v →
            InitialTrace D u₀ u →
              ∀ t, t₀ ≤ t →
                c1Distance (u t) (fun _ => uStar) +
                  c1Distance (v t) (fun _ => vStar) ≤
                    C * Real.exp (-rate * t) :=
  h sigma pNorm uStar vStar hsigma_low hsigma_high hpNorm heq hstable

/-- Sup-norm local stability with exponential `C¹` decay after a positive
smoothing time. -/
def EventualLocallyExponentiallyStableFromSup
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (uStar vStar : ℝ) : Prop :=
  ∃ δ > 0, ∃ A > 0, ∃ rate > 0, ∃ t₀ > 0,
    ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
      SupCloseToConstant D u₀ uStar δ →
        ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2GlobalClassicalSolution D p u v ∧
          InitialTrace D u₀ u ∧
          EventualExponentialC1ConvergenceWith
            D N u v uStar vStar A rate t₀

/-- Mass-constrained counterpart of eventual sup-norm local stability. -/
def EventualMassConstrainedLocallyExponentiallyStableFromSup
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (uStar vStar : ℝ) : Prop :=
  ∃ δ > 0, ∃ A > 0, ∃ rate > 0, ∃ t₀ > 0,
    ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
      SupCloseToConstant D u₀ uStar δ →
      D.integral u₀ = D.volume * uStar →
        ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2GlobalClassicalSolution D p u v ∧
          InitialTrace D u₀ u ∧
          EventualExponentialC1ConvergenceWith
            D N u v uStar vStar A rate t₀

/-- Convert the eventual raw `X^σ_p` estimate into the nonminimal sup-norm
local stability package. -/
theorem EventualSectorialLocalExponentialRaw.locally_from_sup_control
    {D : BoundedDomainData} {S : SpectralData} {p : CM2Params}
    {N : StabilityNorms D} {sigma pNorm uStar vStar : ℝ}
    (hraw :
      EventualSectorialLocalExponentialRaw
        D p S N.c1Distance N.xpSigmaDistance)
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (ha : 0 < p.a)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hstable : LinearlyStable S p uStar vStar)
    (hcontrol : SupControlsXpSigmaDistance D N sigma pNorm uStar)
    (hexist : ∀ delta > 0, SmallDataGlobalExistence D p uStar delta) :
    EventualLocallyExponentiallyStableFromSup D p N uStar vStar := by
  rcases hraw.local_exponential_stability
      hsigma_low hsigma_high hpNorm heq hstable with
    ⟨eps, heps, A, hA, rate, hrate, t₀, ht₀, hdecay⟩
  rcases hcontrol eps heps with ⟨delta, hdelta, hdist⟩
  refine ⟨delta, hdelta, A, hA, rate, hrate, t₀, ht₀, ?_⟩
  intro u₀ hu₀ hclose
  rcases hexist delta hdelta u₀ hu₀ hclose with
    ⟨u, v, hglobal, htrace⟩
  refine ⟨u, v, hglobal, htrace, ?_⟩
  exact hdecay u₀ hu₀ (hdist u₀ hclose)
    (fun ha0 _hb0 => False.elim ((ne_of_gt ha) ha0))
    u v hglobal htrace

/-- Convert the eventual raw estimate into the mass-constrained sup-norm
local stability package. -/
theorem EventualSectorialLocalExponentialRaw.massConstrained_from_sup_control
    {D : BoundedDomainData} {S : SpectralData} {p : CM2Params}
    {N : StabilityNorms D} {sigma pNorm uStar vStar : ℝ}
    (hraw :
      EventualSectorialLocalExponentialRaw
        D p S N.c1Distance N.xpSigmaDistance)
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hstable : LinearlyStable S p uStar vStar)
    (hcontrol : SupControlsXpSigmaDistance D N sigma pNorm uStar)
    (hexist :
      ∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence D p uStar delta) :
    EventualMassConstrainedLocallyExponentiallyStableFromSup
      D p N uStar vStar := by
  rcases hraw.local_exponential_stability
      hsigma_low hsigma_high hpNorm heq hstable with
    ⟨eps, heps, A, hA, rate, hrate, t₀, ht₀, hdecay⟩
  rcases hcontrol eps heps with ⟨delta, hdelta, hdist⟩
  refine ⟨delta, hdelta, A, hA, rate, hrate, t₀, ht₀, ?_⟩
  intro u₀ hu₀ hclose hmass
  rcases hexist delta hdelta u₀ hu₀ hclose hmass with
    ⟨u, v, hglobal, htrace⟩
  refine ⟨u, v, hglobal, htrace, ?_⟩
  exact hdecay u₀ hu₀ (hdist u₀ hclose) (fun _ha _hb => hmass)
    u v hglobal htrace

/-- Additive eventual-exponential variant of Paper3 Theorem 2.2.

The original `Theorem_2_2` remains unchanged.  The only change here is that
the nonlinear `C¹` convergence conjunct begins at an existential positive
time `t₀`.  The linear stable/unstable conclusions are identical. -/
def Theorem_2_2_EventualExponentialStability
    (D : BoundedDomainData) (p : CM2Params) (S : SpectralData)
    (N : StabilityNorms D) (C : Paper3Constants D p) : Prop :=
  (∀ (ha : 0 < p.a) (hb : 0 < p.b),
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    p.χ₀ < C.chiCritical eq.1 →
      LinearlyStable S p eq.1 eq.2 ∧
      ∃ δ > 0, ∃ A > 0, ∃ rate > 0, ∃ t₀ > 0,
        ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
          SupCloseToConstant D u₀ eq.1 δ →
            ∃ u v : ℝ → D.Point → ℝ,
              IsPaper2GlobalClassicalSolution D p u v ∧
              InitialTrace D u₀ u ∧
              EventualExponentialC1ConvergenceWith
                D N u v eq.1 eq.2 A rate t₀) ∧
  (∀ (ha : 0 < p.a) (hb : 0 < p.b),
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    C.chiCritical eq.1 < p.χ₀ →
      LinearlyUnstable S p eq.1 eq.2) ∧
  (p.a = 0 → p.b = 0 →
    ∀ uStar > 0,
      let eq := minimalEquilibrium p uStar
      p.χ₀ < C.chiCritical uStar →
        LinearlyStable S p eq.1 eq.2 ∧
        ∃ δ > 0, ∃ A > 0, ∃ rate > 0, ∃ t₀ > 0,
          ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
            SupCloseToConstant D u₀ eq.1 δ →
            D.integral u₀ = D.volume * uStar →
              ∃ u v : ℝ → D.Point → ℝ,
                IsPaper2GlobalClassicalSolution D p u v ∧
                InitialTrace D u₀ u ∧
                EventualExponentialC1ConvergenceWith
                  D N u v eq.1 eq.2 A rate t₀) ∧
  (p.a = 0 → p.b = 0 →
    ∀ uStar > 0,
      let eq := minimalEquilibrium p uStar
      C.chiCritical uStar < p.χ₀ →
        LinearlyUnstable S p eq.1 eq.2)

/-- Constructor for the four branches of the eventual Theorem 2.2 variant. -/
theorem Theorem_2_2_EventualExponentialStability.of_parts
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (hpos_stable : ∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      p.χ₀ < C.chiCritical eq.1 →
        LinearlyStable S p eq.1 eq.2 ∧
        ∃ δ > 0, ∃ A > 0, ∃ rate > 0, ∃ t₀ > 0,
          ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
            SupCloseToConstant D u₀ eq.1 δ →
              ∃ u v : ℝ → D.Point → ℝ,
                IsPaper2GlobalClassicalSolution D p u v ∧
                InitialTrace D u₀ u ∧
                EventualExponentialC1ConvergenceWith
                  D N u v eq.1 eq.2 A rate t₀)
    (hpos_unstable : ∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      C.chiCritical eq.1 < p.χ₀ →
        LinearlyUnstable S p eq.1 eq.2)
    (hmin_stable : p.a = 0 → p.b = 0 →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        p.χ₀ < C.chiCritical uStar →
          LinearlyStable S p eq.1 eq.2 ∧
          ∃ δ > 0, ∃ A > 0, ∃ rate > 0, ∃ t₀ > 0,
            ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
              SupCloseToConstant D u₀ eq.1 δ →
              D.integral u₀ = D.volume * uStar →
                ∃ u v : ℝ → D.Point → ℝ,
                  IsPaper2GlobalClassicalSolution D p u v ∧
                  InitialTrace D u₀ u ∧
                  EventualExponentialC1ConvergenceWith
                    D N u v eq.1 eq.2 A rate t₀)
    (hmin_unstable : p.a = 0 → p.b = 0 →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        C.chiCritical uStar < p.χ₀ →
          LinearlyUnstable S p eq.1 eq.2) :
    Theorem_2_2_EventualExponentialStability D p S N C :=
  ⟨hpos_stable, hpos_unstable, hmin_stable, hmin_unstable⟩

/-- Full eventual Theorem 2.2 from the audited critical spectrum, eventual raw
decay, norm control, and small-data global existence. -/
theorem Theorem_2_2_EventualExponentialStability_full_critical_spectrum_of_raw
    {D : BoundedDomainData} {p : CM2Params} {S : SpectralData}
    {N : StabilityNorms D} {C : Paper3Constants D p}
    (H : HasNeumannSpectrum S)
    (hC : Paper3ConstantsUsesCriticalSpectrum S p C)
    (hraw :
      EventualSectorialLocalExponentialRaw
        D p S N.c1Distance N.xpSigmaDistance)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (hcontrol : ∀ uStar, SupControlsXpSigmaDistance D N sigma pNorm uStar)
    (hexist : ∀ uStar, ∀ delta > 0, SmallDataGlobalExistence D p uStar delta)
    (hmexist :
      ∀ uStar, ∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence D p uStar delta) :
    Theorem_2_2_EventualExponentialStability D p S N C := by
  have hthreshold := Theorem_2_2_linear_threshold_branch_direct S p H
  refine Theorem_2_2_EventualExponentialStability.of_parts ?_ ?_ ?_ ?_
  · intro ha hb
    dsimp
    intro hχcrit
    have hstable :
        LinearlyStable S p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2 :=
      (hthreshold.1 ha hb).1
        (by
          simpa [hC.chiCritical_positiveEquilibrium ha hb] using hχcrit)
    have hlocal :
        EventualLocallyExponentiallyStableFromSup D p N
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2 :=
      hraw.locally_from_sup_control
        hsigma_low hsigma_high hpNorm ha
        (paper3ConstantEquilibrium_positive p ha hb) hstable
        (hcontrol (positiveEquilibrium p ⟨ha, hb⟩).1)
        (hexist (positiveEquilibrium p ⟨ha, hb⟩).1)
    rcases hlocal with
      ⟨δ, hδ, A, hA, rate, hrate, t₀, ht₀, hmain⟩
    exact ⟨hstable, δ, hδ, A, hA, rate, hrate, t₀, ht₀, hmain⟩
  · intro ha hb
    dsimp
    intro hχcrit
    exact
      (hthreshold.1 ha hb).2
        (by
          simpa [hC.chiCritical_positiveEquilibrium ha hb] using hχcrit)
  · intro ha hb uStar huStar
    dsimp
    intro hχcrit
    have hstable :
        LinearlyStable S p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2 :=
      (hthreshold.2 ha hb uStar huStar).1
        (by
          simpa [hC.chiCritical_minimalEquilibrium huStar,
            minimalEquilibrium] using hχcrit)
    have hlocal :
        EventualMassConstrainedLocallyExponentiallyStableFromSup D p N
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2 :=
      hraw.massConstrained_from_sup_control
        hsigma_low hsigma_high hpNorm
        (paper3ConstantEquilibrium_minimal p ha hb uStar huStar) hstable
        (hcontrol (minimalEquilibrium p uStar).1)
        (hmexist (minimalEquilibrium p uStar).1)
    rcases hlocal with
      ⟨δ, hδ, A, hA, rate, hrate, t₀, ht₀, hmain⟩
    exact ⟨hstable, δ, hδ, A, hA, rate, hrate, t₀, ht₀, hmain⟩
  · intro ha hb uStar huStar
    dsimp
    intro hχcrit
    exact
      (hthreshold.2 ha hb uStar huStar).2
      (by
          simpa [hC.chiCritical_minimalEquilibrium huStar,
            minimalEquilibrium] using hχcrit)

#print axioms
  Theorem_2_2_EventualExponentialStability_full_critical_spectrum_of_raw

end

end ShenWork.Paper3
