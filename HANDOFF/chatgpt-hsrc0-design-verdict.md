I’ll treat this as an interface-design decision, not a code-writing task. I’ll verify the current repo definitions and the Mathlib names for interval/restricted-measure integrability before giving a concrete verdict.

The relevant existing weak package still assumes global Continuous and a nonnegative-time envelope; its consumers derive envelope nonnegativity from the bound at s = 0. That is exactly the part that becomes unsound for the canonical unpatched family, so the endpoint issue is real, not cosmetic.

Verdict

Use hybrid B + per-target closed horizons:

lean
∀ τ, 0 < τ → τ < T → DuhamelSourceL1ContOn aPatch τ

where

lean
aPatch s k :=
  if s ≤ 0 then a0 k else a s k

and the package remains on Set.Icc 0 τ.

I would not make the main source interface Ioo 0 T unless you are willing to rewrite many engine lemmas around measurability/integrability instead of continuity. The patched family solves the bad s = 0 value in the mathematically canonical way, while per-target τ < T solves the bad top endpoint without pretending you have decay at T.

The reason is simple: your consumers already fit the interval-integral convention ∫ s in 0..t, which Mathlib implements through Ioc 0 t; the value at 0 is measure-invisible, but current weak machinery uses continuity and envelope data at 0 to get nonnegativity and primitive/integrability facts. In the existing weak file, DuhamelSourceL1Cont stores a global envelope bound for all 0 ≤ s and global continuity of each coefficient, and duhamelSpectral_eq_cosineSeries_weak derives 0 ≤ envelope n from the bound at s = 0.

IntervalPicardLimitRestartWeak



IntervalPicardLimitRestartWeak

 So a pure Ioo package would force you to add henv_nonneg and then touch every place that currently gets integrability from Continuous.intervalIntegrable or global continuity.

The top endpoint is different. Since representation data exists only for σ < T, a single source package over Icc 0 T is not producer-fillable. A k-uniform bound at T does not give a summable envelope. Unless you formalize closed-time smoothing/regularity at T, the interface must avoid asking for decaying coefficient bounds at s = T.

Recommended structure

I would define two layers:

lean
structure DuhamelSourceL1ContOn
    (a : ℝ → ℕ → ℝ) (τ : ℝ) where
  envelope : ℕ → ℝ
  henv_nonneg : ∀ n, 0 ≤ envelope n
  henv_summable : Summable envelope
  henv_bound : ∀ s, 0 ≤ s → s ≤ τ → ∀ n, |a s n| ≤ envelope n
  hcont : ∀ n, ContinuousOn (fun s : ℝ => a s n) (Set.Icc 0 τ)

and the producer theorem should be:

lean
theorem source_l1contOn_patched
    (τ : ℝ) (hτ0 : 0 < τ) (hτT : τ < D.T) :
    DuhamelSourceL1ContOn aPatch τ

Then every consumer with target t < T asks for a τ satisfying t ≤ τ < T; usually choose τ = (t + T) / 2. This keeps consumers on closed intervals [0,τ], so the existing Mathlib path remains friendly:

lean
have hsrcτ := source_l1contOn_patched ((t + T) / 2) ...
have htτ : t ≤ (t + T) / 2 := by linarith

Then when the conclusion is about the canonical family a, use intervalIntegral.integral_congr_Ioo_of_le or intervalIntegral.integral_congr_ae_restrict, because aPatch = a on (0, τ], hence on (0,t].

Why not pure A / Ioo 0 T?

Pure A is honest mathematically, but it is worse in Lean plumbing.

If you use

lean
henv_bound : ∀ s, 0 < s → s < T → ...
hcont : ∀ n, ContinuousOn (fun s => a s n) (Set.Ioo 0 T)

then every lemma that currently writes

lean
(hkernel.mul (src.hcont n)).intervalIntegrable 0 t

must be replaced by a bounded-measurable-on-Ioc proof. Mathlib has the tools, but it is noisier. The existing duhamelValue_adot_eq_tsum obtains per-mode integrability from global continuity and intervalIntegrable_iff_integrableOn_Ioc_of_le; see the current proof pattern at the hint construction.

IntervalDuhamelClosedC2

For A, the replacement skeleton is:

lean
have hcontIoc :
    ContinuousOn F (Set.Ioc (0 : ℝ) t) :=
  (src.hcont n).mono (by
    intro s hs
    exact ⟨hs.1, lt_of_le_of_lt hs.2 htT⟩)

have hsm :
    AEStronglyMeasurable F
      (volume.restrict (Set.Ioc (0 : ℝ) t)) :=
  hcontIoc.aestronglyMeasurable measurableSet_Ioc

have hfin : volume (Set.Ioc (0 : ℝ) t) < ∞ := by
  -- usually `simp [Real.volume_Ioc]` or `exact measure_Ioc_lt_top`
  simp

have hbound_ae :
    ∀ᵐ s ∂ volume.restrict (Set.Ioc (0 : ℝ) t), ‖F s‖ ≤ C := by
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
    (by
      intro s hs
      -- use `src.henv_bound s hs.1 (lt_of_le_of_lt hs.2 htT)`
      -- plus kernel bound
      ...)

have hIntOn :
    IntegrableOn F (Set.Ioc (0 : ℝ) t) volume :=
  MeasureTheory.IntegrableOn.of_bound hfin hsm C hbound_ae

have hII :
    IntervalIntegrable F volume 0 t :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).2 hIntOn

The relevant Mathlib names are ContinuousOn.aestronglyMeasurable, MeasureTheory.IntegrableOn.of_bound, MeasureTheory.ae_restrict_of_forall_mem, and intervalIntegrable_iff_integrableOn_Ioc_of_le. Mathlib’s docs list ContinuousOn.aestronglyMeasurable as producing AEStronglyMeasurable f (μ.restrict s) from continuity on a measurable set; IntegrableOn.of_bound turns finite-measure bounded a.e. strongly measurable functions into IntegrableOn; and intervalIntegrable_iff_integrableOn_Ioc_of_le is the interval-integrability bridge for a ≤ b.
Lean Community

Lean Community

Lean Community

This works, but it spreads measure-theoretic noise across many consumers.

For B: right-continuity at 0

There is no hidden spatial-continuity problem from the zero-extension. The coefficient functional only integrates over [0,1], and you already have congruence lemmas for functions that agree on Icc 0 1. The lift may be discontinuous as a function on all ℝ, but the coefficient functional sees only the interval.

The proof architecture should be:

lean
‖u s - u₀‖∞ → 0
⇒ ‖logistic (u s) - logistic u₀‖∞ → 0
⇒ |cosineCoeffs(logistic(u s)) k - cosineCoeffs(logistic(u₀)) k|
   ≤ C * ‖logistic(u s) - logistic(u₀)‖∞
⇒ coefficient continuity at 0

For the coefficient bound, use the elementary estimate

lean
|∫ x in 0..1, h x * cos(kπx)| ≤ ∫ x in 0..1, |h x| ≤ ‖h‖∞

up to the normalization factor 1 or 2. This even gives a uniform-in-k continuity estimate because |cos| ≤ 1.

The patched family is also the right mathematical object: it is the continuous extension of the right-time coefficient family to s = 0.

T-endpoint

I agree with your diagnosis: without formalized regularity at T, the structure must be open at the top or per-target below T.

A non-decaying bound at T cannot be combined with a summable envelope. If the envelope must dominate |a T k| for every k, and all you know is |a T k| ≤ C, then the natural envelope is constant in k, which is not summable. You could mathematically try to prove decay at T from parabolic smoothing, but that is a new regularity theorem for u(T) and then for logistic(u(T)). That is not an interface patch; it is a substantial analytic formalization.

So do not require source data on Icc 0 T for the true T. Use local closed horizons:

lean
τ < T

rather than Ioo 0 T as the primary interface.

Congruence tools for patching back to the canonical family

For interval integrals where the difference is only at s = 0, use:

lean
intervalIntegral.integral_congr_Ioo_of_le

It assumes equality on Set.Ioo a b and a no-atoms measure. Mathlib documents both intervalIntegral.integral_congr_Ioo_of_le and the more general a.e.-restricted version intervalIntegral.integral_congr_ae_restrict.
Lean Community

For ordinary restricted-measure integrals, use:

lean
MeasureTheory.integral_congr_ae
Set.EqOn.aeEq_restrict
MeasureTheory.ae_restrict_of_forall_mem

Set.EqOn.aeEq_restrict is exactly the conversion from equality on a measurable support set to a.e. equality under μ.restrict s, and ae_restrict_of_forall_mem is the predicate version.
Lean Community

Typical patch-back proof:

lean
have hEq : Set.EqOn
    (fun s => kernel t s * aPatch s k)
    (fun s => kernel t s * a s k)
    (Set.Ioo (0 : ℝ) t) := by
  intro s hs
  have hspos : 0 < s := hs.1
  simp [aPatch, not_le.mpr hspos]

exact intervalIntegral.integral_congr_Ioo_of_le ht.le hEq

For a restricted measure:

lean
apply MeasureTheory.integral_congr_ae
exact hEqOn.aeEq_restrict measurableSet_Icc
Fourth option

A useful fourth option is to separate “producer data” from “consumer data”:

Producer proves:

lean
∀ τ, 0 < τ → τ < T → DuhamelSourceL1ContOn aPatch τ

A small adapter lemma derives the consumer-facing canonical statement:

lean
theorem use_canonical_on_target
    {t τ} (ht0 : 0 < t) (htτ : t ≤ τ) (hτT : τ < T)
    (src : DuhamelSourceL1ContOn aPatch τ)
    (hagree : ∀ s, 0 < s → s ≤ τ → ∀ k, aPatch s k = a s k) :
    ... canonical a at target t ...

This localizes all aPatch = a congruence plumbing in one or two adapter lemmas, instead of threading hagree through six engines. The engines should continue to operate on whatever family they are given; the adapter is the only place that knows the family is patched.

So the final design I would implement is:

lean
-- engine-facing
DuhamelSourceL1ContOn a τ
-- closed interval, good continuity, summable envelope, explicit nonnegativity

-- producer-facing
∀ τ < T, DuhamelSourceL1ContOn aPatch τ

-- adapter-facing
engine_result aPatch τ
→ engine_result a t

This is the weakest producer-fillable hypothesis that still preserves the low-friction Mathlib path for the consumers.
