# DESIGN_CHATGPT_AUDIT.md — ChatGPT Pro R2 Audit of Consensus Design

**Auditor**: ChatGPT Pro (GPT-5.5, reasoning mode)
**Date**: 2026-06-04
**Input**: G0-G7 consensus from Opus-Codex 4-round adversarial review

---

## Verdict: Plan is sound, but incomplete

The gap list is close but not complete. Four additions needed:

### NEW: G2.5 — Picard-iterate regularity pass-to-limit

Regularity of every Picard iterate does NOT automatically imply regularity
of the fixed point. Need convergence in a topology strong enough to pass
dt, dx, dxx, boundary conditions, and standard Duhamel identity to the limit.

Options:
- Prove derivative-field convergence on compact sub-cylinders [eps,T] x [0,1]
- Or prove fixed point regularity directly by closed-graph/semigroup smoothing

Estimated: 150-400 lines.

### VERIFY: G8 — Maximum principle / comparison theorem

Paper Theorem 1.1 uses expanded PDE + maximum-principle reasoning for chi0 <= 0.
If not already formalized, this is a major gap (500-1200 lines).
If already done (weak_maximum_principle_linear exists in repo), verify it covers
the needed case.

### EXPLICIT in G4: Elliptic resolvent regularity for v

v = (muI - Delta)^{-1}(nu u^gamma). G4 must include v_xx, elliptic equation,
Neumann BC, composition regularity of u^gamma, and time regularity of v.

### G0 REFINEMENT: No classical regularity at t=0

Paper defines classical solution on (0,T) x Omega_bar, not at t=0.
Do not require C^{1,2} at t=0 unless adding compatibility assumptions.
InitialTrace should be sup-norm trace, not classical trace.

---

## G2/G3 circularity resolution: SOUND with caveat

The Picard induction is analytically sound:
  regular iterate n -> regular source for n+1 -> classical regularity for n+1

BUT: "all iterates regular" -> "fixed point regular" is FALSE without either:
- Strong convergence of derivative fields, or
- Direct smoothing theorem for the fixed point

Recommendation: decouple G2 from time-C1. Gradient-to-standard IBP should
require only spatial differentiability + boundary vanishing + time continuity.
Do not make G2 depend on full DuhamelSourceTimeC1.

---

## "No showstopper": JUSTIFIED with constraints

For [0,1], gamma >= 1, positive continuous initial datum, global existence
via boundedness when m >= 1: no conceptual obstruction.

Self-inflicted showstoppers to avoid:
1. Do NOT require classical regularity at t=0
2. Do NOT rely on Picard regularity without pass-to-limit
3. Do NOT leave maximum principle outside gap list unless already formalized
4. Do NOT let real-power differentiability touch zero; keep strict positivity explicit

---

## Line estimate revision

| Scenario | Lines |
|----------|-------|
| Best case (max principle exists) | 1600-2600 |
| Honest planning (with G2.5) | 2200-3800 |
| If max principle missing | 3000-5000 |

---

## Strict positivity / lower-bound note

Paper assumes inf u0 > 0 and positivity is preserved. Formal proof should
consistently work on compact positive ranges. Do not rely on rpow behavior
at zero. Route through positive lower bound hypotheses.

---

## R3/R4 Follow-up: G2 Decoupling Confirmed

ChatGPT confirms gradient-to-standard IBP does NOT require DuhamelSourceTimeC1.

Required hypotheses for G2 (only):
- Q(s,.) in C1([0,1]) for each s (spatial regularity)
- boundary term vanishes (Neumann)
- Q time-continuous or dominated enough to integrate in s

Clean dependency graph:
  spatial C1(Q) + boundary vanish + time integrability
  => gradient Duhamel = standard source Duhamel  [G2]

Then separately:
  standard source Duhamel + source time regularity
  => classical t-regularity/PDE  [G3/G4]

Neumann kernel caveat: d_x K_N may involve companion kernel / signs.
Check boundary terms against Neumann BC. Does not change dependency conclusion.

This decoupling lets G2 be done BEFORE G3 in the dependency order.

---

## R4 Follow-up: Critical Kernel Identity Correction

ChatGPT identified a critical detail all previous design docs missed:

d_x K_N != -d_y K_N on [0,1]. Full-line kernel has this symmetry, Neumann interval does not.

Correct identities:
1. d_x S_N(t) Q = S_D(t) Q' (DIRICHLET semigroup, not Neumann)
2. -integral d_y K_N Q = S_N Q' when Q(0)=Q(1)=0

Current code uses d_x S_N form -> IBP lands on Dirichlet S_D, not Neumann S_N.

G2 split: G2a (kernel convention) + G2b (spatial IBP, no time-C1).

Lean obligations: Dirichlet kernel if keeping d_x S_N; Q in C1; time integrability; agreement with existing regularity package.
