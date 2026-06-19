# Paper 1 traveling-wave — the FAITHFUL §4.2 architecture (source-grounded, ChatGPT cron3 + paper1.pdf)

Purpose: the avenue-c map. Replaces the guessed wave structure with Shen's ACTUAL §4.2 construction
(filecite-grounded read of paper1.pdf, to be verified per-brick against the source when formalizing).

## FIVE corrections to the earlier guess (each changes the formalization)
1. **NOT a direct elliptic/Schauder solve** of `U''+cU'−χ(U^mV_x)'+U(1−U^α)=0`. The wave is a **long-time
   parabolic limit map** `T_{κ,1}u := lim_{t→∞} w(t,·;u)`, then Schauder on `T_{κ,1}`. Only after the fixed
   point is found is the stationary profile + the wave `u(t,x)=U*(x−ct)` read off.
2. **The trap is EXPONENTIAL barriers, not constant.** `U⁺_{κ,1}=min(1,e^{−κx})`,
   `U⁻_{κ,κ̃,D}=e^{−κx}−De^{−κ̃x}` (plateau on the left). Constant barriers give only `0≤w≤1`
   (global boundedness); the exponential trap gives the connection to 0 at +∞, the right-tail rate, AND the
   compact self-map. ⟹ my constant-barrier energy work is the global-boundedness sub-piece, NOT the wave trap.
3. **The speed c is FREE above a threshold** `c>c*_{χ,m,γ}` (a half-line of speeds, not shooting/eigenvalue).
   `κ=(c−√(c²−4))/2`, so `κ²−cκ+1=0`, `c=κ+κ⁻¹`, `0<κ<1`; choose `κ<κ₁<κ̃≤min{(1+α)κ, mκ+½, 1}`.
4. **Monotonicity (spatial AND temporal) is by DIFFERENTIATED PARABOLIC COMPARISON — a WEAK max principle**,
   not sliding, not ODE linearization, NOT a pointwise strong max principle. `q=w_x` solves a linear parabolic
   inequality `q_t ≤ q_xx + (c+|χ|mw^{m-1}V_x)q_x + B q` (the quadratic `|χ|m(m−1)w^{m-2}q²V_x ≤ 0` since
   V_x≤0), `q(0)≤0 ⟹ q≤0`. **This weak comparison is EXACTLY what the energy machinery (cx_pde) gives — no SMP
   needed.** Time-monotonicity `w(t₂)≤w(t₁)` likewise by comparison with the time-shift.
5. **Left limit U*(−∞)=1 is by CONTRADICTION + translate compactness + Prop 1.2** (stability of the positive
   constant equilibrium) — NOT linearization at U=1. Prop 1.2 = the linear-stability result already
   formalized unconditionally (T10 in PLAYBOOK_AUDIT). So the left tail WIRES an already-done piece.

## The analytic HEART (the hard, paper-specific package — bricks 6–11)
turn local parabolic existence into a compact long-time self-map: exponential sub/super inequalities (Lem
4.1/4.2) → global trapping of the auxiliary flow → spatial monotonicity (differentiated comparison) → time
monotonicity → long-time stationary limit → continuity+compactness of `u↦T_{κ,1}u` → left-end via translate
compactness + Prop 1.2. STANDARD pieces: the local-uniform topology, the one Schauder application, the
diagonal algebra (aux stationary eq → divergence-form wave, via V''=V−U^γ), the right-tail squeeze, the
resolvent endpoint limits.

## The 17-brick ordered formalization list (avenue-c)
1. Speed/exponent algebra: c>c*, κ(c), c=κ+κ⁻¹, 0<κ<1, admissible (κ₁,κ̃) interval nonempty.
2. Exponential barriers U⁺_{κ,1}, U⁻_{κ,κ̃,D}: continuity, monotonicity, endpoints, squeeze.
3. Wave trap E'_{κ,1}: convex, closed in local-uniform topology, bounded, monotone, local-compactness.
4. Frozen elliptic signal: u∈E'_{κ,1} ⟹ V=Ψ(u^γ) has 0≤V≤1, V_x≤0 (positive Yukawa kernel + monotone u).
5. Auxiliary parabolic local existence: eq (4.12) `w_t=w_xx+cw_x−χmw^{m-1}w_xV_x−χw^mV+χw^{m+γ}+w(1−w^α)`,
   w(0)=U⁺_{κ,1}, frozen V. (Use the local mild existence with the PAPER auxiliary operator.)
6. Barrier comparison + global continuation: U⁻≤w(t)≤U⁺ ∀t≥0 (Lem 4.1/4.2). ← energy/weak-comparison.
7. Spatial monotonicity: q=w_x, weak parabolic comparison q_t≤q_xx+a q_x+b q, q(0)≤0 ⟹ w_x≤0. ← cx_pde tool.
8. Time monotonicity: w(t₂)≤w(t₁) by comparison with time-shift (U⁺ a super-solution). ← cx_pde tool.
9. Long-time limit: U(·;u)=lim_{t→∞}w(t,·;u), monotone convergence + local-uniform compactness ⟹ ∈E'_{κ,1}.
10. Stationarity of the limit: pass aux eq to t→∞, A(U;u)=0.
11. T_{κ,1} compact + continuous in local-uniform topology (parabolic a-priori estimates + brick-5 continuity).
12. Schauder fixed point: U*=T_{κ,1}U*. ← WholeLineSchauderFixedPoint (banked) plugs in here.
13. Diagonal stationary eq: u=U* ⟹ aux stationary = U*''+cU*'−χ(U*^m V_x*)'+U*(1−U*^α)=0, V*''−V*+U*^γ=0.
14. Traveling-wave conversion: u(t,x)=U*(x−ct), v=V*(x−ct), verify original PDE.
15. Right tail + monotonicity: barrier squeeze ⟹ U*(+∞)=0, explicit rate U*/e^{−κx}→1, U*_x≤0.
16. Left tail: translate compactness + Prop 1.2 (=T10, done) ⟹ U*(−∞)=1; resolvent ⟹ V*(−∞)=1.
17. Strictness + polished statement: upgrade non-strict trap to the theorem's strict form (last).

## How the banked foundations map in
- WholeLineHeatSemigroup / WholeLineResolvent → bricks 4, 5 (the e^{(Δ−I)t} flow + V=Ψ(u^γ)).
- WholeLineResolvent_second_deriv (V''=V−f) → bricks 4, 13 (the diagonal algebra).
- LocalUniformCompactness (Ascoli+diagonal) → bricks 9, 11 (the local-uniform compactness of T).
- WholeLineConstantBarrierEnergy (weak energy comparison) → GENERALIZES to bricks 6,7,8 (the differentiated
  weak parabolic comparison — same negative-part energy method, now on the linear inequality for q=w_x).
- WholeLineSchauderFixedPoint → brick 12.
- WholeLineMildMap / ...Continuity → bricks 5, 11 (the aux flow + T-continuity).
- Prop 1.2 / T10 (linear stability of positive equilibrium, DONE unconditional) → brick 16 (left tail).

## Verdict
The constant-barrier + Schauder + compactness foundation is CORRECT but is the global-boundedness + abstract-FP
layer. The wave proper needs: the exponential-barrier trap (brick 2-3), the auxiliary moving-frame flow
(brick 5), the differentiated WEAK comparison for monotonicity (brick 7-8, energy-method-provable — no SMP),
the long-time map + its compactness (brick 9-11), and the left-tail wiring to the already-done Prop 1.2/T10.
No constant-barrier-only shortcut reaches the wave; but no pointwise strong max principle is needed either.
