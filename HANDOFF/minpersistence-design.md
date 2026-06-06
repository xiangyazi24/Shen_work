# ClassicalMinPersistence battle plan (general χ₀ ≤ 0) — Session B

Target (`QuantFromThreshold.ClassicalMinPersistence p`): ∀ PID u₀,
∀ window 0 < t₁ < δ, ∃ c > 0 s.t. every classical solution with trace u₀
on horizon T ∈ (t₁, δ] satisfies c ≤ u(t,x) on [t₁, T) × [0,1].
This is the ONLY missing input for general-χ₀ hQuant via the threshold
route (χ₀ = 0 is already closed by the cone).

## The route (fully derived 2026-06-06 night)

m(t) := min_x u(t,x).  Hamilton's trick + Gronwall:
m(t) ≥ m(t₁)·e^{−K(M)(t−t₁)}, K(M) explicit and slab-independent.

### Coefficient bounds (elementary; NO new elliptic machinery)
From the v-fields at fixed t (C² closed Icc = conjunct 7; Neumann;
elliptic identity v_xx = μv − ν·u^γ on inside; v ≥ 0; |u| ≤ M' :=
regimeBound p M via proved hSupNorm):
- v ≤ νM'^γ/μ        (1-d max principle: argmax + 2nd-deriv test)
- |v_x| ≤ 2νM'^γ     (FTC from Neumann endpoint: v_x = ∫₀ˣ v_xx)
- |v_xx| ≤ 2νM'^γ    (directly from the identity)
- φ := (1+v)^{−β}: |φ| ≤ 1, |φ'| ≤ β
⇒ g := ∂ₓ(φ(v)v_x) = φ'v_x² + φv_xx, |g| ≤ K₁(M) := β(2νM'^γ)² + 2νM'^γ.

### Min-point PDE estimate
At a time-t argmin x*:
- interior: u_x(x*) = 0 (IsLocalMin.deriv_eq_zero on the lift; small
  interior nbhd avoids the zero-extension jump), Δu(x*) ≥ 0
  (deriv2_nonneg_of_isLocalMin — Phase A(i)), chemDiv(x*) =
  u_x·φv_x + u·g = u(x*)·g(x*) ⇒ u_t(t,x*) ≥ −(|χ₀|K₁ + bM'^α)·m(t)
  =: −K·m(t).
- boundary x* ∈ {0,1}: u_t extends continuously to the closed slab
  (conjunct 8); PDE-RHS limit uses lim u_x = 0 (conjunct 6) + one-sided
  second-derivative sign.  Options: (a) one-sided test via
  taylor_mean_remainder_lagrange on [0,y] (derivWithin at the endpoint =
  limit of interior derivs from C² + conjunct 6; ξ_y → 0 +
  iteratedDerivWithin continuity); (b) even-reflection gluing.
  Either ~150–250 lines.

### Hamilton slope + Gronwall (the crux)
- m continuous on compact slabs (Heine–Cantor from conjunct 9; pattern =
  GlueExtension.timeShiftInitialTraceWorks proof).
- Right-slope: m(t+h) − m(t) ≥ u(t+h,x_h) − u(t,x_h), x_h := argmin(t+h);
  time-MVT (conjunct 4) = h·u_t(ξ_h,x_h); by-contradiction + sequential
  compactness of [0,1]: limits x* of x_h are argmins of m(t) (joint
  continuity), u_t(ξ_h,x_h) → u_t(t,x*) (conjunct 8) ≥ −K·m(t).
  ⇒ for f := −m: liminf-right-slope f(t) ≤ K·m(t) = (−K)·f(t).
- `le_gronwallBound_of_liminf_deriv_right_le` (Mathlib Analysis/ODE/
  Gronwall) with f := −m, f' := (−K)·f, K_g := −K, ε := 0, δ := −m(t₁):
  f(t) ≤ −m(t₁)e^{−K(t−t₁)} ⇒ m(t) ≥ m(t₁)e^{−K(t−t₁)}.  SIGNS VERIFIED.
  The `hf'` "frequently" hypothesis from the argmin-subsequence
  contradiction argument.

### Assembly
c := m*(t₁)·e^{−K(δ−t₁)}, m*(t₁) := slice-min at t₁ of ONE chosen
solution (classical choice on ∃-solution; vacuous branch c := 1).  All
solutions with the same trace agree at common times by the PROVED
overlap uniqueness (regime), so every solution's Hamilton bound starts
from the same m*(t₁) > 0 (positivity field + compactness + slice
continuity).  K is slab-independent (that is the point of the elliptic
coefficient bounds), so no open-endpoint compactness issue.

## KEY SIMPLIFICATION (discovered during A(iii))
One-sided second-derivative tests (the old A(ii)) are UNNECESSARY:
the "strict trick" — `w(x*) > B/μ` forces `w'' > 0 on a NEIGHBOURHOOD,
so `w'` is strictly monotone there; with a pivot (`w'(x*) = 0` interior
via deriv-continuity-from-C², or `w' → 0` at a Neumann endpoint), `w'`
is one-signed adjacent to the extremum, so `w` strictly moves — beats
the extremum.  The same ε-room exists inside the Hamilton by_contra
(the Gronwall hypothesis `∀ r > f' x, frequently slope < r` is already
strict), so Phase B can use the identical pattern.

## Status (all green + axiom-clean)
- Phase A(i) DONE: deriv2_nonneg_of_isLocalMin / deriv2_nonpos_of_isLocalMax.
- Phase A(iii) DONE (e9fd30c): elliptic_sup_bound (1-d elliptic max
  principle, interior + both Neumann endpoints, via the strict trick)
  + pivot helpers deriv_pos_right/deriv_neg_left_of_deriv2_pos_of_pivot
  (these are exactly the Hamilton-side adjacency lemmas too).
- Phase A(iv) DONE (4764601): elliptic_deriv_bound — |w'| ≤ μ·Mw + B on
  the interior from the Neumann endpoint via FTC + the pivot limit.
- PHASE A COMPLETE (4 atoms, all green + axiom-clean).
- Phase B1 DONE (be2a1c8): sliceMin_isMinOn (attainment) +
  sliceMin_continuousOn (m-trajectory continuity via Heine–Cantor on
  compact slabs) — first-try green, axiom-clean.
- Next session executes B2–B5:
  B2. The slope estimate at fixed t: m(t+h) − m(t) ≥ u(t+h,x_h) − u(t,x_h)
      (x_h := sliceMin argmin at t+h), time-MVT (conjunct 4), and the
      by_contra subsequence: if ∀h∈(0,η) slope ≥ r > (−K)f(t), then
      x_{1/n} has a convergent subsequence → x* (Bolzano–Weierstrass =
      isCompact_Icc.isSeqCompact), x* is an argmin of m(t)
      (sliceMin continuity + joint continuity), u_t(ξ_h,x_h) → u_t(t,x*)
      (conjunct 8), and the min-point PDE estimate (interior: Phase A
      lemmas; boundary: pivot helpers + conjunct 6 Neumann tendsto +
      closed-slab u_t continuity) contradicts r > K·m(t).
  B3. ✅ DONE (green, axiom-clean): hamilton_lower_bound — m continuous +
      right-lower-Dini (∀x∈[a,b), ∀r > Kp·m(x), ∃ᶠ z→x⁺,
      (m(x)−m(z))/(z−x) < r) ⇒ m(a)·e^{−Kp(t−a)} ≤ m(t).  Pure analysis,
      via le_gronwallBound_of_liminf_deriv_right_le (f:=−m, K:=−Kp).
      B2 now only has to produce the Dini hypothesis from the PDE.
  B4. K(M) from the elliptic atoms: |g| ≤ β(2νM'^γ)² + 2νM'^γ via
      elliptic_sup_bound (w := lift v, Src := ν·u^γ lift, B := νM'^γ)
      and elliptic_deriv_bound; K := |χ₀|·K₁ + b·M'^α.
  C.  Assembly: c := m*(t₁)·e^{−K(δ−t₁)} with the chosen-solution trick
      + overlap uniqueness (see above).
