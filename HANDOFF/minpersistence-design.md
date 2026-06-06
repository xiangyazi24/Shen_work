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

## Session A contribution (2026-06-06, on credits) — B2/B4 arithmetic core landed

Three axiom-clean atoms added (separate files, Session-A-owned, importing
worker-3's IntervalDomainMinPersistenceAtoms):
- `IntervalDomainEllipticCoeffBounds.lean` — `elliptic_coeff_bounds`:
  combines worker-3's elliptic_sup_bound + elliptic_deriv_bound into
  `w ≤ B/μ`, `|w'| ≤ 2B`, `|w''| ≤ 2B` (the v-field bounds, B4).
- `IntervalDomainMinPointEstimate.lean` — `min_point_estimate`: the PDE
  inequality `−K·m ≤ u_t` at an argmin (K := |χ₀|K₁ + b·M^α), abstract form
  taking (u''≥0, chemDiv = m·G, |G|≤K₁) as inputs.
- `IntervalDomainFluxCoeffBound.lean` — `flux_coeff_bound` + `fluxCoeffConst`:
  `|φ'v_x² + φv_xx| ≤ K₁ := β(2B)²+2B` from the B4 bounds (φ=(1+v)^{−β}).

These close the ARITHMETIC of B2's min-point step. The two REMAINING B2 pieces
(both genuine analysis, for worker-3 / next):
1. **chemDiv critical-point HasDerivAt expansion**: prove
   `intervalDomainChemotaxisDiv p (u t) (v t) x* = (u t x*)·g` with
   `g = −β(1+v)^{−β−1}v_x² + (1+v)^{−β}v_xx` at a spatial critical point
   (u_x(x*)=0), via deriv_mul (lift u · D, D=φ·v_x) + the φ chain/quotient
   rule (rpow HasDerivAt). Then |chemDiv| side = flux_coeff_bound.
   ⟹ feeds min_point_estimate's `hcd`/`hG`.
2. **Dini wrapper** (the true crux): produce hamilton_lower_bound's hDini
   from min_point_estimate via time-MVT (conjunct 4) + the by_contra
   sequential-compactness argument (isCompact_Icc.isSeqCompact on argmins
   x_h, joint ∂ₜ continuity conjunct 8, sliceMin_continuousOn). ~250-400 ln.
Then B4-instantiation (elliptic_coeff_bounds at Src=ν u^γ, B=νM'^γ via
hSupNorm regimeBound) + C assembly closes ClassicalMinPersistence.

## UPDATE (Session A, on credits): min-point estimate chain COMPLETE (5 atoms)

The full interior min-point estimate `u_t(t,x*) ≥ −K·m` is now assemblable
from axiom-clean atoms (all green, separate Session-A files):
  elliptic_coeff_bounds  (B4: v ≤ B/μ, |v'|,|v''| ≤ 2B)
    → flux_coeff_bound    (|P'| ≤ K₁ := β(2B)²+2B, fluxCoeffConst)
    → flux_integrand_hasDerivAt  (P' = −β(1+v)^{−β−1}v_x² + (1+v)^{−β}v_xx)
    → chemDiv_at_critical (chemDiv = u(x*)·P', via u_x=0 + product rule)
    → min_point_estimate  (u_t ≥ −(|χ₀|K₁+b·M^α)·m at argmin)
K := |χ₀|·K₁ + b·M^α is slab-independent. ✅

### Remaining for ClassicalMinPersistence (worker-3 / next):
A. **Conjunct-extraction wrapper** (mechanical): from IsPaper2ClassicalSolution
   at interior x*, produce the HasDerivAt inputs (hux: u_x=0 from
   IsLocalMin.deriv_eq_zero on the lift over a small interior nbhd; hv/hvxx
   from the C² conjunct 3/7; u''≥0 from deriv2_nonneg_of_isLocalMin; v≥0 from
   the v-nonneg conjunct; the elliptic identity v''=μv−νu^γ from pde_v) →
   feed chemDiv_at_critical + min_point_estimate. The B4 instantiation uses
   Src:=ν·u^γ, B:=νM'^γ (M':=regimeBound via hSupNorm).
B. **Boundary case** x*∈{0,1}: one-sided via Neumann conjunct 6 + the pivot
   helpers deriv_pos_right/deriv_neg_left_of_deriv2_pos_of_pivot.
C. **Dini wrapper** (the true crux, ~250-400 ln): hamilton_lower_bound's hDini
   from min_point_estimate via time-MVT (conjunct 4) + by_contra +
   isCompact_Icc.isSeqCompact on argmins x_h + joint ∂ₜ continuity (conjunct 8)
   + sliceMin_continuousOn. Then C-assembly closes ClassicalMinPersistence
   ⟹ general-χ₀ hQuant via the threshold route.

## UPDATE 2 (Session A): interior min-point machinery = single entry point + first A-atom
- `min_point_estimate_interior` (IntervalDomainMinPointInterior.lean):
  ONE callable `−K·u(x*) ≤ u_t(x*)` from HasDerivAt data + B4 bounds + u''≥0
  + 0≤u(x*)≤M' + the PDE value relation. K = |χ₀|·fluxCoeffConst β (νM'^γ) + b·M'^α.
- `interior_argmin_deriv_zero` + `intervalDomainLift_isLocalMin_of_argmin`
  (IntervalDomainInteriorArgmin.lean): the `hux : u_x=0` input, via Fermat on
  the lift (interior argmin ⟹ IsLocalMin ⟹ deriv 0).
Remaining Phase-A plumbing to feed min_point_estimate_interior from
IsPaper2ClassicalSolution (all worker-3-area, mechanical):
  - hv/hvxx: ContDiffOn ℝ 2 (conjunct 3) on Ioo → DifferentiableAt of lift(v t)
    and of deriv(lift(v t)) at interior x* (ContDiffOn.differentiableAt on the
    open set; deriv of a C² fn is C¹ hence differentiable).
  - huxx: deriv2_nonneg_of_isLocalMin on lift(u t) at x* (have the IsLocalMin
    from intervalDomainLift_isLocalMin_of_argmin; needs the HasDerivAt(deriv) + 
    DifferentiableAt-near from ContDiffOn 2).
  - hvx_bd/hvxx_bd: elliptic_coeff_bounds (B4) instantiated for the v-slice
    (Src=ν·u^γ via pde_v rewritten to deriv²(lift v)=μ·v−ν u^γ; |Src|≤νM'^γ from
    hSupNorm |u|≤M'=regimeBound; Neumann conjunct 6; C² conjunct 7; v≥0), then
    evaluate at x*.
  - PDE relation: pde_u conjunct at interior x* (timeDeriv=deriv(s↦u s x*) t,
    laplacian=deriv²(lift(u t))).
Then B (boundary x*∈{0,1}) + C (Dini wrapper) per UPDATE-1 close it.

## UPDATE 3 (Session A): A-plumbing atoms COMPLETE — only the conjunct-bridge + assembly remain
All min-point inputs now have axiom-clean producer atoms:
  hux       interior_argmin_deriv_zero            (IntervalDomainInteriorArgmin)
  huxx      interior_argmin_deriv2_nonneg         (IntervalDomainInteriorDeriv2)
  hv,hvxx   contDiffOn_two_hasDerivAt_pair        (IntervalDomainC2Extraction)
  Src bd    power_source_abs_le                   (IntervalDomainPowerSourceBound)
  B4        elliptic_coeff_bounds                 (IntervalDomainEllipticCoeffBounds)
  chain     min_point_estimate_interior           (IntervalDomainMinPointInterior)

REMAINING to close the interior min-point estimate from IsPaper2ClassicalSolution
(the only genuinely-new work is the conjunct→lift/real bridge; subtype plumbing):
1. **v-slice B4 instantiation**: feed elliptic_coeff_bounds with
   w := intervalDomainLift (v t), Src := fun y => p.ν*(intervalDomainLift (u t) y)^p.γ,
   μ := p.μ, B := p.ν*M'^p.γ. Hypotheses from the conjuncts:
   - hPDE: pde_v says `0 = laplacian(v t) x − μ·v + ν·u^γ` for x∈inside, with
     laplacian = deriv(deriv(lift(v t))) x.1; bridge to `∀ y∈Ioo,
     deriv²(lift(v t)) y = μ·lift(v t) y − ν·(lift(u t) y)^γ` via the subtype
     y↦⟨y,·⟩ and lift(u/v t) y = (u/v t)⟨y⟩ for y∈[0,1]. ⚠ the rpow base:
     ν·u^γ uses (u t x) — confirm it equals (lift(u t) y)^γ at interior.
   - hSrc: power_source_abs_le with 0≤lift(u t)≤M' (hSupNorm/positivity).
   - hcont/hd1/hd2/hd2c: conjunct 7 (ContDiffOn 2 Icc) + contDiffOn_two_hasDerivAt_pair.
   - hwnn: v-nonneg conjunct. hNeu0/hNeu1: conjunct 6 Neumann tendsto.
   ⟹ |v_x|,|v_xx| ≤ 2νM'^γ on Ioo; evaluate at x*.
2. **PDE relation**: pde_u conjunct at interior x* gives uT := deriv(s↦u s x*) t
   = deriv²(lift(u t)) x*.1 − χ₀·chemDiv + reaction (laplacian/timeDeriv defs).
3. **Capstone**: feed (1)+(2)+hux+huxx+hv+hvxx into min_point_estimate_interior.
Then B (boundary x*∈{0,1}) + C (Dini wrapper) close ClassicalMinPersistence.

The 10 Session-A atoms are all `lake env lean` green + axiom-clean
([propext, Classical.choice, Quot.sound]); committed a1c3df9..(this).

## UPDATE 4 (Session A): PHASE A COMPLETE — interior_min_point_of_solution GREEN
`interior_min_point_of_solution` (IntervalDomainMinPointSolution.lean) — GREEN +
axiom-clean — takes IsPaper2ClassicalSolution + interior time t + interior
spatial argmin x* + |u(t,·)|≤M', returns:
  −(|χ₀|·fluxCoeffConst β (νM'^γ) + b·M'^α)·u(t,x*) ≤ intervalDomain.timeDeriv u t x*.
All conjunct plumbing done: regularity 9-tuple projection (C² Ioo/Icc, Neumann,
positivity, v≥0), pde_v→elliptic identity (subtype/lift bridge), pde_u→PDE
relation. 12 Session-A atoms total, all axiom-clean.

### Only B + C remain for ClassicalMinPersistence:
B. **Boundary argmin** x*∈{0,1}: the min over [0,1] may sit at an endpoint.
   Same conclusion −K·u(0) ≤ u_t(0) via Neumann u_x(0)=0 (conjunct 6) + the
   one-sided second-derivative pivot helpers (deriv_pos_right/_neg_left_of_
   deriv2_pos_of_pivot, already in MinPersistenceAtoms). ~150 ln.
C. **Dini wrapper** (the true crux): assemble interior_min_point_of_solution +
   B into hamilton_lower_bound's hDini, via time-MVT (conjunct 4) + the
   by_contra sequential-compactness on argmins x_h (isCompact_Icc.isSeqCompact)
   + joint ∂ₜ continuity (conjunct 8) + sliceMin_continuousOn. ~250-400 ln.
Then C-assembly (c := m*(t₁)e^{−K(δ−t₁)} + overlap uniqueness) closes
ClassicalMinPersistence ⟹ general-χ₀ hQuant via the threshold route.

The K-constant is fully explicit & slab-independent:
  K = |χ₀|·(β(2νM'^γ)² + 2νM'^γ) + b·M'^α,  M' = regimeBound p M (hSupNorm).

## UPDATE 5 (Session A): Phase-C slope-step landed; B + C-limit are the irreducible crux
- `sliceMin_diff_le_slope` (IntervalDomainSliceMinSlope.lean) GREEN+axiom-clean:
  m x − m z ≤ (x−z)·∂ₛF(ξ,x_z), x_z=argmin(z), ξ∈(x,z) — the per-step time-MVT
  bound the Dini hypothesis is built from. Abstract F (matches sliceMin_isMinOn).

### Exact remaining recipe (single coherent hard proofs — for worker-3):
**C (Dini wrapper)** assembles into hamilton_lower_bound's hDini:
  For x∈[a,b), r > Kp·m(x): want ∃ᶠ z→x⁺, (z−x)⁻¹(m x − m z) < r.
  From sliceMin_diff_le_slope: (z−x)⁻¹(m x − m z) ≤ −∂ₛF(ξ_z, x_z)
  [since (x−z)·d/(z−x) = −d]. Take z→x⁺:
  - x_z ∈ [0,1] compact ⇒ subsequence x_{z_n} → x* (isCompact_Icc.isSeqCompact);
  - x* is an argmin of F x (F z_n x_{z_n}=m z_n → F x x* by joint cont;
    m z_n → m x by sliceMin_continuousOn ⇒ F x x* = m x);
  - ξ_{z_n} → x (squeeze in (x,z_n)); ∂ₛF(ξ_{z_n},x_{z_n}) → ∂ₛF(x,x*)
    [joint ∂ₜ continuity, conjunct 8];
  - min-point estimate at x*: ∂ₛF(x,x*) = u_t(x,x*) ≥ −Kp·m(x)
    [interior_min_point_of_solution if x* interior; **Phase B if x*∈{0,1}**];
  ⇒ −∂ₛF(ξ_{z_n},x_{z_n}) → −u_t(x,x*) ≤ Kp·m(x) < r, so eventually < r. ∎
**B (boundary min-point)** x*∈{0,1}: the lift is DISCONTINUOUS at the endpoint
  (zero-extension jump), so the two-sided HasDerivAt inputs of
  min_point_estimate_interior FAIL there. Need one-sided reformulation:
  u_t(0) = lim_{x→0⁺} u_t(x) [conjunct 8 closed-slab ∂ₜ cont] = lim RHS(x)
  [pde_u interior] = RHS(0) [laplacian cont via conjunct 7 closed C², chemDiv
  cont, reaction cont], with u_x(0)=0 [conjunct 7 endpoint deriv=0] and
  u_xx(0)≥0 [boundary 2nd-deriv test via the pivot helpers]. ~150-250 ln.

All Session-A B2 atoms (14 total incl. slope-step) lake-env-lean green +
axiom-clean. Phase A interior estimate is the single callable
interior_min_point_of_solution. B + C-limit are the irreducible coupled
hard-analysis remaining; recommend one focused worker-3 push (file owner,
has sliceMin + pivot machinery).

## UPDATE 6 (Session A): Phase-B 2nd-deriv test landed (junk-value-free)
- `boundary_min_deriv2_rlimit_nonneg` (IntervalDomainBoundaryDeriv2.lean)
  GREEN+axiom-clean: right-boundary min + w'→0 + w''→V along 0⁺ ⟹ 0 ≤ V.
  Works ENTIRELY with the interior derivative + right-limits (the zero-extension
  lift's two-sided endpoint derivative is junk — this avoids it). The hard
  calculus core of Phase B. (Mirror at x=1 is the analogous left-limit version,
  not yet written — same proof reflected.)

### Phase B remaining (boundary min-point assembly):
At a boundary argmin x*=0: u_t(t,0) = lim_{x→0⁺} u_t-field(t,x) [conjunct 8
closed-slab ∂ₜ continuity] = lim_{x→0⁺} RHS(x) [pde_u interior]. Need:
  - the RHS right-limit = deriv²-rlimit − χ₀·chemDiv-rlimit + reaction(0), with
    deriv²-rlimit ≥ 0 from boundary_min_deriv2_rlimit_nonneg (V := the rlimit),
    chemDiv-rlimit = u(0)·P'-rlimit (critical-pt structure, u'(0⁺)=0 Neumann),
    |P'-rlimit| ≤ K₁ (v-bounds extend to boundary by continuity);
  - assemble via min_point_estimate (abstract, sign analysis) with the rlimit
    quantities ⟹ −K·u(0) ≤ u_t(0).
The rlimit/continuity bookkeeping (conjuncts 6/7/8 → the limits) is the
remaining ~150 ln. C-limit (sequential-compactness Dini) unchanged (UPDATE 5).

Session-A B2/MinPersistence atoms: 15 this campaign, all axiom-clean.

## UPDATE 7 (Session A): PHASE C CRUX DONE — Hamilton trick packaged + axiom-clean
The sequential-compactness Dini argument (flagged as the true crux) is CLOSED:
- `sliceMin_cluster_argmin` — cluster pt of argmins is an argmin (seq-compactness).
- `sliceMin_diff_le_slope` (+ exposed argmin) — per-step time-MVT.
- `sliceMin_dini_of_argmin_bound` — Dini hypothesis from the min-point bound
  (by_contra + cluster + joint-∂ₜ-cont limit). GREEN + axiom-clean.
- `sliceMin_hamilton_bound` — packaged: `m(a)·e^{−Kp(t−a)} ≤ m(t)` from the
  min-point bound (Dini ∘ hamilton_lower_bound). GREEN + axiom-clean.

### ONLY 2 pieces remain for ClassicalMinPersistence:
1. **Boundary min-point assembly (Phase B full)**: feed `hbound` at boundary
   argmins x*∈{0,1}. Have `boundary_min_deriv2_rlimit_nonneg` (the 2nd-deriv
   test). Still need: u_t(0)=lim RHS (conjunct 8) with chemDiv up-to-boundary
   continuity (C¹ of the flux F=lift u·P on Icc) ⟹ −K·u(0) ≤ u_t(0). The
   chemDiv-continuity-to-boundary is the remaining hard sub-piece. [Interior
   argmins already done: interior_min_point_of_solution.]
2. **Final assembly**: instantiate sliceMin_hamilton_bound with F := the
   solution slices (Kp := K(M'), bound from interior_min_point_of_solution ∪
   boundary), then the c := m*(t₁)·e^{−K(δ−t₁)} construction + overlap
   uniqueness (chosen-solution trick) ⟹ ClassicalMinPersistence. Mostly
   wiring once hbound covers all argmins.

Session-A B2/MinPersistence atoms: 18 this campaign, all axiom-clean. The two
genuine analysis cruxes (interior min-point chain + the Dini wrapper) are DONE.

## UPDATE 8 (Session A): per-solution persistence from conjuncts — DONE
- `solution_minPersist_core` (IntervalDomainMinPersistCore.lean): Hamilton bound
  applied to a solution's lift-slices ⟹ u(t,x) ≥ m_u(a)·e^{−Kp(t−a)}, GREEN+ac.
- `solution_minPersist_of_conjuncts` (IntervalDomainMinPersistSolution.lean):
  extracts the Hamilton regularity inputs from IsPaper2ClassicalSolution
  conjuncts 9 (hF, closed-slab solution cont), 8 (hdF_cont, ∂ₜ cont), 4
  (hslice_diff, time slices) on [a,b]⊆(0,T); from the min-point bound hbound
  ⟹ u(t,x) ≥ m_u(a)·e^{−Kp(t−a)}. GREEN + axiom-clean.

### ClassicalMinPersistence — remaining (precise):
The per-solution persistence is COMPLETE modulo `hbound`. To finish:
(a) **hbound at all argmins**: ∀ s∈[a,b], ∀ argmin ys of lift(u s),
    −Kp·m ≤ ∂ₛ(lift(u ·) ys) s.
    - interior ys (ys∈(0,1)): `interior_min_point_of_solution` (need to bridge
      its `intervalDomain.timeDeriv u s ⟨ys⟩` = `deriv (fun r => lift(u r) ys) s`
      and Kp := |χ₀|·fluxCoeffConst β (νM'^γ) + b·M'^α, with hbound's regimeBound
      sup |u|≤M' from hSupNorm).
    - boundary ys∈{0,1}: the boundary assembly (have boundary_min_deriv2_rlimit_
      nonneg; still need u_t(0)=lim RHS via chemDiv up-to-boundary continuity).
(b) **m_u(a) > 0**: a:=t₁/2 interior; u(a,·)>0 (positivity conjunct) continuous
    on compact [0,1] ⟹ min attained > 0 ⟹ m_u(t₁/2) > 0.
(c) **uniform c across solutions**: c := m_{u*}(t₁/2)·e^{−Kp(δ−t₁/2)} for a chosen
    solution u*; overlap uniqueness (OverlapUniqueForPID, proved) ⟹ all
    solutions with trace u₀ agree at t₁/2 ⟹ same m ⟹ uniform c. Moderate wiring.

Session-A MinPersistence campaign: 20 axiom-clean atoms. BOTH analysis cruxes
(interior min-point full chain + the seq-compactness Dini/Hamilton wrapper) +
per-solution persistence from conjuncts are DONE. Remaining = hbound bridge
(interior wiring + boundary chemDiv-continuity) + c-construction/uniformity.

## UPDATE 9 (Session A): PER-SOLUTION ClassicalMinPersistence COMPLETE
- `sliceMin_pos_of_solution`: m_u(t)>0 at interior times (positivity + min attained).
- `solution_persist_exists_c` (IntervalDomainPersistExistsC.lean): from hsol +
  hbound on [t₁/2,T) ⟹ ∃ c>0, ∀ t∈[t₁,T), ∀ x, c ≤ u(t,x).
  c := m_u(t₁/2)·e^{−Kp(δ−t₁/2)}. GREEN + axiom-clean.
This IS ClassicalMinPersistence for a FIXED solution.

### Full ClassicalMinPersistence (∃c BEFORE ∀solution) — 2 remaining:
1. **hbound** (the min-point bound, the input to solution_persist_exists_c):
   - interior argmins: bridge `interior_min_point_of_solution`
     (timeDeriv u s ⟨ys⟩ = deriv(fun r=>lift(u r) ys) s defeq; Kp :=
     |χ₀|·fluxCoeffConst β (νM'^γ)+b·M'^α; M' from hSupNorm).
   - boundary argmins ys∈{0,1}: boundary assembly (have
     boundary_min_deriv2_rlimit_nonneg; need u_t(0)=lim RHS via chemDiv
     up-to-boundary continuity — the one hard analytic gap left).
2. **Cross-solution uniformity**: swap ∀solution,∃c → ∃c,∀solution. c is
   datum-determined: overlap uniqueness (OverlapUniqueForPID, proved) ⟹ all
   solutions with trace u₀ agree at t₁/2 ⟹ same m_u(t₁/2) ⟹ uniform c.
   Chosen-solution trick (vacuous c:=1 if no solution). Moderate wiring.

CAMPAIGN TOTAL (Session A, MinPersistence): 22 axiom-clean atoms. BOTH analysis
cruxes (interior min-point chain, seq-compactness Dini/Hamilton) + per-solution
persistence assembly = DONE. Only the hbound boundary-continuity gap + the
uniqueness wiring remain for the literal predicate.

## UPDATE 10 (Session A): per-solution persistence FULLY ASSEMBLED — residual minimal
- `hbound_interior` (IntervalDomainHboundInterior.lean): interior min-point
  bound in exact hbound shape (bridges interior_min_point_of_solution;
  argmin→hmin + timeDeriv/deriv-lift defeq). GREEN + axiom-clean.
- `hbound_full` + `solution_persist_of_supNorm` (IntervalDomainPersistAssembly.lean):
  interior/boundary by_cases (interior PROVED) → full hbound → per-solution
  persistence `∃c>0, u≥c on [t₁,T)`. GREEN + axiom-clean.

### LITERAL ClassicalMinPersistence — residual now MINIMAL (3 items):
1. **boundary hbound** `hbdry` (ys∈{0,1}): u_t(0)=lim RHS (conjunct 8) with
   chemDiv up-to-boundary continuity (C¹ of flux F=lift u·P on Icc) + the
   2nd-deriv test `boundary_min_deriv2_rlimit_nonneg`. THE one hard analytic gap.
2. **hSupNorm** `|lift(u s)| ≤ M'` on [t₁/2,T): = regimeBound/Lemma 3.1
   (SupNormBridge.interiorSupNorm_le_regimeBound, PROVED) — wiring (the bound
   is for x interior; extend to the lift on all of ℝ via the [0,1]-restriction +
   0-outside). Moderate.
3. **cross-solution uniformity** (∃c BEFORE ∀solution): per-solution c =
   m_u(t₁/2)·e^{−K(δ−t₁/2)}; overlap uniqueness (OverlapUniqueForPID, PROVED)
   ⟹ all solutions with trace u₀ share m_u(t₁/2). Chosen-solution + vacuous
   branch. Moderate wiring.

CAMPAIGN TOTAL (Session A, MinPersistence): 24 axiom-clean atoms. The two
genuine analysis cruxes + the full per-solution persistence assembly are DONE.
Only #1 (hard, chemDiv-boundary-continuity) + #2/#3 (wiring) remain.

## UPDATE 11 (Session A): residual #2 closed, uniformity core landed
- `lift_abs_le_of_slice_bound` + `hSupNorm_of_regime` (IntervalDomainHSupNorm.lean):
  RESIDUAL #2 CLOSED — wires SupNormBridge.interiorSupNorm_le_regimeBound
  (Lemma 3.1) to the hSupNorm shape (M' := regimeBound p M).
- `intervalDomainLift_congr` + `sliceMin_eq_of_slices_eq` (IntervalDomainSliceMinEq.lean):
  uniformity core — equal slices ⟹ equal spatial minima. OverlapUniqueForPID
  (GlueExtension.lean:41) gives u₁(s)=u₂(s) on (0,min T₁ T₂) ⟹ same m at t₁/2.

### Literal ClassicalMinPersistence — final assembly recipe (2 items left):
1. **boundary hbound** `hbdry` (ys∈{0,1}) — the ONE hard analytic gap:
   u_t(0)=lim_{x→0⁺} RHS [conjunct 8] with chemDiv up-to-boundary continuity
   (C¹ of flux F=lift u·P on Icc) + boundary_min_deriv2_rlimit_nonneg.
2. **uniformity assembly** (∃c-before-∀solution), ~200 ln intricate but all
   pieces exist:
   - M from PID: hu₀.1.1 : BddAbove (range |u₀|) ⟹ ∃M>0, |u₀|≤M; M':=regimeBound.
   - Kp := |χ₀|·fluxCoeffConst β (νM'^γ) + b·M'^α.
   - by_cases ∃ solution on (t₁,δ]: NO ⟹ c:=1 vacuous; YES ⟹ chosen u*,
     c := sInf(lift(u* (t₁/2)) '' [0,1])·e^{−Kp(δ−t₁/2)} (>0 via
     sliceMin_pos_of_solution).
   - ∀ solution u: solution_minPersist_of_conjuncts (a:=t₁/2,b:=t) ⟹
     u t x ≥ m_u(t₁/2)·e^{−Kp(t−t₁/2)}; OverlapUniqueForPID + sliceMin_eq_of_slices_eq
     ⟹ m_u(t₁/2)=m_{u*}(t₁/2); exp monotone (t≤δ) ⟹ ≥ c.
     [hbound for each u via hbound_full + hSupNorm_of_regime + hbdry(u).]

CAMPAIGN TOTAL (Session A, MinPersistence): 26 axiom-clean atoms. Both cruxes +
per-solution persistence + interior hbound bridge + hSupNorm + uniformity core
DONE. Only the boundary chemDiv-continuity gap (hard) + the uniformity assembly
wiring (intricate, all pieces present) remain for the literal predicate.
