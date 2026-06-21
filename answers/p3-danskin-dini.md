# Paper 3: compact-min Danskin/Dini lemma

## Target

We need a reusable Lean lemma for the lower-right Dini derivative of a compact spatial minimum.  Let `K : Set R` be compact and nonempty, let `f : R -> R -> R`, and let

    z s = min_{x in K} f s x.

At a fixed time `t`, define

    argmin_t = {x | x in K and f t x = z t}.

The desired statement is

    lowerRightDini z t >= inf_{x in argmin_t} ft t x.

For Lean, the best route is not to chase a sequence realizing `Filter.liminf`.  The buildable route is:

1. prove that every sufficiently small positive difference quotient is bounded below by `G - eps`;
2. conclude `G <= Filter.liminf quotient (nhdsWithin 0 (Ioi 0))` by a small order-filter helper;
3. instantiate `G` as the minimum of `ft t` on the compact argmin set.

This avoids fragile liminf-subsequence API and isolates the only calculus input as a uniform first-order lower expansion.

## 1. Definitions

Use this Dini derivative:

    noncomputable def lowerRightDini (z : R -> R) (t : R) : R :=
      Filter.liminf
        (fun h : R => (z (t + h) - z t) / h)
        (nhdsWithin (0 : R) (Set.Ioi 0))

Use a package for compact minima instead of expanding `sInf` in the core lemma:

    structure CompactMinFamily
        (K : Set R) (f : R -> R -> R) (z : R -> R) : Prop where
      K_compact : IsCompact K
      K_nonempty : K.Nonempty
      z_le : forall s, forall x, x in K -> z s <= f s x
      exists_min : forall s, exists x, x in K and f s x = z s

Define

    def ArgminAt (K : Set R) (f : R -> R -> R) (z : R -> R) (t : R) : Set R :=
      {x | x in K and f t x = z t}

The calculus hypothesis should be the following predicate:

    def UniformRightDerivLowerOnCompact
        (K : Set R) (f ft : R -> R -> R) (t : R) : Prop :=
      forall eps > 0, exists eta > 0,
        forall h, 0 < h -> h < eta ->
          forall x, x in K ->
            ft t x - eps <= (f (t + h) x - f t x) / h

Also use a uniform time-continuity predicate:

    def UniformTimeContinuityOnCompact
        (K : Set R) (f : R -> R -> R) (t : R) : Prop :=
      forall eps > 0, exists eta > 0,
        forall h, 0 < h -> h < eta ->
          forall x, x in K -> abs (f (t + h) x - f t x) <= eps

These two predicates keep the Danskin proof independent of interval-integral or mean-value-theorem API.

## 2. Compact argmin facts

Argmin nonempty follows directly from `CompactMinFamily.exists_min t`.

Argmin compact follows from continuity of `fun x => f t x` on `K`:

    ArgminAt K f z t = K inter (fun x => f t x) preimage {z t}.

Useful Mathlib names:

- `ContinuousOn.preimage_isClosed_of_isClosed`
- `IsCompact.isClosed`
- `isClosed_singleton`
- `IsCompact.of_isClosed_subset`

Skeleton:

    have hclosed : IsClosed (K inter (fun x => f t x) ⁻¹' ({z t} : Set R)) :=
      hcont.preimage_isClosed_of_isClosed H.K_compact.isClosed isClosed_singleton

    have hc : IsCompact (K inter (fun x => f t x) ⁻¹' ({z t} : Set R)) :=
      IsCompact.of_isClosed_subset H.K_compact hclosed (by intro x hx; exact hx.1)

Then `simpa [ArgminAt, Set.setOf_and] using hc`.

The minimum of `ft t` on argmin is obtained using:

- `IsCompact.exists_isMinOn`

with `ContinuousOn (fun x => ft t x) (ArgminAt K f z t)`.

## 3. Near-minimizer upgrade

The main compactness lemma is:

    theorem argmin_ft_lower_near_min
        (H : CompactMinFamily K f z)
        (hf_cont_K : ContinuousOn (fun x => f t x) K)
        (hft_cont_K : ContinuousOn (fun x => ft t x) K)
        (hG : forall x, x in ArgminAt K f z t -> G <= ft t x) :
        forall eps > 0, exists rho > 0,
          forall x, x in K -> f t x <= z t + rho -> G - eps <= ft t x

Proof idea:

1. Define the bad set

       Bad = {x | x in K and ft t x <= G - eps}.

2. `Bad` is compact using `ContinuousOn.preimage_isClosed_of_isClosed` and `isClosed_Iic`.

3. `Bad` is disjoint from argmin, because on argmin we have `G <= ft t x`, while in `Bad` we have `ft t x <= G - eps`.

4. If `Bad` is empty, choose `rho = 1`.

5. If `Bad` is nonempty, use `IsCompact.exists_isMinOn` to minimize `fun x => f t x` on `Bad`.  Let the minimizer be `xbad`.  Since `xbad` is not an argmin and `z t` is the minimum on `K`, prove

       z t < f t xbad.

   Choose

       rho = (f t xbad - z t) / 2.

6. If `x in K` and `f t x <= z t + rho`, then `x` cannot lie in `Bad`.  Hence not `ft t x <= G - eps`, and therefore `G - eps <= ft t x`.

This lemma is the Lean-friendly replacement for the informal subsequence argument `x_h -> x_* in argmin`.

## 4. Core Danskin theorem

The core theorem should be stated with an arbitrary lower bound `G` for `ft` on argmin.

    theorem lowerRightDini_min_ge_of_argmin_ft_lower
        (Hmin : CompactMinFamily K f z)
        (hderivLower : UniformRightDerivLowerOnCompact K f ft t)
        (htimeCont : UniformTimeContinuityOnCompact K f t)
        (hnear : forall eps > 0, exists rho > 0,
          forall x, x in K -> f t x <= z t + rho -> G - eps <= ft t x) :
        G <= lowerRightDini z t

Proof skeleton:

1. It suffices to prove that for every `eps > 0`, eventually as `h -> 0+`,

       G - eps <= (z(t+h) - z(t)) / h.

   Use a helper:

       theorem le_liminf_of_eventually_ge
           (h : forall eps > 0, forallᶠ h in nhdsWithin 0 (Ioi 0), G - eps <= q h) :
           G <= Filter.liminf q (nhdsWithin 0 (Ioi 0))

   Expected Mathlib route: `le_liminf_iff`.  If that name is not available under the current imports, prove this helper once by unfolding the order definition of `Filter.liminf`.

2. Given `eps > 0`, set `eps3 = eps / 3`.

3. Use `hnear eps3` to get `rho > 0`.

4. Use uniform time continuity with `rho / 4`.

5. Use uniform derivative lower with `eps3`.

6. Choose `eta = min eta_time eta_deriv`.

7. For `0 < h < eta`, choose `xh in K` minimizing at time `t+h`, using `Hmin.exists_min (t+h)`.  Choose `x0 in K` minimizing at time `t`, using `Hmin.exists_min t`.

8. Show `xh` is a near-minimizer at time `t`:

       f t xh <= z t + rho.

   Indeed,

       f t xh <= f(t+h,xh) + rho/4
              = z(t+h) + rho/4
              <= f(t+h,x0) + rho/4
              <= f(t,x0) + rho/2
              = z(t) + rho/2
              <= z(t) + rho.

9. Therefore

       G - eps3 <= ft t xh.

10. The uniform derivative lower bound gives

       ft t xh - eps3 <= (f(t+h,xh) - f(t,xh)) / h.

11. Since `z t <= f t xh` and `z(t+h)=f(t+h,xh)`, and `h > 0`,

       (f(t+h,xh) - f(t,xh)) / h
         <= (z(t+h) - z(t)) / h.

12. Combine the inequalities and absorb the `eps / 3` losses.

The theorem can be proved using only compact min facts, uniform time continuity, uniform right derivative lower, and elementary real arithmetic (`nlinarith`/`linarith`).

## 5. Final theorem with inf over argmin

After the explicit-`G` theorem is proved, add a wrapper where `G` is the minimum of `ft t` over `argmin_t`.

Recommended Lean representation:

    noncomputable def minOverSubtype (K : Set R) (f : R -> R -> R) (s : R) : R :=
      iInf (fun x : {x : R // x in K} => f s x.1)

    def ArgminSubtype (K : Set R) (f : R -> R -> R) (t : R) : Type :=
      {x : {x : R // x in K} // f t x.1 = minOverSubtype K f t}

Then target:

    theorem lowerRightDini_minOver_ge_iInf_argmin :
      iInf (fun x : ArgminSubtype K f t => ft t x.1.1) <=
        lowerRightDini (fun s => minOverSubtype K f s) t

To prove it:

1. build `CompactMinFamily K f (fun s => minOverSubtype K f s)` from compactness and continuity;
2. show argmin is nonempty and compact;
3. use `IsCompact.exists_isMinOn` to get an argmin point where `ft t` attains its minimum;
4. instantiate the explicit-`G` theorem with that value;
5. rewrite or compare with the `iInf` value using `iInf_le`, `le_iInf`, or compact-image `sInf` facts.

The explicit-`G` theorem is the one the PDE proof should use directly; the `iInf` theorem is a polished wrapper.

## 6. Discharging uniform derivative lower from C1 data

Keep this as a separate lemma.

Assume a package like:

    structure TimeC1OnCompact
        (K : Set R) (f ft : R -> R -> R) (t eta0 : R) : Prop where
      eta0_pos : 0 < eta0
      deriv : forall s, s in Icc t (t + eta0) -> forall x, x in K ->
        HasDerivAt (fun tau => f tau x) (ft s x) s
      ft_uniform : forall eps > 0, exists eta > 0,
        forall s, s in Icc t (t + eta) -> forall x, x in K ->
          abs (ft s x - ft t x) <= eps

Then prove:

    theorem uniformRightDerivLowerOnCompact_of_timeC1
        (H : TimeC1OnCompact K f ft t eta0) :
        UniformRightDerivLowerOnCompact K f ft t

Proof:

1. fix `eps > 0`;
2. choose `eta` so `ft s x >= ft t x - eps` for `s in [t,t+eta]` and `x in K`;
3. use the fundamental theorem of calculus on `tau |-> f tau x` over `[t,t+h]`;
4. integrate the lower bound to obtain

       f(t+h,x) - f(t,x) >= h * (ft t x - eps);

5. divide by `h > 0`.

The relevant Mathlib theorem names around interval integral/FTC are import-sensitive in v4.29.1.  Use this lemma to isolate that API.  Typical names to check are in the `intervalIntegral` namespace, especially theorem families containing `integral_eq_sub_of_hasDerivAt` or `integral_deriv_eq_sub`.  The compact-min Danskin theorem itself should not depend on these names.

## 7. Chemotaxis persistence application

For the PDE, take

    K = Icc 0 1,
    f t x = u t x,
    ft t x = u_t t x,
    z t = min_{x in [0,1]} u t x.

At a minimizer `x*`, including Neumann endpoints,

    u_x(t,x*) = 0,
    u_xx(t,x*) >= 0.

The PDE is

    u_t = u_xx - d_x (u^m chi(v) v_x) + u(a - b u^alpha).

For `chi(v)=chi0/(1+v)^beta`, `chi0 > 0`, `beta >= 1`, expand

    -d_x (u^m chi(v) v_x)
      = -m u^(m-1) chi(v) u_x v_x
        -u^m chi'(v) |v_x|^2
        -u^m chi(v) v_xx.

At a spatial minimum, the first term vanishes.  Since `chi'(v) <= 0`, the second term is nonnegative.  The elliptic equation gives

    v_xx = mu v - nu u^gamma.

Hence

    -u^m chi(v) v_xx
      >= -mu u^m chi(v) v.

For beta >= 1,

    v / (1 + v)^beta <= Theta_beta(beta - 1).

Thus, with `u(t,x*) = z(t)`, the chemotaxis term is bounded below by

    -chi0 * mu * Theta_beta(beta - 1) * z(t)^m.

Therefore

    lowerRightDini z t >= a*z(t) - b*z(t)^(1+alpha) - Cchi*z(t)^m,

where

    Cchi = chi0 * mu * Theta_beta(beta - 1).

For constant sensitivity, use instead

    Cchi = chi0 * mu * Vmax <= chi0 * nu * M^gamma

if `0 <= u <= M`.  For `chi(v)=chi0/v`, use formally `Cchi = chi0 * mu`, but carry the separate assumption `v > 0`.

## 8. Scalar first-crossing consequence

For the explicit `m = 1` persistence branch, set

    A = a - Cchi.

Assume `A > 0`, `b > 0`, `alpha > 0`, `z(t) > 0`, and

    lowerRightDini z t >= A*z(t) - b*z(t)^(1+alpha).

The scalar theorem should be:

    theorem eventually_lower_of_lowerRightDini_logistic
      (hz_cont : ContinuousOn z (Ici T0))
      (hz_pos : forall t, T0 <= t -> 0 < z t)
      (hDini : forall t, T0 <= t ->
        A * z t - b * z t^(1+alpha) <= lowerRightDini z t)
      (hA : 0 < A) (hb : 0 < b) (ha : 0 < alpha) :
      forall theta, 0 < theta -> theta < (A / b)^(1 / alpha) ->
        eventually_atTop (fun t => theta <= z t)

Proof route:

1. choose a logistic subsolution `y` with small positive initial value below `z(T)`;
2. use Dini comparison to prove `y(t) <= z(t)` for all later times;
3. solve or estimate the logistic ODE to show `y(t)` eventually exceeds any `theta < (A/b)^(1/alpha)`;
4. conclude the same eventual lower bound for `z`.

Equivalently,

    Filter.liminf z atTop >= (A / b)^(1 / alpha).

## 9. Recommended file split

1. `CompactMinDini.lean`
   - `lowerRightDini`
   - `CompactMinFamily`
   - `UniformRightDerivLowerOnCompact`
   - `UniformTimeContinuityOnCompact`
   - `argmin_ft_lower_near_min`
   - `lowerRightDini_min_ge_of_argmin_ft_lower`

2. `UniformRightDeriv.lean`
   - discharges `UniformRightDerivLowerOnCompact` from a C1-in-time package.

3. `ChemotaxisMinEstimate.lean`
   - minimum-point facts on `[0,1]` with Neumann endpoints.
   - chemotaxis lower bound and the constant `Cchi`.

4. `ScalarDiniPersistence.lean`
   - scalar logistic Dini comparison and the eventual lower bound.

This decomposition is the least fragile Lean route: compact-min/Danskin, calculus, PDE minimum algebra, and scalar persistence are independent modules.
