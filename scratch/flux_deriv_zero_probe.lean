import ShenWork.Paper2.IntervalTruncatedPositiveTimeBootstrap

/-! Scratch probe for the flux deriv = 0 theorem -/

-- The approach:
-- Case 1: lift(w)(y) < 0 → flux = 0 in a neighborhood → HasDerivAt flux 0 y → deriv = 0
-- Case 2: lift(w)(y) = 0, y ∉ [0,1] → flux = 0 in a neighborhood → deriv = 0
-- Case 3: lift(w)(y) = 0, y ∈ [0,1] → flux is not differentiable OR HasDerivAt with deriv 0

-- For cases 1 and 2, the key is: flux =ᶠ[𝓝 y] 0
-- Then: HasDerivAt flux 0 y (since HasDerivAt (const 0) 0 y and congr)
-- Then: deriv flux y = 0

-- For case 3: use deriv_zero_of_not_differentiableAt OR direct HasDerivAt

-- Let's check what we need:
-- (a) Continuity of intervalDomainLift w (when w is Continuous)
-- (b) That lift(w) < 0 implies lift(w) < 0 in a nhd
-- (c) That outside [0,1], lift(w) = 0

-- Key fact: if y ∈ interior ([0,1]ᶜ), then lift(w) = 0 near y.
-- If y ∈ interior [0,1] = (0,1) and lift(w)(y) < 0, then lift(w) < 0 near y.

-- For case 3 with y ∈ [0,1]:
-- We know flux(y) = 0 (from truncatedChemFluxLifted_eq_zero_of_lift_nonpos).
-- Need deriv flux y = 0.
-- Approach: flux is not differentiable. Use deriv_zero_of_not_differentiableAt.

-- Actually, simplest unified approach:
-- For ANY y with lift(w)(y) ≤ 0:
-- flux(y) = 0. And we want deriv flux y = 0.
-- If flux is not DifferentiableAt at y, then deriv = 0 by convention. Done.
-- If flux IS DifferentiableAt, then HasDerivAt flux (deriv flux y) y.
-- We show deriv flux y = 0 by squeeze.

-- The squeeze: For any h with lift(w)(y+h) ≤ 0, flux(y+h) = 0.
-- For any h with lift(w)(y+h) > 0, flux(y+h) = positivePart(lift(w)(y+h)) * g(y+h) / denom(y+h).
-- In either case: |flux(y+h)| ≤ |lift(w)(y+h) - lift(w)(y)| * C (using Lipschitz of positivePart)
--   = |lift(w)(y+h)| * C (since lift(w)(y) ≤ 0, |lift(w)(y+h) - lift(w)(y)| ≤ |lift(w)(y+h)| + |lift(w)(y)|
--   Hmm, this doesn't quite work because lift(w)(y) might be < 0.

-- Let me reconsider. For lift(w)(y) < 0:
-- positivePart(lift(w)(y)) = 0 and positivePart(lift(w)(y+h)) ≤ |lift(w)(y+h)| ≤ |lift(w)(y+h) - lift(w)(y)| + |lift(w)(y)|
-- Not tight enough.

-- Better: positivePart is Lipschitz with constant 1:
-- |positivePart(a) - positivePart(b)| ≤ |a - b|
-- So |positivePart(lift(w)(y+h)) - positivePart(lift(w)(y))| ≤ |lift(w)(y+h) - lift(w)(y)|
-- positivePart(lift(w)(y)) = 0 (since lift(w)(y) ≤ 0)
-- So |positivePart(lift(w)(y+h))| ≤ |lift(w)(y+h) - lift(w)(y)|

-- And |flux(y+h)| = |positivePart(lift(w)(y+h))| * |g(y+h)| / |denom(y+h)|
--                 ≤ |lift(w)(y+h) - lift(w)(y)| * |g(y+h)| / |denom(y+h)|

-- If g is bounded by G and denom is bounded below by δ > 0:
-- |flux(y+h)| ≤ (G/δ) * |lift(w)(y+h) - lift(w)(y)|

-- For the derivative ratio: |flux(y+h)|/|h| ≤ (G/δ) * |lift(w)(y+h) - lift(w)(y)| / |h|

-- If lift(w) is differentiable at y: ≤ (G/δ) * (|lift(w)'(y)| + o(1))
-- If lift(w) is NOT differentiable at y: bounded by Lip constant * (G/δ)

-- In either case, the limit flux(y+h)/h as h → 0 is squeezed:
-- flux(y+h) = 0 whenever lift(w)(y+h) ≤ 0
-- flux(y+h)/h ≤ C * (lift(w)(y+h) - 0)/h on the positive side

-- Actually, the key observation for the non-differentiable case:
-- We just need deriv flux y = 0.
-- Either flux is not DifferentiableAt → deriv = 0 ✓
-- Or flux IS DifferentiableAt with some derivative d.
--   Then d = lim_{h→0} flux(y+h)/h.
--   But we know flux(y+h) ≥ 0 doesn't hold in general (flux can be negative).
--   Hmm, actually:
--   positivePart(·) ≥ 0, and denom > 0.
--   So sgn(flux) = sgn(positivePart * resolverGrad) = sgn(resolverGrad) when positivePart > 0.
--   flux can be negative.

-- OK here's the nuclear option for case 3:
-- Show that flux is not differentiable at y ∈ (0,1) with w(y) = 0 by showing
-- the right and left derivatives differ (if they exist).
-- This requires knowing that w changes sign at y, which we don't know.
-- If w ≡ 0 near y, then flux ≡ 0 near y and deriv = 0. This is fine.
-- If w doesn't change sign: w ≤ 0 near y → flux = 0 near y → deriv = 0.
-- If w > 0 on one side and ≤ 0 on the other (typical zero crossing):
--   flux ≠ 0 on one side, = 0 on the other → one-sided limits differ → not differentiable.

-- For y at boundary {0, 1}:
-- If y = 0: for h < 0, lift(w)(h) = 0 (outside [0,1]), so flux(h) = 0.
--   So left "derivative" = 0.
--   If right derivative exists and ≠ 0, then two-sided deriv doesn't exist → deriv = 0.
--   If right derivative = 0 (or doesn't exist), then again deriv = 0.
-- Similar for y = 1.

-- In ALL cases: either flux is not differentiable → deriv = 0,
-- or flux is differentiable with derivative 0.

-- Hmm, I realize the formal proof in Lean for "not differentiable implies deriv = 0"
-- is just `deriv_zero_of_not_differentiableAt`. And for "differentiable with derivative 0",
-- it's `HasDerivAt.deriv`.

-- The challenge is SHOWING which case we're in. We can't easily split on whether
-- flux is differentiable because that's classical and may not simplify.

-- ACTUALLY: The simplest correct proof:
-- By `classical`:
-- `deriv flux y = if DifferentiableAt ℝ flux y then ... else 0`
-- (by `deriv_zero_of_not_differentiableAt`)
-- So it suffices to show: IF DifferentiableAt, THEN the derivative is 0.
-- Suppose HasDerivAt flux d y. Then d = lim flux(y+h)/h.
-- Show d = 0.

-- This is the approach. Let me try to formalize it.

-- Actually, `deriv_eq_zero_of_forall_le_and_forall_ge` or something might exist...
-- No, the cleanest is:

-- 1. classical
-- 2. by_cases h : DifferentiableAt ℝ (truncatedChemFluxLifted p w) y
-- 3. Case ¬DifferentiableAt: exact deriv_zero_of_not_differentiableAt h
-- 4. Case DifferentiableAt:
--    have hda := h.hasDerivAt
--    -- Show the derivative is 0
--    -- This is the hard part. Need to show lim flux(y+h)/h = 0.
--    sorry

-- For step 4: if DifferentiableAt at y with lift(w)(y) ≤ 0:

-- Sub-case lift(w)(y) < 0: flux = 0 in a nhd → HasDerivAt flux 0 y → deriv = 0.
-- This is easy.

-- Sub-case lift(w)(y) = 0, y ∉ [0,1]: flux = 0 in a nhd → deriv = 0. Easy.

-- Sub-case lift(w)(y) = 0, y ∈ [0,1]:
-- If DifferentiableAt ℝ flux y, then HasDerivAt flux (deriv flux y) y.
-- We need deriv flux y = 0.

-- For y = 0: left: flux(0+h) = 0 for h < 0 (outside interval).
--   So HasDerivAt gives: deriv = lim_{h→0} (flux(h) - 0)/h = 0 from the left.
--   But also from the right. Since the limit exists from both sides and equals the same value,
--   we just need flux(h)/h → 0 from the left (which is 0/h = 0).
--   And from the right: if DifferentiableAt, the right limit also exists and equals deriv.
--   So deriv = lim_{h→0-} flux(h)/h = 0.

-- For y = 1: right: flux(1+h) = 0 for h > 0. So deriv = lim_{h→0+} flux(1+h)/h = 0.

-- For y ∈ (0,1): If DifferentiableAt with w(y) = 0:
--   For h with w(y+h) ≤ 0: flux(y+h) = 0, so flux(y+h)/h = 0.
--   If w(y+h) > 0 on a full nhd of y... but w(y) = 0 and w is continuous.
--   w might be ≥ 0 near y (w(y) = 0 and w ≥ 0 in a nhd): then positivePart(w) = w near y,
--   and flux is differentiable IF w is differentiable. flux'(y) = w'(y) * g(y) * q(y) + 0 (product rule).
--   Hmm, deriv might not be 0 in this case!

-- WAIT. w(y) = 0 and w ≥ 0 near y. Then positivePart(w(y+h)) = w(y+h) near y.
-- So flux(y+h) = w(y+h) * g(y+h) * q(y+h). And flux(y) = 0.
-- flux(y+h)/h = w(y+h)/h * g(y+h) * q(y+h) → w'(y) * g(y) * q(y) IF w is differentiable at y.
-- This could be NONZERO!

-- So the theorem AS STATED might be WRONG in this case!

-- Wait, let me re-read the theorem:
-- hy_nonpos : intervalDomainLift w y ≤ 0
-- The hypothesis is lift(w)(y) ≤ 0, which is w(y) ≤ 0 for y ∈ [0,1].
-- If w(y) = 0 and w ≥ 0 near y, then indeed lift(w)(y) = 0 ≤ 0, and the theorem claims
-- deriv flux y = 0. But as shown above, deriv flux y = w'(y) · g(y) · q(y) which might not be 0.

-- IS THE THEOREM WRONG?!

-- Actually wait. In the case w(y) = 0 and w ≥ 0 near y:
-- positivePart(w(y')) = w(y') for y' near y (since w ≥ 0 near y)
-- So flux(y') = w(y') * g(y') / denom(y')
-- flux(y) = 0 * g(y) / denom(y) = 0
-- deriv flux y = w'(y) * g(y) / denom(y) + ... (product rule)
-- If w'(y) > 0, this is > 0. NONZERO.

-- So the theorem is FALSE in general!

-- Unless... there's an additional constraint that makes it true.
-- Let me re-check the hypotheses:
-- p : CM2Params
-- w : intervalDomainPoint → ℝ
-- M : ℝ, hM : 0 < M
-- hw_cont : Continuous w
-- hball : ∀ x, |w x| ≤ M
-- hsmall : ...
-- y : ℝ
-- hy_nonpos : intervalDomainLift w y ≤ 0

-- There's no constraint that prevents w(y) = 0 and w ≥ 0 near y with w'(y) > 0.

-- CONCLUSION: The theorem as stated is FALSE.

-- This is a design gap introduced by the Codex refactoring!
-- The original theorem was about R ≥ 0 and flux deriv = 0.
-- The Codex split it into two parts: R bound (proved) and flux deriv zero (sorry).
-- But the original theorem bundled them BECAUSE the proof needed R ≥ 0 for the flux argument.

-- Let me go back and look at what the original combined theorem was trying to prove:

end
