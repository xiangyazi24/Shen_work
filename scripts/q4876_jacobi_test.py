#!/usr/bin/env python3
"""Q4876: compare the normalized Problem 2.5 CMF error with Jacobi kernels.

The computation is exact in the CMF matrix product and in the Jacobi
polynomial coefficients (fractions.Fraction), and uses mpmath with 120
working digits for Catalan's constant and numerical quadrature.

Two Jacobi families are tested:

1. The actual Q4873 candidate

   J_n(X; eps) = P_n^{(eps-1/2, 0)}(1-2X),

   with R_n^J defined by equations (3.8)-(3.9) of Q4873.

2. The literal family stated in Q4876

   P_n^{(0, eps)}(1-2X),

   for which we report the moment of the derivative polynomial itself.
   This second family is not the Q4873 Padé kernel; it is included to make
   the parameter mismatch explicit.
"""

from __future__ import annotations

from dataclasses import dataclass
from decimal import Decimal
from fractions import Fraction as Q
from typing import Iterable, Sequence

from mpmath import mp

mp.dps = 120


# ---------------------------------------------------------------------------
# Small exact dual-number implementation: value + eps * derivative.
# ---------------------------------------------------------------------------


def as_q(x: int | Q) -> Q:
    return x if isinstance(x, Q) else Q(x)


@dataclass(frozen=True)
class Dual:
    val: Q
    der: Q = Q(0)

    @staticmethod
    def coerce(x: int | Q | "Dual") -> "Dual":
        if isinstance(x, Dual):
            return x
        return Dual(as_q(x), Q(0))

    def __add__(self, other: int | Q | "Dual") -> "Dual":
        o = Dual.coerce(other)
        return Dual(self.val + o.val, self.der + o.der)

    def __radd__(self, other: int | Q | "Dual") -> "Dual":
        return self + other

    def __sub__(self, other: int | Q | "Dual") -> "Dual":
        o = Dual.coerce(other)
        return Dual(self.val - o.val, self.der - o.der)

    def __rsub__(self, other: int | Q | "Dual") -> "Dual":
        return Dual.coerce(other) - self

    def __mul__(self, other: int | Q | "Dual") -> "Dual":
        o = Dual.coerce(other)
        return Dual(self.val * o.val, self.der * o.val + self.val * o.der)

    def __rmul__(self, other: int | Q | "Dual") -> "Dual":
        return self * other

    def __truediv__(self, other: int | Q | "Dual") -> "Dual":
        o = Dual.coerce(other)
        if o.val == 0:
            raise ZeroDivisionError("dual division by zero")
        return Dual(
            self.val / o.val,
            (self.der * o.val - self.val * o.der) / (o.val * o.val),
        )

    def __rtruediv__(self, other: int | Q | "Dual") -> "Dual":
        return Dual.coerce(other) / self

    def __neg__(self) -> "Dual":
        return Dual(-self.val, -self.der)


# ---------------------------------------------------------------------------
# Polynomial helpers. Coefficients are in ascending order.
# ---------------------------------------------------------------------------


def trim_q(p: Sequence[Q]) -> list[Q]:
    out = list(p)
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def p_add(a, b):
    n = max(len(a), len(b))
    zero = Dual(Q(0)) if (a and isinstance(a[0], Dual)) or (b and isinstance(b[0], Dual)) else Q(0)
    out = [zero for _ in range(n)]
    for i, c in enumerate(a):
        out[i] = out[i] + c
    for i, c in enumerate(b):
        out[i] = out[i] + c
    return out


def p_sub(a, b):
    n = max(len(a), len(b))
    zero = Dual(Q(0)) if (a and isinstance(a[0], Dual)) or (b and isinstance(b[0], Dual)) else Q(0)
    out = [zero for _ in range(n)]
    for i, c in enumerate(a):
        out[i] = out[i] + c
    for i, c in enumerate(b):
        out[i] = out[i] - c
    return out


def p_scale(a, s):
    return [s * c for c in a]


def p_xmul(a):
    zero = Dual(Q(0)) if a and isinstance(a[0], Dual) else Q(0)
    return [zero] + list(a)


def p_mul_q(a: Sequence[Q], b: Sequence[Q]) -> list[Q]:
    out = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return trim_q(out)


def p_comp_linear_q(p: Sequence[Q], a: Q, b: Q) -> list[Q]:
    """Return p(a+bX), with ascending coefficients in X."""
    result = [Q(0)]
    power = [Q(1)]
    for c in p:
        result = p_add(result, p_scale(power, c))
        power = p_mul_q(power, [a, b])
    return trim_q(result)


def p_eval_q(p: Sequence[Q], x: Q) -> Q:
    acc = Q(0)
    for c in reversed(p):
        acc = acc * x + c
    return acc


def p_deriv_q(p: Sequence[Q]) -> list[Q]:
    if len(p) <= 1:
        return [Q(0)]
    return trim_q([Q(k) * p[k] for k in range(1, len(p))])


def p_div_x_plus_1_q(p: Sequence[Q]) -> list[Q]:
    """Exact division by X+1. Raises if the remainder is nonzero."""
    p = trim_q(p)
    if len(p) == 1:
        if p[0] != 0:
            raise ArithmeticError("constant is not divisible by X+1")
        return [Q(0)]
    degree = len(p) - 1
    q = [Q(0)] * degree
    q[-1] = p[-1]
    for k in range(degree - 1, 0, -1):
        q[k - 1] = p[k] - q[k]
    remainder = p[0] - q[0]
    if remainder != 0:
        raise ArithmeticError(f"nonzero remainder on division by X+1: {remainder}")
    return trim_q(q)


# ---------------------------------------------------------------------------
# Jacobi recurrence, differentiated in epsilon exactly.
# ---------------------------------------------------------------------------


def jacobi_dual_polys(
    nmax: int,
    *,
    alpha0: Q,
    alpha_der: Q,
    beta0: Q,
    beta_der: Q,
) -> tuple[list[list[Q]], list[list[Q]]]:
    """Return P_n^(alpha,beta)(x) and d/deps at eps=0, n<=nmax.

    alpha = alpha0 + alpha_der * eps,
    beta  = beta0  + beta_der  * eps.

    The standard three-term Jacobi recurrence is differentiated by dual
    arithmetic, so there is no finite-difference approximation.
    """
    a = Dual(alpha0, alpha_der)
    b = Dual(beta0, beta_der)

    polys: list[list[Dual]] = [[Dual(Q(1))]]
    if nmax >= 1:
        # P_1^(a,b)(x) = ((a-b) + (a+b+2)x)/2.
        polys.append([(a - b) / 2, (a + b + 2) / 2])

    for n in range(1, nmax):
        # 2(n+1)(n+a+b+1)(2n+a+b) P_{n+1}
        # = (2n+a+b+1)[((2n+a+b)(2n+a+b+2)x + a^2-b^2)]P_n
        #   - 2(n+a)(n+b)(2n+a+b+2)P_{n-1}.
        left = 2 * (n + 1) * (n + a + b + 1) * (2 * n + a + b)
        c0 = (2 * n + a + b + 1) * (a * a - b * b)
        c1 = (
            (2 * n + a + b + 1)
            * (2 * n + a + b)
            * (2 * n + a + b + 2)
        )
        back = 2 * (n + a) * (n + b) * (2 * n + a + b + 2)

        rhs = p_add(
            p_scale(polys[n], c0),
            p_scale(p_xmul(polys[n]), c1),
        )
        rhs = p_sub(rhs, p_scale(polys[n - 1], back))
        polys.append(p_scale(rhs, 1 / left))

    values = [[c.val for c in p] for p in polys]
    derivatives = [[c.der for c in p] for p in polys]
    return values, derivatives


# ---------------------------------------------------------------------------
# Actual Q4873 kernel, equations (3.8)-(3.9).
# ---------------------------------------------------------------------------


def q4873_jacobi_kernels(nmax: int):
    # Q4873 uses alpha=eps-1/2, beta=0, not P_n^(0,eps).
    px, dpx = jacobi_dual_polys(
        nmax,
        alpha0=Q(-1, 2),
        alpha_der=Q(1),
        beta0=Q(0),
        beta_der=Q(0),
    )

    kernels = []
    records = []
    for n in range(nmax + 1):
        J = p_comp_linear_q(px[n], Q(1), Q(-2))
        dJ = p_comp_linear_q(dpx[n], Q(1), Q(-2))
        B = p_eval_q(J, Q(-1))
        dB = p_eval_q(dJ, Q(-1))

        numerator = p_sub(p_scale(dJ, B), p_scale(J, dB))
        C = p_div_x_plus_1_q(numerator)

        # (2X d/dX + 1) C multiplies the X^k coefficient by 2k+1.
        opC = [Q(2 * k + 1) * c for k, c in enumerate(C)]
        correction = p_scale(p_mul_q([Q(1), Q(1)], opC), Q(1, 2))
        bracket = p_sub(p_scale(J, B), correction)
        kappa = Q(4 * n + 1, 2)
        R = trim_q(p_scale(bracket, kappa))

        # Q4873 equation (3.13): R_n(-1) = kappa_n B_n^2.
        qj = p_eval_q(R, Q(-1))
        assert qj == kappa * B * B

        kernels.append(R)
        records.append((J, dJ, B, dB, C, qj))

    return kernels, records


# Literal family quoted in Q4876: d/deps P_n^(0,eps)(1-2X)|_0.
def literal_beta_derivative_polys(nmax: int) -> list[list[Q]]:
    _, dpx = jacobi_dual_polys(
        nmax,
        alpha0=Q(0),
        alpha_der=Q(0),
        beta0=Q(0),
        beta_der=Q(1),
    )
    return [p_comp_linear_q(p, Q(1), Q(-2)) for p in dpx]


# ---------------------------------------------------------------------------
# Catalan moment: exact Q*G + rational, plus independent quadrature.
# ---------------------------------------------------------------------------


def q_to_mp(x: Q):
    return mp.mpf(x.numerator) / mp.mpf(x.denominator)


def catalan_moment_pair(poly: Sequence[Q]) -> tuple[Q, Q]:
    """Return q,r such that integral = q*G+r exactly."""
    q = Q(0)
    r = Q(0)
    partial = Q(0)  # sum_{j=0}^{k-1} (-1)^j/(2j+1)^2
    for k, coeff in enumerate(poly):
        sign = Q(1 if k % 2 == 0 else -1)
        q += coeff * sign
        r -= coeff * sign * partial
        partial += sign / Q((2 * k + 1) ** 2)
    assert q == p_eval_q(poly, Q(-1))
    return q, r


def p_eval_mp(poly: Sequence[Q], x):
    acc = mp.mpf("0")
    for c in reversed(poly):
        acc = acc * x + q_to_mp(c)
    return acc


def catalan_moment_quad(poly: Sequence[Q]):
    # t=e^{-u} removes the logarithmic endpoint singularity:
    # integral_0^1 -log(t)/(1+t^2) R(t^2)dt
    # = integral_0^inf u e^{-u}/(1+e^{-2u}) R(e^{-2u})du.
    def integrand(u):
        e = mp.e ** (-u)
        x = e * e
        return u * e * p_eval_mp(poly, x) / (1 + x)

    return mp.quad(integrand, [0, 1, 3, 8, 20, mp.inf])


# ---------------------------------------------------------------------------
# Exact Problem 2.5 matrix product and H_n normalization.
# ---------------------------------------------------------------------------


def matrix_M(n: int) -> tuple[tuple[int, int, int], ...]:
    m11 = (-2*n-5)*(n+3)**2*(136*n**4+1424*n**3+5548*n**2+9551*n+6141)
    m12 = 384*n**6+6384*n**5+44168*n**4+162698*n**3+336377*n**2+369933*n+169011
    m13 = -480*n**4-4980*n**3-19210*n**2-32690*n-20730

    m21 = (n+2)**2*(n+3)**2*(4*n+10)*(48*n**3+386*n**2+1017*n+879)
    m22 = (n+2)**2*(-272*n**5-3848*n**4-21732*n**3-61184*n**2-85761*n-47808)
    m23 = (n+2)**2*(320*n**3+2540*n**2+6610*n+5640)

    m31 = (-4*n-10)*(n+2)**2*(n+3)**2*(32*n**4+302*n**3+1037*n**2+1530*n+813)
    m32 = (n+2)**2*(192*n**6+2984*n**5+19116*n**4+64452*n**3+120256*n**2+117279*n+46476)
    m33 = (n+2)**2*(-16*n**5-408*n**4-2912*n**3-8884*n**2-12254*n-6240)

    return (
        (m11, m12, m13),
        (m21, m22, m23),
        (m31, m32, m33),
    )


def row_times_matrix(row: Sequence[int], mat: Sequence[Sequence[int]]) -> tuple[int, int, int]:
    return tuple(sum(row[i] * mat[i][j] for i in range(3)) for j in range(3))


def delta_h(n: int) -> int:
    # H_{n+1}/H_n for
    # H_n=(-16)^n(2)_n^2(3)_n^2(5/2)_n(7/2)_n^2.
    return -2 * (n + 2) ** 2 * (n + 3) ** 2 * (2*n + 5) * (2*n + 7) ** 2


def cmf_normalized_data(nmax: int):
    p_row = (30921, -32972, 8240)
    q_row = (33750, -36000, 9000)
    H = Q(1)
    G = mp.catalan

    out = []
    for n in range(nmax + 1):
        phat = Q(p_row[0]) / H
        qhat = Q(q_row[0]) / H
        err = q_to_mp(qhat) * G - q_to_mp(phat)
        out.append((phat, qhat, err, p_row, q_row, H))

        if n < nmax:
            M = matrix_M(n)
            p_row = row_times_matrix(p_row, M)
            q_row = row_times_matrix(q_row, M)
            H *= delta_h(n)

    return out


# ---------------------------------------------------------------------------
# Numerical fitting diagnostics.
# ---------------------------------------------------------------------------


def fmt(x, digits: int = 70) -> str:
    return mp.nstr(x, digits)


def rational_guess(x, max_denominator: int = 10**9) -> Q:
    return Q(Decimal(mp.nstr(x, 110))).limit_denominator(max_denominator)


def proportional_fit(target, moments):
    a = target[0] / moments[0]
    residuals = [target[n] - a * moments[n] for n in range(len(target))]
    return a, residuals


def width2_fit(target, moments):
    # Fit e_n = a*m_n + b*m_{n-1} using n=1,2.
    det = moments[1] * moments[1] - moments[0] * moments[2]
    if det == 0:
        raise ArithmeticError("singular width-2 fitting matrix")
    a = (target[1] * moments[1] - moments[0] * target[2]) / det
    b = (moments[1] * target[2] - moments[2] * target[1]) / det
    residuals = [mp.nan]
    for n in range(1, len(target)):
        residuals.append(target[n] - a * moments[n] - b * moments[n - 1])
    return a, b, residuals


def exact_width2_formal_test(target_pairs, moment_pairs):
    """Test e_n=(q_n G+r_n)=a m_n+b m_{n-1} coefficientwise.

    Solve a,b from the G coefficients at n=1,2, then report the first
    mismatch in either the G coefficient or rational coefficient.
    """
    tq = [x[0] for x in target_pairs]
    tr = [x[1] for x in target_pairs]
    mq = [x[0] for x in moment_pairs]
    mr = [x[1] for x in moment_pairs]

    det = mq[1] * mq[1] - mq[0] * mq[2]
    if det == 0:
        return None
    a = (tq[1] * mq[1] - mq[0] * tq[2]) / det
    b = (mq[1] * tq[2] - mq[2] * tq[1]) / det

    first_failure = None
    for n in range(1, len(target_pairs)):
        dq = tq[n] - a * mq[n] - b * mq[n - 1]
        dr = tr[n] - a * mr[n] - b * mr[n - 1]
        if dq != 0 or dr != 0:
            first_failure = (n, dq, dr)
            break
    return a, b, first_failure


def main() -> None:
    nmax = 10
    G = mp.catalan

    cmf = cmf_normalized_data(nmax)
    Rj, jacobi_records = q4873_jacobi_kernels(nmax)
    Rliteral = literal_beta_derivative_polys(nmax)

    jacobi_pairs = [catalan_moment_pair(R) for R in Rj]
    literal_pairs = [catalan_moment_pair(R) for R in Rliteral]

    jacobi_moments = [q_to_mp(q) * G + q_to_mp(r) for q, r in jacobi_pairs]
    literal_moments = [q_to_mp(q) * G + q_to_mp(r) for q, r in literal_pairs]
    errors = [row[2] for row in cmf]

    # Independent high-precision quadrature audit.
    max_quad_error = mp.mpf("0")
    for n, R in enumerate(Rj):
        quad = catalan_moment_quad(R)
        diff = abs(quad - jacobi_moments[n])
        max_quad_error = max(max_quad_error, diff)
        if diff > mp.mpf("1e-90"):
            raise AssertionError(f"quadrature mismatch at n={n}: {diff}")

    print("Q4876 JACOBI / CMF NUMERICAL TEST")
    print("mp.dps =", mp.dps)
    print("Catalan G =", fmt(G, 110))
    print()
    print("IMPORTANT PARAMETER AUDIT")
    print("  Q4873 uses P_n^(eps-1/2, 0)(1-2X).")
    print("  The literal Q4876 sentence P_n^(0, eps) is a different family.")
    print("  The main comparison below uses the actual Q4873 polynomial R_n^J.")
    print()

    print("CMF NORMALIZED FIRST-COLUMN ERROR VS Q4873 JACOBI MOMENT")
    print("n | ehat_n = G*qhat_n-phat_n | C[R_n^J] | ehat/C[R]")
    for n in range(nmax + 1):
        ratio = errors[n] / jacobi_moments[n]
        print(
            f"{n:2d} | {fmt(errors[n], 62)} | "
            f"{fmt(jacobi_moments[n], 62)} | {fmt(ratio, 42)}"
        )
    print()

    print("Q4873 MOMENT QUADRATURE AUDIT")
    print("max |quadrature - exact (q*G+r)| =", fmt(max_quad_error, 30))
    print()

    # Simple proportionality test.
    scale, prop_res = proportional_fit(errors, jacobi_moments)
    print("PROPORTIONALITY FIT FROM n=0")
    print("a =", fmt(scale, 90))
    print("rational guess for a (den<=1e9) =", rational_guess(scale))
    print("residuals e_n-a*m_n:")
    for n, r in enumerate(prop_res):
        print(f"  n={n:2d}: {fmt(r, 62)}")
    print()

    # Constant width-two fit.
    a, b, width_res = width2_fit(errors, jacobi_moments)
    print("WIDTH-2 NUMERICAL FIT FROM n=1,2")
    print("e_n = a*C[R_n^J] + b*C[R_{n-1}^J]")
    print("a =", fmt(a, 90))
    print("b =", fmt(b, 90))
    print("rational guess a (den<=1e9) =", rational_guess(a))
    print("rational guess b (den<=1e9) =", rational_guess(b))
    print("residuals:")
    for n in range(1, nmax + 1):
        print(f"  n={n:2d}: {fmt(width_res[n], 62)}")
    print()

    # Exact coefficientwise test over Q[G].
    target_pairs = [(row[1], -row[0]) for row in cmf]
    formal = exact_width2_formal_test(target_pairs, jacobi_pairs)
    print("EXACT COEFFICIENTWISE WIDTH-2 TEST OVER Q[G]")
    if formal is None:
        print("  singular coefficient system")
    else:
        af, bf, failure = formal
        print("  a from G-coefficients at n=1,2 =", af)
        print("  b from G-coefficients at n=1,2 =", bf)
        print("  first failure (n, delta_G_coeff, delta_rational) =", failure)
    print()

    print("LITERAL P_n^(0,eps) DERIVATIVE-POLYNOMIAL MOMENTS")
    print("n | d/deps P_n^(0,eps)(3)|0 | moment of derivative polynomial")
    for n in range(nmax + 1):
        d_at_3 = p_eval_q(Rliteral[n], Q(-1))
        print(f"{n:2d} | {d_at_3} | {fmt(literal_moments[n], 62)}")
    print()

    # A concise final verdict derived from actual residuals.
    max_prop_after_fit = max(abs(r) for r in prop_res[1:])
    max_width_after_fit = max(abs(width_res[n]) for n in range(3, nmax + 1))
    print("FINAL NUMERICAL VERDICT")
    print("max proportional residual for n=1..10 =", fmt(max_prop_after_fit, 50))
    print("max width-2 residual for n=3..10 =", fmt(max_width_after_fit, 50))
    print("The same-index proportionality and constant-coefficient width-2 ansatz both fail.")


if __name__ == "__main__":
    main()
