#!/usr/bin/env python3
from __future__ import annotations

from fractions import Fraction as F
from math import log10
from typing import Callable, List, Tuple

try:
    import sympy as sp
except ImportError:
    sp = None

N_OP = 30
N_MOP_STEP = 24


def trim(p: List[F]) -> List[F]:
    p = p[:]
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def padd(p: List[F], q: List[F]) -> List[F]:
    out = [F(0)] * max(len(p), len(q))
    for i, a in enumerate(p):
        out[i] += a
    for i, a in enumerate(q):
        out[i] += a
    return trim(out)


def psub(p: List[F], q: List[F]) -> List[F]:
    return padd(p, [-a for a in q])


def pscale(c: F, p: List[F]) -> List[F]:
    return trim([c * a for a in p])


def px(p: List[F]) -> List[F]:
    return [F(0)] + p


def peval(p: List[F], x: F) -> F:
    y = F(0)
    for a in reversed(p):
        y = y * x + a
    return y


def solve_linear(A: List[List[F]], b: List[F]) -> List[F]:
    n = len(A)
    if n == 0:
        return []
    M = [row[:] + [b[i]] for i, row in enumerate(A)]
    for col in range(n):
        pivot = next((r for r in range(col, n) if M[r][col] != 0), None)
        if pivot is None:
            raise ArithmeticError(f"singular matrix at column {col}")
        if pivot != col:
            M[col], M[pivot] = M[pivot], M[col]
        piv = M[col][col]
        # Normalize pivot row only from current column onward.
        for j in range(col, n + 1):
            M[col][j] /= piv
        for r in range(n):
            if r == col:
                continue
            c = M[r][col]
            if c == 0:
                continue
            for j in range(col, n + 1):
                M[r][j] -= c * M[col][j]
    return [M[i][n] for i in range(n)]


def monic_op(n: int, moment: Callable[[int], F]) -> List[F]:
    if n == 0:
        return [F(1)]
    A = [[moment(i + j) for j in range(n)] for i in range(n)]
    b = [-moment(i + n) for i in range(n)]
    return solve_linear(A, b) + [F(1)]


def inner(p: List[F], q: List[F], moment: Callable[[int], F]) -> F:
    return sum((a * b * moment(i + j)
                for i, a in enumerate(p)
                for j, b in enumerate(q)), F(0))


def moment_sigma(k: int) -> F:
    return F(1, (2 * k + 1) ** 2)


def moment_base(k: int) -> F:
    return F(1, 2 * k + 1)


def fmt_frac(x: F, max_digits: int = 32) -> str:
    s = str(x)
    if len(s) <= max_digits:
        return s
    return f"[{len(str(abs(x.numerator)))}-digit num]/[{len(str(x.denominator))}-digit den]"


def nfloat(x: F, digits: int = 16) -> str:
    return f"{float(x):.{digits}g}"


# Quadratic field Q(sqrt(2)) as pairs a+b*sqrt(2).
Quad = Tuple[F, F]


def qadd(x: Quad, y: Quad) -> Quad:
    return (x[0] + y[0], x[1] + y[1])


def qmul(x: Quad, y: Quad) -> Quad:
    return (x[0] * y[0] + 2 * x[1] * y[1],
            x[0] * y[1] + x[1] * y[0])


def qeval(p: List[F], x: Quad) -> Quad:
    y = (F(0), F(0))
    for a in reversed(p):
        y = qadd(qmul(y, x), (a, F(0)))
    return y


def qfloat(x: Quad) -> float:
    return float(x[0]) + float(x[1]) * (2.0 ** 0.5)


# CMF matrix and normalized row trajectory.
def cmf_M(n: int) -> List[List[F]]:
    n = F(n)
    m11 = (-2*n-5)*(n+3)**2*(136*n**4+1424*n**3+5548*n**2+9551*n+6141)
    m12 = 384*n**6+6384*n**5+44168*n**4+162698*n**3+336377*n**2+369933*n+169011
    m13 = -480*n**4-4980*n**3-19210*n**2-32690*n-20730
    m21 = (n+2)**2*(n+3)**2*(4*n+10)*(48*n**3+386*n**2+1017*n+879)
    m22 = (n+2)**2*(-272*n**5-3848*n**4-21732*n**3-61184*n**2-85761*n-47808)
    m23 = (n+2)**2*(320*n**3+2540*n**2+6610*n+5640)
    m31 = (-4*n-10)*(n+2)**2*(n+3)**2*(32*n**4+302*n**3+1037*n**2+1530*n+813)
    m32 = (n+2)**2*(192*n**6+2984*n**5+19116*n**4+64452*n**3+120256*n**2+117279*n+46476)
    m33 = (n+2)**2*(-16*n**5-408*n**4-2912*n**3-8884*n**2-12254*n-6240)
    return [[F(m11), F(m12), F(m13)],
            [F(m21), F(m22), F(m23)],
            [F(m31), F(m32), F(m33)]]


def delta_H(n: int) -> F:
    n = F(n)
    return -2*(n+2)**2*(n+3)**2*(2*n+5)*(2*n+7)**2


def row_mul(row: List[F], M: List[List[F]]) -> List[F]:
    return [sum((row[i] * M[i][j] for i in range(3)), F(0)) for j in range(3)]


def cmf_q_sequence(N: int) -> List[F]:
    row = [F(33750), F(-36000), F(9000)]
    out = []
    for n in range(N + 1):
        out.append(row[0])
        if n < N:
            d = delta_H(n)
            MH = [[x / d for x in r] for r in cmf_M(n)]
            row = row_mul(row, MH)
    return out


def typeII(n1: int, n2: int) -> List[F]:
    N = n1 + n2
    if N == 0:
        return [F(1)]
    A: List[List[F]] = []
    b: List[F] = []
    for j in range(n1):
        A.append([moment_base(j + k) for k in range(N)])
        b.append(-moment_base(j + N))
    for j in range(n2):
        A.append([moment_sigma(j + k) for k in range(N)])
        b.append(-moment_sigma(j + N))
    return solve_linear(A, b) + [F(1)]


def recurrence_step_line(P: List[List[F]], n: int) -> Tuple[F, F, F, List[F]]:
    # x P_n = P_{n+1} + b_n P_n + c_n P_{n-1} + d_n P_{n-2}
    R = psub(px(P[n]), P[n + 1])
    b = R[n] if len(R) > n else F(0)
    R = psub(R, pscale(b, P[n]))
    c = R[n - 1] if n >= 1 and len(R) > n - 1 else F(0)
    if n >= 1:
        R = psub(R, pscale(c, P[n - 1]))
    d = R[n - 2] if n >= 2 and len(R) > n - 2 else F(0)
    if n >= 2:
        R = psub(R, pscale(d, P[n - 2]))
    return b, c, d, trim(R)


def rational_fit(xs: List[int], ys: List[F], maxdeg: int = 6):
    # Search P(n)/Q(n), deg P<=d, deg Q<=e, Q monic in its highest term.
    if sp is None:
        return None
    X = sp.symbols('X')
    for d in range(maxdeg + 1):
        for e in range(maxdeg + 1):
            need = d + e + 1
            if len(xs) < need + 2:
                continue
            # unknown p_0..p_d, q_0..q_{e-1}; q_e=1
            rows = []
            rhs = []
            for xx, yy in zip(xs[:need], ys[:need]):
                y = sp.Rational(yy.numerator, yy.denominator)
                rows.append([sp.Integer(xx) ** k for k in range(d + 1)] +
                            [-y * sp.Integer(xx) ** k for k in range(e)])
                rhs.append(y * sp.Integer(xx) ** e)
            A = sp.Matrix(rows)
            B = sp.Matrix(rhs)
            try:
                sol = list(A.gauss_jordan_solve(B)[0])
            except Exception:
                continue
            Pexpr = sum(sol[k] * X**k for k in range(d + 1))
            Qexpr = sum(sol[d + 1 + k] * X**k for k in range(e)) + X**e
            ok = True
            for xx, yy in zip(xs, ys):
                val = sp.cancel(Pexpr.subs(X, xx) / Qexpr.subs(X, xx))
                if val != sp.Rational(yy.numerator, yy.denominator):
                    ok = False
                    break
            if ok:
                return sp.factor(Pexpr), sp.factor(Qexpr)
    return None


def main() -> None:
    print("=== sigma orthogonal polynomials ===", flush=True)
    ops = []
    norms = []
    vals_m1 = []
    vals_rho = []
    rho = (F(17), F(-12))
    for n in range(N_OP + 1):
        p = monic_op(n, moment_sigma)
        ops.append(p)
        norms.append(inner(p, p, moment_sigma))
        vals_m1.append(peval(p, F(-1)))
        vals_rho.append(qeval(p, rho))
        if n <= 6:
            print(f"Qsigma_{n}(x) coeffs low-to-high = {p}")
    print("\nmonic three-term recurrence coefficients:")
    for n in range(0, N_OP):
        alpha = inner(px(ops[n]), ops[n], moment_sigma) / norms[n]
        beta = F(0) if n == 0 else norms[n] / norms[n-1]
        if n <= 5 or n >= N_OP - 5:
            print(f"n={n:2d} alpha={nfloat(alpha,17)} beta={nfloat(beta,17)}")

    print("\nvalues and ratios at -1 and rho=17-12sqrt(2):")
    print("n  Q_n(-1) [numeric]  Q_{n+1}(-1)/Q_n(-1)  Q_n(rho) [numeric]")
    for n in range(N_OP + 1):
        rr = "-" if n == N_OP else nfloat(vals_m1[n+1] / vals_m1[n], 17)
        print(f"{n:2d} {nfloat(vals_m1[n],17):>22} {rr:>22} {qfloat(vals_rho[n]): .12e}")
    a = 3 + 2 * (2.0 ** 0.5)
    print("predicted ratio limit at -1 = -(3+2sqrt(2))/4 =", -(a/4))
    print("last ratio =", float(vals_m1[-1] / vals_m1[-2]))
    print("predicted nth-root magnitude inside support at rho = cap([0,1]) = 1/4")
    print("last |Q_n(rho)|^(1/n) =", abs(qfloat(vals_rho[-1])) ** (1/N_OP))

    print("\n=== CMF comparison ===")
    qcmf = cmf_q_sequence(N_OP)
    ratios = [qcmf[n] / vals_m1[n] for n in range(N_OP + 1)]
    print("n   Qcmf(first column) numeric   r_n=Qcmf/Qsigma(-1) numeric   r_{n+1}/r_n")
    for n in range(N_OP + 1):
        gr = "-" if n == N_OP else nfloat(ratios[n+1]/ratios[n], 17)
        if n <= 10 or n >= N_OP - 5:
            print(f"{n:2d} {nfloat(qcmf[n],17):>24} {nfloat(ratios[n],17):>27} {gr:>22}")
    print("Every r_n is rational exactly, because both numerator and denominator are rational.")
    print("predicted consecutive-ratio limit = -4(3+2sqrt(2)) =", -4*a)
    print("last consecutive ratio =", float(ratios[-1]/ratios[-2]))
    fit = rational_fit(list(range(N_OP)), [ratios[n+1]/ratios[n] for n in range(N_OP)], 7)
    print("low-degree rational-function fit for r_{n+1}/r_n (degrees <=7):", fit)

    print("\n=== confluent Jacobi-Pineiro / type-II MOP candidate ===")
    Pstep: List[List[F]] = []
    for N in range(N_MOP_STEP + 2):
        n1 = (N + 1)//2
        n2 = N//2
        Pstep.append(typeII(n1, n2))
    print("first step-line polynomials, coeffs low-to-high:")
    for N in range(0, 7):
        print(f"P_{N} multi-index=({(N+1)//2},{N//2}) coeffs={Pstep[N]}")
    print("\n4-term recurrence coefficients (last values split by parity):")
    rec = []
    for N in range(2, N_MOP_STEP + 1):
        b, c, d, rem = recurrence_step_line(Pstep, N)
        if any(rem):
            print("WARNING nonzero remainder at", N, rem)
        rec.append((N,b,c,d))
        if N >= N_MOP_STEP - 7:
            print(f"N={N:2d} parity={N%2} b={nfloat(b,16)} c={nfloat(c,16)} d={nfloat(d,16)}")
    vstep = [peval(p,F(-1)) for p in Pstep]
    print("\nstep-line evaluations at -1 and ratios:")
    for N in range(max(0,N_MOP_STEP-8), N_MOP_STEP+1):
        print(N, nfloat(vstep[N],17), nfloat(vstep[N+1]/vstep[N],17))

    print("\ndiagonal P_(n,n), scaled by 16^n, compared with CMF:")
    diag = []
    maxdiag = N_MOP_STEP//2
    for n in range(maxdiag + 1):
        val = peval(Pstep[2*n],F(-1)) * (F(16) ** n)
        diag.append(val)
        rat = qcmf[n] / val
        nxt = "-" if n == maxdiag else nfloat((qcmf[n+1]/diag[n+1]) / rat,17)
        print(f"n={n:2d} scaled_diag={nfloat(val,17):>23} cmf/diag={nfloat(rat,17):>23} next-ratio={nxt}")
    print("last scaled diagonal ratio S_{n+1}/S_n =", float(diag[-1]/diag[-2]))
    print("CMF dominant root Lambda =", a*a)
    print("low-degree fit for (CMF/diag) successive ratio:",
          rational_fit(list(range(maxdiag)),
                       [(qcmf[n+1]/diag[n+1])/(qcmf[n]/diag[n]) for n in range(maxdiag)],
                       4))

    print("\n=== compact exact data for report ===")
    for n in [0,1,2,3,4,5,10,15,20,25,30]:
        print("REPORT", n,
              "Qm1=", fmt_frac(vals_m1[n], 80),
              "ratio=", ("-" if n == 0 else nfloat(vals_m1[n]/vals_m1[n-1],18)),
              "Qrho=", f"{qfloat(vals_rho[n]):.15e}",
              "Qcmf=", fmt_frac(qcmf[n],80),
              "cmf/op=", fmt_frac(ratios[n],80))


if __name__ == "__main__":
    main()
