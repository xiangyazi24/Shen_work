#!/usr/bin/env python3
from __future__ import annotations

from math import comb, gcd, log
from fractions import Fraction
from functools import reduce
import json

from sympy import Matrix, Integer
from sympy.matrices.normalforms import smith_normal_form
from sympy.polys.domains import ZZ

TARGETS = [9, 12, 15, 18, 21, 24, 27, 30, 33, 36, 39, 42, 45]


def igcd(values):
    g = 0
    for x in values:
        g = gcd(g, abs(int(x)))
    return g


def logint(x: int) -> float:
    x = abs(int(x))
    if x == 0:
        return float('-inf')
    s = str(x)
    take = min(16, len(s))
    return (len(s) - take) * log(10.0) + log(int(s[:take]))


def falling(a: int, k: int) -> int:
    z = 1
    for i in range(k):
        z *= a - i
    return z


def franel_list(N: int) -> list[int]:
    return [sum(comb(m, r) ** 3 for r in range(m + 1)) for m in range(N + 1)]


def L(n: int, k: int) -> int:
    return comb(n, k) * comb(n + k, k)


def h_row(n: int, J: int, F: list[int]) -> list[int]:
    # h_J(c) = K_c(n,J) g_J(c)
    K = [L(n, J + a) * comb(J + a, J) for a in range(n - J + 1)]
    g = [((-1) ** b) * comb(J, b) * F[J - b] for b in range(J + 1)]
    out = [0] * (n + 1)
    for a, ka in enumerate(K):
        for b, gb in enumerate(g):
            out[a + b] += ka * gb
    return out


def t_rows_and_contents(hrows: list[list[int]]) -> tuple[list[list[int]], list[int]]:
    cur = [0] * len(hrows[0])
    rows, gammas = [], []
    for h in hrows:
        cur = [a + b for a, b in zip(cur, h)]
        rows.append(cur[:])
        gammas.append(igcd(cur))
    return rows, gammas


def selected_det(rows: list[list[int]], cols: list[int]) -> int:
    return int(Matrix([[row[c] for c in cols] for row in rows]).det())


def taylor_matrix(rows: list[list[int]], center: int, H: int) -> Matrix:
    # columns are normalized Taylor coefficients [z^r] f(center+z)
    vals = []
    for row in rows:
        rr = []
        for r in range(H + 1):
            rr.append(sum(row[d] * comb(d, r) * (center ** (d - r)) for d in range(r, len(row))))
        vals.append(rr)
    return Matrix(vals)


def eval_matrix(rows: list[list[int]], points: list[int]) -> Matrix:
    vals = []
    for row in rows:
        rr = []
        for x in points:
            acc = 0
            for a in reversed(row):
                acc = acc * x + a
            rr.append(acc)
        vals.append(rr)
    return Matrix(vals)


def top_formula(n: int, H: int, F: list[int]) -> Fraction:
    z = Fraction(comb(2*n, n) ** (H + 1), 1)
    for J in range(H + 1):
        z *= comb(n, J)
    for r in range(H + 1):
        E = Fraction(0, 1)
        for w in range(r + 1):
            u = r - w
            E += Fraction(comb(r, w) * F[w] * falling(n, u), falling(2*n, u))
        z *= E
    return z


def snf_last_divisor(rows: list[list[int]]) -> tuple[int, list[int]]:
    S = smith_normal_form(Matrix(rows), domain=ZZ)
    d = []
    for i in range(min(S.rows, S.cols)):
        if S[i, i] != 0:
            d.append(abs(int(S[i, i])))
    return reduce(lambda a, b: a*b, d, 1), d


def factors_small(x: int) -> str:
    # Only trial-divide small factors; enough to expose repeated nuisance.
    x = abs(int(x))
    if x == 0:
        return '0'
    parts = []
    p = 2
    while p <= 1000 and p*p <= x:
        if x % p == 0:
            e = 0
            while x % p == 0:
                x //= p
                e += 1
            parts.append(str(p) if e == 1 else f'{p}^{e}')
        p += 1 if p == 2 else 2
    if x != 1:
        parts.append(str(x))
    return '*'.join(parts) if parts else '1'


for n in TARGETS:
    H = (n - 1) // 3
    F = franel_list(H)
    hrows = [h_row(n, J, F) for J in range(H + 1)]
    trows, gammas = t_rows_and_contents(hrows)
    prod_gamma = reduce(lambda a, b: a*b, gammas, 1)

    low = selected_det(hrows, list(range(H + 1)))
    top = selected_det(hrows, list(range(n - H, n + 1)))
    formula = top_formula(n, H, F)
    assert formula.denominator == 1
    assert abs(top) == abs(formula.numerator)
    minus = int(taylor_matrix(hrows, -1, H).det())
    plus = int(taylor_matrix(hrows, 1, H).det())
    evals = int(eval_matrix(hrows, list(range(H + 1))).det())

    delta, diag = snf_last_divisor(hrows)
    assert delta % prod_gamma == 0
    residual = delta // prod_gamma

    scale = n * (H + 1)
    out = {
        'n': n,
        'H': H,
        'rank': H + 1,
        'gammas': gammas,
        'prodGammaRate_n2': logint(prod_gamma)/(n*n),
        'deltaRate_n2': logint(delta)/(n*n),
        'residualRate_n2': logint(residual)/(n*n) if residual else None,
        'topRate_nrank': logint(top)/scale,
        'lowRate_nrank': logint(low)/scale,
        'minusTaylorRate_nrank': logint(minus)/scale,
        'plusTaylorRate_nrank': logint(plus)/scale,
        'eval0HRate_nrank': logint(evals)/scale,
        'delta': str(delta),
        'prodGamma': str(prod_gamma),
        'residualSmallFactor': factors_small(residual),
        'snfDiag': [str(x) for x in diag],
    }
    print('RESULT', json.dumps(out, separators=(',', ':')))
