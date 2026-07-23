#!/usr/bin/env python3
from __future__ import annotations

from math import comb, gcd, log
from functools import reduce
from sympy import Matrix, ilcm

TARGETS = [18, 24, 30, 36, 42, 48, 54, 60, 72, 84, 96, 108, 120]


def apery(N: int) -> list[int]:
    A = [0] * (N + 1)
    A[0] = 1
    if N >= 1:
        A[1] = 5
    for n in range(1, N):
        P = 34*n**3 + 51*n**2 + 27*n + 5
        num = P*A[n] - n**3*A[n-1]
        den = (n+1)**3
        assert num % den == 0
        A[n+1] = num // den
    return A


def primitive_kernel(M: Matrix) -> list[int]:
    ns = M.nullspace()
    assert len(ns) == 1, (M.shape, len(ns))
    v = ns[0]
    den = 1
    for z in v:
        den = ilcm(den, int(z.q))
    w = [int(z * den) for z in v]
    g = reduce(gcd, (abs(x) for x in w if x), 0)
    assert g > 0
    w = [x // g for x in w]
    # Canonical sign.
    for x in w:
        if x:
            if x < 0:
                w = [-y for y in w]
            break
    return w


def logint(x: int) -> float:
    x = abs(x)
    if x == 0:
        return float('-inf')
    s = str(x)
    take = min(16, len(s))
    return (len(s)-take)*log(10.0) + log(int(s[:take]))


def primes_upto(n: int) -> list[int]:
    s = bytearray(b'\x01')*(n+1)
    if n >= 0: s[0] = 0
    if n >= 1: s[1] = 0
    for p in range(2, int(n**0.5)+1):
        if s[p]:
            s[p*p:n+1:p] = b'\x00'*(((n-p*p)//p)+1)
    return [p for p in range(2,n+1) if s[p]]


def one_split(n: int, A: list[int], a: int):
    H = (n-1)//3
    b = H-a
    rows = []
    for j in range(H+1):
        row = [comb(j,i) if i <= j else 0 for i in range(a+1)]
        row += [-(A[j] * (comb(j,k) if k <= j else 0)) for k in range(b+1)]
        rows.append(row)
    v = primitive_kernel(Matrix(rows))
    pc = v[:a+1]
    qc = v[a+1:]
    Pn = sum(pc[i]*comb(n,i) for i in range(a+1))
    Qn = sum(qc[i]*comb(n,i) for i in range(b+1))
    residual = Pn - A[n]*Qn
    # Exact interpolation verification.
    for j in range(H+1):
        Pj = sum(pc[i]*comb(j,i) for i in range(a+1))
        Qj = sum(qc[i]*comb(j,i) for i in range(b+1))
        assert Pj == A[j]*Qj
    # Direct bad-prime certificate verification.
    bad = []
    for p in primes_upto(n):
        if not (2*p > n and p <= n):
            continue
        j = n-p
        if 0 <= j <= H and A[j] % p == 0:
            bad.append((p,j))
            assert Pn % p == 0
            assert residual % p == 0
    maxbits = max(abs(x).bit_length() for x in v)
    return {
        'a':a,'b':b,'Pn':Pn,'Qn':Qn,'R':residual,
        'rateP':logint(Pn)/n,'rateR':logint(residual)/n,
        'kernelBits':maxbits,'zeroP':Pn==0,'bad':bad,
    }


A = apery(max(TARGETS))
print('Q729 EXACT NEWTON-PADE AUDIT')
for n in TARGETS:
    H = (n-1)//3
    if n <= 60:
        splits = list(range(H+1))
    else:
        splits = sorted(set([0,H//6,H//4,H//3,H//2,2*H//3,3*H//4,5*H//6,H]))
    recs=[]
    for a in splits:
        try:
            recs.append(one_split(n,A,a))
        except Exception as e:
            print('FAIL',n,a,type(e).__name__,str(e)[:200])
            raise
    usable=[r for r in recs if not r['zeroP']]
    best=min(usable,key=lambda r:r['rateP'])
    bestR=min((r for r in recs if r['R']!=0),key=lambda r:r['rateR'])
    print('N',n,'H',H,'bad',best['bad'])
    print('BEST_P', {k:best[k] for k in ['a','b','rateP','rateR','kernelBits','zeroP']})
    print('BEST_RESIDUAL', {k:bestR[k] for k in ['a','b','rateP','rateR','kernelBits','zeroP']})
    print('SPLITS', ' '.join(f"{r['a']}:{r['rateP']:.9f}/{r['rateR']:.9f}/{r['kernelBits']}" for r in recs))
