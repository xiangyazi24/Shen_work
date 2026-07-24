#!/usr/bin/env python3
from __future__ import annotations

from math import comb, gcd, log

TARGETS = [54, 100, 200, 300, 321, 400, 600, 717, 800, 11576]


def apery(N: int) -> list[int]:
    A=[0]*(N+1); A[0]=1
    if N>=1: A[1]=5
    for n in range(1,N):
        P=34*n**3+51*n**2+27*n+5
        num=P*A[n]-n**3*A[n-1]
        den=(n+1)**3
        assert num%den==0
        A[n+1]=num//den
    return A


def sieve(n: int):
    s=bytearray(b'\x01')*(n+1); s[:2]=b'\x00\x00'
    for p in range(2,int(n**0.5)+1):
        if s[p]: s[p*p:n+1:p]=b'\x00'*(((n-p*p)//p)+1)
    return [p for p in range(2,n+1) if s[p]]


def logint(x: int) -> float:
    x=abs(x)
    if x==0: return float('-inf')
    # Use bit length; enough for normalized-rate output.
    b=x.bit_length()
    if b<53: return log(x)
    shift=b-53
    return log(x>>shift)+shift*log(2.0)


def factor_small(x: int) -> str:
    x=abs(x); parts=[]
    p=2
    while p<=100000 and p*p<=x:
        if x%p==0:
            e=0
            while x%p==0: x//=p; e+=1
            parts.append(str(p) if e==1 else f'{p}^{e}')
        p += 1 if p==2 else 2
    if x!=1: parts.append(str(x))
    return '*'.join(parts) if parts else '1'


NMAX=max(TARGETS)
HMAX=(NMAX-1)//3
A=apery(HMAX)
primes=sieve(NMAX)

print('Q729 FULL-DEGREE LAGRANGE GCD AUDIT')
for n in TARGETS:
    H=(n-1)//3
    w=comb(n-1,H)  # signed w_0 has irrelevant sign
    g=0
    vals=[]
    for j in range(H+1):
        g=gcd(g,abs(w*A[j]))
        if j<H:
            num=w*(H-j)*(n-j)
            den=(j+1)*(n-j-1)
            assert num%den==0
            w=-(num//den)
    Bminus=comb(n,H+1)
    gd=gcd(g,Bminus)
    # Exact direct q=1 radical.
    R=1; bad=[]
    for p in primes:
        if p>n: break
        j=n-p
        if 0<=j<=H and 2*p>n and A[j]%p==0:
            R*=p; bad.append((p,j))
    assert gd%R==0
    # large-prime support of g for p>H, to check the interpolation localization.
    large=[]
    for p in primes:
        if p<=H or p>n: continue
        if g%p==0:
            r=n%p
            large.append((p,r,A[r]%p if r<=H else None))
            assert r<=H and A[r]%p==0
    print('RESULT', {
        'n':n,'H':H,'bad':bad,
        'g_factor':factor_small(g),'g_rate':logint(g)/n,
        'B_gcd_factor':factor_small(gd),'B_gcd_rate':logint(gd)/n,
        'R':R,'R_rate':logint(R)/n,
        'large_support':large,
    })
