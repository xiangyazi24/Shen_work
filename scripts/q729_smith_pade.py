#!/usr/bin/env python3
from __future__ import annotations

from math import comb, gcd, log
from functools import reduce
from sympy import Matrix
from sympy.matrices.normalforms import smith_normal_form
from sympy.polys.domains import ZZ

TARGETS = [12,15,18,21,24,27,30,33,36,39,42,45]


def apery(N):
    A=[0]*(N+1); A[0]=1
    if N>=1: A[1]=5
    for n in range(1,N):
        P=34*n**3+51*n**2+27*n+5
        num=P*A[n]-n**3*A[n-1]
        den=(n+1)**3
        assert num%den==0
        A[n+1]=num//den
    return A


def primes_upto(n):
    s=bytearray(b'\x01')*(n+1); s[:2]=b'\x00\x00'
    for p in range(2,int(n**.5)+1):
        if s[p]: s[p*p:n+1:p]=b'\x00'*(((n-p*p)//p)+1)
    return [p for p in range(2,n+1) if s[p]]


def det_divisor(M: Matrix) -> int:
    S=smith_normal_form(M,domain=ZZ)
    z=1; rank=0
    for i in range(min(S.rows,S.cols)):
        d=int(S[i,i])
        if d:
            z*=abs(d); rank+=1
    assert rank==M.rows, (M.shape,rank)
    return z


def logint(x):
    x=abs(int(x))
    if x==0: return float('-inf')
    s=str(x); take=min(16,len(s))
    return (len(s)-take)*log(10)+log(int(s[:take]))


def direct_rad(n,H,A):
    R=1; rows=[]
    for p in primes_upto(n):
        j=n-p
        if 2*p>n and 0<=j<=H and A[j]%p==0:
            R*=p; rows.append((p,j))
    return R,rows


def certificate_ideal(n,H,A,a,b):
    # Unknown coefficients in the binomial bases for P and Q.
    rows=[]
    for j in range(H+1):
        rows.append(
            [comb(j,i) if i<=j else 0 for i in range(a+1)]
            +[-A[j]*(comb(j,k) if k<=j else 0) for k in range(b+1)]
        )
    M=Matrix(rows)
    d0=det_divisor(M)
    L=[comb(n,i) for i in range(a+1)]+[0]*(b+1)
    Aug=M.col_join(Matrix([L]))
    # If the evaluation row is rationally dependent, every certificate is zero.
    if Aug.rank()<H+2:
        return 0,d0,0
    d1=det_divisor(Aug)
    assert d1%d0==0
    return d1//d0,d0,d1


A=apery(max(TARGETS))
print('Q729 SMITH NEWTON-PADE IDEAL AUDIT')
for n in TARGETS:
    H=(n-1)//3
    R,bad=direct_rad(n,H,A)
    rec=[]
    # extra = kernel dimension - 1; total degree a+b=H+extra
    for extra in range(0,min(5,H+1)):
        total=H+extra
        splits=sorted(set([0,total//4,total//2,3*total//4,total]))
        for a in splits:
            b=total-a
            # Avoid degrees beyond H+4 individually; columns above H have
            # identical zero patterns on the interpolation nodes and are allowed,
            # but make the audit much slower without adding local information.
            if a>H+4 or b>H+4: continue
            g,d0,d1=certificate_ideal(n,H,A,a,b)
            if g:
                assert g%R==0
            rec.append((extra,a,b,g,logint(g)/n if g else float('-inf'),logint(d0)/(n*n)))
    best=min((x for x in rec if x[3]),key=lambda x:x[4])
    print('N',n,'H',H,'R',R,'bad',bad,'BEST',best)
    for extra in range(0,min(5,H+1)):
        xs=[x for x in rec if x[0]==extra and x[3]]
        if xs:
            y=min(xs,key=lambda x:x[4])
            print(' EXTRA',extra,'BEST',y,'ALL',' '.join(f'{x[1]},{x[2]}:{x[4]:.9f}' for x in xs))
