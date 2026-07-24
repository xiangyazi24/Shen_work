#!/usr/bin/env python3
from __future__ import annotations
from math import comb, gcd, log
from functools import reduce
from sympy import Matrix, ilcm

TARGETS=[60,100,120,200,300,321,400,600,717,800]
BMAX=6

def apery(N):
    A=[0]*(N+1); A[0]=1
    if N: A[1]=5
    for n in range(1,N):
        num=(34*n**3+51*n**2+27*n+5)*A[n]-n**3*A[n-1]
        den=(n+1)**3
        assert num%den==0
        A[n+1]=num//den
    return A

def primitive_kernel(M):
    if M.rows==0: return [1]
    ns=M.nullspace(); assert len(ns)==1
    v=ns[0]; den=1
    for z in v: den=ilcm(den,int(z.q))
    w=[int(z*den) for z in v]
    g=reduce(gcd,(abs(x) for x in w if x),0)
    w=[x//g for x in w]
    for x in w:
        if x:
            if x<0: w=[-y for y in w]
            break
    return w

def logint(x):
    x=abs(int(x))
    if x<=1: return 0.0
    s=str(x); t=min(16,len(s))
    return (len(s)-t)*log(10.0)+log(int(s[:t]))

def primes_upto(n):
    s=bytearray(b'\x01')*(n+1); s[:2]=b'\x00\x00'
    for p in range(2,int(n**.5)+1):
        if s[p]: s[p*p:n+1:p]=b'\x00'*(((n-p*p)//p)+1)
    return [p for p in range(2,n+1) if s[p]]

def differences(A,N):
    T=[A[:N+1]]
    for _ in range(N): T.append([T[-1][i+1]-T[-1][i] for i in range(len(T[-1])-1)])
    return T

def split_num(n,H,b,A,D):
    a=H-b
    M=Matrix([[comb(k,l)*D[k-l][l] if l<=k else 0 for l in range(b+1)] for k in range(a+1,H+1)])
    q=primitive_kernel(M)
    vals=[A[j]*sum(q[l]*comb(j,l) for l in range(b+1)) for j in range(H+1)]
    # Newton coefficients of P=AQ on the interpolation nodes.
    cur=vals[:]; pc=[]
    for k in range(H+1):
        pc.append(cur[0])
        cur=[cur[i+1]-cur[i] for i in range(len(cur)-1)]
    assert all(x==0 for x in pc[a+1:])
    pc=pc[:a+1]
    assert reduce(gcd,(abs(x) for x in pc+q if x),0)==1
    Pn=sum(pc[i]*comb(n,i) for i in range(a+1))
    assert Pn!=0
    return Pn,pc,q

A=apery(max(TARGETS))
D=differences(A,max((n-1)//3 for n in TARGETS)+BMAX+3)
print('Q754 SPLIT-GCD AND ADJACENT-DETERMINANT AUDIT')
for n in TARGETS:
    H=(n-1)//3
    recs=[]
    for b in range(min(BMAX,H)+1):
        Pn,pc,q=split_num(n,H,b,A,D)
        recs.append((Pn,pc,q))
    nums=[r[0] for r in recs]
    prefix=[]; g=0
    for z in nums:
        g=gcd(g,abs(z)); prefix.append(g)
    pair=[gcd(abs(nums[i]),abs(nums[i+1])) for i in range(len(nums)-1)]
    # K_b = top Newton coefficient of P_(H-b,b) times top Newton
    # coefficient of Q_(H-b-1,b+1).  Factorials are p-units for p>H.
    Ks=[]
    for b in range(len(recs)-1):
        _,pc0,_=recs[b]
        _,_,q1=recs[b+1]
        Ks.append(pc0[-1]*q1[-1])
    Kg=[]; gk=0
    for z in Ks:
        gk=gcd(gk,abs(z)); Kg.append(gk)
    bad=[]; R=1
    cand=[]
    for p in primes_upto(n):
        j=n-p
        if n//2 < p <= n and 0<=j<=H:
            cand.append((p,j))
            if A[j]%p==0:
                bad.append((p,j)); R*=p
    assert all(z%R==0 for z in nums)
    print('N',n,'H',H,'bad',bad,'R',R,'Rrate',logint(R)/n)
    print('NUMRATES',' '.join(f'b{i}:{logint(z)/n:.9f}' for i,z in enumerate(nums)))
    print('PREFIXGCD',' '.join(f'k{i}:{logint(z)/n:.9f}' for i,z in enumerate(prefix)))
    print('PAIRGCD',' '.join(f'{i}-{i+1}:{logint(z)/n:.9f}' for i,z in enumerate(pair)))
    print('K_RATES',' '.join(f'K{i}:{logint(z)/n:.9f}' for i,z in enumerate(Ks)))
    print('K_PREFIX_GCD',' '.join(f'K0..{i}:{logint(z)/n:.9f}' for i,z in enumerate(Kg)))
    # Top-half candidate support in common K constants and in all numerators.
    commonK=[]; commonP=[]
    for p,j in cand:
        if Ks and all(z%p==0 for z in Ks): commonK.append((p,j,A[j]%p==0))
        if all(z%p==0 for z in nums): commonP.append((p,j,A[j]%p==0))
    print('COMMON_K_CAND',commonK)
    print('COMMON_P_CAND',commonP)
    print('GCD_OVER_R',prefix[-1]//R,'rate',logint(prefix[-1]//R)/n)
