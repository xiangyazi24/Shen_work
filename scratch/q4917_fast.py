#!/usr/bin/env python3
from math import comb

P = 1000003
NTERMS = 210


def inv(a): return pow(a % P, P-2, P)

def M(n):
    return [
      [(-2*n-5)*(n+3)**2*(136*n**4+1424*n**3+5548*n**2+9551*n+6141),
       384*n**6+6384*n**5+44168*n**4+162698*n**3+336377*n**2+369933*n+169011,
       -480*n**4-4980*n**3-19210*n**2-32690*n-20730],
      [(n+2)**2*(n+3)**2*(4*n+10)*(48*n**3+386*n**2+1017*n+879),
       (n+2)**2*(-272*n**5-3848*n**4-21732*n**3-61184*n**2-85761*n-47808),
       (n+2)**2*(320*n**3+2540*n**2+6610*n+5640)],
      [(-4*n-10)*(n+2)**2*(n+3)**2*(32*n**4+302*n**3+1037*n**2+1530*n+813),
       (n+2)**2*(192*n**6+2984*n**5+19116*n**4+64452*n**3+120256*n**2+117279*n+46476),
       (n+2)**2*(-16*n**5-408*n**4-2912*n**3-8884*n**2-12254*n-6240)]]

def delta(n): return -2*(n+2)**2*(n+3)**2*(2*n+5)*(2*n+7)**2

def rowmul(v,A): return [sum(v[i]*A[i][j] for i in range(3))%P for j in range(3)]

def seqs():
    q=[33750%P,-36000%P,9000%P]
    p=[30921%P,-32972%P,8240%P]
    Q=[]; G=[]
    for n in range(NTERMS):
        Q.append(q[0]); G.append(p[0])
        A=[[x%P for x in row] for row in M(n)]
        di=inv(delta(n))
        A=[[x*di%P for x in row] for row in A]
        q=rowmul(q,A); p=rowmul(p,A)
    return Q,G

def B(n,k):
    return pow(2,k,P)*(comb(2*k,k)%P)*(comb(n,k)%P)*(comb(n+k,k)%P)%P

def invert_transform(a):
    f=[]
    for n in range(len(a)):
        s=a[n]
        for k in range(n): s=(s-B(n,k)*f[k])%P
        f.append(s*inv(B(n,n))%P)
    return f

# RREF nullspace: returns basis, usually zero or one vector.
def nullspace(rows, ncols):
    A=[[(x%P) for x in row] for row in rows]
    m=len(A); piv=[]; r=0
    for c in range(ncols):
        pivot=next((i for i in range(r,m) if A[i][c]),None)
        if pivot is None: continue
        A[r],A[pivot]=A[pivot],A[r]
        z=inv(A[r][c]); A[r]=[(x*z)%P for x in A[r]]
        for i in range(m):
            if i!=r and A[i][c]:
                z=A[i][c]; A[i]=[(A[i][j]-z*A[r][j])%P for j in range(ncols)]
        piv.append(c); r+=1
        if r==m: break
    free=[c for c in range(ncols) if c not in piv]
    basis=[]
    for fc in free:
        v=[0]*ncols; v[fc]=1
        for i,c in reversed(list(enumerate(piv))):
            v[c]=(-sum(A[i][j]*v[j] for j in free))%P
        basis.append(v)
    return basis, len(piv)

def build(f,g,r,d,train):
    rows=[]
    for a in (f,g):
      for n in range(train):
        pw=[1]
        for _ in range(d): pw.append(pw[-1]*n%P)
        row=[]
        for j in range(r+1): row += [a[n+j]*x%P for x in pw]
        rows.append(row)
    return rows

def verify(v,f,g,r,d,start,end):
    for a in (f,g):
      for n in range(start,end):
        pw=[1]
        for _ in range(d): pw.append(pw[-1]*n%P)
        s=0; t=0
        for j in range(r+1):
          for m in range(d+1): s=(s+v[t]*pw[m]*a[n+j])%P; t+=1
        if s: return False
    return True

def print_pols(v,r,d):
    for j in range(r+1):
        cs=v[j*(d+1):(j+1)*(d+1)]
        print('p%d coeffs='%j,cs)

Q,G=seqs(); f=invert_transform(Q); g=invert_transform(G)
print('first f',f[:10]); print('first g',g[:10])
# Predicted rank-three search first, then broader.
pairs=[]
for d in range(0,61): pairs.append((3,d))
for r in range(1,16):
    if r!=3:
      for d in range(0,41): pairs.append((r,d))
for r,d in pairs:
    U=(r+1)*(d+1)
    train=max(30,(U+1)//2+8)  # two sequences => 2*train equations
    if train+r+30>NTERMS: continue
    rows=build(f,g,r,d,train)
    bas,rank=nullspace(rows,U)
    if bas:
        for v in bas:
            if verify(v,f,g,r,d,train,NTERMS-r):
                # normalize last nonzero to 1
                last=next(x for x in reversed(v) if x)
                il=inv(last); v=[x*il%P for x in v]
                print('FOUND order',r,'degree',d,'rank',rank,'nullity',len(bas))
                print_pols(v,r,d)
                raise SystemExit
        print('spurious kernel',r,d,len(bas))
print('NO RECURRENCE FOUND')
